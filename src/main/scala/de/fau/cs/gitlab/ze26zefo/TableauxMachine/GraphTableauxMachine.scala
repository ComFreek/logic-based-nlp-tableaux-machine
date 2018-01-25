package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.objects._

import scala.collection.immutable.HashSet
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.GraphPredef._
import scalax.collection.GraphTraversal.Predecessors
import scalax.collection.mutable.Graph

/**
  * A FOL model generator based on a Tableaux calculus working on trees.
  *
  * Supported rules are:
  * - (∨E): `(a ∨ b)^T`
  * - `(a ∨ b)^F`
  * - (=E): `(a = b)^T` in conjunction with `ϕ = ψ`, of them containing `a` or `b`.
  * - (RM: ∀): `(∀x.ϕ)^T`
  * - (RM: ∃): `(∀x. ϕ)^F`
  *
  * <h2>General introduction</h2>
  *
  * Each node in the tree (in the following subsumed under 'graph') corresponds
  * to a list of terms with some additional attributes (a TableauxColumn instance).
  * Initially, the graph only consists of one root node which gets all the terms
  * you feed into the machine.
  * Some of the above mentioned rules have the property that they branch. For example,
  * the `(a ∨ b)^T` rule will branch into exactly two branches on the node where the term
  * it is applied on is contained. The left branch, a new TableauxColumn, will contain a,
  * and the right branch, a new TableauxColumn as well, will contain b.
  * Multiple children of a node generally indicate different world conditions (i.e. models)
  * which might be true.
  *
  * This implementation applies the rule exhaustively until the first model is found upon
  * nextModel() calls. Note that this is actually implementation-defined and might well
  * happen in feed() instead.
  *
  * <h2>Specifics</h2>
  *
  * <h3>Branching</h3>
  *
  * The branching rules are:
  *
  * - (∨E)
  * - (RM: ∃)
  *
  * If a branching rule is applied on a node, the branching "interface" and the children of
  * this node are implicitly reserved for the used term. On a single node, never are two or
  * more applications of (∨E), (RM: ∃) or combinations thereof performed.
  *
  * This means that upon the machine working in lower nodes in the tree unprocessed instances
  * of branching rules in upper nodes need to be checked as well. Especially, a term which a
  * branching rule is applied on need not be in the same node where the branching occurs.
  *
  * Instances of TableauxColumn save the information on the applied branching rule. Unprocessed
  * terms (i.e. ORs or existential quantifiers) are queried on-the-fly from upper nodes in
  * GraphTableauxMachine's internal method.
  *
  * <h3>Keeping track of the current node</h3>
  *
  * The class keeps track of a `curNode` variable referring to the current node of inspection
  * inside the graph.
  * nextModel() and step() are built around the idea that, starting from the root, we always
  * first saturate the current node before stepping down to one of its children. By this means,
  * we can make use of GraphTableauxMachine.isConsistent() which does not perform steps
  * anymore, but checks for consistency in a "naive" way. Cf. its documentation on formalization
  * on "naive".
  *
  * <h3>Equalities</h3>
  *
  * (=E) was implemented in another way contrary to the other rules: when nextModel() checks
  * for consistency using isConsistent(), the method will search for pairs (φ^s, ψ^t) with
  * s != t and φ = ψ either syntactically or up to replacements of individual constants deemed
  * equivalent. Hereby, we avoid having to actually apply any replacement rule in step(), which
  * would require complicated tracking of which individual constants have been replaced in
  * which terms yet on the very branch the machine is currently on.
  *
  * The equivalence sets (e.g. having (a = b)^T, (c = d)^T, (a = d)^T, (e = f)^T, one would get
  * {a, b, c, d}, {e, f}) are computed in step() with equivalenceSetsClosure and used by
  * isConsistent().
  */
class GraphTableauxMachine extends ModelGenerator {

  import info.kwarc.gf.Convenience._

  /**
    * Instances of this class correspond 1:1 to nodes in the graph. They save a
    * list of terms.
    * @see GraphTableauxMachine
    */
  class TableauxColumn(_terms: List[(Term, Boolean)] = Nil) {

    import TermStringHelpers._

    /**
      * Annotated terms.
      */
    var terms: mutable.ArrayBuffer[(Term, Boolean)] = ArrayBuffer(_terms: _*)

    /**
      * Processed terms from this column only. This makes it easier
      * to check whether processing (not(a), sgn) is necessary.
      * Due to the nature of (a or b, true) terms and that each node
      * can only process one of them, processedTerms does *not* capture
      * these (a or b, true) terms!
      *
      * @see processedOr
      */
    var processedTerms: mutable.Set[(Term, Boolean)] = mutable.HashSet()

    /**
      * The equivalence sets induced by all equations of the form (a = b, true)
      * on the path from node corresponding to this column up to the root.
      *
      * Self-mappings are not necessarily stored herein, e.g. if no equations
      * were ever fed into the machine, equivalenceSets will be an empty set,
      * even though [a] = {a} for every term a trivially holds.
      *
      * This variable is always updated in step().
      *
      * @see GraphTableauxMachine.step()
      */
    var equivalenceSets: Set[Set[Term]] = HashSet()

    /**
      * Every column/corresponding node can only process one (a or b, true) term.
      * When doing so, two children of the node are generated with (a, true) and (b, true).
      *
      * Note that the term does not need to belong to this node. It must belong to one node
      * from the path from this node up to the root, however.
      */
    var processedOr: Option[Term] = None

    /**
      * If the corresponding node ands its children deals with an existential quantifier,
      * it is stored herein.
      *
      * The LocalName tuple field is the quantified variable (e.g. LocalName(SimpleStep("x")))
      * and the Term tuple field is the inner term, which might mention the quantified variable.
      */
    var processedExistentialQuantifier: Option[(LocalName, Term)] = None

    /**
      * If processedExistentialQuantifier is populated, this set keeps track of the individual
      * constants with which the existential quantifier has been instantiiated.
      */
    val processedExistentialConstants: mutable.Set[LocalName] = mutable.HashSet()

    /**
      * If processedExistentialQuantifier is populated, this flag keeps track whether we have
      * yet instantiiated the existential quantifier with a freshly created individual constant.
      *
      * This is useful in the following case:
      *
      * If all branches of a node with a processed existential quantifier close and we already used
      * a fresh individual constant, we can conclude that the existential quantifier leads to a
      * contradiction.
      */
    var usedFreshExistentialConstants: Boolean = false

    /**
      * Flag whether this column has been closed yet, i.e. whether there is a
      * contradiction among the set of terms on the path from the node
      * corresponding to this column up to the root.
      */
    var isClosed: Boolean = false

    override def toString: String = termSeqToString(terms)
  }

  // Node type Column, edges are directed (TODO: add weighted edges later on!)
  private val graph = Graph[TableauxColumn, DiEdge](new TableauxColumn())

  private val root: graph.NodeT = graph.nodes.head
  /**
    * The current tableaux column. It might be either closed or saturated or none of them (i.e. still open).
    */
  private var curNode: graph.NodeT = graph.nodes.head

  /**
    * Store the assigned fresh individiual constants in the course of (RM: \exists) applications.
    */
  private val freshIndividualConstants: mutable.Set[LocalName] = mutable.HashSet[LocalName]()

  /**
    * Feed a new term into the machine, which is annotated with True.
    *
    * @see feedAnnotated
    */
  override def feed(term: Term): Unit = {
    feedAnnotated((term, true))
  }

  /**
    * Feed a new annotated term into the machine.
    */
  private def feedAnnotated(input: (Term, Boolean)): Unit = {
    // Currently, we always feed new inputs to the root node
    // because of two reasons:
    // 1. If we added it in curNode and curNode would then close
    //    by any means, we would need to re-feed the inputs
    //    to the next unclosed node to which we backtracked.
    //
    // 2. We reset curNode to root because nextModel() always
    //    assumes that all nodes from curNode's parent up to
    //    the root are saturated.

    root.terms = root.terms :+ input
    curNode = root
  }

  /**
    * Check whether all terms in a given node, and optionally all those found on the path
    * up to the root, form a "naive" consistent set of terms.
    *
    * A set of terms is "native" consistent iff. it doesn't contain annotated formulae
    * φ^s and ψ^t with:
    *
    * 1. different annotations: s != t
    * 2. and φ = ψ syntactically or up to replacements of individual constants deemed equivalent.
    *    Individual constants are deemed equivalent iff. they are both in the same equivalence set
    *    induced by all equality terms occurring in the node (or optionally on the path up to the root).
    *
    * For this method to be useful with, you have to saturate the node (and optionally all
    * nodes on the path up to the root) before calling it.
    *
    * @see equivalenceSetsClosure
    *
    * @param node The node to inspect.
    * @param inspectUpToRoot If True, the node itself and all the nodes on the path up to the root are
    *                        inspected as a whole.
    * @return True iff. the terms form a "native" consistent set of terms.
    */
  private def isConsistent(node: graph.NodeT, inspectUpToRoot: Boolean): Boolean = {
    lazy val allTermsToRoot = node
      .innerNodeTraverser
      .withDirection(Predecessors)
      .flatMap((node: graph.NodeT) => node.terms)
      .toSet

    val terms: Set[(Term, Boolean)] = if (inspectUpToRoot) allTermsToRoot else node.terms.toList.toSet

    !terms.exists((annotatedTerm) =>
      terms.exists((otherAnnotatedTerm) => {
        if (annotatedTerm._1 == otherAnnotatedTerm._1 &&
          annotatedTerm._2 != otherAnnotatedTerm._2) {
          true
        }
        else {
          // Two n-ary predicates pred(c_1, ..., c_n)^T, pred'(d_1, ..., d_n)^F
          // lead to contradiction iff
          //  1. pred = pred', i.e. their names are equal
          //  2. c_i = d_i for all i <=> [c_i] = [d_i] when [.] denotes the equivalence class
          //     as formed by equivalence terms (a = b). See step().
          //
          //     As TableauxColumn#equivalenceSets does not necessarily contain self-mappings, i.e.
          //     a \in [a] if no equations were ever fed into the machine, we getOrElse(Set[Term](a))
          //     in all cases.
          (annotatedTerm, otherAnnotatedTerm) match {
            case ((Pred1(predName1, arg1), true), (Pred1(predName2, arg2), false)) if predName1.equals(predName2) =>
              val eqvSets: Set[Set[Term]] = node.equivalenceSets
              eqvSets.find(_.contains(arg1)).getOrElse(Set[Term](arg1)).contains(arg2)
            case ((Pred2(predName1, arg11, arg12), true), (Pred2(predName2, arg21, arg22), false)) if predName1.equals(predName2) =>
              val eqvSets: Set[Set[Term]] = node.equivalenceSets
              eqvSets.find(_.contains(arg11)).getOrElse(Set[Term](arg11)).contains(arg21) &&
                eqvSets.find(_.contains(arg12)).getOrElse(Set[Term](arg12)).contains(arg22)

            // = can also be seen as a predicate, with a fixed definition, however.
            // ("logical constant" as it is the same in every model)
            case ((Eq(a, b), true), (Eq(c, d), false)) =>
              val eqvSets: Set[Set[Term]] = node.equivalenceSets
              eqvSets.find(_.contains(a)).getOrElse(Set[Term](a)).contains(c) &&
                eqvSets.find(_.contains(b)).getOrElse(Set[Term](b)).contains(d)
            case _ => false
          }
        }
      })
    )
  }

  /**
    * Form the equivalence sets of the equivalence set closure of the passed equivalence.
    *
    * The equivalence set closure closes the passed equivalences with respect to
    * i) symmetry, ii) reflexivity, and iii) transivity.
    *
    * For example, if you pass ((a, b), (c, d), (b, d), (e, f), (g, h), (e, h)), the
    * equivalence sets will be {a, b, c, d} and {e, f, g, h}.
    *
    * @param equivalences The equivalences as a set of tuples, i.e. each tuple corresponds
    *                     to an equality.
    * @return All equivalence sets.
    */
  private def equivalenceSetsClosure(equivalences: Seq[(Term, Term)]): Set[Set[Term]] = {
    var classes = mutable.ArrayBuffer[mutable.Set[Term]]()

    equivalences.foreach(equation => {
      val class1 = classes.find(c => c.contains(equation._1))
      val class2 = classes.find(c => c.contains(equation._2))

      if (class1.isEmpty && class2.isEmpty) {
        // Add new equivalence class
        classes.append(mutable.HashSet(equation._1, equation._2))
      }
      else if (class1.isDefined && class2.isEmpty) {
        class1.get.add(equation._2)
      }
      else if (class1.isEmpty && class2.isDefined) {
        class2.get.add(equation._1)
      }
      else if (class1.isDefined && class2.isDefined) {
        if (class1.get == class2.get) {
          // Nothing to be done
        }
        else {
          // Merge the equivalence classes class1, class2
          classes = classes.filter(c => c != class1.get && c != class2.get)
          classes.append(class1.get union class2.get)
        }
      }
      else {
        assert(false)
      }
    })

    classes.map(s => s.toSet).toSet
  }

  /**
    * Collect all individual constants occurring on the path from the passed node
    * up to the root.
    * Individual constants are exactly the free variables of the terms.
    */
  private def collectIndividualConstants(node: graph.NodeT): Set[LocalName] = {
    node
      .innerNodeTraverser
      .withDirection(Predecessors)
      .flatMap((node: graph.NodeT) => node.terms.flatMap((annotatedTerm: (Term, Boolean)) => annotatedTerm._1.freeVars).toList)
      .toSet
  }

  private def stepRMForallRule(node: graph.NodeT): Boolean = {
    // (RM:∀) rule
    val individualConstants = collectIndividualConstants(node)

    val forallInducedTerms: Set[(Term, Boolean)] = node
      .innerNodeTraverser
      .withDirection(Predecessors)
      .flatMap((node: graph.NodeT) => node.terms.collect{
        case (forall(x, innerTerm), true) => {
          individualConstants
            .map(ind => innerTerm.substitute(Substitution(Sub(x, OMV(ind))))(PlainSubstitutionApplier))
        }
      })
      .flatten
      .map((_, true)) // Annotate with true
      .toSet

    lazy val allTerms: Set[(Term, Boolean)] = node
      .innerNodeTraverser
      .withDirection(Predecessors)
      .flatMap(_.terms)
      .toSet

    val newTerms = forallInducedTerms diff allTerms
    if (newTerms.nonEmpty) {
      node.terms.append(newTerms.toList : _*)
      true
    }
    else {
      false
    }
  }

  /**
    * Do an unspecified number of Tableaux steps in the given node.
    * To ensure saturation, call this function until it returns false.
    * Consistency is neither checked nor updated in node.isClosed.
    *
    * A yet unprocessed (a or b, true) from the given node or one of its
    * parents will only be processed if this node does not have any children yet.
    *
    * @return changed - True when a step has been done, False otherwise.
    */
  private def step(node: graph.NodeT): Boolean = {
    val curColumn: TableauxColumn = node.value

    var termIndex = 0
    var changed = false
    while (termIndex < curColumn.terms.size) {
      val term = curColumn.terms(termIndex)
      if (!curColumn.processedTerms.contains(term)) term match {
        case (not(a), sgn) =>
          curColumn.terms.append((a, !sgn))
          curColumn.processedTerms.add(term)

          changed = true

        case (a or b, false) =>
          curColumn.terms.append((a, false), (b, false))
          curColumn.processedTerms.add(term)

          changed = true

        case _ =>
      }
      termIndex = termIndex + 1
    }

    if (node.diSuccessors.isEmpty && node.processedOr.isEmpty) {
      // Resolve unresolved (a or b, true) from parents

      // 1. Gather all processed ORs on the path from this node up to the root
      val processedOrs: Set[info.kwarc.mmt.api.objects.Term] = node
        .innerNodeTraverser
        .withDirection(Predecessors)
        .map((node: graph.NodeT) => node.processedOr)
        .filter(_.isDefined)
        .map(_.get)
        .toSet

      // 2. Gather all ORs on the path from this node up to the root
      val allOrs: Set[info.kwarc.mmt.api.objects.Term] = node
        .innerNodeTraverser
        .withDirection(Predecessors)
        .flatMap((node: graph.NodeT) => node.terms.collect { case (a or b, true) => a or b })
        .toSet

      val unprocessedOrs = allOrs diff processedOrs

      // Take an arbitrary OR to process
      if (unprocessedOrs.nonEmpty) unprocessedOrs.head match {
        case a or b =>
          val left = new TableauxColumn(List((a, true)))
          val right = new TableauxColumn(List((b, true)))

          graph.add(curColumn ~> left)
          graph.add(curColumn ~> right)

          node.processedOr = Some(a or b)
          changed = true

        case _ => assert(false)
      }
    }

    // Update equivalence sets
    node.equivalenceSets = equivalenceSetsClosure(
      node
      .innerNodeTraverser
      .withDirection(Predecessors)
      .flatMap((node: graph.NodeT) => node.terms.collect{ case (a Eq b, true) => (a, b) })
      .toSeq
    )

    if (changed) {
      return true
    }

    // Only apply (RM: \forall) if no other rule was applicable. (This is an optional design decision.)
    if (stepRMForallRule(node)) {
      return true
    }
    // Only apply (RM: \exists) if no other rule was applicable,
    // so that existential quantifiers are only resolved (actually created) at leafs.
    // Their branches (apart from the first one) are created in backtrackToUnclosed.

    if (node.processedExistentialQuantifier.isEmpty && node.diSuccessors.isEmpty) {
      return tryBeginningOfRMExistsRule(node)
    }

    false
  }

  /**
    * Begin a *new* (RM: \exists) rule application on a node. The \exists quantifier
    * is taken from a (potentially far away) predecessor node.
    *
    * The passed node must not have any children yet and its corresponding TableauxColumn
    * object must not have its TableauxColumn.processedExistentialQuantifier set.
    *
    * If a yet unprocessed existential quantifier is found in any predecessor node, it is
    * marked as processed in the passed node and (RM: \exists) is applied *once*.
    * Hence, only one child branch (with either an existent individual constant
    * or a freshly created constant if the former doesn't exist) is created. More branches
    * are added in backtrackToUnclosed(), namely when the previous branches all got closed
    * and we backtrack.
    *
    * @return True if (RM: \exists) could be applied. That is the case iff. an unprocessed
    *         existential quantifier could be found in a predecessor node. Otherwise, False
    *         is returned and it is guaranteed that no changed have been made anywhere.
    */
  private def tryBeginningOfRMExistsRule(node: graph.NodeT): Boolean = {
    assert(node.processedExistentialQuantifier.isEmpty)
    assert(node.diSuccessors.isEmpty)

    val existentialQuantifiers: Set[(LocalName, Term)] =
      node
        .innerNodeTraverser
        .withDirection(Predecessors)
        .flatMap((node: graph.NodeT) => node.terms.collect {
          case (forall(x, innerTerm), false) => (x, innerTerm).asInstanceOf[(LocalName, Term)]
        })
        .toSet

    val processedExistentialQuantifiers: Set[(LocalName, Term)] =
      node
        .innerNodeTraverser
        .withDirection(Predecessors)
        .map((node: graph.NodeT) => node.processedExistentialQuantifier)
        .filter(_.isDefined)
        .map(_.get)
        .toSet

    val unprocessedExistentialQuantifiers = existentialQuantifiers diff processedExistentialQuantifiers

    if (unprocessedExistentialQuantifiers.nonEmpty) {
      // Pick an arbitrary one
      val existentialQuantifier = unprocessedExistentialQuantifiers.head
      node.processedExistentialQuantifier = Some(existentialQuantifier)

      oneStepRMExistential(node)
      true
    }
    else {
      false
    }
  }

  /**
    * Create a new fresh individual constant, register it at
    * GraphTableauxMachine.freshIndividualConstants and return it.
    *
    * This method is inherently not thread-safe.
    *
    * @return The new fresh individual constant. Its name is implementation-defined.
    */
  private def createFreshIndividualConstant(): LocalName = {
    val name = LocalName(SimpleStep("fresh" + freshIndividualConstants.size))
    freshIndividualConstants.add(name)
    name
  }

  /**
    * Perform one step of (RM: \exists) on a given node assuming an existential quantifier has already been
    * chosen to be processed.
    *
    * @param node The node to perform the step on. The corresponding TableauxColumn must have its
    *             processedExistentialQuantifier field filled. The field
    *             processedExistentialConstants can be empty, though, as is the case at the
    *             beginning of a new (RM: \exists) application.
    * @return The new child with a one-element tableaux, namely with the term introduced by (RM: \exists).
    */
  private def oneStepRMExistential(node: graph.NodeT): graph.NodeT = {
    assert(node.processedExistentialQuantifier.isDefined)

    assert(!node.usedFreshExistentialConstants, "Application of (RM: \\exists) even though we" +
      "already have a fresh existential constant branch. If that branch has been closed, no" +
      "other fresh branch could be saturated without closing.")

    val unprocessedIndividualConstants = collectIndividualConstants(node) diff node.processedExistentialConstants

    val constant = if (unprocessedIndividualConstants.nonEmpty) {
      unprocessedIndividualConstants.head
    } else {
      node.usedFreshExistentialConstants = true
      createFreshIndividualConstant()
    }

    node.processedExistentialConstants.add(constant)

    val existentialQuantifier: (LocalName, Term) = node.processedExistentialQuantifier.get

    val substitution: Term = existentialQuantifier._2.substitute(
      Substitution(Sub(existentialQuantifier._1, OMV(constant)))
    )(PlainSubstitutionApplier)

    // (RM: \exists) rule
    val newExistenceChild = new TableauxColumn(List((substitution, false)))
    graph.addAndGet(node.value ~> newExistenceChild).to
  }

  /**
    * Check whether an annotated term is atomic, i.e. it is one of
    * - pred(t_1, ..., t_n), an n-ary predicate
    *
    * @author Dennis Müller in his ModelGenerator.
    */
  private def isAtomic(tm: (Term, Boolean)) = tm match {
    case (Pred1(_, a), _) => true
    case (Pred2(_, a, b), _) => true
    case _ => false
  }

  /**
    * Collects a model from a given node all the way up to the root.
    * All atomic formulae will be put into the model with their respective sign/annotation (true/false).
    *
    * @param originNode
    * @return
    */
  private def collectModel(originNode: graph.NodeT): Model = {
    // Traverse the current node up to the root while collecting all atomic terms
    val atomicTerms: List[(Term, Boolean)] = List(
      curNode.outerNodeTraverser.withDirection(Predecessors).flatMap(_.terms.filter(isAtomic _))
    ).flatten

    // Add (=) closure, cf. LBS lecture notes, slide 103 ("PL_NQ^=: Adding equality to PL_NQ")
    val closuredAtomicTerms: Seq[(Term, Boolean)] = atomicTerms.flatMap((tm: (Term, Boolean)) => tm match {
      case (Pred1(predName, arg1), sgn) =>
        originNode.equivalenceSets.find(s => s.contains(arg1)).getOrElse(Set(arg1)).map(equivalentConstant =>
          (Pred1(predName, equivalentConstant), sgn)
        )

      case (Pred2(predName, arg1, arg2), sgn) =>
        originNode.equivalenceSets.find(s => s.contains(arg1)).getOrElse(Set(arg1)).flatMap(equivalentConstant1 =>
          originNode.equivalenceSets.find(s => s.contains(arg2)).getOrElse(Set(arg2)).map(equivalentConstant2 =>
            (Pred2(predName, equivalentConstant1, equivalentConstant2), sgn)
          )
        )

      case _ => List(tm)
    })

    val interpretation = closuredAtomicTerms.map(x => x._1 -> x._2).toMap

    new Model {
      def getInterpretation: Map[Term, Boolean] = {
        interpretation
      }
    }
  }

  /**
    * Get the parent of a node as an optional value.
    * (It is assumed that node only has one predecessor.)
    */
  private def parent(node: graph.NodeT): Option[graph.NodeT] = {
    node.diPredecessors.toSeq.headOption
  }

  /**
    * Backtracks from a closed node to the next (allegedly) unclosed node.
    * Consistency is *not* doublechecked with isConsistent.
    *
    * @param origin The closed node to start from.
    * @return Some node if there is still an unclosed node or None.
    */
  private def backtrackToUnclosed(origin: graph.NodeT): Option[graph.NodeT] = {
    assert(origin.isClosed)

    val originParent = parent(origin)
    if (originParent.isEmpty || originParent.get.isClosed) {
      // The root is itself closed
      return None
    }
    var curNode = originParent.get
    while (true) {
      val children = curNode.diSuccessors
      if (children.isEmpty) {
        // curNode is (currently yet) a leaf
        return Some(curNode)
      }

      val unclosedChildren = curNode.diSuccessors.filter(!_.isClosed)
      if (unclosedChildren.isEmpty) {
        // Only closed children (>= 1 children, though) and we do not have an infinitely spawning
        // existential quantifier node at hand
        if (curNode.processedExistentialQuantifier.isEmpty) {
          curNode.isClosed = true
          if (parent(curNode).isEmpty) {
            // The root itself has been just closed
            return None
          }
          curNode = parent(curNode).get
        }
        else {
          // If we already have used a fresh existential constant and that branch
          // apparently closed (otherwise we would have unclosedChildren.nonEmpty),
          // the existential quantifier leads itself to a contradiction.
          if (curNode.usedFreshExistentialConstants) {
            curNode.isClosed = true
            if (parent(curNode).isEmpty) {
              // The root itself has been just closed
              return None
            }
            curNode = parent(curNode).get
          }
          else {
            curNode = oneStepRMExistential(curNode)
          }
        }
      }
      else {
        // Descend to a "random"/unspecified open child
        curNode = unclosedChildren.head
      }
    }

    None
  }

  /**
    * Generate the next model if it exists.
    *
    * @return A populated Option if a model exists and None otherwise.
    */
  @Override
  override def nextModel(): Option[Model] = {
    while (true) {
      val changed = step(curNode)

      if (!changed) {
        if (curNode.hasSuccessors) {
          curNode = curNode.diSuccessors.head
        }
        else {
          // Saturated, check if consistent model
          if (isConsistent(curNode, inspectUpToRoot = true)) {
            return Some(collectModel(curNode))
          }
          else {
            curNode.isClosed = true

            val nextUnclosedLeaf = backtrackToUnclosed(curNode)
            if (nextUnclosedLeaf.isEmpty) {
              return None
            }
            curNode = nextUnclosedLeaf.get
            assert(!curNode.isClosed)
          }
        }
      }
    }

    None
  }

  /**
    * Generate a fully self-contained LaTeX .tex document which shows
    * the current state of the graph.
    *
    * Internally, the LaTeX package "forest" is used.
    *
    * @return The LaTeX document as a string.
    */
  def generateLatexDocument(): String = {

    // \ u005c\ u0075 (without the spaces) is a necessary encoding for "\ u" because Scala treats
    // Unicode escape sequences at the parser level, thus also in raw strings:
    // https://stackoverflow.com/q/24058549
    val latexHeader = """% Template copied from https://tex.stackexchange.com/a/282192
%
% @author cfr <https://tex.stackexchange.com/users/39222/cfr>
% @license CC BY-SA 3.0 with attribution required <https://creativecommons.org/licenses/by-sa/3.0/>
\documentclass[tikz,border=10pt]{standalone}
\u005c\u0075sepackage{forest}
\forestset{
  smullyan tableaux/.style={
    for tree={
      math content,
      parent anchor=south,
      child anchor=north,
    },
    where n children=1{
      !1.before computing xy={l=\baselineskip},
      !1.no edge
    }{},
  },
}
\begin{document}
\begin{forest}
  smullyan tableaux
"""

    latexHeader + generateLatexFromNode(root) + "\\end{forest}\\end{document}"
  }

  /**
    * Generate recursively LaTeX code for use inside a \begin{forest}\end{forest}
    * environment in conjunction with the LaTeX "forest" package.
    *
    * @param node The node to start from. The graph reachable from this ndoe must
    *             be a tree and must not contain loops. Otherwise, this method
    *             will run into an infinite loop.
    * @return LaTeX code for use inside a "forest" environment.
    */
  private def generateLatexFromNode(node: graph.NodeT): String = {
    val nodeTermContents: List[String] = node.terms.map((annotatedTerm: (Term, Boolean)) => {
      "{" + TermStringHelpers.termToLatex(annotatedTerm._1) + "}^" + (if (annotatedTerm._2) "T" else "F")
    }).toList

    val nodeContents = nodeTermContents ++ (if (node.isClosed) List("\\bot") else Nil)

    "%s%s%s".format(
      nodeContents.map(s => "[" + s).mkString("\n"),
      node.diSuccessors.map(generateLatexFromNode).mkString(" "),
      "]" * nodeContents.size
    )
  }
}

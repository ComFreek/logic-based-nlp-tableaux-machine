package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api.objects.Term

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scalax.collection.GraphEdge.DiEdge
import scalax.collection.GraphPredef._
import scalax.collection.GraphTraversal.Predecessors
import scalax.collection.mutable.Graph

class GraphTableauxMachine extends ModelGenerator {

  import info.kwarc.gf.Convenience._

  object TermStringHelpers {
    def termToString(term: Term): String = term match {
      case a or b => "(" + termToString(a) + ") v (" + termToString(b) + ")"
      case not(a) => "not(" + termToString(a) + ")"
      case Pred1(globalName, innerTerm) => globalName.name.steps.last.toPath
      case _ => ???
    }

    def termSeqToString(terms: Seq[(Term, Boolean)]): String = {
      terms.map(annotatedTerm => termToString(annotatedTerm._1) + ": " + annotatedTerm._2).mkString(", ")
    }

    def termSetToString(terms: Set[(Term, Boolean)]): String = termSeqToString(terms.toSeq)
  }


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
      * Every column/corresponding node can only process one (a or b, true) term.
      * When doing so, two children of the node are generated with (a, true) and (b, true).
      *
      * Note that the term does not need to belong to this node. It must belong to one node
      * from the path from this node up to the root, however.
      */
    var processedOr: Option[Term] = None

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

  override def feed(term: Term): Unit = {
    feedAnnotated((term, true))
  }

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

  private def isConsistent(node: graph.NodeT, inspectUpToRoot: Boolean): Boolean = {
    lazy val allTermsToRoot = node
      .innerNodeTraverser
      .withDirection(Predecessors)
      .flatMap((node: graph.NodeT) => node.terms)
      .toSet

    val terms: Set[(Term, Boolean)] = if (inspectUpToRoot) allTermsToRoot else node.terms.toList.toSet

    !terms.exists((annotatedTerm) =>
      terms.exists((otherAnnotatedTerm) => {
        annotatedTerm._1 == otherAnnotatedTerm._1 &&
          annotatedTerm._2 != otherAnnotatedTerm._2
      })
    )
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

    if (node.processedOr.isEmpty) {
      // Resolve unresolved (a or b, true) from parents

      // 1. Gather all processed ORs on the path from this node up to the root
      val processedOrs: Set[info.kwarc.mmt.api.objects.Term] = curNode
        .innerNodeTraverser
        .withDirection(Predecessors)
        .map((node: graph.NodeT) => node.processedOr)
        .filter(_.isDefined)
        .map(_.get)
        .toSet

      // 2. Gather all ORs on the path from this node up to the root
      val allOrs: Set[info.kwarc.mmt.api.objects.Term] = curNode
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

    changed
  }

  /**
    * Check whether an annotated term is atomic, i.e. it is one of
    * - pred(t_1, ..., t_n), an n-ary predicate
    * - t_1 = t_2, an equality
    *
    * @author Dennis Müller in his ModelGenerator.
    */
  private def isAtomic(tm: (Term, Boolean)) = tm match {
    case (Pred1(_, a), _) => true
    case (Pred2(_, a, b), _) => true
    case (a Eq b, _) => true
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
    val interpretation = atomicTerms.map(x => x._1 -> x._2).toMap

    new Model {
      def getInterpretation: Map[Term, Boolean] = {
        interpretation
      }
    }
  }

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
        // All children are closed, so we can close curNode as well
        curNode.isClosed = true
        if (parent(curNode).isEmpty) {
          // The root itself has been just closed
          return None
        }
        curNode = parent(curNode).get
      }
      else {
        // Descend to a "random"/unspecified open child
        curNode = unclosedChildren.head
      }
    }

    None
  }

  /**
    * Generates the next model if it exists.
    * @return
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
}

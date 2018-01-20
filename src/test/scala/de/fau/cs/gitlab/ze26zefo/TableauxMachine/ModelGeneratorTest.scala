package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.utils.URI
import org.scalatest._
import info.kwarc.gf.Convenience.{Pred1, Pred2, Eq => termEq, forall => termForall, not => termNot, or => termOr}

import scala.collection.Map
class ModelGeneratorTest extends FlatSpec with Matchers {

  trait Machine {
    val machine: ModelGenerator = new GraphTableauxMachine()
  }

  // For debugging purposes
  private def modelToString(model: Model): String = {
    val interpretation = model.getInterpretation
    interpretation.keys.map(term => {
      TermStringHelpers.termToString(term) + ": " + interpretation(term)
    }).mkString("\n")
  }

  private def genGlobalPredName(name: String): GlobalName = {
    val mpath = MPath(DPath(URI.http colon "test"), new LocalName(List(SimpleStep("test"))))
    GlobalName(mpath, new LocalName(List(SimpleStep(name))))
  }

  private def v(name: String): Term = {
    val term = new OMV(new LocalName(List(SimpleStep(name))))

    Pred1(genGlobalPredName(name), term)
  }

  private def c(name: String): Term = {
    OMV(LocalName(List(SimpleStep(name))))
  }

  private def pred1(name: String, arg1: Term): Term = {
    Pred1(genGlobalPredName(name), arg1)
  }

  private def pred2(name: String, arg1: Term, arg2: Term): Term = {
    Pred2(genGlobalPredName(name), arg1, arg2)
  }

  private def and(term1: Term, term2: Term): Term = {
    termNot(termOr(termNot(term1), termNot(term2)))
  }

  private def imp(term1: Term, term2: Term): Term = {
    termOr(termNot(term1), term2)
  }

  private def forall(variableName: String, innerTerm: Term): OMA = {
    termForall(new LocalName(List(SimpleStep(variableName))), innerTerm)
  }

  private def exists(variableName: String, innerTerm: Term): Term = {
    termNot(forall(variableName, termNot(innerTerm)))
  }

  // FRAGMENT 1 - Simple Tableaux Calculus
  // ========================================

  it should "generate simple models" in new Machine {
    machine.feed(v("a"))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> true))

    machine.feed(v("b"))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> true, v("b") -> true))

    machine.feed(termNot(v("c")))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> true, v("b") -> true, v("c") -> false))
  }

  it should "switch models upon closing of branches" in new Machine {
    machine.feed(termOr(v("a"), v("b")))

    machine.feed(termNot(v("a")))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> false, v("b") -> true))

    machine.feed(termNot(v("b")))
    machine.nextModel() should be (None)
  }

  it should "retain fed inputs upon switching models" in new Machine {
    machine.feed(termOr(v("a"), v("b")))

    machine.feed(termNot(v("c")))
    machine.feed(termNot(v("a")))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> false, v("b") -> true, v("c") -> false))
  }

  it should "generate some deeply-branched models" in new Machine {
    machine.feed(termOr(v("a"), termOr(v("b"), termNot(v("c")))))
    machine.feed(termOr(v("d"), v("a")))

    machine.feed(v("c"))
    machine.feed(termNot(v("a")))
    machine.nextModel().get.getInterpretation should be (Map(v("a") -> false, v("b") -> true, v("c") -> true, v("d") -> true))
  }

  it should "work with binary predicates as in the course notes" in new Machine {
    // Cf. LBS lecture notes, slide 101, Example 5.3.6

    // (Peter loves Mary and Mary sleeps) or (Peter snores)
    val initialTerm = termOr(and(pred2("love", v("peter"), v("mary")), pred1("sleep", v("mary"))), pred1("snore", v("peter")))
    machine.feed(initialTerm)

    // Peter does not love Mary.
    machine.feed(termNot(pred2("love", v("peter"), v("mary"))))

    machine.nextModel().get.getInterpretation should be (Map(
      pred2("love", v("peter"), v("mary")) -> false,
      pred1("snore", v("peter")) -> true
    ))

    machine.feed(pred1("sleep", v("mary")))

    // No changes expected
    machine.nextModel().get.getInterpretation should be (Map(
      pred2("love", v("peter"), v("mary")) -> false,
      pred1("snore", v("peter")) -> true,
      pred1("sleep", v("mary")) -> true
    ))
  }

  it should "generate models with Pred1 and Pred2" in new Machine {
    machine.feed(pred1("like", v("dog")))
    machine.feed(pred2("kill", v("mouse"), v("something")))

    machine.nextModel().get.getInterpretation should be (Map(
      pred1("like", v("dog")) -> true,
      pred2("kill", v("mouse"), v("something")) -> true
    ))

    machine.feed(termEq(v("hammer"), v("something")))

    machine.nextModel().get.getInterpretation should be (Map(
      pred1("like", v("dog")) -> true,
      pred2("kill", v("mouse"), v("something")) -> true,
      pred2("kill", v("mouse"), v("hammer")) -> true
    ))
  }

  // FRAGMENT 1 - PL_NQ with equality (=)
  // ========================================

  it should "propagate one-level equalities with Pred1" in new Machine {
    machine.feed(termEq(v("a"), v("b")))
    machine.feed(pred1("like", v("b")))

    machine.nextModel().get.getInterpretation should be (Map(
      pred1("like", v("a")) -> true,
      pred1("like", v("b")) -> true
    ))

    machine.feed(termNot(pred1("like", v("a"))))

    machine.nextModel() should be(None)
  }

  it should "propagate one-level equalities with Pred2" in new Machine {
    // Cf. LBS lecture notes, slide 104

    // Mary is the teacher. Peter likes the teacher.
    machine.feed(termEq(v("mary"), v("the_teacher")))
    machine.feed(pred2("like", v("peter"), v("the_teacher")))

    // Check whether this entails: Peter likes Mary, i.e.
    // the negation must lead to a contradiction (on all branches).
    machine.feed(termNot(pred2("like", v("peter"), v("mary"))))

    machine.nextModel() should be (None)
  }

  it should "propagate two-level equalities with Pred2" in new Machine {
    // Cf. LBS lecture notes, slide 104

    // Mary is the teacher. Peter likes the teacher.
    machine.feed(termEq(v("mary"), v("the_teacher")))
    machine.feed(termEq(v("the_teacher"), v("the_mother")))
    machine.feed(pred2("like", v("peter"), v("the_mother")))

    // Check whether this entails: Peter likes Mary, i.e.
    // the negation must lead to a contradiction (on all branches).
    machine.feed(termNot(pred2("like", v("peter"), v("mary"))))

    machine.nextModel() should be (None)
  }

  it should "propagate deep-level equalities" in new Machine {
    // Cf. LBS lecture notes, slide 104

    // a = b, c = d, b = c
    // a = c as well
    machine.feed(termEq(v("a"), v("b")))
    machine.feed(termEq(v("c"), v("d")))
    machine.feed(termEq(v("b"), v("c")))

    machine.feed(termNot(termEq(v("a"), v("c"))))

    machine.nextModel() should be (None)
  }

  it should "propagate deep-level equalities with a big AND" in new Machine {
    // Cf. LBS lecture notes, slide 104

    // a = b, c = d, b = c
    // a = c as well
    val equations: List[Term] = List(
      ("a", "b"),
      ("c", "d"),
      ("b", "c"),

      ("e", "f"),
      ("g", "h"),
      ("g", "e")
    ).map(tuple => termEq(v(tuple._1), v(tuple._2)))
    machine.feed(equations.reduce((a, b) => and(a, b)))

    // The equivalence classes [a] = {a, b, c, d} and [e] = {e, f, g, h}
    // are distinct, thus leading to no contradiction.
    machine.feed(termNot(termEq(v("a"), v("e"))))

    machine.nextModel() should not be None
    machine.feed(termNot(termEq(v("a"), v("c"))))

    machine.nextModel() should be (None)
  }

  it should "propagate equalities across tree heights 1 (i.e. with multiple branches)" in new Machine {
    machine.feed(termEq(v("a"), v("b")))
    machine.feed(termEq(v("c"), v("d")))

    machine.feed(termOr(termEq(v("d"), v("a")), termEq(v("c"), v("b"))))
    machine.feed(termNot(termEq(v("c"), v("a"))))

    machine.nextModel() should be (None)
  }

  it should "propagate equalities across tree heights 2 (i.e. with multiple branches)" in new Machine {
    // Mary is the teacher. Peter likes the teacher.
    machine.feed(termEq(v("mary"), v("the_teacher")))
    machine.feed(termOr(
      termEq(v("the_teacher"), v("the_mother")),
      termEq(v("the_teacher"), v("the_sister"))
    ))
    machine.feed(termEq(v("the_writer"), v("the_mother")))

    // Peter likes the teacher. Peter does not like the (his) mother.
    // => The teacher is the (his) sister.
    machine.feed(pred2("like", v("peter"), v("the_teacher")))
    machine.feed(termNot(pred2("like", v("peter"), v("the_mother"))))

    machine.nextModel().get.getInterpretation should be (Map(
      pred2("like", v("peter"), v("the_mother")) -> false,
      pred2("like", v("peter"), v("the_writer")) -> false,

      pred2("like", v("peter"), v("the_sister")) -> true,
      pred2("like", v("peter"), v("the_teacher")) -> true,
      pred2("like", v("peter"), v("mary")) -> true
    ))
  }

  // FRAGMENT 2 - Free variables
  // ========================================
  ignore should "Free variables with world knowledge" in new Machine {
    // Mary is the teacher. Peter likes the teacher.
    machine.feed(termEq(v("mary"), v("the_teacher")))
    machine.feed(termOr(
      termEq(v("the_teacher"), v("the_mother")),
      termEq(v("the_teacher"), v("the_sister"))
    ))
    machine.feed(termEq(v("the_writer"), v("the_mother")))

    // Peter likes the teacher. Peter does not like the (his) mother.
    // => The teacher is the (his) sister.
    machine.feed(pred2("like", v("peter"), v("fido")))
    machine.feed(pred2("bite", v("x"), v("y")))

    machine.feed(pred1("dog", v("fido")))
    machine.feed(pred1("human", v("peter")))

    // No one bites himself.
    machine.feed(termNot(pred2("bite", v("x"), v("x"))))
    // Humans do not bite dogs.
    machine.feed(imp(and(pred1("dog", v("x")), pred1("human", v("y"))), termNot(pred2("bite", v("y"), v("x")))))

    machine.nextModel().get.getInterpretation should be (Map(
      pred1("dog", v("fido")) -> true,
      pred1("human", v("peter")) -> true,

      pred2("bite", v("fido"), v("peter")) -> true
    ))
  }

  // FRAGMENT 4 - Quantifiers
  // ========================================
  // https://mathhub.info/Teaching/LBS?LogicSyntax?ind
  it should "Forall quantifier 1" in new Machine {
    // Cf. LBS lecture notes, slide 149.

    // Peter is a man.
    machine.feed(pred1("man", c("peter")))

    // No man walks.
    machine.feed(termNot(
      exists(
        "x",
        and(pred1("man", c("x")), pred1("walk", c("x")))
      )
    ))

    machine.nextModel().get.getInterpretation should be (Map(
      pred1("man", c("peter")) -> true,
      pred1("walk", c("peter")) -> false
    ))
  }

  it should "Forall quantifier 2" in new Machine {
    // Cf. LBS lecture notes, slide 149.

    // Peter is a man.
    machine.feed(pred1("man", c("peter")))

    // All men are hungry or sleeping.
    machine.feed(forall("x", imp(pred1("man", c("x")), termOr(pred1("hungry", c("x")), pred1("sleep", c("x"))))))

    machine.feed(termNot(pred1("hungry", c("peter"))))

    machine.nextModel().get.getInterpretation should be (Map(
      pred1("man", c("peter")) -> true,
      pred1("sleep", c("peter")) -> true,
      pred1("hungry", c("peter")) -> false
    ))
  }

  /**
    * This test runs very long (> 2min at least).
    * Might stem from the combinatorial explosion.
    */
  ignore should "Multiple forall quantifiers" in new Machine {
    // Cf. LBS lecture notes, slide 149.

    // Peter is a man.
    machine.feed(pred1("man", c("peter")))

    // The teacher is a woman.
    machine.feed(pred1("woman", c("the_teacher")))

    // The sister = The teacher = Mary, who is a woman.
    machine.feed(termEq(c("the_sister"), c("the_teacher")))
    machine.feed(termEq(c("mary"), c("the_sister")))
    machine.feed(pred1("woman", c("mary")))

    // Every man likes very woman.
    machine.feed(
      forall("x",
        forall("y",
          imp(
            and(pred1("man", c("x")), pred1("woman", c("y"))),
            pred2("like", c("x"), c("y"))
          )
        )
      )
    )

    machine.feed(termNot(pred2("like", c("peter"), c("mary"))))

    machine.nextModel() should be (None)
  }

  it should "cope with nested forall quantifiers (prenex normal form)" in new Machine {
    // Cf. LBS lecture notes, slide 149.

    // Peter is a man.
    machine.feed(pred1("man", c("peter")))

    // Mary is a woman.
    machine.feed(pred1("woman", c("mary")))

    // Every man likes very woman.
    machine.feed(
      forall("x",
        forall("y",
          imp(
            and(pred1("man", c("x")), pred1("woman", c("y"))),
            pred2("like", c("x"), c("y"))
          )
        )
      )
    )

    machine.feed(termNot(pred2("like", c("peter"), c("mary"))))

    machine.nextModel() should be (None)
  }

  it should "cope with nested forall quantifiers (no prenex normal form)" in new Machine {
    // Cf. LBS lecture notes, slide 149.

    // Peter is a man.
    machine.feed(pred1("man", c("peter")))

    // Mary is a woman.
    machine.feed(pred1("woman", c("mary")))

    // Every man likes very woman.
    machine.feed(
      forall("x",
        imp(
          pred1("man", c("x")),
          forall("y",
            imp(
              pred1("woman", c("y")),
              pred2("like", c("x"), c("y"))
            )
          )
        )
      )
    )

    machine.feed(termNot(pred2("like", c("peter"), c("mary"))))

    machine.nextModel() should be (None)
  }
}

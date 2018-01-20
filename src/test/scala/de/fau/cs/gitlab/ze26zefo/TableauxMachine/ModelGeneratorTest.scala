package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.objects.{OMV, Term}
import info.kwarc.mmt.api.utils.URI
import org.scalatest._
import info.kwarc.gf.Convenience.{Pred1, Pred2, not => termNot, or => termOr, Eq => termEq}

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

  private def pred1(name: String, arg1: Term): Term = {
    Pred1(genGlobalPredName(name), arg1)
  }

  private def pred2(name: String, arg1: Term, arg2: Term): Term = {
    Pred2(genGlobalPredName(name), arg1, arg2)
  }

  private def and(term1: Term, term2: Term): Term = {
    termNot(termOr(termNot(term1), termNot(term2)))
  }

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
}

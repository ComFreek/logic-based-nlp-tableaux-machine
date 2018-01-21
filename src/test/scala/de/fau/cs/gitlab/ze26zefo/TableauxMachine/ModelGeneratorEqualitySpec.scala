package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.mmt.api.objects.Term
import info.kwarc.gf.Convenience.{Eq => termEq, not => termNot, or => termOr}

import scala.collection.Map

class ModelGeneratorEqualitySpec extends ModelGeneratorSpec {
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
}

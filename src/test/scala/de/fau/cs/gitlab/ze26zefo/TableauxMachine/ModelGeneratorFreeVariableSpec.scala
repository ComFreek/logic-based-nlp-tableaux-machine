package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.gf.Convenience.{Eq => termEq, not => termNot, or => termOr}

import scala.collection.Map

class ModelGeneratorFreeVariableSpec extends ModelGeneratorSpec {
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
}

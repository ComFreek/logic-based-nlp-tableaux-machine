package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.gf.Convenience.{Eq => termEq, not => termNot, or => termOr}
import org.scalatest.tagobjects.Slow

import scala.collection.Map

class ModelGeneratorQuantifierSpec extends ModelGeneratorSpec {
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
    * This test runs in about 30s.
    */
  it should "instantiate nested forall quantifiers" taggedAs Slow in new Machine {
    // Peter is a man.
    machine.feed(pred1("man", c("peter")))

    // The teacher is a woman.
    machine.feed(pred1("woman", c("the_teacher")))

    // The teacher = Mary, who is a woman.
    machine.feed(termEq(c("mary"), c("the_teacher")))
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

  /**
    * This test runs in about 60-70s.
    *
    * It is the same as "instantiate nested forall quantifiers" except that we do
    * not feed anymore that Mary is a woman. This has to be inferred from the fact
    * that the teacher (= Mary) is a woman.
    */
  it should "instantiate nested forall quantifiers and resolve equalities" taggedAs Slow in new Machine {
    // Peter is a man.
    machine.feed(pred1("man", c("peter")))

    // The teacher is a woman.
    machine.feed(pred1("woman", c("the_teacher")))

    // The teacher = Mary, who is a woman.
    machine.feed(termEq(c("mary"), c("the_teacher")))

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

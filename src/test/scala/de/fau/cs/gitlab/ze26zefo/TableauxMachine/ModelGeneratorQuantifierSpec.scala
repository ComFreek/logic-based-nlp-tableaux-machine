package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import info.kwarc.gf.Convenience.{Eq => termEq, not => termNot, or => termOr}

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

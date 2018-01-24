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

  it should "resolve existential quantifiers with collected individual constants" in new Machine {
    machine.feed(
      exists("x",
        and(
          pred1("man", c("x")),
          pred1("hungry", c("x"))
        )
      )
    )

    machine.feed(
      forall("x",
        imp(
          pred1("hungry", c("x")),
          termEq(c("peter"), c("x"))
        )
      )
    )

    machine.nextModel().get.getInterpretation should be (Map(
      pred1("man", c("peter")) -> true,
      pred1("hungry", c("peter")) -> true
    ))
  }

  it should "resolve nested existential quantifiers" in new Machine {
    // Cf. LBS lecture notes, slide 151
    // Mary is married to Jeff. Her husband is not in town.

    machine.feed(and(
      pred1("man", c("jeff")),
      termNot(pred1("man", c("mary")))
    ))

    machine.feed(pred2("married", c("mary"), c("jeff")))
    machine.feed(
      exists("x",
        exists("y",
          and(
            pred1("man", c("x")),
            termNot(pred1("man", c("y"))),
            pred2("hubby", c("x"), c("y")),
            termNot(pred1("intown", c("x")))
          )
        )
      )
    )

    machine.nextModel().get.getInterpretation should be (Map(
      pred1("man", c("jeff")) -> true,
      pred1("man", c("mary")) -> false,
      pred2("hubby", c("jeff"), c("mary")) -> true,
      pred1("intown", c("jeff")) -> false,
      pred2("married", c("mary"), c("jeff")) -> true
    ))
  }

  it should "resolve existential quantifiers with probing (variant 1)" in new Machine {
    machine.feed(pred1("man", c("jeff")))
    machine.feed(termNot(pred1("man", c("mary"))))
    machine.feed(termNot(pred1("man", c("lucy"))))

    machine.feed(
      exists("x",
        exists("y",
          and(
            pred2("married", c("x"), c("y")),
            pred1("man", c("x")),
            termNot(pred1("man", c("y"))),
            pred2("hubby", c("x"), c("y")),
            termNot(pred1("intown", c("x")))
          )
        )
      )
    )

    machine.feed(termNot(pred2("married", c("jeff"), c("lucy"))))

    (Map(
      pred1("man", c("jeff")) -> true,
      pred1("man", c("mary")) -> false,
      pred1("man", c("lucy")) -> false,

      pred2("hubby", c("jeff"), c("mary")) -> true,
      pred1("intown", c("jeff")) -> false,
      pred2("married", c("jeff"), c("mary")) -> true,
      pred2("married", c("jeff"), c("lucy")) -> false
    ).toSet subsetOf machine.nextModel().get.getInterpretation.toSet) should be (true)
  }

  it should "resolve existential quantifiers with probing (variant 2)" in new Machine {
    machine.feed(pred1("man", c("jeff")))
    machine.feed(termNot(pred1("man", c("mary"))))
    machine.feed(termNot(pred1("man", c("lucy"))))

    machine.feed(
      exists("x",
        exists("y",
          and(
            pred2("married", c("x"), c("y")),
            pred1("man", c("x")),
            termNot(pred1("man", c("y"))),
            pred2("hubby", c("x"), c("y")),
            termNot(pred1("intown", c("x")))
          )
        )
      )
    )

    machine.feed(termNot(pred2("married", c("jeff"), c("mary"))))

    (Map(
      pred1("man", c("jeff")) -> true,
      pred1("man", c("mary")) -> false,
      pred1("man", c("lucy")) -> false,

      pred2("hubby", c("jeff"), c("lucy")) -> true,
      pred1("intown", c("jeff")) -> false,
      pred2("married", c("jeff"), c("mary")) -> false,
      pred2("married", c("jeff"), c("lucy")) -> true
    ).toSet subsetOf machine.nextModel().get.getInterpretation.toSet) should be (true)
  }

  it should "close the branch with the existential quantifier when a fresh instantiation closed" in new Machine {
    machine.feed(termNot(pred1("man", c("lucy"))))
    machine.feed(exists("x", pred1("man", c("lucy"))))

    machine.nextModel() should be (None)
  }
}

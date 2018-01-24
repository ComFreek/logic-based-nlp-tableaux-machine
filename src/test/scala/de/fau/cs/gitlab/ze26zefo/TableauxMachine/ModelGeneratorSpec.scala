package de.fau.cs.gitlab.ze26zefo.TableauxMachine

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.utils.URI
import org.scalatest._
import info.kwarc.gf.Convenience.{Pred1, Pred2, forall => termForall, not => termNot, or => termOr}

/**
  * Common Spec functions and traits for suites testing the GraphTableauxMachine or
  * - more generally - a ModelGenerator.
  *
  * Especially, you can use the Machine trait specified herein to use a freshly
  * created ModelGenerator instance:
  *
  * <code>
  *   it should "your test name" in new Machine {
  *     machine.feed(/* ... */);
  *   }
  * </code>
  *
  * If TRACK_TEST_MODELS_LATEX is set, in each test upon a call of nextModel(), the
  * model is generated, intercepted and exported as a LaTeX file in the paths
  * given by TEST_MODELS_DIR and TEST_MODELS_LATEX_DIR. The LaTeX file name depends
  * on the test name.
  */
abstract class ModelGeneratorSpec extends FlatSpec with Matchers {

  private val TRACK_TEST_MODELS_LATEX = true
  private val TEST_MODELS_DIR = Paths.get("test-models-output")
  private val TEST_MODELS_LATEX_DIR = TEST_MODELS_DIR.resolve("latex")

  trait Machine {
    private val actualMachine: GraphTableauxMachine = new GraphTableauxMachine()
    private var nextModelCounter = 1

    val machine: ModelGenerator = if (TRACK_TEST_MODELS_LATEX) {
      new ModelGenerator {
        override def feed(term: Term): Unit = {
          actualMachine.feed(term)
        }

        override def nextModel(): Option[Model] = {
          val model = actualMachine.nextModel()

          // Escape for filename use
          val escapedTestName = _currentTestName.get().replaceAll("[^\\w ]+", "").replace(' ', '-')
          val latexFile = TEST_MODELS_LATEX_DIR.resolve(escapedTestName + "-" + nextModelCounter + ".tex")

          Files.write(
            latexFile,
            actualMachine.generateLatexDocument().getBytes(StandardCharsets.UTF_8)
          )

          nextModelCounter += 1
          model
        }
      }
    }
    else {
      actualMachine
    }
  }

  // Save the current test name to use in LaTeX export upon nextModel()
  //
  // Copied from https://stackoverflow.com/a/36766748
  // Author: Alexey Romanov <https://stackoverflow.com/users/9204/alexey-romanov>
  // License: CC BY-SA 3.0 with attribution required
  private val _currentTestName = new ThreadLocal[String]

  override def withFixture(test: NoArgTest): Outcome = {
    _currentTestName.set(test.name)
    val outcome = super.withFixture(test)
    _currentTestName.set(null)
    outcome
  }
  // End code for saving the current test name.

  // For debugging purposes
  protected def modelToString(model: Model): String = {
    val interpretation = model.getInterpretation
    interpretation.keys.map(term => {
      TermStringHelpers.termToString(term) + ": " + interpretation(term)
    }).mkString("\n")
  }

  protected def genGlobalPredName(name: String): GlobalName = {
    val mpath = MPath(DPath(URI.http colon "test"), new LocalName(List(SimpleStep("test"))))
    GlobalName(mpath, new LocalName(List(SimpleStep(name))))
  }

  protected def v(name: String): Term = {
    val term = new OMV(new LocalName(List(SimpleStep(name))))

    Pred1(genGlobalPredName(name), term)
  }

  protected def c(name: String): Term = {
    OMV(LocalName(List(SimpleStep(name))))
  }

  protected def pred1(name: String, arg1: Term): Term = {
    Pred1(genGlobalPredName(name), arg1)
  }

  protected def pred2(name: String, arg1: Term, arg2: Term): Term = {
    Pred2(genGlobalPredName(name), arg1, arg2)
  }

  private def and2(term1: Term, term2: Term): Term = {
    termNot(termOr(termNot(term1), termNot(term2)))
  }

  protected def and(terms: Term*): Term = {
    terms.reduce((term1, term2) => {
      and2(term1, term2)
    })
  }

  protected def imp(term1: Term, term2: Term): Term = {
    termOr(termNot(term1), term2)
  }

  protected def forall(variableName: String, innerTerm: Term): OMA = {
    termForall(new LocalName(List(SimpleStep(variableName))), innerTerm)
  }

  protected def exists(variableName: String, innerTerm: Term): Term = {
    termNot(forall(variableName, termNot(innerTerm)))
  }
}

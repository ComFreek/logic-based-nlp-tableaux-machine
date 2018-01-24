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
  * model is generated, intercepted and the current graph representation (assumes
  * GraphTableauxMachine) of the machine xported as a LaTeX file.
  * The file will be placed into
  * {TEST_MODELS_LATEX_DIR}/{suite name}/{test name}-{nextModel() count}.tex
  *
  * E.g. in a suite "ABC" and a test "DEF" you perform two nextModel() calls, then
  * {TEST_MODELS_LATEX_DIR}/ABC/DEF-{1,2}.tex will be generated.
  */
abstract class ModelGeneratorSpec extends FlatSpec with Matchers with BeforeAndAfterAll {

  private val TRACK_TEST_MODELS_LATEX = true
  private val TEST_MODELS_DIR = Paths.get("test-models-output")
  private val TEST_MODELS_LATEX_DIR = TEST_MODELS_DIR.resolve("latex")

  /**
    * Trait providing a ModelGenerator machine instance, which exports its graph after every
    * intercepted nextModel() call.
    * See ModelGeneratorSpec's class documentation for more details on the export path.
    */
  trait Machine {
    private val actualMachine: GraphTableauxMachine = new GraphTableauxMachine()

    /***
      * Count the number of nextModel() calls to form the filename upon the next call.
      */
    private var nextModelCounter = 0

    val machine: ModelGenerator = if (TRACK_TEST_MODELS_LATEX) {
      new ModelGenerator {
        override def feed(term: Term): Unit = {
          actualMachine.feed(term)
        }

        override def nextModel(): Option[Model] = {
          val model = actualMachine.nextModel()

          val escapedSuiteName = _currentSuiteName.get().replace("\\W+", "")
          val suiteDirectory = TEST_MODELS_LATEX_DIR.resolve(escapedSuiteName)

          suiteDirectory.toFile.mkdirs()

          val escapedTestName = _currentTestName.get().replaceAll("[^\\w ]+", "").replace(' ', '-')
          val latexFile = suiteDirectory.resolve(escapedTestName + "-" + (nextModelCounter + 1) + ".tex")

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

  private val _currentSuiteName = new ThreadLocal[String]

  override def beforeAll(): Unit = {
    super.beforeAll()
    _currentSuiteName.set(suiteName)
  }

  override def afterAll(): Unit = {
    super.afterAll()
    _currentSuiteName.set(null)
  }

    // Save the current test name to use in LaTeX export upon nextModel()
  //
  // Copied from https://stackoverflow.com/a/36766748
  // Author: Alexey Romanov <https://stackoverflow.com/users/9204/alexey-romanov>
  // License: CC BY-SA 3.0 with attribution required
  private val _currentTestName = new ThreadLocal[String]

  override def withFixture(test: NoArgTest): Outcome = {
    print(test.scopes)
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

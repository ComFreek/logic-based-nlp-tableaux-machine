# TableauxMachine

Theorem prover and model generator for [first-order logic](https://en.wikipedia.org/wiki/First-order_logic).

Implemented as an exercise for the course ["Logik-Basierte Sprachverarbeitung" (LBS)](https://kwarc.info/courses/lbs/) by [Michael Kohlhase](https://kwarc.info/people/mkohlhase)
at the [Friedrich-Alexander University Erlangen-Nuremberg](https://www.fau.eu/) in the winter
term 2017/2018.

Supported rules:

- `(a ∨ b)^T`
- `(a ∨ b)^F`
- `(a = b)^T` in conjunction with `ϕ = ψ`, of them containing `a` or `b`.
- (RM: ∀): `(∀x.ϕ)^T`
- (RM: ∃): `(∀x. ϕ)^F`
- (RM: ∃⊥): If (RM: ∃) has been applied with a fresh individual constant and that branch closes
  entirely, the column which branched because of (RM: ∃) is closed as well.

## Installation

1. Clone
2. If you are not using Windows: add the compiled GF `*.so` libraries in `lib/`.
3. Install [SBT](https://www.scala-sbt.org/) if you do not have it already installed. (Check `sbt` on the command line.)

## Usage

1. Run `sbt` in the root directory and then enter
   - `test` for all tests (might run several minutes)
   - `testOnly -- -l org.scalatest.tags.Slow` to exclude slow tests.

2. For every run test corresponding LaTeX files with the tableaux graph will be
created in the directory `test-models-output/latex`.

   You can use the LaTeX distribution of your choice, the generated code is supposed to
   be very portable. If you have `latexmk` at your fingertips, you can run `latexmk -pdf`
   in every suite subdirectory to automatically generate the PDFs.

   Note that due to the use of the specific LaTeX package for the visualizations,
   nodes with one child do not display their branch visually, they are simply
   concatenated. This might happen in conjunction with (RM: ∃).

## Documentation

Extensive documentation with a high-level overview of the inner workings can be found in [`GraphTableauxMachine.scala`](https://gitlab.cs.fau.de/ze26zefo/TableauxMachine/blob/master/src/main/scala/de/fau/cs/gitlab/ze26zefo/TableauxMachine/GraphTableauxMachine.scala).

## Developing tips

- Inside SBT, you can use `testOnly -- -z "xyz"` to only run the tests whose names contain "xyz".
- Looking at the generated graphs in `test-models-output/latex` is recommended to catch
  bugs when implementing new functionality.
- If tests are failing and manual comparisons between models (i.e. between Maps) is cumbersome, you can temporarily use the following code:

      println(modelToString(machine.nextModel().get))

- The test files and their classes must be suffixed with `*Spec`, otherwise `sbt test` might not run all of them.

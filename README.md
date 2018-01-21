# TableauxMachine

Implemented as an exercise for the course ["Logik-Basierte Sprachverarbeitung" (LBS)](https://kwarc.info/courses/lbs/).

## Usage

1. Clone
2. If you are not using Windows: add the compiled GF `*.so` libraries in `lib/`.
3. Install [SBT](https://www.scala-sbt.org/) if you do not have it already installed. (Check `sbt` on the command line.)
4. Run `sbt` in the root directory and then enter `test`.


## Developing

- Inside SBT, you can use `testOnly -- -z "xyz"` to only run the tests whose names contain "xyz".
- If tests are failing and manual comparisons between models (i.e. between Maps) is cumbersome, you can temporarily use the following code:

      println(modelToString(machine.nextModel().get))

- The test files and their classes must be suffixed with `*Spec`, otherwise `sbt test` might not run all of them.
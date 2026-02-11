# Naproche/ZF

Naproche/ZF is an experimental [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant)
based on [set theory](https://en.wikipedia.org/wiki/Set_theory) (and [classical logic](https://en.wikipedia.org/wiki/Classical_logic)).
It uses a [controlled language](https://en.wikipedia.org/wiki/Controlled_natural_language)
embedded into subset of LaTeX as input format, supporting [literate formalization](https://en.wikipedia.org/wiki/Literate_programming).


## Example

```latex
\begin{theorem}[Cantor]\label{cantor}
    There exists no surjection from $A$ to $\pow{A}$.
\end{theorem}
\begin{proof}
    Suppose not.
    Consider a surjection $f$ from $A$ to $\pow{A}$.
    Let $B = \{a \in A \mid a\notin f(a)\}$.
    Then $B\in\pow{A}$.
    Take an element $a'$ of $A$ such that $f(a') = B$ by \cref{surj}.
    Now $a' \in B$ iff $a' \notin f(a') = B$.
    Contradiction.
\end{proof}
```


## Development

### Prerequisites

We rely on automated theorem provers like
[Vampire](https://vprover.github.io/)
and
[E](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html)
to discharge proof tasks.

You may also need to install `zlib` on certain operating systems.
For example, on Ubuntu you can install the development version of
`zlib` by running `sudo apt install zlib1g-dev`.

#### Obtaining Vampire

The default prover is Vampire and the included library is written against a specific release of Vampire.
Currently the library uses [Vampire 5.0.0](https://github.com/vprover/vampire/releases/tag/v5.0.0).

If there are no binaries for your platform, you can install Vampire by compiling from source.
Download the source code release and follow the instructions in Vampire’s `README.md` and make sure that the resulting binary is available as `vampire` on your `$PATH` (running `vampire --version` should tell you the right version).
If you have multiple versions of Vampire installed, you can export the `$NAPROCHE_VAMPIRE` environment variable to choose a specific version,
e.g. by adding
```
export NAPROCHE_VAMPIRE="/absolute/path/to/vampire"
```
to your shell configuration.

#### Obtaining E

You can usually install a reasonably up-to-date version of E via your system’s package manager
(e.g. via `apt-get install eprover` on Ubuntu and `brew install eprover` on macOS).
Alternatively, you can build E [from source](https://github.com/eprover/eprover).
By default whichever `eprover` is on your `$PATH` will be used,
but you can override the default executable using the `NAPROCHE_EPROVER` environment variable.

### Building

This project uses [Stack](http://haskellstack.org/) to manage Haskell libraries and GHC.
You can install Stack and other Haskell tooling using [GHCup](https://www.haskell.org/ghcup/). Follow the GHCup install instructions and then use `ghcup tui` to install Stack.
Stack should install the correct GHC version when you first try to build the software. You can also use GHCup to install the Haskell Language Server, which enables IDE features in some text editors. For VS Code you also need to install the [Haskell extension](https://marketplace.visualstudio.com/items?itemName=haskell.haskell).

You can build the project using `stack build` in the root directory of this project.

Supported platforms are Linux x86-64 and macOS AArch64/x86-64.
Support for Windows is currently untested, but using [WSL2](https://learn.microsoft.com/en-us/windows/wsl/) may work.


### Checking individual files

After running `stack build` you can run the program with `stack exec zf -- <FILENAME>` in the root directory of this project.
The double hyphens `--` separate the arguments of `stack`
from the arguments of the proof checker. Here's an example invocation:

```
stack exec zf -- library/set.tex --log --uncached
```

For a list of all options run `stack exec zf -- --help`.


### Checking the entire standard library

Run `make lib` to check the file `library/everything.tex`.


### Compiling the PDF of the standard library

```
cd latex && xelatex stdlib.tex
```

### Setting up other formalization environments

When looking for imported files, the following list of base directories is considered (in descending priority):

- the current working directory `.`
- the directory `./library`, which you can override with the environment variable `NAPROCHE_LIB`


### Running the tests

There are a few [golden tests](https://hackage.haskell.org/package/tasty-golden-2.3.4/docs/Test-Tasty-Golden.html)
that compare the output of the program to previously accepted output.
You can run the tests with `stack test`, which will fail if the output differs from the existing golden files.
Run

```
make test
```

or, equivalently

```
stack test --test-arguments "--accept"
```

to update the golden files.


### Building Haskell documentation

Running `stack haddock` will build the project together with its documentation,
placing the rendered HTML files into `haddocks/`.


### Profiling

The following makes sure that stack uses a dedicated directory
to cache the profiled version of all dependencies. Otherwise
switching between profiled and unprofiled builds will cause
lots of recompilation.

```
stack --work-dir .stack-work-profile --profile build
```

Basic time profiling:

```
stack --work-dir .stack-work-profile exec --profile zf -- library/ordinal.tex --uncached +RTS -p
```

If you have [ghc-prof-flamegraph](https://hackage.haskell.org/package/ghc-prof-flamegraph) installed
(e.g. after running `cabal install ghc-prof-flamegraph`), you can generate an interactive `zf.prof.svg` from the `.prof` file
by running the following:

```
ghc-prof-flamegraph zf.prof
```


### Debugging

If verification fails, then the failed TPTP encoded task is dumped to stderr.
You can redirect that output to a file to experiment with it.

```
stack exec zf -- file-that-fails.tex 2> debug/fail.p
```

You can then run provers manually on that file.

```
eprover --auto --soft-cpu-limit=10  --memory-limit=5000 --silent --proof-object debug/fail.p

vampire --mode casc debug/fail.p
```

You can also dump all prover task by passing, e.g. `--dump ./dump` (the `.gitignore` is set up to ignore files in this specific directory).

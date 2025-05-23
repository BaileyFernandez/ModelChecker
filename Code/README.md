This package is built on the SMT solver [Z3](https://github.com/Z3Prover/z3) to provide a programmatic semantics for a range of hyperintensional operators along with a general purpose methodology for developing novel programmatic semantic theories and studying their logics.
You can find more information about the background theory [here](http://www.benbrastmckie.com/research#access).

## The Language of Thought

<!-- Intensional action is predicated on forethought and planning, where this applies to AI agents as much as it does to human agents. -->
<!-- Since strategic planning requires agents to contemplate nearby counterfactual possibilities, temporal eventualities, and causal and constitutive explanatory relationships, it is important to equip AI with the conceptual resources needed to think counterfactually, causally, modally, and temporally. -->
<!-- Whereas logic has traditionally focused on small language fragments, this project develops a unified semantics for a _Language of Thought_ (LoT) for AI agents to plan and reason with. -->
<!-- I am working to extend this list to include indicative conditionals, epistemic modals, and probability operators for reasoning under uncertainty as well as deontic modal and explanatory operators for aligning with other agents in navigating preferences and values. -->
<!---->
Rather than computing whether a given sentence is a logical consequence of some set of sentences by hand (typical in logic), these resources allow users to find countermodels or establish logical consequence up to a finite level complexity specified by the user.
This package integrates with formal methods to provide tooling for quickly finding hyperintensional countermodels and establish validity in a propositional language with the following operators:

  - `neg` for _negation_
  - `wedge` for _conjunction_
  - `vee` for _disjunction_
  - `rightarrow` for the _material conditional_
  - `leftrightarrow` for the _material biconditional_
  - `boxright` for the _must counterfactual conditional_
  - `diamondright` for the _might counterfactual conditional_
  - `Box` for _necessity_
  - `Diamond` for _possibility_
  - `Future` read 'it will always be the case that'
  - `future` read 'it will be the case that'
  - `Past` read 'it always has been the case that'
  - `past` read 'it has been the case that'
  - `leq` for _ground_ read 'sufficient for'
  - `sqsubseteq` for _essence_ read 'necessary for'
  - `equiv` for _propositional identity_ read 'just is for'
  - `preceq` for _relevance_

More specific details about the implementation of this hyperintensional semantics can be found [here](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/README.md).

## TheoryLib

The `model-checker` includes a growing library of semantic theories, each of which:

  - Introduces the primitives that make up a frame
  - Defines the propositions over a frame
  - Defines the models of the language by assigning sentence letters to propositions
  - Provides semantic clauses for the operators included in the language
  - Includes a range of examples of logical consequences and countermodels

Once the extension of a semantic theory has been adequately explored with adequate results, that theory can be included in the `TheoryLib`.

## Installation

### Basic Installation

For core functionality (command line interface and model checking):

```bash
pip install model-checker
```

This installs the essential `z3-solver` dependency needed for constraint solving.

### Optional Features

For Jupyter notebook integration with interactive visualizations:

```bash
pip install model-checker[jupyter]
```

For development tools (running tests):

```bash
pip install model-checker[dev]
```

For a complete installation with all features:

```bash
pip install model-checker[all]
```

More installation information can be found in the [accessible instructions](https://github.com/benbrastmckie/ModelChecker/blob/master/installation.md).

## Updating

Once installed, you can check the current version of the `model-checker` with:

```
model-checker -v
```

To update to the latest version, run:

```
model-checker -u
```

## Usage

Run `model-checker` in the terminal without arguments to create a new project with the following modules:

  - `semantic.py` specifies the Z3 primitives, frame constraints, models, theory of logical consequence, defined semantic terms, theory of propositions, and print instructions for displaying countermodels for the default semantics.
  - `operators.py` specifies the semantic clauses for the primitive operators included in the default language along with a number of defined operators.
  - `examples.py` specifies the settings, a collection of examples, and the protocol for finding and printing countermodels if there are any.

Alternatively, run `model-checker -l THEORY_NAME` to create a copy of the semantic theory with the name 'THEORY_NAME'.
The library of available semantic theories can be found [here](https://github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib).
Additional theories can be added by submitting a pull request.

After changing to the project directory that you created, run `model-checker project_examples.py` to find a countermodel if there is any.
The example settings specify the following inputs where the defaults are indicated below:

  - The number of atomic states to include in each model: `N = 3`.
  - An option to require all sentence letters to be contingent: `contingent = False`.
  - An option to require all sentence letters to have at least one verifier and at least one falsifier: `non_empty = False`.
  - An option to prevent sentence letters from having the null state as a verifier or a falsifier: `non_null = False`.
  - An option to prevent sentence letters from having overlapping verifiers or falsifiers: `disjoint = False`.
  - The maximum time in seconds to spend looking for a model: `max_time = 1`.

A number of general settings may also be specified with the following:

  - An option to print impossible states: `print_impssible = False`.
  - An option to print all Z3 constraints or unsatisfiable core constraints: `print_constraints = False`.
  - An option to print the Z3 model if there is any: `print_z3 = False`.
  - An option to prompt the user to append the output to the current file or to create a new file: `save_output = False`.

Examples are specified by defining a list as follows:
  ```
  # CF_CM_1: COUNTERFACTUAL ANTECEDENT STRENGTHENING

  CF_CM_1_premises = ['(A \\boxright C)']
  CF_CM_1_conclusions = ['((A \\wedge B) \\boxright C)']
  CF_CM_1_settings = {
      'N' : 3,
      'contingent' : True,
      'non_null' : True,
      'non_empty' : True,
      'disjoint' : False,
      'max_time' : 1,
  }

  CF_CM_1_example = [
      CF_CM_1_premises,
      CF_CM_1_conclusions,
      CF_CM_1_settings,
  ]
  ```
The example `CF_CM_1_example` includes:

  - A list of zero or more premises that are treated conjunctively: `premises = []`.
  - A list of zero or more conclusions that are treated disjunctively: `conclusions = []`.
  - A dictionary of settings where the defaults are indicated above.

Alternatively, users can define a general stock of `example_settings`, reusing these for an number of examples.
Users can override these settings from the command line by including the following flags:

  - Include `-c` to set `contingent = True`.
  - Include `-d` to set `disjoint = True`.
  - Include `-e` to set `non_empty = True`.
  - Include `-i` to set `print_impossibe = True`.
  - Include `-n` to set `non_null = True`.
  - Include `-p` to set `print_constraints = True`.
  - Include `-s` to set `save_bool = True`.
  - Include `-z` to set `print_z3 = True`.

Additional flags have been included in order to manage the package version:

  - Include `-h` to print help information about the package and its usage.
  - Include `-v` to print the installed version number.
  - Include `-u` to upgrade to the latest version.

## Jupyter Notebook Integration

ModelChecker can be used interactively in Jupyter notebooks, allowing for dynamic exploration of logical models with an interactive interface.

### Installation

To use ModelChecker in Jupyter notebooks, install with optional dependencies:

```bash
pip install ipywidgets matplotlib networkx
```

### Basic Usage

For quick formula checking, both LaTeX and some unicode characters are accepted:

```python
from model_checker.notebook import check_formula

# Check a counterfactual formula
check_formula("(A \\vee B \\boxright C) \\rightarrow (A \\boxright C)")

# Check a modal formula
check_formula("□(p → q) → (□p → □q)")

# Check with premises
check_formula("q", premises=["p", "p \\diamondright q"])
```

### Interactive Explorer

For interactive exploration with a UI:

```python
from model_checker.notebook import InteractiveModelExplorer

# Create and display the explorer
explorer = InteractiveModelExplorer()
explorer.display()
```

The interactive explorer provides:
- Formula input with syntax highlighting
- Theory selection and settings customization
- Multiple visualization options
- Ability to find alternative models

For a demonstration, see the `examples/jupyter_demo.ipynb` notebook and the `examples/README_jupyter.md` documentation.

<!-- ## Hyperintensional Semantics -->
<!---->
<!-- This section sketches the underlying semantics. -->
<!-- More information can be found in the GitHub [repository](https://github.com/benbrastmckie/ModelChecker).  -->
<!---->
<!-- The semantics is hyperintensional insofar as sentences are evaluated at _states_ which may be partial rather than total as in intensional semantic theories. -->
<!-- States are modeled by bitvectors of a specified length (e.g., `#b00101` has length `5`), where _state fusion_ is modeled by the bitwise OR operator `|`. -->
<!-- For instance, `#b00101 | #b11001 = #b11101`. -->
<!-- The _atomic states_ have exactly one occurrence of `1` and the _null state_ has no occurrences of `1`. -->
<!-- The space of states is finite and closed under fusion. -->
<!---->
<!-- States are named by lowercase letters in order to print readable countermodels. -->
<!-- Fusions are printed using `.` where `a.b` is the fusion of the states `a` and `b`. -->
<!-- A state `a` is _part_ of a state `b` just in case `a.b = b`. -->
<!-- States may be either _possible_ or _impossible_ where the null state is required to be possible and every part of a possible state is possible. -->
<!-- The states `a` and `b` are _compatible_ just in case `a.b` is possible. -->
<!-- A _world state_ is any state that is both possible and includes every compatible state as a part. -->
<!---->
<!-- Sentences are assigned _verifier states_ and _falsifier states_ where both the verifiers and falsifiers are required to be closed under fusion. -->
<!-- A sentence is _true at_ a world state `w` just in case `w` includes a verifier for that sentence as a part and _false at_ `w` just in case `w` includes a falsifier for that sentence as a part. -->
<!-- In order to ensure that sentence letters have at most one truth-value at each world state, a fusion `a.b` is required to be impossible whenever `a` is verifier for a sentence letter `A` and `b` is a falsifier for `A`. -->
<!-- Additionally, sentence letters are guaranteed to have at least one truth-value at each world state by requiring every possible state to be compatible with either a verifier or falsifier for any sentence letter. -->
<!---->
<!-- A _negated sentence_ is verified by the falsifiers for the sentence negated and falsified by the verifiers for the sentence negated. -->
<!-- A _conjunctive sentence_ is verified by the pairwise fusions of verifiers for the conjuncts and falsified by falsifiers for either of the conjuncts or fusions thereof. -->
<!-- A _disjunctive sentence_ is verified by the verifiers for either disjunct or fusions thereof and falsified by pairwise fusions of falsifiers for the disjuncts. -->
<!-- Conjunction and disjunction are dual operators obeying the standard idempotence and De Morgan laws. -->
<!-- The absorption laws do not hold, nor does conjunction distribute over disjunction, nor _vice versa_. -->
<!-- For a defense of the background theory of hyperintensional propositions, see this [paper](https://link.springer.com/article/10.1007/s10992-021-09612-w). -->
<!---->
<!-- A _necessity sentence_ `Box A` is true at a world just in case every world state includes a part that verifies `A` and a _possibility sentence_ `Diamond A` is true at a world just in case some world state includes a part that verifies `A`. -->
<!-- Given a world state `w` and state `s`, an `s`_-alternative_ to `w` is any world state to include as parts both `s` and a maximal part of `w` that is compatible with `s`. -->
<!-- A _must counterfactual conditional sentences_ `A boxright B` is true at a world state `w` just in case its consequent is true at any `s`-alternative to `w` for any verifier `s` for the antecedent of the counterfactual. -->
<!-- A _might counterfactual conditional sentences_ `A boxright B` is true at a world state `w` just in case its consequent is true at some `s`-alternative to `w` for some verifier `s` for the antecedent of the counterfactual. -->
<!-- The semantic theory for counterfactual conditionals is motivated and further elaborated in this accompanying [paper](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf). -->
<!-- This account builds on [Fine 2012](https://www.pdcnet.org/jphil/content/jphil_2012_0109_0003_0221_0246) and [Fine2012a](https://link.springer.com/article/10.1007/s11229-012-0094-y?error=cookies_not_supported&code=5166a4da-1834-438c-9f93-75b61f58b6db). -->
<!---->
<!-- A _grounding sentence_ `A leq B` may be read '`A` is _sufficient for_ `B`' and an _essence sentence_ `A sqsubseteq B` may be read '`A` is _necessary for_ `B`'. -->
<!-- A _propositional identity sentence_ `A equiv B` may be read '`A` _just is for_ `B`'. -->
<!-- A _relevance sentence_ `A preceq B` may be read '`A` _is wholly relevant to_ `B`'. -->
<!-- The semantics for ground requires every verifier for the antecedent to be a verifier for the consequent, any fusion of a falsifier for the antecedent and consequent to be a falsifier for the consequent, and any falsifier for the consequent to have a part that falsifies the antecedent. -->
<!-- The semantics for essence requires every fusion of a verifier for the antecedent and consequent to be a verifier for the consequent, any verifier for the consequent must have a part that verifies the antecedent, and every falsifier for the antecedent to be a falsifier for the consequent. -->
<!-- The semantics for propositional identity requires the two arguments to have the same verifiers and falsifiers. -->
<!-- The semantics for relevance requires any fusion of verifiers for the antecedent and consequent to be a verifier for the consequent and, similarly, any fusion of falsifiers for the antecedent and consequent to be a falsifier for the consequent. -->
<!-- Whereas the first three constitutive operators are interdefinable, relevance is definable in terms of the other constitutive operators but not _vice versa_: -->
<!---->
<!-- - `A leq B  :=  neg A sqsubseteq neg B  :=  (A vee B) equiv B`. -->
<!-- - `A sqsubseteq B  :=  neg A leq neg B  :=  (A wedge B) equiv B`. -->
<!-- - `A equiv B  :=  (A leq B) wedge (B leq A)  :=  (A sqsubseteq B) wedge (B sqsubseteq A)`. -->
<!-- - `A preceq B  :=  (A wedge B) leq B :=  (A vee B) sqsubseteq B`. -->
<!---->
<!-- Instead of a Boolean lattice as in extensional and intensional semantics theories, the space of hyperintensional propositions forms a non-interlaced bilattice as described in this [paper](https://link.springer.com/article/10.1007/s10992-021-09612-w), building on [Fine 2017](https://link.springer.com/article/10.1007/s10992-016-9413-y). -->
<!---->
<!-- More information can be found in the GitHub [repository](https://github.com/benbrastmckie/ModelChecker) as well as in this recent [manuscript](https://github.com/benbrastmckie/ModelChecker/blob/master/Counterfactuals.pdf).  -->


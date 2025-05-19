# Linear Temporal Logic Implementation

## Table of Contents

- [Overview](#overview)
  - [Package Contents](#package-contents)
- [Basic Usage](#basic-usage)
  - [Settings](#settings)
  - [Example Structure](#example-structure)
  - [Running Examples](#running-examples)
    - [1. From the Command Line](#1-from-the-command-line)
    - [2. In VSCodium/VSCode](#2-in-vscodiumvscode)
    - [3. In Development Mode](#3-in-development-mode)
    - [4. Using the API](#4-using-the-api)
  - [Theory Configuration](#theory-configuration)
- [Key Classes](#key-classes)
  - [BimodalSemantics](#bimodalsemantics)
  - [BimodalProposition](#bimodalpropositon)
  - [BimodalStructure](#bimodalstructure)
- [Bimodal Language](#bimodal-language)
  - [Necessity Operator](#necessity-operator-box)
  - [Future Operator](#future-operator-future)
  - [Past Operator](#past-operator-past)
- [Important Theorems](#important-theorems)
- [Implementation Details](#implementation-details)
  - [World and Time Representation](#world-and-time-representation)
  - [Time-Shift Relations](#time-shift-relations)
  - [Model Extraction Process](#model-extraction-process)
- [Frame Constraints](#frame-constraints)
- [Known Limitations](#known-limitations)
- [References](#references)

## Overview

The LTL-theory implements a semantics for a logic called Linear Temporal Logic, henceforth LTL. 

LTL was originally developed by the Israeli logician Amir Pneuli (1977). It was inspired by work by Arthur prior 
and Saul Kripke on their temporal and modal logics respectively. While those logics are now most well known by philosophers, LTL by contrast became important within the literature on formal methods in computer science. 

In particular, LTL is most widely used today in the procedures for formal verification and model checking. Developing a model checker that checks the validity of formulas in LTL, then, has special significance in the 
project of developing model checkers for non-standard modal logics. 

LTL-formulas are typically verified or falsified by Buchi-Automata. 

There are existing model checkers for LTL. SPOT is probably the most useful program with which to consider them. 

In addition to the standard connectives found in propositional logic, LTL implements a semantics for the following operators:

1. **Always/Eventually**: These operators are represetend by \\Box and \\Diamond respectively. The former donates that for all times in the future, the formula operated over holds. \\Diamond, by contrast, holds that for some time in the future, the formula operated over holds. Philosophical logicains will recognize the symbols and their meaning as similar to the \Box and \Diamond operators representing necessitiy and possibility in classical modal logic. Indeed, it is possible to thikn of the states in LTL as a restricted class of possible worlds whose connections are only left linear and transitive, or which can be converted to such an arrangement. 
2. **Next**: The \\Next Operator establishes that some formula will be true at the next time stage. 
3. **Until**: The \\Until operator takes two arguments occuring at two different times, and evaluates both formulae as well as the time interval between them. The semantics demand that 

This implementation provides a framework to study LTL where:

--A program is an sequence of times represetned by an ordered list of integers. These times correspond to states in a finite state machine. 
--Each time is an instantaneous configuration of the system 
--It is assumed that each time transitions to the next time 
--Sentence letters are assigned truth values at times
--the evaluation time is always zero 
--Metric tense operators next and until. 

### Package Contents

This package includes the following core modules:

- `semantic.py`: Defines the core semantics and model structure for LTL 
- `operators.py`: Implements all primitive and derived logical operators
- `examples.py`: Contains example formulas for testing and demonstration
- `__init__.py`: Exposes package definitions for external use

## Key Classes

### LTLSemantics

The `LTLSemantics` class defines the semantic models for the language, including:

- **Times**: An ordered list of integers defining times extending from the evaluation point
- **Truth conditions**: How to evaluate atomic propositions at times

The semantics is independent of the operators defined over the semantics.
This modular design makes it easy to compare semantic theories for the same operators as well as to compare operators for the same semantics.

### LTLProposition

The `LTLProposition` class handles the interpretation and representation of sentences over a model.
This includes:

- **Extension calculation**: Computing truth/falsity across  times
- **Truth evaluation**: Checking truth values at specific times
- **Proposition display**: Visualizing propositions in the model

Although sentence letters may be evaluated at the eval point on their own, tense operators can only be evaluated when considering the temporal structure. 

### LTLStructure

The `LTLStructure` class manages the model structure extracted from a Z3 model:

- **Time intervals**: Valid intervals for each time
- **Visualization**: Methods to display the resulting model structure

## Basic Usage

The LTL theory provides a framework which extends propositional logic with metric tense operators. This section explains how to use the theory's main components and run examples.

### Settings

The LTL theory supports the following configurable settings:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    # Number of times
    'M': 2,
    # Whether sentence_letters are assigned to contingent propositions
    'contingent': False,
    # Whether sentence_letters are assigned to distinct world_states
    'disjoint': False,
    # Maximum time Z3 is permitted to look for a model
    'max_time': 1,
    # Whether a model is expected or not (used for unit testing)
    'expectation': True,
}

# LTL-specific general settings that affect display format
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False, 
    "save_output": False,
    "maximize": False,
    "align_vertically": True,  # LTL-specific setting for timeline visualization
}
```

LTL theory defines two unique settings derived from Benjamin Brast McKie's implementation of the bimodal theory:

1. **M**: Controls the number of time points in the temporal dimension. Higher values allow for evaluating truth values over more complex formulas but increase computational complexity.

2. **align_vertically**: When set to `True`, displays world histories with time flowing vertically (top to bottom) which is often easier to read for bimodal models. When set to `False`, displays world histories horizontally.

### Example Structure

Each example is structured as a list containing three elements:

```python
[premises, conclusions, settings]
```

Where:
- `premises`: List of formulas that must be true in the model
- `conclusions`: List of formulas to check (invalid if all premises are true and at least one conclusion is false)
- `settings`: Dictionary of settings for this example

Here's a complete example definition:

The LTL theory supports the following configurable settings:

```python
DEFAULT_EXAMPLE_SETTINGS = {
    # Number of times
    'M': 2,
    # Whether sentence_letters are assigned to contingent propositions
    'contingent': False,
    # Whether sentence_letters are assigned to distinct world_states
    'disjoint': False,
    # Maximum time Z3 is permitted to look for a model
    'max_time': 1,
    # Whether a model is expected or not (used for unit testing)
    'expectation': True,
}

# LTL-specific general settings that affect display format
DEFAULT_GENERAL_SETTINGS = {
    "print_impossible": False,
    "print_constraints": False,
    "print_z3": False, 
    "save_output": False,
    "maximize": False,
    "align_vertically": True,  # LTL-specific setting for timeline visualization
}

```

### Running Examples

You can run examples in several ways:

#### 1. From the Command Line

```bash
# Run the default example from examples.py
model-checker path/to/examples.py

# Run with constraints printed 
model-checker -p path/to/examples.py

# Run with Z3 output
model-checker -z path/to/examples.py

# Force vertical alignment for display (bimodal-specific)
model-checker -a path/to/examples.py
```

#### 2. In VSCodium/VSCode

1. Open the `examples.py` file in VSCodium/VSCode
2. Use one of these methods:
   - Click the "Run Python File" play button in the top-right corner
   - Right-click in the editor and select "Run Python File in Terminal"
   - Use keyboard shortcut (Shift+Enter) to run selected lines

#### 3. In Development Mode

For development purposes, you can use the `dev_cli.py` script from the project root directory:

```bash
# Run the examples file
./dev_cli.py path/to/examples.py

# Run with constraints printed
./dev_cli.py -p path/to/examples.py

# Run with Z3 output and constraints printed (combined flags)
./dev_cli.py -z path/to/examples.py

# Run with vertical alignment (bimodal-specific)
./dev_cli.py -a path/to/examples.py
```

#### 4. Using the API

LTL exposes a clean API:

```python
from model_checker.theory_lib.LTL import (
    LTLSemantics, LTLProposition, LTLStructure, LTL_operators
)
from model_checker import ModelConstraints
from model_checker.theory_lib import get_examples

# Get examples
examples = get_examples('bimodal')
example_data = examples['BM_CM_1']
premises, conclusions, settings = example_data

# Create semantic structure
semantics = LTLSemantics(settings)
model_constraints = ModelConstraints(semantics, LTL_operators)
model = LTLStructure(model_constraints, settings)

# Check a formula
prop = LTLProposition("\\Box A", model)
is_true = prop.truth_value_at(model.main_time)
```

### Theory Configuration

LTL is defined by combining several components:

```python
LTL_theory = {
    "semantics": LTLSemantics,
    "proposition": LTLProposition,
    "model": LTLStructure,
    "operators": LTL_operators,
}

# Define which theories to use when running examples
semantic_theories = {
    "Brast-McKie" : LTL_theory,
    # additional theories will require translation dictionaries
}
```

#### Countermodel Example

Examples that are expected to have countermodels may be presented as follows:

```python
#Countermodel showing that Next A does not imply A Until B 
LTL_CM_1_premises=['\\Next A']
LTL_CM_1_conclusions=['A \\Until B']
LTL_CM_1_settings=
    'M': 3, 
    'contingent': False, 
    'disjoint': False, 
    'max_time': 5 
    'expectation': True, #Expects to find a countermodel 


**LTL_CM_1:** Shows that "Next A → A Until B" is not valid (has a countermodel).

#### Theorem Example

Examples that are not expected to have countermodels may be presented as follows:

'''python'''

# Theorem showing that Next A implies Eventually A 
LTL_TH_1_premises = ['\\Next A']
LTL_TH_1_conclusions = ['\\Eventually A']
LTL_TH_1_settings = {
    'M': 2,
    'contingent': False,
    'disjoint': False,
    'max_time': 5,
    'expectation': False,  # Expects NOT to find a countermodel
}
LTL_TH_1_example = [
    LTL_TH_1_premises,
    LTL_TH_1_conclusions,
    LTL_TH_1_settings,
]
```

**LTL_TH_1:** Shows that "Next A → Eventually A" is valid (no countermodel exists).

### Testing

The examples are then collected into dictionaries with `name_string : example` entries:

```python
example_range = {
    # Selected examples for current use
    "LTL_CM_2": LTL_CM_2_example,
    "LTL_TH_1": LTL_TH_1_example,
}
```

The `semantic_theories` are then used to evaluate the examples in the `example_range` given the `general_settings`.
It is typical to include many examples, most of which are commented out in order to focus on particular cases.

An optional `test_example_range` may be provided for automating testing when developing semantic theories:

```python
test_example_range = {
    # All examples for testing
    "LTL_CM_1": LTL_CM_1_example,
    "LTL_TH_1": LTL_TH_1_example,
    # ... more examples
}
```

See the [README.md](test/README.md) in the `test/` directory for further details on setting up unit testing.py` is run.

## LTL Language

> [NOTE] The code blocks included below are abridged for readability.
> Consult the `operators.py` for the complete implementation of the semantic clauses for the language.

Formal languages implemented in the `model-checker` must conform to the following specifications:

- Operators are designated with a double backslash as in `\\Always` and `\\Next`.
- Sentence letters are alpha-numeric strings as in `A`, `B_2`, `Mary_sings`, etc., using underscore `_` for spaces.
- Parentheses must be included around sentences whose main connective is a binary operator.
- Parentheses must NOT be included around sentences whose main connective is a unary operator.

### Always Operator (`\Always`)

The Always operator (`\Always`) evaluates whether a formula holds across all possible times after the evaluation
point. 

The operator implements 'It is always the case that' which takes one sentence as an argument. 
The operatore evalues whether its argument is true at all evaluation times. 

Note that in LTL, \\Always is typically represented with the Box symbol. However, out of concern that this notation may be confusing to users coming from  philosophy and linguistics backgrounds as well as to be consistent 
with the notation for the bimodal logic, I have opted to use \\Always to represent this operator. 

**Key Properties:**

- Evaluates truth across all times 
- Returns true only if the argument is true in ALL times
- Returns false if there exists ANY time where the argument is false

#### Truth Condition

`\\Always A` is true at `eval_time` if and only if `A` is true at all times considered.

```python
def true_at(self, argument,eval_time):
    return z3.ForAll(
        time,
        z3.Implies(
                semantics.is_valid_time_for_world(eval_world, time),
            ),
            semantics.true_at(argument, eval_world, time)
        )
```

#### Falsity Condition

`\\Always A` is false at `eval_time` if and only if `A` is false at some time in  `eval_time`.

### Eventually Operator (`\Eventually`)

The  operator (`\Eventually`) evaluates whether a formula holds at some future time in a world history. 

This operator implements 'It will eventually be the case that' which takes one sentence as an argument.
This operator is defined in light of the always operator, i.e. it holds whenever \\neg(\\Always\\neg 'A') holds. 

Note that in LTL, \\Eventually is typically represented with the Diamond symbol. However, out of concern that this notation may be confusing to users coming from  philosophy and linguistics backgrounds as well as to be consistent 
with the notation for the bimodal logic, I have opted to use \\Eventually to represent this operator.



**Key Properties:**

- Evaluates truth across all times
- Returns true only if the argument is true at SOME future time
- Returns false if for ALL future timmes the argument is false. 

#### Truth Condition

`\Eventually A' is true at a time 't' if and only if it is not the case that '\Always \Neg A' is true at time 't.'

#### Falsity Condition

`\Eventually A' is false at time 't' if and only if it is the case that '\Always \Neg A' is true at time 't.' 

### Next Operator (`\Next`)

The next operator `\Next A` relies on the discrete nature of time in our implementation. It states for any formula 'A' at any time of evaluation, the formula 'A' is true at the time of evaluation +1. 

The operator implements 'next it will be the case that' which takes one sentence as an argument. 

**Key Properties:**

- Evaluates truth across all times
- Returns true only if the argument is true at the time of evaluation +1 
- Returns false if the argument is false at the time of evaluation +1. 

#### Truth Condition

`\Next A` is true at time `t` if and only if A is true at the time 't+1.'

```python
 def true_at(self, argument, eval_time):
        """Returns true if argument is true at the time of evaluation plus one. 
        
        Args:
            argument: The argument to apply the next operator to
            eval_world: The world ID for evaluation context
            eval_time: The time for evaluation context
        """
        semantics = self.semantics
        
        # Extract world and time from eval_point
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]

        #define "next time" variable
        next_time = eval_time + 1

        return z3.And(
                
            #Time is within the valid range for this world's interval
            semantics.is_valid_time_for_world(next_time),

            #Formula is true at next time in world 
            semantics.true_at(argument, next_time)
            )
```

#### Falsity Condition

`\Next A' is false at time t if and only if A is false at 't+1.'

### Until Operator (`\Until`)

The until operator 'A \Until B' relies on the discrete nature of time in our implementation. It states that for any two formulas 'A' and 'B', if A is true at some time t, and B is true at some time t', then for all t'' such that t<t''<t' , 'A' is true at t''

The operator implemenets 'A will be the case until B' which takes two sentences as arguments. 


**Key Properties:**

- Evaluates truth across a time interval defined by the left and right arguments 
--Returns true if and only if for some time t and some other time t', 'A' is true at t, 'B' is true at t', and 
for all times t'' such that t<t''<t', 'A' is true at t''. 
--Returns true (vacuously) if there is no time t where A is true or no time t' where B is true. 
- Returns false if 'A' is false at some time t'' as defined above. 

#### Truth Condition

`A \Until B` is true at time `t` if and only if A is true at 't,' 'B' is true at some time t' such that t<t', and for all times t'' such that t<t''>t', A is true at t''. 

```python
 def true_at(self, leftarg, rightarg, eval_point):
        
        """
        Returns true if the left argument is true at all times from eval_time up to (but not including) the time
        when the right argument becomes true. The right argument must eventually be true.
        """
        semantics = self.semantics
        
        eval_time = eval_point["time"]
        
        some_time = z3.Int('some_time')
        t = z3.Int('t')
        
        return z3.Exists(
            some_time,

            z3.And(
                semantics.is_valid_time_for_world(some_time),
                eval_time < some_time,
                semantics.true_at(rightarg, some_point),

            z3.ForAll(
                t,
                z3.Implies(
                    z3.And(
                        semantics.is_valid_time_for_world(t),
                        eval_time <= t,
                        t < some_time
                    ),
                    semantics.true_at(leftarg, mid_point)
                )
            )
        )
    )
```

#### Falsity Condition

'''python
    def false_at(self, leftarg, rightarg, eval_point):
        """Returns true if argument is false at at least one future time in this world's interval.
        
        Args:
            argument: The argument to apply the future operator to
            eval_point: Dictionary containing evaluation parameters:
                - "world": The world ID for evaluation context
                - "time": The time for evaluation context
        """

        """Returns true if argument is true at all future times in this world's interval."""
        semantics = self.semantics
        
        eval_world = eval_point["world"]
        eval_time = eval_point["time"]
        
        some_time = z3.Int('some_time')
        t = z3.Int('t')
        
        some_point = {"world": eval_world, "time": some_time}
        mid_point = {"world": eval_world, "time": t}
        
        # If there exists a future time where rightarg is true, but some point between now and that time where leftarg is false
        return z3.Exists(
            some_time,
            z3.And(
                semantics.is_valid_time_for_world(some_time),
                eval_time < some_time,
                semantics.true_at(rightarg, some_point),
            z3.Exists(
                t,
                z3.And(
                    semantics.is_valid_time_for_world(t),
                    eval_time <= t,
                    t < some_time,
                    semantics.false_at(leftarg, mid_point)
                )
            )
        )
    )
'''

## Important Theorems

To be expanded later 

## Implementation Details

### Time Representation

The LTL implementation uses these key representations:

- **Time points**: Integers allowing zero and positive values (no negative values)
- **Time intervals**: There is a valid time interval always defined 
- **Evaluation point**: Fixed at time 0

The semantic model defines several Z3 sorts used throughout the implementation:

```python
# Define the Z3 sort used in the LTL model 
self.TimeSort = z3.IntSort()                 # Time points as integers
```

### Time-Shift Relations

Each world has a valid time interval defined by two functions:

```python
# Define interval tracking functions
self.time_interval_start = z3.Function(
    'time_interval_start',
    self.TimeSort      # Start time of interval
)

self.time_interval_end = z3.Function(
    'time_interval_end',
    self.TimeSort      # End time of interval
)
```
Time intervals are required to be convex (no gaps) and are generated within the range [-M+1, M-1]:

```python
def generate_time_intervals(self, M):
    """Generate all valid time intervals of length M that include time 0."""
    intervals = []
    for start in range(-M+1, 1):  # Start points from -M+1 to 0
        end = start + M - 1       # Each interval has exactly M time points
        intervals.append((start, end))
    return intervals
```

## Frame Constraints

LTL is defined by the following key frame constraints that determine the structure of models, as implemented in `build_frame_constraints()`:

### 1. Valid Time Constraint

Every model must have a valid evaluation time (designated as time 0).

```python
valid_main_time = self.is_valid_time(self.main_time)
```

### 2. Classical Truth Constraint

Each atomic sentence must have a consistent classical truth value at each world state.

```python
classical_truth = z3.ForAll(
    [time, sentence_letter],
    z3.Or(
        # Either sentence_letter is true at that time
        self.truth_condition(time, sentence_letter),
        # Or not
        z3.Not(self.truth_condition(time, sentence_letter))
    )
)
```
### 4. World Enumeration Constraint

World histories must be enumerated in sequence starting from 0.

```python
enumeration_constraint = z3.ForAll(
    [enumerate_world],
    z3.Implies(
        # If enumerate_world is a world
        self.is_world(enumerate_world),
        # Then it's non-negative
        enumerate_world >= 0,
    )
)
```

### 5. Convex World Ordering Constraint

There can be no gaps in the enumeration of worlds, ensuring worlds are created in sequence.

```python
convex_world_ordering = z3.ForAll(
    [convex_world],
    z3.Implies(
        # If both:
        z3.And(
            # The convex_world is a world
            self.is_world(convex_world),
            # And greater than 0
            convex_world > 0,
        ),
        # Then world_id - 1 must be valid
        self.is_world(convex_world - 1)
    )
)
```

### 6. Lawful Transition Constraint

Each world history must follow lawful transitions between consecutive states.

```python
lawful = z3.ForAll(
    [lawful_world, lawful_time],
    # If for any lawful_world and lawful time
    z3.Implies(
        z3.And(
            # The lawful_world is a valid world
            self.is_world(lawful_world),
            # The lawful_time is in (-M - 1, M - 1), so has a successor
            self.is_valid_time(lawful_time, -1),
            # The lawful_time is in the lawful_world
            self.is_valid_time_for_world(lawful_world, lawful_time),
            # The successor of the lawful_time is in the lawful_world
            self.is_valid_time_for_world(lawful_world, lawful_time + 1),
        ),
        # Then there is a task
        self.task(
            # From the lawful_world at the lawful_time
            z3.Select(self.world_function(lawful_world), lawful_time),
            # To the lawful_world at the successor of the lawful_time
            z3.Select(self.world_function(lawful_world), lawful_time + 1)
        )
    )
)
```

### 8. Skolem Abundance Constraint

An optimized version of the abundance constraint using Skolem functions to eliminate nested quantifiers, improving Z3 performance.

```python
# Define Skolem functions that directly compute the necessary worlds
forward_of = z3.Function('forward_of', self.WorldIdSort, self.WorldIdSort)
backward_of = z3.Function('backward_of', self.WorldIdSort, self.WorldIdSort)

# Use Skolem functions instead of existential quantifiers
return z3.ForAll(
    [source_world],
    z3.Implies(
        # If the source_world is a valid world
        self.is_world(source_world),
        # Then both:
        z3.And(
            # Forwards condition - if source can shift forward
            z3.Implies(
                self.can_shift_forward(source_world),
                z3.And(
                    # The forward_of function must produce a valid world
                    self.is_world(forward_of(source_world)),
                    # The produced world must be properly shifted
                    self.is_shifted_by(source_world, 1, forward_of(source_world))
                )
            ),
            # Backwards condition - if source can shift backwards
            z3.Implies(
                self.can_shift_backward(source_world),
                z3.And(
                    # The backward_of function must produce a valid world
                    self.is_world(backward_of(source_world)),
                    # The produced world must be properly shifted
                    self.is_shifted_by(source_world, -1, backward_of(source_world))
                )
            )
        )
    )
)
```



### 9. Time Interval Constraint

An optimized version of the world interval constraint that directly defines interval bounds for each world.

```python
# Generate valid time intervals
time_intervals = self.generate_time_intervals(self.M)

# Create direct mapping for interval bounds
interval_constraints = []

# For each valid world ID, create direct interval constraints
for world_id in range(self.max_world_id):
    # A world must have exactly one of the valid intervals if it exists
    world_constraint = z3.Implies(
        self.is_world(world_id),
        z3.Or(*world_interval_options)
    )

    interval_constraints.append(world_constraint)

# Combine all world constraints
return z3.And(*interval_constraints)
```

### Additional Optional Constraints

The semantic model also defines several optional constraints that can be enabled as needed:

#### Task Restriction Constraint

Ensures the task relation only holds between states in lawful world histories.

```python
task_restriction = z3.ForAll(
    [some_state, next_state],
    z3.Implies(
        # If there is a task from some_state to next_state
        self.task(some_state, next_state),
        # Then for some task_world at time_shifted:
        z3.Exists(
            [task_world, time_shifted],
            z3.And(
                # The task_world is a valid world
                self.is_world(task_world),
                # The successor or time_shifted is a valid time
                self.is_valid_time(time_shifted, -1),
                # Where time_shifted is a time in the task_world,
                self.is_valid_time_for_world(task_world, time_shifted),
                # The successor of time_shifted is a time in the task_world
                self.is_valid_time_for_world(task_world, time_shifted + 1),
                # The task_world is in some_state at time_shifted
                some_state == z3.Select(self.world_function(task_world), time_shifted),
                # And the task_world is in next_state at the successor of time_shifted
                next_state == z3.Select(self.world_function(task_world), time_shifted + 1)
            )
        )
    )
)
```

#### Task Minimization Constraint

Guides Z3 to prefer solutions where consecutive world states are identical when possible, reducing unnecessary state changes.

```python
task_minimization = z3.ForAll(
    [world_id, time_point],
    z3.Implies(
        z3.And(
            self.is_world(world_id),
            self.is_valid_time_for_world(world_id, time_point),
            self.is_valid_time_for_world(world_id, time_point + 1)
        ),
        # Encourage identical states if possible (soft constraint)
        z3.Select(self.world_function(world_id), time_point) ==
        z3.Select(self.world_function(world_id), time_point + 1)
    )
)
```

The frame constraints are applied in a specific order to guide Z3's model search efficiently.

## Known Limitations

- **Performance**: Models with many time points or complex formulas may run slowly
- **Z3 Timeouts**: Complex models may hit solver timeouts (adjust the `max_time` setting)
- **Abundance Impact**: The abundance constraint significantly increases computational load
- **Model Complexity**: The full bimodal semantics creates models that may challenge Z3's capabilities
- **Memory Usage**: Large models with many worlds and times can consume significant memory

## References

For more information on bimodal logics and related topics, see:

- The full ModelChecker documentation in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/README.md`
- The test suite in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/theory_lib/LTL/test/`
- The Counterfactuals paper in `/home/benjamin/Documents/Philosophy/Projects/ModelChecker/Counterfactuals.pdf`

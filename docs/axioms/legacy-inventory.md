# Legacy algebraic-axiom inventory

This inventory records the intent of the historical checkout before new production
code is written. It is evidence, not a supported DIG dependency.

## Provenance and disposition

- Source remote: `git@github.com:nguyenthanhvuh/algebraicaxioms.git`
- Imported revision: `a22e1a07d8963465c2fe85d934ada384c34db3fa`
- Revision date: 2021-08-22
- Current form: a nested Git checkout at `algebraicaxioms/`
- Production dependency: forbidden

The revision contains no `LICENSE`, copying notice, or package metadata declaring a
license. Therefore its implementation is treated as not licensed for copying into
DIG. Algorithms and externally observable behavior may be independently
reimplemented; code must not be copied. DIG's own license does not change that.

Decision: preserve the checkout locally as a read-only archival reference during the
port and exclude `algebraicaxioms/` from DIG through `.gitignore`. It is neither a
production dependency nor a distributed artifact. The behavior inventory and pinned
commit make the checkout removable without losing intended behavior. Resolving the
upstream license remains a prerequisite to distributing or formalizing it as a
submodule, but not to the clean-room implementation.

## Intended behavior table

| Area | Legacy declaration or mechanism | Behavior to preserve | Behavior to reject/change |
|---|---|---|---|
| Stack | `push`, `pop`, `peek`, `empty`, `search` | typed composition; `pop(push(s,x)) = x`; post-state observations | raw `Stack` classes and generated Java files in the source tree |
| Python list | `append`, `extend`, `insert`, `pop` | mutator effects on argument 0; indices and element values | interpreting a `None` return as the mutation result |
| String | `fake`, `concat`, `isEmpty`, `length` sketches | pure observer/composition examples | incomplete `fake` declaration and name-only Java dispatch |
| String buffer | `append`, with planned reverse/delete/insert/replace | mutable receiver plus snapshot equality | ad-hoc custom type flags (`fname`, `createNew`) |
| Aliasing | `Term.gen_args()` instantiation patterns | shared and distinct same-type roots | duplicate integer assignments and noncanonical variable names |
| Effects | `side_effect_idxs` and `merge_se` | propagate declared effects through nested terms | optional merging that can compare one side after contaminating state |
| Exceptions | soft checks around selected Python/Java exceptions | exclude undefined inputs such as empty pop | converting caught exceptions into Boolean success/failure without evidence |
| Testing | generated `Test.py` / `Test.java`, random examples | executable refutation and boundary examples | fixed working-directory files, global RNG, pass/fail-only results |

## Behavior fixtures to carry forward

### Stack

- `pop(push(stack_0, item_0)) == item_0` compares both return and stack post-state.
- `peek(push(stack_0, item_0)) == item_0` preserves the pushed element.
- Empty `pop`/`peek` cases are invalid-domain samples under the default policy.
- `stack_0` used twice and `stack_0`/`stack_1` are separate alias cases.

### List

- Append and insert are void mutators whose effective result is the list snapshot.
- Duplicate values, empty lists, negative/zero/boundary indices, and aliasing between
  two list arguments must occur in deterministic recipes.
- One-side exception refutes; two-side exception does not support a law.

### Strings and string buffers

- Immutable strings use value equality.
- Mutable buffers require a configured string snapshot.
- `reverse(reverse(buffer))` is expected to restore the observable buffer state,
  subject to the API's return-value convention.

## Reusable ideas, not modules

- bottom-up typed tree construction;
- alias-pattern enumeration;
- explicit side-effect propagation;
- structural normalization and redundancy pruning;
- batching candidate tests.

## Known defects and modernization decisions

1. Private/obsolete typing details such as `__parameters__` make the prototype
   incompatible with modern Python typing behavior.
2. Assertions perform user/runtime validation and disappear under `python -O`.
3. Global `random.seed` and set iteration make runs hard to reproduce.
4. Generated `Test.py`, `Test.java`, and class files pollute the working directory.
5. Shell command strings and a machine-specific Java classpath are unsafe and
   nonportable.
6. Equality can omit observable mutations or conflate return values with state.
7. Both-side exceptions can make partial operations appear lawful.
8. A hard-coded exception list loses class/payload and domain evidence.
9. Pairwise equation testing scales quadratically and loses per-term observations.
10. Structural implication pruning has no independent soundness oracle.
11. Flat imports and copied `vu_common.py` couple the prototype to an old layout.
12. There is no result schema, replayable counterexample, proof scope, or distinction
    between discovery and validation.

The new implementation may use the legacy algorithms as design input only. Tests for
the new core must not import from `algebraicaxioms/python/src`.

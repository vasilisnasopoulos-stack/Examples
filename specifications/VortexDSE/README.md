# Vortex DSE — C-slot admission and per-slot agreement

Vortex DSE is a deterministic consensus protocol in which a message carries its
own slot stamp and each node decides admission locally, against its own clock.
There is no leader, no quorum and no vote: admission is an O(1) local predicate,
and cross-node agreement on the per-slot input set is established afterwards by
a separate layer.

These specifications model that structure. They are the formal counterpart of a
running implementation; the implementation itself is not part of this
contribution.

## Two admission modes

The protocol has two admission rules, and the difference is one operator.

| module | rule | meaning |
| --- | --- | --- |
| `Vortex_DSE_CSlot` | `m.cslot <= current_slot` | the default. A message stamped for slot *k* that arrives late is still admitted, into slot *k*. Nothing is dropped. |
| `Vortex_DSE_CSlot_TTL` | `m.cslot = current_slot` | an opt-in bounded-memory mode. A message that misses its slot is rejected permanently, so state does not grow behind the frontier. |

Both modes are specified because both are implemented; the strict rule is a
memory concession, not a stronger version of the protocol.

## Modules

| module | what it adds |
| --- | --- |
| `Vortex_DSE_CSlot` | admission, crash and rejoin via a persisted snapshot |
| `Vortex_DSE_CSlot_Proofs` | `TypeCorrect`, `NoFutureAdmissionCorrect` |
| `Vortex_DSE_CSlot_ExactlyOnce_Proof` | `StrictExactlyOnceCorrect` |
| `Vortex_DSE_CSlot_TTL` | the strict admission mode |
| `Vortex_DSE_CSlot_Skew` | replaces the single global slot with a per-node clock, plus Byzantine injection of forged slot stamps and origins |
| `Vortex_DSE_CSlot_AE` | the agreement layer: `Freeze`, `Reconcile`, `Commit` over the strict mode |
| `Vortex_DSE_CSlot_AE_Proofs` | deductive proofs for the agreement layer |
| `Vortex_DSE_CSlot_AE_Refinement` | the agreement cycle as a refinement of the core |
| `Vortex_DSE_CSlot_AE_Refinement_Proofs` | the refinement theorem |

None of these carries a slot horizon: the ticker is unbounded and the
adversary may forge any slot in `Nat`. Horizons are a model-checking concern
and live in the `MC_` modules, which bound the actions directly rather than
applying a state constraint — under a constraint TLC discards successor
states, which is unsound for the temporal properties. `MaxSkew` is the one
bound that stays in a specification, because it is an assumption the protocol
relies on rather than a checking artifact.

`Vortex_DSE_CSlot_AE` is specified over the strict admission rule and is not a
refinement of anything: its `NextCslot` clears `processed` for every node at a
slot boundary, which no action of the core can do, and it models no crash.

`Vortex_DSE_CSlot_AE_Refinement` is the same agreement cycle written as an
actual layer. It carries the core's variables unchanged, lets `processed`
accumulate, and keeps the per-slot input set in `committed`. Every action is
either a core action or leaves the core's variables alone, so

```
THEOREM Refinement == Spec => C!Spec
```

holds under the identity mapping — proved in
`Vortex_DSE_CSlot_AE_Refinement_Proofs`, and checked by TLC as a temporal
property besides.

## What is checked

All TLAPS proofs discharge under `tlapm --strict`, which fails on unproved
obligations and on proof steps left open — a plain `tlapm` invocation exits 0
in both cases. There are no `OMITTED` steps in these modules.

| | obligations |
| --- | --- |
| `Vortex_DSE_CSlot_Proofs` | 191 |
| `Vortex_DSE_CSlot_ExactlyOnce_Proof` | 128 |
| `Vortex_DSE_CSlot_AE_Proofs` | 32 |
| `Vortex_DSE_CSlot_AE_Refinement_Proofs` | 25 |

Every model completes in a few seconds. `Vortex_DSE_CSlot_AE` also carries
Apalache type annotations, but no symbolic model is registered here; the models
below are TLC only.

## Scope

`Vortex_DSE_CSlot_Skew` bounds pairwise clock skew structurally, by forbidding
any tick that would breach `MaxSkew`. It states the assumption; it does not
model the mechanism that maintains it. Likewise `Reconcile` is a single atomic
step at specification level — the multi-round protocol underneath is out of
scope here.

Source repositories, including the whitepaper and the model-checking logs:
<https://github.com/vasilisnasopoulos>

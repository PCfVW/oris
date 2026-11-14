-- SPDX-License-Identifier: MIT OR Apache-2.0
import Lean

/-!
# The axiom gate

`#audit_axioms N` checks every declaration whose name starts with `N` and fails if any of them
depends on an axiom outside Lean's three standard ones (`propext`, `Classical.choice`,
`Quot.sound`). That catches, in one place:

- `sorry` (it elaborates to the axiom `sorryAx`),
- `native_decide` and `bv_decide` (both rest on `Lean.ofReduceBool`, i.e. on trusting compiled
  code rather than the kernel),
- any `axiom` declared by hand.

So a green build means every theorem was checked by the kernel alone. Rationale and policy:
`Lean/README.md`, "Rigour rules".
-/

open Lean Elab Command

/-- The axioms a proof in this project may depend on. -/
def Oris.Audit.allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Fails unless every declaration under the given namespace prefix depends only on
`Oris.Audit.allowedAxioms`; on success, logs how many declarations it checked. -/
elab "#audit_axioms " ns:ident : command => do
  let env ← getEnv
  let pre := ns.getId
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if pre.isPrefixOf n && !n.isInternal then
      let axs ← liftCoreM <| collectAxioms n
      let bad := axs.filter (fun a => !Oris.Audit.allowedAxioms.contains a)
      unless bad.isEmpty do
        throwError m!"{n} depends on non-standard axioms: {bad.toList}"
      count := count + 1
  if count == 0 then
    throwError m!"no declarations found under {pre}: the audit checked nothing"
  logInfo m!"audited {count} declarations under {pre}: standard axioms only"

-- SPDX-License-Identifier: MIT OR Apache-2.0
import Oris
import Oris.Audit

/-!
# The gate

Runs the axiom audit (`Oris/Audit.lean`) over every proof in the project: the whole `Oris`
namespace (every module `Oris.lean` imports, which `scripts/check-imports.sh` checks is every
module under `Oris/`) and the vendored `RBTree` library. `lake build` fails here if any theorem
depends on `sorry`, on `native_decide` or `bv_decide`, or on a hand-written axiom.
-/

#audit_axioms Oris
#audit_axioms RBTree

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVWI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QVWI.
Import ListNotations. Import AX2. Import APC. Import AP. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition node_smear47_at (p : Z) (cs : acs) (args : list expr) : option acs :=
match args with
| [] =>
if Z.eqb (pc cs) p then
match erange (kn cs) (reg cs 10) with
| Some (lo, hi) =>
if (Z.leb (2^46) lo && Z.ltb hi (2^47))%bool then
Some (set_pc (set_reg (set_reg (set_reg (set_reg (set_reg (set_reg cs
10 (ELit (2^47 - 1))) 11 (ELit 0x5555555555555555)) 12 (ELit 0x3333333333333333))
13 (ELit 0x0f0f0f0f0f0f0f0f)) 14 (ELit 0x0101010101010101)) 15 (ELit 0x7fff)) (p + 0x70))
else None
| None => None
end
else None
| _ => None
end.

Definition JO6_SMEAR : Z := 0x765b8.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.
Definition XNjo6 (id : nat) (args : list expr) (cs : acs) : option acs :=
match id with
| 1%nat => node_joinv segs nx0 cs args
| 2%nat => node_smear47_at JO6_SMEAR cs args
| _ => None
end.
End WithSegs.

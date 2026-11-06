(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
Import ListNotations.
Open Scope bv_scope.

Fixpoint code_at (segs : list Segment) (base : Z) (ws : list Z) : Prop :=
match ws with
| [] => True
| w :: ws' => fetch_word segs (Z_to_bv 64 base) = Some (Z_to_bv 32 w) /\ code_at segs (base + 4) ws'
end.

Lemma code_at_nth : forall segs ws base k w,
code_at segs base ws -> nth_error ws k = Some w ->
fetch_word segs (Z_to_bv 64 (base + 4 * Z.of_nat k)) = Some (Z_to_bv 32 w).
Proof.
intros segs ws. induction ws as [|w0 ws IH]; intros base k w HC Hn; [destruct k; discriminate|].
destruct k as [|k]; cbn in Hn.
- inversion Hn; subst. replace (base + 4 * Z.of_nat 0)%Z with base by lia. exact (proj1 HC).
- replace (base + 4 * Z.of_nat (S k))%Z with ((base + 4) + 4 * Z.of_nat k)%Z by lia.
eapply IH; [exact (proj2 HC)| exact Hn].
Qed.

Ltac pstep_core segs R F base off fc rv m ro CODE :=
let k := eval vm_compute in (Z.to_nat (off / 4)) in
lazymatch type of CODE with code_at _ _ ?ws =>
let wo := eval vm_compute in (nth_error ws k) in
lazymatch wo with
| Some ?wz =>
let w := constr:(Z_to_bv 32 wz) in
let d := eval vm_compute in (decode_any w) in
lazymatch d with
| Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 (base + off)) fc rv m ro w i sz);
[ | replace (base + off)%Z with (base + 4 * Z.of_nat k)%Z by (cbn; lia);
exact (code_at_nth segs ws base k wz CODE eq_refl)
| vm_compute; reflexivity | vm_compute; reflexivity ];
exec_pre i;
exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
try solve_load; try solve_store;
reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
| None => fail "undecodable"
end
| None => fail "no code word at offset" off
end end.

Ltac pstep CODE :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 (?base + ?off)%Z) ?fc ?rv ?m ?ro) => pstep_core segs R F base off fc rv m ro CODE
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?base) ?fc ?rv ?m ?ro) =>
replace (Z_to_bv 64 base : word) with (Z_to_bv 64 (base + 0) : word) by (f_equal; lia);
pstep_core segs R F base 0%Z fc rv m ro CODE
end.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Tactic Notation "callc" uconstr(SPEC) tactic3(clr) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | clr; post_call segs m ]
end.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1ct X1d5.
Ltac tlia_strict := olia ltac:(
sf_clear_big;
first [ Zify.zify; xlia zchecker
| match goal with H : hid (_ \/ _) |- _ => unfold hid in H; Zify.zify; xlia zchecker end ]).

Section WithSegs.
Variable segs : list Segment.

Definition JX (pc : Z) (m : word -> option byte) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
: machine_state -> Prop :=
fun ms => exists (a0 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F' (Z_to_bv 64 pc) fc' None m (seg_rom segs)
/\ frm0 fc'.
End WithSegs.
Ltac jx_done := apply evt_done; do 3 eexists; split; [reflexivity| assumption].

Tactic Notation "join" constr(pcJ) integer(n1) integer(n2) :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut segs (JX segs pcJ mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
[ let B := fresh "B" in if_cases B;
[ do n1 astep; jx_done | do n2 astep; jx_done ]
| try match goal with H : frm0 _ |- _ => clear H end;
let FRM := fresh "FRM" in intros ? (? & ? & ? & -> & FRM) ]
end.

Lemma land_m32_16 : forall x, 16 <= x < 2^64 -> x mod 32 = 16 -> Z.land x 18446744073709551584 = x - 16.
Proof.
intros x Hx H. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.

Lemma seg0A : exists s rest, asegs = s :: rest /\ seg_base s = 0x10000%N /\ seg_size s = 0x34000%N /\ seg_writable s = false.
Proof. unfold asegs. lazymatch goal with |- context [?l = _ :: _] => let l' := eval hnf in l in lazymatch l' with ?s :: ?r => exists s, r; split; [reflexivity|]; repeat split; vm_compute; reflexivity end end. Qed.

Lemma ro_addr_seg0A : forall x, 0x10000 <= x < 0x44000 -> ro_addr asegs (Z_to_bv 64 x) = true.
Proof.
intros x Hx. destruct seg0A as (s & rest & E & B & S & Wr). unfold ro_addr. rewrite E. cbn [find_segment]. rewrite B, S.
rewrite (unsigned_small64 x) by lia.
replace (Z.of_N 65536 <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x + 1 <=? Z.of_N 65536 + Z.of_N 212992) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb]. rewrite Wr. reflexivity.
Qed.

Lemma ro_cells_rodataA : forall (m m' : word -> option byte) A cs, mem_inv asegs m -> mem_inv asegs m' ->
0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x44000 -> ro_cells asegs m A cs -> ro_cells asegs m' A cs.
Proof.
intros m m' A cs MI MI' HA HB [WF (B0 & B1 & BA)]. split; [exact WF|]. split; [exact B0|]. split; [exact B1|].
intros i Hi. rewrite <- (BA i Hi).
assert (Li : Z.of_nat (length (cells_bytes cs)) = Z.of_nat (cells_size cs)) by (rewrite cells_bytes_length by exact WF; reflexivity).
assert (RO : ro_addr asegs (wa (A + Z.of_nat i)) = true) by (apply ro_addr_seg0A; lia).
unfold mrd. destruct (m' (wa (A + Z.of_nat i))) eqn:E1; [pose proof (mem_inv_ro asegs _ _ _ MI' E1); congruence|].
destruct (m (wa (A + Z.of_nat i))) eqn:E2; [pose proof (mem_inv_ro asegs _ _ _ MI E2); congruence|]. reflexivity.
Qed.

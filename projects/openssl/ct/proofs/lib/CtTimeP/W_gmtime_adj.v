(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Layout Lib_kit F_memset.
From OSSVerify.Proofs.openssl.ct.lib.CtBnP Require Import BnKit.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Import ApWalkTac.
From OSSVerify.Proofs.openssl.ct.lib.CtPrnP Require Import MagicDiv.
From OSSVerify.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeMagic W_posix_to_tm W_gmtime W_tm_to_posix.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPENSSL_GMTIME_ADJ_STACK : Z := 64.     (* [comment removed for export] *)

Lemma ro_of_rw : forall m A cs, rw_cells ctpsegs m A cs -> ro_cells ctpsegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

(* [comment removed for export] *)
Ltac brT tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
  let BC := fresh "BC" in assert (BC : c = true) by tac; rewrite BC; clear BC; change (if true then a else b) with a end.
Ltac brF tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
  let BC := fresh "BC" in assert (BC : c = false) by tac; rewrite BC; clear BC; change (if false then a else b) with b end.
Ltac ltsz := rewrite ?lts_lit; rewrite ?swrap64_small by lia; rewrite ?swrap64_big by lia; cbn [negb];
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity | rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity].

(* [comment removed for export] *)
Lemma gmtime_adj_checks : forall (x1 x2 gp tp x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (pt sec : Z),
  (- 2^50 <= pt <= 2^50)%Z -> (0 <= sec <= 86399)%Z ->
  evt ctpsegs (fun ms' => exists x11', ms' =
      MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 pt) x11' (Z_to_bv 64 9223372036854775807) x13 x14 x15 x16 x17 (Z_to_bv 64 sec) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (Z_to_bv 64 0x11e2f4) fc None m (seg_rom ctpsegs))
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 pt) (Z_to_bv 64 (9223372036854775807 - pt)) (Z_to_bv 64 9223372036854775807) x13 x14 x15 x16 x17 (Z_to_bv 64 sec) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x11e2c0) fc None m (seg_rom ctpsegs)).
Proof.
  intros until sec. intros Hpt Hsec.
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (E50 : 2^50 = 1125899906842624) by reflexivity.
  destruct (Z_lt_le_dec 0 pt) as [P|NP].
  - (* [comment removed for export] *)
    zstep. brF ltsz. zstep. brF ltsz. zstep. brT ltsz. apply evt_done. eexists. reflexivity.
  - (* [comment removed for export] *)
    zstep. brT ltsz.
    destruct (Z.eq_dec pt 0) as [Z0|NZ].
    + (* [comment removed for export] *) zstep. brT ltsz. apply evt_done. eexists. reflexivity.
    + (* [comment removed for export] *)
      zstep. brF ltsz. zstep. setreg 11%Z (Z_to_bv 64 (9223372036854775808 - pt)) ltac:(wmodk Hpt).
      zstep. brT ltsz. apply evt_done. eexists. reflexivity.
Qed.

Lemma OPENSSL_gmtime_adj_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A d sec : Z),
  stk ctpsegs m lo (bv_unsigned sp) -> mem_inv ctpsegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - OPENSSL_GMTIME_ADJ_STACK)%Z ->
  (0 < A)%Z -> (bv_unsigned sp <= A)%Z -> (A + 56 <= 2^64)%Z -> rw_cells ctpsegs m A (tm_cells epoch_tm) ->
  (- 2^31 <= d < 2^31)%Z -> (0 <= sec <= 86399)%Z ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 d -> a2 = Z_to_bv 64 sec ->
  evt ctpsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (p2tm_ret (d * 86400 + sec))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctpsegs)
      /\ munch [(bv_unsigned sp - OPENSSL_GMTIME_ADJ_STACK, bv_unsigned sp); (A, A + 56)]%Z m m' /\ wmono ctpsegs m m' /\ mem_inv ctpsegs m'
      /\ stk ctpsegs m' lo (bv_unsigned sp)
      /\ rw_cells ctpsegs m' A (p2tm_cells (d * 86400 + sec)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_GMTIME_ADJ) fc None m (seg_rom ctpsegs)).
Proof.
  intros until sec. intros ST MI GLO LO HA HA2 HA3 TM Hd Hsec -> -> ->. unfold GLOBALS_TOP in GLO. unfold OPENSSL_GMTIME_ADJ, OPENSSL_GMTIME_ADJ_STACK in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + 56)]%Z m) as MU. pose proof (wmono_refl ctpsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (SEPA : A + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= A) by lia.
  carve_frame 48%nat ST. do 7 zstep.
  (* [comment removed for export] *)
  do 5 zstep.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) =>
    pose proof (proj1 (rw_cells_app _ _ [c0] rest) FR) as [PT FRH]; clear FR end.
  cbn [cells_size csize Nat.add] in FRH. replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in FRH by lia.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  name_mem m1. eapply evt_cut.
  { eapply (OPENSSL_tm_to_posix_epoch_spec _ (Z_to_bv 64 (bv_unsigned sp + -48))) with (lo := lo) (A := A) (B := bv_unsigned sp + -48);
      rewrite ?ESP; [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| lia| lia| apply ro_of_rw; exact TM| lia| lia| lia| exact PT| reflexivity| f_equal; lia]. }
  post_call_esp ESP m1. rename PC into ST. rewrite ESP in ST. name_mem m2. rename MI0 into MI. rename POST into PT.
  (* [comment removed for export] *)
  zstep. brc. zstep. zstep. zstep.
  zstep. setreg 10%Z (Z_to_bv 64 (d * 86400)) ltac:(wmodk Hd).
  zstep. zstep. zstep. setreg 10%Z (Z_to_bv 64 (d * 86400)) ltac:(wmodk Hd).
  zstep. setreg 11%Z (Z_to_bv 64 (9223372036854775807 - d * 86400)) ltac:(wmodk Hd).
  eapply evt_cut; [eapply gmtime_adj_checks; lia|]. intros ms' [x11' ->].
  (* [comment removed for export] *)
  zstep. setreg 10%Z (Z_to_bv 64 (d * 86400 + sec)) ltac:(wmodk Hd).
  zstep.
  replace (bv_unsigned sp + -40) with (bv_unsigned sp + -48 + Z.of_nat (cells_size [C8 (Z_to_bv 64 0)])) in FRH by (cbn; lia).
  pose proof (proj2 (rw_cells_app _ _ [C8 (Z_to_bv 64 0)] _) (conj PT FRH)) as FR. clear PT FRH. cbn [app] in FR.
  do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  destruct (rw_cells_forget _ _ _ _ TM) as [junk56 TMJ]. cbn [cells_size csize Nat.add] in TMJ.
  name_mem m3. eapply evt_cut.
  { eapply (OPENSSL_posix_to_tm_spec ra sp) with (lo := lo) (t := d * 86400 + sec) (D := A) (junk := junk56);
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| lia| exact TMJ| lia| reflexivity| reflexivity]. }
  post_call ctpsegs m3.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

End WithCeiling.

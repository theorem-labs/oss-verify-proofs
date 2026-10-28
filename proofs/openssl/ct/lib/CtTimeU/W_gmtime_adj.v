(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit F_memset.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import MagicDiv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit3 TimeMagic W_posix_to_tm W_gmtime W_tm_to_posix.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPENSSL_GMTIME_ADJ_STACK : Z := 80.     (* [comment removed for export] *)

Lemma ro_of_rw : forall m A cs, rw_cells ctusegs m A cs -> ro_cells ctusegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

Lemma sltz_lit : forall a, - 2^63 <= a < 2^63 -> (Z.lxor (Z.land a 18446744073709551615) 9223372036854775808 <? 9223372036854775808) = (a <? 0).
Proof.
  intros a Ha. rewrite !land64.
  rewrite !(zb_lxor_sign) by (change (2^64) with 18446744073709551616; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
  change (2^63) with 9223372036854775808 in *. change (2^64) with 18446744073709551616 in *.
  destruct (Z.ltb_spec a 0) as [L|L]; [apply Z.ltb_lt| apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Ltac brT tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
  let BC := fresh "BC" in assert (BC : c = true) by tac; rewrite BC; clear BC; change (if true then a else b) with a end.
Ltac brF tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
  let BC := fresh "BC" in assert (BC : c = false) by tac; rewrite BC; clear BC; change (if false then a else b) with b end.
Ltac ltsz := rewrite ?lts_lit; rewrite ?swrap64_small by lia; rewrite ?swrap64_big by lia; cbn [negb];
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity | rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity].

(* [comment removed for export] *)
Lemma gmtime_adj_checks : forall (x1 x2 gp tp x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (pt sec : Z),
  (- 2^50 <= pt <= 2^50)%Z -> (0 <= sec <= 86399)%Z ->
  evt ctusegs (fun ms' => exists x10', ms' =
      MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10' (Z_to_bv 64 pt) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sec) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (Z_to_bv 64 0x12d39c) fc None m (seg_rom ctusegs))
    (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (9223372036854775807 - pt)) (Z_to_bv 64 pt) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sec) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x12d380) fc None m (seg_rom ctusegs)).
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
      zstep. brF ltsz. zstep. setreg 10%Z (Z_to_bv 64 (9223372036854775808 - pt)) ltac:(wmodk Hpt).
      zstep. brT ltsz. apply evt_done. eexists. reflexivity.
Qed.

Lemma OPENSSL_gmtime_adj_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo A d sec : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - OPENSSL_GMTIME_ADJ_STACK)%Z -> bv_unsigned sp mod 16 = 0 ->
  (0 < A)%Z -> (bv_unsigned sp <= A)%Z -> (A + 56 <= 2^64)%Z -> (A mod 8 = 0)%Z -> rw_cells ctusegs m A (tm_cells epoch_tm) ->
  (- 2^31 <= d < 2^31)%Z -> (0 <= sec <= 86399)%Z ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 d -> a2 = Z_to_bv 64 sec ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (p2tm_ret (d * 86400 + sec))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - OPENSSL_GMTIME_ADJ_STACK, bv_unsigned sp); (A, A + 56)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' A (p2tm_cells (d * 86400 + sec)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OPENSSL_GMTIME_ADJ) fc None m (seg_rom ctusegs)).
Proof.
  intros until sec. intros ST MI GLO LO SP16 HA HA2 HA3 ALA TM Hd Hsec -> -> ->. unfold GLOBALS_TOP in GLO. unfold OPENSSL_GMTIME_ADJ, OPENSSL_GMTIME_ADJ_STACK in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 56)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
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
      rewrite ?ESP; [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| lia| lia| exact ALA| apply ro_of_rw; exact TM| lia| lia| lia| clear - SP16; Z.div_mod_to_equations; lia| exact PT| reflexivity| f_equal; lia]. }
  post_call_esp ESP m1. rename PC into ST. rewrite ESP in ST. name_mem m2. rename MI0 into MI. rename POST into PT.
  (* [comment removed for export] *)
  zstep. brc. zstep. zstep. zstep.
  zstep. setreg 12%Z (Z_to_bv 64 (d * 86400)) ltac:(wmodk Hd).
  zstep. setreg 11%Z (Z_to_bv 64 (d * 86400)) ltac:(wmodk Hd).
  zstep. setreg 10%Z (Z_to_bv 64 (Z.b2z (d * 86400 <? 0))) ltac:(f_equal; f_equal; symmetry; apply sltz_lit; clear - Hd E63; lia).
  zstep. setreg 12%Z (Z_to_bv 64 (Z.b2z (d * 86400 <? 0))) ltac:(f_equal; f_equal; symmetry; rewrite (Z.add_0_l 9223372036854775808); apply sltz_lit; clear - Hd E63; lia).
  zstep. let C := fresh "C" in if_cases C; [exfalso; zify_cond C; lia | clear C].
  zstep. zstep. zstep.
  zstep. setreg 10%Z (Z_to_bv 64 (9223372036854775807 - d * 86400)) ltac:(wmodk Hd).
  eapply evt_cut; [eapply gmtime_adj_checks; lia|]. intros ms' [x10' ->].
  (* [comment removed for export] *)
  zstep. setreg 10%Z (Z_to_bv 64 (d * 86400 + sec)) ltac:(wmodk Hd).
  zstep. setreg 11%Z (Z_to_bv 64 (Z.b2z (d * 86400 + sec <? d * 86400))) ltac:(f_equal; f_equal; symmetry; apply slt_signed_small; clear - Hd Hsec E63; lia).
  zstep. setreg 12%Z (Z_to_bv 64 (Z.b2z (sec <? 0))) ltac:(f_equal; f_equal; symmetry; rewrite (Z.add_0_l 9223372036854775808); first [apply sltz_lit; clear - Hsec E63; lia| rewrite slti_lit by (clear - Hsec E63; lia); change (9223372036854775808 - 9223372036854775808) with 0; reflexivity]).
  replace (d * 86400 + sec <? d * 86400) with (sec <? 0) by (symmetry; destruct (Z.ltb_spec sec 0) as [Hs|Hs]; [apply Z.ltb_lt| apply Z.ltb_ge]; clear - Hs; lia).
  zstep. let C := fresh "C" in if_cases C; [exfalso; zify_cond C; lia | clear C].
  zstep. zstep.
  destruct (rw_cells_forget _ _ _ _ TM) as [junk56 TMJ]. cbn [cells_size csize Nat.add] in TMJ.
  name_mem m3. eapply evt_cut.
  { eapply (OPENSSL_posix_to_tm_spec _ (Z_to_bv 64 (bv_unsigned sp + -48))) with (lo := lo) (t := d * 86400 + sec) (D := A) (junk := junk56);
      rewrite ?ESP; [exact ST| exact MI| unfold GLOBALS_TOP; lia| lia| lia| lia| exact TMJ| lia| reflexivity| reflexivity]. }
  post_call_esp ESP m3. rename PC into ST. rewrite ?ESP in ST.
  lazymatch type of PT with rw_cells _ _ _ ?c1 =>
    replace (bv_unsigned sp + -40) with (bv_unsigned sp + -48 + Z.of_nat (cells_size c1)) in FRH by (cbn; lia);
    pose proof (proj2 (rw_cells_app _ _ c1 _) (conj PT FRH)) as FR end.
  clear PT FRH. cbn [app] in FR.
  do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.

End WithCeiling.

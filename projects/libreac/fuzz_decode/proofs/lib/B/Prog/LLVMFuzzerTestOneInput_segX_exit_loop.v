(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_exit_loop: the scan loop L6 of image B's LLVMFuzzerTestOneInput exit group,
   +0xa34 .. +0xa64, and the stretch it falls into, +0xa78 .. +0xab8, on the path where reac_upstream_decode #3
   refused (a0 = -1):
     +0xa34 bltu s9, a3 (UBSan wrap of s7 + i)    +0xa38 add a1, s7, a3     +0xa3c..+0xa48 the ASan check
     +0xa4c lbu a1, 0(a1); addi a1, a1, -0xa5; snez a1; addi a3, a3, 1; or a2, a2, a1; bne s8, a3, +0xa34
     +0xa64 j +0xa78; +0xa78 bnez a2 (abort unless every byte is 0xa5); +0xa7c blez a0, +0xab8
   It is the up group's L5 (lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_loop.v up_loop, +0x918 .. +0x958) with the
   index in a3 instead of a2 and the accumulator in a2 instead of a1; the proof is up_loop's, step for step, on the
   up group's env (EL) and helpers. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segX_up_a LLVMFuzzerTestOneInput_segX_up_b LLVMFuzzerTestOneInput_segX_up_c
LLVMFuzzerTestOneInput_segX_up_loop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN1y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the originals
   (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* The seat of one iteration: up_loop's (up_lfacts / ss_loop) with the index in a3. *)
Definition ex_lfacts : facts :=
  mkFacts [(18%nat, mkAF 2147450880 2147450880 0); (33%nat, mkAF 4096 UP_BLK_HI 0)] []
    [(SAlu ALU_ADD (SOff 23 0) (SOff 13 0), SOff 33 0)].
Definition ex_ss_loop : sstate := mkSS 0xa34 sr_atoms [up_lreg] None ex_lfacts.
(* The registers one iteration leaves alone: up_keepL and a0 (the refused call's -1, read at +0xa7c). *)
Definition ex_keepL : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs _ decodeb_listing PI_decodeb).
#[local] Abbreviation VAL := (@pa_val _ decodeb_listing PI_decodeb).
#[local] Abbreviation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let RUNTO := @paj_run_to fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.

(* up_loop.v up_lseat, at +0xa34 with the index in a3. *)
Lemma ex_lseat : forall regs (W : world SEGS) mem md ly S upb m i,
  AR SEGS B ly S W mem md -> In (upb, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 23 = w64 upb -> getr regs 13 = w64 i ->
  aview SEGS (w_H W) mem (upb + i) = Some 165 ->
  st_ok_pi SEGS VAL (EL regs (upb + i)) ex_ss_loop
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xa34)) mem (seg_rom SEGS))) /\
  sh_ok SEGS LBx up_LSH (EL regs (upb + i)) (mrestrict (w_H W) mem).
Proof.
intros regs W mem md ly S upb m i HAR Hin Hi H18 H23 H13 Hbyte.
destruct (al_blocks _ _ LAWS ly S W mem md upb m HAR Hin) as (_ & H4096 & Hc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Ha : 0 <= upb + i < 18446744073709551616) by lia.
set (E := EL regs (upb + i)).
assert (U33 : U E (SOff 33 0) = upb + i) by exact (EL_U_33 regs (upb + i) Ha).
assert (U18 : U E (SOff 18 0) = SHADOW_OFF)
  by (exact (EL_U_reg regs (upb + i) 18%bv 18 SHADOW_OFF eq_refl H18 ltac:(unfold SHADOW_OFF; lia))).
assert (U23 : U E (SOff 23 0) = upb) by (exact (EL_U_reg regs (upb + i) 23%bv 23 upb eq_refl H23 ltac:(lia))).
assert (U13 : U E (SOff 13 0) = i) by (exact (EL_U_reg regs (upb + i) 13%bv 13 i eq_refl H13 ltac:(lia))).
rewrite restrict_mkst_fx. split.
- apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor]. unfold region_ok, up_lreg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    assert (B33 : bv_unsigned (ew E 33) = upb + i)
      by (subst E; rewrite EL_33, Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
          apply Z.mod_small; exact Ha).
    rewrite B33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (upb + i) 0 1 (SLit 165) 165);
      [reflexivity | first [cbn; lia | vm_compute; split; [discriminate | reflexivity]] | lia |].
    rewrite Z.add_0_r. exact (up_val1 W mem (upb + i) Hbyte).
  + cbn [pairwise_disjoint all_disjoint]. split; exact I.
  + split; [|split].
    * cbn [f_atoms atoms_ok ex_lfacts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      assert (B18 : bv_unsigned (ew E 18) = SHADOW_OFF)
        by (subst E; rewrite (EL_reg regs (upb + i) 18%bv 18 eq_refl), H18; reflexivity).
      assert (B33 : bv_unsigned (ew E 33) = upb + i)
        by (subst E; rewrite EL_33, Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
            apply Z.mod_small; exact Ha).
      rewrite B18, B33. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF, UP_BLK_HI.
      repeat split; try exact I; lia.
    * exact I.
    * cbn [f_alias alias_ok ex_lfacts]. split; [|exact I].
      apply U_inj. rewrite U_SAlu, U23, U13, U33. cbn [zalu_raw]. apply zcanon_id.
      change M64 with 18446744073709551616. lia.
- constructor; [|constructor]. split.
  + cbn [she_m she_lo she_hi]. rewrite U33, Z.add_0_r. change (1 - 0) with 1.
    apply (obl_of_block SEGS B LAWS ly S W mem md E LBx (upb + i) 1 upb m HAR Hin U18); lia.
  + unfold app_apart, LBx. cbn [she_m she_lo she_hi]. rewrite U33. rewrite ?U18. intros a Ha'.
    change (Z.min 0 1) with 0 in Ha'. change (Z.max 0 1) with 1 in Ha'.
    unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia.
Qed.

(* up_loop.v's in_tac / up_agree_of (Section-local there). *)
Ltac in_tac := repeat (first [left; reflexivity | right]).
Ltac up_agree_of HS regs a H :=
  pose proof (EL_agree regs a) as HAE0;
  lazymatch type of HS with
  | st_ok_pi _ _ ?E _ _ => assert (H : env_agree 32 (Ereg regs (up_lextra a)) E) by up_agree_ext
  | st_ok _ ?E _ _ => assert (H : env_agree 32 (Ereg regs (up_lextra a)) E) by up_agree_ext
  end; clear HAE0.

(* +0xa34 .. +0xab8: the loop over the bytes left, then +0xa78 / +0xa7c, both deciding for free #2. *)
Lemma ex_loop : forall (W : world SEGS) STK sp0 FP ly0 S0 W0 mem0 md0 own ly S k (regs0 : bvmap 5 word) mem upb m
    (Q : world SEGS -> config -> Prop),
  In (upb, m) (ablocks B ly S) -> 1 <= m <= 1440 ->
  (forall j, 0 <= j < m -> aview SEGS (w_H W) mem (upb + j) = Some 165) ->
  getr regs0 18 = w64 SHADOW_OFF -> getr regs0 23 = w64 upb -> getr regs0 24 = w64 m ->
  getr regs0 25 = w64 (Z.lnot upb) -> getr regs0 10 = w64 (-1) ->
  (forall regsT mdT,
     (forall x, In x ex_keepL -> getr regsT x = getr regs0 x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + 0xab8)) mem (seg_rom SEGS)) mdT) Q) ->
  forall n i regs md, n = Z.to_nat (m - i) -> 0 <= i < m ->
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  getr regs 12 = w64 0 -> getr regs 13 = w64 i ->
  (forall x, In x ex_keepL -> getr regs x = getr regs0 x) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xa34)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W STK sp0 FP ly0 S0 W0 mem0 md0 own ly S k regs0 mem upb m Q Hin Hm Hfill R18 R23 R24 R25 R10 HK n.
induction n as [n IH] using lt_wf_ind.
intros i regs md Hn Hi HJ H12 H13 Hkeep.
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly S W mem md upb m HAR Hin) as (_ & H4096 & Hbc & _).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
pose proof asan_consts as (C1 & _).
assert (G18 : getr regs 18 = w64 SHADOW_OFF) by (rewrite (Hkeep 18%bv ltac:(in_tac)); exact R18).
assert (G23 : getr regs 23 = w64 upb) by (rewrite (Hkeep 23%bv ltac:(in_tac)); exact R23).
assert (G24 : getr regs 24 = w64 m) by (rewrite (Hkeep 24%bv ltac:(in_tac)); exact R24).
assert (G10 : getr regs 10 = w64 18446744073709551615).
{ rewrite (Hkeep 10%bv ltac:(in_tac)), R10. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. }
assert (G25 : getr regs 25 = w64 (18446744073709551615 - upb)).
{ rewrite (Hkeep 25%bv ltac:(in_tac)), R25. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. rewrite up_lnot_mod by lia.
  rewrite (Z.mod_small (18446744073709551615 - upb)) by lia. reflexivity. }
destruct (ex_lseat regs W mem md ly S upb m i HAR Hin ltac:(lia) G18 G23 H13 (Hfill i Hi)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EL regs (upb + i))) by (unfold EL; apply Eimg_env).
pose proof (EL_agree regs (upb + i)) as HA0.
assert (U25 : U (EL regs (upb + i)) (SOff 25 0) = 18446744073709551615 - upb)
  by (rewrite (up_U_agree regs _ _ 25 25%bv _ 0 HA0 eq_refl G25 ltac:(lia)), Z.add_0_r; apply zcanon_id; change M64 with 18446744073709551616; lia).
assert (U13 : U (EL regs (upb + i)) (SOff 13 0) = i)
  by (rewrite (up_U_agree regs _ _ 13 13%bv _ 0 HA0 eq_refl H13 ltac:(lia)), Z.add_0_r; apply zcanon_id; change M64 with 18446744073709551616; lia).
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb0.
{ exfalso. rewrite branch_ltu_U, U25, U13 in Hb0. apply Z.ltb_lt in Hb0. lia. }
paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
up_agree_of HS regs (upb + i) HA1.
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb1.
- (* bytes left: back to +0xa34 with i + 1 *)
  rewrite branch_ne_U in Hb1.
  rewrite (up_U_agree regs _ _ 24 24%bv m 0 HA1 eq_refl G24 ltac:(lia)),
          (up_U_agree regs _ _ 13 13%bv i 1 HA1 eq_refl H13 ltac:(lia)) in Hb1.
  rewrite Z.add_0_r, !zcanon_id in Hb1 by (change M64 with 18446744073709551616; lia).
  apply negb_true_iff, Z.eqb_neq in Hb1.
  paj_run_to_tok RUNTO HS HJ SHOK UPspan 0xa34; [awr_ro|]. up_memeq HF.
  up_agree_of HS regs (upb + i) HA2.
  lazymatch goal with Hmem : ms_mem _ = _ |- _ => rewrite Hmem in HJ end.
  pmkst HS.
  lazymatch goal with Hmem : ms_mem _ = _ |- _ => rewrite Hmem end.
  eapply (IH (Z.to_nat (m - (i + 1))) ltac:(lia) (i + 1) _ _ eq_refl ltac:(lia) HJ).
  + up_rege HS (12%bv : bv 5) (SAlu ALU_OR (SOff 12 0) (SLit 0)).
    apply up_w64_of_U; [|lia]. rewrite U_SAlu, (up_U_agree regs _ _ 12 12%bv 0 0 HA2 eq_refl H12 ltac:(lia)), U_SLit.
    reflexivity.
  + up_rege HS (13%bv : bv 5) (SOff 13 1).
    apply up_w64_of_U; [|lia]. rewrite (up_U_agree regs _ _ 13 13%bv i 1 HA2 eq_refl H13 ltac:(lia)).
    apply zcanon_id. change M64 with 18446744073709551616. lia.
  + intros x Hx. rewrite <- (Hkeep x Hx).
    lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?msx) =>
      exact (regs_kept_of_st_ok_pi E ss (restrict H msx) regs (up_lextra (upb + i)) ex_keepL HS HA2
               ltac:(vm_compute; reflexivity) x Hx) end.
- (* the last byte: a2 = 0, so +0xa78 does not abort, and a0 = -1 takes +0xa7c to free #2 *)
  rewrite branch_ne_U in Hb1.
  rewrite (up_U_agree regs _ _ 24 24%bv m 0 HA1 eq_refl G24 ltac:(lia)),
          (up_U_agree regs _ _ 13 13%bv i 1 HA1 eq_refl H13 ltac:(lia)) in Hb1.
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  up_agree_of HS regs (upb + i) HA2.
  psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb2.
  { exfalso. rewrite branch_ne_U, U_SAlu, (up_U_agree regs _ _ 12 12%bv 0 0 HA2 eq_refl H12 ltac:(lia)), !U_SLit in Hb2.
    cbn in Hb2. discriminate. }
  paj_run_tok RUN HS HJ SHOK UPspan; [awr_ro|]. up_memeq HF.
  up_agree_of HS regs (upb + i) HA3.
  psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb3.
  + paj_run_to_tok RUNTO HS HJ SHOK UPspan 0xab8; [awr_ro|]. up_memeq HF.
    up_agree_of HS regs (upb + i) HA4.
    lazymatch goal with Hmem : ms_mem _ = _ |- _ => rewrite Hmem in HJ end.
    pmkst HS.
    lazymatch goal with Hmem : ms_mem _ = _ |- _ => rewrite Hmem end.
    apply HK; [|exact HJ].
    intros x Hx. rewrite <- (Hkeep x Hx).
    lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?msx) =>
      exact (regs_kept_of_st_ok_pi E ss (restrict H msx) regs (up_lextra (upb + i)) ex_keepL HS HA4
               ltac:(vm_compute; reflexivity) x Hx) end.
  + exfalso. rewrite (up_den_agree regs _ _ 10 10%bv HA3 eq_refl ltac:(lia)), G10 in Hb3.
    vm_compute in Hb3. discriminate.
Qed.
End g.

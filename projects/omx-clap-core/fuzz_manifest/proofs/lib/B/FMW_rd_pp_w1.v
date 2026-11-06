(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pp_w1.v (a working branch e2e59892bef), re-walked
   for B's code (B-readings.lst 0x82098 .. 0x820ec). *)
(* lv2_locate_manifest_readings on fm.asan-ubsan, segment PP, the first inner loop (lv2_locate.c:116, while
   (isspace (p[0])) p++): its head 0x82098 (FMW_rd_pp_cuts.v pp_at_L1) with k spaces consumed after p0.  One
   iteration: the shadow check of a1 = p0 + k, the byte c at s6 = p0 + k, `addi a3, c, -9; bgeu a3, s3` then
   `bne c, s2`.  A space: the guard 0x820b4 `beq s6, s0` (decided not taken by the token engine from pp_entry_L1's
   fact 4096 <= s6 <= 2^47 - 16, atom 22), s6, a1, a0 += 1, s9, s10 -= 1, back to the head at k + 1 (strong induction
   on the bytes left).  Not a space: 0x820e4 a1 = 0, s8 = s6 = p1, the second loop's head 0x820ec with no name byte. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_rd_cuts FMW_rd_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB FMW_rd_pp_cuts FMW_rd_pp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).

(* ---- the loop: one iteration from pp_at_L1, re-entry by strong induction on |text| - (i + s11 + k) ---- *)
Lemma w1_loop : forall f, pp_seg_W2 B CTX f ->
  forall r cx i d s11 k ly3 S3 W3 regs mem md,
  r = (length (cx_tb cx) - (i + s11 + k))%nat ->
  rd_base B CTX cx -> pp_at_L1 B cx i d (S f) s11 k ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L1 regs mem md) (rd_post B cx).
Proof.
intros f HW2 r. induction r as [r IH] using lt_wf_ind.
intros cx i d s11 k ly3 S3 W3 regs mem md Hr HB HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HP as ((HI & HA & Hi & Hh & Hs11 & Hsp0 & R21) & Hk & R10 & R11 & R22 & R25 & R26).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  ((V58 & Hu2 & HFc & HF2 & HF16) & R2 & R27 & HPN & R9 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
pose proof (pp_head_le (cx_tb cx) i _ Hh) as Hple.
pose proof (pp_cw_le is_space (cx_tb cx) (i + s11)) as Hcwle.
assert (Hq : (i + s11 + k <= length (cx_tb cx))%nat) by lia.
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (i + s11 + k) Ct Hq) as [Vc Hcb].
set (c := byte_at (cx_tb cx) (i + s11 + k)) in *.
assert (Hcdef : c = byte_at (cx_tb cx) (i + s11 + k)) by reflexivity.
assert (Hp0 : rd_p0 cx i s11 = cx_t cx + Z.of_nat i + Z.of_nat s11) by reflexivity.
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem) (rd_p0 cx i s11 + Z.of_nat k) 1 c)
  by (replace (rd_p0 cx i s11 + Z.of_nat k) with (cx_t cx + Z.of_nat (i + s11 + k)) by lia; exact Vc).
pose proof (pp_entry_L1 W3 regs mem (cx_F cx) (rd_p0 cx i s11 + Z.of_nat k) c R2 R27 HPN HFc HF2 HF16 R11 R22
  ltac:(lia) ltac:(lia) Hcb Vc') as HS.
set (E := Ereg regs (pp_extra 0 c 0)) in *.
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q)
  by (intros n q Hn; unfold E; apply ew_Ereg_nat; exact Hn).
pose proof (eq_trans (EE 9%nat 9%bv eq_refl) R9) as E9.
pose proof (eq_trans (EE 10%nat 10%bv eq_refl) R10) as E10.
pose proof (eq_trans (EE 11%nat 11%bv eq_refl) R11) as E11.
pose proof (eq_trans (EE 21%nat 21%bv eq_refl) R21) as E21.
pose proof (eq_trans (EE 22%nat 22%bv eq_refl) R22) as E22.
pose proof (eq_trans (EE 25%nat 25%bv eq_refl) R25) as E25.
pose proof (eq_trans (EE 26%nat 26%bv eq_refl) R26) as E26.
pose proof (eq_trans (EE 27%nat 27%bv eq_refl) R27) as E27.
assert (E33 : ew E 33 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
clear EE.
assert (HBx : U E PP_Bx = SHADOW_OFF) by exact (pp_U_Bx E E27).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L1) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_L1) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_L1) with (Z_to_bv 64 PP_L1).
(* 0x82098 .. 0x820b0: the shadow check of a1 = p0 + k, the byte c at s6 = p0 + k, a3 = c - 9 *)
aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
{ apply (pp_obl1 W3 _ E (SOff 11 0) (cx_t cx) (cx_tb cx) Ct HBx);
    rewrite (pp_U_off E 11%nat (rd_p0 cx i s11 + Z.of_nat k) 0 E11); unfold zcanon, M64;
    rewrite Z.mod_small by lia; lia. }
{ awr_ok_tac. }
pp_fr Hm.
srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
- (* bgeu taken: c is not 9 .. 13; 0x820d0 tests c against s2 = 32 *)
  pp_decb HS E33 c Hc.
  aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
  { awr_ok_tac. }
  pp_fr Hm2.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + (* bne taken: c is not 32, not a space; 0x820e4 a1 = 0, s8 = s6, the second loop's head *)
    pp_decb HS E33 c Hc0.
    assert (Hns : is_space c = false) by exact (pp_sp_no c Hcb Hc Hc0).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L2.
    { awr_ok_tac. }
    pp_fr Hm3.
    pp_land HS HJ E regs HK.
    apply (HW2 cx i d s11 (i + s11 + k)%nat 0%nat ly3 S3 W3 _ _ _ HB).
    unfold pp_at_L2, pp_head, pp_cd, pp_s10_L2.
    split; [split|].
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
    * split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
      pp_g HS.
    * split; [rewrite (pp_cw_exact is_space (cx_tb cx) (i + s11) k Hk Hns); reflexivity|].
      split; [lia|].
      split; [pp_g HS|]. split; [pp_g HS|].
      split; [rewrite Nat.add_0_r; pp_g HS|].
      do 3 (split; [pp_g HS|]). pp_g HS.
  + (* c = 32: a space; 0x820d4 j 0x820b4, the guard, back to the head at k + 1 *)
    pp_decb HS E33 c Hc0.
    assert (Hsp : is_space c = true) by exact (pp_sp_32 c Hcb Hc Hc0).
    assert (Hlt : (i + s11 + k < length (cx_tb cx))%nat) by exact (pp_lt_of_nz _ _ (pp_sp_nz c Hsp)).
    pose proof (pp_cw_next is_space (cx_tb cx) (i + s11) k Hk Hsp Hlt) as Hn.
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L1.
    { awr_ok_tac. }
    pp_fr Hm3.
    pp_land HS HJ E regs HK.
    apply (IH (length (cx_tb cx) - (i + s11 + S k))%nat ltac:(lia) cx i d s11 (S k) ly3 S3 W3 _ _ _
      eq_refl HB).
    unfold pp_at_L1, pp_head, pp_cd. cbv zeta.
    split; [split|].
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
    * split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
      pp_g HS.
    * split; [exact Hn|]. do 4 (split; [pp_g HS|]). pp_g HS.
- (* bgeu not taken: c is 9 .. 13, a space; 0x820b4 the guard, back to the head at k + 1 *)
  pp_decb HS E33 c Hc.
  assert (Hsp : is_space c = true) by exact (pp_sp_in c Hcb Hc).
  assert (Hlt : (i + s11 + k < length (cx_tb cx))%nat) by exact (pp_lt_of_nz _ _ (pp_sp_nz c Hsp)).
  pose proof (pp_cw_next is_space (cx_tb cx) (i + s11) k Hk Hsp Hlt) as Hn.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L1.
  { awr_ok_tac. }
  pp_fr Hm2.
  pp_land HS HJ E regs HK.
  apply (IH (length (cx_tb cx) - (i + s11 + S k))%nat ltac:(lia) cx i d s11 (S k) ly3 S3 W3 _ _ _
    eq_refl HB).
  unfold pp_at_L1, pp_head, pp_cd. cbv zeta.
  split; [split|].
  + apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | ..]; pp_g HS.
  + split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
    pp_g HS.
  + split; [exact Hn|]. do 4 (split; [pp_g HS|]). pp_g HS.
Qed.

Theorem pp_w1_holds : forall f, pp_seg_W2 B CTX f -> pp_seg_W1 B CTX f.
Proof.
intros f HW2 cx i d s11 k ly3 S3 W3 regs mem md HB HP.
exact (w1_loop f HW2 _ cx i d s11 k ly3 S3 W3 regs mem md eq_refl HB HP).
Qed.

End c.

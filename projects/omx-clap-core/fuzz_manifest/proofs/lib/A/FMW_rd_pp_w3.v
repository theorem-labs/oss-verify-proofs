(* lv2_locate_manifest_readings, segment PP, piece W3: the third inner loop at 0x81eb4 (lv2_locate.c:126, the spaces
   after the name's ':'), pp_seg_W3 of lib/A/FMW_rd_pp_cuts.v.  One iteration checks and loads the byte c at
   a0 + s10 + 1 = text + S p2 + m (0x81eb4 .. 0x81ecc) and tests it (0x81ed4 bgeu (c - 9, 5), 0x81eec bne (c, 32),
   0x81f04 bne (c, '<')): a space (0x81ed8: s10 += 1, s4, s9, s5 -= 1) goes back to the head at m + 1; '<' falls into
   the stores-and-strchr stretch at 0x81f08 (pp_seg_ST) with p3 = S p2 + m; any other byte makes the declaration DNone
   (readings_scan.db_nlt) and the scan goes on at i + 1 (0x82024 -> RD_L, pp_to_L).  The loop closes by strong
   induction on |text| - (S p2 + m), as G4's FMW_ex_decl_d3.v d3_loop (a working branch) closes the same C loop
   inlined in expected. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_cuts FMW_rd_ret ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_pp_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require readings_scan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- pure facts ---- *)
(* a byte other than NUL is inside the text (after G4 FMW_ex_decl_d3.v d3_lt) *)
Lemma w3_lt_of_nz : forall (tb : list Z) q, byte_at tb q <> 0 -> (q < length tb)%nat.
Proof.
intros tb q H. destruct (Nat.lt_ge_cases q (length tb)) as [Hq|Hq]; [exact Hq|].
exfalso. apply H. exact (readings_scan.byte_at_past tb q Hq).
Qed.

Lemma w3_sp_nz : forall c, is_space c = true -> c <> 0.
Proof. intros c H Hz. subst c. vm_compute in H. discriminate H. Qed.

(* one more byte of the class consumed (after G4 FMW_ex_decl_d3.v dm_cw_next) *)
Lemma w3_cw_next : forall f l p k, (k <= count_while f (skipn p l))%nat ->
  f (byte_at l (p + k)) = true -> (p + k < length l)%nat -> (S k <= count_while f (skipn p l))%nat.
Proof.
intros f l p k Hk Hf Hlt. rewrite (pp_cw_shift f l p k Hk), (readings_scan.cw_step f l (p + k) Hlt).
destruct (f (byte_at l (p + k))) eqn:Ef; [lia | congruence].
Qed.

(* membership of a register in a literal list of registers *)
Ltac w3_in := cbv [In]; repeat first [left; apply bv_eq; reflexivity | right].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).

Lemma w3_loop : forall f, rd_seg_L B CTX f -> pp_seg_ST B CTX f ->
  forall r cx i d s11 p1 p2 m ly3 S3 W3 regs mem md,
  r = (length (cx_tb cx) - (S p2 + m))%nat -> rd_base B CTX cx ->
  pp_at_L3 B cx i d (S f) s11 p1 p2 m ly3 S3 W3 regs mem md ->
  SRr tfibsegs W3 (cfg_at tfibsegs PP_L3 regs mem md) (rd_post B cx).
Proof.
intros f HL HST r. induction r as [r IH] using lt_wf_ind.
intros cx i d s11 p1 p2 m ly3 S3 W3 regs mem md Hr HB HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HP as ((HI & HA & Hi & Hh & Hs11 & Hsp0 & R19 & R24 & R27) & Ep1 & Ep2 & H58 & Hmc &
  R10 & R11 & R15 & R16 & R20 & R21 & R22 & R23 & R25 & R26).
pose proof (pp_facts_of B CTX cx d ly3 S3 W3 regs mem md HB HI) as
  (HFR & R2 & R8 & R9 & R18 & Ct & Cu & Ht4 & Htc & Hu4 & Huc & HWR & HJ).
assert (Hp0 : rd_p0 cx i s11 = cx_t cx + Z.of_nat i + Z.of_nat s11) by reflexivity.
assert (Hs10 : pp_s10_L3 cx i s11 p2 m = Z.of_nat p2 - Z.of_nat i - Z.of_nat s11 + Z.of_nat m) by reflexivity.
assert (Hp2 : (p2 < length (cx_tb cx))%nat) by (apply w3_lt_of_nz; rewrite H58; lia).
assert (Hle : (S p2 + m <= length (cx_tb cx))%nat)
  by (pose proof (pp_cw_le is_space (cx_tb cx) (S p2)); lia).
destruct (pp_val_at W3 mem (cx_t cx) (cx_tb cx) (S p2 + m) Ct Hle) as [Vc Hcr].
set (c := byte_at (cx_tb cx) (S p2 + m)) in *.
assert (Ha : rd_p0 cx i s11 + 1 + pp_s10_L3 cx i s11 p2 m = cx_t cx + Z.of_nat (S p2 + m)) by lia.
assert (Vc' : val_mem tfibsegs (mrestrict (w_H W3) mem) (rd_p0 cx i s11 + 1 + pp_s10_L3 cx i s11 p2 m) 1 c)
  by (rewrite Ha; exact Vc).
assert (Hs10n : 0 <= pp_s10_L3 cx i s11 p2 m) by lia.
assert (Hp0a : 4096 <= rd_p0 cx i s11) by lia.
assert (Hp0b : rd_p0 cx i s11 + pp_s10_L3 cx i s11 p2 m + 2 <= alloc_ceiling) by lia.
pose proof (pp_entry_L3 W3 regs mem (cx_F cx) (cx_u cx - 2) (cx_u cx - 3) (rd_p0 cx i s11)
  (pp_s10_L3 cx i s11 p2 m) c HFR R2 R8 R9 R18 R10 R11 R26 Hp0a Hs10n Hp0b Hcr Vc') as HS.
set (E := Ereg regs (pp_extra (cx_u cx - 2) (cx_u cx - 3) c
  (rd_p0 cx i s11 + 1 + pp_s10_L3 cx i s11 p2 m))) in *.
assert (E8 : ew E 8 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E20 : ew E 20 = w64 (cx_u cx - 3 - rd_p0 cx i s11 - pp_s10_L3 cx i s11 p2 m))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - pp_s10_L3 cx i s11 p2 m))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E24 : ew E 24 = w64 (cx_t cx + Z.of_nat i))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 (cx_u cx - 2 - rd_p0 cx i s11 - pp_s10_L3 cx i s11 p2 m))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (pp_s10_L3 cx i s11 p2 m))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E34 : ew E 34 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (rd_p0 cx i s11 + 1 + pp_s10_L3 cx i s11 p2 m))
  by (unfold E; exact (ew_Ereg_extra regs _ 3)).
assert (HBx : U E PP_Bx = SHADOW_OFF) by exact (pp_U_Bx E E8).
assert (SHOK : sh_ok tfibsegs PP_Bx [] E
  (mrestrict (w_H W3) (ms_mem (mkst regs (Z_to_bv 64 PP_L3) mem (seg_rom tfibsegs))))) by constructor.
change mem with (ms_mem (mkst regs (Z_to_bv 64 PP_L3) mem (seg_rom tfibsegs))) in HJ.
unfold cfg_at. change (w64 PP_L3) with (Z_to_bv 64 PP_L3).
(* 0x81eb4 .. 0x81ed4: the check of a1 + s10, the byte c at a0 + s10 + 1, bgeu (c - 9, 5) *)
aj_run_tok rd_tbl_ok HS HJ SHOK PP_Bspan.
{ apply (pp_obl1 W3 _ E (SOff 35 0) (cx_t cx) (cx_tb cx) Ct HBx);
    rewrite (pp_U_off E 35%nat _ 0 E35); unfold zcanon, M64; rewrite Z.mod_small by lia; lia. }
{ awr_ok_tac. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Hm0 end.
cbn [ms_mem] in Hm0.
srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
- (* c - 9 >=u 5: 0x81eec bne (c, 32) *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H34 : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
  erewrite (pp_Db_of _ c _ _ _ H34) in Hc by reflexivity. clear H34.
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan 0x81eec.
  { awr_ok_tac. }
  lazymatch type of HF0 with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF0) as Hm1 end.
  cbn [ms_mem] in Hm1.
  srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
  + (* c <> 32: not a space; 0x81f00 a0 = '<', 0x81f04 bne (c, '<') *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (H34 : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
    erewrite (pp_Db_of _ c _ _ _ H34) in Hc0 by reflexivity. clear H34.
    assert (Hns : is_space c = false) by exact (pp_sp_no c Hcr Hc Hc0).
    assert (Hcw : count_while is_space (skipn (S p2) (cx_tb cx)) = m)
      by exact (pp_cw_exact is_space (cx_tb cx) (S p2) m Hmc Hns).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan 0x81f04.
    { awr_ok_tac. }
    lazymatch type of HF1 with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF1) as Hm2 end.
    cbn [ms_mem] in Hm2.
    srr_branch_tok rd_tbl_ok HS SHOK PP_Bspan.
    * (* c <> '<': the declaration is DNone; 0x82024 .. 0x82030, the scan goes on at i + 1 *)
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        assert (H34 : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
      erewrite (pp_Db_of _ c _ _ _ H34) in Hc1 by reflexivity. clear H34.
      assert (Hn60 : c <> 60) by exact (pp_lt_no c Hcr Hc1).
      assert (Hdecl : decl (cx_tb cx) i = DNone).
      { rewrite (readings_scan.decl_some (cx_tb cx) i (i + s11)%nat Hh).
        apply (readings_scan.db_nlt (cx_tb cx) (i + s11)%nat p1 p2 (S p2 + m)%nat Hsp0 Ep1 Ep2 H58);
          [rewrite Hcw; reflexivity | exact Hn60]. }
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan RD_L.
      { awr_ok_tac. }
      lazymatch type of HF2 with frame_of _ ?rs _ _ =>
        pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF2) as Hm3 end.
      cbn [ms_mem] in Hm3.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
          ltac:(vm_compute; reflexivity)) as HK end.
      cbn [ms_regs restrict] in HK.
      pp_lift HS F24 24%nat E24.
      pp_rd HS (20%bv : bv 5) Q20. pp_rd HS (24%bv : bv 5) Q24.
      pp_rd HS (9%bv : bv 5) Q9. pp_rd HS (18%bv : bv 5) Q18.
      rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
      lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
        let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
      rewrite Hm3, Hm2, Hm1, Hm0 in HJ |- *.
      apply (pp_to_L B CTX f cx i d ly3 S3 W3 _ mem _ HL HB).
      -- apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | |];
           [rewrite Q9 | rewrite Q18]; cbn [sv_denot]; reflexivity.
      -- exact HA.
      -- exact Hi.
      -- exact Hdecl.
      -- rewrite Q20. cbn [sv_denot]. reflexivity.
      -- rewrite Q24, (pp_reg_off _ 24%nat _ 1 F24). reflexivity.
    * (* c = '<': the stores and strchr at 0x81f08 with p3 = S p2 + m *)
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        assert (H34 : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
      erewrite (pp_Db_of _ c _ _ _ H34) in Hc1 by reflexivity. clear H34.
      assert (H60 : c = 60) by exact (pp_lt_yes c Hcr Hc1).
      assert (Hp3 : (S p2 + m < length (cx_tb cx))%nat)
        by (apply w3_lt_of_nz; change (byte_at (cx_tb cx) (S p2 + m)) with c; lia).
      aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_ST.
      { awr_ok_tac. }
      lazymatch type of HF2 with frame_of _ ?rs _ _ =>
        pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF2) as Hm3 end.
      cbn [ms_mem] in Hm3.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
          ltac:(vm_compute; reflexivity)) as HK;
        pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ [15; 16; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS
          ltac:(env_agree_chain (env_agree_refl 32 E)) ltac:(vm_compute; reflexivity)) as HK2 end.
      cbn [ms_regs restrict] in HK, HK2.
      pp_lift HS F35 35%nat E35.
      pp_rd HS (12%bv : bv 5) Q12. pp_rd HS (9%bv : bv 5) Q9. pp_rd HS (18%bv : bv 5) Q18.
      rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
      lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
        let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
      rewrite Hm3, Hm2, Hm1, Hm0 in HJ |- *.
      assert (Hs3 : rd_s10 i s11 (S p2 + m) = pp_s10_L3 cx i s11 p2 m) by (unfold rd_s10; lia).
      apply (HST cx i d s11 p1 p2 (S p2 + m)%nat ly3 S3 W3 _ mem _ HB).
      unfold pp_at_ST, pp_head. cbv zeta. rewrite Hs3.
      split; [split|].
      -- apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | |];
           [rewrite Q9 | rewrite Q18]; cbn [sv_denot]; reflexivity.
      -- split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|].
         split; [exact Hsp0|].
         split; [rewrite (HK2 19%bv ltac:(w3_in)); exact R19|].
         split; [rewrite (HK2 24%bv ltac:(w3_in)); exact R24 | rewrite (HK2 27%bv ltac:(w3_in)); exact R27].
      -- split.
         { unfold rd_decl. cbv zeta.
           split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
           split; [exact Ep1|]. split; [exact Ep2|]. split; [exact H58|].
           split; [rewrite Hcw; reflexivity|]. split; [exact H60 | exact Hp3]. }
         split; [rewrite Q12, (pp_reg_off _ 35%nat _ (-1) F35); unfold w64; f_equal; lia|].
         split; [rewrite (HK2 15%bv ltac:(w3_in)); exact R15|].
         split; [rewrite (HK2 16%bv ltac:(w3_in)); exact R16|].
         split; [rewrite (HK2 20%bv ltac:(w3_in)); exact R20|].
         split; [rewrite (HK2 21%bv ltac:(w3_in)); exact R21|].
         split; [rewrite (HK2 22%bv ltac:(w3_in)); exact R22|].
         split; [rewrite (HK2 23%bv ltac:(w3_in)); exact R23|].
         split; [rewrite (HK2 25%bv ltac:(w3_in)); exact R25|].
         rewrite (HK2 26%bv ltac:(w3_in)). exact R26.
  + (* c = 32: a space; 0x81ef0 .. 0x81ee8, back to the head at m + 1 *)
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (H34 : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
    erewrite (pp_Db_of _ c _ _ _ H34) in Hc0 by reflexivity. clear H34.
    assert (Hsp : is_space c = true) by exact (pp_sp_32 c Hcr Hc Hc0).
    assert (Hlt : (S p2 + m < length (cx_tb cx))%nat)
      by (apply w3_lt_of_nz; change (byte_at (cx_tb cx) (S p2 + m)) with c; exact (w3_sp_nz c Hsp)).
    assert (Hmc' : (S m <= count_while is_space (skipn (S p2) (cx_tb cx)))%nat)
      by exact (w3_cw_next is_space (cx_tb cx) (S p2) m Hmc Hsp Hlt).
    aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L3.
    { awr_ok_tac. }
    lazymatch type of HF1 with frame_of _ ?rs _ _ =>
      pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF1) as Hm2 end.
    cbn [ms_mem] in Hm2.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
        ltac:(vm_compute; reflexivity)) as HK;
      pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ [10; 11; 15; 16; 19; 22; 23; 24; 27]%bv HS
        ltac:(env_agree_chain (env_agree_refl 32 E)) ltac:(vm_compute; reflexivity)) as HK2 end.
    cbn [ms_regs restrict] in HK, HK2.
    pp_lift HS F20 20%nat E20. pp_lift HS F21 21%nat E21. pp_lift HS F25 25%nat E25.
    pp_lift HS F26 26%nat E26.
    pp_rd HS (20%bv : bv 5) Q20. pp_rd HS (21%bv : bv 5) Q21. pp_rd HS (25%bv : bv 5) Q25.
    pp_rd HS (26%bv : bv 5) Q26. pp_rd HS (9%bv : bv 5) Q9. pp_rd HS (18%bv : bv 5) Q18.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
    lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
      let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
    rewrite Hm2, Hm1, Hm0 in HJ |- *.
    assert (Hs' : pp_s10_L3 cx i s11 p2 (S m) = pp_s10_L3 cx i s11 p2 m + 1) by (unfold pp_s10_L3; lia).
    apply (IH (length (cx_tb cx) - (S p2 + S m))%nat ltac:(lia) cx i d s11 p1 p2 (S m) ly3 S3 W3 _ mem _
      eq_refl HB).
    unfold pp_at_L3, pp_head. cbv zeta. rewrite Hs'.
    split; [split|].
    * apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | |];
        [rewrite Q9 | rewrite Q18]; cbn [sv_denot]; reflexivity.
    * split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
      split; [rewrite (HK2 19%bv ltac:(w3_in)); exact R19|].
      split; [rewrite (HK2 24%bv ltac:(w3_in)); exact R24 | rewrite (HK2 27%bv ltac:(w3_in)); exact R27].
    * split; [exact Ep1|]. split; [exact Ep2|]. split; [exact H58|]. split; [exact Hmc'|].
      split; [rewrite (HK2 10%bv ltac:(w3_in)); exact R10|].
      split; [rewrite (HK2 11%bv ltac:(w3_in)); exact R11|].
      split; [rewrite (HK2 15%bv ltac:(w3_in)); exact R15|].
      split; [rewrite (HK2 16%bv ltac:(w3_in)); exact R16|].
      split; [rewrite Q20, (pp_reg_off _ 20%nat _ (-1) F20); unfold w64; f_equal; lia|].
      split; [rewrite Q21, (pp_reg_off _ 21%nat _ (-1) F21); unfold w64; f_equal; lia|].
      split; [rewrite (HK2 22%bv ltac:(w3_in)); exact R22|].
      split; [rewrite (HK2 23%bv ltac:(w3_in)); exact R23|].
      split; [rewrite Q25, (pp_reg_off _ 25%nat _ (-1) F25); unfold w64; f_equal; lia|].
      rewrite Q26, (pp_reg_off _ 26%nat _ 1 F26). reflexivity.
- (* c - 9 <u 5: c is \t .. \r, a space; 0x81ed8 .. 0x81ee8, back to the head at m + 1 *)
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (H34 : ew Ev 34 = Z_to_bv 64 c) by (cbn [ew ewset extK Nat.eqb]; exact E34) end.
  erewrite (pp_Db_of _ c _ _ _ H34) in Hc by reflexivity. clear H34.
  assert (Hsp : is_space c = true) by exact (pp_sp_in c Hcr Hc).
  assert (Hlt : (S p2 + m < length (cx_tb cx))%nat)
    by (apply w3_lt_of_nz; change (byte_at (cx_tb cx) (S p2 + m)) with c; exact (w3_sp_nz c Hsp)).
  assert (Hmc' : (S m <= count_while is_space (skipn (S p2) (cx_tb cx)))%nat)
    by exact (w3_cw_next is_space (cx_tb cx) (S p2) m Hmc Hsp Hlt).
  aj_run_to_tok rd_tbl_ok HS HJ SHOK PP_Bspan PP_L3.
  { awr_ok_tac. }
  lazymatch type of HF0 with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF0) as Hm1 end.
  cbn [ms_mem] in Hm1.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ PP_KEPT HS ltac:(env_agree_chain (env_agree_refl 32 E))
      ltac:(vm_compute; reflexivity)) as HK;
    pose proof (g3_regs_of_st_ok tfibsegs Ev _ _ regs _ [10; 11; 15; 16; 19; 22; 23; 24; 27]%bv HS
      ltac:(env_agree_chain (env_agree_refl 32 E)) ltac:(vm_compute; reflexivity)) as HK2 end.
  cbn [ms_regs restrict] in HK, HK2.
  pp_lift HS F20 20%nat E20. pp_lift HS F21 21%nat E21. pp_lift HS F25 25%nat E25.
  pp_lift HS F26 26%nat E26.
  pp_rd HS (20%bv : bv 5) Q20. pp_rd HS (21%bv : bv 5) Q21. pp_rd HS (25%bv : bv 5) Q25.
  pp_rd HS (26%bv : bv 5) Q26. pp_rd HS (9%bv : bv 5) Q9. pp_rd HS (18%bv : bv 5) Q18.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl).
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
  rewrite Hm1, Hm0 in HJ |- *.
  assert (Hs' : pp_s10_L3 cx i s11 p2 (S m) = pp_s10_L3 cx i s11 p2 m + 1) by (unfold pp_s10_L3; lia).
  apply (IH (length (cx_tb cx) - (S p2 + S m))%nat ltac:(lia) cx i d s11 p1 p2 (S m) ly3 S3 W3 _ mem _
    eq_refl HB).
  unfold pp_at_L3, pp_head. cbv zeta. rewrite Hs'.
  split; [split|].
  + apply (pp_loop_keep B cx d ly3 S3 W3 regs _ md); [exact HI | exact HJ | exact HK | |];
      [rewrite Q9 | rewrite Q18]; cbn [sv_denot]; reflexivity.
  + split; [exact HA|]. split; [exact Hi|]. split; [exact Hh|]. split; [exact Hs11|]. split; [exact Hsp0|].
    split; [rewrite (HK2 19%bv ltac:(w3_in)); exact R19|].
    split; [rewrite (HK2 24%bv ltac:(w3_in)); exact R24 | rewrite (HK2 27%bv ltac:(w3_in)); exact R27].
  + split; [exact Ep1|]. split; [exact Ep2|]. split; [exact H58|]. split; [exact Hmc'|].
    split; [rewrite (HK2 10%bv ltac:(w3_in)); exact R10|].
    split; [rewrite (HK2 11%bv ltac:(w3_in)); exact R11|].
    split; [rewrite (HK2 15%bv ltac:(w3_in)); exact R15|].
    split; [rewrite (HK2 16%bv ltac:(w3_in)); exact R16|].
    split; [rewrite Q20, (pp_reg_off _ 20%nat _ (-1) F20); unfold w64; f_equal; lia|].
    split; [rewrite Q21, (pp_reg_off _ 21%nat _ (-1) F21); unfold w64; f_equal; lia|].
    split; [rewrite (HK2 22%bv ltac:(w3_in)); exact R22|].
    split; [rewrite (HK2 23%bv ltac:(w3_in)); exact R23|].
    split; [rewrite Q25, (pp_reg_off _ 25%nat _ (-1) F25); unfold w64; f_equal; lia|].
    rewrite Q26, (pp_reg_off _ 26%nat _ 1 F26). reflexivity.
Qed.

Theorem pp_w3_holds : forall f, rd_seg_L B CTX f -> pp_seg_ST B CTX f -> pp_seg_W3 B CTX f.
Proof.
intros f HL HST cx i d s11 p1 p2 m ly3 S3 W3 regs mem md HB HP.
exact (w3_loop f HL HST _ cx i d s11 p1 p2 m ly3 S3 W3 regs mem md eq_refl HB HP).
Qed.
End c.

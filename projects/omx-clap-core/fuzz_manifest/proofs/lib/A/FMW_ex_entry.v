(* G4.ExEntry: ex_seg_entry (FMW_ex_base.v:163). expected 0x81130 from its entry: prologue (sp -= 208, ra/s0..s11 saved
   at F+200..F+104), s1 = uri, s9 = the shadow base (GOT 0x999b0 -> 0xa1d78), s7 = text, strlen (uri); n = 0 returns 0
   at EX_R; else s2 = n and strchr (text, '<'): no '<' goes to the scan's setup EX_MS, a '<' at j enters ex_whole's loop
   at EX_WL (FMW_ex_entry_wl.v, _b.v, _s.v, by strong induction on |text| - j); the setup reaches EX_L
   (FMW_ex_entry_ms.v) and the continuation of ex_seg_entry. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_entry_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
  FMW_ex_entry_ms FMW_ex_entry_s FMW_ex_entry_b FMW_ex_entry_wl.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* expected's entry: the stack below sp (208 bytes of frame), the GOT slot and the shadow-base cell (FMW_plain.v ss_P0) *)
Definition ee_E0_facts : facts := mkFacts [(2%nat, EE_SP); (32%nat, mkAF FW_SB FW_SB 0)] [] [].
Definition ss_E0 : sstate := mkSS A_expected sr_atoms [fw_stack 208; fw_got; fw_cell 32] None ee_E0_facts.

(* run-to-run memory bookkeeping: the frame of a run whose regions have no write window *)
Ltac ee_fr W lo hi :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let K := fresh "KR" in
    pose proof (ee_kept_nowin _ _ W lo hi m0 m1 HFr ltac:(vm_compute; reflexivity)) as K end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Let CELLS : fw_cells B := conj (tl_got_shadow B TL) (tl_shadow_cell B TL).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Lemma ee_cfg : forall (W : world tfibsegs) pc regs mem md Q,
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.


Lemma ee_E0_entry : forall ly S W regs mem md ch,
  afn_pre tfibsegs B STK_expected ly S W regs mem md ch ->
  st_ok tfibsegs (Ereg regs [Z_to_bv 64 FW_SB]) ss_E0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_expected) mem (seg_rom tfibsegs))).
Proof.
  intros ly S W regs mem md ch HPRE.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct CELLS as [HBgot HBcell].
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs [Z_to_bv 64 FW_SB]).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 FW_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (HSTK : STK_expected = 8432) by reflexivity.
  unfold ss_E0. apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 FW_SB]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold fw_stack, fw_got, fw_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
    + cbn [base_val]. unfold FW_GOT. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. rewrite <- (Z.add_0_l 0x999b0) at 1.
      apply (chunk_ok_val tfibsegs E _ 0 0x999b0 8 (SLit FW_CELL) FW_CELL);
        [reflexivity | unfold FW_CELL; zside | zside |].
      exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kgot).
    + cbn [base_val]. unfold FW_CELL. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa1d78) at 1.
      apply (chunk_ok_val tfibsegs E _ 0 0xa1d78 8 (SOff 32 0) FW_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold FW_SB; zside | zside |].
      exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents. unfold fw_stack, fw_got, fw_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
    unfold FW_GOT, FW_CELL.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil Hstk0 C1. clear. intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok ee_E0_facts]. unfold afact_ok, EE_SP. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, !unsigned_lit_small by (unfold FW_SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hstk0 C1 Hal16. clear. unfold FW_SB. intros. repeat split; lia.
Qed.

(* the saved registers survive a change below F + 104 *)
Lemma ee_saved_keep : forall cx W lo hi m m', ex_saved_ok cx W m -> ee_kept W lo hi m m' ->
  hi <= cx_F cx + 104 -> 0 <= cx_F cx -> cx_F cx + 208 <= 2 ^ 64 -> ex_saved_ok cx W m'.
Proof.
  intros cx W lo hi m m' HSV K Hhi H0 H1. unfold ex_saved_ok in *. rewrite Forall_forall in HSV |- *.
  intros s Hs. apply (ee_val_kept W lo hi m m' _ _ _ K); [| | | exact (HSV s Hs)];
    cbv [EX_SAVED In] in Hs; repeat (destruct Hs as [<-|Hs]; [cbn [fst]; lia|]); destruct Hs.
Qed.

(* the loop by strong induction on |text| - j *)
Lemma ee_WL_go : ex_WL_seg B -> forall cx j ly3 S3 W3 regs3 mem3 md3,
  ex_K B cx -> ex_at_WL B cx j ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_WL regs3 mem3 md3) (ex_post B cx).
Proof.
  intros WLG cx.
  assert (G : forall k j ly3 S3 W3 regs3 mem3 md3, (length (cx_tb cx) - j = k)%nat -> ex_K B cx ->
    ex_at_WL B cx j ly3 S3 W3 regs3 mem3 md3 -> SRr tfibsegs W3 (cfg_at tfibsegs EX_WL regs3 mem3 md3) (ex_post B cx)).
  { induction k as [k IH] using lt_wf_ind. intros j ly3 S3 W3 regs3 mem3 md3 Hk HK HW.
    apply (WLG cx j ly3 S3 W3 regs3 mem3 md3 HK); [|exact HW].
    intros j' ly4 S4 W4 regs4 mem4 md4 Hj' HW'.
    pose proof HW' as (_ & Hj'l & _).
    exact (IH (length (cx_tb cx) - j')%nat ltac:(lia) j' ly4 S4 W4 regs4 mem4 md4 eq_refl HK HW'). }
  intros j ly3 S3 W3 regs3 mem3 md3 HK HW. exact (G _ j ly3 S3 W3 regs3 mem3 md3 eq_refl HK HW).
Qed.

Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis STRCHR : astrchr_realizes tfibsegs B PC_strchr.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis SEG_R : ex_seg_R B.
(* the pieces (FMW_ex_entry_ms.v, _s.v, _b.v, _wl.v) *)
Let MSG : ex_MS_seg B := ex_MS_holds B.
Let SG : ex_S_seg B := ex_S_holds B IMG STRCHR MSG.
Let BG : ex_B_seg B := ex_B_holds B SEG_R SG.
Let WLG : ex_WL_seg B := ex_WL_holds B IMG STRNCMP SG BG.

Theorem ex_seg_entry_holds : ex_seg_entry B.
Proof.
  intros cx HB HK. fold (ex_K B cx) in HK.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HB as ((HPRE & HRO) & HGL & Ht & Hu & Ct & Cu & Kt & Ku & Hlen & Htl).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_expected = 8432) by reflexivity.
  assert (HRS : STK_RT_STR = 8192) by reflexivity.
  set (sp0 := spZ (cx_regs cx)) in *.
  assert (HFe : cx_F cx = sp0 - 208) by reflexivity.
  assert (HSP : cx_sp cx = sp0) by reflexivity.
  pose proof (ee_E0_entry (cx_ly cx) (cx_S cx) (cx_W cx) (cx_regs cx) (cx_mem cx) (cx_md cx) (cx_ch cx) HPRE) as HS.
  assert (SHOK : sh_ok tfibsegs EX_Bx [] (Ereg (cx_regs cx) [Z_to_bv 64 FW_SB])
    (mrestrict (w_H (cx_W cx)) (ms_mem (mkst (cx_regs cx) (Z_to_bv 64 A_expected) (cx_mem cx) (seg_rom tfibsegs)))))
    by constructor.
  pose proof (ajournal_init tfibsegs B STK_expected [] _ _ _ _ _ _ _ HPRE) as HJ.
  set (E0 := Ereg (cx_regs cx) [Z_to_bv 64 FW_SB]) in *.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr (cx_regs cx) r)
    by (intros n r Hn; subst E0; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E0 32 = Z_to_bv 64 FW_SB) by (subst E0; exact (ew_Ereg_extra (cx_regs cx) _ 0)).
  assert (Usp : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  unfold cfg_at. change (w64 A_expected) with (Z_to_bv 64 A_expected).
  change (cx_mem cx) with (ms_mem (mkst (cx_regs cx) (Z_to_bv 64 A_expected) (cx_mem cx) (seg_rom tfibsegs))) in HJ at 2.
  (* the prologue to the strlen call *)
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac; try exact Usp. }
  pose proof (fw_win tfibsegs _ _ _ _ _ (sp0 - 208) sp0 HFr) as KE.
  assert (KE1 : ee_kept (cx_W cx) (sp0 - 208) sp0 (cx_mem cx) (ms_mem ms)).
  { intros a Ha Hn. apply KE; [|exact Ha|exact Hn].
    lazymatch goal with |- Forall _ ?rs => let v := eval vm_compute in rs in change rs with v end.
    repeat apply Forall_cons; try apply Forall_nil;
      cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val]; first [left; lia | right; rewrite Usp; lia]. }
  clear KE.
  (* the saved registers, from the frame region of the run *)
  assert (HSV : ex_saved_ok cx (cx_W cx) (ms_mem ms)).
  { lazymatch type of HS with st_ok _ _ ?ss _ =>
      let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
      lazymatch r with Some ?rg =>
        pose proof (fw_region_nth tfibsegs _ ss _ 0 rg HS ltac:(vm_compute; reflexivity)) as HR end end.
    rewrite restrict_mem in HR.
    unfold ex_saved_ok, EX_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (cx_F cx + ?o) 8 (bv_unsigned (getr _ (Z_to_bv 5 ?r))) =>
      let rn := eval vm_compute in (Z.to_nat r) in
      replace (cx_F cx + o) with (sp0 + (o - 208)) by (rewrite HFe; lia);
      apply (fw_field tfibsegs E0 _ 2 sp0 _ _ _ _ _ (o - 208) 8 (SOff rn 0) _ HR Usp);
      [ cbn [In]; repeat (first [left; reflexivity | right])
      | cbn [sv_denot]; rewrite (EE rn (Z_to_bv 5 r) ltac:(vm_compute; reflexivity)), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr (cx_regs cx) (Z_to_bv 5 r))) as R;
        change (bv_modulus 64) with (2 ^ 64) in R; exact R
      | cbn; lia ] end. }
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
  rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  assert (KL1 : fw_low tfibsegs (w_H (cx_W cx)) (cx_mem cx) (ms_mem ms)) by (apply (ee_low _ _ _ _ _ KE1); lia).
  eapply SRr_bind.
  { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strlen STK_RT_STR (fun v => v = Z.of_nat (length (cx_ub cx)))
      (cx_W cx) (ms_regs ms) (ms_mem ms) STK_expected sp0 [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) []
      (cx_ly cx) (cx_S cx) _ 0 (-208) (Z_to_bv 64 0x81184) HJ).
    - unfold spZ at 1. rewrite Rsp. cbn [sv_denot]. rewrite Usp. apply unsigned_lit_small. lia.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - lia.
    - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact Rra.
    - vm_compute. reflexivity.
    - intros HPK. apply (STRLEN (cx_ly cx) (cx_S cx) (cx_W cx) (ms_regs ms) (ms_mem ms) _ (cx_u cx) (cx_ub cx) HPK).
      + exact (proj1 (IMG (cx_ly cx) (cx_S cx) (cx_W cx) (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ (cx_mem cx) _ Hsegs KL1 HRO))).
      + rewrite Ra0, (EE 11%nat 11%bv eq_refl). exact Hu.
      + exact (fw_cstr_low tfibsegs (cx_W cx) (cx_mem cx) _ (cx_u cx) (cx_ub cx) KL1 Cu). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & Hvl & Hfr2 & Hpres2).
  clear Ra0 Rra Rsp Rgp Rtp.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let K := eval vm_compute in (run_K 0 EX_Bx [] ss) in
    jafter_call_keep HS K regs2 (mrestrict (w_H (cx_W cx)) mem2) HP2 (@nil nat) HS2 end.
  match type of HS2 with ?tt -> _ => assert (HK2 : tt) by constructor end.
  specialize (HS2 HK2). clear HK2 HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (HSV2 : ex_saved_ok cx (cx_W cx) mem2)
    by (apply (ee_saved_keep cx (cx_W cx) _ _ (ms_mem ms) mem2 HSV Hfr2); rewrite HFe; lia).
  assert (KM2 : ee_kept (cx_W cx) (sp0 - STK_expected) sp0 (cx_mem cx) mem2)
    by (apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KE1 Hfr2); lia).
  clear KE1 KL1 Hfr2 HSV.
  clear SHOK. lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) =>
    assert (SHOK : sh_ok tfibsegs EX_Bx [] Ex (mrestrict (w_H (cx_W cx)) (ms_mem msx))) by constructor end.
  change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 0x81184) mem2 (seg_rom tfibsegs))) in HJ2.
  clear HJ. rename HJ2 into HJ. clear HP2 Hpres2 ms.
  set (E1 := havoc E0 33 (map (getr regs2) CLOB)) in *.
  assert (E1o : forall k, (k < 33)%nat -> ew E1 k = ew E0 k) by (intros k Hk; apply ew_havoc_old; exact Hk).
  assert (E37 : ew E1 37 = Z_to_bv 64 (Z.of_nat (length (cx_ub cx)))).
  { change 37%nat with (33 + 4)%nat. unfold E1. rewrite (ew_havoc_new E0 33 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
    transitivity (getr regs2 10); [reflexivity|]. rewrite Hv, Hvl. reflexivity. }
  assert (Hn255 : Z.of_nat (length (cx_ub cx)) < 2 ^ 64) by lia.
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  { (* n = 0: return 0 *)
    rewrite branch_eq_U, (U_atom E1 37 (Z.of_nat (length (cx_ub cx))) E37), U_SLit in Hc by lia.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_R; [awr_ok_tac|].
    ee_fr (cx_W cx) (sp0 - STK_expected) (sp0 - 208).
    ee_mk HS. apply ee_cfg.
    apply (SEG_R cx (cx_ly cx) (cx_S cx) _ _ _ _ HB).
    - apply (ee_com_entry B cx _ _ _ HB HJ).
      + apply (ee_low _ (sp0 - STK_expected) sp0); [|lia].
        apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KM2 KR); lia.
      + ee_g HS. rewrite E1o, Usp by lia. rewrite HFe. unfold w64; f_equal; lia.
      + ee_g HS. rewrite E1o by lia. apply EE. reflexivity.
      + ee_g HS. rewrite E1o by lia. apply EE. reflexivity.
      + ee_g HS. rewrite E1o, E32 by lia. reflexivity.
      + apply (ee_saved_keep cx (cx_W cx) _ _ mem2 _ HSV2 KR); rewrite HFe; lia.
    - ee_g HS. unfold cx_res. rewrite ee_names_0 by lia. rewrite E37, Hc. reflexivity. }
  { (* n <> 0: strchr (text, '<') *)
    rewrite branch_eq_U, (U_atom E1 37 (Z.of_nat (length (cx_ub cx))) E37), U_SLit in Hc by lia.
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. rename Hc into Hn0.
    aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan; [awr_ok_tac|].
    ee_fr (cx_W cx) (sp0 - STK_expected) (sp0 - 208).
    rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
    rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
    assert (KM3 : ee_kept (cx_W cx) (sp0 - STK_expected) sp0 (cx_mem cx) (ms_mem ms))
      by (apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KM2 KR); lia).
    assert (KL3 : fw_low tfibsegs (w_H (cx_W cx)) (cx_mem cx) (ms_mem ms)) by (apply (ee_low _ _ _ _ _ KM3); lia).
    eapply SRr_bind.
    { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strchr STK_RT_STR
        (fun v => (v = 0 /\ ~ In 60 (cx_tb cx)) \/ (exists j, first_at (cx_tb cx) 60 j /\ v = cx_t cx + Z.of_nat j))
        (cx_W cx) (ms_regs ms) (ms_mem ms) STK_expected sp0 [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) []
        (cx_ly cx) (cx_S cx) _ 0 (-208) (Z_to_bv 64 0x81198) HJ).
      - unfold spZ at 1. rewrite Rsp. rewrite ?E1o by lia. cbn [sv_denot]. rewrite ?E1o by lia. rewrite Usp.
        apply unsigned_lit_small. lia.
      - reflexivity.
      - lia.
      - unfold ESTACK. lia.
      - lia.
      - rewrite Rgp, ?E1o, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
      - rewrite Rtp, ?E1o, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
      - exact Rra.
      - vm_compute. reflexivity.
      - intros HPK. apply (STRCHR (cx_ly cx) (cx_S cx) (cx_W cx) (ms_regs ms) (ms_mem ms) _ (cx_t cx) 60 (cx_tb cx) HPK).
        + exact (proj1 (IMG (cx_ly cx) (cx_S cx) (cx_W cx) (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ (cx_mem cx) _ Hsegs KL3 HRO))).
        + exact (proj1 (proj2 (IMG (cx_ly cx) (cx_S cx) (cx_W cx) (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ (cx_mem cx) _ Hsegs KL3 HRO)))).
        + rewrite Ra0, ?E1o, (EE 10%nat 10%bv eq_refl) by lia. exact Ht.
        + rewrite Ra1. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
        + lia.
        + exact (fw_cstr_low tfibsegs (cx_W cx) (cx_mem cx) _ (cx_t cx) (cx_tb cx) KL3 Ct). }
    cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v3 & -> & HJ3 & HP3 & Hv3 & Hrg3 & HR3 & Hfr3 & Hpres3).
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let K := eval vm_compute in (run_K 0 EX_Bx [] ss) in
      jafter_call_keep HS K regs3 (mrestrict (w_H (cx_W cx)) mem3) HP3 (@nil nat) HS2 end.
    match type of HS2 with ?tt -> _ => assert (HK2 : tt) by constructor end.
    specialize (HS2 HK2). clear HK2 HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    assert (HSV3 : ex_saved_ok cx (cx_W cx) mem3).
    { apply (ee_saved_keep cx (cx_W cx) (sp0 - STK_expected) (sp0 - 208) mem2 mem3 HSV2); [|rewrite HFe; lia ..].
      apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KR Hfr3); lia. }
    assert (KM4 : ee_kept (cx_W cx) (sp0 - STK_expected) sp0 (cx_mem cx) mem3)
      by (apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KM3 Hfr3); lia).
    clear KM2 KM3 KL3 KR Hfr3 HSV2.
    clear SHOK. lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) =>
      assert (SHOK : sh_ok tfibsegs EX_Bx [] Ex (mrestrict (w_H (cx_W cx)) (ms_mem msx))) by constructor end.
    change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 0x81198) mem3 (seg_rom tfibsegs))) in HJ3.
    clear HJ. rename HJ3 into HJ. clear HP3 Hpres3 Ra0 Ra1 Rra Rsp Rgp Rtp ms.
    set (E2 := havoc E1 49 (map (getr regs3) CLOB)) in *.
    assert (E2o : forall k, (k < 49)%nat -> ew E2 k = ew E1 k) by (intros k Hk; apply ew_havoc_old; exact Hk).
    assert (E53 : ew E2 53 = Z_to_bv 64 v3).
    { change 53%nat with (49 + 4)%nat. unfold E2. rewrite (ew_havoc_new E1 49 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
      transitivity (getr regs3 10); [reflexivity|]. exact Hv3. }
    pose proof Ct as (_ & Ht4 & Htc & _).
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    { (* no '<': the setup *)
      rewrite branch_eq_U, (U_atom E2 53 v3 E53 Hrg3), U_SLit in Hc.
      change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. subst v3.
      destruct HR3 as [(_ & Hni) | (j & Hj & Hv0)]; [|lia].
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_MS; [awr_ok_tac|].
      ee_fr (cx_W cx) (sp0 - STK_expected) (sp0 - 208).
      ee_mk HS. apply ee_cfg.
      apply (MSG cx (cx_ly cx) (cx_S cx) _ _ _ _ HK). split.
      - split; [exact HB|]. split.
        { apply (ee_com_entry B cx _ _ _ HB HJ).
          - apply (ee_low _ (sp0 - STK_expected) sp0); [|lia].
            apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KM4 KR); lia.
          - ee_g HS. rewrite ?E2o, ?E1o, Usp by lia. rewrite HFe. unfold w64; f_equal; lia.
          - ee_g HS. rewrite ?E2o, ?E1o by lia. apply EE. reflexivity.
          - ee_g HS. rewrite ?E2o, ?E1o by lia. apply EE. reflexivity.
          - ee_g HS. rewrite ?E2o, ?E1o, E32 by lia. reflexivity.
          - apply (ee_saved_keep cx (cx_W cx) _ _ mem3 _ HSV3 KR); rewrite HFe; lia. }
        split; [lia|].
        split; [ee_g HS; rewrite ?E2o, ?E1o by lia; rewrite (EE 11%nat 11%bv eq_refl); exact Hu|].
        split; [ee_g HS; rewrite ?E2o, ?E1o by lia; rewrite E37; reflexivity|].
        ee_g HS; rewrite ?E2o, ?E1o by lia; rewrite (EE 10%nat 10%bv eq_refl); exact Ht.
      - apply (ee_whole_false _ _ 0); [intros k Hk; lia|].
        intros k Hk. exact (ee_not_in _ _ Hni k ltac:(lia)). }
    { (* a '<' at j: ex_whole's loop *)
      rewrite branch_eq_U, (U_atom E2 53 v3 E53 Hrg3), U_SLit in Hc.
      change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
      destruct HR3 as [(Hv0 & _) | (j & Hj & Hv0)]; [lia|]. subst v3.
      pose proof Hj as (Hjl & Hj60 & _).
      aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_WL; [awr_ok_tac|].
      ee_fr (cx_W cx) (sp0 - STK_expected) (sp0 - 208).
      ee_mk HS. apply ee_cfg.
      apply (ee_WL_go WLG cx j (cx_ly cx) (cx_S cx) _ _ _ _ HK). split.
      - split; [exact HB|]. split.
        { apply (ee_com_entry B cx _ _ _ HB HJ).
          - apply (ee_low _ (sp0 - STK_expected) sp0); [|lia].
            apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KM4 KR); lia.
          - ee_g HS. rewrite ?E2o, ?E1o, Usp by lia. rewrite HFe. unfold w64; f_equal; lia.
          - ee_g HS. rewrite ?E2o, ?E1o by lia. apply EE. reflexivity.
          - ee_g HS. rewrite ?E2o, ?E1o by lia. apply EE. reflexivity.
          - ee_g HS. rewrite ?E2o, ?E1o, E32 by lia. reflexivity.
          - apply (ee_saved_keep cx (cx_W cx) _ _ mem3 _ HSV3 KR); rewrite HFe; lia. }
        split; [lia|].
        split; [ee_g HS; rewrite ?E2o, ?E1o by lia; rewrite (EE 11%nat 11%bv eq_refl); exact Hu|].
        split; [ee_g HS; rewrite ?E2o, ?E1o by lia; rewrite E37; reflexivity|].
        ee_g HS; rewrite ?E2o, ?E1o by lia; rewrite (EE 10%nat 10%bv eq_refl); exact Ht.
      - split; [exact Hjl|]. split; [exact Hj60|].
        split.
        { intros k Hk. apply expected_m.whole_at_not_lt. unfold ManifestModel.byte_at.
          exact (ee_first_before _ _ _ Hj k Hk). }
        split; [ee_g HS; rewrite E53; reflexivity|].
        ee_g HS. first [reflexivity | apply bv_eq; vm_compute; reflexivity]. } }
Qed.
End W.

Print Assumptions ex_seg_entry_holds.

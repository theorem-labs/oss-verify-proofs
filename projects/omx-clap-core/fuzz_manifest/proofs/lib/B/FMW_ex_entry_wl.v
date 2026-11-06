(* G4.ExEntry, IMAGE B: ex_whole's loop head EX_WL 0x812f8 (fuzz_manifest.c:118-119): s4 = r + 1 (r = s3, a '<' of
   text), strncmp (r + 1, uri = s5, n = s6) at 0x81308; nonzero goes to EX_S 0x81334 (no "<uri>" at r), zero passes the
   UBSan guard 0x81314 (K2: not a0, s3; bltu a0, s0 with s0 = n + 1, the trap arm needs r + n + 1 >= 2^64, impossible
   for r + 1 + n inside text) to EX_B 0x8131c with a0 = r + 1 + n (the uri's bytes follow r). B twin of
   lib/A/FMW_ex_entry_wl.v (06d82004dc3). ex_WL_seg (FMW_ex_entry_kit.v). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_entry_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition ss_WL : sstate := mkSS EX_WL sr_atoms [] None (mkFacts [] [] []).

(* FMW_ex_entry.v ee_fr *)
Ltac ewl_fr W lo hi :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let K := fresh "KR" in
    pose proof (ee_kept_nowin _ _ W lo hi m0 m1 HFr ltac:(vm_compute; reflexivity)) as K end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
(* a register of the symbolic state, as an sv (no cbn): for the U-level lemmas *)
Ltac ewl_r HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      rewrite (st_ok_restrict_reg segs H E ss ms r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis SG : ex_S_seg B.
Hypothesis BG : ex_B_seg B.

Lemma ewl_cfg : forall (W : world tfibsegs) pc regs mem md Q,
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

Lemma ewl_entry : forall (W : world tfibsegs) mem regs3,
  st_ok tfibsegs (Ereg regs3 []) ss_WL (restrict (w_H W) (mkst regs3 (Z_to_bv 64 EX_WL) mem (seg_rom tfibsegs))).
Proof.
  intros W mem regs3. rewrite restrict_mkst_fx. unfold ss_WL. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. first [exact I | constructor].
Qed.

Theorem ex_WL_holds : ex_WL_seg B.
Proof.
  intros cx j ly3 S3 W3 regs3 mem3 md3 HK HWF ((HB & HC & Hn & R21 & R22 & V78) & Hj & Hj60 & Hbf & R19 & HWR).
  pose proof HWR as (R8 & R9 & R18).
  pose proof (AR_laws_ok tfibsegs B) as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ee_base_facts B cx HB) as (Hal & Hsp & Hsp47 & Hgp & Htp).
  assert (HSTK : STK_expected = 8464) by reflexivity. assert (HRS : STK_RT_STR = 8192) by reflexivity.
  pose proof HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  pose proof Ct as ((_ & Htnz) & Ht4 & Htc & _). pose proof Cu as ((_ & Hunz) & Hu4 & Huc & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen & _).
  assert (HCUT : ex_cut B cx ly3 S3 W3 regs3 mem3 md3)
    by exact (conj HB (conj HC (conj Hn (conj R21 (conj R22 V78))))).
  assert (HFe : cx_F cx = cx_sp cx - 240) by reflexivity.
  assert (Hnd : cx_n cx = Z.of_nat (length (cx_ub cx))) by reflexivity.
  pose proof (ewl_entry W3 mem3 regs3) as HS.
  set (E := Ereg regs3 []) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hnq; subst E; apply ew_Ereg_nat; exact Hnq).
  assert (SHOK : sh_ok tfibsegs EE_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_WL) mem3 (seg_rom tfibsegs))))) by constructor.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_WL) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_WL) with (Z_to_bv 64 EX_WL).
  (* to strncmp (r + 1, uri, n) *)
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  ewl_fr W3 (cx_sp cx - STK_expected) (cx_F cx).
  rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2.
  rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
  assert (KL1 : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms)) by (apply (ee_low _ _ _ _ _ KR); lia).
  pose proof (ee_cstr_suffix W3 mem3 (cx_t cx) (cx_tb cx) (S j) ltac:(lia) Ct) as Ct1.
  eapply SRr_bind.
  { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strncmp STK_RT_STR
      (fun v => v = 0 <-> strn_eq (Z.to_nat (cx_n cx)) (skipn (S j) (cx_tb cx)) (cx_ub cx))
      W3 (ms_regs ms) (ms_mem ms) STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) []
      ly3 S3 _ 0 (-240) (Z_to_bv 64 0x8130c) HJ).
    - unfold spZ at 1. rewrite Rsp, (EE 2%nat 2%bv eq_refl), R2. unfold w64.
      rewrite unsigned_lit_small by (rewrite HFe; lia). rewrite HFe. lia.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - lia.
    - rewrite Rgp, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
    - rewrite Rtp, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
    - exact Rra.
    - vm_compute. reflexivity.
    - intros HPK. apply (STRNCMP ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (cx_t cx + Z.of_nat (S j)) (cx_u cx) (cx_n cx)
        (skipn (S j) (cx_tb cx)) (cx_ub cx) HPK).
      + exact (proj1 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ mem3 _ Hsegs KL1 HRO))).
      + exact (proj1 (proj2 (IMG ly3 S3 W3 (ms_mem ms) _ (proj1 HJ) (fw_rodata_low tfibsegs B _ mem3 _ Hsegs KL1 HRO)))).
      + rewrite Ra0, (EE 19%nat 19%bv eq_refl), R19. unfold w64. rewrite unsigned_lit_small by lia.
        f_equal; lia.
      + rewrite Ra1, (EE 21%nat 21%bv eq_refl). exact R21.
      + rewrite Ra2, (EE 22%nat 22%bv eq_refl). exact R22.
      + unfold cx_n. lia.
      + exact (fw_cstr_low tfibsegs W3 mem3 _ _ _ KL1 Ct1).
      + exact (fw_cstr_low tfibsegs W3 mem3 _ _ _ KL1 Cu). }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & v & -> & HJ4 & HP4 & Hv & Hrg & HR & Hfr4 & Hpres4).
  clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let K := eval vm_compute in (run_K 0 EE_Bx [] ss) in
    jafter_call_keep HS K regs4 (mrestrict (w_H W3) mem4) HP4 (@nil nat) HS2 end.
  match type of HS2 with ?tt -> _ => assert (HK2 : tt) by constructor end.
  specialize (HS2 HK2). clear HK2 HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (KM : ee_kept W3 (cx_sp cx - STK_expected) (cx_F cx) mem3 mem4)
    by (apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KR Hfr4); rewrite ?HFe; lia).
  clear KR KL1 Hfr4.
  clear SHOK. lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) =>
    assert (SHOK : sh_ok tfibsegs EE_Bx [] Ex (mrestrict (w_H W3) (ms_mem msx))) by constructor end.
  change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 0x8130c) mem4 (seg_rom tfibsegs))) in HJ4.
  clear HJ. rename HJ4 into HJ. clear HP4 Hpres4 ms.
  set (E1 := havoc E 32 (map (getr regs4) CLOB)) in *.
  assert (E1o : forall k, (k < 32)%nat -> ew E1 k = ew E k) by (intros k Hk; apply ew_havoc_old; exact Hk).
  assert (E36 : ew E1 36 = Z_to_bv 64 v).
  { change 36%nat with (32 + 4)%nat. unfold E1. rewrite (ew_havoc_new E 32 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
    transitivity (getr regs4 10); [reflexivity|]. exact Hv. }
  assert (U19 : U E1 (SOff 19 0) = cx_t cx + Z.of_nat j).
  { apply U_atom; [rewrite E1o by lia; rewrite (EE 19%nat 19%bv eq_refl); exact R19 | lia]. }
  assert (U8 : U E1 (SOff 8 0) = cx_n cx + 1).
  { apply U_atom; [rewrite E1o by lia; rewrite (EE 8%nat 8%bv eq_refl); exact R8 | lia]. }
  unfold cx_n in HR. rewrite Nat2Z.id in HR.
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  { (* strncmp <> 0: no "<uri>" at r *)
    rewrite branch_ne_U, (U_atom E1 36 v E36 Hrg), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hb1 : ex_before cx (S j)).
    { intros k Hk. destruct (Nat.eq_dec k j) as [->|Hkj]; [|apply Hbf; lia].
      apply ee_whole_at_firstn. apply (ee_strn_false (length (cx_ub cx))); [reflexivity|].
      intros Hs. apply Hc. apply HR. exact Hs. }
    clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_S; [awr_ok_tac|].
    ewl_fr W3 (cx_sp cx - STK_expected) (cx_F cx).
    ee_mk HS. apply ewl_cfg.
    apply (SG cx j ly3 S3 W3 _ _ _ HK HWF).
    split.
    - apply (ee_cut_keep B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HCUT HJ);
        [apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KM KR); lia | ..];
        ee_g HS; rewrite ?E1o by lia; apply EE; reflexivity.
    - split; [exact Hj|]. split; [exact Hb1|]. split.
      + ee_g HS. rewrite ?E1o by lia. rewrite (EE 19%nat 19%bv eq_refl), R19. unfold w64.
        rewrite unsigned_lit_small by lia. f_equal; lia.
      + apply (ee_wregs_keep cx regs3 _ HWR); ee_g HS; rewrite ?E1o by lia; apply EE; reflexivity. }
  { (* strncmp = 0: the uri follows r *)
    rewrite branch_ne_U, (U_atom E1 36 v E36 Hrg), U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    destruct (ee_strn_true (length (cx_ub cx)) _ _ eq_refl Hunz (proj1 HR Hc)) as [Hle Hfst].
    rewrite length_skipn in Hle.
    clear Hc.
    (* guard 0x81314 (K2): the trap arm needs ~r <u n + 1, i.e. r + n + 1 >= 2^64 *)
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_G2; [awr_ok_tac|].
    ewl_fr W3 (cx_sp cx - STK_expected) (cx_F cx).
    assert (KM' : ee_kept W3 (cx_sp cx - STK_expected) (cx_F cx) mem3 (ms_mem ms))
      by (apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KM KR); lia).
    clear KM KR. rename KM' into KM.
    srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
    { match goal with HT : branch_taken _ _ _ = true |- _ => fm_kill_trap HT end. }
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_B; [awr_ok_tac|].
    ewl_fr W3 (cx_sp cx - STK_expected) (cx_F cx).
    ee_mk HS. apply ewl_cfg.
    apply (BG cx j ly3 S3 W3 _ _ _ HK HWF).
    split.
    - apply (ee_cut_keep B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HCUT HJ);
        [apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KM KR); lia | ..];
        ee_g HS; rewrite ?E1o by lia; apply EE; reflexivity.
    - split; [lia|]. split; [exact Hj60|]. split; [exact Hfst|]. split; [exact Hbf|]. split.
      + ewl_r HS. unfold w64. apply fw_sv_U.
        first [ rewrite (U_add2 E1 _ _) by (rewrite ?U19, ?U8; lia); rewrite ?U19, ?U8; lia
              | rewrite U_add_off_atom; [rewrite ?E1o by lia; rewrite (EE 19%nat 19%bv eq_refl), (EE 8%nat 8%bv eq_refl),
                  R19, R8; unfold w64; rewrite !unsigned_lit_small by lia; lia | ..];
                rewrite ?E1o by lia; rewrite ?(EE 19%nat 19%bv eq_refl), ?(EE 8%nat 8%bv eq_refl), ?R19, ?R8;
                unfold w64; rewrite ?unsigned_lit_small by lia; unfold M64; lia ].
      + split.
        * ee_g HS. rewrite ?E1o by lia. rewrite (EE 19%nat 19%bv eq_refl), R19. unfold w64.
          rewrite unsigned_lit_small by lia. f_equal; lia.
        * apply (ee_wregs_keep cx regs3 _ HWR); ee_g HS; rewrite ?E1o by lia; apply EE; reflexivity. }
Qed.
End W.

Print Assumptions ex_WL_holds.

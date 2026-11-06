(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_scanner_get_token.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_scanner_get_token H_vfm_A.
Import ListNotations.
Open Scope Z_scope.

Notation ERRNO_A := 0x5e68cc%Z.

Lemma tok_cstrA : forall m A bs (cur len : Z),
  bytes_at asegs m A bs -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> (0 <= cur <= len)%Z ->
  bytes_at asegs m (A + cur) (firstn (Z.to_nat (len - cur)) (skipn (Z.to_nat cur) bs) ++ [Z_to_bv 8 0]).
Proof.
  intros m A bs cur len B N HC. assert (L : (Z.to_nat len < length bs)%nat) by (apply nth_error_Some; rewrite N; discriminate).
  rewrite <- (firstn_skipn (Z.to_nat cur) bs) in B. apply bytes_at_app in B. destruct B as [_ B].
  rewrite firstn_length, Nat.min_l, Z2Nat.id in B by lia.
  rewrite <- (firstn_skipn (Z.to_nat (len - cur)) (skipn (Z.to_nat cur) bs)) in B. rewrite skipn_skipn in B.
  replace (Z.to_nat (len - cur) + Z.to_nat cur)%nat with (Z.to_nat len) in B by lia.
  destruct (skipn (Z.to_nat len) bs) as [|z rest] eqn:SK.
  { exfalso. apply (f_equal (@length byte)) in SK. rewrite skipn_length in SK. cbn in SK. lia. }
  assert (Hz : z = Z_to_bv 8 0).
  { rewrite <- (firstn_skipn (Z.to_nat len) bs) in N. rewrite nth_error_app2 in N by (rewrite firstn_length; lia).
    rewrite firstn_length, Nat.min_l, Nat.sub_diag, SK in N by lia. cbn in N. congruence. }
  subst z. change (?f ++ Z_to_bv 8 0 :: rest) with (f ++ [Z_to_bv 8 0] ++ rest) in B. rewrite app_assoc in B.
  apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

Lemma sub_fp_in : forall (W : list ivl) a b c d, In (c, d) W -> c <= a -> b <= d -> sub_fp [(a, b)] W.
Proof. intros W a b c d HI H1 H2 x O. cbn [outside]. split; [| exact I]. pose proof (outside_In W c d x HI O). lia. Qed.
Lemma sub_fp_cons1 : forall (iv : ivl) (L W : list ivl), sub_fp [iv] W -> sub_fp L W -> sub_fp (iv :: L) W.
Proof. intros [a b] L W H1 H2 x O. cbn [outside]. split; [exact (proj1 (H1 x O))| exact (H2 x O)]. Qed.
Lemma sub_fp_nil : forall W : list ivl, sub_fp [] W.
Proof. intros W x _. exact I. Qed.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Section VF.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (Wx : list ivl) (FMT flen : Z).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis VOK : vf_okA FI q lo S MB A len cap cur0 bs st Wx.
  Hypothesis RF0 : RFAKE FI st m0.

  Notation F := (vF FI st). Notation FL := (vFL FI st). Notation st1 := (vst1 FI st). Notation SF := (vSF FI st).
  Notation WV := ((S + 8, S + 16) :: Wx)%Z.
  Notation W0 := ((lo, q) :: FSIV WV)%Z.
  Notation SHC := (vSHC S). Notation SHE := (vSHE S).
  Notation vrest := (vrest FI q lo S st Wx ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
  Notation vscr := (vscr FI S cur0 st). Notation vtok := vtok.
  Notation vinv := (vinv FI q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
  Notation headstA := (headstA FI q S st gp tp F_ fc). Notation contstA := (contstA FI q S st gp tp F_ fc). Notation errstA := (errstA FI q S st gp tp F_ fc).
  Notation WL := (vWL lo S Wx).
  Notation WP := (vWP lo S).

  Local Notation lb_in_fs := (H_vfm_A.lb_in_fs FI st m0 RF0).
  Local Notation sub_app_iv_fs := (H_vfm_A.sub_app_iv_fs FI).
  Local Notation Wx_app := (H_vfm_A.Wx_app FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation WV_app := (H_vfm_A.WV_app FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation WV_fsout := (H_vfm_A.WV_fsout FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation W0_fsw := (H_vfm_A.W0_fsw FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation S_al := (H_vfm_A.S_al FI q lo S MB A len cap cur0 bs st Wx VOK).
  Local Notation MB_al := (H_vfm_A.MB_al FI q lo S MB A len cap cur0 bs st Wx VOK).
  Local Notation prologueV := (H_vfm_A.prologueV FI STACK_MALLOC_1 q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation Wx_below := (H_vfm_A.Wx_below FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation Wx_apart_new := (H_vfm_A.Wx_apart_new FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation Wx_fk := (H_vfm_A.Wx_fk FI st Wx).
  Local Notation vrest_step := (H_vfm_A.vrest_step FI q lo S MB A len cap cur0 bs st Wx ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 VOK RF0).
  Local Notation WL_app := (H_vfm_A.WL_app FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation WL_env := (H_vfm_A.WL_env FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation vinv_step := (H_vfm_A.vinv_step FI q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 VOK RF0).
  Local Notation shz_stepV := (H_vfm_A.shz_stepV FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation shw_stepV := (H_vfm_A.shw_stepV FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation contV := (H_vfm_A.contV FI q S st gp tp F_ fc).
  Local Notation pctV := (H_vfm_A.pctV FI q S cur0 st gp tp F_ fc).
  Local Notation sgt_callV := (H_vfm_A.sgt_callV IC FI q lo S MB A len cap cur0 bs st Wx F_ fc VOK).
  Local Notation tok_shw := (H_vfm_A.tok_shw FI q lo S MB A len cap cur0 bs st Wx VOK).
  Local Notation dir_cV := (H_vfm_A.dir_cV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation dir_wV := (H_vfm_A.dir_wV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation dir_tabV := (H_vfm_A.dir_tabV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation dir_iV := (H_vfm_A.dir_iV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation WL_out := (H_vfm_A.WL_out lo S Wx).
  Local Notation dir_sV := (H_vfm_A.dir_sV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation nth_bsA := (H_vfm_A.nth_bsA FI q lo S MB A len cap cur0 bs st Wx VOK).
  Local Notation dir_litV := (H_vfm_A.dir_litV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation sp_incV := (H_vfm_A.sp_incV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK).
  Local Notation sp_restoreV := (H_vfm_A.sp_restoreV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation sp_loopV := (H_vfm_A.sp_loopV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation dir_spV := (H_vfm_A.dir_spV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation out_facts := (H_vfm_A.out_facts FI q lo S MB A len cap cur0 bs st Wx m0 VOK RF0).
  Local Notation L_loopV := (H_vfm_A.L_loopV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation dir_LV := (H_vfm_A.dir_LV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation S_exit_errV := (H_vfm_A.S_exit_errV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation S_exit_okV := (H_vfm_A.S_exit_okV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation S_bodyV := (H_vfm_A.S_bodyV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation S_loopV := (H_vfm_A.S_loopV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation dir_SV := (H_vfm_A.dir_SV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation R_failV := (H_vfm_A.R_failV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation R_okV := (H_vfm_A.R_okV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation R_trimV := (H_vfm_A.R_trimV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation R_doneV := (H_vfm_A.R_doneV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation R_loopV := (H_vfm_A.R_loopV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation dir_RV := (H_vfm_A.dir_RV IC FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation epiV := (H_vfm_A.epiV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Local Notation errV := (H_vfm_A.errV FI q lo S MB A len cap cur0 bs st Wx FMT flen ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 VOK RF0).
  Ltac vokA V := destruct V as (CLO & LO & AL16 & QHI & MBLO & MBS & SHI & SAL & MBAL & PLB & A0 & AHI & LBS & CAP & ACAP & CUR0 & TXP & TFS & TBAND & WXL & WXT & WXP).

  Ltac open_vinv INV :=
    destruct INV as (ST & (j0 & w8 & w16 & SCR) & (j136 & tyA & tbA & tlA & j160 & tyB & tbB & tlB & TOK) & SC & MBC & BUF & MI & AE & SHS & SHMB & SHA & SHSEP & SHFMT & SHZ & CR & (QB & QAL) & VR);
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC; hide QAL.
  Ltac joinB q' :=
    match goal with TYB : rw_cells asegs ?m (q' + 164)%Z _, TKB : rw_cells asegs ?m (q' + 168)%Z _ |- _ => let J1 := fresh "J1" in join_chunks TYB TKB J1 end;
    match goal with TKP : rw_cells asegs ?m (q' + 136)%Z _, J1 : rw_cells asegs ?m (q' + 164)%Z _ |- _ => let TOK := fresh "TOK" in join_chunks TKP J1 TOK end.

  Ltac post_callK segs m MUk WMk :=
    let ms' := fresh "ms'" in let PO := fresh "POST" in
    intros ms' PO; destruct_exs PO;
    let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
    destruct PO as [E [MUc [WMc PO]]];
    first [ destruct PO as [MIc PO] | rename PO into MIc ];
    subst ms';
    pose proof MUc as MUk; pose proof WMc as WMk; hide MUk; hide WMk;
    lazymatch type of MUc with
    | munch _ m ?m' => transport_after_call segs m m' MUc WMc; clear MUc WMc; try match goal with H : mem_inv segs m |- _ => clear H end
    end;
    try destruct_ands PO;
    try (lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end).

  Ltac trH H DJ MU WM := unhide H;
    lazymatch type of H with rw_cells ?sg ?ma ?A ?cs =>
      lazymatch type of MU with munch ?W ma ?mb =>
        let H' := fresh in
        assert (H' : rw_cells sg mb A cs)
          by (apply (rw_cells_transport sg W ma mb A cs H MU WM); eapply ATac.disjoint_from_sub; [exact DJ| clear; lia| clear; simpl_sizes; lia]);
        clear H; rename H' into H end end.

  #[using="m0 RF0"] Lemma shw_fkeepV : forall W m m' X n,
    shw m X n -> fkeep FI W st m m' -> lb (fs_live FI st) X n ->
    (forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside W a) -> shw m' X n.
  Proof.
    intros W m m' X n SW FK (g & Hg & G1 & G2) OUT.
    pose proof (live_num FI st m0 RF0) as LN. rewrite Forall_forall in LN.
    destruct (LN g Hg) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4 & F5).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (SB_mod8 (ff_class g)) as S8. change (SB_of (ff_class g)) with (ff_shsize g) in S8.
    assert (ESG : sh (ff_addr g) = ff_addr g / 8 + 2147450880) by reflexivity.
    eapply (shw_band_eq m m' X n (sh (ff_addr g)) (sh (ff_addr g) + ff_shsize g) SW).
    - intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (FK a _ _ _) Hv).
      + rewrite ESG in Ha. clear - Ha L1 L2 L6 F1 F2 ACR L7. Z.div_mod_to_equations. lia.
      + exists g. split; [exact Hg|]. right; left. exact Ha.
      + apply OUT. lia.
    - rewrite ESG. clear - L1 F1. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L1 L2 L6 L7 F1 F2 ACR. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L3. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L3 S8. Z.div_mod_to_equations. lia.
    - apply sh_mono. exact G1.
    - intros Hn. rewrite ESG. unfold sh, SHADOW_OFF. clear - G1 G2 L3 L6 Hn. Z.div_mod_to_equations. lia.
  Qed.

  Definition vWLX (q' : Z) : list ivl := ((lo, q' + 184) :: (F + 32, F + 40) :: (SF + 4, SF + 5) :: WV)%Z.

  Definition vWPX (q' P : Z) : list ivl :=
    [(lo, q' + 184); (S + 8, S + 16); (P, P + 4); (ERRNO_A, ERRNO_A + 4); (F + 32, F + 40); (SF + 4, SF + 5)]%Z.
  Notation WLX := vWLX.

  #[using="q S MB A len cap cur0 bs Wx m0 VOK RF0"] Lemma xframe_facts :
    FSB FI + 36864 <= F /\ F + 128 <= FSB FI + A0_FS_SIZE /\ F mod 64 = 0 /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + 36864
    /\ 8 * (SF - 2147450880) = F
    /\ sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE /\ SF + 16 <= lo /\ 0 <= SF /\ sh (FSB FI) + A0_FS_SHSIZE <= lo
    /\ (FL + 1 <= SF \/ SF + 16 <= FL) /\ (F + 128 <= SF \/ SF + 16 <= F).
  Proof.
    pose proof VOK as VOK'. vokA VOK'. clear TXP TFS TBAND WXT WXP WXL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI. clear APART.
    assert (SFB : 8 * (SF - 2147450880) = F) by (unfold vSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (SHB8 : 8 * (sh (FSB FI) - 2147450880) = FSB FI) by (unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia).
    split; [exact FLO|]. split; [exact FHI|]. split; [exact FAL|]. split; [exact FLLO|]. split; [exact FLHI|]. split; [exact SFB|].
    clear - SFB SHB8 FLO FHI FLLO FLHI FSB1 FSB2 FSB5 ACR CLO. lia.
  Qed.
  #[using="Type"] Lemma WLX_sub : forall q' P m m', In (P, P + 4) Wx -> In (ERRNO_A, ERRNO_A + 4) Wx -> munch (vWPX q' P) m m' -> munch (WLX q') m m'.
  Proof.
    intros q' P m m' PIN EIN MU. eapply munch_weaken; [| exact MU]. unfold vWLX, vWPX. intros x O. cbn [outside] in *.
    destruct O as (O1 & O2 & O3 & O4 & O5). split; [exact O1|]. split; [exact O4|].
    split; [exact (outside_In Wx P (P + 4) x PIN O5)|]. split; [exact (outside_In Wx ERRNO_A (ERRNO_A + 4) x EIN O5)|]. split; [exact O2|]. split; [exact O3| exact I].
  Qed.

  Definition vshadow : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  #[using="MB A len cap cur0 bs VOK RF0"] Lemma vrest_stepX : forall q' m m' (e' : word), vrest q' m -> munch (WLX q') m m' -> wmono asegs m m' ->
    rw_cells asegs m' (F + 32) [C8 e'] -> rw_cells asegs m' SF vshadow -> vrest q' m'.
  Proof.
    intros q' m m' e' (Hq & GAP & FRhi & FH & (e & j & FT1) & FT2 & SHF & FLG & MU & WM & FK & RF & LIVE1) MUL WML FE' SHF'.
    pose proof VOK as VOK'. vokA VOK'. clear TXP TFS TBAND WXT WXP.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & _).
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & APART).
    cbn [FB_of SB_of] in APART.
    assert (QB : q + -304 <= q' <= q + -288) by (clear - Hq; lia). hide Hq.
    assert (PC8 : lb (fs_live FI st) (S + 8) 8) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PC8 APART) as P1.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PC8 ltac:(lia) ltac:(lia)) as P2.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PC8 FLLO FLHI) as P3.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    assert (DJS : forall a n, q' + 184 <= a -> 0 <= n -> disjoint_from (WLX q') a n).
    { intros a n Ha Hn. unfold vWLX. cbn [disjoint_from]. split; [right; lia|]. split; [right; clear - Ha QB LO CLO FHI FSB2; lia|]. split; [right; clear - Ha QB LO SH3; lia|].
      split; [right; lia|]. apply Wx_below; lia. }
    assert (DJF : forall a n, (F <= a /\ a + n <= F + 32) \/ (F + 40 <= a /\ a + n <= F + 128) \/ (a = FL /\ n = 1) -> disjoint_from (WLX q') a n).
    { intros a n HP. unfold vWLX. cbn [disjoint_from]. split; [left; clear - HP FHI FSB2 CLO FLHI; lia|].
      split; [clear - HP FLO FLHI; lia|]. split; [clear - HP FLSF FSF; lia|]. split; [clear - HP P1 P3; lia|].
      apply Wx_apart_new. clear - HP. lia. }
    split_chunk FT1 1%nat FE FJ.
    assert (FJ' : rw_cells asegs m' (F + 40) [CB 80 j]).
    { eapply rw_cells_transport; [exact FJ| exact MUL| exact WML| apply DJF; right; left; simpl_sizes; lia]. }
    pose proof FE' as FE2. join_chunks FE2 FJ' FT1'.
    unfold H_vfm_A.vrest. unhide Hq.
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUL| exact WML| apply DJS; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUL| exact WML| apply DJS; [lia| simpl_sizes; lia]]|].
    split; [eapply rw_cells_transport; [exact FH| exact MUL| exact WML| apply DJF; left; simpl_sizes; lia]|].
    split; [exists e', j; exact FT1'|].
    split; [eapply rw_cells_transport; [exact FT2| exact MUL| exact WML| apply DJF; right; left; simpl_sizes; lia]|].
    split; [exact SHF'|].
    split; [eapply rw_cells_transport; [exact FLG| exact MUL| exact WML| apply DJF; right; right; simpl_sizes; lia]|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUL]. unfold vWLX. intros xo Ho. cbn [outside] in *. destruct Ho as (H1 & H2 & H3 & H4).
             split; [clear - H1 QB; lia|]. split; [clear - H2 FLO FHI; lia|]. split; [clear - H3 SH1 SH2; lia| exact H4]. }
    split; [eapply wmono_trans; [exact WM| exact WML]|].
    split. { eapply fkeep_trans; [exact FK|]. eapply (fkeep_of_munch FI WV (WLX q') st st1 m m m' RF LSUB MUL).
             unfold vWLX. apply Forall_cons; [right; left; cbn [fst snd]; clear - QB LO CLO FSB2 SH5; lia|].
             apply Forall_cons. { replace (F + 40) with (F + 32 + 8) by lia. apply (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl). left. cbn [FB_of]. lia. }
             apply Forall_cons. { replace (SF + 5) with (SF + 4 + 1) by lia. apply (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl). right; left. cbn [SB_of]. lia. }
             apply Forall_cons; [left; cbn [inside fst snd]; left; lia|]. apply Wx_fk. }
    split; [| exact LIVE1].
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS.
    unfold ff_size, ff_shsize in LVF, LVS.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _). rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVF, LVS. change (sh F) with SF in LVS.
    eapply (rfake_frame FI st1 m m' (WLX q') RF MUL WML). unfold vWLX.
    apply Forall_cons; [left; cbn [fst snd]; clear - QB LO CLO FSB2 SH5; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; apply (Contracts.lb_sub _ _ _ _ _ LVF); lia|].
    apply Forall_cons; [right; right; cbn [fst snd]; apply (Contracts.ls_sub _ _ _ _ _ LVS); lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; apply (lb_mono (fs_live FI st)); [apply (Contracts.lb_sub _ _ _ _ _ PC8); lia| exact LSUB]|].
    eapply Forall_impl; [| exact WXL]. intros iv [LE [LB|ER]]; [right; left; exact (lb_mono _ _ _ _ LB LSUB)|].
    left. clear - ER FSB1 SH1. unfold sh, SHADOW_OFF in *. split; left; Z.div_mod_to_equations; lia.
  Qed.
  #[using="q MB A len cap cur0 bs m0 VOK RF0"] Lemma WLX_fsw : forall q', Forall (fsw_iv FI) (WLX q').
  Proof.
    intros q'. pose proof VOK as VOK'. vokA VOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    unfold vWLX. apply fsw_cons_app; [apply app_iv_stack; lia|]. apply fsw_cons_app; [apply sub_app_iv_fs; lia|].
    constructor; [right; cbn [fst snd]; lia|].
    eapply Forall_impl; [| exact WV_app]. intros iv H. left. exact H.
  Qed.
  #[using="q MB A len cap cur0 bs m0 VOK RF0"] Lemma WLX_env : forall q', env_safe (WLX q').
  Proof.
    intros q'. pose proof VOK as VOK'. vokA VOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & _).
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    unfold env_safe, vWLX. constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia|].
    constructor; [left; cbn [fst snd]; clear - SH1 FSB1; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia|].
    constructor; [left; cbn [fst snd]; lia|].
    eapply Forall_impl; [| exact WXL]. intros iv [LE [LB|ER]]; [left; destruct (lb_in_fs _ _ LB) as [H1 H2]; lia|].
    do 6 right. left. exact ER.
  Qed.
  #[using="MB A len cap cur0 bs m0 VOK RF0"] Lemma WLX_fkeep : forall q' m m', q + -304 <= q' <= q + -288 -> RFAKE FI st1 m -> (forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) ->
    munch (WLX q') m m' -> fkeep FI WV st m m'.
  Proof.
    intros q' m m' QB RF LSUB MUL. pose proof VOK as VOK'. vokA VOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    eapply (fkeep_of_munch FI WV (WLX q') st st1 m m m' RF LSUB MUL).
    unfold vWLX. apply Forall_cons; [right; left; cbn [fst snd]; clear - QB LO CLO FSB2 SH5; lia|].
    apply Forall_cons. { replace (F + 40) with (F + 32 + 8) by lia. apply (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl). left. cbn [FB_of]. lia. }
    apply Forall_cons. { replace (SF + 5) with (SF + 4 + 1) by lia. apply (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl). right; left. cbn [SB_of]. lia. }
    apply Forall_cons; [left; cbn [inside fst snd]; left; lia|]. apply Wx_fk.
  Qed.

  #[using="VOK RF0"] Lemma vinv_stepX : forall q' cur G cs cur' G' cs' m m' (e' : word),
    vinv q' cur G cs m -> munch (WLX q') m m' -> wmono asegs m m' ->
    stk asegs m' lo q' -> vscr q' G' cs' m' -> vtok q' m' ->
    rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] ->
    rw_cells asegs m' MB (mbuf_cells A len cap) -> bytes_at asegs m' A bs -> mem_inv asegs m' ->
    rw_cells asegs m' (F + 32) [C8 e'] -> rw_cells asegs m' SF vshadow ->
    cur0 <= cur' <= len -> FMT + flen <= 0x609000 ->
    vinv q' cur' G' cs' m'.
  Proof.
    intros q' cur G cs cur' G' cs' m m' e' (ST & SCR & TOK & SC & MBC & BUF & MI & AE & SHS & SHMB & SHA & SHSEP & SHFMT & SHZ & CR & QBA & VR) MUL WML ST' SCR' TOK' SC' MBC' BUF' MI' FE' SHF' CR' FMTHI.
    pose proof (WLX_fsw q') as WF. pose proof VOK as VOK'. vokA VOK'.
    pose proof VR as VR0. destruct VR0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RF & LIVE1).
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (WLX_fkeep q' m m' (proj1 QBA) RF LSUB MUL) as FKs.
    assert (PLS : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
    assert (PLM : lb (fs_live FI st) MB 32) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    unfold H_vfm_A.vinv. repeat (split; [assumption|]).
    split; [exact (asan_env_frame asegs m m' (WLX q') AE MUL WML (WLX_env q'))|].
    split; [exact (shw_fkeepV WV m m' S 24 SHS FKs PLS WV_fsout)|]. split; [exact (shw_fkeepV WV m m' MB 32 SHMB FKs PLM WV_fsout)|].
    split; [intros HL; apply (shw_frame_fs FI (WLX q') m m' A len (SHA HL) MUL WF); clear - TFS LBS; lia|].
    split; [exact (shw_frame_fs FI (WLX q') m m' SEPTAB_A 20 SHSEP MUL WF ltac:(left; unfold SEPTAB_A; lia))|].
    split; [apply (shw_frame_fs FI (WLX q') m m' FMT flen SHFMT MUL WF); left; clear - FMTHI FSB1; lia|].
    split; [exact (shz_stack_fs FI (WLX q') m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q QHI) MUL WF)|].
    split; [exact CR'|]. split; [exact QBA|]. exact (vrest_stepX q' m m' e' VR MUL WML FE' SHF').
  Qed.

  Section ADV.
    Variables (q' P : Z) (m m' : mem).
    Hypothesis QB : q + -304 <= q' <= q + -288.
    Hypothesis PIN : In (P, P + 4) Wx.
    Hypothesis EIN : In (ERRNO_A, ERRNO_A + 4) Wx.
    Hypothesis RFc : RFAKE FI st1 m.
    Hypothesis LIVE1 : fs_live FI st1 = fs_newff FI st 1 :: fs_live FI st.
    Hypothesis MUP : munch (vWPX q' P) m m'.

    #[using="q lo S MB A len cap cur0 bs Wx m0 VOK RF0 q' P QB PIN EIN RFc LIVE1 MUP"] Lemma shw_advX_in : forall X n, lb (fs_live FI st) X n -> shw m X n -> shw m' X n.
    Proof.
      intros X n LB SW.
      assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
      exact (shw_fkeepV WV m m' X n SW (WLX_fkeep q' m m' QB RFc LSUB (WLX_sub q' P m m' PIN EIN MUP)) LB WV_fsout).
    Qed.
    #[using="q lo S MB A len cap cur0 bs st Wx m0 VOK RF0 q' P PIN EIN MUP"] Lemma shw_advX_out : forall X n, (X + n <= FSB FI \/ FSB FI + A0_FS_SIZE <= X) -> shw m X n -> shw m' X n.
    Proof. intros X n OUT SW. exact (shw_frame_fs FI (WLX q') m m' X n SW (WLX_sub q' P m m' PIN EIN MUP) (WLX_fsw q') OUT). Qed.
    #[using="HC FI S MB A len cap cur0 bs st Wx m0 VOK RF0 q' P PIN EIN MUP"] Lemma shz_advX : shz m (sh lo) (sh q) -> shz m' (sh lo) (sh q).
    Proof.
      intros SHZ. pose proof VOK as VOK'. vokA VOK'.
      exact (shz_stack_fs FI (WLX q') m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q QHI) (WLX_sub q' P m m' PIN EIN MUP) (WLX_fsw q')).
    Qed.
  End ADV.

  #[using="q lo S MB A len cap cur0 bs Wx m0 VOK RF0"] Lemma eptr_shw : forall m,
    rw_cells asegs m SF [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                         C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                         C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
                         C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    shw m (F + 32) 8.
  Proof.
    intros m SHF. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    assert (F8 : F mod 8 = 0) by (clear - FAL; Z.div_mod_to_equations; lia).
    change [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      with (shadow_cells [241; 241; 241; 241; 0; 242; 242; 242; 0; 0; 243; 243; 0; 0; 0; 0]) in SHF.
    split; [| split].
    - eapply (accessible_of_chunk m F _ (F + 32) 8 SHF F8); [lia| cbn [length]; lia|].
      intros i Hi H1 H2. cbn [length] in Hi.
      assert (Ei : (i = 4)%nat) by lia. subst i. reflexivity.
    - eapply (sh_readable_of_chunk m F _ (F + 32) 8 SHF); cbn [length]; unfold sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia.
    - unfold win_ok. split; [lia|]. clear - FLO FHI B1 B2 B5 ACR. change (2^47) with 140737488355328. lia.
  Qed.

  Definition xWA (q' : Z) : list ivl := [(lo, q' + 184); (S + 8, S + 16)]%Z.
  Definition xWB (q' : Z) : list ivl := [(lo, q'); (F + 32, F + 32 + 8); (ERRNO_A, ERRNO_A + 4)]%Z.
  #[using="MB len cap cur0 m0 VOK RF0"] Lemma xdj : forall q' P, q + -304 <= q' <= q + -288 -> In (P, P + 4) Wx -> 0x609000 <= P -> 0x609000 <= A ->
    (disjoint_from (xWA q') (F + 32) 88 /\ disjoint_from (xWA q') SF 16 /\ disjoint_from (xWA q') P 4
     /\ disjoint_from (xWA q') ERRNO_A 4 /\ disjoint_from (xWA q') 0xaad68 8 /\ disjoint_from (xWA q') 0x6069b0 8)
    /\ (disjoint_from (xWB q') S 24 /\ disjoint_from (xWB q') P 4 /\ disjoint_from (xWB q') SF 16 /\ disjoint_from (xWB q') A (Z.of_nat (length bs)))
    /\ (disjoint_from [(P, P + 4)] S 24 /\ disjoint_from [(P, P + 4)] (F + 32) 8 /\ disjoint_from [(P, P + 4)] SF 16)
    /\ (disjoint_from [(S + 8, S + 16)] (F + 32) 8 /\ disjoint_from [(S + 8, S + 16)] P 4).
  Proof.
    intros q' P QB PIN PLO ALO. pose proof VOK as VOK'. vokA VOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & APART).
    cbn [FB_of SB_of] in APART.
    assert (LBP : lb (fs_live FI st) P 4).
    { rewrite Forall_forall in WXL. destruct (WXL _ PIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER PLO; lia]. replace (P + 4 - P) with 4 in LB by lia. exact LB. }
    destruct (lb_in_fs _ _ PLB) as [PB1 PB2]. destruct (lb_in_fs _ _ LBP) as [PF1 PF2].
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as OF.
    pose proof (lb_apart_frame _ _ _ F 128 _ _ LBP APART) as PF.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as OS.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 LBP ltac:(lia) ltac:(lia)) as PS.
    pose proof (In_disjoint Wx P (P + 4) _ _ PIN WXP) as PO. pose proof (In_disjoint Wx P (P + 4) _ _ PIN WXT) as PT.
    unfold xWA, xWB. cbn [disjoint_from].
    split. { clear - QB LO CLO FHI FSB2 SH3 OF OS PO MBS MBLO PF1 PF2 ACR FSB1. repeat split; try exact I; lia. }
    split. { clear - QB LO CLO SHI MBS OF PF PS FSF PLO SFB FLO FSB1 PF2 FSB2 AHI TFS ALO FHI MBLO SH3. repeat split; try exact I; lia. }
    split. { clear - PO MBS PF PS. repeat split; try exact I; lia. }
    clear - OF PO MBS. repeat split; try exact I; lia.
  Qed.

  #[using="VOK RF0"] Lemma vinv_stepX2 : forall q' cur G cs cur' G' cs' m m' (e' : word),
    vinv q' cur G cs m -> munch (WLX q') m m' -> wmono asegs m m' ->
    stk asegs m' lo q' -> vscr q' G' cs' m' -> vtok q' m' ->
    rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] -> mem_inv asegs m' ->
    rw_cells asegs m' (F + 32) [C8 e'] -> rw_cells asegs m' SF vshadow ->
    cur0 <= cur' <= len -> FMT + flen <= 0x609000 ->
    vinv q' cur' G' cs' m'.
  Proof.
    intros q' cur G cs cur' G' cs' m m' e' INV MUL WML ST' SCR' TOK' SC' MI' FE' SHF' CR' FMTHI.
    pose proof INV as INV0. destruct INV0 as (_ & _ & _ & _ & MBC & BUF & _ & _ & _ & _ & _ & _ & _ & _ & _ & QBA & _).
    pose proof VOK as VOK'. vokA VOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & APART).
    cbn [FB_of SB_of] in APART.
    destruct (lb_in_fs _ _ PLB) as [PB1 PB2].
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as OF.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)) as OS.
    eapply (vinv_stepX q' cur G cs cur' G' cs' m m' e' INV MUL WML); try eassumption.
    - unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *. eapply rw_cells_transport; [exact MBC| exact MUL| exact WML|].
      unfold vWLX. cbn [disjoint_from]. simpl_sizes.
      split; [clear - SHI CLO MBS; lia|]. split; [clear - OF MBS; lia|]. split; [clear - OS MBS; lia|]. split; [clear - MBS; lia|].
      eapply disjoint_from_sub; [exact WXP| lia| lia].
    - apply (bytes_at_transport asegs _ m m' A bs BUF MUL). unfold vWLX. cbn [disjoint_from].
      split; [clear - AHI CLO; lia|]. split; [clear - TFS FLO FHI; lia|]. split; [clear - TBAND SFB FLO FHI FSB1 FSB2 ACR; lia|]. split; [clear - TXP MBS; lia| exact WXT].
  Qed.

  #[using="MB A len cap cur0 bs m0 VOK RF0"] Lemma xdj2 : forall q' P, q + -304 <= q' <= q + -288 -> In (P, P + 4) Wx -> 0x609000 <= P ->
    disjoint_from [(lo, q' + 184); (S + 8, S + 16); (SF + 4, SF + 5)]%Z P 4
    /\ disjoint_from [(lo, q' + 184); (S + 8, S + 16); (SF + 4, SF + 5)]%Z ERRNO_A 4.
  Proof.
    intros q' P QB PIN PLO. pose proof VOK as VOK'. vokA VOK'.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    assert (LBP : lb (fs_live FI st) P 4).
    { rewrite Forall_forall in WXL. destruct (WXL _ PIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER PLO; lia]. replace (P + 4 - P) with 4 in LB by lia. exact LB. }
    destruct (lb_in_fs _ _ LBP) as [PF1 PF2].
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 LBP ltac:(lia) ltac:(lia)) as PS.
    pose proof (In_disjoint Wx P (P + 4) _ _ PIN WXP) as PO.
    cbn [disjoint_from].
    clear - QB LO CLO PF2 FSB2 PO MBS PS MBLO ACR SFB FLO FSB1. repeat split; try exact I; lia.
  Qed.

  Definition vshadowU : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  Definition KXt (q' : Z) (m mi : mem) (P fp G cs cur' r : Z) (Q : machine_state -> Prop) : Prop :=
    forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 m',
      vinv q' cur' (G + 8) cs m' -> munch (vWPX q' P) m m' -> wmono asegs m m' ->
      munch [(lo, q' + 184); (S + 8, S + 16); (SF + 4, SF + 5)]%Z mi m' -> wmono asegs mi m' ->
      evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 m').

  #[using="VOK RF0"] Lemma x_tailV : forall (q' fp G cs cur cur' P r : Z) (e' : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    vinv q' cur G cs m -> munch (vWPX q' P) m mi -> wmono asegs m mi ->
    In (P, P + 4) Wx -> In (ERRNO_A, ERRNO_A + 4) Wx -> FMT + flen <= 0x609000 ->
    stk asegs mi lo q' -> vscr q' G cs mi -> vtok q' mi ->
    rw_cells asegs mi S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] -> mem_inv asegs mi ->
    rw_cells asegs mi (F + 32) [C8 e'] -> rw_cells asegs mi SF vshadowU ->
    cur0 <= cur' <= len ->
    KXt q' m mi P fp G cs cur' r Q ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz r) x11 x12 x13 x14 x15 x16 x17
                         (wz SF) (wz 4) (wz S) (wz 2147450880) (wz (S + 8)) (wz SHC) (wz (fp + 2)) x25 x26 (wz F) x28 x29 x30 x31)
                    F_ (wz 0x87448) fc None mi (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur cur' P r e' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 m mi Q INV0 MUP WMP PIN EIN FMTHI ST (j0 & w8 & w16 & SCR) TOK SC MI FE SHF CR K.
    pose proof INV0 as INVq. destruct INVq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (QB & _) & _).
    pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & _).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. unfold vSHC, vSHE, vshadowU in *.
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & _ & _).
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct (lb_in_fs _ _ PLB) as [PB1 PB2]. clear PLB. hide FAL.
    pose proof (fs_shadow_apart FI) as FSAP.
    destruct TOK as (j136 & tyA & tbA & tlA & j160 & tyB & tbB & tlB & TOK).
    hide MUP. hide WMP.
    pose proof (munch_refl [(lo, q' + 184); (S + 8, S + 16); (SF + 4, SF + 5)]%Z mi) as MUt. pose proof (wmono_refl asegs mi) as WMt.
    zstep. zstep. sstep. zstep.
    sstep.
    step.
    assert (SUBt : sub_fp [(lo, q' + 184); (S + 8, S + 16); (SF + 4, SF + 5)]%Z (vWPX q' P)).
    { apply sub_fp_cons1; [apply (sub_fp_in _ _ _ lo (q' + 184)); [unfold vWPX; left; reflexivity| lia| lia]|].
      apply sub_fp_cons1; [apply (sub_fp_in _ _ _ (S + 8) (S + 16)); [unfold vWPX; right; left; reflexivity| lia| lia]|].
      apply (sub_fp_in _ _ _ (SF + 4) (SF + 5)); [unfold vWPX; do 5 right; left; reflexivity| lia| lia]. }
    unhide MUP. unhide WMP.
    pose proof (munch_trans _ _ _ _ MUP (munch_weaken _ _ _ _ SUBt MUt)) as MUP2. pose proof (wmono_trans _ _ _ _ WMP WMt) as WMP2.
    unfold KXt, H_vfm_A.contstA, vSHC in K. eapply K; [| exact MUP2| exact WMP2| exact MUt| exact WMt].
    eapply (vinv_stepX2 q' cur G cs cur' (G + 8) cs m _ e' INV0 (WLX_sub q' P _ _ PIN EIN MUP2) WMP2); [exact ST| do 3 eexists; exact SCR| do 8 eexists; exact TOK| exact SC| exact MI| exact FE| exact SHF| exact CR| exact FMTHI].
  Qed.

  #[using="VOK RF0"] Lemma x_failV : forall (q' fp G cs cur curx P r : Z) (e' : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    vinv q' cur G cs m -> munch (vWPX q' P) m mi -> wmono asegs m mi ->
    In (P, P + 4) Wx -> In (ERRNO_A, ERRNO_A + 4) Wx -> FMT + flen <= 0x609000 ->
    stk asegs mi lo q' -> vscr q' G cs mi -> vtok q' mi ->
    rw_cells asegs mi S [C8 (wz MB); C8 (wz curx); C4 (wz 0)] -> mem_inv asegs mi ->
    rw_cells asegs mi (F + 32) [C8 e'] -> rw_cells asegs mi SF vshadowU ->
    KXt q' m mi P fp G cs cur r Q ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz r) x11 x12 x13 x14 x15 x16 x17
                         (wz SF) (wz 4) (wz S) (wz 2147450880) (wz cur) (wz SHC) (wz (fp + 2)) x25 x26 (wz F) x28 x29 x30 x31)
                    F_ (wz 0x87434) fc None mi (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur curx P r e' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 m mi Q INV0 MUP WMP PIN EIN FMTHI ST SCR0 TOK SC MI FE SHF K.
    pose proof INV0 as INVq. destruct INVq as (_ & _ & _ & _ & _ & _ & _ & _ & SHS & _ & _ & _ & _ & _ & CR & (QB & _) & VR).
    destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFc & LIVE1).
    pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & _).
    assert (PLS : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
    pose proof (shw_advX_in q' P m mi QB PIN EIN RFc LIVE1 MUP S 24 PLS SHS) as SHSn. clear SHS RFc LIVE1 PLS.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. unfold vSHC, vSHE, vshadowU in *.
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & _ & _).
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct (lb_in_fs _ _ PLB) as [PB1 PB2]. hide FAL.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (_ & _ & _ & _ & _ & _ & APART).
    cbn [FB_of SB_of] in APART.
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as OF. clear APART PLB.
    pose proof (fs_shadow_apart FI) as FSAP.
    pose proof SCR0 as SCR1. destruct SCR1 as (j0 & w8 & w16 & SCR). clear SCR0.
    destruct TOK as (j136 & tyA & tbA & tlA & j160 & tyB & tbB & tlB & TOK).
    hide MUP. hide WMP.
    pose proof (munch_refl [(S + 8, S + 16)]%Z mi) as MUt. pose proof (wmono_refl asegs mi) as WMt.
    pose proof (proj1 SHSn) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS SHSn.
    zstep. sstep. zstep.
    assert (SUBt : sub_fp [(S + 8, S + 16)]%Z (vWPX q' P)) by (apply (sub_fp_in _ _ _ (S + 8) (S + 16)); [unfold vWPX; right; left; reflexivity| lia| lia]).
    unhide MUP. unhide WMP.
    pose proof (munch_trans _ _ _ _ MUP (munch_weaken _ _ _ _ SUBt MUt)) as MUP2. pose proof (wmono_trans _ _ _ _ WMP WMt) as WMP2.
    eapply (x_tailV q' fp G cs cur cur P r e' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ Q INV0 MUP2 WMP2 PIN EIN FMTHI ST);
      [do 3 eexists; exact SCR| do 8 eexists; exact TOK| exact SC| exact MI| exact FE| exact SHF| exact CR|].
    unfold KXt in *. intros until m'. intros INV' MU' WM' MUt' WMt'.
    eapply K; [exact INV'| exact MU'| exact WM'| | exact (wmono_trans _ _ _ _ WMt WMt')].
    eapply munch_trans; [| exact MUt']. eapply munch_weaken; [| exact MUt].
    apply (sub_fp_in _ _ _ (S + 8) (S + 16)); [right; left; reflexivity| lia| lia].
  Qed.

  #[using="IC VOK RF0"] Lemma dir_xV : forall (q' fp G cs cur P : Z) (b2 : byte) (pv ev canary : word) x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 120 -> 0 <= fp < 2^62 -> FMT + flen <= 0x609000 ->
    rw_cells asegs m G [C8 (wz P)] -> shw m G 8 -> q <= G -> G + 8 <= 2^47 -> G mod 8 = 0 ->
    rw_cells asegs m P [C4 pv] -> shw m P 4 -> In (P, P + 4) Wx -> P mod 4 = 0 -> 0x609000 <= P ->
    bv_unsigned tp = 0x5e6970 ->
    rw_cells asegs m ERRNO_A [C4 ev] -> shw m ERRNO_A 4 -> In (ERRNO_A, ERRNO_A + 4) Wx ->
    rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
    0x609000 <= A -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> shw m A (len + 1) -> len + 1 <= 2^40 ->
    (forall (r cur' : Z) (pv' ev' : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 m',
       vinv q' cur' (G + 8) cs m' -> munch (vWPX q' P) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C4 pv'] -> rw_cells asegs m' ERRNO_A [C4 ev'] ->
       (r = 4 -> exists v l, pv' = wz v /\ 0 <= v < 2^31 /\ 1 <= l /\ cur' = cur + l /\ cur' < len) -> (r <> 4 -> cur' = cur) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur P b2 pv ev canary x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 m Q INV HACC RD HB FPR FMTHI GC SHG GLO GHI GAL PC SHP PIN PAL PLO
      TPV ERRC SHE EIN SSPG SSPC ALO NULT SHAN LENB KC.
    eapply (pctV q' fp 120 G cs b2); [exact (proj1 (proj2 INV))| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) | reflexivity| exact HACC| exact RD| exact HB| exact FPR|].
    intros y1 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31. cbn [vjt_off_A Z.eqb Pos.eqb Z.add].

    assert (KX : forall (r cur' : Z) (pv' ev' : word) mi, rw_cells asegs mi P [C4 pv'] -> rw_cells asegs mi ERRNO_A [C4 ev'] -> 0 <= r <= 5 ->
               (r = 4 -> exists v l, pv' = wz v /\ 0 <= v < 2^31 /\ 1 <= l /\ cur' = cur + l /\ cur' < len) -> (r <> 4 -> cur' = cur) ->
               KXt q' m mi P fp G cs cur' r Q).
    { intros r cur' pv' ev' mi PCi ERi RR XOK XNO. unfold KXt. intros until m'. intros INV' MU' WM' MUt' WMt'.
      pose proof INV as INVq. destruct INVq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (QB & _) & _).
      destruct (xdj2 q' P QB PIN PLO) as [DT1 DT2].
      eapply (KC r cur' pv' ev'); [exact INV'| exact MU'| exact WM'| exact RR| | | exact XOK| exact XNO].
      - exact (rw_cells_transport asegs _ mi m' P [C4 pv'] PCi MUt' WMt' DT1).
      - exact (rw_cells_transport asegs _ mi m' ERRNO_A [C4 ev'] ERi MUt' WMt' DT2). }
    clear KC.

    pose proof INV as INV0. open_vinv INV.
    pose proof VR as VR0. destruct VR0 as (_ & _ & _ & _ & (e & j & FT1) & _ & SHF & _ & _ & _ & _ & RFc & LIVE1). clear VR.
    destruct (xdj q' P QB PIN PLO ALO) as ((DA1 & DA2 & DA3 & DA4 & DA5 & DA6) & (DB1 & DB2 & DB3 & DB4) & (DC1 & DC2 & DC3) & (DS1 & DS2)).
    unfold xWA in DA1, DA2, DA3, DA4, DA5, DA6. unfold xWB in DB1, DB2, DB3, DB4.
    hide DA1. hide DA2. hide DA3. hide DA4. hide DA5. hide DA6. hide DB1. hide DB2. hide DB3. hide DB4. hide DC1. hide DC2. hide DC3. hide DS1. hide DS2.
    assert (LBP : lb (fs_live FI st) P 4).
    { pose proof VOK as VOK'. destruct VOK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & _).
      rewrite Forall_forall in WXL. destruct (WXL _ PIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER PLO; lia].
      replace (P + 4 - P) with 4 in LB by lia. exact LB. }
    destruct (lb_in_fs _ _ LBP) as [PF1 PF2].
    pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & A0 & AHI & LBS & CAP & ACAP & CUR0 & TXP & TFS & TBAND & _ & _ & _).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. unfold vSHC, vSHE in *.
    destruct xframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & _ & _).
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    destruct (lb_in_fs _ _ PLB) as [PB1 PB2].
    assert (PLS : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
    assert (PLM : lb (fs_live FI st) MB 32) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
    clear PLB.
    pose proof (fs_shadow_apart FI) as FSAP.
    hide TXP. hide TFS. hide TBAND. hide FAL.
    unfold A0_got_ssp, A0_ssp_guard in SSPG, SSPC.
    assert (LENL : len + 1 <= Z.of_nat (length bs)) by (assert (Z.to_nat len < length bs)%nat by (apply nth_error_Some; rewrite NULT; discriminate); lia).
    pose proof (proj1 SHG) as ACG.

    zstep. zstep. zstep. acc_chk0 10 G ACG. step. clear_shr. step. lit_branch. clear ACG.
    zstep. step. lit_branch. zstep. step.

    zstep. zstep. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF + 4, SF + 5)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide BUF. hide_mem_except SHF. unhide MUs. unhide WMs.
    sstep.
    unhide_transport MUs WMs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (BUF1 : bytes_at asegs mm A bs) end.
    { unhide BUF. apply (bytes_at_transport asegs _ _ _ A bs BUF MUs). cbn [disjoint_from]. split; [| exact I].
      unhide TBAND. clear - TBAND SFB FLO FHI FSB1 FSB2 ACR. lia. }
    clear BUF. rename BUF1 into BUF.

    lazymatch type of MUs with munch _ ?ma ?mb => assert (MUP : munch (vWPX q' P) ma mb) end.
    { eapply munch_weaken; [| exact MUs]. apply (sub_fp_in _ _ _ (SF + 4) (SF + 5)); [unfold vWPX; do 5 right; left; reflexivity| lia| lia]. }
    rename WMs into WMP. clear MUs. hide MUP. hide WMP.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof MUP as MUPn; unhide MUPn; pose proof WMP as WMPn; unhide WMPn;
      pose proof (shw_advX_in q' P m mm QB PIN EIN RFc LIVE1 MUPn S 24 PLS SHS) as SHSn;
      pose proof (shw_advX_in q' P m mm QB PIN EIN RFc LIVE1 MUPn MB 32 PLM SHMB) as SHMBn;
      assert (SHAn : 0 < len -> shw mm A len)
        by (intros HL; apply (shw_advX_out q' P m mm PIN EIN MUPn A len); [unhide TFS; clear - TFS LENL; lia| exact (SHA HL)]);
      pose proof (shw_advX_out q' P m mm PIN EIN MUPn SEPTAB_A 20 ltac:(left; unfold SEPTAB_A; clear - FSB1; lia) SHSEP) as SHSEPn;
      pose proof (shz_advX q' P m mm PIN EIN MUPn SHZ) as SHZn;
      pose proof (asan_env_frame asegs m mm (vWLX q') AE (WLX_sub q' P m mm PIN EIN MUPn) WMPn (WLX_env q')) as AEn;
      clear MUPn WMPn end.

    pose proof (proj1 SHSn) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
    zstep. zstep. zstep. zstep. step.

    hide FT1. hide SHF. hide PC. hide ERRC. hide SSPG. hide SSPC. hide FSAP. unhide TXP.
    clear SHS SHMB SHA SHSEP SHZ AE.
    split_chunk TOK 5%nat TKP TOK1. split_chunk TOK1 1%nat TYB TKB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (sgt_callV q' (q' + 168) (q' + 164) cur); try eassumption; try reflexivity;
        first [ (eapply (tok_shw q'); [eassumption| eassumption| lia| lia| lia]) | (match goal with QAL : hid (q' mod 16 = 0) |- _ => let Q2 := fresh in pose proof QAL as Q2; unfold hid in Q2; clear - Q2 end; Z.div_mod_to_equations; lia) | lia ]
    | post_callK asegs mm MUk WMk ] end.
    rename PC0 into ST. rename PC2 into SC. rename PC3 into TKB. rename PC4 into TYB. rename POST into RES. rename PC1 into AE. rename MI0 into MI.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into rr end.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.

    lazymatch type of MUk with hid (munch _ ?ma ?mb) => assert (MUA : munch [(lo, q' + 184); (S + 8, S + 16)]%Z ma mb) end.
    { unhide MUk. eapply munch_weaken; [| exact MUk]. intros xx OO. cbn [outside] in *. clear - OO QB LO. lia. }
    unhide WMk. unhide DA1. unhide DA2. unhide DA3. unhide DA4. unhide DA5. unhide DA6.
    trH FT1 DA1 MUA WMk. trH SHF DA2 MUA WMk. trH PC DA3 MUA WMk. trH ERRC DA4 MUA WMk. trH SSPG DA5 MUA WMk. trH SSPC DA6 MUA WMk.
    hide DA1. hide DA2. hide DA3. hide DA4. hide DA5. hide DA6.
    assert (SUBA : sub_fp [(lo, q' + 184); (S + 8, S + 16)]%Z (vWPX q' P)).
    { apply sub_fp_cons1; [apply (sub_fp_in _ _ _ lo (q' + 184)); [unfold vWPX; left; reflexivity| lia| lia]|].
      apply (sub_fp_in _ _ _ (S + 8) (S + 16)); [unfold vWPX; right; left; reflexivity| lia| lia]. }
    unhide MUP. unhide WMP.
    pose proof (munch_trans _ _ _ _ MUP (munch_weaken _ _ _ _ SUBA MUA)) as MUP2. pose proof (wmono_trans _ _ _ _ WMP WMk) as WMP2.
    clear MUP WMP MUA WMk MUk. rename MUP2 into MUP. rename WMP2 into WMP. hide MUP. hide WMP.
    clear SHSn SHMBn SHAn SHSEPn SHZn AEn MBC. hide TXP.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    split_chunk FT1 1%nat FE FJ. clear FJ.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    2:{
      step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
      joinB q'. unhide MUP. unhide WMP.
      eapply (x_failV q' fp G cs cur cur P rr e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ Q INV0 MUP WMP PIN EIN FMTHI ST);
        [do 3 eexists; exact SCR| do 8 eexists; exact TOK| exact SC| exact MI| exact FE| exact SHF|].
      eapply (KX rr cur pv ev); [exact PC| exact ERRC| lia| intros X; exfalso; lia| intros _; reflexivity]. }
    subst rr. clear CRB CRL. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia. zstep.
    step. if_cases KT; zify_cond KT.
    {
      joinB q'. unhide MUP. unhide WMP.
      eapply (x_failV q' fp G cs cur (cur + tlz) P 5 e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ Q INV0 MUP WMP PIN EIN FMTHI ST);
        [do 3 eexists; exact SCR| do 8 eexists; exact TOK| exact SC| exact MI| exact FE| exact SHF|].
      eapply (KX 5 cur pv ev); [exact PC| exact ERRC| lia| intros X; exfalso; lia| intros _; reflexivity]. }
    assert (ty = 0) by lia. subst ty.

    step. zstep. zstep. step.
    replace (bv_unsigned tp + -164) with ERRNO_A by (rewrite TPV; reflexivity).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof MUP as MUPn; unhide MUPn;
      pose proof (shw_advX_out q' P m mm PIN EIN MUPn ERRNO_A 4 ltac:(left; clear - FSB1; lia) SHE) as SHEn;
      clear MUPn end.

    zstep. zstep.
    pose proof (proj1 SHEn (ERRNO_A + 4 - 1) ltac:(lia)) as HACE.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 11 in
      destruct (AWAuto2.acc_loadw mm ERRNO_A 4 a ltac:(lia) ltac:(change (ERRNO_A mod 8) with 4; lia) ltac:(lia) HACE ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.
    destruct Hk as [-> | [K1 K2]]; [| exfalso; change (ERRNO_A mod 8) with 4 in K2; lia].
    step. step. lit_branch. clear SHR HACE SHEn.

    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(ERRNO_A, ERRNO_A + 4)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide BUF. hide_mem_except ERRC. unhide MUs. unhide WMs.
    sstep.
    unhide_transport MUs WMs.
    lazymatch type of MUs with munch _ _ ?mc => assert (AE3 : asan_env asegs mc) end.
    { eapply (asan_env_frame asegs _ _ _ AE MUs WMs). unfold env_safe. constructor; [do 6 right; left; cbn [fst snd]; lia| constructor]. }
    clear AE. rename AE3 into AE.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (BUF1 : bytes_at asegs mm A bs) end.
    { unhide BUF. apply (bytes_at_transport asegs _ _ _ A bs BUF MUs). cbn [disjoint_from]. split; [| exact I]. clear - ALO. lia. }
    clear BUF. rename BUF1 into BUF.

    unhide MUP.
    lazymatch type of MUP with munch _ ?ma ?mb => lazymatch type of MUs with munch _ _ ?mc => assert (MUP2 : munch (vWPX q' P) ma mc) end end.
    { eapply munch_trans; [exact MUP|]. eapply munch_weaken; [| exact MUs]. apply (sub_fp_in _ _ _ ERRNO_A (ERRNO_A + 4)); [unfold vWPX; do 3 right; left; reflexivity| lia| lia]. }
    clear MUP MUs WMs. rename MUP2 into MUP. hide MUP. hide WMP.
    zstep. zstep. zstep. step.

    pose proof (tok_cstrA _ A bs cur len BUF NULT ltac:(lia)) as CSTR.
    assert (LSTR : Z.of_nat (length (firstn (Z.to_nat (len - cur)) (skipn (Z.to_nat cur) bs))) = len - cur).
    { rewrite length_firstn, length_skipn. clear - CR CUR0 LENL. lia. }
    assert (ETP : bv_unsigned tp - 164 = ERRNO_A) by (rewrite TPV; reflexivity).
    destruct (rw_cells_forget asegs _ (F + 32) [C8 e] FE) as (ej & FEB). cbn [cells_size csize Nat.add] in FEB. clear FE.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof MUP as MUPn; unhide MUPn;
      assert (SHWs : shw mm (A + cur) (len - cur + 1))
        by (apply (shw_sub mm A (len + 1)); [apply (shw_advX_out q' P m mm PIN EIN MUPn A (len + 1)); [unhide TFS; clear - TFS LENL; lia| exact SHAN]| lia| lia| lia]);
      pose proof (eptr_shw mm SHF) as SHWe;
      clear MUPn end.
    assert (EAL : (F + 32) mod 8 = 0) by (unhide FAL; clear - FAL; Z.div_mod_to_equations; lia).
    assert (ETX : F + 32 + 8 <= A + cur \/ A + cur + (len - cur) + 1 <= F + 32) by (unhide TFS; clear - TFS FLO FHI LENL CR CUR0; lia).
    hide SC. hide PC. hide SHF. hide BUF. hide FSAP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_strtol IC) with (S := A + cur) (str := firstn (Z.to_nat (len - cur)) (skipn (Z.to_nat cur) bs)) (E := F + 32) (base := 16)
                                 (ejunk := ej) (errv := wz 0) (canary := canary) (lo := lo) (q := q');
      rewrite ?LSTR, ?ETP;
      [ exact CSTR | exact FEB | exact ERRC | exact SSPG | exact SSPC | exact AE
      | exact (proj1 SHWs) | exact (proj1 (proj2 SHWs)) | exact (proj2 (proj2 SHWs))
      | clear - LENB CR CUR0; lia
      | exact (proj1 SHWe) | exact (proj1 (proj2 SHWe)) | exact (proj2 (proj2 SHWe))
      | right; reflexivity
      | exact ST | exact CLO | unfold A0_STRTOL_DEPTH; clear - LO QB; lia | clear - QB QHI; change (2^47) with 140737488355328 in QHI; lia
      | rewrite TPV; lia | rewrite TPV; lia | exact TPV
      | clear - ALO CR CUR0; lia | clear - AHI LENL; lia
      | clear - FLO FSB1; lia | clear - FHI FSB2; lia | exact EAL
      | exact ETX
      | exact MI | reflexivity | reflexivity | reflexivity ]
    | clear ERRC FEB SSPG SSPC CSTR SHWs SHWe; post_callK asegs mm MUk WMk ] end.
    rename PC0 into ST. rename PC1 into AE'. rename PC3 into SSPG. rename PC4 into SSPC. rename PC5 into ERRC. rename PC6 into KR. rename POST into FE. rename MI0 into MI.
    rewrite ETP in ERRC. rewrite LSTR in KR. clear PC2 AE BUF.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename a into num end.
    lazymatch type of KR with _ <= ?kk <= _ => rename kk into k end.
    lazymatch type of ERRC with rw_cells _ _ _ [C4 ?e2] => rename e2 into ev2 end.

    unhide MUk. rewrite ETP in MUk. unhide WMk. unhide DB1. unhide DB2. unhide DB3.
    trH SC DB1 MUk WMk. trH PC DB2 MUk WMk. trH SHF DB3 MUk WMk.
    hide DB1. hide DB2. hide DB3.
    assert (SUBB : sub_fp [(lo, q'); (F + 32, F + 32 + 8); (ERRNO_A, ERRNO_A + 4)]%Z (vWPX q' P)).
    { apply sub_fp_cons1; [apply (sub_fp_in _ _ _ lo (q' + 184)); [unfold vWPX; left; reflexivity| lia| lia]|].
      apply sub_fp_cons1; [apply (sub_fp_in _ _ _ (F + 32) (F + 40)); [unfold vWPX; do 4 right; left; reflexivity| lia| lia]|].
      apply (sub_fp_in _ _ _ ERRNO_A (ERRNO_A + 4)); [unfold vWPX; do 3 right; left; reflexivity| lia| lia]. }
    unhide MUP. unhide WMP.
    pose proof (munch_trans _ _ _ _ MUP (munch_weaken _ _ _ _ SUBB MUk)) as MUP2. pose proof (wmono_trans _ _ _ _ WMP WMk) as WMP2.
    clear MUP WMP MUk WMk SUBB. rename MUP2 into MUP. rename WMP2 into WMP. hide MUP. hide WMP.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
    pose proof (word_lt64 num) as NB.
    clear SSPG SSPC.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof MUP as MUPn; unhide MUPn;
      pose proof (shw_advX_in q' P m mm QB PIN EIN RFc LIVE1 MUPn P 4 LBP SHP) as SHPn;
      clear MUPn end.
    pose proof (proj1 SHPn (P + 4 - 1) ltac:(lia)) as HACP. clear SHPn.
    unhide FSAP.

    gen2 CONT 0x87418 11%nat 12%nat.
    { intros yi yj.
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let a := reg_val 11 in
        destruct (AWAuto2.acc_loadw mm P 4 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACP ltac:(shadow_addr_tac)) as (k' & SHR & Hk) end.
      step.
      gen2 CONT2 0x87428 11%nat 12%nat.
      2:{ destruct Hk as [-> | [K1 K2]].
          - step. lit_branch. apply CONT2.
          - rewrite sxb_small by lia. step. if_cases KB; zify_cond KB. 2:{ exfalso; lia. }
            zstep. zstep. step. if_cases KC'; zify_cond KC'; zify_granule KC'; [apply CONT2| exfalso; lia]. }
      intros ya1 ya2. clear SHR Hk HACP.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(P, P + 4)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
      hide_mem_except PC. unhide MUs. unhide WMs.
      sstep.
      unhide DC1. unhide DC2. unhide DC3.
      trH SC DC1 MUs WMs. trH FE DC2 MUs WMs. trH SHF DC3 MUs WMs.
      unhide_transport MUs WMs.
      unhide MUP.
      lazymatch type of MUP with munch _ ?ma ?mb => lazymatch type of MUs with munch _ _ ?mc => assert (MUP2 : munch (vWPX q' P) ma mc) end end.
      { eapply munch_trans; [exact MUP|]. eapply munch_weaken; [| exact MUs]. apply (sub_fp_in _ _ _ P (P + 4)); [unfold vWPX; do 2 right; left; reflexivity| lia| lia]. }
      clear MUP MUs WMs. rename MUP2 into MUP.
      zstep. zstep.
      joinB q'.
      eapply (x_failV q' fp G cs cur (cur + tlz) P 5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ Q INV0 MUP WMP PIN EIN FMTHI ST);
        [do 3 eexists; exact SCR| do 8 eexists; exact TOK| exact SC| exact MI| exact FE| exact SHF|].
      eapply (KX 5 cur num ev2); [exact PC| exact ERRC| lia| intros X; exfalso; lia| intros _; reflexivity]. }

    zstep. step. if_cases K2; zify_cond K2.
    { apply CONT. }

    zstep. zstep. zstep. zstep. step. if_cases K3; zify_cond K3.
    2:{ apply CONT. }
    clear CONT.

    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 11 in
      destruct (AWAuto2.acc_loadw mm P 4 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACP ltac:(shadow_addr_tac)) as (k' & SHR & Hk) end.
    step.
    gen2 CONT2 0x875ec 11%nat 12%nat.
    2:{ destruct Hk as [-> | [K1 K2']].
        - step. lit_branch. apply CONT2.
        - rewrite sxb_small by lia. step. if_cases KB; zify_cond KB. 2:{ exfalso; lia. }
          zstep. zstep. step. if_cases KC'; zify_cond KC'; zify_granule KC'; [apply CONT2| exfalso; lia]. }
    intros ya1 ya2. clear SHR Hk HACP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(P, P + 4)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except PC. unhide MUs. unhide WMs.
    sstep.
    unhide DC1. unhide DC2. unhide DC3.
    trH SC DC1 MUs WMs. trH FE DC2 MUs WMs. trH SHF DC3 MUs WMs.
    unhide_transport MUs WMs.
    unhide MUP.
    lazymatch type of MUP with munch _ ?ma ?mb => lazymatch type of MUs with munch _ _ ?mc => assert (MUP2 : munch (vWPX q' P) ma mc) end end.
    { eapply munch_trans; [exact MUP|]. eapply munch_weaken; [| exact MUs]. apply (sub_fp_in _ _ _ P (P + 4)); [unfold vWPX; do 2 right; left; reflexivity| lia| lia]. }
    clear MUP MUs WMs. rename MUP2 into MUP.
    zstep. zstep. zstep. step.
    joinB q'.
    eapply (x_tailV q' fp G cs cur (cur + tlz) P 4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ Q INV0 MUP WMP PIN EIN FMTHI ST);
      [do 3 eexists; exact SCR| do 8 eexists; exact TOK| exact SC| exact MI| exact FE| exact SHF| clear - CR CL TL1; lia|].
    eapply (KX 4 (cur + tlz) num ev2); [exact PC| exact ERRC| lia| | intros X; exfalso; apply X; reflexivity].
    intros _. exists (bv_unsigned num), tlz. split; [symmetry; apply Z_to_bv_bv_unsigned|]. split.
    { split; [clear - NB; lia|]. rewrite Z.shiftr_div_pow2 in K2 by lia. change (2^31) with 2147483648 in *. clear - K2 NB. Z.div_mod_to_equations. lia. }
    split; [exact TL1|]. split; [reflexivity|]. apply STRICT. left. reflexivity.
  Qed.

End VF.
End W.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4 LbB_ContVot LbB_TablStmt LbB_TablOS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT4 LbB_TablPT6 LbB_TablPT8 LbB_TablPT9 LbB_TablPT11 LbB_TablXP1 LbB_TablXPk1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section XPk2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Definition xsl_ok (e : xpent H) (iv : Z * Z) : Prop := snd iv <= xS1 e + 16 \/ xS1 e + 32 <= fst iv.

  Lemma xframe_munch : forall e mL M sL LBi eL W,
    xpre H e -> xframe H e mL sL LBi eL -> munch W mL M -> wmono asegs mL M -> mem_inv asegs M ->
    stk asegs M (x_lo e) (xSP e) -> Forall (xok0 H e LBi) W ->
    xframe H e M sL LBi eL.
  Proof.
    intros e mL M sL LBi eL W P PF MU WM MI SK FW.
    destruct PF as (MI0 & AC0 & ST0 & S00 & ER0 & RA0 & SV0 & CL0 & FP0 & WF0 & WS0 & WP0 & WL0 & KC0 & RF0 & RH0 & OW0).
    pose proof (xgeoP_of H e P) as G. destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                                                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP).
    destruct (client_frame H HB sL LBi (xLF e) (x_B e) W mL M RH0 RF0 AC0 RA0 MU WM
                (Forall_impl _ (fun iv (X : xok0 H e LBi iv) => proj1 X) FW)
                (Forall_impl _ (fun iv (X : xok0 H e LBi iv) => proj1 (proj2 X)) FW)
                (Forall_impl _ (fun iv (X : xok0 H e LBi iv) => proj1 (proj2 (proj2 X))) FW)) as (RH1 & RF1 & AC1 & RA1).
    assert (ERA : errno_addr (x_tp e) = ATP - 164) by (rewrite TP, HLib.u64_of_Z by (unfold ATP; lia); lia).
    unfold xframe.
    split; [exact MI|]. split; [exact AC1|]. split; [exact SK|].
    split; [eapply stack0_transport; [exact S00 | exact MU | exact WM | exact (Forall_impl _ (fun iv (X : xok0 H e LBi iv) => proj1 (proj2 (proj2 (proj2 X)))) FW)]|].
    split.
    { eapply rw_cells_transport; [exact ER0 | exact MU | exact WM |]. rewrite ERA. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & X & _). cbn. lia. }
    split; [exact RA1|].
    split.
    { eapply rw_cells_transport; [exact SV0 | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & X & _). cbn. lia. }
    split.
    { eapply rw_cells_transport; [exact CL0 | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & _ & X & _). cbn. lia. }
    split.
    { eapply rw_cells_transport; [exact FP0 | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & _ & _ & X & _). cbn. lia. }
    split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WF0 WM)|]. split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WS0 WM)|].
    split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WP0 WM)|]. split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WL0 WM)|].
    split.
    { eapply rw_cells_transport; [exact KC0 | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & X). cbn. lia. }
    split; [exact RF1|]. split; [exact RH1|]. exact (lb_own_wmono _ _ _ OW0 WM).
  Qed.

  Lemma xslot_keep : forall e sv mL M W,
    xslotP H e sv mL -> munch W mL M -> wmono asegs mL M -> Forall (xsl_ok e) W -> xslotP H e sv M.
  Proof.
    intros e sv mL M W SL MU WM FW. destruct sv as [bA|]; [|exact I].
    unfold xslotP in *. unfold xslotc in *. cbn [g_S1 g_v xg] in *.
    destruct bA.
    - eapply rw_cells_transport; [exact SL | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. unfold xsl_ok in X. cbn. lia.
    - eapply rw_cells_transport; [exact SL | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. unfold xsl_ok in X. cbn. lia.
  Qed.

  Lemma xvec_munch : forall e ys mL M LBi bi capi pidi W,
    xvec H e ys mL LBi bi capi pidi -> munch W mL M -> wmono asegs mL M ->
    disjoint_from W (x_v e) 24 -> disjoint_from W bi (4 * Zlen ys) ->
    (0 < capi -> disjoint_from W (sh bi) (nsh (4 * capi))) -> disjoint_from W (sh (x_v e)) (nsh 24) ->
    xvec H e ys M LBi bi capi pidi.
  Proof.
    intros e ys mL M LBi bi capi pidi W PV MU WM D1 D2 D3 D4.
    destruct PV as (VEC & SH & AD & WV & OB & GR).
    pose proof VEC as (_ & _ & _ & Hlen & _).
    split; [exact (vec32A_munch LBi mL M (x_v e) bi ys capi W VEC MU D1 D2)|].
    split; [intros Hc; eapply SHAD_transport; [exact (SH Hc) | exact MU | exact WM |]; rewrite cc_gen_length by lia; exact (D3 Hc)|].
    split; [eapply addressable_transport; [exact AD | exact MU | exact WM | exact D4]|].
    split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WV WM)|].
    split; [exact OB | exact GR].
  Qed.

  Lemma xgrown_blocks : forall e LBi bi capi pidi, xpre H e -> xgrown H e LBi bi capi pidi ->
    forall bb, In bb (x_LB e) -> In bb LBi \/ (bb = (x_pid e, x_b e, 4 * x_cap e) /\ 0 < x_cap e /\ x_b e <> 0).
  Proof.
    intros e LBi bi capi pidi P GR bb Hb.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & _).
    destruct GR as [(_ & _ & -> & _)|(_ & -> & _)]; [left; exact Hb|].
    unfold v4_newLB. destruct (Z.eqb_spec (x_b e) 0) as [B0|B0]; [left; right; exact Hb|].
    destruct OLD as [(E0 & _)|(C0 & HIn)]; [contradiction|].
    destruct (Z.eq_dec (blk_id bb) (x_pid e)) as [E|NE].
    - right. destruct bb as [[pb Ab] nb]. cbn [blk_id fst] in E. subst pb.
      pose proof (LbB_ContV4.nodup_id_same _ _ _ _ _ _ ND HIn Hb) as EQ. rewrite <- EQ. split; [reflexivity|]. split; [exact C0 | exact B0].
    - left. right. exact (LbB_ContV4.lb_remove_keep H HB _ _ _ ND Hb NE).
  Qed.

  Lemma xvec_blk : forall e ys mL sL LBi bi capi pidi, as_RHEAP H sL LBi mL -> xvec H e ys mL LBi bi capi pidi ->
    0 <= Zlen ys <= capi /\ ((capi = 0 /\ bi = 0) \/ (0 < capi /\ In (pidi, bi, 4 * capi) LBi /\ ablock_range H bi (4 * capi)))
    /\ (bi <> 0 -> x_v e + 24 <= bi \/ bi + 4 * capi <= x_v e).
  Proof.
    intros e ys mL sL LBi bi capi pidi RH PV. destruct PV as (VEC & _ & _ & _ & OB & _).
    pose proof VEC as (_ & _ & _ & Hlen & Hb & _).
    split; [exact Hlen|]. split.
    - destruct OB as [(E0 & E1)|(C0 & HIn)]; [left; split; assumption|].
      right. split; [exact C0|]. split; [exact HIn|]. exact (ah_blocks H HB _ _ _ _ RH HIn).
    - intros NZ. destruct Hb as [(E0 & _)|(_ & _ & _ & _ & _ & D)]; [contradiction | exact D].
  Qed.

  Lemma xvec_frm : forall e ys mL M sL LBi bi capi pidi W, xpre H e -> as_RHEAP H sL LBi mL ->
    xvec H e ys mL LBi bi capi pidi -> munch W mL M -> wmono asegs mL M ->
    Forall (fun iv : Z * Z => (x_ff e <= fst iv /\ snd iv <= x_ff e + 256) \/ (sh (x_ff e) <= fst iv /\ snd iv <= sh (x_ff e) + 32)
                              \/ (xS1 e <= fst iv /\ snd iv <= xSP e)) W ->
    xvec H e ys M LBi bi capi pidi.
  Proof.
    intros e ys mL M sL LBi bi capi pidi W P RH PV MU WM FW.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SH1 & SH2 & SH3 & SH4 & FB & PB
                   & V8 & VB & VL & VF & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct (xvec_blk e ys mL sL LBi bi capi pidi RH PV) as (LEN & BK & _).
    pose proof (sh_lt_2_45 (x_ff e + 256) ltac:(lia)) as SB.
    assert (VS : x_v e + 24 <= sh (x_ff e) \/ sh (x_ff e) + 32 <= x_v e).
    { destruct (pt_app_sh (x_v e) 24 (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left | right]; lia)) as [X|X];
        change (nsh 256) with 32 in X; lia. }
    pose proof (sh_lt_2_45 (x_v e + 24) ltac:(destruct VB; lia)) as SV.
    assert (SVn : sh (x_v e) + nsh 24 <= sh (x_v e + 24) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
    assert (SVF : sh (x_v e) + nsh 24 <= x_ff e \/ x_ff e + 256 <= sh (x_v e)).
    { destruct (pt_app_sh (x_ff e) 256 (x_v e) 24 ltac:(destruct VB; lia) ltac:(lia) ltac:(destruct VB; lia) ltac:(destruct FB; [left | right]; lia)) as [X|X]; lia. }
    assert (F8 : x_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (SVS : sh (x_v e) + nsh 24 <= sh (x_ff e) \/ sh (x_ff e) + nsh 256 <= sh (x_v e)).
    { apply pt_sh_apart; [destruct VB; lia | lia | lia | lia | exact V8 | exact F8 | clear - VF; lia]. }
    change (nsh 256) with 32 in SVS.
    eapply xvec_munch; [exact PV | exact MU | exact WM | | | |].
    - apply dj_of_Forall. eapply Forall_impl; [|exact FW]. intros [l h] X. cbn [fst snd] in *. clear - X VF VS VL S1S LO. lia.
    - apply dj_of_Forall. eapply Forall_impl; [|exact FW]. intros [l h] X. cbn [fst snd] in *.
      destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & AC & AF & AP))]; [subst bi; clear - X LEN C0 FL SH2 S45; lia|].
      destruct (pt_app_sh bi (4 * Zlen ys) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left | right]; lia)) as [Y|Y];
        change (nsh 256) with 32 in Y; clear - X Y LEN AF AC CE LO S1S P1 P2 P3 P4 FS1; unfold AFS_SIZE, AFS_HDR in *; lia.
    - intros Hc. apply dj_of_Forall. eapply Forall_impl; [|exact FW]. intros [l h] X. cbn [fst snd] in *.
      destruct BK as [(C0 & B0)|(C0 & HIn & (A0 & A16 & An & AI & AC & AF & AP))]; [lia|].
      assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
      destruct (pt_app_sh (x_ff e) 256 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct FB; [left | right]; lia)) as [Y|Y];
      destruct (pt_sh_apart bi (4 * capi) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8 F8
                 ltac:(clear - AF P3 P4; unfold AFS_SIZE, AFS_HDR in *; lia)) as [Z'|Z']; change (nsh 256) with 32 in Z';
      pose proof (sh_lt_2_45 (bi + 4 * capi) ltac:(lia)) as SB2;
      assert (SBn : sh bi + nsh (4 * capi) <= sh (bi + 4 * capi) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia);
      clear - X Y Z' SB2 SBn S45; lia.
    - apply dj_of_Forall. eapply Forall_impl; [|exact FW]. intros [l h] X. cbn [fst snd] in *. clear - X SVF SVS SV SVn S45. lia.
  Qed.

  Lemma xok0_frm : forall e LBi a n, xpre H e -> x_ff e + 36 <= a -> a + n <= x_ff e + 248 -> 0 < n ->
    xok0 H e LBi (a, a + n) /\ xsl_ok e (a, a + n).
  Proof.
    intros e LBi a n P A1 A2 N0. pose proof (xgeoP_of H e P) as G.
    pose proof P as (FF & _).
    pose proof (x2frame_facts H _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    destruct G as (_ & S45 & _ & S1S & _ & _ & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SH1 & SH2 & SH3 & SH4 & FB & PB & _).
    unfold xok0, xsl_ok. cbn [fst snd]. unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    split; [|lia].
    split; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
    split; [right; exists (2, x_ff e, x_fp e); split; [left; reflexivity | cbn; change (fsz 2) with 256; lia]|].
    split; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
    split; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
    unfold ATP. unfold ASHADOW_BASE in *. lia.
  Qed.

  Lemma xok0_shb : forall e LBi k, xpre H e -> 5 <= k -> k < 32 ->
    xok0 H e LBi (sh (x_ff e) + k, sh (x_ff e) + k + 1) /\ xsl_ok e (sh (x_ff e) + k, sh (x_ff e) + k + 1).
  Proof.
    intros e LBi k P K1 K2. pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & _ & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SH1 & SH2 & SH3 & SH4 & FB & PB & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (SHA : sh (as_FSB H) <= sh (x_ff e) /\ sh (x_ff e + 256) <= sh (as_FSB H + AFS_SIZE))
      by (split; apply sh_mono; unfold AFS_SIZE in *; lia).
    assert (SHT : sh AIMG_TOP <= sh (x_ff e)) by (apply sh_mono; unfold AIMG_TOP in *; lia).
    pose proof SHT as SHT'. replace (sh AIMG_TOP) with 0x800d5000 in SHT' by reflexivity.
    assert (SHC : sh (x_ff e + 256) <= sh aceil) by (apply sh_mono; lia).
    pose proof (sh_lt_2_45 (x_ff e + 256) ltac:(lia)) as SB.
    unfold xok0, xsl_ok. cbn [fst snd]. unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    split; [|lia].
    split; [right; right; right; right; right; left; cbn [fst snd]; lia|].
    split; [left; cbn [fst snd]; split; [unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
    split; [apply aconst_ok_high; [cbn [fst]; clear - SHT K1; lia | right; left; cbn [fst]; clear - SHT' K1; lia]|].
    split; [right; cbn [snd]; lia|].
    unfold ATP. unfold ASHADOW_BASE in *. lia.
  Qed.

  Lemma xok0_sh : forall e LBi pidi bi capi, xpre H e -> In (pidi, bi, 4 * capi) LBi -> ablock_range H bi (4 * capi) -> 0 < capi ->
    xok0 H e LBi (sh bi, sh bi + nsh (4 * capi)) /\ xsl_ok e (sh bi, sh bi + nsh (4 * capi)).
  Proof.
    intros e LBi pidi bi capi P HIn ABR C0.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & SH2 & SH3 & _ & FB & _ & _).
    pose proof P as (FF & _).
    pose proof (x2frame_facts H _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (D1 : sh bi + nsh (4 * capi) <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh bi)
      by (apply aapp_disjoint_sh; [exact G10 | lia | unfold AAPP_HI; lia | lia]).
    assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    assert (F8 : x_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (D2 : sh bi + nsh (4 * capi) <= sh (x_ff e) \/ sh (x_ff e) + nsh 256 <= sh bi).
    { apply pt_sh_apart; [lia | lia | lia | lia | exact B8 | exact F8 |]. unfold AFS_SIZE, AFS_HDR in *. lia. }
    change (nsh 256) with 32 in D2.
    assert (D3 : sh bi + nsh (4 * capi) <= x_ff e \/ x_ff e + 256 <= sh bi).
    { destruct (pt_app_sh (x_ff e) 256 bi (4 * capi) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct FB; [left | right]; lia)) as [X|X]; lia. }
    assert (SL : 0x6e7248 <= sh bi) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SH : sh bi + nsh (4 * capi) <= sh (bi + 4 * capi) + 1) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
    pose proof (sh_lt_2_45 (bi + 4 * capi) ltac:(lia)) as SB.
    unfold xok0, xsl_ok. cbn [fst snd].
    split; [|lia].
    split; [right; right; right; left; exists (pidi, bi, 4 * capi); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    split; [left; cbn [fst snd]; split; [unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
    split; [apply aconst_ok_high; [apply sh_mono; unfold AIMG_TOP in *; lia | right; left; lia]|].
    split; [apply stack0_ok_sh; lia|].
    unfold ATP. unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    clear - D2 D3 SL SH SB S45 S1S LO CE ACF1 FL FH SH2 SH3. lia.
  Qed.

  Lemma xok0_stk : forall e LBi k, xpre H e -> 0 <= k <= XP_STACK - 192 ->
    xok0 H e LBi (xS1 e - k, xS1 e) /\ xsl_ok e (xS1 e - k, xS1 e).
  Proof.
    intros e LBi k P Hk.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & SH1 & SH2 & _ & _ & _ & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (AK : aceil <= xS1 e - k) by (clear - Hk LO CE; lia).
    destruct (stack_window_ok H LBi (xLF e) (xS1 e - k) (xS1 e) AK FS2) as (W1 & W2 & W3).
    pose proof (sh_lt_2_45 (x_ff e + 256) ltac:(lia)) as SB.
    unfold xok0, xsl_ok. cbn [fst snd].
    split; [|lia].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
    split; [left; cbn [fst]; unfold AHI_LO; lia|].
    unfold ATP. lia.
  Qed.

  Lemma xok0_slot : forall e LBi pidi bi capi a, xpre H e -> In (pidi, bi, 4 * capi) LBi -> ablock_range H bi (4 * capi) ->
    bi <= a -> a + 4 <= bi + 4 * capi ->
    xok0 H e LBi (a, a + 4) /\ xsl_ok e (a, a + 4).
  Proof.
    intros e LBi pidi bi capi a P HIn ABR A1 A2.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & SH1 & SH2 & _ & _ & _ & _).
    pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (D : a + 4 <= sh (x_ff e) \/ sh (x_ff e) + 32 <= a).
    { destruct (pt_app_sh a 4 (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left | right]; lia)) as [X|X];
      change (nsh 256) with 32 in X; lia. }
    unfold xok0, xsl_ok. cbn [fst snd].
    split; [|clear - A1 A2 ACe CE LO; unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia].
    split; [right; right; left; exists (pidi, bi, 4 * capi); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    split; [left; cbn [fst snd]; split; [unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia]|].
    split; [eapply (LbB_SR.aconst_ok_app bi (4 * capi)); [exact AP | lia | lia]|].
    split; [eapply (stack0_ok_aapp bi (4 * capi)); [exact AP | lia | lia]|].
    unfold ATP, AIMG_TOP in *. unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    unfold AFS_SIZE, AFS_HDR in *. clear - D A1 A2 A0 AI AF ACe CE LO S1S P1 P2 P3 P4 FL FH ACF1. lia.
  Qed.

  Lemma xok0_hdr : forall e LBi bi capi pidi, xpre H e -> xgrown H e LBi bi capi pidi ->
    xok0 H e LBi (x_v e + 8, x_v e + 16) /\ xsl_ok e (x_v e + 8, x_v e + 16).
  Proof.
    intros e LBi bi capi pidi P GR.
    pose proof (xgrown_blocks e LBi bi capi pidi P GR) as BL.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & _ & SH1 & SH2 & _ & FB & _
                   & V8 & VB & VL & VF & _).
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OBJ & _ & _ & _ & _ & _ & _ & _ & _ & _
                     & CX & B0C & BB & BD).
    destruct OBJ as (_ & _ & WO & FW & CO & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    assert (DB : x_v e + 16 <= x_b e \/ x_b e + 4 * x_cap e <= x_v e + 8).
    { destruct (Z.eq_dec (x_b e) 0) as [E|E]; [right; pose proof (B0C E); lia|]. destruct (BD E); lia. }
    assert (DS : x_v e + 16 <= sh (x_b e) \/ sh (x_b e) + nsh (4 * x_cap e) <= x_v e + 8).
    { destruct (pt_app_sh (x_v e + 8) 8 (x_b e) (4 * x_cap e) ltac:(destruct BB; lia) ltac:(lia) ltac:(destruct BB; lia)
                 ltac:(destruct VB; [left | right]; lia)) as [X|X]; lia. }
    assert (D : x_v e + 16 <= sh (x_ff e) \/ sh (x_ff e) + 32 <= x_v e + 8).
    { destruct (pt_app_sh (x_v e + 8) 8 (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VB; [left | right]; lia)) as [X|X];
      change (nsh 256) with 32 in X; lia. }
    unfold xok0, xsl_ok. cbn [fst snd].
    split; [|clear - VL S1S LO; unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia].
    split.
    { replace (x_v e + 16) with (x_v e + 8 + 8) by lia.
      eapply (pt_awo_LBi H (x_LB e) LBi (x_v e + 8) 8 (x_b e) (4 * x_cap e)); [| lia | | lia | lia].
      - replace (x_v e + 8 + 8) with (x_v e + 16) by lia.
        exact (aclient_write_ok_sub H (x_LB e) (x_v e) (x_v e + 24) (x_v e + 8) (x_v e + 16) WO ltac:(lia) ltac:(lia)).
      - intros bb Hb. destruct (BL bb Hb) as [IN|(EQ & _)]; [left; exact IN | right; subst bb; cbn; split; reflexivity]. }
    split; [eapply (pt_afs_LF H (x_LF e) (xLF e)); [exact (afs_write_ok_sub H (x_LF e) (x_v e) (x_v e + 24) (x_v e + 8) (x_v e + 16) FW ltac:(lia) ltac:(lia))
                                                  | intros f Hf; right; exact Hf]|].
    split; [exact (aconst_ok_sub (x_v e) (x_v e + 24) (x_v e + 8) (x_v e + 16) CO ltac:(lia) ltac:(lia))|].
    split.
    { unfold stack0_ok. cbn [fst snd].
      assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      destruct VB as [VB|VB]; [right | left; unfold AHI_LO]; lia. }
    unfold ATP. unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    destruct VL; destruct VF; lia.
  Qed.

  Lemma xgrown_tail : forall e LBi bi capi pidi, xpre H e ->
    LBi = v4_newLB H (x_LB e) (x_b e) (x_pid e) pidi bi (4 * capi) ->
    exists LBt, LBi = (pidi, bi, 4 * capi) :: LBt
      /\ (forall bb, In bb (x_LB e) -> In bb LBt \/ (bb = (x_pid e, x_b e, 4 * x_cap e) /\ 0 < x_cap e /\ x_b e <> 0)).
  Proof.
    intros e LBi bi capi pidi P EQ.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & _).
    unfold v4_newLB in EQ. destruct (Z.eqb_spec (x_b e) 0) as [B0|B0].
    - exists (x_LB e). split; [exact EQ|]. intros bb Hb. left. exact Hb.
    - exists (as_lb_remove H (x_pid e) (x_LB e)). split; [exact EQ|]. intros bb Hb.
      destruct OLD as [(E0 & _)|(C0 & HIn)]; [contradiction|].
      destruct (Z.eq_dec (blk_id bb) (x_pid e)) as [E|NE].
      + right. destruct bb as [[pb Ab] nb]. cbn [blk_id fst] in E. subst pb.
        pose proof (LbB_ContV4.nodup_id_same _ _ _ _ _ _ ND HIn Hb) as EQ2. rewrite <- EQ2. split; [reflexivity|]. split; [exact C0 | exact B0].
      + left. exact (LbB_ContV4.lb_remove_keep H HB _ _ _ ND Hb NE).
  Qed.

  Lemma xXE_old : forall e a, 0 < x_cap e -> x_b e <> 0 ->
    (x_b e <= a < x_b e + 4 * x_cap e \/ sh (x_b e) <= a < sh (x_b e) + nsh (4 * x_cap e)) -> rin_ivs (xXE H e) a.
  Proof.
    intros e a C0 B0 Ha. unfold xXE, v4_oldx. destruct (Z.eqb_spec (x_b e) 0) as [E|_]; [contradiction|].
    cbn [rin_ivs app fst snd]. right. destruct Ha as [Ha|Ha]; [left; exact Ha | right; left; exact Ha].
  Qed.

  Lemma xXE_frm : forall e a,
    (x_ff e <= a < x_ff e + 256 \/ sh (x_ff e) <= a < sh (x_ff e) + 32 \/ (x_fp e <= a < x_fp e + 1)
     \/ (as_FSB H <= a < as_FSB H + AFS_FLAGS)) -> rin_ivs (xXE H e) a.
  Proof.
    intros e a Ha. unfold xXE. cbn [rin_ivs]. right. apply rin_ivs_app. right. unfold xXS. cbn [rin_ivs fst snd]. lia.
  Qed.

  Lemma xp_xstep : forall e LBi bi capi pidi sL mL m1 m2 W,
    xpre H e -> xgrown H e LBi bi capi pidi -> as_RHEAP H sL LBi mL -> 0 < capi ->
    munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (bi <= fst iv /\ snd iv <= bi + 4 * capi) \/ (sh bi <= fst iv /\ snd iv <= sh bi + nsh (4 * capi))
                              \/ (aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (xXE H e) a)) W ->
    xpres H (x_LB e) (xSP e) (xXE H e) m1 m2.
  Proof.
    intros e LBi bi capi pidi sL mL m1 m2 W P GR RH C0 MU WM FW.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & RH0 & _).
    destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3)].
    - subst capi bi LBi pidi.
      assert (B0 : x_b e <> 0).
      { destruct OLD as [(X & Y)|(X & Y)]; [lia|].
        pose proof (ah_blocks H HB _ _ _ _ RH0 Y) as (A0 & _). unfold blk_addr in A0. cbn [fst snd] in A0. lia. }
      eapply (xpres_of_munch H (x_s e) (x_LB e) (xSP e) (xXE H e) W (x_m e) m1 m2); [exact HB | exact RH0 | exact MU | exact WM |].
      eapply Forall_impl; [|exact FW]. intros [l h] K. cbn [fst snd] in *.
      destruct K as [K|[K|[K|K]]]; [right | right | left; exact K | right; exact K].
      + intros a Ha. apply xXE_old; [exact C0 | exact B0 | left; lia].
      + intros a Ha. apply xXE_old; [exact C0 | exact B0 | right; lia].
    - destruct (xgrown_tail e LBi bi capi pidi P G2) as (LBt & EL & BL).
      rewrite EL in RH.
      assert (NI : ~ In pidi (map blk_id LBt)).
      { pose proof (ah_nodup H HB _ _ _ RH) as NDi. cbn [map] in NDi. apply NoDup_cons_iff in NDi as [X _]. exact X. }
      pose proof (aceil_facts) as ACF.
      assert (SPc : aceil <= xSP e).
      { pose proof P as (_ & _ & _ & _ & _ & _ & _ & CE & LO & _). unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO. lia. }
      pose proof (pt_xp_munch H HB sL LBt pidi bi (4 * capi) (xSP e) (xXE H e) W mL m1 m2 RH NI SPc MU WM FW) as XP.
      eapply (pt_xp_lift H LBt (xSP e) (xXE H e) (x_LB e) (xSP e) (xXE H e) m1 m2 XP ltac:(lia)); [|intros a Ha; exact Ha].
      intros bb Hb. destruct (BL bb Hb) as [IN|(EQ & Cc & Bc)]; [left; exact IN|].
      right. intros a Ha. subst bb. cbn [blk_addr blk_size fst snd] in Ha. apply xXE_old; [exact Cc | exact Bc | exact Ha].
  Qed.

  Lemma xcap_bound : forall (e : xpent H) LBi bi capi pidi, xpre H e -> XV e -> xgrown H e LBi bi capi pidi ->
    capi <= xcapm e /\ 4 * xcapm e <= 2 ^ 26 /\ x_cap e <= capi.
  Proof.
    intros e LBi bi capi pidi P XVH GR.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1' & _).
    pose proof (proj1 (B1' XVH)) as B1.
    assert (CM : x_cap e <= xcapm e) by (unfold xcapm, capmax; destruct (PrsGrammar.expand (x_t e)); lia).
    destruct GR as [(E1 & _)|(G1 & _)]; [subst capi; split; [exact CM|]; split; [exact B1 | lia]|].
    split; [lia|]. split; [exact B1 | lia].
  Qed.

  Lemma x_newLB_meas : forall e pidi bi n, xpre H e ->
    lb_small (v4_newLB H (x_LB e) (x_b e) (x_pid e) pidi bi n) <= nsmall n + lb_small (x_LB e)
    /\ (length (v4_newLB H (x_LB e) (x_b e) (x_pid e) pidi bi n) <= S (length (x_LB e)))%nat
    /\ nlarge (v4_newLB H (x_LB e) (x_b e) (x_pid e) pidi bi n) <= nlg n + nlarge (x_LB e).
  Proof.
    intros e pidi bi n P.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & RH0 & _).
    unfold v4_newLB. rewrite lb_small_cons, nlarge_cons. cbn [length blk_size snd].
    destruct (Z.eqb_spec (x_b e) 0) as [B0|B0]; [split; [lia|]; split; [lia | lia]|].
    destruct OLD as [(E0 & _)|(C0 & HIn)]; [contradiction|].
    pose proof (pt_lb_remove_perm H HB _ _ _ _ ND HIn) as PM.
    pose proof (pt_small_perm _ _ PM) as S. pose proof (pt_large_perm _ _ PM) as L. pose proof (Permutation_length PM) as N.
    rewrite lb_small_cons in S. rewrite nlarge_cons in L. cbn [length blk_size snd] in S, L, N.
    pose proof (nsmall_bounds (4 * x_cap e) ltac:(lia)) as B1. pose proof (nlg_bounds (4 * x_cap e)) as B2.
    split; [lia|]. split; [lia | lia].
  Qed.

  Lemma x_budget : forall e LBi bi capi pidi, xpre H e -> XV e -> xgrown H e LBi bi capi pidi -> 0 <= capi ->
    lb_small LBi + nsmall (4 * vgrow capi) <= RT_SMALL_MAX /\ Z.of_nat (length LBi) + 1 <= RT_CNT_MAX
    /\ nlarge LBi + nlg (4 * vgrow capi) <= RT_LARGE_MAX.
  Proof.
    intros e LBi bi capi pidi P XVH GR C0.
    pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BS' & BC' & BL' & _).
    pose proof (BS' XVH) as BS. pose proof (BC' XVH) as BC. pose proof (BL' XVH) as BL.
    pose proof (vgrow_ge capi C0) as VG.
    pose proof (pt_nsmall_max (4 * vgrow capi) ltac:(lia)) as NS. pose proof (nlg_bounds (4 * vgrow capi)) as NL.
    destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3)].
    - subst LBi. split; [lia|]. split; [lia | lia].
    - subst LBi.
      destruct (x_newLB_meas e pidi bi (4 * capi) P) as (T1 & T2 & T3).
      pose proof (pt_nsmall_max (4 * capi) ltac:(lia)) as NS2. pose proof (nlg_bounds (4 * capi)) as NL2.
      split; [lia|]. split; [lia | lia].
  Qed.

  Lemma x_src_keep : forall e LBi SPc m k t, xpre H e -> 4 <= k -> k < 31 ->
    rw_cells asegs m (x_ff e + 8 * k) [C4 (Z_to_bv 64 t)] -> rw_cells asegs m (sh (x_ff e) + k) [C1 (b8 4)] -> 0 <= t < 2 ^ 32 ->
    src4_keep H LBi SPc m (x_ff e + 8 * k) t.
  Proof.
    intros e LBi SPc m k t P K1 K2 CL CK TR m' AC' MI' AP'.
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3 & _).
    assert (CLx : forall a, x_ff e + 8 * k <= a < x_ff e + 8 * k + 4 -> aclient_addr H LBi SPc a).
    { intros a Ha. right; right; right; right; left. unfold AFS_SIZE in *. lia. }
    assert (SHx : aclient_addr H LBi SPc (sh (x_ff e) + k)).
    { right; right; right; right; right; left.
      assert (sh (as_FSB H) <= sh (x_ff e)) by (apply sh_mono; lia).
      assert (sh (x_ff e + 256) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; unfold AFS_SIZE in *; lia). lia. }
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    split.
    - unfold fldA. apply fld_of_rw_cells4 in CL; [|lia]. unfold fldA in CL.
      eapply fld_agree; [lia | cbn; lia | exact CL |].
      intros a Ha. unfold zwin in Ha. cbn in Ha. exact (proj1 (AP' a ltac:(lia) (CLx a ltac:(lia)))).
    - split; [lia|]. split; [unfold AAPP_HI; lia|].
      intros x Hx. exists 4. split; [lia|].
      assert (E : sh x = sh (x_ff e) + k) by (unfold sh; Z.div_mod_to_equations; lia).
      rewrite E. split.
      + destruct CK as [[_ (_ & _ & B)] _]. specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B.
        unfold mrd in *. unfold wa in *.
        destruct (AP' (sh (x_ff e) + k) ltac:(unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia) SHx) as [EQ _].
        unfold wa in EQ. rewrite EQ. exact B.
      + unfold byte_ok. right. assert (x mod 8 <= 3) by (Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma x_newLB_eq : forall e LBi bi capi pidi pid' b' n', xpre H e -> xgrown H e LBi bi capi pidi ->
    List.NoDup (map blk_id LBi) ->
    v4_newLB H LBi bi pidi pid' b' n' = v4_newLB H (x_LB e) (x_b e) (x_pid e) pid' b' n'.
  Proof.
    intros e LBi bi capi pidi pid' b' n' P GR NDi.
    destruct GR as [(E1 & E2 & E3 & E4)|(G1 & G2 & G3)]; [subst; reflexivity|].
    pose proof G3 as (A0 & _).
    unfold v4_newLB at 1. destruct (Z.eqb_spec bi 0) as [B0|B0]; [lia|].
    rewrite G2. unfold v4_newLB at 1.
    pose proof (ah_lb_remove H HB) as (L1 & _ & _).
    rewrite G2 in NDi. unfold v4_newLB in NDi. cbn [map] in NDi. apply NoDup_cons_iff in NDi as [NI _].
    rewrite L1 by exact NI. unfold v4_newLB. reflexivity.
  Qed.

  Lemma xframe_v4 : forall e mL m' sL s' LBi LBi' bi capi eL errv',
    xpre H e -> xframe H e mL sL LBi eL -> (bi = 0 /\ capi = 0 \/ (0 < capi /\ ablock_range H bi (4 * capi))) ->
    mem_inv asegs m' -> ACONST m' -> stk asegs m' (x_lo e) (xS1 e) -> stack0 m' (x_lo e) (x_shi e) ->
    rw_cells asegs m' (errno_addr (x_tp e)) [C4 errv'] -> as_rauxv_ok H m' (x_B e) ->
    as_RFS H (xLF e) m' -> as_RHEAP H s' LBi' m' -> lb_own LBi' m' ->
    xpres H LBi (xS1 e) ((x_v e, x_v e + 24) :: v4_oldx bi (4 * capi)) mL m' ->
    xframe H e m' s' LBi' errv' /\ (forall sv, xslotP H e sv mL -> xslotP H e sv m').
  Proof.
    intros e mL m' sL s' LBi LBi' bi capi eL errv' P PF BK MI' AC' ST' S0' ER' RA' RF' RH' OW' XP.
    pose proof PF as (_ & _ & ST & _ & _ & _ & SV & CL & FPc & WF & WS & WP & WL & KC & _).
    pose proof (xgeoP_of H e P) as G.
    destruct G as (_ & S45 & _ & S1S & _ & SPH & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SHF0 & SHF1 & SHF2 & SHF3 & FB & PB
                   & V8 & VB & VL & VF & VFL & VFP & SV1 & SV2 & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.

    assert (XW : forall l h, In (l, h) ((x_v e, x_v e + 24) :: v4_oldx bi (4 * capi)) ->
                 (l = x_v e /\ h = x_v e + 24) \/ (h <= aceil /\ ((h <= as_FSB H \/ as_FSB H + AFS_SIZE <= l)))
                 /\ (h <= sh (x_ff e) \/ sh (x_ff e) + 32 <= l)).
    { intros l h Hin. destruct Hin as [E|Hin]; [left; injection E as -> ->; split; reflexivity|].
      right. unfold v4_oldx in Hin. destruct (Z.eqb_spec bi 0) as [B0|B0]; [destruct Hin|].
      destruct BK as [(E0 & _)|(CP & ABR)]; [contradiction|].
      pose proof ABR as (A0 & A16 & An & AI & ACe & AF & AP).
      assert (B8 : bi mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
      assert (F8 : x_ff e mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      assert (SH1 : sh bi + nsh (4 * capi) <= sh (bi + 4 * capi) + 1) by (clear; unfold sh, nsh; Z.div_mod_to_equations; lia).
      pose proof (sh_lt_2_45 (bi + 4 * capi) ltac:(lia)) as SH2.
      pose proof P as (FF & _). pose proof (x2frame_facts H _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
      destruct Hin as [E|[E|[]]]; injection E as <- <-.
      - split; [split; [lia | unfold AFS_SIZE in *; lia]|].
        destruct (pt_app_sh bi (4 * capi) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia)
                   ltac:(unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left|right]; lia)) as [X|X];
          change (nsh 256) with 32 in X; lia.
      - split; [split; [lia|]; apply aapp_disjoint_sh; [exact G10 | lia | unfold AAPP_HI; lia | lia]|].
        destruct (pt_sh_apart bi (4 * capi) (x_ff e) 256 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) B8 F8
                   ltac:(unfold AFS_SIZE, AFS_HDR in *; lia)) as [X|X]; change (nsh 256) with 32 in X; lia. }
    assert (XR : forall A n, (forall l h, In (l, h) ((x_v e, x_v e + 24) :: v4_oldx bi (4 * capi)) -> A + n <= l \/ h <= A) ->
                 Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) ((x_v e, x_v e + 24) :: v4_oldx bi (4 * capi))).
    { intros A n K. apply Forall_forall. intros [l h] Hin. exact (K l h Hin). }
    assert (CR : forall A n, 0 <= n -> (xS1 e <= A \/ (as_FSB H <= A /\ A + n <= as_FSB H + AFS_SIZE)
                                        \/ (sh (as_FSB H) <= A /\ A + n <= sh (as_FSB H + AFS_SIZE))) ->
                 (forall l h, In (l, h) ((x_v e, x_v e + 24) :: v4_oldx bi (4 * capi)) -> A + n <= l \/ h <= A) ->
                 xclient_range H LBi (xS1 e) ((x_v e, x_v e + 24) :: v4_oldx bi (4 * capi)) A n).
    { intros A n N0 K D. split; [|exact (XR A n D)]. unfold aclient_range.
      destruct K as [K|[K|K]]; [left; exact K | right; right; right; right; left; exact K | right; right; right; right; right; left; exact K]. }
    assert (SHFr : sh (as_FSB H) <= sh (x_ff e) /\ sh (x_ff e + 256) <= sh (as_FSB H + AFS_SIZE))
      by (split; apply sh_mono; unfold AFS_SIZE in *; lia).
    split.
    2:{ intros sv SLP. destruct sv as [bA|]; [|exact I]. unfold xslotP, xslotc in *. cbn [g_S1 g_v xg] in *.
        destruct bA;
          (eapply (xpres_rw_cells H); [exact XP | exact SLP |]);
          (change (Z.of_nat (cells_size _)) with 16; apply CR; [lia | left; lia |];
           intros l h Hin; destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [destruct VL; lia | lia]). }
    unfold xframe.
    split; [exact MI'|]. split; [exact AC'|].
    split.
    { apply (stk_merge asegs m' (x_lo e) (xS1 e) (xSP e)); [exact ST' | | lia].
      eapply (xpres_stk H); [exact XP | exact (proj2 (stk_split asegs mL (x_lo e) (xS1 e) (xSP e) ST ltac:(lia))) | lia |].
      apply Forall_forall. intros [l h] Hin. cbn [fst snd].
      destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [destruct VL; lia | lia]. }
    split; [exact S0'|]. split; [exact ER'|]. split; [exact RA'|].
    split.
    { eapply (xpres_rw_cells H); [exact XP | exact SV |]. change (Z.of_nat (cells_size (xsaved e))) with 104.
      apply CR; [lia | left; lia |]. intros l h Hin. destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [destruct VL; lia | lia]. }
    split.
    { eapply (xpres_rw_cells H); [exact XP | exact CL |]. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 (x_t e))])) with 4.
      apply CR; [lia | right; left; unfold AFS_SIZE in *; lia |].
      intros l h Hin. destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [lia | unfold AFS_SIZE in *; lia]. }
    split.
    { eapply (xpres_rw_cells H); [exact XP | exact FPc |]. change (Z.of_nat (cells_size [C8 (Z_to_bv 64 (x_fp e))])) with 8.
      apply CR; [lia | right; left; unfold AFS_SIZE in *; lia |].
      intros l h Hin. destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [lia | unfold AFS_SIZE in *; lia]. }
    split.
    { eapply (xpres_wr_at H); [exact XP | exact WF |]. apply CR; [lia | right; left; unfold AFS_SIZE in *; lia |].
      intros l h Hin. destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [lia | unfold AFS_SIZE in *; lia]. }
    split.
    { eapply (xpres_wr_at H); [exact XP | exact WS |]. apply CR; [lia | right; right; lia |].
      intros l h Hin. destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [lia | lia]. }
    split.
    { eapply (xpres_wr_at H); [exact XP | exact WP |]. apply CR; [lia | right; left; unfold AFS_SIZE in *; lia |].
      intros l h Hin. destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [lia | unfold AFS_SIZE in *; lia]. }
    split.
    { eapply (xpres_wr_at H); [exact XP | exact WL |]. apply CR; [lia | right; left; unfold AFS_SIZE in *; lia |].
      intros l h Hin. destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [lia | unfold AFS_SIZE in *; lia]. }
    split.
    { eapply (xpres_rw_cells H); [exact XP | exact KC |]. change (Z.of_nat (cells_size [C1 (b8 4)])) with 1.
      apply CR; [lia | right; right; lia |].
      intros l h Hin. destruct (XW l h Hin) as [(-> & ->)|((X1 & X2) & X3)]; [lia | lia]. }
    split; [exact RF'|]. split; [exact RH' | exact OW'].
  Qed.

End XPk2.

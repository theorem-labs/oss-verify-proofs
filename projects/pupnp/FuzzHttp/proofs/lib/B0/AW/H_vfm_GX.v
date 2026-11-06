(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_scanner_get_token H_vfm_A H_vfm_G H_vfm_X.
Import ListNotations.
Open Scope Z_scope.

Section GX.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.

Notation FMT_CHUNK_A := 0x219e0%Z.
Definition fb_chunk : list byte := map (Z_to_bv 8) [37; 120; 37; 76; 37; 99; 0].
#[using="Type"] Lemma fb_chunk_at : forall m, mem_inv asegs m -> bytes_at asegs m FMT_CHUNK_A fb_chunk.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m FMT_CHUNK_A fb_chunk MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Section CHK.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (P P2 : Z) (m0 : mem) (canary : word).
  Notation WxC := [(P, P + 4); (P2, P2 + 16); (ERRNO_A, ERRNO_A + 4)]%Z.
  Hypothesis VOK : vf_okA FI q lo S MB A len cap cur0 bs st WxC.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis PLO : 0x609000 <= P.
  Hypothesis AP12 : P + 4 <= P2 \/ P2 + 16 <= P.

  Notation F := (vF FI st). Notation FL := (vFL FI st). Notation SF := (vSF FI st).

  #[using="Type"] Lemma cPIN : In (P, P + 4) WxC.  Proof. left; reflexivity. Qed.
  #[using="Type"] Lemma cPIN2 : In (P2, P2 + 16) WxC.  Proof. right; left; reflexivity. Qed.
  #[using="Type"] Lemma cEIN : In (ERRNO_A, ERRNO_A + 4) WxC.  Proof. right; right; left; reflexivity. Qed.

  Definition clow (ev : word) (m : mem) : Prop :=
    rw_cells asegs m ERRNO_A [C4 ev] /\ rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m A0_ssp_guard [C8 canary].

  #[using="A len cap cur0 bs m0 VOK RF0 PLO"] Lemma cbounds :
    alloc_ceiling <= lo /\ lo <= q - 304 - 8192 /\ 0x609000 <= MB /\ MB + 32 <= S /\ S + 24 <= alloc_ceiling
    /\ lb (fs_live FI st) P 4 /\ lb (fs_live FI st) P2 16
    /\ FSB FI + 36864 <= P /\ P + 4 <= FSB FI + A0_FS_SIZE /\ FSB FI + 36864 <= P2 /\ P2 + 16 <= FSB FI + A0_FS_SIZE
    /\ (P + 4 <= MB \/ S + 24 <= P) /\ (P2 + 16 <= MB \/ S + 24 <= P2)
    /\ 0x609000 <= FSB FI /\ FSB FI + A0_FS_SIZE <= alloc_ceiling.
  Proof.
    pose proof VOK as VOK'. destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & WXP & _).
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _).
    rewrite Forall_forall in WXL.
    assert (LBP : lb (fs_live FI st) P 4).
    { destruct (WXL _ cPIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER PLO; lia]. replace (P + 4 - P) with 4 in LB by lia. exact LB. }
    assert (LBP2 : lb (fs_live FI st) P2 16).
    { destruct (WXL _ cPIN2) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER; lia]. replace (P2 + 16 - P2) with 16 in LB by lia. exact LB. }
    destruct (H_vfm_A.lb_in_fs FI st m0 RF0 _ _ LBP) as [H1 H2]. destruct (H_vfm_A.lb_in_fs FI st m0 RF0 _ _ LBP2) as [H3 H4].
    pose proof (In_disjoint _ P (P + 4) _ _ cPIN WXP) as D1. pose proof (In_disjoint _ P2 (P2 + 16) _ _ cPIN2 WXP) as D2.
    repeat (split; [first [assumption | lia]|]). lia.
  Qed.
  Local Notation XF := (xframe_facts FI q lo S MB A len cap cur0 bs st WxC m0 VOK RF0).

  #[using="q lo S MB A len cap cur0 bs P2 VOK RF0 PLO"] Lemma c4_pro : forall (pv : word) m, rw_cells asegs m0 P [C4 pv] -> shw m0 P 4 -> wmono asegs m0 m -> fkeep FI [] st m0 m ->
    rw_cells asegs m P [C4 pv] /\ shw m P 4.
  Proof.
    intros pv m PC SHP WM FK. destruct cbounds as (_ & _ & _ & _ & _ & LBP & _).
    split; [eapply (rw_cells_fkeep FI [] st m0 m P _ PC FK WM); [left; exact LBP| exact I]| exact (shw_fkeep0 FI st m0 m P 4 SHP FK RF0 LBP)].
  Qed.
  #[using="S MB cap cur0 st P P2 VOK RF0 PLO"] Lemma clow_pro : forall ev m, clow ev m0 -> shw m0 ERRNO_A 4 -> shw m0 A (len + 1) -> len + 1 <= Z.of_nat (length bs) ->
    munch ((lo, q) :: (FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: []) m0 m -> wmono asegs m0 m ->
    clow ev m /\ shw m ERRNO_A 4 /\ shw m A (len + 1).
  Proof.
    intros ev m (E1 & E2 & E3) SHE SHAN LENL MU WM. destruct cbounds as (CLO & LO & MBLO & MBS & SHI & _ & _ & _ & _ & _ & _ & _ & _ & FSB1 & FSB2).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof VOK as VOK'. destruct VOK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TFS & _).
    assert (FW : Forall (fsw_iv FI) ((lo, q) :: (FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: [])).
    { apply fsw_cons_app; [apply app_iv_stack; lia|]. apply (fsw_FSIV FI []). constructor. }
    assert (DJ : forall X n, X + n <= 0x609000 -> disjoint_from ((lo, q) :: (FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: []) X n).
    { intros X n HX. cbn [disjoint_from]. unfold sh, SHADOW_OFF. split; [left; lia|]. split; [left; lia|]. split; [left; clear - HX FSB1; Z.div_mod_to_equations; lia| exact I]. }
    unfold clow, A0_got_ssp, A0_ssp_guard in *.
    split; [split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply DJ; simpl_sizes; lia])|].
    split; [exact (shw_frame_fs FI _ m0 m ERRNO_A 4 SHE MU FW ltac:(left; lia))|].
    apply (shw_frame_fs FI _ m0 m A (len + 1) SHAN MU FW). clear - TFS LENL. lia.
  Qed.

  #[using="VOK RF0 PLO AP12"] Lemma x_carry : forall FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q' cur G cs G2 (pw1 pw2 : word) m m',
    vinv FI q lo S MB A len cap cur0 bs st WxC FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 q' cur G cs m ->
    q <= G2 -> G2 + 8 <= 2^47 ->
    vaP G2 P2 m -> rw_cells asegs m P2 [C8 pw1; C8 pw2] ->
    rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
    munch (vWPX FI lo S st q' P) m m' -> wmono asegs m m' ->
    vaP G2 P2 m' /\ rw_cells asegs m' P2 [C8 pw1; C8 pw2]
    /\ rw_cells asegs m' A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m' A0_ssp_guard [C8 canary].
  Proof.
    intros until m'. intros INV GLO GHI (GC & SHG & SHP2) PC2 G1 G2c MU WM.
    pose proof (vinv_qb FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as QB.
    destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VR).
    destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RFc & LIVE1).
    destruct cbounds as (CLO & LO & MBLO & MBS & SHI & LBP & LBP2 & PF1 & PF2 & PF3 & PF4 & D1 & D2 & FSB1 & FSB2).
    destruct XF as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (In_disjoint _ P2 (P2 + 16) _ _ cPIN2 (Wx_apart_new FI q lo S MB A len cap cur0 bs st WxC m0 VOK RF0 (F + 32) 8 ltac:(left; lia))) as DF.
    pose proof (In_disjoint _ P2 (P2 + 16) _ _ cPIN2 (Wx_apart_new FI q lo S MB A len cap cur0 bs st WxC m0 VOK RF0 (SF + 4) 1 ltac:(right; left; lia))) as DS.
    unfold A0_got_ssp, A0_ssp_guard in *.
    split; [split; [| split]|].
    - eapply rw_cells_transport; [exact GC| exact MU| exact WM|]. unfold vWPX. cbn [disjoint_from]. simpl_sizes.
      clear - QB GLO CLO LO SHI PF2 FSB2 ACR FHI SH3. repeat split; try exact I; right; lia.
    - apply (shw_advX_out FI q lo S MB A len cap cur0 bs st WxC m0 VOK RF0 q' P m m' cPIN cEIN MU G2 8); [right; clear - GLO CLO LO FSB2; lia| exact SHG].
    - exact (shw_advX_in FI q lo S MB A len cap cur0 bs st WxC m0 VOK RF0 q' P m m' QB cPIN cEIN RFc LIVE1 MU P2 16 LBP2 SHP2).
    - split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]); unfold vWPX; cbn [disjoint_from]; simpl_sizes.
      + clear - CLO PF3 PF4 FSB1 FSB2 D2 MBS AP12 DF DS. repeat split; try exact I; lia.
      + clear - CLO MBLO MBS PLO ACR FLO FSB1 SFB. repeat split; try exact I; lia.
      + clear - CLO MBLO MBS PLO ACR FLO FSB1 SFB. repeat split; try exact I; lia.
  Qed.

  #[using="HC FI MB A len cap cur0 bs st m0 VOK RF0 PLO AP12"] Lemma c4_step : forall q' WD (pv : word) m m', q + -304 <= q' <= q + -288 -> (WD = [] \/ WD = [(P2, P2 + 16)]%Z) ->
    rw_cells asegs m P [C4 pv] -> munch (vWP lo S q' WD) m m' -> wmono asegs m m' -> rw_cells asegs m' P [C4 pv].
  Proof.
    intros q' WD pv m m' QB HWD PC MU WM.
    destruct cbounds as (CLO & LO & MBLO & MBS & SHI & LBP & LBP2 & PF1 & PF2 & PF3 & PF4 & D1 & D2 & FSB1 & FSB2).
    eapply rw_cells_transport; [exact PC| exact MU| exact WM|]. unfold vWP. simpl_sizes.
    destruct HWD as [-> | ->]; cbn [disjoint_from]; clear - CLO PF2 FSB2 D1 MBS AP12; repeat split; try exact I; lia.
  Qed.
  #[using="HC FI MB A len cap cur0 bs st P m0 VOK RF0 PLO"] Lemma clow_step : forall q' WD ev m m', q + -304 <= q' <= q + -288 -> (WD = [] \/ WD = [(P2, P2 + 16)]%Z) ->
    clow ev m -> munch (vWP lo S q' WD) m m' -> wmono asegs m m' -> clow ev m'.
  Proof.
    intros q' WD ev m m' QB HWD (E1 & E2 & E3) MU WM.
    destruct cbounds as (CLO & LO & MBLO & MBS & SHI & LBP & LBP2 & PF1 & PF2 & PF3 & PF4 & D1 & D2 & FSB1 & FSB2).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold clow, A0_got_ssp, A0_ssp_guard in *.
    split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]); unfold vWP; simpl_sizes;
      (destruct HWD as [-> | ->]; cbn [disjoint_from]; clear - CLO MBLO MBS PF3 FSB1 ACR; repeat split; try exact I; lia).
  Qed.

  #[using="MB A len cap cur0 bs P2 m0 VOK RF0 PLO"] Lemma c4_rframe_c : forall pv : word, rframeA FI q lo S st (fun mm => rw_cells asegs mm P [C4 pv]).
  Proof.
    intros pv m m' H MU WM.
    destruct cbounds as (CLO & LO & MBLO & MBS & SHI & LBP & LBP2 & PF1 & PF2 & PF3 & PF4 & D1 & D2 & FSB1 & FSB2).
    pose proof (In_disjoint _ P (P + 4) _ _ cPIN (Wx_apart_new FI q lo S MB A len cap cur0 bs st WxC m0 VOK RF0 F 128 ltac:(left; lia))) as DF.
    pose proof (In_disjoint _ P (P + 4) _ _ cPIN (Wx_apart_new FI q lo S MB A len cap cur0 bs st WxC m0 VOK RF0 SF 16 ltac:(right; left; lia))) as DS.
    pose proof (In_disjoint _ P (P + 4) _ _ cPIN (Wx_apart_new FI q lo S MB A len cap cur0 bs st WxC m0 VOK RF0 FL 1 ltac:(right; right; split; reflexivity))) as DL.
    eapply rw_cells_transport; [exact H| exact MU| exact WM|]. unfold vWE. cbn [disjoint_from]. simpl_sizes.
    clear - CLO PF2 FSB2 DF DS DL D1 MBS. repeat split; try exact I; lia.
  Qed.
  #[using="MB A len cap cur0 bs P2 m0 VOK RF0 PLO"] Lemma c4_rframe : rframeA FI q lo S st (fun mm => exists pv, rw_cells asegs mm P [C4 pv]).
  Proof. intros m m' (pv & H) MU WM. exists pv. exact (c4_rframe_c pv m m' H MU WM). Qed.
  #[using="MB A len cap cur0 bs P P2 m0 VOK RF0 PLO"] Lemma clow_rframe : rframeA FI q lo S st (fun mm => exists ev, clow ev mm).
  Proof.
    intros m m' (ev & E1 & E2 & E3) MU WM. exists ev.
    destruct cbounds as (CLO & LO & MBLO & MBS & SHI & LBP & LBP2 & PF1 & PF2 & PF3 & PF4 & D1 & D2 & FSB1 & FSB2).
    destruct XF as (FLO & FHI & FAL & FLLO & FLHI & SFB & SH1 & SH2 & SH3 & SH4 & SH5 & FLSF & FSF).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold clow, A0_got_ssp, A0_ssp_guard in *.
    split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]); unfold vWE; cbn [disjoint_from]; simpl_sizes;
      clear - CLO MBLO MBS ACR FLO FLLO FSB1 SFB; repeat split; try exact I; lia.
  Qed.
  #[using="S MB A len cap cur0 bs st P P2 VOK RF0 PLO"] Lemma gcell_pro : forall G (w : word) m, rw_cells asegs m0 G [C8 w] -> shw m0 G 8 -> q <= G -> G + 8 <= 2^47 ->
    munch ((lo, q) :: (FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: []) m0 m -> wmono asegs m0 m ->
    rw_cells asegs m G [C8 w] /\ shw m G 8.
  Proof.
    intros G w m GC SHG GLO GHI MU WM. destruct cbounds as (CLO & LO & MBLO & MBS & SHI & _ & _ & _ & _ & _ & _ & _ & _ & FSB1 & FSB2).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (FW : Forall (fsw_iv FI) ((lo, q) :: (FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: [])).
    { apply fsw_cons_app; [apply app_iv_stack; lia|]. apply (fsw_FSIV FI []). constructor. }
    split.
    - eapply rw_cells_transport; [exact GC| exact MU| exact WM|]. cbn [disjoint_from]. simpl_sizes.
      split; [right; lia|]. split; [right; lia|]. split; [right; unfold sh, SHADOW_OFF; clear - FSB2 ACR CLO LO GLO; Z.div_mod_to_equations; lia| exact I].
    - exact (shw_frame_fs FI _ m0 m G 8 SHG MU FW ltac:(right; lia)).
  Qed.

  Definition X_chunkA : mem -> Z -> Z -> Prop := fun m' r cur' =>
    exists (pv pa pb ev : word), rw_cells asegs m' P [C4 pv] /\ rw_cells asegs m' P2 [C8 pa; C8 pb] /\ clow ev m'
      /\ (r = 4 -> exists v, pv = wz v /\ 0 <= v < 2^31 /\ cur0 + 1 <= cur').
  Definition R_chunkA (mm : mem) : Prop :=
    (exists pv, rw_cells asegs mm P [C4 pv]) /\ (exists pa pb, rw_cells asegs mm P2 [C8 pa; C8 pb]) /\ (exists ev, clow ev mm).
  #[using="MB A len cap cur0 bs m0 VOK RF0 PLO"] Lemma R_chunk_rframe : rframeA FI q lo S st R_chunkA.
  Proof.
    apply rframeA_and; [exact c4_rframe|]. apply rframeA_and; [| exact clow_rframe].
    eapply out_rframe; [exact VOK| exact RF0| exact cPIN2].
  Qed.
  #[using="Type"] Lemma X_chunk_err : forall mm rr cc, R_chunkA mm -> rr <> 4 -> X_chunkA mm rr cc.
  Proof.
    intros mm rr cc ((pv & H1) & (pa & pb & H2) & (ev & H3)) RN. exists pv, pa, pb, ev.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3| intros E; exfalso; exact (RN E)].
  Qed.
  #[using="IC STACK_MALLOC_1 VOK RF0 PLO AP12"] Theorem vf_chunkA : forall (G : Z) (pv pw1 pw2 ev : word)
      ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F_ : bvmap 5 word) fc,
    fs_call_ok FI st tp 1 ->
    FSENV FI m0 ->
    stk asegs m0 lo q ->
    rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) -> bytes_at asegs m0 A bs ->
    mem_inv asegs m0 -> asan_env asegs m0 ->
    shw m0 S 24 -> shw m0 MB 32 -> shw m0 A (len + 1) -> shw m0 SEPTAB_A 20 -> shw m0 FMT_CHUNK_A 7 ->
    shz m0 (sh lo) (sh q) ->
    rw_cells asegs m0 G [C8 (wz P)] -> shw m0 G 8 -> rw_cells asegs m0 (G + 8) [C8 (wz P2)] -> shw m0 (G + 8) 8 ->
    q <= G -> G + 16 <= 2^47 -> G mod 8 = 0 ->
    rw_cells asegs m0 P [C4 pv] -> shw m0 P 4 -> P mod 4 = 0 ->
    rw_cells asegs m0 P2 [C8 pw1; C8 pw2] -> shw m0 P2 16 -> P2 mod 8 = 0 ->
    bv_unsigned tp = 0x5e75b0 -> clow ev m0 -> shw m0 ERRNO_A 4 ->
    0x609000 <= A -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> len + 1 <= 2^40 ->
    evt asegs (vpostA FI q lo S MB A len cap cur0 bs st WxC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 X_chunkA)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_CHUNK_A) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz vfmatch_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros until fc. intros FCO FE0 ST SC MBC BUF MI AE SHS SHMB SHAN SHSEP SHFMT SHZ GC1 SHG1 GC2 SHG2 GLO GHI GAL PC1 SHP1 PAL1 PC2 SHP2 PAL2 TPV CLOW SHE ALO NULT LENB.
    assert (LENL : len + 1 <= Z.of_nat (length bs)) by (assert (Z.to_nat len < length bs)%nat by (apply nth_error_Some; rewrite NULT; discriminate); lia).
    assert (LEN0 : 0 <= len) by (destruct VOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CUR0 & _); lia).
    assert (SHA : 0 < len -> shw m0 A len) by (intros _; apply (shw_sub m0 A (len + 1)); [exact SHAN| lia| lia| lia]).
    assert (SUB0 : forall iv : ivl, In iv [] -> In iv WxC) by (intros iv []).
    assert (SUBP2 : forall iv : ivl, In iv [(P2, P2 + 16)] -> In iv WxC) by (intros iv [<-|[]]; exact cPIN2).
    eapply (prologueV FI STACK_MALLOC_1) with (FMT := FMT_CHUNK_A) (flen := 7) (c0 := 37) (b0 := Z_to_bv 8 37); try eassumption; try reflexivity; try lia.
    { intros m MIm. exact (fmt_rdA m FMT_CHUNK_A fb_chunk 0 37 (fb_chunk_at m MIm) eq_refl). }
    intros q' m x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 INV MUF WMF FKF.
    pose proof (vinv_qb FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as QB.
    destruct (gcell_pro G _ m GC1 SHG1 GLO ltac:(lia) MUF WMF) as [GCa SHGa].
    pose proof (vaP_pro FI q lo S MB A len cap cur0 bs st _ m0 (G + 8) P2 m VOK RF0 cPIN2 ltac:(lia) ltac:(lia) (conj GC2 (conj SHG2 SHP2)) MUF WMF FKF) as VA2.
    destruct (c4_pro _ m PC1 SHP1 WMF FKF) as [PCa SHPa].
    pose proof (out_pro FI q lo S MB A len cap cur0 bs st _ m0 P2 _ _ m VOK cPIN2 PC2 WMF FKF) as PCb.
    destruct (clow_pro ev m CLOW SHE SHAN LENL MUF WMF) as (CLa & SHEa & SHANa).
    clear GC1 SHG1 GC2 SHG2 SHP2 PC1 SHP1 PC2 CLOW SHE SHAN MUF WMF FKF.
    assert (F0' : 0 < FMT_CHUNK_A) by lia. assert (FH' : FMT_CHUNK_A + 7 < 2^62) by lia.
    pose proof (CONTk FI q lo S MB A len cap cur0 bs st _ FMT_CHUNK_A 7 fb_chunk ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R_chunkA q' VOK RF0 fb_chunk_at eq_refl R_chunk_rframe X_chunk_err) as CONTK.
    pose proof (ERRk FI q lo S MB A len cap cur0 bs st _ FMT_CHUNK_A 7 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 _ R_chunkA q' VOK RF0 R_chunk_rframe X_chunk_err) as ERRK.

    destruct CLa as (ERa & SGa & SCa).
    eapply (dir_xV IC FI) with (b2 := Z_to_bv 8 120) (P := P) (ev := ev) (canary := canary).
    3: exact INV. 1: exact VOK. 1: exact RF0.
    1: { eapply vinv_fmt_acc; [exact INV| lia]. }
    1: { exact (fmt_rdA m FMT_CHUNK_A fb_chunk 1 120 (fb_chunk_at m (vinv_mi FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV)) eq_refl). }
    1: reflexivity. 1: lia. 1: lia. 1: exact GCa. 1: exact SHGa. 1: exact GLO. 1: lia. 1: exact GAL. 1: exact PCa. 1: exact SHPa. 1: exact cPIN. 1: exact PAL1. 1: exact PLO.
    1: exact TPV. 1: exact ERa. 1: exact SHEa. 1: exact cEIN. 1: exact SGa. 1: exact SCa. 1: exact ALO. 1: exact NULT. 1: exact SHANa. 1: exact LENB.
    intros r1 cur1 pv1 ev1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m1 INV1 MU1 WM1 RR1 PC_1 ER_1 XOK1 XNO1.
    destruct (x_carry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (G + 8) _ _ m m1 INV ltac:(lia) ltac:(lia) VA2 PCb SGa SCa MU1 WM1) as (VA2_1 & PCb_1 & SG_1 & SC_1).
    assert (R1 : R_chunkA m1) by (split; [eexists; exact PC_1| split; [eexists; eexists; exact PCb_1| exists ev1; exact (conj ER_1 (conj SG_1 SC_1))]]).
    eapply (CONTK 2%nat 37); [exact INV1| reflexivity| lia| lia| lia| exact RR1| exact R1|].
    intros E1. intros. destruct (XOK1 E1) as (v1 & l1 & -> & V1 & L1 & -> & CL1). clear XOK1 XNO1 R1.

    destruct VA2_1 as (GCb & SHGb & SHPb).
    eapply (dir_LV IC FI) with (b2 := Z_to_bv 8 76) (P := P2).
    3: exact INV1. 1: exact VOK. 1: exact RF0.
    1: { eapply vinv_fmt_acc; [exact INV1| lia]. }
    1: { exact (fmt_rdA m1 FMT_CHUNK_A fb_chunk 3 76 (fb_chunk_at m1 (vinv_mi FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV1)) eq_refl). }
    1: reflexivity. 1: lia. 1: exact GCb. 1: exact SHGb. 1: lia. 1: lia. 1: { clear - GAL. Z.div_mod_to_equations. lia. } 1: exact PCb_1. 1: exact SHPb. 1: exact cPIN2. 1: exact PAL2.
    intros r2 cur2 pb2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 INV2 MU2 WM2 RR2 PCb_2 X2.
    pose proof (c4_step q' _ _ m1 m2 QB (or_intror eq_refl) PC_1 MU2 WM2) as PC_2.
    pose proof (clow_step q' _ ev1 m1 m2 QB (or_intror eq_refl) (conj ER_1 (conj SG_1 SC_1)) MU2 WM2) as CL_2.
    assert (R2 : R_chunkA m2) by (split; [eexists; exact PC_2| split; [eexists; eexists; exact PCb_2| exists ev1; exact CL_2]]).
    eapply (CONTK 4%nat 37); [exact INV2| reflexivity| lia| lia| lia| exact RR2| exact R2|].
    intros E2. intros. destruct (X2 E2) as (l2 & -> & L2 & -> & CL2 & BY2). clear X2 R2.

    eapply (dir_cV IC FI) with (b2 := Z_to_bv 8 99).
    3: exact INV2. 1: exact VOK. 1: exact RF0.
    1: { eapply vinv_fmt_acc; [exact INV2| lia]. }
    1: { exact (fmt_rdA m2 FMT_CHUNK_A fb_chunk 5 99 (fb_chunk_at m2 (vinv_mi FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2)) eq_refl). }
    1: reflexivity. 1: lia.
    - intros r3 cur3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 INV3 MU3 WM3 RR3 X3.
      pose proof (c4_step q' _ _ m2 m3 QB (or_introl eq_refl) PC_2 MU3 WM3) as PC_3.
      pose proof (out_step0 FI q lo S MB A len cap cur0 bs st _ m0 q' P2 _ _ m2 m3 VOK RF0 cPIN2 PCb_2 MU3 WM3) as PCb_3.
      pose proof (clow_step q' _ ev1 m2 m3 QB (or_introl eq_refl) CL_2 MU3 WM3) as CL_3.
      pose proof (vinv_cur FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV3) as CR3.
      pose proof (vinv_cur FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2) as CR2.
      pose proof (vinv_cur FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as CR0.
      assert (R3 : R_chunkA m3) by (split; [eexists; exact PC_3| split; [eexists; eexists; exact PCb_3| exists ev1; exact CL_3]]).
      eapply contV with (c := 0) (b := Z_to_bv 8 0).
      + eapply vinv_fmt_acc; [exact INV3| lia].
      + exact (fmt_rdA m3 FMT_CHUNK_A fb_chunk 6 0 (fb_chunk_at m3 (vinv_mi FI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV3)) eq_refl).
      + reflexivity.
      + lia.
      + exact RR3.
      + intros _ C. exfalso. apply C. reflexivity.
      + intros -> _. intros.
        eapply evt_mono.
        * eapply (epiV FI) with (R := fun mm => rw_cells asegs mm P [C4 (wz v1)] /\ (exists pa pb, rw_cells asegs mm P2 [C8 pa; C8 pb]) /\ (exists ev', clow ev' mm))
                               (XP := fun r c => r = 4 -> cur0 + 1 <= c).
          1: exact VOK. 1: exact RF0. 1: exact INV3. 1: lia. 1: { intros _. lia. } 1: { intros C; exfalso; apply C; reflexivity. }
          1: { split; [exact PC_3| split; [eexists; eexists; exact PCb_3| exists ev1; exact CL_3]]. }
          1: { apply rframeA_and; [exact (c4_rframe_c (wz v1))|]. apply rframeA_and; [| exact clow_rframe].
               eapply out_rframe; [exact VOK| exact RF0| exact cPIN2]. }
          intros _. specialize (X3 eq_refl). clear - X3 L1 L2. lia.
        * intros ms V. eapply vpostA_mono; [exact V|]. cbn beta. intros mm rr cc [(H1 & (pa & pb & H2) & (ev' & H3)) HXP].
          exists (wz v1), pa, pb, ev'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros E. exists v1. split; [reflexivity|]. split; [exact V1| exact (HXP E)].
      + intros RN. intros. eapply ERRK; [exact INV3| exact RR3| exact RN| exact R3].
    - intros r3 cur3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 INV3 MU3 WM3 RR3 RN3.
      pose proof (c4_step q' _ _ m2 m3 QB (or_introl eq_refl) PC_2 MU3 WM3) as PC_3.
      pose proof (out_step0 FI q lo S MB A len cap cur0 bs st _ m0 q' P2 _ _ m2 m3 VOK RF0 cPIN2 PCb_2 MU3 WM3) as PCb_3.
      pose proof (clow_step q' _ ev1 m2 m3 QB (or_introl eq_refl) CL_2 MU3 WM3) as CL_3.
      eapply ERRK; [exact INV3| exact RR3| exact RN3| split; [eexists; exact PC_3| split; [eexists; eexists; exact PCb_3| exists ev1; exact CL_3]]].
  Qed.
End CHK.
End GX.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr Agree SysStep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_presp_B H_phdr_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjA HObjK HObjF FsEnvKit H_list_access H_memptr_cmp H_ListFind H_freelist H_ListAddTail
     H_init_shw H_scanner_get_token H_map_str_to_int H_vfm_A H_vfm_G H_match_A HPrepA H_list_shw.
Import ListNotations.
Open Scope Z_scope.

Definition hid2 (P : Prop) : Prop := P.
Ltac hide2 H := lazymatch type of H with ?T => change (hid2 T) in H end.
Ltac unhide2 H := unfold hid2 in H.

Definition parse_headers_entryA : Z := 0x88134.
Notation TAB_HDR_A := 0xae6c0%Z.
Notation ZERO_ADDR_A := 0x5e5f80%Z.
Notation COMMA_ADDR_A := 0x218e0%Z.
Notation PH_HEAD := 0x88300%Z.
Notation PH_NEXT := 0x885dc%Z.
Notation PH_EPI := 0x887fc%Z.
Notation PHDR_DEPTH_A := 32768%Z.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation hdr := (hdr FI AI).

Definition ph_okA (q lo P A len cap : Z) (st : fsstate FI) : Prop :=
  alloc_ceiling <= lo /\ lo <= q - PHDR_DEPTH_A /\ q mod 16 = 0 /\ q + 64 <= 2^47
  /\ 0x609000 <= P /\ P + 504 <= alloc_ceiling /\ P mod 8 = 0 /\ lb (fs_live FI st) P 504
  /\ 0x609000 <= A /\ A + (cap + 1) + 16 <= alloc_ceiling /\ 0 <= len <= cap /\ A mod 16 = 0
  /\ (A + (cap + 1) <= FSB FI \/ FSB FI + A0_FS_SIZE <= A)
  /\ (A + (cap + 1) + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= A)
  /\ cap + 1 <= 2^43.
Ltac hokA V := destruct V as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB & ALO & AHI & LENC & AAL & TFS & TBAND & CAPB).

Section DEFS.
  Variables (q lo P A len cap : Z) (st : fsstate FI).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).

  Definition hF := fs_F FI st 2.  Definition hFL := fs_FL FI st 2.  Definition hSF := sh hF.
  Notation F := hF. Notation FL := hFL. Notation SF := hSF.
  Notation S := (P + 480)%Z. Notation MB := (P + 400)%Z. Notation L := (P + 288)%Z.

  Definition hWHP : list ivl := [(P + 488, P + 496)]%Z.

  Definition hWHS : list ivl := [(P + 4, P + 8); (P + 488, P + 496)]%Z.

  Definition hW0 : list ivl := ((lo, q) :: FSIV ((A, A + (cap + 1)) :: hWHS))%Z.

  Definition hpm (mb m : mem) : Prop :=
    forall meth, rw_cells asegs mb (P + 4) [C4 (wz meth)] -> exists meth', rw_cells asegs m (P + 4) [C4 (wz meth')] /\ (meth' = meth \/ meth' = 11).
  Definition hSHC : Z := Z.shiftr (P + 488) 3 + 2147450880.

  Definition hshadow (t : Z) : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t);
     C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  Definition hrestT (t : Z) (q' : Z) (mb m : mem) : Prop :=
    (q' = q + -256 \/ q' = q + -256 - 16)
    /\ stk asegs m (q' + 152) (q + -104)
    /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m F [C8 (wz 0x41b58ab3); C8 (wz 0x17fea); C8 (wz 0x88134); C8 (wz q')]
    /\ (exists j, rw_cells asegs m (F + 32) [CB 88 j])
    /\ (exists j, rw_cells asegs m (F + 120) [CB 40 j])
    /\ (exists j, rw_cells asegs m (F + 176) [CB 72 j])
    /\ rw_cells asegs m (F + 248) [C8 (wz FL)]
    /\ rw_cells asegs m SF (hshadow t)
    /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
    /\ munch hW0 mb m /\ wmono asegs mb m
    /\ fkeep FI hWHS st mb m
    /\ (exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 2 :: fs_live FI st)
    /\ hpm mb m.

  Definition hscr (q' : Z) (m : mem) : Prop :=
    exists j0 w32 j96 j128,
      rw_cells asegs m q' [CB 8 j0; C8 (wz P); C8 (wz F); C8 (wz F); C8 w32; C8 (wz (F + 32)); C8 (wz (P + 4)); C8 (wz TAB_HDR_A);
                           C8 (wz S); C8 (wz (P + 488)); C8 (wz FMT_HDR_A); C8 (wz hSHC); CB 24 j96; C8 (wz F); CB 4 j128].

  Definition hscrE (q' : Z) (m : mem) : Prop :=
    (exists j, rw_cells asegs m q' [CB 88 j]) /\ rw_cells asegs m (q' + 88) [C8 (wz hSHC)] /\ (exists j, rw_cells asegs m (q' + 96) [CB 36 j]).
  Definition hinvGT (t : Z) (scr : Z -> mem -> Prop) (q' cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem) : Prop :=
    stk asegs m lo q' /\ scr q' m
    /\ rw_cells asegs m (q' + 132) [C4 ty; C8 tb; C8 tl]
    /\ rw_cells asegs m (F + 160) [C8 va; C8 vl]
    /\ rw_cells asegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)]
    /\ rw_cells asegs m MB (mbuf_cells A len cap)
    /\ rw_cells asegs m A [CB (Z.to_nat (cap + 1)) bs]
    /\ mem_inv asegs m /\ asan_env asegs m
    /\ shw m P 504 /\ shw m A (cap + 1) /\ shw m SEPTAB_A 20 /\ shw m FMT_HDR_A 8
    /\ shz m (sh lo) (sh q) /\ shr m (sh lo - sh lo mod 8) (sh q + 8)
    /\ 0 <= cur <= len
    /\ (q + -272 <= q' <= q + -256 /\ q' mod 16 = 0)
    /\ hrestT t q' mb m.

  Definition hinv := hinvGT 248 hscr.
  Definition hinvE := hinvGT 248 hscrE.

  Definition headstH (q' sv : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            (wz sv) (wz TAB_HDR_A) (wz 2147450880) x21 x22 (wz (P + 488)) (wz (F + 160)) (wz L) (wz S) (wz SF) x28 x29 x30 x31)
       F_ (wz PH_HEAD) fc None m (seg_rom asegs).
  Definition epistH (q' r : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz r) x11 x12 x13 x14 x15 x16 x17
            x18 (wz F) (wz 2147450880) (wz F) x22 x23 x24 x25 x26 (wz SF) x28 x29 x30 x31)
       F_ (wz PH_EPI) fc None m (seg_rom asegs).
End DEFS.

Section PH.
  Variables (q lo P A len cap : Z) (st : fsstate FI).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis HOK : ph_okA q lo P A len cap st.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st tp 3.
  Hypothesis FE0 : FSENV FI m0.

  Notation F := (hF st). Notation FL := (hFL st). Notation SF := (hSF st).
  Notation S := (P + 480)%Z. Notation MB := (P + 400)%Z. Notation L := (P + 288)%Z.
  Notation WHP := (hWHP P). Notation WHS := (hWHS P). Notation hpm := (hpm P). Notation W0 := (hW0 q lo P A cap). Notation SHC := (hSHC P).
  Notation hrestT := (hrestT q lo P A cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation hrest := (hrestT 248).
  Notation hscr := (hscr P st).
  Notation hscrE := (hscrE P).
  Notation hinvGT := (hinvGT q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation hinvG := (hinvGT 248).
  Notation hinv := (hinv q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation hinvE := (hinvE q lo P A len cap st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation headstH := (headstH q P st gp tp F_ fc). Notation epistH := (epistH q st gp tp F_ fc).

  #[using="m0 RF0"] Lemma lb_in_fsH : forall a n, lb (fs_live FI st) a n -> FSB FI + 36864 <= a /\ a + n <= FSB FI + A0_FS_SIZE.
  Proof.
    intros a n (g & Hg & G1 & G2). pose proof (live_num FI st m0 RF0) as LN. rewrite Forall_forall in LN.
    destruct (LN g Hg) as (L1 & L2 & _). lia.
  Qed.
  #[using="Type"] Lemma sub_app_iv_fsH : forall a b, FSB FI <= a -> a <= b -> b <= FSB FI + A0_FS_SIZE -> app_iv (a, b).
  Proof.
    intros a b H1 H2 H3. pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5). unfold app_iv, SH_HI. cbn [fst snd]. lia.
  Qed.
  #[using="HC FI q lo A len cap st m0 HOK RF0"] Lemma WHP_app : app_ivs WHP.
  Proof.
    hokA HOK. destruct (lb_in_fsH _ _ PLB) as [H1 H2]. unfold hWHP.
    repeat (constructor; [apply sub_app_iv_fsH; lia|]). constructor.
  Qed.
  #[using="HC FI q lo A len cap st m0 HOK RF0"] Lemma WHS_app : app_ivs WHS.
  Proof.
    hokA HOK. destruct (lb_in_fsH _ _ PLB) as [H1 H2]. unfold hWHS.
    repeat (constructor; [apply sub_app_iv_fsH; lia|]). constructor.
  Qed.
  #[using="HC FI q lo P len st HOK"] Lemma text_app_iv : app_iv (A, A + (cap + 1)).
  Proof. hokA HOK. unfold app_iv, SH_HI. cbn [fst snd]. lia. Qed.
  #[using="len st m0 HOK RF0"] Lemma W0_fsw : Forall (fsw_iv FI) W0.
  Proof.
    hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    apply fsw_cons_app; [apply app_iv_stack; lia|]. apply fsw_FSIV. constructor; [exact text_app_iv| exact WHS_app].
  Qed.

  #[using="q lo A len cap m0 HOK RF0"] Lemma hframe_facts :
    FSB FI + A0_FS_FRAMES <= F /\ F + 256 <= FSB FI + A0_FS_SIZE /\ F mod 64 = 0
    /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + A0_FS_FRAMES
    /\ 8 * (SF - 2147450880) = F
    /\ sh (FSB FI) <= SF /\ SF + 32 <= sh (FSB FI) + A0_FS_SHSIZE
    /\ (P + 504 <= F \/ F + 256 <= P) /\ (P + 504 <= FL \/ FL + 1 <= P).
  Proof.
    hokA HOK.
    destruct (new_frame_facts FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5).
    pose proof (lb_apart_frame _ _ _ F 256 _ _ PLB APART) as P1.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PLB FLLO FLHI) as P3.
    split; [exact FLO|]. split; [exact FHI|]. split; [exact FAL|]. split; [exact FLLO|]. split; [exact FLHI|].
    split; [unfold hSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia|].
    split; [unfold hSF, sh, SHADOW_OFF; clear - FLO B4; Z.div_mod_to_equations; lia|].
    split; [unfold hSF, sh, SHADOW_OFF in *; clear - FHI FLO B4; Z.div_mod_to_equations; lia|].
    split; [exact P1| exact P3].
  Qed.

  Definition hWL (q' : Z) : list ivl := ((lo, q' + 152) :: (A, A + (cap + 1)) :: (F + 160, F + 176) :: WHP)%Z.
  Notation WL := hWL.

  #[using="q P A len cap st HOK"] Lemma fs_shadow_band : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000 /\ sh (FSB FI) + A0_FS_SHSIZE <= lo.
  Proof.
    hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _). unfold sh, SHADOW_OFF in *.
    clear - B1 B2 B4 ACR CLO. repeat split; Z.div_mod_to_equations; lia.
  Qed.

  #[using="q lo P len st HOK"] Lemma text_out_fs : (A + (cap + 1) <= FSB FI \/ FSB FI + A0_FS_SIZE <= A) /\ (A + (cap + 1) <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= A).
  Proof.
    pose proof fs_shadow_band as (S1 & S2 & _). hokA HOK. split; [exact TFS|]. clear - S1 S2 TBAND. lia.
  Qed.

  #[using="q len m0 HOK RF0"] Lemma WL_app : forall q', app_ivs (WL q').
  Proof.
    intros q'. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & _).
    unfold hWL. constructor; [apply app_iv_stack; lia|]. constructor; [exact text_app_iv|].
    constructor; [apply sub_app_iv_fsH; pose proof (fsb_ok FI) as (B1 & _); lia| exact WHP_app].
  Qed.

  #[using="q len m0 HOK RF0"] Lemma WL_env : forall q', env_safe (WL q').
  Proof.
    intros q'. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & _). destruct hframe_facts as (FLO & _). destruct (lb_in_fsH _ _ PLB) as [H1 H2].
    unfold env_safe, hWL, hWHP. repeat (constructor; [left; cbn [fst snd]; lia|]). constructor.
  Qed.

  #[using="len m0 HOK RF0"] Lemma WL_sub0 : forall q', q' + 152 <= q -> sub_fp (WL q') W0.
  Proof.
    intros q' HQ. destruct hframe_facts as (FLO & FHI & _).
    unfold sub_fp, hWL, hW0, hWHP, hWHS. intros xo Ho. cbn [outside] in *.
    destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & _).
    repeat split; try assumption; lia.
  Qed.

  #[using="q len m0 HOK RF0"] Lemma WL_fk : forall q', Forall (fk_ok FI WHS st) (WL q').
  Proof.
    intros q'. pose proof fs_shadow_band as (S1 & S2 & S3). pose proof text_out_fs as (T1 & T2).
    hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof (new_frame_fk FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    unfold hWL, hWHP, hWHS.
    apply Forall_cons; [unfold fk_ok; right; left; cbn [fst snd]; lia|].
    apply Forall_cons; [unfold fk_ok; right; left; cbn [fst snd]; lia|].
    apply Forall_cons; [replace (F + 176) with (F + 160 + 16) by lia; apply NFK; cbn [FB_of SB_of]; lia|].
    repeat (apply Forall_cons; [unfold fk_ok; left; cbn [inside fst snd]; lia|]).
    apply Forall_nil.
  Qed.

  Definition hlive (stc : fsstate FI) : Prop :=
    lb (fs_live FI stc) F 256 /\ ls (fs_live FI stc) SF 32 /\ lf (fs_live FI stc) FL /\ lb (fs_live FI stc) P 504
    /\ (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)).
  #[using="q lo A len cap m0 HOK RF0"] Lemma hlive_of : forall stc, fs_live FI stc = fs_newff FI st 2 :: fs_live FI st -> hlive stc.
  Proof.
    intros stc LIVE1. hokA HOK.
    destruct (new_frame_facts FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 2)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 2)) with FL in LVL. change (sh F) with SF in LVS.
    split; [exact LVF|]. split; [exact LVS|]. split; [exact LVL|]. split; [exact (lb_mono _ _ _ _ PLB LSUB)| exact LSUB].
  Qed.

  #[using="q len HOK"] Lemma WL_rf : forall q' stc m m', hlive stc -> RFAKE FI stc m -> munch (WL q') m m' -> wmono asegs m m' -> RFAKE FI stc m'.
  Proof.
    intros q' stc m m' (LVF & LVS & LVL & LVP & LSUB) RF MU WM.
    pose proof fs_shadow_band as (S1 & S2 & S3). pose proof text_out_fs as (T1 & T2).
    hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _).
    eapply (rfake_frame FI stc m m' (WL q') RF MU WM). unfold hWL, hWHP.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; apply (Contracts.lb_sub _ _ _ _ _ LVF); lia|].
    repeat (apply Forall_cons; [right; left; cbn [fst snd]; apply (Contracts.lb_sub _ _ _ _ _ LVP); lia|]).
    apply Forall_nil.
  Qed.

  #[using="q len m0 HOK RF0"] Lemma WL_dj_stack : forall q' a n, q' + 152 <= a -> lo <= q' + 152 -> 0 <= n -> disjoint_from (WL q') a n.
  Proof.
    intros q' a n Ha Hl Hn. hokA HOK. destruct hframe_facts as (FLO & FHI & _). pose proof (fsb_ok FI) as (B1 & B2 & _).
    unfold hWL, hWHP. cbn [disjoint_from]. repeat (split; [right; lia|]). exact I.
  Qed.
  #[using="q len m0 HOK RF0"] Lemma WL_dj_frame : forall q' a n,
    (F <= a /\ a + n <= F + 160) \/ (F + 176 <= a /\ a + n <= F + 256) \/ (SF <= a /\ a + n <= SF + 32) \/ (a = FL /\ n = 1) ->
    disjoint_from (WL q') a n.
  Proof.
    intros q' a n HP. pose proof fs_shadow_band as (S1 & S2 & S3). pose proof text_out_fs as (T1 & T2).
    hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    assert (PSH : P + 504 <= SF \/ SF + 32 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 32 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    unfold hWL, hWHP. cbn [disjoint_from].
    split; [left; clear - HP FHI B2 CLO S3 SHF2 FLHI; lia|].
    split; [clear - HP T1 T2 FLO FHI SHF1 SHF2 FLLO FLHI B1; lia|].
    split; [clear - HP FLO FHI SHF1 SHF2 FLLO FLHI B1 S1 S2; pose proof (fs_shadow_apart FI); lia|].
    repeat (split; [clear - HP PAF PAFL PSH; lia|]). exact I.
  Qed.

  #[using="Type"] Lemma hpm_refl : forall m, hpm m m.
  Proof. intros m meth C. exists meth. split; [exact C| left; reflexivity]. Qed.
  #[using="Type"] Lemma hpm_step : forall (W : list ivl) mb m m', hpm mb m -> munch W m m' -> wmono asegs m m' -> disjoint_from W (P + 4) 4 -> hpm mb m'.
  Proof.
    intros W mb m m' HP MU WM DJ meth C. destruct (HP meth C) as (meth' & C' & OR). exists meth'. split; [| exact OR].
    eapply rw_cells_transport; [exact C'| exact MU| exact WM| simpl_sizes; exact DJ].
  Qed.
  #[using="Type"] Lemma hpm_fkeep : forall (W : list ivl) (stx : fsstate FI) mb m m', hpm mb m -> fkeep FI W stx m m' -> wmono asegs m m' ->
    lb (fs_live FI stx) P 504 -> disjoint_from W (P + 4) 4 -> hpm mb m'.
  Proof.
    intros W stx mb m m' HP FK WM LV DJ meth C. destruct (HP meth C) as (meth' & C' & OR). exists meth'. split; [| exact OR].
    eapply (rw_cells_fkeep FI W stx); [exact C'| exact FK| exact WM| left; apply (Contracts.lb_sub _ _ _ _ _ LV); simpl_sizes; lia| simpl_sizes; exact DJ].
  Qed.
  #[using="Type"] Lemma hpm_set : forall mb m m', hpm mb m -> rw_cells asegs m' (P + 4) [C4 (wz 11)] -> hpm mb m'.
  Proof. intros mb m m' HP C meth C0. exists 11. split; [exact C| right; reflexivity]. Qed.
  #[using="q len m0 HOK RF0"] Lemma WL_dj_meth : forall q', lo <= q' + 152 -> disjoint_from (WL q') (P + 4) 4.
  Proof.
    intros q' Hl. hokA HOK. destruct hframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    unfold hWL, hWHP. cbn [disjoint_from]. split; [clear - PHI CLO Hl; lia|]. split; [clear - TFS PF1 PF2; lia|].
    split; [clear - PAF; lia|]. split; [clear; lia| exact I].
  Qed.

  Definition hWok (W : list ivl) (q' : Z) : Prop :=
    app_ivs W /\ env_safe W /\ sub_fp W W0 /\ Forall (fk_ok FI WHS st) W
    /\ (forall stc m m', hlive stc -> RFAKE FI stc m -> munch W m m' -> wmono asegs m m' -> RFAKE FI stc m')
    /\ (forall a n, q' + 152 <= a -> 0 <= n -> disjoint_from W a n)
    /\ (forall a n, (F <= a /\ a + n <= F + 160) \/ (F + 176 <= a /\ a + n <= F + 256) \/ (SF <= a /\ a + n <= SF + 32) \/ (a = FL /\ n = 1) ->
                    disjoint_from W a n).
  #[using="len m0 HOK RF0"] Lemma WL_ok : forall q', q + -272 <= q' <= q + -256 -> hWok (WL q') q'.
  Proof.
    intros q' QB. hokA HOK.
    split; [exact (WL_app q')|]. split; [exact (WL_env q')|]. split; [apply (WL_sub0 q'); clear - QB; lia|]. split; [exact (WL_fk q')|].
    split; [intros stc m m' HL RF MU WM; exact (WL_rf q' stc m m' HL RF MU WM)|].
    split; [intros a n Ha Hn; apply WL_dj_stack; [exact Ha| clear - QB LO; lia| exact Hn]|].
    intros a n HP. exact (WL_dj_frame q' a n HP).
  Qed.

  #[using="len m0 HOK RF0"] Lemma hrest_stepG : forall (W : list ivl) t q' mb m m', hWok W q' -> hrestT t q' mb m -> munch W m m' -> wmono asegs m m' -> hpm mb m' ->
    hrestT t q' mb m'.
  Proof.
    intros W t q' mb m m' (WA & WE & WSUB & WFK & WRF & DJS & DJF)
      (Hq & GAP & FRhi & FH & (j1 & FT1) & (j2 & FT2) & (j3 & FT3) & FLP & SHF & FLG & MU & WM & FK & (stc & RF & LIVE1) & _) MUL WML HPM'.
    pose proof HOK as HOK'. hokA HOK'.
    assert (QB : q + -272 <= q' <= q + -256) by (clear - Hq; lia).
    pose proof (hlive_of stc LIVE1) as HL.
    unfold hrestT.
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUL| exact WML| apply DJS; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUL| exact WML| apply DJS; [lia| simpl_sizes; lia]]|].
    split; [eapply rw_cells_transport; [exact FH| exact MUL| exact WML| apply DJF; left; simpl_sizes; lia]|].
    split; [exists j1; eapply rw_cells_transport; [exact FT1| exact MUL| exact WML| apply DJF; left; simpl_sizes; lia]|].
    split; [exists j2; eapply rw_cells_transport; [exact FT2| exact MUL| exact WML| apply DJF; left; simpl_sizes; lia]|].
    split; [exists j3; eapply rw_cells_transport; [exact FT3| exact MUL| exact WML| apply DJF; right; left; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact FLP| exact MUL| exact WML| apply DJF; right; left; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact SHF| exact MUL| exact WML| apply DJF; right; right; left; unfold hshadow; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MUL| exact WML| apply DJF; right; right; right; simpl_sizes; lia]|].
    split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [exact WSUB| exact MUL]|].
    split; [eapply wmono_trans; [exact WM| exact WML]|].
    split. { eapply fkeep_trans; [exact FK|]. destruct HL as (_ & _ & _ & _ & LSUB). exact (fkeep_of_munch FI WHS W st stc m m m' RF LSUB MUL WFK). }
    split; [exists stc; split; [exact (WRF stc m m' HL RF MUL WML)| exact LIVE1]|].
    exact HPM'.
  Qed.
  #[using="Type"] Lemma hrest_hpm : forall t q' mb m, hrestT t q' mb m -> hpm mb m.
  Proof. intros t q' mb m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
  #[using="Type"] Lemma hrest_qb : forall t q' mb m, hrestT t q' mb m -> q + -272 <= q' <= q + -256.
  Proof. intros t q' mb m (Hq & _). clear - Hq. lia. Qed.
  #[using="len m0 HOK RF0"] Lemma hrest_stepW : forall t q' mb m m', hrestT t q' mb m -> munch (WL q') m m' -> wmono asegs m m' -> hrestT t q' mb m'.
  Proof.
    intros t q' mb m m' HR MUL WML. pose proof (hrest_qb t q' mb m HR) as QB. hokA HOK.
    apply (hrest_stepG (WL q') t q' mb m m' (WL_ok q' QB) HR MUL WML).
    exact (hpm_step (WL q') mb m m' (hrest_hpm t q' mb m HR) MUL WML (WL_dj_meth q' ltac:(clear - QB LO; lia))).
  Qed.

  #[using="HC FI P A len cap st HOK"] Lemma sh_window_ok : SH_LO <= sh lo - sh lo mod 8 /\ sh lo - sh lo mod 8 <= sh lo /\ sh q <= SH_HI /\ sh q + 8 <= SH_HI.
  Proof.
    hokA HOK. destruct (stack_window_lo FI lo CLO) as [S1 _]. pose proof (stack_lo_ok lo).
    pose proof (sh_hi_ok q ltac:(lia)). pose proof (sh_hi_ok8 q ltac:(lia)). repeat split; assumption.
  Qed.

  #[using="m0 HOK RF0"] Lemma hinv_stepG : forall (W : list ivl) t (scr scr' : Z -> mem -> Prop) q' cur ty tb tl va vl bs cur' ty' tb' tl' va' vl' bs' mb m m',
    hWok W q' ->
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch W m m' -> wmono asegs m m' -> hpm mb m' ->
    stk asegs m' lo q' -> scr' q' m' ->
    rw_cells asegs m' (q' + 132) [C4 ty'; C8 tb'; C8 tl'] ->
    rw_cells asegs m' (F + 160) [C8 va'; C8 vl'] ->
    rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] ->
    rw_cells asegs m' MB (mbuf_cells A len cap) ->
    rw_cells asegs m' A [CB (Z.to_nat (cap + 1)) bs'] ->
    mem_inv asegs m' -> 0 <= cur' <= len ->
    hinvGT t scr' q' cur' ty' tb' tl' va' vl' bs' mb m'.
  Proof.
    intros W t scr scr' q' cur ty tb tl va vl bs cur' ty' tb' tl' va' vl' bs' mb m m' WOK
      (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & QBA & HR) MUL WML HPM' ST' SCR' TOK' VAL' SC' MBC' TXT' MI' CR'.
    pose proof WOK as (WA & WE & _). destruct sh_window_ok as (W1 & W2 & W3 & W4).
    unfold hinvGT. repeat (split; [assumption|]).
    split; [exact (asan_env_frame asegs m m' W AE MUL WML WE)|].
    split; [exact (shw_frame _ _ _ _ _ SHP MUL WA)|]. split; [exact (shw_frame _ _ _ _ _ SHA MUL WA)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MUL WA)|]. split; [exact (shw_frame _ _ _ _ _ SHFMT MUL WA)|].
    split; [eapply shz_frame; [exact SHZ| lia| lia| exact MUL| exact WA]|].
    split; [eapply shr_frame; [exact SHR| lia| lia| exact MUL| exact WA]|].
    split; [exact CR'|]. split; [exact QBA|]. exact (hrest_stepG W t q' mb m m' WOK HR MUL WML HPM').
  Qed.

  #[using="m0 HOK RF0"] Lemma hinv_stepW : forall t (scr scr' : Z -> mem -> Prop) q' cur ty tb tl va vl bs cur' ty' tb' tl' va' vl' bs' mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch (WL q') m m' -> wmono asegs m m' ->
    stk asegs m' lo q' -> scr' q' m' ->
    rw_cells asegs m' (q' + 132) [C4 ty'; C8 tb'; C8 tl'] ->
    rw_cells asegs m' (F + 160) [C8 va'; C8 vl'] ->
    rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] ->
    rw_cells asegs m' MB (mbuf_cells A len cap) ->
    rw_cells asegs m' A [CB (Z.to_nat (cap + 1)) bs'] ->
    mem_inv asegs m' -> 0 <= cur' <= len ->
    hinvGT t scr' q' cur' ty' tb' tl' va' vl' bs' mb m'.
  Proof.
    intros t scr scr' q' cur ty tb tl va vl bs cur' ty' tb' tl' va' vl' bs' mb m m'
      (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & QBA & HR) MUL WML ST' SCR' TOK' VAL' SC' MBC' TXT' MI' CR'.
    pose proof (WL_app q') as WA. destruct sh_window_ok as (W1 & W2 & W3 & W4).
    unfold hinvGT. repeat (split; [assumption|]).
    split; [exact (asan_env_frame asegs m m' (WL q') AE MUL WML (WL_env q'))|].
    split; [exact (shw_frame _ _ _ _ _ SHP MUL WA)|]. split; [exact (shw_frame _ _ _ _ _ SHA MUL WA)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MUL WA)|]. split; [exact (shw_frame _ _ _ _ _ SHFMT MUL WA)|].
    split; [eapply shz_frame; [exact SHZ| lia| lia| exact MUL| exact WA]|].
    split; [eapply shr_frame; [exact SHR| lia| lia| exact MUL| exact WA]|].
    split; [exact CR'|]. split; [exact QBA|]. exact (hrest_stepW t q' mb m m' HR MUL WML).
  Qed.

  Definition hWC : list ivl := [(S + 8, S + 16); (F + 160, F + 176)]%Z.
  Notation WC := hWC.
  Definition hWF (q' : Z) : list ivl := ((lo, q') :: FSIV WC)%Z.
  Notation WF := hWF.

  #[using="Type"] Lemma fkeep_weaken_fkH : forall W Wc sta stb m mx m',
    fkeep FI Wc stb m m' -> RFAKE FI sta mx -> (forall g, In g (fs_live FI sta) -> In g (fs_live FI stb)) ->
    Forall (fk_ok FI W sta) Wc -> fkeep FI W sta m m'.
  Proof.
    intros W Wc sta stb m mx m' H HR HL OK a Ha (g & Hg & Hp) Ho.
    apply H; [exact Ha| exists g; split; [apply HL; exact Hg| exact Hp]|].
    apply Contracts.outside_of_forall. eapply Forall_impl; [| exact OK]. intros [lo' hi'] K0. unfold fk_ok, fst, snd in K0. unfold fst, snd.
    destruct K0 as [K0|[K0|K0]].
    - intros Hr. apply (inside_not_outside W lo' (hi' - lo') a K0); [lia| exact Ho].
    - pose proof (live_pieces_inside FI sta mx g a HR Hg Hp) as X. lia.
    - rewrite Forall_forall in K0. specialize (K0 g Hg). unfold fst, snd in K0. unfold in_pieces in Hp. lia.
  Qed.

  #[using="m0 RF0"] Lemma WC_fk : Forall (fk_ok FI WHS st) WC.
  Proof.
    pose proof (new_frame_fk FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    unfold hWC, hWHS.
    apply Forall_cons; [unfold fk_ok; left; cbn [inside fst snd]; lia|].
    apply Forall_cons; [replace (F + 176) with (F + 160 + 16) by lia; apply NFK; cbn [FB_of SB_of]; lia|].
    apply Forall_nil.
  Qed.

  #[using="q lo A len cap m0 HOK RF0"] Lemma WC_app : app_ivs WC.
  Proof.
    hokA HOK. destruct hframe_facts as (FLO & FHI & _). pose proof (fsb_ok FI) as (B1 & _).
    destruct (lb_in_fsH _ _ PLB) as [H1 H2]. unfold hWC.
    constructor; [apply sub_app_iv_fsH; lia|]. constructor; [apply sub_app_iv_fsH; lia|]. constructor.
  Qed.
  #[using="q A len cap m0 HOK RF0"] Lemma WF_fsw : forall q', Forall (fsw_iv FI) (WF q').
  Proof.
    intros q'. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold hWF. apply fsw_cons_app; [apply app_iv_stack; lia|]. apply fsw_FSIV. exact WC_app.
  Qed.
  #[using="q A len cap m0 HOK RF0"] Lemma WF_env : forall q', env_safe (WF q').
  Proof.
    intros q'. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & _). destruct hframe_facts as (FLO & _). destruct (lb_in_fsH _ _ PLB) as [H1 H2].
    pose proof fs_shadow_band as (S1 & _).
    unfold env_safe, hWF, hWC. repeat (constructor; [left; cbn [fst snd]; lia|]). constructor.
  Qed.
  #[using="len m0 HOK RF0"] Lemma WF_sub0 : forall q', q' <= q -> sub_fp (WF q') W0.
  Proof.
    intros q' HQ. destruct hframe_facts as (FLO & FHI & _).
    unfold sub_fp, hWF, hWC, hW0, hWHS. intros xo Ho. cbn [outside] in *.
    destruct Ho as (H1 & H2 & H3 & H4 & H5 & H6 & _).
    repeat split; try assumption; lia.
  Qed.
  #[using="q A len cap m0 HOK RF0"] Lemma WF_dj_stack : forall q' a n, q' <= a -> lo <= q' -> 0 <= n -> disjoint_from (WF q') a n.
  Proof.
    intros q' a n Ha Hl Hn. hokA HOK. destruct hframe_facts as (FLO & FHI & _). pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof fs_shadow_band as (S1 & S2 & S3).
    unfold hWF, hWC. cbn [disjoint_from]. repeat (split; [right; lia|]). exact I.
  Qed.
  #[using="q lo A len cap m0 HOK RF0"] Lemma WC_dj_frame : forall a n,
    (F <= a /\ a + n <= F + 160) \/ (F + 176 <= a /\ a + n <= F + 256) \/ (SF <= a /\ a + n <= SF + 32) \/ (a = FL /\ n = 1) ->
    disjoint_from WC a n.
  Proof.
    intros a n HP. pose proof fs_shadow_band as (S1 & S2 & S3).
    hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    assert (PSH : P + 504 <= SF \/ SF + 32 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 32 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    unfold hWC. cbn [disjoint_from].
    split; [clear - HP PAF PAFL PSH; lia|].
    split; [clear - HP FLO FHI SHF1 SHF2 FLLO FLHI B1 S1 S2; pose proof (fs_shadow_apart FI); lia|]. exact I.
  Qed.

  #[using="len m0 HOK RF0"] Lemma hrest_stepF : forall t q' mb m m' stc st',
    hrestT t q' mb m -> fs_live FI stc = fs_newff FI st 2 :: fs_live FI st ->
    munch (WF q') m m' -> wmono asegs m m' -> fkeep FI WC stc m m' ->
    fs_live FI st' = fs_live FI stc -> RFAKE FI st' m' -> hrestT t q' mb m'.
  Proof.
    intros t q' mb m m' stc st' (Hq & GAP & FRhi & FH & (j1 & FT1) & (j2 & FT2) & (j3 & FT3) & FLP & SHF & FLG & MU & WM & FK & _ & HPM) LIVE1 MUF WMF FKc LIVE' RF'.
    pose proof HOK as HOK'. hokA HOK'.
    assert (QB : q + -272 <= q' <= q + -256) by (clear - Hq; lia).
    assert (DJS : forall a n, q' <= a -> 0 <= n -> disjoint_from (WF q') a n) by (intros a n Ha Hn; apply WF_dj_stack; lia).
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    assert (ILF : forall a n, F <= a -> a + n <= F + 256 -> in_live FI stc a n) by (intros a n H1 H2; left; apply (Contracts.lb_sub _ _ _ _ _ LVF); lia).
    unfold hrestT.
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUF| exact WMF| apply DJS; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUF| exact WMF| apply DJS; [lia| simpl_sizes; lia]]|].
    split; [eapply (rw_cells_fkeep FI WC stc); [exact FH| exact FKc| exact WMF| apply ILF; simpl_sizes; lia| apply WC_dj_frame; left; simpl_sizes; lia]|].
    split; [exists j1; eapply (rw_cells_fkeep FI WC stc); [exact FT1| exact FKc| exact WMF| apply ILF; simpl_sizes; lia| apply WC_dj_frame; left; simpl_sizes; lia]|].
    split; [exists j2; eapply (rw_cells_fkeep FI WC stc); [exact FT2| exact FKc| exact WMF| apply ILF; simpl_sizes; lia| apply WC_dj_frame; left; simpl_sizes; lia]|].
    split; [exists j3; eapply (rw_cells_fkeep FI WC stc); [exact FT3| exact FKc| exact WMF| apply ILF; simpl_sizes; lia| apply WC_dj_frame; right; left; simpl_sizes; lia]|].
    split; [eapply (rw_cells_fkeep FI WC stc); [exact FLP| exact FKc| exact WMF| apply ILF; simpl_sizes; lia| apply WC_dj_frame; right; left; simpl_sizes; lia]|].
    split; [eapply (rw_cells_fkeep FI WC stc); [exact SHF| exact FKc| exact WMF| right; left; apply (ls_sub _ _ _ _ _ LVS); unfold hshadow; simpl_sizes; lia| apply WC_dj_frame; right; right; left; unfold hshadow; simpl_sizes; lia]|].
    split; [eapply (rw_cells_fkeep FI WC stc); [exact FLG| exact FKc| exact WMF| right; right; split; [exact LVL| simpl_sizes; lia]| apply WC_dj_frame; right; right; right; simpl_sizes; lia]|].
    split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [apply (WF_sub0 q'); lia| exact MUF]|].
    split; [eapply wmono_trans; [exact WM| exact WMF]|].
    split; [eapply fkeep_trans; [exact FK|]; exact (fkeep_weaken_fkH WHS WC st stc m m0 m' FKc RF0 LSUB WC_fk)|].
    split; [exists st'; split; [exact RF'| rewrite LIVE'; exact LIVE1]|].
    apply (hpm_fkeep WC stc mb m m' HPM FKc WMF LVP). unfold hWC. cbn [disjoint_from]. split; [clear; lia|].
    destruct hframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & PAF & _). split; [clear - PAF; lia| exact I].
  Qed.

  #[using="Type"] Lemma hrest_rf : forall t q' mb m, hrestT t q' mb m -> exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 2 :: fs_live FI st.
  Proof. intros t q' mb m HR. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HR)))))))))))))). Qed.

  #[using="q lo A len cap m0 HOK RF0"] Lemma WC_fsout : forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside WC a.
  Proof.
    intros a Ha. hokA HOK. destruct hframe_facts as (FLO & FHI & _). pose proof (fsb_ok FI) as (B1 & _).
    destruct (lb_in_fsH _ _ PLB) as [H1 H2]. pose proof (fs_shadow_apart FI) as AP.
    unfold hWC. cbn [outside]. repeat split; try exact I; lia.
  Qed.

  #[using="m0 HOK RF0"] Lemma hinv_stepF : forall q' cur ty tb tl va vl bs cur' va' vl' mb m m' stc st',
    hinv q' cur ty tb tl va vl bs mb m ->
    RFAKE FI stc m -> fs_live FI stc = fs_newff FI st 2 :: fs_live FI st ->
    munch (WF q') m m' -> wmono asegs m m' -> fkeep FI WC stc m m' ->
    fs_live FI st' = fs_live FI stc -> RFAKE FI st' m' ->
    stk asegs m' lo q' -> rw_cells asegs m' (F + 160) [C8 va'; C8 vl'] ->
    rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] ->
    mem_inv asegs m' -> asan_env asegs m' -> 0 <= cur' <= len ->
    hinv q' cur' ty tb tl va' vl' bs mb m'.
  Proof.
    intros q' cur ty tb tl va vl bs cur' va' vl' mb m m' stc st'
      (ST & (j0 & w32 & j96 & j128 & SCR) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & QBA & HR)
      RF LIVE1 MUF WMF FKc LIVE' RF' ST' VAL' SC' MI' AE' CR'.
    pose proof (WF_fsw q') as WA. destruct sh_window_ok as (W1 & W2 & W3 & W4).
    pose proof HOK as HOK'. hokA HOK'. pose proof text_out_fs as (T1 & T2).
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    assert (DJS : forall a n, q' <= a -> 0 <= n -> disjoint_from (WF q') a n) by (intros a n Ha Hn; apply WF_dj_stack; lia).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _). pose proof fs_shadow_band as (S1 & S2 & S3).
    unfold hinv, hinvGT.
    split; [exact ST'|].
    split; [exists j0, w32, j96, j128; eapply rw_cells_transport; [exact SCR| exact MUF| exact WMF| apply DJS; [lia| simpl_sizes; lia]]|].
    split; [eapply rw_cells_transport; [exact TOK| exact MUF| exact WMF| apply DJS; [lia| simpl_sizes; lia]]|].
    split; [exact VAL'|]. split; [exact SC'|].
    split. { eapply (rw_cells_fkeep FI WC stc); [exact MBC| exact FKc| exact WMF| left; apply (Contracts.lb_sub _ _ _ _ _ LVP); unfold mbuf_cells; simpl_sizes; lia|].
             unfold hWC, mbuf_cells. cbn [disjoint_from]. simpl_sizes. split; [lia|]. split; [clear - PAF; lia| exact I]. }
    split. { eapply rw_cells_transport; [exact TXT| exact MUF| exact WMF|]. unfold hWF, hWC. cbn [disjoint_from cells_size csize Nat.add].
             rewrite Nat.add_0_r, Z2Nat.id by lia.
             split; [left; lia|]. split; [clear - TFS; lia|]. split; [clear - T2; lia|]. split; [clear - TFS PF1 PF2; lia|]. split; [clear - TFS FLO FHI B1; lia| exact I]. }
    split; [exact MI'|]. split; [exact AE'|].
    split; [exact (shw_fkeep FI WC stc m m' P 504 SHP FKc RF LVP WC_fsout)|].
    split; [exact (shw_frame_fs FI _ _ _ _ _ SHA MUF WA TFS)|].
    split; [apply (shw_frame_fs FI _ _ _ _ _ SHSEP MUF WA); left; unfold SEPTAB_A; lia|].
    split; [apply (shw_frame_fs FI _ _ _ _ _ SHFMT MUF WA); left; lia|].
    split; [eapply (shz_stack_fs FI); [exact SHZ| exact CLO| lia| lia| exact MUF| exact WA]|].
    split; [eapply (shr_stack_fs FI); [exact SHR| exact CLO| lia| lia| exact MUF| exact WA]|].
    split; [exact CR'|]. split; [exact QBA|].
    exact (hrest_stepF 248 q' mb m m' stc st' HR LIVE1 MUF WMF FKc LIVE' RF').
  Qed.

  #[using="Type"] Lemma hscr_E : forall q' m, hscr q' m -> hscrE q' m.
  Proof.
    intros q' m (j0 & w32 & j96 & j128 & SCR).
    split_chunk SCR 11%nat S1 S2. split_chunk S2 1%nat S3 S4.
    lazymatch type of S1 with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge asegs m q' [] cs []) as M1 end.
    lazymatch type of S4 with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge asegs m (q' + 96) [] cs []) as M4 end.
    rewrite !app_nil_r in M1, M4. cbn [app cells_size csize Nat.add] in M1, M4. specialize (M1 S1). specialize (M4 S4).
    split; [eexists; exact M1|]. split; [exact S3| eexists; exact M4].
  Qed.
  #[using="Type"] Lemma hinv_E : forall q' cur ty tb tl va vl bs mb m, hinv q' cur ty tb tl va vl bs mb m -> hinvE q' cur ty tb tl va vl bs mb m.
  Proof.
    intros q' cur ty tb tl va vl bs mb m (ST & SCR & REST). split; [exact ST|]. split; [exact (hscr_E q' m SCR)| exact REST].
  Qed.

  #[using="HC FI P A len cap st HOK"] Lemma tok_shwH : forall q' m X n, shz m (sh lo) (sh q) -> q + -272 <= q' <= q + -256 -> q' + 8 <= X -> X + n <= q' + 152 -> 0 <= n -> shw m X n.
  Proof.
    intros q' m X n SHZ QB H1 H2 Hn. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    eapply (shw_of_shz m (sh lo) (sh q) X n SHZ).
    - unfold win_ok. split; [exact Hn|]. right. change (2^47) with 140737488355328 in *. lia.
    - unfold sh, SHADOW_OFF. clear - H1 QB LO. Z.div_mod_to_equations. lia.
    - unfold sh, SHADOW_OFF. clear - H2 QB. Z.div_mod_to_equations. lia.
  Qed.

  Definition hWS (q' : Z) : list ivl := [(lo, q'); (S + 8, S + 16); (q' + 136, q' + 136 + 16); (q' + 132, q' + 132 + 4)]%Z.
  Notation WS := hWS.

  #[using="Type"] Lemma WS_sub : forall q', lo <= q' -> sub_fp (WS q') (WL q').
  Proof.
    intros q' HQ. unfold sub_fp, hWS, hWL, hWHP. intros xo Ho. cbn [outside] in *.
    destruct Ho as (H1 & H2 & H3 & H4 & _). repeat split; try exact I; lia.
  Qed.

  #[using="HC FI q lo P len st HOK"] Lemma text_bytesH : forall m bs, rw_cells asegs m A [CB (Z.to_nat (cap + 1)) bs] -> bytes_at asegs m A bs /\ Z.of_nat (length bs) = cap + 1.
  Proof.
    intros m bs TXT. hokA HOK. pose proof (rw_cells_bytes_at asegs _ _ _ TXT) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
    destruct TXT as [[W _] _]. cbn in W. destruct W as [W _]. split; [exact B| lia].
  Qed.

  #[using="q len m0 HOK RF0"] Lemma WS_dj_obj : forall q' a n, lo <= q' ->
    (F + 160 <= a /\ a + n <= F + 176) \/ (MB <= a /\ a + n <= MB + 32) \/ (A <= a /\ a + n <= A + (cap + 1)) ->
    disjoint_from (WS q') a n.
  Proof.
    intros q' a n HQ HP. hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    unfold hWS. cbn [disjoint_from].
    split; [left; clear - HP FHI B2 CLO HQ PF2 AHI; lia|].
    split; [clear - HP PAF TFS PF1 PF2; lia|].
    split; [left; clear - HP FHI B2 CLO HQ PF2 AHI; lia|].
    split; [left; clear - HP FHI B2 CLO HQ PF2 AHI; lia| exact I].
  Qed.

  #[using="m0 HOK RF0"] Lemma hinv_stepS : forall t (scr scr' : Z -> mem -> Prop) q' cur ty tb tl va vl bs cur' ty' tb' tl' mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch (WS q') m m' -> wmono asegs m m' ->
    stk asegs m' lo q' -> scr' q' m' ->
    rw_cells asegs m' (q' + 132) [C4 ty'; C8 tb'; C8 tl'] ->
    rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] ->
    mem_inv asegs m' -> 0 <= cur' <= len ->
    hinvGT t scr' q' cur' ty' tb' tl' va vl bs mb m'.
  Proof.
    intros t scr scr' q' cur ty tb tl va vl bs cur' ty' tb' tl' mb m m' INV MUS WMS ST' SCR' TOK' SC' MI' CR'.
    pose proof INV as (ST & _ & _ & VAL & _ & MBC & TXT & _ & _ & _ & _ & _ & _ & _ & _ & _ & (QB & _) & _).
    pose proof HOK as HOK'. hokA HOK'.
    assert (LQ : lo <= q') by (clear - QB LO; lia).
    eapply (hinv_stepW t scr scr' q' cur ty tb tl va vl bs cur' ty' tb' tl' va vl bs mb m m' INV);
      [eapply munch_weaken; [exact (WS_sub q' LQ)| exact MUS]| exact WMS| exact ST'| exact SCR'| exact TOK'| | exact SC'| | | exact MI'| exact CR'].
    - eapply rw_cells_transport; [exact VAL| exact MUS| exact WMS| apply WS_dj_obj; [exact LQ| left; simpl_sizes; lia]].
    - eapply rw_cells_transport; [exact MBC| exact MUS| exact WMS| apply WS_dj_obj; [exact LQ| right; left; unfold mbuf_cells; simpl_sizes; lia]].
    - eapply rw_cells_transport; [exact TXT| exact MUS| exact WMS| apply WS_dj_obj; [exact LQ| right; right; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]].
  Qed.

  #[using="A len cap m0 HOK RF0"] Lemma hscr_stepS : forall q' m m', q + -272 <= q' -> hscr q' m -> munch (WS q') m m' -> wmono asegs m m' -> hscr q' m'.
  Proof.
    intros q' m m' QB (j0 & w32 & j96 & j128 & SCR) MUS WMS. exists j0, w32, j96, j128.
    hokA HOK. destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    eapply rw_cells_transport; [exact SCR| exact MUS| exact WMS|]. unfold hWS. cbn [disjoint_from]. simpl_sizes.
    repeat split; try exact I; lia.
  Qed.

  #[using="IC m0 HOK RF0"] Lemma sgt_callH : forall t (scr : Z -> mem -> Prop) (q' cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem)
      (ra' gp' tp' t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 : word) (Q : machine_state -> Prop),
    hinvGT t scr q' cur ty tb tl va vl bs mb m ->
    (forall m', scr q' m -> munch (WS q') m m' -> wmono asegs m m' -> scr q' m') ->
    (forall m' (tlz ty' : Z) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinvGT t scr q' (cur + tlz) (wz ty') (wz (A + cur)) (wz tlz) va vl bs mb m' ->
       1 <= tlz -> cur + tlz <= len -> 0 <= ty' <= 5 -> ((ty' = TT_IDENTIFIER \/ ty' = TT_WHITESPACE) -> cur + tlz < len) ->
       (ty' = TT_CRLF -> tlz <= 2) ->
       evt asegs Q (MS (mkR ra' (wz q') gp' tp' y5 y6 y7 s0' s1' (wz PARSE_OK) y11 y12 y13 y14 y15 y16 y17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' y28 y29 y30 y31)
                       F_ (ret_pc ra') fc None m' (seg_rom asegs))) ->
    (forall m' (r : Z) (tb' tl' : word) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinvGT t scr q' cur ty tb' tl' va vl bs mb m' -> (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE) ->
       evt asegs Q (MS (mkR ra' (wz q') gp' tp' y5 y6 y7 s0' s1' (wz r) y11 y12 y13 y14 y15 y16 y17 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' y28 y29 y30 y31)
                       F_ (ret_pc ra') fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra' (wz q') gp' tp' t0 t1 t2 s0' s1' (wz S) (wz (q' + 136)) (wz (q' + 132)) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
                    F_ (wz sgt_entryA) fc None m (seg_rom asegs)).
  Proof.
    intros t scr q' cur ty tb tl va vl bs mb m ra' gp' tp' t0 t1 t2 s0' s1' a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 Q INV SCRT KOK KERR.
    pose proof INV as (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & (QB & QAL) & HR).
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (text_bytesH m bs TXT) as [BUF BL].
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    split_chunk TOK 1%nat TYC TKC.
    eapply evt_cut.
    { eapply (scanner_get_token_spec_A IC S (q' + 136) (q' + 132) MB A cur len cap lo bs tb tl ty q');
        [exact SC| exact MBC| exact BUF| lia| exact CR| lia| lia| exact TKC| exact TYC| exact AE
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | eapply (tok_shwH q'); [exact SHZ| exact QB| lia| lia| lia]
        | eapply (tok_shwH q'); [exact SHZ| exact QB| lia| lia| lia]
        | intros _; apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | exact SHSEP
        | lia| lia| clear - PAL; Z.div_mod_to_equations; lia
        | lia| lia| clear - PAL; Z.div_mod_to_equations; lia
        | lia| left; lia| clear - QAL; Z.div_mod_to_equations; lia
        | lia| lia| clear - QAL; Z.div_mod_to_equations; lia
        | lia| lia| lia| right; lia| right; lia| right; lia| clear - TFS PF1 PF2 BL; lia
        | exact ST| exact CLO| lia| unfold A0_RT_STACK in *; lia| exact MI| reflexivity| reflexivity| reflexivity]. }
    intros ms' POST. unfold sgt_post_A in POST.
    destruct POST as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & r & cur' & tb' & tl' & tyw' & -> & MUS & WMS & MI' & ST' & AE' & SC' & TKC' & TYC' & RES).
    join_chunks TYC' TKC' TOK'.
    assert (SCR' : scr q' m') by (apply (SCRT m' SCR); [exact MUS| exact WMS]).
    destruct RES as [(tlz & ty' & -> & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HRr & -> & ->)].
    - eapply (KOK m' tlz ty'); [| exact TL1| exact CL| exact TY5| exact STRICT| exact CRL].
      eapply (hinv_stepS t scr scr q' cur ty tb tl va vl bs (cur + tlz) _ _ _ mb m m' INV MUS WMS ST' SCR' TOK' SC' MI'). lia.
    - eapply (KERR m' r tb' tl'); [| exact HRr].
      eapply (hinv_stepS t scr scr q' cur ty tb tl va vl bs cur _ _ _ mb m m' INV MUS WMS ST' SCR' TOK' SC' MI'). lia.
  Qed.

  #[using="m0 HOK RF0"] Lemma hinv_stepX : forall t (scr scr' : Z -> mem -> Prop) q' cur ty tb tl va vl bs mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch [(lo, q' + 132)]%Z m m' -> wmono asegs m m' ->
    stk asegs m' lo q' -> scr' q' m' -> mem_inv asegs m' ->
    hinvGT t scr' q' cur ty tb tl va vl bs mb m'.
  Proof.
    intros t scr scr' q' cur ty tb tl va vl bs mb m m' INV MUX WMX ST' SCR' MI'.
    pose proof INV as (ST & _ & TOK & VAL & SC & MBC & TXT & _ & _ & _ & _ & _ & _ & _ & _ & CR & (QB & _) & _).
    pose proof HOK as HOK'. hokA HOK'. pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct hframe_facts as (FLO & FHI & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    assert (DJ : forall a n, (q' + 132 <= a) \/ (a + n <= alloc_ceiling) -> disjoint_from [(lo, q' + 132)]%Z a n)
      by (intros a n Ha; cbn [disjoint_from]; split; [lia| exact I]).
    eapply (hinv_stepW t scr scr' q' cur ty tb tl va vl bs cur ty tb tl va vl bs mb m m' INV);
      [eapply munch_weaken; [| exact MUX]| exact WMX| exact ST'| exact SCR'| | | | | | exact MI'| exact CR].
    - unfold sub_fp, hWL. intros xo Ho. cbn [outside] in *. destruct Ho as (H1 & _). split; [lia| exact I].
    - eapply rw_cells_transport; [exact TOK| exact MUX| exact WMX| apply DJ; left; lia].
    - eapply rw_cells_transport; [exact VAL| exact MUX| exact WMX| apply DJ; right; simpl_sizes; lia].
    - eapply rw_cells_transport; [exact SC| exact MUX| exact WMX| apply DJ; right; simpl_sizes; lia].
    - eapply rw_cells_transport; [exact MBC| exact MUX| exact WMX| apply DJ; right; unfold mbuf_cells; simpl_sizes; lia].
    - eapply rw_cells_transport; [exact TXT| exact MUX| exact WMX| apply DJ; right; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia].
  Qed.

  Definition hWE : list ivl := [(lo, q); (F, F + 256); (SF, SF + 32); (FL, FL + 1)]%Z.
  Notation WE := hWE.

  #[using="A len cap m0 HOK RF0"] Lemma WE_fk : Forall (fk_ok FI WHS st) WE.
  Proof.
    pose proof (new_frame_fk FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _). pose proof fs_shadow_band as (S1 & S2 & S3).
    unfold hWE.
    apply Forall_cons; [unfold fk_ok; right; left; cbn [fst snd]; lia|].
    apply Forall_cons; [apply NFK; cbn [FB_of SB_of]; lia|].
    apply Forall_cons; [apply NFK; cbn [FB_of SB_of]; lia|].
    apply Forall_cons; [apply NFK; cbn [FB_of SB_of]; lia|].
    apply Forall_nil.
  Qed.
  #[using="P A len cap m0 HOK RF0"] Lemma WE_fsw : Forall (fsw_iv FI) WE.
  Proof.
    hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _). pose proof (fsb_ok FI) as (B1 & _).
    unfold hWE. apply fsw_cons_app; [apply app_iv_stack; lia|]. apply fsw_cons_app; [apply sub_app_iv_fsH; lia|].
    constructor; [right; cbn [fst snd]; lia|]. apply fsw_cons_app; [apply sub_app_iv_fsH; lia| constructor].
  Qed.
  #[using="P A len cap m0 HOK RF0"] Lemma WE_env : env_safe WE.
  Proof.
    hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _). pose proof (fsb_ok FI) as (B1 & _).
    pose proof fs_shadow_band as (S1 & _).
    unfold env_safe, hWE. repeat (constructor; [left; cbn [fst snd]; lia|]). constructor.
  Qed.
  #[using="len m0 HOK RF0"] Lemma WE_sub0 : sub_fp WE W0.
  Proof.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _).
    unfold sub_fp, hWE, hW0. intros xo Ho. cbn [outside] in *. destruct Ho as (H1 & H2 & H3 & _).
    repeat split; try exact I; lia.
  Qed.

  #[using="len m0 HOK RF0"] Lemma WE_dj_obj : forall a n, (P <= a /\ a + n <= P + 504) \/ (A <= a /\ a + n <= A + (cap + 1)) -> disjoint_from WE a n.
  Proof.
    intros a n HP. hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _). pose proof text_out_fs as (T1 & T2).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    assert (PSH : P + 504 <= SF \/ SF + 32 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 32 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    unfold hWE. cbn [disjoint_from].
    split; [left; clear - HP PHI AHI CLO; lia|].
    split; [clear - HP PAF TFS FLO FHI B1; lia|].
    split; [clear - HP PSH T2 SHF1 SHF2; lia|].
    split; [clear - HP PAFL TFS FLLO FLHI B1; lia| exact I].
  Qed.

  #[using="q lo A len cap m0 HOK RF0"] Lemma shwP_fkeep : forall m m', shw m P 504 -> fkeep FI WHS st m m' -> shw m' P 504.
  Proof.
    intros m m' SW FK. hokA HOK. destruct PLB as (g & Hg & G1 & G2).
    pose proof (live_num FI st m0 RF0) as LN. rewrite Forall_forall in LN.
    destruct (LN g Hg) as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4 & F5).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (SB_mod8 (ff_class g)) as S8. change (SB_of (ff_class g)) with (ff_shsize g) in S8.
    assert (ESG : sh (ff_addr g) = ff_addr g / 8 + 2147450880) by reflexivity.
    pose proof (fs_shadow_apart FI) as SAP.
    eapply (shw_band_eq m m' P 504 (sh (ff_addr g)) (sh (ff_addr g) + ff_shsize g) SW).
    - intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (FK a _ _ _) Hv).
      + rewrite ESG in Ha. clear - Ha L1 L2 L6 F1 F2 ACR L7. Z.div_mod_to_equations. lia.
      + exists g. split; [exact Hg|]. right; left. exact Ha.
      + unfold hWHS. cbn [outside]. clear - Ha L8 L9 SAP G1 G2 L1 L2. repeat split; try exact I; lia.
    - rewrite ESG. clear - L1 F1. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L1 L2 L6 L7 F1 F2 ACR. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L3. Z.div_mod_to_equations. lia.
    - rewrite ESG. clear - L3 S8. Z.div_mod_to_equations. lia.
    - apply sh_mono. exact G1.
    - intros Hn. rewrite ESG. unfold sh, SHADOW_OFF. clear - G1 G2 L3 L6 Hn. Z.div_mod_to_equations. lia.
  Qed.

  Definition hpostE (r cur : Z) (bs : list byte) (mb m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch WE m m' /\ wmono asegs m m'
      /\ munch W0 mb m' /\ wmono asegs mb m' /\ fkeep FI WHS st mb m'
      /\ mem_inv asegs m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
      /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ rw_cells asegs m' S [C8 (wz MB); C8 (wz cur); C4 (wz 0)] /\ rw_cells asegs m' MB (mbuf_cells A len cap)
      /\ rw_cells asegs m' A [CB (Z.to_nat (cap + 1)) bs]
      /\ shw m' P 504 /\ shw m' A (cap + 1) /\ shz m' (sh lo) (sh q) /\ shr m' (sh lo - sh lo mod 8) (sh q + 8).

  Definition xstH (q' r sv : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz r) x11 x12 x13 x14 x15 x16 x17
            (wz sv) (wz F) (wz 2147450880) (wz F) x22 (wz (P + 488)) x24 x25 x26 (wz SF) x28 x29 x30 x31)
       F_ (wz 0x886f0) fc None m (seg_rom asegs).

  #[using="m0 HOK RF0"] Lemma exitH1 : forall (q' r sv cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinvE q' cur ty tb tl va vl bs mb m -> 0 <= sv <= len ->
    (forall m' y11 y18 y23, hinvE q' sv ty tb tl va vl bs mb m' ->
       evt asegs Q (epistH q' r x1 x5 x6 x7 y11 x12 x13 x14 x15 x16 x17 y18 x22 y23 x24 x25 x26 x28 x29 x30 x31 m')) ->
    evt asegs Q (xstH q' r sv x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' r sv cur ty tb tl va vl bs mb m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x28 x29 x30 x31 Q INV SV KE.
    pose proof INV as (ST & ((j88 & SCR1) & SCR2 & (j36 & SCR3)) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & _ & _ & _ & _ & _ & CR & (QB & QAL) & HR).
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide PAL. hide AAL. hide QAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof (munch_refl (WL q') m) as MUL. pose proof (wmono_refl asegs m) as WML. unfold hWL, hWHP in MUL.
    destruct hframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _).
    pose proof (munch_refl [(S + 8, S + 16)]%Z m) as MUc.
    unfold xstH, hSHC in *. clear HR.
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC. hide TXT.
    walk_to 0x887fc%Z.

    unhide TXT. unhide TFS.
    eapply (KE _ _ _ _).
    eapply (hinv_stepW 248 hscrE hscrE q' cur ty tb tl va vl bs sv ty tb tl va vl bs mb m m1 INV MUL WML ST); [| exact TOK| exact VAL| exact SC| exact MBC| | exact MI| exact SV].
    - split; [exists j88; exact SCR1|]. split; [exact SCR2| exists j36; exact SCR3].
    - eapply rw_cells_transport; [exact TXT| exact MUc| exact WML|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      split; [clear - TFS PF1 PF2; lia| exact I].
  Qed.

  #[using="m0 HOK RF0"] Lemma epiH : forall (q' r cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    hinvE q' cur ty tb tl va vl bs mb m ->
    evt asegs (hpostE r cur bs mb m)
      (epistH q' r x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' r cur ty tb tl va vl bs mb m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x26 x28 x29 x30 x31 INV.
    unfold epistH.
    destruct INV as (ST & ((j88 & SCR1) & SCR2 & (j36 & SCR3)) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & _ & _ & SHZ & SHR & CR & (QB & QAL) & HR).
    destruct HR as (Hq & GAP & FRhi & FH & (j1 & FT1) & (j2 & FT2) & (j3 & FT3) & FLP & SHF & FLG & MU & WM & FK & (stc & RF & LIVE1) & _).
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide PAL. hide AAL. hide QAL. hide Hq.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & _). hide FSB4.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL). hide FAL. hide PAF. hide PAFL.
    pose proof fs_shadow_band as (SB1 & SB2 & SB3). pose proof (fs_shadow_apart FI) as FSAP.
    pose proof (new_frame_fk FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).

    hide2 ST. hide2 SCR1. hide2 SCR2. hide2 SCR3. hide2 TOK. hide2 GAP. hide2 VAL. hide2 FT1. hide2 FT2. hide2 FT3.
    hide2 SC. hide2 MBC. hide2 TXT. hide2 SHP. hide2 SHA. hide2 SHZ. hide2 SHR. hide2 MU. hide2 WM.
    pose proof (munch_refl [(F, F + 8); (SF, SF + 32); (FL, FL + 1)]%Z m) as MUw. pose proof (wmono_refl asegs m) as WMw.
    pose proof (munch_refl [(F, F + 8); (SF, SF + 32)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    pose proof RF as RFm.
    unfold hshadow in SHF.
    zstep. sstep. sstep.
    zstep. zstep. sstep.
    step. if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 32)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except SHF. unhide MUs. unhide WMs.
    do 32 sstep.
    unhide_transport MUs WMs. clear MUs WMs.
    zstep.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
    sstep.
    env_sync AE MU0 WM0. fk_sync FI RF MU0 FK LSUB.
    unhide2 FT1. unhide2 FT2. unhide2 VAL. unhide2 FT3.
    apply (rw_cells_transport asegs _ m m2) with (2 := MUw) (3 := WMw) in FT1; [| cbn [disjoint_from]; simpl_sizes; lia].
    apply (rw_cells_transport asegs _ m m2) with (2 := MUw) (3 := WMw) in FT2; [| cbn [disjoint_from]; simpl_sizes; lia].
    apply (rw_cells_transport asegs _ m m2) with (2 := MUw) (3 := WMw) in VAL; [| cbn [disjoint_from]; simpl_sizes; lia].
    apply (rw_cells_transport asegs _ m m2) with (2 := MUw) (3 := WMw) in FT3; [| cbn [disjoint_from]; simpl_sizes; lia].
    join_chunks FT3 FLP J1. join_chunks VAL J1 J2. join_chunks FT2 J2 J3. join_chunks FT1 J3 J4. join_chunks FH J4 FRF.
    destruct (new_frame_facts FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
    assert (SHF' : rw_cells asegs m2 (sh (ff_addr (fs_newff FI st 2))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 2))))))
      by (change (ff_addr (fs_newff FI st 2)) with F; change (sh F) with SF; unfold ff_shsize; rewrite FCLS; exact SHF).
    destruct (release FI stc (fs_newff FI st 2) (fs_live FI st) m3 m2 _ RF LIVE1 MU0 WM0 FLG SHF' FRF ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3].
    clear RF MU0 WM0 SHF'.
    step. zstep. do 13 step. step. step.

    unhide2 ST. unhide2 SCR1. unhide2 SCR2. unhide2 SCR3. unhide2 TOK. unhide2 GAP.
    apply (stk_transport_disjoint asegs _ m m2) with (2 := MUw) (3 := WMw) in ST; [| cbn [disjoint_from]; lia].
    apply (stk_transport_disjoint asegs _ m m2) with (2 := MUw) (3 := WMw) in GAP; [| cbn [disjoint_from]; lia].
    apply (rw_cells_transport asegs _ m m2) with (2 := MUw) (3 := WMw) in SCR1; [| cbn [disjoint_from]; simpl_sizes; lia].
    apply (rw_cells_transport asegs _ m m2) with (2 := MUw) (3 := WMw) in SCR2; [| cbn [disjoint_from]; simpl_sizes; lia].
    apply (rw_cells_transport asegs _ m m2) with (2 := MUw) (3 := WMw) in SCR3; [| cbn [disjoint_from]; simpl_sizes; lia].
    apply (rw_cells_transport asegs _ m m2) with (2 := MUw) (3 := WMw) in TOK; [| cbn [disjoint_from]; simpl_sizes; lia].
    release_frame SCR1 ST (q' + 88)%Z. release_frame SCR2 ST (q' + 96)%Z. release_frame SCR3 ST (q' + 132)%Z. release_frame TOK ST (q' + 152)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST GAP ltac:(lia)) as STm. clear ST GAP.
    release_frame FRhi STm q.
    assert (MUE : munch WE m m2).
    { eapply munch_weaken; [| exact MUw]. unfold sub_fp, hWE. intros xo Ho. cbn [outside] in *. destruct Ho as (_ & H2 & H3 & H4 & _). repeat split; try exact I; lia. }
    unhide2 SC. unhide2 MBC. unhide2 TXT. unhide2 SHP. unhide2 SHA. unhide2 SHZ. unhide2 SHR. unhide2 MU. unhide2 WM. unhide TFS.
    destruct sh_window_ok as (W1 & W2 & W3 & W4).
    assert (FKE : fkeep FI WHS st m m2) by exact (fkeep_of_munch FI WHS WE st stc m m m2 RFm LSUB MUE WE_fk).
    apply evt_done. unfold hpostE. do 14 eexists. exists m2, (fs_after_release FI stc).
    split; [reflexivity|]. split; [exact MUE|]. split; [exact WMw|].
    split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [exact WE_sub0| exact MUE]|].
    split; [exact (wmono_trans asegs _ _ _ WM WMw)|]. split; [exact FK|]. split; [exact MI|]. split; [exact LIVE3|]. split; [exact RF3|].
    split; [exact STm|]. split; [exact AE|].
    split; [eapply rw_cells_transport; [exact SC| exact MUE| exact WMw| apply WE_dj_obj; left; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact MBC| exact MUE| exact WMw| apply WE_dj_obj; left; unfold mbuf_cells; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact TXT| exact MUE| exact WMw| apply WE_dj_obj; right; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia]|].
    split; [exact (shwP_fkeep m m2 SHP FKE)|].
    split; [exact (shw_frame_fs FI _ _ _ _ _ SHA MUE WE_fsw TFS)|].
    split; [eapply (shz_stack_fs FI); [exact SHZ| exact CLO| lia| lia| exact MUE| exact WE_fsw]|].
    eapply (shr_stack_fs FI); [exact SHR| exact CLO| lia| lia| exact MUE| exact WE_fsw].
  Qed.

  #[using="IC STACK_MALLOC_2 HOK RF0 FCO FE0"] Lemma prologueH : forall (cur0 : Z) (bs : list byte) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Q : machine_state -> Prop),
    stk asegs m0 lo q ->
    rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) ->
    rw_cells asegs m0 A [CB (Z.to_nat (cap + 1)) bs] ->
    mem_inv asegs m0 -> asan_env asegs m0 ->
    shw m0 P 504 -> shw m0 A (cap + 1) -> shw m0 SEPTAB_A 20 -> shw m0 FMT_HDR_A 8 ->
    shz m0 (sh lo) (sh q) -> shr m0 (sh lo - sh lo mod 8) (sh q + 8) ->
    0 <= cur0 <= len ->
    (forall q' m (tlz ty : Z) (va vl : word) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31,
       hinv q' (cur0 + tlz) (wz ty) (wz (A + cur0)) (wz tlz) va vl bs m0 m ->
       1 <= tlz -> cur0 + tlz <= len -> 0 <= ty <= 5 -> (ty = TT_IDENTIFIER -> cur0 + tlz < len) ->
       evt asegs Q (headstH q' cur0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 m)) ->
    (forall q' m (r : Z) (ty tb tl va vl : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x28 x29 x30 x31,
       hinvE q' cur0 ty tb tl va vl bs m0 m -> (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE) ->
       evt asegs Q (xstH q' r cur0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x28 x29 x30 x31 m)) ->
    evt asegs Q
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz parse_headers_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros cur0 bs t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q ST SC MBC TXT MI AG SHP SHA SHSEP SHFMT SHZ SHR CUR0 KH KX.
    pose proof HOK as HOK'. hokA HOK'. unfold parse_headers_entryA.
    hide SC. hide MBC. hide TXT. hide SHP. hide SHA. hide SHSEP. hide SHFMT. hide SHZ. hide SHR. hide TFS. hide TBAND.
    pose proof PLB as PLB0. hide PLB0. clear PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    assert (SHB8 : 8 * (sh (FSB FI) - 2147450880) = FSB FI) by (unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia).
    assert (ESF : SF = F / 8 + 2147450880) by reflexivity.
    hide FAL. hide FSB4. hide ESF. hide PAL. hide AAL. hide PAF. hide PAFL.
    pose proof (new_frame_fk FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    pose proof (munch_refl W0 m0) as MU. pose proof (wmono_refl asegs m0) as WM. unfold hW0, hWHS in MU.
    pose proof (munch_refl ((lo, q) :: FSIV [])%Z m0) as MUF.
    pose proof (munch_refl [(lo, q)]%Z m0) as MU0. pose proof (wmono_refl asegs m0) as WM0.
    pose proof (fkeep_refl FI [] st m0) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
    pose proof RF0 as RF.
    carve_frame 256%nat ST.
    step. do 14 (step; fix_lit_store).
    step.
    step.
    rewrite (unsigned_lit (q + -256)) by lia. rewrite land_align32 by lia.
    remember (q + -256 - (q + -256) mod 32)%Z as q' eqn:Eq0.
    assert (Hq : q' = q + -256 \/ q' = q + -256 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
    assert (QAL : q' mod 16 = 0) by (clear - Hq AL16; Z.div_mod_to_equations; lia).
    hide AL16. hide QAL.
    clear Eq0.
    lazymatch goal with FRx : rw_cells asegs ?mm (q + -256) (?c0 :: ?c1 :: ?rest) |- _ =>
      destruct (align_frame_gen mm lo (q + -256) q' [c0; c1] rest 152%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
      clear FRx end.
    clear ST. rename STq into ST. assert (QB : q + -272 <= q' <= q + -256) by lia. hide Hq. change (Z.of_nat 152) with 152 in GAP, FRhi. replace (q + -256 + 152) with (q + -104) in GAP, FRhi by lia.
    step.
    step. step. step. step.
    step. step.
    step.
    step. lit_branch.
    step.
    step.
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    pose proof (fs_call_ok_le FI _ _ _ 1%nat FCO ltac:(lia)) as FCO1.
    call (STACK_MALLOC_2 st lo q' 192 F SF FL 256 216%nat 32%nat).
    all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).
    match goal with A1 : asan_env asegs _ |- _ => try clear AE; rename A1 into AE end.
    match goal with R : RFAKE FI (fs_next FI st 2) _ |- _ => rename R into RF end.
    match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end.
    match goal with K0 : fkeep FI [] st _ _ |- _ => rename K0 into FKc end.
    match goal with P1 : rw_cells asegs _ F _ |- _ => rename P1 into FRF end.
    match goal with P1 : rw_cells asegs _ SF _ |- _ => rename P1 into SHF; shadow_cells_lit SHF end.
    match goal with P1 : rw_cells asegs _ FL _ |- _ => rename P1 into FLG end.
    fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 256); (SF, SF + 32)]%Z.
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS.
    assert (FCLS : ff_class (fs_newff FI st 2) = 2) by (destruct (new_frame_facts FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (X & _); exact X).
    rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 2)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 2)) with FL in LVL. change (sh F) with SF in LVS.
    step. step.
    step. if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
    do 10 step.
    step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
    step. step.
    replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
      by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; unhide ESF; rewrite ESF; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 32)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except SHF. unhide MUs. unhide WMs.
    do 4 sstep.
    zstep.
    do 6 sstep.
    zstep.
    do 11 sstep.
    do 5 sstep.
    zstep.
    unhide_transport MUs WMs. clear MUs WMs.
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    match goal with P1 : stk asegs _ lo q' |- _ => rename P1 into ST end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(lo, q)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
    unhide PLB0.
    assert (PLS : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB0); lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (shw_fkeep0 FI st m0 mm P 504 SHP FK RF0 PLB0) as SHP3;
      pose proof (rw_cells_fkeep FI [] st m0 mm S _ SC FK WM ltac:(solve_in_live) I) as SC3 end.
    splitcb QC 0%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 24; 8; 4; 4; 8; 8]%nat.
    recell QC 1%nat. recell QC 2%nat. recell QC 3%nat. recell QC 4%nat. recell QC 5%nat. recell QC 6%nat. recell QC 7%nat. recell QC 8%nat.
    recell QC 9%nat. recell QC 10%nat. recell QC 11%nat. recell QC 13%nat. recell QC 15%nat. recell QC 16%nat. recell QC 17%nat.
    name_junk QC.
    sstep.
    cstep.
    sstep.
    cstep.
    step.
    zstep. zstep. zstep. step.
    step.

    repeat match type of QC with context [CB ?n ?t] => tryif is_var t then fail else (let j := fresh "jb" in set (j := t) in QC; clearbody j) end.
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    split_chunk QC 15%nat SCR TOK.
    split_chunk FRF 4%nat FH FR1.
    splitcb FR1 0%nat [88; 40; 8; 8; 72]%nat. recell FR1 2%nat. recell FR1 3%nat. name_junk FR1.
    split_chunk FR1 1%nat FT1 FR2. split_chunk FR2 1%nat FT2 FR3. split_chunk FR3 2%nat VAL FR4. split_chunk FR4 1%nat FT3 FLP.
    change (Z.of_nat 132) with 132 in TOK. change (Z.of_nat 32) with 32 in FT1.
    unhide MBC. unhide TXT. unhide SHP. unhide SHA. unhide SHSEP. unhide SHFMT. unhide SHZ. unhide SHR. unhide TFS. unhide Hq. unhide QAL.
    assert (FSWF : Forall (fsw_iv FI) ((lo, q) :: FSIV [])%Z) by (apply fsw_cons_app; [apply app_iv_stack; lia| apply fsw_FSIV; constructor]).
    destruct sh_window_ok as (W1 & W2 & W3 & W4). destruct text_out_fs as (T1 & T2).
    lazymatch type of SCR with rw_cells _ _ _ ?cs => set (scrP := fun (qq : Z) (mm : mem) => rw_cells asegs mm qq cs) end.
    assert (SCRT : forall mm mm', q + -272 <= q' -> scrP q' mm -> munch (WS q') mm mm' -> wmono asegs mm mm' -> scrP q' mm').
    { intros mm mm' QB' SCRm MUS WMS. unfold scrP in *. destruct (lb_in_fsH _ _ PLB0) as [PF1 PF2].
      eapply rw_cells_transport; [exact SCRm| exact MUS| exact WMS|]. unfold hWS. cbn [disjoint_from]. simpl_sizes.
      repeat split; try exact I; lia. }
    assert (INV0 : hinvG scrP q' cur0 jw11 jw12 jw13 jw14 jw15 bs m0 m4).
    { unfold hinvGT.
      split; [exact ST|]. split; [exact SCR|]. split; [exact TOK|]. split; [exact VAL|]. split; [exact SC3|].
      split; [eapply (rw_cells_fkeep FI [] st m0 m4); [exact MBC| exact FK| exact WM| left; apply (Contracts.lb_sub _ _ _ _ _ PLB0); unfold mbuf_cells; simpl_sizes; lia| exact I]|].
      split. { eapply rw_cells_transport; [exact TXT| exact MUF| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
               split; [left; lia|]. split; [clear - T1; lia|]. split; [clear - T2; lia| exact I]. }
      split; [exact MI0|]. split; [exact AE|].
      split; [exact (shw_fkeep0 FI st m0 m4 P 504 SHP FK RF0 PLB0)|].
      split; [exact (shw_frame_fs FI _ _ _ _ _ SHA MUF FSWF TFS)|].
      split; [apply (shw_frame_fs FI _ _ _ _ _ SHSEP MUF FSWF); left; unfold SEPTAB_A; lia|].
      split; [apply (shw_frame_fs FI _ _ _ _ _ SHFMT MUF FSWF); left; lia|].
      split; [eapply (shz_stack_fs FI); [exact SHZ| exact CLO| lia| lia| exact MUF| exact FSWF]|].
      split; [eapply (shr_stack_fs FI); [exact SHR| exact CLO| lia| lia| exact MUF| exact FSWF]|].
      split; [exact CUR0|]. split; [split; [exact QB| exact QAL]|].
      unfold hrestT. split; [exact Hq|]. split; [exact GAP|]. split; [exact FRhi|]. split; [exact FH|].
      split; [eexists; exact FT1|]. split; [eexists; exact FT2|]. split; [eexists; exact FT3|]. split; [exact FLP|].
      split; [unfold hshadow; exact SHF|]. split; [exact FLG|]. split; [exact MU|]. split; [exact WM|].
      split; [eapply (fkeep_weaken FI [] WHS st st m0 m4 FK); [intros xo _; exact I| intros g Hg; exact Hg]|].
      split; [exists (fs_next FI st 2); split; [exact RF| exact LIVE1]|].
      exact (hpm_fkeep [] st m0 m0 m4 (hpm_refl m0) FK WM PLB0 I). }
    clear - INV0 SCRT KH KX QB HOK RF0 CUR0 IC.
    eapply (sgt_callH 248 scrP q' cur0 jw11 jw12 jw13 jw14 jw15 bs m0 m4); [exact INV0| intros m' SCRm MUS WMS; exact (SCRT m4 m' (proj1 QB) SCRm MUS WMS)| |].
    -
      intros m' tlz ty' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV TL1 CL TY5 STRICT CRL.
      replace (ret_pc (Z_to_bv 64 557748)) with (Z_to_bv 64 557748) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof INV as (ST & SCR & _ & _ & _ & _ & _ & MI & _). unfold scrP in SCR.
      pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide PAL. hide AAL.
      pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
      pose proof (munch_refl [(lo, q' + 132)]%Z m') as MUX. pose proof (wmono_refl asegs m') as WMX.
      unfold PARSE_OK.
      walk_to 0x88300%Z.
      eapply (KH q' _ tlz ty' jw14 jw15); [| exact TL1| exact CL| exact TY5| intros E; apply STRICT; left; exact E].
      eapply (hinv_stepX 248 scrP hscr q' _ _ _ _ _ _ _ m0 m' _ INV MUX WMX ST); [| exact MI].
      do 4 eexists. exact SCR.
    -
      intros m' r tb' tl' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV HRr.
      replace (ret_pc (Z_to_bv 64 557748)) with (Z_to_bv 64 557748) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (INVE : hinvE q' cur0 jw11 tb' tl' jw14 jw15 bs m0 m').
      { destruct INV as (ST & SCR & REST). split; [exact ST|]. split; [| exact REST]. unfold scrP in SCR.
        split_chunk SCR 11%nat S1 S2. split_chunk S2 1%nat S3 S4.
        lazymatch type of S1 with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge asegs m' q' [] cs []) as M1 end.
        lazymatch type of S4 with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge asegs m' (q' + 96) [] cs []) as M4 end.
        rewrite !app_nil_r in M1, M4. cbn [app cells_size csize Nat.add] in M1, M4. specialize (M1 S1). specialize (M4 S4).
        split; [eexists; exact M1|]. split; [exact S3| eexists; exact M4]. }
      clear INV SCRT. unfold PARSE_INCOMPLETE, PARSE_FAILURE in *.
      destruct HRr as [-> | ->].
      + step. step. lit_branch. eapply (KX q' m' 1); [exact INVE| left; reflexivity].
      + step. step. lit_branch. eapply (KX q' m' 3); [exact INVE| right; reflexivity].
  Qed.

  #[using="m0 HOK RF0"] Lemma hvf_ok : forall q' cur (bs : list byte) stc,
    hlive stc -> q + -272 <= q' <= q + -256 -> q' mod 16 = 0 -> Z.of_nat (length bs) = cap + 1 -> 0 <= cur <= len ->
    vf_okA FI q' lo S MB A len cap cur bs stc [(F + 160, F + 160 + 16)]%Z.
  Proof.
    intros q' cur bs stc (LVF & LVS & LVL & LVP & LSUB) QB QAL BL CR.
    hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    unfold vf_okA. rewrite BL.
    split; [exact CLO|]. split; [lia|]. split; [exact QAL|]. split; [change (2^47) with 140737488355328 in *; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [clear - PAL; Z.div_mod_to_equations; lia|]. split; [clear - PAL; Z.div_mod_to_equations; lia|].
    split; [apply (Contracts.lb_sub _ _ _ _ _ LVP); lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [change (2^63) with 9223372036854775808; change (2^47) with 140737488355328 in *; lia|].
    split; [exact CR|].
    split; [clear - TFS PF1 PF2; lia|]. split; [exact TFS|]. split; [clear - TBAND; lia|].
    split; [constructor; [cbn [fst snd]; split; [lia| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); lia]| constructor]|].
    split; [cbn [disjoint_from]; split; [clear - TFS FLO FHI B1; lia| exact I]|].
    cbn [disjoint_from]. split; [clear - PAF; lia| exact I].
  Qed.

  #[using="len m0 HOK RF0"] Lemma hval_shw : forall t q' mb m, hrestT t q' mb m -> shw m (F + 160) 16.
  Proof.
    intros t q' mb m (_ & _ & _ & _ & _ & _ & _ & _ & SHF & _).
    hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL). pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    assert (F8 : F mod 8 = 0) by (clear - FAL; Z.div_mod_to_equations; lia).
    unfold hshadow in SHF.
    change [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
            C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t);
            C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t); C1 (Z_to_bv 8 t);
            C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      with (shadow_cells [241; 241; 241; 241; t; t; t; t; t; t; t; t; t; t; t; 242; 242; 242; 242; 242; 0; 0; 243; 243; 0; 0; 0; 0; 0; 0; 0; 0]) in SHF.
    split; [| split].
    - eapply (accessible_of_chunk m F _ (F + 160) 16 SHF F8); [lia| cbn [length]; lia|].
      intros i Hi H1 H2. cbn [length] in Hi.
      assert (Ei : i = 20%nat \/ i = 21%nat) by lia. destruct Ei as [-> | ->]; reflexivity.
    - eapply (sh_readable_of_chunk m F _ (F + 160) 16 SHF); cbn [length]; unfold sh, SHADOW_OFF; clear - F8; Z.div_mod_to_equations; lia.
    - unfold win_ok. split; [lia|]. clear - FLO FHI B1 B2 B5 ACR. change (2^47) with 140737488355328. lia.
  Qed.

  #[using="Type"] Lemma hrest_mu : forall t q' mb m, hrestT t q' mb m -> munch W0 mb m /\ wmono asegs mb m /\ fkeep FI WHS st mb m.
  Proof. intros t q' mb m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & FK & _). auto. Qed.

  Definition endstH (q' sv ty : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz ty) x11 x12 x13 x14 x15 x16 x17
            (wz sv) (wz TAB_HDR_A) (wz 2147450880) x21 x22 (wz (P + 488)) (wz (F + 160)) (wz L) (wz S) (wz SF) x28 x29 x30 x31)
       F_ (wz 0x88660) fc None m (seg_rom asegs).
  Definition namestH (q' sv : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            (wz sv) (wz TAB_HDR_A) (wz 2147450880) x21 x22 (wz (P + 488)) (wz (F + 160)) (wz L) (wz S) (wz SF) x28 x29 x30 x31)
       F_ (wz 0x88320) fc None m (seg_rom asegs).

  #[using="IC STACK_MALLOC_0 STACK_MALLOC_1 m0 HOK RF0 FCO"] Lemma headH : forall (q' sv cur ty : Z) (tb tl va vl : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur (wz ty) tb tl va vl bs mb m -> 0 <= ty <= 5 -> 0 <= sv <= len ->
    FSENV FI m ->
    (ty <> 0 -> forall y1 y11, evt asegs Q (endstH q' sv ty y1 x5 x6 x7 y11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 m)) ->
    (forall m' (r : Z) va' vl' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y24 y25 y26 y28 y29 y30 y31,
       hinvE q' sv (wz ty) tb tl va' vl' bs mb m' -> 0 <= r <= 5 -> r <> 4 ->
       evt asegs Q (epistH q' r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y24 y25 y26 y28 y29 y30 y31 m')) ->
    (forall m' (cur' o l : Z) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinv q' cur' (wz ty) tb tl (wz (A + o)) (wz l) bs mb m' -> FSENV FI m' ->
       cur + 1 <= o -> 0 <= l -> o + l <= len -> cur + 1 <= cur' -> o + l + 1 <= cur' -> cur' <= len ->
       evt asegs Q (namestH q' sv y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x21 x22 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstH q' sv x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 m).
  Proof.
    intros q' sv cur ty tb tl va vl bs mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 Q INV TY SV FE KEND KX KN.
    pose proof INV as (ST & (j0 & w32 & j96 & j128 & SCR) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & (QB & QAL) & HR).
    unfold headstH.
    step. rewrite (sx32_lit ty) by lia.
    step. if_cases K0; zify_cond K0.
    {   apply KEND. lia. }
    assert (TY0 : ty = 0) by lia. clear K0.
    step. step. step. step.
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (hrest_rf 248 q' mb m HR) as (stc & RF & LIVE1). pose proof (hlive_of stc LIVE1) as HL.
    destruct (text_bytesH m bs TXT) as [BUF BL].
    pose proof (hval_shw 248 q' mb m HR) as SHV.
    destruct sh_window_ok as (W1 & W2 & W3 & W4).
    eapply evt_cut.
    { eapply (match_hdrA IC FI STACK_MALLOC_0 STACK_MALLOC_1 S MB A len cap cur (F + 160) lo q' bs stc va vl);
        [ exact (hvf_ok q' cur bs stc HL QB QAL BL CR) | lia | change (2^47) with 140737488355328 in *; lia | exact RF | exact (fs_call_ok_push FI st stc tp 2%nat _ FCO LIVE1) | exact FE
        | exact ST | exact MI | exact AE | exact SC | exact MBC | exact BUF
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | intros _; apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | exact SHSEP | exact SHFMT
        | apply (shz_sub _ _ _ _ _ SHZ); [lia| apply sh_mono; lia]
        | intros a Ha; apply SHR; pose proof (sh_mono q' q ltac:(lia)); lia
        | exact VAL | exact SHV
        | destruct hframe_facts as (_ & _ & FAL & _); clear - FAL; Z.div_mod_to_equations; lia ]. }
    intros ms' POST. unfold match_postXA in POST.
    destruct POST as (r & cur' & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MUF & WMF & MI' & FKc & LIVE' & RF' & ST' & AE' & SC' & RR & CR' & ROK & RNOK & XF).
    destruct XF as (pa & pb & VAL' & XOK).
    assert (FE' : FSENV FI m').
    { destruct hframe_facts as (HF1 & HF2 & _). destruct (lb_in_fsH P 504 PLB) as [PF1 PF2].
      refine (fsenv_FSIV FI _ lo q' m m' FE MUF CLO _).
      constructor; [apply fcls_in_fs; lia|]. constructor; [apply fcls_in_fs; lia| constructor]. }
    replace (ret_pc (Z_to_bv 64 557848)) with (Z_to_bv 64 557848) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (INV' : hinv q' cur' (wz ty) tb tl pa pb bs mb m').
    { eapply (hinv_stepF q' cur (wz ty) tb tl va vl bs cur' pa pb mb m m' stc st' INV RF LIVE1); [| exact WMF| | exact LIVE'| exact RF'| exact ST'| exact VAL'| exact SC'| exact MI'| exact AE'| exact CR'].
      - unfold hWF, hWC. replace (F + 176) with (F + 160 + 16) by lia. exact MUF.
      - unfold hWC. replace (F + 176) with (F + 160 + 16) by lia. exact FKc. }
    clear INV MUF WMF FKc ST SC MBC TXT VAL SHV BUF AE MI SHP SHA SHSEP SHFMT SHZ SHR HR RF TOK SCR.
    step. step.
    if_cases K0; zify_cond K0.
    -
      assert (R4 : r <> 4) by lia. clear K0.
      pose proof INV' as (ST & (j0' & w32' & j96' & j128' & SCR) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & _ & _ & _ & _ & _ & _ & _ & _).
      hide TFS. hide TBAND. hide AL16. hide PAL. hide AAL. hide QAL. clear XOK ROK RNOK HL.
      destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
      destruct hframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _).
      pose proof (munch_refl (WL q') m') as MUL. pose proof (wmono_refl asegs m') as WML. unfold hWL, hWHP in MUL.
      pose proof (munch_refl [(S + 8, S + 16)]%Z m') as MUc.
      unfold hSHC in *. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC. hide TXT.
      walk_to 0x887fc%Z.
      unhide TXT. unhide TFS.
      eapply (KX m1 r pa pb); [| exact RR| exact R4].
      eapply (hinv_stepW 248 hscr hscrE q' cur' (wz ty) tb tl pa pb bs sv (wz ty) tb tl pa pb bs mb m' m1 INV' MUL WML ST); [| exact TOK| exact VAL| exact SC| exact MBC| | exact MI| exact SV].
      + apply hscr_E. do 4 eexists. exact SCR.
      + eapply rw_cells_transport; [exact TXT| exact MUc| exact WML|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
        split; [clear - TFS PF1 PF2; lia| exact I].
    -
      assert (R4 : r = 4) by lia. clear K0. destruct (XOK R4) as (o & l & -> & -> & O1 & L0 & OL & C1 & C2).
      eapply (KN m' cur' o l); [exact INV'| exact FE'| exact O1| exact L0| exact OL| exact C1| exact C2| lia].
  Qed.

  Variable ws : list word.
  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64.

  Definition hstat (m : mem) : Prop := u64arr asegs m TAB_HDR_A ws /\ shw m TAB_HDR_A 528 /\ table_strings_A m ws 33.

  #[using="ws WSL"] Lemma above_image_dj : forall (W : list ivl) a n, Forall (fun iv : ivl => 0x609000 <= fst iv) W -> a + n <= 0x609000 -> disjoint_from W a n.
  Proof.
    induction W as [|[x y] W IH]; intros a n HW Ha; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [left; lia| exact (IH a n H2 Ha)].
  Qed.

  #[using="WSL"] Lemma hstat_step : forall (W : list ivl) m m', hstat m -> munch W m m' -> wmono asegs m m' ->
    Forall (fsw_iv FI) W -> Forall (fun iv : ivl => 0x609000 <= fst iv) W -> hstat m'.
  Proof.
    intros W m m' (TB & SHT & TS) MU WM HF HA. pose proof (fsb_ok FI) as (B1 & _).
    split; [| split].
    - eapply u64arr_transport; [exact TB| exact MU| exact WM|]. apply above_image_dj; [exact HA| rewrite WSL; lia].
    - apply (shw_frame_fs FI W m m' _ _ SHT MU HF). left. lia.
    - intros i Hi. destruct (TS i Hi) as (Sx & str & slack & E1 & E2 & E3 & E4 & E5 & E6 & E7).
      exists Sx, str, slack. repeat (split; [assumption|]).
      apply (shw_frame_fs FI W m m' _ _ E7 MU HF). left. lia.
  Qed.

  #[using="q len m0 HOK RF0 ws WSL"] Lemma WL_above : forall q', Forall (fun iv : ivl => 0x609000 <= fst iv) (WL q').
  Proof.
    intros q'. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & _). pose proof (fsb_ok FI) as (B1 & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    unfold hWL, hWHP. repeat (constructor; [cbn [fst]; lia|]). constructor.
  Qed.
  #[using="q A len cap m0 HOK RF0 ws WSL"] Lemma WF_above : forall q', Forall (fun iv : ivl => 0x609000 <= fst iv) (WF q').
  Proof.
    intros q'. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & _). pose proof (fsb_ok FI) as (B1 & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    pose proof fs_shadow_band as (S1 & _).
    unfold hWF, hWC. repeat (constructor; [cbn [fst]; lia|]). constructor.
  Qed.
  #[using="q len m0 HOK RF0"] Lemma WL_fsw : forall q', Forall (fsw_iv FI) (WL q').
  Proof. intros q'. eapply Forall_impl; [| exact (WL_app q')]. intros iv H. left. exact H. Qed.

  #[using="ws WSL"] Lemma bytes_skipnH : forall m a (bs : list byte) k, bytes_at asegs m a bs -> 0 <= k <= Z.of_nat (length bs) ->
    bytes_at asegs m (a + k) (skipn (Z.to_nat k) bs).
  Proof.
    intros m a bs k H Hk. rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
    rewrite length_firstn, Nat.min_l, Z2Nat.id in H by lia. exact H.
  Qed.

  Definition knownstH (q' idx tcur tlz : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz idx) x11 x12 x13 x14 x15 x16 x17
            (wz tlz) (wz TAB_HDR_A) (wz 2147450880) (wz (A + tcur)) x22 (wz (P + 488)) (wz (F + 160)) (wz L) (wz S) (wz SF) x28 x29 x30 x31)
       F_ (wz 0x88348) fc None m (seg_rom asegs).
  Definition unkstH (q' tcur tlz : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            (wz tlz) (wz TAB_HDR_A) (wz 2147450880) (wz (A + tcur)) x22 (wz (P + 488)) (wz (F + 160)) (wz L) (wz S) (wz SF) x28 x29 x30 x31)
       F_ (wz 0x883ec) fc None m (seg_rom asegs).

  #[using="IC STACK_MALLOC_0 m0 HOK RF0 FCO WSL"] Lemma nameH : forall (q' sv cur tcur tlz : Z) (ty va vl : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m -> hstat m -> FSENV FI m -> 0 <= tcur -> 1 <= tlz -> tcur + tlz <= len ->
    (forall m' (idx : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m' -> hstat m' -> 0 <= idx < 33 ->
       evt asegs Q (knownstH q' idx tcur tlz y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 x22 y28 y29 y30 y31 m')) ->
    (forall m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m' -> hstat m' ->
       evt asegs Q (unkstH q' tcur tlz y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x22 y28 y29 y30 y31 m')) ->
    evt asegs Q (namestH q' sv x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 m).
  Proof.
    intros q' sv cur tcur tlz ty va vl bs mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 Q INV HS FE TC0 TL1 TCL KK KU.
    pose proof INV as (ST & (j0 & w32 & j96 & j128 & SCR) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & (QB & QAL) & HR).
    pose proof HS as (TB & SHT & TS).
    unfold namestH.
    step. step. step. step. step. step. step. step.
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (hrest_rf 248 q' mb m HR) as (stc & RF & LIVE1).
    destruct (text_bytesH m bs TXT) as [BUF BL].
    pose proof (bytes_skipnH m A bs tcur BUF ltac:(lia)) as TOKB.
    assert (TKL : Z.of_nat (length (skipn (Z.to_nat tcur) bs)) = cap + 1 - tcur) by (rewrite length_skipn; lia).
    eapply evt_cut.
    { eapply (map_str_to_int_spec_A IC FI STACK_MALLOC_0 (A + tcur) tlz TAB_HDR_A 33 0 lo (skipn (Z.to_nat tcur) bs) ws stc);
        [ exact TOKB | lia | lia | lia | lia
        | apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | clear - TFS TKL TC0; lia | clear - TBAND TKL TC0; lia
        | exact TB | rewrite WSL; reflexivity | lia | lia | lia | reflexivity | exact SHT | exact TS
        | exact ST | exact CLO | unfold A0_RT_STACK; lia | exact QAL | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; lia
        | exact MI | exact AE | exact RF | exact (fs_call_ok_le FI _ _ _ 1%nat (fs_call_ok_push FI st stc tp 2%nat _ FCO LIVE1) ltac:(lia)) | exact FE | lia
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]. }
    intros ms' POST. unfold map_str_to_int_post_A in POST.
    destruct POST as (r & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & st' & -> & MU0 & WM' & MI' & FK0 & LIVE' & RF' & ST' & AE' & RES).
    replace (ret_pc (Z_to_bv 64 557888)) with (Z_to_bv 64 557888) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    assert (MUF : munch (WF q') m m').
    { eapply munch_weaken; [| exact MU0]. unfold sub_fp, hWF, hWC. intros xo Ho. cbn [outside] in *. destruct Ho as (H1 & H2 & H3 & _). repeat split; try exact I; assumption. }
    assert (FKc : fkeep FI WC stc m m') by (eapply (fkeep_weaken FI [] WC stc stc m m' FK0); [intros xo _; exact I| intros g Hg; exact Hg]).
    assert (INV' : hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m').
    { eapply (hinv_stepF q' cur ty (wz (A + tcur)) (wz tlz) va vl bs cur va vl mb m m' stc st' INV RF LIVE1 MUF WM' FKc LIVE' RF' ST'); [| | exact MI'| exact AE'| exact CR].
      - eapply (rw_cells_fkeep FI [] stc m m'); [exact VAL| exact FK0| exact WM'| left; apply (Contracts.lb_sub _ _ _ _ _ LVF); simpl_sizes; lia| exact I].
      - eapply (rw_cells_fkeep FI [] stc m m'); [exact SC| exact FK0| exact WM'| left; apply (Contracts.lb_sub _ _ _ _ _ LVP); simpl_sizes; lia| exact I]. }
    assert (HS' : hstat m') by (eapply (hstat_step (WF q') m m' HS MUF WM' (WF_fsw q') (WF_above q'))).
    clear - INV' HS' RES KK KU HOK RF0 WSL HID.
    destruct RES as [-> | RR].
    - step. step. lit_branch. eapply KU; [exact INV'| exact HS'].
    - step. step. if_cases K0; zify_cond K0. { exfalso. lia. }
      eapply (KK m' r); [exact INV'| exact HS'| exact RR].
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma hinv_stepSh : forall t t' (scr : Z -> mem -> Prop) q' cur ty tb tl va vl bs mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch [(SF, SF + 32)]%Z m m' -> wmono asegs m m' ->
    rw_cells asegs m' SF (hshadow t') -> mem_inv asegs m' ->
    (scr q' m -> scr q' m') ->
    hinvGT t' scr q' cur ty tb tl va vl bs mb m'.
  Proof.
    intros t t' scr q' cur ty tb tl va vl bs mb m m'
      (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & (QB & QAL) & HR) MUs WMs SHF' MI' SCRT.
    destruct HR as (Hq & GAP & FRhi & FH & (j1 & FT1) & (j2 & FT2) & (j3 & FT3) & FLP & SHF & FLG & MU & WM & FK & (stc & RF & LIVE1) & HPM).
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    pose proof fs_shadow_band as (SB1 & SB2 & SB3). pose proof (fs_shadow_apart FI) as FSAP. pose proof text_out_fs as (T1 & T2).
    pose proof (fsb_ok FI) as (B1 & B2 & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    destruct sh_window_ok as (W1 & W2 & W3 & W4).
    pose proof (new_frame_fk FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    assert (DJ : forall a n, a + n <= SF \/ SF + 32 <= a -> disjoint_from [(SF, SF + 32)]%Z a n) by (intros a n Ha; cbn [disjoint_from]; split; [lia| exact I]).

    assert (FAP : F + 256 <= SF \/ SF + 32 <= F) by (clear - FSAP FLO FHI SHF1 SHF2; lia).
    assert (FLAP : FL + 1 <= SF \/ SF + 32 <= FL) by (clear - FSAP FLLO FLHI SHF1 SHF2; lia).
    assert (PAP : P + 504 <= SF \/ SF + 32 <= P) by (clear - FSAP PF1 PF2 SHF1 SHF2; lia).
    assert (AAP : A + (cap + 1) <= SF \/ SF + 32 <= A) by (clear - T2 SHF1 SHF2; lia).
    assert (STKAP : SF + 32 <= lo) by (clear - SB3 SHF2; lia).
    assert (QLO : lo <= q') by (clear - QB LO; lia).
    clear FSAP T1 T2 PAF PAFL. hide TFS. hide TBAND.
    assert (FSW : Forall (fsw_iv FI) [(SF, SF + 32)]%Z) by (constructor; [right; cbn [fst snd]; lia| constructor]).
    assert (FKs : fkeep FI WHS st m m').
    { apply (fkeep_of_munch FI WHS [(SF, SF + 32)]%Z st stc m m m' RF LSUB MUs). constructor; [apply NFK; cbn [FB_of SB_of]; lia| constructor]. }
    unfold hinvGT.
    split; [eapply stk_transport_disjoint; [exact ST| exact MUs| exact WMs| apply DJ; clear - STKAP; lia]|].
    split; [exact (SCRT SCR)|].
    split; [eapply rw_cells_transport; [exact TOK| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - STKAP QLO; lia]|].
    split; [eapply rw_cells_transport; [exact VAL| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - FAP; lia]|].
    split; [eapply rw_cells_transport; [exact SC| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - PAP; lia]|].
    split; [eapply rw_cells_transport; [exact MBC| exact MUs| exact WMs| apply DJ; unfold mbuf_cells; simpl_sizes; clear - PAP; lia]|].
    split; [eapply rw_cells_transport; [exact TXT| exact MUs| exact WMs| apply DJ; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - AAP; lia]|].
    split; [exact MI'|].
    split; [eapply asan_env_frame; [exact AE| exact MUs| exact WMs|]; unfold env_safe; constructor; [left; cbn [fst snd]; lia| constructor]|].
    split; [exact (shwP_fkeep m m' SHP FKs)|].
    split; [unhide TFS; exact (shw_frame_fs FI _ _ _ _ _ SHA MUs FSW TFS)|].
    split; [apply (shw_frame_fs FI _ _ _ _ _ SHSEP MUs FSW); left; unfold SEPTAB_A; lia|].
    split; [apply (shw_frame_fs FI _ _ _ _ _ SHFMT MUs FSW); left; lia|].
    split; [eapply (shz_stack_fs FI); [exact SHZ| exact CLO| lia| lia| exact MUs| exact FSW]|].
    split; [eapply (shr_stack_fs FI); [exact SHR| exact CLO| lia| lia| exact MUs| exact FSW]|].
    split; [exact CR|]. split; [split; [exact QB| exact QAL]|].
    unfold hrestT.
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUs| exact WMs| apply DJ; clear - STKAP QLO; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - STKAP QLO QB; lia]|].
    split; [eapply rw_cells_transport; [exact FH| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - FAP; lia]|].
    split; [exists j1; eapply rw_cells_transport; [exact FT1| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - FAP; lia]|].
    split; [exists j2; eapply rw_cells_transport; [exact FT2| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - FAP; lia]|].
    split; [exists j3; eapply rw_cells_transport; [exact FT3| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - FAP; lia]|].
    split; [eapply rw_cells_transport; [exact FLP| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - FAP; lia]|].
    split; [exact SHF'|].
    split; [eapply rw_cells_transport; [exact FLG| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - FLAP; lia]|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUs]. unfold sub_fp, hW0. intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [lia| exact I]. }
    split; [eapply wmono_trans; [exact WM| exact WMs]|].
    split; [eapply fkeep_trans; [exact FK| exact FKs]|].
    split. { exists stc. split; [| exact LIVE1].
             eapply (rfake_frame FI stc m m' _ RF MUs WMs). constructor; [right; right; cbn [fst snd]; apply (ls_sub _ _ _ _ _ LVS); lia| constructor]. }
    apply (hpm_step _ mb m m' HPM MUs WMs). apply DJ. clear - PAP. lia.
  Qed.

  #[using="len m0 HOK RF0 ws WSL"] Lemma WM_ok : forall q', q + -272 <= q' <= q + -256 -> hWok [(P + 4, P + 8)]%Z q'.
  Proof.
    intros q' QB. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    assert (PSH : P + 504 <= SF \/ SF + 32 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 32 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    split; [constructor; [apply sub_app_iv_fsH; lia| constructor]|].
    split; [unfold env_safe; constructor; [left; cbn [fst snd]; lia| constructor]|].
    split. { unfold sub_fp, hW0, hWHS. intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & _ & _ & H5 & _). split; [exact H5| exact I]. }
    split; [unfold hWHS; constructor; [unfold fk_ok; left; cbn [inside fst snd]; lia| constructor]|].
    split. { intros stc m m' (_ & _ & _ & LVP & _) RF MU WM. eapply (rfake_frame FI stc m m' _ RF MU WM).
             constructor; [right; left; cbn [fst snd]; apply (Contracts.lb_sub _ _ _ _ _ LVP); lia| constructor]. }
    split; [intros a n Ha Hn; cbn [disjoint_from]; split; [clear - Ha QB LO PHI CLO; lia| exact I]|].
    intros a n HP. cbn [disjoint_from]. split; [clear - HP PAF PAFL PSH; lia| exact I].
  Qed.
  #[using="m0 HOK RF0 ws WSL"] Lemma hinv_stepM : forall t (scr : Z -> mem -> Prop) q' cur ty tb tl va vl bs mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch [(P + 4, P + 8)]%Z m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    rw_cells asegs m' (P + 4) [C4 (wz 11)] ->
    (scr q' m -> scr q' m') ->
    hinvGT t scr q' cur ty tb tl va vl bs mb m'.
  Proof.
    intros t scr q' cur ty tb tl va vl bs mb m m' INV MUc WMc MI' METH' SCRT.
    pose proof INV as (ST & SCR & TOK & VAL & SC & MBC & TXT & _ & _ & _ & _ & _ & _ & _ & _ & CR & (QB & _) & HR).
    pose proof HOK as HOK'. hokA HOK'. pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct hframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    assert (DJ : forall a n, a + n <= P + 4 \/ P + 8 <= a -> disjoint_from [(P + 4, P + 8)]%Z a n) by (intros a n Ha; cbn [disjoint_from]; split; [lia| exact I]).
    assert (QLO : P + 8 <= q') by (clear - QB LO PHI CLO; lia).
    assert (AAP : A + (cap + 1) <= P + 4 \/ P + 8 <= A) by (clear - TFS PF1 PF2; lia).
    assert (FAP : F + 256 <= P + 4 \/ P + 8 <= F) by (clear - PAF; lia).
    clear TFS TBAND PAF.
    eapply (hinv_stepG [(P + 4, P + 8)]%Z t scr scr q' cur ty tb tl va vl bs cur ty tb tl va vl bs mb m m' (WM_ok q' QB) INV MUc WMc);
      [exact (hpm_set mb m m' (hrest_hpm t q' mb m HR) METH')| | exact (SCRT SCR)| | | | | | exact MI'| exact CR].
    - eapply stk_transport_disjoint; [exact ST| exact MUc| exact WMc| apply DJ; clear - PHI CLO; lia].
    - eapply rw_cells_transport; [exact TOK| exact MUc| exact WMc| apply DJ; simpl_sizes; clear - QLO; lia].
    - eapply rw_cells_transport; [exact VAL| exact MUc| exact WMc| apply DJ; simpl_sizes; clear - FAP; lia].
    - eapply rw_cells_transport; [exact SC| exact MUc| exact WMc| apply DJ; simpl_sizes; clear; lia].
    - eapply rw_cells_transport; [exact MBC| exact MUc| exact WMc| apply DJ; unfold mbuf_cells; simpl_sizes; clear; lia].
    - eapply rw_cells_transport; [exact TXT| exact MUc| exact WMc| apply DJ; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - AAP; lia].
  Qed.

  #[using="HC FI q lo A len cap st m0 HOK RF0 WSL"] Lemma hstat_stepM : forall m m', hstat m -> munch [(P + 4, P + 8)]%Z m m' -> wmono asegs m m' -> hstat m'.
  Proof.
    intros m m' HS MUc WMc. hokA HOK. destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & _).
    eapply (hstat_step _ m m' HS MUc WMc); [constructor; [left; apply sub_app_iv_fsH; lia| constructor]| constructor; [cbn [fst]; lia| constructor]].
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma unpoisonH : forall (scr : Z -> mem -> Prop) (q' cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem)
      x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinvGT 248 scr q' cur ty tb tl va vl bs mb m ->
    (forall m m', scr q' m -> munch [(SF, SF + 32)]%Z m m' -> wmono asegs m m' -> scr q' m') ->
    (forall m', hinvGT 0 scr q' cur ty tb tl va vl bs mb m' ->
       evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz SF) x28 x29 x30 x31)
                       F_ (wz 0x883b8) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz SF) x28 x29 x30 x31)
                    F_ (wz 0x8838c) fc None m (seg_rom asegs)).
  Proof.
    intros scr q' cur ty tb tl va vl bs mb m x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 Q INV SCRT KK.
    pose proof INV as (_ & _ & _ & _ & _ & _ & _ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR).
    destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & SHF & _).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _). pose proof fs_shadow_band as (SB1 & SB2 & SB3).
    pose proof (munch_refl [(SF, SF + 32)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
    unfold hshadow in SHF.
    do 11 sstep.
    apply KK. eapply (hinv_stepSh 248 0 scr q' cur ty tb tl va vl bs mb m _ INV MUs WMs); [unfold hshadow; exact SHF| exact MI|].
    intros SCRm. exact (SCRT m _ SCRm MUs WMs).
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma repoisonH : forall (scr : Z -> mem -> Prop) (q' cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem)
      x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinvGT 0 scr q' cur ty tb tl va vl bs mb m ->
    (forall m m', scr q' m -> munch [(SF, SF + 32)]%Z m m' -> wmono asegs m m' -> scr q' m') ->
    (forall m', hinvGT 248 scr q' cur ty tb tl va vl bs mb m' ->
       evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz (-8)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz SF) x28 x29 x30 x31)
                       F_ (wz 0x88598) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz SF) x28 x29 x30 x31)
                    F_ (wz 0x88568) fc None m (seg_rom asegs)).
  Proof.
    intros scr q' cur ty tb tl va vl bs mb m x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 Q INV SCRT KK.
    pose proof INV as (_ & _ & _ & _ & _ & _ & _ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR).
    destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & SHF & _).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _). pose proof fs_shadow_band as (SB1 & SB2 & SB3).
    pose proof (munch_refl [(SF, SF + 32)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
    unfold hshadow in SHF.
    step. do 11 sstep.
    apply KK. eapply (hinv_stepSh 0 248 scr q' cur ty tb tl va vl bs mb m _ INV MUs WMs); [unfold hshadow; exact SHF| exact MI|].
    intros SCRm. exact (SCRT m _ SCRm MUs WMs).
  Qed.

  #[using="ws WSL"] Lemma u64arr_read4A : forall m X (xs : list word) (i : Z) w a,
    u64arr asegs m X xs -> nth_error xs (Z.to_nat i) = Some w -> 0 <= i -> a = wa (X + 8 * i) ->
    ov_read_bytes asegs m a 4 = Some (le4 w).
  Proof.
    intros m X xs i w a [Hb _] Hn Hi ->.
    destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
    replace (8 * i) with (Z.of_nat (8 * Z.to_nat i)) by lia.
    rewrite (bytes_at_ov_read asegs m X (u64s xs) (8 * Z.to_nat i) 4 Hb).
    2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
    rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
    rewrite firstn_app. replace (firstn 4 (le8 w)) with (le4 w) by reflexivity.
    rewrite length_le8. replace (4 - 8)%nat with 0%nat by reflexivity. rewrite firstn_O, app_nil_r. reflexivity.
  Qed.

  Definition tempstH (q' id tcur tlz : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            (wz tlz) (wz TAB_HDR_A) (wz 2147450880) (wz (A + tcur)) (wz id) (wz (P + 488)) (wz (F + 160)) (wz L) (wz S) (wz SF) x28 x29 x30 x31)
       F_ (wz 0x8838c) fc None m (seg_rom asegs).

  #[using="m0 HOK RF0 WSL HID"] Lemma knownA : forall (q' idx tcur tlz cur meth : Z) (ty va vl : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m -> hstat m -> 0 <= idx < 33 ->
    rw_cells asegs m (P + 4) [C4 (wz meth)] ->
    (forall m' (id meth' : Z) y10 y11 y12 y13,
       hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m' -> hstat m' -> rw_cells asegs m' (P + 4) [C4 (wz meth')] ->
       0 <= id < 64 -> (meth' = meth \/ meth' = 11) ->
       evt asegs Q (tempstH q' id tcur tlz x1 x5 x6 x7 y10 y11 y12 y13 x14 x15 x16 x17 x28 x29 x30 x31 m')) ->
    evt asegs Q (knownstH q' idx tcur tlz x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m).
  Proof.
    intros q' idx tcur tlz cur meth ty va vl bs mb m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 Q INV HS IDX METH KK.
    pose proof INV as (ST & (j0 & w32 & j96 & j128 & SCR) & _ & _ & _ & _ & _ & MI & _ & SHP & _ & _ & _ & _ & _ & _ & (QB & _) & _).
    pose proof HS as (TB & SHT & _).
    destruct (HID idx IDX) as (id & HN & IDR).
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide AAL.
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof (munch_refl [(P + 4, P + 8)]%Z m) as MUc. pose proof (wmono_refl asegs m) as WMc.
    unfold knownstH.
    zstep. zstep. zstep.
    replace (Z.shiftl idx 4) with (16 * idx) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    cstep. cstep. cstep.
    cstep. cstep.
    pose proof (u64arr_read4A m TAB_HDR_A ws (2 * idx + 1) (wz id) (Z_to_bv 64 (714432 + 16 * idx + 8)) TB HN ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. rewrite (sx32_lit id) by lia. clear RD.
    zstep. step. if_cases K0; zify_cond K0.
    -
      eapply (KK m id meth); [exact INV| exact HS| exact METH| exact IDR| left; reflexivity].
    -
      assert (ID19 : id = 19) by lia. subst id.
      walk_to 0x8838c%Z.
      eapply (KK m1 19 11); [| exact (hstat_stepM m m1 HS MUc WMc)| exact METH| lia| right; reflexivity].
      eapply (hinv_stepM 248 hscr q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m m1 INV MUc WMc MI METH).
      intros _. do 4 eexists. exact SCR.
  Qed.

  Definition own_iv (iv : ivl) : Prop := fst iv <= snd iv /\ ((F + 32 <= fst iv /\ snd iv <= F + 120) \/ (SF <= fst iv /\ snd iv <= SF + 32)).

  #[using="Type"] Lemma own_dj : forall (W : list ivl) a n, Forall own_iv W -> (a + n <= F + 32 \/ F + 120 <= a) -> (a + n <= SF \/ SF + 32 <= a) -> disjoint_from W a n.
  Proof.
    induction W as [|[x y] W IH]; intros a n HW H1 H2; cbn [disjoint_from]; [exact I|].
    inversion HW as [|? ? HO HW']; subst. unfold own_iv in HO. cbn [fst snd] in HO. split; [| exact (IH a n HW' H1 H2)].
    clear - HO H1 H2. lia.
  Qed.
  #[using="len m0 HOK RF0"] Lemma own_sub0 : forall (W : list ivl), Forall own_iv W -> sub_fp W W0.
  Proof.
    intros W HW. destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _).
    unfold sub_fp, hW0. intros xo Ho. cbn [outside] in Ho. destruct Ho as (_ & H2 & H3 & _).
    induction W as [|[x y] W IH]; cbn [outside]; [exact I|]. inversion HW as [|? ? HO HW']; subst. unfold own_iv in HO. cbn [fst snd] in HO.
    split; [clear - HO H2 H3 FLO FHI SHF1 SHF2; lia| exact (IH HW')].
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma hinv_stepOwn : forall t t' (scr : Z -> mem -> Prop) (W : list ivl) q' cur ty tb tl va vl bs mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch W m m' -> wmono asegs m m' -> Forall own_iv W ->
    (exists j, rw_cells asegs m' (F + 32) [CB 88 j]) -> rw_cells asegs m' SF (hshadow t') -> mem_inv asegs m' ->
    (scr q' m -> scr q' m') ->
    hinvGT t' scr q' cur ty tb tl va vl bs mb m'.
  Proof.
    intros t t' scr W q' cur ty tb tl va vl bs mb m m'
      (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & (QB & QAL) & HR) MUs WMs HW FT1' SHF' MI' SCRT.
    destruct HR as (Hq & GAP & FRhi & FH & _ & (j2 & FT2) & (j3 & FT3) & FLP & _ & FLG & MU & WM & FK & (stc & RF & LIVE1) & HPM).
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    pose proof fs_shadow_band as (SB1 & SB2 & SB3). pose proof (fs_shadow_apart FI) as FSAP. pose proof text_out_fs as (T1 & T2).
    pose proof (fsb_ok FI) as (B1 & B2 & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    destruct sh_window_ok as (W1 & W2 & W3 & W4).
    pose proof (new_frame_fk FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.

    assert (FLAP : (FL + 1 <= F + 32) /\ (FL + 1 <= SF \/ SF + 32 <= FL)) by (clear - FSAP FLLO FLHI FLO SHF1 SHF2; lia).
    assert (PAP1 : P + 504 <= F + 32 \/ F + 120 <= P) by (clear - PAF; lia).
    assert (PAP2 : P + 504 <= SF \/ SF + 32 <= P) by (clear - FSAP PF1 PF2 SHF1 SHF2; lia).
    assert (AAP1 : A + (cap + 1) <= F + 32 \/ F + 120 <= A) by (clear - T1 FLO FHI B1; lia).
    assert (AAP2 : A + (cap + 1) <= SF \/ SF + 32 <= A) by (clear - T2 SHF1 SHF2; lia).
    assert (STK1 : F + 120 <= lo /\ SF + 32 <= lo) by (clear - SB3 SHF2 FHI B2 CLO; lia).
    assert (FSF : F + 256 <= SF \/ SF + 32 <= F) by (clear - FSAP FLO FHI SHF1 SHF2; lia).
    assert (QLO : lo <= q') by (clear - QB LO; lia).
    clear FSAP T1 T2 PAF PAFL. hide TFS. hide TBAND.
    assert (FSW : Forall (fsw_iv FI) W).
    { eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold own_iv in HO. cbn [fst snd] in HO.
      destruct HO as [LE [HO|HO]]; [left; apply sub_app_iv_fsH; clear - LE HO FLO FHI B1; lia| right; cbn [fst snd]; clear - HO SHF1 SHF2; lia]. }
    assert (FKs : fkeep FI WHS st m m').
    { apply (fkeep_of_munch FI WHS W st stc m m m' RF LSUB MUs). eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold own_iv in HO. cbn [fst snd] in HO.
      replace y with (x + (y - x)) by lia. apply NFK. cbn [FB_of SB_of]. clear - HO. lia. }
    unfold hinvGT.
    split; [eapply stk_transport_disjoint; [exact ST| exact MUs| exact WMs| apply own_dj; [exact HW| clear - STK1; lia| clear - STK1; lia]]|].
    split; [exact (SCRT SCR)|].
    split; [eapply rw_cells_transport; [exact TOK| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear - STK1 QLO; lia| simpl_sizes; clear - STK1 QLO; lia]]|].
    split; [eapply rw_cells_transport; [exact VAL| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear; lia| simpl_sizes; clear - FSF; lia]]|].
    split; [eapply rw_cells_transport; [exact SC| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear - PAP1; lia| simpl_sizes; clear - PAP2; lia]]|].
    split; [eapply rw_cells_transport; [exact MBC| exact MUs| exact WMs| apply own_dj; [exact HW| unfold mbuf_cells; simpl_sizes; clear - PAP1; lia| unfold mbuf_cells; simpl_sizes; clear - PAP2; lia]]|].
    split. { eapply rw_cells_transport; [exact TXT| exact MUs| exact WMs|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia.
             apply own_dj; [exact HW| clear - AAP1; lia| clear - AAP2; lia]. }
    split; [exact MI'|].
    split. { eapply asan_env_frame; [exact AE| exact MUs| exact WMs|]. unfold env_safe. eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold own_iv in HO. cbn [fst snd] in HO |- *.
             left. clear - HO FLO B1 SHF1 SB1. lia. }
    split; [exact (shwP_fkeep m m' SHP FKs)|].
    split; [unhide TFS; exact (shw_frame_fs FI _ _ _ _ _ SHA MUs FSW TFS)|].
    split; [apply (shw_frame_fs FI _ _ _ _ _ SHSEP MUs FSW); left; unfold SEPTAB_A; clear - B1; lia|].
    split; [apply (shw_frame_fs FI _ _ _ _ _ SHFMT MUs FSW); left; clear - B1; lia|].
    split; [eapply (shz_stack_fs FI); [exact SHZ| exact CLO| clear - W1 W2; lia| clear - W3; lia| exact MUs| exact FSW]|].
    split; [eapply (shr_stack_fs FI); [exact SHR| exact CLO| clear; lia| clear - W4; lia| exact MUs| exact FSW]|].
    split; [exact CR|]. split; [split; [exact QB| exact QAL]|].
    unfold hrestT.
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUs| exact WMs| apply own_dj; [exact HW| clear - STK1 QLO; lia| clear - STK1 QLO; lia]]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear - STK1 QLO QB; lia| simpl_sizes; clear - STK1 QLO QB; lia]]|].
    split; [eapply rw_cells_transport; [exact FH| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear; lia| simpl_sizes; clear - FSF; lia]]|].
    split; [exact FT1'|].
    split; [exists j2; eapply rw_cells_transport; [exact FT2| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear; lia| simpl_sizes; clear - FSF; lia]]|].
    split; [exists j3; eapply rw_cells_transport; [exact FT3| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear; lia| simpl_sizes; clear - FSF; lia]]|].
    split; [eapply rw_cells_transport; [exact FLP| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear; lia| simpl_sizes; clear - FSF; lia]]|].
    split; [exact SHF'|].
    split; [eapply rw_cells_transport; [exact FLG| exact MUs| exact WMs| apply own_dj; [exact HW| simpl_sizes; clear - FLAP; lia| simpl_sizes; clear - FLAP; lia]]|].
    split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [exact (own_sub0 W HW)| exact MUs]|].
    split; [eapply wmono_trans; [exact WM| exact WMs]|].
    split; [eapply fkeep_trans; [exact FK| exact FKs]|].
    split. { exists stc. split; [| exact LIVE1].
      eapply (rfake_frame FI stc m m' _ RF MUs WMs). eapply Forall_impl; [| exact HW]. intros [x y] HO. unfold own_iv in HO. cbn [fst snd] in HO |- *.
      destruct HO as [LE [HO|HO]]; [right; left; apply (Contracts.lb_sub _ _ _ _ _ LVF); clear - HO; lia| right; right; apply (ls_sub _ _ _ _ _ LVS); clear - HO; lia]. }
    apply (hpm_step W mb m m' HPM MUs WMs). apply own_dj; [exact HW| clear - PAP1; lia| clear - PAP2; lia].
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma hinv_stepL : forall t (scr : Z -> mem -> Prop) q' cur ty tb tl va vl bs mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch [(lo, q')]%Z m m' -> wmono asegs m m' ->
    stk asegs m' lo q' -> mem_inv asegs m' -> (scr q' m -> scr q' m') ->
    hinvGT t scr q' cur ty tb tl va vl bs mb m'.
  Proof.
    intros t scr q' cur ty tb tl va vl bs mb m m' INV MUX WMX ST' MI' SCRT.
    pose proof INV as (ST & SCR & TOK & VAL & SC & MBC & TXT & _ & _ & _ & _ & _ & _ & _ & _ & CR & (QB & _) & _).
    pose proof HOK as HOK'. hokA HOK'. pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct hframe_facts as (FLO & FHI & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    assert (DJ : forall a n, (q' <= a) \/ (a + n <= alloc_ceiling) -> disjoint_from [(lo, q')]%Z a n)
      by (intros a n Ha; cbn [disjoint_from]; split; [clear - Ha CLO; lia| exact I]).
    clear TFS TBAND.
    eapply (hinv_stepW t scr scr q' cur ty tb tl va vl bs cur ty tb tl va vl bs mb m m' INV);
      [eapply munch_weaken; [| exact MUX]| exact WMX| exact ST'| exact (SCRT SCR)| | | | | | exact MI'| exact CR].
    - unfold sub_fp, hWL. intros xo Ho. cbn [outside] in *. destruct Ho as (H1 & _). split; [clear - H1; lia| exact I].
    - eapply rw_cells_transport; [exact TOK| exact MUX| exact WMX| apply DJ; left; clear; lia].
    - eapply rw_cells_transport; [exact VAL| exact MUX| exact WMX| apply DJ; right; simpl_sizes; clear - FHI B2; lia].
    - eapply rw_cells_transport; [exact SC| exact MUX| exact WMX| apply DJ; right; simpl_sizes; clear - PHI; lia].
    - eapply rw_cells_transport; [exact MBC| exact MUX| exact WMX| apply DJ; right; unfold mbuf_cells; simpl_sizes; clear - PHI; lia].
    - eapply rw_cells_transport; [exact TXT| exact MUX| exact WMX| apply DJ; right; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - AHI; lia].
  Qed.
  #[using="ws WSL"] Lemma hscr_stepL : forall q' m m', hscr q' m -> munch [(lo, q')]%Z m m' -> wmono asegs m m' -> hscr q' m'.
  Proof.
    intros q' m m' (j0 & w32 & j96 & j128 & SCR) MU WM. exists j0, w32, j96, j128.
    eapply rw_cells_transport; [exact SCR| exact MU| exact WM|]. cbn [disjoint_from]. split; [right; lia| exact I].
  Qed.
  #[using="HC FI q P A len cap st HOK WSL"] Lemma hstat_stepL : forall q' m m', hstat m -> munch [(lo, q')]%Z m m' -> wmono asegs m m' -> hstat m'.
  Proof.
    intros q' m m' HS MUX WMX. hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    eapply (hstat_step _ m m' HS MUX WMX); [constructor; [left; apply app_iv_stack; lia| constructor]| constructor; [cbn [fst]; lia| constructor]].
  Qed.

  #[using="len m0 HOK RF0 ws WSL"] Lemma htmp_shw : forall q' mb m, hrestT 0 q' mb m -> shw m (F + 32) 88.
  Proof.
    intros q' mb m (_ & _ & _ & _ & _ & _ & _ & _ & SHF & _).
    hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL). pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    assert (F8 : F mod 8 = 0) by (clear - FAL; Z.div_mod_to_equations; lia).
    unfold hshadow in SHF.
    change [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
            C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      with (shadow_cells [241; 241; 241; 241; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 242; 242; 242; 242; 242; 0; 0; 243; 243; 0; 0; 0; 0; 0; 0; 0; 0]) in SHF.
    split; [| split].
    - eapply (accessible_of_chunk m F _ (F + 32) 88 SHF F8); [lia| cbn [length]; lia|].
      intros i Hi H1 H2. cbn [length] in Hi.
      assert (Ei : (4 <= i <= 14)%nat) by lia.
      do 4 (destruct i as [|i]; [lia|]). do 11 (destruct i as [|i]; [reflexivity|]). lia.
    - eapply (sh_readable_of_chunk m F _ (F + 32) 88 SHF); cbn [length]; unfold sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia.
    - unfold win_ok. split; [lia|]. clear - FLO FHI B1 B2 B5 ACR. change (2^47) with 140737488355328. lia.
  Qed.

  #[using="Type"] Lemma lsegA_In : forall ns m first pv TAIL N it id,
    lsegA m ns first pv TAIL -> In (N, it, id) ns -> exists pv' nx, rw_cells asegs m N (node_cells pv' nx it).
  Proof.
    induction ns as [|[[N0 it0] id0] ns IH]; intros m first pv TAIL N it id LS HI; [destruct HI|]. cbn [lsegA] in LS.
    destruct LS as (E & NT & NNZ & ITNZ & IDR & nx & n1 & n2 & pad & NC & ICc & LS').
    destruct HI as [HI|HI]; [inversion HI; subst; exists pv, nx; exact NC| exact (IH m nx N0 TAIL N it id LS' HI)].
  Qed.

  Definition hapx (X n : Z) : Prop :=
    (X + n <= FSB FI \/ FSB FI + A0_FS_SIZE <= X) /\ (X + n + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= X) /\ (X + n <= A \/ A + (cap + 1) <= X).
  Definition hlist (m : mem) (first last size flh fk ffree : Z) (ns : list (Z * Z * Z)) : Prop :=
    rw_cells asegs m L (llist_cells first last size flh fk ffree httpmsg_compare_entryA)
    /\ lsegA m ns first L (L + 24)
    /\ (forall N it id, In (N, it, id) ns -> objA m N 24 /\ objA m it 24)
    /\ (forall N it id, In (N, it, id) ns -> hapx N 24 /\ hapx it 24).

  #[using="len st m0 HOK RF0"] Lemma hapx_dj0 : forall X n, 0x609000 <= X -> X + n <= alloc_ceiling -> 0 <= n -> hapx X n -> disjoint_from W0 X n.
  Proof.
    intros X n XLO XHI Hn (H1 & H2 & H3). hokA HOK. destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    pose proof fs_shadow_band as (S1 & S2 & _).
    unfold hW0, hWHS. cbn [disjoint_from].
    split; [left; clear - XHI CLO; lia|]. split; [clear - H1; lia|]. split; [clear - H2 S1 S2; lia|]. split; [clear - H3; lia|].
    repeat (split; [clear - H1 PF1 PF2; lia|]). exact I.
  Qed.

  #[using="len m0 HOK RF0 ws WSL"] Lemma hlist_stretch : forall mb m first last size flh fk ffree ns,
    hlist mb first last size flh fk ffree ns -> munch W0 mb m -> wmono asegs mb m -> fkeep FI WHS st mb m ->
    hlist m first last size flh fk ffree ns.
  Proof.
    intros mb m first last size flh fk ffree ns (LC & LS & OBJ & HAP) MU WM FK. hokA HOK.
    split; [| split; [| split; [| exact HAP]]].
    - eapply (rw_cells_fkeep FI WHS st mb m); [exact LC| exact FK| exact WM| left; apply (Contracts.lb_sub _ _ _ _ _ PLB); unfold llist_cells; simpl_sizes; lia|].
      unfold hWHS, llist_cells. cbn [disjoint_from]. simpl_sizes. repeat (split; [lia|]). exact I.
    - eapply lsegA_transport; [exact LS| exact MU| exact WM|]. intros N it id HI.
      destruct (OBJ N it id HI) as [(N1 & N2 & _) (I1 & I2 & _)]. destruct (HAP N it id HI) as [HN HIt].
      split; apply hapx_dj0; assumption || lia.
    - intros N it id HI. destruct (OBJ N it id HI) as [(N1 & N2 & N3 & N4) (I1 & I2 & I3 & I4)]. destruct (HAP N it id HI) as [(HN & _) (HIt & _)].
      split; (split; [assumption|]; split; [assumption|]; split; [assumption|]).
      + exact (shw_frame_fs FI _ _ _ _ _ N4 MU W0_fsw HN).
      + exact (shw_frame_fs FI _ _ _ _ _ I4 MU W0_fsw HIt).
  Qed.

  #[using="q len st HOK ws WSL"] Lemma hlist_stepL : forall q' m m' first last size flh fk ffree ns, lo <= q' ->
    hlist m first last size flh fk ffree ns -> munch [(lo, q')]%Z m m' -> wmono asegs m m' ->
    hlist m' first last size flh fk ffree ns.
  Proof.
    intros q' m m' first last size flh fk ffree ns LQ (LC & LS & OBJ & HAP) MU WM. hokA HOK.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (DJ : forall a n, a + n <= alloc_ceiling -> disjoint_from [(lo, q')]%Z a n) by (intros a n Ha; cbn [disjoint_from]; split; [left; lia| exact I]).
    assert (APP : app_ivs [(lo, q')]%Z) by (constructor; [apply app_iv_stack; lia| constructor]).
    split; [| split; [| split; [| exact HAP]]].
    - eapply rw_cells_transport; [exact LC| exact MU| exact WM| apply DJ; unfold llist_cells; simpl_sizes; lia].
    - eapply lsegA_transport; [exact LS| exact MU| exact WM|]. intros N it id HI.
      destruct (OBJ N it id HI) as [(N1 & N2 & _) (I1 & I2 & _)]. split; apply DJ; lia.
    - intros N it id HI. destruct (OBJ N it id HI) as [(N1 & N2 & N3 & N4) (I1 & I2 & I3 & I4)].
      split; (split; [assumption|]; split; [assumption|]; split; [assumption|]).
      + exact (shw_frame _ _ _ _ _ N4 MU APP).
      + exact (shw_frame _ _ _ _ _ I4 MU APP).
  Qed.

  #[using="len st m0 HOK RF0 ws WSL"] Lemma W0_above : Forall (fun iv : ivl => 0x609000 <= fst iv) W0.
  Proof.
    hokA HOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof fs_shadow_band as (S1 & _).
    unfold hW0, hWHS. repeat (constructor; [cbn [fst]; lia|]). constructor.
  Qed.
  #[using="len st m0 HOK RF0 WSL"] Lemma hstat_stretch : forall mb m, hstat mb -> munch W0 mb m -> wmono asegs mb m -> hstat m.
  Proof. intros mb m HS MU WM. exact (hstat_step W0 mb m HS MU WM W0_fsw W0_above). Qed.

  #[using="m0 HOK RF0 WSL"] Lemma hnow : forall t scr q' cur ty tb tl va vl bs mb m first last size flh fk ffree ns,
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> hstat mb -> hlist mb first last size flh fk ffree ns ->
    hstat m /\ hlist m first last size flh fk ffree ns.
  Proof.
    intros t scr q' cur ty tb tl va vl bs mb m first last size flh fk ffree ns INV HS HLI.
    destruct (hrest_mu t q' mb m (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))))))))))))))) as (MU & WM & FK).
    split; [exact (hstat_stretch mb m HS MU WM)| exact (hlist_stretch mb m _ _ _ _ _ _ _ HLI MU WM FK)].
  Qed.

  #[using="Type"] Lemma hinv_rest : forall t scr q' cur ty tb tl va vl bs mb m, hinvGT t scr q' cur ty tb tl va vl bs mb m -> hrestT t q' mb m.
  Proof. intros t scr q' cur ty tb tl va vl bs mb m INV. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))))))))))))). Qed.
  #[using="HOK ws WSL"] Lemma hpcells_now : forall t scr q' cur ty tb tl va vl bs mb m a cs,
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> rw_cells asegs mb a cs ->
    P <= a -> a + Z.of_nat (cells_size cs) <= P + 504 -> disjoint_from WHS a (Z.of_nat (cells_size cs)) ->
    rw_cells asegs m a cs.
  Proof.
    intros t scr q' cur ty tb tl va vl bs mb m a cs INV C H1 H2 DJ. hokA HOK.
    destruct (hrest_mu t q' mb m (hinv_rest _ _ _ _ _ _ _ _ _ _ _ _ INV)) as (MU & WM & FK).
    eapply (rw_cells_fkeep FI WHS st mb m); [exact C| exact FK| exact WM| left; apply (Contracts.lb_sub _ _ _ _ _ PLB); lia| exact DJ].
  Qed.
  #[using="Type"] Lemma hmeth_now : forall t scr q' cur ty tb tl va vl bs mb m meth,
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> rw_cells asegs mb (P + 4) [C4 (wz meth)] ->
    exists meth', rw_cells asegs m (P + 4) [C4 (wz meth')] /\ (meth' = meth \/ meth' = 11).
  Proof. intros t scr q' cur ty tb tl va vl bs mb m meth INV C. exact (hrest_hpm t q' mb m (hinv_rest _ _ _ _ _ _ _ _ _ _ _ _ INV) meth C). Qed.

  Definition newstH (q' id tcur tlz : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            (wz tlz) x19 (wz 2147450880) (wz (A + tcur)) (wz id) (wz 0) (wz (F + 160)) (wz L) x26 (wz SF) x28 x29 x30 x31)
       F_ (wz 0x88474) fc None m (seg_rom asegs).
  Definition existstH (q' it : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x26 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 (wz 2147450880) x21 x22 (wz it) (wz (F + 160)) (wz L) x26 (wz SF) x28 x29 x30 x31)
       F_ (wz 0x8859c) fc None m (seg_rom asegs).

  #[using="lo A len cap m0 HOK RF0"] Lemma hscr_stepSh : forall q' m m', q + -272 <= q' -> hscr q' m -> munch [(SF, SF + 32)]%Z m m' -> wmono asegs m m' -> hscr q' m'.
  Proof.
    intros q' m m' QB (j0 & w32 & j96 & j128 & SCR) MUs WMs. exists j0, w32, j96, j128.
    hokA HOK. pose proof fs_shadow_band as (_ & _ & SB3). destruct hframe_facts as (_ & _ & _ & _ & _ & _ & _ & SHF2 & _).
    eapply rw_cells_transport; [exact SCR| exact MUs| exact WMs|]. cbn [disjoint_from]. simpl_sizes. split; [right; clear - QB LO SB3 SHF2; lia| exact I].
  Qed.

  #[using="m0 HOK RF0 WSL"] Lemma knownB : forall (q' id tcur tlz cur first last size flh fk ffree : Z) (ns : list (Z * Z * Z)) (ty va vl : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m -> hstat mb -> hlist mb first last size flh fk ffree ns -> 0 <= id < 64 ->
    (forall m' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m' ->
       evt asegs Q (newstH q' id tcur tlz y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz TAB_HDR_A) (wz S) y28 y29 y30 y31 m')) ->
    (forall m' (N it : Z) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinv q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m' -> In (N, it, id) ns ->
       evt asegs Q (existstH q' it y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz tlz) (wz TAB_HDR_A) (wz (A + tcur)) (wz id) (wz S) y28 y29 y30 y31 m')) ->
    evt asegs Q (tempstH q' id tcur tlz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    intros q' id tcur tlz cur first last size flh fk ffree ns ty va vl bs mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Q INV HS HLI IDR KNEW KEX.
    pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (QB & _) & _).
    unfold tempstH.
    eapply (unpoisonH hscr q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m); [exact INV| intros ma mb' SCRm MUs WMs; exact (hscr_stepSh q' ma mb' (proj1 QB) SCRm MUs WMs)|].
    intros m1 INV1. clear INV.

    pose proof INV1 as (ST & (j0 & w32 & j96 & j128 & SCR) & _ & _ & _ & _ & _ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR).
    destruct HR as (_ & _ & _ & _ & (j1 & FT1) & _ & _ & _ & SHF & _).
    unfold hshadow in SHF.
    splitcb FT1 0%nat [16; 4; 68]%nat. recell FT1 1%nat. name_junk FT1.
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide PAL. hide AAL.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _). pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (FSF : F + 256 <= SF \/ SF + 32 <= F) by (pose proof (fs_shadow_apart FI) as FSAP; clear - FSAP FLO FHI SHF1 SHF2; lia).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(F + 32, F + 120)]%Z m1) as MUo. pose proof (wmono_refl asegs m1) as WMo.
    step. sstep.
    repeat match type of FT1 with context [CB ?n ?t] => tryif is_var t then fail else (let j := fresh "jb" in set (j := t) in FT1; clearbody j) end.
    assert (INV2 : hinvGT 0 hscr q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m2).
    { eapply (hinv_stepOwn 0 0 hscr [(F + 32, F + 120)]%Z q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m1 m2 INV1 MUo WMo);
        [constructor; [split; [cbn [fst snd]; lia| left; cbn [fst snd]; lia]| constructor]| | unfold hshadow; exact SHF| exact MI| intros _; do 4 eexists; exact SCR].
      lazymatch type of FT1 with rw_cells _ _ _ ?cs => pose proof (rw_cells_merge asegs m2 (F + 32) [] cs []) as M1 end.
      rewrite !app_nil_r in M1. cbn [app cells_size csize Nat.add] in M1. eexists. exact (M1 FT1). }
    destruct (hnow 0 hscr q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m2 first last size flh fk ffree ns INV2 HS HLI) as (HS2 & LC2 & LS2 & OBJ2 & HAP2).
    pose proof INV2 as (_ & _ & _ & _ & _ & _ & _ & _ & AE2 & SHP2 & _ & _ & _ & _ & _ & _ & _ & HR2).
    pose proof (htmp_shw q' mb m2 HR2) as SHT2.
    split_chunk FT1 2%nat ITC FTR.
    step. step. step.
    eapply evt_cut.
    { eapply (ListFind_spec_A L (F + 32) id last size flh fk ffree lo ns _ _ q');
        [ exact LC2 | exact LS2 | exact ITC | lia
        | split; [lia|]; split; [lia|]; split; [unhide PAL; clear - PAL; Z.div_mod_to_equations; lia| apply (shw_sub _ P 504); [exact SHP2| lia| lia| lia]]
        | split; [lia|]; split; [lia|]; split; [unhide FAL; clear - FAL; Z.div_mod_to_equations; lia| apply (shw_sub _ (F + 32) 88); [exact SHT2| lia| lia| lia]]
        | exact OBJ2 | exact AE2 | exact ST | exact CLO | lia | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; lia | exact MI
        | reflexivity | reflexivity | reflexivity ]. }
    intros ms' POST. unfold ListFind_post_A in POST.
    destruct POST as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & r & -> & MU3 & WM3 & MI3 & ST3 & AE3 & RES).
    replace (ret_pc (Z_to_bv 64 558028)) with (Z_to_bv 64 558028) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LQ : lo <= q') by (clear - QB LO; lia).
    pose proof (hinv_stepL 0 hscr q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m2 m3 INV2 MU3 WM3 ST3 MI3 (fun SCRm => hscr_stepL q' m2 m3 SCRm MU3 WM3)) as INV3.
    pose proof (hlist_stepL q' m2 m3 first last size flh fk ffree ns LQ (conj LC2 (conj LS2 (conj OBJ2 HAP2))) MU3 WM3) as (_ & LS3 & OBJ3 & _).
    clear - INV3 LS3 OBJ3 RES KNEW KEX HOK RF0 QB IDR ws WSL HID.
    assert (SCRT : forall ma mb', hscr q' ma -> munch [(SF, SF + 32)]%Z ma mb' -> wmono asegs ma mb' -> hscr q' mb')
      by (intros ma mb' SCRm MUs WMs; exact (hscr_stepSh q' ma mb' (proj1 QB) SCRm MUs WMs)).
    destruct RES as [-> | (it & HIN)].
    -
      step. lit_branch. step.
      eapply (repoisonH hscr q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m3); [exact INV3| exact SCRT|].
      intros m4 INV4. step. lit_branch.
      eapply KNEW. exact INV4.
    -
      destruct (OBJ3 r it id HIN) as [(N1 & N2 & N3 & SHN) (I1 & I2 & _)].
      destruct (lsegA_In ns m3 first L (L + 24) r it id LS3 HIN) as (pvx & nxx & NC).
      pose proof INV3 as (_ & _ & _ & _ & _ & _ & _ & MI3 & _).
      pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
      unfold node_cells in NC.
      step. if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
      cstep. cstep. cstep. cstep. cstep. cstep. step.
      eapply (repoisonH hscr q' cur ty (wz (A + tcur)) (wz tlz) va vl bs mb m3); [exact INV3| exact SCRT|].
      intros m4 INV4. step. if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
      eapply (KEX m4 r it); [exact INV4| exact HIN].
  Qed.

  Notation zb := (Z_to_bv 8 0).
  Notation set_byte := P0.H_presp_B.set_byte.

  Definition hscrW (w32 : word) (q' : Z) (m : mem) : Prop :=
    exists j0 j96 j128,
      rw_cells asegs m q' [CB 8 j0; C8 (wz P); C8 (wz F); C8 (wz F); C8 w32; C8 (wz (F + 32)); C8 (wz (P + 4)); C8 (wz TAB_HDR_A);
                           C8 (wz S); C8 (wz (P + 488)); C8 (wz FMT_HDR_A); C8 (wz SHC); CB 24 j96; C8 (wz F); CB 4 j128].
  #[using="Type"] Lemma hscrW_hscr : forall w q' m, hscrW w q' m -> hscr q' m.
  Proof. intros w q' m (j0 & j96 & j128 & H). exists j0, w, j96, j128. exact H. Qed.
  #[using="ws WSL"] Lemma hscrW_stepL : forall w q' m m', hscrW w q' m -> munch [(lo, q')]%Z m m' -> wmono asegs m m' -> hscrW w q' m'.
  Proof.
    intros w q' m m' (j0 & j96 & j128 & SCR) MU WM. exists j0, j96, j128.
    eapply rw_cells_transport; [exact SCR| exact MU| exact WM|]. cbn [disjoint_from]. split; [right; lia| exact I].
  Qed.

  Definition hslk (m : mem) (sl : list byte) : Prop :=
    bytes_at asegs m (A + (cap + 1)) sl /\ Z.of_nat (length sl) = (- (A + (cap + 1))) mod 8.
  #[using="len st m0 HOK RF0 ws WSL"] Lemma hslk_stretch : forall mb m sl, hslk mb sl -> munch W0 mb m -> hslk m sl.
  Proof.
    intros mb m sl (B & LS) MU. split; [| exact LS]. hokA HOK. destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    pose proof fs_shadow_band as (S1 & S2 & _). pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _).
    pose proof (Z.mod_pos_bound (- (A + (cap + 1))) 8 ltac:(lia)) as M8.
    assert (FSB8 : FSB FI mod 8 = 0) by (clear - B4; Z.div_mod_to_equations; lia).
    assert (OUTFS : A + (cap + 1) + (- (A + (cap + 1))) mod 8 <= FSB FI \/ FSB FI + A0_FS_SIZE <= A + (cap + 1)).
    { destruct TFS as [T1|T1]; [left| right; clear - T1 LENC; lia]. clear - T1 FSB8. Z.div_mod_to_equations. lia. }
    eapply bytes_at_transport; [exact B| exact MU|]. rewrite LS. unfold hW0, hWHS. cbn [disjoint_from].
    split; [left; clear - AHI CLO M8; lia|].
    split; [clear - OUTFS; lia|].
    split; [clear - TBAND S1 S2 M8 LENC; lia|].
    split; [right; clear; lia|].
    repeat (split; [clear - OUTFS PF1 PF2; lia|]). exact I.
  Qed.

  Definition hnames (m : mem) (ns : list (Z * Z * Z)) : Prop :=
    forall N it id, In (N, it, id) ns -> exists T n tok,
      rw_cells asegs m it (memptr_cells T n) /\ bytes_at asegs m T tok /\ Z.of_nat (length tok) >= n /\ 1 <= n <= 2^43
      /\ shw m T n /\ 0x609000 <= T /\ T + Z.of_nat (length tok) <= alloc_ceiling /\ hapx T (Z.of_nat (length tok)).
  #[using="ws WSL"] Lemma hnames_gen : forall (W : list ivl) m m' ns, hnames m ns -> munch W m m' -> wmono asegs m m' -> Forall (fsw_iv FI) W ->
    (forall N it id, In (N, it, id) ns -> disjoint_from W it 16) ->
    (forall X n, 0x609000 <= X -> X + n <= alloc_ceiling -> 0 <= n -> hapx X n -> disjoint_from W X n) ->
    hnames m' ns.
  Proof.
    intros W m m' ns HN MU WM HF DIT DJ N it id HI. destruct (HN N it id HI) as (T & n & tok & MPC & TOK & TL & N1 & SHT & TLO & THI & HAP).
    exists T, n, tok. split; [eapply rw_cells_transport; [exact MPC| exact MU| exact WM| unfold memptr_cells; cbn [cells_size csize Nat.add]; exact (DIT N it id HI)]|].
    split; [eapply bytes_at_transport; [exact TOK| exact MU| apply DJ; [exact TLO| exact THI| lia| exact HAP]]|].
    split; [exact TL|]. split; [exact N1|].
    split; [apply (shw_frame_fs FI W m m' _ _ SHT MU HF); destruct HAP as (H1 & _); lia|].
    split; [exact TLO|]. split; [exact THI| exact HAP].
  Qed.

  #[using="ra ws WSL"] Lemma cb_split1H : forall m X (n : nat) (xs : list byte) (k : nat) (b : byte),
    rw_cells asegs m X [CB n xs] -> nth_error xs k = Some b -> 0 <= X ->
    rw_cells asegs m X [CB k (firstn k xs)] /\ rw_cells asegs m (X + Z.of_nat k) [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)].
  Proof.
    intros m X n xs k b BLK Hb X0.
    assert (LXS : length xs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    assert (LT : (k < length xs)%nat) by (apply nth_error_Some; rewrite Hb; discriminate).
    apply (rw_cells_split_CB asegs m X [] n xs [] [k; 1%nat; (n - k - 1)%nat]) in BLK; [| cbn; lia].
    cbn [app mk_CB_cells] in BLK.
    lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
      destruct (proj1 (rw_cells_app asegs m X [c1] [c2; c3]) BLK) as [BLK1 BLK23] end.
    cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r in BLK23.
    assert (E1 : firstn 1 (skipn k xs) = [b]).
    { destruct (nth_error_split _ _ _ Hb) as (pre & post & E & Hlen). rewrite E at 1. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity. }
    rewrite E1 in BLK23.
    replace (firstn (n - k - 1) (skipn 1 (skipn k xs))) with (skipn (k + 1) xs) in BLK23.
    2:{ rewrite skipn_skipn. replace (1 + k)%nat with (k + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
    split; [exact BLK1| exact BLK23].
  Qed.
  #[using="ws WSL"] Lemma cb_join1H : forall m X (n : nat) (xs : list byte) (k : nat) (b : byte),
    rw_cells asegs m X [CB k (firstn k xs)] -> rw_cells asegs m (X + Z.of_nat k) [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)] ->
    (k < n)%nat -> length xs = n ->
    rw_cells asegs m X [CB n (set_byte xs k b)].
  Proof.
    intros m X n xs k b BLK1 BLK23 LT LXS.
    pose proof (proj2 (rw_cells_app asegs m X [CB k (firstn k xs)] [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)])) as J.
    cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J. specialize (J (conj BLK1 BLK23)). cbn [app] in J.
    pose proof (rw_cells_merge asegs m X [] [CB k (firstn k xs); CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)] []) as M.
    rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
    replace (k + Datatypes.S (n - k - 1 + 0))%nat with n in M by lia.
    pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ.
  Qed.

  Definition scanstH (pc q' tcur tlz : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            (wz tlz) (wz (A + tcur + tlz)) (wz 2147450880) (wz (A + tcur)) (wz (Z.shiftr (A + tcur + tlz) 3 + 2147450880)) x23 (wz (F + 160)) (wz L) x26 (wz SF) x28 x29 x30 x31)
       F_ (wz pc) fc None m (seg_rom asegs).

  #[using="m0 HOK RF0 ws WSL"] Lemma unkA : forall (q' curS cur tcur tlz : Z) (ty va vl : word) (bs : list byte) (bE : byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' curS ty (wz (A + tcur)) (wz tlz) va vl bs mb m -> 0 <= tcur -> 1 <= tlz -> tcur + tlz = cur -> cur <= len ->
    nth_error bs (Z.to_nat cur) = Some bE ->
    (forall m' y10 y11,
       hinvGT 248 (hscrW (wz (bv_unsigned bE))) q' curS ty (wz (A + tcur)) (wz tlz) va vl (set_byte bs (Z.to_nat cur) zb) mb m' ->
       evt asegs Q (scanstH 0x8840c q' tcur tlz x1 x5 x6 x7 y10 y11 x12 x13 x14 x15 x16 x17 (wz (P + 488)) (wz S) x28 x29 x30 x31 m')) ->
    evt asegs Q (unkstH q' tcur tlz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m).
  Proof.
    intros q' curS cur tcur tlz ty va vl bs bE mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 Q INV TC0 TL1 TCL CLN HbE KK.
    pose proof INV as (ST & (j0 & w32 & j96 & j128 & SCR) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & _ & _ & _ & _ & CR & (QB & QAL) & HR).
    pose proof HOK as HOK'. hokA HOK'. hide TBAND. hide AL16. hide PAL. hide AAL. hide QAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct (text_bytesH m bs TXT) as [_ BL].
    pose proof (munch_refl (WL q') m) as MUL. pose proof (wmono_refl asegs m) as WML. unfold hWL, hWHP in MUL.
    pose proof (proj1 SHA (A + cur) ltac:(lia)) as HACC.
    destruct (cb_split1H m A (Z.to_nat (cap + 1)) bs (Z.to_nat cur) bE TXT HbE ltac:(lia)) as [TX1 TX23]. clear TXT.
    rewrite Z2Nat.id in TX23 by lia.
    remember (Z.to_nat (cap + 1) - Z.to_nat cur - 1)%nat as nr eqn:Enr.
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC. clear HR SHP SHA.
    unfold unkstH.
    zstep. zstep. zstep.
    replace (A + tcur + tlz) with (A + cur) by lia.
    gen2 CONT 0x88400 10%nat 11%nat.
    { intros yi yj.
      remember (A + cur) as V eqn:EV.
      step. sstep. step; fix_lit_store.
      subst V.
      apply (rw_cells_reshape asegs _ _ _ [CB 1 [zb]; CB nr (skipn (Z.to_nat cur + 1) bs)]) in TX23;
        [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
      subst nr.
      pose proof (cb_join1H _ A (Z.to_nat (cap + 1)) bs (Z.to_nat cur) zb TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) ltac:(lia)) as TXT'.
      replace (A + cur) with (A + tcur + tlz) by lia.
      apply (KK _ (zxb bE) yj).
      eapply (hinv_stepW 248 hscr (hscrW (wz (bv_unsigned bE))) q' curS ty (wz (A + tcur)) (wz tlz) va vl bs curS ty (wz (A + tcur)) (wz tlz) va vl _ mb m _ INV MUL WML ST);
        [| exact TOK| exact VAL| exact SC| exact MBC| exact TXT'| exact MI| exact CR].
      do 3 eexists. exact SCR. }
    acc_chk 22 (A + cur) HACC kk SHRk Hk. clear HACC.
    destruct Hk as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT.
    - step. rewrite (sxb_small kk) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT.
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma unkB : forall (q' curS cur tcur tlz s7v : Z) (ty va vl : word) (bs : list byte) (bE : byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinvGT 248 (hscrW (wz (bv_unsigned bE))) q' curS ty (wz (A + tcur)) (wz tlz) va vl (set_byte bs (Z.to_nat cur) zb) mb m ->
    0 <= tcur -> 1 <= tlz -> tcur + tlz = cur -> cur <= len -> nth_error bs (Z.to_nat cur) = Some bE -> 0 <= s7v < 2^64 ->
    (s7v = 0 -> forall m' y10 y11,
       hinv q' curS ty (wz (A + tcur)) (wz tlz) va vl bs mb m' ->
       evt asegs Q (newstH q' (-1) tcur tlz x1 x5 x6 x7 y10 y11 x12 x13 x14 x15 x16 x17 (wz (A + tcur + tlz)) x26 x28 x29 x30 x31 m')) ->
    (s7v <> 0 -> forall m' y10 y11,
       hinv q' curS ty (wz (A + tcur)) (wz tlz) va vl bs mb m' ->
       evt asegs Q (existstH q' s7v x1 x5 x6 x7 y10 y11 x12 x13 x14 x15 x16 x17 (wz tlz) (wz (A + tcur + tlz)) (wz (A + tcur)) (wz (-1)) x26 x28 x29 x30 x31 m')) ->
    evt asegs Q (scanstH 0x8845c q' tcur tlz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz s7v) x26 x28 x29 x30 x31 m).
  Proof.
    intros q' curS cur tcur tlz s7v ty va vl bs bE mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 Q INV TC0 TL1 TCL CLN HbE S7R KNEW KEX.
    pose proof INV as (ST & (j0 & j96 & j128 & SCR) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & _ & _ & _ & _ & CR & (QB & QAL) & HR).
    pose proof HOK as HOK'. hokA HOK'. hide TBAND. hide AL16. hide PAL. hide AAL. hide QAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof (nth_error_Some (A:=byte) bs (Z.to_nat cur)) as LTb. rewrite HbE in LTb. assert (LT : (Z.to_nat cur < length bs)%nat) by (apply LTb; discriminate). clear LTb.
    set (bs1 := set_byte bs (Z.to_nat cur) zb) in *.
    assert (LB1 : length bs1 = length bs) by (subst bs1; apply P0.H_presp_B.set_byte_length; exact LT).
    destruct (text_bytesH m bs1 TXT) as [_ BL].
    assert (Hz : nth_error bs1 (Z.to_nat cur) = Some zb) by (subst bs1; apply P0.H_presp_B.set_byte_same; exact LT).
    pose proof (munch_refl (WL q') m) as MUL. pose proof (wmono_refl asegs m) as WML. unfold hWL, hWHP in MUL.
    pose proof (proj1 SHA (A + cur) ltac:(lia)) as HACC.
    destruct (cb_split1H m A (Z.to_nat (cap + 1)) bs1 (Z.to_nat cur) zb TXT Hz ltac:(lia)) as [TX1 TX23]. clear TXT.
    rewrite Z2Nat.id in TX23 by lia.
    remember (Z.to_nat (cap + 1) - Z.to_nat cur - 1)%nat as nr eqn:Enr.
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC. clear HR SHP SHA.
    unfold scanstH. replace (A + tcur + tlz) with (A + cur) by lia.
    gen2 CONT 0x88464 10%nat 11%nat.
    { intros yi yj.
      remember (A + cur) as V eqn:EV.
      step.
      step. change (Z_to_bv 64 (bv_unsigned bE)) with (zxb bE). rewrite le1_zxb. mem_after_store. subst V.
      apply (rw_cells_reshape asegs _ _ _ [CB 1 [bE]; CB nr (skipn (Z.to_nat cur + 1) bs1)]) in TX23;
        [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
      subst nr.
      pose proof (cb_join1H _ A (Z.to_nat (cap + 1)) bs1 (Z.to_nat cur) bE TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) ltac:(lia)) as TXT'.
      assert (RESTORE : set_byte bs1 (Z.to_nat cur) bE = bs) by (subst bs1; apply P0.H_presp_B.set_byte_restore; exact HbE).
      rewrite RESTORE in TXT'.
      zstep.
      assert (INV' : hinv q' curS ty (wz (A + tcur)) (wz tlz) va vl bs mb m1).
      { eapply (hinv_stepW 248 (hscrW (wz (bv_unsigned bE))) hscr q' curS ty (wz (A + tcur)) (wz tlz) va vl bs1 curS ty (wz (A + tcur)) (wz tlz) va vl bs mb m m1 INV MUL WML ST);
          [| exact TOK| exact VAL| exact SC| exact MBC| exact TXT'| exact MI| exact CR].
        apply (hscrW_hscr (wz (bv_unsigned bE))). do 3 eexists. exact SCR. }
      replace (A + cur) with (A + tcur + tlz) by lia.
      step. if_cases K0; zify_cond K0.
      - apply (KEX ltac:(lia) m1 _ yj). exact INV'.
      - assert (S70 : s7v = 0) by lia. subst s7v. apply (KNEW eq_refl m1 _ yj). exact INV'. }
    acc_chk 22 (A + cur) HACC kk SHRk Hk. clear HACC.
    destruct Hk as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT.
    - step. rewrite (sxb_small kk) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT.
  Qed.

  #[using="len st m0 HOK RF0 ws WSL"] Lemma lseg_stretch : forall mb m (nsr ns : list (Z * Z * Z)) first last size flh fk ffree N pv,
    hlist mb first last size flh fk ffree ns -> (forall x, In x nsr -> In x ns) ->
    lsegA mb nsr N pv (L + 24) -> munch W0 mb m -> wmono asegs mb m -> lsegA m nsr N pv (L + 24).
  Proof.
    intros mb m nsr ns first last size flh fk ffree N pv (_ & _ & OBJ & HAP) SUB LS MU WM.
    eapply lsegA_transport; [exact LS| exact MU| exact WM|]. intros N1 it id HI. pose proof (SUB _ HI) as HI'.
    destruct (OBJ N1 it id HI') as [(N1a & N2a & _) (I1 & I2 & _)]. destruct (HAP N1 it id HI') as [HN HIt].
    split; apply hapx_dj0; assumption || lia.
  Qed.
  #[using="len st m0 HOK RF0 ws WSL"] Lemma hnames_stretch : forall mb m ns first last size flh fk ffree,
    hlist mb first last size flh fk ffree ns -> hnames mb ns -> munch W0 mb m -> wmono asegs mb m -> hnames m ns.
  Proof.
    intros mb m ns first last size flh fk ffree (_ & _ & OBJ & HAP) HN MU WM.
    eapply (hnames_gen W0 mb m ns HN MU WM W0_fsw).
    - intros N it id HI. destruct (OBJ N it id HI) as [_ (I1 & I2 & _)]. destruct (HAP N it id HI) as [_ (H1 & H2 & H3)].
      apply hapx_dj0; [exact I1| lia| lia|]. split; [lia|]. split; [lia| lia].
    - intros X n X1 X2 Xn HX. exact (hapx_dj0 X n X1 X2 Xn HX).
  Qed.

  #[using="HC FI q lo P len st HOK ws WSL"] Lemma hcstr : forall m (bs1 sl : list byte) (tcur tlz : Z),
    rw_cells asegs m A [CB (Z.to_nat (cap + 1)) bs1] -> hslk m sl -> 0 <= tcur -> 1 <= tlz -> tcur + tlz <= cap ->
    nth_error bs1 (Z.to_nat (tcur + tlz)) = Some zb ->
    exists str slack, bytes_at asegs m (A + tcur) (str ++ zb :: slack) /\ ~ In zb str
      /\ (- (A + tcur + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
      /\ Z.of_nat (length str) <= tlz
      /\ A + tcur + Z.of_nat (length str) + 1 + Z.of_nat (length slack) = A + (cap + 1) + Z.of_nat (length sl).
  Proof.
    intros m bs1 sl tcur tlz TXT (SLB & SLL) TC0 TL1 TCL Hz.
    destruct (text_bytesH m bs1 TXT) as [BUF BL].
    pose proof (bytes_skipnH m A bs1 tcur BUF ltac:(lia)) as TOKB.
    assert (INZ : In zb (skipn (Z.to_nat tcur) bs1)).
    { apply (nth_error_In _ (Z.to_nat tlz)). rewrite P0.H_presp_B.nth_error_skipnZ. rewrite <- Hz. f_equal. lia. }
    destruct (P0.H_phdr_A.first_nul _ zb INZ) as (str & r & E & NI).
    assert (LSTR : (length str <= Z.to_nat tlz)%nat).
    { destruct (Nat.le_gt_cases (length str) (Z.to_nat tlz)) as [H|H]; [exact H| exfalso].
      apply NI. apply (nth_error_In _ (Z.to_nat tlz)).
      assert (X : nth_error (skipn (Z.to_nat tcur) bs1) (Z.to_nat tlz) = Some zb) by (rewrite P0.H_presp_B.nth_error_skipnZ; rewrite <- Hz; f_equal; lia).
      rewrite E in X. rewrite nth_error_app1 in X by lia. exact X. }
    assert (LEN : Z.of_nat (length (skipn (Z.to_nat tcur) bs1)) = cap + 1 - tcur) by (rewrite length_skipn; lia).
    rewrite E in LEN. rewrite length_app in LEN. cbn [length] in LEN.
    exists str, (r ++ sl).
    split. { replace (str ++ zb :: r ++ sl) with ((str ++ zb :: r) ++ sl) by (rewrite <- app_assoc; reflexivity).
             apply bytes_at_app. split; [rewrite <- E; exact TOKB|]. rewrite <- E. replace (A + tcur + Z.of_nat (length (skipn (Z.to_nat tcur) bs1))) with (A + (cap + 1)) by (rewrite length_skipn; lia). exact SLB. }
    split; [exact NI|]. rewrite length_app.
    split; [rewrite Nat2Z.inj_add, SLL; clear - LEN; Z.div_mod_to_equations; lia|].
    split; [lia|]. rewrite Nat2Z.inj_add. lia.
  Qed.

  #[using="IC m0 HOK RF0 ws WSL"] Lemma unkLoop : forall (nsr : list (Z * Z * Z)) (N pv q' curS cur tcur tlz first last size flh fk ffree : Z) (ns : list (Z * Z * Z))
      (w ty va vl : word) (bs1 sl : list byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinvGT 248 (hscrW w) q' curS ty (wz (A + tcur)) (wz tlz) va vl bs1 mb m ->
    hlist mb first last size flh fk ffree ns -> hnames mb ns -> hslk mb sl ->
    (forall x, In x nsr -> In x ns) -> lsegA m nsr N pv (L + 24) -> nsr <> [] ->
    0 <= tcur -> 1 <= tlz -> tcur + tlz = cur -> cur <= len -> nth_error bs1 (Z.to_nat cur) = Some zb ->
    (forall m' (s7v : Z) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y26 y28 y29 y30 y31,
       hinvGT 248 (hscrW w) q' curS ty (wz (A + tcur)) (wz tlz) va vl bs1 mb m' ->
       (s7v = 0 \/ exists N' id', In (N', s7v, id') ns) -> 0 <= s7v < 2^64 ->
       evt asegs Q (scanstH 0x8845c q' tcur tlz y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz s7v) y26 y28 y29 y30 y31 m')) ->
    evt asegs Q (scanstH 0x8841c q' tcur tlz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 (wz N) x28 x29 x30 x31 m).
  Proof.
    induction nsr as [|[[N0 it] id] rest IH];
      intros N pv q' curS cur tcur tlz first last size flh fk ffree ns w ty va vl bs1 sl mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 Q
             INV HLI HNM HSL SUB LSB NNE TC0 TL1 TCL CLN Hz KK; [contradiction|]. clear NNE.
    pose proof INV as (ST & SCR & _ & _ & _ & _ & TXT & MI & AE & SHP & SHA & _ & _ & _ & _ & CR & (QB & QAL) & HR).
    destruct (hrest_mu 248 q' mb m HR) as (MU & WM & FK).
    pose proof (hlist_stretch mb m _ _ _ _ _ _ _ HLI MU WM FK) as (LC & _ & OBJ & HAP).
    pose proof (hnames_stretch mb m ns _ _ _ _ _ _ HLI HNM MU WM) as HNMm.
    pose proof (hslk_stretch mb m sl HSL MU) as HSLm.
    cbn [lsegA] in LSB. destruct LSB as (-> & NT & NNZ & ITNZ & IDR & nx & n1 & n2 & pad & NC & ICc & LSr).
    assert (HIN : In (N0, it, id) ns) by (apply SUB; left; reflexivity).
    destruct (OBJ N0 it id HIN) as [(N1 & N2 & N3 & SHN) (I1 & I2 & I3 & SHI)].
    destruct (HNMm N0 it id HIN) as (T & n & tok & MPC & TOKB & TOKL & NR & SHT & TLO & THI & _).
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide PAL. hide AAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (hcstr m bs1 sl tcur tlz TXT HSLm TC0 TL1 ltac:(lia) ltac:(rewrite TCL; exact Hz)) as (str & slack & CSTR & NONUL & PAD & LSTR & CEND).
    assert (SLB : Z.of_nat (length sl) < 8) by (destruct HSLm as [_ E]; rewrite E; apply Z.mod_pos_bound; lia).
    unfold node_cells in NC. unfold scanstH.
    pose proof HLI as HLIx. pose proof HNM as HNMx. pose proof HSL as HSLx.
    clear HR MU WM FK HLI HNM HSL.
    cstep. cstep. cstep. cstep. cstep. cstep.
    zstep. zstep. step.
    eapply evt_cut.
    { eapply (memptr_cmp_nocase_shw IC it T n (A + tcur) lo tok str slack q');
        [ exact MPC | exact TOKB | exact TOKL | exact NR | exact CSTR | exact NONUL | exact PAD | exact AE
        | apply (shw_sub _ it 24); [exact SHI| lia| lia| lia]
        | exact SHT
        | apply (shw_sub _ A (cap + 1)); [exact SHA| lia| lia| lia]
        | exact I1 | lia | exact I3 | exact THI | lia | lia
        | exact ST | exact CLO | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; lia | unfold A0_RT_STACK; lia | exact MI
        | reflexivity | reflexivity ]. }
    intros ms' POST. unfold memptr_cmp_post_A in POST.
    destruct POST as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & r & -> & MU2 & WM2 & MI2 & ST2 & AE2 & RR).
    replace (ret_pc (Z_to_bv 64 558144)) with (Z_to_bv 64 558144) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LQ : lo <= q') by (clear - QB LO; lia).
    pose proof (hinv_stepL 248 (hscrW w) q' curS ty (wz (A + tcur)) (wz tlz) va vl bs1 mb m m2 INV MU2 WM2 ST2 MI2 (fun SCRm => hscrW_stepL w q' m m2 SCRm MU2 WM2)) as INV2.
    step. if_cases K0; zify_cond K0.
    -
      eapply (KK m2 it); [exact INV2| right; exists N0, id; exact HIN| lia].
    -
      clear K0.
      assert (DJ2 : forall a k, a + k <= alloc_ceiling -> disjoint_from [(lo, q')]%Z a k) by (intros a k Ha; cbn [disjoint_from]; split; [left; lia| exact I]).
      assert (APP2 : app_ivs [(lo, q')]%Z) by (constructor; [apply app_iv_stack; lia| constructor]).
      pose proof (rw_cells_transport asegs _ m m2 _ _ NC MU2 WM2 ltac:(apply DJ2; simpl_sizes; lia)) as NC2.
      pose proof (shw_frame _ _ _ _ _ SHN MU2 APP2) as SHN2.
      assert (LSr2 : lsegA m2 rest nx N0 (L + 24)).
      { eapply lsegA_transport; [exact LSr| exact MU2| exact WM2|]. intros Nx itx idx HI.
        destruct (OBJ Nx itx idx (SUB _ (or_intror HI))) as [(X1 & X2 & _) (X3 & X4 & _)]. split; apply DJ2; lia. }
      assert (NXR : 0 <= nx < 2^64).
      { destruct rest as [|[[Nr itr] idr] rest']; cbn [lsegA] in LSr; [subst nx; destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]; pose proof (fsb_ok FI) as (B1 & _); lia|].
        destruct LSr as (-> & _). destruct (OBJ Nr itr idr (SUB _ (or_intror (or_introl eq_refl)))) as [(X1 & X2 & _) _]. lia. }
      destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
      step. step. step.
      eapply evt_cut.
      { eapply (ListNext_shw L N0 pv nx it lo q');
          [ exact NC2 | lia | exact NNZ | exact NXR | lia | exact AE2 | exact SHN2 | exact N1 | exact N2 | exact N3
          | exact ST2 | exact CLO | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; lia | lia | exact MI2
          | reflexivity | reflexivity ]. }
      intros ms' POST. unfold ListNext_post_A in POST.
      destruct POST as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m3 & -> & MU3 & WM3 & MI3 & ST3 & AE3).
      replace (ret_pc (Z_to_bv 64 558160)) with (Z_to_bv 64 558160) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (hinv_stepL 248 (hscrW w) q' curS ty (wz (A + tcur)) (wz tlz) va vl bs1 mb m2 m3 INV2 MU3 WM3 ST3 MI3 (fun SCRm => hscrW_stepL w q' m2 m3 SCRm MU3 WM3)) as INV3.
      assert (LSr3 : lsegA m3 rest nx N0 (L + 24)).
      { eapply lsegA_transport; [exact LSr2| exact MU3| exact WM3|]. intros Nx itx idx HI.
        destruct (OBJ Nx itx idx (SUB _ (or_intror HI))) as [(X1 & X2 & _) (X3 & X4 & _)]. split; apply DJ2; lia. }
      clear - IH INV3 LSr3 NXR SUB KK TC0 TL1 TCL CLN Hz HLIx HNMx HSLx HOK RF0 ws WSL HID IC.
      destruct rest as [|[[Nr itr] idr] rest'].
      +
        cbn [lsegA] in LSr3. subst nx. rewrite Z.eqb_refl.
        zstep. step. lit_branch. zstep.
        eapply (KK m3 0); [exact INV3| left; reflexivity| lia].
      + pose proof LSr3 as LSx. cbn [lsegA] in LSx. destruct LSx as (-> & NTr & NNZr & _).
        replace (Nr =? L + 24) with false by (symmetry; apply Z.eqb_neq; exact NTr).
        zstep. step. if_cases K1; zify_cond K1; [| exfalso; lia].
        eapply (IH Nr N0 q' curS cur tcur tlz first last size flh fk ffree ns w ty va vl bs1 sl mb m3); [exact INV3| exact HLIx| exact HNMx| exact HSLx| | exact LSr3| discriminate| exact TC0| exact TL1| exact TCL| exact CLN| exact Hz| exact KK].
        intros x Hx. apply SUB. right. exact Hx.
  Qed.

  #[using="IC m0 HOK RF0 ws WSL"] Lemma unkH : forall (q' curS cur tcur tlz first last size flh fk ffree : Z) (ns : list (Z * Z * Z))
      (w ty va vl : word) (bs1 sl : list byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinvGT 248 (hscrW w) q' curS ty (wz (A + tcur)) (wz tlz) va vl bs1 mb m ->
    hlist mb first last size flh fk ffree ns -> hnames mb ns -> hslk mb sl ->
    0 <= size < 2^63 -> (size = 0 <-> ns = []) ->
    0 <= tcur -> 1 <= tlz -> tcur + tlz = cur -> cur <= len -> nth_error bs1 (Z.to_nat cur) = Some zb ->
    (forall m' (s7v : Z) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y26 y28 y29 y30 y31,
       hinvGT 248 (hscrW w) q' curS ty (wz (A + tcur)) (wz tlz) va vl bs1 mb m' ->
       (s7v = 0 \/ exists N' id', In (N', s7v, id') ns) -> 0 <= s7v < 2^64 ->
       evt asegs Q (scanstH 0x8845c q' tcur tlz y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (wz s7v) y26 y28 y29 y30 y31 m')) ->
    evt asegs Q (scanstH 0x8840c q' tcur tlz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' curS cur tcur tlz first last size flh fk ffree ns w ty va vl bs1 sl mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 Q
           INV HLI HNM HSL SZR SZE TC0 TL1 TCL CLN Hz KK.
    pose proof INV as (ST & SCR & _ & _ & _ & _ & _ & MI & AE & SHP & _ & _ & _ & _ & _ & _ & (QB & QAL) & HR).
    destruct (hrest_mu 248 q' mb m HR) as (MU & WM & FK).
    pose proof (hlist_stretch mb m _ _ _ _ _ _ _ HLI MU WM FK) as (LC & LS & OBJ & HAP).
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide AAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    assert (FR : 0 <= first < 2^64).
    { destruct ns as [|[[N0 it] id] rest]; cbn [lsegA] in LS; [subst first; lia|]. destruct LS as (-> & _).
      destruct (OBJ N0 it id (or_introl eq_refl)) as [(X1 & X2 & _) _]. lia. }
    unfold scanstH. clear HR MU WM FK.
    step. step.
    eapply evt_cut.
    { eapply (ListHead_shw L first last size flh fk ffree httpmsg_compare_entryA lo q');
        [ exact LC | lia | exact SZR | exact FR | exact AE
        | apply (shw_sub _ P 504); [exact SHP| lia| lia| lia]
        | lia | lia | clear - PAL; Z.div_mod_to_equations; lia
        | exact ST | exact CLO | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; lia | lia | exact MI | reflexivity ]. }
    intros ms' POST. unfold ListHead_post_A in POST.
    destruct POST as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & AE2).
    replace (ret_pc (Z_to_bv 64 558100)) with (Z_to_bv 64 558100) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (hinv_stepL 248 (hscrW w) q' curS ty (wz (A + tcur)) (wz tlz) va vl bs1 mb m m2 INV MU2 WM2 ST2 MI2 (fun SCRm => hscrW_stepL w q' m m2 SCRm MU2 WM2)) as INV2.
    destruct (Z.eqb_spec size 0) as [S0|S1].
    -
      step. lit_branch. zstep.
      eapply (KK m2 0); [exact INV2| left; reflexivity| lia].
    - assert (NNE : ns <> []) by (intros E; apply S1; apply SZE; exact E).
      assert (LS2 : lsegA m2 ns first L (L + 24)).
      { eapply lsegA_transport; [exact LS| exact MU2| exact WM2|]. intros Nx itx idx HI.
        destruct (OBJ Nx itx idx HI) as [(X1 & X2 & _) (X3 & X4 & _)]. split; (cbn [disjoint_from]; split; [left; lia| exact I]). }
      assert (F0 : first <> 0).
      { destruct ns as [|[[N0 it] id] rest]; [contradiction|]. cbn [lsegA] in LS. destruct LS as (-> & _ & NZ & _). exact NZ. }
      step. if_cases K0; zify_cond K0; [exfalso; lia|].
      zstep.
      eapply (unkLoop ns first L q' curS cur tcur tlz first last size flh fk ffree ns w ty va vl bs1 sl mb m2); [exact INV2| exact HLI| exact HNM| exact HSL| intros x Hx; exact Hx| exact LS2| exact NNE| exact TC0| exact TL1| exact TCL| exact CLN| exact Hz| exact KK].
  Qed.

  Definition nextstH (q' : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 (wz 2147450880) x21 x22 x23 (wz (F + 160)) (wz L) x26 (wz SF) x28 x29 x30 x31)
       F_ (wz 0x885dc) fc None m (seg_rom asegs).

  #[using="IC m0 HOK RF0 ws WSL"] Lemma nextH : forall (q' cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty tb tl va vl bs mb m ->
    (forall m' (tlz ty' : Z) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinv q' (cur + tlz) (wz ty') (wz (A + cur)) (wz tlz) va vl bs mb m' ->
       1 <= tlz -> cur + tlz <= len -> 0 <= ty' <= 5 -> (ty' = TT_IDENTIFIER -> cur + tlz < len) ->
       evt asegs Q (headstH q' cur y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x21 x22 y28 y29 y30 y31 m')) ->
    (forall m' (r : Z) tb' tl' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinvE q' cur ty tb' tl' va vl bs mb m' -> (r = PARSE_INCOMPLETE \/ r = PARSE_FAILURE) ->
       evt asegs Q (xstH q' r cur y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 x22 (wz (F + 160)) (wz L) (wz S) y28 y29 y30 y31 m')) ->
    evt asegs Q (nextstH q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' cur ty tb tl va vl bs mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 Q INV KH KX.
    pose proof INV as (ST & (j0 & w32 & j96 & j128 & SCR) & _ & _ & SC & _ & _ & MI & _ & SHP & _ & _ & _ & _ & _ & CR & (QB & QAL) & _).
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide AAL. hide QAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    unfold nextstH, hSHC in *.
    walk_to 0x889f4%Z.
    clear ST SCR SC MI SHP.
    eapply (sgt_callH 248 hscr q' cur ty tb tl va vl bs mb m); [exact INV| intros m' SCRm MUS WMS; exact (hscr_stepS q' m m' (proj1 QB) SCRm MUS WMS)| |].
    -
      intros m' tlz ty' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV' TL1 CL TY5 STRICT CRL.
      replace (ret_pc (Z_to_bv 64 558596)) with (Z_to_bv 64 558596) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof INV' as (ST & (j0' & w32' & j96' & j128' & SCR) & _ & _ & _ & _ & _ & MI & _).
      unfold PARSE_OK.
      step. step. step. lit_branch.
      eapply (KH m' tlz ty'); [exact INV'| exact TL1| exact CL| exact TY5| intros E; apply STRICT; left; exact E].
    -
      intros m' r tb' tl' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV' HRr.
      replace (ret_pc (Z_to_bv 64 558596)) with (Z_to_bv 64 558596) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof INV' as (ST & (j0' & w32' & j96' & j128' & SCR) & _ & _ & _ & _ & _ & MI & _).
      unfold PARSE_INCOMPLETE, PARSE_FAILURE in *.
      destruct HRr as [-> | ->].
      + step. step. step. lit_branch. step. step. step.
        eapply (KX m' 1 tb' tl'); [exact (hinv_E _ _ _ _ _ _ _ _ _ _ INV')| left; reflexivity].
      + step. step. step. lit_branch. step. step. step.
        eapply (KX m' 3 tb' tl'); [exact (hinv_E _ _ _ _ _ _ _ _ _ _ INV')| right; reflexivity].
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma hinv_stepPR : forall t (scr scr' : Z -> mem -> Prop) q' cur ty tb tl va vl bs mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch [(P + 448, P + 452)]%Z m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    scr' q' m' ->
    hinvGT t scr' q' cur ty tb tl va vl bs m' m'.
  Proof.
    intros t scr scr' q' cur ty tb tl va vl bs mb m m'
      (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & (QB & QAL) & HR) MUs WMs MI' SCR'.
    destruct HR as (Hq & GAP & FRhi & FH & (j1 & FT1) & (j2 & FT2) & (j3 & FT3) & FLP & SHF & FLG & _ & _ & _ & (stc & RF & LIVE1) & _).
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    pose proof (fsb_ok FI) as (B1 & B2 & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    assert (PSH : P + 504 <= SF \/ SF + 32 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 32 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    destruct sh_window_ok as (W1 & W2 & W3 & W4).
    assert (DJ : forall a n, a + n <= P + 448 \/ P + 452 <= a -> disjoint_from [(P + 448, P + 452)]%Z a n) by (intros a n Ha; cbn [disjoint_from]; split; [lia| exact I]).
    assert (WA : app_ivs [(P + 448, P + 452)]%Z) by (constructor; [apply sub_app_iv_fsH; lia| constructor]).
    assert (QLO : P + 504 <= q') by (clear - QB LO PHI CLO; lia).
    assert (AAP : A + (cap + 1) <= P \/ P + 504 <= A) by (clear - TFS PF1 PF2; lia).
    clear TFS TBAND.
    unfold hinvGT.
    split; [eapply stk_transport_disjoint; [exact ST| exact MUs| exact WMs| apply DJ; clear - PHI CLO; lia]|].
    split; [exact SCR'|].
    split; [eapply rw_cells_transport; [exact TOK| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - QLO; lia]|].
    split; [eapply rw_cells_transport; [exact VAL| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - PAF; lia]|].
    split; [eapply rw_cells_transport; [exact SC| exact MUs| exact WMs| apply DJ; simpl_sizes; clear; lia]|].
    split; [eapply rw_cells_transport; [exact MBC| exact MUs| exact WMs| apply DJ; unfold mbuf_cells; simpl_sizes; clear; lia]|].
    split; [eapply rw_cells_transport; [exact TXT| exact MUs| exact WMs| apply DJ; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - AAP; lia]|].
    split; [exact MI'|].
    split; [eapply asan_env_frame; [exact AE| exact MUs| exact WMs|]; unfold env_safe; constructor; [left; cbn [fst snd]; lia| constructor]|].
    split; [exact (shw_frame _ _ _ _ _ SHP MUs WA)|]. split; [exact (shw_frame _ _ _ _ _ SHA MUs WA)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MUs WA)|]. split; [exact (shw_frame _ _ _ _ _ SHFMT MUs WA)|].
    split; [eapply shz_frame; [exact SHZ| lia| lia| exact MUs| exact WA]|].
    split; [eapply shr_frame; [exact SHR| lia| lia| exact MUs| exact WA]|].
    split; [exact CR|]. split; [split; [exact QB| exact QAL]|].
    unfold hrestT.
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUs| exact WMs| apply DJ; clear - QLO; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - QLO QB; lia]|].
    split; [eapply rw_cells_transport; [exact FH| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - PAF; lia]|].
    split; [exists j1; eapply rw_cells_transport; [exact FT1| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - PAF; lia]|].
    split; [exists j2; eapply rw_cells_transport; [exact FT2| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - PAF; lia]|].
    split; [exists j3; eapply rw_cells_transport; [exact FT3| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - PAF; lia]|].
    split; [eapply rw_cells_transport; [exact FLP| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - PAF; lia]|].
    split; [eapply rw_cells_transport; [exact SHF| exact MUs| exact WMs| apply DJ; unfold hshadow; simpl_sizes; clear - PSH; lia]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MUs| exact WMs| apply DJ; simpl_sizes; clear - PAFL; lia]|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [apply fkeep_refl|].
    split; [| apply hpm_refl].
    exists stc. split; [| exact LIVE1].
    eapply (rfake_frame FI stc m m' _ RF MUs WMs). constructor; [right; left; cbn [fst snd]; apply (Contracts.lb_sub _ _ _ _ _ LVP); lia| constructor].
  Qed.

  Definition end_r (ty isreq meth : Z) : Z := if ty =? 2 then (if (negb (isreq =? 0) && (meth =? 4))%bool then 0 else 4) else 3.
  Definition end_pos (ty isreq meth pos : Z) : Z := if ty =? 2 then (if (negb (isreq =? 0) && (meth =? 4))%bool then 4 else 3) else pos.

  #[using="m0 HOK RF0 ws WSL"] Lemma endH : forall (q' sv ty cur isreq maj min meth err hack pos : Z) (pad tb tl va vl : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur (wz ty) tb tl va vl bs mb m -> ty <> 0 -> 0 <= ty <= 5 ->
    rw_cells asegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] -> 0 <= isreq <= 1 ->
    rw_cells asegs m (P + 4) [C4 (wz meth)] -> 0 <= meth <= 11 ->
    rw_cells asegs m (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos)] ->
    (forall mb' m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y24 y25 y26 y28 y29 y30 y31,
       hinvE q' cur (wz ty) tb tl va vl bs mb' m' ->
       ((mb' = mb /\ m' = m /\ ty <> 2) \/ (mb' = m' /\ ty = 2 /\ munch [(P + 448, P + 452)]%Z m m' /\ wmono asegs m m')) ->
       rw_cells asegs m' (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] ->
       rw_cells asegs m' (P + 4) [C4 (wz meth)] ->
       rw_cells asegs m' (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz (end_pos ty isreq meth pos))] ->
       evt asegs Q (epistH q' (end_r ty isreq meth) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y24 y25 y26 y28 y29 y30 y31 m')) ->
    evt asegs Q (endstH q' sv ty x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 m).
  Proof.
    intros q' sv ty cur isreq maj min meth err hack pos pad tb tl va vl bs mb m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 Q
           INV TY0 TY5 VER ISR METH MR CTL KK.
    pose proof INV as (ST & (j0 & w32 & j96 & j128 & SCR) & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & _ & _ & _ & _ & _ & CR & (QB & QAL) & HR).
    pose proof HOK as HOK'. hokA HOK'. hide TBAND. hide AL16. hide AAL. hide QAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & _ & _ & _ & _ & _ & _ & PAF & _). hide PAF.
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof (wmono_refl asegs m) as WML.
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC. clear HR. hide TXT. hide VAL.
    unfold endstH, end_r, end_pos.
    step. step. if_cases K0; zify_cond K0.
    -
      unfold end_r, end_pos in KK. replace (ty =? 2) with false in KK by (symmetry; apply Z.eqb_neq; exact K0).
      step. step. step.
      eapply (KK mb m); [exact (hinv_E _ _ _ _ _ _ _ _ _ _ INV)| left; split; [reflexivity| split; [reflexivity| exact K0]]| exact VER| exact METH| exact CTL].
    -
      assert (TY2 : ty = 2) by lia. subst ty. unfold end_r, end_pos in KK. cbn [Z.eqb Pos.eqb] in KK.
      walk_to 0x88690%Z.
      pose proof (munch_refl [(P + 448, P + 452)]%Z m) as MUc.
      rewrite ?(sx32_lit isreq) by lia.
      step. if_cases K1; zify_cond K1.
      +
        assert (E0 : isreq = 0) by lia. subst isreq. cbn [Z.eqb negb andb] in KK.
        walk_to 0x887fc%Z.
        eapply (KK _ _); [| right; split; [reflexivity| split; [reflexivity| split; [exact MUc| exact WML]]]| eassumption| eassumption| eassumption].
        eapply (hinv_stepPR 248 hscr hscrE q' cur (wz 2) tb tl va vl bs mb m _ INV MUc WML MI).
        apply hscr_E. do 4 eexists. exact SCR.
      + assert (E1 : isreq = 1) by lia. subst isreq. cbn [Z.eqb negb andb] in KK.
        walk_to 0x886ac%Z. rewrite ?(sx32_lit meth) by lia.
        step. if_cases K2; zify_cond K2.
        *
          replace (meth =? 4) with false in KK by (symmetry; apply Z.eqb_neq; lia).
          walk_to 0x887fc%Z.
          eapply (KK _ _); [| right; split; [reflexivity| split; [reflexivity| split; [exact MUc| exact WML]]]| eassumption| eassumption| eassumption].
          eapply (hinv_stepPR 248 hscr hscrE q' cur (wz 2) tb tl va vl bs mb m _ INV MUc WML MI).
          apply hscr_E. do 4 eexists. exact SCR.
        *
          replace (meth =? 4) with true in KK by (symmetry; apply Z.eqb_eq; lia).
          walk_to 0x887fc%Z.
          eapply (KK _ _); [| right; split; [reflexivity| split; [reflexivity| split; [exact MUc| exact WML]]]| eassumption| eassumption| eassumption].
          eapply (hinv_stepPR 248 hscr hscrE q' cur (wz 2) tb tl va vl bs mb m _ INV MUc WML MI).
          apply hscr_E. do 4 eexists. exact SCR.
  Qed.

  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.

  Definition aj_iv (iv : ivl) : Prop :=
    fst iv <= snd iv /\ 0x609000 <= fst iv /\ snd iv <= alloc_ceiling /\
    ( ((snd iv <= FSB FI \/ FSB FI + A0_FS_SIZE <= fst iv) /\ (snd iv + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= fst iv)
       /\ (snd iv <= A \/ A + (cap + 1) <= fst iv))
      \/ (P + 288 <= fst iv /\ snd iv <= P + 384) ).

  #[using="q lo len m0 HOK RF0 ws WSL"] Lemma aj_dj : forall (W : list ivl) a n, Forall aj_iv W ->
    (alloc_ceiling <= a) \/ (F <= a /\ a + n <= F + 256) \/ (SF <= a /\ a + n <= SF + 32) \/ (a = FL /\ n = 1)
    \/ (P + 400 <= a /\ a + n <= P + 504) \/ (A <= a /\ a + n <= A + (cap + 1)) ->
    disjoint_from W a n.
  Proof.
    intros W a n HW HP. hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _). pose proof fs_shadow_band as (S1 & S2 & _).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    assert (PSH : P + 504 <= SF \/ SF + 32 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 32 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    induction W as [|[x y] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
    unfold aj_iv in HO. cbn [fst snd] in HO. destruct HO as (LE & XLO & YHI & [(O1 & O2 & O3)|O4]).
    - destruct HP as [HP|[HP|[HP|[HP|[HP|HP]]]]].
      + clear - HP YHI. lia.
      + clear - HP O1 FLO FHI B1. lia.
      + clear - HP O2 SHF1 SHF2 S1 S2. lia.
      + clear - HP O1 FLLO FLHI B1. lia.
      + clear - HP O1 PF1 PF2. lia.
      + clear - HP O3. lia.
    - destruct HP as [HP|[HP|[HP|[HP|[HP|HP]]]]].
      + clear - HP O4 PHI. lia.
      + clear - HP O4 PAF. lia.
      + clear - HP O4 PSH. lia.
      + clear - HP O4 PAFL. lia.
      + clear - HP O4. lia.
      + clear - HP O4 TFS PF1 PF2. lia.
  Qed.
  #[using="q lo len st m0 HOK RF0"] Lemma aj_app : forall (W : list ivl), Forall aj_iv W -> app_ivs W.
  Proof.
    intros W HW. hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    eapply Forall_impl; [| exact HW]. intros [x y] (LE & XLO & YHI & [(O1 & O2 & O3)|O4]); unfold app_iv, SH_HI; cbn [fst snd] in *; [clear - O2 XLO LE; lia| clear - O4 PF1 PF2 B1 B2 B5 LE; lia].
  Qed.
  #[using="q lo len st m0 HOK RF0"] Lemma aj_out_band : forall (W : list ivl), Forall aj_iv W -> forall a, 0x7fffa000 <= a < 0x800b9200 -> outside W a.
  Proof.
    intros W HW a Ha. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). hokA HOK. destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    induction W as [|[x y] W IH]; cbn [outside]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
    unfold aj_iv in HO. cbn [fst snd] in HO. destruct HO as (LE & XLO & YHI & [(O1 & O2 & O3)|O4]); [clear - O2 Ha; lia| clear - O4 Ha PF1 PF2 B5; lia].
  Qed.
  #[using="q len st m0 HOK RF0"] Lemma aj_out_stksh : forall (W : list ivl), Forall aj_iv W -> forall a, sh lo - sh lo mod 8 <= a < 0x10007fff8000 -> outside W a.
  Proof.
    intros W HW a Ha. pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5). hokA HOK. destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    destruct sh_window_ok as (W1 & _). unfold SH_LO in W1.
    induction W as [|[x y] W IH]; cbn [outside]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
    unfold aj_iv in HO. cbn [fst snd] in HO. destruct HO as (LE & XLO & YHI & [(O1 & O2 & O3)|O4]); [clear - O2 Ha W1; lia| clear - O4 Ha PF1 PF2 B5 W1; lia].
  Qed.

  #[using="ws WSL AMS"] Lemma stack_shadow_clientH : forall (LB : BL) q0 lo' a,
    sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> lo' <= a < 0x10007fff8000 -> aclient FI AI LB q0 a.
  Proof.
    intros LB q0 lo' a H1 H2. right; left. exists lo', 0x10007fff8000. split; [| lia].
    apply AMS. unfold a0_static. split; [lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
  Qed.

  #[using="m0 HOK RF0 ws WSL AMS"] Lemma hinv_stepA : forall t (scr : Z -> mem -> Prop) (W : list ivl) (LBK LB2 : BL) (sx : aps FI AI) (kA : am_K FI AI) (stc : fsstate FI)
      q' cur ty tb tl va vl bs mb m m2,
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> apx FI AI W LBK q' m m2 -> Forall aj_iv W ->
    RHEAP_A FI AI sx LB2 m2 -> In (kA, A, cap + 1) LBK -> In (kA, A, cap + 1) LB2 ->
    stk asegs m2 lo q' -> mem_inv asegs m2 -> asan_env asegs m2 ->
    RFAKE FI stc m -> RFAKE FI stc m2 -> fs_live FI stc = fs_newff FI st 2 :: fs_live FI st ->
    (scr q' m -> scr q' m2) ->
    hinvGT t scr q' cur ty tb tl va vl bs m2 m2.
  Proof.
    intros t scr W LBK LB2 sx kA stc q' cur ty tb tl va vl bs mb m m2
      (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & (QB & QAL) & HR)
      AP HW HR2 KIN KIN2 ST2 MI2 AE2 RF RF2 LIVE1 SCRT.
    destruct HR as (Hq & GAP & FRhi & FH & (j1 & FT1) & (j2 & FT2) & (j3 & FT3) & FLP & SHF & FLG & _ & _ & _ & _ & _).
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _).
    pose proof (fsb_ok FI) as (B1 & B2 & _). destruct (lb_in_fsH _ _ PLB) as [PF1 PF2].
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    destruct sh_window_ok as (W1 & W2 & W3 & W4).
    assert (QLO : lo <= q' /\ alloc_ceiling <= q') by (clear - QB LO CLO; lia).
    hide TFS. hide TBAND.
    assert (TRS : forall X cs, q' <= X -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs HX C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_above; exact HX| apply aj_dj; [exact HW| left; clear - HX QLO; lia]]. }
    assert (TRF : forall X cs, F <= X -> X + Z.of_nat (cells_size cs) <= F + 256 -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs H1 H2 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_fs; clear - H1 H2 FLO FHI; lia| apply aj_dj; [exact HW| right; left; clear - H1 H2; lia]]. }
    assert (TRP : forall X cs, P + 400 <= X -> X + Z.of_nat (cells_size cs) <= P + 504 -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs H1 H2 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_fs; clear - H1 H2 PF1 PF2; lia| apply aj_dj; [exact HW| do 4 right; left; clear - H1 H2; lia]]. }
    unfold hinvGT.
    split; [exact ST2|]. split; [exact (SCRT SCR)|].
    split; [apply TRS; [clear; lia| exact TOK]|].
    split; [apply TRF; [clear; lia| simpl_sizes; clear; lia| exact VAL]|].
    split; [apply TRP; [clear; lia| simpl_sizes; clear; lia| exact SC]|].
    split; [apply TRP; [clear; lia| unfold mbuf_cells; simpl_sizes; clear; lia| exact MBC]|].
    split. { eapply (apx_rw_cells FI AI); [exact AP| exact TXT| | apply aj_dj; [exact HW| do 5 right; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear; lia]].
             cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. eapply (aclient_range_block FI AI); [exact KIN| cbn; lia| cbn; lia]. }
    split; [exact MI2|]. split; [exact AE2|].
    split. { eapply (mlocNB_shw_apx FI AI AMS W LBK q' stc m m2 P 504); [right; exact LVP| exact SHP| exact AP| exact (aj_app W HW)| exact RF| clear - QLO; lia]. }
    split; [eapply (block_shw FI AI sx LB2 m2 (kA, A, cap + 1) A (cap + 1) HR2 KIN2); cbn; lia|].
    assert (IMGSH : forall X n, shw m X n -> 0x10000 <= X -> X + n <= 0x609000 -> shw m2 X n).
    { intros X n SW X1 X2. pose proof (shw_win_ok _ _ _ SW) as [Hn _].
      eapply (shw_band_eq m m2 X n 0x7fffa000 0x800b9200 SW).
      - intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) _ _)) Hv).
        + right; left. exists 0x7fffa000, 0x800b9200. split; [| lia]. apply AMS. unfold a0_static. split; [lia|]. do 11 right. left. lia.
        + apply (aj_out_band W HW). exact Ha.
      - lia.
      - lia.
      - reflexivity.
      - reflexivity.
      - unfold sh, SHADOW_OFF. clear - X1. Z.div_mod_to_equations. lia.
      - intros _. unfold sh, SHADOW_OFF. clear - X2 Hn. Z.div_mod_to_equations. lia. }
    split; [apply IMGSH; [exact SHSEP| unfold SEPTAB_A; lia| unfold SEPTAB_A; lia]|].
    split; [apply IMGSH; [exact SHFMT| lia| lia]|].
    assert (STKSH : forall a, sh lo - sh lo mod 8 <= a < sh q + 8 -> aclient FI AI LBK q' a /\ outside W a).
    { intros a Ha. assert (SLO : sh alloc_ceiling - sh alloc_ceiling mod 8 <= sh lo - sh lo mod 8).
      { pose proof (sh_mono alloc_ceiling lo CLO). clear - H. Z.div_mod_to_equations. lia. }
      split; [apply (stack_shadow_clientH LBK q' (sh lo - sh lo mod 8) a SLO); unfold SH_HI in W4; lia|].
      apply (aj_out_stksh W HW). unfold SH_HI in W4. lia. }
    split. { intros a Ha. destruct (STKSH a ltac:(lia)) as [C O]. exact (gkeep_mrd _ _ _ _ (proj1 (AP a ltac:(unfold SH_LO, SH_HI in *; lia) C O)) (SHZ a Ha)). }
    split. { intros a Ha. destruct (SHR a Ha) as [v Hv]. exists v. destruct (STKSH a Ha) as [C O]. exact (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(unfold SH_LO, SH_HI in *; lia) C O)) Hv). }
    split; [exact CR|]. split; [split; [exact QB| exact QAL]|].
    unfold hrestT.
    split; [exact Hq|].
    split. { eapply (stk_gagree (fun a => aclient FI AI LBK q' a /\ outside W a)); [intros a Ha [Hc Ho]; exact (AP a Ha Hc Ho)| exact GAP|].
             intros a Ha. split; [left; clear - Ha; lia|]. eapply disjoint_outside; [apply (aj_dj W a 1 HW); left; clear - Ha QLO; lia| lia]. }
    split; [apply TRS; [clear - QB; lia| exact FRhi]|].
    split; [apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FH]|].
    split; [exists j1; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT1]|].
    split; [exists j2; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT2]|].
    split; [exists j3; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT3]|].
    split; [apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FLP]|].
    split. { eapply (apx_rw_cells FI AI); [exact AP| exact SHF| apply aclient_range_fs_shadow; unfold hshadow; simpl_sizes; clear - SHF1 SHF2; lia| apply aj_dj; [exact HW| right; right; left; unfold hshadow; simpl_sizes; clear; lia]]. }
    split. { eapply (apx_rw_cells FI AI); [exact AP| exact FLG| apply aclient_range_fs; simpl_sizes; clear - FLLO FLHI; lia| apply aj_dj; [exact HW| do 3 right; left; simpl_sizes; clear; lia]]. }
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [apply fkeep_refl|].
    split; [exists stc; split; [exact RF2| exact LIVE1]| apply hpm_refl].
  Qed.

  Definition ajcallstH (pc ra' q' : Z) (a0 a1 a2 : word) (x5 x6 x7 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR (wz ra') (wz q') gp tp x5 x6 x7 (wz q) (wz q') a0 a1 a2 x13 x14 x15 x16 x17
            x18 x19 (wz 2147450880) x21 x22 x23 (wz (F + 160)) (wz L) x26 (wz SF) x28 x29 x30 x31)
       F_ (wz pc) fc None m (seg_rom asegs).

  Definition ajretstH (ra' q' : Z) (r : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR (wz ra') (wz q') gp tp x5 x6 x7 (wz q) (wz q') r x11 x12 x13 x14 x15 x16 x17
            x18 x19 (wz 2147450880) x21 x22 x23 (wz (F + 160)) (wz L) x26 (wz SF) x28 x29 x30 x31)
       F_ (wz ra') fc None m (seg_rom asegs).

  #[using="ws WSL"] Lemma existE1 : forall (q' it cur l : Z) (ty tb tl va : word) (bs : list byte) (mb m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty tb tl va (wz l) bs mb m -> 0 <= l < 2^63 -> 0 <= it -> it + 24 < 2^64 ->
    (l = 0 -> evt asegs Q (nextstH q' x1 x5 x6 x7 (wz 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 (wz it) x26 x28 x29 x30 x31 m)) ->
    (l <> 0 -> evt asegs Q (ajcallstH 0x8c690 0x885b8 q' (wz (it + 24)) (wz COMMA_ADDR_A) x12 x5 x6 x7 x13 x14 x15 x16 x17 x18 x19 x21 x22 (wz (it + 24)) x26 x28 x29 x30 x31 m)) ->
    evt asegs Q (existstH q' it x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' it cur l ty tb tl va bs mb m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x26 x28 x29 x30 x31 Q INV LR IT0 ITH K0 K1.
    pose proof INV as (_ & _ & _ & VAL & _ & _ & _ & MI & _).
    unfold existstH.
    step. step. if_cases KB; zify_cond KB.
    - assert (L0 : l = 0) by lia. subst l. apply K0. reflexivity.
    - zstep. step. zstep. zstep. step. apply K1. lia.
  Qed.

  #[using="Type"] Lemma existE2 : forall (q' it cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem)
      x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty tb tl va vl bs mb m ->
    evt asegs Q (ajcallstH 0x8c3c4 0x885cc q' (wz (it + 24)) va vl x5 x6 x7 x13 x14 x15 x16 x17 (wz 0) x19 x21 x22 (wz (it + 24)) x26 x28 x29 x30 x31 m) ->
    evt asegs Q (ajretstH 0x885b8 q' (wz 0) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 (wz (it + 24)) x26 x28 x29 x30 x31 m).
  Proof.
    intros q' it cur ty tb tl va vl bs mb m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x26 x28 x29 x30 x31 Q INV K1.
    pose proof INV as (_ & _ & _ & VAL & _ & _ & _ & MI & _).
    unfold ajretstH.
    step. step. zstep. zstep. step. exact K1.
  Qed.

  #[using="Type"] Lemma existE3 : forall (q' : Z) (m : mem)
      x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    mem_inv asegs m ->
    evt asegs Q (nextstH q' (wz 0x885cc) x5 x6 x7 (wz 0) (wz (-104)) x12 x13 x14 x15 x16 x17 (wz 0) x19 x21 x22 x23 x26 x28 x29 x30 x31 m) ->
    evt asegs Q (ajretstH 0x885cc q' (wz 0) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 (wz 0) x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x26 x28 x29 x30 x31 Q MI K1.
    unfold ajretstH.
    step. step. lit_branch. step. step. lit_branch. exact K1.
  Qed.

  Definition hb_iv (q' H : Z) (iv : ivl) : Prop :=
    fst iv <= snd iv /\ ((lo <= fst iv /\ snd iv <= q') \/ (H <= fst iv /\ snd iv <= H + 88) \/ (F + 160 <= fst iv /\ snd iv <= F + 176)).

  #[using="q len m0 HOK RF0 ws WSL"] Lemma hb_dj : forall (W : list ivl) q' H a n, Forall (hb_iv q' H) W -> lo <= q' -> 0x609000 <= H -> H + 88 <= alloc_ceiling -> hapx H 88 ->
    (q' <= a) \/ (F <= a /\ a + n <= F + 160) \/ (F + 176 <= a /\ a + n <= F + 256) \/ (SF <= a /\ a + n <= SF + 32) \/ (a = FL /\ n = 1)
    \/ (P <= a /\ a + n <= P + 504) \/ (A <= a /\ a + n <= A + (cap + 1)) ->
    disjoint_from W a n.
  Proof.
    intros W q' H a n HW LQ HLO HHI (H1 & H2 & H3) HP. hokA HOK. pose proof (fsb_ok FI) as (B1 & B2 & _). pose proof fs_shadow_band as (S1 & S2 & S3).
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL).
    destruct (lb_in_fsH _ _ PLB) as [PF1 PF2]. pose proof (fs_shadow_apart FI) as FSAP.
    assert (PSH : P + 504 <= SF \/ SF + 32 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 32 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    assert (FSF : F + 256 <= SF \/ SF + 32 <= F) by (clear - FSAP FLO FHI SHF1 SHF2; lia).
    assert (FLF : FL + 1 <= F /\ (FL + 1 <= SF \/ SF + 32 <= FL)) by (clear - FSAP FLLO FLHI FLO SHF1 SHF2; lia).
    pose proof text_out_fs as (T1 & T2).
    induction W as [|[x y] W IH]; cbn [disjoint_from]; [exact I|]. inversion HW as [|? ? HO HW']; subst. split; [| exact (IH HW')].
    unfold hb_iv in HO. cbn [fst snd] in HO. destruct HO as (LE & [O1|[O2|O3]]).
    - destruct HP as [HP|[HP|[HP|[HP|[HP|[HP|HP]]]]]].
      + clear - HP O1. lia.
      + clear - HP O1 FHI B2 CLO. lia.
      + clear - HP O1 FHI B2 CLO. lia.
      + clear - HP O1 S3 SHF2. lia.
      + clear - HP O1 FLHI B2 CLO FLO. lia.
      + clear - HP O1 PHI CLO. lia.
      + clear - HP O1 AHI CLO. lia.
    - destruct HP as [HP|[HP|[HP|[HP|[HP|[HP|HP]]]]]].
      + clear - HP O2 HHI CLO LQ. lia.
      + clear - HP O2 H1 FLO FHI B1. lia.
      + clear - HP O2 H1 FLO FHI B1. lia.
      + clear - HP O2 H2 SHF1 SHF2 S1 S2. lia.
      + clear - HP O2 H1 FLLO FLHI B1. lia.
      + clear - HP O2 H1 PF1 PF2. lia.
      + clear - HP O2 H3. lia.
    - destruct HP as [HP|[HP|[HP|[HP|[HP|[HP|HP]]]]]].
      + clear - HP O3 FHI B2 CLO LQ. lia.
      + clear - HP O3. lia.
      + clear - HP O3. lia.
      + clear - HP O3 FSF. lia.
      + clear - HP O3 FLF. lia.
      + clear - HP O3 PAF. lia.
      + clear - HP O3 T1 FLO FHI B1. lia.
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma hinv_stepHB : forall t (scr : Z -> mem -> Prop) (W : list ivl) (H : Z) q' cur ty tb tl va vl va' vl' bs mb m m',
    hinvGT t scr q' cur ty tb tl va vl bs mb m -> munch W m m' -> wmono asegs m m' -> Forall (hb_iv q' H) W ->
    0x609000 <= H -> H + 88 <= alloc_ceiling -> hapx H 88 ->
    stk asegs m' lo q' -> rw_cells asegs m' (F + 160) [C8 va'; C8 vl'] -> mem_inv asegs m' ->
    (scr q' m -> scr q' m') ->
    hinvGT t scr q' cur ty tb tl va' vl' bs m' m'.
  Proof.
    intros t scr W H q' cur ty tb tl va vl va' vl' bs mb m m'
      (ST & SCR & TOK & VAL & SC & MBC & TXT & MI & AE & SHP & SHA & SHSEP & SHFMT & SHZ & SHR & CR & (QB & QAL) & HR) MUs WMs HW HLO HHI HAPH ST' VAL' MI' SCRT.
    destruct HR as (Hq & GAP & FRhi & FH & (j1 & FT1) & (j2 & FT2) & (j3 & FT3) & FLP & SHF & FLG & _ & _ & _ & (stc & RF & LIVE1) & _).
    pose proof HOK as HOK'. hokA HOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & _).
    pose proof (fsb_ok FI) as (B1 & B2 & _). pose proof fs_shadow_band as (S1 & S2 & S3).
    destruct (hlive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    destruct sh_window_ok as (W1 & W2 & W3 & W4).
    pose proof (new_frame_fk FI st 2 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    assert (LQ : lo <= q') by (clear - QB LO; lia).
    pose proof (hb_dj W q' H) as DJ0.
    assert (DJ : forall a n, (q' <= a) \/ (F <= a /\ a + n <= F + 160) \/ (F + 176 <= a /\ a + n <= F + 256) \/ (SF <= a /\ a + n <= SF + 32) \/ (a = FL /\ n = 1)
                             \/ (P <= a /\ a + n <= P + 504) \/ (A <= a /\ a + n <= A + (cap + 1)) -> disjoint_from W a n)
      by (intros a n HP; exact (DJ0 a n HW LQ HLO HHI HAPH HP)). clear DJ0.
    destruct HAPH as (HA1 & HA2 & HA3).
    assert (FSW : Forall (fsw_iv FI) W).
    { eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *; left.
      - apply app_iv_stack. clear - O CLO. lia.
      - unfold app_iv, SH_HI. cbn [fst snd]. clear - O HA2 HLO. lia.
      - apply sub_app_iv_fsH; clear - O LE FLO FHI B1; lia. }
    assert (FKs : fkeep FI WHS st m m').
    { apply (fkeep_of_munch FI WHS W st stc m m m' RF LSUB MUs). eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *.
      - right; left. cbn [fst snd]. clear - O B2 CLO S3. lia.
      - right; left. cbn [fst snd]. clear - O HA1 HA2 S1 S2. lia.
      - replace y with (x + (y - x)) by lia. apply NFK. cbn [FB_of SB_of]. clear - O. lia. }
    hide TFS. hide TBAND.
    unfold hinvGT.
    split; [exact ST'|]. split; [exact (SCRT SCR)|].
    split; [eapply rw_cells_transport; [exact TOK| exact MUs| exact WMs| apply DJ; left; clear; lia]|].
    split; [exact VAL'|].
    split; [eapply rw_cells_transport; [exact SC| exact MUs| exact WMs| apply DJ; do 5 right; left; simpl_sizes; clear; lia]|].
    split; [eapply rw_cells_transport; [exact MBC| exact MUs| exact WMs| apply DJ; do 5 right; left; unfold mbuf_cells; simpl_sizes; clear; lia]|].
    split; [eapply rw_cells_transport; [exact TXT| exact MUs| exact WMs| apply DJ; do 6 right; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear; lia]|].
    split; [exact MI'|].
    split. { eapply asan_env_frame; [exact AE| exact MUs| exact WMs|]. unfold env_safe. eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *; left; [clear - O CLO ACR; lia| clear - O HLO; lia| clear - O FLO B1; lia]. }
    split; [exact (shwP_fkeep m m' SHP FKs)|].
    split; [unhide TFS; exact (shw_frame_fs FI _ _ _ _ _ SHA MUs FSW TFS)|].
    split; [apply (shw_frame_fs FI _ _ _ _ _ SHSEP MUs FSW); left; unfold SEPTAB_A; clear - B1; lia|].
    split; [apply (shw_frame_fs FI _ _ _ _ _ SHFMT MUs FSW); left; clear - B1; lia|].
    split; [eapply (shz_stack_fs FI); [exact SHZ| exact CLO| clear - W1 W2; lia| clear - W3; lia| exact MUs| exact FSW]|].
    split; [eapply (shr_stack_fs FI); [exact SHR| exact CLO| clear; lia| clear - W4; lia| exact MUs| exact FSW]|].
    split; [exact CR|]. split; [split; [exact QB| exact QAL]|].
    unfold hrestT.
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUs| exact WMs| apply DJ; left; clear; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUs| exact WMs| apply DJ; left; clear - QB; lia]|].
    split; [eapply rw_cells_transport; [exact FH| exact MUs| exact WMs| apply DJ; right; left; simpl_sizes; clear; lia]|].
    split; [exists j1; eapply rw_cells_transport; [exact FT1| exact MUs| exact WMs| apply DJ; right; left; simpl_sizes; clear; lia]|].
    split; [exists j2; eapply rw_cells_transport; [exact FT2| exact MUs| exact WMs| apply DJ; right; left; simpl_sizes; clear; lia]|].
    split; [exists j3; eapply rw_cells_transport; [exact FT3| exact MUs| exact WMs| apply DJ; right; right; left; simpl_sizes; clear; lia]|].
    split; [eapply rw_cells_transport; [exact FLP| exact MUs| exact WMs| apply DJ; right; right; left; simpl_sizes; clear; lia]|].
    split; [eapply rw_cells_transport; [exact SHF| exact MUs| exact WMs| apply DJ; do 3 right; left; unfold hshadow; simpl_sizes; clear; lia]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MUs| exact WMs| apply DJ; do 4 right; left; simpl_sizes; clear; lia]|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [apply fkeep_refl|].
    split; [| apply hpm_refl].
    exists stc. split; [| exact LIVE1].
    eapply (rfake_frame FI stc m m' _ RF MUs WMs). eapply Forall_impl; [| exact HW]. intros [x y] (LE & [O|[O|O]]); cbn [fst snd] in *.
    - left. clear - O B2 CLO S3. lia.
    - left. clear - O HA1 HA2 S1 S2. lia.
    - right; left. apply (Contracts.lb_sub _ _ _ _ _ LVF); clear - O; lia.
  Qed.

  #[using="Type"] Lemma newN1 : forall (q' id tcur tlz : Z) (m : mem)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    mem_inv asegs m ->
    evt asegs Q (ajcallstH 0x58630 0x8847c q' (wz 88) x11 x12 x5 x6 x7 x13 x14 x15 x16 x17 (wz tlz) x19 (wz (A + tcur)) (wz id) (wz 0) x26 x28 x29 x30 x31 m) ->
    evt asegs Q (newstH q' id tcur tlz x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' id tcur tlz m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 Q MI K1.
    unfold newstH. step. step. exact K1.
  Qed.

  #[using="Type"] Lemma newN3 : forall (q' H cur : Z) (ty tb tl va vl : word) (bs : list byte) (mb m : mem)
      x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty tb tl va vl bs mb m ->
    evt asegs Q (ajcallstH 0x8c15c 0x884dc q' (wz (H + 24)) va vl x5 x6 x7 x13 x14 x15 x16 x17 x18 (wz H) x21 x22 (wz (H + 24)) (wz (H + 56)) x28 x29 x30 x31 m) ->
    evt asegs Q (ajretstH 0x884c8 q' (wz 0) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 (wz H) x21 x22 (wz (H + 24)) (wz (H + 56)) x28 x29 x30 x31 m).
  Proof.
    intros q' H cur ty tb tl va vl bs mb m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 Q INV K1.
    pose proof INV as (_ & _ & _ & VAL & _ & _ & _ & MI & _).
    unfold ajretstH. step. lit_branch. step. step. zstep. step. exact K1.
  Qed.

  #[using="ws WSL"] Lemma newN5 : forall (q' r : Z) (m : mem)
      x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    mem_inv asegs m -> 0 < r < 2^64 ->
    evt asegs Q (nextstH q' (wz 0x8855c) x5 x6 x7 (wz r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 m) ->
    evt asegs Q (ajretstH 0x8855c q' (wz r) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Proof.
    intros q' r m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x26 x28 x29 x30 x31 Q MI RR K1.
    unfold ajretstH. step. if_cases K0; zify_cond K0; [| exfalso; lia]. exact K1.
  Qed.

  Definition hWN (q' H : Z) : list ivl := [(H, H + 88); (lo, q'); (F + 160, F + 176)]%Z.

  #[using="IC m0 HOK RF0 ws WSL"] Lemma newN2 : forall (q' H id tcur tlz cur l : Z) (ty tb tl va : word) (bs junk : list byte) (mb m : mem)
      x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty tb tl va (wz l) bs mb m -> 0 <= l < 2^63 ->
    rw_cells asegs m H [CB 88 junk] -> shw m H 88 -> 0x609000 <= H -> H + 88 <= alloc_ceiling -> H mod 8 = 0 -> hapx H 88 ->
    (forall m' (va' : word) (l' : Z) (j24 : list byte) y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       hinv q' cur ty tb tl va' (wz l') bs m' m' -> munch (hWN q' H) m m' -> wmono asegs m m' ->
       rw_cells asegs m' H [CB 24 j24] -> rw_cells asegs m' (H + 24) (mbuf_cells 0 0 0) -> rw_cells asegs m' (H + 56) (mbuf_cells 0 0 0) ->
       shw m' H 88 ->
       ((l <> 0 /\ va' = va /\ l' = l) \/ (l = 0 /\ va' = wz ZERO_ADDR_A /\ l' = 1)) ->
       evt asegs Q (ajcallstH 0x8c15c 0x884c8 q' (wz (H + 56)) (wz (A + tcur)) (wz tlz) y5 y6 y7 y13 y14 y15 y16 y17 (wz tlz) (wz H) (wz (A + tcur)) (wz id) (wz (H + 24)) (wz (H + 56)) y28 y29 y30 y31 m')) ->
    evt asegs Q (ajretstH 0x8847c q' (wz H) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 (wz tlz) x19 (wz (A + tcur)) (wz id) (wz 0) x26 x28 x29 x30 x31 m).
  Proof.
    intros q' H id tcur tlz cur l ty tb tl va bs junk mb m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 Q INV LR HCK SHH HLO HHI HAL HAPH KK.
    pose proof INV as (ST & _ & _ & VAL & _ & _ & _ & MI & AE & _ & _ & _ & _ & _ & _ & _ & (QB & QAL) & _).
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide PAL. hide AAL. hide QAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & _). pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof HAPH as (HA1 & HA2 & HA3). hide HA2. hide HA3.
    pose proof (munch_refl (hWN q' H) m) as MUw. pose proof (wmono_refl asegs m) as WMw. unfold hWN in MUw.
    splitcb HCK 0%nat [24; 32; 32]%nat. split_chunk HCK 1%nat HC0 HC1. split_chunk HC1 1%nat HCV HCN.
    change (Z.of_nat 24) with 24 in HCV. replace (H + 24 + Z.of_nat 32) with (H + 56) in HCN by lia.
    unfold ajretstH.
    step. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    zstep. zstep. zstep. step.
    eapply evt_cut.
    { eapply (membuffer_init_shw IC (H + 56) lo _ q');
        [ exact HCN | lia | lia | clear - HAL; Z.div_mod_to_equations; lia
        | apply (shw_sub _ H 88); [exact SHH| lia| lia| lia]
        | exact AE | exact ST | exact CLO | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; lia | unfold A0_RT_STACK; lia
        | exact MI | reflexivity ]. }
    intros ms' POST. unfold membuffer_init_post_S in POST.
    destruct POST as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1 & MI1 & HCN1 & ST1 & AE1).
    replace (ret_pc (Z_to_bv 64 558224)) with (Z_to_bv 64 558224) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (APP1 : app_ivs [(H + 56, H + 56 + 32); (lo, q')]%Z).
    { constructor; [unfold app_iv, SH_HI; cbn [fst snd]; unhide HA2; clear - HA2 HLO; lia|]. constructor; [apply app_iv_stack; lia| constructor]. }
    pose proof (shw_frame _ _ _ _ _ SHH MU1 APP1) as SHH1.
    assert (DJ1 : forall a n, (a + n <= H + 56 \/ H + 88 <= a) -> (q' <= a \/ a + n <= alloc_ceiling) -> disjoint_from [(H + 56, H + 56 + 32); (lo, q')]%Z a n)
      by (intros a n D1 D2; cbn [disjoint_from]; split; [clear - D1; lia| split; [clear - D2 CLO; lia| exact I]]).
    pose proof (rw_cells_transport asegs _ m m1 _ _ HC0 MU1 WM1 ltac:(apply DJ1; simpl_sizes; lia)) as HC01.
    pose proof (rw_cells_transport asegs _ m m1 _ _ HCV MU1 WM1 ltac:(apply DJ1; simpl_sizes; lia)) as HCV1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ VAL MU1 WM1 ltac:(apply DJ1; simpl_sizes; [clear - HA1 FLO FHI B1; lia| clear - FHI B2; lia])) as VAL1.
    assert (MUw1 : munch [(H, H + 88); (lo, q'); (F + 160, F + 176)]%Z m m1).
    { eapply munch_trans; [exact MUw|]. eapply munch_weaken; [| exact MU1]. unfold sub_fp. intros xo Ho. cbn [outside] in *. destruct Ho as (O1 & O2 & _). repeat split; try exact I; lia. }
    pose proof (wmono_trans asegs _ _ _ WMw WM1) as WMw1.
    clear MUw WMw MU1 WM1 HC0 HCV HCN VAL ST AE MI SHH APP1 DJ1.
    zstep. zstep. step.
    eapply evt_cut.
    { eapply (membuffer_init_shw IC (H + 24) lo _ q');
        [ exact HCV1 | lia | lia | clear - HAL; Z.div_mod_to_equations; lia
        | apply (shw_sub _ H 88); [exact SHH1| lia| lia| lia]
        | exact AE1 | exact ST1 | exact CLO | change (2^64) with 18446744073709551616; change (2^47) with 140737488355328 in *; lia | unfold A0_RT_STACK; lia
        | exact MI1 | reflexivity ]. }
    intros ms' POST. unfold membuffer_init_post_S in POST.
    destruct POST as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & -> & MU2 & WM2 & MI2 & HCV2 & ST2 & AE2).
    replace (ret_pc (Z_to_bv 64 558236)) with (Z_to_bv 64 558236) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (APP2 : app_ivs [(H + 24, H + 24 + 32); (lo, q')]%Z).
    { constructor; [unfold app_iv, SH_HI; cbn [fst snd]; unhide HA2; clear - HA2 HLO; lia|]. constructor; [apply app_iv_stack; lia| constructor]. }
    pose proof (shw_frame _ _ _ _ _ SHH1 MU2 APP2) as SHH2.
    assert (DJ2 : forall a n, (a + n <= H + 24 \/ H + 56 <= a) -> (q' <= a \/ a + n <= alloc_ceiling) -> disjoint_from [(H + 24, H + 24 + 32); (lo, q')]%Z a n)
      by (intros a n D1 D2; cbn [disjoint_from]; split; [clear - D1; lia| split; [clear - D2 CLO; lia| exact I]]).
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ HC01 MU2 WM2 ltac:(apply DJ2; simpl_sizes; lia)) as HC02.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ HCN1 MU2 WM2 ltac:(apply DJ2; unfold mbuf_cells; simpl_sizes; lia)) as HCN2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ VAL1 MU2 WM2 ltac:(apply DJ2; simpl_sizes; [clear - HA1 FLO FHI B1; lia| clear - FHI B2; lia])) as VAL2.
    assert (MUw2 : munch [(H, H + 88); (lo, q'); (F + 160, F + 176)]%Z m m2).
    { eapply munch_trans; [exact MUw1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp. intros xo Ho. cbn [outside] in *. destruct Ho as (O1 & O2 & _). repeat split; try exact I; lia. }
    pose proof (wmono_trans asegs _ _ _ WMw1 WM2) as WMw2.
    clear MUw1 WMw1 MU2 WM2 HC01 HCV1 HCN1 VAL1 ST1 AE1 MI1 SHH1 APP2 DJ2.
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in HCV2, HCN2.
    step. step. if_cases K1; zify_cond K1.
    -
      zstep. zstep. zstep. step.
      assert (HBW : Forall (hb_iv q' H) [(H, H + 88); (lo, q'); (F + 160, F + 176)]%Z).
      { constructor; [split; [cbn [fst snd]; lia| right; left; cbn [fst snd]; lia]|]. constructor; [split; [cbn [fst snd]; lia| left; cbn [fst snd]; lia]|].
        constructor; [split; [cbn [fst snd]; lia| right; right; cbn [fst snd]; lia]| constructor]. }
      eapply (KK m2 va l); [| exact MUw2| exact WMw2| exact HC02| exact HCV2| exact HCN2| exact SHH2| left; split; [lia| split; reflexivity]].
      eapply (hinv_stepHB 248 hscr _ H q' cur ty tb tl va (wz l) va (wz l) bs mb m m2 INV MUw2 WMw2 HBW HLO HHI HAPH ST2 VAL2 MI2).
      intros (j0 & w32 & j96 & j128 & SCR). exists j0, w32, j96, j128.
      eapply rw_cells_transport; [exact SCR| exact MUw2| exact WMw2|]. apply (hb_dj _ q' H _ _ HBW ltac:(lia) HLO HHI HAPH). left. lia.
    -
      assert (L0 : l = 0) by lia. subst l.
      pose proof (munch_refl [(F + 160, F + 176)]%Z m2) as MUv.
      step. zstep. sstep. zstep. sstep.
      zstep. zstep. zstep. step.
      assert (HBW : Forall (hb_iv q' H) [(H, H + 88); (lo, q'); (F + 160, F + 176)]%Z).
      { constructor; [split; [cbn [fst snd]; lia| right; left; cbn [fst snd]; lia]|]. constructor; [split; [cbn [fst snd]; lia| left; cbn [fst snd]; lia]|].
        constructor; [split; [cbn [fst snd]; lia| right; right; cbn [fst snd]; lia]| constructor]. }
      eapply (KK _ (wz ZERO_ADDR_A) 1); [| eassumption| eassumption| eassumption| eassumption| eassumption| | right; split; [reflexivity| split; reflexivity]].
      + eapply (hinv_stepHB 248 hscr _ H q' cur ty tb tl va (wz 0) (wz ZERO_ADDR_A) (wz 1) bs mb m _ INV); [eassumption| eassumption| exact HBW| exact HLO| exact HHI| exact HAPH| eassumption| eassumption| eassumption|].
        intros (j0 & w32 & j96 & j128 & SCR). exists j0, w32, j96, j128.
        eapply rw_cells_transport; [exact SCR| eassumption| eassumption|]. apply (hb_dj _ q' H _ _ HBW ltac:(lia) HLO HHI HAPH). left. lia.
      + eapply (shw_frame _ _ _ _ _ SHH2 MUv). constructor; [apply sub_app_iv_fsH; clear - FLO FHI B1; lia| constructor].
  Qed.

  #[using="m0 HOK RF0 ws WSL"] Lemma newN4 : forall (q' H id NA nlen ncap cur : Z) (ty tb tl va vl : word) (bs j24 : list byte) (mb m : mem)
      x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x28 x29 x30 x31 (Q : machine_state -> Prop),
    hinv q' cur ty tb tl va vl bs mb m ->
    rw_cells asegs m H [CB 24 j24] -> rw_cells asegs m (H + 56) (mbuf_cells NA nlen ncap) -> shw m H 88 ->
    0x609000 <= H -> H + 88 <= alloc_ceiling -> H mod 8 = 0 -> hapx H 88 -> - 2^31 <= id < 2^31 ->
    (forall m' (pad : word) y12,
       hinv q' cur ty tb tl va vl bs m' m' -> munch [(H, H + 24)]%Z m m' -> wmono asegs m m' ->
       rw_cells asegs m' H [C8 (wz NA); C8 (wz nlen); C4 (wz id); C4 pad] -> shw m' H 88 ->
       evt asegs Q (ajcallstH 0x8b500 0x8855c q' (wz L) (wz H) y12 x5 x6 x7 x13 x14 x15 x16 x17 x18 (wz H) x21 (wz id) (wz (H + 24)) (wz (H + 56)) x28 x29 x30 x31 m')) ->
    evt asegs Q (ajretstH 0x884dc q' (wz 0) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 (wz H) x21 (wz id) (wz (H + 24)) (wz (H + 56)) x28 x29 x30 x31 m).
  Proof.
    intros q' H id NA nlen ncap cur ty tb tl va vl bs j24 mb m x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x21 x28 x29 x30 x31 Q INV HC0 HCN SHH HLO HHI HAL HAPH IDR KK.
    pose proof INV as (ST & _ & _ & VAL & _ & _ & _ & MI & _ & _ & _ & _ & _ & _ & _ & _ & (QB & QAL) & _).
    pose proof HOK as HOK'. hokA HOK'. hide TFS. hide TBAND. hide AL16. hide PAL. hide AAL. hide QAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct hframe_facts as (FLO & FHI & _). pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof HAPH as (HA1 & HA2 & HA3). hide HA2. hide HA3.
    pose proof (munch_refl [(H, H + 24)]%Z m) as MUw. pose proof (wmono_refl asegs m) as WMw.
    splitcb HC0 0%nat [8; 8; 4; 4]%nat. recell HC0 0%nat. recell HC0 1%nat. recell HC0 2%nat. recell HC0 3%nat. name_junk HC0.
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in HCN.
    unfold ajretstH.
    walk_to 0x8b500%Z.
    assert (HBW : Forall (hb_iv q' H) [(H, H + 24)]%Z) by (constructor; [split; [cbn [fst snd]; lia| right; left; cbn [fst snd]; lia]| constructor]).
    eapply (KK m1); [| exact MUw| exact WMw| exact HC0|].
    - eapply (hinv_stepHB 248 hscr _ H q' cur ty tb tl va vl va vl bs mb m m1 INV MUw WMw HBW HLO HHI HAPH ST VAL MI).
      intros (j0 & w32 & j96 & j128 & SCR). exists j0, w32, j96, j128.
      eapply rw_cells_transport; [exact SCR| exact MUw| exact WMw|]. apply (hb_dj _ q' H _ _ HBW ltac:(lia) HLO HHI HAPH). left. lia.
    - eapply (shw_frame _ _ _ _ _ SHH MUw). constructor; [unfold app_iv, SH_HI; cbn [fst snd]; unhide HA2; clear - HA2 HLO; lia| constructor].
  Qed.
End PH.
End W.

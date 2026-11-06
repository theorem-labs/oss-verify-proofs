(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA LibIface L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9IcptLayout Pm9L5DefsA Pm9ArtIfaceLaws Pm9ArtIfaceInst Pm9ArtIfaceInstX Pm9ArtIfaceLayout Pm9DrvG Pm9DrvLibL Pm9DrvLibInit Pm9DrvMain Pm9MainPhaseA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import FrmInv Pm9FrmInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require SymDriveX.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmCurSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ASMCB.
Abbreviation IC := PMLA.C_cboth.
Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Definition LIB_STACK : Z := 16384.
Definition LayJ9 : lib_layoutA := {|
  lla_L := art_L;
  lla_entry := 0xaf544;
  lla_gp := 0x10800;
  lla_empty := 0x690360;
  lla_initc := [];
  lla_init_img := [(0x10000, 0x156000); (0x690351, 0x691cc0); (0x158c38, 0x158d28); (0x6b2058, 0x6b2088); (0x6b2100, 0x6b2104)];
  lla_td_self := 0x691cc8; lla_td_tid := 0x691ce8; lla_td_locale := 0x691d60; lla_locale := 0x6b2058; lla_td_canary := 0x691d80; lla_guard := 0x6b1dd0; lla_auxvp := 0x6b2028;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x156000;
  lla_stack := LIB_STACK;
  lla_frames := fun _ => PMSA.LIB_FRAMES;
  lla_leak := fun _ => 0;
  lla_credit := PMSA.pm_creditA art_L;
  lla_foot := PMLA.FOOT IC;
  lla_junk := [(0x691cec, 0x691cf0)];
  lla_atexit := 0x6b1de0; lla_hs0 := [(0x135340, 0x9eb04); (0x135340, 0xaf4cc)]; lla_need_locks := 0x6b2023;
  lla_init_cells := []
|}.

Definition LayC9 : lib_layoutA := {|
  lla_L := art_L;
  lla_entry := 0xaf544;
  lla_gp := 0x10800;
  lla_empty := 0x690360;
  lla_initc := [];
  lla_init_img := [(0x10000, 0x156000); (0x690351, 0x691cc0); (0x158c38, 0x158d28); (0x6b2058, 0x6b2088); (0x6b2100, 0x6b2104)];
  lla_td_self := 0x691cc8; lla_td_tid := 0x691ce8; lla_td_locale := 0x691d60; lla_locale := 0x6b2058; lla_td_canary := 0x691d80; lla_guard := 0x6b1dd0; lla_auxvp := 0x6b2028;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x156000;
  lla_stack := LIB_STACK;
  lla_frames := fun _ => PMCSA.LIB_FRAMES_C;
  lla_leak := fun _ => 0;
  lla_credit := PMCSA.pm_creditA_c art_L;
  lla_foot := PMLA.FOOT IC;
  lla_junk := [(0x691cec, 0x691cf0)];
  lla_atexit := 0x6b1de0; lla_hs0 := [(0x135340, 0x9eb04); (0x135340, 0xaf4cc)]; lla_need_locks := 0x6b2023;
  lla_init_cells := []
|}.

Definition LStC9 (ar : asan_run) : lib_statics := PMSA.pm_staticsA art_L IC.

Lemma art_lay : L5A.as0_layout art_L art_C.
Proof.
  constructor; try reflexivity.
  - cbn [art_C art_statics_cells asc_cells]. apply incl_appl. apply incl_refl.
  - intros a S. pose proof (art_L_static_img a S). lia.
  - exact art_L_ro_img.
  - intros a S. pose proof (art_L_static_img a S). lia.
  - cbn. lia.
Qed.
Lemma art_sm0 : hl_stack_malloc art_L 0 = 0x64e64.    Proof. reflexivity. Qed.
Lemma art_sm1 : hl_stack_malloc art_L 1 = 0x64fd8.    Proof. reflexivity. Qed.
Lemma art_sm2 : hl_stack_malloc art_L 2 = 0x65168.    Proof. reflexivity. Qed.
Lemma art_sm3 : hl_stack_malloc art_L 3 = 0x65304.    Proof. reflexivity. Qed.
Lemma art_sm4 : hl_stack_malloc art_L 4 = 0x654b0.    Proof. reflexivity. Qed.
Lemma art_sm5 : hl_stack_malloc art_L 5 = 0x6567c.    Proof. reflexivity. Qed.
Lemma art_sfree5 : hlx_stack_free art_LX 5 = 0x65888. Proof. reflexivity. Qed.
Lemma art_sfree_pat : hlx_sfree_pat art_LX = 0x103a8. Proof. reflexivity. Qed.
Lemma art_segs : hl_segs art_L = ASEGS.                Proof. reflexivity. Qed.
Lemma art_tp : hl_tp art_L = 0x691d90.                 Proof. reflexivity. Qed.

Lemma art_footc : forall a, PMLA.in_foot IC a -> ~ hl_rt_static art_L a.
Proof.
  intros a (iv & Hin & Hr) Hs. cbn [art_L hl_rt_static] in Hs. unfold art_static in Hs.
  cbn [PMLA.FOOT PMLA.C_cboth In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). exact Hin.
Qed.

Lemma art_fpm : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps ASEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom ASEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom ASEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Proof. intros fx fx' R pc M R' pc' M' H. exact (Pm9FrmInv.msteps_fp_ok fx fx' R _ M _ R' _ M' _ H). Qed.

Lemma rdn_img4 : forall (M : word -> option byte) (a : Z),
  0 <= a -> a + 4 <= 2 ^ 64 -> (forall i, a <= i < a + 4 -> M (Z_to_bv 64 i) = None) ->
  rdn ASEGS M (Z_to_bv 64 a) 4 = rdn ASEGS (fun _ => None) (Z_to_bv 64 a) 4.
Proof.
  intros M a Ha Hn H. apply SymDriveX.rdn_agree. intros j Hj. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. apply H. lia.
Qed.
Lemma locale_lock_img : forall M : word -> option byte,
  (forall a, PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 -> M (Z_to_bv 64 a) = None) -> cell_is (hl_segs art_L) M (PMLA.LOCALE_LOCK IC) 4 0.
Proof.
  intros M H. cbn [PMLA.LOCALE_LOCK PMLA.C_cboth] in *. unfold cell_is. rewrite art_segs.
  rewrite (rdn_img4 M 0x6b2100) by (first [lia | exact H]). vm_compute. reflexivity.
Qed.

Lemma LayJ9_pm : PMSA.pm_layout_okA art_L IC LayJ9.
Proof.
  unfold PMSA.pm_layout_okA. cbn [lla_L lla_stack lla_foot lla_junk lla_frames lla_leak lla_credit lla_rw_lo lla_atexit lla_hs0 lla_need_locks lla_init_img LayJ9].
  split; [reflexivity|].
  split. { apply Z.leb_le. vm_compute. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|]. split; [rewrite art_tp; reflexivity|].
  split; [intros k Hk; split; reflexivity|]. split; [intros n; reflexivity|].
  split; [cbn [PMLA.IMG_RO_HI PMLA.C_cboth]; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  -
    intros a Ha. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.NEED_LOCKS PMLA.C_cboth] in Ha. unfold PMLA.in_tab, ATEXIT_TAB_BYTES in Ha. cbn [PMLA.ATEXIT_TAB PMLA.C_cboth] in Ha.
    destruct Ha as [Ha|((iv & Hin & Hr) & Ht & Hn)].
    + exists (0x10000, 0x156000). split; [cbn; tauto | cbn [fst snd]; lia].
    + cbn [PMLA.FOOT PMLA.C_cboth In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr;
        first [ (exists (0x690351, 0x691cc0); split; [cbn; tauto | cbn [fst snd]; lia])
              | (exists (0x6b2100, 0x6b2104); split; [cbn; tauto | cbn [fst snd]; lia])
              | (exfalso; lia) ] |]).
      destruct Hin.
  - exact locale_lock_img.
Qed.
Lemma LayC9_pm : PMCSA.pm_layout_okA_c art_L IC LayC9.
Proof.
  unfold PMCSA.pm_layout_okA_c. cbn [lla_L lla_stack lla_foot lla_junk lla_frames lla_leak lla_credit lla_rw_lo lla_atexit lla_hs0 lla_need_locks lla_init_img LayC9].
  split; [reflexivity|].
  split. { apply Z.leb_le. vm_compute. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|]. split; [rewrite art_tp; reflexivity|].
  split; [intros k Hk; split; reflexivity|]. split; [intros n; reflexivity|].
  split; [cbn [PMLA.IMG_RO_HI PMLA.C_cboth]; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  -
    intros a Ha. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.NEED_LOCKS PMLA.C_cboth] in Ha. unfold PMLA.in_tab, ATEXIT_TAB_BYTES in Ha. cbn [PMLA.ATEXIT_TAB PMLA.C_cboth] in Ha.
    destruct Ha as [Ha|((iv & Hin & Hr) & Ht & Hn)].
    + exists (0x10000, 0x156000). split; [cbn; tauto | cbn [fst snd]; lia].
    + cbn [PMLA.FOOT PMLA.C_cboth In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr;
        first [ (exists (0x690351, 0x691cc0); split; [cbn; tauto | cbn [fst snd]; lia])
              | (exists (0x6b2100, 0x6b2104); split; [cbn; tauto | cbn [fst snd]; lia])
              | (exfalso; lia) ] |]).
      destruct Hin.
  - exact locale_lock_img.
Qed.

Lemma la1 : drv_lib_layoutA LayC9 art_L.
Proof.
  constructor; try reflexivity.
  - cbn [lla_stack LayC9]. unfold LIB_STACK. split; [lia | reflexivity].
  - intros iv Hin. cbn [lla_foot LayC9 PMLA.FOOT PMLA.C_cboth In] in Hin. unfold LIB_HOLES.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd];
      first [ (exists 0x690380, 0x690390; split; [cbn [In]; tauto | lia])
            | (exists 0x6905c0, 0x691488; split; [cbn [In]; tauto | lia])
            | (exists 0x6b1de0, 0x6b2000; split; [cbn [In]; tauto | lia])
            | (exists 0x6b2023, 0x6b2024; split; [cbn [In]; tauto | lia])
            | (exists 0x6b2100, 0x6b2104; split; [cbn [In]; tauto | lia]) ] |]).
    destruct Hin.
  - intros iv Hin. cbn [lla_junk LayC9 In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd]. unfold LIB_HOLES. exists 0x691cec, 0x691cf0. split; [cbn [In]; tauto | lia].
  - intros n Hn. cbn [lla_credit LayC9]. unfold PMCSA.pm_creditA_c. cbn [fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead]. lia.
  - intros k Hk. cbn [lla_leak lla_frames LayC9]. unfold PMCSA.LIB_FRAMES_C.
    cbn [In PM_FS_CLASSES] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; repeat split; discriminate.
Qed.

Lemma la2 : drv_lib_cellsA LayC9.
Proof.
  constructor; try reflexivity.
  - intros iv Hin. cbn [lla_init_img LayC9 In] in Hin. unfold LIBINIT_IMG.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd];
      first [ (exists 65536, 1400832; split; [cbn [In]; tauto | lia]) | (exists 6882129, 6888640; split; [cbn [In]; tauto | lia])
            | (exists 1412152, 1412392; split; [cbn [In]; tauto | lia]) | (exists 7020632, 7020680; split; [cbn [In]; tauto | lia])
            | (exists 7020800, 7020804; split; [cbn [In]; tauto | lia]) ] |]).
    destruct Hin.
  - cbn [lla_rw_lo LayC9]. lia.
  - intros iv Hin. cbn [lla_initc LayC9 In] in Hin. destruct Hin.
  - intros iv Hin. cbn [lla_initc LayC9 In] in Hin. destruct Hin.
Qed.

Lemma la3 : drv_budgetA art_L LayC9.
Proof.
  intros n Hn. unfold credA, CAPk, adebit. cbn [fst snd lla_credit LayC9 art_L hl_k_per_malloc hl_b_lin hl_b_overhead]. unfold PMCSA.pm_creditA_c.
  cbn [fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead]. lia.
Qed.

Section LibOk.
Variable scfg : SpuriousCfg.
#[local] Instance scfgP : ScfgP := MkScfgP scfg.
Variable IL : icpt_layout.
Variable ILX : icpt_layout_x.
Hypothesis ILok : as0_icpt_layout IL.
Hypothesis ILXok : pm_icpt_layout_x ILX.

Hypothesis LIBTOP : forall (ar : asan_run) (HI : asan_iface),
  as0_icpt_layout IL -> pm_icpt_layout_x ILX ->
  pm_asan_iface_ok art_L art_LX ar art_C scfg HI ->
  pm_aicpt_ok art_L ar IL ILX scfg HI (aannotate_spec art_L ar scfg HI (iclx_annotate ILX) 4096) ->
  afree_null_spec art_L ar scfg HI ->
  PMCSA.lib_specA_c art_L ar HI IC LayC9.

Theorem la4 : lib_ok_stmt scfg art_L art_LX art_C IL ILX LayC9 LStC9.
Proof.
  intros ar HI HIok ICok FN. split; [reflexivity|].
  exists (PMLA.ls_atexit IC). split.
  - constructor.
    + exact (LIBTOP ar HI ILok ILXok HIok ICok FN LayC9_pm).
    + exact (PMTA.lib_init_okA art_L ar IC LayJ9 PMTA.C_cboth_wf LayJ9_pm).
    + exact (PMTA.lib_frame_okA art_L ar IC LayJ9 PMTA.C_cboth_wf LayJ9_pm).
    + exact (PMCSA.lib_exit_okA_c art_L IC LayC9 LayC9_pm).
  - intros g. unfold LS2_HANDLERS, LS2C_HANDLERS, LS2JC_HANDLERS, LS2CJ_HANDLERS.
    destruct (PMTA.ls_atexit_cases IC g) as [E|[E|[E|[E|E]]]]; rewrite E;
      [left | right; left | right; right; left | right; right; right; left | right; right; right; right]; reflexivity.
Qed.
End LibOk.
End ASMCB.


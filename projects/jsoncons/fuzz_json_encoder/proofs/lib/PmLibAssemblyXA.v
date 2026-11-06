(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA LibIface L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecsXA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import L5Core HeapIfaceN Pm4ArtIfaceInstN PmLibIfaceAW Pm4DrvLibLW Pm4MainPhaseAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require PmXasanFinalW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4IcptLayout Pm4L5DefsA Pm4ArtIfaceLaws Pm4ArtIfaceInst Pm4ArtIfaceInstX Pm4ArtIfaceLayout Pm4DrvG Pm4DrvLibL Pm4DrvLibInit Pm4DrvMain Pm4MainPhaseA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import FrmInv Pm4FrmInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require SymDriveX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopSpecsXA HnKitXA PmTopSpecsXA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ASMXA.
Abbreviation IC := PMLA.C_xasan.
Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIB_STACK : Z := 18432.                 (* [comment removed for export] *)
Definition CLX : Z := 2 ^ 32 + 31.                  (* [comment removed for export] *)
Definition VISX : Z := 16384.                       (* [comment removed for export] *)
Definition BENCX : PMES.eghost -> Z := PMESA.benc art_L CLX.
Definition LayXA : lib_layoutA := {|
  lla_L := art_L;
  lla_entry := 0xb0550;                                            (* [comment removed for export] *)
  lla_gp := 0x10800;
  lla_empty := 0x69c560;                                           (* [comment removed for export] *)
  lla_initc := [];                                                 (* [comment removed for export] *)
  lla_init_img := [(0x10000, 0x162000); (0x69c551, 0x69df00); (0x165360, 0x165448); (0x6be298, 0x6be2c8); (0x6be340, 0x6be344)];   (* [comment removed for export] *)
  lla_td_self := 0x69df08; lla_td_tid := 0x69df28; lla_td_locale := 0x69dfa0; lla_locale := 0x6be298; lla_td_canary := 0x69dfc0; lla_guard := 0x6be010; lla_auxvp := 0x6be268;
  lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
  lla_rw_lo := 0x162000;
  lla_stack := LIB_STACK;
  lla_frames := fun _ => TPSXA.LIB_FRAMESXA;
  lla_leak := fun _ => 0;
  lla_credit := TPSXA.pm_creditxA art_L BENCX;
  lla_foot := PMLA.FOOTX IC;
  lla_junk := [(0x69df2c, 0x69df30)];                              (* [comment removed for export] *)
  lla_atexit := 0x6be020; lla_hs0 := [(0x1419c0, 0x9fb10); (0x1419c0, 0xb04d8)]; lla_need_locks := 0x6be263;      (* [comment removed for export] *)
  lla_init_cells := []                                              (* [comment removed for export] *)
|}.
(* [comment removed for export] *)
Definition LStXA (ar : asan_run) : lib_statics := TPSXA.pm_staticsxA art_L IC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma art_lay : L5A.as0_layout art_L art_C.
Proof.
  constructor; try reflexivity.
  - cbn [art_C art_statics_cells asc_cells]. apply incl_appl. apply incl_refl.
  - intros a S. pose proof (art_L_static_img a S). lia.
  - exact art_L_ro_img.
  - intros a S. pose proof (art_L_static_img a S). lia.
  - cbn. lia.
Qed.
Lemma art_sm0 : hl_stack_malloc art_L 0 = 0x65e70.    Proof. reflexivity. Qed.
Lemma art_sm1 : hl_stack_malloc art_L 1 = 0x65fe4.    Proof. reflexivity. Qed.
Lemma art_sm2 : hl_stack_malloc art_L 2 = 0x66174.    Proof. reflexivity. Qed.
Lemma art_sm3 : hl_stack_malloc art_L 3 = 0x66310.    Proof. reflexivity. Qed.
Lemma art_sm4 : hl_stack_malloc art_L 4 = 0x664bc.    Proof. reflexivity. Qed.
Lemma art_sm5 : hl_stack_malloc art_L 5 = 0x66688.    Proof. reflexivity. Qed.
Lemma art_sfree5 : hlx_stack_free art_LX 5 = 0x66894. Proof. reflexivity. Qed.
Lemma art_sfree_pat : hlx_sfree_pat art_LX = 0x10398. Proof. reflexivity. Qed.
Lemma art_segs : hl_segs art_L = ASEGS.                Proof. reflexivity. Qed.
Lemma art_tp : hl_tp art_L = 0x69dfd0.                 Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma art_footc : forall a, PMLA.in_foot IC a -> ~ hl_rt_static art_L a.
Proof.
  intros a (iv & Hin & Hr) Hs. cbn [art_L hl_rt_static] in Hs. unfold art_static in Hs.
  cbn [PMLA.FOOT PMLA.C_xasan In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). exact Hin.
Qed.
Lemma art_footc2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static art_L a /\ ~ hl_rt_ro art_L a.
Proof.
  intros a (iv & Hin & Hr). cbn [art_L hl_rt_static hl_rt_ro]. unfold art_static, art_ro.
  cbn [PMLA.FOOT PMLA.C_xasan In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Lemma footx_cases : forall a, PMLA.in_footx IC a -> PMLA.in_foot IC a \/ PMLA.LIT_LO IC <= a < PMLA.LIT_HI IC.
Proof.
  intros a (iv & Hin & Hr). unfold PMLA.FOOTX in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - left. exists iv. split; assumption.
  - right. cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd] in Hr. exact Hr.
Qed.
Lemma art_footxc : forall a, PMLA.in_footx IC a -> ~ hl_rt_static art_L a.
Proof.
  intros a Ha. destruct (footx_cases a Ha) as [Hf|Hl]; [exact (art_footc a Hf)|].
  intros Hs. cbn [art_L hl_rt_static] in Hs. unfold art_static in Hs. unfold PMLA.LIT_LO, PMLA.LIT_HI in Hl; cbn [PMLA.LIT_NULL_S PMLA.LIT_FALSE_G PMLA.C_xasan] in Hl. lia.
Qed.
Lemma art_footxc2 : forall a, PMLA.in_footx IC a -> ~ hl_rt_static art_L a /\ ~ hl_rt_ro art_L a.
Proof.
  intros a Ha. destruct (footx_cases a Ha) as [Hf|Hl]; [exact (art_footc2 a Hf)|].
  cbn [art_L hl_rt_static hl_rt_ro]. unfold art_static, art_ro. unfold PMLA.LIT_LO, PMLA.LIT_HI in Hl; cbn [PMLA.LIT_NULL_S PMLA.LIT_FALSE_G PMLA.C_xasan] in Hl. lia.
Qed.
(* [comment removed for export] *)
Lemma art_fpm : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps ASEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom ASEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom ASEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Proof. intros fx fx' R pc M R' pc' M' H. exact (Pm4FrmInv.msteps_fp_ok fx fx' R _ M _ R' _ M' _ H). Qed.

(* [comment removed for export] *)
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
  intros M H. cbn [PMLA.LOCALE_LOCK PMLA.C_xasan] in *. unfold cell_is. rewrite art_segs.
  rewrite (rdn_img4 M 0x6be340) by (first [lia | exact H]). vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma LayXA_pm : TPSXA.pm_layout_okxA art_L IC VISX BENCX LayXA.
Proof.
  unfold TPSXA.pm_layout_okxA. cbn [lla_L lla_stack lla_foot lla_junk lla_frames lla_leak lla_credit lla_rw_lo lla_atexit lla_hs0 lla_need_locks lla_init_img LayXA].
  split; [reflexivity|].
  split. { apply Z.leb_le. vm_compute. reflexivity. }     (* [comment removed for export] *)
  split; [reflexivity|]. split; [reflexivity|]. split; [rewrite art_tp; reflexivity|].
  split; [intros k Hk; split; reflexivity|]. split; [intros n; reflexivity|].
  split; [cbn [PMLA.IMG_RO_HI PMLA.C_xasan]; lia|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  - (* [comment removed for export] *)
    intros a Ha. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.NEED_LOCKS PMLA.C_xasan] in Ha. unfold PMLA.in_tab, ATEXIT_TAB_BYTES in Ha. cbn [PMLA.ATEXIT_TAB PMLA.C_xasan] in Ha.
    destruct Ha as [Ha|(Hfx & Ht & Hn)].
    + exists (0x10000, 0x162000). split; [cbn; tauto | cbn [fst snd]; lia].
    + destruct (footx_cases a Hfx) as [(iv & Hin & Hr)|Hl];
        [| exists (0x69c551, 0x69df00); split; [cbn; tauto | unfold PMLA.LIT_LO, PMLA.LIT_HI in Hl; cbn [PMLA.LIT_NULL_S PMLA.LIT_FALSE_G PMLA.C_xasan] in Hl; cbn [fst snd]; lia]].
      cbn [PMLA.FOOT PMLA.C_xasan In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr;
        first [ (exists (0x69c551, 0x69df00); split; [cbn; tauto | cbn [fst snd]; lia])
              | (exists (0x6be340, 0x6be344); split; [cbn; tauto | cbn [fst snd]; lia])
              | (exfalso; lia) ] |]).
      destruct Hin.
  - exact locale_lock_img.
Qed.

(* [comment removed for export] *)
Lemma u8_agree : forall (M M' : PMSA.mem) a v, 0 <= a -> a + 1 <= 2 ^ 64 -> L5C.agree_on M M' a 1 -> PMLA.u8 ASEGS M a v -> PMLA.u8 ASEGS M' a v.
Proof. intros M M' a v H0 H1 HA Hc. unfold PMLA.u8, L5.u8_at in *. rewrite (L5C.rdn_agree ASEGS M M' 1%nat a H0 ltac:(cbn; lia)); [exact Hc|]. intros i Hi. apply HA. cbn in Hi. lia. Qed.
Lemma u64_agree : forall (M M' : PMSA.mem) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> L5C.agree_on M M' a 8 -> PMLA.u64 ASEGS M a v -> PMLA.u64 ASEGS M' a v.
Proof. intros M M' a v H0 H1 HA Hc. unfold PMLA.u64, L5.u64_at in *. rewrite (L5C.rdn_agree ASEGS M M' 8%nat a H0 ltac:(cbn; lia)); [exact Hc|]. intros i Hi. apply HA. cbn in Hi. lia. Qed.
Lemma lit_ok_agree : forall (M M' : PMSA.mem) S G txt len,
  PMLA.LIT_LO IC <= S -> S + 16 <= PMLA.LIT_HI IC -> PMLA.LIT_LO IC <= G -> G + 2 <= PMLA.LIT_HI IC ->
  (forall i, PMLA.LIT_LO IC <= i < PMLA.LIT_HI IC -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  PMLA.lit_ok ASEGS M S G txt len -> PMLA.lit_ok ASEGS M' S G txt len.
Proof.
  intros M M' S G txt len HS1 HS2 HG1 HG2 HA HL. unfold PMLA.LIT_LO, PMLA.LIT_HI in *. cbn [PMLA.LIT_NULL_S PMLA.LIT_FALSE_G PMLA.C_xasan] in *.
  assert (A8 : forall a, 6931848 <= a -> a + 8 <= 6931920 -> L5C.agree_on M M' a 8) by (intros a X Y i Hi; apply HA; lia).
  assert (A1 : forall a, 6931848 <= a -> a + 1 <= 6931920 -> L5C.agree_on M M' a 1) by (intros a X Y i Hi; apply HA; lia).
  unfold PMLA.lit_ok in *. destruct HL as [(X1 & X2 & X3 & X4)|(X1 & X2 & X3 & X4)]; [left|right]; repeat split;
    first [ apply (u8_agree M M'); [lia|lia|apply A1; lia|assumption] | apply (u64_agree M M'); [lia|lia|apply A8; lia|assumption] ].
Qed.
Lemma lits_ok_agree : forall (M M' : PMSA.mem), (forall i, PMLA.LIT_LO IC <= i < PMLA.LIT_HI IC -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  PMLA.lits_ok ASEGS IC M -> PMLA.lits_ok ASEGS IC M'.
Proof.
  intros M M' HA (L1 & L2 & L3). unfold PMLA.lits_ok.
  split; [| split]; (eapply lit_ok_agree; [| | | | exact HA | eassumption]);
    unfold PMLA.LIT_LO, PMLA.LIT_HI; cbn [PMLA.LIT_NULL_S PMLA.LIT_NULL_G PMLA.LIT_TRUE_S PMLA.LIT_TRUE_G PMLA.LIT_FALSE_S PMLA.LIT_FALSE_G PMLA.C_xasan]; lia.
Qed.

Lemma lib_frame_okxA : forall ar, PmLibIfaceA.lib_statics_frameA LayXA ar (TPSXA.pm_staticsxA art_L IC).
Proof.
  intros ar. unfold lib_statics_frameA, lib_statics_frame. intros g M M' Hok Hfoot Hro _.
  cbn [LibIface.ls_ok TPSXA.pm_staticsxA] in *. destruct Hok as [Hok Hl].
  assert (FEQ : forall a, 0 <= a < 2 ^ 64 -> PMLA.in_foot IC a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha (iv & Hin & Hr). apply Hfoot; [exact Ha|]. unfold LibIface.in_foot. cbn [ll_foot lib_view lla_foot LayXA]. exists iv. split; [| exact Hr].
    unfold PMLA.FOOTX. apply in_or_app. left. exact Hin. }
  assert (LEQ : forall i, PMLA.LIT_LO IC <= i < PMLA.LIT_HI IC -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply Hfoot.
    - unfold PMLA.LIT_LO, PMLA.LIT_HI in Hi. cbn [PMLA.LIT_NULL_S PMLA.LIT_FALSE_G PMLA.C_xasan] in Hi. lia.
    - unfold LibIface.in_foot. cbn [ll_foot lib_view lla_foot LayXA]. exists (PMLA.LIT_LO IC, PMLA.LIT_HI IC). split; [| cbn [fst snd]; exact Hi].
      unfold PMLA.FOOTX. apply in_or_app. right. left. reflexivity. }
  split.
  - rewrite art_segs in Hok |- *. apply (PMTA.ls_ok_frame ASEGS IC PMTA.C_xasan_wf M M' FEQ); [| exact Hok].
    intros i Hi Hn. apply Hro; [| exact Hn]. pose proof (PMTA.cw_ro IC PMTA.C_xasan_wf) as (R0 & R1). rewrite PMTA.u64_of_Z by lia. cbn [ll_rw_lo lib_view lla_rw_lo LayXA].
    cbn [PMLA.IMG_RO_HI PMLA.C_xasan] in Hi. lia.
  - rewrite art_segs in Hl |- *. destruct g.
    + intros a Ha. rewrite (LEQ a Ha). exact (Hl a Ha).
    + exact (lits_ok_agree M M' LEQ Hl).
    + exact (lits_ok_agree M M' LEQ Hl).
Qed.

Lemma lib_init_okxA : forall ar, PmLibIfaceA.lib_statics_initA LayXA ar (TPSXA.pm_staticsxA art_L IC).
Proof.
  intros ar. pose proof LayXA_pm as (HL & _ & _ & _ & _ & _ & _ & _ & HA & HH & HN & COV & LLZ).
  unfold lib_statics_initA. intros av uid rnd tid canary hw M F TAB NL.
  destruct F as (IMG & _). cbn [ll_init_img lib_view] in IMG.
  cbn [LibIface.ls_ok LibIface.ls_g0 TPSXA.pm_staticsxA]. unfold PMLA.ls_okx, PMLA.ls_ok. rewrite HL, HA, HH in TAB. rewrite HL, HN in NL.
  split; [split; [| split; [split; [| split] |]] |].
  - intros i Hi. destruct (COV i (or_introl Hi)) as (iv & Hin & Hr). exact (IMG iv i Hin Hr).
  - cbn [PMLA.ls_atexit]. rewrite app_nil_r. exact TAB.
  - exact NL.
  - apply LLZ. intros a Ha. pose proof (PMTA.cw_ll IC PMTA.C_xasan_wf) as (L0 & L1 & LF). pose proof (PMTA.cw_ll_off IC PMTA.C_xasan_wf) as (T1 & T2 & NLo).
    assert (NT : ~ PMLA.in_tab IC a) by (unfold PMLA.in_tab, ATEXIT_TAB_BYTES in *; lia).
    assert (NN : a <> PMLA.NEED_LOCKS IC) by (clear - Ha NLo; lia).
    assert (FX : PMLA.in_footx IC a). { destruct (LF a Ha) as (iv & Hin & Hr). exists iv. split; [unfold PMLA.FOOTX; apply in_or_app; left; exact Hin | exact Hr]. }
    destruct (COV a (or_intror (conj FX (conj NT NN)))) as (iv & Hin & Hr). exact (IMG iv a Hin Hr).
  - intros a Hf Ht Hn. assert (FX : PMLA.in_footx IC a). { destruct Hf as (iv & Hin & Hr). exists iv. split; [unfold PMLA.FOOTX; apply in_or_app; left; exact Hin | exact Hr]. }
    destruct (COV a (or_intror (conj FX (conj Ht Hn)))) as (iv & Hin & Hr). exact (IMG iv a Hin Hr).
  - (* [comment removed for export] *)
    intros a Ha. apply (IMG (0x69c551, 0x69df00)); [cbn; tauto|]. unfold PMLA.LIT_LO, PMLA.LIT_HI in Ha. cbn [PMLA.LIT_NULL_S PMLA.LIT_FALSE_G PMLA.C_xasan] in Ha. cbn [fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma kenc0_eq : PMXA.kenc art_L PMES.g0 = 432.  Proof. vm_compute. reflexivity. Qed.
Lemma benc0_eq : BENCX PMES.g0 = 51653050650.  Proof. vm_compute. reflexivity. Qed.   (* [comment removed for export] *)

Lemma la1 : drv_lib_layoutA LayXA art_L.
Proof.
  constructor; try reflexivity.
  - cbn [lla_stack LayXA]. unfold LIB_STACK. split; [lia | reflexivity].
  - intros iv Hin. cbn [lla_foot LayXA] in Hin. unfold PMLA.FOOTX in Hin. unfold PMLA.LIT_LO, PMLA.LIT_HI in Hin. cbn [PMLA.FOOT PMLA.LIT_NULL_S PMLA.LIT_FALSE_G PMLA.C_xasan In app] in Hin. unfold LIB_HOLES.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd];
      first [ (exists 0x69c580, 0x69c5d0; split; [cbn [In]; tauto | lia])
            | (exists 0x69c800, 0x69d6c8; split; [cbn [In]; tauto | lia])
            | (exists 0x6be020, 0x6be240; split; [cbn [In]; tauto | lia])
            | (exists 0x6be263, 0x6be264; split; [cbn [In]; tauto | lia])
            | (exists 0x6be340, 0x6be344; split; [cbn [In]; tauto | lia]) ] |]).
    destruct Hin.
  - intros iv Hin. cbn [lla_junk LayXA In] in Hin. destruct Hin as [<-|[]]. cbn [fst snd]. unfold LIB_HOLES. exists 0x69df2c, 0x69df30. split; [cbn [In]; tauto | lia].
  - intros n Hn. cbn [lla_credit LayXA]. unfold TPSXA.pm_creditxA. rewrite kenc0_eq, benc0_eq. cbn [fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead]. lia.
  - intros k Hk. cbn [lla_leak lla_frames LayXA]. unfold TPSXA.LIB_FRAMESXA.
    cbn [In PM_FS_CLASSES] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; vm_compute; repeat split; discriminate.
Qed.

Lemma la2 : drv_lib_cellsA LayXA.
Proof.
  constructor; try reflexivity.
  - intros iv Hin. cbn [lla_init_img LayXA In] in Hin. unfold LIBINIT_IMG.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd];
      first [ (exists 65536, 1449984; split; [cbn [In]; tauto | lia]) | (exists 6931793, 6938368; split; [cbn [In]; tauto | lia])
            | (exists 1463136, 1463368; split; [cbn [In]; tauto | lia]) | (exists 7070360, 7070408; split; [cbn [In]; tauto | lia])
            | (exists 7070528, 7070532; split; [cbn [In]; tauto | lia]) ] |]).
    destruct Hin.
  - cbn [lla_rw_lo LayXA]. lia.
  - intros iv Hin. cbn [lla_initc LayXA In] in Hin. destruct Hin.
  - intros iv Hin. cbn [lla_initc LayXA In] in Hin. destruct Hin.      (* [comment removed for export] *)
Qed.

Lemma la3 : drv_budgetA art_L LayXA PmXasanFinalW.BUDGET0.
Proof.
  intros n Hn. unfold credA, CAPk, adebit. cbn [fst snd lla_credit LayXA art_L hl_k_per_malloc hl_b_lin hl_b_overhead]. unfold TPSXA.pm_creditxA.
  rewrite kenc0_eq, benc0_eq. cbn [fst snd art_L hl_k_per_malloc hl_b_lin hl_b_overhead]. unfold PmXasanFinalW.BUDGET0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LibOk.
Variable scfg : SpuriousCfg.
#[local] Instance scfgP : ScfgP := MkScfgP scfg.
Variable IL : icpt_layout.
Variable ILX : icpt_layout_x.
Hypothesis ILok : as0_icpt_layout IL.              (* [comment removed for export] *)
Hypothesis ILXok : pm_icpt_layout_x ILX.           (* [comment removed for export] *)

(* [comment removed for export] *)
Variable PHI : list byte -> Prop.
(* [comment removed for export] *)
Definition lib_specxAW_exp (ar : asan_run) (HI : asan_iface) (Lay : lib_layoutA) : Prop :=
  TPSXA.pm_layout_okxA art_L IC VISX BENCX Lay -> PmLibIfaceAW.lib_call_okAW Lay ar scfg HI (TPSXA.pm_staticsxA art_L IC) PHI.
Hypothesis LIBTOPW : forall (ar : asan_run) (HI : asan_iface),
  as0_icpt_layout IL -> pm_icpt_layout_x ILX ->                    (* [comment removed for export] *)
  pm_asan_iface_ok art_L art_LX ar art_C scfg HI ->
  pm_aicpt_ok art_L ar IL ILX scfg HI (aannotate_spec art_L ar scfg HI (iclx_annotate ILX) 4096) ->
  afree_null_spec art_L ar scfg HI ->
  Pm4ArtIfaceInstN.pm_instN art_L ar IL scfg HI ->      (* [comment removed for export] *)
  lib_specxAW_exp ar HI LayXA.

Theorem la4w : lib_ok_stmtW scfg art_L art_LX art_C IL ILX LayXA LStXA PHI.
Proof.
  intros ar HI HIok ICok FN INok. split; [reflexivity|].
  exists (PMLA.ls_atexit IC). split.
  - constructor.
    + exact (LIBTOPW ar HI ILok ILXok HIok ICok FN INok LayXA_pm).
    + exact (lib_init_okxA ar).
    + exact (lib_frame_okxA ar).
    + exact (TPSXA.lib_exit_okxA art_L IC VISX BENCX LayXA LayXA_pm).
  - intros g. unfold LS2_HANDLERS. destruct (PMTA.ls_atexit_cases IC g) as [E|E]; rewrite E; [left; reflexivity | right; reflexivity].
Qed.
End LibOk.
End ASMXA.


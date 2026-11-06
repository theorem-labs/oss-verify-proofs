(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA LibIface PmLibIfaceA PmLibIfaceAW DrvKitA DrvNodesLazyK As0DrvKitA Pm5DrvEntry Pm5Drv_defs Pm5DrvLib.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5DrvLibL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition lib_iface_okDW (Lay : lib_layoutA) (ar : asan_run) (scfg : SpuriousCfg) (HI : asan_iface) (LSt : lib_statics) (PHI : list byte -> Prop) : Prop :=
  exists LSA : ls_state LSt -> list (Z * Z), lib_iface_okAW Lay ar scfg HI LSt PHI LSA /\ (forall g, LSA g = [] \/ LSA g = LS2_HANDLERS).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section LibSiteW.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_ok L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  Variable Lay : lib_layoutA.
  Variable LSt : lib_statics.
  Hypothesis DLL : drv_lib_layoutA Lay L.
  Variable PHI : list byte -> Prop.
  Hypothesis LIokW : lib_call_okAW Lay ar scfg HI LSt PHI.

  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation LV := (lib_view Lay ar).

  Lemma alib_sitew : forall vals ebs sr kn R M (model : Model) LB LK cr A g so stk bls vbnd (ptr ra : Z) (payload : list byte) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true ->
    (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 21 <= so <= 0 -> so mod 16 = 0 -> lla_stack Lay <= stk <= 2 ^ 21 ->
    getr R 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 47 -> ra mod 2 = 0 ->
    getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x6a1890 ->
    getr R 10 = Z_to_bv 64 ptr -> getr R 11 = Z_to_bv 64 (Z.of_nat (length payload)) -> Z.of_nat (length payload) < 2 ^ 26 ->
    ((length payload = 0%nat /\ ptr = lla_empty Lay) \/ (0 < Z.of_nat (length payload) /\ In (ptr, Z.of_nat (length payload)) LB)) ->
    rdn ASEGS M (Z_to_bv 64 ptr) (length payload) = Some payload ->
    credit_le (lla_credit Lay (Z.of_nat (length payload))) cr ->
    (forall k, In k PM_FS_CLASSES -> Z.of_nat (ff_count k LK) + lla_frames Lay k <= ff_cap k) ->
    ls_ok LSt g M ->
    dinvA LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    fp_ok fx ->                                   (* [comment removed for export] *)
    PHI payload ->                                (* [comment removed for export] *)
    K [] ->
    (forall (fx' : PropExec.FPState) R' M' (model' : Model) g' cr' LK' A',
       fp_ok fx' ->                               (* [comment removed for export] *)
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_upd (sr_after_call_j sr (map ridx c_kept) (length vals)) (ridx 10) (ELit 0)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (keep_libA so stk bls vbnd kn) ->
       dinvA LB LK' cr' A' M' model' -> model_rt model model' -> incl A A' ->
       (forall k, In k PM_FS_CLASSES -> Z.of_nat (ff_count k LK') <= Z.of_nat (ff_count k LK) + lla_leak Lay k) ->
       ls_ok LSt g' M' ->
       credit_le (credit_sub cr (lla_credit Lay (Z.of_nat (length payload)))) cr' ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_LIB_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xb0e20) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A g so stk bls vbnd ptr ra payload K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal Hstk R1 Hra Hra2 R3 R4 R10 R11 Hlen Hptr Hpay Hcr Hroom Hls DI Hbl Hvb HFP HPHI HK0 CONT.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined scfg L ar C HI HIok sp0 Hsp M0 M0_def _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'. destruct (dlla_stack Lay L DLL) as ((ST1 & ST2) & ST3).
    set (sp := bv_unsigned sp0 + so) in *.
    assert (WDEF : forall a, bv_unsigned sp0 - 8388608 <= a < bv_unsigned sp0 -> M (Z_to_bv 64 a) <> None)
      by (exact (window_defined sp0 Hsp vals ebs (ahid A model) M kn HK Hiw P0)).
    destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & (B4096 & TOPEQ & _ & _) & TOP47 & _).
    pose proof (LIokW fx g LB [] LK cr A sp ptr ra payload R M model K) as MS.
    unfold lib_cfgA in MS. rewrite (dlla_L Lay L DLL), (dla_segs L ar IL sp0 DL), (dlla_entry Lay L DLL) in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *)
      constructor; rewrite ?(dlla_L Lay L DLL), ?(dla_segs L ar IL sp0 DL), ?(dla_tp L ar IL sp0 DL), ?(dlla_gp Lay L DLL); try assumption.
      + split; [exact Hra | exact Hra2].
      + (* [comment removed for export] *)
        intros Hpos. destruct Hptr as [(H0 & _)|(_ & Hin)]; [rewrite H0 in Hpos; cbn in Hpos; lia|].
        exact (di_blksh _ _ _ _ _ _ _ _ _ _ DI (ptr, Z.of_nat (length payload)) Hin).
      + (* [comment removed for export] *)
        rewrite (dla_sptop L ar IL sp0 DL). unfold sp.
        split; [rewrite Z.add_mod, Hal', Hsoal by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * intros i Hi. apply WDEF. lia.
        * intros i Hi. destruct (Z_lt_le_dec (bv_unsigned sp0 + so + i) (bv_unsigned sp0)) as [Hlo|Hhi].
          -- apply WDEF. lia.
          -- replace (bv_unsigned sp0 + so + i) with (bv_unsigned sp0 + (so + i)) by ring. apply Hdef. lia.
      + intros f [].
      + (* [comment removed for export] *)
        intros j Hj. apply (di_stksh _ _ _ _ _ _ _ _ _ _ DI). unfold STKTOP, in_shadow_of, S, SB. rewrite (dla_sptop L ar IL sp0 DL) in *.
        set (mx := Z.max (bv_unsigned sp0) (ar_stack_top ar)) in *.
        replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) by ring.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        unfold sp in *. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - (* [comment removed for export] *)
      intros fx' g' R' M' model' cr' LK' A' HFP' POST HRT HINC Hh' HMI' HLEAK HH'.
      destruct POST as [Qa0 Qregs Qcr Qframe Qscr Qgrows Qstk Qls].
      rewrite ?(dlla_L Lay L DLL) in *.
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (FR : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB [] sp stk a -> ~ in_foot LV a /\ ~ in_junk Lay a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha Hc [Hf Hj]. apply Qframe; [exact Ha | | exact Hf | exact Hj]. apply (aclient_scr_mono L ar sp0 Hsp LB [] sp stk (lla_stack Lay) a); [lia | exact Hc]. }
      assert (ABOVE : forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. apply FR; [lia | | split; [apply (not_foot_off_image L ar sp0 Hsp Lay DLL) | apply (not_junk_off_image L sp0 Hsp Lay DLL)]; lia]. unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). unfold sp. lia. }
      apply (CONT fx' R' M' model' g' cr' LK' A' HFP' HL'); try assumption.
      + (* [comment removed for export] *)
        apply regs_ok_upd_sameA; [| discriminate | cbn [edenot]; symmetry; exact Qa0].
        apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA sp0 Hsp R R' Qregs) c_kept_no0A).
      + (* [comment removed for export] *)
        unfold keep_libA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so stk bls vbnd [] IMG_LIB_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPl L ar Lay LB sp stk (ahid A model) (ahid A' model')) (SCa sp stk)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
        * eapply ((regions_callL scfg L ar C IL HI HIok sp0 Hsp DL Lay DLL) (vals ++ junk_vals R') ebs so stk bls vbnd LB LK LK' cr cr' A A' M M' model model');
            [exact P0' | lia | lia | exact HH | exact HH' | | ].
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha ((HC & HF) & V1 & V2). unfold mrestrict. rewrite V1, V2. apply FR; assumption.
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH') by (unfold sp in *; lia).
          destruct (Z_lt_le_dec a (sp - lla_stack Lay)) as [Hlo|Hhi].
          -- rewrite Qframe; [apply WDEF; unfold sp in *; lia | unfold sp in *; lia | | apply (not_foot_off_image L ar sp0 Hsp Lay DLL); unfold sp in *; lia | apply (not_junk_off_image L sp0 Hsp Lay DLL); unfold sp in *; lia].
             unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). unfold sp in *. lia.
          -- replace a with (sp - lla_stack Lay + (a - (sp - lla_stack Lay))) by ring. apply Qscr. lia.
      + (* [comment removed for export] *)
        apply DINV; [exact HH' | exact HMI' | exact Hh' | | | |].
        * intros a Ha. rewrite (ABOVE a Ha). exact (di_above _ _ _ _ _ _ _ _ _ _ DI a Ha).
        * intros x Hx. destruct (stksh_rng scfg L ar C IL HI HIok sp0 Hsp DL _ _ _ _ _ _ _ x HH Hx) as (XR & XC).
          unfold STKTOP, in_shadow_of, S, SB in Hx. rewrite (dla_sptop L ar IL sp0 DL) in Hx.
          set (mx := Z.max (bv_unsigned sp0) (ar_stack_top ar)) in *.
          replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) in Hx by ring.
          destruct (Z_lt_le_dec x (S (sp - lla_stack Lay))) as [Hlo|Hhi].
          -- unfold byte_at. rewrite FR; [exact (di_stksh _ _ _ _ _ _ _ _ _ _ DI x ltac:(unfold STKTOP, in_shadow_of, S, SB; rewrite (dla_sptop L ar IL sp0 DL); fold mx;
                   replace (bv_unsigned sp0 - 8388608 + (mx - (bv_unsigned sp0 - 8388608)) - 1) with (mx - 1) by ring; exact Hx)) | lia | | split; [apply (not_foot_off_image L ar sp0 Hsp Lay DLL) | apply (not_junk_off_image L sp0 Hsp Lay DLL)]; lia].
             unfold aclient. right. right. right. right. left. exact XC.
          -- replace x with (S (sp - lla_stack Lay) + (x - S (sp - lla_stack Lay))) by ring. apply Qstk.
             rewrite (dla_sptop L ar IL sp0 DL). fold mx. unfold S, SB in *.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             unfold sp in *. lia.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        * intros x Hx. pose proof (hish_rng L ar IL sp0 Hsp DL x Hx) as XR. unfold byte_at.
          rewrite FR; [exact (di_hish _ _ _ _ _ _ _ _ _ _ DI x Hx) | lia | unfold aclient; right; right; right; right; left; exact Hx | split; [apply (not_foot_off_image L ar sp0 Hsp Lay DLL) | apply (not_junk_off_image L sp0 Hsp Lay DLL)]; lia].
        * intros b Hb. apply (blksh_keep1 scfg L ar C HI HIok _ _ _ _ _ _ _ M' b HH Hb (di_blksh _ _ _ _ _ _ _ _ _ _ DI b Hb)).
          intros x Hx. destruct (blksh_rng scfg L ar C HI HIok _ _ _ _ _ _ _ b x HH Hb Hx) as (X1 & X2).
          apply FR; [exact X2 | | split; [apply (not_foot_off_image L ar sp0 Hsp Lay DLL) | apply (not_junk_off_image L sp0 Hsp Lay DLL)]; lia].
          unfold aclient, aclient_g. right. right. right. right. right. right. exists b. split; [exact Hb | exact Hx].
      + intros a Ha Hb. apply FR; [exact Ha | left; exact Hb |].
        destruct Hb as (b & Hb & Hr). destruct (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WF & _). destruct (WF b Hb) as (HBR & _).
        pose proof (hzA_of_block_range L ar IL sp0 DL _ _ HBR) as (Y1 & Y2 & Y3). split; [apply (not_foot_off_image L ar sp0 Hsp Lay DLL) | apply (not_junk_off_image L sp0 Hsp Lay DLL)]; lia.
      + intros lo hi a Hin Ha. destruct (img_lib_sub lo hi Hin) as ((lo' & hi' & Hin' & S1 & S2) & I1 & I2 & I3 & HOLE).
        apply FR; [lia | | split; [apply (not_foot_of_hole L ar sp0 Hsp Lay DLL) | apply (not_junk_of_hole L sp0 Hsp Lay DLL)]; intros hl hh Hhol; destruct (HOLE hl hh Hhol); lia].
        unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL). split; [lia|].
        apply (dla_client L ar IL sp0 DL lo' hi' a Hin'). lia.
  Qed.
End LibSiteW.
End FPX_1.

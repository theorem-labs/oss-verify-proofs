(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section FreeNull.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis FNULL : afree_null_spec L ar scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable M0 : word -> option byte.
  Hypothesis M0_def : defined M0 (bv_unsigned sp0) (ar_stack_top ar - bv_unsigned sp0).
  #[local] Notation dinvA := (dinv ar HI sp0 M0).

  Lemma afree_null_site : forall vals ebs sr kn R M (model : Model) LB LK cr A so bls vbnd (ra : Z) K,
    let E := Env (vals_ev vals) ebs in
    regs_ok E sr R -> know_ok ASEGS E (mrestrict (ahid A model) M) kn ->
    sr_vars_lt (length vals) sr = true -> kn_vars_lt (length vals) kn = true -> (1 <= length vals)%nat -> vals_ev vals 0 = sp0 -> has_window kn = true ->
    getr R 2%bv = Z_to_bv 64 (bv_unsigned sp0 + so) -> - 2 ^ 22 <= so <= 0 -> so mod 16 = 0 ->
    getr R 10%bv = Z_to_bv 64 0 -> getr R 4%bv = Z_to_bv 64 0x673d00 -> getr R 1%bv = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    dinvA LB LK cr A M model ->
    (forall i nb, find_nz i bls = Some nb -> (i < length vals)%nat /\ sub_blockA L ar LB (bv_unsigned (vals_ev vals i)) nb) ->
    (forall v b, find_nz v vbnd = Some b -> (v < length vals)%nat /\ bv_unsigned (vals_ev vals v) <= b) ->
    K [] ->
    (forall R' M' (model' : Model) A',
       let vals' := vals ++ junk_vals R' in
       let E' := Env (vals_ev vals') ebs in
       length vals' = (length vals + 32)%nat ->
       regs_ok E' (sr_after_call_j sr (map ridx c_kept) (length vals)) R' ->
       know_ok ASEGS E' (mrestrict (ahid A' model') M') (keep_allocA so 4096 bls vbnd kn) ->
       dinvA LB LK cr A' M' model' -> model_rt model model' -> incl A A' ->
       (forall a, bv_unsigned sp0 <= a < 2 ^ 47 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall a, 0 <= a < 2 ^ 64 -> in_block LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       (forall lo hi a, In (lo, hi) IMG_CLIENT_A -> lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
       srealizes ASEGS scfg (mkCfg (mkst R' (Z_to_bv 64 ra) M' (seg_rom ASEGS)) model') K) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x79814) M (seg_rom ASEGS)) model) K.
  Proof.
    intros vals ebs sr kn R M model LB LK cr A so bls vbnd ra K E HR HK Hsv Hkv HL1 P0 Hiw
           R2 Hso Hsoal R10 R4 R1 Hra Hra2 DI Hbl Hvb HK0 CONT.
    set (FF := @nil fframe) in *.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ DI) as HH. pose proof (di_halt _ _ _ _ _ _ _ _ _ _ DI) as Hh. pose proof (di_minv _ _ _ _ _ _ _ _ _ _ DI) as HMI.
    pose proof (dinv_stack_defined scfg L ar C HI HIok sp0 Hsp M0 M0_def _ _ _ _ _ _ DI) as Hdef.
    pose proof Hsp as Hsp'. pose proof (dla_scr L ar IL sp0 DL) as (SC1 & SC2 & SC3).
    pose proof (FNULL fx R M model LB FF LK cr A K) as MS.
    rewrite (dla_segs L ar IL sp0 DL), (dla_free L ar IL sp0 DL), (dla_tp L ar IL sp0 DL) in MS. rewrite R1 in MS.
    apply MS; clear MS; try assumption.
    - (* [comment removed for export] *) apply ret_ok_even. rewrite u_small by lia. exact Hra2.
    - (* [comment removed for export] *) rewrite R2, u_small by lia.
      eapply (astack_ok_of_window L ar IL HI sp0 Hsp Hal DL vals ebs (ahid A model) M kn so); eauto; lia.
    - intros R' M' model' A' HP HPRES HRT HINC HMI' HH'.
      rewrite R2, u_small in HPRES by lia. destruct HPRES as (PR1 & PR2).
      assert (Hh' : m_halted model' = None) by (rewrite (model_rt_halted _ _ HRT); exact Hh).
      assert (HL' : length (vals ++ junk_vals R') = (length vals + 32)%nat) by (rewrite length_app, junk_vals_length; reflexivity).
      assert (P0' : vals_ev (vals ++ junk_vals R') 0 = sp0) by (rewrite vals_ev_app_l by lia; exact P0).
      assert (CLI : forall a, aclient L ar LB FF (bv_unsigned sp0 + so) 4096 a -> aclient L ar LB FF (bv_unsigned sp0 + so) (hl_scr_free L) a)
        by (intros a; apply (aclient_scr_mono L ar sp0 Hsp); lia).
      apply (CONT R' M' model' A' HL'); try assumption.
      + (* [comment removed for export] *) apply (regs_after_keeps vals ebs sr R R' c_kept Hsv HR (regs_preserved_keptA sp0 Hsp R R' HP) c_kept_no0A).
      + (* [comment removed for export] *) unfold keep_allocA.
        pose proof (env_app_know ASEGS vals (junk_vals R') ebs _ kn Hkv HK) as HK1.
        refine (know_keep_sound ASEGS 0 so 4096 bls vbnd [] IMG_CLIENT_A IMG_RW_A
                  (Env (vals_ev (vals ++ junk_vals R')) ebs)
                  (CPa L ar LB FF (bv_unsigned sp0 + so) 4096 (ahid A model) (ahid A' model')) (SCa (bv_unsigned sp0 + so) 4096)
                  _ (mrestrict (ahid A model) M) (mrestrict (ahid A' model') M') _ _ kn HK1).
        * eapply (regions_callA scfg L ar C IL HI HIok sp0 Hsp DL (vals ++ junk_vals R') ebs so 4096 bls vbnd LB LB LB FF FF LK LK cr cr A A' M M' model model');
            [exact P0' | exact Hso | lia | exact HH | exact HH' | | | | ].
          -- intros a Ha. exact Ha.
          -- intros a Ha; exact Ha.
          -- intros i nb Hf. destruct (Hbl i nb Hf) as (Hi32 & H1). rewrite vals_ev_app_l by exact Hi32. exact H1.
          -- intros v b Hf. destruct (Hvb v b Hf) as [Hv H1]. rewrite vals_ev_app_l by exact Hv. exact H1.
        * intros a Ha (HC & V1 & V2). unfold mrestrict. rewrite V1, V2. apply PR1; [exact Ha | apply CLI; exact HC].
        * intros a HS. unfold SCa in HS. unfold mrestrict.
          rewrite (vis_of_inv scfg L ar C IL HI HIok sp0 DL _ _ _ _ _ _ _ a HH') by lia.
          destruct (Z_lt_le_dec a (bv_unsigned sp0 + so - hl_scr_free L)) as [Hlo|Hhi].
          -- rewrite PR1; [apply (window_defined sp0 Hsp vals ebs (ahid A model) M kn HK Hiw P0); lia | lia |].
             unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). lia.
          -- apply PR2. lia.
      + (* [comment removed for export] *)
        apply (dinv_call scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LB LB LK LK cr cr A A' M M' model model' (bv_unsigned sp0 + so) (hl_scr_free L) DI ltac:(lia)); assumption.
      + (* [comment removed for export] *) intros a Ha. apply PR1; [lia|]. unfold aclient. right. left. rewrite (dla_sptop L ar IL sp0 DL). lia.
      + intros a Ha Hb. apply PR1; [exact Ha | left; exact Hb].
      + intros lo hi a Hin' Ha. assert (0 <= a < 2 ^ 64).
        { destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3). lia. }
        apply PR1; [assumption|]. unfold aclient. right. right. left. rewrite (dla_img_lo L ar IL sp0 DL), (dla_img_hi L ar IL sp0 DL).
        split; [destruct (img_client_rng lo hi Hin') as (I1 & I2 & I3); lia | exact (dla_client L ar IL sp0 DL lo hi a Hin' Ha)].
  Qed.
End FreeNull.
End FPX_1.

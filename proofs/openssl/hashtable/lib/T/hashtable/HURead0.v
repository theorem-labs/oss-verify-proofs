(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac Frame MemSplit LibMaskBits
  SumWalkTac RefMemcpyLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame LibKnowXfer
  RefNodes PhaseG RefReadLib HUReadBase HUReadStage HUReadChunk.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HU_code_dd000_de000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import HUReadChunk.H0ReadChunkW.
Import ConeCfg.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition front_kept : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

(* [comment removed for export] *)
Lemma front_walk : forall regs mem rom (buf : Z),
  getr regs 10 = Z_to_bv 64 buf -> (0 < buf < 2 ^ 64)%Z -> getr regs 21 = Z_to_bv 64 65536 ->
  exists regs',
    msteps RSEGS (mkst regs (0xe19e0 : word) mem rom) (mkst regs' (0xe1a68 : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 STAGE
    /\ (forall r, In r front_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf Ha0 Hbuf Hs5. eexists. split.
  - stepb_ft F_dd0a8 D_dd0a8 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_dd0ac D_dd0ac. rewrite Ha0.
    stepn F_dd0b0 D_dd0b0.
    stepn F_dd0b4 D_dd0b4.
    stepn F_dd0b8 D_dd0b8.
    stepb_tk F_dd0bc D_dd0bc ltac:(rewrite Hs5; cond_compute).
    stepn F_dd0e4 D_dd0e4.
    stepn F_dd0e8 D_dd0e8.
    apply mst_refl.
  - split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; apply bv_eq; vm_compute; reflexivity|].
    intros r Hr; cbv [front_kept In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

Section R0.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  Let MPRE := model_pre path VM stdin0 fs0 tid.
  Let MPOST := model_post VM stdin0 fs0 tid.

  (* [comment removed for export] *)
  Lemma loop_entry : forall mode Q R M K,
    read_pre sp0 p1 mb bw gm can sec R M ->
    (forall R1, getr R1 9 = Z_to_bv 64 (bv_unsigned gm + 32) -> getr R1 23 = Z_to_bv 64 (bv_unsigned gm + 32) ->
       getr R1 19 = Z_to_bv 64 0 -> getr R1 22 = Z_to_bv 64 STAGE ->
       (forall r, In r front_kept -> getr R1 r = getr R r) ->
       GG RSEGS mode Q K (mkCfg (mkst R1 (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) MPRE)) ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS)) MPRE).
  Proof.
    intros mode Q R M K RP HK. pose proof (rp_gm _ _ _ _ _ _ _ _ _ RP) as Hgm. pose proof (rp_sp0 _ _ _ _ _ _ _ _ _ RP) as Hsp.
    destruct (front_walk R M (seg_rom RSEGS) (bv_unsigned gm + 32) (rp_a0 _ _ _ _ _ _ _ _ _ RP) ltac:(lia) (rp_s5 _ _ _ _ _ _ _ _ _ RP))
      as (R1 & RUN & A9 & A23 & A19 & A22 & AK).
    replace (Z_to_bv 64 0xe19e0) with (0xe19e0 : word) by (apply bv_eq; reflexivity).
    eapply gg_msteps; [reflexivity | reflexivity | exact RUN |].
    replace (0xe1a68 : word) with (Z_to_bv 64 0xe1a68) by (apply bv_eq; reflexivity).
    apply HK; assumption.
  Qed.

  (* [comment removed for export] *)
  Theorem read_k0 : forall mode Q R M K,
    read_pre sp0 p1 mb bw gm can sec R M -> (L < 65536)%Z ->
    (forall R' M', read_post0 sp0 p1 gm content R M R' M' ->
       GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1aa0) M' (seg_rom RSEGS)) MPOST)) ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS)) MPRE).
  Proof.
    intros mode Q R M K RP HL Hk.
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hbi Hgm Hgb Hst Hgr Hmw Her Hsw Hkm].
    apply (loop_entry mode Q R M K RP). intros R1 A9 A23 A19 A22 AK.
    change MPRE with (modelG path stdin0 fs0 tid 0 VM).
    apply (chunk_loop_mid path content stdin0 fs0 tid VM Hfile mode Q (Z.to_nat 65536) R1 M (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [exact A9 | split; [exact A19 | split; [|split; [|exact A22]]]]].
      + rewrite (AK 2%bv) by (cbn; noncert_qtauto). exact Rsp.
      + rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
      + rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - subst L. lia.
    - replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia.
    - replace (bv_unsigned gm + 32 + 0)%Z with (bv_unsigned gm + 32)%Z by lia. apply Hgr; lia.
    - exact Hsw.
    - intros HcL. exfalso. subst L. lia.
    - intros HLc R' M' (P2 & P9 & P19 & P22 & P23 & PK) PM. apply Hk.
      pose proof PM as [[EQ GR] RD].
      constructor.
      + exact P2.
      + rewrite (PK 3%bv) by (cbn; noncert_qtauto). rewrite (AK 3%bv) by (cbn; noncert_qtauto). exact Rgp.
      + rewrite (PK 4%bv) by (cbn; noncert_qtauto). rewrite (AK 4%bv) by (cbn; noncert_qtauto). exact Rtp.
      + rewrite (PK 8%bv) by (cbn; noncert_qtauto). rewrite (AK 8%bv) by (cbn; noncert_qtauto). exact Rs0.
      + exact P9.
      + rewrite (PK 18%bv) by (cbn; noncert_qtauto). rewrite (AK 18%bv) by (cbn; noncert_qtauto). exact Rs2.
      + rewrite P19. subst L. reflexivity.
      + rewrite (PK 20%bv) by (cbn; noncert_qtauto). rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
      + rewrite (PK 21%bv) by (cbn; noncert_qtauto). rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
      + exact P22.
      + exact P23.
      + intros r Hr. cbv [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
          (rewrite PK by (cbn; noncert_qtauto); rewrite AK by (cbn; noncert_qtauto); reflexivity).
      + (* [comment removed for export] *)
        intros a [O1 [O2 [O3 _]]]. apply EQ. cbn [outside loop_regions]. unfold in_rng, STAGE in *. rewrite !u_small in * by lia.
        subst L. repeat split; lia.
      + exact GR.
      + (* [comment removed for export] *)
        subst L. eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned gm + 32) 0); try lia; [|exact PM].
        rewrite pref_0. reflexivity.
      + eapply stack_writable_grows; [exact GR | exact Hst].
      + eapply group_writable_grows; [exact GR | exact Hgr].
      + eapply stage_writable_grows; [exact GR | exact Hsw].
  Qed.

  (* [comment removed for export] *)
  Theorem read_full0 : forall mode Q R M K (e : word),
    read_pre sp0 p1 mb bw gm can sec R M -> (65536 <= L)%Z ->
    rdn RSEGS M (Z_to_bv 64 0x331a44) 4 = Some (word_to_le_bytes 4 e) ->
    (forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None) ->
    (forall R' M', full0 sp0 p1 mb bw gm L e can sec content M R' M' ->
       stack_writable M' sp0 ->
       GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1a24) M' (seg_rom RSEGS)) (modelG path stdin0 fs0 tid 65536 VM))) ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe19e0) M (seg_rom RSEGS)) MPRE).
  Proof.
    intros mode Q R M K e RP HL He Hpage0 Hk.
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hbi Hgm Hgb Hst Hgr Hmw Her Hsw Hkm].
    apply (loop_entry mode Q R M K RP). intros R1 A9 A23 A19 A22 AK.
    change MPRE with (modelG path stdin0 fs0 tid 0 VM).
    apply (chunk_loop_mid path content stdin0 fs0 tid VM Hfile mode Q (Z.to_nat 65536) R1 M (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [exact A9 | split; [exact A19 | split; [|split; [|exact A22]]]]].
      + rewrite (AK 2%bv) by (cbn; noncert_qtauto). exact Rsp.
      + rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
      + rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - subst L. lia.
    - replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia.
    - replace (bv_unsigned gm + 32 + 0)%Z with (bv_unsigned gm + 32)%Z by lia. apply Hgr; lia.
    - exact Hsw.
    - intros HcL R' M' (P2 & P9 & P19 & P22 & P23 & PK) PM. pose proof PM as [[EQ GR] RD]. apply Hk.
      2:{ eapply stack_writable_grows; [exact GR | exact Hst]. }
      split.
      2:{ eapply (pres_loop_post content M M M' sp0); [apply pres_refl | exact PM | lia | lia | lia | lia]. }
      exists (junk_vals R'). split; [apply junk_vals_length|].
      set (E := ENV_RD sp0 p1 mb bw gm L (Z_to_bv 64 0) e can sec (junk_vals R') content).
      split.
      + (* [comment removed for export] *)
        apply (sr_LOOP_regs sp0 p1 mb bw gm L (Z_to_bv 64 0) e can sec content R' (gmx 32) (bv_unsigned gm + 32) 65536 65536 (lr_gmx _ _ _ _ _ _ _ _ _ _ _ _ 32));
          try assumption.
        * rewrite (PK 3%bv) by (cbn; noncert_qtauto). rewrite (AK 3%bv) by (cbn; noncert_qtauto). exact Rgp.
        * rewrite (PK 4%bv) by (cbn; noncert_qtauto). rewrite (AK 4%bv) by (cbn; noncert_qtauto). exact Rtp.
        * rewrite (PK 8%bv) by (cbn; noncert_qtauto). rewrite (AK 8%bv) by (cbn; noncert_qtauto). exact Rs0.
        * rewrite (PK 18%bv) by (cbn; noncert_qtauto). rewrite (AK 18%bv) by (cbn; noncert_qtauto). exact Rs2.
        * rewrite (PK 20%bv) by (cbn; noncert_qtauto). rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
        * rewrite (PK 21%bv) by (cbn; noncert_qtauto). rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
      + (* [comment removed for export] *)
        assert (KG : know_ok RSEGS E M kn_G0).
        { unfold kn_G0. apply (proj2 (know_ok_app _ _ _ _ _)). split; [| apply (know_ok_noblob_irrel RSEGS _ (blobs_ev []) (gblobs content) M kn_M1 eq_refl (Hkm sp0 p1 (Z_to_bv 64 L) (Z_to_bv 64 0) e (Z_to_bv 64 0) (junk_vals R') []))].
          unfold know_ok.
          repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
            change (ev E 0) with sp0; change (ev E 1) with p1; change (ev E 2) with mb; change (ev E 3) with gm; change (ev E 6) with e;
            unfold flat, estart, LA, HUGE, CEIL; cbn [a_base a_off edenot];
            change (ev E 0) with sp0; change (ev E 2) with mb; change (ev E 3) with gm;
            try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
          - split; [lia | exact (proj2 Hsp)].
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 0) with sp0.
            replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia. apply Hst; lia.
          - lia.
          - split; [lia | exact (proj2 (proj2 Hb))].
          - lia.
          - lia.
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with mb.
            apply Hmw; lia.
          - split; [lia | exact (proj2 (proj2 Hgm))].
          - lia.
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 3) with gm.
            rewrite Z.add_0_r. apply Hgr; lia.
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot].
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
            replace (0 + 3268608 + d)%Z with (3268608 + d)%Z by lia. apply data_store_ok; lia.
          - split; [lia|]. split; [lia|]. unfold adenot, v_addi. cbn [a_base a_off edenot].
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. exact He.
          - split; [lia|]. split; [lia|]. exact Hpage0. }
        (* [comment removed for export] *)
        assert (KG' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn_G0 (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 3) 32 65536)).
        { apply (know_ok_frame3 E M M' kn_G0 (EVar 0) (-136) 8 (ELit 0) STAGE 65536 (EVar 3) 32 65536 KG).
          - apply flat_intro; cbn [edenot]; change (ev E 0) with sp0; lia.
          - apply flat_intro; cbn [edenot]; unfold STAGE; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia.
          - apply flat_intro; cbn [edenot]; change (ev E 3) with gm; lia.
          - unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 0) with sp0. change (ev E 3) with gm.
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l.
            replace (bv_unsigned sp0 + -136)%Z with (bv_unsigned sp0 - 136)%Z by lia.
            replace 65536%Z with (65536 - 0)%Z at 3 by lia.
            replace (bv_unsigned gm + 32)%Z with (bv_unsigned gm + 32 + 0)%Z by lia. exact (proj1 PM). }
        assert (EQK : kn_frame (kn_frame (kn_frame kn_G0 (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 3) 32 65536 = kn_G0) by (vm_compute; reflexivity).
        rewrite EQK in KG'. clear KG EQK.
        (* [comment removed for export] *)
        assert (KB : kentry_ok RSEGS E M' (KBlob (GMA 32) (ELit 65536) 0%nat)).
        { unfold GMA. apply (kblob_of_rdn E M' (EVar 3) gm 32 65536 0%nat (pref 65536 content)).
          - reflexivity.
          - cbn [eb E ENV_RD]. rewrite <- (gblobs_fb 0) by lia. reflexivity.
          - pose proof (pref_length 65536 content ltac:(lia)). subst L. lia.
          - lia.
          - lia.
          - pose proof (pref_length 65536 content ltac:(lia)) as PL.
            replace (length (pref 65536 content)) with (Z.to_nat (65536 - 0)) by (subst L; lia).
            replace (bv_unsigned gm + 32)%Z with (bv_unsigned gm + 32 + 0)%Z by lia.
            rewrite RD. rewrite dropz_0. f_equal. }
        unfold kn_FULL0. apply (proj2 (know_ok_app _ _ _ _ _)). split; [exact KG'|].
        apply know_ok_cons; [exact KB | apply Forall_nil].
    - intros HLc. exfalso. subst L. lia.
  Qed.
End R0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

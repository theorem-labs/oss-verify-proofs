(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac Frame MemSplit LibMaskBits SumWalkTac RefMemcpyLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame LibKnowXfer RefNodes RefReadLib UbReadBase UbReadStage UbReadChunk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Frame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MemSplit OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibMaskBits OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SumWalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymExec2Sound OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymRun OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDrive OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SymDriveX OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowFrame OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibKnowXfer OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefNodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefReadLib OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadBase OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadStage OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadChunk.RefReadChunkW OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbReadChunk.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import Ub_code_32468_33000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := ImgU.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPW_1. Context {fx : PropExec.FPState}.

Section R0.
  Variables (sp0 p1 mb gm can sec : word) (path content : list byte).   (* [comment removed for export] *)
  Variables (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  Let MPRE := model_pre path VM stdin0 fs0 tid.
  Let MPOST := model_post VM stdin0 fs0 tid.

  (* [comment removed for export] *)
  Lemma loop_entry : forall R M K,
    read_pre sp0 p1 mb gm can sec R M ->
    (forall R1, getr R1 9 = Z_to_bv 64 (bv_unsigned gm + 32) -> getr R1 23 = Z_to_bv 64 (bv_unsigned gm + 32) ->
       getr R1 19 = Z_to_bv 64 0 -> getr R1 22 = Z_to_bv 64 STAGE ->
       (forall r, In r [1; 2; 3; 4; 8; 18; 20; 21; 24; 25; 26; 27]%bv -> getr R1 r = getr R r) ->
       realizes RSEGS (mkCfg (mkst R1 (Z_to_bv 64 0x32700) M (seg_rom RSEGS)) MPRE) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32688) M (seg_rom RSEGS)) MPRE) K.
  Proof.
    intros R M K RP HK. pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hgm. pose proof (rp_sp0 _ _ _ _ _ _ _ _ RP) as Hsp0.
    destruct (walkA0 R M (seg_rom RSEGS) (bv_unsigned gm + 32) 65536 (rp_a0 _ _ _ _ _ _ _ _ RP) (rp_s5 _ _ _ _ _ _ _ _ RP) ltac:(lia) ltac:(lia))
      as (R1 & RUN & A9 & A23 & A19 & A22 & AK).
    replace (Z_to_bv 64 0x32688) with (0x32688 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN |].
    replace (0x32700 : word) with (Z_to_bv 64 0x32700) by (apply bv_eq; reflexivity).
    apply HK; assumption.
  Qed.

  (* [comment removed for export] *)
  Theorem read_k0 : forall R M K,
    read_pre sp0 p1 mb gm can sec R M -> (L < 65536)%Z ->
    (forall R' M', read_post0 sp0 p1 gm content R M R' M' ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x32730) M' (seg_rom RSEGS)) MPOST) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32688) M (seg_rom RSEGS)) MPRE) K.
  Proof.
    intros R M K RP HL Hk.
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hbi Hgm Hgb Hst Hgr Hmw Her Hkm].
    apply (loop_entry R M K RP). intros R1 A9 A23 A19 A22 AK.
    change MPRE with (modelG path stdin0 fs0 tid 0 VM).
    apply (chunk_loop_mid path content stdin0 fs0 tid VM Hfile (Z.to_nat 65536) R1 M (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [exact A9 | split; [exact A19 | split; [|split]]]].
      + rewrite (AK 2%bv) by (cbn; noncert_qtauto). exact Rsp.
      + rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
      + rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
      + exact A22.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - subst L. lia.
    - replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia.
    - replace (bv_unsigned gm + 32 + 0)%Z with (bv_unsigned gm + 32)%Z by lia. apply Hgr; lia.
    - intros HcL. exfalso. subst L. lia.
    - intros HLc R' M' (P2 & P9 & P23 & P19 & PK) PM. apply Hk.
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
      + rewrite (PK 22%bv) by (cbn; noncert_qtauto). exact A22.
      + exact P23.
      + intros r Hr. cbv [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]];
          (rewrite PK by (cbn; noncert_qtauto); rewrite AK by (cbn; noncert_qtauto); reflexivity).
      + (* [comment removed for export] *)
        intros a [O1 [O2 [O3 _]]]. apply EQ. cbn [outside loop_regions fst snd]. unfold in_rng, STAGE in *. rewrite !u_small in * by lia.
        subst L. repeat split; lia.
      + exact GR.
      + (* [comment removed for export] *)
        subst L. eapply (content_at_buf content M M' (bv_unsigned sp0) (bv_unsigned gm + 32) 0); try lia; [|exact PM].
        rewrite pref_0. reflexivity.
      + eapply stack_writable_grows; [exact GR | exact Hst].
      + eapply group_writable_grows; [exact GR | exact Hgr].
  Qed.

  (* [comment removed for export] *)
  Theorem read_full0 : forall R M K (e : word),
    read_pre sp0 p1 mb gm can sec R M -> (65536 <= L)%Z ->
    rdn RSEGS M (Z_to_bv 64 0xc4f74) 4 = Some (word_to_le_bytes 4 e) ->
    (forall i, (0 <= i < 0x1000)%Z -> M (Z_to_bv 64 i) = None) ->
    (forall R' M', full0 sp0 p1 mb gm L e can sec content M R' M' ->
       stack_writable M' sp0 ->
       realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x326c8) M' (seg_rom RSEGS)) (modelG path stdin0 fs0 tid 65536 VM)) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32688) M (seg_rom RSEGS)) MPRE) K.
  Proof.
    intros R M K e RP HL He Hpage0 Hk.
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hbi Hgm Hgb Hst Hgr Hmw Her Hkm].
    apply (loop_entry R M K RP). intros R1 A9 A23 A19 A22 AK.
    change MPRE with (modelG path stdin0 fs0 tid 0 VM).
    apply (chunk_loop_mid path content stdin0 fs0 tid VM Hfile (Z.to_nat 65536) R1 M (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536 K).
    - rewrite Z2Nat.id by lia. lia.
    - split; [|split; [exact A9 | split; [exact A19 | split; [|split]]]].
      + rewrite (AK 2%bv) by (cbn; noncert_qtauto). exact Rsp.
      + rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
      + rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
      + exact A22.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - subst L. lia.
    - replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia.
    - replace (bv_unsigned gm + 32 + 0)%Z with (bv_unsigned gm + 32)%Z by lia. apply Hgr; lia.
    - intros HcL R' M' (P2 & P9 & P23 & P19 & PK) PM. pose proof PM as [[EQ GR] RD]. apply Hk.
      2:{ eapply stack_writable_grows; [exact GR | exact Hst]. }
      split.
      2:{ eapply (pres_loop_post content M M M' sp0); [apply pres_refl | exact PM | lia | lia | lia | lia]. }
      exists (junk_vals R'). split; [apply junk_vals_length|].
      set (E := ENV_RD sp0 p1 mb gm L (Z_to_bv 64 0) e can sec (junk_vals R') content).
      split.
      + (* [comment removed for export] *)
        apply (sr_LOOP_regs sp0 p1 mb gm L (Z_to_bv 64 0) e can sec content R' (gmx 32) (bv_unsigned gm + 32) 65536 65536 (lr_gmx _ _ _ _ _ _ _ _ _ _ _ 32));
          try assumption.
        * rewrite (PK 3%bv) by (cbn; noncert_qtauto). rewrite (AK 3%bv) by (cbn; noncert_qtauto). exact Rgp.
        * rewrite (PK 4%bv) by (cbn; noncert_qtauto). rewrite (AK 4%bv) by (cbn; noncert_qtauto). exact Rtp.
        * rewrite (PK 8%bv) by (cbn; noncert_qtauto). rewrite (AK 8%bv) by (cbn; noncert_qtauto). exact Rs0.
        * rewrite (PK 18%bv) by (cbn; noncert_qtauto). rewrite (AK 18%bv) by (cbn; noncert_qtauto). exact Rs2.
        * rewrite (PK 20%bv) by (cbn; noncert_qtauto). rewrite (AK 20%bv) by (cbn; noncert_qtauto). exact Rs4.
        * rewrite (PK 21%bv) by (cbn; noncert_qtauto). rewrite (AK 21%bv) by (cbn; noncert_qtauto). exact Rs5.
        * rewrite (PK 22%bv) by (cbn; noncert_qtauto). exact A22.
      + (* [comment removed for export] *)
        assert (KG : know_ok RSEGS E M kn_G0).
        { unfold kn_G0. apply (proj2 (know_ok_app _ _ _ _ _)). split; [| apply (know_ok_noblob_irrel RSEGS _ (blobs_ev []) (gblobs content) M kn_M1 eq_refl (Hkm sp0 p1 (Z_to_bv 64 L) (Z_to_bv 64 0) e (tl (junk_vals R')) []))].
          unfold know_ok.
          repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
            change (ev E 0) with sp0; change (ev E 1) with p1; change (ev E 2) with mb; change (ev E 3) with gm; change (ev E 6) with e;
            unfold flat, estart, LA, BELOW; cbn [a_base a_off edenot];
            change (ev E 0) with sp0; change (ev E 2) with mb; change (ev E 3) with gm;
            try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
          - split; [lia | exact (proj2 Hsp)].
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 0) with sp0.
            replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia. apply Hst; lia.
          - lia.
          - split; [lia | exact (proj2 (proj2 Hb))].
          - unfold CEIL. lia.
          - lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 2) with mb.
            apply Hmw; lia.
          - split; [lia | exact (proj2 (proj2 Hgm))].
          - unfold CEIL. lia.
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 3) with gm.
            rewrite Z.add_0_r. apply Hgr; lia.
          - lia.
          - lia.   (* [comment removed for export] *)
          - lia.   (* [comment removed for export] *)
          - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot].
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
            replace (0 + 733184 + d)%Z with (733184 + d)%Z by lia. apply data_store_ok; lia.
          - split; [lia|]. split; [lia|]. unfold adenot, v_addi. cbn [a_base a_off edenot].
            change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. exact He.
          - split; [lia|]. split; [lia|]. exact Hpage0. }
        (* [comment removed for export] *)
        assert (KG' : know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn_G0 (EVar 0) (-136) 8) (ELit 0) STAGE 65536) (EVar 3) 32 65536)).
        { apply (know_ok_frame3 E M M' kn_G0 (EVar 0) (-136) 8 (ELit 0) STAGE 65536 (EVar 3) 32 65536 KG).
          - apply flat_intro; cbn [edenot]; change (ev E 0) with sp0; lia.
          - apply flat_intro; cbn [edenot]; unfold STAGE; rewrite ?u_small by lia; lia.
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
End FPW_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec StepTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VState2 VStepMem2 VGamma2 VStepMem2SoundA VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound1_both VContractASound2 VContractASound2_both VContractASound3.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require BothRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require CatSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VBothTlsWalk VBothStackMallocWalk VBothStackMallocEff.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac vm_refl := vm_refl_bv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_GOT_cflags : Z := 0xa94a8.  (* [comment removed for export] *)
Definition A_GOT_ndl : Z := 0xa9508.     (* [comment removed for export] *)
Definition A_DESC0 : Z := 0xaa198.       (* [comment removed for export] *)
Definition A_DESC1 : Z := 0xaa1a0.       (* [comment removed for export] *)
Definition A_GOT_dtls : Z := 0xaa1a8.    (* [comment removed for export] *)
Definition A_REAL_tga : Z := 0xab268.    (* [comment removed for export] *)

Lemma GOT_cflags_bytes : rdn BSEGS (fun _ => None) (wordZ A_GOT_cflags) 8 = Some (word_to_le_bytes 8 (wordZ 0x1436e8)).
Proof. vm_refl_bv. Qed.
Lemma GOT_ndl_bytes : rdn BSEGS (fun _ => None) (wordZ A_GOT_ndl) 8 = Some (word_to_le_bytes 8 (wordZ 0x141658)).
Proof. vm_refl_bv. Qed.
Lemma DESC0_bytes : rdn BSEGS (fun _ => None) (wordZ A_DESC0) 8 = Some (word_to_le_bytes 8 (wordZ 1)).
Proof. vm_refl_bv. Qed.
Lemma DESC1_bytes : rdn BSEGS (fun _ => None) (wordZ A_DESC1) 8 = Some (word_to_le_bytes 8 (wordZ 0xfffffffffffff800)).
Proof. vm_refl_bv. Qed.
Lemma GOT_dtls_bytes : rdn BSEGS (fun _ => None) (wordZ A_GOT_dtls) 8 = Some (word_to_le_bytes 8 (wordZ 0x8)).
Proof. vm_refl_bv. Qed.
Lemma REAL_tga_bytes : rdn BSEGS (fun _ => None) (wordZ A_REAL_tga) 8 = Some (word_to_le_bytes 8 (wordZ 0xa33dc)).
Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
Definition sm_tgt (cid : Z) : Z :=
  match cid with 0 => 0x3ece8 | 1 => 0x3ee5c | 2 => 0x3efec | 3 => 0x3f188 | _ => 0x3f334 end.
Definition TP_asan : Z := 0x5e4bb0.
Definition TSD_asan : Z := 0x605f58.

(* [comment removed for export] *)
Lemma geo0 fs p : flag_addr fs 0 p = fs + 4096 + p /\ frame_addr fs 0 p = fs + 36864 + 64 * p /\ fake_size 0 = 64 /\ fs_nframes 0 = 16384.
Proof.
  unfold flag_addr, frame_addr, fs_flags_off. change (fake_size 0) with 64. change (fs_nframes 0) with 16384.
  change (fs_flags_off_nat (Z.to_nat 0)) with 0. unfold FS_FLAGS, FS_FRAMES, FS_SSL. change (2 ^ 20) with 1048576. lia.
Qed.
Lemma geo1 fs p : flag_addr fs 1 p = fs + 20480 + p /\ frame_addr fs 1 p = fs + 1085440 + 128 * p /\ fake_size 1 = 128 /\ fs_nframes 1 = 8192.
Proof.
  unfold flag_addr, frame_addr, fs_flags_off. change (fake_size 1) with 128. change (fs_nframes 1) with 8192.
  change (fs_flags_off_nat (Z.to_nat 1)) with 16384. unfold FS_FLAGS, FS_FRAMES, FS_SSL. change (2 ^ 20) with 1048576. lia.
Qed.
Lemma geo2 fs p : flag_addr fs 2 p = fs + 28672 + p /\ frame_addr fs 2 p = fs + 2134016 + 256 * p /\ fake_size 2 = 256 /\ fs_nframes 2 = 4096.
Proof.
  unfold flag_addr, frame_addr, fs_flags_off. change (fake_size 2) with 256. change (fs_nframes 2) with 4096.
  change (fs_flags_off_nat (Z.to_nat 2)) with 24576. unfold FS_FLAGS, FS_FRAMES, FS_SSL. change (2 ^ 20) with 1048576. lia.
Qed.
Lemma geo3 fs p : flag_addr fs 3 p = fs + 32768 + p /\ frame_addr fs 3 p = fs + 3182592 + 512 * p /\ fake_size 3 = 512 /\ fs_nframes 3 = 2048.
Proof.
  unfold flag_addr, frame_addr, fs_flags_off. change (fake_size 3) with 512. change (fs_nframes 3) with 2048.
  change (fs_flags_off_nat (Z.to_nat 3)) with 28672. unfold FS_FLAGS, FS_FRAMES, FS_SSL. change (2 ^ 20) with 1048576. lia.
Qed.
Lemma geo4 fs p : flag_addr fs 4 p = fs + 34816 + p /\ frame_addr fs 4 p = fs + 4231168 + 1024 * p /\ fake_size 4 = 1024 /\ fs_nframes 4 = 1024.
Proof.
  unfold flag_addr, frame_addr, fs_flags_off. change (fake_size 4) with 1024. change (fs_nframes 4) with 1024.
  change (fs_flags_off_nat (Z.to_nat 4)) with 30720. unfold FS_FLAGS, FS_FRAMES, FS_SSL. change (2 ^ 20) with 1048576. lia.
Qed.

Lemma asan_caller_saved (clob : reg -> bool) regs regs' :
  (forall r : reg, clob r = false -> getr regs' r = getr regs r) ->
  (forall r : reg, clob r = true -> In (bv_unsigned r) CALLER_SAVED) ->
  forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r.
Proof. intros K C r _ N. apply K. destruct (clob r) eqn:E; [|reflexivity]. exfalso. exact (N (C r E)). Qed.

Lemma sm_clob_saved (r : reg) : VBothStackMallocWalk.sm_clob r = true -> In (bv_unsigned r) CALLER_SAVED.
Proof.
  unfold VBothStackMallocWalk.sm_clob. intros H.
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]);
    unfold bv_eqb in H; apply Z.eqb_eq in H; rewrite H; unfold CALLER_SAVED; cbn; tauto.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_img_asan : forall (a : word), 0x607000 <= bv_unsigned a -> seg_rom BSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom. unfold memory_read.
  cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
  cbn [Z.of_N].
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a) && ?c)%bool] =>
              replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.

(* [comment removed for export] *)
Section Contracts.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO2 : params_ok2 BSEGS P.
  Hypothesis SHOFF : vp_shoff P = SBz.
  Hypothesis VTP : vp_tp P = TP_asan.
  Hypothesis CITP : ci_tp CI = vp_tp P.
  (* [comment removed for export] *)
  Hypothesis VIMG : 0x607000 <= vp_imgend P.
  Lemma ROM_IMG_asan : forall a : word, vp_imgend P <= bv_unsigned a -> seg_rom BSEGS a = None.
  Proof. intros a Ha. apply seg_rom_img_asan. pose proof VIMG. lia. Qed.
  (* [comment removed for export] *)
  Hypothesis Z_HINTS : zone_covers P FSB 0 0 88.
  Hypothesis Z_FLAGS : zone_covers P FSB 0 FS_FLAGS FS_FRAMES.
  Hypothesis Z_FRAMES : zone_covers P FSB 0 FS_FRAMES (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL).
  Hypothesis Z_FSHAD : zone_covers P FS8 SBz (FS_FRAMES / 8) ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8).
  (* [comment removed for export] *)
  Hypothesis PRI_GOT1 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_cflags /\ A_GOT_hend + 8 <= phi.
  Hypothesis PRI_GOT2 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_ndl /\ A_GOT_ndl + 8 <= phi.
  Hypothesis PRI_DESC : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_DESC0 /\ A_DESC1 + 8 <= phi.
  Hypothesis PRI_GOT3 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_dtls /\ A_GOT_dtls + 8 <= phi.
  Hypothesis PRI_REAL : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_REAL_tga /\ A_REAL_tga + 8 <= phi.
  (* [comment removed for export] *)
  Hypothesis K_shb : In (A_shb, (8, SBz)) (vp_kcells P).
  Hypothesis K_mid1 : In (A_mid1, (8, 0)) (vp_kcells P).
  Hypothesis K_mid2 : In (A_mid2, (8, 0)) (vp_kcells P).
  Hypothesis K_hend : In (A_hend, (8, 2 ^ 47 - 1)) (vp_kcells P).
  Hypothesis K_inited : In (0xb2898, (1, 1)) (vp_kcells P).
  Hypothesis K_tsdki : In (0xb1420, (1, 1)) (vp_kcells P).
  Hypothesis K_tsdkey : In (0xb1424, (4, 0)) (vp_kcells P).
  Hypothesis K_ndl : In (0x141658, (4, 0)) (vp_kcells P).
  Hypothesis K_itga : In (0x143771, (1, 1)) (vp_kcells P).
  Hypothesis K_tsd : In (0x5e4b58, (8, TSD_asan)) (vp_kcells P).
  Hypothesis K_dtv : In (0x5e4ba8, (8, 0x5e4bd0)) (vp_kcells P).
  Hypothesis K_dtv1 : In (0x5e4bd8, (8, 0x5e53b0)) (vp_kcells P).

  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 BSEGS P E mem0).

  (* [comment removed for export] *)
  Definition SM_MCELLS (m : word -> option byte) : Prop := VBothTlsWalk.tcells m /\ BothRegionPoisoned.cells m.

  Lemma kcellN A nu regs mem a w v :
    gamma2P A nu regs mem -> In (a, (w, v)) (vp_kcells P) ->
    rdn BSEGS mem (wordZ a) (Z.to_nat w) = Some (Z_to_le_bytes (Z.to_nat w) v).
  Proof.
    intros HG2 Hin. pose proof HG2 as (_ & _ & (KC & _) & _).
    destruct (KC _ _ _ Hin) as (_ & _ & _ & bs & R & V). rewrite R, <- V, <- (rdn_length _ _ _ _ _ R). f_equal. symmetry. apply Z_to_le_bytes_to_Z.
  Qed.

  Lemma SM_MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> SM_MCELLS mem.
  Proof.
    intros A nu regs mem HG2. unfold SM_MCELLS, VBothTlsWalk.tcells, BothRegionPoisoned.cells, BothRegionPoisoned.cell.
    change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
    change BothRegionPoisoned.SB with SBz. change BothRegionPoisoned.kHighEnd with (2 ^ 47 - 1).
    fold (wordZ 0xb2898) (wordZ 0xab268) (wordZ 0xa33dc) (wordZ 0xaa198) (wordZ 1) (wordZ 0xaa1a0) (wordZ 0xfffffffffffff800)
         (wordZ 0x5e4ba8) (wordZ 0x5e4bd0) (wordZ 0x5e4bd8) (wordZ 0x5e53b0) (wordZ 0xb1420) (wordZ 0xb1424) (wordZ 0)
         (wordZ 0x5e4b58) (wordZ 0x605f58) (wordZ 0xa94a8) (wordZ 0x1436e8) (wordZ 0x143771) (wordZ 0xa9508) (wordZ 0x141658)
         (wordZ 0xaa1a8) (wordZ 0x8)
         (wordZ 0xa94b8) (wordZ 0xb1bb8) (wordZ 0xa94c0) (wordZ 0xb28a8) (wordZ 0xa94c8) (wordZ 0xb28b0)
         (wordZ 0xa94d0) (wordZ 0xb28a0) (wordZ SBz) (wordZ (2 ^ 47 - 1)).
    destruct PRI_DESC as (plo & phi & G1 & G2 & G3). unfold A_DESC0, A_DESC1 in G2, G3.
    destruct PRI_GOT1 as (qlo & qhi & Q1 & Q2 & Q3). unfold A_GOT_cflags, A_GOT_hend in Q2, Q3.
    repeat split.
    - exact (kcellN A nu regs mem _ _ _ HG2 K_inited).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exact PRI_REAL|exact REAL_tga_bytes].
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact DESC0_bytes].
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact DESC1_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_dtv).
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_dtv1).
    - exact (kcellN A nu regs mem _ _ _ HG2 K_tsdki).
    - exact (kcellN A nu regs mem _ _ _ HG2 K_tsdkey).
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_tsd).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists qlo, qhi; split; [exact Q1|lia]|exact GOT_cflags_bytes].
    - exact (kcellN A nu regs mem _ _ _ HG2 K_itga).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exact PRI_GOT2|exact GOT_ndl_bytes].
    - exact (kcellN A nu regs mem _ _ _ HG2 K_ndl).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exact PRI_GOT3|exact GOT_dtls_bytes].
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists qlo, qhi; split; [exact Q1|unfold A_GOT_shb; lia]|exact GOT_shb_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_shb).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists qlo, qhi; split; [exact Q1|unfold A_GOT_mid1; lia]|exact GOT_mid1_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_mid1).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists qlo, qhi; split; [exact Q1|unfold A_GOT_mid2; lia]|exact GOT_mid2_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_mid2).
    - apply (pristine8 P E mem0 PO2 A nu regs mem _ _ HG2); [exists qlo, qhi; split; [exact Q1|unfold A_GOT_hend; lia]|exact GOT_hend_bytes].
    - exact (kcell8 P E mem0 A nu regs mem _ _ HG2 K_hend).
  Qed.

  Lemma SM_TSD_OK : forall A nu regs mem bs, gamma2P A nu regs mem ->
    rdn BSEGS mem (wordZ (vp_tp P - 88)) 8 = Some bs -> bytes_le_to_Z bs = TSD_asan.
  Proof.
    intros A nu regs mem bs HG2 R. rewrite VTP in R. change (TP_asan - 88) with 0x5e4b58 in R.
    pose proof (kcellN A nu regs mem _ _ _ HG2 K_tsd) as K. change (Z.to_nat 8) with 8%nat in K.
    rewrite K in R. injection R as <-. vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma smH_of mem usp fs ctx thr db beg (a2v a3v : word) :
    SM_MCELLS mem ->
    rdn BSEGS mem (wordZ TP_asan) 8 = Some (word_to_le_bytes 8 (wordZ fs)) ->
    rdn BSEGS mem (wordZ TSD_asan) 8 = Some (word_to_le_bytes 8 (wordZ ctx)) -> 0 < ctx -> ctx + 160 <= 2 ^ 64 ->
    rdn BSEGS mem (wordZ (ctx + 152)) 8 = Some (word_to_le_bytes 8 (wordZ thr)) -> 0 < thr -> thr + 64 <= 2 ^ 64 ->
    rdn BSEGS mem (wordZ (thr + 48)) 8 = Some (word_to_le_bytes 8 a2v) ->
    rdn BSEGS mem (wordZ (thr + 56)) 8 = Some (word_to_le_bytes 8 a3v) ->
    rdn BSEGS mem (wordZ (TP_asan + 8)) 8 = Some (word_to_le_bytes 8 (wordZ db)) -> 0 < db -> db + 32 <= 2 ^ 64 ->
    rdn BSEGS mem (wordZ (db + 24)) 8 = Some (word_to_le_bytes 8 (wordZ beg)) -> 0 < beg < 2 ^ 64 ->
    (ctx + 160 <= usp - K208 \/ usp <= ctx + 152) -> (thr + 64 <= usp - K208 \/ usp <= thr + 48) -> (db + 32 <= usp - K208 \/ usp <= db + 24) ->
    rdn BSEGS mem (wordZ (fs + 96)) 1 = Some [Z_to_bv 8 0] ->
    rdn BSEGS mem (wordZ (fs + 88)) 8 = Some (word_to_le_bytes 8 (wordZ 20)) ->
    vp_imgend P <= fs -> off_band fs (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) -> fs + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= 2 ^ 47 -> fs mod 4096 = 0 ->
    (fs + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= usp - K208 \/ usp <= fs) ->
    HIGH_MEM_BEG + K208 <= usp -> usp + 16 <= 2 ^ 64 ->
    (forall a, usp - K208 <= a < usp -> store_ok BSEGS mem (wordZ a) 1 = true) ->
    VBothStackMallocWalk.smH mem usp fs ctx thr db beg a2v a3v.
  Proof.
    intros [TC CC] Cfs Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3 Cdb NZ3 Bdb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl FSimg FSob FShi FSal FSAP U1 U2 JOK.
    pose proof VIMG. unfold K208, off_band, LOW_MEM_TOP, HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
    constructor; unfold VBothStackMallocWalk.fs_band, VBothStackMallocWalk.SM_FRAME, VBothStackMallocWalk.FS_AREA, BothRegionPoisoned.cell, VBothTlsWalk.TP;
      change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
    - lia. - exact JOK. - exact TC. - exact Cctx. - lia. - exact Cthr. - lia. - exact Ca2. - exact Ca3. - exact Cdb. - lia.
    - exact Cbeg. - exact Bbeg. - exact AP1. - exact AP2. - exact AP3. - exact CC. - exact Cfs. - lia. - clear -FSAP; lia. - exact Cgc. - exact Cssl.
  Qed.

  Lemma RUN0 : RUN_spec BSEGS P rom 0 (sm_tgt 0) SM_MCELLS TSD_asan.
  Proof.
    unfold RUN_spec. intros mem usp tp fs tsd ctx thr db beg a2v a3v hint FL p0 regs ra MC Etp Cfs Ctsd Etsd Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3
      Cdb NZ3 Bdb Ndb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl FSimg FSob FShi FSal FSAP U1 U2 JOK Hhint Hflags Hp0 Zp0 Whint Wflag Wframe Wshad Hret H1 H2 H4.
    rewrite VTP in Etp. subst tp tsd.
    pose proof (smH_of mem usp fs ctx thr db beg a2v a3v MC Cfs Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3 Cdb NZ3 Bdb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl
                  FSimg FSob FShi FSal FSAP U1 U2 JOK) as SH.
    unfold K208, HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
    (* [comment removed for export] *)
    rewrite Z.mul_0_r, Z.add_0_r in Hhint.
    assert (Hflags' : forall q, 0 <= q < 16384 -> rdn BSEGS mem (wordZ (fs + 4096 + q)) 1 = Some [FL q]).
    { intros q Hq. destruct (geo0 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Hflags. rewrite G4. exact Hq. }
    assert (Hp0' : 0 <= p0 < 16384) by (rewrite <- (proj2 (proj2 (proj2 (geo0 fs 0)))); exact Hp0).
    assert (Whint' : forall j, 0 <= j < 8 -> store_ok BSEGS mem (wordZ (fs + j)) 1 = true).
    { intros j Hj. replace (fs + j) with (fs + 8 * 0 + j) by lia. apply Whint. exact Hj. }
    assert (Wflag' : forall q, 0 <= q < 16384 -> store_ok BSEGS mem (wordZ (fs + 4096 + q)) 1 = true).
    { intros q Hq. destruct (geo0 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Wflag. rewrite G4. exact Hq. }
    assert (Wframe' : forall q j, 0 <= q < 16384 -> 0 <= j < 64 -> store_ok BSEGS mem (wordZ (fs + 36864 + 64 * q + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo0 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wframe; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    assert (Wshad' : forall q j, 0 <= q < 16384 -> 0 <= j < 8 -> store_ok BSEGS mem (wordZ (SBz + (fs + 36864 + 64 * q) / 8 + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo0 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wshad; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    destruct (VBothStackMallocWalk.sm0_AM mem rom usp fs ctx thr db beg a2v a3v SH regs ra Hret H1 H2 H4 hint FL p0
                Hhint Hflags' (conj Hp0' Zp0) Whint' Wflag' Wframe' Wshad')
      as (i & p & regs' & m' & Hi & Hp & ZP & MS & Q10 & Q2 & Q1 & QK & QM & QG & QS).
    rewrite (VBothStackMallocEff.WR0_eq usp fs hint mem i p) in QM.
    unfold VBothStackMallocWalk.N0, VBothStackMallocWalk.pos in Hi, Hp. unfold VBothStackMallocWalk.ff, VBothStackMallocWalk.FR0 in Q10.
    destruct (geo0 fs p) as (Gfl & Gfr & Gsz & Gn).
    assert (PR : 0 <= p < 16384) by (rewrite Hp; apply Z.mod_pos_bound; lia).
    pose proof (conj (eq_refl 64) (eq_refl 56) : 64 = 64 * (1 + Z.of_nat 0) /\ 56 = 64 - 8) as Xsz.
    assert (Xh : 0 <= 0 /\ 0 + 8 <= 4096) by lia. assert (Xfl : 0 <= p /\ 4096 + p < 36864) by lia.
    assert (Xfs : 0 <= fs /\ (fs + 36864 + 64 * p + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ fs + 36864 + 64 * p + 64 <= 2 ^ 47) by (pose proof VIMG; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG in FSob; lia).
    exists i, p, regs', m', (VBothStackMallocEff.WRG 0 4096 36864 64 56 0 usp fs hint mem i p).
    split; [rewrite Gn; exact Hi|]. split; [rewrite Gn; exact Hp|]. split; [exact ZP|]. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?q _ _) _ =>
        replace (wordZ (sm_tgt 0)) with q by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [rewrite Gfr; exact Q10|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK sm_clob_saved)|].
    split.
    { unfold effect, in_blocks. rewrite Gfl, Gfr, Gsz. change (64 / 8) with 8. change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      - intros y Hy NB. apply (VBothStackMallocEff.WRG_out 0 4096 36864 64 56 0 usp fs hint mem i p Xsz Xh Xfl Xfs y Hy).
        change BothRegionPoisoned.SB with SBz. change (64 / 8) with 8. clear -NB. intros X. apply NB. lia.
      - exact (VBothStackMallocEff.WRG_flag 0 4096 36864 64 56 0 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - exact (VBothStackMallocEff.WRG_24 0 4096 36864 64 56 0 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - replace (fs + 36864 + 64 * p + 64 - 8) with (fs + 36864 + 64 * p + 56) by lia.
        exact (VBothStackMallocEff.WRG_sz 0 4096 36864 64 56 0 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - intros g Hg. exact (VBothStackMallocEff.WRG_zero 0 4096 36864 64 56 0 usp fs hint mem i p Xsz Xh Xfl Xfs g Hg).
      - intros x Hx. exact (VBothStackMallocEff.WRG_keep 0 4096 36864 64 56 0 usp fs hint mem i p x Hx).
      - intros x Hx. exact (VBothStackMallocEff.WRG_sok 0 4096 36864 64 56 0 usp fs hint mem i p x Hx). }
    split; [exact QM|exact QG].
  Qed.
  Lemma RUN1 : RUN_spec BSEGS P rom 1 (sm_tgt 1) SM_MCELLS TSD_asan.
  Proof.
    unfold RUN_spec. intros mem usp tp fs tsd ctx thr db beg a2v a3v hint FL p0 regs ra MC Etp Cfs Ctsd Etsd Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3
      Cdb NZ3 Bdb Ndb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl FSimg FSob FShi FSal FSAP U1 U2 JOK Hhint Hflags Hp0 Zp0 Whint Wflag Wframe Wshad Hret H1 H2 H4.
    rewrite VTP in Etp. subst tp tsd.
    pose proof (smH_of mem usp fs ctx thr db beg a2v a3v MC Cfs Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3 Cdb NZ3 Bdb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl
                  FSimg FSob FShi FSal FSAP U1 U2 JOK) as SH.
    unfold K208, HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
    (* [comment removed for export] *)
    change (fs + 8 * 1) with (fs + 8) in Hhint.
    assert (Hflags' : forall q, 0 <= q < 8192 -> rdn BSEGS mem (wordZ (fs + 20480 + q)) 1 = Some [FL q]).
    { intros q Hq. destruct (geo1 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Hflags. rewrite G4. exact Hq. }
    assert (Hp0' : 0 <= p0 < 8192) by (rewrite <- (proj2 (proj2 (proj2 (geo1 fs 0)))); exact Hp0).
    assert (Whint' : forall j, 8 <= j < 16 -> store_ok BSEGS mem (wordZ (fs + j)) 1 = true).
    { intros j Hj. replace (fs + j) with (fs + 8 * 1 + (j - 8)) by lia. apply Whint. lia. }
    assert (Wflag' : forall q, 0 <= q < 8192 -> store_ok BSEGS mem (wordZ (fs + 20480 + q)) 1 = true).
    { intros q Hq. destruct (geo1 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Wflag. rewrite G4. exact Hq. }
    assert (Wframe' : forall q j, 0 <= q < 8192 -> 0 <= j < 128 -> store_ok BSEGS mem (wordZ (fs + 1085440 + 128 * q + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo1 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wframe; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    assert (Wshad' : forall q j, 0 <= q < 8192 -> 0 <= j < 16 -> store_ok BSEGS mem (wordZ (SBz + (fs + 1085440 + 128 * q) / 8 + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo1 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wshad; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    destruct (VBothStackMallocWalk.sm1_AM mem rom usp fs ctx thr db beg a2v a3v SH regs ra Hret H1 H2 H4 hint FL p0
                Hhint Hflags' (conj Hp0' Zp0) Whint' Wflag' Wframe' Wshad')
      as (i & p & regs' & m' & Hi & Hp & ZP & MS & Q10 & Q2 & Q1 & QK & QM & QG & QS).
    rewrite (VBothStackMallocEff.WR1_eq usp fs hint mem i p) in QM.
    unfold VBothStackMallocWalk.N1, VBothStackMallocWalk.pos1 in Hi, Hp. unfold VBothStackMallocWalk.ff1, VBothStackMallocWalk.FR1 in Q10.
    destruct (geo1 fs p) as (Gfl & Gfr & Gsz & Gn).
    assert (PR : 0 <= p < 8192) by (rewrite Hp; apply Z.mod_pos_bound; lia).
    pose proof (conj (eq_refl 128) (eq_refl 120) : 128 = 64 * (1 + Z.of_nat 1) /\ 120 = 128 - 8) as Xsz.
    assert (Xh : 0 <= 8 /\ 8 + 8 <= 20480) by lia. assert (Xfl : 0 <= p /\ 20480 + p < 1085440) by lia.
    assert (Xfs : 0 <= fs /\ (fs + 1085440 + 128 * p + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ fs + 1085440 + 128 * p + 128 <= 2 ^ 47) by (pose proof VIMG; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG in FSob; lia).
    exists i, p, regs', m', (VBothStackMallocEff.WRG 8 20480 1085440 128 120 1 usp fs hint mem i p).
    split; [rewrite Gn; exact Hi|]. split; [rewrite Gn; exact Hp|]. split; [exact ZP|]. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?q _ _) _ =>
        replace (wordZ (sm_tgt 1)) with q by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [rewrite Gfr; exact Q10|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK sm_clob_saved)|].
    split.
    { unfold effect, in_blocks. rewrite Gfl, Gfr, Gsz. change (128 / 8) with 16. change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      - intros y Hy NB. apply (VBothStackMallocEff.WRG_out 8 20480 1085440 128 120 1 usp fs hint mem i p Xsz Xh Xfl Xfs y Hy).
        change BothRegionPoisoned.SB with SBz. change (128 / 8) with 16. clear -NB. intros X. apply NB. lia.
      - exact (VBothStackMallocEff.WRG_flag 8 20480 1085440 128 120 1 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - exact (VBothStackMallocEff.WRG_24 8 20480 1085440 128 120 1 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - replace (fs + 1085440 + 128 * p + 128 - 8) with (fs + 1085440 + 128 * p + 120) by lia.
        exact (VBothStackMallocEff.WRG_sz 8 20480 1085440 128 120 1 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - intros g Hg. exact (VBothStackMallocEff.WRG_zero 8 20480 1085440 128 120 1 usp fs hint mem i p Xsz Xh Xfl Xfs g Hg).
      - intros x Hx. exact (VBothStackMallocEff.WRG_keep 8 20480 1085440 128 120 1 usp fs hint mem i p x Hx).
      - intros x Hx. exact (VBothStackMallocEff.WRG_sok 8 20480 1085440 128 120 1 usp fs hint mem i p x Hx). }
    split; [exact QM|exact QG].
  Qed.
  Lemma RUN2 : RUN_spec BSEGS P rom 2 (sm_tgt 2) SM_MCELLS TSD_asan.
  Proof.
    unfold RUN_spec. intros mem usp tp fs tsd ctx thr db beg a2v a3v hint FL p0 regs ra MC Etp Cfs Ctsd Etsd Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3
      Cdb NZ3 Bdb Ndb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl FSimg FSob FShi FSal FSAP U1 U2 JOK Hhint Hflags Hp0 Zp0 Whint Wflag Wframe Wshad Hret H1 H2 H4.
    rewrite VTP in Etp. subst tp tsd.
    pose proof (smH_of mem usp fs ctx thr db beg a2v a3v MC Cfs Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3 Cdb NZ3 Bdb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl
                  FSimg FSob FShi FSal FSAP U1 U2 JOK) as SH.
    unfold K208, HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
    (* [comment removed for export] *)
    change (fs + 8 * 2) with (fs + 16) in Hhint.
    assert (Hflags' : forall q, 0 <= q < 4096 -> rdn BSEGS mem (wordZ (fs + 28672 + q)) 1 = Some [FL q]).
    { intros q Hq. destruct (geo2 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Hflags. rewrite G4. exact Hq. }
    assert (Hp0' : 0 <= p0 < 4096) by (rewrite <- (proj2 (proj2 (proj2 (geo2 fs 0)))); exact Hp0).
    assert (Whint' : forall j, 16 <= j < 24 -> store_ok BSEGS mem (wordZ (fs + j)) 1 = true).
    { intros j Hj. replace (fs + j) with (fs + 8 * 2 + (j - 16)) by lia. apply Whint. lia. }
    assert (Wflag' : forall q, 0 <= q < 4096 -> store_ok BSEGS mem (wordZ (fs + 28672 + q)) 1 = true).
    { intros q Hq. destruct (geo2 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Wflag. rewrite G4. exact Hq. }
    assert (Wframe' : forall q j, 0 <= q < 4096 -> 0 <= j < 256 -> store_ok BSEGS mem (wordZ (fs + 2134016 + 256 * q + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo2 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wframe; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    assert (Wshad' : forall q j, 0 <= q < 4096 -> 0 <= j < 32 -> store_ok BSEGS mem (wordZ (SBz + (fs + 2134016 + 256 * q) / 8 + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo2 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wshad; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    destruct (VBothStackMallocWalk.sm2_AM mem rom usp fs ctx thr db beg a2v a3v SH regs ra Hret H1 H2 H4 hint FL p0
                Hhint Hflags' (conj Hp0' Zp0) Whint' Wflag' Wframe' Wshad')
      as (i & p & regs' & m' & Hi & Hp & ZP & MS & Q10 & Q2 & Q1 & QK & QM & QG & QS).
    rewrite (VBothStackMallocEff.WR2_eq usp fs hint mem i p) in QM.
    unfold VBothStackMallocWalk.N2, VBothStackMallocWalk.pos2 in Hi, Hp. unfold VBothStackMallocWalk.ff2, VBothStackMallocWalk.FR2 in Q10.
    destruct (geo2 fs p) as (Gfl & Gfr & Gsz & Gn).
    assert (PR : 0 <= p < 4096) by (rewrite Hp; apply Z.mod_pos_bound; lia).
    pose proof (conj (eq_refl 256) (eq_refl 248) : 256 = 64 * (1 + Z.of_nat 3) /\ 248 = 256 - 8) as Xsz.
    assert (Xh : 0 <= 16 /\ 16 + 8 <= 28672) by lia. assert (Xfl : 0 <= p /\ 28672 + p < 2134016) by lia.
    assert (Xfs : 0 <= fs /\ (fs + 2134016 + 256 * p + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ fs + 2134016 + 256 * p + 256 <= 2 ^ 47) by (pose proof VIMG; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG in FSob; lia).
    exists i, p, regs', m', (VBothStackMallocEff.WRG 16 28672 2134016 256 248 3 usp fs hint mem i p).
    split; [rewrite Gn; exact Hi|]. split; [rewrite Gn; exact Hp|]. split; [exact ZP|]. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?q _ _) _ =>
        replace (wordZ (sm_tgt 2)) with q by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [rewrite Gfr; exact Q10|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK sm_clob_saved)|].
    split.
    { unfold effect, in_blocks. rewrite Gfl, Gfr, Gsz. change (256 / 8) with 32. change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      - intros y Hy NB. apply (VBothStackMallocEff.WRG_out 16 28672 2134016 256 248 3 usp fs hint mem i p Xsz Xh Xfl Xfs y Hy).
        change BothRegionPoisoned.SB with SBz. change (256 / 8) with 32. clear -NB. intros X. apply NB. lia.
      - exact (VBothStackMallocEff.WRG_flag 16 28672 2134016 256 248 3 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - exact (VBothStackMallocEff.WRG_24 16 28672 2134016 256 248 3 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - replace (fs + 2134016 + 256 * p + 256 - 8) with (fs + 2134016 + 256 * p + 248) by lia.
        exact (VBothStackMallocEff.WRG_sz 16 28672 2134016 256 248 3 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - intros g Hg. exact (VBothStackMallocEff.WRG_zero 16 28672 2134016 256 248 3 usp fs hint mem i p Xsz Xh Xfl Xfs g Hg).
      - intros x Hx. exact (VBothStackMallocEff.WRG_keep 16 28672 2134016 256 248 3 usp fs hint mem i p x Hx).
      - intros x Hx. exact (VBothStackMallocEff.WRG_sok 16 28672 2134016 256 248 3 usp fs hint mem i p x Hx). }
    split; [exact QM|exact QG].
  Qed.
  Lemma RUN3 : RUN_spec BSEGS P rom 3 (sm_tgt 3) SM_MCELLS TSD_asan.
  Proof.
    unfold RUN_spec. intros mem usp tp fs tsd ctx thr db beg a2v a3v hint FL p0 regs ra MC Etp Cfs Ctsd Etsd Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3
      Cdb NZ3 Bdb Ndb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl FSimg FSob FShi FSal FSAP U1 U2 JOK Hhint Hflags Hp0 Zp0 Whint Wflag Wframe Wshad Hret H1 H2 H4.
    rewrite VTP in Etp. subst tp tsd.
    pose proof (smH_of mem usp fs ctx thr db beg a2v a3v MC Cfs Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3 Cdb NZ3 Bdb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl
                  FSimg FSob FShi FSal FSAP U1 U2 JOK) as SH.
    unfold K208, HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
    (* [comment removed for export] *)
    change (fs + 8 * 3) with (fs + 24) in Hhint.
    assert (Hflags' : forall q, 0 <= q < 2048 -> rdn BSEGS mem (wordZ (fs + 32768 + q)) 1 = Some [FL q]).
    { intros q Hq. destruct (geo3 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Hflags. rewrite G4. exact Hq. }
    assert (Hp0' : 0 <= p0 < 2048) by (rewrite <- (proj2 (proj2 (proj2 (geo3 fs 0)))); exact Hp0).
    assert (Whint' : forall j, 24 <= j < 32 -> store_ok BSEGS mem (wordZ (fs + j)) 1 = true).
    { intros j Hj. replace (fs + j) with (fs + 8 * 3 + (j - 24)) by lia. apply Whint. lia. }
    assert (Wflag' : forall q, 0 <= q < 2048 -> store_ok BSEGS mem (wordZ (fs + 32768 + q)) 1 = true).
    { intros q Hq. destruct (geo3 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Wflag. rewrite G4. exact Hq. }
    assert (Wframe' : forall q j, 0 <= q < 2048 -> 0 <= j < 512 -> store_ok BSEGS mem (wordZ (fs + 3182592 + 512 * q + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo3 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wframe; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    assert (Wshad' : forall q j, 0 <= q < 2048 -> 0 <= j < 64 -> store_ok BSEGS mem (wordZ (SBz + (fs + 3182592 + 512 * q) / 8 + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo3 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wshad; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    destruct (VBothStackMallocWalk.sm3_AM mem rom usp fs ctx thr db beg a2v a3v SH regs ra Hret H1 H2 H4 hint FL p0
                Hhint Hflags' (conj Hp0' Zp0) Whint' Wflag' Wframe' Wshad')
      as (i & p & regs' & m' & Hi & Hp & ZP & MS & Q10 & Q2 & Q1 & QK & QM & QG & QS).
    rewrite (VBothStackMallocEff.WR3_eq usp fs hint mem i p) in QM.
    unfold VBothStackMallocWalk.N3, VBothStackMallocWalk.pos3 in Hi, Hp. unfold VBothStackMallocWalk.ff3, VBothStackMallocWalk.FR3 in Q10.
    destruct (geo3 fs p) as (Gfl & Gfr & Gsz & Gn).
    assert (PR : 0 <= p < 2048) by (rewrite Hp; apply Z.mod_pos_bound; lia).
    pose proof (conj (eq_refl 512) (eq_refl 504) : 512 = 64 * (1 + Z.of_nat 7) /\ 504 = 512 - 8) as Xsz.
    assert (Xh : 0 <= 24 /\ 24 + 8 <= 32768) by lia. assert (Xfl : 0 <= p /\ 32768 + p < 3182592) by lia.
    assert (Xfs : 0 <= fs /\ (fs + 3182592 + 512 * p + 512 <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ fs + 3182592 + 512 * p + 512 <= 2 ^ 47) by (pose proof VIMG; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG in FSob; lia).
    exists i, p, regs', m', (VBothStackMallocEff.WRG 24 32768 3182592 512 504 7 usp fs hint mem i p).
    split; [rewrite Gn; exact Hi|]. split; [rewrite Gn; exact Hp|]. split; [exact ZP|]. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?q _ _) _ =>
        replace (wordZ (sm_tgt 3)) with q by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [rewrite Gfr; exact Q10|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK sm_clob_saved)|].
    split.
    { unfold effect, in_blocks. rewrite Gfl, Gfr, Gsz. change (512 / 8) with 64. change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      - intros y Hy NB. apply (VBothStackMallocEff.WRG_out 24 32768 3182592 512 504 7 usp fs hint mem i p Xsz Xh Xfl Xfs y Hy).
        change BothRegionPoisoned.SB with SBz. change (512 / 8) with 64. clear -NB. intros X. apply NB. lia.
      - exact (VBothStackMallocEff.WRG_flag 24 32768 3182592 512 504 7 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - exact (VBothStackMallocEff.WRG_24 24 32768 3182592 512 504 7 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - replace (fs + 3182592 + 512 * p + 512 - 8) with (fs + 3182592 + 512 * p + 504) by lia.
        exact (VBothStackMallocEff.WRG_sz 24 32768 3182592 512 504 7 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - intros g Hg. exact (VBothStackMallocEff.WRG_zero 24 32768 3182592 512 504 7 usp fs hint mem i p Xsz Xh Xfl Xfs g Hg).
      - intros x Hx. exact (VBothStackMallocEff.WRG_keep 24 32768 3182592 512 504 7 usp fs hint mem i p x Hx).
      - intros x Hx. exact (VBothStackMallocEff.WRG_sok 24 32768 3182592 512 504 7 usp fs hint mem i p x Hx). }
    split; [exact QM|exact QG].
  Qed.
  Lemma RUN4 : RUN_spec BSEGS P rom 4 (sm_tgt 4) SM_MCELLS TSD_asan.
  Proof.
    unfold RUN_spec. intros mem usp tp fs tsd ctx thr db beg a2v a3v hint FL p0 regs ra MC Etp Cfs Ctsd Etsd Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3
      Cdb NZ3 Bdb Ndb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl FSimg FSob FShi FSal FSAP U1 U2 JOK Hhint Hflags Hp0 Zp0 Whint Wflag Wframe Wshad Hret H1 H2 H4.
    rewrite VTP in Etp. subst tp tsd.
    pose proof (smH_of mem usp fs ctx thr db beg a2v a3v MC Cfs Cctx NZ1 Bctx Cthr NZ2 Bthr Ca2 Ca3 Cdb NZ3 Bdb Cbeg Bbeg AP1 AP2 AP3 Cgc Cssl
                  FSimg FSob FShi FSal FSAP U1 U2 JOK) as SH.
    unfold K208, HIGH_MEM_BEG, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
    (* [comment removed for export] *)
    change (fs + 8 * 4) with (fs + 32) in Hhint.
    assert (Hflags' : forall q, 0 <= q < 1024 -> rdn BSEGS mem (wordZ (fs + 34816 + q)) 1 = Some [FL q]).
    { intros q Hq. destruct (geo4 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Hflags. rewrite G4. exact Hq. }
    assert (Hp0' : 0 <= p0 < 1024) by (rewrite <- (proj2 (proj2 (proj2 (geo4 fs 0)))); exact Hp0).
    assert (Whint' : forall j, 32 <= j < 40 -> store_ok BSEGS mem (wordZ (fs + j)) 1 = true).
    { intros j Hj. replace (fs + j) with (fs + 8 * 4 + (j - 32)) by lia. apply Whint. lia. }
    assert (Wflag' : forall q, 0 <= q < 1024 -> store_ok BSEGS mem (wordZ (fs + 34816 + q)) 1 = true).
    { intros q Hq. destruct (geo4 fs q) as (G1 & _ & _ & G4). rewrite <- G1. apply Wflag. rewrite G4. exact Hq. }
    assert (Wframe' : forall q j, 0 <= q < 1024 -> 0 <= j < 1024 -> store_ok BSEGS mem (wordZ (fs + 4231168 + 1024 * q + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo4 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wframe; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    assert (Wshad' : forall q j, 0 <= q < 1024 -> 0 <= j < 128 -> store_ok BSEGS mem (wordZ (SBz + (fs + 4231168 + 1024 * q) / 8 + j)) 1 = true).
    { intros q j Hq Hj. destruct (geo4 fs q) as (_ & G2 & G3 & G4). rewrite <- G2. apply Wshad; [rewrite G4; exact Hq|rewrite G3; exact Hj]. }
    destruct (VBothStackMallocWalk.sm4_AM mem rom usp fs ctx thr db beg a2v a3v SH regs ra Hret H1 H2 H4 hint FL p0
                Hhint Hflags' (conj Hp0' Zp0) Whint' Wflag' Wframe' Wshad')
      as (i & p & regs' & m' & Hi & Hp & ZP & MS & Q10 & Q2 & Q1 & QK & QM & QG & QS).
    rewrite (VBothStackMallocEff.WR4_eq usp fs hint mem i p) in QM.
    unfold VBothStackMallocWalk.N4, VBothStackMallocWalk.pos4 in Hi, Hp. unfold VBothStackMallocWalk.ff4, VBothStackMallocWalk.FR4 in Q10.
    destruct (geo4 fs p) as (Gfl & Gfr & Gsz & Gn).
    assert (PR : 0 <= p < 1024) by (rewrite Hp; apply Z.mod_pos_bound; lia).
    pose proof (conj (eq_refl 1024) (eq_refl 1016) : 1024 = 64 * (1 + Z.of_nat 15) /\ 1016 = 1024 - 8) as Xsz.
    assert (Xh : 0 <= 32 /\ 32 + 8 <= 34816) by lia. assert (Xfl : 0 <= p /\ 34816 + p < 4231168) by lia.
    assert (Xfs : 0 <= fs /\ (fs + 4231168 + 1024 * p + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ fs + 4231168 + 1024 * p + 1024 <= 2 ^ 47) by (pose proof VIMG; unfold off_band, LOW_MEM_TOP, HIGH_MEM_BEG in FSob; lia).
    exists i, p, regs', m', (VBothStackMallocEff.WRG 32 34816 4231168 1024 1016 15 usp fs hint mem i p).
    split; [rewrite Gn; exact Hi|]. split; [rewrite Gn; exact Hp|]. split; [exact ZP|]. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?q _ _) _ =>
        replace (wordZ (sm_tgt 4)) with q by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [rewrite Gfr; exact Q10|]. split; [exact Q2|]. split; [exact Q1|].
    split; [exact (asan_caller_saved _ regs regs' QK sm_clob_saved)|].
    split.
    { unfold effect, in_blocks. rewrite Gfl, Gfr, Gsz. change (1024 / 8) with 128. change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      - intros y Hy NB. apply (VBothStackMallocEff.WRG_out 32 34816 4231168 1024 1016 15 usp fs hint mem i p Xsz Xh Xfl Xfs y Hy).
        change BothRegionPoisoned.SB with SBz. change (1024 / 8) with 128. clear -NB. intros X. apply NB. lia.
      - exact (VBothStackMallocEff.WRG_flag 32 34816 4231168 1024 1016 15 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - exact (VBothStackMallocEff.WRG_24 32 34816 4231168 1024 1016 15 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - replace (fs + 4231168 + 1024 * p + 1024 - 8) with (fs + 4231168 + 1024 * p + 1016) by lia.
        exact (VBothStackMallocEff.WRG_sz 32 34816 4231168 1024 1016 15 usp fs hint mem i p Xsz Xh Xfl Xfs).
      - intros g Hg. exact (VBothStackMallocEff.WRG_zero 32 34816 4231168 1024 1016 15 usp fs hint mem i p Xsz Xh Xfl Xfs g Hg).
      - intros x Hx. exact (VBothStackMallocEff.WRG_keep 32 34816 4231168 1024 1016 15 usp fs hint mem i p x Hx).
      - intros x Hx. exact (VBothStackMallocEff.WRG_sok 32 34816 4231168 1024 1016 15 usp fs hint mem i p x Hx). }
    split; [exact QM|exact QG].
  Qed.

  (* [comment removed for export] *)
  Theorem stack_malloc_post_asan cid : 0 <= cid <= 4 -> contract_post2 BSEGS P E mem0 rom CI (C_stack_malloc cid) (sm_tgt cid).
  Proof.
    intros Hcid.
    assert (C : cid = 0 \/ cid = 1 \/ cid = 2 \/ cid = 3 \/ cid = 4) by lia.
    destruct C as [->|[->|[->|[->| ->]]]].
    - exact (stack_malloc_post BSEGS P E mem0 rom CI PO2 SHOFF Z_HINTS Z_FLAGS Z_FRAMES Z_FSHAD 0 ltac:(lia) _ SM_MCELLS SM_MCELLS_OK TSD_asan SM_TSD_OK RUN0 CITP ROM_IMG_asan).
    - exact (stack_malloc_post BSEGS P E mem0 rom CI PO2 SHOFF Z_HINTS Z_FLAGS Z_FRAMES Z_FSHAD 1 ltac:(lia) _ SM_MCELLS SM_MCELLS_OK TSD_asan SM_TSD_OK RUN1 CITP ROM_IMG_asan).
    - exact (stack_malloc_post BSEGS P E mem0 rom CI PO2 SHOFF Z_HINTS Z_FLAGS Z_FRAMES Z_FSHAD 2 ltac:(lia) _ SM_MCELLS SM_MCELLS_OK TSD_asan SM_TSD_OK RUN2 CITP ROM_IMG_asan).
    - exact (stack_malloc_post BSEGS P E mem0 rom CI PO2 SHOFF Z_HINTS Z_FLAGS Z_FRAMES Z_FSHAD 3 ltac:(lia) _ SM_MCELLS SM_MCELLS_OK TSD_asan SM_TSD_OK RUN3 CITP ROM_IMG_asan).
    - exact (stack_malloc_post BSEGS P E mem0 rom CI PO2 SHOFF Z_HINTS Z_FLAGS Z_FRAMES Z_FSHAD 4 ltac:(lia) _ SM_MCELLS SM_MCELLS_OK TSD_asan SM_TSD_OK RUN4 CITP ROM_IMG_asan).
  Qed.

  Theorem stack_malloc_dead_asan cid : contract_dead2 BSEGS P E mem0 CI (C_stack_malloc cid).
  Proof. exact (stack_malloc_dead BSEGS P E mem0 CI cid). Qed.
End Contracts.

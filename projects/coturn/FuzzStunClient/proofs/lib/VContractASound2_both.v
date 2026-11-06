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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VState2 VStepMem2 VGamma2 VStepMem2SoundA VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound1_both VContractASound2.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require BothRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require CatSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require VBothMemsetWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma seg_rom_high_asan : forall (a : word), 0x685000 <= bv_unsigned a -> seg_rom BSEGS a = None.
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

Lemma ROM_HI_asan : forall a : word, SBz <= bv_unsigned a -> seg_rom BSEGS a = None.
Proof. intros a Ha. apply seg_rom_high_asan. unfold SBz in Ha. lia. Qed.

(* [comment removed for export] *)
Definition A_GOT_shb : Z := 0xa94b8.     (* [comment removed for export] *)
Definition A_GOT_mid1 : Z := 0xa94c0.    (* [comment removed for export] *)
Definition A_GOT_mid2 : Z := 0xa94c8.    (* [comment removed for export] *)
Definition A_GOT_hend : Z := 0xa94d0.    (* [comment removed for export] *)
Definition A_GOT_ri : Z := 0xaa020.      (* [comment removed for export] *)
Definition A_shb : Z := 0xb1bb8.
Definition A_mid1 : Z := 0xb28a8.
Definition A_mid2 : Z := 0xb28b0.
Definition A_hend : Z := 0xb28a0.
Definition A_ri : Z := 0xb2899.

Lemma GOT_shb_bytes : rdn BSEGS (fun _ => None) (wordZ A_GOT_shb) 8 = Some (word_to_le_bytes 8 (wordZ A_shb)).
Proof. vm_refl_bv. Qed.
Lemma GOT_mid1_bytes : rdn BSEGS (fun _ => None) (wordZ A_GOT_mid1) 8 = Some (word_to_le_bytes 8 (wordZ A_mid1)).
Proof. vm_refl_bv. Qed.
Lemma GOT_mid2_bytes : rdn BSEGS (fun _ => None) (wordZ A_GOT_mid2) 8 = Some (word_to_le_bytes 8 (wordZ A_mid2)).
Proof. vm_refl_bv. Qed.
Lemma GOT_hend_bytes : rdn BSEGS (fun _ => None) (wordZ A_GOT_hend) 8 = Some (word_to_le_bytes 8 (wordZ A_hend)).
Proof. vm_refl_bv. Qed.
Lemma GOT_ri_bytes : rdn BSEGS (fun _ => None) (wordZ A_GOT_ri) 8 = Some (word_to_le_bytes 8 (wordZ A_ri)).
Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Contracts.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO2 : params_ok2 BSEGS P.
  Hypothesis SHOFF : vp_shoff P = SBz.
  Hypothesis FSLEN : forall len ssl, vp_fs P = Some (len, ssl) -> FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL < len.
  (* [comment removed for export] *)
  Hypothesis GOT1_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_shb /\ A_GOT_hend + 8 <= phi.
  Hypothesis GOT2_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_ri /\ A_GOT_ri + 8 <= phi.
  Hypothesis CELL_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_memset /\ A_CELL_memset + 8 <= phi.
  (* [comment removed for export] *)
  Hypothesis K_shb : In (A_shb, (8, SBz)) (vp_kcells P).
  Hypothesis K_mid1 : In (A_mid1, (8, 0)) (vp_kcells P).
  Hypothesis K_mid2 : In (A_mid2, (8, 0)) (vp_kcells P).
  Hypothesis K_hend : In (A_hend, (8, 2 ^ 47 - 1)) (vp_kcells P).
  Hypothesis K_ri : In (A_ri, (1, 1)) (vp_kcells P).

  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 BSEGS P E mem0).

  (* [comment removed for export] *)
  Definition MCELLS_asan (m : word -> option byte) : Prop := VBothMemsetWalk.am_cells m.

  Lemma kcell8 A nu regs mem a v :
    gamma2P A nu regs mem -> In (a, (8, v)) (vp_kcells P) ->
    rdn BSEGS mem (wordZ a) 8 = Some (word_to_le_bytes 8 (wordZ v)).
  Proof.
    intros HG2 Hin. pose proof HG2 as (_ & _ & (KC & _) & _).
    destruct (KC _ _ _ Hin) as (_ & _ & _ & bs & R & V). change (Z.to_nat 8) with 8%nat in R.
    rewrite R. f_equal. unfold wordZ. eapply rdn8_word; [exact R|exact V].
  Qed.

  Lemma pristine8 A nu regs mem a c :
    gamma2P A nu regs mem ->
    (exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= a /\ a + 8 <= phi) ->
    rdn BSEGS (fun _ => None) (wordZ a) 8 = Some (word_to_le_bytes 8 (wordZ c)) ->
    rdn BSEGS mem (wordZ a) 8 = Some (word_to_le_bytes 8 (wordZ c)).
  Proof.
    intros HG2 HP HB. rewrite (rdn_pristine2 BSEGS P E mem0 PO2 0 ltac:(lia) mem A nu regs a 8 HG2); [exact HB|].
    destruct HP as [plo [phi X]]. exists plo, phi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. exact X.
  Qed.

  Lemma MCELLS_OK_asan : forall A nu regs mem, gamma2P A nu regs mem -> MCELLS_asan mem.
  Proof.
    intros A nu regs mem HG2. unfold MCELLS_asan, VBothMemsetWalk.am_cells.
    unfold BothRegionPoisoned.cells, BothRegionPoisoned.cell.
    change (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec.rdn) with rdn.
    change BothRegionPoisoned.SB with SBz. change BothRegionPoisoned.kHighEnd with (2 ^ 47 - 1).
    fold (wordZ 0xa94b8) (wordZ 0xb1bb8) (wordZ 0xa94c0) (wordZ 0xb28a8) (wordZ 0xa94c8) (wordZ 0xb28b0)
         (wordZ 0xa94d0) (wordZ 0xb28a0) (wordZ 0xaa020) (wordZ 0xb2899) (wordZ 0xab330)
         (wordZ SBz) (wordZ 0) (wordZ (2 ^ 47 - 1)) (wordZ 0xa2bec).
    destruct GOT1_PRISTINE as (plo & phi & G1 & G2 & G3). unfold A_GOT_shb, A_GOT_hend in G2, G3.
    repeat split.
    - apply (pristine8 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_shb_bytes].
    - exact (kcell8 A nu regs mem _ _ HG2 K_shb).
    - apply (pristine8 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_mid1_bytes].
    - exact (kcell8 A nu regs mem _ _ HG2 K_mid1).
    - apply (pristine8 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_mid2_bytes].
    - exact (kcell8 A nu regs mem _ _ HG2 K_mid2).
    - apply (pristine8 A nu regs mem _ _ HG2); [exists plo, phi; split; [exact G1|lia]|exact GOT_hend_bytes].
    - exact (kcell8 A nu regs mem _ _ HG2 K_hend).
    - apply (pristine8 A nu regs mem _ _ HG2); [exact GOT2_PRISTINE|exact GOT_ri_bytes].
    - pose proof HG2 as (_ & _ & (KC & _) & _).
      destruct (KC _ _ _ K_ri) as (_ & _ & _ & bs & R & V). change (Z.to_nat 1) with 1%nat in R.
      pose proof (rdn_length _ _ _ _ _ R) as L. destruct bs as [|b [|]]; try discriminate.
      unfold A_ri in R. rewrite R. do 2 f_equal. apply bv_eq. cbn [bytes_le_to_Z] in V. rewrite Z.shiftl_0_l, Z.lor_0_r in V.
      rewrite V. reflexivity.
    - apply (pristine8 A nu regs mem _ _ HG2); [exact CELL_PRISTINE|exact CELL_BYTES_asan].
  Qed.

  (* [comment removed for export] *)
  Lemma RUN_asan : forall mem (d c n usp : Z) regs (ra : word),
    MCELLS_asan mem ->
    0 <= n <= 2 ^ 40 -> 0 <= d -> 0 <= c < 2 ^ 64 -> d + n < 2 ^ 64 ->
    (0 < n -> band_ok d n) ->
    SBz + 2208 <= usp < 2 ^ 64 ->
    (n = 0 \/ usp <= d \/ d + n <= usp - JUNK) ->
    (0 < n -> SBz + (d + n - 1) / 8 + 8 < usp - JUNK) ->
    (forall g, 0 < n -> d / 8 <= g < (d + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0)) ->
    (0 < n -> exists b1 : byte, mem (wordZ (SBz + (d + n - 1) / 8)) = Some b1
                               /\ (bv_unsigned b1 = 0 \/ (d + n - 1) mod 8 < bv_unsigned b1 < 8)) ->
    (0 < n -> exists w : word, rdn BSEGS mem (wordZ ((SBz + d / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)) ->
    (0 < n -> exists w : word, rdn BSEGS mem (wordZ ((SBz + (d + n - 1) / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w)) ->
    (forall j, 0 <= j < n -> store_ok BSEGS mem (wordZ (d + j)) 1 = true) ->
    (forall a, usp - JUNK <= a < usp -> store_ok BSEGS mem (wordZ a) 1 = true) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ usp ->
    getr regs 10%bv = wordZ d -> getr regs 11%bv = wordZ c -> getr regs 12%bv = wordZ n ->
    exists regs' m',
      msteps BSEGS (mkst regs (wordZ 0x542bc) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10%bv = wordZ d /\ getr regs' 2%bv = wordZ usp /\ getr regs' 1%bv = ra
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r)
      /\ (forall x : word, (bv_unsigned x < usp - JUNK \/ usp <= bv_unsigned x) ->
            m' x = wbytes mem (wordZ d) (repeat (Z_to_bv 8 c) (Z.to_nat n)) x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Proof.
    intros mem d c n usp regs ra MC Hn Hd Hc Hdn Hrng Husp Hdst Hshd Hzero Hlast Hw1 Hw2 Hdok Hstk Hret H1 H2 H10 H11 H12.
    assert (AH : VBothMemsetWalk.amH mem d c n usp).
    { constructor; unfold VBothMemsetWalk.AM_FRAME, BothRegionPoisoned.SB, BothRegionPoisoned.kLowEnd,
        BothRegionPoisoned.kHighBeg, BothRegionPoisoned.kHighEnd; unfold JUNK, SBz, band_ok, LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END in *;
        try exact MC; try (intros; lia); try lia.
      - exact Hzero.
      - exact Hlast.
      - exact Hw1.
      - exact Hw2.
      - exact Hdok.
      - exact Hstk. }
    destruct (VBothMemsetWalk.asan_memset_run mem rom d c n usp AH regs ra Hret H1 H2 H10 H11 H12)
      as (regs' & m' & MS & Q10 & Q2 & Q1 & QK & QM & QG).
    exists regs', m'. split.
    { lazymatch type of MS with OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim.msteps _ (_ _ ?p _ _) _ =>
        replace (wordZ 0x542bc) with p by bveq end.
      apply asan_msteps_bridge. exact MS. }
    split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [|split; [exact QM|exact QG]].
    intros r Hr0 Hcs. apply QK. unfold VBothMemsetWalk.am_clob.
    assert (NE : forall k : reg, In (bv_unsigned k) CALLER_SAVED -> bv_eqb r k = false).
    { intros k Hk. apply bv_eqb_neq. intros ->. exact (Hcs Hk). }
    rewrite !NE by (unfold CALLER_SAVED; cbn; auto 20). reflexivity.
  Qed.

  Theorem asan_memset_post_asan : contract_post2 BSEGS P E mem0 rom CI C_asan_memset 0x542bc.
  Proof.
    exact (asan_memset_post BSEGS P E mem0 rom CI PO2 SHOFF ROM_HI_asan 0x542bc MCELLS_asan MCELLS_OK_asan FSLEN RUN_asan).
  Qed.

  Theorem asan_memset_dead_asan : contract_dead2 BSEGS P E mem0 CI C_asan_memset.
  Proof. exact (asan_memset_dead BSEGS P E mem0 CI PO2). Qed.
End Contracts.

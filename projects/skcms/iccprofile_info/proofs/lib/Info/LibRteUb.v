(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibWP1Spec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

#[local] Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

Section RTE.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret c data t8 t16 : word) (n len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hc : getr regs 10 = c.
  Hypothesis Hcal : (bv_unsigned c mod 8 = 0)%Z.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hc24 : (bv_unsigned c + 24 <= 2 ^ 64)%Z.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdata : (bv_unsigned data + len < 2 ^ 64)%Z.
  Hypothesis Hblob : forall i, (0 <= i < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  Hypothesis Hcurve : n = 0%Z \/
     ((2 <= n <= 2 ^ 24)%Z
      /\ (bv_unsigned t8 <> 0%Z -> bv_unsigned data <= bv_unsigned t8 /\ bv_unsigned t8 + n <= bv_unsigned data + len)%Z
      /\ (bv_unsigned t16 <> 0%Z -> bv_unsigned data <= bv_unsigned t16 /\ bv_unsigned t16 + 2 * n <= bv_unsigned data + len)%Z).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 n; t8; t16; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  Definition kn0 : list kentry :=
    [KAlign (EVar 10) 8;
     KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 8) 8 (EVar 65); KWord (SA (EVar 10) 16) 8 (EVar 66);
     KBlobD (SA (EVar 67) 0) (EVar 68) 0].

  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using FPI Hblob Hbs Hc Hc24 Hcal Hdata Hlen Hn Ht16 Ht8 rom.
    unfold kn0. pose proof (u64_range c). pose proof (u64_range data).
    constructor; [apply kalign_intro; [lia | cbn; rewrite Hc; exact Hcal]|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    - eapply (kword_intro SEGS E mem (EVar 10) c 0 4 (EVar 64) (Z_to_bv 64 n)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 8 8 (EVar 65) t8); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 16 8 (EVar 66) t16); cbn; try lia; auto.
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros i Hi. rewrite Z.add_0_r. apply Hblob. exact Hi.
  Qed.

  Ltac post :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?FPI ?R _ ?M _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E _ R, HF : fregs_ok _ _ (@fp_regs FPI), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr) |- _ =>
        exists FPI, R, M; split; [| split; [|split; [|reflexivity]]]; unfold regs_kept, fregs_kept;
        [ regv HR (1%bv:reg); rewrite_getr; reflexivity
        | eapply (regs_same_on E sr0 _ regs R abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
        | eapply (fregs_same_on E sfr0 _ fr _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ] ]
      end
    end.

  Theorem rte_run_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x131b8) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ mem' = mem.
  Proof using E Hblob Hbs Hc Hc24 Hcal Hcurve Hdata Hlen Hn Hra Hret Ht16 Ht8.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\ mem' = mem).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range t8). pose proof (u64_range t16). pose proof (u64_range data).
    destruct Hcurve as [Hn0 | (Hnr & H8 & H16)].
    - (* [comment removed for export] *)
      assert (HK : know_ok SEGS E mem (KRange (EVar 64) 0 0 :: kn0)).
      { constructor; [apply krange_intro; cbn; subst n; rewrite u_small by lia; lia | apply kn0_ok]. }
      run_fp 100%nat (@nil Z) noscr false. fin_ret. post.
    - (* [comment removed for export] *)
      assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 2 (2^24))).
      { apply krange_intro; cbn; rewrite u_small by lia; lia. }
      assert (Kcase : forall (i : nat) (t : word) (z : {bv_unsigned t = 0%Z} + {bv_unsigned t <> 0%Z}),
                edenot E (EVar i) = t ->
                kentry_ok SEGS E mem (if z then KRange (EVar i) 0 0 else KRange (EVar i) 1 (2^64 - 1))).
      { intros i t z Hi. pose proof (u64_range t). destruct z; apply krange_intro; rewrite Hi; lia. }
      pose proof (Kcase 65%nat t8 (Z.eq_dec (bv_unsigned t8) 0) eq_refl) as K65.
      pose proof (Kcase 66%nat t16 (Z.eq_dec (bv_unsigned t16) 0) eq_refl) as K66.
      assert (HK : know_ok SEGS E mem
               (KRange (EVar 64) 2 (2^24)
                :: (if Z.eq_dec (bv_unsigned t8) 0 then KRange (EVar 65) 0 0 else KRange (EVar 65) 1 (2^64 - 1))
                :: (if Z.eq_dec (bv_unsigned t16) 0 then KRange (EVar 66) 0 0 else KRange (EVar 66) 1 (2^64 - 1))
                :: kn0)).
      { constructor; [exact K64|]. constructor; [exact K65|]. constructor; [exact K66|]. apply kn0_ok. }
      clear K64 K65 K66 Kcase.
      destruct (Z.eq_dec (bv_unsigned t8) 0) as [Ht8z | Ht8nz];
        [| specialize (H8 Ht8nz)];
      destruct (Z.eq_dec (bv_unsigned t16) 0) as [Ht16z | Ht16nz];
        try specialize (H16 Ht16nz);
      run_fp 100%nat (@nil Z) (dirs [false; false]) false; fin_ret; post.
  Qed.
End RTE.

Theorem rte_Ub_ok : rte_contract SEGS 0x131b8.
Proof.
  intros data len bs c FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hc & (Hlen & Hbs & Hdnz & Hdata & Hblob) & Hcurve & Hal & Hc32).
  destruct Hcurve as (n & t8 & t16 & [Hn32 Hn] & H8c & H16c & Hcv).
  unfold cell64, cell in H8c, H16c. unfold cell in Hn.
  destruct (rte_run_ok FPI regs mem rom ret c data t8 t16 n len bs Hra Hret Hc Hal
              ltac:(rewrite Z.add_0_r; exact Hn) H8c H16c ltac:(lia) Hlen Hbs ltac:(lia) Hblob
              ltac:(destruct Hcv as [Hz | (Hr & Hnz & H8 & H16)]; [left; exact Hz | right];
                    split; [exact Hr|]; split;
                    [ intros Hz; destruct (H8 Hz) as (A & _ & B); split; [exact A|exact B]
                    | intros Hz; destruct (H16 Hz) as (A & _ & B); split; [exact A|exact B] ]))
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hmem).
  exists FPI', regs', mem'. unfold rte_post. auto.
Qed.

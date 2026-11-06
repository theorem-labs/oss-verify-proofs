(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare StepTac ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefStrLib UbTolower UbMemset UbMemcmp UbMemchr UbStrcmp UbStrlen UbStrncpy UbMemcpyWBase UbMemcpyW.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VContract VContractSound VContractSound2 VContractSound3 VContractSound4 VContractTab VContractSound_src0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Abbreviation SEGSU := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition RC_LO_ub : Z := 0x10580.
Definition RC_HI_ub : Z := 0x105a0.

Section Ub.
  Variable rom : word -> option byte.

  Lemma TOLOWER_ub : forall regs mem (c : Z) (ret : word),
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = Z_to_bv 64 c -> 0 <= c <= 255 ->
    exists regs',
      msteps SEGSU (mkst regs (wordZ 0x1b708) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10%bv = Z_to_bv 64 (tolower_Z c)
      /\ regs_agree (fun r => In r tolower_clob) regs regs'.
  Proof.
    intros. rewrite (wordZ_lit (0x1b708 : word)) by reflexivity. eapply UbTolower.ref_tolower_byte; eauto.
  Qed.

  Lemma MEMSET_ub : forall mem (d : word) (n : Z) regs (ret : word),
    0 <= n -> bv_unsigned d + n < 2 ^ 64 -> store_ok SEGSU mem d (Z.to_nat n) = true ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = d -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGSU (mkst regs (wordZ 0x23eec) mem rom) (mkst regs' ret (wbytes mem d (zeros (Z.to_nat n))) rom)
      /\ keeps regs regs'.
  Proof.
    intros. rewrite (wordZ_lit (0x23eec : word)) by reflexivity. eapply UbMemset.ref_memset0_keeps; eauto.
  Qed.

  Lemma MEMCPY_ub : forall mem (dst src : word) (n : Z) regs (ret : word),
    0 <= n < 2 ^ 64 ->
    (forall i, 0 <= i < n -> exists b, rdn SEGSU mem (at_ src i) 1 = Some [b]) ->
    store_ok SEGSU mem dst (Z.to_nat n) = true ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs' (bs' : list byte),
      length bs' = Z.to_nat n
      /\ msteps SEGSU (mkst regs (wordZ 0x23ae8) mem rom) (mkst regs' ret (wbytes mem dst bs') rom)
      /\ keeps regs regs'.
  Proof.
    intros mem dst src n regs ret Hn Hsrc Hdst Hs Hd Hret H1 H10 H11 H12.
    rewrite (wordZ_lit (0x23ae8 : word)) by reflexivity.
    apply (UbMemcpyW.ref_memcpy_weak mem dst src n rom regs ret); auto. constructor; auto.
  Qed.

  Lemma cmp_of_mc_postU (la lb : list byte) (n : nat) regs' (i : nat) :
    mc_post n la lb regs' i -> exists dlt, - 255 <= dlt <= 255 /\ getr regs' 10%bv = Z_to_bv 64 dlt.
  Proof.
    intros (Hi & Hpre & [[Ei R]|(Hlt & Hne & R)]).
    - exists 0. split; [lia|exact R].
    - exists (bv_unsigned (nth i la (Z_to_bv 8 0)) - bv_unsigned (nth i lb (Z_to_bv 8 0))).
      pose proof (u8_range (nth i la (Z_to_bv 8 0))). pose proof (u8_range (nth i lb (Z_to_bv 8 0))).
      split; [lia|]. rewrite R. unfold v_sub, LBv. rewrite !u_Z2bv by lia. reflexivity.
  Qed.

  Lemma memcmp_clob_CSU : forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) memcmp_clob = true.
  Proof. reflexivity. Qed.
  Lemma memcmp_clob_raU : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) memcmp_clob = false.
  Proof. reflexivity. Qed.

  Lemma MEMCMP_ub : cmp_spec SEGSU rom 0x23ab8.
  Proof.
    intros mem l r n la lb regs ret Hla Hlb Hn Hl Hr Hret H1 H10 H11 H12.
    destruct (UbMemcmp.ref_memcmp mem rom l r n la lb Hla Hlb Hn Hr regs ret Hret H1 H10 H11 H12) as (regs' & i & RUN & AG & POST).
    destruct (cmp_of_mc_postU la lb n regs' i POST) as [dlt [Hd R10]].
    exists regs', dlt. rewrite (wordZ_lit (0x23ab8 : word)) by reflexivity.
    split; [exact RUN|]. split; [exact (regs_agree_CS memcmp_clob regs regs' memcmp_clob_CSU AG)|].
    split; [exact (regs_agree_ra memcmp_clob regs regs' memcmp_clob_raU AG)|]. split; [exact Hd|exact R10].
  Qed.

  Lemma BCMP_ub : cmp_spec SEGSU rom 0x239e8.
  Proof.
    intros mem l r n la lb regs ret Hla Hlb Hn Hl Hr Hret H1 H10 H11 H12.
    destruct (UbMemcmp.ref_bcmp mem rom l r n la lb Hla Hlb Hn Hr regs ret Hret H1 H10 H11 H12) as (regs' & i & RUN & AG & POST).
    destruct (cmp_of_mc_postU la lb n regs' i POST) as [dlt [Hd R10]].
    exists regs', dlt. rewrite (wordZ_lit (0x239e8 : word)) by reflexivity.
    split; [exact RUN|]. split; [exact (regs_agree_CS memcmp_clob regs regs' memcmp_clob_CSU AG)|].
    split; [exact (regs_agree_ra memcmp_clob regs regs' memcmp_clob_raU AG)|]. split; [exact Hd|exact R10].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma strcmp_clob_CSU : forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) strcmp_clob = true.
  Proof. reflexivity. Qed.
  Lemma strcmp_clob_raU : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) strcmp_clob = false.
  Proof. reflexivity. Qed.

  Lemma STRCMP_ub : forall mem (l r : word) (K : nat) (la lb : list byte) regs (ret : word),
    rdn SEGSU mem l (S K) = Some la -> rdn SEGSU mem r (S K) = Some lb ->
    bv_unsigned (nth K lb (Z_to_bv 8 0)) = 0 ->
    bv_unsigned l + Z.of_nat K < 2 ^ 64 -> bv_unsigned r + Z.of_nat K < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = l -> getr regs 11%bv = r ->
    exists regs' (dlt : Z),
      msteps SEGSU (mkst regs (wordZ 0x23fe4) mem rom) (mkst regs' ret mem rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv
      /\ - 255 <= dlt <= 255 /\ getr regs' 10%bv = Z_to_bv 64 dlt.
  Proof.
    intros mem l r K la lb regs ret Hla Hlb HK Hl Hr Hret H1 H10 H11.
    destruct (UbStrcmp.ref_strcmp mem rom l r K la lb Hla Hlb HK regs ret Hret H1 H10 H11) as (regs' & i & RUN & AG & _ & _ & _ & R10).
    exists regs', (bv_unsigned (nth i la (Z_to_bv 8 0)) - bv_unsigned (nth i lb (Z_to_bv 8 0))).
    rewrite (wordZ_lit (0x23fe4 : word)) by reflexivity.
    split; [exact RUN|]. split; [exact (regs_agree_CS strcmp_clob regs regs' strcmp_clob_CSU AG)|].
    split; [exact (regs_agree_ra strcmp_clob regs regs' strcmp_clob_raU AG)|].
    pose proof (u8_range (nth i la (Z_to_bv 8 0))). pose proof (u8_range (nth i lb (Z_to_bv 8 0))).
    split; [lia|]. rewrite R10. unfold v_sub, LBv. rewrite !u_Z2bv by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma strlen_clob_CSU : forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) strlen_clob = true.
  Proof. reflexivity. Qed.
  Lemma strlen_clob_raU : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) strlen_clob = false.
  Proof. reflexivity. Qed.

  Lemma STRLEN_ub : forall mem (s : word) (buf : list byte) (K : Z) regs (ret : word),
    rdn SEGSU mem s (length buf) = Some buf -> 0 <= K -> K + 8 <= Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 -> bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall i, RC_LO_ub <= i < RC_HI_ub -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s ->
    exists regs' (i : Z),
      msteps SEGSU (mkst regs (wordZ 0x2401c) mem rom) (mkst regs' ret mem rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv
      /\ 0 <= i <= K /\ bv_unsigned (nth (Z.to_nat i) buf (Z_to_bv 8 0)) = 0
      /\ (forall j, 0 <= j < i -> bv_unsigned (nth (Z.to_nat j) buf (Z_to_bv 8 0)) <> 0)
      /\ getr regs' 10%bv = Z_to_bv 64 i.
  Proof.
    intros mem s buf K regs ret Hbuf HK0 HK8 Hnw Hz Hro Hret H1 H10.
    pose proof (UbStrlen.slH_of_window mem s buf K Hbuf HK0 HK8 Hnw Hz Hro) as HOK.
    destruct (UbStrlen.ref_strlen mem s buf K rom HOK regs ret Hret H1 H10) as (regs' & i & RUN & AG & Hi & Zi & NZ & R10).
    exists regs', i. rewrite (wordZ_lit (0x2401c : word)) by reflexivity.
    split; [exact RUN|]. split; [exact (regs_agree_CS strlen_clob regs regs' strlen_clob_CSU AG)|].
    split; [exact (regs_agree_ra strlen_clob regs regs' strlen_clob_raU AG)|].
    split; [exact Hi|]. split; [exact Zi|]. split; [exact NZ|exact R10].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma strncpy_clob_CSU : forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) strncpy_clob = true.
  Proof. reflexivity. Qed.
  Lemma strncpy_clob_raU : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) strncpy_clob = false.
  Proof. reflexivity. Qed.
  Lemma strncpy_clob_a0U : existsb (fun r : reg => Z.eqb (bv_unsigned r) (bv_unsigned (10%bv : reg))) strncpy_clob = false.
  Proof. reflexivity. Qed.

  Lemma STRNCPY_ub : forall mem (d s sp : word) (n : Z) (src : list byte) regs (ret : word),
    rdn SEGSU mem s (length src) = Some src ->
    (n <= Z.of_nat (length src) \/
     exists K, 0 <= K < Z.of_nat (length src) /\ bv_unsigned (nth (Z.to_nat K) src (Z_to_bv 8 0)) = 0 /\ K + 8 <= Z.of_nat (length src)) ->
    store_ok SEGSU mem d (Z.to_nat n) = true -> 0 <= n ->
    bv_unsigned s + Z.of_nat (length src) < 2 ^ 64 -> bv_unsigned d + n < 2 ^ 64 ->
    (bv_unsigned d + n <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length src) <= bv_unsigned d) ->
    (forall i, RC_LO_ub <= i < RC_HI_ub -> mem (Z_to_bv 64 i) = None) ->
    (RC_HI_ub <= bv_unsigned d \/ bv_unsigned d + n <= RC_LO_ub) ->
    store_ok SEGSU mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
    RC_HI_ub <= bv_unsigned sp - 32 ->
    (bv_unsigned sp <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length src) <= bv_unsigned sp - 32) ->
    (bv_unsigned sp <= bv_unsigned d \/ bv_unsigned d + n <= bv_unsigned sp - 32) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
    getr regs 10%bv = d -> getr regs 11%bv = s -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs' mem',
      msteps SEGSU (mkst regs (wordZ 0x240ac) mem rom) (mkst regs' ret mem' rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv /\ getr regs' 10%bv = getr regs 10%bv
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32); (d, n)].
  Proof.
    intros mem d s sp n src regs ret Hsrc Hroom Hdst Hn Hnws Hnwd Hdisj Hro Hdro Hstk Hspro Hsps Hspd Hret H1 H2 H10 H11 H12.
    assert (Hroom' : n <= Z.of_nat (length src) \/
                     exists K, 0 <= K < Z.of_nat (length src) /\ bv_unsigned (nth (Z.to_nat K) src (Z_to_bv 8 0)) = 0 /\
                               UbStrlen.strlen_span (bv_unsigned s) K <= Z.of_nat (length src)).
    { destruct Hroom as [Hle|[K (HK1&HK2&HK3)]]; [left; exact Hle|right]. exists K.
      split; [exact HK1|]. split; [exact HK2|].
      pose proof (u64_range s). pose proof (UbStrlen.strlen_span_le (bv_unsigned s) K ltac:(lia) ltac:(lia)). lia. }
    assert (HOK : UbStrncpy.sncH mem d s sp n src).
    { constructor; try assumption; unfold RC_LO_ub, RC_HI_ub in *; lia. }
    destruct (UbStrncpy.ref_strncpy mem d s sp n src rom regs ret HOK Hret H1 H2 H10 H11 H12) as (regs' & mem' & m & RUN & AG & _ & _ & _ & FM).
    exists regs', mem'. rewrite (wordZ_lit (0x240ac : word)) by reflexivity.
    split; [exact RUN|]. split; [exact (regs_agree_CS strncpy_clob regs regs' strncpy_clob_CSU AG)|].
    split; [exact (regs_agree_ra strncpy_clob regs regs' strncpy_clob_raU AG)|].
    split; [exact (regs_agree_notin strncpy_clob regs regs' 10%bv strncpy_clob_a0U AG)|exact FM].
  Qed.
End Ub.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition expected_ub : list (Z * contract) :=
  [(0x23ae8, C_memcpy); (0x23eec, C_memset); (0x2401c, C_strlen); (0x23fe4, C_strcmp); (0x240ac, C_strncpy);
   (0x239e8, C_bcmp); (0x23ab8, C_memcmp); (0x23938, C_strtoul); (0x1b708, C_tolower)].

(* [comment removed for export] *)
Definition contracts_check_ub (P : vparams) : bool :=
  in_ranges (vp_pristine P) RC_LO_ub (RC_HI_ub - RC_LO_ub).

Theorem ctab_sound_ub_nostrtoul (P : vparams) (E : venv) (mem0 rom : word -> option byte) (CI : cimg) (ctab : pmap contract) :
  params_ok SEGSU P -> contracts_check_ub P = true -> ctab_check expected_ub ctab = true ->
  (contract_post SEGSU P E mem0 rom CI C_strtoul 0x23938 /\ contract_dead SEGSU P E mem0 CI C_strtoul) ->
  ctab_sound SEGSU P E mem0 rom CI ctab.
Proof.
  intros PO CC TC ST. apply (ctab_sound_of_check SEGSU P E mem0 rom CI expected_ub ctab TC).
  unfold contracts_check_ub in CC. destruct (in_ranges_sound _ _ _ CC) as [plo [phi (Hin&Q1&Q2)]].
  assert (RC : exists plo phi, In (plo, phi) (vp_pristine P) /\ plo <= RC_LO_ub /\ RC_HI_ub <= phi)
    by (exists plo, phi; repeat split; auto; lia).
  assert (Hrc : RC_LO_ub <= RC_HI_ub) by (cbv; discriminate).
  unfold expected_ub.
  repeat apply Forall_cons; try apply Forall_nil; unfold entry_ok; cbn [fst snd].
  - split; [exact (memcpy_post SEGSU P E mem0 rom CI PO _ (MEMCPY_ub rom))|exact (memcpy_dead SEGSU P E mem0 CI PO)].
  - split; [exact (memset_post SEGSU P E mem0 rom CI PO _ (MEMSET_ub rom))|exact (memset_dead SEGSU P E mem0 CI)].
  - split; [exact (strlen_post SEGSU P E mem0 rom CI PO _ _ _ RC (STRLEN_ub rom))|exact (strlen_dead SEGSU P E mem0 CI PO)].
  - split; [exact (strcmp_post SEGSU P E mem0 rom CI PO _ (STRCMP_ub rom))|exact (strcmp_dead SEGSU P E mem0 CI PO)].
  - split; [exact (strncpy_post SEGSU P E mem0 rom CI PO _ _ _ RC (STRNCPY_ub rom) Hrc)|exact (strncpy_dead SEGSU P E mem0 CI PO)].
  - split; [exact (bcmp_post SEGSU P E mem0 rom CI PO _ (BCMP_ub rom))|exact (bcmp_dead SEGSU P E mem0 CI PO)].
  - split; [exact (memcmp_post SEGSU P E mem0 rom CI PO _ (MEMCMP_ub rom))|exact (memcmp_dead SEGSU P E mem0 CI PO)].
  - exact ST.
  - split; [exact (tolower_post SEGSU P E mem0 rom CI PO _ (TOLOWER_ub rom))|exact (tolower_dead SEGSU P E mem0 CI)].
Qed.

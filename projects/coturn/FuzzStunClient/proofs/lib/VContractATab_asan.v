(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FContract.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLinalg VState VLogic VGamma VStepMem VStepMemSound VCert VItab VContract VDriver VContractTab VState2 VStepMem2 VCert2 VContract2 VDriver2 VGamma2 VStepMem2SoundA VContractA VContract2Iface FPA_asan VGenv_asan VContractASound1_asan VContractASound2 VContractASound2_asan VContractASound3 VContractASound3_asan VContractASound4_asan VContractASound5_asan VContractASound6_asan VContractASound7_asan VContractASound8_asan VContractASoundV1_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition contract2_eqb (a b : contract2) : bool :=
  match a, b with
  | CV1 x, CV1 y => VContractTab.contract_eqb x y
  | C_stack_malloc i, C_stack_malloc j => Z.eqb i j
  | C_set_shadow x, C_set_shadow y => Z.eqb x y
  | C_asan_memset, C_asan_memset | C_asan_memcpy, C_asan_memcpy
  | C_i_strlen, C_i_strlen | C_i_strcmp, C_i_strcmp | C_i_strncpy, C_i_strncpy | C_i_bcmp, C_i_bcmp => true
  | _, _ => false
  end.

Lemma contract2_eqb_eq a b : contract2_eqb a b = true -> a = b.
Proof.
  destruct a, b; cbn; intros H; try discriminate; try reflexivity.
  - f_equal. apply VContractTab.contract_eqb_eq. exact H.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
Qed.

Definition ctab_check2 (expected : list (Z * contract2)) (ctab : pmap contract2) : bool :=
  forallb (fun kv : positive * contract2 =>
             existsb (fun e : Z * contract2 =>
                        Z.ltb 0 (fst e) && Pos.eqb (fst kv) (Z.to_pos (fst e)) && contract2_eqb (snd kv) (snd e))
                     expected)
          (pm_elements ctab).

Section Tab.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.

  Definition entry_ok2 (e : Z * contract2) : Prop :=
    contract_post2 SEGS P E mem0 rom CI (snd e) (fst e) /\ contract_dead2 SEGS P E mem0 CI (snd e).

  Lemma ctab_sound2_of_check expected ctab :
    ctab_check2 expected ctab = true -> Forall entry_ok2 expected -> ctab_sound2 SEGS P E mem0 rom CI ctab.
  Proof.
    intros Hc HF tgt c Ht Hg. unfold ctab_check2 in Hc.
    apply pm_elements_complete in Hg.
    pose proof (proj1 (forallb_forall _ _) Hc _ Hg) as X. cbn beta in X.
    apply existsb_exists in X as [[t' c'] [Hin Hb]]. cbn [fst snd] in Hb.
    apply andb_prop in Hb as [Hb Hcc]. apply andb_prop in Hb as [Ht' Hk].
    apply Z.ltb_lt in Ht'. apply Pos.eqb_eq in Hk. apply contract2_eqb_eq in Hcc. subst c'.
    assert (tgt = t') by (apply (Z2Pos.inj tgt t' Ht Ht'); exact Hk). subst t'.
    exact (proj1 (Forall_forall _ _) HF _ Hin).
  Qed.
End Tab.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition expected_asan : list (Z * contract2) :=
  [ (0x3ecf8, C_stack_malloc 0); (0x3ee6c, C_stack_malloc 1); (0x3effc, C_stack_malloc 2); (0x3f198, C_stack_malloc 3); (0x3f344, C_stack_malloc 4)
  ; (0x56cf0, C_set_shadow 0x00); (0x56df8, C_set_shadow 0xf5); (0x56e10, C_set_shadow 0xf8)
  ; (0x542cc, C_asan_memset); (0x53e30, C_asan_memcpy)
  ; (0x44230, C_i_strlen); (0x44238, C_i_strcmp); (0x44244, C_i_bcmp); (0x442c0, C_i_strncpy)
  ; (0x99ed0, CV1 C_tolower); (0xa3f44, CV1 C_strtoul) ].

Lemma ctab_check_asan : ctab_check2 expected_asan ctab_asan = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Unit.
  Variable U : vunit2.
  Let P : vparams2 := unit_params2 (genv_asan true) U.

  (* [comment removed for export] *)
  Local Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
  (* [comment removed for export] *)
  Local Ltac arith := vm_compute; first [reflexivity | discriminate | (intros ?; discriminate) | (split; first [reflexivity | discriminate | (intros ?; discriminate)])].

  Lemma U_shoff : vp_shoff P = SBz. Proof. reflexivity. Qed.
  Lemma U_fslen : forall len ssl, vp_fs P = Some (len, ssl) -> FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL < len.
  Proof. intros len ssl H. cbn in H. injection H as <- <-. vm_compute. reflexivity. Qed.
  Lemma U_fssome : vp_fs P <> None. Proof. cbn. discriminate. Qed.
  Lemma U_frame40 : vp_frame (p1 P) < 2 ^ 40. Proof. vm_compute. reflexivity. Qed.
  Lemma U_datal : 8 <= vp_datal P. Proof. vm_compute. discriminate. Qed.
  Lemma U_tp : vp_tp P = TP_asan. Proof. reflexivity. Qed.
  Lemma U_citp : ci_tp CI_asan = vp_tp P. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma U_pri (a b : Z) :
    (0x10000 <= a /\ b <= 0xa98e4) \/ (0xaa8e8 <= a /\ b <= 0xabb78) \/ (0xacb80 <= a /\ b <= 0xaccf8) ->
    exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= a /\ b <= phi.
  Proof.
    intros [[H1 H2]|[[H1 H2]|[H1 H2]]].
    - exists 0x10000, 0xa98e4. split; [inlist|lia].
    - exists 0xaa8e8, 0xabb78. split; [inlist|lia].
    - exists 0xacb80, 0xaccf8. split; [inlist|lia].
  Qed.
  (* [comment removed for export] *)
  Lemma U_imgend : 0x608000 <= vp_imgend P. Proof. vm_compute. discriminate. Qed.
  Lemma U_segimg : forall lo hi, In (lo, hi) (vp_segs (p1 P)) -> hi <= vp_imgend P.
  Proof.
    assert (X : forallb (fun c : Z * Z => snd c <=? vp_imgend P) (vp_segs (p1 P)) = true) by (vm_compute; reflexivity).
    intros lo hi H. rewrite forallb_forall in X. apply Z.leb_le. exact (X (lo, hi) H).
  Qed.
  Local Ltac pr := apply U_pri; cbv -[Z.le Z.lt Z.add Z.sub Z.mul]; lia.

  (* [comment removed for export] *)
  Lemma U_kc (a w v : Z) : In (a, w, v) FPA_asan_kcells -> In (a, (w, v)) (vp_kcells P).
  Proof.
    intros H. change (vp_kcells P) with (map (fun c : Z * Z * Z => (fst (fst c), (snd (fst c), snd c))) (fa_kcells FPA_asan)).
    apply in_map_iff. exists (a, w, v). split; [reflexivity|exact H].
  Qed.
  Local Ltac kc := apply U_kc; inlist.

  (* [comment removed for export] *)
  Lemma U_zone (b : sym) (d l h lo hi : Z) :
    In (mkFZ b d (lconst l) (lconst h) true) (vp_fzones P) -> l <= lo -> hi <= h -> zone_covers P b d lo hi.
  Proof. intros H H1 H2. exists (mkFZ b d (lconst l) (lconst h) true), l, h. repeat split; auto. Qed.

  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Hypothesis PO2 : params_ok2 SEGSA P.

  Theorem entries_ok_asan : Forall (entry_ok2 SEGSA P E mem0 rom CI_asan) expected_asan.
  Proof.
    pose proof U_shoff as SHOFF. pose proof U_fslen as FSLEN. pose proof U_fssome as FS_SOME. pose proof U_frame40 as FRAME40.
    pose proof U_datal as DATAL. pose proof U_tp as VTP. pose proof U_citp as CITP.
    pose proof U_imgend as VIMG. pose proof U_segimg as SEG_IMG.
    (* [comment removed for export] *)
    assert (PRI_GOT1 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_cflags /\ A_GOT_hend + 8 <= phi) by pr.
    assert (GOT1_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_shb /\ A_GOT_hend + 8 <= phi) by pr.
    assert (GOT_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ (plo <= A_GOT_memset)%Z /\ (A_GOT_memset + 8 <= phi)%Z) by pr.
    assert (CELL_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ (plo <= A_CELL_memset)%Z /\ (A_CELL_memset + 8 <= phi)%Z) by pr.
    assert (GOT2_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_ri /\ A_GOT_ri + 8 <= phi) by pr.
    assert (CELL_memcpy : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_memcpy /\ A_CELL_memcpy + 8 <= phi) by pr.
    assert (PRI_CELL_strlen : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_strlen /\ A_CELL_strlen + 8 <= phi) by pr.
    assert (PRI_RC : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= RC_LO /\ RC_HI <= phi) by pr.
    assert (PRI_CELLS7 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_memcmp /\ A_CELL_bcmp + 8 <= phi) by pr.
    assert (PRI_CELLS8 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_CELL_memchr /\ A_CELL_memset + 8 <= phi) by pr.
    assert (PRI_GOT2 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_ndl /\ A_GOT_ndl + 8 <= phi) by pr.
    assert (PRI_DESC : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_DESC0 /\ A_DESC1 + 8 <= phi) by pr.
    assert (PRI_GOT3 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_dtls /\ A_GOT_dtls + 8 <= phi) by pr.
    assert (PRI_REAL : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_REAL_tga /\ A_REAL_tga + 8 <= phi) by pr.
    assert (PRI_GOTV1 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= A_GOT_asan /\ A_GOT_asan + 8 <= phi) by pr.
    assert (PRI_RO1 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= RO1_LO_asan /\ RO1_HI_asan <= phi) by pr.
    assert (PRI_RO2 : exists plo phi, In (plo, phi) (vp_pristine (p1 P)) /\ plo <= RO2_LO_asan /\ RO2_HI_asan <= phi) by pr.
    (* [comment removed for export] *)
    assert (K_shb : In (A_shb, (8, SBz)) (vp_kcells P)) by kc.
    assert (K_mid1 : In (A_mid1, (8, 0)) (vp_kcells P)) by kc.
    assert (K_mid2 : In (A_mid2, (8, 0)) (vp_kcells P)) by kc.
    assert (K_hend : In (A_hend, (8, 2 ^ 47 - 1)) (vp_kcells P)) by kc.
    assert (K_ri : In (A_ri, (1, 1)) (vp_kcells P)) by kc.
    assert (K_inited : In (0xb42d8, (1, 1)) (vp_kcells P)) by kc.
    assert (K_inited' : In (A_inited, (1, 1)) (vp_kcells P)) by kc.
    assert (K_tsdki : In (0xb2e60, (1, 1)) (vp_kcells P)) by kc.
    assert (K_tsdkey : In (0xb2e64, (4, 0)) (vp_kcells P)) by kc.
    assert (K_ndl : In (0x143098, (4, 0)) (vp_kcells P)) by kc.
    assert (K_itga : In (0x1451b1, (1, 1)) (vp_kcells P)) by kc.
    assert (K_tsd : In (0x5e6598, (8, TSD_asan)) (vp_kcells P)) by kc.
    assert (K_dtv : In (0x5e65e8, (8, 0x5e6610)) (vp_kcells P)) by kc.
    assert (K_dtv1 : In (0x5e6618, (8, 0x5e6df0)) (vp_kcells P)) by kc.
    assert (K_istrlen : In (A_istrlen, (1, 1)) (vp_kcells P)) by kc.
    assert (K_istrcmp : In (A_istrcmp, (1, 1)) (vp_kcells P)) by kc.
    assert (K_sstrict : In (A_sstrict, (1, 0)) (vp_kcells P)) by kc.
    assert (K_imemcmp : In (A_imemcmp, (1, 1)) (vp_kcells P)) by kc.
    assert (K_smemcmp : In (A_smemcmp, (1, 1)) (vp_kcells P)) by kc.
    assert (K_rstr : In (A_rstr, (1, 1)) (vp_kcells P)) by kc.
    (* [comment removed for export] *)
    assert (Z_HINTS : zone_covers P FSB 0 0 88) by (apply (U_zone FSB 0 0 FS_HINTS); [inlist|arith|arith]).
    assert (Z_FLAGS : zone_covers P FSB 0 FS_FLAGS FS_FRAMES)
      by (apply (U_zone FSB 0 FContractAsan.FS_FLAGS (FContractAsan.FS_FLAGS + FS_FLAGS_LEN)); [inlist|arith|arith]).
    assert (Z_FRAMES : zone_covers P FSB 0 FS_FRAMES (FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL))
      by (apply (U_zone FSB 0 FContractAsan.FS_FRAMES (FContractAsan.FS_FRAMES + FS_FRAMES_LEN)); [inlist|arith|arith]).
    assert (Z_FSHAD : zone_covers P FS8 SBz (FS_FRAMES / 8) ((FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL) / 8))
      by (apply (U_zone FS8 A_shoff (FContractAsan.FS_FRAMES / 8) (FContractAsan.FS_FRAMES / 8 + FS_FRAMES_LEN / 8)); [inlist|arith|arith]).
    (* [comment removed for export] *)
    assert (SEG_GUARD : exists lo hi, In (lo, hi) (vp_segs (p1 P)) /\ lo <= A_GUARD_asan /\ A_GUARD_asan + 8 <= hi)
      by (exists 0x606630, 0x606638; split; [inlist|cbv -[Z.le Z.lt Z.add]; lia]).
    assert (CI_ERRNO : ci_errno CI_asan = ci_tp CI_asan - 164) by reflexivity.
    assert (CI_TP : RO_MIN_asan + 164 <= ci_tp CI_asan < 2 ^ 64) by arith.
    assert (RO_MIN : 0 <= RO_MIN_asan <= vp_splo (p1 P) - vp_frame (p1 P)) by arith.
    assert (GUARD_ERR : A_GUARD_asan + 8 <= ci_errno CI_asan \/ ci_errno CI_asan + 4 <= A_GUARD_asan) by (right; arith).
    assert (SPHI8 : vp_sphi (p1 P) + 8 < 2 ^ 64) by arith.
    unfold expected_asan.
    repeat apply Forall_cons; try apply Forall_nil; unfold entry_ok2; cbn [fst snd].
    (* [comment removed for export] *)
    Local Ltac by_inst post dead := split; [eapply post | eapply dead]; try eassumption; try lia.
    - by_inst stack_malloc_post_asan stack_malloc_dead_asan.
    - by_inst stack_malloc_post_asan stack_malloc_dead_asan.
    - by_inst stack_malloc_post_asan stack_malloc_dead_asan.
    - by_inst stack_malloc_post_asan stack_malloc_dead_asan.
    - by_inst stack_malloc_post_asan stack_malloc_dead_asan.
    - by_inst set_shadow_00_post set_shadow_dead_any.
    - by_inst set_shadow_f5_post set_shadow_dead_any.
    - by_inst set_shadow_f8_post set_shadow_dead_any.
    - by_inst asan_memset_post_asan asan_memset_dead_asan.
    - by_inst asan_memcpy_post_asan asan_memcpy_dead_asan.
    - by_inst i_strlen_post_asan i_strlen_dead_asan.
    - by_inst i_strcmp_post_asan i_strcmp_dead_asan.
    - by_inst i_bcmp_post_asan i_bcmp_dead_asan.
    - by_inst i_strncpy_post_asan i_strncpy_dead_asan.
    - by_inst tolower_post_asan tolower_dead_asan.
    - by_inst strtoul_post_asan strtoul_dead_asan.
  Qed.
End Unit.

(* [comment removed for export] *)
Theorem ctab_ok2_asan : forall rom (U : vunit2) (E : venv2) (mem0 : word -> option byte),
  params_ok2 SEGSA (unit_params2 (genv_asan true) U) ->
  ctab_sound2 SEGSA (unit_params2 (genv_asan true) U) E mem0 rom (ge2_CI (genv_asan true)) (ge2_ctab (genv_asan true)).
Proof.
  intros rom U E mem0 PO2.
  exact (ctab_sound2_of_check SEGSA (unit_params2 (genv_asan true) U) E mem0 rom CI_asan expected_asan ctab_asan
           ctab_check_asan (entries_ok_asan U E mem0 rom PO2)).
Qed.

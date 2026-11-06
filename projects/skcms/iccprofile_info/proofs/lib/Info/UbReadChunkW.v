(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits SumWalkTac RefMemcpyLib
 Ub_code_1299c_12db8 Ub_code_1735c_17f20 Ub_code_198d4_19c3c Ub_code_1e6dc_1f0b8.
From Stdlib Require Import Zify.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
Definition RS : Z := 0x213c9%Z.

(* [comment removed for export] *)
Definition want (cap len : Z) : Z := if (cap - len <? 65536)%Z then (cap - len)%Z else 65536%Z.

Lemma want_range : forall cap len, (0 <= len < cap)%Z -> (1 <= want cap len <= 65536)%Z /\ (want cap len <= cap - len)%Z.
Proof. intros cap len H. unfold want. destruct (Z.ltb_spec (cap - len) 65536); lia. Qed.

(* [comment removed for export] *)
Definition loop_kept : list reg := [3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition loopB_kept : list reg := [1; 2; 3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.
(* [comment removed for export] *)
Definition loopC_kept : list reg := [9; 19; 3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.
(* [comment removed for export] *)
Definition loopD_kept : list reg := [9; 19; 23; 3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.
Definition front_kept : list reg := [2; 3; 4; 8; 18; 20; 21; 24; 25; 26; 27]%bv.

End WithFP1.

Ltac kept_list l :=
  intros r Hr; cbv [l In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.

Section WithFP2. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
Lemma walkF : forall regs mem rom (buf : Z),
  getr regs 10 = Z_to_bv 64 buf -> getr regs 21 = Z_to_bv 64 65536 ->
  (0 < buf < 2 ^ 64)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x12b3c : word) mem rom) (mkst regs' (0x12bb4 : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf
    /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 RS
    /\ (forall r, In r front_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf Ha0 Hs5 Hbuf. eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_12b3c D_12b3c ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_12b40 D_12b40. rewrite Ha0.
    stepn F_12b44 D_12b44.
    stepn F_12b48 D_12b48. stepn F_12b4c D_12b4c.
    (* [comment removed for export] *)
    stepb_tk F_12b50 D_12b50 ltac:(rewrite Hs5; cond_compute).
    (* [comment removed for export] *)
    stepn F_12b74 D_12b74. stepn F_12b78 D_12b78.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption.
    kept_list front_kept.
Qed.

(* [comment removed for export] *)
Lemma walkA : forall regs mem rom (sp0 len cap : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 128) -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
  getr regs 20 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 RS ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x12bb4 : word) mem rom)
                 (mkst regs' (0x1f000 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0x1f0ac /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = getr regs 9 /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 len cap Hsp Hs3 Hs5 Hs4 Hs6 SPlo SPhi Hlen Hcap SOK.
  (* [comment removed for export] *)
  Ltac walkA_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_12bc4 D_12bc4; rewrite Hs4;
      stepn F_12bc8 D_12bc8; rewrite Hs6;
      stepn F_12bcc D_12bcc;
      (* [comment removed for export] *)
      stepn F_1f084 D_1f084; rewrite Hsp; sp_renorm;
      stepST F_1f088 D_1f088 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x12bd0) ltac:(exact SOK);
      stepn F_1f08c D_1f08c; stepn F_1f090 D_1f090; stepn F_1f094 D_1f094; stepn F_1f098 D_1f098;
      stepn F_1f09c D_1f09c; stepn F_1f0a0 D_1f0a0; stepn F_1f0a4 D_1f0a4; stepn F_1f0a8 D_1f0a8;
      stepn F_1f008 D_1f008;
      stepn F_1efe4 D_1efe4; stepn F_1efe8 D_1efe8; stepn F_1efec D_1efec; stepn F_1eff0 D_1eff0;
      stepn F_1eff4 D_1eff4; stepn F_1eff8 D_1eff8; stepn F_1effc D_1effc;
      apply mst_refl.
  Ltac walkA_post :=
      repeat split; gres; try reflexivity; try assumption;
      kept_list loop_kept.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  - (* [comment removed for export] *)
    stepn F_12bb4 D_12bb4. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    (* [comment removed for export] *)
    stepn F_12bb8 D_12bb8.
    (* [comment removed for export] *)
    stepb_tk F_12bbc D_12bbc ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
  - stepn F_12bb4 D_12bb4. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_12bb8 D_12bb8.
    (* [comment removed for export] *)
    stepb_ft F_12bbc D_12bbc ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_12bc0 D_12bc0.
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
Qed.

(* [comment removed for export] *)
Lemma walkB1 : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0x1f0ac -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 RS ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len + n <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x1f004 : word) mem rom) (mkst regs' (0x1e6dc : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x12b68 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 23 = Z_to_bv 64 n
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hln RD.
  eexists. split.
  - (* [comment removed for export] *)
    stepret F_1f004 D_1f004 (0x1f0ac : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_1f0ac D_1f0ac (Z_to_bv 64 0x12bd0).
    (* [comment removed for export] *)
    stepn F_1f0b0 D_1f0b0. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_1f0b4 D_1f0b4.
    (* [comment removed for export] *)
    stepn F_1771c D_1771c. stepn F_17720 D_17720.
    (* [comment removed for export] *)
    stepb_tk F_17724 D_17724 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepret F_17750 D_17750 (0x12bd0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_ft F_12bd0 D_12bd0 ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).
    (* [comment removed for export] *)
    stepn F_12bd4 D_12bd4. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_tk F_12bd8 D_12bd8 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_12b58 D_12b58. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_12b5c D_12b5c. rewrite Hs6.
    stepn F_12b60 D_12b60.
    stepn F_12b64 D_12b64.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2 : forall regs mem rom (buf len n cap : Z),
  getr regs 23 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 < n)%Z -> (0 <= len)%Z -> (len + n <= cap)%Z -> (cap <= 2 ^ 62)%Z ->
  exists regs' pc',
    msteps RSEGS (mkst regs (0x12b68 : word) mem rom) (mkst regs' pc' mem rom)
    /\ pc' = (if (len + n =? cap)%Z then (0x12b7c : word) else (0x12bb4 : word))
    /\ getr regs' 19 = Z_to_bv 64 (len + n) /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs7 Hs3 Hs1 Hs5 Hn Hlen Hln Hcap.
  destruct (Z.eqb_spec (len + n) cap) as [EQ|NE]; do 2 eexists; split.
  - (* [comment removed for export] *)
    stepn F_12b68 D_12b68. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    (* [comment removed for export] *)
    stepn F_12b6c D_12b6c. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_tk F_12b70 D_12b70 ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
    apply mst_refl.
  - split; [reflexivity|]. repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    kept_list loopB_kept.
  - stepn F_12b68 D_12b68. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_12b6c D_12b6c. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_ft F_12b70 D_12b70 ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_12b74 D_12b74. stepn F_12b78 D_12b78.
    apply mst_refl.
  - split; [reflexivity|]. repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkBC : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x1f0ac -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bd0)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x1f004 : word) mem rom)
                 (mkst regs' (0x1f000 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12be4))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0x1f050 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loopC_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 Hs4 SPlo SPhi RD SOK.
  eexists. split.
  - stepret F_1f004 D_1f004 (0x1f0ac : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_1f0ac D_1f0ac (Z_to_bv 64 0x12bd0).
    stepn F_1f0b0 D_1f0b0. rewrite Hsp. sp_renorm.
    stepn F_1f0b4 D_1f0b4.
    stepn F_1771c D_1771c. stepn F_17720 D_17720.
    stepb_tk F_17724 D_17724 ltac:(rewrite Ha0; cond_compute).
    stepret F_17750 D_17750 (0x12bd0 : word) ltac:(bveq).
    stepb_ft F_12bd0 D_12bd0 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_12bd4 D_12bd4. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_ft F_12bd8 D_12bd8 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_12bdc D_12bdc. rewrite Hs4.
    stepn F_12be0 D_12be0.
    (* [comment removed for export] *)
    stepn F_1f024 D_1f024. sp_renorm.
    stepST F_1f028 D_1f028 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x12be4) ltac:(exact SOK).
    stepn F_1f02c D_1f02c.
    stepret F_19ab4 D_19ab4 (0x1f030 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1f030 D_1f030. stepn F_1f034 D_1f034. stepn F_1f038 D_1f038. stepn F_1f03c D_1f03c.
    stepn F_1f040 D_1f040. stepn F_1f044 D_1f044. stepn F_1f048 D_1f048. stepn F_1f04c D_1f04c.
    stepn F_1f008 D_1f008.
    stepn F_1efe4 D_1efe4. stepn F_1efe8 D_1efe8. stepn F_1efec D_1efec. stepn F_1eff0 D_1eff0.
    stepn F_1eff4 D_1eff4. stepn F_1eff8 D_1eff8. stepn F_1effc D_1effc.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopC_kept.
Qed.

(* [comment removed for export] *)
Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x1f050 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12be4)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x1f004 : word) mem rom) (mkst regs' (0x12be4 : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r loopD_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_1f004 D_1f004 (0x1f050 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepn F_1f050 D_1f050. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_1f054 D_1f054. stepn F_1f058 D_1f058. stepn F_1f05c D_1f05c. stepn F_1f060 D_1f060.
    (* [comment removed for export] *)
    stepn F_1f064 D_1f064.
    stepn F_1771c D_1771c. stepn F_17720 D_17720.
    stepb_tk F_17724 D_17724 ltac:(cond_compute).
    stepret F_17750 D_17750 (0x1f068 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1f068 D_1f068.
    stepLD8 F_1f06c D_1f06c (Z_to_bv 64 0x12be4).
    stepn F_1f070 D_1f070. rewrite Hsp. sp_renorm.
    stepret F_1f074 D_1f074 (0x12be4 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopD_kept.
Qed.

End WithFP2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits SumWalkTac RefMemcpyLib
  Ref_code_1293c_12d58 Ref_code_161c8_17084 Ref_code_183b0_19140 Ref_code_1dbe0_1e5bc.
From Stdlib Require Import Zify.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
Definition RS : Z := 0x208d9%Z.

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
    msteps RSEGS (mkst regs (0x12adc : word) mem rom) (mkst regs' (0x12b54 : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf
    /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 RS
    /\ (forall r, In r front_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf Ha0 Hs5 Hbuf. eexists. split.
  - (* [comment removed for export] *)
    stepb_ft F_12adc D_12adc ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_12ae0 D_12ae0. rewrite Ha0.
    stepn F_12ae4 D_12ae4.
    stepn F_12ae8 D_12ae8. stepn F_12aec D_12aec.
    (* [comment removed for export] *)
    stepb_tk F_12af0 D_12af0 ltac:(rewrite Hs5; cond_compute).
    (* [comment removed for export] *)
    stepn F_12b14 D_12b14. stepn F_12b18 D_12b18.
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
    msteps RSEGS (mkst regs (0x12b54 : word) mem rom)
                 (mkst regs' (0x1e504 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12b70))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0x1e5b0 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = getr regs 9 /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 len cap Hsp Hs3 Hs5 Hs4 Hs6 SPlo SPhi Hlen Hcap SOK.
  (* [comment removed for export] *)
  Ltac walkA_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_12b64 D_12b64; rewrite Hs4;
      stepn F_12b68 D_12b68; rewrite Hs6;
      stepn F_12b6c D_12b6c;
      (* [comment removed for export] *)
      stepn F_1e588 D_1e588; rewrite Hsp; sp_renorm;
      stepST F_1e58c D_1e58c (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x12b70) ltac:(exact SOK);
      stepn F_1e590 D_1e590; stepn F_1e594 D_1e594; stepn F_1e598 D_1e598; stepn F_1e59c D_1e59c;
      stepn F_1e5a0 D_1e5a0; stepn F_1e5a4 D_1e5a4; stepn F_1e5a8 D_1e5a8; stepn F_1e5ac D_1e5ac;
      stepn F_1e50c D_1e50c;
      stepn F_1e4e8 D_1e4e8; stepn F_1e4ec D_1e4ec; stepn F_1e4f0 D_1e4f0; stepn F_1e4f4 D_1e4f4;
      stepn F_1e4f8 D_1e4f8; stepn F_1e4fc D_1e4fc; stepn F_1e500 D_1e500;
      apply mst_refl.
  Ltac walkA_post :=
      repeat split; gres; try reflexivity; try assumption;
      kept_list loop_kept.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  - (* [comment removed for export] *)
    stepn F_12b54 D_12b54. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    (* [comment removed for export] *)
    stepn F_12b58 D_12b58.
    (* [comment removed for export] *)
    stepb_tk F_12b5c D_12b5c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
  - stepn F_12b54 D_12b54. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_12b58 D_12b58.
    (* [comment removed for export] *)
    stepb_ft F_12b5c D_12b5c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_12b60 D_12b60.
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
Qed.

(* [comment removed for export] *)
Lemma walkB1 : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0x1e5b0 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 RS ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len + n <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b70)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x1e508 : word) mem rom) (mkst regs' (0x1dbe0 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x12b08 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 23 = Z_to_bv 64 n
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hln RD.
  eexists. split.
  - (* [comment removed for export] *)
    stepret F_1e508 D_1e508 (0x1e5b0 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_1e5b0 D_1e5b0 (Z_to_bv 64 0x12b70).
    (* [comment removed for export] *)
    stepn F_1e5b4 D_1e5b4. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_1e5b8 D_1e5b8.
    (* [comment removed for export] *)
    stepn F_16c20 D_16c20. stepn F_16c24 D_16c24.
    (* [comment removed for export] *)
    stepb_tk F_16c28 D_16c28 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepret F_16c54 D_16c54 (0x12b70 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_ft F_12b70 D_12b70 ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).
    (* [comment removed for export] *)
    stepn F_12b74 D_12b74. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_tk F_12b78 D_12b78 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_12af8 D_12af8. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_12afc D_12afc. rewrite Hs6.
    stepn F_12b00 D_12b00.
    stepn F_12b04 D_12b04.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2 : forall regs mem rom (buf len n cap : Z),
  getr regs 23 = Z_to_bv 64 n -> getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 < n)%Z -> (0 <= len)%Z -> (len + n <= cap)%Z -> (cap <= 2 ^ 62)%Z ->
  exists regs' pc',
    msteps RSEGS (mkst regs (0x12b08 : word) mem rom) (mkst regs' pc' mem rom)
    /\ pc' = (if (len + n =? cap)%Z then (0x12b1c : word) else (0x12b54 : word))
    /\ getr regs' 19 = Z_to_bv 64 (len + n) /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs7 Hs3 Hs1 Hs5 Hn Hlen Hln Hcap.
  destruct (Z.eqb_spec (len + n) cap) as [EQ|NE]; do 2 eexists; split.
  - (* [comment removed for export] *)
    stepn F_12b08 D_12b08. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    (* [comment removed for export] *)
    stepn F_12b0c D_12b0c. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_tk F_12b10 D_12b10 ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
    apply mst_refl.
  - split; [reflexivity|]. repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    kept_list loopB_kept.
  - stepn F_12b08 D_12b08. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_12b0c D_12b0c. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_ft F_12b10 D_12b10 ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_12b14 D_12b14. stepn F_12b18 D_12b18.
    apply mst_refl.
  - split; [reflexivity|]. repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkBC : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x1e5b0 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b70)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x1e508 : word) mem rom)
                 (mkst regs' (0x1e504 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x12b84))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0x1e554 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loopC_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 Hs4 SPlo SPhi RD SOK.
  eexists. split.
  - stepret F_1e508 D_1e508 (0x1e5b0 : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_1e5b0 D_1e5b0 (Z_to_bv 64 0x12b70).
    stepn F_1e5b4 D_1e5b4. rewrite Hsp. sp_renorm.
    stepn F_1e5b8 D_1e5b8.
    stepn F_16c20 D_16c20. stepn F_16c24 D_16c24.
    stepb_tk F_16c28 D_16c28 ltac:(rewrite Ha0; cond_compute).
    stepret F_16c54 D_16c54 (0x12b70 : word) ltac:(bveq).
    stepb_ft F_12b70 D_12b70 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_12b74 D_12b74. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_ft F_12b78 D_12b78 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_12b7c D_12b7c. rewrite Hs4.
    stepn F_12b80 D_12b80.
    (* [comment removed for export] *)
    stepn F_1e528 D_1e528. sp_renorm.
    stepST F_1e52c D_1e52c (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x12b84) ltac:(exact SOK).
    stepn F_1e530 D_1e530.
    stepret F_18fb8 D_18fb8 (0x1e534 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1e534 D_1e534. stepn F_1e538 D_1e538. stepn F_1e53c D_1e53c. stepn F_1e540 D_1e540.
    stepn F_1e544 D_1e544. stepn F_1e548 D_1e548. stepn F_1e54c D_1e54c. stepn F_1e550 D_1e550.
    stepn F_1e50c D_1e50c.
    stepn F_1e4e8 D_1e4e8. stepn F_1e4ec D_1e4ec. stepn F_1e4f0 D_1e4f0. stepn F_1e4f4 D_1e4f4.
    stepn F_1e4f8 D_1e4f8. stepn F_1e4fc D_1e4fc. stepn F_1e500 D_1e500.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopC_kept.
Qed.

(* [comment removed for export] *)
Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x1e554 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12b84)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x1e508 : word) mem rom) (mkst regs' (0x12b84 : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r loopD_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_1e508 D_1e508 (0x1e554 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepn F_1e554 D_1e554. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_1e558 D_1e558. stepn F_1e55c D_1e55c. stepn F_1e560 D_1e560. stepn F_1e564 D_1e564.
    (* [comment removed for export] *)
    stepn F_1e568 D_1e568.
    stepn F_16c20 D_16c20. stepn F_16c24 D_16c24.
    stepb_tk F_16c28 D_16c28 ltac:(cond_compute).
    stepret F_16c54 D_16c54 (0x1e56c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1e56c D_1e56c.
    stepLD8 F_1e570 D_1e570 (Z_to_bv 64 0x12b84).
    stepn F_1e574 D_1e574. rewrite Hsp. sp_renorm.
    stepret F_1e578 D_1e578 (0x12b84 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopD_kept.
Qed.

End WithFP2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

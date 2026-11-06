(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits SumWalkTac RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1_code_656b0_66064 U1_code_d1054_d2138 U1_code_d7138_d8138 U1_code_e3138_e4138 U1_code_e7138_e7c2c    .
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition RS : Z := 0xf0249.

Ltac kept_list l :=
  intros r Hr; cbv [l In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.

Section FXALL1.
Context {fx : FPState}.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition want (cap len : Z) : Z := if (cap - len <? 65536)%Z then (cap - len)%Z else 65536%Z.

Lemma want_range : forall cap len, (0 <= len < cap)%Z -> (1 <= want cap len <= 65536)%Z /\ (want cap len <= cap - len)%Z.
Proof. intros cap len H. unfold want. destruct (Z.ltb_spec (cap - len) 65536); lia. Qed.

Definition loop_kept : list reg := [3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.

Lemma walkH : forall regs mem rom (sp0 buf len cap : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 128) -> getr regs 9 = Z_to_bv 64 buf -> getr regs 19 = Z_to_bv 64 len ->
  getr regs 20 = Z_to_bv 64 3 -> getr regs 21 = Z_to_bv 64 cap -> getr regs 22 = Z_to_bv 64 RS ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x65908 : word) mem rom)
                 (mkst regs' (0xe3ba4 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x65924))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0xe7b28 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len cap Hsp Hs1 Hs3 Hs4 Hs5 Hs6 SPlo SPhi Hlen Hcap SOK.
  Ltac walkH_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_658d8 D_658d8; rewrite Hs4;
      stepn F_658dc D_658dc; rewrite Hs6;
      stepn F_658e0 D_658e0;

      stepn F_e7acc D_e7acc; rewrite Hsp; sp_renorm;
      stepST F_e7ad0 D_e7ad0 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x65924) ltac:(exact SOK);
      stepn F_e7ad4 D_e7ad4; stepn F_e7ad8 D_e7ad8; stepn F_e7adc D_e7adc; stepn F_e7ae0 D_e7ae0;
      stepn F_e7ae4 D_e7ae4; stepn F_e7ae8 D_e7ae8; stepn F_e7aec D_e7aec; stepn F_e7af0 D_e7af0;
      stepn F_e3b78 D_e3b78;
      stepn F_e3b54 D_e3b54; stepn F_e3b58 D_e3b58; stepn F_e3b5c D_e3b5c; stepn F_e3b60 D_e3b60;
      stepn F_e3b64 D_e3b64; stepn F_e3b68 D_e3b68; stepn F_e3b6c D_e3b6c;
      apply mst_refl.
  Ltac walkH_post :=
      repeat split; gres; try reflexivity; try assumption;
      intros r Hr; cbv [loop_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  -
    stepn F_658c8 D_658c8. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.

    stepn F_658cc D_658cc.

    stepb_tk F_658d0 D_658d0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkH_tail Hs4 Hs6 Hsp SOK sp0.
  - walkH_post.
  - stepn F_658c8 D_658c8. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_658cc D_658cc.

    stepb_ft F_658d0 D_658d0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_658d4 D_658d4.
    walkH_tail Hs4 Hs6 Hsp SOK sp0.
  - walkH_post.
Qed.

Lemma walkRn : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0xe7b28 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 RS ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len + n <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65924)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xe3ba8 : word) mem rom) (mkst regs' (0xe2b9c : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x658bc /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 23 = Z_to_bv 64 n
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hln RD.
  eexists. split.
  -
    stepret F_e3b74 D_e3b74 (0xe7b28 : word) ltac:(rewrite Hra; bveq).

    stepLD8 F_e7af4 D_e7af4 (Z_to_bv 64 0x65924).

    stepn F_e7af8 D_e7af8. rewrite Hsp. sp_renorm.

    stepn F_e7afc D_e7afc.

    stepn F_d1fe0 D_d1fe0. stepn F_d1fe4 D_d1fe4.

    stepb_tk F_d1fe8 D_d1fe8 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).

    stepret F_d2014 D_d2014 (0x65924 : word) ltac:(bveq).

    stepb_ft F_658e4 D_658e4 ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).

    stepn F_658e8 D_658e8. rewrite Ha0.

    stepb_tk F_658ec D_658ec ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

    stepn F_6586c D_6586c. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_65870 D_65870. rewrite Hs6.
    stepn F_65874 D_65874.
    stepn F_65878 D_65878.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

Lemma walkR0 : forall regs mem rom (sp0 buf len : Z),
  getr regs 1 = Z_to_bv 64 0xe7b28 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z -> (0 <= len < 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65924)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0xe3ba8 : word) mem rom)
                 (mkst regs' (0xe3ba4 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x65938))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0xe7acc /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len Hra Hsp Ha0 Hs3 Hs1 Hs4 SPlo SPhi Hlen RD SOK.
  eexists. split.
  - stepret F_e3b74 D_e3b74 (0xe7b28 : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_e7af4 D_e7af4 (Z_to_bv 64 0x65924).
    stepn F_e7af8 D_e7af8. rewrite Hsp. sp_renorm.
    stepn F_e7afc D_e7afc.
    stepn F_d1fe0 D_d1fe0. stepn F_d1fe4 D_d1fe4.
    stepb_tk F_d1fe8 D_d1fe8 ltac:(rewrite Ha0; cond_compute).
    stepret F_d2014 D_d2014 (0x65924 : word) ltac:(bveq).
    stepb_ft F_658e4 D_658e4 ltac:(rewrite Ha0; cond_compute).

    stepn F_658e8 D_658e8. rewrite Ha0.

    stepb_ft F_658ec D_658ec ltac:(rewrite Ha0; cond_compute).

    stepn F_658f0 D_658f0. rewrite Hs4.
    stepn F_658f4 D_658f4.

    stepn F_e7a6c D_e7a6c. sp_renorm.
    stepST F_e7a70 D_e7a70 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x65938) ltac:(exact SOK).
    stepn F_e7a74 D_e7a74.
    stepret F_d7238 D_d7238 (0xe7aac : word) ltac:(bveq).

    stepn F_e7a78 D_e7a78. stepn F_e7a7c D_e7a7c. stepn F_e7a80 D_e7a80. stepn F_e7a84 D_e7a84.
    stepn F_e7a88 D_e7a88. stepn F_e7a8c D_e7a8c. stepn F_e7a90 D_e7a90. stepn F_e7a94 D_e7a94.
    stepn F_e3b78 D_e3b78.
    stepn F_e3b54 D_e3b54. stepn F_e3b58 D_e3b58. stepn F_e3b5c D_e3b5c. stepn F_e3b60 D_e3b60.
    stepn F_e3b64 D_e3b64. stepn F_e3b68 D_e3b68. stepn F_e3b6c D_e3b6c.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loop_kept.
Qed.

Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0xe7acc -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65938)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xe3ba8 : word) mem rom) (mkst regs' (0x65938 : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r (9 :: 19 :: 23 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_e3b74 D_e3b74 (0xe7acc : word) ltac:(rewrite Hra; bveq).

    stepn F_e7a98 D_e7a98. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_e7a9c D_e7a9c. stepn F_e7aa0 D_e7aa0. stepn F_e7aa4 D_e7aa4. stepn F_e7aa8 D_e7aa8.

    stepn F_e7aac D_e7aac.
    stepn F_d1fe0 D_d1fe0. stepn F_d1fe4 D_d1fe4.
    stepb_tk F_d1fe8 D_d1fe8 ltac:(cond_compute).
    stepret F_d2014 D_d2014 (0xe7ae4 : word) ltac:(bveq).

    stepn F_e7ab0 D_e7ab0.
    stepLD8 F_e7ab4 D_e7ab4 (Z_to_bv 64 0x65938).
    stepn F_e7ab8 D_e7ab8. rewrite Hsp. sp_renorm.
    stepret F_e7abc D_e7abc (0x65938 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

End FXALL1.

Section FXALL2.
Context {fx : FPState}.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma u_small' : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma srli26_small : forall cap, (0 <= cap < 2 ^ 26)%Z -> v_srli (Z_to_bv 64 cap) 26 = Z_to_bv 64 0.
Proof.
  intros cap Hc. unfold v_srli. rewrite u_small' by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma srli26_big : v_srli (Z_to_bv 64 (2 ^ 26)) 26 = Z_to_bv 64 1.
Proof. unfold v_srli. rewrite u_small' by lia. reflexivity. Qed.
Lemma slli1_double : forall cap, (0 <= cap < 2 ^ 62)%Z -> v_slli (Z_to_bv 64 cap) 1 = Z_to_bv 64 (2 * cap).
Proof.
  intros cap Hc. unfold v_slli. rewrite u_small' by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
Qed.

Lemma walkC_head : forall regs mem rom (buf len n cap : Z),
  getr regs 9 = Z_to_bv 64 buf -> getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 < n)%Z -> (len + n < cap)%Z -> (cap <= 2 ^ 40)%Z -> (0 <= buf < 2 ^ 63)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x658bc : word) mem rom) (mkst regs' (0x65908 : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 (len + n)
    /\ (forall r, In r (2 :: 1 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs1 Hs3 Hs7 Hs5 Hl Hn Hlc Hcap Hb.
  eexists. split.
  -
    stepn F_6587c D_6587c. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.

    stepn F_65880 D_65880. rewrite Hs1.

    stepb_ft F_65884 D_65884 ltac:(rewrite Hs5; unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

    stepn F_65888 D_65888.
    stepn F_6588c D_6588c.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

Lemma walkC_full : forall regs mem rom (buf len n cap : Z),
  getr regs 9 = Z_to_bv 64 buf -> getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 < n)%Z -> (len + n = cap)%Z -> (cap <= 2 ^ 40)%Z -> (0 <= buf < 2 ^ 63)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x658bc : word) mem rom) (mkst regs' (0x658d0 : word) mem rom)
    /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 cap
    /\ (forall r, In r (2 :: 1 :: 9 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs1 Hs3 Hs7 Hs5 Hl Hn Hlc Hcap Hb.
  eexists. split.
  - stepn F_6587c D_6587c. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_65880 D_65880. rewrite Hs1.

    stepb_tk F_65884 D_65884 ltac:(rewrite Hs5; unfold c_eq, bv_eqb; apply Z.eqb_eq; u_norm; lia).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

Lemma walkG : forall regs mem rom (cap : Z),
  getr regs 19 = Z_to_bv 64 cap ->
  (0 < cap < 2 ^ 26)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x658d0 : word) mem rom) (mkst regs' (0xd3e38 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x658e4 /\ getr regs' 10 = Z_to_bv 64 (2 * cap)
    /\ getr regs' 21 = Z_to_bv 64 (2 * cap)
    /\ (forall r, In r (2 :: 9 :: 19 :: 23 :: [3; 4; 8; 18; 20; 22; 24; 25; 26; 27])%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom cap Hs3 Hc.
  eexists. split.
  -
    stepn F_65890 D_65890.
    stepb_ft F_65894 D_65894 ltac:(rewrite Hs3, srli26_small by lia; apply c_eq_0_true).

    stepn F_65898 D_65898. rewrite Hs3, slli1_double by lia.
    stepn F_6589c D_6589c.
    stepn F_658a0 D_658a0.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

Lemma walkRef : forall regs mem rom,
  getr regs 19 = Z_to_bv 64 (2 ^ 26) ->
  exists regs',
    msteps RSEGS (mkst regs (0x658d0 : word) mem rom) (mkst regs' (0x65a84 : word) mem rom)
    /\ (forall r : reg, r <> 10 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom H19.
  eexists. split.
  - stepn F_65890 D_65890.
    stepb_tk F_65894 D_65894 ltac:(rewrite H19, srli26_big; apply c_eq_0_false; rewrite u_small' by lia; lia).
    apply mst_refl.
  - intros r H10. rewrite !getr_other by assumption. reflexivity.
Qed.

Lemma walkG1 : forall regs mem rom (nb old len : Z),
  getr regs 10 = Z_to_bv 64 nb -> getr regs 23 = Z_to_bv 64 old -> getr regs 19 = Z_to_bv 64 len ->
  (0 < nb < 2 ^ 63)%Z -> (0 < len < 2 ^ 63)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x658e4 : word) mem rom) (mkst regs' (0xe2b9c : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x65900 /\ getr regs' 10 = Z_to_bv 64 nb /\ getr regs' 11 = Z_to_bv 64 old
    /\ getr regs' 12 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 nb
    /\ (forall r, In r (2 :: 19 :: 23 :: 21 :: [3; 4; 8; 18; 20; 22; 24; 25; 26; 27])%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom nb old len Ha0 Hs7 Hs3 Hnb Hl.
  eexists. split.
  -
    stepb_ft F_658a4 D_658a4 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

    stepn F_658a8 D_658a8. rewrite Ha0.

    stepb_ft F_658ac D_658ac ltac:(rewrite Hs3; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

    stepn F_658b0 D_658b0.
    stepn F_658b4 D_658b4. rewrite Hs7.
    stepn F_658b8 D_658b8. rewrite Hs3.
    stepn F_658bc D_658bc.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

Lemma walkG2 : forall regs mem rom (old : Z),
  getr regs 23 = Z_to_bv 64 old ->
  exists regs',
    msteps RSEGS (mkst regs (0x65900 : word) mem rom) (mkst regs' (0xd3cf8 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x65908 /\ getr regs' 10 = Z_to_bv 64 old
    /\ (forall r, In r (2 :: 9 :: 19 :: 23 :: 21 :: [3; 4; 8; 18; 20; 22; 24; 25; 26; 27])%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom old Hs7.
  eexists. split.
  - stepn F_658c0 D_658c0. rewrite Hs7.
    stepn F_658c4 D_658c4.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption.
    intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

End FXALL2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

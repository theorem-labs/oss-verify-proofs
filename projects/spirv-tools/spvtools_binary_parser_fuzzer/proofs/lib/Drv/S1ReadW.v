(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits SumWalkTac RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1_code_6545c_66064 S1_code_d0138_d1138 S1_code_d5138_d6138 S1_code_e1214_e2138 S1_code_e5138_e5ed4.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition RS : Z := 0xee4e9.

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
    msteps RSEGS (mkst regs (0x656b4 : word) mem rom)
                 (mkst regs' (0xe1e4c : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x656d0))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0xe5dd0 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len cap Hsp Hs1 Hs3 Hs4 Hs5 Hs6 SPlo SPhi Hlen Hcap SOK.
  Ltac walkH_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_65684 D_65684; rewrite Hs4;
      stepn F_65688 D_65688; rewrite Hs6;
      stepn F_6568c D_6568c;

      stepn F_e5d74 D_e5d74; rewrite Hsp; sp_renorm;
      stepST F_e5d78 D_e5d78 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x656d0) ltac:(exact SOK);
      stepn F_e5d7c D_e5d7c; stepn F_e5d80 D_e5d80; stepn F_e5d84 D_e5d84; stepn F_e5d88 D_e5d88;
      stepn F_e5d8c D_e5d8c; stepn F_e5d90 D_e5d90; stepn F_e5d94 D_e5d94; stepn F_e5d98 D_e5d98;
      stepn F_e1e20 D_e1e20;
      stepn F_e1dfc D_e1dfc; stepn F_e1e00 D_e1e00; stepn F_e1e04 D_e1e04; stepn F_e1e08 D_e1e08;
      stepn F_e1e0c D_e1e0c; stepn F_e1e10 D_e1e10; stepn F_e1e14 D_e1e14;
      apply mst_refl.
  Ltac walkH_post :=
      repeat split; gres; try reflexivity; try assumption;
      intros r Hr; cbv [loop_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  -
    stepn F_65674 D_65674. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.

    stepn F_65678 D_65678.

    stepb_tk F_6567c D_6567c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkH_tail Hs4 Hs6 Hsp SOK sp0.
  - walkH_post.
  - stepn F_65674 D_65674. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_65678 D_65678.

    stepb_ft F_6567c D_6567c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_65680 D_65680.
    walkH_tail Hs4 Hs6 Hsp SOK sp0.
  - walkH_post.
Qed.

Lemma walkRn : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0xe5dd0 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 RS ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len + n <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x656d0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xe1e50 : word) mem rom) (mkst regs' (0xe0e44 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x65668 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 RS /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 23 = Z_to_bv 64 n
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hln RD.
  eexists. split.
  -
    stepret F_e1e1c D_e1e1c (0xe5dd0 : word) ltac:(rewrite Hra; bveq).

    stepLD8 F_e5d9c D_e5d9c (Z_to_bv 64 0x656d0).

    stepn F_e5da0 D_e5da0. rewrite Hsp. sp_renorm.

    stepn F_e5da4 D_e5da4.

    stepn F_d0288 D_d0288. stepn F_d028c D_d028c.

    stepb_tk F_d0290 D_d0290 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).

    stepret F_d02bc D_d02bc (0x656d0 : word) ltac:(bveq).

    stepb_ft F_65690 D_65690 ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).

    stepn F_65694 D_65694. rewrite Ha0.

    stepb_tk F_65698 D_65698 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

    stepn F_65618 D_65618. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_6561c D_6561c. rewrite Hs6.
    stepn F_65620 D_65620.
    stepn F_65624 D_65624.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

Lemma walkR0 : forall regs mem rom (sp0 buf len : Z),
  getr regs 1 = Z_to_bv 64 0xe5dd0 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z -> (0 <= len < 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x656d0)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0xe1e50 : word) mem rom)
                 (mkst regs' (0xe1e4c : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x656e4))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0xe5d74 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loop_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len Hra Hsp Ha0 Hs3 Hs1 Hs4 SPlo SPhi Hlen RD SOK.
  eexists. split.
  - stepret F_e1e1c D_e1e1c (0xe5dd0 : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_e5d9c D_e5d9c (Z_to_bv 64 0x656d0).
    stepn F_e5da0 D_e5da0. rewrite Hsp. sp_renorm.
    stepn F_e5da4 D_e5da4.
    stepn F_d0288 D_d0288. stepn F_d028c D_d028c.
    stepb_tk F_d0290 D_d0290 ltac:(rewrite Ha0; cond_compute).
    stepret F_d02bc D_d02bc (0x656d0 : word) ltac:(bveq).
    stepb_ft F_65690 D_65690 ltac:(rewrite Ha0; cond_compute).

    stepn F_65694 D_65694. rewrite Ha0.

    stepb_ft F_65698 D_65698 ltac:(rewrite Ha0; cond_compute).

    stepn F_6569c D_6569c. rewrite Hs4.
    stepn F_656a0 D_656a0.

    stepn F_e5d14 D_e5d14. sp_renorm.
    stepST F_e5d18 D_e5d18 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x656e4) ltac:(exact SOK).
    stepn F_e5d1c D_e5d1c.
    stepret F_d54e0 D_d54e0 (0xe5d54 : word) ltac:(bveq).

    stepn F_e5d20 D_e5d20. stepn F_e5d24 D_e5d24. stepn F_e5d28 D_e5d28. stepn F_e5d2c D_e5d2c.
    stepn F_e5d30 D_e5d30. stepn F_e5d34 D_e5d34. stepn F_e5d38 D_e5d38. stepn F_e5d3c D_e5d3c.
    stepn F_e1e20 D_e1e20.
    stepn F_e1dfc D_e1dfc. stepn F_e1e00 D_e1e00. stepn F_e1e04 D_e1e04. stepn F_e1e08 D_e1e08.
    stepn F_e1e0c D_e1e0c. stepn F_e1e10 D_e1e10. stepn F_e1e14 D_e1e14.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loop_kept.
Qed.

Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0xe5d74 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x656e4)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xe1e50 : word) mem rom) (mkst regs' (0x656e4 : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r (9 :: 19 :: 23 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_e1e1c D_e1e1c (0xe5d74 : word) ltac:(rewrite Hra; bveq).

    stepn F_e5d40 D_e5d40. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_e5d44 D_e5d44. stepn F_e5d48 D_e5d48. stepn F_e5d4c D_e5d4c. stepn F_e5d50 D_e5d50.

    stepn F_e5d54 D_e5d54.
    stepn F_d0288 D_d0288. stepn F_d028c D_d028c.
    stepb_tk F_d0290 D_d0290 ltac:(cond_compute).
    stepret F_d02bc D_d02bc (0xe5d8c : word) ltac:(bveq).

    stepn F_e5d58 D_e5d58.
    stepLD8 F_e5d5c D_e5d5c (Z_to_bv 64 0x656e4).
    stepn F_e5d60 D_e5d60. rewrite Hsp. sp_renorm.
    stepret F_e5d64 D_e5d64 (0x656e4 : word) ltac:(bveq).
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
    msteps RSEGS (mkst regs (0x65668 : word) mem rom) (mkst regs' (0x656b4 : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 (len + n)
    /\ (forall r, In r (2 :: 1 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs1 Hs3 Hs7 Hs5 Hl Hn Hlc Hcap Hb.
  eexists. split.
  -
    stepn F_65628 D_65628. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.

    stepn F_6562c D_6562c. rewrite Hs1.

    stepb_ft F_65630 D_65630 ltac:(rewrite Hs5; unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

    stepn F_65634 D_65634.
    stepn F_65638 D_65638.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

Lemma walkC_full : forall regs mem rom (buf len n cap : Z),
  getr regs 9 = Z_to_bv 64 buf -> getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 < n)%Z -> (len + n = cap)%Z -> (cap <= 2 ^ 40)%Z -> (0 <= buf < 2 ^ 63)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x65668 : word) mem rom) (mkst regs' (0x6567c : word) mem rom)
    /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 cap
    /\ (forall r, In r (2 :: 1 :: 9 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs1 Hs3 Hs7 Hs5 Hl Hn Hlc Hcap Hb.
  eexists. split.
  - stepn F_65628 D_65628. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_6562c D_6562c. rewrite Hs1.

    stepb_tk F_65630 D_65630 ltac:(rewrite Hs5; unfold c_eq, bv_eqb; apply Z.eqb_eq; u_norm; lia).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loop_kept.
Qed.

Lemma walkG : forall regs mem rom (cap : Z),
  getr regs 19 = Z_to_bv 64 cap ->
  (0 < cap < 2 ^ 26)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x6567c : word) mem rom) (mkst regs' (0xd20e0 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x65690 /\ getr regs' 10 = Z_to_bv 64 (2 * cap)
    /\ getr regs' 21 = Z_to_bv 64 (2 * cap)
    /\ (forall r, In r (2 :: 9 :: 19 :: 23 :: [3; 4; 8; 18; 20; 22; 24; 25; 26; 27])%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom cap Hs3 Hc.
  eexists. split.
  -
    stepn F_6563c D_6563c.
    stepb_ft F_65640 D_65640 ltac:(rewrite Hs3, srli26_small by lia; apply c_eq_0_true).

    stepn F_65644 D_65644. rewrite Hs3, slli1_double by lia.
    stepn F_65648 D_65648.
    stepn F_6564c D_6564c.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

Lemma walkRef : forall regs mem rom,
  getr regs 19 = Z_to_bv 64 (2 ^ 26) ->
  exists regs',
    msteps RSEGS (mkst regs (0x6567c : word) mem rom) (mkst regs' (0x65830 : word) mem rom)
    /\ (forall r : reg, r <> 10 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom H19.
  eexists. split.
  - stepn F_6563c D_6563c.
    stepb_tk F_65640 D_65640 ltac:(rewrite H19, srli26_big; apply c_eq_0_false; rewrite u_small' by lia; lia).
    apply mst_refl.
  - intros r H10. rewrite !getr_other by assumption. reflexivity.
Qed.

Lemma walkG1 : forall regs mem rom (nb old len : Z),
  getr regs 10 = Z_to_bv 64 nb -> getr regs 23 = Z_to_bv 64 old -> getr regs 19 = Z_to_bv 64 len ->
  (0 < nb < 2 ^ 63)%Z -> (0 < len < 2 ^ 63)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x65690 : word) mem rom) (mkst regs' (0xe0e44 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x656ac /\ getr regs' 10 = Z_to_bv 64 nb /\ getr regs' 11 = Z_to_bv 64 old
    /\ getr regs' 12 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 nb
    /\ (forall r, In r (2 :: 19 :: 23 :: 21 :: [3; 4; 8; 18; 20; 22; 24; 25; 26; 27])%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom nb old len Ha0 Hs7 Hs3 Hnb Hl.
  eexists. split.
  -
    stepb_ft F_65650 D_65650 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

    stepn F_65654 D_65654. rewrite Ha0.

    stepb_ft F_65658 D_65658 ltac:(rewrite Hs3; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).

    stepn F_6565c D_6565c.
    stepn F_65660 D_65660. rewrite Hs7.
    stepn F_65664 D_65664. rewrite Hs3.
    stepn F_65668 D_65668.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia).
    intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

Lemma walkG2 : forall regs mem rom (old : Z),
  getr regs 23 = Z_to_bv 64 old ->
  exists regs',
    msteps RSEGS (mkst regs (0x656ac : word) mem rom) (mkst regs' (0xd1fa0 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x656b4 /\ getr regs' 10 = Z_to_bv 64 old
    /\ (forall r, In r (2 :: 9 :: 19 :: 23 :: 21 :: [3; 4; 8; 18; 20; 22; 24; 25; 26; 27])%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom old Hs7.
  eexists. split.
  - stepn F_6566c D_6566c. rewrite Hs7.
    stepn F_65670 D_65670.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption.
    intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

End FXALL2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Ref_code_13894_14104 Ref_code_1b104_1c2fc Ref_code_1d2fc_1e5f0 Ref_code_235f0_2427c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Notation RSTAGE := 0x26689%Z (only parsing).

(* [comment removed for export] *)
Definition want (cap len : Z) : Z := if (cap - len <? 65536)%Z then (cap - len)%Z else 65536%Z.

Lemma want_range : forall cap len, (0 <= len < cap)%Z -> (1 <= want cap len <= 65536)%Z /\ (want cap len <= cap - len)%Z.
Proof. intros cap len H. unfold want. destruct (Z.ltb_spec (cap - len) 65536); lia. Qed.

(* [comment removed for export] *)
Definition loop_kept : list reg := [3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.

Ltac kept_list l :=
  intros r Hr; cbv [l In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.

(* [comment removed for export] *)
Lemma walkF : forall regs mem rom (buf : Z),
  getr regs 10 = Z_to_bv 64 buf -> getr regs 21 = Z_to_bv 64 65536 -> (0 < buf < 2 ^ 64)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x13a34 : word) mem rom) (mkst regs' (0x13aac : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 RSTAGE
    /\ (forall r, In r [2; 3; 4; 8; 18; 20; 21; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf Ha0 Hs5 Hbuf. eexists. split.
  - stepb_ft F_13a34 D_13a34 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_13a38 D_13a38. rewrite Ha0.
    stepn F_13a3c D_13a3c.
    stepn F_13a40 D_13a40.
    stepn F_13a44 D_13a44.
    stepb_tk F_13a48 D_13a48 ltac:(rewrite Hs5; cond_compute).
    stepn F_13a6c D_13a6c.
    stepn F_13a70 D_13a70.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
    intros r Hr; cbv [In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma walkA : forall regs mem rom (sp0 buf len cap : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 128) -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
  getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 RSTAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x13aac : word) mem rom)
                 (mkst regs' (0x24098 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13ac8))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 RSTAGE /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0x24270 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r (23 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len cap Hsp Hs3 Hs5 Hs1 Hs4 Hs6 SPlo SPhi Hlen Hcap SOK.
  Ltac walkA_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_13abc D_13abc; rewrite Hs4;
      stepn F_13ac0 D_13ac0; rewrite Hs6;
      stepn F_13ac4 D_13ac4;
      (* [comment removed for export] *)
      stepn F_24248 D_24248; rewrite Hsp; sp_renorm;
      stepST F_2424c D_2424c (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x13ac8) ltac:(exact SOK);
      stepn F_24250 D_24250; stepn F_24254 D_24254; stepn F_24258 D_24258; stepn F_2425c D_2425c;
      stepn F_24260 D_24260; stepn F_24264 D_24264; stepn F_24268 D_24268; stepn F_2426c D_2426c;
      stepn F_240a0 D_240a0;
      stepn F_2407c D_2407c; stepn F_24080 D_24080; stepn F_24084 D_24084; stepn F_24088 D_24088;
      stepn F_2408c D_2408c; stepn F_24090 D_24090; stepn F_24094 D_24094;
      apply mst_refl.
  Ltac walkA_post :=
      repeat split; gres; try reflexivity; try assumption;
      intros r Hr; cbv [loop_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  - (* [comment removed for export] *)
    stepn F_13aac D_13aac. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    (* [comment removed for export] *)
    stepn F_13ab0 D_13ab0.
    (* [comment removed for export] *)
    stepb_tk F_13ab4 D_13ab4 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
  - stepn F_13aac D_13aac. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_13ab0 D_13ab0.
    (* [comment removed for export] *)
    stepb_ft F_13ab4 D_13ab4 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_13ab8 D_13ab8.
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
Qed.

(* [comment removed for export] *)
Definition loopB_kept : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma walkB : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0x24270 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 RSTAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len + n <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13ac8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2409c : word) mem rom) (mkst regs' (0x23640 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x13a60 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 RSTAGE /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 23 = Z_to_bv 64 n
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hln RD.
  eexists. split.
  - (* [comment removed for export] *)
    stepret F_2409c D_2409c (0x24270 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_24270 D_24270 (Z_to_bv 64 0x13ac8).
    (* [comment removed for export] *)
    stepn F_24274 D_24274. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_24278 D_24278.
    (* [comment removed for export] *)
    stepn F_1bc50 D_1bc50. stepn F_1bc54 D_1bc54.
    (* [comment removed for export] *)
    stepb_tk F_1bc58 D_1bc58 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepret F_1bc84 D_1bc84 (0x13ac8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_ft F_13ac8 D_13ac8 ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).
    (* [comment removed for export] *)
    stepn F_13acc D_13acc. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_tk F_13ad0 D_13ad0 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_13a50 D_13a50. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_13a54 D_13a54. rewrite Hs6.
    stepn F_13a58 D_13a58.
    stepn F_13a5c D_13a5c.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2_full : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap -> (0 <= len)%Z -> (0 <= n)%Z -> (len + n <= 2 ^ 62)%Z -> (len + n = cap)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x13a60 : word) mem rom) (mkst regs' (0x13a74 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 cap /\ getr regs' 23 = Z_to_bv 64 buf
    /\ (forall r, In r (2 :: loopB_kept)%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Hln Heq. eexists. split.
  - stepn F_13a60 D_13a60. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_13a64 D_13a64. rewrite Hs1.
    stepb_tk F_13a68 D_13a68 ltac:(gres; rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try (f_equal; lia).
    intros r Hr Hne; cbv [loopB_kept In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | exfalso; apply Hne; reflexivity]|]); destruct Hr.
Qed.

Lemma walkB2_more : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap -> (0 <= len)%Z -> (0 <= n)%Z -> (len + n <= 2 ^ 62)%Z -> (0 <= cap < 2 ^ 62)%Z ->
  (len + n <> cap)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x13a60 : word) mem rom) (mkst regs' (0x13aac : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 (len + n) /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r (2 :: loopB_kept)%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Hln Hcap Hne. eexists. split.
  - stepn F_13a60 D_13a60. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_13a64 D_13a64. rewrite Hs1.
    stepb_ft F_13a68 D_13a68 ltac:(gres; rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_13a6c D_13a6c.
    stepn F_13a70 D_13a70.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try (f_equal; lia).
    intros r Hr Hne'; cbv [loopB_kept In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | exfalso; apply Hne'; reflexivity | rewrite Hs1; reflexivity]|]); destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma walkBC : forall regs mem rom (sp0 buf len : Z),
  getr regs 1 = Z_to_bv 64 0x24270 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z -> (0 <= len < 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13ac8)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x2409c : word) mem rom)
                 (mkst regs' (0x24098 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13adc))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0x24214 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len Hra Hsp Ha0 Hs3 Hs1 Hs4 SPlo SPhi Hlen RD SOK.
  eexists. split.
  - stepret F_2409c D_2409c (0x24270 : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_24270 D_24270 (Z_to_bv 64 0x13ac8).
    stepn F_24274 D_24274. rewrite Hsp. sp_renorm.
    stepn F_24278 D_24278.
    stepn F_1bc50 D_1bc50. stepn F_1bc54 D_1bc54.
    stepb_tk F_1bc58 D_1bc58 ltac:(rewrite Ha0; cond_compute).
    stepret F_1bc84 D_1bc84 (0x13ac8 : word) ltac:(bveq).
    stepb_ft F_13ac8 D_13ac8 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_13acc D_13acc. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_ft F_13ad0 D_13ad0 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_13ad4 D_13ad4. rewrite Hs4.
    stepn F_13ad8 D_13ad8.
    (* [comment removed for export] *)
    stepn F_241e8 D_241e8. sp_renorm.
    stepST F_241ec D_241ec (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x13adc) ltac:(exact SOK).
    stepn F_241f0 D_241f0.
    stepret F_1d848 D_1d848 (0x241f4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_241f4 D_241f4. stepn F_241f8 D_241f8. stepn F_241fc D_241fc. stepn F_24200 D_24200.
    stepn F_24204 D_24204. stepn F_24208 D_24208. stepn F_2420c D_2420c. stepn F_24210 D_24210.
    stepn F_240a0 D_240a0.
    stepn F_2407c D_2407c. stepn F_24080 D_24080. stepn F_24084 D_24084. stepn F_24088 D_24088.
    stepn F_2408c D_2408c. stepn F_24090 D_24090. stepn F_24094 D_24094.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x24214 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13adc)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2409c : word) mem rom) (mkst regs' (0x13adc : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r (23 :: loopB_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_2409c D_2409c (0x24214 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepn F_24214 D_24214. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_24218 D_24218. stepn F_2421c D_2421c. stepn F_24220 D_24220. stepn F_24224 D_24224.
    (* [comment removed for export] *)
    stepn F_24228 D_24228.
    stepn F_1bc50 D_1bc50. stepn F_1bc54 D_1bc54.
    stepb_tk F_1bc58 D_1bc58 ltac:(cond_compute).
    stepret F_1bc84 D_1bc84 (0x2422c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2422c D_2422c.
    stepLD8 F_24230 D_24230 (Z_to_bv 64 0x13adc).
    stepn F_24234 D_24234. rewrite Hsp. sp_renorm.
    stepret F_24238 D_24238 (0x13adc : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

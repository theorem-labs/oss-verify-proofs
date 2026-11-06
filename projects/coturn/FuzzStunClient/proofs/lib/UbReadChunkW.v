(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Ub_code_13974_14104 Ub_code_1b104_1c2fc Ub_code_1d2fc_1e5e4 Ub_code_235f0_245f0 Ub_code_245f0_24724   .
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

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Notation RSTAGE := 0x26b39%Z (only parsing).

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
    msteps RSEGS (mkst regs (0x13b14 : word) mem rom) (mkst regs' (0x13b8c : word) mem rom)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 RSTAGE
    /\ (forall r, In r [2; 3; 4; 8; 18; 20; 21; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf Ha0 Hs5 Hbuf. eexists. split.
  - stepb_ft F_13b14 D_13b14 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_13b18 D_13b18. rewrite Ha0.
    stepn F_13b1c D_13b1c.
    stepn F_13b20 D_13b20.
    stepn F_13b24 D_13b24.
    stepb_tk F_13b28 D_13b28 ltac:(rewrite Hs5; cond_compute).
    stepn F_13b4c D_13b4c.
    stepn F_13b50 D_13b50.
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
    msteps RSEGS (mkst regs (0x13b8c : word) mem rom)
                 (mkst regs' (0x24540 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13ba8))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 RSTAGE /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0x24718 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r (23 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len cap Hsp Hs3 Hs5 Hs1 Hs4 Hs6 SPlo SPhi Hlen Hcap SOK.
  Ltac walkA_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_13b9c D_13b9c; rewrite Hs4;
      stepn F_13ba0 D_13ba0; rewrite Hs6;
      stepn F_13ba4 D_13ba4;
      (* [comment removed for export] *)
      stepn F_246f0 D_246f0; rewrite Hsp; sp_renorm;
      stepST F_246f4 D_246f4 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x13ba8) ltac:(exact SOK);
      stepn F_246f8 D_246f8; stepn F_246fc D_246fc; stepn F_24700 D_24700; stepn F_24704 D_24704;
      stepn F_24708 D_24708; stepn F_2470c D_2470c; stepn F_24710 D_24710; stepn F_24714 D_24714;
      stepn F_24548 D_24548;
      stepn F_24524 D_24524; stepn F_24528 D_24528; stepn F_2452c D_2452c; stepn F_24530 D_24530;
      stepn F_24534 D_24534; stepn F_24538 D_24538; stepn F_2453c D_2453c;
      apply mst_refl.
  Ltac walkA_post :=
      repeat split; gres; try reflexivity; try assumption;
      intros r Hr; cbv [loop_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  - (* [comment removed for export] *)
    stepn F_13b8c D_13b8c. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    (* [comment removed for export] *)
    stepn F_13b90 D_13b90.
    (* [comment removed for export] *)
    stepb_tk F_13b94 D_13b94 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
  - stepn F_13b8c D_13b8c. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_13b90 D_13b90.
    (* [comment removed for export] *)
    stepb_ft F_13b94 D_13b94 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_13b98 D_13b98.
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
Qed.

(* [comment removed for export] *)
Definition loopB_kept : list reg := [3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma walkB : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0x24718 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 RSTAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len + n <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13ba8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x24544 : word) mem rom) (mkst regs' (0x23ae8 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x13b40 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 RSTAGE /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 23 = Z_to_bv 64 n
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hln RD.
  eexists. split.
  - (* [comment removed for export] *)
    stepret F_24544 D_24544 (0x24718 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_24718 D_24718 (Z_to_bv 64 0x13ba8).
    (* [comment removed for export] *)
    stepn F_2471c D_2471c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_24720 D_24720.
    (* [comment removed for export] *)
    stepn F_1c0f8 D_1c0f8. stepn F_1c0fc D_1c0fc.
    (* [comment removed for export] *)
    stepb_tk F_1c100 D_1c100 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepret F_1c12c D_1c12c (0x13ba8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_ft F_13ba8 D_13ba8 ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).
    (* [comment removed for export] *)
    stepn F_13bac D_13bac. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_tk F_13bb0 D_13bb0 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_13b30 D_13b30. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_13b34 D_13b34. rewrite Hs6.
    stepn F_13b38 D_13b38.
    stepn F_13b3c D_13b3c.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2_full : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap -> (0 <= len)%Z -> (0 <= n)%Z -> (len + n <= 2 ^ 62)%Z -> (len + n = cap)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x13b40 : word) mem rom) (mkst regs' (0x13b54 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 cap /\ getr regs' 23 = Z_to_bv 64 buf
    /\ (forall r, In r (2 :: loopB_kept)%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Hln Heq. eexists. split.
  - stepn F_13b40 D_13b40. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_13b44 D_13b44. rewrite Hs1.
    stepb_tk F_13b48 D_13b48 ltac:(gres; rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
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
    msteps RSEGS (mkst regs (0x13b40 : word) mem rom) (mkst regs' (0x13b8c : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 (len + n) /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r (2 :: loopB_kept)%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Hln Hcap Hne. eexists. split.
  - stepn F_13b40 D_13b40. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_13b44 D_13b44. rewrite Hs1.
    stepb_ft F_13b48 D_13b48 ltac:(gres; rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepn F_13b4c D_13b4c.
    stepn F_13b50 D_13b50.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try (f_equal; lia).
    intros r Hr Hne'; cbv [loopB_kept In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | exfalso; apply Hne'; reflexivity | rewrite Hs1; reflexivity]|]); destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma walkBC : forall regs mem rom (sp0 buf len : Z),
  getr regs 1 = Z_to_bv 64 0x24718 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z -> (0 <= len < 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13ba8)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x24544 : word) mem rom)
                 (mkst regs' (0x24540 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13bbc))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0x246bc /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len Hra Hsp Ha0 Hs3 Hs1 Hs4 SPlo SPhi Hlen RD SOK.
  eexists. split.
  - stepret F_24544 D_24544 (0x24718 : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_24718 D_24718 (Z_to_bv 64 0x13ba8).
    stepn F_2471c D_2471c. rewrite Hsp. sp_renorm.
    stepn F_24720 D_24720.
    stepn F_1c0f8 D_1c0f8. stepn F_1c0fc D_1c0fc.
    stepb_tk F_1c100 D_1c100 ltac:(rewrite Ha0; cond_compute).
    stepret F_1c12c D_1c12c (0x13ba8 : word) ltac:(bveq).
    stepb_ft F_13ba8 D_13ba8 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_13bac D_13bac. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_ft F_13bb0 D_13bb0 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_13bb4 D_13bb4. rewrite Hs4.
    stepn F_13bb8 D_13bb8.
    (* [comment removed for export] *)
    stepn F_24690 D_24690. sp_renorm.
    stepST F_24694 D_24694 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x13bbc) ltac:(exact SOK).
    stepn F_24698 D_24698.
    stepret F_1dcf0 D_1dcf0 (0x2469c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2469c D_2469c. stepn F_246a0 D_246a0. stepn F_246a4 D_246a4. stepn F_246a8 D_246a8.
    stepn F_246ac D_246ac. stepn F_246b0 D_246b0. stepn F_246b4 D_246b4. stepn F_246b8 D_246b8.
    stepn F_24548 D_24548.
    stepn F_24524 D_24524. stepn F_24528 D_24528. stepn F_2452c D_2452c. stepn F_24530 D_24530.
    stepn F_24534 D_24534. stepn F_24538 D_24538. stepn F_2453c D_2453c.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x246bc -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13bbc)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x24544 : word) mem rom) (mkst regs' (0x13bbc : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r (23 :: loopB_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_24544 D_24544 (0x246bc : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepn F_246bc D_246bc. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_246c0 D_246c0. stepn F_246c4 D_246c4. stepn F_246c8 D_246c8. stepn F_246cc D_246cc.
    (* [comment removed for export] *)
    stepn F_246d0 D_246d0.
    stepn F_1c0f8 D_1c0f8. stepn F_1c0fc D_1c0fc.
    stepb_tk F_1c100 D_1c100 ltac:(cond_compute).
    stepret F_1c12c D_1c12c (0x246d4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_246d4 D_246d4.
    stepLD8 F_246d8 D_246d8 (Z_to_bv 64 0x13bbc).
    stepn F_246dc D_246dc. rewrite Hsp. sp_renorm.
    stepret F_246e0 D_246e0 (0x13bbc : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

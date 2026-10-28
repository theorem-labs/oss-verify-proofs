(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac Frame MemSplit LibMaskBits
  SumWalkTac RefMemcpyLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  RefNodes PhaseG LibKnowFrame RefReadLib HUMemcpyBase HUMemcpy HUExitBase HUReadBase HUReadStage.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
 HU_code_26b000_26c000 HU_code_26e000_26f000 HU_code_276000_277000 HU_code_277000_278000 HU_code_27a000_27b000 HU_code_dd000_de000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module H0ReadChunkW.

(* [comment removed for export] *)
Definition want (cap len : Z) : Z := if (cap - len <? 65536)%Z then (cap - len)%Z else 65536%Z.

Lemma want_range : forall cap len, (0 <= len < cap)%Z -> (1 <= want cap len <= 65536)%Z /\ (want cap len <= cap - len)%Z.
Proof. intros cap len H. unfold want. destruct (Z.ltb_spec (cap - len) 65536); lia. Qed.

(* [comment removed for export] *)
Definition loop_kept : list reg := [3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition loopB_kept : list reg := [3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

(* [comment removed for export] *)
Definition loopB2_kept : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 10; 18; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Ltac kept_list l :=
  intros r Hr; cbv [l In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.

(* [comment removed for export] *)
Lemma walkA : forall regs mem rom (sp0 buf len cap : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 128) -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
  getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 STAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0xe1a68 : word) mem rom)
                 (mkst regs' (0x2bd1dc : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1a88))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 STAGE /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0x2c071c /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 9 = Z_to_bv 64 buf /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r (23 :: loopB_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len cap Hsp Hs3 Hs5 Hs1 Hs4 Hs6 SPlo SPhi Hlen Hcap SOK.
  (* [comment removed for export] *)
  Ltac walkA_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_dd140 D_dd140; rewrite Hs4;
      stepn F_dd144 D_dd144; rewrite Hs6;
      stepn F_dd148 D_dd148;
      stepjr F_dd14c D_dd14c (0x2c0a80 : word) ltac:(gres; first [reflexivity | bveq]); vnorm;    (* [comment removed for export] *)
      (* [comment removed for export] *)
      stepn F_27ab08 D_27ab08; rewrite Hsp; sp_renorm;
      stepST F_27ab0c D_27ab0c (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0xe1a88) ltac:(exact SOK);
      stepn F_27ab10 D_27ab10; stepn F_27ab14 D_27ab14; stepn F_27ab18 D_27ab18; stepn F_27ab1c D_27ab1c;
      stepn F_27ab20 D_27ab20; stepn F_27ab24 D_27ab24; stepn F_27ab28 D_27ab28; stepn F_27ab2c D_27ab2c;
      stepn F_2775f8 D_2775f8;
      stepn F_2775d4 D_2775d4; stepn F_2775d8 D_2775d8; stepn F_2775dc D_2775dc; stepn F_2775e0 D_2775e0;
      stepn F_2775e4 D_2775e4; stepn F_2775e8 D_2775e8; stepn F_2775ec D_2775ec;
      apply mst_refl.
  Ltac walkA_post :=
      repeat split; gres; try reflexivity; try assumption;
      intros r Hr; cbv [loopB_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  - (* [comment removed for export] *)
    stepn F_dd130 D_dd130. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    (* [comment removed for export] *)
    stepn F_dd134 D_dd134.
    (* [comment removed for export] *)
    stepb_tk F_dd138 D_dd138 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
  - stepn F_dd130 D_dd130. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_dd134 D_dd134.
    (* [comment removed for export] *)
    stepb_ft F_dd138 D_dd138 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_dd13c D_dd13c.
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
Qed.

(* [comment removed for export] *)
Lemma walkB1 : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0x2c071c -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 STAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len + n <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe1a88)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2bd1e0 : word) mem rom) (mkst regs' (0x2bc024 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0xe1a10 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 STAGE /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 23 = Z_to_bv 64 n /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hbn RD.
  eexists. split.
  - (* [comment removed for export] *)
    stepret F_2775f4 D_2775f4 (0x2c071c : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_27ab30 D_27ab30 (Z_to_bv 64 0xe1a88).
    (* [comment removed for export] *)
    stepn F_27ab34 D_27ab34. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_27ab38 D_27ab38.
    (* [comment removed for export] *)
    stepn F_26bd58 D_26bd58. stepn F_26bd5c D_26bd5c.
    (* [comment removed for export] *)
    stepb_tk F_26bd60 D_26bd60 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepret F_26bd8c D_26bd8c (0xe1a88 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_ft F_dd150 D_dd150 ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).
    (* [comment removed for export] *)
    stepn F_dd154 D_dd154. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_tk F_dd158 D_dd158 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_dd0c4 D_dd0c4. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_dd0c8 D_dd0c8. rewrite Hs6.
    stepn F_dd0cc D_dd0cc.
    stepn F_dd0d0 D_dd0d0.
    stepjr F_dd0d4 D_dd0d4 (0x2bba08 : word) ltac:(gres; first [reflexivity | bveq]); vnorm.    (* [comment removed for export] *)
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2_more : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 <= n)%Z -> (len + n < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xe1a10 : word) mem rom) (mkst regs' (0xe1a68 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 (len + n) /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r loopB2_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Hlt Hcap.
  eexists. split.
  - (* [comment removed for export] *)
    stepn F_dd0d8 D_dd0d8. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    (* [comment removed for export] *)
    stepn F_dd0dc D_dd0dc. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_ft F_dd0e0 D_dd0e0 ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_dd0e4 D_dd0e4.
    stepn F_dd0e8 D_dd0e8.
    apply mst_refl.
  - split; [|split; [|split]];
      [gres; first [assumption | reflexivity | f_equal; lia] | gres; first [assumption | reflexivity] | gres; first [assumption | reflexivity] |].
    kept_list loopB2_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2_full : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf ->
  getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 <= n)%Z -> (len + n = cap)%Z -> (cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0xe1a10 : word) mem rom) (mkst regs' (0xe1a24 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 cap /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r loopB2_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Heq Hcap.
  eexists. split.
  - stepn F_dd0d8 D_dd0d8. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_dd0dc D_dd0dc. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_tk F_dd0e0 D_dd0e0 ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
    apply mst_refl.
  - split; [|split; [|split]];
      [gres; first [assumption | reflexivity | f_equal; lia] | gres; first [assumption | reflexivity] | gres; first [assumption | reflexivity] |].
    kept_list loopB2_kept.
Qed.

(* [comment removed for export] *)
Lemma walkBC : forall regs mem rom (sp0 buf len : Z),
  getr regs 1 = Z_to_bv 64 0x2c071c -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z -> (0 <= len < 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe1a88)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x2bd1e0 : word) mem rom)
                 (mkst regs' (0x2bd1dc : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1aa0))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0x2c0680 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len Hra Hsp Ha0 Hs3 Hs1 Hs4 SPlo SPhi Hlen RD SOK.
  eexists. split.
  - stepret F_2775f4 D_2775f4 (0x2c071c : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_27ab30 D_27ab30 (Z_to_bv 64 0xe1a88).
    stepn F_27ab34 D_27ab34. rewrite Hsp. sp_renorm.
    stepn F_27ab38 D_27ab38.
    stepn F_26bd58 D_26bd58. stepn F_26bd5c D_26bd5c.
    stepb_tk F_26bd60 D_26bd60 ltac:(rewrite Ha0; cond_compute).
    stepret F_26bd8c D_26bd8c (0xe1a88 : word) ltac:(bveq).
    stepb_ft F_dd150 D_dd150 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_dd154 D_dd154. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_ft F_dd158 D_dd158 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_dd15c D_dd15c. rewrite Hs4.
    stepn F_dd160 D_dd160.
    stepjr F_dd164 D_dd164 (0x2c0a98 : word) ltac:(gres; first [reflexivity | bveq]); vnorm.    (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepn F_27aa68 D_27aa68. sp_renorm.
    stepST F_27aa6c D_27aa6c (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0xe1aa0) ltac:(exact SOK).
    stepn F_27aa70 D_27aa70.
    stepret F_26ebd0 D_26ebd0 (0x2c0660 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_27aa74 D_27aa74. stepn F_27aa78 D_27aa78. stepn F_27aa7c D_27aa7c. stepn F_27aa80 D_27aa80.
    stepn F_27aa84 D_27aa84. stepn F_27aa88 D_27aa88. stepn F_27aa8c D_27aa8c. stepn F_27aa90 D_27aa90.
    stepn F_2775f8 D_2775f8.
    stepn F_2775d4 D_2775d4. stepn F_2775d8 D_2775d8. stepn F_2775dc D_2775dc. stepn F_2775e0 D_2775e0.
    stepn F_2775e4 D_2775e4. stepn F_2775e8 D_2775e8. stepn F_2775ec D_2775ec.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x2c0680 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe1aa0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2bd1e0 : word) mem rom) (mkst regs' (0xe1aa0 : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r (23 :: loopB_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_2775f4 D_2775f4 (0x2c0680 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepn F_27aa94 D_27aa94. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_27aa98 D_27aa98. stepn F_27aa9c D_27aa9c. stepn F_27aaa0 D_27aaa0. stepn F_27aaa4 D_27aaa4.
    (* [comment removed for export] *)
    stepn F_27aaa8 D_27aaa8.
    stepn F_26bd58 D_26bd58. stepn F_26bd5c D_26bd5c.
    stepb_tk F_26bd60 D_26bd60 ltac:(cond_compute).
    stepret F_26bd8c D_26bd8c (0x2c0698 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_27aaac D_27aaac.
    stepLD8 F_27aab0 D_27aab0 (Z_to_bv 64 0xe1aa0).
    stepn F_27aab4 D_27aab4. rewrite Hsp. sp_renorm.
    stepret F_27aab8 D_27aab8 (0xe1aa0 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

End H0ReadChunkW.
Import H0ReadChunkW.
Import SX2. Import SX2S.
Import ConeCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dropz_dropz : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  dropz a (dropz b l) = dropz (b + a) l.
Proof.
  intros a b l Ha Hb. unfold dropz. rewrite skipn_skipn. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma pref_chain : forall (len n m : Z) l, (0 <= len)%Z -> (0 <= n)%Z -> (0 <= m)%Z ->
  pref n (dropz len l) ++ pref m (dropz (len + n) l) = pref (n + m) (dropz len l).
Proof.
  intros len n m l Hl Hn Hm. rewrite <- (dropz_dropz n len) by lia. apply pref_app; lia.
Qed.

Lemma pref_0 : forall l, pref 0 l = [].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma read_chunk : forall content (len want : Z),
  (0 <= len <= Z.of_nat (length content))%Z -> (len < 2 ^ 62)%Z -> (0 <= want < 2 ^ 62)%Z ->
  let bs := file_read content (Z_to_bv 64 len) (Z_to_bv 64 want) in
  let n := Z.of_nat (length bs) in
  n = Z.min want (Z.of_nat (length content) - len) /\ bs = pref n (dropz len content).
Proof.
  intros content len want Hlen Hlen2 Hwant. cbn zeta.
  rewrite file_read_pref by lia.
  pose proof (pref_length want (dropz len content) ltac:(lia)) as PL.
  pose proof (dropz_length len content ltac:(lia)) as DL.
  split; [lia|].
  destruct (Z.le_gt_cases want (Z.of_nat (length content) - len)) as [Hle|Hgt].
  - f_equal. lia.
  - rewrite (pref_all want) by lia. symmetry. apply pref_all. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mid_regs (R : bvmap 5 word) (sp0 buf len cap : Z) : Prop :=
  getr R 2 = Z_to_bv 64 (sp0 - 128) /\ getr R 9 = Z_to_bv 64 buf /\ getr R 19 = Z_to_bv 64 len
  /\ getr R 20 = Z_to_bv 64 3 /\ getr R 21 = Z_to_bv 64 cap /\ getr R 22 = Z_to_bv 64 STAGE.

(* [comment removed for export] *)
Definition loop_post_regs (R R' : bvmap 5 word) (sp0 buf len' s7v : Z) : Prop :=
  getr R' 2 = Z_to_bv 64 (sp0 - 128) /\ getr R' 9 = Z_to_bv 64 buf /\ getr R' 19 = Z_to_bv 64 len'
  /\ getr R' 22 = Z_to_bv 64 STAGE /\ getr R' 23 = Z_to_bv 64 s7v
  /\ (forall r, In r loop_kept -> getr R' r = getr R r).

(* [comment removed for export] *)
Definition loop_regions (sp0 buf len len' : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp0 - 136), 8%Z); (Z_to_bv 64 STAGE, 65536%Z); (Z_to_bv 64 (buf + len), (len' - len)%Z)].

(* [comment removed for export] *)
Definition loop_post_mem (content : list byte) (M M' : word -> option byte) (sp0 buf len len' : Z) : Prop :=
  frame_mod M M' (loop_regions sp0 buf len len')
  /\ rdn RSEGS M' (Z_to_bv 64 (buf + len)) (Z.to_nat (len' - len)) = Some (pref (len' - len) (dropz len content)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma loop_kept_B : forall r, In r loop_kept -> In r loopB_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [loopB_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma loop_kept_callee : forall r, In r loop_kept -> In r callee_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [callee_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma loop_kept_B2 : forall r, In r loop_kept -> In r loopB2_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [loopB2_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma kept_regupd10 : forall X (v : word) r, In r loop_kept -> getr (regupd X 10 v) r = getr X r.
Proof.
  intros X v r Hr. cbv [loop_kept In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [rewrite getr_other by reg_neq_tac; reflexivity|]). destruct Hr.
Qed.

Lemma post_regs_compose : forall R R2 R' sp0 buf len' s7v,
  loop_post_regs R2 R' sp0 buf len' s7v ->
  (forall r, In r loop_kept -> getr R2 r = getr R r) ->
  loop_post_regs R R' sp0 buf len' s7v.
Proof.
  intros R R2 R' sp0 buf len' s7v (P2 & P9 & P19 & P22 & P23 & PK) HK.
  repeat split; try assumption. intros r Hr. rewrite (PK r Hr). apply HK, Hr.
Qed.

(* [comment removed for export] *)
Lemma outside_In : forall x rs b n, outside x rs -> In (b, n) rs -> ~ in_rng x b n.
Proof.
  intros x rs b n. induction rs as [|[c m] rs IH]; cbn [outside In]; [tauto|].
  intros [H1 H2] [E|Hin]; [injection E as -> ->; exact H1 | apply IH; assumption].
Qed.

Lemma frame_mod_wbytes_in : forall M (a : word) bs rs (b : word) (n : Z),
  In (b, n) rs ->
  (bv_unsigned b <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned b + n)%Z ->
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  frame_mod M (wbytes M a bs) rs.
Proof.
  intros M a bs rs b n Hin Hlo Hhi Hnw. split; [|apply wbytes_grows].
  intros x Hout. apply Frame.wbytes_outside; [|exact Hnw].
  intros Hx. apply (outside_In x rs b n Hout Hin). unfold in_rng in *. lia.
Qed.

Lemma loop_regions_mono : forall (sp0 buf len len1 len2 : Z) x,
  (0 <= buf)%Z -> (0 <= len <= len1)%Z -> (len1 <= len2)%Z -> (buf + len2 < 2 ^ 64)%Z ->
  outside x (loop_regions sp0 buf len len2) ->
  outside x (loop_regions sp0 buf len len1) /\ outside x (loop_regions sp0 buf len1 len2).
Proof.
  intros sp0 buf len len1 len2 x Hb Hl Hl2 Hnw [O1 [O2 [O3 _]]]. cbn [outside loop_regions].
  unfold in_rng in *. rewrite (u_small (buf + len)) in O3 by lia.
  repeat split; try assumption; rewrite ?(u_small (buf + len)), ?(u_small (buf + len1)) by lia; lia.
Qed.

Section PostAlgebra.
  Variables (content : list byte) (M : word -> option byte) (sp0 buf len n : Z) (bs : list byte).
  Hypothesis Hlen : (0 <= len)%Z.
  Hypothesis Hn : (0 <= n <= 65536)%Z.
  Hypothesis Hbuf : (0x354000 <= buf)%Z.
  Hypothesis Hsp : (sp0 <= 2 ^ 63)%Z.
  Hypothesis Hbl : Z.of_nat (length bs) = n.
  Hypothesis Hbs : bs = pref n (dropz len content).

  #[local] Notation M1 := (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1a88))) (only parsing).
  #[local] Notation M2 := (wbytes M1 (Z_to_bv 64 STAGE) bs) (only parsing).
  #[local] Notation M3 := (wbytes M2 (Z_to_bv 64 (buf + len)) bs) (only parsing).

  (* [comment removed for export] *)
  Lemma post_mem_here : (buf + len + n <= sp0 - 144)%Z ->
    loop_post_mem content M M3 sp0 buf len (len + n).
  Proof.
    intros Hb. pose proof (length_N_to_le_bytes 8 (Z_to_bv 64 0xe1a88)) as L8.
    set (rs := loop_regions sp0 buf len (len + n)).
    assert (F1 : frame_mod M M1 rs).
    { apply (frame_mod_wbytes_in M _ _ rs (Z_to_bv 64 (sp0 - 136)) 8);
        [subst rs; cbn [loop_regions In]; tauto | lia | rewrite L8; lia | rewrite L8, u_small by lia; lia]. }
    assert (F2 : frame_mod M1 M2 rs).
    { apply (frame_mod_wbytes_in _ _ _ rs (Z_to_bv 64 STAGE) 65536);
        [subst rs; cbn [loop_regions In]; tauto | lia | unfold STAGE; rewrite Hbl, !u_small by lia; lia | unfold STAGE; rewrite u_small by lia; lia]. }
    assert (F3 : frame_mod M2 M3 rs).
    { apply (frame_mod_wbytes_in _ _ _ rs (Z_to_bv 64 (buf + len)) (len + n - len));
        [subst rs; cbn [loop_regions In]; tauto | lia | rewrite Hbl, !u_small by lia; lia | rewrite u_small by lia; lia]. }
    split.
    - eapply frame_mod_trans_same; [eapply frame_mod_trans_same; [exact F1 | exact F2] | exact F3].
    - replace (len + n - len)%Z with n by lia. rewrite <- Hbs. replace (Z.to_nat n) with (length bs) by lia.
      apply rdn_wbytes_self. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma post_mem_compose : forall M' (len' : Z),
    (len + n <= len')%Z -> (buf + len' <= sp0 - 144)%Z ->
    loop_post_mem content M3 M' sp0 buf (len + n) len' ->
    loop_post_mem content M M' sp0 buf len len'.
  Proof.
    intros M' len' Hl' Hb' [FR RD]. pose proof (length_N_to_le_bytes 8 (Z_to_bv 64 0xe1a88)) as L8.
    pose proof (post_mem_here ltac:(lia)) as [FRh RDh]. split.
    - eapply frame_mod_weaken; [ | exact (frame_mod_trans _ _ _ _ _ FRh FR)].
      intros a Ha. apply outside_app. apply (loop_regions_mono sp0 buf len (len + n) len'); try lia. exact Ha.
    - replace (Z.to_nat (len' - len)) with (length bs + Z.to_nat (len' - (len + n)))%nat by lia.
      replace (pref (len' - len) (dropz len content)) with (bs ++ pref (len' - (len + n)) (dropz (len + n) content))
        by (rewrite Hbs at 1; rewrite pref_chain by lia; f_equal; lia).
      apply SeqExec.rdn_app.
      + rewrite (frame_mod_rdn RSEGS _ M' _ (length bs) (Z_to_bv 64 (buf + len)) FR).
        * apply rdn_wbytes_self. rewrite u_small by lia. lia.
        * intros i Hi. rewrite (u_small (buf + len)) by lia. cbn [outside loop_regions]. unfold in_rng, STAGE. rewrite ?Hbl, !u_small by lia. repeat split; lia.
        * rewrite u_small by lia. lia.
      + replace (Z_to_bv 64 (buf + len) + nat_to_word (length bs)) with (Z_to_bv 64 (buf + (len + n))); [exact RD|].
        unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
  Qed.
End PostAlgebra.

(* [comment removed for export] *)
Lemma post_mem_end : forall content M (sp0 buf len : Z) (ra1 ra2 : word),
  (0 <= len)%Z -> (sp0 <= 2 ^ 63)%Z -> (144 <= sp0)%Z -> (0 <= buf)%Z -> (buf + len < 2 ^ 64)%Z ->
  loop_post_mem content M
    (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra1)) (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra2))
    sp0 buf len len.
Proof.
  intros content M sp0 buf len ra1 ra2 Hl Hsp Hsp' Hb Hbl.
  pose proof (length_N_to_le_bytes 8 ra1) as L1. pose proof (length_N_to_le_bytes 8 ra2) as L2.
  set (rs := loop_regions sp0 buf len len).
  set (Ma := wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra1)).
  assert (F1 : frame_mod M Ma rs).
  { apply (frame_mod_wbytes_in M _ _ rs (Z_to_bv 64 (sp0 - 136)) 8);
      [subst rs; cbn [loop_regions In]; tauto | lia | rewrite L1; lia | rewrite L1, u_small by lia; lia]. }
  assert (F2 : frame_mod Ma (wbytes Ma (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra2)) rs).
  { apply (frame_mod_wbytes_in Ma _ _ rs (Z_to_bv 64 (sp0 - 136)) 8);
      [subst rs; cbn [loop_regions In]; tauto | lia | rewrite L2; lia | rewrite L2, u_small by lia; lia]. }
  split.
  - eapply frame_mod_trans_same; [exact F1 | exact F2].
  - rewrite Z.sub_diag. cbn [Z.to_nat rdn]. rewrite pref_0. reflexivity.
Qed.

Lemma stage_writable_grows : forall M M', mem_grows M M' -> stage_writable M -> stage_writable M'.
Proof. intros M M' G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.

Section ChunkLoop.
  Variables (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) (V : VmMaps).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).

  Theorem chunk_loop_mid : forall (mode : bool) (Q : config -> Prop) (fuel : nat)
      (R : bvmap 5 word) (M : word -> option byte) (sp0 buf len cap : Z) (K : TSet),
    (cap - len <= Z.of_nat fuel)%Z ->
    mid_regs R sp0 buf len cap ->
    (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z -> (0x354000 <= buf)%Z -> (buf + cap <= sp0 - 8388608)%Z ->
    (0x7fff80000000 <= sp0 <= 0x800000000000)%Z ->
    (len <= L)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 136)) 8 = true ->
    store_ok RSEGS M (Z_to_bv 64 (buf + len)) (Z.to_nat (cap - len)) = true ->
    stage_writable M ->
    (* [comment removed for export] *)
    ((cap <= L)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf cap buf -> loop_post_mem content M M' sp0 buf len cap ->
        GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1a24) M' (seg_rom RSEGS)) (modelG cap V))) ->
    (* [comment removed for export] *)
    ((L < cap)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf L 0 -> loop_post_mem content M M' sp0 buf len L ->
        GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1aa0) M' (seg_rom RSEGS)) (model_post V stdin0 fs0 tid))) ->
    GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG len V)).
  Proof.
    induction fuel as [|fuel IH]; intros R M sp0 buf len cap K Hfuel (R2 & R9 & R19 & R20 & R21 & R22) Hlen Hcap Hbuf Hbc Hsp HlenL SOKs SOKb SOKst HFULL HEND.
    { exfalso. cbn in Hfuel. lia. }
    pose proof (want_range cap len Hlen) as [Hw1 Hw2].
    pose proof rw_bytes_max_ge17 as HRW.
    (* [comment removed for export] *)
    destruct (walkA R M (seg_rom RSEGS) sp0 buf len cap R2 R19 R21 R9 R20 R22
               ltac:(lia) ltac:(lia) Hlen Hcap SOKs)
      as (R1 & RUN1 & A17 & A10 & A11 & A12 & A1 & A2 & A9 & A19 & AK0).
    assert (AK : forall r, In r loop_kept -> getr R1 r = getr R r) by (intros r Hr; apply AK0; right; apply loop_kept_B, Hr).
    replace (Z_to_bv 64 0xe1a68) with (0xe1a68 : word) by (apply bv_eq; reflexivity).
    eapply gg_msteps; [reflexivity | reflexivity | exact RUN1 |]. clear RUN1.
    set (M1 := wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1a88))).
    assert (GR1 : mem_grows M M1) by (subst M1; apply wbytes_grows).
    assert (SOK1s : store_ok RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = true) by (eapply store_ok_mono; [exact GR1 | exact SOKs]).
    assert (RD1 : rdn RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe1a88)))
      by (apply rdn_wbytes_hit8; rewrite u_small by lia; lia).
    (* [comment removed for export] *)
    pose proof (read_chunk content len (want cap len) ltac:(lia) ltac:(lia) ltac:(lia)) as RC. cbn zeta in RC.
    destruct RC as [RN RB].
    remember (file_read content (Z_to_bv 64 len) (Z_to_bv 64 (want cap len))) as bs eqn:Hbs.
    set (n := Z.of_nat (length bs)) in *.
    eapply (gg_read_file RSEGS mode Q R1 (0x2bd1dc : word) M1 (modelG len V) W_2775f0 (Z_to_bv 64 3) path (Z_to_bv 64 len) content (want cap len) K F_2775f0 E_2775f0).
    - reflexivity.
    - reflexivity.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - reflexivity.
    - exact Hfile.
    - exact A12.
    - lia.
    - lia.
    - lia.
    - rewrite A11. eapply store_ok_mono; [exact GR1|].
      replace STAGE with (STAGE + 0)%Z by lia. apply SOKst; lia.
    - rewrite A11. apply access_okb_true_intro; [lia|]. unfold STAGE. rewrite u_small by lia. lia.
    - cbv zeta. rewrite A12, A11, <- Hbs. rewrite modelG_read.
      change (len_word bs) with (Z_to_bv 64 n).
      replace (Z_to_bv 64 len + Z_to_bv 64 n) with (Z_to_bv 64 (len + n))
        by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; rewrite bv_wrap_small; [lia | unfold bv_modulus; lia]).
      change (mkModelA (fds_file path (Z_to_bv 64 (len + n))) V stdin0 fs0 None (Some tid) None) with (modelG (len + n) V).
      replace (v_addi (0x2bd1dc : word) 4) with (0x2bd1e0 : word) by (apply bv_eq; reflexivity).
      set (M2 := wbytes M1 (Z_to_bv 64 STAGE) bs).
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      + (* [comment removed for export] *)
        assert (bs = []) as Hnil by (destruct bs; [reflexivity | subst n; cbn in Hn0; lia]).
        assert (HLe : L = len) by lia.
        subst M2. rewrite Hnil. cbn [wbytes]. rewrite Hn0.
        destruct (walkBC (regupd R1 10 (Z_to_bv 64 0)) M1 (seg_rom RSEGS) sp0 buf len
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 20%bv) by (cbv; noncert_qtauto); exact R20)
                   ltac:(lia) ltac:(lia) ltac:(lia) RD1 SOK1s)
          as (R3 & RUN3 & C17 & C10 & C1 & C2 & C19 & C23 & CK).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN3 |]. clear RUN3.
        set (M3 := wbytes M1 (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1aa0))).
        (* [comment removed for export] *)
        eapply (gg_close RSEGS mode Q R3 (0x2bd1dc : word) M3 (modelG (len + 0) V) W_2775f0 (Z_to_bv 64 3) _ K F_2775f0 E_2775f0).
        * reflexivity.
        * reflexivity.
        * exact C17.
        * exact C10.
        * rewrite u_small by lia. lia.
        * reflexivity.
        * rewrite modelG_close.
          replace (v_addi (0x2bd1dc : word) 4) with (0x2bd1e0 : word) by (apply bv_eq; reflexivity).
          destruct (walkD (regupd R3 10 (Z_to_bv 64 0)) M3 (seg_rom RSEGS) sp0
                     ltac:(gres; exact C1) ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(subst M3; apply rdn_wbytes_hit8; rewrite u_small by lia; lia))
            as (R4 & RUN4 & D2 & DK).
          eapply gg_msteps; [reflexivity | reflexivity | exact RUN4 |]. clear RUN4.
          replace (0xe1aa0 : word) with (Z_to_bv 64 0xe1aa0) by (apply bv_eq; reflexivity).
          apply (HEND ltac:(lia) R4 M3).
          -- (* [comment removed for export] *)
             split; [exact D2|]. split; [|split; [|split; [|split]]].
             ++ rewrite (DK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac.
                rewrite (CK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact A9.
             ++ rewrite (DK 19%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. rewrite C19. f_equal. lia.
             ++ rewrite (DK 22%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac.
                rewrite (CK 22%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac.
                rewrite (AK0 22%bv) by (cbv; noncert_qtauto). exact R22.
             ++ rewrite (DK 23%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact C23.
             ++ intros r Hr. rewrite (DK r) by (cbn [In]; right; apply loop_kept_B, Hr).
                rewrite (kept_regupd10 _ _ r Hr). rewrite (CK r (loop_kept_B r Hr)). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr.
          -- (* [comment removed for export] *)
             subst M3 M1. rewrite <- HLe. apply post_mem_end; lia.
      + (* [comment removed for export] *)
        assert (GR2 : mem_grows M M2).
        { subst M2 M1. eapply mem_grows_trans; [|apply wbytes_grows]. apply wbytes_grows. }
        assert (RD2 : rdn RSEGS M2 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe1a88))).
        { subst M2. unfold STAGE. rewrite rdn_wbytes_out; [exact RD1 | rewrite !u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia]. }
        destruct (walkB1 (regupd R1 10 (Z_to_bv 64 n)) M2 (seg_rom RSEGS) sp0 buf len n
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK0 22%bv) by (cbv; noncert_qtauto); exact R22)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RD2)
          as (R5 & RUN5 & B1 & B2 & B10 & B11 & B12 & B23 & B19 & B9 & BK).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN5 |]. clear RUN5.
        assert (BKK : forall r, In r loop_kept -> getr R5 r = getr R r).
        { intros r Hr. rewrite (BK r (loop_kept_B r Hr)). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr. }
        (* [comment removed for export] *)
        assert (MC : mcH M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 STAGE) n bs).
        { constructor.
          - lia.
          - lia.
          - subst M2. apply rdn_wbytes_self. unfold STAGE. rewrite u_small by lia. lia.
          - eapply store_ok_mono; [exact GR2|].
            eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          - unfold STAGE. rewrite !u_small by lia. lia.
          - unfold STAGE. rewrite u_small by lia. lia.
          - rewrite u_small by lia. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0xe1a10)) by (apply bv_eq; vm_compute; reflexivity).
        destruct (ref_memcpy M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 STAGE) n bs (seg_rom RSEGS) MC R5 (Z_to_bv 64 0xe1a10) RT B1 B10 B11 B12)
          as (R6 & RUN6 & KEEP). clear RT MC.
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN6 |]. clear RUN6.
        set (M3 := wbytes M2 (Z_to_bv 64 (buf + len)) bs).
        assert (GR3 : mem_grows M M3) by (subst M3; eapply mem_grows_trans; [exact GR2 | apply wbytes_grows]).
        assert (CKK : forall r, In r loop_kept -> getr R6 r = getr R r).
        { intros r Hr. rewrite (KEEP r (loop_kept_callee r Hr)). apply BKK, Hr. }
        assert (C19 : getr R6 19 = Z_to_bv 64 len) by (rewrite (KEEP 19%bv) by (cbv; noncert_qtauto); exact B19).
        assert (C23 : getr R6 23 = Z_to_bv 64 n) by (rewrite (KEEP 23%bv) by (cbv; noncert_qtauto); exact B23).
        assert (C9 : getr R6 9 = Z_to_bv 64 buf) by (rewrite (KEEP 9%bv) by (cbv; noncert_qtauto); exact B9).
        assert (C21 : getr R6 21 = Z_to_bv 64 cap) by (rewrite (CKK 21%bv) by (cbv; noncert_qtauto); exact R21).
        assert (C2 : getr R6 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (KEEP 2%bv) by (cbv; noncert_qtauto); exact B2).
        destruct (Z.eq_dec (len + n) cap) as [Hfull|Hmore].
        * (* [comment removed for export] *)
          destruct (walkB2_full R6 M3 (seg_rom RSEGS) buf len n cap C19 C23 C9 C21 ltac:(lia) ltac:(lia) Hfull Hcap)
            as (R7 & RUN7 & D19 & D23 & D9 & DK).
          replace (Z_to_bv 64 0xe1a10) with (0xe1a10 : word) by (apply bv_eq; reflexivity).
          eapply gg_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
          replace (0xe1a24 : word) with (Z_to_bv 64 0xe1a24) by (apply bv_eq; reflexivity).
          rewrite Hfull.
          apply (HFULL ltac:(lia) R7 M3).
          -- split; [rewrite (DK 2%bv) by (cbv; noncert_qtauto); exact C2|].
             split; [exact D9|]. split; [exact D19|]. split; [|split; [exact D23|]].
             ++ rewrite (DK 22%bv) by (cbv; noncert_qtauto). rewrite (CKK 22%bv) by (cbv; noncert_qtauto). exact R22.
             ++ intros r Hr. rewrite (DK r (loop_kept_B2 r Hr)). apply CKK, Hr.
          -- subst M3 M2 M1. rewrite <- Hfull. apply post_mem_here; try lia. exact RB.
        * (* [comment removed for export] *)
          destruct (walkB2_more R6 M3 (seg_rom RSEGS) buf len n cap C19 C23 C9 C21 ltac:(lia) ltac:(lia) ltac:(lia) Hcap)
            as (R7 & RUN7 & D19 & D23 & D9 & DK).
          replace (Z_to_bv 64 0xe1a10) with (0xe1a10 : word) by (apply bv_eq; reflexivity).
          eapply gg_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
          replace (0xe1a68 : word) with (Z_to_bv 64 0xe1a68) by (apply bv_eq; reflexivity).
          assert (DKK : forall r, In r loop_kept -> getr R7 r = getr R r).
          { intros r Hr. rewrite (DK r (loop_kept_B2 r Hr)). apply CKK, Hr. }
          apply (IH R7 M3 sp0 buf (len + n)%Z cap K ltac:(lia)).
          -- split; [rewrite (DK 2%bv) by (cbv; noncert_qtauto); exact C2|].
             split; [exact D9|]. split; [exact D19|].
             split; [rewrite (DKK 20%bv) by (cbv; noncert_qtauto); exact R20|].
             split; [rewrite (DKK 21%bv) by (cbv; noncert_qtauto); exact R21|].
             rewrite (DKK 22%bv) by (cbv; noncert_qtauto); exact R22.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- eapply store_ok_mono; [exact GR3 | exact SOKs].
          -- eapply store_ok_mono; [exact GR3 |].
             eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          -- intros d m Hd Hm. eapply store_ok_mono; [exact GR3 | apply SOKst; assumption].
          -- intros HcL R' M' PR PM. apply (HFULL HcL R' M').
             ++ eapply post_regs_compose; [exact PR | exact DKK].
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | exact RB | | | exact PM]; lia.
          -- intros HLc R' M' PR PM. apply (HEND HLc R' M').
             ++ eapply post_regs_compose; [exact PR | exact DKK].
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | exact RB | | | exact PM]; lia.
  Qed.
End ChunkLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma frame_mod_split_cons : forall M M' (a1 : word) (n1 : Z) rs,
  frame_mod M M' ((a1, n1) :: rs) ->
  exists Mm, frame_mod M Mm [(a1, n1)] /\ frame_mod Mm M' rs.
Proof.
  intros M M' a1 n1 rs [EQ GR].
  exists (fun x => if in_rngb x a1 n1 then M' x else M x). split; split.
  - intros a [Ha _]. destruct (in_rngb a a1 n1) eqn:Hb; [|reflexivity].
    exfalso. apply Ha. apply in_rngb_spec. exact Hb.
  - intros x Hx. destruct (in_rngb x a1 n1); [apply GR, Hx | exact Hx].
  - intros a Ha. destruct (in_rngb a a1 n1) eqn:Hb; [reflexivity|].
    apply EQ. cbn [outside]. split; [|exact Ha].
    intros Hin. apply in_rngb_spec in Hin. rewrite Hin in Hb. discriminate.
  - intros x Hx. destruct (in_rngb x a1 n1); [exact Hx | apply GR, Hx].
Qed.

(* [comment removed for export] *)
Lemma know_ok_frame3 : forall E M M' kn (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) (b3 : expr) (k3 n3 : Z),
  know_ok RSEGS E M kn -> flat E (SA b1 k1) n1 -> flat E (SA b2 k2) n2 -> flat E (SA b3 k3) n3 ->
  frame_mod M M' [(adenot E (SA b1 k1), n1); (adenot E (SA b2 k2), n2); (adenot E (SA b3 k3), n3)] ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 k1 n1) b2 k2 n2) b3 k3 n3).
Proof.
  intros E M M' kn b1 k1 n1 b2 k2 n2 b3 k3 n3 HK F1 F2 F3 FR.
  destruct (frame_mod_split_cons _ _ _ _ _ FR) as (Ma & [E1 G1] & FR2).
  destruct (frame_mod_split_cons _ _ _ _ _ FR2) as (Mb & [E2 G2] & [E3 G3]).
  pose proof (flat_u E _ _ F1) as U1. pose proof (flat_u E _ _ F2) as U2. pose proof (flat_u E _ _ F3) as U3.
  eapply know_ok_frame; [eapply know_ok_frame; [eapply know_ok_frame; [exact HK | exact F1 | | exact G1] | exact F2 | | exact G2] | exact F3 | | exact G3].
  - intros x Hx. apply E1. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U1. lia.
  - intros x Hx. apply E2. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U2. lia.
  - intros x Hx. apply E3. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite U3. lia.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0x354000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof.
  intros a Ha. unfold seg_rom. unfold memory_read.
  cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
  cbn [Z.of_N].
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
              replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.

Lemma rdn1_mem_high : forall M (a : word) (b : byte),
  (0x354000 <= bv_unsigned a)%Z -> rdn RSEGS M a 1 = Some [b] -> M a = Some b.
Proof.
  intros M a b Ha H. cbn [rdn] in H. destruct (M a) as [b'|] eqn:Hm.
  - injection H as ->. reflexivity.
  - rewrite seg_rom_high in H by exact Ha. discriminate.
Qed.

(* [comment removed for export] *)
Lemma kblob_of_rdn : forall E M (e : expr) (a : word) (off n : Z) (k : nat) (bs : list byte),
  edenot E e = a -> eb E k = bs -> Z.of_nat (length bs) = n ->
  (0x354000 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + n < 2 ^ 64)%Z ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned a + off)) (length bs) = Some bs ->
  kentry_ok RSEGS E M (KBlob (SA e off) (ELit n) k).
Proof.
  intros E M e a off n k bs He Hb Hn Hlo Hhi RD.
  eapply (kblob_intro RSEGS E M e a off (ELit n) k bs He Hb); try lia.
  - cbn [edenot]. rewrite u_small by lia. lia.
  - intros i Hi.
    pose proof (SeqExec.rdn_nth RSEGS M (length bs) (Z_to_bv 64 (bv_unsigned a + off)) bs (Z.to_nat i) RD ltac:(lia)) as R1.
    apply rdn1_mem_high; [rewrite u_small by lia; lia|].
    replace (Z_to_bv 64 (bv_unsigned a + off + i)) with (Z_to_bv 64 (bv_unsigned a + off) + nat_to_word (Z.to_nat i)); [exact R1|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

(* [comment removed for export] *)
Lemma pres_loop_post : forall content M0 M M' (sp0 : word) (buf len len' : Z),
  pres M0 M sp0 -> loop_post_mem content M M' (bv_unsigned sp0) buf len len' ->
  (0x7fff80000000 <= bv_unsigned sp0)%Z -> (0x354000 <= buf + len)%Z -> (buf + len' <= bv_unsigned sp0 - 8388608)%Z -> (len <= len')%Z ->
  pres M0 M' sp0.
Proof.
  intros content M0 M M' sp0 buf len len' P [[EQ _] _] Hsp Hlo Hhi Hll x Hx.
  pose proof (u64_range sp0) as U.
  rewrite <- (P x Hx). apply EQ. cbn [outside loop_regions]. unfold in_rng, STAGE, rd_cell in *. rewrite !u_small by lia.
  repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma stack_writable_grows : forall M M' sp0, mem_grows M M' -> stack_writable M sp0 -> stack_writable M' sp0.
Proof. intros M M' sp0 G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma group_writable_grows : forall M M' gm, mem_grows M M' -> group_writable M gm -> group_writable M' gm.
Proof. intros M M' gm G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma meta_writable_grows : forall M M' mb, mem_grows M M' -> meta_writable M mb -> meta_writable M' mb.
Proof. intros M M' mb G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.

(* [comment removed for export] *)
Lemma content_at_buf : forall content M M' (sp0 buf held : Z),
  (0 <= held <= Z.of_nat (length content))%Z -> (0x354000 <= buf)%Z -> (buf + Z.of_nat (length content) <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS M (Z_to_bv 64 buf) (Z.to_nat held) = Some (pref held content) ->
  loop_post_mem content M M' sp0 buf held (Z.of_nat (length content)) ->
  rdn RSEGS M' (Z_to_bv 64 buf) (length content) = Some content.
Proof.
  intros content M M' sp0 buf held Hh Hb Hbl Hsp HELD [FR RD].
  replace (length content) with (Z.to_nat held + Z.to_nat (Z.of_nat (length content) - held))%nat by lia.
  rewrite <- (pref_dropz_app held content) at 2. rewrite <- (pref_all (Z.of_nat (length content) - held) (dropz held content))
    by (rewrite dropz_length by lia; lia).
  apply SeqExec.rdn_app.
  - rewrite (frame_mod_rdn RSEGS M M' _ (Z.to_nat held) (Z_to_bv 64 buf) FR); [exact HELD| |rewrite u_small by lia; lia].
    intros i Hi. rewrite (u_small buf) by lia. cbn [outside loop_regions]. unfold in_rng, STAGE. rewrite !u_small by lia. repeat split; lia.
  - replace (Z_to_bv 64 buf + nat_to_word (Z.to_nat held)) with (Z_to_bv 64 (buf + held)); [exact RD|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

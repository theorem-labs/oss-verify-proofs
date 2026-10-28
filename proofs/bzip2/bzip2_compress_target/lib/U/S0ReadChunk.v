(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ModelAmb.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk LibMaskBits SumWalkTac RefMemcpyLib.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StepTac StoreOk ShapeAlg Hoare WalkTac Frame MemSplit LibMaskBits SumWalkTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ModelAmb.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymExec SymExec2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX RefNodes LibKnowFrame RefReadLib U.S0ReadBase.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WsegFast ShapeAlg MmapSim. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require MmapSim. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require StreamSim SymExec SymExec2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Frame MemSplit U.S0TargetPre U.S0ReadBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0WsegData.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0ReadStage.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WsegFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim.AllocSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPre OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase.
   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope bv_scope.
Import SX2. Import SX2S.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cap_of (j : Z) : Z := 65536 * 2 ^ j.
(* [comment removed for export] *)
(* [comment removed for export] *)        (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)          (* [comment removed for export] *)
(* [comment removed for export] *)          (* [comment removed for export] *)
(* [comment removed for export] *)         (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition pref (n : Z) (l : list byte) : list byte := firstn (Z.to_nat n) l.
Definition dropz (n : Z) (l : list byte) : list byte := skipn (Z.to_nat n) l.
Arguments pref : simpl never.
Arguments dropz : simpl never.
(* [comment removed for export] *)
Global Strategy 1000 [pref dropz].

Lemma pref_length : forall n l, (0 <= n)%Z -> Z.of_nat (length (pref n l)) = Z.min n (Z.of_nat (length l)).
Proof. intros n l Hn. unfold pref. rewrite length_firstn. lia. Qed.

Lemma dropz_length : forall n l, (0 <= n)%Z -> Z.of_nat (length (dropz n l)) = Z.max 0 (Z.of_nat (length l) - n).
Proof. intros n l Hn. unfold dropz. rewrite length_skipn. lia. Qed.

Lemma file_read_pref : forall data (off cnt : Z),
  (0 <= off < 2 ^ 64)%Z -> (0 <= cnt < 2 ^ 64)%Z ->
  file_read data (Z_to_bv 64 off) (Z_to_bv 64 cnt) = pref cnt (dropz off data).
Proof.
  intros data off cnt Ho Hc. rewrite file_read_unguarded. unfold pref, dropz, word_to_nat. rewrite !u_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pref_app : forall (a b : Z) l, (0 <= a)%Z -> (0 <= b)%Z ->
  pref a l ++ pref b (dropz a l) = pref (a + b) l.
Proof.
  intros a b l Ha Hb. unfold pref, dropz. rewrite Z2Nat.inj_add by lia. rewrite firstn_skipn_comm.
  transitivity (firstn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l) ++ skipn (Z.to_nat a) (firstn (Z.to_nat a + Z.to_nat b) l)).
  - f_equal. rewrite firstn_firstn. f_equal. lia.
  - apply firstn_skipn.
Qed.

(* [comment removed for export] *)
Lemma pref_dropz_app : forall n l, pref n l ++ dropz n l = l.
Proof. intros n l. unfold pref, dropz. apply firstn_skipn. Qed.

(* [comment removed for export] *)
Lemma pref_all : forall n l, (Z.of_nat (length l) <= n)%Z -> pref n l = l.
Proof. intros n l H. unfold pref. apply firstn_all2. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition modelG (path : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) (off : Z) (V : VmMaps) : Model :=
  mkModelA (fds_file path (Z_to_bv 64 off)) V stdin0 fs0 None (Some tid) None.

Lemma modelG_read : forall path stdin0 fs0 tid off V (off' : word),
  with_fds (fd_insert (m_fds (modelG path stdin0 fs0 tid off V)) (Z_to_bv 64 3) (FdFile path off'))
           (modelG path stdin0 fs0 tid off V)
  = mkModelA (fds_file path off') V stdin0 fs0 None (Some tid) None.
Proof. intros. reflexivity. Qed.

Lemma modelG_close : forall path stdin0 fs0 tid off V,
  with_fds (fd_remove (m_fds (modelG path stdin0 fs0 tid off V)) (Z_to_bv 64 3)) (modelG path stdin0 fs0 tid off V)
  = model_post V stdin0 fs0 tid.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0ReadStage.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WsegFast StreamSim U.S0MemcpyBase U.S0Memcpy.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec U.S0_code_1337c_1378c U.S0_code_1f620_20620 U.S0_code_20620_216f4 U.S0_code_256f4_26728 U.S0_code_26728_26f04   .
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHideSum.
Import WalkHideSum.OptIn.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0WsegData.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Module S7ReadChunkW.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibMaskBits OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase.

(* [comment removed for export] *)
Definition want (cap len : Z) : Z := if (cap - len <? 65536)%Z then (cap - len)%Z else 65536%Z.

Lemma want_range : forall cap len, (0 <= len < cap)%Z -> (1 <= want cap len <= 65536)%Z /\ (want cap len <= cap - len)%Z.
Proof. intros cap len H. unfold want. destruct (Z.ltb_spec (cap - len) 65536); lia. Qed.

(* [comment removed for export] *)
Definition loop_kept : list reg := [3; 4; 8; 18; 20; 21; 22; 24; 25; 26; 27]%bv.   (* [comment removed for export] *)

Ltac kept_list l :=
  intros r Hr; cbv [l In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.

(* [comment removed for export] *)
Lemma walkA : forall regs mem rom (sp0 len cap : Z),
  getr regs 2 = Z_to_bv 64 (sp0 - 128) -> getr regs 19 = Z_to_bv 64 len -> getr regs 21 = Z_to_bv 64 cap ->
  getr regs 20 = Z_to_bv 64 3 -> getr regs 22 = Z_to_bv 64 READ_STAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x1364c : word) mem rom)
                 (mkst regs' (0x30fd0 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13668))) rom)
    /\ getr regs' 17 = Z_to_bv 64 63 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 11 = Z_to_bv 64 READ_STAGE /\ getr regs' 12 = Z_to_bv 64 (want cap len)
    /\ getr regs' 1 = Z_to_bv 64 0x3107c /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len
    /\ (forall r, In r (9 :: 23 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 len cap Hsp Hs3 Hs5 Hs4 Hs6 SPlo SPhi Hlen Hcap SOK.
  (* [comment removed for export] *)
  Ltac walkA_tail Hs4 Hs6 Hsp SOK sp0 :=
      stepn F_135a4 D_135a4; rewrite Hs4;
      stepn F_135a8 D_135a8; rewrite Hs6;
      stepn F_135ac D_135ac;
      (* [comment removed for export] *)
      stepn F_26ed0 D_26ed0; rewrite Hsp; sp_renorm;
      stepST F_26ed4 D_26ed4 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x13668) ltac:(exact SOK);
      stepn F_26ed8 D_26ed8; stepn F_26edc D_26edc; stepn F_26ee0 D_26ee0; stepn F_26ee4 D_26ee4;
      stepn F_26ee8 D_26ee8; stepn F_26eec D_26eec; stepn F_26ef0 D_26ef0; stepn F_26ef4 D_26ef4;
      stepn F_26e60 D_26e60;
      stepn F_26e3c D_26e3c; stepn F_26e40 D_26e40; stepn F_26e44 D_26e44; stepn F_26e48 D_26e48;
      stepn F_26e4c D_26e4c; stepn F_26e50 D_26e50; stepn F_26e54 D_26e54;
      apply mst_refl.
  Ltac walkA_post :=
      repeat split; gres; try reflexivity; try assumption;
      intros r Hr; cbv [loop_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr.
  unfold want. destruct (Z.ltb_spec (cap - len) 65536) as [LT|GE]; eexists; split.
  - (* [comment removed for export] *)
    stepn F_13594 D_13594. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    (* [comment removed for export] *)
    stepn F_13598 D_13598.
    (* [comment removed for export] *)
    stepb_tk F_1359c D_1359c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
  - stepn F_13594 D_13594. rewrite Hs5, Hs3. rewrite (v_sub_ZZ cap len) by lia.
    stepn F_13598 D_13598.
    (* [comment removed for export] *)
    stepb_ft F_1359c D_1359c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
    stepn F_135a0 D_135a0.
    walkA_tail Hs4 Hs6 Hsp SOK sp0.
  - walkA_post.
Qed.

(* [comment removed for export] *)
Definition loopB_kept : list reg := [3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma walkB : forall regs mem rom (sp0 buf len n : Z),
  getr regs 1 = Z_to_bv 64 0x3107c -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 n ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 22 = Z_to_bv 64 READ_STAGE ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  (0 < n <= 65536)%Z -> (0 <= len)%Z -> (0 <= buf)%Z -> (buf + len <= 2 ^ 62)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13668)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x30fd4 : word) mem rom) (mkst regs' (0x306ac : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0x13600 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ getr regs' 10 = Z_to_bv 64 (buf + len) /\ getr regs' 11 = Z_to_bv 64 READ_STAGE /\ getr regs' 12 = Z_to_bv 64 n
    /\ getr regs' 23 = Z_to_bv 64 n /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len n Hra Hsp Ha0 Hs3 Hs1 Hs6 SPlo SPhi Hn Hlen Hbuf Hbl RD.
  eexists. split.
  - (* [comment removed for export] *)
    stepret F_26e5c D_26e5c (0x3107c : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepLD8 F_26ef8 D_26ef8 (Z_to_bv 64 0x13668).
    (* [comment removed for export] *)
    stepn F_26efc D_26efc. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_26f00 D_26f00.
    (* [comment removed for export] *)
    stepn F_1f638 D_1f638. stepn F_1f63c D_1f63c.
    (* [comment removed for export] *)
    stepb_tk F_1f640 D_1f640 ltac:(rewrite Ha0; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    stepret F_1f66c D_1f66c (0x13668 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepb_ft F_135b0 D_135b0 ltac:(rewrite Ha0; apply c_lts_pos_0; u_norm; lia).
    (* [comment removed for export] *)
    stepn F_135b4 D_135b4. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_tk F_135b8 D_135b8 ltac:(rewrite Ha0; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_13538 D_13538. rewrite Hs1, Hs3. rewrite (v_add_ZZ buf len) by lia.
    stepn F_1353c D_1353c. rewrite Hs6.
    stepn F_13540 D_13540.
    stepn F_13544 D_13544.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2 : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf -> getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 <= n)%Z -> (len + n < cap)%Z -> (cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x13600 : word) mem rom) (mkst regs' (0x1364c : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 (len + n) /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r (1 :: 2 :: 10 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Hlt Hcap.
  eexists. split.
  - (* [comment removed for export] *)
    stepn F_13548 D_13548. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    (* [comment removed for export] *)
    stepn F_1354c D_1354c. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_ft F_13550 D_13550 ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepn F_13554 D_13554.
    stepn F_13558 D_13558.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try (f_equal; lia). kept_list loop_kept.
Qed.

(* [comment removed for export] *)
Lemma walkB2F : forall regs mem rom (buf len n cap : Z),
  getr regs 19 = Z_to_bv 64 len -> getr regs 23 = Z_to_bv 64 n -> getr regs 9 = Z_to_bv 64 buf -> getr regs 21 = Z_to_bv 64 cap ->
  (0 <= len)%Z -> (0 <= n)%Z -> (len + n = cap)%Z -> (cap <= 2 ^ 40)%Z ->
  exists regs',
    msteps RSEGS (mkst regs (0x13600 : word) mem rom) (mkst regs' (0x13614 : word) mem rom)
    /\ getr regs' 19 = Z_to_bv 64 cap /\ getr regs' 23 = Z_to_bv 64 buf /\ getr regs' 9 = Z_to_bv 64 buf
    /\ (forall r, In r (1 :: 2 :: 10 :: loop_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom buf len n cap Hs3 Hs7 Hs1 Hs5 Hlen Hn Heq Hcap.
  eexists. split.
  - stepn F_13548 D_13548. rewrite Hs7, Hs3. rewrite (v_add_ZZ n len) by lia.
    stepn F_1354c D_1354c. rewrite Hs1.
    (* [comment removed for export] *)
    stepb_tk F_13550 D_13550 ltac:(rewrite Hs5; rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). kept_list loop_kept.
Qed.

(* [comment removed for export] *)
Lemma walkBC : forall regs mem rom (sp0 buf len : Z),
  getr regs 1 = Z_to_bv 64 0x3107c -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  getr regs 19 = Z_to_bv 64 len -> getr regs 9 = Z_to_bv 64 buf -> getr regs 20 = Z_to_bv 64 3 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z -> (0 <= len < 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13668)) ->
  store_ok RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x30fd4 : word) mem rom)
                 (mkst regs' (0x30fd0 : word)
                       (wbytes mem (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x1367c))) rom)
    /\ getr regs' 17 = Z_to_bv 64 57 /\ getr regs' 10 = Z_to_bv 64 3
    /\ getr regs' 1 = Z_to_bv 64 0x31020 /\ getr regs' 2 = Z_to_bv 64 (sp0 - 144)
    /\ getr regs' 19 = Z_to_bv 64 len /\ getr regs' 23 = Z_to_bv 64 0
    /\ (forall r, In r loopB_kept -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 buf len Hra Hsp Ha0 Hs3 Hs1 Hs4 SPlo SPhi Hlen RD SOK.
  eexists. split.
  - stepret F_26e5c D_26e5c (0x3107c : word) ltac:(rewrite Hra; bveq).
    stepLD8 F_26ef8 D_26ef8 (Z_to_bv 64 0x13668).
    stepn F_26efc D_26efc. rewrite Hsp. sp_renorm.
    stepn F_26f00 D_26f00.
    stepn F_1f638 D_1f638. stepn F_1f63c D_1f63c.
    stepb_tk F_1f640 D_1f640 ltac:(rewrite Ha0; cond_compute).
    stepret F_1f66c D_1f66c (0x13668 : word) ltac:(bveq).
    stepb_ft F_135b0 D_135b0 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_135b4 D_135b4. rewrite Ha0.
    (* [comment removed for export] *)
    stepb_ft F_135b8 D_135b8 ltac:(rewrite Ha0; cond_compute).
    (* [comment removed for export] *)
    stepn F_135bc D_135bc. rewrite Hs4.
    stepn F_135c0 D_135c0.
    (* [comment removed for export] *)
    stepn F_26e70 D_26e70. sp_renorm.
    stepST F_26e74 D_26e74 (Z_to_bv 64 (sp0 - 136)) (Z_to_bv 64 0x1367c) ltac:(exact SOK).
    stepn F_26e78 D_26e78.
    stepret F_20fc8 D_20fc8 (0x31000 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26e7c D_26e7c. stepn F_26e80 D_26e80. stepn F_26e84 D_26e84. stepn F_26e88 D_26e88.
    stepn F_26e8c D_26e8c. stepn F_26e90 D_26e90. stepn F_26e94 D_26e94. stepn F_26e98 D_26e98.
    stepn F_26e60 D_26e60.
    stepn F_26e3c D_26e3c. stepn F_26e40 D_26e40. stepn F_26e44 D_26e44. stepn F_26e48 D_26e48.
    stepn F_26e4c D_26e4c. stepn F_26e50 D_26e50. stepn F_26e54 D_26e54.
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption. all: kept_list loopB_kept.
Qed.

(* [comment removed for export] *)
Lemma walkD : forall regs mem rom (sp0 : Z),
  getr regs 1 = Z_to_bv 64 0x31020 -> getr regs 2 = Z_to_bv 64 (sp0 - 144) -> getr regs 10 = Z_to_bv 64 0 ->
  (4096 <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1367c)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x30fd4 : word) mem rom) (mkst regs' (0x1367c : word) mem rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp0 - 128)
    /\ (forall r, In r (9 :: 19 :: 23 :: loopB_kept)%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom sp0 Hra Hsp Ha0 SPlo SPhi RD.
  eexists. split.
  - stepret F_26e5c D_26e5c (0x31020 : word) ltac:(rewrite Hra; bveq).
    (* [comment removed for export] *)
    stepn F_26e9c D_26e9c. rewrite Ha0. rewrite v_addiw_id by (u_norm; lia).
    stepn F_26ea0 D_26ea0. stepn F_26ea4 D_26ea4. stepn F_26ea8 D_26ea8. stepn F_26eac D_26eac.
    (* [comment removed for export] *)
    stepn F_26eb0 D_26eb0.
    stepn F_1f638 D_1f638. stepn F_1f63c D_1f63c.
    stepb_tk F_1f640 D_1f640 ltac:(cond_compute).
    stepret F_1f66c D_1f66c (0x31038 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26eb4 D_26eb4.
    stepLD8 F_26eb8 D_26eb8 (Z_to_bv 64 0x1367c).
    stepn F_26ebc D_26ebc. rewrite Hsp. sp_renorm.
    stepret F_26ec0 D_26ec0 (0x1367c : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity; try assumption; try (f_equal; lia). all: kept_list loopB_kept.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7ReadChunkW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Frame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MemSplit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibMaskBits OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ModelAmb.SpecConsts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefNodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibKnowFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefReadLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ReadChunk.S0ReadStage OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WsegFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MemcpyBase OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0Memcpy S7ReadChunkW.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac noncert_qtauto :=
  first [ solve [ repeat match goal with H : _ |- _ => clear H end; intuition fail ] | tauto ].
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
  /\ getr R 20 = Z_to_bv 64 3 /\ getr R 21 = Z_to_bv 64 cap /\ getr R 22 = Z_to_bv 64 READ_STAGE.

(* [comment removed for export] *)
Definition loop_post_regs (R R' : bvmap 5 word) (sp0 buf len' s7v : Z) : Prop :=
  getr R' 2 = Z_to_bv 64 (sp0 - 128) /\ getr R' 9 = Z_to_bv 64 buf /\ getr R' 23 = Z_to_bv 64 s7v
  /\ getr R' 19 = Z_to_bv 64 len'
  /\ (forall r, In r loop_kept -> getr R' r = getr R r).

(* [comment removed for export] *)
Definition loop_regions (sp0 buf len len' : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp0 - 136), 8%Z); (Z_to_bv 64 (buf + len), (len' - len)%Z); (Z_to_bv 64 READ_STAGE, 65536%Z)].
Definition loop_post_mem (content : list byte) (M M' : word -> option byte) (sp0 buf len len' : Z) : Prop :=
  frame_mod M M' (loop_regions sp0 buf len len')
  /\ rdn RSEGS M' (Z_to_bv 64 (buf + len)) (Z.to_nat (len' - len)) = Some (pref (len' - len) (dropz len content)).

(* [comment removed for export] *)
Lemma stage_wseg : wseg_ok RSEGS (Z_to_bv 64 READ_STAGE) (Z.to_nat 65536) = true.
Proof. apply (wseg_fast_sound_sub RSEGS (Z_to_bv 64 0x33000) _ 208896 (Z.to_nat (READ_STAGE - 0x33000)) _ S0WsegData.wseg_fast_data). vm_cast_no_check (@eq_refl bool true). Qed.  (* [comment removed for export] *)

Lemma stage_store_ok : forall M (n : nat), (Z.of_nat n <= 65536)%Z -> store_ok RSEGS M (Z_to_bv 64 READ_STAGE) n = true.
Proof.
  intros M n Hn. eapply (store_ok_sub _ _ _ _ (Z.to_nat 65536)); [ | apply store_ok_wseg, stage_wseg | | ];
    unfold READ_STAGE; rewrite ?u_small by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma loop_kept_B : forall r, In r loop_kept -> In r loopB_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [loopB_kept In].
  repeat (destruct Hr as [<-|Hr]; [noncert_qtauto|]). destruct Hr.
Qed.

Lemma loop_kept_C : forall r, In r loop_kept -> In r callee_kept.
Proof.
  intros r Hr. cbv [loop_kept In] in Hr. cbv [callee_kept In].
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
  (intros R R2 R' sp0 buf len' s7v; cps_intros (P2 & P9 & P23 & P19 & PK); intros HK).
  repeat split; try assumption. intros r Hr. rewrite (PK r Hr). apply HK, Hr.
Qed.

(* [comment removed for export] *)
Lemma frame_three : forall M (a1 a2 a3 : word) bs1 bs2 bs3,
  (bv_unsigned a1 + Z.of_nat (length bs1) <= 2 ^ 64)%Z ->
  (bv_unsigned a2 + Z.of_nat (length bs2) <= 2 ^ 64)%Z ->
  (bv_unsigned a3 + Z.of_nat (length bs3) <= 2 ^ 64)%Z ->
  frame_mod M (wbytes (wbytes (wbytes M a1 bs1) a2 bs2) a3 bs3)
            [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2)); (a3, Z.of_nat (length bs3))].
Proof.
  intros M a1 a2 a3 bs1 bs2 bs3 H1 H2 H3.
  change [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2)); (a3, Z.of_nat (length bs3))]
    with (([(a1, Z.of_nat (length bs1))] ++ [(a2, Z.of_nat (length bs2))]) ++ [(a3, Z.of_nat (length bs3))]).
  eapply frame_mod_trans; [eapply frame_mod_trans|]; apply frame_mod_wbytes; assumption.
Qed.

(* [comment removed for export] *)
Lemma frame_two : forall M (a1 a2 : word) bs1 bs2,
  (bv_unsigned a1 + Z.of_nat (length bs1) <= 2 ^ 64)%Z ->
  (bv_unsigned a2 + Z.of_nat (length bs2) <= 2 ^ 64)%Z ->
  frame_mod M (wbytes (wbytes M a1 bs1) a2 bs2) [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2))].
Proof.
  intros M a1 a2 bs1 bs2 H1 H2.
  change [(a1, Z.of_nat (length bs1)); (a2, Z.of_nat (length bs2))] with ([(a1, Z.of_nat (length bs1))] ++ [(a2, Z.of_nat (length bs2))]).
  eapply frame_mod_trans; apply frame_mod_wbytes; assumption.
Qed.

Section PostAlgebra.
  Variables (content : list byte) (M : word -> option byte) (sp0 buf len n : Z) (ra : word) (bs : list byte).
  Hypothesis Hlen : (0 <= len)%Z.
  Hypothesis Hn : (0 <= n <= 65536)%Z.
  Hypothesis Hbuf : (0x66000 <= buf)%Z.
  Hypothesis Hsp : (sp0 <= 2 ^ 63)%Z.
  Hypothesis Hbl : Z.of_nat (length bs) = n.
  Hypothesis Hbs : bs = pref n (dropz len content).

  (* [comment removed for export] *)
  #[local] Notation M3 := (wbytes (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 READ_STAGE) bs)
                            (Z_to_bv 64 (buf + len)) bs) (only parsing).

  (* [comment removed for export] *)
  Lemma post_mem_here : (buf + len + n <= sp0 - 144)%Z ->
    loop_post_mem content M M3 sp0 buf len (len + n).
  Proof.
    intros Hb. pose proof (length_N_to_le_bytes 8 ra) as L8. split.
    - eapply frame_mod_weaken; [|apply frame_three; unfold READ_STAGE; rewrite ?L8, ?Hbl, u_small by lia; lia].
      intros a Ha. cbn [outside loop_regions] in *. rewrite L8, Hbl. replace (len + n - len)%Z with n in Ha by lia.
      unfold in_rng in *. unfold READ_STAGE in *. rewrite !u_small in * by lia. repeat split; try lia. all: try exact I. all: intuition lia.
    - replace (len + n - len)%Z with n by lia. rewrite <- Hbs. replace (Z.to_nat n) with (length bs) by lia.
      apply rdn_wbytes_self. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma post_mem_compose : forall M' (len' : Z),
    (len + n <= len')%Z -> (buf + len' <= sp0 - 144)%Z ->
    loop_post_mem content M3 M' sp0 buf (len + n) len' ->
    loop_post_mem content M M' sp0 buf len len'.
  Proof.
    intros M' len' Hl' Hb' [FR RD]. pose proof (length_N_to_le_bytes 8 ra) as L8. split.
    - eapply frame_mod_weaken.
      2: { eapply frame_mod_trans; [ | exact FR ]. apply frame_three; unfold READ_STAGE; rewrite ?L8, ?Hbl, u_small by lia; lia. }
      intros a [O1 [O2 [O3 _]]]. cbn [outside loop_regions app]. rewrite L8, Hbl. unfold in_rng in *. unfold READ_STAGE in *.
      rewrite !u_small in * by lia. repeat split; lia.
    - replace (Z.to_nat (len' - len)) with (length bs + Z.to_nat (len' - (len + n)))%nat by lia.
      replace (pref (len' - len) (dropz len content)) with (bs ++ pref (len' - (len + n)) (dropz (len + n) content))
        by (rewrite Hbs at 1; rewrite pref_chain by lia; f_equal; lia).
      apply SeqExec.rdn_app.
      + rewrite (frame_mod_rdn RSEGS M3 M' _ (length bs) (Z_to_bv 64 (buf + len)) FR).
        * apply rdn_wbytes_self. rewrite u_small by lia. lia.
        * intros i Hi. rewrite (u_small (buf + len)) by lia. cbn [outside loop_regions]. unfold in_rng. unfold READ_STAGE.
          rewrite ?Hbl, !u_small by lia. repeat split; lia.
        * rewrite u_small by lia. lia.
      + replace (Z_to_bv 64 (buf + len) + nat_to_word (length bs)) with (Z_to_bv 64 (buf + (len + n))); [exact RD|].
        unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
  Qed.
End PostAlgebra.

(* [comment removed for export] *)
Lemma post_mem_end : forall content M (sp0 buf len : Z) (ra1 ra2 : word),
  (0 <= len)%Z -> (len <= Z.of_nat (length content))%Z -> (sp0 <= 2 ^ 63)%Z -> (144 <= sp0)%Z ->
  (len = Z.of_nat (length content))%Z ->
  loop_post_mem content M
    (wbytes (wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra1)) (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 ra2))
    sp0 buf len len.
Proof.
  intros content M sp0 buf len ra1 ra2 Hl HlL Hsp Hsp' HL.
  pose proof (length_N_to_le_bytes 8 ra1) as L1. pose proof (length_N_to_le_bytes 8 ra2) as L2. split.
  - eapply frame_mod_weaken; [|apply frame_two; rewrite ?L1, ?L2, u_small by lia; lia].
    intros a [O1 _]. cbn [outside]. rewrite L1, L2. noncert_qtauto.
  - rewrite Z.sub_diag. cbn [Z.to_nat rdn]. rewrite pref_0. reflexivity.
Qed.

Section ChunkLoop.
  Variables (path content : list byte) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) (V : VmMaps).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (S0ReadStage.modelG path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Theorem chunk_loop_mid : forall (fuel : nat) (R : bvmap 5 word) (M : word -> option byte) (sp0 buf len cap : Z) (K : TSet),
    (cap - len <= Z.of_nat fuel)%Z ->
    mid_regs R sp0 buf len cap ->
    (0 <= len < cap)%Z -> (cap <= 2 ^ 40)%Z -> (0x66000 <= buf)%Z -> (buf + cap <= sp0 - 144)%Z ->
    (sp0 <= 2 ^ 47)%Z ->
    (len <= L)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 136)) 8 = true ->
    store_ok RSEGS M (Z_to_bv 64 (buf + len)) (Z.to_nat (cap - len)) = true ->
    (* [comment removed for export] *)
    ((cap <= L)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf cap buf -> loop_post_mem content M M' sp0 buf len cap ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x13614) M' (seg_rom RSEGS)) (modelG cap V)) K) ->
    (* [comment removed for export] *)
    ((L < cap)%Z -> forall R' M',
        loop_post_regs R R' sp0 buf L 0 -> loop_post_mem content M M' sp0 buf len L ->
        realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x1367c) M' (seg_rom RSEGS)) (model_post V stdin0 fs0 tid)) K) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1364c) M (seg_rom RSEGS)) (modelG len V)) K.
  Proof.
    induction fuel as [|fuel IH]; (intros R M sp0 buf len cap K Hfuel; cps_intros (R2 & R9 & R19 & R20 & R21 & R22); intros Hlen Hcap Hbuf Hbc Hsp HlenL SOKs SOKb HFULL HEND).
    { exfalso. cbn in Hfuel. lia. }
    pose proof (want_range cap len Hlen) as [Hw1 Hw2].
    (* [comment removed for export] *)
    cps_destruct (walkA R M (seg_rom RSEGS) sp0 len cap R2 R19 R21 R20 R22
               ltac:(lia) ltac:(lia) Hlen Hcap SOKs)
      as (R1 & RUN1 & A17 & A10 & A11 & A12 & A1 & A2 & A19 & AK0).
    assert (AK : forall r, In r loop_kept -> getr R1 r = getr R r) by (intros r Hr; apply AK0; right; right; exact Hr).
    assert (A9 : getr R1 9 = Z_to_bv 64 buf) by (rewrite (AK0 9%bv) by (cbv; noncert_qtauto); exact R9).
    replace (Z_to_bv 64 0x1364c) with (0x1364c : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact RUN1 |]. clear RUN1.
    set (M1 := wbytes M (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x13668))).
    assert (SOK1s : store_ok RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = true)
      by (eapply store_ok_mono; [apply wbytes_grows | exact SOKs]).
    assert (RD1 : rdn RSEGS M1 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13668)))
      by (apply rdn_wbytes_hit8; rewrite u_small by lia; lia).
    (* [comment removed for export] *)
    pose proof (read_chunk content len (want cap len) ltac:(lia) ltac:(lia) ltac:(lia)) as RC. cbn zeta in RC.
    destruct RC as [RN RB].
    remember (file_read content (Z_to_bv 64 len) (Z_to_bv 64 (want cap len))) as bs eqn:Hbs.
    set (n := Z.of_nat (length bs)) in *.
    eapply (rz_read_file RSEGS R1 (0x30fd0 : word) M1 (modelG len V) W_26e58 (Z_to_bv 64 3) path (Z_to_bv 64 len) content (want cap len) K F_26e58 E_26e58).
    - reflexivity.
    - reflexivity.
    - exact A17.
    - exact A10.
    - rewrite u_small by lia. lia.
    - reflexivity.
    - exact Hfile.
    - exact A12.
    - lia.
    - pose proof MAX_RW_COUNT_ge31. lia.
    - lia.
    - rewrite A11. apply stage_store_ok. lia.
    - rewrite A11, A12. apply access_okb_intro_num. unfold READ_STAGE. rewrite !u_small by lia. lia.
    - cbv zeta. rewrite A12, A11, <- Hbs. rewrite modelG_read.
      change (len_word bs) with (Z_to_bv 64 n).
      replace (Z_to_bv 64 len + Z_to_bv 64 n) with (Z_to_bv 64 (len + n))
        by (apply bv_eq; rewrite bv_add_unsigned, !u_small by lia; rewrite bv_wrap_small; [lia | unfold bv_modulus; lia]).
      change (mkModelA (fds_file path (Z_to_bv 64 (len + n))) V stdin0 fs0 None (Some tid) None) with (modelG (len + n) V).
      replace (v_addi (0x30fd0 : word) 4) with (0x30fd4 : word) by (apply bv_eq; reflexivity).
      set (M2 := wbytes M1 (Z_to_bv 64 READ_STAGE) bs).
      destruct (Z.eq_dec n 0) as [Hn0|Hn0].
      + (* [comment removed for export] *)
        assert (bs = []) as Hnil by (destruct bs; [reflexivity | subst n; cbn in Hn0; lia]).
        assert (HLe : L = len) by lia.
        subst M2. rewrite Hnil. cbn [wbytes]. rewrite Hn0.
        cps_destruct (walkBC (regupd R1 10 (Z_to_bv 64 0)) M1 (seg_rom RSEGS) sp0 buf len
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 20%bv) by (cbv; noncert_qtauto); exact R20)
                   ltac:(lia) ltac:(lia) ltac:(lia) RD1 SOK1s)
          as (R3 & RUN3 & C17 & C10 & C1 & C2 & C19 & C23 & CK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN3 |]. clear RUN3.
        set (M3 := wbytes M1 (Z_to_bv 64 (sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0x1367c))).
        (* [comment removed for export] *)
        eapply (rz_close RSEGS R3 (0x30fd0 : word) M3 (modelG (len + 0) V) W_26e58 (Z_to_bv 64 3) _ K F_26e58 E_26e58).
        * reflexivity.
        * reflexivity.
        * exact C17.
        * exact C10.
        * rewrite u_small by lia. lia.
        * reflexivity.
        * rewrite modelG_close.
          replace (v_addi (0x30fd0 : word) 4) with (0x30fd4 : word) by (apply bv_eq; reflexivity).
          cps_destruct (walkD (regupd R3 10 (Z_to_bv 64 0)) M3 (seg_rom RSEGS) sp0
                     ltac:(gres; exact C1) ltac:(gres; exact C2) ltac:(gres; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(subst M3; apply rdn_wbytes_hit8; rewrite u_small by lia; lia))
            as (R4 & RUN4 & D2 & DK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN4 |]. clear RUN4.
          replace (0x1367c : word) with (Z_to_bv 64 0x1367c) by (apply bv_eq; reflexivity).
          apply (HEND ltac:(lia) R4 M3).
          -- (* [comment removed for export] *)
             split; [exact D2|]. split; [|split; [|split]].
             ++ rewrite (DK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac.
                rewrite (CK 9%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact A9.
             ++ rewrite (DK 23%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. exact C23.
             ++ rewrite (DK 19%bv) by (cbv; noncert_qtauto). rewrite getr_other by reg_neq_tac. rewrite C19. f_equal. lia.
             ++ intros r Hr. rewrite (DK r) by (cbn [In]; right; right; right; apply loop_kept_B, Hr).
                rewrite (kept_regupd10 _ _ r Hr). rewrite (CK r (loop_kept_B r Hr)). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr.
          -- (* [comment removed for export] *)
             subst M3 M1. rewrite <- HLe. apply post_mem_end; lia.
      + (* [comment removed for export] *)
        assert (RD2 : rdn RSEGS M2 (Z_to_bv 64 (sp0 - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13668))).
        { subst M2. rewrite rdn_wbytes_out; [exact RD1 | unfold READ_STAGE; rewrite !u_small by lia; lia | rewrite u_small by lia; lia | unfold READ_STAGE; rewrite u_small by lia; lia]. }
        cps_destruct (walkB (regupd R1 10 (Z_to_bv 64 n)) M2 (seg_rom RSEGS) sp0 buf len n
                   ltac:(gres; exact A1) ltac:(gres; exact A2) ltac:(gres; reflexivity)
                   ltac:(gres; exact A19) ltac:(gres; exact A9) ltac:(gres; rewrite (AK 22%bv) by (cbv; noncert_qtauto); exact R22)
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RD2)
          as (R5 & RUN5 & B1 & B2 & B10 & B11 & B12 & B23 & B19 & B9 & BK).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN5 |]. clear RUN5.
        assert (BKK : forall r, In r loop_kept -> getr R5 r = getr R r).
        { intros r Hr. rewrite (BK r (loop_kept_B r Hr)). rewrite (kept_regupd10 _ _ r Hr). apply AK, Hr. }
        (* [comment removed for export] *)
        assert (MC : mcH M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 READ_STAGE) n bs).
        { constructor.
          - lia.
          - lia.
          - subst M2. apply rdn_wbytes_self. unfold READ_STAGE. rewrite u_small by lia. lia.
          - subst M2 M1. eapply store_ok_mono; [eapply mem_grows_trans; apply wbytes_grows|].
            eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          - right. unfold READ_STAGE. rewrite !u_small by lia. lia.
          - unfold READ_STAGE. rewrite u_small by lia. lia.
          - rewrite u_small by lia. lia. }
        cps_destruct (S0Memcpy.ref_memcpy M2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 READ_STAGE) n bs (seg_rom RSEGS) MC R5 (0x13600 : word)
                   ltac:(apply ret_ok_even; reflexivity) ltac:(rewrite B1; apply bv_eq; reflexivity) B10 B11 B12)
          as (R6 & RUN6 & KP).
        eapply rz_msteps; [reflexivity | reflexivity | exact RUN6 |]. clear RUN6.
        set (M3 := wbytes M2 (Z_to_bv 64 (buf + len)) bs).
        assert (K6 : forall r : reg, In r callee_kept -> getr R6 r = getr R5 r) by exact KP.
        assert (C19 : getr R6 19 = Z_to_bv 64 len) by (rewrite (K6 19%bv) by (cbv; noncert_qtauto); exact B19).
        assert (C23 : getr R6 23 = Z_to_bv 64 n) by (rewrite (K6 23%bv) by (cbv; noncert_qtauto); exact B23).
        assert (C9 : getr R6 9 = Z_to_bv 64 buf) by (rewrite (K6 9%bv) by (cbv; noncert_qtauto); exact B9).
        assert (C21 : getr R6 21 = Z_to_bv 64 cap) by (rewrite (K6 21%bv) by (cbv; noncert_qtauto); rewrite (BKK 21%bv) by (cbv; noncert_qtauto); exact R21).
        assert (C2 : getr R6 2 = Z_to_bv 64 (sp0 - 128)) by (rewrite (K6 2%bv) by (cbv; noncert_qtauto); exact B2).
        assert (GR3 : mem_grows M M3).
        { subst M3 M2 M1. eapply mem_grows_trans; [|apply wbytes_grows]. eapply mem_grows_trans; [|apply wbytes_grows]. apply wbytes_grows. }
        destruct (Z.eq_dec (len + n) cap) as [Hfull|Hmore].
        * (* [comment removed for export] *)
          cps_destruct (walkB2F R6 M3 (seg_rom RSEGS) buf len n cap C19 C23 C9 C21 ltac:(lia) ltac:(lia) Hfull Hcap)
            as (R7 & RUN7 & D19 & D23 & D9 & DK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
          replace (0x13614 : word) with (Z_to_bv 64 0x13614) by (apply bv_eq; reflexivity).
          rewrite Hfull.
          apply (HFULL ltac:(lia) R7 M3).
          -- split; [rewrite (DK 2%bv) by (cbv; noncert_qtauto); exact C2|].
             split; [exact D9|]. split; [exact D23|]. split; [exact D19|].
             intros r Hr. rewrite (DK r) by (cbn [In]; right; right; right; exact Hr).
             rewrite (K6 r (loop_kept_C r Hr)). apply BKK, Hr.
          -- subst M3 M2 M1. rewrite <- Hfull. apply post_mem_here; try lia. exact RB.
        * (* [comment removed for export] *)
          cps_destruct (walkB2 R6 M3 (seg_rom RSEGS) buf len n cap C19 C23 C9 C21 ltac:(lia) ltac:(lia) ltac:(lia) Hcap)
            as (R7 & RUN7 & D19 & D23 & D9 & DK).
          eapply rz_msteps; [reflexivity | reflexivity | exact RUN7 |]. clear RUN7.
          replace (0x1364c : word) with (Z_to_bv 64 0x1364c) by (apply bv_eq; reflexivity).
          assert (CKK : forall r, In r loop_kept -> getr R7 r = getr R r).
          { intros r Hr. rewrite (DK r) by (cbn [In]; right; right; right; exact Hr).
            rewrite (K6 r (loop_kept_C r Hr)). apply BKK, Hr. }
          apply (IH R7 M3 sp0 buf (len + n)%Z cap K ltac:(lia)).
          -- repeat split.
             ++ rewrite (DK 2%bv) by (cbv; noncert_qtauto). exact C2.
             ++ exact D9.
             ++ exact D19.
             ++ rewrite (CKK 20%bv) by (cbv; noncert_qtauto). exact R20.
             ++ rewrite (CKK 21%bv) by (cbv; noncert_qtauto). exact R21.
             ++ rewrite (CKK 22%bv) by (cbv; noncert_qtauto). exact R22.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- lia.
          -- eapply store_ok_mono; [exact GR3 | exact SOKs].
          -- eapply store_ok_mono; [exact GR3 |].
             eapply (store_ok_sub _ _ _ _ (Z.to_nat (cap - len))); [ | exact SOKb | | ]; rewrite ?u_small by lia; lia.
          -- intros HcL R' M' PR PM. apply (HFULL HcL R' M').
             ++ eapply post_regs_compose; [exact PR | exact CKK].
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | exact RB | | | exact PM]; lia.
          -- intros HLc R' M' PR PM. apply (HEND HLc R' M').
             ++ eapply post_regs_compose; [exact PR | exact CKK].
             ++ subst M3 M2 M1. eapply post_mem_compose; [ | | | | | exact RB | | | exact PM]; lia.
  Qed.
End ChunkLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stack_writable_grows : forall M M' sp0, mem_grows M M' -> stack_writable M sp0 -> stack_writable M' sp0.
Proof. intros M M' sp0 G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma group_writable_grows : forall M M' gm, mem_grows M M' -> group_writable M gm -> group_writable M' gm.
Proof. intros M M' gm G W d m Hd Hm. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.

(* [comment removed for export] *)
Lemma content_at_buf : forall content M M' (sp0 buf held : Z),
  (0 <= held <= Z.of_nat (length content))%Z -> (0x66000 <= buf)%Z -> (buf + Z.of_nat (length content) <= sp0 - 144)%Z -> (sp0 <= 2 ^ 63)%Z ->
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
    intros i Hi. rewrite (u_small buf) by lia. cbn [outside loop_regions]. unfold in_rng, READ_STAGE. rewrite !u_small by lia. repeat split; lia.
  - replace (Z_to_bv 64 buf + nat_to_word (Z.to_nat held)) with (Z_to_bv 64 (buf + held)); [exact RD|].
    unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, Z2Nat.id, !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

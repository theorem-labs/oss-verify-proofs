(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* C34 for uncompress2 (1.4): unc C34 text with lineage 9 -> 7 and unc2's
   frames (Plain/U2Seg c13): UU = usp - 240; the harness frame 32 (ra at UU+232), uncompress2's 48 (s1 / s0 / ra at
   UU+184 / 192 / 200), uncompress2_z's 160 at UU (saves at UU+112 .. 160); uncompress2_z's s0 / s1 = usp-24 / usp-16. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Exec MonadX CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Plain Require Import PImg StdioFiles.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Plain Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_facts U2Kit U2Seg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Malloc Monad CMonad CMonadX Stdio Harness Prog ProgC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require HarnessC Client.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Plain Require Import RunDraw.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.S7LibStmt OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* kitfix4 alias stage: Module OZ := OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase expanded *)

Lemma outside_Forall : forall (P : Z * Z -> Prop) (W : list (Z * Z)) x,
  Forall P W -> (forall iv, P iv -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  intros P W x HF HP. induction HF as [|[a b] W Hiv _ IH]; cbn; [exact I|]. split; [exact (HP _ Hiv)| exact IH].
Qed.

Lemma nodup_app_disj : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a l1 IH]; cbn; intros l2 x ND H1 H2; [exact H1|]. inversion ND as [|? ? NI ND']; subst.
  destruct H1 as [->|H1]; [apply NI; apply in_or_app; right; exact H2| exact (IH l2 x ND' H1 H2)].
Qed.

(* 1.4: uncompress2_z does not save s5, so the S7 end-register list is S_ENTRY5 = s5 :: S_ENTRY (S7LibStmt). *)
Lemma sregs_entry_eq : forall (R : bvmap 5 word) (x21 x22 x23 x24 x25 x26 x27 : word),
  OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.sregs R OL.S_ENTRY5 = [bv_unsigned x21; bv_unsigned x22; bv_unsigned x23; bv_unsigned x24; bv_unsigned x25; bv_unsigned x26; bv_unsigned x27] ->
  OP.getr R 21 = x21 /\ OP.getr R 22 = x22 /\ OP.getr R 23 = x23 /\ OP.getr R 24 = x24 /\ OP.getr R 25 = x25 /\ OP.getr R 26 = x26 /\ OP.getr R 27 = x27.
Proof.
  intros R x21 x22 x23 x24 x25 x26 x27 H. unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.sregs, OL.S_ENTRY5, OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY in H. cbn [map app] in H.
  injection H as H21 H22 H23 H24 H25 H26 H27. repeat split; apply bv_eq; assumption.
Qed.

Lemma end_regs_mkR : forall (R : bvmap 5 word) (u blk : Z) (g3 g4 y21 y22 y23 y24 y25 y26 y27 : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  OL.end_regs_S7 R (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) u blk
                 [bv_unsigned y21; bv_unsigned y22; bv_unsigned y23; bv_unsigned y24; bv_unsigned y25; bv_unsigned y26; bv_unsigned y27] ->
  OP.getr R 3 = g3 -> OP.getr R 4 = g4 ->
  x14 = Z_to_bv 64 OL.S7_ZCFREE /\ x11 = Z_to_bv 64 blk /\ x10 = Z_to_bv 64 0 /\ x8 = Z_to_bv 64 u /\ x2 = Z_to_bv 64 (u - 16)
  /\ x3 = g3 /\ x4 = g4 /\ x21 = y21 /\ x22 = y22 /\ x23 = y23 /\ x24 = y24 /\ x25 = y25 /\ x26 = y26 /\ x27 = y27.
Proof.
  intros until x31. intros (G14 & G11 & G10 & G8 & G2 & G3 & G4 & GS) E3 E4.
  apply sregs_entry_eq in GS. destruct GS as (S21 & S22 & S23 & S24 & S25 & S26 & S27).
  pose proof (getr_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20
        & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31).
  rewrite H14 in G14. rewrite H11 in G11. rewrite H10 in G10. rewrite H8 in G8. rewrite H2 in G2.
  rewrite H3, E3 in G3. rewrite H4, E4 in G4. rewrite H21 in S21. rewrite H22 in S22. rewrite H23 in S23. rewrite H24 in S24.
  rewrite H25 in S25. rewrite H26 in S26. rewrite H27 in S27.
  repeat split; assumption.
Qed.

(* 1.4: zc returns with sp = u + 160 and s0 .. s4 restored; s5 is the caller's, untouched. *)
Lemma zc_regs_mkR : forall (R : bvmap 5 word) (u : Z) (v0 v1 v2 v3 v4 g3 g4 g21 g22 g23 g24 g25 g26 g27 : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R' := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  OP.getr R' 2 = Z_to_bv 64 (u + 160) ->
  OP.getr R' 8 = v0 -> OP.getr R' 9 = v1 -> OP.getr R' 18 = v2 -> OP.getr R' 19 = v3 -> OP.getr R' 20 = v4 -> OP.getr R' 21 = OP.getr R 21 ->
  (forall r : reg, In r ([3; 4]%bv ++ OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY) -> OP.getr R' r = OP.getr R r) ->
  OP.getr R 3 = g3 -> OP.getr R 4 = g4 -> OP.getr R 21 = g21 -> OP.getr R 22 = g22 -> OP.getr R 23 = g23 -> OP.getr R 24 = g24 ->
  OP.getr R 25 = g25 -> OP.getr R 26 = g26 -> OP.getr R 27 = g27 ->
  x2 = Z_to_bv 64 (u + 160) /\ x8 = v0 /\ x9 = v1 /\ x18 = v2 /\ x19 = v3 /\ x20 = v4 /\ x21 = g21
  /\ x3 = g3 /\ x4 = g4 /\ x22 = g22 /\ x23 = g23 /\ x24 = g24 /\ x25 = g25 /\ x26 = g26 /\ x27 = g27.
Proof.
  intros until x31. intros R' Z2 Z8 Z9 Z18 Z19 Z20 Z21 ZK E3 E4 E21 E22 E23 E24 E25 E26 E27.
  pose proof (getr_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20
        & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31).
  fold R' in H2, H3, H4, H8, H9, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27.
  assert (K : forall r : reg, In r ([3; 4]%bv ++ OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY) -> OP.getr R' r = OP.getr R r) by exact ZK.
  pose proof (K 3%bv ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY; cbn [In app]; auto 10)) as K3.
  pose proof (K 4%bv ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY; cbn [In app]; auto 10)) as K4.
  pose proof (K 22%bv ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY; cbn [In app]; auto 10)) as K22.
  pose proof (K 23%bv ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY; cbn [In app]; auto 10)) as K23.
  pose proof (K 24%bv ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY; cbn [In app]; auto 10)) as K24.
  pose proof (K 25%bv ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY; cbn [In app]; auto 10)) as K25.
  pose proof (K 26%bv ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY; cbn [In app]; auto 10)) as K26.
  pose proof (K 27%bv ltac:(unfold OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ZlibStmtBase.S_ENTRY; cbn [In app]; auto 10)) as K27.
  repeat split; congruence.
Qed.

Lemma zw_regs_mkR : forall (R : bvmap 5 word) (u : Z) (g3 g4 : word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R' := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  OP.getr R' 13 = Z_to_bv 64 OL.S7_ZCALLOC -> OP.getr R' 10 = Z_to_bv 64 0 -> OP.getr R' 11 = Z_to_bv 64 OL.S7_WIN_N ->
  OP.getr R' 12 = Z_to_bv 64 1 -> OP.getr R' 2 = Z_to_bv 64 (u - OL.S7_ZWD) ->
  OP.getr R' 3 = OP.getr R 3 -> OP.getr R' 4 = OP.getr R 4 -> OP.getr R 3 = g3 -> OP.getr R 4 = g4 ->
  x13 = Z_to_bv 64 OL.S7_ZCALLOC /\ x10 = Z_to_bv 64 0 /\ x11 = Z_to_bv 64 OL.S7_WIN_N /\ x12 = Z_to_bv 64 1
  /\ x2 = Z_to_bv 64 (u - OL.S7_ZWD) /\ x3 = g3 /\ x4 = g4.
Proof.
  intros until x31. intros R' Z13 Z10 Z11 Z12 Z2 Z3 Z4 E3 E4.
  pose proof (getr_mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
    as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20
        & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31).
  fold R' in H2, H3, H4, H10, H11, H12, H13.
  repeat split; congruence.
Qed.

(* 1.4: uncompress2's tail (0x14f04 ..) reads and writes the harness's frames, so U2Seg's ret segment takes them as
   rw_cells. These lemmas carve them from the stack and give the saved cells the values md_uf reads there. *)
Section FBLeRoundtrip.
Local Open Scope Z_scope.
Lemma fb_testbit_small_high : forall a k, 0 <= a < 2 ^ 8 -> 8 <= k -> Z.testbit a k = false.
Proof.
  intros a k Ha Hk. destruct (Z.eq_dec a 0) as [->|Hnz]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 8); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma fb_lor_byte_testbit : forall a r k, 0 <= a < 2 ^ 8 -> 0 <= r -> 0 <= k ->
  Z.testbit (Z.lor a (Z.shiftl r 8)) k = if k <? 8 then Z.testbit a k else Z.testbit r (k - 8).
Proof.
  intros a r k Ha Hr Hk. rewrite Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec0 k 8).
  - rewrite (Z.testbit_neg_r r (k - 8)) by lia. apply orb_false_r.
  - rewrite (fb_testbit_small_high a k) by lia. reflexivity.
Qed.

Lemma fb_lor_byte_low : forall (b : byte) r, 0 <= r -> Z_to_bv 8 (Z.lor (bv_unsigned b) (Z.shiftl r 8)) = b.
Proof.
  intros b r Hr. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  apply Z.bits_inj'. intros k Hk.
  destruct (Z.ltb_spec0 k 8).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite fb_lor_byte_testbit by lia.
    replace (k <? 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite (fb_testbit_small_high (bv_unsigned b) k) by lia. reflexivity.
Qed.

Lemma fb_lor_byte_high : forall a r, 0 <= a < 2 ^ 8 -> 0 <= r -> Z.shiftr (Z.lor a (Z.shiftl r 8)) 8 = r.
Proof.
  intros a r Ha Hr. apply Z.bits_inj'. intros k Hk.
  rewrite Z.shiftr_spec by lia. rewrite fb_lor_byte_testbit by lia.
  replace (k + 8 <? 8) with false by (symmetry; apply Z.ltb_ge; lia). f_equal. lia.
Qed.

Lemma fb_bytes_le_to_Z_nonneg : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range|]. apply Z.shiftl_nonneg. exact IH.
Qed.

Lemma fb_Z_to_le_bytes_bytes_le_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (fb_bytes_le_to_Z_nonneg bs) as Hr. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  rewrite fb_lor_byte_low by exact Hr. rewrite fb_lor_byte_high by lia. rewrite IH. reflexivity.
Qed.

Lemma fb_bytes_le_to_Z_bound : forall bs : list byte, bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs.
  pose proof (bytes_le_to_Z_to_le_bytes (length bs) (bytes_le_to_Z bs) (fb_bytes_le_to_Z_nonneg bs)) as E.
  rewrite fb_Z_to_le_bytes_bytes_le_to_Z in E. rewrite E at 1.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma fb_le8_roundtrip : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (fb_bytes_le_to_Z_bound bs) as B. rewrite L in B. pose proof (fb_bytes_le_to_Z_nonneg bs) as N.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by (cbn in B |- *; lia).
  rewrite <- L. apply fb_Z_to_le_bytes_bytes_le_to_Z.
Qed.
End FBLeRoundtrip.

Lemma rw_cells_peel8 : forall (M : word -> option byte) A pre (n : nat) j post,
  rw_cells psegs M A (pre ++ CB (8 + n) j :: post) ->
  rw_cells psegs M A (pre ++ C8 (le_bytes_to_word (firstn 8 j)) :: CB n (skipn 8 j) :: post).
Proof.
  intros M A pre n j post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn [cell_wf] in H2.
  assert (E8 : le8 (le_bytes_to_word (firstn 8 j)) = firstn 8 j)
    by (apply fb_le8_roundtrip; rewrite firstn_length; lia).
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. cbn [cells_wf cell_wf]. split; [exact I|]. split; [rewrite skipn_length; lia | exact H3].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite E8, (app_assoc (firstn 8 j)), firstn_skipn. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *.
    replace (8 + (n + cells_size post))%nat with (8 + n + cells_size post)%nat by lia. exact Hw.
Qed.

Lemma rw_cells_last8 : forall (M : word -> option byte) A pre j,
  rw_cells psegs M A (pre ++ [CB 8 j]) -> rw_cells psegs M A (pre ++ [C8 (le_bytes_to_word j)]).
Proof.
  intros M A pre j [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 _]]. cbn [cell_wf] in H2.
  assert (E8 : le8 (le_bytes_to_word j) = j) by (apply fb_le8_roundtrip; exact H2).
  split; [split|].
  - apply cells_wf_app. split; [exact H1 | cbn [cells_wf cell_wf]; tauto].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite E8. exact Hb.
  - rewrite cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

Lemma rw_cells_C8_eq : forall (M : word -> option byte) A pre (w v : word) post (a : Z),
  rw_cells psegs M A (pre ++ C8 w :: post) ->
  OP.rdn psegs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> a = A + Z.of_nat (cells_size pre) ->
  rw_cells psegs M A (pre ++ C8 v :: post).
Proof.
  intros M A pre w v post a RW RD Ea.
  assert (E : w = v).
  { destruct RW as [[Hwf Hb] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 _].
    rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
    assert (LE : (length (cells_bytes pre) + 8 <= length (cells_bytes pre ++ le8 w ++ cells_bytes post))%nat)
      by (rewrite !app_length, length_le8; lia).
    pose proof (bytes_at_rdn psegs M A _ _ 8 Hb LE) as X.
    rewrite skipn_app_exact in X.
    assert (F8 : firstn 8 (le8 w ++ cells_bytes post) = le8 w)
      by (rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r; apply firstn_all2; rewrite length_le8; lia).
    rewrite F8, (cells_bytes_length pre H1) in X. unfold wa in X. rewrite <- Ea in X.
    assert (SV : Some (le8 w) = Some (word_to_le_bytes 8 v)) by (rewrite <- X; exact RD).
    apply (f_equal (fun o : option (list byte) => match o with Some x => x | None => [] end)) in SV. cbv beta iota in SV.
    assert (E2 : le_bytes_to_word (le8 w) = le_bytes_to_word (le8 v)) by (f_equal; exact SV).
    rewrite !le_bytes_to_word_le8 in E2. exact E2. }
  rewrite <- E. exact RW.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section CALL.
Variable C7 : forall fx : OP.FPState, @OL.zlib_u2_contract_S7 fx.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.

Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem)
          (st0 : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z).
Notation usp := (bv_unsigned sp).
Notation UU := (bv_unsigned sp - 240).
Notation n := (zlength payload).
Notation CT := (C7 (OP.mkFP F fc)).
Notation ZW := (@OL.zw_inv_S7 (OP.mkFP F fc) CT).
Hypothesis FP : Forall (fun c => 0 <= c < 256) payload.
Hypothesis D16 : D mod 16 = 0.
Hypothesis D0 : 0 < D.
Hypothesis DT : D + n <= ATOP.
Hypothesis PL : n < 2^26.
Hypothesis SPAB : usp <= AB.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= usp - HARNESS_STACK.
Hypothesis FRM : frm0 fc.
Hypothesis TP : tp = wz RATP.
Hypothesis SP16 : usp mod 16 = 0.
Hypothesis RAE : bv_unsigned ra mod 2 = 0.
Hypothesis SP47 : usp <= 2^47.
Hypothesis PB : (n = 0 /\ D = PEMPTY) \/ exists b, In b LB /\ blk_addr b <= D /\ D + n <= blk_addr b + blk_size b.

Notation POST := (fuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st0 LB AB lo m0).
Notation pbytes := (map (Z_to_bv 8) payload).
Notation SE := [bv_unsigned s5; bv_unsigned s6; bv_unsigned s7; bv_unsigned s8; bv_unsigned s9; bv_unsigned s10; bv_unsigned s11].

Lemma n_nonneg : 0 <= n. Proof. unfold zlength. lia. Qed.
Lemma usp_facts : 0x7fff7f800000 <= usp < 2^64 /\ 0x7fff7f800000 <= ATOP /\ ATOP + 16384 <= usp /\ (usp - 240) mod 16 = 0.
Proof.
  pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  pose proof atop_range as AR. unfold HARNESS_STACK in LO.
  split; [lia|]. split; [lia|]. split; [lia|].
  replace (usp - 240) with (usp + (-15) * 16) by lia. rewrite Z_mod_plus_full. exact SP16.
Qed.

Record MID (LBx : list block) (s : PState) (m : mem) : Prop := {
  md_heap : RHEAP s (LBx ++ LB) m;
  md_mi   : mem_inv psegs m;
  md_stk  : stk psegs m lo usp;
  md_err  : exists errv : word, rw_cells psegs m (errno_addr tp) [C4 errv];
  md_aux  : rauxv_ok m AB;
  md_pres : harness_pres LB usp m0 m;
  md_so   : ps_so s = ps_so st0;
  md_uf   : u2_frames usp m ra s0 s1 s2 s3 s4 s5;
  md_pay  : bytes_at psegs m D pbytes;
  md_wr   : Forall (fun b => wr_at psegs m (blk_addr b) (blk_size b)) LBx }.

Lemma MID_blk : forall LBx s m b, MID LBx s m -> In b (LBx ++ LB) -> rblock_range (blk_addr b) (blk_size b).
Proof. intros LBx s m b H Hb. exact (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b (md_heap _ _ _ H) Hb). Qed.

Lemma MID_disj : forall LBx s m b1 b2, MID LBx s m -> In b1 LBx -> In b2 LB ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros LBx s m b1 b2 H H1 H2.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ H)) as ND.
  apply (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b1 b2 (md_heap _ _ _ H)); [apply in_or_app; left; exact H1| apply in_or_app; right; exact H2|].
  rewrite map_app in ND. intros E. apply (nodup_app_disj _ _ (blk_id b1) ND); [apply in_map; exact H1| rewrite E; apply in_map; exact H2].
Qed.

Lemma MID_disj2 : forall s m b1 b2 LBr, MID (b1 :: b2 :: LBr) s m ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros s m b1 b2 LBr H.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ H)) as ND. cbn [app map] in ND.
  apply (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ b1 b2 (md_heap _ _ _ H)); [left; reflexivity| right; left; reflexivity|].
  inversion ND as [|? ? NI _]; subst. intros E. apply NI. left. symmetry. exact E.
Qed.

Lemma pay_same_on : forall (P : Z -> Prop) m m',
  same_on P m m' -> (forall b a, In b LB -> blk_addr b <= a < blk_addr b + blk_size b -> P a) ->
  bytes_at psegs m D pbytes -> bytes_at psegs m' D pbytes.
Proof.
  intros P m m' SO HP BY. eapply bytes_at_magree; [exact SO| exact BY|].
  intros a Ha. rewrite length_map in Ha. destruct PB as [[E _]|(b & Hb & B1 & B2)].
  - exfalso. unfold zlength in E. lia.
  - apply (HP b a Hb). unfold zlength in B2. lia.
Qed.

Lemma MID_heap : forall LBx LBx' LBp s s' m m' SPc,
  MID LBx s m ->
  rheap_pres LBp SPc m m' -> (forall b, In b LB -> In b LBp) ->
  (forall b, In b LBx' -> (In b LBx /\ In b LBp) \/ wr_at psegs m' (blk_addr b) (blk_size b)) ->
  lo <= SPc <= UU + 112 ->
  RHEAP s' (LBx' ++ LB) m' -> mem_inv psegs m' -> stk psegs m' lo SPc ->
  (exists errv : word, rw_cells psegs m' (errno_addr tp) [C4 errv]) -> rauxv_ok m' AB -> ps_so s' = ps_so s ->
  MID LBx' s' m'.
Proof.
  intros LBx LBx' LBp s s' m m' SPc H HP SUBL SUB HS HH' MI' ST' ER' AX' SO'.
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  pose proof (same_on_rheap_pres _ _ _ _ HP) as SO.
  constructor.
  - exact HH'.
  - exact MI'.
  - destruct (stk_split psegs m lo SPc usp (md_stk _ _ _ H) ltac:(lia)) as [_ STu].
    eapply stk_merge; [exact ST'| eapply rheap_pres_stk; [exact HP| exact STu| lia]| lia].
  - exact ER'.
  - exact AX'.
  - eapply harness_pres_trans; [exact (md_pres _ _ _ H)|]. apply harness_pres_of_heap.
    eapply rheap_pres_weaken; [exact HP| lia| exact SUBL].
  - rewrite SO'. exact (md_so _ _ _ H).
  - destruct (md_uf _ _ _ H) as [F1 F1w F1a F1b F2 F3 F4 F5 F6 F7].
    constructor; (rewrite (rdn_same_on _ m m' _ _ SO); [assumption| intros x Hx; left; cbn in Hx; lia| lia| cbn; lia]).
  - eapply pay_same_on; [exact SO| | exact (md_pay _ _ _ H)].
    intros b a Hb Ha. right; right. exists b. split; [apply SUBL; exact Hb| exact Ha].
  - apply Forall_forall. intros b Hb. destruct (SUB b Hb) as [[Hb' Hp]|WR]; [| exact WR].
    eapply rheap_pres_wr_at; [exact HP| exact (proj1 (Forall_forall _ _) (md_wr _ _ _ H) b Hb')|].
    right; right. exists b. split; [exact Hp| lia].
Qed.

Definition fp_ok (LBx : list block) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= UU + 112) \/ ((UU + 160 <= fst iv /\ snd iv <= UU + 184) \/ (UU + 208 <= fst iv /\ snd iv <= UU + 232))
  \/ (exists b, In b LBx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
  \/ (HBUF <= fst iv /\ snd iv <= HBUF + HBUF_N).

(* 1.4: the munch form (uncompress2's tail writes the fuzzer's sourceLen / destLen cells by a munch, not a frame_mod). *)
Lemma MID_mu : forall LBx s m m' (ivs : list (Z * Z)),
  MID LBx s m -> munch ivs m m' -> wmono psegs m m' -> Forall (fp_ok LBx) ivs -> MID LBx s m'.
Proof.
  intros LBx s m m' ivs H MU WM FW.
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  pose proof (same_on_munch _ _ _ MU WM) as SO.
  assert (BLK : forall b, In b (LBx ++ LB) -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (MID_blk _ _ _ b H Hb)).
  assert (OUT : forall x, (usp <= x \/ (UU + 112 <= x < UU + 160 \/ UU + 184 <= x < UU + 208) \/ (UU + 232 <= x) \/ (0x10000 <= x < 0x94000 /\ ~ hbuf_addr x)
                           \/ (exists b, In b LB /\ blk_addr b <= x < blk_addr b + blk_size b)) -> outside ivs x).
  { intros x Hx. apply (outside_Forall _ _ x FW). intros [a b] [K|[K|[(blk & Hb & K1 & K2)|K]]]; cbn [fst snd] in *; intros IN.
    - destruct Hx as [Hx|[Hx|[Hx|[[Hx _]|(b2 & Hb2 & Hx)]]]]; try lia.
      pose proof (BLK b2 ltac:(apply in_or_app; right; exact Hb2)) as (_ & _ & _ & B4 & _). lia.
    - destruct Hx as [Hx|[Hx|[Hx|[[Hx _]|(b2 & Hb2 & Hx)]]]]; try lia.
      pose proof (BLK b2 ltac:(apply in_or_app; right; exact Hb2)) as (_ & _ & _ & B4 & _). lia.
    - pose proof (BLK blk ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & B4 & B5).
      destruct Hx as [Hx|[Hx|[Hx|[[Hx _]|(b2 & Hb2 & Hx)]]]]; try lia.
      pose proof (MID_disj _ _ _ blk b2 H Hb Hb2). lia.
    - unfold hbuf_addr, HBUF, HBUF_N in *.
      destruct Hx as [Hx|[Hx|[Hx|[[Hx NB]|(b2 & Hb2 & Hx)]]]]; try lia.
      pose proof (BLK b2 ltac:(apply in_or_app; right; exact Hb2)) as (_ & _ & _ & _ & B5). lia. }
  constructor.
  - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact (md_heap _ _ _ H)| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros [a b] [K|[K|[(blk & Hb & K1 & K2)|K]]]; cbn [fst snd] in *.
    + left. cbn [fst]. lia.
    + left. cbn [fst]. lia.
    + right; right. exists blk. split; [apply in_or_app; left; exact Hb| cbn [fst snd]; lia].
    + right; left. cbn [fst snd]. unfold HBUF, HBUF_N, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *. lia.
  - eapply mem_inv_munch; [exact (md_mi _ _ _ H)| exact MU|]. intros a Ha. apply OUT. right; right; right; left.
    unfold hbuf_addr, HBUF, HBUF_N. lia.
  - eapply stk_wmono; [exact (md_stk _ _ _ H)| lia| exact WM].
  - destruct (md_err _ _ _ H) as [errv ER]. exists errv. eapply rw_cells_magree; [exact SO| exact ER|].
    intros a Ha. apply OUT. right; right; right; left. rewrite TP in Ha. unfold wz, RATP in Ha. rewrite unsigned_lit in Ha by lia.
    change (Z.of_nat (cells_size [C4 errv])) with 4 in Ha. unfold hbuf_addr, HBUF, HBUF_N. lia.
  - eapply rauxv_ok_frame; [exact (md_aux _ _ _ H)| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. intros [a b] [K|[K|[(blk & Hb & K1 & K2)|K]]]; cbn [fst snd] in *; unfold RAUXV_CELL.
    + split; [lia| right; lia].
    + split; [lia| right; lia].
    + pose proof (BLK blk ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & B4 & B5). split; [lia| lia].
    + unfold HBUF, HBUF_N in *. split; [lia| left; lia].
  - eapply harness_pres_trans; [exact (md_pres _ _ _ H)|]. intros a Ha Hc NB. apply SO; [exact Ha|]. apply OUT.
    destruct Hc as [Hc|[[Hc NS]|(b & Hb & Hr)]]; [left; exact Hc| right; right; right; left; split; [lia| exact NB]|].
    right; right; right; right. exists b. split; [exact Hb| exact Hr].
  - exact (md_so _ _ _ H).
  - destruct (md_uf _ _ _ H) as [F1 F1w F1a F1b F2 F3 F4 F5 F6 F7].
    constructor; (rewrite (rdn_same_on _ m m' _ _ SO); [assumption| intros x Hx; apply OUT; cbn in Hx; lia| lia| cbn; lia]).
  - eapply pay_same_on; [exact SO| | exact (md_pay _ _ _ H)].
    intros b a Hb Ha. apply OUT. right; right; right; right. exists b. split; [exact Hb| exact Ha].
  - eapply Forall_impl; [| exact (md_wr _ _ _ H)]. intros b (W0 & W1 & W). split; [exact W0|]. split; [exact W1|].
    intros i Hi. apply WM. apply W. exact Hi.
Qed.

Lemma MID_fm : forall LBx s m m' rs,
  MID LBx s m -> OF.frame_mod m m' rs -> Forall (fp_ok LBx) (fm_ivs rs) -> MID LBx s m'.
Proof.
  intros LBx s m m' rs H FM FW.
  destruct (munch_of_frame_mod _ _ _ FM) as [MU WM].
  exact (MID_mu LBx s m m' (fm_ivs rs) H MU WM FW).
Qed.

Lemma lib_layout_of_MID : forall LBx s m (pp : bptr) (p : Z),
  MID LBx s m -> In (pp, p, OL.S7_INFL_N) LBx -> OL.lib_layout_S7 ATOP m UU p D n.
Proof.
  intros LBx s m pp p H Hin.
  pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof n_nonneg as N0.
  pose proof (MID_blk _ _ _ (pp, p, OL.S7_INFL_N) H ltac:(apply in_or_app; left; exact Hin)) as (P1 & P2 & P3 & P4 & P5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5.
  assert (PAYLOC : (n = 0 /\ D = 0x32e90) \/ ((D + n <= 0x10000 \/ 0x94000 <= D) /\ (D + n <= p \/ p + OL.S7_INFL_N <= D))).
  { destruct PB as [E|(b & Hb & B1 & B2)]; [left; exact E| right].
    pose proof (MID_blk _ _ _ b H ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & Q5).
    pose proof (MID_disj _ _ _ (pp, p, OL.S7_INFL_N) b H Hin Hb) as DJ. cbn [blk_addr blk_size fst snd] in DJ. lia. }
  unfold OL.lib_layout_S7, OL.S7_FRA, OL.S7_IMG_TOP, OL.S7_INFL_N, OL.S7_BUF, OL.S7_BUF_N, OL.S7_RO_LO, OL.S7_RO_HI in *.
  unfold HARNESS_STACK in LO.
  repeat split; try lia; try assumption.
  - intros i Hi. pose proof (payload_rdn m D pbytes (md_pay _ _ _ H) i) as X. rewrite length_map in X. apply X. unfold zlength in Hi. lia.
  - intros i Hi. apply (pristine_of_mem_inv m (md_mi _ _ _ H)). lia.
  - apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ H)| lia| lia].
  - pose proof (proj1 (Forall_forall _ _) (md_wr _ _ _ H) _ Hin) as WR. cbn [blk_addr blk_size fst snd] in WR.
    pose proof (wr_at_store_ok psegs m p 7176 0 (Z.to_nat 7176) WR ltac:(lia) ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X.
Qed.


(* 1.4: the harness's two frames below usp as rw_cells: LLVMFuzzerTestOneInput's (usp-32: a cell, sourceLen, destLen,
   ra) and uncompress2's (usp-80: a cell, the sourceLen / destLen copies, its saved s1 / s0, its ra). *)
Lemma ret_cells : forall LBx s m, MID LBx s m ->
  exists w0 sl dl b0 bsl bdl : word,
    rw_cells psegs m (usp - 80) [C8 w0; C8 sl; C8 dl; C8 s1; C8 s0; C8 (Z_to_bv 64 S7_UNC_RA)] /\
    rw_cells psegs m (usp - 32) [C8 b0; C8 bsl; C8 bdl; C8 ra].
Proof.
  intros LBx s m H. pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  destruct (md_uf _ _ _ H) as [F_hra F_wra F_us0 F_us1 _ _ _ _ _ _].
  pose proof (md_stk _ _ _ H) as ST.
  rewrite <- (le8_lit S7_UNC_RA) in F_wra by (unfold S7_UNC_RA; lia).
  destruct (stk_carve psegs m lo usp 32%nat ST ltac:(lia)) as [ST1 [j1 C1]].
  destruct (stk_carve psegs m lo (usp - Z.of_nat 32) 48%nat ST1 ltac:(lia)) as [_ [j0 C0]].
  change (Z.of_nat 32) with 32 in C1, C0. change (Z.of_nat 48) with 48 in C0.
  replace (usp - 32 - 48) with (usp - 80) in C0 by lia.
  pose proof (rw_cells_peel8 m (usp - 32) [] 24 j1 [] C1) as C1a. cbn [app] in C1a.
  pose proof (rw_cells_peel8 m (usp - 32) [_] 16 _ [] C1a) as C1b. cbn [app] in C1b.
  pose proof (rw_cells_peel8 m (usp - 32) [_; _] 8 _ [] C1b) as C1c. cbn [app] in C1c.
  pose proof (rw_cells_last8 m (usp - 32) [_; _; _] _ C1c) as C1d. cbn [app] in C1d.
  pose proof (rw_cells_C8_eq m (usp - 32) [_; _; _] _ ra [] _ C1d F_hra ltac:(cbn; lia)) as C1e. cbn [app] in C1e.
  pose proof (rw_cells_peel8 m (usp - 80) [] 40 j0 [] C0) as C0a. cbn [app] in C0a.
  pose proof (rw_cells_peel8 m (usp - 80) [_] 32 _ [] C0a) as C0b. cbn [app] in C0b.
  pose proof (rw_cells_peel8 m (usp - 80) [_; _] 24 _ [] C0b) as C0c. cbn [app] in C0c.
  pose proof (rw_cells_peel8 m (usp - 80) [_; _; _] 16 _ [] C0c) as C0d. cbn [app] in C0d.
  pose proof (rw_cells_peel8 m (usp - 80) [_; _; _; _] 8 _ [] C0d) as C0e. cbn [app] in C0e.
  pose proof (rw_cells_last8 m (usp - 80) [_; _; _; _; _] _ C0e) as C0f. cbn [app] in C0f.
  pose proof (rw_cells_C8_eq m (usp - 80) [_; _; _] _ s1 [_; _] _ C0f F_us1 ltac:(cbn; lia)) as C0g. cbn [app] in C0g.
  pose proof (rw_cells_C8_eq m (usp - 80) [_; _; _; _] _ s0 [_] _ C0g F_us0 ltac:(cbn; lia)) as C0h. cbn [app] in C0h.
  pose proof (rw_cells_C8_eq m (usp - 80) [_; _; _; _; _] _ (Z_to_bv 64 S7_UNC_RA) [] _ C0h F_wra ltac:(cbn; lia)) as C0i.
  cbn [app] in C0i.
  eexists _, _, _, _, _, _. split; [exact C0i | exact C1e].
Qed.

(* 1.4: from uncompress2's return point (0x14f04, sp = usp-80, s0 / s1 = usp-24 / usp-16 = &sourceLen / &destLen)
   back to the harness. *)
Lemma L_ret : forall s m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  MID [] s m ->
  implM psegs (mret 0) s POST
    (MS (mkR x1 (Z_to_bv 64 (usp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x14f64) fc None m (seg_rom psegs)).
Proof.
  intros s m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO. apply implM_ret.
  destruct (ret_cells [] s m H) as (w0 & sl & dl & b0 & bsl & bdl & FR0 & FR).
  eapply (u2_seg_ret_evt usp); try exact U1; [exact FR0 | exact FR |].
  intros M1 MU1 WM1.
  assert (H1 : MID [] s M1).
  { apply (MID_mu [] s m M1 _ H MU1 WM1). constructor; [| constructor]. right; left. cbn [fst snd]. lia. }
  destruct (md_err _ _ _ H1) as [errv ER].
  unfold fuzz_one_post. exists x5, x6, x7, sl, dl, x13, x14, x15, x16, x17, x28, x29, x30, x31, F, fc, M1, errv.
  rewrite (Z_to_bv_bv_unsigned sp).
  split; [reflexivity|]. split; [lia|]. split; [exact (md_mi _ _ _ H1)|]. split; [exact FRM|]. split; [exact (md_stk _ _ _ H1)|].
  split; [exact ER|]. split; [exact (md_aux _ _ _ H1)|]. split; [exact (md_pres _ _ _ H1)|]. split; [exact (md_heap _ _ _ H1)|].
  exact (md_so _ _ _ H1).
Qed.

Lemma L_zc : forall s m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  MID [] s m ->
  OP.rdn psegs m (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.S7_RA2) ->
  implM psegs (mret 0) s POST
    (MS (mkR x1 (Z_to_bv 64 (UU - 16)) gp tp x5 x6 x7 (Z_to_bv 64 UU) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5
             s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 OL.S7_ZC) fc None m (seg_rom psegs)).
Proof.
  intros s m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 H RA2.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  destruct (md_uf _ _ _ H) as [F_hra F_wra F_us0 F_us1 F_ura F_s0 F_s1 F_s2 F_s3 F_s4].
  set (R0 := mkR x1 (Z_to_bv 64 (UU - 16)) gp tp x5 x6 x7 (Z_to_bv 64 UU) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5
                 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31).
  destruct (OL.run_zc_S7 CT R0 m UU (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) s2 s3 s4 s5) as (R' & m' & RUN & FM & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & ZK).
  1: reflexivity. 1: reflexivity. 1: exact U4. 1: unfold OL.S7_IMG_TOP; lia. 1: lia.
  1: { change (Z.to_nat 224) with 224%nat. apply (store_ok_of_stk m lo usp); [exact (md_stk _ _ _ H)| lia| lia]. }
  1: exact RA2. 1: exact F_ura. 1: exact F_s0. 1: exact F_s1. 1: exact F_s2. 1: exact F_s3. 1: exact F_s4.
  assert (H' : MID [] s m').
  { apply (MID_fm [] s m m' _ H FM). unfold fm_ivs. cbn [map fst snd]. rewrite unsigned_lit by lia.
    constructor; [| constructor]. left. cbn [fst snd]. lia. }
  eapply implM_evt with (P := fun ms' => exists y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word,
      ms' = MS (mkR y1 (Z_to_bv 64 (usp - 80)) gp tp y5 y6 y7 (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
               F (Z_to_bv 64 0x14f64) fc None m' (seg_rom psegs)).
  - eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
    intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ER'.
    subst R'.
    destruct (zc_regs_mkR R0 UU (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) s2 s3 s4 gp tp s5 s6 s7 s8 s9 s10 s11
                y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
                Z2 Z8 Z9 Z18 Z19 Z20 Z21 ZK eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
      as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
    exists y1, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31.
    replace (UU + 160) with (usp - 80) by lia. reflexivity.
  - intros ms' (y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & ->).
    apply (L_ret s m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H').
Qed.

Lemma MID_stk_below : forall LBx s m SPc, MID LBx s m -> lo <= SPc <= usp -> stk psegs m lo SPc.
Proof. intros LBx s m SPc H HS. exact (proj1 (stk_split psegs m lo SPc usp (md_stk _ _ _ H) HS)). Qed.

Lemma L_ze2 : forall s m (pp : bptr) (p : Z) (y1 y5 y6 y7 y9 y12 y13 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 : word),
  MID [(pp, p, OL.S7_INFL_N)] s m ->
  OP.rdn psegs m (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.S7_RA2) ->
  implM psegs (HarnessC.fuzz_without raw_free [pp]) s POST
    (MS (mkR y1 (Z_to_bv 64 (UU - 16)) gp tp y5 y6 y7 (Z_to_bv 64 UU) y9 (Z_to_bv 64 0) (Z_to_bv 64 p) y12 y13 (Z_to_bv 64 0x17228) y15 y16 y17
             y18 y19 y20 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (Z_to_bv 64 0x171fc) fc None m (seg_rom psegs)).
Proof.
  intros s m pp p y1 y5 y6 y7 y9 y12 y13 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 H RA2.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  destruct (md_err _ _ _ H) as [errv ER].
  unfold HarnessC.fuzz_without. cbn [free_all]. apply implM_bind_assoc.
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply u2_seg_ze2_evt; reflexivity| intros ms' ->].
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := [(pp, p, OL.S7_INFL_N)] ++ LB) (p := pp) (A := p) (n := OL.S7_INFL_N) (errv := errv);
      rewrite ?(unsigned_lit (usp - 240 - 16)) by lia.
    - exact (md_heap _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp - 240 - 16)) in ST' by lia. rewrite ?(unsigned_lit (usp - 240 - 16)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ H)) as ND.
  cbn [app] in HPR, HEAP', ND. rewrite (lb_remove_head (pp, p, OL.S7_INFL_N) LB ND) in HPR, HEAP'.
  assert (H' : MID [] s' m').
  { apply (MID_heap [(pp, p, OL.S7_INFL_N)] [] LB s s' m m' (UU - 16) H); cbn [app];
      [exact HPR| intros b Hb; exact Hb| intros b []| lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  assert (RA2' : OP.rdn psegs m' (Z_to_bv 64 (UU - 8)) 8 = Some (Z_to_le_bytes 8 OL.S7_RA2)).
  { rewrite <- RA2. apply (rdn_same_on _ m m' _ _ (same_on_rheap_pres _ _ _ _ HPR)); [intros x Hx; left; cbn in Hx; lia| lia| cbn; lia]. }
  apply implM_retb.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  apply (L_zc s' m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H' RA2').
Qed.

Lemma end_cells_heap : forall LBc SPc m m' p, rheap_pres LBc SPc m m' -> SPc <= UU - 16 ->
  OL.end_cells_S7 m UU p -> OL.end_cells_S7 m' UU p.
Proof.
  intros LBc SPc m m' p HPR HS (E1 & E2 & E3 & E4). pose proof usp_facts as (U1 & U2 & U3 & U4). unfold OL.end_cells_S7.
  repeat split;
    (rewrite (rdn_same_on _ m m' _ _ (same_on_rheap_pres _ _ _ _ HPR)); [assumption| intros x Hx; left; cbn in Hx; lia| lia| cbn; lia]).
Qed.

Lemma L_ze1 : forall s m (pw pp : bptr) (w p : Z) (y1 y5 y6 y7 y9 y12 y13 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 : word),
  MID [(pw, w, OL.S7_WIN_N); (pp, p, OL.S7_INFL_N)] s m ->
  OL.end_cells_S7 m UU p ->
  implM psegs (HarnessC.fuzz_without raw_free [pw; pp]) s POST
    (MS (mkR y1 (Z_to_bv 64 (UU - 16)) gp tp y5 y6 y7 (Z_to_bv 64 UU) y9 (Z_to_bv 64 0) (Z_to_bv 64 w) y12 y13 (Z_to_bv 64 0x17228) y15 y16 y17
             y18 y19 y20 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (Z_to_bv 64 0x171e4) fc None m (seg_rom psegs)).
Proof.
  intros s m pw pp w p y1 y5 y6 y7 y9 y12 y13 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 H EC.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  destruct (md_err _ _ _ H) as [errv ER].
  pose proof (MID_blk _ _ _ (pp, p, OL.S7_INFL_N) H ltac:(right; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5.
  unfold HarnessC.fuzz_without. cbn [free_all]. apply implM_bind_assoc.
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply u2_seg_ze1_evt; reflexivity| intros ms' ->].
  eapply implM_bind.
  { unfold rfree_stmt in FREE.
    eapply FREE with (lo := lo) (B := AB) (LB := [(pw, w, OL.S7_WIN_N); (pp, p, OL.S7_INFL_N)] ++ LB) (p := pw) (A := w) (n := OL.S7_WIN_N) (errv := errv);
      rewrite ?(unsigned_lit (usp - 240 - 16)) by lia.
    - exact (md_heap _ _ _ H).
    - left; reflexivity.
    - exact (md_aux _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RFREE_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ H).
    - exact TP.
    - reflexivity. }
  cbv beta. intros [] s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & HEAP').
  rewrite ?(unsigned_lit (usp - 240 - 16)) in ST' by lia. rewrite ?(unsigned_lit (usp - 240 - 16)) in HPR by lia.
  pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ (md_heap _ _ _ H)) as ND.
  cbn [app] in HPR, HEAP', ND. rewrite (lb_remove_head (pw, w, OL.S7_WIN_N) ((pp, p, OL.S7_INFL_N) :: LB) ND) in HPR, HEAP'.
  assert (H' : MID [(pp, p, OL.S7_INFL_N)] s' m').
  { apply (MID_heap [(pw, w, OL.S7_WIN_N); (pp, p, OL.S7_INFL_N)] [(pp, p, OL.S7_INFL_N)] ((pp, p, OL.S7_INFL_N) :: LB) s s' m m' (UU - 16) H); cbn [app];
      [exact HPR| intros b Hb; right; exact Hb| intros b Hb; left; split; [right; exact Hb| destruct Hb as [<-|[]]; left; reflexivity]
      | lia| exact HEAP'| exact MI'| exact ST'| exists errv; exact ERR'| exact AUX'| exact SOE]. }
  pose proof (end_cells_heap _ _ m m' p HPR ltac:(lia) EC) as EC'.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply (u2_seg_ze1b_evt usp); [exact EC'| lia| reflexivity]| intros ms' ->].
  apply (L_ze2 s' m' pp p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H' (proj1 EC')).
Qed.

Lemma ZW_heap : forall LBp SPc m m' (pp : bptr) (p : Z) (sW : list Z),
  rheap_pres LBp SPc m m' -> SPc <= UU - 272 -> In (pp, p, OL.S7_INFL_N) LBp -> (forall b, In b LB -> In b LBp) ->
  ZW UU p D n ATOP SE sW m -> ZW UU p D n ATOP SE sW m'.
Proof.
  intros LBp SPc m m' pp p sW HPR HS Hp SUBL HZ.
  pose proof usp_facts as (U1 & U2 & U3 & U4).
  apply (OL.zw_local_S7 CT UU p D n ATOP SE sW m m'); [| exact HZ].
  intros a IN. pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with (2^64) in RA.
  assert (CA : rclient_addr LBp SPc (bv_unsigned a)).
  { unfold OL.in_fpw_S7, OL.S7_ZWD, OL.S7_INFL_N, OL.S7_BUF, OL.S7_BUF_N in IN. cbv zeta in IN.
    destruct IN as [IN|[IN|[IN|IN]]].
    - left. lia.
    - right; right. exists (pp, p, OL.S7_INFL_N). split; [exact Hp|]. cbn [blk_addr blk_size fst snd]. unfold OL.S7_INFL_N. lia.
    - right; left. split; [lia|]. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia.
    - right; right. destruct PB as [[E _]|(b & Hb & B1 & B2)]; [exfalso; lia|].
      exists b. split; [apply SUBL; exact Hb| lia]. }
  destruct (HPR (bv_unsigned a) RA CA) as [E _]. unfold wa in E. rewrite (Z_to_bv_bv_unsigned a) in E. exact E.
Qed.

Lemma L_zw : forall s m (pp : bptr) (p : Z)
    (y1 y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  MID [(pp, p, OL.S7_INFL_N)] s m ->
  ZW UU p D n ATOP SE [bv_unsigned y8; bv_unsigned y9; bv_unsigned y18; bv_unsigned y19; bv_unsigned y20; bv_unsigned y21;
                       bv_unsigned y22; bv_unsigned y23; bv_unsigned y24; bv_unsigned y25; bv_unsigned y26; bv_unsigned y27] m ->
  implM psegs (HarnessC.fuzz_with raw_malloc raw_free Client.CLIENT_OPT [pp]) s POST
    (MS (mkR y1 (Z_to_bv 64 (UU - 272)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x17218) y14 y15 y16 y17
             y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
        F (Z_to_bv 64 0x1706c) fc None m (seg_rom psegs)).
Proof.
  intros s m pp p y1 y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 H HZ.
  pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof n_nonneg as N0. unfold HARNESS_STACK in LO.
  destruct (md_err _ _ _ H) as [errv ER].
  pose proof (MID_blk _ _ _ (pp, p, OL.S7_INFL_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5.
  unfold HarnessC.fuzz_with, Client.CLIENT_OPT, Client.WINDOW_SIZE. cbn [alloc_all]. apply implM_bind_assoc.
  eapply implM_evt with (P := fun ms' => ms' = _); [eapply u2_seg_zw_evt; reflexivity| intros ms' ->].
  eapply implM_bind.
  { unfold rmalloc_stmt in MALLOC.
    eapply MALLOC with (lo := lo) (B := AB) (LB := [(pp, p, OL.S7_INFL_N)] ++ LB) (n := 32768) (errv := errv);
      rewrite ?(unsigned_lit (usp - 240 - 272)) by lia.
    - exact (md_heap _ _ _ H).
    - exact (md_aux _ _ _ H).
    - lia.
    - apply (MID_stk_below _ _ _ _ H). lia.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER.
    - exact (md_mi _ _ _ H).
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros r s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp - 240 - 272)) in ST' by lia. rewrite ?(unsigned_lit (usp - 240 - 272)) in HPR by lia.
  cbn [app] in HPR.
  pose proof (ZW_heap _ _ m m' pp p _ HPR ltac:(lia) ltac:(left; reflexivity) ltac:(intros b Hb; right; exact Hb) HZ) as HZ'.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  destruct r as [pw|].
  -
    destruct RES as (A & junk & -> & BR & HEAP' & BLK & _).
    destruct BR as (A1 & A2 & A3 & A4 & A5).
    pose proof (rw_cells_wr_at _ _ _ _ 32768 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
    assert (H' : MID [(pw, A, OL.S7_WIN_N); (pp, p, OL.S7_INFL_N)] s' m').
    { apply (MID_heap [(pp, p, OL.S7_INFL_N)] [(pw, A, OL.S7_WIN_N); (pp, p, OL.S7_INFL_N)] ((pp, p, OL.S7_INFL_N) :: LB) s s' m m' (UU - 272) H); cbn [app];
        [exact HPR| intros b Hb; right; exact Hb
        | intros b [<-|[<-|[]]]; [right; exact WRA| left; split; left; reflexivity]
        | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
    pose proof (MID_disj2 _ _ _ _ _ H') as DJ. cbn [blk_addr blk_size fst snd] in DJ.
    pose proof (lib_layout_of_MID _ _ _ pp p H' ltac:(right; left; reflexivity)) as LAY.
    set (R0 := mkR (Z_to_bv 64 0x17070) (Z_to_bv 64 (UU - 272)) gp tp w0 w1 w2 y8 y9 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                   y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 w3 w4 w5 w6).
    pose proof (OL.run_zb_S7 CT R0 m' UU (Z_to_bv 64 p) (Z_to_bv 64 D) (Z_to_bv 64 A) n ATOP SE
                  [bv_unsigned y8; bv_unsigned y9; bv_unsigned y18; bv_unsigned y19; bv_unsigned y20; bv_unsigned y21;
                   bv_unsigned y22; bv_unsigned y23; bv_unsigned y24; bv_unsigned y25; bv_unsigned y26; bv_unsigned y27]) as ZB.
    cbv zeta in ZB. rewrite (unsigned_lit p), (unsigned_lit D), (unsigned_lit A) in ZB by lia.
    destruct ZB as (R' & m'' & RUN & FM & ER' & EC).
    1: reflexivity. 1: reflexivity. 1: reflexivity. 1: exact HZ'. 1: exact LAY.
    1: exact A2. 1: exact A1. 1: unfold OL.S7_WIN_N; lia.
    1: { unfold OL.S7_BUF, OL.S7_BUF_N, OL.S7_WIN_N. lia. }
    1: { unfold OL.S7_INFL_N, OL.S7_WIN_N in *. lia. }
    1: { unfold OL.S7_WIN_N. destruct PB as [[E0 E1]|(b & Hb & B1 & B2)]; [unfold PEMPTY in E1; lia|].
         pose proof (MID_disj _ _ _ (pw, A, OL.S7_WIN_N) b H' ltac:(left; reflexivity) Hb) as DJ2. cbn [blk_addr blk_size fst snd] in DJ2.
         unfold OL.S7_WIN_N in DJ2. lia. }
    1: { unfold OL.S7_WIN_N, OL.S7_IMG_TOP. lia. }
    1: { pose proof (wr_at_store_ok psegs m' A 32768 0 (Z.to_nat 32768) WRA ltac:(lia) ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
    assert (H'' : MID [(pw, A, OL.S7_WIN_N); (pp, p, OL.S7_INFL_N)] s' m'').
    { apply (MID_fm _ s' m' m'' _ H' FM). unfold OL.WA_S7, fm_ivs, OL.S7_FRA, OL.S7_INFL_N, OL.S7_BUF, OL.S7_BUF_N, OL.S7_WIN_N.
      cbn [map fst snd app]. rewrite !unsigned_lit by lia.
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; right; left; exists (pp, p, 7176); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
      apply Forall_cons; [right; right; right; cbn [fst snd]; unfold HBUF, HBUF_N; lia|].
      apply Forall_cons; [right; right; left; exists (pw, A, 32768); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
      apply Forall_nil. }
    apply implM_retb.
    eapply implM_evt with (P := fun ms' => exists z1 z5 z6 z7 z9 z12 z13 z15 z16 z17 z18 z19 z20 z28 z29 z30 z31 : word,
        ms' = MS (mkR z1 (Z_to_bv 64 (UU - 16)) gp tp z5 z6 z7 (Z_to_bv 64 UU) z9 (Z_to_bv 64 0) (Z_to_bv 64 A) z12 z13 (Z_to_bv 64 0x17228) z15 z16 z17
                      z18 z19 z20 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                 F (Z_to_bv 64 0x171e4) fc None m'' (seg_rom psegs)).
    + eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m' m'' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
      intros z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 EQ.
      subst R'.
      destruct (end_regs_mkR R0 UU A gp tp s5 s6 s7 s8 s9 s10 s11
                  z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
                  ER' eq_refl eq_refl)
        as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
      exists z1, z5, z6, z7, z9, z12, z13, z15, z16, z17, z18, z19, z20, z28, z29, z30, z31. reflexivity.
    + intros ms' (z1 & z5 & z6 & z7 & z9 & z12 & z13 & z15 & z16 & z17 & z18 & z19 & z20 & z28 & z29 & z30 & z31 & ->).
      apply (L_ze1 s' m'' pw pp A p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H'' EC).
  -
    destruct RES as (-> & HEAP').
    assert (H' : MID [(pp, p, OL.S7_INFL_N)] s' m').
    { apply (MID_heap [(pp, p, OL.S7_INFL_N)] [(pp, p, OL.S7_INFL_N)] ((pp, p, OL.S7_INFL_N) :: LB) s s' m m' (UU - 272) H); cbn [app];
        [exact HPR| intros b Hb; right; exact Hb
        | intros b [<-|[]]; left; split; left; reflexivity
        | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
    pose proof (lib_layout_of_MID _ _ _ pp p H' ltac:(left; reflexivity)) as LAY.
    set (R0 := mkR (Z_to_bv 64 0x17070) (Z_to_bv 64 (UU - 272)) gp tp w0 w1 w2 y8 y9 (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7
                   y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 w3 w4 w5 w6).
    pose proof (OL.run_zb0_S7 CT R0 m' UU (Z_to_bv 64 p) (Z_to_bv 64 D) n ATOP SE
                  [bv_unsigned y8; bv_unsigned y9; bv_unsigned y18; bv_unsigned y19; bv_unsigned y20; bv_unsigned y21;
                   bv_unsigned y22; bv_unsigned y23; bv_unsigned y24; bv_unsigned y25; bv_unsigned y26; bv_unsigned y27]) as ZB.
    cbv zeta in ZB. rewrite (unsigned_lit p), (unsigned_lit D) in ZB by lia.
    destruct ZB as (R' & m'' & RUN & FM & ER' & EC).
    1: reflexivity. 1: reflexivity. 1: reflexivity. 1: exact HZ'. 1: exact LAY.
    assert (H'' : MID [(pp, p, OL.S7_INFL_N)] s' m'').
    { apply (MID_fm _ s' m' m'' _ H' FM). unfold OL.WA_S7, fm_ivs, OL.S7_FRA, OL.S7_INFL_N, OL.S7_BUF, OL.S7_BUF_N.
      cbn [map fst snd app]. rewrite !unsigned_lit by lia.
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [right; right; left; exists (pp, p, 7176); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
      apply Forall_cons; [right; right; right; cbn [fst snd]; unfold HBUF, HBUF_N; lia|].
      apply Forall_nil. }
    apply implM_retb.
    eapply implM_evt with (P := fun ms' => exists z1 z5 z6 z7 z9 z12 z13 z15 z16 z17 z18 z19 z20 z28 z29 z30 z31 : word,
        ms' = MS (mkR z1 (Z_to_bv 64 (UU - 16)) gp tp z5 z6 z7 (Z_to_bv 64 UU) z9 (Z_to_bv 64 0) (Z_to_bv 64 p) z12 z13 (Z_to_bv 64 0x17228) z15 z16 z17
                      z18 z19 z20 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                 F (Z_to_bv 64 0x171fc) fc None m'' (seg_rom psegs)).
    + eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m' m'' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
      intros z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 EQ.
      subst R'.
      destruct (end_regs_mkR R0 UU p gp tp s5 s6 s7 s8 s9 s10 s11
                  z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
                  ER' eq_refl eq_refl)
        as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
      exists z1, z5, z6, z7, z9, z12, z13, z15, z16, z17, z18, z19, z20, z28, z29, z30, z31. reflexivity.
    + intros ms' (z1 & z5 & z6 & z7 & z9 & z12 & z13 & z15 & z16 & z17 & z18 & z19 & z20 & z28 & z29 & z30 & z31 & ->).
      apply (L_ze2 s' m'' pp p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H'' (proj1 EC)).
Qed.

Lemma za_cells_heap : forall LBc SPc m m', rheap_pres LBc SPc m m' -> SPc <= UU - 32 ->
  u2_za_cells usp m D -> u2_za_cells usp m' D.
Proof.
  intros LBc SPc m m' HPR HS [Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9]. pose proof usp_facts as (U1 & U2 & U3 & U4).
  constructor;
    (rewrite (rdn_same_on _ m m' _ _ (same_on_rheap_pres _ _ _ _ HPR)); [assumption| intros x Hx; left; cbn in Hx; lia| lia| cbn; lia]).
Qed.

Lemma L_za : forall s m (pp : bptr) (p : Z)
    (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
  MID [(pp, p, OL.S7_INFL_N)] s m ->
  u2_za_cells usp m D ->
  implMC psegs (cchoice (clift (HarnessC.fuzz_with raw_malloc raw_free Client.CLIENT_OPT [pp])) (clift (HarnessC.fuzz_without raw_free [pp]))) s POST
    (MS (mkR (Z_to_bv 64 0x1516c) (Z_to_bv 64 (usp - 272)) gp tp y5 y6 y7 (Z_to_bv 64 (usp - 64)) (Z_to_bv 64 (usp - 240))
             (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
             (Z_to_bv 64 0x32eb0) (Z_to_bv 64 n) (Z_to_bv 64 0x40000) s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (Z_to_bv 64 0x1516c) fc None m (seg_rom psegs)).
Proof.
  intros s m pp p y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 H ZC.
  pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof n_nonneg as N0. unfold HARNESS_STACK in LO.
  pose proof (MID_blk _ _ _ (pp, p, OL.S7_INFL_N) H ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5).
  cbn [blk_addr blk_size fst snd] in P1, P2, P3, P4, P5.
  pose proof (lib_layout_of_MID _ _ _ pp p H ltac:(left; reflexivity)) as LAY.
  destruct ZC as [Z_s2 Z_s1 Z_s0 Z_ra Z_in Z_av Z_za Z_zf Z_op].
  replace (usp - 272) with (UU - 32) by lia.
  set (R0 := mkR (Z_to_bv 64 0x1516c) (Z_to_bv 64 (UU - 32)) gp tp y5 y6 y7 (Z_to_bv 64 (usp - 64)) (Z_to_bv 64 UU)
                 (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 0x32eb0) (Z_to_bv 64 n) (Z_to_bv 64 0x40000) s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31).
  pose proof (OL.run_za_S7 CT R0 m UU (Z_to_bv 64 p) (Z_to_bv 64 D) n ATOP) as ZA.
  cbv zeta in ZA. rewrite (unsigned_lit p), (unsigned_lit D) in ZA by lia.
  destruct ZA as (R' & m' & pc' & RUN & FM & EXIT).
  1: reflexivity. 1: reflexivity. 1: reflexivity. 1: reflexivity. 1: reflexivity. 1: exact LAY.
  1: exact Z_s2. 1: exact Z_s1. 1: exact Z_s0. 1: exact Z_ra. 1: exact Z_in. 1: exact Z_av. 1: exact Z_za. 1: exact Z_zf. 1: exact Z_op.
  assert (H' : MID [(pp, p, OL.S7_INFL_N)] s m').
  { apply (MID_fm _ s m m' _ H FM). unfold OL.WA_S7, fm_ivs, OL.S7_FRA, OL.S7_INFL_N, OL.S7_BUF, OL.S7_BUF_N.
    cbn [map fst snd app]. rewrite !unsigned_lit by lia.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; right; left; exists (pp, p, 7176); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
    apply Forall_cons; [right; right; right; cbn [fst snd]; unfold HBUF, HBUF_N; lia|].
    apply Forall_nil. }
  destruct EXIT as [(-> & ER' & EC)|(-> & W13 & W10 & W11 & W12 & W2 & W3 & W4 & HZ)].
  -
    apply implMC_choice_r. apply implMC_lift.
    eapply implM_evt with (P := fun ms' => exists z1 z5 z6 z7 z9 z12 z13 z15 z16 z17 z18 z19 z20 z28 z29 z30 z31 : word,
        ms' = MS (mkR z1 (Z_to_bv 64 (UU - 16)) gp tp z5 z6 z7 (Z_to_bv 64 UU) z9 (Z_to_bv 64 0) (Z_to_bv 64 p) z12 z13 (Z_to_bv 64 0x17228) z15 z16 z17
                      z18 z19 z20 s5 s6 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                 F (Z_to_bv 64 0x171fc) fc None m' (seg_rom psegs)).
    + eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
      intros z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 EQ.
      subst R'.
      destruct (end_regs_mkR R0 UU p gp tp s5 s6 s7 s8 s9 s10 s11
                  z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
                  ER' eq_refl eq_refl)
        as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
      exists z1, z5, z6, z7, z9, z12, z13, z15, z16, z17, z18, z19, z20, z28, z29, z30, z31. reflexivity.
    + intros ms' (z1 & z5 & z6 & z7 & z9 & z12 & z13 & z15 & z16 & z17 & z18 & z19 & z20 & z28 & z29 & z30 & z31 & ->).
      apply (L_ze2 s m' pp p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H' (proj1 EC)).
  -
    apply implMC_choice_l. apply implMC_lift.
    eapply implM_evt with (P := fun ms' => exists z1 z5 z6 z7 z8 z9 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word,
        ZW UU p D n ATOP SE [bv_unsigned z8; bv_unsigned z9; bv_unsigned z18; bv_unsigned z19; bv_unsigned z20; bv_unsigned z21;
                             bv_unsigned z22; bv_unsigned z23; bv_unsigned z24; bv_unsigned z25; bv_unsigned z26; bv_unsigned z27] m'
        /\ ms' = MS (mkR z1 (Z_to_bv 64 (UU - 272)) gp tp z5 z6 z7 z8 z9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 0x17218) z14 z15 z16 z17
                      z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)
                 F (Z_to_bv 64 0x1706c) fc None m' (seg_rom psegs)).
    + eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
      intros z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 EQ.
      subst R'.
      destruct (zw_regs_mkR R0 UU gp tp
                  z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31
                  W13 W10 W11 W12 W2 W3 W4 eq_refl eq_refl)
        as (-> & -> & -> & -> & -> & -> & ->).
      exists z1, z5, z6, z7, z8, z9, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31.
      split; [exact HZ| reflexivity].
    + intros ms' (z1 & z5 & z6 & z7 & z8 & z9 & z14 & z15 & z16 & z17 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31 & HZ' & ->).
      apply (L_zw s m' pp p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H' HZ').
Qed.

Lemma MID_entry : forall (M1 : mem) (errv : word),
  RHEAP st0 LB m0 -> bytes_at psegs m0 D pbytes -> rauxv_ok m0 AB -> stk psegs m0 lo usp ->
  rw_cells psegs m0 (errno_addr tp) [C4 errv] -> mem_inv psegs m0 ->
  munch [(usp - 272, usp)] m0 M1 -> wmono psegs m0 M1 -> mem_inv psegs M1 ->
  u2_frames usp M1 ra s0 s1 s2 s3 s4 s5 ->
  MID [] st0 M1.
Proof.
  intros M1 errv HEAP BY AUX ST ER MI MU WM MI1 UF.
  pose proof usp_facts as (U1 & U2 & U3 & U4). unfold HARNESS_STACK in LO.
  pose proof (same_on_munch _ _ _ MU WM) as SO.
  assert (OUT : forall x, usp <= x \/ x < usp - 272 -> outside [(usp - 272, usp)] x).
  { intros x Hx. cbn [outside fst snd]. split; [lia| exact I]. }
  assert (BLK : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
  { intros b Hb. exact (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b HEAP Hb). }
  constructor.
  - cbn [app]. eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|].
    apply Forall_cons; [left; cbn [fst]; lia| apply Forall_nil].
  - exact MI1.
  - eapply stk_wmono; [exact ST| lia| exact WM].
  - exists errv. eapply rw_cells_magree; [exact SO| exact ER|].
    intros a Ha. apply OUT. right. rewrite TP in Ha. unfold wz, RATP in Ha. rewrite unsigned_lit in Ha by lia.
    change (Z.of_nat (cells_size [C4 errv])) with 4 in Ha. lia.
  - eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
    apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; split; [lia| right; lia]| apply Forall_nil].
  - intros a Ha Hc NB. apply SO; [exact Ha|]. apply OUT.
    destruct Hc as [Hc|[[Hc NS]|(b & Hb & Hr)]]; [left; exact Hc| right; lia|].
    pose proof (BLK b Hb) as (_ & _ & _ & B4 & _). right. lia.
  - reflexivity.
  - exact UF.
  - eapply pay_same_on; [exact SO| | exact BY].
    intros b a Hb Ha. apply OUT. pose proof (BLK b Hb) as (_ & _ & _ & B4 & _). right. lia.
  - apply Forall_nil.
Qed.

Theorem fuzz_one_call : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (errv : word),
  RHEAP st0 LB m0 -> bytes_at psegs m0 D pbytes -> harness_cells m0 ->
  rauxv_ok m0 AB -> stk psegs m0 lo usp -> rw_cells psegs m0 (errno_addr tp) [C4 errv] -> mem_inv psegs m0 ->
  implMC psegs (ProgC.fuzz_oneC payload) st0 POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PFUZZ_ENTRY) fc None m0 (seg_rom psegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv HEAP BY GOT AUX ST ER MI.
  pose proof usp_facts as (U1 & U2 & U3 & U4). pose proof n_nonneg as N0. unfold HARNESS_STACK in LO.
  unfold ProgC.fuzz_oneC, HarnessC.fuzz_one, Client.CLIENT_PRE, Client.STATE_SIZE. cbn [alloc_all].
  apply implMC_lift_bind_assoc.
  set (PO := POST). rewrite <- (Z_to_bv_bv_unsigned sp). subst PO.
  apply implMC_from_evt.
  eapply (u2_seg1_evt usp U1 _ D n lo m0 F fc); [lia| lia| lia| lia| lia| exact ST| exact MI|].
  intros M1 MU WM MI1 UF ZC.
  pose proof (MID_entry M1 errv HEAP BY AUX ST ER MI MU WM MI1 UF) as H1.
  destruct (md_err _ _ _ H1) as [errv1 ER1].
  eapply implMC_lift_bind.
  { unfold rmalloc_stmt in MALLOC.
    eapply MALLOC with (lo := lo) (B := AB) (LB := [] ++ LB) (n := 7176) (errv := errv1);
      rewrite ?(unsigned_lit (usp - 272)) by lia.
    - exact (md_heap _ _ _ H1).
    - exact (md_aux _ _ _ H1).
    - lia.
    - apply (MID_stk_below _ _ _ _ H1). lia.
    - exact CEIL.
    - unfold RMALLOC_STACK. lia.
    - exact ER1.
    - exact (md_mi _ _ _ H1).
    - exact TP.
    - reflexivity.
    - lia. }
  cbv beta. intros r s' ms' PO.
  destruct PO as (w0 & w1 & w2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR & FAE & SOE & RES).
  rewrite ?(unsigned_lit (usp - 272)) in ST' by lia. rewrite ?(unsigned_lit (usp - 272)) in HPR by lia.
  cbn [app] in HPR.
  pose proof (za_cells_heap _ _ M1 m' HPR ltac:(lia) ZC) as ZC'.
  rewrite ret_pc_even by (first [lia| reflexivity]).
  destruct r as [pp|].
  -
    destruct RES as (A & junk & -> & BR & HEAP' & BLK & _).
    pose proof (rw_cells_wr_at _ _ _ _ 7176 BLK ltac:(cbn [cells_size csize]; lia)) as WRA.
    assert (H' : MID [(pp, A, OL.S7_INFL_N)] s' m').
    { apply (MID_heap [] [(pp, A, OL.S7_INFL_N)] LB st0 s' M1 m' (usp - 272) H1); cbn [app];
        [exact HPR| intros b Hb; exact Hb| intros b [<-|[]]; right; exact WRA
        | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
    apply implMC_liftretb.
    change ((length [pp] <? length [7176%Z])%nat) with false. cbv iota.
    apply (L_za s' m' pp A _ _ _ _ _ _ _ _ _ _ _ _ _ _ H' ZC').
  -
    destruct RES as (-> & HEAP').
    assert (H' : MID [] s' m').
    { apply (MID_heap [] [] LB st0 s' M1 m' (usp - 272) H1); cbn [app];
        [exact HPR| intros b Hb; exact Hb| intros b []
        | lia| exact HEAP'| exact MI'| exact ST'| exists errv'; exact ERR'| exact AUX'| exact SOE]. }
    apply implMC_liftretb.
    change ((length (@nil bptr) <? length [7176%Z])%nat) with true. cbv iota.
    apply implMC_lift. unfold HarnessC.fuzz_without. cbn [free_all]. apply implM_retb.
    eapply implM_evt with (P := fun ms' => exists y10 y13 : word,
        ms' = MS (mkR (Z_to_bv 64 OL.S7_HARN_RA) (Z_to_bv 64 (usp - 80)) gp tp w0 w1 w2 (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 (usp - 16)) y10 b1 b2 y13 b4 b5 b6 b7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                 F (Z_to_bv 64 OL.S7_HARN_RA) fc None m' (seg_rom psegs)).
    + eapply (u2_seg_null_evt usp U1 _ D m' F fc ra s0 s1 s2 s3 s4 s5); [exact (md_uf _ _ _ H')| exact ZC'|].
      intros y10 y13. exists y10, y13. reflexivity.
    + intros ms' (y10 & y13 & ->).
      apply (L_ret s' m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H').
Qed.

End CALL.

Theorem fuzz_one_bridge :
  (forall fx : OP.FPState, @OL.zlib_u2_contract_S7 fx) -> rmalloc_stmt -> rfree_stmt -> fuzz_one_stmt.
Proof.
  intros C7 MALLOC FREE. unfold fuzz_one_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB D payload AB lo errv
         HEAP BY FP RC D16 D0 DT PL GOT SE0 AUX SPAB STK CEIL LO ERR MI FRM TP SP16 -> -> RAE SP47 PB.
  eapply (fuzz_one_call C7 MALLOC FREE); eassumption.
Qed.
End CANSEC1.

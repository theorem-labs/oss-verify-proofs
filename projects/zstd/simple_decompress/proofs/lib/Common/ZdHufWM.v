(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun WStr STRW_tac FseWalkKit FseWalkMem ZdSeqBuildW ZdWalkKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma upd_bytes_map2 : forall (f : Z -> byte) (l : list Z) (i : nat) a b, (i + 2 <= length l)%nat ->
  upd_bytes (map f l) i [f a; f b] = map f (upd_nat (i + 1) b (upd_nat i a l)).
Proof.
  intros f l i. revert l. induction i as [|i IH]; intros l a b H.
  - destruct l as [|x [|y t]]; cbn [length] in H; try lia. reflexivity.
  - destruct l as [|x t]; cbn [length] in H; [lia|].
    change (upd_bytes (map f (x :: t)) (S i) [f a; f b]) with (f x :: upd_bytes (map f t) i [f a; f b]).
    rewrite IH by lia. reflexivity.
Qed.

Section Mem.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma u8arr_sh : forall m A (buf : list Z) i x v,
  u8arr segs m A (map (Z_to_bv 8) buf) -> 0 <= i -> i + 2 <= Z.of_nat (length buf) -> x mod 2^16 = v mod 2^16 ->
  u8arr segs (write_to_mem m (wa (A + i)) (le2 (Z_to_bv 64 x))) A
        (map (Z_to_bv 8) (Zupd (i + 1) ((v / 256) mod 256) (Zupd i (v mod 256) buf))).
Proof.
  intros m A buf i x v ARR Hi Hl E.
  pose proof (u8arr_writen segs m A _ i (le2 (Z_to_bv 64 x)) ARR Hi ltac:(rewrite length_map, length_le2; lia)) as H.
  rewrite (le2_Z x v E) in H |- *. unfold zle2 in H |- *. cbn [map] in H |- *.
  rewrite upd_bytes_map2 in H by lia. unfold Zupd. replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma u8_znth : forall m A (buf : list Z) i a,
  u8arr segs m A (map (Z_to_bv 8) buf) -> 0 <= i < Z.of_nat (length buf) -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (Znth i buf)].
Proof.
  intros m A buf i a ARR Hi ->. eapply (u8arr_read segs m A _ i); [exact ARR| | lia | reflexivity].
  apply nth_error_map_Znth. exact Hi.
Qed.
Lemma u8ro_znth : forall m A (buf : list Z) i a,
  bytes_at segs m A (map (Z_to_bv 8) buf) -> 0 <= i < Z.of_nat (length buf) -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (Znth i buf)].
Proof.
  intros m A buf i a B Hi ->. eapply (u8ro_read segs m A _ i); [exact B| | lia | reflexivity].
  apply nth_error_map_Znth. exact Hi.
Qed.
End Mem.

(* [comment removed for export] *)
Ltac u8_sok2 ARR i :=
  lazymatch type of ARR with u8arr ?segs ?mx ?A ?bs =>
    let a := cur_mem_addr in
    pose proof (u8arr_storen_ok segs mx A bs i 2%nat a ARR ltac:(lia) ltac:(rewrite ?length_map, ?Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK
  end.
Ltac u8_store2 ARR i v :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le2 (Z_to_bv 64 ?x))) _) =>
    lazymatch type of ARR with u8arr ?segs mx ?A (map (Z_to_bv 8) ?buf) =>
      let E := addr_expr a in
      let ARR' := fresh "ARR" in
      assert (ARR' : u8arr segs (write_to_mem mx (wa E) (le2 (Z_to_bv 64 x))) A
                       (map (Z_to_bv 8) (Zupd (i + 1) ((v / 256) mod 256) (Zupd i (v mod 256) buf))));
      [ replace (wa E) with (wa (A + i)) by (unfold wa; f_equal; lia);
        apply (u8arr_sh segs mx A buf i x v ARR); [ lia | rewrite ?Zupd_length; lia | ]
      | clear ARR; store_done; rename ARR' into ARR ]
    end
  end.

(* [comment removed for export] *)
Lemma raw_byte_rd : forall segs m A (bs : list byte) i a,
  bytes_at segs m A bs -> 0 <= i < Z.of_nat (length bs) -> a = wa (A + i) ->
  ov_read_bytes segs m a 1 = Some [nth (Z.to_nat i) bs (Z_to_bv 8 0)].
Proof.
  intros segs m A bs i a B Hi ->. rewrite (bytes_at_read segs m A bs i 1 B) by lia. f_equal.
  rewrite <- (firstn_skipn (Z.to_nat i) bs) at 2. rewrite app_nth2 by (rewrite firstn_length; lia).
  rewrite firstn_length. replace (Z.to_nat i - Nat.min (Z.to_nat i) (length bs))%nat with 0%nat by lia.
  destruct (skipn (Z.to_nat i) bs) as [|b t] eqn:E; [|reflexivity].
  exfalso. pose proof (skipn_length (Z.to_nat i) bs) as L. rewrite E in L. cbn [length] in L. lia.
Qed.

(* [comment removed for export] *)
Ltac lbyte SRCB :=
  lazymatch type of SRCB with bytes_at ?segs ?mx ?A ?bs =>
    let a := cur_mem_addr in
    let E := addr_expr a in
    let RD := fresh "RDB" in
    pose proof (raw_byte_rd segs mx A bs (E - A) a SRCB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
    zstep; cbv beta; clear RD
  end.

(* [comment removed for export] *)
Ltac forget_reg r :=
  let v := reg_val r in
  let x := fresh "w" in
  generalize v; intro x.

(* [comment removed for export] *)
Lemma u8arr_store_forget : forall segs m A bs a xs,
  u8arr segs m A bs -> A <= a -> a + Z.of_nat (length xs) <= A + Z.of_nat (length bs) ->
  exists bs', u8arr segs (write_to_mem m (wa a) xs) A bs' /\ length bs' = length bs.
Proof.
  intros segs m A bs a xs [Hb Hw] H1 H2. pose proof Hb as (B0 & B1 & _).
  exists (upd_bytes bs (Z.to_nat (a - A)) xs).
  assert (L : length (upd_bytes bs (Z.to_nat (a - A)) xs) = length bs) by (apply upd_bytes_length; lia).
  split; [|exact L]. split.
  - pose proof (bytes_at_write_inside segs m A bs (a - A) xs Hb ltac:(lia) ltac:(lia)) as X.
    replace (A + (a - A)) with a in X by lia. exact X.
  - rewrite L. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
Ltac outst OUT LEN :=
  lazymatch type of OUT with u8arr ?segs ?mx ?A ?bs =>
    let a := cur_mem_addr in
    let E := addr_expr a in
    let SOK := fresh "SOK" in
    pose proof (u8arr_storen_ok segs mx A bs (E - A) 1%nat a OUT ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mx ?a2 ?xs) _) =>
      let bs' := fresh "out" in let OUT' := fresh "OUT" in let LEN' := fresh "LEN" in
      destruct (u8arr_store_forget segs mx A bs E xs OUT ltac:(lia) ltac:(simpl_sizes; lia)) as (bs' & OUT' & LEN');
      rewrite <- LEN' in LEN;
      clear OUT; store_done; rename OUT' into OUT; clear LEN'
    end
  end.

(* [comment removed for export] *)
Lemma hle4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 4) with 4294967296 in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma hcb4_as_c4 : forall segs m A pre j post,
  rw_cells segs m A (pre ++ CB 4 j :: post) -> exists w, rw_cells segs m A (pre ++ C4 w :: post).
Proof.
  intros segs m A pre j post H. exists (le_bytes_to_word j).
  pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [WF1 [WFJ WF2]]. cbn in WFJ.
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact WF1|]. split; [exact I| exact WF2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite hle4_of_bytes by exact WFJ. reflexivity.
Qed.

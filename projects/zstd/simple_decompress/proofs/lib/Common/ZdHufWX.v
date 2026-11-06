(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun WStr STRW_tac FseWalkKit FseWalkMem ZdSeqBuildW ZdWalkKit ZdCellKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma firstn4_skipn : forall {X} (d : X) (l : list X) (i : nat), (i + 4 <= length l)%nat ->
  firstn 4 (skipn i l) = [nth i l d; nth (i + 1) l d; nth (i + 2) l d; nth (i + 3) l d].
Proof.
  intros X d l i. revert l. induction i as [|i IH]; intros l H.
  - destruct l as [|a [|b [|c [|e t]]]]; cbn [length] in H; try lia. reflexivity.
  - destruct l as [|a t]; cbn [length] in H; [lia|]. cbn [skipn]. rewrite (IH t) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition d4 (sv nb : Z) : Z := Z.lor (sv ≪ 8 mod 18446744073709551616) nb * 281479271743489.

Lemma d4_bytes : forall sv nb, 0 <= sv < 256 -> 0 <= nb < 256 ->
  0 <= d4 sv nb < 18446744073709551616 /\
  d4 sv nb mod 256 = nb /\ (d4 sv nb ≫ 8) mod 256 = sv /\ (d4 sv nb ≫ 16) mod 256 = nb /\ (d4 sv nb ≫ 24) mod 256 = sv /\
  (d4 sv nb ≫ 32) mod 256 = nb /\ (d4 sv nb ≫ 40) mod 256 = sv /\ (d4 sv nb ≫ 48) mod 256 = nb /\ (d4 sv nb ≫ 56) mod 256 = sv.
Proof.
  set (chk := fun sv nb => let D := d4 sv nb in
     (0 <=? D) && (D <? 18446744073709551616) && (D mod 256 =? nb) && ((D ≫ 8) mod 256 =? sv) && ((D ≫ 16) mod 256 =? nb) && ((D ≫ 24) mod 256 =? sv)
     && ((D ≫ 32) mod 256 =? nb) && ((D ≫ 40) mod 256 =? sv) && ((D ≫ 48) mod 256 =? nb) && ((D ≫ 56) mod 256 =? sv)).
  assert (B : forallb (fun sv => forallb (fun nb => chk sv nb) (ZdSeqTable.zseq 256 0)) (ZdSeqTable.zseq 256 0) = true) by (vm_compute; reflexivity).
  intros sv nb Hs Hn. rewrite forallb_forall in B. specialize (B sv ltac:(apply ZdSeqBuildThm.zseq_In_iff; lia)).
  rewrite forallb_forall in B. specialize (B nb ltac:(apply ZdSeqBuildThm.zseq_In_iff; lia)). unfold chk in B. cbv zeta in B.
  repeat (apply andb_prop in B; destruct B as [B ?]).
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
  apply Z.leb_le in B. match goal with H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
  repeat split; assumption.
Qed.

Lemma u32s_zeros : forall k : nat, u32s (map (Z_to_bv 64) (repeat 0 k)) = repeat (Z_to_bv 8 0) (4 * k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat map u32s]. rewrite IH.
  replace (4 * S k)%nat with (4 + 4 * k)%nat by lia. reflexivity.
Qed.

Section Mem.
Variable segs : list Segment.

Lemma u32arr_of_u32s : forall m A ws, u8arr segs m A (u32s ws) -> u32arr segs m A ws.
Proof.
  intros m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length in Hw.
  replace (4 * Z.of_nat (length ws)) with (Z.of_nat (4 * length ws)) by lia. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u8_znth4 : forall m A (buf : list Z) i a,
  bytes_at segs m A (map (Z_to_bv 8) buf) -> Forall (fun c => 0 <= c < 256) buf -> 0 <= i -> i + 4 <= Z.of_nat (length buf) -> a = wa (A + i) ->
  ov_read_bytes segs m a 4 =
    Some (le4 (Z_to_bv 64 (Znth i buf + 256 * Znth (i + 1) buf + 65536 * Znth (i + 2) buf + 16777216 * Znth (i + 3) buf))).
Proof.
  intros m A buf i a ARR BY Hi Hl ->.
  rewrite (bytes_at_read segs m A _ i 4 ARR Hi) by (rewrite length_map; lia). f_equal.
  rewrite (firstn4_skipn (Z_to_bv 8 0)) by (rewrite length_map; lia).
  pose proof (Forall_Znth _ buf i BY ltac:(lia)) as B0. pose proof (Forall_Znth _ buf (i + 1) BY ltac:(lia)) as B1.
  pose proof (Forall_Znth _ buf (i + 2) BY ltac:(lia)) as B2. pose proof (Forall_Znth _ buf (i + 3) BY ltac:(lia)) as B3. cbv beta in *.
  set (v := Znth i buf + 256 * Znth (i + 1) buf + 65536 * Znth (i + 2) buf + 16777216 * Znth (i + 3) buf).
  rewrite (le4_Z v v eq_refl). unfold zle4. cbn [map].
  change (Z_to_bv 8 0) with (Z_to_bv 8 0). 
  assert (N : forall k, 0 <= k -> k < Z.of_nat (length buf) -> nth (Z.to_nat k) (map (Z_to_bv 8) buf) (Z_to_bv 8 0) = Z_to_bv 8 (Znth k buf)).
  { intros k Hk Hk2. unfold Znth. change (Z_to_bv 8 0) with ((Z_to_bv 8) 0). rewrite map_nth. reflexivity. }
  replace (Z.to_nat i + 1)%nat with (Z.to_nat (i + 1)) by lia. replace (Z.to_nat i + 2)%nat with (Z.to_nat (i + 2)) by lia.
  replace (Z.to_nat i + 3)%nat with (Z.to_nat (i + 3)) by lia.
  rewrite !N by lia.
  assert (E0 : v mod 256 = Znth i buf) by (unfold v; Z.div_mod_to_equations; lia).
  assert (E1 : (v / 256) mod 256 = Znth (i + 1) buf) by (unfold v; Z.div_mod_to_equations; lia).
  assert (E2 : (v / 65536) mod 256 = Znth (i + 2) buf) by (unfold v; Z.div_mod_to_equations; lia).
  assert (E3 : (v / 16777216) mod 256 = Znth (i + 3) buf) by (unfold v; Z.div_mod_to_equations; lia).
  rewrite E0, E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma words_of_unsigned : forall ws : list word, map (Z_to_bv 64) (map bv_unsigned ws) = ws.
Proof. induction ws as [|w t IH]; [reflexivity|]. cbn [map]. rewrite IH, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma u32arr_of_stk : forall m A (k : nat), stk segs m A (A + 4 * Z.of_nat k) -> 0 <= A ->
  exists l : list Z, u32arr segs m A (map (Z_to_bv 64) l) /\ length l = k.
Proof.
  intros m A k ST HA.
  destruct (stk_open segs m A (A + 4 * Z.of_nat k) A (4 * k)%nat ST ltac:(lia) ltac:(lia)) as (bs & C & _ & _).
  assert (BL : length bs = (4 * k)%nat) by (destruct C as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
  apply u8arr_of_rw_cells in C.
  destruct (u32arr_of_u8arr segs m A bs k C BL) as (ws & WL & _ & ARR).
  exists (map bv_unsigned ws). split; [rewrite words_of_unsigned; exact ARR | rewrite length_map; exact WL].
Qed.
End Mem.

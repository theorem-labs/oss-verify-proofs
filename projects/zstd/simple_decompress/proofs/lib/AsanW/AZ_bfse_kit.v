(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
Import ListNotations. Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Zupd_app_l : forall i v (a b : list Z), 0 <= i < zlen a -> Zupd i v (a ++ b) = Zupd i v a ++ b.
Proof.
  intros i v a b Hi. unfold Zupd. remember (Z.to_nat i) as n. assert (Hn : (n < length a)%nat) by lia. clear Heqn Hi.
  revert n Hn. induction a as [|x t IH]; intros [|n] Hn; cbn [length] in Hn; try lia; cbn; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.
Lemma Zupd_app_r : forall i v (a b : list Z), zlen a <= i -> Zupd i v (a ++ b) = a ++ Zupd (i - zlen a) v b.
Proof.
  intros i v a b Hi. unfold Zupd. replace (Z.to_nat i) with (length a + Z.to_nat (i - zlen a))%nat by lia.
  generalize (Z.to_nat (i - zlen a)). clear. intros n. induction a as [|x t IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma sqb_len : forall cells, zlen (flat_map seqsym_bytes cells) = 8 * zlen cells.
Proof. induction cells as [|c l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, seqsym_bytes_length. cbn [length] in *. lia. Qed.

(* [comment removed for export] *)
Lemma sqb_Zupd_cell : forall pre (mid : list Z) post u i v, length pre = Z.to_nat u -> length mid = 8%nat -> 0 <= u -> 8 * u <= i < 8 * u + 8 ->
  Zupd i v (flat_map seqsym_bytes pre ++ mid ++ flat_map seqsym_bytes post)
  = flat_map seqsym_bytes pre ++ Zupd (i - 8 * u) v mid ++ flat_map seqsym_bytes post.
Proof.
  intros pre mid post u i v L LM Hu Hi. pose proof (sqb_len pre) as LP.
  rewrite Zupd_app_r by lia. rewrite Zupd_app_l by lia.
  f_equal. f_equal. f_equal. lia.
Qed.
Ltac sqb_cell_rw pre post u :=
  rewrite (sqb_Zupd_cell pre _ post u); [| assumption | rewrite ?Zupd_length; reflexivity | lia | lia].

(* [comment removed for export] *)
Lemma sqb_set_cell : forall (g : list Z -> list Z) cells u c',
  0 <= u < zlen cells ->
  (forall pre post, length pre = Z.to_nat u ->
     g (flat_map seqsym_bytes pre ++ seqsym_bytes (cell_nth cells u) ++ flat_map seqsym_bytes post)
     = flat_map seqsym_bytes pre ++ seqsym_bytes c' ++ flat_map seqsym_bytes post) ->
  g (flat_map seqsym_bytes cells) = flat_map seqsym_bytes (set_cell u c' cells).
Proof.
  intros g cells u c0 Hu Hg.
  destruct (cells_split cells u ltac:(unfold FseNCount.Zlength; lia)) as (pre & post & EC & L).
  remember (cell_nth cells u) as cu eqn:Ecu in *. clear Ecu. subst cells.
  rewrite (set_cell_split pre _ post c0 u L ltac:(lia)).
  rewrite !flat_map_app. cbn [flat_map]. apply Hg. exact L.
Qed.

(* [comment removed for export] *)
Lemma sqb_base4 : forall cells u x i0 i1 i2 i3, 0 <= u < zlen cells ->
  i0 = 8 * u + 4 -> i1 = 8 * u + 4 + 1 -> i2 = 8 * u + 4 + 2 -> i3 = 8 * u + 4 + 3 ->
  Zupd i3 ((x / 16777216) mod 256) (Zupd i2 ((x / 65536) mod 256) (Zupd i1 ((x / 256) mod 256) (Zupd i0 (x mod 256)
    (flat_map seqsym_bytes cells))))
  = flat_map seqsym_bytes (set_base u x cells).
Proof.
  intros cells u x i0 i1 i2 i3 Hu -> -> -> ->.
  rewrite (set_base_as_set_cell cells u x) by (unfold FseNCount.Zlength; lia).
  apply (sqb_set_cell (fun l => Zupd (8 * u + 4 + 3) ((x / 16777216) mod 256) (Zupd (8 * u + 4 + 2) ((x / 65536) mod 256)
                         (Zupd (8 * u + 4 + 1) ((x / 256) mod 256) (Zupd (8 * u + 4) (x mod 256) l))))); [exact Hu|].
  intros pre post L. do 4 sqb_cell_rw pre post u.
  replace (8 * u + 4 - 8 * u) with 4 by lia. replace (8 * u + 4 + 1 - 8 * u) with 5 by lia.
  replace (8 * u + 4 + 2 - 8 * u) with 6 by lia. replace (8 * u + 4 + 3 - 8 * u) with 7 by lia.
  destruct (cell_nth cells u) as [nx ad nb bs]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sqb_cell8 : forall cells u nx ad nb bs i0 i1 i2 i3 i4 i5 i6 i7, 0 <= u < zlen cells -> 0 <= ad < 256 -> 0 <= nb < 256 ->
  i0 = 8 * u -> i1 = 8 * u + 1 -> i2 = 8 * u + 2 -> i3 = 8 * u + 3 ->
  i4 = 8 * u + 4 -> i5 = 8 * u + 4 + 1 -> i6 = 8 * u + 4 + 2 -> i7 = 8 * u + 4 + 3 ->
  Zupd i7 ((bs / 16777216) mod 256) (Zupd i6 ((bs / 65536) mod 256) (Zupd i5 ((bs / 256) mod 256) (Zupd i4 (bs mod 256)
    (Zupd i2 (ad mod 256) (Zupd i1 ((nx / 256) mod 256) (Zupd i0 (nx mod 256) (Zupd i3 (nb mod 256) (flat_map seqsym_bytes cells))))))))
  = flat_map seqsym_bytes (set_cell u (mkSS nx ad nb bs) cells).
Proof.
  intros cells u nx ad nb bs i0 i1 i2 i3 i4 i5 i6 i7 Hu Had Hnb -> -> -> -> -> -> -> ->.
  apply (sqb_set_cell (fun l =>
    Zupd (8 * u + 4 + 3) ((bs / 16777216) mod 256) (Zupd (8 * u + 4 + 2) ((bs / 65536) mod 256) (Zupd (8 * u + 4 + 1) ((bs / 256) mod 256) (Zupd (8 * u + 4) (bs mod 256)
    (Zupd (8 * u + 2) (ad mod 256) (Zupd (8 * u + 1) ((nx / 256) mod 256) (Zupd (8 * u) (nx mod 256) (Zupd (8 * u + 3) (nb mod 256) l))))))))); [exact Hu|].
  intros pre post L. do 8 sqb_cell_rw pre post u.
  replace (8 * u + 4 - 8 * u) with 4 by lia. replace (8 * u + 4 + 1 - 8 * u) with 5 by lia.
  replace (8 * u + 4 + 2 - 8 * u) with 6 by lia. replace (8 * u + 4 + 3 - 8 * u) with 7 by lia.
  replace (8 * u - 8 * u) with 0 by lia. replace (8 * u + 1 - 8 * u) with 1 by lia.
  replace (8 * u + 2 - 8 * u) with 2 by lia. replace (8 * u + 3 - 8 * u) with 3 by lia.
  rewrite (Z.mod_small ad 256), (Z.mod_small nb 256) by lia.
  destruct (cell_nth cells u) as [nx0 ad0 nb0 bs0]. reflexivity.
Qed.

Lemma set_base_length2 : forall i v cells, zlen (set_base i v cells) = zlen cells.
Proof. intros. rewrite set_base_length. reflexivity. Qed.
Lemma set_cell_length2 : forall i c cells, zlen (set_cell i c cells) = zlen cells.
Proof. intros. rewrite set_cell_length. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RD.
Variable segs : list Segment.

Lemma bytes_le_to_Z_le4 : forall x, bytes_le_to_Z (le4 (Z_to_bv 64 x)) = x mod 4294967296.
Proof.
  intros x. unfold le4. rewrite bytes_le_to_Z_to_le_bytes by (apply bv_unsigned_in_range).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (4294967296 * 4294967296).
  change (2 ^ (8 * Z.of_nat 4)) with 4294967296. rewrite Z.rem_mul_r by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma rdval_sqb_base : forall m A cells u az,
  u8arr segs m A (map (Z_to_bv 8) (flat_map seqsym_bytes cells)) -> az = A + (8 * u + 4) -> 0 <= u < zlen cells ->
  rdval segs m (wa az) 4 false = Z_to_bv 64 (ss_base (cell_nth cells u) mod 4294967296).
Proof.
  intros m A cells u az [HB _] -> Hu. pose proof (sqb_len cells) as L.
  rewrite (rdval_bytes_at segs m A _ (8 * u + 4) 4 false HB); [| lia| rewrite length_map; lia].
  f_equal. change (map (Z_to_bv 8) (flat_map seqsym_bytes cells)) with (cellsB cells).
  rewrite (cellsB_read_base cells u) by (unfold FseNCount.Zlength; lia).
  unfold extz. apply bytes_le_to_Z_le4.
Qed.

(* [comment removed for export] *)
Lemma rdval_u32s : forall m A (l : list Z) i az sx,
  bytes_at segs m A (u32s (map (Z_to_bv 64) l)) -> az = A + 4 * i -> 0 <= i < zlen l -> 0 <= Znth i l < 2147483648 ->
  rdval segs m (wa az) 4 sx = Z_to_bv 64 (Znth i l).
Proof.
  intros m A l i az sx HB -> Hi Hv.
  rewrite (rdval_bytes_at segs m A _ (4 * i) 4 sx HB); [| lia| rewrite u32s_length, length_map; lia].
  destruct (nth_error_split (map (Z_to_bv 64) l) (Z.to_nat i) _ (nth_error_map_Znth (Z_to_bv 64) l i Hi)) as (pre & post & E & Hlen).
  rewrite E. rewrite u32s_app. cbn [u32s].
  replace (Z.to_nat (4 * i)) with (length (u32s pre)) by (rewrite u32s_length; lia).
  rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [app]. rewrite skipn_O.
  rewrite firstn_app, length_le4. replace (4 - 4)%nat with 0%nat by reflexivity. rewrite firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite length_le4; lia).
  rewrite bytes_le_to_Z_le4. rewrite (Z.mod_small (Znth i l) 4294967296) by lia.
  destruct sx; [|reflexivity]. unfold extz. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N (8 * N.of_nat 4)) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma rdval_u8s : forall m A (l : list Z) i az,
  bytes_at segs m A (map (Z_to_bv 8) l) -> az = A + i -> 0 <= i < zlen l -> Forall (fun v : Z => 0 <= v < 256) l ->
  rdval segs m (wa az) 1 false = Z_to_bv 64 (Znth i l).
Proof.
  intros m A l i az HB -> Hi HF.
  rewrite (rdval_bytes_at segs m A _ i 1 false HB) by (rewrite ?length_map; lia).
  f_equal.
  rewrite (firstn1_skipn (Z.to_nat i) (map (Z_to_bv 8) l) (Z_to_bv 8 (Znth i l))) by (apply nth_error_map_Znth; lia).
  unfold extz. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small.
  pose proof (Forall_Znth _ l i HF Hi) as B. cbv beta in B. change (2 ^ Z.of_N 8) with 256. lia.
Qed.
End RD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxk_sbase7 B1 B2 B3 B4 B5 B6 B7 t :=
  lazymatch t with
  | context [B1] => B1 | context [B2] => B2 | context [B3] => B3 | context [B4] => B4 | context [B5] => B5
  | context [B6] => B6 | context [B7] => B7 | _ => t
  end.
Ltac kx_sep_unhide7 B1 B2 B3 B4 B5 B6 B7 :=
  match goal with
  | |- context [?a + _ <= ?b \/ _] =>
      let X := kxk_sbase7 B1 B2 B3 B4 B5 B6 B7 a in let Y := kxk_sbase7 B1 B2 B3 B4 B5 B6 B7 b in unhide_related X Y
  end.
Ltac kx_lia_sep7 B1 B2 B3 B4 B5 B6 B7 :=
  first [ lia | kx_sep_unhide7 B1 B2 B3 B4 B5 B6 B7; lia | kx_bv_ranges; lia ].

(* [comment removed for export] *)
Lemma kind_lens : forall k, zlen (kind_base k) = kind_max k + 1 /\ zlen (kind_bits k) = kind_max k + 1.
Proof. intros [| |]; split; reflexivity. Qed.
Lemma kind_bits_bytes : forall k, Forall (fun v : Z => 0 <= v < 256) (kind_bits k).
Proof. intros [| |]; cbn; repeat constructor; lia. Qed.
Lemma kind_base_small : forall k, Forall (fun v : Z => 0 <= v < 2147483648) (kind_base k).
Proof. intros [| |]; cbn; repeat constructor; lia. Qed.

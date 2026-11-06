(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Mem Cells.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxQuery.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition region_export (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) : Prop :=
  forall i, 0 <= i < to_Z (rg_size rg) -> exists b, mrd segs m (wa (B + i)) = Some b /\ kb_ok rho (rg_kb segs rg i) b
                                           /\ (rg_wr rg = true -> wview segs m (wa (B + i)) <> None).   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma region_export_of_ok (rho : valuation) (t : int) (rg : region) (m : word -> option byte) :
  region_ok segs rho t rg m -> region_export m rho (rbase rho t rg) rg.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & H) i Hi. destruct (H i Hi) as (b & E & K & W). exists b. auto. Qed.

Lemma region_export_lit (rho : valuation) (M : HxMem.mem) (m : word -> option byte) (t : int) (rg : region) (a : int) :
  Rmem segs rho M m -> mget M t = Some rg -> rg_abs rg = Some a -> region_export m rho (to_Z a) rg.
Proof.
  intros [HR _] Hg Ha. pose proof (region_export_of_ok rho t rg m (HR t rg Hg)) as X. unfold rbase in X. rewrite Ha in X. exact X.
Qed.

Lemma region_export_blk (rho : valuation) (M : HxMem.mem) (m : word -> option byte) (t : int) (rg : region) :
  Rmem segs rho M m -> mget M t = Some rg -> rg_abs rg = None -> region_export m rho (rho t) rg.
Proof.
  intros [HR _] Hg Ha. pose proof (region_export_of_ok rho t rg m (HR t rg Hg)) as X. unfold rbase in X. rewrite Ha in X. exact X.
Qed.

(* [comment removed for export] *)
Definition kbs_of (rg : region) (off : Z) (n : nat) : list kb := map (fun j => rg_kb segs rg (off + Z.of_nat j)) (seq 0 n).

Lemma kbs_of_length rg off n : length (kbs_of rg off n) = n.
Proof. unfold kbs_of. rewrite length_map, length_seq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma export_bytes (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (n : nat) :
  region_export m rho B rg -> 0 <= B -> 0 <= off -> off + Z.of_nat n <= to_Z (rg_size rg) -> B + to_Z (rg_size rg) <= 2 ^ 64 ->
  exists bs, Forall2 (kb_ok rho) (kbs_of rg off n) bs /\ bytes_at segs m (B + off) bs.
Proof.
  intros HE HB Hoff Hfit Htop. revert off Hoff Hfit. induction n as [|n IH]; intros off Hoff Hfit.
  - exists []. split; [constructor|]. split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
  - cbn [Z.of_nat] in Hfit. destruct (IH (off + 1) ltac:(lia) ltac:(lia)) as (bs & HF & (_ & _ & Hb)).
    destruct (HE off ltac:(lia)) as (b & Eb & Kb & _).
    exists (b :: bs). split.
    + unfold kbs_of. cbn [seq map]. rewrite <- seq_shift, map_map. constructor; [rewrite Z.add_0_r; exact Kb|].
      unfold kbs_of in HF. erewrite map_ext; [exact HF|]. intros j. cbn. f_equal. lia.
    + pose proof (Forall2_length HF) as Hl. rewrite kbs_of_length in Hl.
      split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i].
      * cbn [nth_error]. rewrite Nat2Z.inj_0, Z.add_0_r. exact Eb.
      * cbn [nth_error]. cbn [length] in Hi. rewrite <- (Hb i ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma export_Z (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (n : nat) (z : Z) :
  region_export m rho B rg -> 0 <= B -> 0 <= off -> off + Z.of_nat n <= to_Z (rg_size rg) -> B + to_Z (rg_size rg) <= 2 ^ 64 ->
  kbs_of rg off n = kbs_Z n z -> 0 <= z ->
  bytes_at segs m (B + off) (Z_to_le_bytes n z).
Proof.
  intros HE HB Ho Hf Ht Ek Hz. destruct (export_bytes m rho B rg off n HE HB Ho Hf Ht) as (bs & HF & Hb).
  rewrite Ek in HF. rewrite <- (kbs_Z_bytes rho n z bs Hz HF). exact Hb.
Qed.

(* [comment removed for export] *)
Lemma export_ptr (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (t : int) :
  region_export m rho B rg -> 0 <= B -> 0 <= off -> off + 8 <= to_Z (rg_size rg) -> B + to_Z (rg_size rg) <= 2 ^ 64 ->
  kbs_of rg off 8 = kbs_ptr t -> 0 <= rho t < 2 ^ 64 ->
  bytes_at segs m (B + off) (le8 (Z_to_bv 64 (rho t))).
Proof.
  intros HE HB Ho Hf Ht Ek Hr. destruct (export_bytes m rho B rg off 8 HE HB Ho ltac:(cbn [Z.of_nat]; lia) Ht) as (bs & HF & Hb).
  rewrite Ek in HF. rewrite <- (kbs_ptr_bytes rho t bs Hr HF). exact Hb.
Qed.

(* [comment removed for export] *)
Lemma export_run (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (zs : list Z) :
  region_export m rho B rg -> 0 <= B -> 0 <= off -> off + Z.of_nat (length zs) <= to_Z (rg_size rg) -> B + to_Z (rg_size rg) <= 2 ^ 64 ->
  kbs_of rg off (length zs) = kbs_bytes zs ->
  bytes_at segs m (B + off) (map (Z_to_bv 8) zs).
Proof.
  intros HE HB Ho Hf Ht Ek. destruct (export_bytes m rho B rg off (length zs) HE HB Ho Hf Ht) as (bs & HF & Hb).
  rewrite Ek in HF. rewrite <- (kbs_bytes_bytes rho zs bs HF). exact Hb.
Qed.

(* [comment removed for export] *)
Lemma export_wr (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off n : Z) :
  region_export m rho B rg -> rg_wr rg = true -> 0 <= B -> 0 <= off -> 0 <= n -> off + n <= to_Z (rg_size rg) -> B + to_Z (rg_size rg) <= 2 ^ 64 ->
  wr_at segs m (B + off) n.
Proof.
  intros HE Hw HB Ho Hn Hf Ht. split; [lia|]. split; [lia|]. intros i Hi. destruct (HE (off + i) ltac:(lia)) as (b & _ & _ & W).
  replace (B + off + i) with (B + (off + i)) by ring. exact (W Hw).
Qed.

(* [comment removed for export] *)
Lemma bs_ptr (rho : valuation) (tag : int) (bs : list byte) : 0 < rho tag -> rho tag < 2 ^ 63 ->
  Forall2 (kb_ok rho) (kbs_ptr tag) bs -> bs = cells_bytes [C8 (wz (rho tag))].
Proof. intros H0 H1 H. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (kbs_ptr_bytes rho tag bs); [lia | exact H]. Qed.

Lemma bs_lit8 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  Forall2 (kb_ok rho) (kbs_Z 8 z) bs -> bs = cells_bytes [C8 (wz z)].
Proof.
  intros Hz H. cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite (kbs_Z_bytes rho 8 z bs ltac:(lia) H).
  unfold le8, word_to_le_bytes, wz. rewrite Z_to_bv_unsigned, bv_wrap_small by exact Hz. reflexivity.
Qed.

Lemma bs_lit4 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  Forall2 (kb_ok rho) (kbs_Z 4 z) bs -> bs = le4 (wz z).
Proof. intros Hz H. rewrite (kbs_Z_bytes rho 4 z bs ltac:(lia) H). unfold le4, wz. rewrite Z_to_bv_unsigned, bv_wrap_small by exact Hz. reflexivity. Qed.

Lemma bs_lit1 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z ->
  Forall2 (kb_ok rho) (kbs_Z 1 z) bs -> bs = [Z_to_bv 8 z].
Proof. intros Hz H. rewrite (kbs_Z_bytes rho 1 z bs Hz H). reflexivity. Qed.

Lemma F2_nil (rho : valuation) (bs : list byte) : Forall2 (kb_ok rho) [] bs -> bs = cells_bytes [].
Proof. intros H. inversion H. reflexivity. Qed.

Lemma F2_ptr (rho : valuation) (tag : int) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 < rho tag -> rho tag < 2 ^ 63 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_ptr tag ++ ks) bs -> bs = cells_bytes (C8 (wz (rho tag)) :: cs).
Proof.
  intros H0 H1 Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. pose proof (bs_ptr rho tag b1 H0 H1 F1) as E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma F2_lit8 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 8 z ++ ks) bs -> bs = cells_bytes (C8 (wz z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. pose proof (bs_lit8 rho z b1 Hz F1) as E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma F2_lit4 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 4 z ++ ks) bs -> bs = cells_bytes (C4 (wz z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. exact (bs_lit4 rho z b1 Hz F1).
Qed.

Lemma F2_lit1 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 1 z ++ ks) bs -> bs = cells_bytes (C1 (Z_to_bv 8 z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. exact (bs_lit1 rho z b1 Hz F1).
Qed.

Lemma F2_bytes (rho : valuation) (zs : list Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) :
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_bytes zs ++ ks) bs -> bs = cells_bytes (CB (length zs) (map (Z_to_bv 8) zs) :: cs).
Proof.
  intros Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. exact (kbs_bytes_bytes rho zs b1 F1).
Qed.

(* [comment removed for export] *)
Lemma export_cells (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (cs : list Cells.cell) (ks : list kb) :
  region_export m rho B rg -> 0 <= B -> 0 <= off -> off + Z.of_nat (cells_size cs) <= to_Z (rg_size rg) -> B + to_Z (rg_size rg) <= 2 ^ 64 ->
  cells_wf cs -> kbs_of rg off (cells_size cs) = ks -> (forall bs, Forall2 (kb_ok rho) ks bs -> bs = cells_bytes cs) ->
  cells_at segs m (B + off) cs.
Proof.
  intros HE HB Ho Hf Ht Hwf Ek Hbs. destruct (export_bytes m rho B rg off (cells_size cs) HE HB Ho Hf Ht) as (bs & HF & Hb).
  rewrite Ek in HF. rewrite (Hbs bs HF) in Hb. split; [exact Hwf | exact Hb].
Qed.

Lemma export_cells_rw (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (cs : list Cells.cell) (ks : list kb) :
  region_export m rho B rg -> rg_wr rg = true -> 0 <= B -> 0 <= off -> off + Z.of_nat (cells_size cs) <= to_Z (rg_size rg) -> B + to_Z (rg_size rg) <= 2 ^ 64 ->
  cells_wf cs -> kbs_of rg off (cells_size cs) = ks -> (forall bs, Forall2 (kb_ok rho) ks bs -> bs = cells_bytes cs) ->
  cells_at segs m (B + off) cs /\ wr_at segs m (B + off) (Z.of_nat (cells_size cs)).
Proof.
  intros HE Hw HB Ho Hf Ht Hwf Ek Hbs. split; [exact (export_cells m rho B rg off cs ks HE HB Ho Hf Ht Hwf Ek Hbs)|].
  exact (export_wr m rho B rg off _ HE Hw HB Ho (Nat2Z.is_nonneg _) Hf Ht).
Qed.

End WithSegs.

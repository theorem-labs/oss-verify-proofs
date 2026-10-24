(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Image Tac.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import DietLia2 ZBridge TacDiet2.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Storrsf Stor5a9.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive wr_within (m0 : word -> option byte) (lo hi : Z) : (word -> option byte) -> Prop :=
| ww_nil : wr_within m0 lo hi m0
| ww_cons : forall m a bs, wr_within m0 lo hi m -> (lo <= a)%Z -> (a + Z.of_nat (length bs) <= hi)%Z ->
    wr_within m0 lo hi (write_to_mem m (wa a) bs).

(* [comment removed for export] *)

Lemma ww_frame : forall (P : (word -> option byte) -> Prop) m0 lo hi,
  (forall m a bs, (lo <= a)%Z -> (a + Z.of_nat (length bs) <= hi)%Z -> P m -> P (write_to_mem m (wa a) bs)) ->
  forall mp, wr_within m0 lo hi mp -> P m0 -> P mp.
Proof. intros P m0 lo hi Hst mp Hw H0. induction Hw; auto. Qed.

(* [comment removed for export] *)
Inductive wr_list (m0 : word -> option byte) (A : Z) : list (Z * Z) -> (word -> option byte) -> Prop :=
| wl_nil : wr_list m0 A [] m0
| wl_cons : forall ws m k bs, wr_list m0 A ws m ->
    wr_list m0 A ((k, Z.of_nat (length bs)) :: ws) (write_to_mem m (wa (A + k)) bs).

(* [comment removed for export] *)
Definition sb_pend (m0 mp : word -> option byte) (A : Z) (ws : list (Z * Z)) : Prop := wr_list m0 A ws mp.

Lemma sb_pend_first : forall m0 A k c,
  cell_wf c -> sb_pend m0 (write_to_mem m0 (wa (A + Z.of_nat k)) (cbytes c)) A [(Z.of_nat k, Z.of_nat (csize c))].
Proof.
  intros m0 A k c Hwf. unfold sb_pend. rewrite <- (cbytes_length c Hwf). constructor. constructor.
Qed.
Lemma sb_pend_next : forall m0 mp A ws k c,
  sb_pend m0 mp A ws -> cell_wf c ->
  sb_pend m0 (write_to_mem mp (wa (A + Z.of_nat k)) (cbytes c)) A ((Z.of_nat k, Z.of_nat (csize c)) :: ws).
Proof.
  intros m0 mp A ws k c Hp Hwf. unfold sb_pend in *. rewrite <- (cbytes_length c Hwf). constructor. exact Hp.
Qed.

(* [comment removed for export] *)
Definition all_in (l n : Z) (ws : list (Z * Z)) : bool :=
  forallb (fun p => andb (Z.leb l (fst p)) (Z.leb (fst p + snd p) (l + n))) ws.
Definition sb_hull (m0 mp : word -> option byte) (A l n : Z) : Prop := wr_within m0 (A + l) (A + l + n) mp.
Lemma sb_hull_of_pend : forall m0 mp A ws l n, sb_pend m0 mp A ws -> all_in l n ws = true -> sb_hull m0 mp A l n.
Proof.
  intros m0 mp A ws l n Hp. unfold sb_pend, sb_hull in *. induction Hp as [|ws m k bs Hp IH]; intros Hc; [constructor|].
  cbn [all_in forallb fst snd] in Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2].
  apply Bool.andb_true_iff in H1. destruct H1 as [Ha Hb]. apply Z.leb_le in Ha. apply Z.leb_le in Hb.
  constructor; [exact (IH H2) | lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hull_framed (P : (word -> option byte) -> Prop) (A2 sz : Z) : Prop :=
  forall m a bs, P m -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
    (A2 + sz <= a \/ a + Z.of_nat (length bs) <= A2)%Z -> P (write_to_mem m (wa a) bs).

Lemma ws_h : forall P A2 sz, hull_framed P A2 sz ->
  forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b -> P m0 ->
  (A2 + sz <= A + l \/ A + l + n <= A2)%Z -> P mp.
Proof.
  intros P A2 sz HF m0 mp A l n X b Hp (Ha & Hl & _) H0 Hd.
  apply (ww_frame P m0 _ _) with (2 := Hp); [|exact H0].
  intros m a bs H1 H2 Hm. apply HF; [exact Hm | lia | lia | lia].
Qed.
Lemma ws_lit : forall P A2 sz, hull_framed P A2 sz ->
  forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b -> P m0 ->
  chk_lit b A2 sz = true -> P mp.
Proof.
  intros P A2 sz HF m0 mp A l n X b Hp SC H0 Hc. apply (ws_h P A2 sz HF m0 mp A l n X b Hp SC H0).
  destruct SC as (_ & _ & Hb). eapply chk_lit_sound; eauto.
Qed.
Lemma ws_sb : forall P c sz X, hull_framed P (X + c) sz ->
  forall m0 mp A l n b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b -> P m0 ->
  chk_sb b c sz = true -> P mp.
Proof.
  intros P c sz X HF m0 mp A l n b Hp SC H0 Hc. apply (ws_h P (X + c) sz HF m0 mp A l n X b Hp SC H0).
  destruct SC as (_ & _ & Hb). eapply chk_sb_sound; eauto.
Qed.
Lemma ws_sb0 : forall P sz X, hull_framed P X sz ->
  forall m0 mp A l n b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b -> P m0 ->
  chk_sb b 0 sz = true -> P mp.
Proof.
  intros P sz X HF m0 mp A l n b Hp SC H0 Hc. apply (ws_h P X sz HF m0 mp A l n X b Hp SC H0).
  destruct SC as (_ & _ & Hb). eapply chk_sb0_sound; eauto.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma rw_cells_hf : forall A2 cs, hull_framed (fun m => rw_cells segs m A2 cs) A2 (Z.of_nat (cells_size cs)).
Proof. intros A2 cs m a bs H H1 H2 H3. apply rw_cells_frame; assumption. Qed.
Lemma ro_cells_hf : forall A2 cs, hull_framed (fun m => ro_cells segs m A2 cs) A2 (Z.of_nat (cells_size cs)).
Proof. intros A2 cs m a bs H H1 H2 H3. apply ro_cells_frame; assumption. Qed.
Lemma bytes_at_hf : forall A2 cs, hull_framed (fun m => bytes_at segs m A2 cs) A2 (Z.of_nat (length cs)).
Proof. intros A2 cs m a bs H H1 H2 H3. apply bytes_at_write_other; assumption. Qed.
Lemma u8arr_hf : forall A2 xs, hull_framed (fun m => u8arr segs m A2 xs) A2 (Z.of_nat (length xs)).
Proof. intros A2 xs m a bs H H1 H2 H3. apply u8arr_frame; assumption. Qed.
Lemma u32arr_hf : forall A2 ws, hull_framed (fun m => u32arr segs m A2 ws) A2 (4 * Z.of_nat (length ws)).
Proof. intros A2 ws m a bs H H1 H2 H3. apply u32arr_frame; assumption. Qed.
Lemma u64arr_hf : forall A2 ws, hull_framed (fun m => u64arr segs m A2 ws) A2 (8 * Z.of_nat (length ws)).
Proof. intros A2 ws m a bs H H1 H2 H3. apply u64arr_frame; assumption. Qed.
Lemma u8ro_hf : forall A2 xs, hull_framed (fun m => u8ro segs m A2 xs) A2 (Z.of_nat (length xs)).
Proof. intros A2 xs m a bs H H1 H2 H3. apply u8ro_frame; assumption. Qed.

(* [comment removed for export] *)
Lemma rw_cells_ws_lit : forall m0 mp A l n X b A2 cs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  rw_cells segs m0 A2 cs -> chk_lit b A2 (Z.of_nat (cells_size cs)) = true -> rw_cells segs mp A2 cs.
Proof. intros m0 mp A l n X b A2 cs Hp SC. exact (ws_lit _ _ _ (rw_cells_hf A2 cs) m0 mp A l n X b Hp SC). Qed.
Lemma rw_cells_ws_sb : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall c cs, rw_cells segs m0 (X + c) cs -> chk_sb b c (Z.of_nat (cells_size cs)) = true -> rw_cells segs mp (X + c) cs.
Proof. intros m0 mp A l n X b Hp SC c cs. exact (ws_sb _ _ _ _ (rw_cells_hf (X + c) cs) m0 mp A l n b Hp SC). Qed.
Lemma rw_cells_ws_sb0 : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall cs, rw_cells segs m0 X cs -> chk_sb b 0 (Z.of_nat (cells_size cs)) = true -> rw_cells segs mp X cs.
Proof. intros m0 mp A l n X b Hp SC cs. exact (ws_sb0 _ _ _ (rw_cells_hf X cs) m0 mp A l n b Hp SC). Qed.
Lemma rw_cells_ws_h : forall m0 mp A l n X b A2 cs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  rw_cells segs m0 A2 cs -> (A2 + Z.of_nat (cells_size cs) <= A + l \/ A + l + n <= A2)%Z -> rw_cells segs mp A2 cs.
Proof. intros m0 mp A l n X b A2 cs Hp SC. exact (ws_h _ _ _ (rw_cells_hf A2 cs) m0 mp A l n X b Hp SC). Qed.

Lemma ro_cells_ws_lit : forall m0 mp A l n X b A2 cs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  ro_cells segs m0 A2 cs -> chk_lit b A2 (Z.of_nat (cells_size cs)) = true -> ro_cells segs mp A2 cs.
Proof. intros m0 mp A l n X b A2 cs Hp SC. exact (ws_lit _ _ _ (ro_cells_hf A2 cs) m0 mp A l n X b Hp SC). Qed.
Lemma ro_cells_ws_sb : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall c cs, ro_cells segs m0 (X + c) cs -> chk_sb b c (Z.of_nat (cells_size cs)) = true -> ro_cells segs mp (X + c) cs.
Proof. intros m0 mp A l n X b Hp SC c cs. exact (ws_sb _ _ _ _ (ro_cells_hf (X + c) cs) m0 mp A l n b Hp SC). Qed.
Lemma ro_cells_ws_sb0 : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall cs, ro_cells segs m0 X cs -> chk_sb b 0 (Z.of_nat (cells_size cs)) = true -> ro_cells segs mp X cs.
Proof. intros m0 mp A l n X b Hp SC cs. exact (ws_sb0 _ _ _ (ro_cells_hf X cs) m0 mp A l n b Hp SC). Qed.
Lemma ro_cells_ws_h : forall m0 mp A l n X b A2 cs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  ro_cells segs m0 A2 cs -> (A2 + Z.of_nat (cells_size cs) <= A + l \/ A + l + n <= A2)%Z -> ro_cells segs mp A2 cs.
Proof. intros m0 mp A l n X b A2 cs Hp SC. exact (ws_h _ _ _ (ro_cells_hf A2 cs) m0 mp A l n X b Hp SC). Qed.

Lemma bytes_at_ws_lit : forall m0 mp A l n X b A2 cs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  bytes_at segs m0 A2 cs -> chk_lit b A2 (Z.of_nat (length cs)) = true -> bytes_at segs mp A2 cs.
Proof. intros m0 mp A l n X b A2 cs Hp SC. exact (ws_lit _ _ _ (bytes_at_hf A2 cs) m0 mp A l n X b Hp SC). Qed.
Lemma bytes_at_ws_sb : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall c cs, bytes_at segs m0 (X + c) cs -> chk_sb b c (Z.of_nat (length cs)) = true -> bytes_at segs mp (X + c) cs.
Proof. intros m0 mp A l n X b Hp SC c cs. exact (ws_sb _ _ _ _ (bytes_at_hf (X + c) cs) m0 mp A l n b Hp SC). Qed.
Lemma bytes_at_ws_sb0 : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall cs, bytes_at segs m0 X cs -> chk_sb b 0 (Z.of_nat (length cs)) = true -> bytes_at segs mp X cs.
Proof. intros m0 mp A l n X b Hp SC cs. exact (ws_sb0 _ _ _ (bytes_at_hf X cs) m0 mp A l n b Hp SC). Qed.
Lemma bytes_at_ws_h : forall m0 mp A l n X b A2 cs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  bytes_at segs m0 A2 cs -> (A2 + Z.of_nat (length cs) <= A + l \/ A + l + n <= A2)%Z -> bytes_at segs mp A2 cs.
Proof. intros m0 mp A l n X b A2 cs Hp SC. exact (ws_h _ _ _ (bytes_at_hf A2 cs) m0 mp A l n X b Hp SC). Qed.

Lemma u8arr_ws_lit : forall m0 mp A l n X b A2 xs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  u8arr segs m0 A2 xs -> chk_lit b A2 (Z.of_nat (length xs)) = true -> u8arr segs mp A2 xs.
Proof. intros m0 mp A l n X b A2 xs Hp SC. exact (ws_lit _ _ _ (u8arr_hf A2 xs) m0 mp A l n X b Hp SC). Qed.
Lemma u8arr_ws_sb : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall c xs, u8arr segs m0 (X + c) xs -> chk_sb b c (Z.of_nat (length xs)) = true -> u8arr segs mp (X + c) xs.
Proof. intros m0 mp A l n X b Hp SC c xs. exact (ws_sb _ _ _ _ (u8arr_hf (X + c) xs) m0 mp A l n b Hp SC). Qed.
Lemma u8arr_ws_sb0 : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall xs, u8arr segs m0 X xs -> chk_sb b 0 (Z.of_nat (length xs)) = true -> u8arr segs mp X xs.
Proof. intros m0 mp A l n X b Hp SC xs. exact (ws_sb0 _ _ _ (u8arr_hf X xs) m0 mp A l n b Hp SC). Qed.
Lemma u8arr_ws_h : forall m0 mp A l n X b A2 xs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  u8arr segs m0 A2 xs -> (A2 + Z.of_nat (length xs) <= A + l \/ A + l + n <= A2)%Z -> u8arr segs mp A2 xs.
Proof. intros m0 mp A l n X b A2 xs Hp SC. exact (ws_h _ _ _ (u8arr_hf A2 xs) m0 mp A l n X b Hp SC). Qed.

Lemma u32arr_ws_lit : forall m0 mp A l n X b A2 ws, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  u32arr segs m0 A2 ws -> chk_lit b A2 (4 * Z.of_nat (length ws)) = true -> u32arr segs mp A2 ws.
Proof. intros m0 mp A l n X b A2 ws Hp SC. exact (ws_lit _ _ _ (u32arr_hf A2 ws) m0 mp A l n X b Hp SC). Qed.
Lemma u32arr_ws_sb : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall c ws, u32arr segs m0 (X + c) ws -> chk_sb b c (4 * Z.of_nat (length ws)) = true -> u32arr segs mp (X + c) ws.
Proof. intros m0 mp A l n X b Hp SC c ws. exact (ws_sb _ _ _ _ (u32arr_hf (X + c) ws) m0 mp A l n b Hp SC). Qed.
Lemma u32arr_ws_sb0 : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall ws, u32arr segs m0 X ws -> chk_sb b 0 (4 * Z.of_nat (length ws)) = true -> u32arr segs mp X ws.
Proof. intros m0 mp A l n X b Hp SC ws. exact (ws_sb0 _ _ _ (u32arr_hf X ws) m0 mp A l n b Hp SC). Qed.
Lemma u32arr_ws_h : forall m0 mp A l n X b A2 ws, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  u32arr segs m0 A2 ws -> (A2 + 4 * Z.of_nat (length ws) <= A + l \/ A + l + n <= A2)%Z -> u32arr segs mp A2 ws.
Proof. intros m0 mp A l n X b A2 ws Hp SC. exact (ws_h _ _ _ (u32arr_hf A2 ws) m0 mp A l n X b Hp SC). Qed.

Lemma u64arr_ws_lit : forall m0 mp A l n X b A2 ws, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  u64arr segs m0 A2 ws -> chk_lit b A2 (8 * Z.of_nat (length ws)) = true -> u64arr segs mp A2 ws.
Proof. intros m0 mp A l n X b A2 ws Hp SC. exact (ws_lit _ _ _ (u64arr_hf A2 ws) m0 mp A l n X b Hp SC). Qed.
Lemma u64arr_ws_sb : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall c ws, u64arr segs m0 (X + c) ws -> chk_sb b c (8 * Z.of_nat (length ws)) = true -> u64arr segs mp (X + c) ws.
Proof. intros m0 mp A l n X b Hp SC c ws. exact (ws_sb _ _ _ _ (u64arr_hf (X + c) ws) m0 mp A l n b Hp SC). Qed.
Lemma u64arr_ws_sb0 : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall ws, u64arr segs m0 X ws -> chk_sb b 0 (8 * Z.of_nat (length ws)) = true -> u64arr segs mp X ws.
Proof. intros m0 mp A l n X b Hp SC ws. exact (ws_sb0 _ _ _ (u64arr_hf X ws) m0 mp A l n b Hp SC). Qed.
Lemma u64arr_ws_h : forall m0 mp A l n X b A2 ws, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  u64arr segs m0 A2 ws -> (A2 + 8 * Z.of_nat (length ws) <= A + l \/ A + l + n <= A2)%Z -> u64arr segs mp A2 ws.
Proof. intros m0 mp A l n X b A2 ws Hp SC. exact (ws_h _ _ _ (u64arr_hf A2 ws) m0 mp A l n X b Hp SC). Qed.

Lemma u8ro_ws_lit : forall m0 mp A l n X b A2 xs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  u8ro segs m0 A2 xs -> chk_lit b A2 (Z.of_nat (length xs)) = true -> u8ro segs mp A2 xs.
Proof. intros m0 mp A l n X b A2 xs Hp SC. exact (ws_lit _ _ _ (u8ro_hf A2 xs) m0 mp A l n X b Hp SC). Qed.
Lemma u8ro_ws_sb : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall c xs, u8ro segs m0 (X + c) xs -> chk_sb b c (Z.of_nat (length xs)) = true -> u8ro segs mp (X + c) xs.
Proof. intros m0 mp A l n X b Hp SC c xs. exact (ws_sb _ _ _ _ (u8ro_hf (X + c) xs) m0 mp A l n b Hp SC). Qed.
Lemma u8ro_ws_sb0 : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  forall xs, u8ro segs m0 X xs -> chk_sb b 0 (Z.of_nat (length xs)) = true -> u8ro segs mp X xs.
Proof. intros m0 mp A l n X b Hp SC xs. exact (ws_sb0 _ _ _ (u8ro_hf X xs) m0 mp A l n b Hp SC). Qed.
Lemma u8ro_ws_h : forall m0 mp A l n X b A2 xs, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  u8ro segs m0 A2 xs -> (A2 + Z.of_nat (length xs) <= A + l \/ A + l + n <= A2)%Z -> u8ro segs mp A2 xs.
Proof. intros m0 mp A l n X b A2 xs Hp SC. exact (ws_h _ _ _ (u8ro_hf A2 xs) m0 mp A l n X b Hp SC). Qed.


Lemma wr_at_ws : forall m0 mp A l n A2 n2, sb_hull m0 mp A l n -> wr_at segs m0 A2 n2 -> wr_at segs mp A2 n2.
Proof.
  intros m0 mp A l n A2 n2 Hp H0. apply (ww_frame (fun m => wr_at segs m A2 n2) m0 _ _) with (2 := Hp); [|exact H0].
  intros m a bs _ _ Hm. apply wr_at_write. exact Hm.
Qed.
Lemma wmono_ws : forall mq m0 mp A l n, sb_hull m0 mp A l n -> wmono segs mq m0 -> wmono segs mq mp.
Proof.
  intros mq m0 mp A l n Hp H0. apply (ww_frame (fun m => wmono segs mq m) m0 _ _) with (2 := Hp); [|exact H0].
  intros m a bs _ _ Hm. apply wmono_write. exact Hm.
Qed.
Lemma stk_ws : forall m0 mp A l n X b lo hi, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  stk segs m0 lo hi -> stk segs mp lo hi.
Proof.
  intros m0 mp A l n X b lo hi Hp (Ha & Hl & _) H0.
  apply (ww_frame (fun m => stk segs m lo hi) m0 _ _) with (2 := Hp); [|exact H0].
  intros m a bs H1 H2 Hm. apply stk_write; [exact Hm | lia | lia].
Qed.
End WithSegs.

Lemma inside_sub : forall W lo n a k, inside W lo n -> (lo <= a)%Z -> (a + k <= lo + n)%Z -> inside W a k.
Proof.
  induction W as [|[wl wh] W IH]; cbn; intros lo n a k Hin H1 H2; [exact Hin|].
  destruct Hin as [Hin|Hin]; [left; lia | right; eapply IH; eauto].
Qed.
Lemma munch_ws_h : forall W mq m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  munch W mq m0 -> inside W (A + l) n -> munch W mq mp.
Proof.
  intros W mq m0 mp A l n X b Hp (Ha & Hl & _) H0 Hin.
  apply (ww_frame (fun m => munch W mq m) m0 _ _) with (2 := Hp); [|exact H0].
  intros m a bs H1 H2 Hm. apply munch_write; [exact Hm | lia | lia |]. eapply inside_sub; eauto.
Qed.
Lemma munch_ws_wd : forall W mq m0 mp A l n X b D, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  wds_ok X W D -> munch W mq m0 -> chk_inside D b n = true -> munch W mq mp.
Proof.
  intros W mq m0 mp A l n X b D Hp SC HD H0 Hc. apply (munch_ws_h W mq m0 mp A l n X b Hp SC H0).
  destruct SC as (_ & _ & Hb). eapply chk_inside_sound; eauto.
Qed.

(* [comment removed for export] *)
Lemma munch_of_hull_sc : forall m0 mp A l n X b, sb_hull m0 mp A l n -> store_ctx (A + l) n X b ->
  munch [((A + l)%Z, (A + l + n)%Z)] m0 mp.
Proof.
  intros m0 mp A l n X b Hp SC. apply (munch_ws_h [((A + l)%Z, (A + l + n)%Z)] m0 m0 mp A l n X b Hp SC (munch_refl _ m0)).
  cbn [inside]. left. lia.
Qed.

(* [comment removed for export] *)
Fixpoint inside_all (W : list ivl) (A : Z) (ws : list (Z * Z)) : Prop :=
  match ws with
  | [] => True
  | (k, sz) :: ws' => inside W (A + k) sz /\ inside_all W A ws'
  end.
Lemma munch_ws_list : forall W mq m0 mp A ws l n X b, sb_pend m0 mp A ws -> store_ctx (A + l) n X b ->
  all_in l n ws = true -> munch W mq m0 -> inside_all W A ws -> munch W mq mp.
Proof.
  intros W mq m0 mp A ws l n X b Hp (Ha & Hl & _). unfold sb_pend in Hp.
  induction Hp as [|ws m k bs Hp IH]; intros Hc H0 Hin; [exact H0|].
  cbn [all_in forallb fst snd] in Hc. apply Bool.andb_true_iff in Hc. destruct Hc as [H1 H2].
  apply Bool.andb_true_iff in H1. destruct H1 as [Hk1 Hk2]. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
  cbn [inside_all] in Hin. destruct Hin as [Hi1 Hi2].
  apply munch_write; [exact (IH H2 H0 Hi2) | lia | lia | exact Hi1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sb_store_ctx_of_facts full a n Ha Hl hullprover k :=
  let Hd := fresh "dHd" in let HPQ := fresh "dHPQ" in let SC := fresh "dSC" in
  sb_split a ltac:(fun X d pfd =>
    try (assert (Hd : dfact (a = (X + d)%Z)) by exact pfd);
    let av := match constr:(tt) with _ => let v := zval a in constr:(@Some Z v) | _ => constr:(@None Z) end in
    lazymatch full with
    | true =>
        lazymatch av with
        | Some _ => idtac
        | None => diet_hull ltac:(fun hv =>
                    lazymatch hv with
                    | Some (?smin, ?emax) => try (assert (HPQ : dfact (a + n <= smin \/ emax <= a)%Z) by (unfold dfact; hullprover))
                    | None => idtac
                    end)
        end
    | false => idtac
    end;
    let l := lazymatch goal with _ : dfact (a = (X + d)%Z) |- _ => constr:(@Some Z d) | _ => constr:(@None Z) end in
    let h := lazymatch l with
             | Some _ => let e := eval vm_compute in (d + n)%Z in constr:(@Some Z e)
             | _ => constr:(@None Z)
             end in
    let U := lazymatch av with
             | Some ?v => let e := eval vm_compute in (v + n)%Z in constr:(@Some Z e)
             | None => constr:(@None Z)
             end in
    let PQ := lazymatch goal with
              | _ : dfact (a + n <= ?smin \/ ?emax <= a)%Z |- _ => constr:(@Some (Z * Z) (smin, emax))
              | _ => constr:(@None (Z * Z))
              end in
    let b := constr:(IB l h av U PQ) in
    assert (SC : store_ctx a n X b);
    [ apply store_ctx_intro; [ exact Ha | exact Hl | ];
      cbv beta iota delta [ib_ok opt_holds ib_l ib_h ib_L ib_U ib_PQ];
      split; [ | split; [ | split; [ | split ] ] ];
      [ (* [comment removed for export] *) first [ exact I | lazymatch goal with |- ?G => lazymatch goal with Hf : dfact G |- _ => exact Hf end end ]
      | (* [comment removed for export] *) first [ exact I
                      | lazymatch goal with Hf : dfact (a = (X + d)%Z) |- _ =>
                          exact (@eq_trans Z (a + n)%Z (X + d + n)%Z (X + (d + n))%Z
                                 (@f_equal Z Z (fun t => (t + n)%Z) a (X + d)%Z Hf)
                                 (@eq_sym Z (X + (d + n))%Z (X + d + n)%Z (Z.add_assoc X d n)))
                        end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- (?v <= _)%Z => exact (Z.le_refl v) end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- (_ <= ?v)%Z => exact (Z.le_refl v) end ]
      | (* [comment removed for export] *) first [ exact I | lazymatch goal with |- ?G => lazymatch goal with Hf : dfact G |- _ => exact Hf end end ] ]
    | k SC X b;
      try clear SC; try clear HPQ; try clear Hd ]).

Ltac sb_store_ctx_pose full a n side k kfail :=
  let Ha := fresh "dHa" in let Hl := fresh "dHl" in
  tryif (first [ lazymatch a with
                 | (?A0 + ?k)%Z =>
                     lazymatch goal with
                     | HB : (0 <= A0 /\ A0 + ?sz <= 2 ^ 64)%Z |- _ =>
                         pose proof (store_lb_of_bound A0 sz k n HB (@eq_refl bool true)) as Ha
                     end
                 end
               | assert (Ha : (0 <= a)%Z) by (diet_lia side) ])
  then (
   tryif (first [ lazymatch a with
                  | (?A0 + ?k)%Z =>
                      lazymatch goal with
                      | HB : (0 <= A0 /\ A0 + ?sz <= 2 ^ 64)%Z |- _ =>
                          pose proof (store_ub_of_bound A0 sz k n HB (@eq_refl bool true)) as Hl
                      end
                  end
                | assert (Hl : (a + n <= 2^64)%Z) by (diet_side_store side ltac:(simpl_sizes; slia)) ])
   then (sb_store_ctx_of_facts full a n Ha Hl ltac:(diet_side_store side ltac:(simpl_sizes; slia)) k; clear Ha Hl)
   else (clear Ha; kfail))
  else kfail.

(* [comment removed for export] *)
Ltac sb_tr_lit H lem b A2 sz :=
  is_Zlit A2;
  let s := size_lit sz in
  lazymatch eval vm_compute in (chk_lit b A2 s) with true => idtac end;
  apply lem in H; [ | exact (@eq_refl bool true) ]; diet_note_lit.
Ltac sb_tr_sb H lem lem0 b X A2 sz :=
  let s := size_lit sz in
  lazymatch A2 with
  | Z.add X ?c => is_Zlit c; lazymatch eval vm_compute in (chk_sb b c s) with true => idtac end;
                 apply lem in H; [ | exact (@eq_refl bool true) ]; diet_note_sb
  | X => lazymatch eval vm_compute in (chk_sb b 0%Z s) with true => idtac end;
         apply lem0 in H; [ | exact (@eq_refl bool true) ]; diet_note_sb
  end.

(* [comment removed for export] *)
Ltac sb_transport_chunks segs m0 mp A l n PEND SC X b side :=
  repeat match goal with
  | H : bytes_at segs m0 ?A2 ?bs2 |- _ =>
      first [ sb_tr_lit H (bytes_at_ws_lit segs m0 mp A l n X b A2 bs2 PEND SC) b A2 constr:(Z.of_nat (@length byte bs2))
            | sb_tr_sb H (bytes_at_ws_sb segs m0 mp A l n X b PEND SC) (bytes_at_ws_sb0 segs m0 mp A l n X b PEND SC) b X A2 constr:(Z.of_nat (@length byte bs2))
            | apply (bytes_at_ws_h segs m0 mp A l n X b A2 bs2 PEND SC) in H; [ | diet_side_store side ltac:(simpl_sizes; simpl_arr_sizes; slia) ]; diet_note_h
            | diet_note_drop; idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m0 ?A2 ?n2 |- _ => apply (wr_at_ws segs m0 mp A l n A2 n2 PEND) in H
  | H : rw_cells segs m0 ?A2 ?cs2 |- _ =>
      first [ sb_tr_lit H (rw_cells_ws_lit segs m0 mp A l n X b A2 cs2 PEND SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | sb_tr_sb H (rw_cells_ws_sb segs m0 mp A l n X b PEND SC) (rw_cells_ws_sb0 segs m0 mp A l n X b PEND SC) b X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (rw_cells_ws_h segs m0 mp A l n X b A2 cs2 PEND SC) in H; [ | diet_side_store side ltac:(simpl_sizes; slia) ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m0 ?A2 ?cs2 |- _ =>
      first [ sb_tr_lit H (ro_cells_ws_lit segs m0 mp A l n X b A2 cs2 PEND SC) b A2 constr:(Z.of_nat (cells_size cs2))
            | sb_tr_sb H (ro_cells_ws_sb segs m0 mp A l n X b PEND SC) (ro_cells_ws_sb0 segs m0 mp A l n X b PEND SC) b X A2 constr:(Z.of_nat (cells_size cs2))
            | apply (ro_cells_ws_h segs m0 mp A l n X b A2 cs2 PEND SC) in H; [ | diet_side_store side ltac:(simpl_sizes; slia) ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m0 ?A2 ?xs |- _ =>
      first [ sb_tr_lit H (u8arr_ws_lit segs m0 mp A l n X b A2 xs PEND SC) b A2 constr:(Z.of_nat (@length byte xs))
            | sb_tr_sb H (u8arr_ws_sb segs m0 mp A l n X b PEND SC) (u8arr_ws_sb0 segs m0 mp A l n X b PEND SC) b X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8arr_ws_h segs m0 mp A l n X b A2 xs PEND SC) in H; [ | diet_side_store side ltac:(simpl_sizes; simpl_arr_sizes; slia) ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m0 ?A2 ?ws |- _ =>
      first [ sb_tr_lit H (u32arr_ws_lit segs m0 mp A l n X b A2 ws PEND SC) b A2 constr:((4 * Z.of_nat (@length word ws))%Z)
            | sb_tr_sb H (u32arr_ws_sb segs m0 mp A l n X b PEND SC) (u32arr_ws_sb0 segs m0 mp A l n X b PEND SC) b X A2 constr:((4 * Z.of_nat (@length word ws))%Z)
            | apply (u32arr_ws_h segs m0 mp A l n X b A2 ws PEND SC) in H; [ | diet_side_store side ltac:(simpl_sizes; simpl_arr_sizes; slia) ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m0 ?A2 ?ws |- _ =>
      first [ sb_tr_lit H (u64arr_ws_lit segs m0 mp A l n X b A2 ws PEND SC) b A2 constr:((8 * Z.of_nat (@length word ws))%Z)
            | sb_tr_sb H (u64arr_ws_sb segs m0 mp A l n X b PEND SC) (u64arr_ws_sb0 segs m0 mp A l n X b PEND SC) b X A2 constr:((8 * Z.of_nat (@length word ws))%Z)
            | apply (u64arr_ws_h segs m0 mp A l n X b A2 ws PEND SC) in H; [ | diet_side_store side ltac:(simpl_sizes; simpl_arr_sizes; slia) ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m0 ?A2 ?xs |- _ =>
      first [ sb_tr_lit H (u8ro_ws_lit segs m0 mp A l n X b A2 xs PEND SC) b A2 constr:(Z.of_nat (@length byte xs))
            | sb_tr_sb H (u8ro_ws_sb segs m0 mp A l n X b PEND SC) (u8ro_ws_sb0 segs m0 mp A l n X b PEND SC) b X A2 constr:(Z.of_nat (@length byte xs))
            | apply (u8ro_ws_h segs m0 mp A l n X b A2 xs PEND SC) in H; [ | diet_side_store side ltac:(simpl_sizes; simpl_arr_sizes; slia) ]; diet_note_h
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac sb_footprint segs m0 mp A l n ws PENDL PEND SC X b side :=
  repeat match goal with
  | MU : munch ?Wq ?mq m0 |- _ =>
      first [ let D := wdesc_of X Wq in
              lazymatch eval vm_compute in (chk_inside D b n) with true => idtac end;
              let WDH := fresh "dWD" in
              assert (WDH : wds_ok X Wq D) by
                (cbv beta iota delta [wds_ok wd_ok opt_holds wd_l wd_h wd_lo wd_hi];
                 repeat match goal with |- _ /\ _ => split end;
                 first [ exact I | reflexivity | symmetry; apply Z.add_0_r ]);
              apply (munch_ws_wd Wq mq m0 mp A l n X b D PEND SC WDH) in MU; [ | exact (@eq_refl bool true) ];
              clear WDH
            | apply (munch_ws_h Wq mq m0 mp A l n X b PEND SC) in MU;
              [ | cbn [inside]; diet_side_store side ltac:(simpl_sizes; slia) ]
            | (* [comment removed for export] *)
              apply (munch_ws_list Wq mq m0 mp A ws l n X b PENDL SC (@eq_refl bool true)) in MU;
              [ | cbn [inside_all inside];
                  repeat match goal with |- _ /\ _ => split | |- True => exact I end;
                  diet_side_store side ltac:(simpl_sizes; slia) ]
            | fail 100 "store run outside the declared footprint:" A ws ]
  | WMo : wmono segs ?mq m0 |- _ => apply (wmono_ws segs mq m0 mp A l n PEND) in WMo
  | STq : stk segs m0 ?loq ?hiq |- _ => apply (stk_ws segs m0 mp A l n X b loq hiq PEND SC) in STq
  end.

Module SbL2.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 hash_string (h0 : int) (s : string) : int :=
    let n := String.length s in
    let rec go (i : int) (h : int) : int :=
      if Int.ge i n then h
      else go (Int.add i 1) (Int.mod (Int.add (Int.mul h 131) (Char.to_int (String.get s i))) 1000000007) in
    go 0 h0.
  Ltac2 hash_constr (h0 : int) (c : constr) : int := hash_string h0 (Message.to_string (Message.of_constr c)).
  Ltac2 is_prop (ty : constr) : bool :=
    match Control.case (fun () => Constr.type ty) with
    | Val v => let (s, _) := v in lazy_match! s with Prop => true | _ => false end
    | Err _ => false
    end.
  Ltac2 mcat (l : message list) : message := List.fold_left Message.concat (Message.of_string "") l.
  Ltac2 trace (tag : string) : unit :=
    Control.enter (fun () =>
      let hs := Control.hyps () in
      let hg := hash_constr 7 (Control.goal ()) in
      let one (h : ident * constr option * constr) : int :=
        let (id, bd, ty) := h in
        let x := hash_constr (hash_string 11 (Ident.to_string id)) ty in
        match bd with Some b => hash_constr x b | None => x end in
      let hv := List.map one hs in
      let ordered := List.fold_left (fun acc x => Int.mod (Int.add (Int.mul acc 1000003) x) 1000000007) 17 hv in
      let summed := List.fold_left (fun acc x => Int.mod (Int.add acc x) 1000000007) 0 hv in
      let props := List.fold_left (fun acc (h : ident * constr option * constr) =>
                      let (_, _, ty) := h in
                      if is_prop ty then Int.mod (Int.add (Int.mul acc 1000003) (one h)) 1000000007 else acc) 19 hs in
      Message.print (mcat [Message.of_string "SBTRACE "; Message.of_string tag; Message.of_string " n="; Message.of_int (List.length hs);
                           Message.of_string " goal="; Message.of_int hg; Message.of_string " set="; Message.of_int summed;
                           Message.of_string " props="; Message.of_int props; Message.of_string " ordered="; Message.of_int ordered])).
  Ltac2 mutable sb_trace : bool := false.
  Ltac2 mutable sb_debug : bool := false.
  Ltac2 trace_if (tag : string) : unit := if sb_trace then trace tag else ().
  (* [comment removed for export] *)
  Ltac2 note (s : string) : unit :=
    if sb_debug then
      Control.enter (fun () =>
        let pcm := lazy_match! goal with
                   | [ |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) ] => Message.of_constr pc
                   | [ |- _ ] => Message.of_string "?"
                   end in
        Message.print (mcat [Message.of_string "SB-PATH "; Message.of_string s; Message.of_string " next-pc="; pcm]))
    else ().
End SbL2.
(* [comment removed for export] *)
Ltac sb_seq_rest prev k cont :=
  lazymatch k with
  | O => cont prev
  | S ?k' => let n := fresh "m" in sb_seq_rest n k' cont
  end.
Ltac sb_finish base cur ws :=
  let k := eval cbv beta iota delta [length] in (@length (Z * Z) ws) in
  let tmp := fresh "sbmem__" in
  rename cur into tmp;
  (* [comment removed for export] *)
  let n1 := fresh "m" in
  try clear base;
  lazymatch k with
  | S ?k' => sb_seq_rest n1 k' ltac:(fun nk => rename tmp into nk)
  end.
Ltac sb_trace_flushed := ltac2:(SbL2.trace_if "FLUSHED").
Ltac sb_trace_single := ltac2:(SbL2.trace_if "SINGLE").
Ltac sb_trace_pending := ltac2:(if SbL2.sb_trace then Message.print (Message.of_string "SBTRACE PENDING") else ()).
Ltac sb_note_start := ltac2:(SbL2.note "run starts").
Ltac sb_note_cont := ltac2:(SbL2.note "run continues").
Ltac sb_note_flush := ltac2:(SbL2.note "flush").
Ltac sb_note_single := ltac2:(SbL2.note "single").

(* [comment removed for export] *)
Ltac sb_hull_of ws k :=
  let l := eval vm_compute in (fold_right (fun (p : Z * Z) acc => Z.min (fst p) acc) (fst (hd (0, 0)%Z ws)) ws) in
  let h := eval vm_compute in (fold_right (fun (p : Z * Z) acc => Z.max (fst p + snd p)%Z acc) 0%Z ws) in
  let n := eval vm_compute in (h - l)%Z in
  k l n.

(* [comment removed for export] *)
Ltac sb_flush_gen extra :=
  lazymatch goal with
  | PENDL : sb_pend ?m0 ?mp ?A ?ws |- evt ?segs _ (MS _ _ _ _ _ ?mp _) =>
      lazymatch goal with
      | H : rw_cells segs mp A ?cs |- _ =>
          sb_note_flush;
          sb_hull_of ws ltac:(fun l n =>
            let PEND := fresh "sbHULL" in
            pose proof (sb_hull_of_pend m0 mp A ws l n PENDL (@eq_refl bool true)) as PEND;
            let HB := fresh "HB" in
            first [ OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.natz_pose_bound segs mp A cs H HB
                  | (let szn := eval cbv beta iota delta [cells_size csize Nat.add] in (cells_size cs) in
                     pose proof (rw_cells_bound segs mp A cs H : (0 <= A /\ A + Z.of_nat szn <= 2 ^ 64)%Z) as HB) ];
            diet_with_side ltac:(fun side side_ns side_dm =>
              sb_store_ctx_pose true (A + l)%Z n side_ns
                ltac:(fun SC X b => idtac; sb_transport_chunks segs m0 mp A l n PEND SC X b side;
                                    sb_footprint segs m0 mp A l n ws PENDL PEND SC X b side_ns;
                                    extra segs m0 mp A l n X b PEND SC)
                ltac:(fail 100 "Stor0fe: no store_ctx for the run" A l n));
            clear HB; clear PEND; clear PENDL;
            sb_finish m0 mp ws)
      end
  end.

Ltac sb_no_extra segs m0 mp A l n X b PEND SC := idtac.
Ltac sb_flush := sb_flush_gen sb_no_extra.
(* [comment removed for export] *)
Ltac sb_sf_extra segs m0 mp A l n X b PEND SC :=
  let MUs := fresh "MUs" in let WMs := fresh "WMs" in
  pose proof (munch_of_hull_sc m0 mp A l n X b PEND SC) as MUs;
  pose proof (wmono_ws segs m0 m0 mp A l n PEND (wmono_refl segs m0)) as WMs;
  OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Storrsf.transport_call_extra segs (@cons ivl ((A + l)%Z, (A + l + n)%Z) (@nil ivl)) m0 mp MUs WMs;
  clear MUs WMs.

(* [comment removed for export] *)
Ltac sb_reg_value R r :=
  let p := eval vm_compute in (bv_key r) in
  eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => w0 end).
Ltac sb_next_in_chunk A cs :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      is_Zlit pc; is_concrete_map R;
      (* [comment removed for export] *)
      lazymatch Q with context [pc] => fail | _ => idtac end;
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
        let d := eval vm_compute in (decode_any w) in
        lazymatch d with
        | Some (Store ?sz ?rs1 _ ?imm, _) =>
            let v := sb_reg_value R rs1 in
            let EB := lazymatch v with
                      | Z_to_bv 64 ?E => E
                      | wa ?E => E
                      | _ => let chk := match v with _ => is_var v end in constr:(bv_unsigned v)
                      end in
            let simm := eval vm_compute in (bv_signed imm) in
            let nb := eval vm_compute in (msize_bytes sz) in
            let szc := eval cbv beta iota delta [cells_size csize Nat.add] in (cells_size cs) in
            sb_split EB ltac:(fun X d pf =>
              sb_split A ltac:(fun XA dA pfA =>
                constr_eq X XA;
                lazymatch eval vm_compute in (let k := (d + simm - dA)%Z in andb (Z.leb 0 k) (Z.leb (k + nb) (Z.of_nat szc))) with
                | true => idtac
                end))
        end
      end
  end.

(* [comment removed for export] *)
Ltac sb_absorb_pending :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          (* [comment removed for export] *)
          let kz := eval vm_compute in (Z.of_nat kn) in
          let nz := eval vm_compute in (Z.of_nat n) in
          lazymatch goal with
          | PEND : sb_pend ?m0 m A ?ws |- _ =>
              let PEND' := fresh "sbPEND" in
              pose proof (sb_pend_next m0 m A ws kn c' PEND I
                          : sb_pend m0 (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A ((kz, nz) :: ws)) as PEND';
              clear PEND;
              let m' := fresh "m" in
              remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
              clear Heqm; try clear m; try rename H' into H
          | _ =>
              let PEND := fresh "sbPEND" in
              pose proof (sb_pend_first m A kn c' I
                          : sb_pend m (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) A ((kz, nz) :: nil)) as PEND;
              let m' := fresh "m" in
              remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
              clear Heqm; try rename H' into H
          end
        end
    end
  end.

(* [comment removed for export] *)
Ltac sb_mem_after_store_gen2 single flush :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      lazymatch goal with
      | PEND : sb_pend _ m A _ |- _ =>
          (* [comment removed for export] *)
          sb_note_cont; sb_absorb_pending;
          lazymatch goal with
          | H : rw_cells segs ?mp A ?cs |- evt _ _ (MS _ _ _ _ _ ?mp _) =>
              tryif sb_next_in_chunk A cs then sb_trace_pending else (flush; sb_trace_flushed)
          end
      | _ =>
          lazymatch goal with
          | H : rw_cells segs m A ?cs0 |- _ =>
              (* [comment removed for export] *)
              tryif sb_next_in_chunk A cs0
              then (sb_note_start; sb_absorb_pending; sb_trace_pending)
              else (single; sb_note_single; sb_trace_single)
          end
      end
  end.

Ltac sb_mem_after_store_gen single := sb_mem_after_store_gen2 single ltac:(idtac; sb_flush).

(* [comment removed for export] *)
Ltac sb_mem_after_store :=
  sb_mem_after_store_gen ltac:(idtac; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store).
(* [comment removed for export] *)
Ltac sb_mem_after_store_plain :=
  sb_mem_after_store_gen ltac:(idtac; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.mem_after_store_orig).
(* [comment removed for export] *)
Ltac sb_mem_after_store_sf :=
  sb_mem_after_store_gen ltac:(idtac; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Storrsf.mem_after_store_fast).

(* [comment removed for export] *)
Ltac sb_mem_after_store_sfx :=
  sb_mem_after_store_gen2 ltac:(idtac; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Storrsf.mem_after_store_fast) ltac:(idtac; sb_flush_gen sb_sf_extra).

(* [comment removed for export] *)
Ltac sb_mem_after_store_sfd :=
  sb_mem_after_store_gen ltac:(idtac; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor5a9.sd_mem_after_store).
Ltac sb_mem_after_store_sfdx :=
  sb_mem_after_store_gen2 ltac:(idtac; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor5a9.sd_mem_after_store) ltac:(idtac; sb_flush_gen sb_sf_extra).

(* [comment removed for export] *)
Ltac sb_mem_after_store_ref := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store; sb_trace_single.
Ltac sb_mem_after_store_plain_ref := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.mem_after_store_orig; sb_trace_single.
Ltac sb_mem_after_store_sf_ref := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Storrsf.mem_after_store_fast; sb_trace_single.
Ltac sb_mem_after_store_sfd_ref := OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor5a9.sd_mem_after_store; sb_trace_single.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition kx_sbytes (E : env) (w : nat) (v : expr) : list byte := word_to_le_bytes w (edenot E v).

Lemma kx_sbytes_length : forall E w v, length (kx_sbytes E w v) = w.
Proof. intros. unfold kx_sbytes, word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

Lemma mem_denot_one : forall E m a w v,
  mem_denot E m [SE a w v] = write_to_mem m (wa (estart E a)) (kx_sbytes E w v).
Proof. reflexivity. Qed.

Lemma mem_denot_cons : forall E m a w v rest,
  mem_denot E m (SE a w v :: rest) = write_to_mem (mem_denot E m rest) (wa (estart E a)) (kx_sbytes E w v).
Proof. reflexivity. Qed.

Lemma mem_denot_app : forall E m l1 l2, mem_denot E m (l1 ++ l2) = mem_denot E (mem_denot E m l2) l1.
Proof. intros E m l1 l2. induction l1 as [|[a w v] l1 IH]; cbn [app mem_denot]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mem_denot_unroll : forall E m l a w v,
  mem_denot E m (l ++ [SE a w v]) = mem_denot E (write_to_mem m (wa (estart E a)) (kx_sbytes E w v)) l.
Proof. intros. rewrite mem_denot_app. reflexivity. Qed.

Lemma log_flat_app : forall E l1 l2, log_flat E (l1 ++ l2) -> log_flat E l1 /\ log_flat E l2.
Proof.
  intros E l1 l2. induction l1 as [|[a w v] l1 IH]; cbn [app log_flat]; intros H; [split; [exact I | exact H]|].
  destruct H as (H1 & H2 & H3). destruct (IH H3) as [IH1 IH2]. split; [split; [exact H1 | split; [exact H2 | exact IH1]] | exact IH2].
Qed.

Lemma log_flat_last : forall E l a w v, log_flat E (l ++ [SE a w v]) ->
  log_flat E l /\ 0 <= estart E a /\ estart E a + Z.of_nat w <= 2^64.
Proof.
  intros E l a w v H. apply log_flat_app in H as [H1 H2]. split; [exact H1|].
  cbn [log_flat] in H2. destruct H2 as (_ & (F1 & F2 & F3 & F4) & _). lia.
Qed.

Section Mem.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cells_store (cs : list cell) (k : nat) (c' : cell) : option (list cell) :=
  if cb_split_ok cs k (csize c') then
    let cs2 := cb_split cs k (csize c') in
    match cell_at cs2 k with
    | Some c => if Nat.eqb (csize c) (csize c') then Some (cell_upd cs2 k c') else None
    | None => None
    end
  else None.

Lemma kx_rw_cells_store : forall m A cs k c' cs',
  rw_cells segs m A cs -> cells_store cs k c' = Some cs' -> cell_wf c' ->
  rw_cells segs (write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) A cs'.
Proof.
  intros m A cs k c' cs' H Hs Hwf. unfold cells_store in Hs.
  destruct (cb_split_ok cs k (csize c')) eqn:Hok; [|discriminate Hs].
  pose proof (rw_cells_cb_split segs m A cs _ k (csize c') H Hok eq_refl) as H2.
  destruct (cell_at (cb_split cs k (csize c')) k) as [c|] eqn:Hc; [|discriminate Hs].
  destruct (Nat.eqb (csize c) (csize c')) eqn:Hsz; [|discriminate Hs]. apply Nat.eqb_eq in Hsz.
  injection Hs as <-. exact (rw_cells_write segs m A _ k c c' H2 Hc (eq_sym Hsz) Hwf).
Qed.

Lemma kx_rw_cells_storeZ : forall m A cs (k : Z) c' cs',
  rw_cells segs m A cs -> cells_store cs (Z.to_nat k) c' = Some cs' -> cell_wf c' -> 0 <= k ->
  rw_cells segs (write_to_mem m (wa (A + k)) (cbytes c')) A cs'.
Proof.
  intros m A cs k c' cs' H Hs Hwf Hk. rewrite <- (Z2Nat.id k Hk) at 1. exact (kx_rw_cells_store m A cs _ c' cs' H Hs Hwf).
Qed.

(* [comment removed for export] *)
Definition kx_cell (w : nat) (v : word) : cell :=
  match w with
  | 8%nat => C8 v
  | 4%nat => C4 v
  | 2%nat => C2 v
  | 1%nat => CB 1 (le1 v)
  | _ => CB w (word_to_le_bytes w v)
  end.
Lemma kx_cell_bytes : forall w v, cbytes (kx_cell w v) = word_to_le_bytes w v.
Proof. intros w v. unfold kx_cell. destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; reflexivity. Qed.
Lemma kx_cell_wf : forall w v, cell_wf (kx_cell w v).
Proof.
  intros w v. unfold kx_cell. destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try exact I;
    cbn [cell_wf]; unfold word_to_le_bytes, le1; apply length_Z_to_le_bytes.
Qed.

Lemma kx_u8arr_store : forall m A bs a xs,
  u8arr segs m A bs -> (A <= a /\ a + Z.of_nat (length xs) <= A + Z.of_nat (length bs)) ->
  exists bs', u8arr segs (write_to_mem m (wa a) xs) A bs' /\ length bs' = length bs.
Proof.
  intros m A bs a xs [Hb Hw] [H1 H2]. pose proof Hb as (B0 & B1 & _).
  exists (upd_bytes bs (Z.to_nat (a - A)) xs).
  assert (L : length (upd_bytes bs (Z.to_nat (a - A)) xs) = length bs) by (apply upd_bytes_length; lia).
  split; [|exact L]. split.
  - pose proof (bytes_at_write_inside segs m A bs (a - A) xs Hb ltac:(lia) ltac:(lia)) as X.
    replace (A + (a - A)) with a in X by lia. exact X.
  - rewrite L. apply wr_at_write. exact Hw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kx_wmono_log : forall E m log, wmono segs m (mem_denot E m log).
Proof.
  intros E m log. induction log as [|[a w v] rest IH]; cbn [mem_denot]; [apply wmono_refl|].
  apply (wmono_write segs m _ (adenot E a) (word_to_le_bytes w (edenot E v)) IH).
Qed.

Lemma kx_wr_at_log : forall E m log A N, wr_at segs m A N -> wr_at segs (mem_denot E m log) A N.
Proof.
  intros E m log A N (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. apply (kx_wmono_log E m log). apply H. exact Hi.
Qed.

Lemma kx_stk_log : forall E m log lo hi, log_flat E log -> stk segs m lo hi -> stk segs (mem_denot E m log) lo hi.
Proof.
  intros E m log lo hi. induction log as [|[a w v] rest IH]; cbn [mem_denot log_flat]; intros Hlf Hs; [exact Hs|].
  destruct Hlf as (_ & (F1 & F2 & F3 & F4) & Hlf).
  apply (stk_write segs _ lo hi (estart E a) (kx_sbytes E w v) (IH Hlf Hs)); [lia | rewrite kx_sbytes_length; lia].
Qed.

Fixpoint log_apart (E : env) (log : list sentry) (A N : Z) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest => (A + N <= estart E a \/ estart E a + Z.of_nat w <= A) /\ log_apart E rest A N
  end.

Lemma kx_bytes_at_log : forall E m log A bs, log_flat E log -> log_apart E log A (Z.of_nat (length bs)) ->
  bytes_at segs m A bs -> bytes_at segs (mem_denot E m log) A bs.
Proof.
  intros E m log A bs. induction log as [|[a w v] rest IH]; cbn [mem_denot log_flat log_apart]; intros Hlf Hap Hb; [exact Hb|].
  destruct Hlf as (_ & (F1 & F2 & F3 & F4) & Hlf). destruct Hap as [Hd Hap].
  apply (bytes_at_write_other segs _ (estart E a) (kx_sbytes E w v) A bs (IH Hlf Hap Hb)); rewrite ?kx_sbytes_length; lia.
Qed.

Fixpoint log_inside (E : env) (log : list sentry) (W : list ivl) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest => inside W (estart E a) (Z.of_nat w) /\ log_inside E rest W
  end.

Lemma kx_munch_log : forall E m0 m log W, log_flat E log -> log_inside E log W ->
  munch W m0 m -> munch W m0 (mem_denot E m log).
Proof.
  intros E m0 m log W. induction log as [|[a w v] rest IH]; cbn [mem_denot log_flat log_inside]; intros Hlf Hin Hm; [exact Hm|].
  destruct Hlf as (_ & (F1 & F2 & F3 & F4) & Hlf). destruct Hin as [Hi Hin].
  apply (munch_write W m0 _ (estart E a) (kx_sbytes E w v) (IH Hlf Hin Hm)); rewrite ?kx_sbytes_length; [lia | lia | exact Hi].
Qed.

(* [comment removed for export] *)
Lemma estart_ez : forall zs E a, atoms_ok zs E -> 0 <= ez E zs (a_base a) < 2^64 ->
  estart E a = ez E zs (a_base a) + a_off a.
Proof.
  intros zs E a HA Hr. unfold estart. rewrite (ez_sound zs E (a_base a) HA), Z_to_bv_unsigned.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); exact Hr). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma kx_rd_ok : forall m E a n A N, rd_at segs m A N -> A <= estart E a -> estart E a + Z.of_nat n <= A + N -> rd_ok segs m E a n.
Proof.
  intros m E a n A N (H0 & H1 & H) Ha Hn. unfold rd_ok. rewrite adenot_estart. apply rdn_rd_at.
  intros i Hi. replace (estart E a + i) with (A + (estart E a - A + i)) by lia. apply H. lia.
Qed.

Lemma kx_store_ok : forall m E a n A N, wr_at segs m A N -> A <= estart E a -> estart E a + Z.of_nat n <= A + N ->
  store_ok segs m (adenot E a) n = true.
Proof.
  intros m E a n A N Hw Ha Hn. rewrite adenot_estart.
  pose proof (wr_at_store_ok segs m A N (estart E a - A) n Hw ltac:(lia) ltac:(lia)) as X.
  replace (A + (estart E a - A)) with (estart E a) in X by lia. exact X.
Qed.

(* [comment removed for export] *)
Lemma rdval_bytes_at : forall m A bs (k : Z) n sx,
  bytes_at segs m A bs -> 0 <= k -> (Z.to_nat k + n <= length bs)%nat ->
  rdval segs m (wa (A + k)) n sx = Z_to_bv 64 (extz sx n (bytes_le_to_Z (firstn n (skipn (Z.to_nat k) bs)))).
Proof.
  intros m A bs k n sx Hb Hk Hn. unfold rdval.
  pose proof (bytes_at_rdn segs m A bs (Z.to_nat k) n Hb Hn) as H. rewrite Z2Nat.id in H by lia. rewrite H. reflexivity.
Qed.

End Mem.

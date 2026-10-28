(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition es_rep (m : mem) (E top bot : Z) (fl mk buf fs ls fn : list word) : Prop :=
  u32arr usegs m E fl /\ length fl = 16%nat
  /\ u32arr usegs m (E + 64) mk /\ length mk = 16%nat
  /\ u64arr usegs m (E + 128) buf /\ length buf = 16%nat
  /\ u8arr usegs m (E + 256) (zeros 128) /\ u8arr usegs m (E + 384) (zeros 128) /\ u8arr usegs m (E + 512) (zeros 64)
  /\ u64arr usegs m (E + 576) fs /\ length fs = 16%nat
  /\ u32arr usegs m (E + 704) ls /\ length ls = 16%nat
  /\ u64arr usegs m (E + 768) fn /\ length fn = 16%nat
  /\ rw_cells usegs m (E + 896) [C4 (Z_to_bv 64 top); C4 (Z_to_bv 64 bot)] /\ 0 <= top < 16 /\ 0 <= bot < 16.

(* [comment removed for export] *)
Definition slot_word (fs fn : list word) (ik : Z * bool) : option word := nth_error (if snd ik then fn else fs) (Z.to_nat (fst ik)).
Definition slots_ok (fs fn : list word) (ks : list (Z * bool)) (strs : list block) : Prop :=
  NoDup ks /\ length ks = length strs /\ (forall ik, In ik ks -> 0 <= fst ik < 16)
  /\ (forall j ik b, nth_error ks j = Some ik -> nth_error strs j = Some b -> slot_word fs fn ik = Some (Z_to_bv 64 (blk_addr b)) /\ 0 < blk_addr b /\ 0 < blk_size b)
  /\ (forall ik w, 0 <= fst ik < 16 -> slot_word fs fn ik = Some w -> ~ In ik ks -> w = Z_to_bv 64 0)
  (* [comment removed for export] *)
  /\ List.NoDup (map blk_id strs).

(* [comment removed for export] *)
Definition errst_live (E top bot : Z) (strs : list block) (m : mem) : Prop :=
  exists fl mk buf fs ls fn ks, es_rep m E top bot fl mk buf fs ls fn /\ slots_ok fs fn ks strs.

Definition errst_at_rest (E : Z) (strs : list block) (m : mem) : Prop :=
  strs = [] /\ exists fl mk buf ls, es_rep m E 0 0 fl mk buf (repeat (Z_to_bv 64 0) 16) ls (repeat (Z_to_bv 64 0) 16).

Definition errst_fp (E : Z) (strs : list block) (a : Z) : Prop :=
  (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u8arr_agree : forall P (m m' : mem) A bs, agree_on P m m' -> u8arr usegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr usegs m' A bs.
Proof.
  intros P m m' A bs AG [HB HW] HR. split.
  - eapply bytes_at_agree; eauto.
  - eapply wr_at_agree; eauto.
Qed.
Lemma u32arr_agree : forall P (m m' : mem) A ws, agree_on P m m' -> u32arr usegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) -> u32arr usegs m' A ws.
Proof.
  intros P m m' A ws AG [HB HW] HR. split.
  - eapply bytes_at_agree; eauto. rewrite u32s_length. intros a Ha. apply HR. lia.
  - eapply wr_at_agree; eauto.
Qed.
Lemma u64arr_agree : forall P (m m' : mem) A ws, agree_on P m m' -> u64arr usegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr usegs m' A ws.
Proof.
  intros P m m' A ws AG [HB HW] HR. split.
  - eapply bytes_at_agree; eauto. rewrite u64s_length. intros a Ha. apply HR. lia.
  - eapply wr_at_agree; eauto.
Qed.

Lemma es_rep_agree : forall P (m m' : mem) E top bot fl mk buf fs ls fn, agree_on P m m' -> es_rep m E top bot fl mk buf fs ls fn ->
  (forall a, E <= a < E + 904 -> P a) -> es_rep m' E top bot fl mk buf fs ls fn.
Proof.
  intros P m m' E top bot fl mk buf fs ls fn AG (A1 & L1 & A2 & L2 & A3 & L3 & Z1 & Z2 & Z3 & A4 & L4 & A5 & L5 & A6 & L6 & TB & HT & HB) HR.
  assert (R32 : forall A ws, u32arr usegs m A ws -> length ws = 16%nat -> E <= A -> A + 64 <= E + 904 -> u32arr usegs m' A ws)
    by (intros A ws H HL H1 H2; apply (u32arr_agree P m m' A ws AG H); rewrite HL; intros; apply HR; lia).
  assert (R64 : forall A ws, u64arr usegs m A ws -> length ws = 16%nat -> E <= A -> A + 128 <= E + 904 -> u64arr usegs m' A ws)
    by (intros A ws H HL H1 H2; apply (u64arr_agree P m m' A ws AG H); rewrite HL; intros; apply HR; lia).
  assert (R8 : forall A n, u8arr usegs m A (zeros n) -> E <= A -> A + Z.of_nat n <= E + 904 -> u8arr usegs m' A (zeros n))
    by (intros A n H H1 H2; apply (u8arr_agree P m m' A _ AG H); rewrite repeat_length; intros; apply HR; lia).
  split; [apply R32; [exact A1| exact L1| lia| lia]|]. split; [exact L1|].
  split; [apply R32; [exact A2| exact L2| lia| lia]|]. split; [exact L2|].
  split; [apply R64; [exact A3| exact L3| lia| lia]|]. split; [exact L3|].
  split; [apply R8; [exact Z1| lia| cbn; lia]|]. split; [apply R8; [exact Z2| lia| cbn; lia]|]. split; [apply R8; [exact Z3| lia| cbn; lia]|].
  split; [apply R64; [exact A4| exact L4| lia| lia]|]. split; [exact L4|].
  split; [apply R32; [exact A5| exact L5| lia| lia]|]. split; [exact L5|].
  split; [apply R64; [exact A6| exact L6| lia| lia]|]. split; [exact L6|].
  split; [| exact (conj HT HB)].
  apply (rw_cells_agree P m m' _ _ AG TB). cbn [cells_size csize Nat.add]. intros; apply HR; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Proof.
  intros m m' E strs (-> & fl & mk & buf & ls & H) AG. split; [reflexivity|]. exists fl, mk, buf, ls.
  apply (es_rep_agree _ m m' E 0 0 fl mk buf _ ls _ AG H). intros a Ha. left. exact Ha.
Qed.

Theorem errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
Proof.
  intros m m' E top bot strs (fl & mk & buf & fs & ls & fn & ks & H & HS) AG. exists fl, mk, buf, fs, ls, fn, ks. split; [| exact HS].
  apply (es_rep_agree _ m m' E top bot fl mk buf fs ls fn AG H). intros a Ha. left. exact Ha.
Qed.

Theorem errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
Proof. intros E strs a H. exact H. Qed.

Theorem errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
Proof.
  intros m E (_ & fl & mk & buf & ls & H). exists fl, mk, buf, (repeat (Z_to_bv 64 0) 16), ls, (repeat (Z_to_bv 64 0) 16), [].
  split; [exact H|].
  split; [constructor|]. split; [reflexivity|]. split; [intros ik []|].
  split; [intros j ik b Hj; destruct j; discriminate Hj|].
  split; [| constructor].
  intros [i isf] w Hi Hw _. unfold slot_word in Hw. cbn [fst snd] in *.
  assert (X : forall l : list word, l = repeat (Z_to_bv 64 0) 16 -> nth_error l (Z.to_nat i) = Some w -> w = Z_to_bv 64 0).
  { intros l -> Hn. apply nth_error_In in Hn. apply repeat_spec in Hn. exact Hn. }
  destruct isf; eapply X; eauto.
Qed.

(* [comment removed for export] *)
Lemma errst_live_rest : forall m E, errst_live E 0 0 [] m ->
  errst_at_rest E [] m.
Proof.
  intros m E (fl & mk & buf & fs & ls & fn & ks & H & (ND & LEN & RNG & SL & NUL & NDS)).
  destruct ks; [| discriminate LEN].
  destruct H as (A1 & L1 & A2 & L2 & A3 & L3 & Z1 & Z2 & Z3 & A4 & L4 & A5 & L5 & A6 & L6 & TB & HT & HB).
  assert (FS0 : forall (l : list word) (isf : bool), length l = 16%nat -> (forall i w, 0 <= i < 16 -> nth_error l (Z.to_nat i) = Some w -> w = Z_to_bv 64 0) ->
                l = repeat (Z_to_bv 64 0) 16).
  { intros l isf Hl Hz. apply nth_ext with (d := Z_to_bv 64 0) (d' := Z_to_bv 64 0); [rewrite repeat_length; exact Hl|].
    intros n Hn. rewrite nth_repeat. destruct (nth_error l n) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
    rewrite (nth_error_nth l n (Z_to_bv 64 0) Hw). apply (Hz (Z.of_nat n) w); [lia|]. rewrite Nat2Z.id. exact Hw. }
  assert (EFS : fs = repeat (Z_to_bv 64 0) 16).
  { apply (FS0 fs false L4). intros i w Hi Hw. apply (NUL (i, false) w); [cbn; lia| unfold slot_word; cbn [fst snd]; exact Hw| intros []]. }
  assert (EFN : fn = repeat (Z_to_bv 64 0) 16).
  { apply (FS0 fn true L6). intros i w Hi Hw. apply (NUL (i, true) w); [cbn; lia| unfold slot_word; cbn [fst snd]; exact Hw| intros []]. }
  subst fs fn. split; [reflexivity|]. exists fl, mk, buf, ls.
  exact (conj A1 (conj L1 (conj A2 (conj L2 (conj A3 (conj L3 (conj Z1 (conj Z2 (conj Z3 (conj A4 (conj L4 (conj A5 (conj L5 (conj A6 (conj L6 (conj TB (conj HT HB))))))))))))))))).
Qed.

End WithCeiling0.

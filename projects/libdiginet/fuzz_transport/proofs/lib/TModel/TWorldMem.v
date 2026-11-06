(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/varnish/esi_parse_fuzzer/lib/Yd/DA_Tac.v, with its module paths and module names changed; 635 of its 698 lines of code are new or changed and 187 lines of the source are left out. *)
(* Requiring this file REDEFINES the kit's solve_load, solve_store and mem_after_store_opt (as Lib/Tac.v redefines
   Lib/Step.v's): each first tries the world hook and otherwise runs the kit's own tactic, so a walk that imports a
   build's Prog/T/WMem.v steps world loads and stores with the kit's [step] (and StepFast's sf_step_core, which calls
   the same three tactics). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas.
Import ListNotations.
Open Scope Z_scope.

(* The world at base A in memory m: ONE writable cell of W_LEN bytes holding B (so length B = W_LEN). It is an
   abbreviation, so a hypothesis or postcondition [wmem_at segs A m B] IS an rw_cells fact: the kit's transport
   tactics (transport_chunks, transport_after_call, rw_cells_frame) carry it across stores and calls outside the
   world, and the hooks below find it by its cell size [Z.to_nat W_LEN]. Keep A a NAME (W_BASE_PLAIN, W_BASE_UBSAN):
   the kit's cell machinery only engages for a literal base and would then build 65536-deep unary nats. *)
Abbreviation wmem_at segs A m B := (rw_cells segs m A (CB (Z.to_nat W_LEN) B :: nil)).

Lemma W_LEN_val : W_LEN = 65616.
Proof. reflexivity. Qed.

Lemma wm_size : forall B, Z.of_nat (cells_size [CB (Z.to_nat W_LEN) B]) = W_LEN.
Proof. intros. cbn [cells_size csize]. rewrite Nat.add_0_r. rewrite Z2Nat.id; [reflexivity | unfold W_LEN; lia]. Qed.

Section WithSegs.
Variable segs : list Segment.

(* ---- shape ---- *)

Lemma wm_len : forall A m B, wmem_at segs A m B -> length B = Z.to_nat W_LEN.
Proof. intros A m B [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hc _]. exact Hc. Qed.

Lemma wm_bytes : forall A m B, wmem_at segs A m B -> bytes_at segs m A B.
Proof. intros A m B [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma wm_wr : forall A m B, wmem_at segs A m B -> wr_at segs m A W_LEN.
Proof. intros A m B [_ Hw]. rewrite wm_size in Hw. exact Hw. Qed.

Lemma wm_bound : forall A m B, wmem_at segs A m B -> 0 <= A /\ A + W_LEN <= 2 ^ 64.
Proof. intros A m B H. pose proof (rw_cells_bound segs m A _ H) as R. rewrite wm_size in R. exact R. Qed.

Lemma wm_intro : forall A m B, bytes_at segs m A B -> wr_at segs m A W_LEN -> length B = Z.to_nat W_LEN ->
  wmem_at segs A m B.
Proof.
  intros A m B Hb Hw Hl. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - rewrite wm_size. exact Hw.
Qed.

(* ---- (a) loads: n bytes at A + k inside the world are the model's sub B k n ---- *)

Lemma wm_read : forall A m B k n a, wmem_at segs A m B -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  a = Z_to_bv 64 (A + k) -> ov_read_bytes segs m a n = Some (sub B k n).
Proof.
  intros A m B k n a H Hk Hn ->. pose proof (wm_len _ _ _ H) as L.
  exact (bytes_at_read segs m A B k n (wm_bytes _ _ _ H) Hk ltac:(rewrite L; unfold W_LEN in *; lia)).
Qed.

(* ---- (b) stores ---- *)

Lemma wm_store_ok : forall A m B k n a, wmem_at segs A m B -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  a = Z_to_bv 64 (A + k) -> store_ok segs m a n = true.
Proof. intros A m B k n a H Hk Hn ->. exact (wr_at_store_ok segs m A W_LEN k n (wm_wr _ _ _ H) Hk Hn). Qed.

Lemma wm_write : forall A m B k v, wmem_at segs A m B -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  wmem_at segs A (write_to_mem m (wa (A + k)) v) (upd B k v).
Proof.
  intros A m B k v H Hk Hv. pose proof (wm_len _ _ _ H) as L.
  apply wm_intro.
  - rewrite upd_upd_bytes. apply bytes_at_write_inside; [exact (wm_bytes _ _ _ H) | exact Hk |].
    rewrite L. unfold W_LEN in *. lia.
  - apply wr_at_write. exact (wm_wr _ _ _ H).
  - rewrite length_upd; [exact L | exact Hk |]. rewrite L. unfold W_LEN in *. lia.
Qed.

Lemma wm_write_at : forall A m B k v E, wmem_at segs A m B -> 0 <= k -> k + Z.of_nat (length v) <= W_LEN ->
  E = A + k -> wmem_at segs A (write_to_mem m (wa E) v) (upd B k v).
Proof. intros A m B k v E H Hk Hv ->. apply wm_write; assumption. Qed.

(* Every address outside the stored span keeps its byte. *)
Lemma wm_write_outside : forall m a v (x : word), 0 <= a -> a + Z.of_nat (length v) <= 2 ^ 64 ->
  ~ (a <= bv_unsigned x < a + Z.of_nat (length v)) -> write_to_mem m (wa a) v x = m x.
Proof.
  intros m a v x Ha Hl Hx. rewrite write_to_mem_spec by assumption.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length v)));
    cbn [andb]; try reflexivity.
  exfalso. lia.
Qed.

Lemma wm_write_munch : forall m a v, 0 <= a -> a + Z.of_nat (length v) <= 2 ^ 64 ->
  munch [(a, a + Z.of_nat (length v))] m (write_to_mem m (wa a) v).
Proof. intros m a v Ha Hl x Hx. cbn [outside] in Hx. apply wm_write_outside; [exact Ha | exact Hl | tauto]. Qed.

(* ---- (c) pieces for the libc contracts (Prog/memcpy_c.v:33-42, Prog/memset_c.v:19-25) ---- *)

(* A memcpy source inside the world. *)
Lemma wm_bytes_sub : forall A m B k n, wmem_at segs A m B -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  bytes_at segs m (A + k) (sub B k n).
Proof.
  intros A m B k n H Hk Hn. pose proof (wm_len _ _ _ H) as L. pose proof (wm_bytes _ _ _ H) as (Ha & Hl & Hb).
  unfold W_LEN in *.
  assert (LS : length (sub B k n) = n) by (apply length_sub; lia).
  split; [lia|]. split; [rewrite LS; lia|].
  intros i Hi. rewrite LS in Hi. rewrite ne_sub by lia.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  replace (A + k + Z.of_nat i) with (A + Z.of_nat (Z.to_nat k + i)) by lia.
  apply Hb. lia.
Qed.

Lemma wm_src : forall A m B k n X, wmem_at segs A m B -> X = A + k -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  bytes_at segs m X (sub B k n).
Proof. intros A m B k n X H -> Hk Hn. apply wm_bytes_sub; assumption. Qed.

(* A memcpy / memset destination inside the world: the cell the contracts ask for, with junk = the old bytes. *)
Lemma wm_piece : forall A m B k n X, wmem_at segs A m B -> X = A + k -> 0 <= k -> 0 <= n -> k + n <= W_LEN ->
  rw_cells segs m X [CB (Z.to_nat n) (sub B k (Z.to_nat n))].
Proof.
  intros A m B k n X H -> Hk Hn Hkn. pose proof (wm_len _ _ _ H) as L.
  pose proof (wm_bytes_sub A m B k (Z.to_nat n) H Hk ltac:(lia)) as Hs.
  pose proof (wm_wr _ _ _ H) as (Ha & Hl & Hw). unfold W_LEN in *.
  assert (LS : length (sub B k (Z.to_nat n)) = Z.to_nat n) by (apply length_sub; lia).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LS | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hs.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|].
    intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply Hw. lia.
Qed.

(* ---- the world after a callee that wrote an out cell inside it ----
   The general form: the callee's post gives its footprint W (munch W m m') and the cell [X, X + c) it filled with
   src; every world byte outside that cell must be outside W. W may hold any number of spans: the callee's own stack
   window, the out cell, more cells off the world (diginet_frame_build's munch [(sp - 240, sp); (out, out + cap)]).
   The world is then upd B k src. *)
Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.

Lemma wm_fill_out : forall A m m' B W X k c src,
  wmem_at segs A m B ->
  munch W m m' -> wmono segs m m' ->
  rw_cells segs m' X [CB c src] ->
  X = A + k -> 0 <= k -> k + Z.of_nat c <= W_LEN ->
  (forall x, A <= x < A + W_LEN -> ~ (X <= x < X + Z.of_nat c) -> outside W x) ->
  wmem_at segs A m' (upd B k src).
Proof.
  intros A m m' B W X k c src H MU WM D -> Hk Hkc OUT.
  pose proof (wm_len _ _ _ H) as L. pose proof (wm_bytes _ _ _ H) as (HBa & HBl & HB).
  pose proof (wm_wr _ _ _ H) as HW. pose proof (wm_bound _ _ _ H) as [HA HA2].
  destruct D as [[Dwf Db] _]. cbn [cells_wf cell_wf] in Dwf. destruct Dwf as [LS _].
  cbn [cells_bytes cbytes] in Db. rewrite app_nil_r in Db. destruct Db as (_ & _ & Dbi).
  unfold W_LEN in * |-.
  assert (LU : length (upd B k src) = length B) by (apply length_upd; [exact Hk | rewrite LS, L; lia]).
  apply wm_intro.
  - split; [lia|]. split; [rewrite LU, L; lia|].
    intros i Hi. rewrite LU, L in Hi.
    rewrite ne_upd by (rewrite ?LS, ?L; lia). rewrite LS.
    destruct ((Z.to_nat k <=? i) && (i <? Z.to_nat k + c))%nat eqn:C.
    + apply andb_true_iff in C. destruct C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.ltb_lt in C2.
      rewrite <- Dbi by (rewrite ?LS; lia).
      f_equal. unfold wa. f_equal. lia.
    + rewrite <- HB by (rewrite ?L; lia).
      unfold mrd. rewrite MU; [reflexivity|].
      rewrite wa_unsigned by lia. apply OUT; [lia|].
      apply andb_false_iff in C. destruct C as [C|C]; [apply Nat.leb_gt in C | apply Nat.ltb_ge in C]; lia.
  - eapply wr_at_transport; [exact HW | exact WM].
  - rewrite LU. exact L.
Qed.

(* One span [X, X + n) with the bytes src (memcpy_post's / memset_post's munch and cell). *)
Lemma wm_fill : forall A m m' B X k n src,
  wmem_at segs A m B ->
  munch [(X, X + n)] m m' -> wmono segs m m' ->
  rw_cells segs m' X [CB (Z.to_nat n) src] ->
  X = A + k -> 0 <= k -> 0 <= n -> k + n <= W_LEN ->
  wmem_at segs A m' (upd B k src).
Proof.
  intros A m m' B X k n src H MU WM D EX Hk Hn Hkn.
  apply (wm_fill_out A m m' B [(X, X + n)] X k (Z.to_nat n) src H MU WM D EX Hk); [lia|].
  intros x _ Hx. cbn [outside]. split; [lia | exact I].
Qed.

(* The list form: the out cell's span between spans W1 and W2 that miss the world. *)
Lemma wm_fill_spans : forall A m m' B W1 W2 X n k c src,
  wmem_at segs A m B ->
  munch (W1 ++ (X, X + n) :: W2) m m' -> wmono segs m m' ->
  rw_cells segs m' X [CB c src] -> n <= Z.of_nat c ->
  X = A + k -> 0 <= k -> k + Z.of_nat c <= W_LEN ->
  disjoint_from W1 A W_LEN -> disjoint_from W2 A W_LEN ->
  wmem_at segs A m' (upd B k src).
Proof.
  intros A m m' B W1 W2 X n k c src H MU WM D Hn EX Hk Hkc D1 D2.
  apply (wm_fill_out A m m' B _ X k c src H MU WM D EX Hk Hkc).
  intros x Hx Hc. apply outside_app. split; [exact (disjoint_outside W1 A W_LEN x D1 Hx)|].
  cbn [outside]. split; [lia | exact (disjoint_outside W2 A W_LEN x D2 Hx)].
Qed.

(* The destination in the form [CB (length oj) oj] (diginet_frame_build's out, fuzz_frame/lib/Prog/
   diginet_frame_build_c.v): oj = sub B k n, the old bytes of the world there. *)
Lemma wm_cell : forall A m B k n X, wmem_at segs A m B -> X = A + k -> 0 <= k -> k + Z.of_nat n <= W_LEN ->
  rw_cells segs m X [CB (length (sub B k n)) (sub B k n)].
Proof.
  intros A m B k n X H EX Hk Hkn. pose proof (wm_len _ _ _ H) as L.
  rewrite length_sub by (rewrite ?L; unfold W_LEN in *; lia).
  pose proof (wm_piece A m B k (Z.of_nat n) X H EX Hk ltac:(lia) Hkn) as P.
  rewrite Nat2Z.id in P. exact P.
Qed.

(* ---- the machine word a load writes into rd (Riscv/Sem.v:386-392 load_val, Lib/MState.v:49-53) ---- *)

Lemma ld_val : forall bs, bv_extract 0 64 (le_bytes_to_word bs) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs. transitivity (le_bytes_to_word bs); [|reflexivity].
  apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

End WithSegs.

Lemma wm_wrap_small : forall B k n, (n <= 8)%nat -> bv_wrap 64 (u_at B k n) = u_at B k n.
Proof.
  intros B k n Hn. pose proof (u_at_range B k n) as R. apply bv_wrap_small.
  unfold bv_modulus. change (Z.of_N 64) with 64.
  assert (P : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* ld *)
Lemma wm_ld : forall B k, bv_extract 0 64 (le_bytes_to_word (sub B k 8)) = Z_to_bv 64 (u_at B k 8).
Proof. intros. apply ld_val. Qed.

(* lwu, lhu, lbu: zero extension of u_at *)
Lemma wm_lwu : forall B k, zext 64 (bv_extract 0 32 (le_bytes_to_word (sub B k 4))) = Z_to_bv 64 (u_at B k 4).
Proof.
  intros. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 4). rewrite wm_wrap_small by lia.
  pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R. change (Z.of_N 32) with 32.
  apply Z.mod_small. exact R.
Qed.
Lemma wm_lhu : forall B k, zext 64 (bv_extract 0 16 (le_bytes_to_word (sub B k 2))) = Z_to_bv 64 (u_at B k 2).
Proof.
  intros. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 2). rewrite wm_wrap_small by lia.
  pose proof (u_at_range B k 2) as R. change (8 * Z.of_nat 2) with 16 in R. change (Z.of_N 16) with 16.
  apply Z.mod_small. exact R.
Qed.
Lemma wm_lbu : forall B k, zext 64 (bv_extract 0 8 (le_bytes_to_word (sub B k 1))) = Z_to_bv 64 (u_at B k 1).
Proof.
  intros. rewrite zext_small. f_equal. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 1). rewrite wm_wrap_small by lia.
  pose proof (u_at_range B k 1) as R. change (8 * Z.of_nat 1) with 8 in R. change (Z.of_N 8) with 8.
  apply Z.mod_small. exact R.
Qed.

(* lw: s32_at; lh, lb: the signed wrap of u_at *)
Lemma wm_lw : forall B k, sext 64 (bv_extract 0 32 (le_bytes_to_word (sub B k 4))) = Z_to_bv 64 (s32_at B k).
Proof.
  intros. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 4). rewrite wm_wrap_small by lia.
  reflexivity.
Qed.
Lemma wm_lh : forall B k, sext 64 (bv_extract 0 16 (le_bytes_to_word (sub B k 2))) = Z_to_bv 64 (bv_swrap 16 (u_at B k 2)).
Proof.
  intros. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 2). rewrite wm_wrap_small by lia.
  reflexivity.
Qed.
Lemma wm_lb : forall B k, sext 64 (bv_extract 0 8 (le_bytes_to_word (sub B k 1))) = Z_to_bv 64 (bv_swrap 8 (u_at B k 1)).
Proof.
  intros. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. fold (u_at B k 1). rewrite wm_wrap_small by lia.
  reflexivity.
Qed.

(* lw as the sign extension of the 32-bit u_at, and s32_at as that same word. *)
Lemma wm_lw_u : forall B k,
  sext 64 (bv_extract 0 32 (le_bytes_to_word (sub B k 4))) = sext 64 (Z_to_bv 32 (u_at B k 4)).
Proof.
  intros. f_equal. apply bv_eq. rewrite extract_low_mod by lia.
  unfold le_bytes_to_word. rewrite !Z_to_bv_unsigned. fold (u_at B k 4). rewrite wm_wrap_small by lia.
  pose proof (u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R. change (Z.of_N 32) with 32.
  unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32. reflexivity.
Qed.

Lemma s32_at_sext : forall B k, Z_to_bv 64 (s32_at B k) = sext 64 (Z_to_bv 32 (u_at B k 4)).
Proof.
  intros. rewrite sext_small. f_equal. unfold s32_at, bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap.
  f_equal. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* ---- the stack window of a walk lies above the world ---- *)
Definition w_off_stack (A : Z) (sp : word) (K : Z) : Prop := A + W_LEN <= bv_unsigned sp - K.

(* ---- for the indexed-address and the post-call tactics below ---- *)

(* two addresses equal mod 2^64 are the same word (wk_bv_eq) *)
Lemma wk_bv_eqm : forall e1 e2, e1 mod 2 ^ 64 = e2 mod 2 ^ 64 -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof. intros e1 e2 H. apply bv_eq. rewrite !unsigned_lit_wrap. exact H. Qed.

(* the range of a register, for lia (wk_disj_side) *)
Lemma wk_word_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as R. unfold bv_modulus in R. exact R. Qed.

(* Two byte lists with the same values are equal. Lists built two ways (le8 (Z_to_bv 64 v) turned into put 8 v by
   le8_put, a literal list, an app of both) can hold the same bytes and still not be convertible, so [reflexivity]
   fails; compare their values instead. On CLOSED lists the premise goes by [vm_compute; reflexivity]: no open
   bitvector is in it. (First written as Prog/T/WalkNotify.v's.) *)
Lemma bytes_eq_of_zs : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity |].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

(* ==== tactics ==== *)

(* [t = its value] in the context, for lia (W_LEN, and the world base name). *)
Ltac wk_eq_fact t :=
  let v := eval vm_compute in t in
  lazymatch goal with
  | _ : t = v |- _ => idtac
  | _ => let E := fresh "Ew" in assert (E : t = v) by (vm_compute; reflexivity)
  end.

Ltac wk_facts :=
  wk_eq_fact W_LEN;
  try match goal with _ : rw_cells _ _ ?A [CB (Z.to_nat W_LEN) _] |- _ =>
        lazymatch A with Z0 => idtac | Zpos _ => idtac | _ => wk_eq_fact A end
      end.

(* The value of a CLOSED address expression, computed WITHOUT ever normalising an open term: [vm_compute] on a
   term that still holds [Z_to_bv 64 <open>] normalises that bitvector's well-formedness proof, which is ruinous
   (one such call cost 93 GB and 50 minutes before it was killed). So walk down +, -, * and bv_unsigned ourselves
   and only ever compute on atoms (a literal, or a constant such as W_BASE_PLAIN / A_M_desk / OFF_g_q). *)
Ltac wk_zval E :=
  lazymatch E with
  | Z0 => E
  | Zpos _ => E
  | Zneg _ => E
  | Z.add ?x ?y => let a := wk_zval x in let b := wk_zval y in eval vm_compute in (Z.add a b)
  | Z.sub ?x ?y => let a := wk_zval x in let b := wk_zval y in eval vm_compute in (Z.sub a b)
  | Z.mul ?x ?y => let a := wk_zval x in let b := wk_zval y in eval vm_compute in (Z.mul a b)
  | Z.opp ?x => let a := wk_zval x in eval vm_compute in (Z.opp a)
  | bv_unsigned (Z_to_bv 64 ?z) => let a := wk_zval z in eval vm_compute in (Z.modulo a 18446744073709551616)
  | ?f ?x => fail 0 "wk_zval: open address"
  | _ => let v := eval vm_compute in E in
         lazymatch v with Z0 => v | Zpos _ => v | Zneg _ => v end
  end.

(* the literal d = c - A when the literal c lies in the world *)
Ltac wk_world_lit A c :=
  let Av := wk_zval A in
  let cv := wk_zval c in
  let d := eval vm_compute in (cv - Av) in
  let ok := eval vm_compute in (andb (Z.leb 0 d) (Z.ltb d W_LEN)) in
  lazymatch ok with true => d end.

(* the world offset k of address a (a word): A + k by syntax; a closed address by computation; an indexed address
   c + X with the literal c inside the world (an array base plus a scaled index, as vnorm leaves auipc / addi /
   slli / add) as (c - A) + X *)
Ltac wk_offset A a :=
  let E := addr_expr a in
  lazymatch E with
  | Z.add A ?k => k
  | _ =>
      match E with
      | _ => let Av := wk_zval A in let L := wk_zval E in eval vm_compute in (L - Av)
      | Z.add ?c ?X => let d := wk_world_lit A c in constr:(Z.add d X)
      | Z.add ?X ?c => let d := wk_world_lit A c in constr:(Z.add d X)
      end
  end.

(* a literal offset must lie in the world; a symbolic one is left to lia *)
Ltac wk_in_range k n :=
  lazymatch k with
  | Z0 => idtac
  | Zpos _ => let ok := eval vm_compute in (Z.leb (k + Z.of_nat n) W_LEN) in lazymatch ok with true => idtac end
  | Zneg _ => fail
  | _ => idtac
  end.

(* An OPEN bitvector in t: [Z_to_bv _ z] or [wa z] with a free variable in z. [vm_compute] on such a term
   normalises the bitvector's well-formedness proof over the open z, which is ruinous: an open address in an early
   wk_offset (93 GB, 50 min), a stored value [le4 (Z_to_bv 64 v)] in wk_len_side (a ubsan compile killed after
   more than 20 min). *)
Ltac wk_open_bv t :=
  match t with
  | context [Z_to_bv _ ?z] => match z with context [?x] => is_var x end
  | context [wa ?z] => match z with context [?x] => is_var x end
  end.
Ltac wk_no_open_bv t := tryif (wk_open_bv t) then fail else idtac.

(* vm_compute ONLY on a numeric comparison / equation with no open bitvector in it: never on a [bv 64] equation,
   whose normal form carries the well-formedness proofs and, with a free index in the address, is ruinous to
   normalise; never on a goal that holds [Z_to_bv 64 <open>]. *)
Ltac wk_vm_close :=
  lazymatch goal with |- ?G => wk_no_open_bv G end;
  lazymatch goal with
  | |- (_ <= _)%Z => vm_compute; congruence
  | |- (_ < _)%Z => vm_compute; congruence
  | |- (_ <= _)%nat => vm_compute; congruence
  | |- (_ < _)%nat => vm_compute; congruence
  | |- @eq Z _ _ => vm_compute; reflexivity
  | |- @eq nat _ _ => vm_compute; reflexivity
  end.

(* a goal over Z with world constants, a scaled index (slli) and bv literals *)
Ltac wk_zside :=
  rewrite ?unsigned_lit by (unfold W_LEN in *; lia);
  rewrite ?Z.shiftl_mul_pow2 by lia;
  unfold W_LEN in *; lia.

(* lia with the array bounds of TWorld.v unfolded, for an index bound stated by name (0 <= i < OW_t_N) *)
Ltac wk_nlia := unfold W_LEN, OW_t_N, GOT_t_N, S_queue_N, Cmd_N in *; lia.

Ltac wk_side := first [ lia | (unfold W_LEN in *; lia) | wk_nlia | wk_zside | wk_vm_close ].
(* the length of the stored bytes by its lemma FIRST, then lia: a stored [le4 (Z_to_bv 64 <open>)] never reaches
   vm_compute *)
Ltac wk_len_side :=
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_put; cbn [length];
  wk_side.
Ltac wk_addr_eq :=
  first [ (f_equal; first [ reflexivity | lia | wk_zside ])
        | (unfold wa; f_equal; first [ reflexivity | lia | wk_zside ])
        | (apply wa_of_Z_to_bv; first [ lia | wk_zside ])
        | reflexivity ].

Ltac wk_load_post :=
  cbv beta iota;
  rewrite ?wm_ld, ?wm_lw, ?wm_lwu, ?wm_lh, ?wm_lhu, ?wm_lb, ?wm_lbu.

(* ---- indexed world addresses ----
   wk_offset reads A + k, a closed address, and c + X (one literal inside the world and the rest). The field of an
   element of a struct array, addressed through a register (OW.t[n].f, GOT.t[n].f, g_cmd[k].f, g_s.queue[i].f), has
   no such form: the compiler leaves (base + esz * idx) + field, two literals with the index between them, and the
   index often still wrapped (12 * n as bv_unsigned (Z_to_bv 64 (n << 4)) - bv_unsigned (Z_to_bv 64 (n << 2))).
   For such an address the hooks first run wk_idx_norm: wk_offset_idx reads the address by syntax as
   A + (d + esz * idx), wk_bv_eq proves that reading (mod 2^64, so with no bound), and the address is rewritten to it
   in the goal. Every later side goal is then lia over d + esz * idx with the index bound from the context, and the
   new world (wk_fold_store) and the loaded value (wk_fold_load) get the model's offset A_<field> idx. No step calls
   vm_compute on an open term. *)

(* a reading of E by syntax: bv_unsigned (Z_to_bv 64 z) as z, Z.shiftl x k (k closed) as x * 2^k. Equal to E only
   mod 2^64, so it is used only through wk_bv_eq. *)
Ltac wk_unwrap E :=
  match E with
  | Z.add ?x ?y => let a := wk_unwrap x in let b := wk_unwrap y in constr:(Z.add a b)
  | Z.sub ?x ?y => let a := wk_unwrap x in let b := wk_unwrap y in constr:(Z.sub a b)
  | Z.mul ?x ?y => let a := wk_unwrap x in let b := wk_unwrap y in constr:(Z.mul a b)
  | Z.opp ?x => let a := wk_unwrap x in constr:(Z.opp a)
  | Z.shiftl ?x ?k => let a := wk_unwrap x in let k0 := wk_zval k in
                      let p := eval vm_compute in (Z.pow 2 k0) in constr:(Z.mul a p)
  | bv_unsigned (Z_to_bv 64 ?z) => wk_unwrap z
  | _ => E
  end.

Ltac wk_zplus X Y := lazymatch X with Z0 => Y | _ => lazymatch Y with Z0 => X | _ => constr:(Z.add X Y) end end.
Ltac wk_zminus X Y :=
  lazymatch Y with Z0 => X | _ => lazymatch X with Z0 => constr:(Z.opp Y) | _ => constr:(Z.sub X Y) end end.

(* E as (c, X): c the literal sum of E's closed summands, X the rest (0 when there is none) *)
Ltac wk_split E :=
  match E with
  | _ => let v := wk_zval E in constr:((v, 0%Z))
  | Z.add ?x ?y =>
      let p := wk_split x in let q := wk_split y in
      lazymatch p with (?c1, ?X1) => lazymatch q with (?c2, ?X2) =>
        let c := eval vm_compute in (Z.add c1 c2) in let X := wk_zplus X1 X2 in constr:((c, X)) end end
  | Z.sub ?x ?y =>
      let p := wk_split x in let q := wk_split y in
      lazymatch p with (?c1, ?X1) => lazymatch q with (?c2, ?X2) =>
        let c := eval vm_compute in (Z.sub c1 c2) in let X := wk_zminus X1 X2 in constr:((c, X)) end end
  | _ => constr:((0%Z, E))
  end.

(* the one open atom of X (the index); fails when X has none *)
Ltac wk_atom X :=
  match X with
  | Z.add ?x _ => wk_atom x
  | Z.add _ ?y => wk_atom y
  | Z.sub ?x _ => wk_atom x
  | Z.sub _ ?y => wk_atom y
  | Z.mul ?x _ => wk_atom x
  | Z.mul _ ?y => wk_atom y
  | Z.opp ?x => wk_atom x
  | Z.add _ _ => fail 1
  | Z.sub _ _ => fail 1
  | Z.mul _ _ => fail 1
  | Z.opp _ => fail 1
  | _ => let closed := match constr:(tt) with _ => let v := wk_zval X in constr:(true) | _ => constr:(false) end in
         lazymatch closed with false => X end
  end.

(* X = x0 + e * i, read off X at i = 0 and i = 1 (wk_bv_eq proves the result, so a wrong reading only fails); fails
   unless i is X's only open atom *)
Ltac wk_lin X :=
  let i := wk_atom X in
  let px := eval pattern i in X in
  let f := lazymatch px with ?f _ => f end in
  let t0 := eval cbv beta in (f 0%Z) in
  let t1 := eval cbv beta in (f 1%Z) in
  let v0 := wk_zval t0 in
  let v1 := wk_zval t1 in
  let e := eval vm_compute in (Z.sub v1 v0) in
  constr:((v0, e, i)).

(* the model's name of the world offset d + e * i (TWorld.v): A_<field> i of a struct array, or g_q's
   OFF_g_q + 4 * i (Q_at's offset); fails when no field has element 0 at d and element size e *)
Ltac wk_field_at F d e i :=
  let v0 := eval vm_compute in (F 0%Z) in
  let v1 := eval vm_compute in (Z.sub (F 1%Z) (F 0%Z)) in
  lazymatch v0 with d => lazymatch v1 with e => eval cbv beta in (F i) end end.
Ltac wk_field d e i :=
  match constr:(tt) with
  | _ => wk_field_at A_OW_t_state d e i
  | _ => wk_field_at A_OW_t_old d e i
  | _ => wk_field_at A_OW_t_reason d e i
  | _ => wk_field_at A_GOT_t_state d e i
  | _ => wk_field_at A_GOT_t_old d e i
  | _ => wk_field_at A_GOT_t_reason d e i
  | _ => wk_field_at A_S_queue_bytes d e i
  | _ => wk_field_at A_S_queue_len d e i
  | _ => wk_field_at A_S_queue_display d e i
  | _ => wk_field_at A_S_queue_key d e i
  | _ => wk_field_at A_Cmd_st d e i
  | _ => wk_field_at A_Cmd_key d e i
  | _ => wk_field_at A_Cmd_display d e i
  | _ => wk_field_at A_Cmd_bytes d e i
  | _ => wk_field_at A_Cmd_len d e i
  | _ => wk_field_at (fun j : Z => OFF_g_q + 4 * j) d e i
  end.
Ltac wk_unfold_fields :=
  unfold A_OW_t_state, A_OW_t_old, A_OW_t_reason, A_GOT_t_state, A_GOT_t_old, A_GOT_t_reason,
         A_S_queue_bytes, A_S_queue_len, A_S_queue_display, A_S_queue_key,
         A_Cmd_st, A_Cmd_key, A_Cmd_display, A_Cmd_bytes, A_Cmd_len,
         OFF_OW, OFF_GOT, OFF_g_s, OFF_g_cmd, OFF_g_q.
Ltac wk_field_of k :=
  lazymatch k with
  | Z.add ?d (Z.mul ?e ?i) => let d0 := zlit d in let e0 := zlit e in wk_field d0 e0 i
  end.

(* the offset K of an indexed world address a: d + esz * idx (d, esz literals), or d + X when the open part X is not
   one index times a constant. Fails unless the literal part of a lies in the world (base A). *)
Ltac wk_offset_idx A a :=
  let E := addr_expr a in
  let Av := wk_zval A in
  let Eu := wk_unwrap E in
  let p := wk_split Eu in
  lazymatch p with
  | (?c, ?X) =>
      let d := eval vm_compute in (Z.sub c Av) in
      let ok := eval vm_compute in (andb (Z.leb 0 d) (Z.ltb d W_LEN)) in
      lazymatch ok with
      | true =>
          lazymatch X with
          | Z0 => fail
          | _ =>
              match constr:(tt) with
              | _ => let q := wk_lin X in
                     lazymatch q with
                     | (?x0, ?e, ?i) =>
                         lazymatch e with
                         | Z0 => fail
                         | _ => let d' := eval vm_compute in (Z.add d x0) in constr:(Z.add d' (Z.mul e i))
                         end
                     end
              | _ => constr:(Z.add d X)
              end
          end
      end
  end.

(* Z_to_bv 64 E = Z_to_bv 64 (A + K): by lia when E holds no wrap, else mod 2^64 (each bv_unsigned (Z_to_bv 64 z)
   as z mod 2^64, each shift as a product, the powers as literals) *)
Ltac wk_pow_lits :=
  repeat match goal with
  | |- context [Z.pow ?b ?k] =>
      let b0 := wk_zval b in let k0 := wk_zval k in
      let v := eval vm_compute in (Z.pow b0 k0) in change (Z.pow b k) with v
  end.
Ltac wk_bv_eq :=
  first [ (apply (f_equal (Z_to_bv 64)); lia)
        | (apply wk_bv_eqm; rewrite ?unsigned_lit_wrap;
           repeat match goal with
           | |- context [Z.shiftl ?x ?k] => let k0 := wk_zval k in rewrite (Z.shiftl_mul_pow2 x k) by lia
           end;
           wk_pow_lits; Z.div_mod_to_equations; lia) ].

Ltac wk_isafe := first [ lia | wk_nlia ].

(* Rewrite the indexed world address a of an n-byte access to Z_to_bv 64 (A + K). Fails LOUDLY when K is not
   provably inside the world (the walk has no index bound in its context) or the reading does not prove. *)
Ltac wk_idx_norm A a n :=
  let K := wk_offset_idx A a in
  let E := addr_expr a in
  first [ assert_succeeds
            (assert (0 <= K /\ K + Z.of_nat n <= W_LEN)
               by (split; [ wk_isafe
                          | rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_put; cbn [length];
                            wk_isafe ]))
        | fail 100 "wk_idx_norm: the indexed world access at W_BASE +" K "is not provably inside the world;"
                   "put the index bound (0 <= i < N) in the context before the access" ];
  let EQ := fresh "Eidx" in
  first [ assert (EQ : Z_to_bv 64 E = Z_to_bv 64 (A + K)) by wk_bv_eq
        | fail 100 "wk_idx_norm: cannot prove the address" E "is W_BASE +" K ];
  lazymatch a with wa _ => change a with (Z_to_bv 64 E) | _ => idtac end;
  rewrite EQ; clear EQ.

(* Before a hook: an address of a world access that wk_offset cannot read is rewritten by wk_idx_norm; any other
   address is left as it is. *)
Ltac wk_idx_prep_load :=
  try match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) _] |- _ =>
          tryif (let k := wk_offset A a in idtac) then fail else idtac;
          wk_facts;
          wk_idx_norm A a n
      end
  end.
Ltac wk_idx_prep_store :=
  try match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) _] |- _ =>
          tryif (let k := wk_offset A a in idtac) then fail else idtac;
          wk_facts;
          wk_idx_norm A a n
      end
  end.

(* The model's offset A_<field> i for d + e * i: in the loaded value (s32_at / u_at, the forms wk_load_post leaves),
   and in the new world after a store. Only for an address the hooks see as A + k (wk_idx_norm's form, wk_is_at):
   an address c + X keeps the offset d + X that wk_offset reads, as before, for the walks that name it themselves.
   Nothing when the table of wk_field has no such field. *)
Ltac wk_fold_load k :=
  try (let FI := wk_field_of k in
       let EQK := fresh "EQk" in
       assert (EQK : k = FI) by (wk_unfold_fields; lia);
       repeat match goal with
       | |- context [s32_at ?B k] =>
           let e := fresh "Ek" in
           assert (e : s32_at B k = s32_at B FI) by (rewrite EQK; reflexivity); rewrite e; clear e
       | |- context [u_at ?B k ?n] =>
           let e := fresh "Ek" in
           assert (e : u_at B k n = u_at B FI n) by (rewrite EQK; reflexivity); rewrite e; clear e
       end;
       clear EQK).
Ltac wk_fold_store k H :=
  try (let FI := wk_field_of k in replace k with FI in H by (wk_unfold_fields; lia)).
Ltac wk_is_at A a := let E := addr_expr a in lazymatch E with Z.add A _ => idtac end.

(* load hook: rewrite the read of a world address by wm_read *)
Ltac wk_solve_load_world :=
  wk_idx_prep_load;
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) ?B] |- _ =>
          wk_facts;
          let k := wk_offset A a in
          wk_in_range k n;
          rewrite (wm_read segs A m B k n a H) by first [ wk_side | wk_addr_eq ];
          wk_load_post;
          tryif wk_is_at A a then wk_fold_load k else idtac
      end
  end.

(* store hook: the store target is writable by wm_store_ok *)
Ltac wk_solve_store_world :=
  wk_idx_prep_store;
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) ?B] |- _ =>
          wk_facts;
          let k := wk_offset A a in
          wk_in_range k n;
          rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
          rewrite (wm_store_ok segs A m B k n a H) by first [ wk_side | wk_addr_eq ];
          cbv beta iota
      end
  end.

(* after a world store: the world hypothesis becomes upd B k bs about the new memory; store_done (Lib/Tac.v:358-401)
   then updates mem_inv, carries the other hypotheses and the footprint across the store and names the memory.
   RKw (k inside the world) is in the context while store_done runs, so its lia side goals see the offset's range
   even when the walk states the index bound by name. *)
Ltac wk_world_after_store :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
      match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) ?B] |- _ =>
          let k := wk_offset A a in
          lazymatch bs with
          | le8 _ => idtac | le4 _ => idtac | le2 _ => idtac | le1 _ => idtac
          | cons _ nil => idtac | put _ _ => idtac
          | _ => wk_no_open_bv bs
          end;
          let n := lazymatch bs with
                   | le8 _ => constr:(8%nat) | le4 _ => constr:(4%nat)
                   | le2 _ => constr:(2%nat) | le1 _ => constr:(1%nat)
                   | cons _ nil => constr:(1%nat)
                   | put ?w _ => w
                   | _ => eval vm_compute in (length bs)
                   end in
          wk_in_range k n;
          wk_facts;
          let E := addr_expr a in
          let RK := fresh "RKw" in
          assert (RK : 0 <= k /\ k + Z.of_nat n <= W_LEN) by (split; wk_side);
          let HS := fresh "HSw" in
          assert (HS : store_ok segs m (wa E) (length bs) = true)
            by (apply (wm_store_ok segs A m B k); [exact H | wk_side | wk_len_side | wk_addr_eq]);
          let H' := fresh "WMw" in
          assert (H' : rw_cells segs (write_to_mem m (wa E) bs) A [CB (Z.to_nat W_LEN) (upd B k bs)])
            by (apply (wm_write_at segs A m B k bs E);
                [ exact H | wk_side | wk_len_side | first [ reflexivity | lia | wk_zside | wk_vm_close ] ]);
          clear H;
          store_done;
          clear RK;
          rewrite ?le8_put, ?le4_put, ?le2_put, ?le1_put in H';
          lazymatch E with Z.add A _ => wk_fold_store k H' | _ => idtac end
      end
  end.

(* Lib/Step.v:493-523 (solve_store), verbatim. *)
Ltac wk_solve_store_kit :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

(* Lib/Tac.v:149-156 (mem_after_store_opt after its fix_lit_store), verbatim. *)
Ltac wk_mem_after_store_opt_kit :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Ltac wk_solve_load := first [ wk_solve_load_world | solve_load_base | solve_load_image ].
Ltac wk_solve_store := first [ wk_solve_store_world | wk_solve_store_kit ].
Ltac wk_mem_after_store_opt := try fix_lit_store; first [ wk_world_after_store | wk_mem_after_store_opt_kit ].

Ltac solve_load ::= wk_solve_load.
Ltac solve_store ::= wk_solve_store.
Ltac mem_after_store_opt ::= wk_mem_after_store_opt.

(* The side goals of wm_fill_out. X = A + k: by syntax, by lia, or by computation when both sides are CLOSED
   (wk_zval refuses an open term, so vm_compute never sees a Z_to_bv 64 <open>). *)
Ltac wk_fill_eq :=
  first [ reflexivity | lia | wk_zside
        | lazymatch goal with |- @eq Z ?L ?R =>
            let l := wk_zval L in let r := wk_zval R in vm_compute; reflexivity end ].

(* k + Z.of_nat c <= W_LEN, also for a cell of size [length (sub B k n)] (wm_cell's form); H is the world. *)
Ltac wk_fill_len H :=
  first [ wk_side
        | (rewrite length_sub; [ wk_side | wk_side | rewrite (wm_len _ _ _ _ H); wk_side ]) ].

(* Every world byte outside the out cell is outside each span of the footprint: the out cell's own span by the
   hypothesis, the callee's stack window by w_off_stack (or any bound in the context), another cell by its bounds. *)
Ltac wk_fill_out_side :=
  let x := fresh "x" in let Hx := fresh "Hx" in let Hc := fresh "Hc" in
  intros x Hx Hc; cbn [outside]; try unfold w_off_stack in *;
  repeat split;
  first [ lia | (unfold W_LEN in *; lia)
        | (rewrite ?unsigned_lit by (unfold W_LEN in *; lia); unfold W_LEN in *; lia) ].

(* Fail loudly when a span of the footprint W starts at a CLOSED address inside the world (computed by wk_zval). *)
Ltac wk_spans_hit_world A W :=
  lazymatch W with
  | nil => idtac
  | cons (?X, _) ?W' =>
      let inr := match X with
                 | _ => let Av := wk_zval A in let Xv := wk_zval X in
                        eval vm_compute in (andb (Z.leb Av Xv) (Z.ltb Xv (Av + W_LEN)))
                 | _ => constr:(false)
                 end in
      lazymatch inr with
      | true => fail 100 "wk_post_call: the callee writes inside the world but its post could not be folded into the world"
      | _ => wk_spans_hit_world A W'
      end
  end.

(* The world misses a callee's footprint W (a memset / memcpy into the stack, a callee that leaves the world alone
   but does not restate it): disjoint_from W A W_LEN. The callee's addresses are often still wrapped
   (memset_post's [bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -88))]); each is unwrapped by unsigned_lit with lia
   (the register ranges posed by wk_word_ranges, the stack window above the world by w_off_stack), never by
   computation. *)
Ltac wk_word_ranges :=
  repeat match goal with
  | |- context [bv_unsigned ?w] =>
      is_var w;
      lazymatch goal with
      | _ : 0 <= bv_unsigned w < 2 ^ 64 |- _ => fail
      | _ => pose proof (wk_word_range w)
      end
  end.
Ltac wk_unlit :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by (unfold W_LEN in *; lia)
  end.
Ltac wk_disj_side :=
  rewrite ?wm_size; cbn [disjoint_from]; try unfold w_off_stack in *;
  wk_word_ranges; wk_unlit;
  repeat split; first [ exact I | lia | (unfold W_LEN in *; lia) ].

(* After a call: a callee that returns the world (its post has wmem_at about m') replaces the old world; a callee
   that filled an out cell [X, X + c) inside the world with bytes src is folded in by wm_fill_out, whatever other
   spans its footprint has (memcpy / memset: the one span; diginet_frame_build: its stack window and the out cell);
   a callee whose footprint misses the world (wk_disj_side) leaves it as it was. Runs before transport_after_call,
   which would otherwise drop the world (it overlaps the callee's footprint, or slia cannot read a wrapped callee
   address). *)
Ltac wk_world_after_call segs m m' :=
  try match goal with
      | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) _], H2 : rw_cells segs m' ?A [CB (Z.to_nat W_LEN) _] |- _ => clear H
      end;
  repeat match goal with
  | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) ?B],
    MU : munch ?W m m',
    WMo : wmono segs m m',
    D : rw_cells segs m' ?X [CB ?c ?src] |- _ =>
      footprint_starts_at W X;
      let k := wk_offset A (Z_to_bv 64 X) in
      let H' := fresh "WMc" in
      assert (H' : rw_cells segs m' A [CB (Z.to_nat W_LEN) (upd B k src)])
        by (apply (wm_fill_out segs A m m' B W X k c src H MU WMo D);
            [ wk_fill_eq | wk_side | wk_fill_len H | wk_fill_out_side ]);
      clear H D
  end;
  try match goal with
  | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) ?B], MU : munch ?W m m', WMo : wmono segs m m' |- _ =>
      let H' := fresh "WMk" in
      assert (H' : rw_cells segs m' A [CB (Z.to_nat W_LEN) B])
        by (apply (rw_cells_transport segs W m m' A _ H MU WMo); wk_disj_side);
      clear H; rename H' into H
  end;
  try match goal with
  | H : rw_cells segs m ?A [CB (Z.to_nat W_LEN) _], MU : munch ?W m m' |- _ => wk_spans_hit_world A W
  end.

(* Lib/Tac.v:228-248 (post_call) with the world step before transport_after_call. *)
Ltac wk_post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  try destruct_ands PO;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      wk_facts;
      wk_world_after_call segs m m';
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "wcall" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | wk_post_call segs m ]
  end.

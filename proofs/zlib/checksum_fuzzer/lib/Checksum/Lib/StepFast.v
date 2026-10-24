(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Stepl9h.
From Stdlib Require Uint63.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Import Bool.
Unset Lia Cache.
Unset Nia Cache.
Import Ltac2.Bool.BoolNotations.
Import ListNotations.
Open Scope bv_scope.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sf_evt_step : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w i sz ms1,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
  lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro w i sz ms1 Hf He Hd Hx K.
  eapply evt_step; [ | exact K ]. split; [reflexivity|].
  rewrite (step_gen segs R F pc fc rv m ro w i sz Hf He Hd). exact Hx.
Qed.

(* [comment removed for export] *)
Lemma sf_evt_step_w : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w ms1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  match decode_any w with
  | Some (i, sz) => lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1
  | None => False
  end ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro w ms1 Hf He Hx K. destruct (decode_any w) as [[i sz]|] eqn:Hd; [|contradiction].
  exact (sf_evt_step segs Q R F pc fc rv m ro w i sz ms1 Hf He Hd Hx K).
Qed.

(* [comment removed for export] *)
Definition sf_w32 (n : PrimInt63.int) : bv 32 := Z_to_bv 32 (Uint63.to_Z n).
Definition sf_fetch_ok (segs : list Segment) (pc : word) (n : PrimInt63.int) : bool :=
  match fetch_word segs pc with
  | Some w => andb (Z.eqb (bv_unsigned w) (Uint63.to_Z n)) (negb (is_ecall w))
  | None => false
  end.
Lemma sf_evt_step_n : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro n ms1,
  sf_fetch_ok segs pc n = true ->
  match decode_any (sf_w32 n) with
  | Some (i, sz) => lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1
  | None => False
  end ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro n ms1 Hf Hx K. unfold sf_fetch_ok in Hf.
  destruct (fetch_word segs pc) as [w|] eqn:Hw; [|discriminate].
  apply Bool.andb_true_iff in Hf. destruct Hf as [E Ec]. apply Z.eqb_eq in E. apply Bool.negb_true_iff in Ec.
  assert (Ew : sf_w32 n = w) by (unfold sf_w32; rewrite <- E; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned).
  rewrite Ew in Hx. exact (sf_evt_step_w segs Q R F pc fc rv m ro w ms1 Hw Ec Hx K).
Qed.

(* [comment removed for export] *)
Definition sf_fetch_dec_ok (segs : list Segment) (pc : word) (n : PrimInt63.int) (i : instr) (sz : Z) : bool :=
  andb (sf_fetch_ok segs pc n) (bool_decide (decode_any (sf_w32 n) = Some (i, sz))).
Lemma sf_evt_step_d : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro n i sz ms1,
  sf_fetch_dec_ok segs pc n i sz = true ->
  lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro n i sz ms1 Hf Hx K. unfold sf_fetch_dec_ok in Hf.
  apply Bool.andb_true_iff in Hf. destruct Hf as [Hf Hd]. apply bool_decide_eq_true_1 in Hd.
  apply (sf_evt_step_n segs Q R F pc fc rv m ro n ms1 Hf); [| exact K]. rewrite Hd. exact Hx.
Qed.

(* [comment removed for export] *)
Definition sf_load_goal segs (m : word -> option byte) (a : word) (n : nat) (f : list byte -> word) : option word :=
  match ov_read_bytes segs m a n with Some bs => Some (f bs) | None => None end.

Lemma sf_install_load : forall segs (ro m : word -> option byte) (a : word) (n : nat) (f : list byte -> word) (v : word)
    (K : word -> machine_result (core * (word -> option byte))) (r : machine_result machine_state),
  sf_load_goal segs m a n f = Some v ->
  lift_result ro (K v) = r ->
  lift_result ro (match ov_read_bytes segs m a n with Some bs => K (f bs) | None => MachineFault end) = r.
Proof.
  intros segs ro m a n f v K r H1 H2. unfold sf_load_goal in H1. destruct (ov_read_bytes segs m a n); [|discriminate].
  injection H1 as <-. exact H2.
Qed.

(* [comment removed for export] *)
Definition sf_store_goal segs (m : word -> option byte) (a : word) (n : nat) (bs : list byte) : option (word -> option byte) :=
  if store_ok segs m a n then Some (write_to_mem m a bs) else None.

Lemma sf_install_store : forall segs (ro m : word -> option byte) (a : word) (n : nat) (bs : list byte)
    (m' : word -> option byte) (K : (word -> option byte) -> machine_result (core * (word -> option byte)))
    (r : machine_result machine_state),
  sf_store_goal segs m a n bs = Some m' ->
  lift_result ro (K m') = r ->
  lift_result ro (if store_ok segs m a n then K (write_to_mem m a bs) else MachineFault) = r.
Proof.
  intros segs ro m a n bs m' K r H1 H2. unfold sf_store_goal in H1. destruct (store_ok segs m a n); [|discriminate].
  injection H1 as <-. exact H2.
Qed.


(* [comment removed for export] *)
Lemma sf_load8_direct : forall segs (m : word -> option byte) A cs kn (v a : word),
  rw_cells segs m A cs -> cell_at cs kn = Some (C8 v) -> a = wa (A + Z.of_nat kn) ->
  sf_load_goal segs m a 8 (fun bs => @bv_extract 64 0 64 (le_bytes_to_word bs)) = Some v.
Proof.
  intros segs m A cs kn v a H Hc Ha. unfold sf_load_goal.
  rewrite (rw_cells_read_at segs m A cs kn (C8 v) 8 a H Hc eq_refl Ha). cbn [cbytes]. rewrite load_u64. reflexivity.
Qed.
Lemma sf_store8_direct : forall segs (m : word -> option byte) A cs kn c0 (a v : word),
  rw_cells segs m A cs -> cell_at cs kn = Some c0 -> 8%nat = csize c0 -> a = wa (A + Z.of_nat kn) ->
  sf_store_goal segs m a 8 (Z_to_le_bytes 8 (@bv_unsigned 64 v)) = Some (write_to_mem m (wa (A + Z.of_nat kn)) (le8 v)).
Proof.
  intros segs m A cs kn c0 a v H Hc Hn Ha. unfold sf_store_goal.
  rewrite (rw_cells_store_ok_at segs m A cs kn c0 8 a H Hc Hn Ha). rewrite store_bytes_8', Ha. reflexivity.
Qed.
Lemma sf_store8_direct0 : forall segs (m : word -> option byte) A cs kn c0 (a : word),
  rw_cells segs m A cs -> cell_at cs kn = Some c0 -> 8%nat = csize c0 -> a = wa (A + Z.of_nat kn) ->
  sf_store_goal segs m a 8 (Z_to_le_bytes 8 (@bv_unsigned 64 w0)) = Some (write_to_mem m (wa (A + Z.of_nat kn)) (Z_to_le_bytes 8 0)).
Proof.
  intros segs m A cs kn c0 a H Hc Hn Ha. unfold sf_store_goal.
  rewrite (rw_cells_store_ok_at segs m A cs kn c0 8 a H Hc Hn Ha). rewrite Ha. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma sf_ad1 : forall X c1 c2 n, c1 = (c2 + Z.of_nat n)%Z -> (X + c1 = X + c2 + Z.of_nat n)%Z.
Proof. intros X c1 c2 n ->. apply Z.add_assoc. Qed.
Lemma sf_ad2 : forall X c1 n, c1 = Z.of_nat n -> (X + c1 = X + Z.of_nat n)%Z.
Proof. intros X c1 n ->. reflexivity. Qed.
Lemma sf_ad3 : forall X c2 n, 0%Z = (c2 + Z.of_nat n)%Z -> (X = X + c2 + Z.of_nat n)%Z.
Proof. intros X c2 n H. rewrite <- Z.add_assoc, <- H. symmetry. apply Z.add_0_r. Qed.
Lemma sf_ad4 : forall X n, 0%Z = Z.of_nat n -> (X = X + Z.of_nat n)%Z.
Proof. intros X n H. rewrite <- H. symmetry. apply Z.add_0_r. Qed.
(* [comment removed for export] *)
Lemma sf_addr_ztobv : forall (a : word) E e, a = Z_to_bv 64 E -> E = e -> a = wa e.
Proof. intros a E e -> ->. reflexivity. Qed.
Lemma sf_addr_var : forall (a x : word) e, a = x -> bv_unsigned x = e -> a = wa e.
Proof. intros a x e -> H. symmetry. apply wa_of_var. exact H. Qed.

(* [comment removed for export] *)
Definition sf_exec_abs (sz : Z) (i : instr) (R0 F0 : bvmap 5 word) (PC0 : word) (FC0 : bv 32) (RV0 : option word) : eff :=
  exec (Z_to_bv 64 sz) i (Core R0 F0 PC0 FC0 RV0).

(* [comment removed for export] *)
Lemma sf_evt_mem : forall segs (Q : machine_state -> Prop) R F pc fc rv (m m' ro : word -> option byte),
  m = m' -> evt segs Q (MS R F pc fc rv m' ro) -> evt segs Q (MS R F pc fc rv m ro).
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma sf_btgt : forall (p t : Z) (n : N) (imm : bv n), t = (p + bv_signed imm)%Z ->
  (Z_to_bv 64 p + sext 64 imm : word) = Z_to_bv 64 t.
Proof.
  intros p t n imm ->. rewrite b_addsext. unfold v_addi. apply unsigned_Z_to_bv_add.
Qed.

Lemma sf_branch_pc : forall (b : bool) (p t f sz : Z) (n : N) (imm : bv n),
  t = (p + bv_signed imm)%Z -> f = (p + sz)%Z ->
  (if b then Z_to_bv 64 p + sext 64 imm else Z_to_bv 64 p + Z_to_bv 64 sz : word) =
  (if b then Z_to_bv 64 t else Z_to_bv 64 f).
Proof.
  intros b p t f sz n imm Ht Hf. rewrite (sf_btgt p t n imm Ht), lit_add_lit, <- Hf. reflexivity.
Qed.

(* [comment removed for export] *)
Section Cong.
  Local Notation MR := (machine_result machine_state).
  Definition sf_cong1 (f : word -> MR) x1 y1 (H1 : x1 = y1) : f x1 = f y1 :=
    match H1 in _ = y return f x1 = f y with eq_refl => eq_refl end.
  Definition sf_cong2 (f : word -> word -> MR) x1 y1 x2 y2 (H1 : x1 = y1) (H2 : x2 = y2) : f x1 x2 = f y1 y2 :=
    eq_trans (sf_cong1 (fun a => f a x2) x1 y1 H1) (sf_cong1 (fun b => f y1 b) x2 y2 H2).
  Definition sf_cong3 (f : word -> word -> word -> MR) x1 y1 x2 y2 x3 y3 (H1 : x1 = y1) (H2 : x2 = y2) (H3 : x3 = y3)
    : f x1 x2 x3 = f y1 y2 y3 :=
    eq_trans (sf_cong2 (fun a b => f a b x3) x1 y1 x2 y2 H1 H2) (sf_cong1 (fun c => f y1 y2 c) x3 y3 H3).
  Definition sf_cong4 (f : word -> word -> word -> word -> MR) x1 y1 x2 y2 x3 y3 x4 y4
      (H1 : x1 = y1) (H2 : x2 = y2) (H3 : x3 = y3) (H4 : x4 = y4) : f x1 x2 x3 x4 = f y1 y2 y3 y4 :=
    eq_trans (sf_cong3 (fun a b c => f a b c x4) x1 y1 x2 y2 x3 y3 H1 H2 H3) (sf_cong1 (fun d => f y1 y2 y3 d) x4 y4 H4).
  Definition sf_cong5 (f : word -> word -> word -> word -> word -> MR) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5
      (H1 : x1 = y1) (H2 : x2 = y2) (H3 : x3 = y3) (H4 : x4 = y4) (H5 : x5 = y5) : f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5 :=
    eq_trans (sf_cong4 (fun a b c d => f a b c d x5) x1 y1 x2 y2 x3 y3 x4 y4 H1 H2 H3 H4) (sf_cong1 (fun e => f y1 y2 y3 y4 e) x5 y5 H5).
  Definition sf_refl (x : MR) : x = x := eq_refl.
  Definition sf_transMR (x y z : MR) (H1 : x = y) (H2 : y = z) : x = z := eq_trans H1 H2.
  (* [comment removed for export] *)
  Definition sf_congT {T : Type} (f : T -> MR) (x y : T) (H : x = y) : f x = f y :=
    match H in _ = y' return f x = f y' with eq_refl => eq_refl end.
End Cong.
Definition sf_trans {A : Type} (x y z : A) (H1 : x = y) (H2 : y = z) : x = z := eq_trans H1 H2.

(* [comment removed for export] *)
Section CongR.
  Local Notation MR := (machine_result machine_state).
  Variables (R : tree word) (F : bvmap 5 word) (fc : bv 32) (rv : option word) (m ro : word -> option byte).
  Lemma sf_cr0pc : forall (pc pc' : word), pc = pc' -> (MachineOk (MS R F pc fc rv m ro) : MR) = MachineOk (MS R F pc' fc rv m ro).
  Proof. intros pc pc' ->. reflexivity. Qed.
  Lemma sf_cr1 : forall p1 (pc x1 y1 : word), x1 = y1 ->
    (MachineOk (MS (tset p1 x1 R) F pc fc rv m ro) : MR) = MachineOk (MS (tset p1 y1 R) F pc fc rv m ro).
  Proof. intros p1 pc x1 y1 ->. reflexivity. Qed.
  Lemma sf_cr2 : forall p1 p2 (pc x1 y1 x2 y2 : word), (x1, x2) = (y1, y2) ->
    (MachineOk (MS (tset p2 x2 (tset p1 x1 R)) F pc fc rv m ro) : MR) = MachineOk (MS (tset p2 y2 (tset p1 y1 R)) F pc fc rv m ro).
  Proof. intros p1 p2 pc x1 y1 x2 y2 H. injection H as -> ->. reflexivity. Qed.
  Lemma sf_cr3 : forall p1 p2 p3 (pc x1 y1 x2 y2 x3 y3 : word), (x1, (x2, x3)) = (y1, (y2, y3)) ->
    (MachineOk (MS (tset p3 x3 (tset p2 x2 (tset p1 x1 R))) F pc fc rv m ro) : MR) = MachineOk (MS (tset p3 y3 (tset p2 y2 (tset p1 y1 R))) F pc fc rv m ro).
  Proof. intros p1 p2 p3 pc x1 y1 x2 y2 x3 y3 H. injection H as -> -> ->. reflexivity. Qed.
  Lemma sf_cr1pc : forall p1 (x1 y1 pc pc' : word), (x1, pc) = (y1, pc') ->
    (MachineOk (MS (tset p1 x1 R) F pc fc rv m ro) : MR) = MachineOk (MS (tset p1 y1 R) F pc' fc rv m ro).
  Proof. intros p1 x1 y1 pc pc' H. injection H as -> ->. reflexivity. Qed.
  Lemma sf_cr2pc : forall p1 p2 (x1 y1 x2 y2 pc pc' : word), (x1, (x2, pc)) = (y1, (y2, pc')) ->
    (MachineOk (MS (tset p2 x2 (tset p1 x1 R)) F pc fc rv m ro) : MR) = MachineOk (MS (tset p2 y2 (tset p1 y1 R)) F pc' fc rv m ro).
  Proof. intros p1 p2 x1 y1 x2 y2 pc pc' H. injection H as -> -> ->. reflexivity. Qed.
  Lemma sf_cr3pc : forall p1 p2 p3 (x1 y1 x2 y2 x3 y3 pc pc' : word), (x1, (x2, (x3, pc))) = (y1, (y2, (y3, pc'))) ->
    (MachineOk (MS (tset p3 x3 (tset p2 x2 (tset p1 x1 R))) F pc fc rv m ro) : MR) = MachineOk (MS (tset p3 y3 (tset p2 y2 (tset p1 y1 R))) F pc' fc rv m ro).
  Proof. intros p1 p2 p3 x1 y1 x2 y2 x3 y3 pc pc' H. injection H as -> -> -> ->. reflexivity. Qed.
End CongR.

(* [comment removed for export] *)
Lemma sfx_tset_tget {A} (p : positive) (x : A) (t : tree A) : tget p t = Some x -> tset p x t = t.
Proof.
  revert t; induction p; intros [|l v r] H; cbn in H |- *; try discriminate; try (rewrite (IHp _ H); reflexivity).
  subst v; reflexivity.
Qed.
Section SfxR.
  Variables (segs : list Segment) (Q : machine_state -> Prop) (R : tree word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (rv : option word)
            (m ro : word -> option byte) (nw : PrimInt63.int) (i : instr) (sz : Z).
  Local Notation RUN := (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F (Z_to_bv 64 pc) fc rv)) m).
  Local Notation PRE := (MS R F (Z_to_bv 64 pc) fc rv m ro).
  Hypothesis Hf : sf_fetch_dec_ok segs (Z_to_bv 64 pc) nw i sz = true.

  Local Ltac pre E K :=
    lazymatch type of E with _ = MachineOk (?c, ?m') =>
      apply (sf_evt_step_d segs Q R F (Z_to_bv 64 pc) fc rv m ro nw i sz (MS_of_core c m' ro) Hf); [ rewrite E; reflexivity | exact K ]
    end.

  (* [comment removed for export] *)
  Lemma sfx_cr0 : match RUN with MachineOk (c, m') =>
      evt segs Q (MS (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I. intros K. pre E K. Qed.
  Lemma sfx_cr0pc : forall pc' : word, match RUN with MachineOk (c, m') =>
      c_pc c = pc' -> evt segs Q (MS (c_regs c) (c_fregs c) pc' (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof. intros pc'. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I. intros <- K. pre E K. Qed.

  (* [comment removed for export] *)
  Lemma sfx_cr1 : forall p1 (y1 : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c) with Some x1 => x1 = y1 | None => False end ->
      evt segs Q (MS (tset p1 y1 (c_regs c)) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 y1. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T; [| intros []]. intros <- K. rewrite (sfx_tset_tget _ _ _ T) in K. destruct c; pre E K.
  Qed.
  Lemma sfx_cr1pc : forall p1 (y1 pc' : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c) with Some x1 => (x1, c_pc c) = (y1, pc') | None => False end ->
      evt segs Q (MS (tset p1 y1 (c_regs c)) (c_fregs c) pc' (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 y1 pc'. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T; [| intros []]. intros H K. injection H as <- <-. rewrite (sfx_tset_tget _ _ _ T) in K. destruct c; pre E K.
  Qed.
  Lemma sfx_cr1pf : forall p1 (y1 pc' : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c) with Some x1 => x1 = y1 | None => False end -> c_pc c = pc' ->
      evt segs Q (MS (tset p1 y1 (c_regs c)) (c_fregs c) pc' (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 y1 pc'. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T; [| intros []]. intros <- <- K. rewrite (sfx_tset_tget _ _ _ T) in K. destruct c; pre E K.
  Qed.

  (* [comment removed for export] *)
  Lemma sfx_cr2 : forall p1 p2 (y1 y2 : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c), tget p2 (c_regs c) with Some x1, Some x2 => (x1, x2) = (y1, y2) | _, _ => False end ->
      evt segs Q (MS (tset p2 y2 (tset p1 y1 (c_regs c))) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 p2 y1 y2. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T1; [| intros []]. destruct (tget p2 (c_regs c)) as [x2|] eqn:T2; [| intros []].
    intros H K. injection H as <- <-. rewrite (sfx_tset_tget _ _ _ T1), (sfx_tset_tget _ _ _ T2) in K. destruct c; pre E K.
  Qed.
  Lemma sfx_cr2pc : forall p1 p2 (y1 y2 pc' : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c), tget p2 (c_regs c) with Some x1, Some x2 => (x1, (x2, c_pc c)) = (y1, (y2, pc')) | _, _ => False end ->
      evt segs Q (MS (tset p2 y2 (tset p1 y1 (c_regs c))) (c_fregs c) pc' (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 p2 y1 y2 pc'. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T1; [| intros []]. destruct (tget p2 (c_regs c)) as [x2|] eqn:T2; [| intros []].
    intros H K. injection H as <- <- <-. rewrite (sfx_tset_tget _ _ _ T1), (sfx_tset_tget _ _ _ T2) in K. destruct c; pre E K.
  Qed.
  Lemma sfx_cr2pf : forall p1 p2 (y1 y2 pc' : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c), tget p2 (c_regs c) with Some x1, Some x2 => (x1, x2) = (y1, y2) | _, _ => False end -> c_pc c = pc' ->
      evt segs Q (MS (tset p2 y2 (tset p1 y1 (c_regs c))) (c_fregs c) pc' (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 p2 y1 y2 pc'. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T1; [| intros []]. destruct (tget p2 (c_regs c)) as [x2|] eqn:T2; [| intros []].
    intros H <- K. injection H as <- <-. rewrite (sfx_tset_tget _ _ _ T1), (sfx_tset_tget _ _ _ T2) in K. destruct c; pre E K.
  Qed.

  (* [comment removed for export] *)
  Lemma sfx_cr3 : forall p1 p2 p3 (y1 y2 y3 : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c), tget p2 (c_regs c), tget p3 (c_regs c) with Some x1, Some x2, Some x3 => (x1, (x2, x3)) = (y1, (y2, y3)) | _, _, _ => False end ->
      evt segs Q (MS (tset p3 y3 (tset p2 y2 (tset p1 y1 (c_regs c)))) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 p2 p3 y1 y2 y3. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T1; [| intros []]. destruct (tget p2 (c_regs c)) as [x2|] eqn:T2; [| intros []].
    destruct (tget p3 (c_regs c)) as [x3|] eqn:T3; [| intros []].
    intros H K. injection H as <- <- <-. rewrite (sfx_tset_tget _ _ _ T1), (sfx_tset_tget _ _ _ T2), (sfx_tset_tget _ _ _ T3) in K. destruct c; pre E K.
  Qed.
  Lemma sfx_cr3pc : forall p1 p2 p3 (y1 y2 y3 pc' : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c), tget p2 (c_regs c), tget p3 (c_regs c) with Some x1, Some x2, Some x3 => (x1, (x2, (x3, c_pc c))) = (y1, (y2, (y3, pc'))) | _, _, _ => False end ->
      evt segs Q (MS (tset p3 y3 (tset p2 y2 (tset p1 y1 (c_regs c)))) (c_fregs c) pc' (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 p2 p3 y1 y2 y3 pc'. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T1; [| intros []]. destruct (tget p2 (c_regs c)) as [x2|] eqn:T2; [| intros []].
    destruct (tget p3 (c_regs c)) as [x3|] eqn:T3; [| intros []].
    intros H K. injection H as <- <- <- <-. rewrite (sfx_tset_tget _ _ _ T1), (sfx_tset_tget _ _ _ T2), (sfx_tset_tget _ _ _ T3) in K. destruct c; pre E K.
  Qed.
  Lemma sfx_cr3pf : forall p1 p2 p3 (y1 y2 y3 pc' : word), match RUN with MachineOk (c, m') =>
      match tget p1 (c_regs c), tget p2 (c_regs c), tget p3 (c_regs c) with Some x1, Some x2, Some x3 => (x1, (x2, x3)) = (y1, (y2, y3)) | _, _, _ => False end -> c_pc c = pc' ->
      evt segs Q (MS (tset p3 y3 (tset p2 y2 (tset p1 y1 (c_regs c)))) (c_fregs c) pc' (c_fcsr c) (c_resv c) m' ro) -> evt segs Q PRE | _ => True end.
  Proof.
    intros p1 p2 p3 y1 y2 y3 pc'. destruct (interp_eff0 _ _ _) as [[c m']| |] eqn:E; try exact I.
    destruct (tget p1 (c_regs c)) as [x1|] eqn:T1; [| intros []]. destruct (tget p2 (c_regs c)) as [x2|] eqn:T2; [| intros []].
    destruct (tget p3 (c_regs c)) as [x3|] eqn:T3; [| intros []].
    intros H <- K. injection H as <- <- <-. rewrite (sfx_tset_tget _ _ _ T1), (sfx_tset_tget _ _ _ T2), (sfx_tset_tget _ _ _ T3) in K. destruct c; pre E K.
  Qed.
End SfxR.

(* [comment removed for export] *)
Lemma sfx_tset_tset {A} (p : positive) (x y : A) (t : tree A) : tset p x (tset p y t) = tset p x t.
Proof. revert t; induction p; intros [|l v r]; cbn; try rewrite IHp; reflexivity. Qed.
Lemma sfx_some_inj {A} (a b : A) : Some a = Some b -> a = b.
Proof. intros H; injection H as H; exact H. Qed.
(* [comment removed for export] *)
Definition sfx_kval (rd : bv 5) (e : eff) : word := match e with EDone c => rget c rd | _ => w0 end.
Section SfxLS.
  Variables (segs : list Segment) (Q : machine_state -> Prop) (R : tree word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (rv : option word)
            (m ro : word -> option byte) (nw : PrimInt63.int) (i : instr) (sz : Z).
  Local Notation CORE := (Core R F (Z_to_bv 64 pc) fc rv).
  Local Notation PRE := (MS R F (Z_to_bv 64 pc) fc rv m ro).
  Hypothesis Hf : sf_fetch_dec_ok segs (Z_to_bv 64 pc) nw i sz = true.

  Lemma sfx_ld0 : forall (v : word),
    match i with
    | Load _ _ rd _ _ =>
        if is_x0 rd then True else
        match exec (Z_to_bv 64 sz) i CORE with
        | ELoad n a k =>
            sf_load_goal segs m a (width_bytes n) (fun bs => sfx_kval rd (k (bv_extract 0 n (le_bytes_to_word bs)))) = Some v ->
            match k (Z_to_bv n 0) with
            | EDone c => evt segs Q (MS (bvmap_set rd v (c_regs c)) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m ro) -> evt segs Q PRE
            | _ => True
            end
        | _ => True
        end
    | _ => True
    end.
  Proof.
    intros v. destruct i; try exact I.
    match goal with |- if ?b then _ else _ => destruct b eqn:X0; [exact I|] end.
    cbv beta iota zeta delta [exec load_val].
    destruct sz0; cbv beta iota; intros H; unfold rset; rewrite X0; cbn [with_regs with_pc c_regs c_fregs c_pc c_fcsr c_resv]; intros K;
      unfold sf_load_goal in H.
    all: match type of H with match ?o with _ => _ end = _ => destruct o as [bs|] eqn:RB; [|discriminate] end; injection H as H;
      cbv beta iota delta [sfx_kval rset] in H; rewrite X0 in H; unfold rget in H; rewrite X0 in H; unfold reg_get, with_regs, with_pc, c_regs in H;
      rewrite bvmap_get_set_same in H.
    all: eapply (sf_evt_step_d segs Q R F (Z_to_bv 64 pc) fc rv m ro nw _ sz _ Hf); [ | exact K ];
      cbv beta iota zeta delta [exec load_val]; cbn [interp_eff0]; rewrite RB; cbv beta iota delta [interp_eff0 rset]; rewrite X0;
      cbv beta iota delta [lift_result MS_of_core with_regs with_pc c_regs c_fregs c_pc c_fcsr c_resv]; rewrite H;
      unfold bvmap_set; rewrite sfx_tset_tset; reflexivity.
  Qed.

  Lemma sfx_st0 : forall (mn : word -> option byte),
    match i with
    | Store _ _ _ _ =>
        match exec (Z_to_bv 64 sz) i CORE with
        | EStore n a vb k =>
            sf_store_goal segs m a (width_bytes n) (Z_to_le_bytes (width_bytes n) (bv_unsigned vb)) = Some mn ->
            match k with
            | EDone c => evt segs Q (MS (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) mn ro) -> evt segs Q PRE
            | _ => True
            end
        | _ => True
        end
    | _ => True
    end.
  Proof.
    intros mn. destruct i; try exact I.
    cbv beta iota zeta delta [exec store_val].
    destruct sz0; cbv beta iota; intros H K; cbv beta delta [sf_store_goal] in H.
    all: match type of H with (if ?o then _ else _) = _ => destruct o eqn:SB; [|discriminate] end; cbv iota in H; apply sfx_some_inj in H.
    all: eapply (sf_evt_step_d segs Q R F (Z_to_bv 64 pc) fc rv m ro nw _ sz _ Hf); [ | exact K ];
      cbv beta iota zeta delta [exec store_val]; cbn [interp_eff0]; rewrite SB; cbv beta iota delta [interp_eff0 lift_result MS_of_core]; rewrite H; reflexivity.
  Qed.
End SfxLS.
(* [comment removed for export] *)
Lemma sf_install_load_r : forall segs (ro m : word -> option byte) (a : word) (n : nat) (f : list byte -> word) (v : word)
    (rd : bv 5) (R : bvmap 5 word) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (r : machine_result machine_state),
  sf_load_goal segs m a n f = Some v ->
  lift_result ro (MachineOk (Core (@bvmap_set 5 word rd v R) F pc fc rv, m)) = r ->
  lift_result ro (match ov_read_bytes segs m a n with
                  | Some bs => MachineOk (Core (@bvmap_set 5 word rd (f bs) R) F pc fc rv, m)
                  | None => MachineFault end) = r.
Proof.
  intros segs ro m a n f v rd R F pc fc rv r.
  exact (sf_install_load segs ro m a n f v (fun x => MachineOk (Core (@bvmap_set 5 word rd x R) F pc fc rv, m)) r).
Qed.
Lemma sf_install_store_r : forall segs (ro m : word -> option byte) (a : word) (n : nat) (bs : list byte) (m' : word -> option byte)
    (R : bvmap 5 word) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (r : machine_result machine_state),
  sf_store_goal segs m a n bs = Some m' ->
  lift_result ro (MachineOk (Core R F pc fc rv, m')) = r ->
  lift_result ro (if store_ok segs m a n then MachineOk (Core R F pc fc rv, write_to_mem m a bs) else MachineFault) = r.
Proof.
  intros segs ro m a n bs m' R F pc fc rv r.
  exact (sf_install_store segs ro m a n bs m' (fun x => MachineOk (Core R F pc fc rv, x)) r).
Qed.
Definition sf_pair_eq1 {A B : Type} (a a' : A) (b b' : B) (H : (a, b) = (a', b')) : a = a' :=
  f_equal fst H.
Definition sf_pair_eq2 {A B : Type} (a a' : A) (b b' : B) (H : (a, b) = (a', b')) : b = b' :=
  f_equal snd H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SF_probe {A : Type} (x : A) : Prop := True.

Ltac2 Type exn ::= [ SF_Captured (constr, (ident * constr option * constr) list) ].

Ltac2 sf_fail (s : string) := Control.zero (Tactic_failure (Some (Message.of_string s))).

(* [comment removed for export] *)
Ltac2 sf_get (a : 'a array) (i : int) : 'a :=
  if Int.lt i (Array.length a) then (if Int.le 0 i then Array.get a i else sf_fail "index") else sf_fail "index".

Ltac2 mutable sf_debug : bool := false.
Ltac2 mutable sf_timing : bool := false.
Ltac2 mutable sf_check : bool := false.
(* [comment removed for export] *)
Ltac2 mutable sf_decvm : bool := true.
(* [comment removed for export] *)
Ltac2 mutable sfx_on : bool := false.
(* [comment removed for export] *)
Ltac2 mutable sfx_ls : bool := true.
Ltac2 mutable sf_stop : int := 100.
Ltac2 stop (k : int) : unit := if Int.le sf_stop k then Control.zero Not_found else ().
Ltac2 rec strip_cast (c : constr) : constr :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Cast c' _ _ => strip_cast c' | _ => c end.
Ltac2 tm (s : string) (f : unit -> 'a) : 'a := if sf_timing then Control.time (Some s) f else f ().

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 kof (r : Std.reference) : constant :=
  match r with Std.ConstRef k => k | _ => sf_fail "kof" end.
Ltac2 cof (r : Std.reference) : constructor :=
  match r with Std.ConstructRef k => k | _ => sf_fail "cof" end.

(* [comment removed for export] *)
Ltac2 is_k (k : constant) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant k' _ => Constant.equal k k'
  | _ => false
  end.
Ltac2 is_c (k : constructor) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor k' _ => Constructor.equal k k'
  | _ => false
  end.
Ltac2 app_of_k (k : constant) (c : constr) : constr array option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => if is_k k f then Some args else None
  | _ => None
  end.
Ltac2 app_of_c (k : constructor) (c : constr) : constr array option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => if is_c k f then Some args else None
  | _ => None
  end.

Ltac2 is_app_of (h : constr) (c : constr) : constr array option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => if Constr.equal f h then Some args else None
  | _ => None
  end.

Ltac2 const_k (c : constr) : constant :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant k _ => k
  | _ => sf_fail "const_k"
  end.

(* [comment removed for export] *)
Ltac2 rec is_pos_lit (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true     (* [comment removed for export] *)
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor _ _ => if Int.equal (Array.length args) 1 then is_pos_lit (Array.get args 0) else false
      | _ => false
      end
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 is_zlit (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor _ _ => if Int.equal (Array.length args) 1 then is_pos_lit (sf_get args 0) else false
      | _ => false
      end
  | _ => false
  end.

(* [comment removed for export] *)
Definition sf_word : Set := bv 64.
(* [comment removed for export] *)
Ltac2 mutable sf_regw : bool := true.
Ltac2 rec sf_retype (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 4 then
        (if Constr.equal h '@TNode then
           let o := Array.get args 2 in
           let o' := match Constr.Unsafe.kind o with
                     | Constr.Unsafe.App ho oargs =>
                         if Int.equal (Array.length oargs) 2 then
                           (if Constr.equal ho '@Some then Constr.Unsafe.make (Constr.Unsafe.App ho [| 'sf_word; Array.get oargs 1 |]) else o)
                         else if Int.equal (Array.length oargs) 1 then
                           (if Constr.equal ho '@None then Constr.Unsafe.make (Constr.Unsafe.App ho [| 'sf_word |]) else o)
                         else o
                     | _ => o
                     end in
           Constr.Unsafe.make (Constr.Unsafe.App h [| 'sf_word; sf_retype (Array.get args 1); o'; sf_retype (Array.get args 3) |])
         else t)
      else if Int.equal (Array.length args) 1 then
        (if Constr.equal h '@TEmpty then Constr.Unsafe.make (Constr.Unsafe.App h [| 'sf_word |]) else t)
      else t
  | _ => t
  end.

(* [comment removed for export] *)
Ltac2 is_concrete_map (r : constr) : bool :=
  match Constr.Unsafe.kind r with
  | Constr.Unsafe.App f args =>
      if Constr.equal f '@TNode then true
      else if Constr.equal f '@mkR then Int.equal (Array.length args) 31
      else false
  | Constr.Unsafe.Constructor _ _ => false
  | _ => false
  end ||
  (match Constr.Unsafe.kind r with
   | Constr.Unsafe.App f args => if Constr.equal f '@TEmpty then Int.equal (Array.length args) 1 else false
   | _ => false
   end).

(* [comment removed for export] *)
Ltac2 rec map_closed (f : constr -> constr option) (c : constr) : constr :=
  match f c with
  | Some c' => c'
  | None => Constr.Unsafe.map (map_closed f) c
  end.

(* [comment removed for export] *)
Ltac2 is_lit_app (cbv_ : constructor) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor k _ => if Constructor.equal k cbv_ then true else is_pos_lit c
      | _ => false
      end
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.

Ltac2 rec map_closed_nolit (cbv_ : constructor) (f : constr -> constr option) (c : constr) : constr :=
  if is_lit_app cbv_ c then c else
  match f c with
  | Some c' => c'
  | None => Constr.Unsafe.map (map_closed_nolit cbv_ f) c
  end.

(* [comment removed for export] *)
Ltac2 rec pos_int (c : constr) : int :=
  lazy_match! c with
  | xH => 1
  | xO ?p => Int.mul 2 (pos_int p)
  | xI ?p => Int.add 1 (Int.mul 2 (pos_int p))
  end.
Ltac2 reg_int (r : constr) : int option :=
  match Constr.Unsafe.kind r with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 3 then
        let z := sf_get args 1 in
        if Constr.equal z 'Z0 then Some 0 else
        lazy_match! z with
        | Zpos ?p => Some (pos_int p)
        | _ => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 zlit_int (c : constr) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => Some 0
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then
        match Constr.Unsafe.kind f with
        | Constr.Unsafe.Constructor k _ =>
            if Constructor.equal k (cof reference:(Zpos)) then Some (pos_int (Array.get args 0))
            else if Constructor.equal k (cof reference:(Zneg)) then Some (Int.sub 0 (pos_int (Array.get args 0)))
            else None
        | _ => None
        end
      else None
  | _ => None
  end.
Ltac2 rec pos_of_int (n : int) : constr :=
  if Int.le n 1 then Env.instantiate reference:(xH)
  else if Int.equal (Int.mod n 2) 0 then Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(xO)) [| pos_of_int (Int.div n 2) |])
  else Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(xI)) [| pos_of_int (Int.div n 2) |]).
Ltac2 int_zlit (n : int) : constr :=
  if Int.equal n 0 then Env.instantiate reference:(Z0)
  else if Int.lt 0 n then Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(Zpos)) [| pos_of_int n |])
  else Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(Zneg)) [| pos_of_int (Int.sub 0 n) |]).
(* [comment removed for export] *)
Ltac2 nlit_int (c : constr) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => Some 0
  | Constr.Unsafe.App _ args => if Int.equal (Array.length args) 1 then Some (pos_int (Array.get args 0)) else None
  | _ => None
  end.
Ltac2 rec ipow2 (k : int) : int := if Int.le k 0 then 1 else Int.mul 2 (ipow2 (Int.sub k 1)).
(* [comment removed for export] *)
Ltac2 imm_signed (imm : constr) : int option :=
  match Constr.Unsafe.kind imm with
  | Constr.Unsafe.App _ args =>
      if Int.equal (Array.length args) 3 then
        match nlit_int (Array.get args 0), zlit_int (Array.get args 1) with
        | Some n, Some z =>
            if Int.le n 32 then
              (if Int.le 1 n then
                 (if Int.lt z (ipow2 (Int.sub n 1)) then Some z else Some (Int.sub z (ipow2 n)))
               else None)
            else None
        | _, _ => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 x0_sub (kx0 : constant) (c : constr) : constr option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if is_k kx0 f then
        match reg_int (sf_get args 0) with
        | Some n => if Int.equal n 0 then Some 'true else Some 'false
        | None =>
            let r := sf_get args 0 in
            if Constr.Unsafe.is_closed r then Some (eval vm_compute in (is_x0 $r)) else None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 exec_abs (sz : constr) (i : constr) (f : constr) (pc : constr) (fc : constr) (rv : constr) : constr :=
  let t0 := Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(sf_exec_abs)) [| sz; i |]) in
  let t := eval cbv beta iota zeta delta [sf_exec_abs exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s is_x0 bv_unsigned Z.eqb] in $t0 in
  (* [comment removed for export] *)
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda b1 t1 =>
      match Constr.Unsafe.kind t1 with
      | Constr.Unsafe.Lambda _ t2 =>
          match Constr.Unsafe.kind t2 with
          | Constr.Unsafe.Lambda _ t3 =>
              match Constr.Unsafe.kind t3 with
              | Constr.Unsafe.Lambda _ t4 =>
                  match Constr.Unsafe.kind t4 with
                  | Constr.Unsafe.Lambda _ body =>
                      (* [comment removed for export] *)
                      let body := Constr.Unsafe.substnl [rv; fc; '(Z_to_bv 64 $pc); f] 0 body in
                      let lam := Constr.Unsafe.make (Constr.Unsafe.Lambda b1 body) in
                      let lam := eval cbv beta iota in $lam in
                      match Constr.Unsafe.kind lam with
                      | Constr.Unsafe.Lambda _ body => body
                      | _ => sf_fail "exec_abs"
                      end
                  | _ => sf_fail "exec_abs"
                  end
              | _ => sf_fail "exec_abs"
              end
          | _ => sf_fail "exec_abs"
          end
      | _ => sf_fail "exec_abs"
      end
  | _ => sf_fail "exec_abs"
  end.

(* [comment removed for export] *)
Ltac2 rec pos_path (p : constr) : bool list :=
  (* [comment removed for export] *)
  lazy_match! p with
  | xH => []
  | xO ?q => false :: pos_path q
  | xI ?q => true :: pos_path q
  end.

Ltac2 rec tree_get (path : bool list) (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 4 then
        match path with
        | [] => lazy_match! (sf_get args 2) with Some ?v => v | _ => sf_fail "tree_get: empty leaf" end
        | d :: path' => if d then tree_get path' (sf_get args 3) else tree_get path' (sf_get args 1)
        end
      else sf_fail "tree_get: TEmpty"
  | _ => sf_fail "tree_get: not a tree"
  end.

Ltac2 rec tree_set_ (csome : constr) (path : bool list) (v : constr) (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 4 then
        match path with
        | [] =>
            let ty := sf_get args 0 in
            Constr.Unsafe.make (Constr.Unsafe.App h [| ty; sf_get args 1; Constr.Unsafe.make (Constr.Unsafe.App csome [| ty; v |]); sf_get args 3 |])
        | d :: path' =>
            if d then Constr.Unsafe.make (Constr.Unsafe.App h [| sf_get args 0; sf_get args 1; sf_get args 2; tree_set_ csome path' v (sf_get args 3) |])
            else Constr.Unsafe.make (Constr.Unsafe.App h [| sf_get args 0; tree_set_ csome path' v (sf_get args 1); sf_get args 2; sf_get args 3 |])
        end
      else sf_fail "tree_set: TEmpty"
  | _ => sf_fail "tree_set: not a tree"
  end.

Ltac2 tree_set (path : bool list) (v : constr) (t : constr) : constr := tree_set_ '@Some path v t.

(* [comment removed for export] *)
Ltac2 rec tree_leaves (t : constr) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 4 then
        let vs := match Constr.Unsafe.kind (sf_get args 2) with
                  | Constr.Unsafe.App _ sargs => if Int.equal (Array.length sargs) 2 then [sf_get sargs 1] else []
                  | _ => []
                  end in
        List.append (tree_leaves (sf_get args 1)) (List.append vs (tree_leaves (sf_get args 3)))
      else []
  | _ => []
  end.

(* [comment removed for export] *)
Ltac2 rec int_path (p : int) : bool list :=
  if Int.le p 1 then [] else
  let b := Int.equal (Int.mod p 2) 1 in b :: int_path (Int.div p 2).
Ltac2 key_path (k : constr) : bool list :=
  match reg_int k with
  | Some n => int_path (Int.add n 1)
  | None => let p := eval vm_compute in (bv_key $k) in pos_path p
  end.

(* [comment removed for export] *)
Ltac2 is_c_app (f : constr) : bool :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.Constructor k _ =>
      (* [comment removed for export] *)
      if Constructor.equal k (cof reference:(BV)) then true
      else if Constructor.equal k (cof reference:(Zpos)) then true
      else if Constructor.equal k (cof reference:(Zneg)) then true
      else if Constructor.equal k (cof reference:(Npos)) then true
      else false
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec resolve (kget : constant) (kset : constant) (ru : constr) (d : int) (c : constr) (hit : bool ref) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if is_c_app f then c else
      let args := Array.map (fun a => resolve kget kset ru d a hit) args in
      if is_k kget f then
        match Constr.Unsafe.kind (sf_get args 0) with
        | Constr.Unsafe.Rel n =>
            if Int.equal n (Int.add 1 d) then
              (hit.(contents) := true; tree_get (key_path (sf_get args 1)) ru)
            else Constr.Unsafe.make (Constr.Unsafe.App f args)
        | _ => Constr.Unsafe.make (Constr.Unsafe.App f args)
        end
      else if is_k kset f then
        (* [comment removed for export] *)
        if Int.equal (Array.length args) 5 then
          match Constr.Unsafe.kind (sf_get args 4) with
          | Constr.Unsafe.Rel n =>
              if Int.equal n (Int.add 1 d) then
                if Int.equal d 0 then
                  (hit.(contents) := true; tree_set (key_path (sf_get args 2)) (sf_get args 3) ru)
                else Constr.Unsafe.make (Constr.Unsafe.App f args)
              else Constr.Unsafe.make (Constr.Unsafe.App f args)
          | _ => Constr.Unsafe.make (Constr.Unsafe.App f args)
          end
        else Constr.Unsafe.make (Constr.Unsafe.App f args)
      else Constr.Unsafe.make (Constr.Unsafe.App (resolve kget kset ru d f hit) args)
  | Constr.Unsafe.Lambda b body => Constr.Unsafe.make (Constr.Unsafe.Lambda b (resolve kget kset ru (Int.add d 1) body hit))
  | Constr.Unsafe.Case ci ret iv scr brs =>
      Constr.Unsafe.make (Constr.Unsafe.Case ci ret iv (resolve kget kset ru d scr hit) (Array.map (fun br => resolve kget kset ru d br hit) brs))
  | _ => c
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 const_set (l : Std.reference list) : constant FSet.t :=
  List.fold_left (fun s r => match r with Std.ConstRef k => FSet.add k s | _ => s end)
    (FSet.empty FSet.Tags.constant_tag) l.

Ltac2 bad_consts () : constant FSet.t := const_set [
  reference:(lift_result); reference:(interp_eff0); reference:(exec); reference:(with_pc); 
  reference:(with_regs); reference:(with_fregs); reference:(with_fcsr); reference:(with_resv); 
  reference:(rget); reference:(rset); reference:(fget); reference:(fset); reference:(c_regs); 
  reference:(c_fregs); reference:(c_pc); reference:(c_fcsr); reference:(c_resv); reference:(MS_of_core); 
  reference:(load_val); reference:(store_val); reference:(branch_taken); reference:(inval_resv); 
  reference:(width_bytes); reference:(accrue); reference:(fari_d); reference:(fcmp_d); reference:(fari_s); 
  reference:(fcmp_s); reference:(is_x0); reference:(reg_get); reference:(tget); reference:(tset); 
  reference:(cbytes); reference:(alu64); reference:(alu32); reference:(mul_div); 
  
  
  reference:(Z_to_le_bytes); reference:(v_addi); reference:(v_add); reference:(v_sub); reference:(v_mul); 
  reference:(v_andi); reference:(v_ori); reference:(v_xori); reference:(v_and); reference:(v_or); 
  reference:(v_xor); reference:(v_slli); reference:(v_srli); reference:(v_srai); reference:(v_sll); 
  reference:(v_srl); reference:(v_sra); reference:(v_lui); reference:(v_auipc); reference:(v_addiw); 
  reference:(v_slliw); reference:(v_srliw); reference:(v_sraiw); reference:(v_addw); reference:(v_subw); 
  reference:(v_sllw); reference:(v_srlw); reference:(v_sraw); reference:(v_mulh); reference:(v_mulhsu); 
  reference:(v_mulhu); reference:(v_mulw); reference:(btgt); reference:(w0); reference:(w1) ].

Ltac2 bad_consts_z () : constant FSet.t := const_set [
  reference:(zxb); reference:(v_sltu); reference:(v_slt); reference:(v_sltiu); reference:(v_slti) ].

Ltac2 inert_heads () : constant FSet.t := const_set [
  reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.opp); reference:(Z.land); reference:(Z.lor);
  reference:(Z.lxor); reference:(Z.shiftl); reference:(Z.shiftr); reference:(Z.b2z); reference:(Z.of_nat); reference:(Z.pow);
  reference:(Z.div); reference:(Z.quot); reference:(Z.rem); reference:(Z.abs); reference:(Z.min); reference:(Z.max);
  reference:(bv_signed); reference:(bv_swrap); reference:(Z.to_nat); reference:(Z.sgn); reference:(Z.ones); reference:(Z.lnot) ].
Ltac2 sp_consts () : constant FSet.t := const_set [
  reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.shiftl); reference:(Z.shiftr);
  reference:(Z.land); reference:(Z.lor); reference:(Z.lxor); reference:(Z.modulo); reference:(Z.pow);
  reference:(bv_unsigned); reference:(bv_signed); reference:(bv_wrap); reference:(bv_swrap); reference:(Z_to_bv);
  reference:(ret_pc); reference:(low32); reference:(nan_box); reference:(bv_add); reference:(bv_and);
  reference:(sext); reference:(zext); reference:(bvmap_set); reference:(bv_extract) ].
Ltac2 Type sf_ctx := {
  bc : constant FSet.t;  bcz : constant FSet.t;  zm : bool;
  k_zadd : constant; k_zsub : constant; k_zmul : constant; k_zshl : constant; k_zshr : constant; k_zland : constant;
  k_zlor : constant; k_zlxor : constant; k_zmod : constant; k_zpow : constant;
  k_unsigned : constant; k_signed : constant; k_wrap : constant; k_swrap : constant; k_ztobv : constant; k_retpc : constant;
  k_concat : constant; k_extract : constant; k_sext : constant; k_zext : constant; k_low32 : constant; k_nanbox : constant;
  k_lebw : constant; k_le8 : constant; k_le4 : constant; k_le2 : constant; k_le1 : constant;
  k_bvset : constant; k_mkr : constant; c_tnode : constructor; c_tempty : constructor;
  k_bvadd : constant; k_bvand : constant; k_bvnot : constant;
  c_z0 : constructor; c_cons : constructor; c_n64 : constr; c_n32 : constr;
  c_zpos : constructor;
  sp_k : constant FSet.t;   (* [comment removed for export] *)
  idioms_seen : bool ref;
  uz_seen : bool ref;   (* [comment removed for export] *)
  inert : constant FSet.t;
  qmode : bool ref;     (* [comment removed for export] *)
  lit_delta : bool ref  (* [comment removed for export] *)
}.

Ltac2 mk_ctx (z : bool) : sf_ctx := {
  bc := bad_consts (); bcz := bad_consts_z (); zm := z;
  k_zadd := kof reference:(Z.add); k_zsub := kof reference:(Z.sub); k_zmul := kof reference:(Z.mul);
  k_zshl := kof reference:(Z.shiftl); k_zshr := kof reference:(Z.shiftr);
  k_zland := kof reference:(Z.land); k_zlor := kof reference:(Z.lor); k_zlxor := kof reference:(Z.lxor);
  k_zmod := kof reference:(Z.modulo); k_zpow := kof reference:(Z.pow);
  k_unsigned := kof reference:(bv_unsigned); k_signed := kof reference:(bv_signed); k_wrap := kof reference:(bv_wrap);
  k_swrap := kof reference:(bv_swrap); k_ztobv := kof reference:(Z_to_bv); k_retpc := kof reference:(ret_pc);
  k_concat := kof reference:(bv_concat); k_extract := kof reference:(bv_extract); k_sext := kof reference:(sext);
  k_zext := kof reference:(zext); k_low32 := kof reference:(low32); k_nanbox := kof reference:(nan_box);
  k_lebw := kof reference:(le_bytes_to_word); k_le8 := kof reference:(le8); k_le4 := kof reference:(le4);
  k_le2 := kof reference:(le2); k_le1 := kof reference:(le1);
  k_bvset := kof reference:(bvmap_set); k_mkr := kof reference:(mkR);
  c_tnode := cof reference:(TNode); c_tempty := cof reference:(TEmpty);
  k_bvadd := kof reference:(bv_add); k_bvand := kof reference:(bv_and); k_bvnot := kof reference:(bv_not);
  c_z0 := cof reference:(Z0); c_cons := cof reference:(cons); c_n64 := '(64%N); c_n32 := '(32%N);
  c_zpos := cof reference:(Zpos); sp_k := sp_consts ();
  idioms_seen := { contents := false }; uz_seen := { contents := false }; inert := inert_heads ();
  qmode := { contents := false }; lit_delta := { contents := false } }.

(* [comment removed for export] *)
Ltac2 ctx_mode (x : sf_ctx) (z : bool) : sf_ctx := {
  bc := x.(bc); bcz := x.(bcz); zm := z;
  k_zadd := x.(k_zadd); k_zsub := x.(k_zsub); k_zmul := x.(k_zmul); k_zshl := x.(k_zshl); k_zshr := x.(k_zshr);
  k_zland := x.(k_zland); k_zlor := x.(k_zlor); k_zlxor := x.(k_zlxor); k_zmod := x.(k_zmod); k_zpow := x.(k_zpow);
  k_unsigned := x.(k_unsigned); k_signed := x.(k_signed); k_wrap := x.(k_wrap); k_swrap := x.(k_swrap);
  k_ztobv := x.(k_ztobv); k_retpc := x.(k_retpc); k_concat := x.(k_concat); k_extract := x.(k_extract);
  k_sext := x.(k_sext); k_zext := x.(k_zext); k_low32 := x.(k_low32); k_nanbox := x.(k_nanbox);
  k_lebw := x.(k_lebw); k_le8 := x.(k_le8); k_le4 := x.(k_le4); k_le2 := x.(k_le2); k_le1 := x.(k_le1);
  k_bvset := x.(k_bvset); k_mkr := x.(k_mkr); c_tnode := x.(c_tnode); c_tempty := x.(c_tempty);
  k_bvadd := x.(k_bvadd); k_bvand := x.(k_bvand); k_bvnot := x.(k_bvnot);
  c_z0 := x.(c_z0); c_cons := x.(c_cons); c_n64 := x.(c_n64); c_n32 := x.(c_n32);
  c_zpos := x.(c_zpos); sp_k := x.(sp_k);
  idioms_seen := { contents := false }; uz_seen := { contents := false }; inert := x.(inert);
  qmode := { contents := false }; lit_delta := x.(lit_delta) }.

(* [comment removed for export] *)
Ltac2 ctx_fresh (x : sf_ctx) : sf_ctx := {
  bc := x.(bc); bcz := x.(bcz); zm := x.(zm);
  k_zadd := x.(k_zadd); k_zsub := x.(k_zsub); k_zmul := x.(k_zmul); k_zshl := x.(k_zshl); k_zshr := x.(k_zshr);
  k_zland := x.(k_zland); k_zlor := x.(k_zlor); k_zlxor := x.(k_zlxor); k_zmod := x.(k_zmod); k_zpow := x.(k_zpow);
  k_unsigned := x.(k_unsigned); k_signed := x.(k_signed); k_wrap := x.(k_wrap); k_swrap := x.(k_swrap);
  k_ztobv := x.(k_ztobv); k_retpc := x.(k_retpc); k_concat := x.(k_concat); k_extract := x.(k_extract);
  k_sext := x.(k_sext); k_zext := x.(k_zext); k_low32 := x.(k_low32); k_nanbox := x.(k_nanbox);
  k_lebw := x.(k_lebw); k_le8 := x.(k_le8); k_le4 := x.(k_le4); k_le2 := x.(k_le2); k_le1 := x.(k_le1);
  k_bvset := x.(k_bvset); k_mkr := x.(k_mkr); c_tnode := x.(c_tnode); c_tempty := x.(c_tempty);
  k_bvadd := x.(k_bvadd); k_bvand := x.(k_bvand); k_bvnot := x.(k_bvnot);
  c_z0 := x.(c_z0); c_cons := x.(c_cons); c_n64 := x.(c_n64); c_n32 := x.(c_n32);
  c_zpos := x.(c_zpos); sp_k := x.(sp_k);
  idioms_seen := { contents := false }; uz_seen := { contents := false }; inert := x.(inert);
  qmode := { contents := (x.(qmode)).(contents) }; lit_delta := { contents := false } }.

Ltac2 is_constructor_app (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App f _ => match Constr.Unsafe.kind f with Constr.Unsafe.Constructor _ _ => true | _ => false end
  | _ => false
  end.

Ltac2 head_k (k : constant) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => is_k k f
  | _ => false
  end.

Ltac2 head_c (k : constructor) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => is_c k f
  | _ => false
  end.

Ltac2 app_args (c : constr) : constr array :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App _ a => a
  | _ => [| |]
  end.

Ltac2 arg_last (c : constr) : constr := let a := app_args c in sf_get a (Int.sub (Array.length a) 1).

Ltac2 both_lit (a : constr) (b : constr) : bool := if is_zlit a then is_zlit b else false.

(* [comment removed for export] *)
Ltac2 rec pos_depth_ge (c : constr) (n : int) : bool :=
  if Int.le n 1 then true else
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App _ args => if Int.equal (Array.length args) 1 then pos_depth_ge (Array.get args 0) (Int.sub n 1) else false
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 zlit_ge_2_64 (x : sf_ctx) (b : constr) : bool :=
  match Constr.Unsafe.kind b with
  | Constr.Unsafe.App f args => if is_c (x.(c_zpos)) f then pos_depth_ge (sf_get args 0) 65 else false
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 ztobv_lit (x : sf_ctx) (c : constr) : bool :=
  if head_k (x.(k_ztobv)) c then is_zlit (arg_last c) else false.

(* [comment removed for export] *)
Ltac2 le_list_redex (x : sf_ctx) (bs : constr) : bool :=
  if head_k (x.(k_le8)) bs then true else if head_k (x.(k_le4)) bs then true
  else if head_k (x.(k_le2)) bs then true else if head_k (x.(k_le1)) bs then true
  else head_c (x.(c_cons)) bs.
(* [comment removed for export] *)
Ltac2 extract_redex (x : sf_ctx) (c : constr) : bool :=
  if head_k (x.(k_extract)) c then
    (let b := arg_last c in if head_k (x.(k_lebw)) b then le_list_redex x (arg_last b) else false)
  else false.

(* [comment removed for export] *)
Ltac2 suspicious (x : sf_ctx) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => match Control.hyp_value id with Some _ => true | None => false end
  | Constr.Unsafe.Constant k _ => if Constant.equal k (x.(k_ztobv)) then false else true
  | Constr.Unsafe.App f _ =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant k _ => if Constant.equal k (x.(k_ztobv)) then false else true
      | Constr.Unsafe.Var id => match Control.hyp_value id with Some _ => true | None => false end
      | _ => false
      end
  | _ => false
  end.
Ltac2 could_be_ztobv (x : sf_ctx) (t : constr) : bool := if head_k (x.(k_ztobv)) t then true else suspicious x t.
Ltac2 could_be_sext (x : sf_ctx) (t : constr) : bool := if head_k (x.(k_sext)) t then true else suspicious x t.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 unsigned64_possible (x : sf_ctx) (u : constr) : bool :=
  let a := app_args u in
  if Int.equal (Array.length a) 2 then
    (let w := Array.get a 0 in
     if Constr.equal w (x.(c_n64)) then true
     else Bool.neg (match Constr.Unsafe.kind w with
                    | Constr.Unsafe.Constructor _ _ => true
                    | Constr.Unsafe.App f args =>
                        (match Constr.Unsafe.kind f with
                         | Constr.Unsafe.Constructor _ _ => if Int.equal (Array.length args) 1 then is_pos_lit (Array.get args 0) else false
                         | _ => false
                         end)
                    | _ => false
                    end))
  else true.
Ltac2 unsigned_ztobv (x : sf_ctx) (u : constr) : bool :=
  if head_k (x.(k_unsigned)) u then (if unsigned64_possible x u then could_be_ztobv x (arg_last u) else false) else false.

(* [comment removed for export] *)
Ltac2 rec u_red_risky (x : sf_ctx) (inert : constant FSet.t) (fuel : int) (u : constr) : bool :=
  if Int.le fuel 0 then true else
  match Constr.Unsafe.kind (match Constr.Unsafe.kind u with Constr.Unsafe.App f _ => f | _ => u end) with
  | Constr.Unsafe.Constant k _ =>
      if Constant.equal k (x.(k_zmod)) then true
      else if Constant.equal k (x.(k_wrap)) then true
      else if Constant.equal k (x.(k_unsigned)) then (if unsigned64_possible x u then could_be_ztobv x (arg_last u) else false)
      else if FSet.mem k inert then false
      else
        (match Control.case (fun () => eval red in $u) with
         | Val (u', _) => if Constr.equal u u' then false else u_red_risky x inert (Int.sub fuel 1) u'
         | Err _ => false   (* [comment removed for export] *)
         end)
  | Constr.Unsafe.Var id => match Control.hyp_value id with Some b => u_red_risky x inert (Int.sub fuel 1) b | None => false end
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 rec b_red_unsigned (x : sf_ctx) (fuel : int) (b : constr) : bool :=
  if Int.le fuel 0 then true else
  match Constr.Unsafe.kind (match Constr.Unsafe.kind b with Constr.Unsafe.App f _ => f | _ => b end) with
  | Constr.Unsafe.Constant k _ =>
      if Constant.equal k (x.(k_unsigned)) then unsigned64_possible x b
      else if FSet.mem k (x.(inert)) then false
      else if Constant.equal k (x.(k_zmod)) then false
      else if Constant.equal k (x.(k_wrap)) then false
      else
        (match Control.case (fun () => eval red in $b) with
         | Val (b', _) => if Constr.equal b b' then false else b_red_unsigned x (Int.sub fuel 1) b'
         | Err _ => false
         end)
  | Constr.Unsafe.Var id => match Control.hyp_value id with Some v => b_red_unsigned x (Int.sub fuel 1) v | None => false end
  | _ => false
  end.

Ltac2 u_risky (x : sf_ctx) (u : constr) : bool :=
  match Constr.Unsafe.kind u with
  | Constr.Unsafe.Var id => match Control.hyp_value id with Some _ => u_red_risky x (x.(inert)) 6 u | None => false end
  | Constr.Unsafe.App _ _ => if is_zlit u then false else u_red_risky x (x.(inert)) 6 u
  | Constr.Unsafe.Constant _ _ => u_red_risky x (x.(inert)) 6 u
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec risky (x : sf_ctx) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant k _ =>
           if Constant.equal k (x.(k_ztobv)) then
             (let b := arg_last t in
              if head_k (x.(k_zadd)) b then
                (let ab := app_args b in
                 let u0 := sf_get ab 0 in let u1 := sf_get ab 1 in
                 (if head_k (x.(k_unsigned)) u0 then suspicious x (arg_last u0) else u_risky x u0) ||
                 (if head_k (x.(k_unsigned)) u1 then suspicious x (arg_last u1) else u_risky x u1))
              else false)
           else if Constant.equal k (x.(k_bvadd)) then
             (let a := sf_get args 1 in let b := sf_get args 2 in
              if could_be_ztobv x a then (if could_be_ztobv x b then (suspicious x a || suspicious x b) else false) else false)
           else false
       | _ => false
       end) ||
      Array.exist (risky x) args
  | Constr.Unsafe.Lambda _ b => risky x b
  | Constr.Unsafe.Case _ _ _ scr brs => if risky x scr then true else Array.exist (risky x) brs
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 bad_app_o (x : sf_ctx) (k : constant) (args : constr array) : bool :=
  let n := Array.length args in
  if Int.equal n 2 then
    let a := sf_get args 0 in let b := sf_get args 1 in
    if Constant.equal k (x.(k_zadd)) then
      (* [comment removed for export] *)
      (if is_c (x.(c_z0)) b then true
       else if is_zlit b then (if is_zlit a then true else (if head_k (x.(k_zadd)) a then is_zlit (sf_get (app_args a) 1) else false))
       else false)
    else if Constant.equal k (x.(k_zsub)) then both_lit a b
    else if Constant.equal k (x.(k_zmul)) then both_lit a b
    else if Constant.equal k (x.(k_zshl)) then both_lit a b
    else if Constant.equal k (x.(k_zshr)) then
      ((x.(idioms_seen)).(contents) := true; both_lit a b)
    else if Constant.equal k (x.(k_zland)) then both_lit a b
    else if Constant.equal k (x.(k_zlor)) then both_lit a b
    else if Constant.equal k (x.(k_zlxor)) then both_lit a b
    else if Constant.equal k (x.(k_zmod)) then
      ((x.(idioms_seen)).(contents) := true; (if x.(zm) then both_lit a b else false))
    else if Constant.equal k (x.(k_zpow)) then (if x.(zm) then both_lit a b else false)
    else if Constant.equal k (x.(k_unsigned)) then
      (* [comment removed for export] *)
      ((if head_k (x.(k_ztobv)) b then (if Constr.equal (sf_get (app_args b) 0) (x.(c_n64)) then (x.(uz_seen)).(contents) := true else ()) else ());
       if is_constructor_app b then true
       else if head_k (x.(k_concat)) b then true
       else if head_k (x.(k_ztobv)) b then (if x.(zm) then true else is_zlit (arg_last b))
       else false)
    else if Constant.equal k (x.(k_signed)) then
      (if is_constructor_app b then true
       else if head_k (x.(k_concat)) b then true
       else ztobv_lit x b)
    else if Constant.equal k (x.(k_wrap)) then is_zlit b
    else if Constant.equal k (x.(k_swrap)) then is_zlit b
    else if Constant.equal k (x.(k_ztobv)) then
      (if Constr.equal a (x.(c_n64)) then
        (if head_k (x.(k_zadd)) b then
           (let ab := app_args b in
            if is_c (x.(c_z0)) (sf_get ab 1) then true
            (* [comment removed for export] *)
            else if unsigned_ztobv x (sf_get ab 0) then true
            else if unsigned_ztobv x (sf_get ab 1) then true
            else if u_risky x (sf_get ab 0) then true
            else u_risky x (sf_get ab 1))
         else if head_k (x.(k_unsigned)) b then Constr.equal (sf_get (app_args b) 0) (x.(c_n64))
         else if (match Constr.Unsafe.kind b with
                  | Constr.Unsafe.App f _ => (match Constr.Unsafe.kind f with Constr.Unsafe.Constant _ _ => true | Constr.Unsafe.Var _ => true | _ => false end)
                  | Constr.Unsafe.Var _ => true | Constr.Unsafe.Constant _ _ => true | _ => false end)
              then (if is_zlit b then false
                    else if (x.(qmode)).(contents) then
                      ((if b_red_unsigned x 6 b then (x.(lit_delta)).(contents) := true else ()); false)
                    else b_red_unsigned x 6 b)
         else if x.(zm) then
           (if head_k (x.(k_zmod)) b then true
            else if is_zlit b then (lazy_match! (eval vm_compute in (Z.leb 18446744073709551616 $b)) with true => true | _ => false end)
            else false)
         else false)
       else false)
    else false
  else if Int.equal n 1 then
    let a := sf_get args 0 in
    if Constant.equal k (x.(k_retpc)) then ztobv_lit x a
    else if Constant.equal k (x.(k_low32)) then ztobv_lit x a
    else if Constant.equal k (x.(k_nanbox)) then ztobv_lit x a
    else false
  else if Int.equal n 3 then
    (* [comment removed for export] *)
    if Constant.equal k (x.(k_bvadd)) then
      (let a := sf_get args 1 in let b := sf_get args 2 in
       (* [comment removed for export] *)
       if could_be_sext x b then true
       else if could_be_ztobv x a then could_be_ztobv x b else false)
    else if Constant.equal k (x.(k_bvand)) then
      (* [comment removed for export] *)
      head_k (x.(k_bvnot)) (sf_get args 2)
    else if Constant.equal k (x.(k_sext)) then
      (let b := sf_get args 2 in
       if ztobv_lit x b then true else if head_k (x.(k_concat)) b then true else extract_redex x b)
    else if Constant.equal k (x.(k_zext)) then
      (let b := sf_get args 2 in if ztobv_lit x b then true else extract_redex x b)
    else false
  else if Int.equal n 5 then
    (if Constant.equal k (x.(k_bvset)) then
       (* [comment removed for export] *)
       (let base := sf_get args 4 in
        if head_c (x.(c_tnode)) base then true
        else if head_c (x.(c_tempty)) base then true
        else if head_k (x.(k_mkr)) base then true
        else if head_k (x.(k_bvset)) base then
          (match reg_int (sf_get args 2), reg_int (sf_get (app_args base) 2) with
           | Some a, Some b => Int.ge a b
           | _, _ => true
           end)
        else false)
     else false)
  else if Int.equal n 4 then
    (if Constant.equal k (x.(k_extract)) then
      (let b := sf_get args 3 in if head_k (x.(k_lebw)) b then le_list_redex x (arg_last b) else false)
     else false)
  else false.

Ltac2 rec bad_o (x : sf_ctx) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant k _ =>
          if FSet.mem k (x.(bc)) then true
          else if (if x.(zm) then FSet.mem k (x.(bcz)) else false) then true
          else if bad_app_o x k args then true
          else bad_args_o x args 0 (Array.length args)
      | Constr.Unsafe.Constructor _ _ => bad_args_o x args 0 (Array.length args)
      | Constr.Unsafe.Lambda _ _ => true
      | _ => if bad_o x f then true else bad_args_o x args 0 (Array.length args)
      end
  | Constr.Unsafe.Constant k _ =>
      if FSet.mem k (x.(bc)) then true else (if x.(zm) then FSet.mem k (x.(bcz)) else false)
  | Constr.Unsafe.Lambda _ body => bad_o x body
  | Constr.Unsafe.LetIn _ _ _ => true
  | Constr.Unsafe.Case _ _ _ scr brs =>
      if is_constructor_app scr then true
      else if bad_o x scr then true else bad_args_o x brs 0 (Array.length brs)
  | Constr.Unsafe.Fix _ _ _ _ => true
  | Constr.Unsafe.CoFix _ _ _ => true
  | Constr.Unsafe.Proj _ _ _ => true
  | Constr.Unsafe.Evar _ _ => true
  | Constr.Unsafe.Cast c' _ _ => bad_o x c'
  | _ => false
  end
with bad_args_o x args i n :=
  if Int.equal i n then false
  else if bad_o x (sf_get args i) then true
  else bad_args_o x args (Int.add i 1) n.


(* [comment removed for export] *)
Ltac2 bad_app (x : sf_ctx) (k : constant) (args : constr array) : bool :=
  let n := Array.length args in
  if Int.equal n 2 then
    let a := sf_get args 0 in let b := sf_get args 1 in
    if Constant.equal k (x.(k_ztobv)) then
      (if Constr.equal a (x.(c_n64)) then
        (if head_k (x.(k_zadd)) b then
           (let ab := app_args b in
            if is_c (x.(c_z0)) (sf_get ab 1) then true
            (* [comment removed for export] *)
            else if unsigned_ztobv x (sf_get ab 0) then true
            else if unsigned_ztobv x (sf_get ab 1) then true
            else if u_risky x (sf_get ab 0) then true
            else u_risky x (sf_get ab 1))
         else if head_k (x.(k_unsigned)) b then Constr.equal (sf_get (app_args b) 0) (x.(c_n64))
         else if (match Constr.Unsafe.kind b with
                  | Constr.Unsafe.App f _ => (match Constr.Unsafe.kind f with Constr.Unsafe.Constant _ _ => true | Constr.Unsafe.Var _ => true | _ => false end)
                  | Constr.Unsafe.Var _ => true | Constr.Unsafe.Constant _ _ => true | _ => false end)
              then (if is_zlit b then false
                    else if (x.(qmode)).(contents) then
                      ((if b_red_unsigned x 6 b then (x.(lit_delta)).(contents) := true else ()); false)
                    else b_red_unsigned x 6 b)
         else if x.(zm) then
           (if head_k (x.(k_zmod)) b then true
            else if is_zlit b then zlit_ge_2_64 x b
            else false)
         else false)
       else false)
    else if Constant.equal k (x.(k_unsigned)) then
      (* [comment removed for export] *)
      ((if head_k (x.(k_ztobv)) b then (if Constr.equal (sf_get (app_args b) 0) (x.(c_n64)) then (x.(uz_seen)).(contents) := true else ()) else ());
       if is_constructor_app b then true
       else if head_k (x.(k_concat)) b then true
       else if head_k (x.(k_ztobv)) b then (if x.(zm) then true else is_zlit (arg_last b))
       else false)
    else if Constant.equal k (x.(k_zadd)) then
      (if is_c (x.(c_z0)) b then true          (* [comment removed for export] *)
       else if is_zlit b then (if is_zlit a then true else (if head_k (x.(k_zadd)) a then is_zlit (sf_get (app_args a) 1) else false))
       else false)
    else if Constant.equal k (x.(k_zsub)) then both_lit a b
    else if Constant.equal k (x.(k_zmul)) then both_lit a b
    else if Constant.equal k (x.(k_zshl)) then both_lit a b
    else if Constant.equal k (x.(k_zshr)) then
      ((x.(idioms_seen)).(contents) := true; both_lit a b)
    else if Constant.equal k (x.(k_zland)) then both_lit a b
    else if Constant.equal k (x.(k_zlor)) then both_lit a b
    else if Constant.equal k (x.(k_zlxor)) then both_lit a b
    else if Constant.equal k (x.(k_zmod)) then
      ((x.(idioms_seen)).(contents) := true; (if x.(zm) then both_lit a b else false))
    else if Constant.equal k (x.(k_zpow)) then (if x.(zm) then both_lit a b else false)
    else if Constant.equal k (x.(k_signed)) then
      (if is_constructor_app b then true
       else if head_k (x.(k_concat)) b then true
       else ztobv_lit x b)
    else if Constant.equal k (x.(k_wrap)) then is_zlit b
    else if Constant.equal k (x.(k_swrap)) then is_zlit b
    else false
  else if Int.equal n 1 then
    let a := sf_get args 0 in
    if Constant.equal k (x.(k_retpc)) then ztobv_lit x a
    else if Constant.equal k (x.(k_low32)) then ztobv_lit x a
    else if Constant.equal k (x.(k_nanbox)) then ztobv_lit x a
    else false
  else if Int.equal n 3 then
    (* [comment removed for export] *)
    if Constant.equal k (x.(k_bvadd)) then
      (let a := sf_get args 1 in let b := sf_get args 2 in
       (* [comment removed for export] *)
       if could_be_sext x b then true
       else if could_be_ztobv x a then could_be_ztobv x b else false)
    else if Constant.equal k (x.(k_bvand)) then
      (* [comment removed for export] *)
      head_k (x.(k_bvnot)) (sf_get args 2)
    else if Constant.equal k (x.(k_sext)) then
      (let b := sf_get args 2 in
       if ztobv_lit x b then true else if head_k (x.(k_concat)) b then true else extract_redex x b)
    else if Constant.equal k (x.(k_zext)) then
      (let b := sf_get args 2 in if ztobv_lit x b then true else extract_redex x b)
    else false
  else if Int.equal n 5 then
    (if Constant.equal k (x.(k_bvset)) then
       (* [comment removed for export] *)
       (let base := sf_get args 4 in
        if head_c (x.(c_tnode)) base then true
        else if head_c (x.(c_tempty)) base then true
        else if head_k (x.(k_mkr)) base then true
        else if head_k (x.(k_bvset)) base then
          (match reg_int (sf_get args 2), reg_int (sf_get (app_args base) 2) with
           | Some a, Some b => Int.ge a b
           | _, _ => true
           end)
        else false)
     else false)
  else if Int.equal n 4 then
    (if Constant.equal k (x.(k_extract)) then
      (let b := sf_get args 3 in if head_k (x.(k_lebw)) b then le_list_redex x (arg_last b) else false)
     else false)
  else false.

(* [comment removed for export] *)
Ltac2 rec lit_chain (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App f a =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor _ _ => if Int.equal (Array.length a) 1 then lit_chain (Array.get a 0) else false
      | _ => false
      end
  | _ => false
  end.
Ltac2 rec bad_n (x : sf_ctx) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant k _ =>
          if FSet.mem k (x.(bc)) then true
          else if (if x.(zm) then FSet.mem k (x.(bcz)) else false) then true
          else if (if FSet.mem k (x.(sp_k)) then bad_app x k args else false) then true
          else bad_args_n x args 0 (Array.length args)
      | Constr.Unsafe.Constructor _ _ =>
          (* [comment removed for export] *)
          if Int.equal (Array.length args) 1 then (if lit_chain (Array.get args 0) then false else bad_n x (Array.get args 0))
          else bad_args_n x args 0 (Array.length args)
      | Constr.Unsafe.Lambda _ _ => true
      | _ => if bad_n x f then true else bad_args_n x args 0 (Array.length args)
      end
  | Constr.Unsafe.Constant k _ =>
      if FSet.mem k (x.(bc)) then true else (if x.(zm) then FSet.mem k (x.(bcz)) else false)
  | Constr.Unsafe.Lambda _ body => bad_n x body
  | Constr.Unsafe.LetIn _ _ _ => true
  | Constr.Unsafe.Case _ _ _ scr brs =>
      if is_constructor_app scr then true
      else if bad_n x scr then true else bad_args_n x brs 0 (Array.length brs)
  | Constr.Unsafe.Fix _ _ _ _ => true
  | Constr.Unsafe.CoFix _ _ _ => true
  | Constr.Unsafe.Proj _ _ _ => true
  | Constr.Unsafe.Evar _ _ => true
  | Constr.Unsafe.Cast c' _ _ => bad_n x c'
  | _ => false
  end
with bad_args_n x args i n :=
  if Int.equal i n then false
  else if bad_n x (sf_get args i) then true
  else bad_args_n x args (Int.add i 1) n.



(* [comment removed for export] *)
Ltac2 mutable sf_badchk : bool := false.
Ltac2 bad (x : sf_ctx) (c : constr) : bool :=
  if sf_badchk then
    (let xo := ctx_fresh x in let xn := ctx_fresh x in
     let ro := bad_o xo c in let rn := bad_n xn c in
     (if (if Bool.equal ro rn then
            (if Bool.equal ((xo.(idioms_seen)).(contents)) ((xn.(idioms_seen)).(contents)) then
               (if Bool.equal ((xo.(uz_seen)).(contents)) ((xn.(uz_seen)).(contents)) then
                  Bool.equal ((xo.(lit_delta)).(contents)) ((xn.(lit_delta)).(contents)) else false) else false) else false)
      then () else printf "BADCHK-MISMATCH %t" c);
     (if (xn.(idioms_seen)).(contents) then (x.(idioms_seen)).(contents) := true else ());
     (if (xn.(uz_seen)).(contents) then (x.(uz_seen)).(contents) := true else ());
     (if (xn.(lit_delta)).(contents) then (x.(lit_delta)).(contents) := true else ());
     rn)
  else bad_n x c.

(* [comment removed for export] *)
Ltac2 rec has_litself (x : sf_ctx) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      (if is_k (x.(k_ztobv)) f then
         (if Int.equal (Array.length args) 2 then
            (if Constr.equal (Array.get args 0) (x.(c_n64)) then
               (let b := Array.get args 1 in
                if head_k (x.(k_unsigned)) b then Constr.equal (sf_get (app_args b) 0) (x.(c_n64)) else false)
             else false)
          else false)
       else false) || (if has_litself x f then true else Array.exist (has_litself x) args)
  | Constr.Unsafe.Lambda b body => if has_litself x (Constr.Binder.type b) then true else has_litself x body
  | Constr.Unsafe.Prod b body => if has_litself x (Constr.Binder.type b) then true else has_litself x body
  | Constr.Unsafe.LetIn b v body => if has_litself x v then true else has_litself x body
  | Constr.Unsafe.Case _ _ _ scr brs => if has_litself x scr then true else Array.exist (has_litself x) brs
  | Constr.Unsafe.Cast c' _ _ => has_litself x c'
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec bad_culprit (x : sf_ctx) (c : constr) : constr :=
  let ch := { contents := None } in
  (match Constr.Unsafe.kind c with
   | Constr.Unsafe.App f args => Array.iter (fun a => match ch.(contents) with None => if bad x a then ch.(contents) := Some a else () | Some _ => () end) args
   | Constr.Unsafe.Lambda _ b => if bad x b then ch.(contents) := Some b else ()
   | Constr.Unsafe.Case _ _ _ scr brs => if bad x scr then ch.(contents) := Some scr else Array.iter (fun a => match ch.(contents) with None => if bad x a then ch.(contents) := Some a else () | Some _ => () end) brs
   | _ => ()
   end);
  match ch.(contents) with Some a => bad_culprit x a | None => c end.

(* [comment removed for export] *)
Ltac sf_probe_idioms t := assert (SF_probe t) by (progress zs_idioms; exact I).
Ltac2 idioms_hit (t : constr) : bool :=
  match Control.case (fun () => let tv := Ltac1.of_constr t in ltac1:(tv |- sf_probe_idioms tv) tv; Control.zero Not_found) with
  | Val _ => true
  | Err e => match e with Not_found => true | _ => false end
  end.

Ltac2 rest_ok (z : bool) (l : constr list) : bool :=
  let x := tm "mk_ctx" (fun () => mk_ctx z) in
  if tm "bad" (fun () => List.exist (fun t => if bad x t then (if sf_debug then printf "STEPFAST-BADREST: %t" t else ()); true else false) l) then false
  else if z then
    (if (x.(idioms_seen)).(contents) then
       (if tm "idioms" (fun () => idioms_hit (List.fold_left (fun acc t => '(($acc, $t))) 'tt l)) then false else true)
     else true)
  else true.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 uz_safe_heads () : constant FSet.t := const_set [
  reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.opp); reference:(Z.land); reference:(Z.lor);
  reference:(Z.lxor); reference:(Z.shiftl); reference:(Z.shiftr); reference:(Z.modulo); reference:(Z.div); reference:(Z.quot);
  reference:(Z.rem); reference:(Z.pow); reference:(Z.b2z); reference:(Z.of_nat); reference:(Z.abs); reference:(Z.min);
  reference:(Z.max); reference:(Z.eqb); reference:(Z.ltb); reference:(Z.leb); reference:(negb); reference:(andb); reference:(orb);
  reference:(Z_to_le_bytes); reference:(bv_wrap); reference:(bv_swrap); reference:(Z.to_nat); reference:(Z.sgn);
  reference:(Z.ones); reference:(Z.lnot); reference:(Z.of_N) ].
(* [comment removed for export] *)
Ltac2 uz_wsafe_heads () : constant FSet.t := const_set [
  reference:(bv_unsigned); reference:(bv_signed); reference:(Lib.Mem.le8); reference:(Lib.Mem.le4);
  reference:(Lib.Mem.le2); reference:(Lib.Mem.le1) ].

(* [comment removed for export] *)
Ltac2 rec uz_red_sum (x : sf_ctx) (safe : constant FSet.t) (rgt : bool) (fuel : int) (b : constr) : bool :=
  if Int.le fuel 0 then true else
  match Constr.Unsafe.kind b with
  | Constr.Unsafe.App g _ =>
      if is_k (x.(k_zadd)) g then true
      else if is_k (x.(k_zsub)) g then (if rgt then false else true)
      else if is_zlit b then false
      else (match Constr.Unsafe.kind g with
            | Constr.Unsafe.Constant kg _ =>
                if FSet.mem kg safe then false
                else (match Control.case (fun () => eval red in $b) with
                      | Val (b', _) => if Constr.equal b b' then false else uz_red_sum x safe rgt (Int.sub fuel 1) b'
                      | Err _ => false
                      end)
            | Constr.Unsafe.Var id =>
                (match Control.hyp_value id with
                 | Some _ => (match Control.case (fun () => eval red in $b) with
                              | Val (b', _) => if Constr.equal b b' then false else uz_red_sum x safe rgt (Int.sub fuel 1) b'
                              | Err _ => true
                              end)
                 | None => false
                 end)
            | Constr.Unsafe.Constructor _ _ => false
            | Constr.Unsafe.Rel _ => false
            | _ => true
            end)
  | Constr.Unsafe.Var id =>
      (match Control.hyp_value id with Some v => uz_red_sum x safe rgt (Int.sub fuel 1) v | None => false end)
  | Constr.Unsafe.Constant kg _ =>
      if FSet.mem kg safe then false
      else (match Control.case (fun () => eval red in $b) with
            | Val (b', _) => if Constr.equal b b' then false else uz_red_sum x safe rgt (Int.sub fuel 1) b'
            | Err _ => false
            end)
  | Constr.Unsafe.Constructor _ _ => false
  | Constr.Unsafe.Case _ _ _ _ _ => false          (* [comment removed for export] *)
  | Constr.Unsafe.Rel _ => false
  | _ => true
  end.

Ltac2 rec uz_cand (x : sf_ctx) (safe : constant FSet.t) (wsafe : constant FSet.t) (kwa : constant) (ksok : constant)
    (krd : constant) (kwtm : constant) (rgt : bool) (zpos : bool) (t : constr) : bool :=
  (* [comment removed for export] *)
  let rc := uz_cand x safe wsafe kwa ksok krd kwtm rgt in
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant k _ =>
           if (if Constant.equal k (x.(k_ztobv)) then true else Constant.equal k kwa) then
             (let b := arg_last t in
              (match Constr.Unsafe.kind b with
               | Constr.Unsafe.App g gargs =>
                   if is_k (x.(k_zadd)) g then
                     (let op := if rgt then sf_get gargs 1 else sf_get gargs 0 in
                      if unsigned_ztobv x op then true else u_risky x op)
                   else if is_k (x.(k_zsub)) g then
                     (if rgt then false else
                      (let op := sf_get gargs 0 in if unsigned_ztobv x op then true else u_risky x op))
                   else if is_zlit b then false
                   else (match Constr.Unsafe.kind g with
                         | Constr.Unsafe.Constant kg _ => if FSet.mem kg safe then false else uz_red_sum x safe rgt 6 b
                         | Constr.Unsafe.Var _ => uz_red_sum x safe rgt 6 b
                         | _ => true
                         end)
               | Constr.Unsafe.Var id => (match Control.hyp_value id with Some _ => uz_red_sum x safe rgt 6 b | None => false end)
               | Constr.Unsafe.Constant _ _ => uz_red_sum x safe rgt 6 b
               | Constr.Unsafe.Constructor _ _ => false
               | Constr.Unsafe.Rel _ => false
               | _ => true
               end) || Array.exist (rc true) args)
           else if (if Constant.equal k ksok then true else Constant.equal k krd) then
             (* [comment removed for export] *)
             (if Int.equal (Array.length args) 4 then
                (if rc true (Array.get args 1) then true else if rc false (Array.get args 2) then true else rc true (Array.get args 3))
              else true)
           else if Constant.equal k kwtm then
             (* [comment removed for export] *)
             (if Int.equal (Array.length args) 3 then
                (if rc true (Array.get args 0) then true else if rc false (Array.get args 1) then true else rc true (Array.get args 2))
              else true)
           else if FSet.mem k safe then Array.exist (rc true) args        (* [comment removed for export] *)
           else if FSet.mem k wsafe then Array.exist (rc false) args      (* [comment removed for export] *)
           else if zpos then Array.exist (rc false) args
           else if Constr.Unsafe.is_closed t then true else Array.exist (rc false) args
       | Constr.Unsafe.Constructor c _ =>
           if Constructor.equal c (cof reference:(BV)) then false          (* [comment removed for export] *)
           else Array.exist (rc false) args
       | Constr.Unsafe.Ind _ _ => Array.exist (rc false) args
       | Constr.Unsafe.Var id =>
           (match Control.hyp_value id with
            | Some _ => if zpos then Array.exist (rc false) args else if Constr.Unsafe.is_closed t then true else Array.exist (rc false) args
            | None => Array.exist (rc false) args
            end)
       | Constr.Unsafe.Rel _ => Array.exist (rc false) args
       | _ => true
       end)
  | Constr.Unsafe.Var id => if zpos then false else (match Control.hyp_value id with Some _ => true | None => false end)
  | Constr.Unsafe.Constant k _ => if zpos then false else if FSet.mem k safe then false else if FSet.mem k wsafe then false else true
  | Constr.Unsafe.Lambda b body => if rc true (Constr.Binder.type b) then true else rc false body
  | Constr.Unsafe.Prod b body => if rc true (Constr.Binder.type b) then true else rc true body
  | Constr.Unsafe.Case _ _ _ scr brs => if rc true scr then true else Array.exist (rc false) brs
  | Constr.Unsafe.Evar _ _ => false
  | Constr.Unsafe.Rel _ => false
  | Constr.Unsafe.Sort _ => false
  | Constr.Unsafe.Ind _ _ => false
  | Constr.Unsafe.Constructor _ _ => false
  | Constr.Unsafe.Cast c _ _ => rc zpos c
  | _ => true
  end.

(* [comment removed for export] *)
Ltac2 sf_uz_cand (rgt : bool) : unit :=
  lazy_match! goal with
  | [ |- ?l = ?r ] =>
      (match Constr.Unsafe.kind r with Constr.Unsafe.Evar _ _ => () | _ => sf_fail "uz_cand: not a small goal" end);
      let x := mk_ctx false in
      if uz_cand x (uz_safe_heads ()) (uz_wsafe_heads ()) (kof reference:(wa)) (kof reference:(store_ok)) (kof reference:(ov_read_bytes))
           (kof reference:(write_to_mem)) rgt false l
      then () else sf_fail "no uz candidate"
  | [ |- _ ] => ()
  end.
Ltac sf_uz_cand_l := ltac2:(sf_uz_cand false).
Ltac sf_uz_cand_r := ltac2:(sf_uz_cand true).

(* [comment removed for export] *)
Ltac2 vt_unfold_consts () : constant FSet.t := const_set [
  reference:(v_addi); reference:(v_add); reference:(v_sub); reference:(v_mul); reference:(v_andi); reference:(v_ori);
  reference:(v_xori); reference:(v_and); reference:(v_or); reference:(v_xor); reference:(v_slli); reference:(v_srli);
  reference:(v_srai); reference:(v_sll); reference:(v_srl); reference:(v_sra); reference:(v_lui); reference:(v_auipc);
  reference:(v_addiw); reference:(v_slliw); reference:(v_srliw); reference:(v_sraiw); reference:(v_addw); reference:(v_subw);
  reference:(v_sllw); reference:(v_srlw); reference:(v_sraw); reference:(v_mulh); reference:(v_mulhsu); reference:(v_mulhu);
  reference:(v_mulw); reference:(btgt) ].
Ltac2 rec has_const (ks : constant FSet.t) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Constant k _ => FSet.mem k ks
  | Constr.Unsafe.App f args => if has_const ks f then true else Array.exist (has_const ks) args
  | Constr.Unsafe.Lambda b body => if has_const ks (Constr.Binder.type b) then true else has_const ks body
  | Constr.Unsafe.Prod b body => if has_const ks (Constr.Binder.type b) then true else has_const ks body
  | Constr.Unsafe.LetIn b v body => if has_const ks (Constr.Binder.type b) then true else if has_const ks v then true else has_const ks body
  | Constr.Unsafe.Case _ _ _ scr brs => if has_const ks scr then true else Array.exist (has_const ks) brs
  | Constr.Unsafe.Cast c _ _ => has_const ks c
  | Constr.Unsafe.Proj _ _ c => has_const ks c
  | Constr.Unsafe.Evar _ _ => false
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 zcons (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor k _ => Constructor.equal k (cof reference:(Z0))
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constructor k _ =>
           if Int.equal (Array.length args) 1 then
             (if Constructor.equal k (cof reference:(Zpos)) then true else Constructor.equal k (cof reference:(Zneg)))
           else false
       | _ => false
       end)
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 rec fold_redex (x : sf_ctx) (kbin : constant FSet.t) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant k _ =>
           let n := Array.length args in
           (if (if Constant.equal k (x.(k_unsigned)) then true else Constant.equal k (x.(k_signed))) then
              (if Int.equal n 2 then
                 (let b := Array.get args 1 in
                  if head_c (cof reference:(BV)) b then true
                  else if head_k (x.(k_concat)) b then true
                  else if head_k (x.(k_ztobv)) b then zcons (arg_last b)
                  else false)
               else true)
            else if FSet.mem k kbin then
              (if Int.equal n 2 then
                 (let a0 := Array.get args 0 in let a1 := Array.get args 1 in
                  if (if zcons a0 then zcons a1 else false) then true
                  else if Constant.equal k (x.(k_zadd)) then
                    (if zcons a1 then (if head_k (x.(k_zadd)) a0 then zcons (arg_last a0) else false) else false)
                  else false)
               else true)
            else if (if Constant.equal k (x.(k_swrap)) then true else Constant.equal k (x.(k_wrap))) then
              (if Int.equal n 2 then zcons (Array.get args 1) else true)
            else if Constant.equal k (x.(k_ztobv)) then
              (if Int.equal n 2 then
                 (if Constr.equal (Array.get args 0) (x.(c_n64)) then
                    (let b := Array.get args 1 in
                     if head_k (x.(k_zadd)) b then (match Constr.Unsafe.kind (arg_last b) with
                                                     | Constr.Unsafe.Constructor k0 _ => Constructor.equal k0 (cof reference:(Z0))
                                                     | _ => false end)
                     else false)
                  else false)
               else true)
            else false) || Array.exist (fold_redex x kbin) args
       | _ => if fold_redex x kbin f then true else Array.exist (fold_redex x kbin) args
       end)
  | Constr.Unsafe.Lambda b body => if fold_redex x kbin (Constr.Binder.type b) then true else fold_redex x kbin body
  | Constr.Unsafe.Prod b body => if fold_redex x kbin (Constr.Binder.type b) then true else fold_redex x kbin body
  | Constr.Unsafe.LetIn b v body => if fold_redex x kbin v then true else fold_redex x kbin body
  | Constr.Unsafe.Case _ _ _ scr brs => if fold_redex x kbin scr then true else Array.exist (fold_redex x kbin) brs
  | Constr.Unsafe.Cast c _ _ => fold_redex x kbin c
  | Constr.Unsafe.Proj _ _ c => fold_redex x kbin c
  | _ => false
  end.
Ltac2 fold_bin_consts () : constant FSet.t := const_set [
  reference:(Z.shiftl); reference:(Z.shiftr); reference:(Z.land); reference:(Z.lor); reference:(Z.lxor);
  reference:(Z.add); reference:(Z.sub); reference:(Z.mul) ].
Ltac2 sf_need_unfold () : unit :=
  if has_const (vt_unfold_consts ()) (Control.goal ()) then () else sf_fail "no unfold".
Ltac2 sf_need_fold () : unit :=
  if fold_redex (mk_ctx false) (fold_bin_consts ()) (Control.goal ()) then () else sf_fail "no fold".
Ltac sf_need_unfold := ltac2:(sf_need_unfold ()).
Ltac sf_need_fold := ltac2:(sf_need_fold ()).

(* [comment removed for export] *)
Ltac sf_vt_litadd := match goal with |- context [@bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 _)] => rewrite ?lit_add_lit | _ => idtac end.
Ltac sf_vt_w01 := (match goal with |- context [w0] => rewrite ?w0_lit | _ => idtac end);
                  (match goal with |- context [w1] => rewrite ?w1_lit | _ => idtac end).
(* [comment removed for export] *)
Ltac sf_vt_unfold := cbv beta iota zeta delta [v_addi v_add v_sub v_mul v_andi v_ori v_xori v_and v_or v_xor
                 v_slli v_srli v_srai v_sll v_srl v_sra v_lui v_auipc
                 v_addiw v_slliw v_srliw v_sraiw v_addw v_subw v_sllw v_srlw v_sraw
                 v_mulh v_mulhsu v_mulhu v_mulw]; unfold btgt.
Ltac sf_vt_uzguard := match goal with |- context [bv_unsigned (Z_to_bv 64 _)] => idtac end.
Ltac sf_vt_uzl := rewrite unsigned_Z_to_bv_add.
Ltac sf_vt_uzr := rewrite unsigned_Z_to_bv_add_r.
Ltac sf_vt_rest :=
  (match goal with |- context [Z_to_bv 64 (bv_unsigned _)] => rewrite ?Z_to_bv_lit_self | _ => idtac end);
  (match goal with |- context [bv_and _ (bv_not _)] => rewrite ?ret_pc_fold | _ => idtac end);
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Ltac2 Type sf_vt := { vt_x : sf_ctx; vt_uzsafe : constant FSet.t; vt_uzwsafe : constant FSet.t; vt_kwa : constant;
                      vt_ksok : constant; vt_krd : constant; vt_kwtm : constant; vt_unf : constant FSet.t; vt_bin : constant FSet.t }.
Ltac2 mk_vt (x : sf_ctx) : sf_vt :=
  { vt_x := x; vt_uzsafe := uz_safe_heads (); vt_uzwsafe := uz_wsafe_heads (); vt_kwa := kof reference:(wa);
    vt_ksok := kof reference:(store_ok); vt_krd := kof reference:(ov_read_bytes); vt_kwtm := kof reference:(write_to_mem);
    vt_unf := vt_unfold_consts (); vt_bin := fold_bin_consts () }.
Ltac2 vt_uz_cand (v : sf_vt) (rgt : bool) : bool :=
  lazy_match! goal with
  | [ |- ?l = ?r ] =>
      (match Constr.Unsafe.kind r with
       | Constr.Unsafe.Evar _ _ =>
           uz_cand (v.(vt_x)) (v.(vt_uzsafe)) (v.(vt_uzwsafe)) (v.(vt_kwa)) (v.(vt_ksok)) (v.(vt_krd)) (v.(vt_kwtm)) rgt false l
       | _ => true
       end)
  | [ |- _ ] => true
  end.
(* [comment removed for export] *)
Ltac2 rec vt_uz_loop (v : sf_vt) (rgt : bool) : unit :=
  if vt_uz_cand v rgt then
    (match Control.case (fun () => if rgt then ltac1:(sf_vt_uzr) else ltac1:(sf_vt_uzl)) with
     | Val _ => vt_uz_loop v rgt
     | Err _ => ()
     end)
  else ().
Ltac2 sf_vnorm_tail2 (v : sf_vt) : unit :=
  ltac1:(sf_vt_litadd);
  ltac1:(sf_vt_w01);
  (if has_const (v.(vt_unf)) (Control.goal ()) then ltac1:(sf_vt_unfold) else ());
  (match Control.case (fun () => ltac1:(sf_vt_uzguard)) with
   | Val _ => vt_uz_loop v false; vt_uz_loop v true
   | Err _ => ()
   end);
  (if fold_redex (v.(vt_x)) (v.(vt_bin)) (Control.goal ()) then ltac1:(fold_closed_in_goal) else ());
  ltac1:(sf_vt_rest).
Ltac2 sf_vnorm_for2 (v : sf_vt) (i : constr) : unit :=
  let iv := Ltac1.of_constr i in
  ltac1:(iv |- vnorm_rw_for iv) iv;
  sf_vnorm_tail2 v.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac2 sf_lhs () : constr := lazy_match! goal with [ |- ?l = _ ] => l end.
(* [comment removed for export] *)
Ltac2 sf_norm_load2 (v : sf_vt) (z : bool) (i : constr) : unit :=
  ltac1:(cbv beta delta [sf_load_goal]); sf_vnorm_for2 v i; ltac1:(solve_load);
  let x := v.(vt_x) in
  (if bad (ctx_mode x false) (sf_lhs ()) then (ltac1:(simp_regs); sf_vnorm_for2 v i) else ());
  if z then
    (let xz := ctx_mode x true in
     if bad xz (sf_lhs ()) then ltac1:(zsimp)
     else if (xz.(idioms_seen)).(contents) then ltac1:(zsimp) else ())
  else ().
Ltac2 sf_norm_store2 (v : sf_vt) (i : constr) : unit :=
  ltac1:(cbv beta delta [sf_store_goal]); sf_vnorm_for2 v i; ltac1:(solve_store);
  let x := v.(vt_x) in
  if bad (ctx_mode x false) (sf_lhs ()) then (ltac1:(simp_regs); sf_vnorm_for2 v i) else ().

(* [comment removed for export] *)
Ltac2 small_goal (pass : unit -> unit) (t : constr) (ty : constr) : ident * constr :=
  let h := Fresh.in_goal @sfE in
  let hv := Ltac1.of_ident h in
  let tv := Ltac1.of_constr t in
  let tyv := Ltac1.of_constr ty in
  ltac1:(hv tv tyv |- eassert (hv : tv = (_ : tyv))) hv tv tyv;
  let cap := { contents := None } in
  Control.focus 1 1 (fun () =>
    pass ();
    lazy_match! goal with [ |- ?l = _ ] => cap.(contents) := Some l end;
    Std.reflexivity ());
  match cap.(contents) with Some l => (h, l) | None => sf_fail "small_goal" end.

(* [comment removed for export] *)
Ltac2 goal_lhs () : constr := lazy_match! goal with [ |- ?l = _ ] => l end.

Ltac2 sf_passes (x : sf_ctx) (z : bool) (i : constr) : unit :=
  let iv := Ltac1.of_constr i in
  let v := mk_vt x in
  sf_vnorm_for2 v i;
  (if bad (ctx_mode x false) (goal_lhs ()) then (ltac1:(simp_regs); sf_vnorm_for2 v i) else ());
  if z then
    (let xz := ctx_mode x true in
     if bad xz (goal_lhs ()) then ltac1:(zsimp)
     else if (xz.(idioms_seen)).(contents) then ltac1:(zsimp) else ())
  else ().

(* [comment removed for export] *)
Ltac2 sf_zpasses (x : sf_ctx) : unit :=
  let xz := ctx_mode x true in
  if bad xz (goal_lhs ()) then ltac1:(zsimp)
  else if (xz.(idioms_seen)).(contents) then ltac1:(zsimp) else ().

(* [comment removed for export] *)
Ltac2 gref (r : Std.reference) : constr := Env.instantiate r.

Ltac2 mk_rel (n : int) : constr := Constr.Unsafe.make (Constr.Unsafe.Rel n).
Ltac2 mk_app (f : constr) (a : constr array) : constr := Constr.Unsafe.make (Constr.Unsafe.App f a).
Ltac2 mk_lam (id : ident) (ty : constr) (body : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Lambda (Constr.Binder.make (Some id) ty) body).
Ltac2 mk_arr (a : constr) (b : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.make None a) b).

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 w0_rhs () : constr := lazy_match! Constr.type '@w0_lit with _ = ?rhs => rhs end.

Ltac2 rec subst_w0 (w0c : constr) (z0 : constr) (c : constr) : constr :=
  if Constr.equal c w0c then z0 else Constr.Unsafe.map (subst_w0 w0c z0) c.

(* [comment removed for export] *)
Ltac2 zlit_add (a : constr) (b : constr) : constr :=
  match zlit_int a, zlit_int b with
  | Some x, Some y =>
      (* [comment removed for export] *)
      if Int.lt (Int.abs x) 1073741824 then (if Int.lt (Int.abs y) 1073741824 then int_zlit (Int.add x y) else
        let t := Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(Z.add)) [| a; b |]) in eval cbv in $t)
      else let t := Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(Z.add)) [| a; b |]) in eval cbv in $t
  | _, _ => let t := Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(Z.add)) [| a; b |]) in eval cbv in $t
  end.
(* [comment removed for export] *)
Ltac2 signed_lit (imm : constr) : constr :=
  match imm_signed imm with
  | Some k => int_zlit k
  | None => let t := Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(bv_signed)) [| sf_get (app_args imm) 0; imm |]) in
            eval vm_compute in $t
  end.
Ltac2 direct_pc (x : sf_ctx) (i : constr) (pc : constr) (sz : constr) (pc1 : constr) : (constr * constr option) option :=
  let ztobv := gref reference:(Z_to_bv) in
  let n64 := x.(c_n64) in
  let zrefl t := mk_app (gref reference:(eq_refl)) [| gref reference:(Z); t |] in
  lazy_match! i with
  | Jalr _ _ _ => None
  | Jal _ ?imm =>
      let t := zlit_add pc (signed_lit imm) in
      lazy_match! pc1 with
      | @bv_add 64 (Z_to_bv 64 ?p) (@sext ?n 64 ?imm') =>
          Some (mk_app ztobv [| n64; t |], Some (mk_app (gref reference:(sf_btgt)) [| p; t; n; imm'; zrefl t |]))
      | _ => None
      end
  | Branch _ _ _ ?imm =>
      match Constr.Unsafe.kind pc1 with
      | Constr.Unsafe.Case ci ret iv c brs =>
          if Int.equal (Array.length brs) 2 then
            lazy_match! (sf_get brs 0) with
            | @bv_add 64 (Z_to_bv 64 ?p) (@sext ?n 64 ?imm') =>
                lazy_match! (sf_get brs 1) with
                | @bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 ?sz') =>
                    let t := zlit_add pc (signed_lit imm) in
                    let f := zlit_add pc sz in
                    let c' := subst_w0 (gref reference:(w0)) (mk_app ztobv [| n64; gref reference:(Z0) |]) c in
                    if bad x c' then None else
                    Some (Constr.Unsafe.make (Constr.Unsafe.Case ci ret iv c' [| mk_app ztobv [| n64; t |]; mk_app ztobv [| n64; f |] |]),
                          Some (mk_app (gref reference:(sf_branch_pc)) [| c'; p; t; f; sz'; n; imm'; zrefl t; zrefl f |]))
                | _ => None
                end
            | _ => None
            end
          else None
      | _ => None
      end
  | _ => let t := zlit_add pc sz in Some (mk_app ztobv [| n64; t |], None)
  end.

Ltac2 vm_eq (ty : constr) (t : constr) (v : constr) : constr :=
  (* [comment removed for export] *)
  Constr.Unsafe.make (Constr.Unsafe.Cast (mk_app (gref reference:(eq_refl)) [| ty; v |]) Constr.Cast.vm
                                          (mk_app (gref reference:(eq)) [| ty; t; v |])).

(* [comment removed for export] *)
Ltac2 rec tree_leaves_p (t : constr) (rp : bool list) : (bool list * constr) list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 4 then
        let vs := match Constr.Unsafe.kind (sf_get args 2) with
                  | Constr.Unsafe.App _ sargs => if Int.equal (Array.length sargs) 2 then [(List.rev rp, sf_get sargs 1)] else []
                  | _ => []
                  end in
        List.append (tree_leaves_p (sf_get args 1) (false :: rp)) (List.append vs (tree_leaves_p (sf_get args 3) (true :: rp)))
      else []
  | _ => []
  end.

(* [comment removed for export] *)
Ltac2 rec dirty_leaves (x : sf_ctx) (trig : constr list ref) (skip : bool list option) (t : constr) (rp : bool list) (acc : (bool list * constr) list)
  : (bool list * constr) list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App _ args =>
      if Int.equal (Array.length args) 4 then
        let acc := dirty_leaves x trig skip (Array.get args 1) (false :: rp) acc in
        let acc := match Constr.Unsafe.kind (Array.get args 2) with
          | Constr.Unsafe.App _ sargs =>
              if Int.equal (Array.length sargs) 2 then
                let l := Array.get sargs 1 in
                match Constr.Unsafe.kind l with
                | Constr.Unsafe.Var _ => acc
                | _ =>
                    let p := List.rev rp in
                    if (match skip with Some sp => path_eq p sp | None => false end) then acc
                    else
                      (* [comment removed for export] *)
                      let uz0 := (x.(uz_seen)).(contents) in
                      let id0 := (x.(idioms_seen)).(contents) in
                      (x.(idioms_seen)).(contents) := false;
                      if bad x l then ((x.(uz_seen)).(contents) := uz0; (if id0 then (x.(idioms_seen)).(contents) := true else ()); (p, l) :: acc)
                      else
                        ((if (x.(idioms_seen)).(contents) then trig.(contents) := l :: trig.(contents)
                          else (x.(idioms_seen)).(contents) := id0);
                         acc)
                end
              else acc
          | _ => acc
          end in
        dirty_leaves x trig skip (Array.get args 3) (true :: rp) acc
      else acc
  | _ => acc
  end
with path_eq (a : bool list) (b : bool list) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if Bool.equal x y then path_eq a' b' else false
  | _, _ => false
  end.

(* [comment removed for export] *)
Ltac2 leaf_cbv (c : constr) : constr :=
  eval cbv beta iota zeta delta [lift_result interp_eff0 exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s] in $c.

(* [comment removed for export] *)
Ltac2 norm_mem (pass : unit -> unit) (t : constr) (ty : constr) : ident * constr :=
  let (h, l) := small_goal pass t ty in
  lazy_match! l with
  | Some ?e => (h, e)
  | _ => sf_fail "norm_mem"
  end.



(* [comment removed for export] *)
Ltac2 mk_congr (ty : constr) (body : constr) (comps : (constr * constr * constr) list) : constr :=
  let k := List.length comps in
  let wd := mk_app (gref reference:(bv)) [| '(64%N) |] in
  let rec lams j b := if Int.equal j 0 then b else lams (Int.sub j 1) (mk_lam @x wd b) in
  let fn := lams k body in
  let pfs := List.map (fun (_, _, p) => p) comps in
  let inter := List.flat_map (fun (a, b, _) => [a; b]) comps in
  match comps with
  | [] => mk_app (gref reference:(sf_refl)) [| body |]
  | _ =>
      let fe := match k with
                | 1 => gref reference:(sf_cong1) | 2 => gref reference:(sf_cong2) | 3 => gref reference:(sf_cong3)
                | 4 => gref reference:(sf_cong4) | 5 => gref reference:(sf_cong5)
                | _ => sf_fail "too many components"
                end in
      mk_app fe (Array.of_list (List.append [fn] (List.append inter pfs)))
  end.

(* [comment removed for export] *)
Ltac2 rec tup (l : (constr * constr) list) : constr * constr :=
  match l with
  | [] => sf_fail "tup"
  | [p] => p
  | p :: rest =>
      let (ty, v) := p in
      let (tyr, tr) := tup rest in
      (mk_app (gref reference:(prod)) [| ty; tyr |], mk_app (gref reference:(pair)) [| ty; tyr; v; tr |])
  end.
Ltac2 rec tup_ty (l : constr list) : constr :=
  match l with
  | [] => sf_fail "tup_ty"
  | [ty] => ty
  | ty :: rest => mk_app (gref reference:(prod)) [| ty; tup_ty rest |]
  end.
Ltac2 rec tup_proj (l : constr list) (t : constr) : constr list :=
  match l with
  | [] => []
  | [_] => [t]
  | ty :: rest =>
      let tyr := tup_ty rest in
      mk_app (gref reference:(fst)) [| ty; tyr; t |] :: tup_proj rest (mk_app (gref reference:(snd)) [| ty; tyr; t |])
  end.
(* [comment removed for export] *)
Ltac2 rec untup (n : int) (t : constr) : constr list :=
  if Int.le n 1 then [t] else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 4 then sf_get args 2 :: untup (Int.sub n 1) (sf_get args 3) else sf_fail "untup"
  | _ => sf_fail "untup"
  end.
(* [comment removed for export] *)
Ltac2 pair_eq1 (ta : constr) (tb : constr) (a : constr) (a' : constr) (b : constr) (b' : constr) (h : constr) : constr :=
  mk_app (gref reference:(sf_pair_eq1)) [| ta; tb; a; a'; b; b'; h |].
Ltac2 pair_eq2 (ta : constr) (tb : constr) (a : constr) (a' : constr) (b : constr) (b' : constr) (h : constr) : constr :=
  mk_app (gref reference:(sf_pair_eq2)) [| ta; tb; a; a'; b; b'; h |].


(* [comment removed for export] *)
Ltac2 rec path_pos (path : bool list) : constr :=
  match path with
  | [] => 'xH
  | d :: rest => let q := path_pos rest in if d then '(xI $q) else '(xO $q)
  end.
(* [comment removed for export] *)
Ltac2 sf_cong_lf (rbase : constr) (f : constr) (fc : constr) (rv : constr) (m : constr) (ro : constr)
    (paths : bool list list) (raws : constr list) (norms : constr list) (pcfix : constr option) (hj : constr) : constr option :=
  let k := List.length paths in
  let ps := List.map path_pos paths in
  let rec inter (a : constr list) (b : constr list) : constr list :=
    match a with
    | [] => []
    | x :: a' => (match b with y :: b' => x :: y :: inter a' b' | [] => [] end)
    end in
  let xy := inter raws norms in
  let hd := [rbase; f; fc; rv; m; ro] in
  match pcfix with
  | Some pc =>
      (* [comment removed for export] *)
      let lem := if Int.equal k 1 then Some (gref reference:(sf_cr1)) else if Int.equal k 2 then Some (gref reference:(sf_cr2))
                 else if Int.equal k 3 then Some (gref reference:(sf_cr3)) else None in
      (match lem with
       | Some l => Some (mk_app l (Array.of_list (List.append hd (List.append ps (pc :: List.append xy [hj])))))
       | None => None
       end)
  | None =>
      (* [comment removed for export] *)
      let lem := if Int.equal k 0 then Some (gref reference:(sf_cr0pc)) else if Int.equal k 1 then Some (gref reference:(sf_cr1pc))
                 else if Int.equal k 2 then Some (gref reference:(sf_cr2pc)) else if Int.equal k 3 then Some (gref reference:(sf_cr3pc)) else None in
      (match lem with
       | Some l => Some (mk_app l (Array.of_list (List.append hd (List.append ps (List.append xy [hj])))))
       | None => None
       end)
  end.

Ltac2 Type sf_comp := { c_path : bool list option (* [comment removed for export] *); c_raw : constr }.

(* [comment removed for export] *)
Ltac2 rec holes (t : constr) (paths : bool list list) (k : int) : constr :=
  match paths with
  | [] => t
  | p :: ps => holes (tree_set p (mk_rel k) t) ps (Int.sub k 1)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 zlit_eq0 (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor _ _ => true   (* [comment removed for export] *)
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 direct_add_tail (x : sf_ctx) (z : bool) (v : constr) (a : constr) (n : constr) (imm : constr) (base : constr)
    : (constr * constr) option :=
  let ztobv := gref reference:(Z_to_bv) in
  let n64 := x.(c_n64) in
  let wd := mk_app (gref reference:(bv)) [| n64 |] in
  let zt := gref reference:(Z) in
  let etrans a b c p q := mk_app (gref reference:(eq_trans)) [| wd; a; b; c; p; q |] in
  let fzw (e1 : constr) (e2 : constr) (p : constr) :=   (* [comment removed for export] *)
    mk_app (gref reference:(f_equal)) [| zt; wd; mk_app ztobv [| n64 |]; e1; e2; p |] in
      if bad (ctx_mode x z) a then None else
      let k := signed_lit imm in
      let zadd p q := mk_app (gref reference:(Z.add)) [| p; q |] in
      let uns t := mk_app (gref reference:(bv_unsigned)) [| n64; t |] in
      match Constr.Unsafe.kind a with
      | Constr.Unsafe.Constant _ _ =>
          if Constr.equal a (gref reference:(w0)) then Some (mk_app ztobv [| n64; k |], base) else None
      | Constr.Unsafe.Var id =>
          (match Control.hyp_value id with
           | Some _ => None
           | None =>
               if zlit_eq0 k then Some (a, etrans v (mk_app ztobv [| n64; zadd (uns a) k |]) a base (mk_app (gref reference:(Z_to_bv_plus0)) [| a |]))
               else Some (mk_app ztobv [| n64; zadd (uns a) k |], base)
           end)
      | Constr.Unsafe.App h args =>
          if Constr.equal h ztobv then
            if Int.equal (Array.length args) 2 then
              if Constr.equal (Array.get args 0) n64 then
                let e := Array.get args 1 in
                let p1 := etrans v (mk_app ztobv [| n64; zadd (uns a) k |]) (mk_app ztobv [| n64; zadd e k |]) base
                                 (mk_app (gref reference:(unsigned_Z_to_bv_add)) [| e; k |]) in
                if is_zlit e then
                  let c := zlit_add e k in
                  (* [comment removed for export] *)
                  (if z then (lazy_match! (eval cbv in (orb (Z.ltb $c 0) (Z.leb 18446744073709551616 $c))) with true => None | _ => Some (mk_app ztobv [| n64; c |], p1) end)
                   else Some (mk_app ztobv [| n64; c |], p1))
                else if (if head_k (x.(k_zadd)) e then is_zlit (arg_last e) else false) then
                  let ea := app_args e in
                  let y := Array.get ea 0 in let a' := Array.get ea 1 in
                  let c' := zlit_add a' k in
                  let p2 := etrans v (mk_app ztobv [| n64; zadd e k |]) (mk_app ztobv [| n64; zadd y c' |]) p1
                              (fzw (zadd e k) (zadd y (zadd a' k))
                                   (mk_app (gref reference:(eq_sym)) [| zt; zadd y (zadd a' k); zadd e k;
                                                                       mk_app (gref reference:(Z.add_assoc)) [| y; a'; k |] |])) in
                  if zlit_eq0 c' then
                    let p3 := etrans v (mk_app ztobv [| n64; zadd y c' |]) (mk_app ztobv [| n64; y |]) p2
                                (fzw (zadd y c') y (mk_app (gref reference:(Z.add_0_r)) [| y |])) in
                    (if head_k (x.(k_unsigned)) y then
                       (let zz := arg_last y in
                        if Constr.equal (sf_get (app_args y) 0) n64 then
                          Some (zz, etrans v (mk_app ztobv [| n64; y |]) zz p3 (mk_app (gref reference:(Z_to_bv_lit_self)) [| zz |]))
                        else None)
                     else Some (mk_app ztobv [| n64; y |], p3))
                  else Some (mk_app ztobv [| n64; zadd y c' |], p2)
                else if zlit_eq0 k then
                  Some (a, etrans v (mk_app ztobv [| n64; zadd e k |]) a p1 (fzw (zadd e k) e (mk_app (gref reference:(Z.add_0_r)) [| e |])))
                else Some (mk_app ztobv [| n64; zadd e k |], p1)
              else None
            else None
          else None
      | _ => None
      end.
Ltac2 direct_addi (x : sf_ctx) (z : bool) (v : constr) : (constr * constr) option :=
  lazy_match! v with
  | alu64 ALU_ADD ?a (@sext ?n 64 ?imm) => direct_add_tail x z v a n imm (mk_app (gref reference:(alu_addi)) [| a; n; imm |])
  | _ => None
  end.
(* [comment removed for export] *)
Ltac2 direct_addr (x : sf_ctx) (v : constr) : (constr * constr) option :=
  lazy_match! v with
  | @bv_add 64 ?a (@sext ?n 64 ?imm) => direct_add_tail x false v a n imm (mk_app (gref reference:(b_addsext)) [| a; n; imm |])
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 sf_addr_expr (x : sf_ctx) (a : constr) : constr :=
  match Constr.Unsafe.kind a with
  | Constr.Unsafe.App h args =>
      if is_k (x.(k_ztobv)) h then
        (if Int.equal (Array.length args) 2 then (if Constr.equal (Array.get args 0) (x.(c_n64)) then Array.get args 1
         else mk_app (gref reference:(Z.add)) [| mk_app (gref reference:(bv_unsigned)) [| x.(c_n64); a |]; gref reference:(Z0) |])
         else mk_app (gref reference:(Z.add)) [| mk_app (gref reference:(bv_unsigned)) [| x.(c_n64); a |]; gref reference:(Z0) |])
      else if is_k (kof reference:(wa)) h then Array.get args 0
      else mk_app (gref reference:(Z.add)) [| mk_app (gref reference:(bv_unsigned)) [| x.(c_n64); a |]; gref reference:(Z0) |]
  | _ => mk_app (gref reference:(Z.add)) [| mk_app (gref reference:(bv_unsigned)) [| x.(c_n64); a |]; gref reference:(Z0) |]
  end.
Ltac2 zsub_lit (a : constr) (b : constr) : constr :=
  let t := mk_app (gref reference:(Z.sub)) [| a; b |] in eval vm_compute in $t.
Ltac2 sf_addr_diff (x : sf_ctx) (e : constr) (a : constr) : constr option :=
  let zadd2 (t : constr) : (constr * constr) option :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args => if is_k (x.(k_zadd)) h then (if Int.equal (Array.length args) 2 then Some (Array.get args 0, Array.get args 1) else None) else None
    | _ => None
    end in
  match zadd2 e with
  | Some (xx, c1) =>
      (match zadd2 a with
       | Some (xa, c2) =>
           if Constr.equal xa xx then (if zcons c1 then (if zcons c2 then Some (zsub_lit c1 c2) else None) else None)
           else if Constr.equal a xx then (if zcons c1 then Some c1 else None)
           else (if zcons e then (if zcons a then Some (zsub_lit e a) else None) else None)
       | None =>
           if Constr.equal a xx then (if zcons c1 then Some c1 else None)
           else (if zcons e then (if zcons a then Some (zsub_lit e a) else None) else None)
       end)
  | None =>
      (match zadd2 a with
       | Some (xa, c2) =>
           if Constr.equal xa e then (if zcons c2 then Some (eval vm_compute in (Z.opp $c2)) else None)
           else if Constr.equal a e then Some (gref reference:(Z0))
           else (if zcons e then (if zcons a then Some (zsub_lit e a) else None) else None)
       | None =>
           if Constr.equal a e then Some (gref reference:(Z0))
           else (if zcons e then (if zcons a then Some (zsub_lit e a) else None) else None)
       end)
  end.

(* [comment removed for export] *)
Ltac2 sf_find_chunk (x : sf_ctx) (segs : constr) (m : constr) (e : constr) (n : constr) : (constr * constr * constr * constr * constr) option :=
  let krw := kof reference:(rw_cells) in
  let res := { contents := None } in
  let stop := { contents := false } in
  List.iter (fun (id, body, ty) =>
    if stop.(contents) then () else
    match body with
    | Some _ => ()
    | None =>
        match Constr.Unsafe.kind ty with
        | Constr.Unsafe.App h args =>
            if is_k krw h then
              (if Int.equal (Array.length args) 4 then
                 (if Constr.equal (Array.get args 0) segs then
                   (if Constr.equal (Array.get args 1) m then
                     (let a := Array.get args 2 in let cs0 := Array.get args 3 in
                      match sf_addr_diff x e a with
                      | None => ()
                      | Some k =>
                          let inr := eval vm_compute in (andb (Z.leb 0 $k) (cells_reach $cs0 ($k + Z.of_nat $n))) in
                          if Constr.equal inr 'true then
                            (let kn := eval vm_compute in (Z.to_nat $k) in
                             let ok := eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split_ok $cs0 $kn $n) in
                             if Constr.equal ok 'true then
                               (* [comment removed for export] *)
                               (stop.(contents) := true;
                                let cs2 := eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split $cs0 $kn $n) in
                                (* [comment removed for export] *)
                                let (hp, cs) := if Constr.equal cs2 cs0 then (Control.hyp id, cs0)
                                  else (mk_app (gref reference:(rw_cells_cb_split)) [| segs; m; a; cs0; cs2; kn; n; Control.hyp id;
                                          mk_app (gref reference:(eq_refl)) [| gref reference:(bool); gref reference:(true) |];
                                          mk_app (gref reference:(eq_refl)) [| mk_app (gref reference:(list)) [| gref reference:(cell) |]; cs2 |] |], cs2) in
                                let c := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at $cs $kn) in
                                lazy_match! c with
                                | Some ?c0 => res.(contents) := Some (hp, a, cs, kn, c0)
                                | _ => ()
                                end)
                             else ())
                          else ()
                      end)
                   else ())
                 else ())
               else ())
            else ()
        | _ => ()
        end
    end) (List.rev (Control.hyps ()));
  res.(contents).

(* [comment removed for export] *)
Ltac2 sf_addr_premise (x : sf_ctx) (a : constr) (an : constr) (pn : constr) (aA : constr) (kn : constr) : constr option :=
  let zt := gref reference:(Z) in
  let ofn := mk_app (gref reference:(Z.of_nat)) [| kn |] in
  let target := mk_app (gref reference:(Z.add)) [| aA; ofn |] in
  let zrefl t := mk_app (gref reference:(eq_refl)) [| zt; t |] in
  let zadd2 (t : constr) : (constr * constr) option :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args => if is_k (x.(k_zadd)) h then (if Int.equal (Array.length args) 2 then Some (Array.get args 0, Array.get args 1) else None) else None
    | _ => None
    end in
  (* [comment removed for export] *)
  let peq (ee : constr) : constr option :=
    match zadd2 ee, zadd2 aA with
    | Some (xx, c1), Some (xa, c2) =>
        if Constr.equal xx xa then Some (mk_app (gref reference:(sf_ad1)) [| xx; c1; c2; kn; zrefl c1 |])
        else if Constr.equal aA xx then Some (mk_app (gref reference:(sf_ad2)) [| xx; c1; kn; zrefl c1 |])
        else if zcons ee then (if zcons aA then Some (zrefl ee) else None) else None
    | Some (xx, c1), None =>
        if Constr.equal aA xx then Some (mk_app (gref reference:(sf_ad2)) [| xx; c1; kn; zrefl c1 |])
        else if zcons ee then (if zcons aA then Some (zrefl ee) else None) else None
    | None, Some (xa, c2) =>
        if Constr.equal xa ee then Some (mk_app (gref reference:(sf_ad3)) [| ee; c2; kn; zrefl (gref reference:(Z0)) |])
        else if zcons ee then (if zcons aA then Some (zrefl ee) else None) else None
    | None, None =>
        if Constr.equal aA ee then Some (mk_app (gref reference:(sf_ad4)) [| ee; kn; zrefl (gref reference:(Z0)) |])
        else if zcons ee then (if zcons aA then Some (zrefl ee) else None) else None
    end in
  match Constr.Unsafe.kind an with
  | Constr.Unsafe.App h args =>
      if is_k (x.(k_ztobv)) h then
        (if Int.equal (Array.length args) 2 then
           (if Constr.equal (Array.get args 0) (x.(c_n64)) then
              (let ee := Array.get args 1 in
               match peq ee with
               | Some pe => Some (mk_app (gref reference:(sf_addr_ztobv)) [| a; ee; target; pn; pe |])
               | None => None
               end)
            else None)
         else None)
      else None
  | Constr.Unsafe.Var _ =>
      (* [comment removed for export] *)
      let ux := mk_app (gref reference:(bv_unsigned)) [| x.(c_n64); an |] in
      (match zadd2 aA with
       | Some (xa, c2) =>
           if Constr.equal xa ux then Some (mk_app (gref reference:(sf_addr_var)) [| a; an; target; pn;
                                              mk_app (gref reference:(sf_ad3)) [| ux; c2; kn; zrefl (gref reference:(Z0)) |] |])
           else None
       | None =>
           if Constr.equal aA ux then Some (mk_app (gref reference:(sf_addr_var)) [| a; an; target; pn;
                                             mk_app (gref reference:(sf_ad4)) [| ux; kn; zrefl (gref reference:(Z0)) |] |])
           else None
       end)
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 sf_direct_load (x : sf_ctx) (z : bool) (segs : constr) (m : constr) (a : constr) (nb : constr) (fl : constr) (n : constr)
    : (constr * constr) option :=
  if Bool.neg (Constr.equal n (x.(c_n64))) then None
  else if Bool.neg (Constr.equal nb '8%nat) then None
  else if Bool.neg (Constr.equal fl '(fun bs : list byte => @bv_extract 64 0 64 (le_bytes_to_word bs))) then None
  else
  match direct_addr x a with
  | None => None
  | Some (an, pn) =>
      let e := sf_addr_expr x an in
      match sf_find_chunk x segs m e nb with
      | None => None
      | Some (h, aA, cs, kn, c0) =>
          lazy_match! c0 with
          | C8 ?v =>
              let sv := mk_app (gref reference:(Some)) [| mk_app (gref reference:(bv)) [| x.(c_n64) |]; v |] in
              if bad (ctx_mode x false) sv then None
              else if (if z then (let xz := ctx_mode x true in if bad xz sv then true else (xz.(idioms_seen)).(contents)) else false) then None
              else
              match sf_addr_premise x a an pn aA kn with
              | None => None
              | Some pa =>
                  let ocell := mk_app (gref reference:(option)) [| gref reference:(cell) |] in
                  let pc := mk_app (gref reference:(eq_refl)) [| ocell; mk_app (gref reference:(Some)) [| gref reference:(cell); c0 |] |] in
                  Some (v, mk_app (gref reference:(sf_load8_direct)) [| segs; m; aA; cs; kn; v; a; h; pc; pa |])
              end
          | _ => None
          end
      end
  end.

(* [comment removed for export] *)
Ltac2 sf_direct_store (x : sf_ctx) (segs : constr) (m : constr) (a : constr) (nb : constr) (n : constr) (v : constr)
    : (constr * constr) option :=
  if Bool.neg (Constr.equal n (x.(c_n64))) then None
  else if Bool.neg (Constr.equal nb '8%nat) then None
  (* [comment removed for export] *)
  else if List.exist (fun h => let (_, _, ty) := h in
                        lazy_match! ty with
                        | store_ok _ ?m' _ _ = true => Constr.equal m' m
                        | _ => false
                        end) (Control.hyps ()) then None
  else if Bool.neg (match Constr.Unsafe.kind v with
                    | Constr.Unsafe.Var id => (match Control.hyp_value id with Some _ => false | None => true end)
                    | Constr.Unsafe.Constant _ _ => Constr.equal v (gref reference:(w0))
                    | Constr.Unsafe.App h args =>
                        if is_k (x.(k_ztobv)) h then
                          (if Int.equal (Array.length args) 2 then
                             (if Constr.equal (Array.get args 0) (x.(c_n64)) then Bool.neg (zcons (Array.get args 1)) else false)
                           else false)
                        else false
                    | _ => false
                    end) then None
  else
  match direct_addr x a with
  | None => None
  | Some (an, pn) =>
      let e := sf_addr_expr x an in
      match sf_find_chunk x segs m e nb with
      | None => None
      | Some (h, aA, cs, kn, c0) =>
          let sz := eval cbv beta iota delta [csize] in (csize $c0) in
          if Bool.neg (Constr.equal sz '8%nat) then None else
          let wa_ := mk_app (gref reference:(wa)) [| mk_app (gref reference:(Z.add)) [| aA; mk_app (gref reference:(Z.of_nat)) [| kn |] |] |] in
          let isw0 := Constr.equal v (gref reference:(w0)) in
          let mn := if isw0 then mk_app (gref reference:(write_to_mem)) [| m; wa_; mk_app (gref reference:(Z_to_le_bytes)) [| '8%nat; gref reference:(Z0) |] |]
                    else mk_app (gref reference:(write_to_mem)) [| m; wa_; mk_app (gref reference:(Lib.Mem.le8)) [| v |] |] in
          let sm := mk_app (gref reference:(Some)) [| '(word -> option byte); mn |] in
          (* [comment removed for export] *)
          if (if isw0 then (if bad (ctx_mode x false) wa_ then true else bad (ctx_mode x false) m) else bad (ctx_mode x false) sm) then None else
          match sf_addr_premise x a an pn aA kn with
          | None => None
          | Some pa =>
              let ocell := mk_app (gref reference:(option)) [| gref reference:(cell) |] in
              let pc := mk_app (gref reference:(eq_refl)) [| ocell; mk_app (gref reference:(Some)) [| gref reference:(cell); c0 |] |] in
              let pz := mk_app (gref reference:(eq_refl)) [| gref reference:(nat); '8%nat |] in
              if isw0 then Some (mn, mk_app (gref reference:(sf_store8_direct0)) [| segs; m; aA; cs; kn; c0; a; h; pc; pz; pa |])
              else Some (mn, mk_app (gref reference:(sf_store8_direct)) [| segs; m; aA; cs; kn; c0; a; v; h; pc; pz; pa |])
          end
      end
  end.

Ltac2 sf_step_ (ph : int ref) (z : bool) : unit :=
  let stop (k : int) := ph.(contents) := k; stop k in
  lazy_match! goal with
  | [ |- evt ?segs ?q (MS ?r ?f (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) ] =>
    let r := if sf_regw then sf_retype r else r in
    stop 1;
    let fw := tm "fetch" (fun () => eval vm_compute in (fetch_word $segs (Z_to_bv 64 $pc))) in
    let w := lazy_match! fw with Some ?w => w | _ => sf_fail "no instruction" end in
    (* [comment removed for export] *)
    (match reg_int w with
     | Some n => if Int.equal n 115 then sf_fail "ecall" else ()
     | None => let ec := eval vm_compute in (is_ecall $w) in (lazy_match! ec with false => () | _ => sf_fail "ecall" end)
     end);
    let d := tm "decode" (fun () => eval vm_compute in (decode_any $w)) in
    let (i, sz) := lazy_match! d with Some (?i, ?sz) => (i, sz) | _ => sf_fail "undecodable" end in
    (* [comment removed for export] *)
    let rd := lazy_match! i with
      | OpImm _ ?rd _ _ => Some rd | ShiftImm _ ?rd _ _ => Some rd | Op _ ?rd _ _ => Some rd | OpImm32 ?rd _ _ => Some rd
      | ShiftImm32 _ ?rd _ _ => Some rd | Op32 _ ?rd _ _ => Some rd | Lui ?rd _ => Some rd | Auipc ?rd _ => Some rd
      | Mul _ ?rd _ _ => Some rd | Mul32 _ ?rd _ _ => Some rd | Jal ?rd _ => Some rd | Jalr ?rd _ _ => Some rd
      | Load _ _ ?rd _ _ => Some rd
      | Branch _ _ _ _ => None | Store _ _ _ _ => None
      | _ => sf_fail "unsupported instruction"
      end in
    let rd := match rd with
      | Some rd => (match reg_int rd with Some n => if Int.equal n 0 then None else Some rd | None => sf_fail "rd" end)
      | None => None
      end in
    (if is_concrete_map r then () else sf_fail "symbolic register file");
    stop 2;
    let body := tm "exec_abs" (fun () => exec_abs sz i f pc fc rv) in
    let ru := lazy_match! r with mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eval cbv beta iota delta [mkR] in $r | _ => r end in
    let ru := if sf_regw then sf_retype ru else ru in
    let hit := { contents := false } in
    let body := tm "resolve" (fun () => resolve (kof reference:(reg_get)) (kof reference:(bvmap_set)) ru 0 body hit) in
    let rnew := if hit.(contents) then ru else r in
    let body := Constr.Unsafe.substnl [rnew] 0 body in
    stop 3;
    let x := tm "mk_ctx" (fun () => mk_ctx z) in
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    let qchk := match Constr.Unsafe.kind q with Constr.Unsafe.Evar _ _ => [] | _ => [q] end in
    (* [comment removed for export] *)
    let trig := { contents := [] } in
    let bad_t (t : constr) : bool :=
      let id0 := (x.(idioms_seen)).(contents) in
      (x.(idioms_seen)).(contents) := false;
      let r := bad x t in
      (if (x.(idioms_seen)).(contents) then (if r then () else trig.(contents) := t :: trig.(contents))
       else (x.(idioms_seen)).(contents) := id0);
      (if id0 then (x.(idioms_seen)).(contents) := true else ());
      r in
    (x.(qmode)).(contents) := true;
    (if tm "rest" (fun () => List.exist (fun t => if bad_t t then (if sf_debug then printf "STEPFAST-BADREST: %t@ CULPRIT: %t" t (bad_culprit x t) else ()); true else false)
                                        qchk) then ((x.(qmode)).(contents) := false; sf_fail "rest not normal") else ());
    (x.(qmode)).(contents) := false;
    (if tm "rest" (fun () => List.exist (fun t => if bad_t t then (if sf_debug then printf "STEPFAST-BADREST: %t@ CULPRIT: %t" t (bad_culprit x t) else ()); true else false)
                                        [f; fc; rv; m; ro]) then sf_fail "rest not normal" else ());
    (* [comment removed for export] *)
    (if List.exist (fun t => let t' := eval cbv delta [mkR] in $t in if Constr.equal t t' then false else true) [f; fc; rv; m; ro; ru]
     then sf_fail "mkR in state" else ());
    let rdpath := match rd with Some rd => Some (key_path rd) | None => None end in
    stop 4;
    let dirty := tm "dirty" (fun () => List.rev (dirty_leaves x trig rdpath rnew [] [])) in
    stop 5;
    (* [comment removed for export] *)
    (match trig.(contents) with
     | [] => ()
     | tl =>
       if z then
         (if tm "idioms" (fun () => idioms_hit (List.fold_left (fun acc t => '(($acc, $t))) 'tt (List.rev tl)))
          then sf_fail "idioms" else ())
       else ()
     end);
    (* [comment removed for export] *)
    let ops := lazy_match! i with
      | OpImm ALU_ADD _ ?a _ => [a] | Op ALU_ADD _ ?a ?b => [a; b]
      | Jalr _ ?a _ => [a] | Load _ _ _ ?a _ => [a] | Store _ ?a _ _ => [a]
      | _ => []
      end in
    let susp_op := List.exist (fun k => match reg_int k with
                             | Some 0 => false
                             | Some _ => let l := tree_get (key_path k) ru in suspicious x l
                             | None => true
                             end) ops in
    (* [comment removed for export] *)
    (if (x.(uz_seen)).(contents) then
       (if susp_op then
          ((if sf_debug then List.iter (fun k => match reg_int k with Some 0 => () | Some _ => printf "STEPFAST-SUSP: %t" (tree_get (key_path k) ru) | None => () end) ops else ());
           sf_fail "suspicious operand")
        else if List.exist (fun (_, l) => risky x l) dirty then sf_fail "risky dirty leaf" else ())
     else ());
    let dirty := List.map (fun (p, l) => (p, leaf_cbv l)) dirty in
    let iv := Ltac1.of_constr i in
    let (fwp, ecp, dcp) := tm "vmeqs" (fun () =>
      let bv32 := mk_app (gref reference:(bv)) [| x.(c_n32) |] in
      let obv32 := mk_app (gref reference:(option)) [| bv32 |] in
      let iz := mk_app (gref reference:(prod)) [| gref reference:(instr); gref reference:(Z) |] in
      (vm_eq obv32 (mk_app (gref reference:(fetch_word)) [| segs; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |] |])
                   (mk_app (gref reference:(Some)) [| bv32; w |]),
       vm_eq (gref reference:(bool)) (mk_app (gref reference:(is_ecall)) [| w |]) (gref reference:(false)),
       vm_eq (mk_app (gref reference:(option)) [| iz |]) (mk_app (gref reference:(decode_any)) [| w |])
             (mk_app (gref reference:(Some)) [| iz; mk_app (gref reference:(pair)) [| gref reference:(instr); gref reference:(Z); i; sz |] |]))) in
    let mr := gref reference:(machine_state) in
    let mrr := mk_app (gref reference:(machine_result)) [| mr |] in
    let ok := gref reference:(MachineOk) in
    let cms := gref reference:(MS) in
    let wd := mk_app (gref reference:(bv)) [| x.(c_n64) |] in
    let ty_mem := '(word -> option byte) in
    let clear_hyps := { contents := [] } in
    (* [comment removed for export] *)
    let joint (pass : unit -> unit) (l : (constr * constr) list) : constr list * constr :=
      let (ty, t) := tup l in
      let (h, tn) := tm "norm" (fun () => small_goal pass t ty) in
      (if sf_timing then printf "NORMED %t ~> %t" t tn else ());
      clear_hyps.(contents) := h :: clear_hyps.(contents);
      (untup (List.length l) tn, Control.hyp h) in
    let dpaths := List.map (fun (p, _) => p) dirty in
    let draws := List.map (fun (_, l) => l) dirty in
    stop 6;
    let sfxb : (constr -> constr -> constr -> constr) option ref := { contents := None } in
    let (eqp, ms1) := lazy_match! body with
    | EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1) =>
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        let rdc := match rdpath with
          | Some p => [(p, tree_get p r1)]
          | None => (if Constr.equal r1 rnew then () else sf_fail "changed registers"); []
          end in
        let lcomps := List.append rdc dirty in
        stop 61;
        let dpc := tm "direct_pc" (fun () => direct_pc x i pc sz pc1) in
        stop 62;
        let pcsmall := match dpc with None => true | _ => false end in
        let raws := List.append (List.map (fun (_, v) => v) lcomps) (if pcsmall then [pc1] else []) in
        let k := List.length raws in
        (match raws with [] => () | _ => () end);
        let (norms, hj) := match raws with
          | [] => ([], gref reference:(I))
          | [v] =>
              (match (lazy_match! i with OpImm ALU_ADD _ _ _ => tm "direct" (fun () => direct_addi x z v) | _ => None end) with
               | Some (vn, pf) => ([vn], pf)
               | None => joint (fun () => sf_passes x z i) [(wd, v)]
               end)
          | _ => joint (fun () => sf_passes x z i) (List.map (fun v => (wd, v)) raws)
          end in
        let lnorms := List.firstn (List.length lcomps) norms in
        let pcn := match dpc with
          | Some (pcn, _) => pcn
          | None => List.last norms
          end in
        let r1n := List.fold_left2 (fun t (p, _) vn => tree_set p vn t) r1 lcomps lnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
        stop 63;
        (* [comment removed for export] *)
        let e1 :=
          match raws with
          | [] => None
          | _ =>
              let tys := List.map (fun _ => wd) raws in
              let projs := tup_proj tys (mk_rel 1) in
              let lprojs := List.firstn (List.length lcomps) projs in
              let rh := List.fold_left2 (fun t (p, _) pr => tree_set p pr t) r1 lcomps lprojs in
              let pch := if pcsmall then List.last projs else (match dpc with Some (_, None) => pcn | _ => pc1 end) in
              (* [comment removed for export] *)
              (match sf_cong_lf rnew f fc rv m ro (List.map (fun (p, _) => p) lcomps) raws norms (if pcsmall then None else Some pch) hj with
               | Some e => Some (e, pch)
               | None =>
              let fn := mk_lam @t (tup_ty tys) (mk_app ok [| mr; mk_app cms [| rh; f; pch; fc; rv; m; ro |] |]) in
              let (_, traw) := tup (List.map (fun v => (wd, v)) raws) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) norms) in
              Some (mk_app (gref reference:(sf_congT)) [| tup_ty tys; fn; traw; tnorm; hj |], pch)
               end)
          end in
        (* [comment removed for export] *)
        let eqp := match dpc with
          | Some (_, Some pf) =>
              (* [comment removed for export] *)
              let e2 := mk_app (gref reference:(sf_cr0pc)) [| r1n; f; fc; rv; m; ro; pc1; pcn; pf |] in
              (match e1 with
               | None => e2
               | Some (e, _) =>
                   mk_app (gref reference:(sf_transMR)) [| mk_app ok [| mr; mk_app cms [| r1; f; pc1; fc; rv; m; ro |] |];
                             mk_app ok [| mr; mk_app cms [| r1n; f; pc1; fc; rv; m; ro |] |]; mk_app ok [| mr; ms1 |]; e; e2 |]
               end)
          | _ =>
              (match e1 with
               | None => mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |]
               | Some (e, _) => e
               end)
          end in
        (* [comment removed for export] *)
        (if sfx_on then
           let kk := List.length lcomps in
           if Int.le kk 3 then
             let ps := List.map (fun (p, _) => path_pos p) lcomps in
             let pre (nw : constr) (fok : constr) := List.append [segs; q; r; f; pc; fc; rv; m; ro; nw; i; sz] [fok] in
             let lemK (k0 : constr) (k1 : constr) (k2 : constr) (k3 : constr) :=
               if Int.equal kk 0 then k0 else if Int.equal kk 1 then k1 else if Int.equal kk 2 then k2 else k3 in
             (match dpc with
              | Some (_, None) =>
                  (match raws with
                   | [] => sfxb.(contents) := Some (fun nw fok k => mk_app (gref reference:(sfx_cr0)) (Array.of_list (List.append (pre nw fok) [k])))
                   | _ => let lem := lemK (gref reference:(sfx_cr0)) (gref reference:(sfx_cr1)) (gref reference:(sfx_cr2)) (gref reference:(sfx_cr3)) in
                          sfxb.(contents) := Some (fun nw fok k => mk_app lem (Array.of_list (List.append (pre nw fok) (List.append ps (List.append lnorms [hj; k])))))
                   end)
              | Some (pcn0, Some pf) =>
                  (match raws with
                   | [] => sfxb.(contents) := Some (fun nw fok k => mk_app (gref reference:(sfx_cr0pc)) (Array.of_list (List.append (pre nw fok) [pcn0; pf; k])))
                   | _ => let lem := lemK (gref reference:(sfx_cr0pc)) (gref reference:(sfx_cr1pf)) (gref reference:(sfx_cr2pf)) (gref reference:(sfx_cr3pf)) in
                          sfxb.(contents) := Some (fun nw fok k => mk_app lem (Array.of_list (List.append (pre nw fok) (List.append ps (List.append lnorms [pcn0; hj; pf; k])))))
                   end)
              | None =>
                  let lem := lemK (gref reference:(sfx_cr0pc)) (gref reference:(sfx_cr1pc)) (gref reference:(sfx_cr2pc)) (gref reference:(sfx_cr3pc)) in
                  sfxb.(contents) := Some (fun nw fok k => mk_app lem (Array.of_list (List.append (pre nw fok) (List.append ps (List.append lnorms [pcn; hj; k])))))
              end)
           else ()
         else ());
        (eqp, ms1)
    | ELoad ?n ?a ?kk =>
        (* [comment removed for export] *)
        (let q' := eval cbv beta iota delta [tset mkR] in $q in if Constr.equal q q' then () else sf_fail "load: Q has mkR/redexes");
        let rdv := match rd with Some rd => rd | None => sf_fail "load to x0" end in
        let rp := match rdpath with Some p => p | None => sf_fail "load to x0" end in
        let (r1, f1, pc1, fc1, rv1) := match Constr.Unsafe.kind kk with
          | Constr.Unsafe.Lambda _ kb =>
              lazy_match! kb with
              | EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1) => (r1, f1, pc1, fc1, rv1)
              | _ => sf_fail "load shape"
              end
          | _ => sf_fail "load shape"
          end in
        (* [comment removed for export] *)
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        let fv := match Constr.Unsafe.kind r1 with
          | Constr.Unsafe.App h args => if Int.equal (Array.length args) 5 then sf_get args 3 else sf_fail "load shape"
          | _ => sf_fail "load shape"
          end in
        let nb := eval cbv beta iota delta [width_bytes] in (width_bytes $n) in
        let ext := match Constr.Unsafe.kind '(fun bs : list byte => @bv_extract 64 0 $n (le_bytes_to_word bs)) with
          | Constr.Unsafe.Lambda _ eb => eb
          | _ => sf_fail "ext"
          end in
        let fl := mk_lam @bs '(list byte) (Constr.Unsafe.substnl [ext] 0 fv) in
        let lg := mk_app (gref reference:(sf_load_goal)) [| segs; m; a; nb; fl |] in
        let owd := mk_app (gref reference:(option)) [| wd |] in
        let direct := match draws with [] => tm "directld" (fun () => sf_direct_load x z segs m a nb fl n) | _ => None end in
        (if sf_timing then (match direct with Some _ => printf "DIRECT-LD yes" | None => printf "DIRECT-LD no %t draws %i" i (List.length draws) end) else ());
        let (norms, hj) := match direct with
          | Some (vl0, pf) => ([mk_app (gref reference:(Some)) [| wd; vl0 |]], pf)
          | None =>
              let vt := mk_vt x in
              joint (fun () => sf_norm_load2 vt z i) ((owd, lg) :: List.map (fun v => (wd, v)) draws)
          end in
        let (vl, dnorms) := match norms with
          | sv :: dn => (lazy_match! sv with Some ?e => e | _ => sf_fail "load result" end, dn)
          | [] => sf_fail "load result"
          end in
        let pcn := match direct_pc x i pc sz pc1 with Some (pcn, None) => pcn | _ => sf_fail "load pc" end in
        let core_pair := mk_app (gref reference:(prod)) [| gref reference:(core); ty_mem |] in
        let kt := mk_lam @x wd (mk_app ok [| core_pair;
                     mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem;
                        mk_app (gref reference:(Core)) [| mk_app (gref reference:(bvmap_set)) [| '5%N; wd; rdv; mk_rel 1; rnew |]; f; pc1; fc; rv |]; m |] |]) in
        let r1v := tree_set rp vl rnew in
        let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) r1v dpaths dnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
        let (h1, ek) := match draws with
          | [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |])
          | _ =>
              let tys := List.map (fun _ => wd) draws in
              let tyl := tup_ty tys in
              let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
              let sv := mk_app (gref reference:(Some)) [| wd; vl |] in
              let h1 := pair_eq1 owd tyl lg sv traw tnorm hj in
              let h2 := pair_eq2 owd tyl lg sv traw tnorm hj in
              let projs := tup_proj tys (mk_rel 1) in
              let rh := List.fold_left2 (fun t p pr => tree_set p pr t) r1v dpaths projs in
              (match sf_cong_lf r1v f fc rv m ro dpaths draws dnorms (Some pcn) h2 with
               | Some e => (h1, e)
               | None =>
              let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| rh; f; pcn; fc; rv; m; ro |] |]) in
              (h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |])
               end)
          end in
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        (if sfx_on then (if sfx_ls then (match draws with [] => (lazy_match! i with Load _ _ _ _ _ => sfxb.(contents) := Some (fun nw fok k => mk_app (gref reference:(sfx_ld0)) (Array.of_list (List.append [segs; q; r; f; pc; fc; rv; m; ro; nw; i; sz; fok] [vl; h1; k]))) | _ => () end) | _ => () end) else ()) else ());
        (mk_app (gref reference:(sf_install_load_r)) [| segs; ro; m; a; nb; fl; vl; rdv; rnew; f; pc1; fc; rv; mk_app ok [| mr; ms1 |]; h1; ek |], ms1)
    | EStore ?n ?a ?v (EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1)) =>
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        (if Constr.equal r1 rnew then () else sf_fail "store changed registers");
        let nb := eval cbv beta iota delta [width_bytes] in (width_bytes $n) in
        let bs := mk_app (gref reference:(Z_to_le_bytes)) [| nb; mk_app (gref reference:(bv_unsigned)) [| n; v |] |] in
        let sg := mk_app (gref reference:(sf_store_goal)) [| segs; m; a; nb; bs |] in
        let omem := mk_app (gref reference:(option)) [| ty_mem |] in
        let direct := match draws with [] => tm "directst" (fun () => sf_direct_store x segs m a nb n v) | _ => None end in
        (if sf_timing then (match direct with Some _ => printf "DIRECT-ST yes" | None => printf "DIRECT-ST no %t draws %i v %t" i (List.length draws) v end) else ());
        let (norms, hj) := match direct with
          | Some (mn0, pf) => ([mk_app (gref reference:(Some)) [| ty_mem; mn0 |]], pf)
          | None =>
              let vt := mk_vt x in
              joint (fun () => sf_norm_store2 vt i) ((omem, sg) :: List.map (fun v => (wd, v)) draws)
          end in
        let (mn, dn1) := match norms with
          | sm :: dn => (lazy_match! sm with Some ?e => e | _ => sf_fail "store result" end, dn)
          | [] => sf_fail "store result"
          end in
        (* [comment removed for export] *)
        let (dnorms, hz) := match draws with
          | [] => ([], None)
          | _ => if z then
                   (let (dn2, h2) := joint (fun () => sf_zpasses x) (List.map (fun v => (wd, v)) dn1) in (dn2, Some (dn1, h2)))
                 else (dn1, None)
          end in
        let pcn := match direct_pc x i pc sz pc1 with Some (pcn, None) => pcn | _ => sf_fail "store pc" end in
        let core_pair := mk_app (gref reference:(prod)) [| gref reference:(core); ty_mem |] in
        let kt := mk_lam @x ty_mem (mk_app ok [| core_pair;
                     mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem; mk_app (gref reference:(Core)) [| rnew; f; pc1; fc; rv |]; mk_rel 1 |] |]) in
        let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) rnew dpaths dnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; mn; ro |] in
        let (h1, ek) := match draws with
          | [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1 |] |])
          | _ =>
              let tys := List.map (fun _ => wd) draws in
              let tyl := tup_ty tys in
              let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
              let (_, tn1) := tup (List.map (fun v => (wd, v)) dn1) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
              let sm := mk_app (gref reference:(Some)) [| ty_mem; mn |] in
              let h1 := pair_eq1 omem tyl sg sm traw tn1 hj in
              let h2 := pair_eq2 omem tyl sg sm traw tn1 hj in
              let h2 := match hz with
                | None => h2
                | Some (_, hz2) => mk_app (gref reference:(sf_trans)) [| tyl; traw; tn1; tnorm; h2; hz2 |]
                end in
              let projs := tup_proj tys (mk_rel 1) in
              let rh := List.fold_left2 (fun t p pr => tree_set p pr t) rnew dpaths projs in
              (match sf_cong_lf rnew f fc rv mn ro dpaths draws dnorms (Some pcn) h2 with
               | Some e => (h1, e)
               | None =>
              let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| rh; f; pcn; fc; rv; mn; ro |] |]) in
              (h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |])
               end)
          end in
        (* [comment removed for export] *)
        (if sfx_on then (if sfx_ls then (match draws with [] => (lazy_match! i with Store _ _ _ _ => sfxb.(contents) := Some (fun nw fok k => mk_app (gref reference:(sfx_st0)) (Array.of_list (List.append [segs; q; r; f; pc; fc; rv; m; ro; nw; i; sz; fok] [mn; h1; k]))) | _ => () end) | _ => () end) else ()) else ());
        (mk_app (gref reference:(sf_install_store_r)) [| segs; ro; m; a; nb; bs; mn; rnew; f; pc1; fc; rv; mk_app ok [| mr; ms1 |]; h1; ek |], ms1)
    | _ => sf_fail "raw shape"
    end in
    (if (x.(lit_delta)).(contents) then
       (if has_litself x ms1 then sf_fail "litself delta-instance in Q and a syntactic instance in the new state" else ())
     else ());
    stop 7;
    tm "install" (fun () =>
      let k := tm "k" (fun () => strip_cast open_constr:(_ : evt $segs $q $ms1)) in
      (* [comment removed for export] *)
      let pcw := mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |] in
      let nw := Std.eval_vm None constr:(Uint63.of_Z (bv_unsigned $w)) in
      let term :=
        if sf_decvm then
          (* [comment removed for export] *)
          let fok := vm_eq (gref reference:(bool)) (mk_app (gref reference:(sf_fetch_dec_ok)) [| segs; pcw; nw; i; sz |]) (gref reference:(true)) in
          (match sfxb.(contents) with
           | Some mk => mk nw fok k   (* [comment removed for export] *)
           | None => mk_app (gref reference:(sf_evt_step_d)) [| segs; q; r; f; pcw; fc; rv; m; ro; nw; i; sz; ms1; fok; eqp; k |]
           end)
        else
          let fok := vm_eq (gref reference:(bool)) (mk_app (gref reference:(sf_fetch_ok)) [| segs; pcw; nw |]) (gref reference:(true)) in
          mk_app (gref reference:(sf_evt_step_n)) [| segs; q; r; f; pcw; fc; rv; m; ro; nw; ms1; fok; eqp; k |] in
      (if sf_check then
         match Constr.Unsafe.check term with
         | Val _ => ()
         | Err e => printf "STEPFAST-ILLTYPED %a" (fun () e => Message.of_exn e) e; sf_fail "ill-typed"
         end
       else ());
      match Constr.Unsafe.kind k with
      | Constr.Unsafe.Evar ev _ => tm "exact" (fun () => Std.exact_no_check term; Control.new_goal ev)
      | _ => sf_fail "install: continuation"
      end);
    stop 8;
    tm "clear" (fun () => Std.clear (clear_hyps.(contents)));
    stop 9;
    (* [comment removed for export] *)
    tm "post" (fun () => lazy_match! goal with
       | [ |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) ] => ltac1:(iv |- mem_after_store_opt; post_step iv) iv
       | [ |- _ ] => ()
       end);
    (if z then
       lazy_match! goal with
       | [ |- evt ?segs' ?q' (MS ?r' ?f' ?pc' ?fc' ?rv' ?m' ?ro') ] =>
           if Constr.is_var m' then () else
           (* [comment removed for export] *)
           let (h, mn) := small_goal (fun () => ltac1:(zsimp)) m' '(word -> option byte) in
           let k := strip_cast open_constr:(_ : evt $segs' $q' (MS $r' $f' $pc' $fc' $rv' $mn $ro')) in
           let term := mk_app '@sf_evt_mem [| segs'; q'; r'; f'; pc'; fc'; rv'; m'; mn; ro'; Control.hyp h; k |] in
           match Constr.Unsafe.kind k with
           | Constr.Unsafe.Evar ev _ => Std.exact_no_check term; Control.new_goal ev; Std.clear [h]
           | _ => sf_fail "install: continuation"
           end
       end
     else ())
  | [ |- _ ] => sf_fail "goal shape"
  end.

(* [comment removed for export] *)
Ltac2 sf_step (z : bool) : unit :=
  let ph := { contents := 0 } in
  if Bool.neg sf_debug then sf_step_ ph z else
  Control.plus (fun () => sf_step_ ph z)
    (fun e => (if sf_debug then
                 (lazy_match! goal with
                  | [ |- evt _ _ (MS _ _ ?pc _ _ _ _) ] => printf "STEPFAST-PHASE %i at pc %t" (ph.(contents)) pc
                  | [ |- _ ] => printf "STEPFAST-PHASE %i" (ph.(contents))
                  end) else ()); Control.zero e).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sf_old_step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core_old segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
Ltac sf_old_zstep := sf_old_step; zsimp.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 hyps_equal (h1 : (ident * constr option * constr) list) (h2 : (ident * constr option * constr) list) : bool :=
  if Int.equal (List.length h1) (List.length h2) then
    List.for_all2 (fun (a : ident * constr option * constr) (b : ident * constr option * constr) =>
       let (ia, ba, ta) := a in let (ib, bb, tb) := b in
       if Ident.equal ia ib then
         if Constr.equal ta tb then
           match ba, bb with
           | None, None => true
           | Some x, Some y => Constr.equal x y
           | _, _ => false
           end
         else false
       else false) h1 h2
  else false.

Ltac2 sf_old (z : bool) : unit := if z then ltac1:(sf_old_zstep) else ltac1:(sf_old_step).

Ltac2 sf_dual (z : bool) : unit :=
  let g0 := Control.goal () in
  let res := Control.case (fun () =>
     sf_step z;
     let g := Control.goal () in
     let hs := Control.hyps () in
     Control.zero (SF_Captured g hs)) in
  match res with
  | Val _ => sf_fail "impossible"
  | Err e =>
      match e with
      | SF_Captured gf hf =>
          sf_old z;
          let go := Control.goal () in
          let ho := Control.hyps () in
          if Constr.equal gf go then
            (if hyps_equal hf ho then printf "STEPFAST-OK" else
               printf "STEPFAST-MISMATCH(hyps) at %t" g0)
          else
            (* [comment removed for export] *)
            (* [comment removed for export] *)
            let qev (g : constr) := match Constr.Unsafe.kind g with
              | Constr.Unsafe.App f args =>
                  if Int.equal (Array.length args) 3 then (if is_k (kof reference:(evt)) f then Some (Array.get args 0, Array.get args 2) else None)
                  else None
              | _ => None end in
            match qev gf, qev go with
            | Some (s1, ms1), Some (s2, ms2) =>
                if Constr.equal s1 s2 then
                  (if Constr.equal ms1 ms2 then
                     (if hyps_equal hf ho then printf "STEPFAST-OK(evarQ)" else printf "STEPFAST-MISMATCH(hyps) at %t" g0)
                   else printf "STEPFAST-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go)
                else printf "STEPFAST-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go
            | _, _ => printf "STEPFAST-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go
            end
      | _ =>
          printf "STEPFAST-FALLBACK %a" (fun () e => Message.of_exn e) e;
          sf_old z
      end
  end.

(* [comment removed for export] *)
Ltac2 mutable sf_mode : int := 1.

Ltac2 sf_core1 (z : bool) : unit :=
  if Int.equal sf_mode 0 then sf_old z
  else if Int.equal sf_mode 1 then
    (* [comment removed for export] *)
    Control.once (fun () =>
      Control.plus (fun () => sf_step z)
        (fun e => (if sf_debug then printf "STEPFAST-FALLBACK %a" (fun () e => Message.of_exn e) e else ()); sf_old z))
  else sf_dual z.

(* [comment removed for export] *)
Ltac2 sf_core (z : bool) : unit := Control.enter (fun () => sf_core1 z).

Ltac sf_step_dual := ltac2:(sf_dual false).
Ltac sf_zstep_dual := ltac2:(sf_dual true).
Ltac sf_step_fast := ltac2:(sf_step false).
Ltac sf_zstep_fast := ltac2:(sf_step true).

(* [comment removed for export] *)
Ltac sf_step_core segs R F pc fc rv m ro := ltac2:(sf_core false).
Ltac sf_zstep := ltac2:(sf_core true).

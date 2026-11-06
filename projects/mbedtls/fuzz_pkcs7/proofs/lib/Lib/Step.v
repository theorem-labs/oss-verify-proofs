(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Exec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Export AEvt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Export FP ZBridge.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Definition ro_cells (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  cells_at segs m A cs.
Definition rw_cells (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  cells_at segs m A cs /\ wr_at segs m A (Z.of_nat (cells_size cs)).

#[using="Type"] Lemma rw_cells_read : forall m A cs k c,
  rw_cells m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof. intros m A cs k c [H _]. apply cells_at_read. exact H. Qed.

#[using="Type"] Lemma ro_cells_read : forall m A cs k c,
  ro_cells m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof. intros m A cs k c H. apply cells_at_read. exact H. Qed.

#[using="Type"] Lemma rw_cells_readn : forall m A cs k c n,
  rw_cells m A cs -> cell_at cs k = Some c -> n = csize c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) n = Some (cbytes c).
Proof. intros; subst; eapply rw_cells_read; eauto. Qed.

#[using="Type"] Lemma ro_cells_readn : forall m A cs k c n,
  ro_cells m A cs -> cell_at cs k = Some c -> n = csize c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) n = Some (cbytes c).
Proof. intros; subst; eapply ro_cells_read; eauto. Qed.

#[using="Type"] Lemma rw_cells_read_at : forall m A cs k c n a,
  rw_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a n = Some (cbytes c).
Proof. intros; subst; eapply rw_cells_read; eauto. Qed.

#[using="Type"] Lemma ro_cells_read_at : forall m A cs k c n a,
  ro_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a n = Some (cbytes c).
Proof. intros; subst; eapply ro_cells_read; eauto. Qed.

#[using="Type"] Lemma rw_cells_cb_split : forall m A cs cs2 k n,
  rw_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> rw_cells m A cs2.
Proof.
  intros m A cs cs2 k n [Hc Hw] Hok ->. split.
  - apply cells_at_cb_split; assumption.
  - rewrite cells_size_cb_split; [exact Hw| exact (cells_at_wf _ _ _ _ Hc) | exact Hok].
Qed.

#[using="Type"] Lemma ro_cells_cb_split : forall m A cs cs2 k n,
  ro_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> ro_cells m A cs2.
Proof. intros m A cs cs2 k n Hc Hok ->. apply cells_at_cb_split; assumption. Qed.

#[using="Type"] Lemma cell_at_bound : forall cs k c, cell_at cs k = Some c -> (k + csize c <= cells_size cs)%nat.
Proof.
  intros cs k c H. destruct (cell_at_split cs k c c H) as (pre & post & -> & Hsz & _).
  rewrite cells_size_app. cbn. lia.
Qed.

#[using="Type"] Lemma rw_cells_store_ok : forall m A cs k c (j : nat),
  rw_cells m A cs -> cell_at cs k = Some c -> j = csize c ->
  store_ok segs m (wa (A + Z.of_nat k)) j = true.
Proof.
  intros m A cs k c j [Hc Hw] Hk ->. pose proof (cell_at_bound _ _ _ Hk).
  apply (wr_at_store_ok segs m A (Z.of_nat (cells_size cs))); [exact Hw| lia | lia].
Qed.

#[using="Type"] Lemma rw_cells_store_ok_at : forall m A cs k c (j : nat) a,
  rw_cells m A cs -> cell_at cs k = Some c -> j = csize c -> a = wa (A + Z.of_nat k) ->
  store_ok segs m a j = true.
Proof. intros; subst. eapply rw_cells_store_ok; eauto. Qed.

#[using="Type"] Lemma rw_cells_write : forall m A cs k c c',
  rw_cells m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
  rw_cells (write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) A (cell_upd cs k c').
Proof.
  intros m A cs k c c' [Hc Hw] Hk Hsz Hwf. split.
  - eapply cells_at_write; eauto.
  - destruct (cell_at_split cs k c c' Hk) as (pre & post & -> & Hszp & ->).
    rewrite cells_size_app in *. cbn [cells_size] in *. rewrite Hsz. apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma rw_cells_frame : forall m A cs (a : Z) bs,
  rw_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  rw_cells (write_to_mem m (wa a) bs) A cs.
Proof.
  intros m A cs a bs [Hc Hw] Ha Hl Hd. split.
  - apply cells_at_frame; assumption.
  - apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma ro_cells_frame : forall m A cs (a : Z) bs,
  ro_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  ro_cells (write_to_mem m (wa a) bs) A cs.
Proof. intros. apply cells_at_frame; assumption. Qed.

#[using="Type"] Lemma rw_cells_bound : forall m A cs, rw_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. intros m A cs [H _]. eapply cells_at_bound; eauto. Qed.
#[using="Type"] Lemma ro_cells_bound : forall m A cs, ro_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. intros m A cs H. eapply cells_at_bound; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mem_inv_store_cbytes : forall m a c',
  mem_inv segs m -> cell_wf c' -> store_ok segs m a (csize c') = true ->
  mem_inv segs (write_to_mem m a (cbytes c')).
Proof.
  intros m a c' Hinv Hwf Hok. apply mem_inv_store; [assumption|].
  rewrite cbytes_length by assumption. exact Hok.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma unsigned_Z_to_bv_add : forall e d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) + d) = Z_to_bv 64 (e + d).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_Z_to_bv_add_r : forall e d, Z_to_bv 64 (d + bv_unsigned (Z_to_bv 64 e)) = Z_to_bv 64 (d + e).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma unsigned_Z_to_bv_sub : forall e d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) - d) = Z_to_bv 64 (e - d).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma bv_add_canon : forall (x y : word), (x + y : word) = Z_to_bv 64 (bv_unsigned x + bv_unsigned y).
Proof. intros. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

Lemma Z_to_bv_lit_self : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma wa_of_Z_to_bv : forall E e, E = e -> wa e = Z_to_bv 64 E.
Proof. intros; subst; reflexivity. Qed.
Lemma wa_of_var : forall (x : word) e, bv_unsigned x = e -> wa e = x.
Proof. intros; subst. unfold wa. apply Z_to_bv_lit_self. Qed.

Lemma store_bytes_8' : forall v : word, Z_to_le_bytes 8 (bv_unsigned v) = le8 v.
Proof. exact store_bytes_8. Qed.
Lemma store_bytes_4' : forall v : word, Z_to_le_bytes 4 (bv_unsigned (low32 v)) = le4 v.
Proof. exact store_bytes_4. Qed.
Lemma store_bytes_2' : forall v : word, Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 v)) = le2 v.
Proof. exact store_bytes_2. Qed.
Lemma store_bytes_1' : forall v : word, Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 v)) = le1 v.
Proof. exact store_bytes_1. Qed.
(* [comment removed for export] *)
Lemma store_bytes_8z : Z_to_le_bytes 8 0 = le8 (Z_to_bv 64 0). Proof. reflexivity. Qed.
Lemma store_bytes_4z : Z_to_le_bytes 4 0 = le4 (Z_to_bv 64 0). Proof. reflexivity. Qed.
Lemma store_bytes_2z : Z_to_le_bytes 2 0 = le2 (Z_to_bv 64 0). Proof. reflexivity. Qed.
Lemma store_bytes_1z : Z_to_le_bytes 1 0 = le1 (Z_to_bv 64 0). Proof. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma evt_step_gen : forall segs Q R F pc fc rv m ro w i sz ms1,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro w i sz ms1 Hf He Hd Hx Hq. eapply evt_step; [|exact Hq].
  split; [reflexivity|]. rewrite (step_gen segs R F pc fc rv m ro w i sz Hf He Hd). exact Hx.
Qed.

Lemma aevtM_step_gen : forall segs mo Q R F pc fc rv m ro w i sz ms1,
  MOK mo ->
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  aevtM segs mo Q ms1 -> aevtM segs mo Q (MS R F pc fc rv m ro).
Proof.
  intros segs mo Q R F pc fc rv m ro w i sz ms1 Hm Hf He Hd Hx Hq. eapply aevtM_step; [exact Hm| |exact Hq].
  split; [reflexivity|]. rewrite (step_gen segs R F pc fc rv m ro w i sz Hf He Hd). exact Hx.
Qed.

(* [comment removed for export] *)
Fixpoint reads_imp (R0 : bvmap 5 word) (l : list (bv 5 * word)) (P : Prop) : Prop :=
  match l with
  | [] => P
  | (r, v) :: l' => reg_get R0 r = v -> reads_imp R0 l' P
  end.
Fixpoint reads_all (R0 : bvmap 5 word) (l : list (bv 5 * word)) : Prop :=
  match l with
  | [] => True
  | (r, v) :: l' => reg_get R0 r = v /\ reads_all R0 l'
  end.
Lemma reads_imp_elim : forall R0 l P, reads_imp R0 l P -> reads_all R0 l -> P.
Proof. induction l as [|[r v] l IH]; cbn; intros P H HA; [exact H | destruct HA as [H1 H2]; exact (IH P (H H1) H2)]. Qed.

Lemma evt_step_r : forall segs Q R F pc fc rv m ro w i sz (rds : list (bv 5 * word)) (g : bvmap 5 word -> machine_state),
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  (forall R0, reads_imp R0 rds
     (lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R0 F pc fc rv)) m) = MachineOk (g R0))) ->
  reads_all R rds ->
  evt segs Q (g R) -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro w i sz rds g Hf He Hd Hx Hr Hq.
  eapply (evt_step_gen segs Q R F pc fc rv m ro w i sz (g R) Hf He Hd); [|exact Hq].
  exact (reads_imp_elim R rds _ (Hx R) Hr).
Qed.

Lemma aevtM_step_r : forall segs mo Q R F pc fc rv m ro w i sz (rds : list (bv 5 * word)) (g : bvmap 5 word -> machine_state),
  MOK mo ->
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  (forall R0, reads_imp R0 rds
     (lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R0 F pc fc rv)) m) = MachineOk (g R0))) ->
  reads_all R rds ->
  aevtM segs mo Q (g R) -> aevtM segs mo Q (MS R F pc fc rv m ro).
Proof.
  intros segs mo Q R F pc fc rv m ro w i sz rds g Hm Hf He Hd Hx Hr Hq.
  eapply (aevtM_step_gen segs mo Q R F pc fc rv m ro w i sz (g R) Hm Hf He Hd); [|exact Hq].
  exact (reads_imp_elim R rds _ (Hx R) Hr).
Qed.

(* [comment removed for export] *)
Definition fetch_dec (segs : list Segment) (pc : word) : option (instr * Z) :=
  match fetch_word segs pc with
  | Some w => if is_ecall w then None else decode_any w
  | None => None
  end.

Lemma evt_step_f : forall segs Q R F pc fc rv m ro i sz (rds : list (bv 5 * word)) (g : bvmap 5 word -> machine_state),
  fetch_dec segs pc = Some (i, sz) ->
  (forall R0, reads_imp R0 rds
     (lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R0 F pc fc rv)) m) = MachineOk (g R0))) ->
  reads_all R rds ->
  evt segs Q (g R) -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro i sz rds g Hfd Hx Hr Hq. unfold fetch_dec in Hfd.
  destruct (fetch_word segs pc) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  exact (evt_step_r segs Q R F pc fc rv m ro w i sz rds g Hf He Hfd Hx Hr Hq).
Qed.

Lemma aevtM_step_f : forall segs mo Q R F pc fc rv m ro i sz (rds : list (bv 5 * word)) (g : bvmap 5 word -> machine_state),
  MOK mo ->
  fetch_dec segs pc = Some (i, sz) ->
  (forall R0, reads_imp R0 rds
     (lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R0 F pc fc rv)) m) = MachineOk (g R0))) ->
  reads_all R rds ->
  aevtM segs mo Q (g R) -> aevtM segs mo Q (MS R F pc fc rv m ro).
Proof.
  intros segs mo Q R F pc fc rv m ro i sz rds g Hm Hfd Hx Hr Hq. unfold fetch_dec in Hfd.
  destruct (fetch_word segs pc) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  exact (aevtM_step_r segs mo Q R F pc fc rv m ro w i sz rds g Hm Hf He Hfd Hx Hr Hq).
Qed.

(* [comment removed for export] *)
Definition R31 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) : bvmap 5 word :=
  TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty)))
       (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2)
       (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cbv_concl_beta_iota :=
  idtac;   (* [comment removed for export] *)
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota in g in set_concl g'.
Ltac cbv_concl_iota :=
  idtac;
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv iota in g in set_concl g'.
Ltac cbv_concl_zeta :=
  idtac;
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv zeta in g in set_concl g'.

Ltac slia := first [ exact I | lia | split; [lia|exact I] ].

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac det_vdefs_absent :=
  assert_fails (progress (cbv delta [v_addi v_add v_sub v_mul v_andi v_ori v_xori v_and v_or v_xor
         v_slli v_srli v_srai v_sll v_srl v_sra v_lui v_auipc
         v_addiw v_slliw v_srliw v_sraiw v_addw v_subw v_sllw v_srlw v_sraw
         v_mulh v_mulhsu v_mulhu v_mulw btgt])).
Ltac det_isa_absent := assert_fails (progress (cbv delta [alu64 alu32 mul_div sext])).

(* [comment removed for export] *)
Ltac fold_closed_loop :=
  repeat match goal with
  | |- context [bv_unsigned (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_unsigned (@BV n z p)) in change (bv_unsigned (@BV n z p)) with v
  | |- context [bv_signed (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_signed (@BV n z p)) in change (bv_signed (@BV n z p)) with v
  | |- context [bv_signed (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_signed (bv_concat n a b)) in is_Zlit v; change (bv_signed (bv_concat n a b)) with v
  | |- context [bv_unsigned (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_unsigned (bv_concat n a b)) in is_Zlit v; change (bv_unsigned (bv_concat n a b)) with v
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
        replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
        replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.shiftr ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [bv_swrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_swrap n z) in
        replace (bv_swrap n z) with v by (vm_compute; reflexivity)
  | |- context [bv_wrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v by (vm_compute; reflexivity)
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  | |- context [Z.add (Z.add ?x ?a) ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in
        replace (Z.add (Z.add x a) b) with (Z.add x v) by (exact (Z.add_assoc x a b))
  | |- context [Z_to_bv 64 (Z.add ?x 0)] => rewrite (Z.add_0_r x)
  end.

(* [comment removed for export] *)
Ltac fcg_maybe :=
  first
  [ lazymatch goal with |- context [@BV _ _ _] => idtac end
  | lazymatch goal with |- context [bv_concat] => idtac end
  | tryif det_bitops_absent then fail else idtac
  | match goal with |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z end
  | match goal with |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z end
  | match goal with |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b end
  | match goal with |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b end
  | match goal with |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b end
  | match goal with |- context [Z.add (Z.add ?x ?a) ?b] => is_Zlit a; is_Zlit b end
  | lazymatch goal with |- context [Z_to_bv 64 (Z.add _ 0)] => idtac end ].
Ltac fold_closed_in_goal := tryif fcg_maybe then fold_closed_loop else idtac.

(* [comment removed for export] *)
Ltac fold_lit_load :=
  repeat match goal with
  | |- context [bv_extract 0 ?n (le_bytes_to_word ?bs)] =>
      lazymatch bs with (_ :: _)%list => idtac end;
      let t := constr:(bv_extract 0 n (le_bytes_to_word bs)) in
      let z := eval vm_compute in (bv_unsigned t) in
      is_Zlit z;
      rewrite (bv_lit_eq n t z) by (vm_compute; reflexivity)
  | |- context [@sext ?k 64 (Z_to_bv ?k ?z)] =>
      is_Zlit z;
      let t := constr:(@sext k 64 (Z_to_bv k z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [@zext ?k 64 (Z_to_bv ?k ?z)] =>
      is_Zlit z;
      let t := constr:(@zext k 64 (Z_to_bv k z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [low32 (Z_to_bv 64 ?z)] =>
      is_Zlit z;
      let t := constr:(low32 (Z_to_bv 64 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 32 t z') by (vm_compute; reflexivity)
  | |- context [nan_box (Z_to_bv 32 ?z)] =>
      is_Zlit z;
      let t := constr:(nan_box (Z_to_bv 32 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  end.

(* [comment removed for export] *)
Ltac simp_is_x0 :=
  repeat match goal with
  | |- context [is_x0 ?r] => let v := eval vm_compute in (is_x0 r) in change (is_x0 r) with v
  end; cbv_concl_beta_iota.

(* [comment removed for export] *)
Ltac is_concrete_map R := lazymatch R with TNode _ _ _ => idtac | TEmpty => idtac end.
Ltac map_cbv_get :=
  idtac;
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tget] in g in set_concl g'.
Ltac map_cbv_set :=
  idtac;
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tset] in g in set_concl g'.

Ltac norm_fchain :=
  repeat match goal with
  | |- context [@bvmap_set 5 word ?k ?x (@bvmap_set 5 word ?k' ?y ?R)] =>
      let a := eval vm_compute in (bv_unsigned k) in
      let b := eval vm_compute in (bv_unsigned k') in
      let c := eval vm_compute in (Z.compare a b) in
      lazymatch c with
      | Eq => rewrite (bvmap_set_set_same' k k' x y R) by reflexivity
      | Gt => rewrite (bvmap_set_set_comm k k' x y R) by reflexivity
      end
  end.

Ltac simp_regs :=
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (reg_get R r) with (match tget p R with Some v => v | None => w0 end);
      map_cbv_get
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (tset p v R);
      map_cbv_set
  | |- context [reg_get (@bvmap_set 5 word ?k ?v ?R) ?r] =>
      first [ rewrite (freg_get_same R k r v) by reflexivity
            | rewrite (freg_get_other R k r v) by reflexivity ]
  end;
  norm_fchain.

(* [comment removed for export] *)
Ltac exec_eval t :=
  eval cbv beta iota zeta delta [lift_result interp_eff0 exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s] in t.
Ltac exec_cbv :=
  idtac;
  let g := lazymatch goal with |- ?g => g end in
  let g' := exec_eval g in set_concl g'.

(* [comment removed for export] *)
Ltac vnorm_rw_table i :=
  lazymatch i with
  | OpImm ALU_ADD _ _ _ => rewrite ?alu_addi
  | OpImm ALU_AND _ _ _ => rewrite ?alu_andi
  | OpImm ALU_OR _ _ _ => rewrite ?alu_ori
  | OpImm ALU_XOR _ _ _ => rewrite ?alu_xori
  | OpImm ALU_SLT _ _ _ => rewrite ?alu_slti
  | OpImm ALU_SLTU _ _ _ => rewrite ?alu_sltiu
  | ShiftImm ALU_SLL _ _ _ => rewrite ?alu_slli
  | ShiftImm ALU_SRL _ _ _ => rewrite ?alu_srli
  | ShiftImm ALU_SRA _ _ _ => rewrite ?alu_srai
  | Op ALU_ADD _ _ _ => rewrite ?alu_add
  | Op ALU_SUB _ _ _ => rewrite ?alu_sub
  | Op ALU_SLT _ _ _ => rewrite ?alu_slt
  | Op ALU_SLTU _ _ _ => rewrite ?alu_sltu
  | Op ALU_AND _ _ _ => rewrite ?alu_and
  | Op ALU_OR _ _ _ => rewrite ?alu_or
  | Op ALU_XOR _ _ _ => rewrite ?alu_xor
  | Op ALU_SLL _ _ _ => rewrite ?alu_sll
  | Op ALU_SRL _ _ _ => rewrite ?alu_srl
  | Op ALU_SRA _ _ _ => rewrite ?alu_sra
  | OpImm32 _ _ _ => rewrite ?w_addiw
  | ShiftImm32 ALU_SLL _ _ _ => rewrite ?w_slliw
  | ShiftImm32 ALU_SRL _ _ _ => rewrite ?w_srliw
  | ShiftImm32 ALU_SRA _ _ _ => rewrite ?w_sraiw
  | Op32 ALU_ADD _ _ _ => rewrite ?w_addw
  | Op32 ALU_SUB _ _ _ => rewrite ?w_subw
  | Op32 ALU_SLL _ _ _ => rewrite ?w_sllw
  | Op32 ALU_SRL _ _ _ => rewrite ?w_srlw
  | Op32 ALU_SRA _ _ _ => rewrite ?w_sraw
  | Mul M_MUL _ _ _ => rewrite ?m_mul
  | Mul M_MULH _ _ _ => rewrite ?m_mulh
  | Mul M_MULHSU _ _ _ => rewrite ?m_mulhsu
  | Mul M_MULHU _ _ _ => rewrite ?m_mulhu
  | Mul M_DIV _ _ _ => rewrite ?m_div
  | Mul M_REM _ _ _ => rewrite ?m_rem
  | Mul32 M_MUL _ _ _ => rewrite ?w_mulw
  | Mul32 M_DIV _ _ _ => rewrite ?w_divw
  | Mul32 M_REM _ _ _ => rewrite ?w_remw
  | Mul32 M_DIVU _ _ _ => rewrite ?w_divuw
  | Mul32 M_REMU _ _ _ => rewrite ?w_remuw
  | Lui _ _ => rewrite ?b_lui
  | Auipc _ _ => rewrite ?b_auipc
  | Load _ _ _ _ _ => rewrite ?b_addsext
  | Store _ _ _ _ => rewrite ?b_addsext
  | FLoad _ _ _ _ => rewrite ?b_addsext
  | FStore _ _ _ _ => rewrite ?b_addsext
  | Jalr _ _ _ => rewrite ?b_addsext
  | Jal _ _ => rewrite ?b_addsext
  | Branch _ _ _ _ => rewrite ?b_addsext
  (* [comment removed for export] *)
  | Fsgnj _ _ _ _ _ => rewrite ?sgnj_self, ?sgnjx_self, ?sgnjn_self
  | Fmv _ _ _ _ => rewrite ?fmv_x_w_val; fold_lit_load
  | Fari _ _ _ _ _ _ => idtac
  | Fcmp _ _ _ _ _ => idtac
  | Fcvt _ _ _ _ _ => idtac
  | Fsqrt _ _ _ _ => idtac
  | Fminmax _ _ _ _ _ => idtac
  | Fclass _ _ _ => idtac
  | Csr _ _ _ _ => idtac
  | CsrI _ _ _ _ => idtac
  | _ =>
  rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
          ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
          ?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
          ?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
          ?b_addsext, ?b_lui, ?b_auipc
  end.

(* [comment removed for export] *)
Ltac vnorm_rw_for i :=
  lazymatch i with
  | Fsgnj _ _ _ _ _ => vnorm_rw_table i
  | Fmv _ _ _ _ => vnorm_rw_table i
  | Fari _ _ _ _ _ _ => idtac
  | Fcmp _ _ _ _ _ => idtac
  | Fcvt _ _ _ _ _ => idtac
  | Fsqrt _ _ _ _ => idtac
  | Fminmax _ _ _ _ _ => idtac
  | Fclass _ _ _ => idtac
  | Csr _ _ _ _ => idtac
  | CsrI _ _ _ _ => idtac
  | _ => tryif det_isa_absent then idtac else vnorm_rw_table i
  end.

Ltac vnorm_tail :=
  (match goal with |- context [@bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 _)] => rewrite ?lit_add_lit | _ => idtac end);
  (match goal with |- context [w0] => rewrite ?w0_lit | _ => idtac end);
  (match goal with |- context [w1] => rewrite ?w1_lit | _ => idtac end);
  (tryif det_vdefs_absent then idtac else
   (let g := lazymatch goal with |- ?g => g end in
    let g' := eval unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
         v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
         v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
         v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt in g in
    set_concl g'));
  (match goal with |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r | _ => idtac end);
  fold_closed_in_goal;
  (match goal with |- context [Z_to_bv 64 (bv_unsigned _)] => rewrite ?Z_to_bv_lit_self | _ => idtac end);
  (match goal with |- context [bv_and _ (bv_not _)] => rewrite ?ret_pc_fold | _ => idtac end);
  (* [comment removed for export] *)
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Ltac vnorm_for i := vnorm_rw_for i; vnorm_tail.

(* [comment removed for export] *)
Ltac vnorm_tail_ref :=
  (match goal with |- context [@bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 _)] => rewrite ?lit_add_lit | _ => idtac end);
  (match goal with |- context [w0] => rewrite ?w0_lit | _ => idtac end);
  (match goal with |- context [w1] => rewrite ?w1_lit | _ => idtac end);
  unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
         v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
         v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
         v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt;
  (match goal with |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r | _ => idtac end);
  fold_closed_loop;
  (match goal with |- context [Z_to_bv 64 (bv_unsigned _)] => rewrite ?Z_to_bv_lit_self | _ => idtac end);
  (match goal with |- context [bv_and _ (bv_not _)] => rewrite ?ret_pc_fold | _ => idtac end);
  (* [comment removed for export] *)
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

Ltac vnorm_for_ref i := vnorm_rw_table i; vnorm_tail_ref.

Ltac vnorm :=
  rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
          ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
          ?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
          ?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
          ?b_addsext, ?b_lui, ?b_auipc, ?lit_add_lit, ?w0_lit, ?w1_lit;
  unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
         v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
         v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
         v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt;
  rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r;
  fold_closed_in_goal;
  rewrite ?Z_to_bv_lit_self, ?ret_pc_fold;
  (* [comment removed for export] *)
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zlit a := lazymatch a with Z0 => a | Zpos _ => a | Zneg _ => a end.

Ltac addr_diff_raw E A :=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
      | X => zlit c1
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  end.
(* [comment removed for export] *)
Ltac addr_diff E A :=
  let k := addr_diff_raw E A in
  lazymatch eval vm_compute in (Z.leb 0 k) with true => k end.

(* [comment removed for export] *)
Ltac addr_expr a :=
  lazymatch a with
  | Z_to_bv 64 ?E => E
  | wa ?E => E
  | _ => constr:(Z.add (bv_unsigned a) 0)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac tb_alia := first [ solve [cbv beta iota delta [Z.of_nat Pos.of_succ_nat Pos.succ]; zify_keep_goal_vars; Z.euclidean_division_equations_cleanup; xlia zchecker] | lia ].
Ltac addr_eq_tac := symmetry; first [ apply wa_of_Z_to_bv; tb_alia | apply wa_of_var; tb_alia | unfold wa; f_equal; tb_alia ].

Ltac cells_cbv := cbv beta iota zeta delta [cell_at cell_upd csize cells_size Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add cbytes].

Ltac eval_cb_split cs kn n :=
  eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split cs kn n).
Ltac eval_cb_split_ok cs kn n :=
  eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split_ok cs kn n).

(* [comment removed for export] *)
Ltac split_for_access H segs m A cs kn n :=
  let ok := eval_cb_split_ok cs kn n in
  lazymatch ok with
  | true =>
      let cs2 := eval_cb_split cs kn n in
      lazymatch cs2 with
      | cs => idtac
      | _ => first [ apply (rw_cells_cb_split segs m A cs cs2 kn n) in H
                   | apply (ro_cells_cb_split segs m A cs cs2 kn n) in H ];
             [ | cells_cbv; reflexivity | cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app]; reflexivity ]
      end
  end.

Ltac eval_cell_at cs kn := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn).



(* [comment removed for export] *)
Ltac load_post :=
  (let g := lazymatch goal with |- ?g => g end in
   let g' := eval cbv beta iota delta [cbytes] in g in set_concl g');
  rewrite ?load_u64, ?zext_extract_le4, ?sext_extract_le4, ?zext_extract_le2, ?sext_extract_le2,
          ?zext_extract_le1, ?sext_extract_le1, ?zext_extract_byte, ?sext_extract_byte;
  fold_lit_load.

(* [comment removed for export] *)
Ltac solve_load_base :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | (* [comment removed for export] *)
                replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

(* [comment removed for export] *)

Ltac solve_load := solve_load_base.

Ltac solve_store :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1', ?store_bytes_8z, ?store_bytes_4z, ?store_bytes_2z, ?store_bytes_1z;
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
          cbv_concl_beta_iota;
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
                (* [comment removed for export] *)
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv_concl_beta_iota
    end
  end.

(* [comment removed for export] *)
Ltac cell_of_bytes bs :=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  end.

(* [comment removed for export] *)
Ltac bn_poslit p := lazymatch p with xI ?q => bn_poslit q | xO ?q => bn_poslit q | xH => idtac end.
Ltac bn_big k :=
  let z := eval lazy [Z.of_nat Pos.of_succ_nat Pos.succ] in (Z.of_nat k) in
  lazymatch z with Zpos ?p => bn_poslit p; let b := eval cbv in (Z.leb 256 z) in lazymatch b with true => idtac end end.
Ltac bn_sizes :=
  repeat match goal with
  | |- context [cells_size ?cs] =>
      let k := eval lazy [cells_size csize Nat.add] in (cells_size cs) in bn_big k; change (cells_size cs) with k
  end.
Ltac bn_sizes_in H :=
  repeat match type of H with
  | context [cells_size ?cs] =>
      let k := eval lazy [cells_size csize Nat.add] in (cells_size cs) in bn_big k; change (cells_size cs) with k in H
  end.
Ltac simpl_sizes :=
  rewrite ?app_length; bn_sizes;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].

(* [comment removed for export] *)
Ltac sf_a0 := first [ assumption | lia ].
Ltac sf_al := first [ assumption | simpl_sizes; slia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac tb_collect segs m a bs seen :=
  match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      let ok := lazymatch seen with context [H] => fail | _ => constr:(tt) end in
      let rest := tb_collect segs m a bs constr:((H, seen)) in
      constr:(((H, bytes_at_write_other segs m a bs A2 bs2), rest))
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      let ok := lazymatch seen with context [H] => fail | _ => constr:(tt) end in
      let rest := tb_collect segs m a bs constr:((H, seen)) in
      constr:(((H, rw_cells_frame segs m A2 cs2 a bs), rest))
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      let ok := lazymatch seen with context [H] => fail | _ => constr:(tt) end in
      let rest := tb_collect segs m a bs constr:((H, seen)) in
      constr:(((H, ro_cells_frame segs m A2 cs2 a bs), rest))
  | _ => constr:(tt)
  end.

(* [comment removed for export] *)
Ltac tb_cells_cbv := cbv beta iota delta [cells_size csize cbytes Nat.add].
Ltac tb_simpl :=
  tb_cells_cbv;
  repeat match goal with
  | |- context [length (le8 ?v)] => change (length (le8 v)) with 8%nat
  | |- context [length (le4 ?v)] => change (length (le4 v)) with 4%nat
  | |- context [length (le2 ?v)] => change (length (le2 v)) with 2%nat
  | |- context [length (le1 ?v)] => change (length (le1 v)) with 1%nat
  end;
  cbv beta iota delta [Z.of_nat Pos.of_succ_nat Pos.succ].

(* [comment removed for export] *)
Ltac tb_free :=
  tb_simpl; zify_keep_goal_vars; Z.euclidean_division_equations_cleanup; xlia zchecker.

(* [comment removed for export] *)
Ltac tb_light_core HB :=
  generalize HB; tb_simpl; zify_keep_goal_vars; intro; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac tb_light_a a :=
  lazymatch a with
  | (?A' + Z.of_nat _)%Z => lazymatch goal with HB : (0 <= A' /\ _)%Z |- _ => tb_light_core HB end
  end.
Ltac tb_light_l a := tb_light_a a.

Ltac tb_try_list lst Ha Hl :=
  lazymatch lst with
  | ((?H, ?L), ?rest) =>
      let D := lazymatch type of L with _ -> _ -> _ -> ?D -> _ => D end in
      let HD := fresh "HD_tb" in
      (tryif assert (HD : D) by tb_free
       then (apply L in H; [ | exact Ha | exact Hl | exact HD ]; clear HD)
       else idtac);
      tb_try_list rest Ha Hl
  | tt => idtac
  end.

Ltac transport_batch segs m a bs Ha Hl :=
  let lst := tb_collect segs m a bs constr:(tt) in
  tb_try_list lst Ha Hl.

Ltac transport_chunks segs m a bs :=
  let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in
  try (assert (Ha : (0 <= a)%Z) by first [tb_light_a a | lia]);
  try (assert (Hl : (a + Z.of_nat (length bs) <= 2^64)%Z) by first [tb_light_l a | (simpl_sizes; slia)]);
  (lazymatch goal with
   | Ha' : (0 <= a)%Z, Hl' : (a + Z.of_nat (length bs) <= 2^64)%Z |- _ => transport_batch segs m a bs Ha' Hl'
   | _ => idtac
   end);
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | sf_a0 | sf_al | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end;
  try clear Ha; try clear Hl.

Ltac mem_after_store :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) (seg_rom ?segs)) =>
    let c' := cell_of_bytes bs in
    lazymatch goal with
    | H : rw_cells segs m A ?cs |- _ =>
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          (* [comment removed for export] *)
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
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store_opt :=
  lazymatch goal with
  | |- _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rm_proof rm c :=
  let z := eval vm_compute in (bv_unsigned rm) in
  lazymatch z with
  | 7%Z =>
      lazymatch c with
      | Core _ _ _ ?fc _ =>
          lazymatch goal with
          | FRM : frm0 fc |- _ => constr:(rmode_dyn rm c (@eq_refl Z 7%Z) FRM)
          | _ => fail 100 "FP instruction with dynamic rounding mode: need a hypothesis [frm0" fc "]"
          end
      end
  | _ =>
      let md := eval vm_compute in (match rmode_of_Z z with Some md => md | None => RNE end) in
      constr:(rmode_static rm c md (@eq_refl bool false) (@eq_refl (option rmode) (Some md)))
  end.

(* [comment removed for export] *)
Ltac exec_pre i :=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
    | Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
    | Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv_concl_zeta
    | Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
    | Csr ?op ?rd ?rs1 ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv_concl_zeta;
            simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv_concl_iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | CsrI ?op ?rd ?uimm ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv_concl_zeta;
            let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
            try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv_concl_iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | _ => idtac
    end
  end;
  (* [comment removed for export] *)
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

(* [comment removed for export] *)
Ltac prove_frm0 :=
  first [ assumption
        | apply frm0_accrue; prove_frm0
        | apply frm0_slice_set_fflags; prove_frm0 ].

Ltac norm_fcsr :=
  lazymatch goal with
  | |- _ (MS _ _ _ ?fce _ _ _) =>
      tryif is_var fce then idtac else
      (let fcn := fresh "fc" in
       let E := fresh "Efc" in
       tryif (let H := fresh "FRM" in
              assert (H : frm0 fce) by prove_frm0;
              repeat match goal with
              | H' : frm0 ?f |- _ => lazymatch f with fce => fail | _ => clear H' end
              end;
              remember fce as fcn eqn:E; clear E;
              try rename H into FRM)
       then idtac
       else (remember fce as fcn eqn:E; clear E))
  | _ => idtac
  end.

Ltac post_step i :=
  lazymatch i with
  | Fari _ _ _ _ _ _ => norm_fcsr
  | Fcmp _ _ _ _ _ => norm_fcsr
  | Fcvt _ _ _ _ _ => norm_fcsr
  | Fsqrt _ _ _ _ => norm_fcsr
  | Fminmax _ _ _ _ _ => norm_fcsr
  | Fma _ _ _ _ _ _ _ => norm_fcsr
  | Csr _ _ _ _ => norm_fcsr
  | CsrI _ _ _ _ => norm_fcsr
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac apply_step_lemma :=
  lazymatch goal with
  | |- evt _ _ _ => eapply evt_step
  | |- aevtM _ _ _ _ => eapply aevtM_step; [ eassumption | | ]
  | |- ?g => fail "apply_step_lemma: goal is neither evt nor aevtM"
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac step_core_ref segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        apply_step_lemma;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for_ref i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for_ref i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac regs_read_eval t := eval cbv beta iota delta [tget] in t.

(* [comment removed for export] *)
Ltac collect_reads body R acc :=
  match body with
  | context [reg_get _ ?r] =>
      lazymatch acc with
      | context [(r, _)] => fail
      | _ =>
        let p := eval vm_compute in (bv_key r) in
        let v := regs_read_eval (match tget p R with Some v => v | None => w0 end) in
        collect_reads body R constr:((r, v) :: acc)
      end
  | _ => acc
  end.

(* [comment removed for export] *)
Ltac reads_all_proof rds :=
  lazymatch rds with
  | nil => constr:(I)
  | (?r, ?v) :: ?l =>
      let pl := reads_all_proof l in
      let tl := type of pl in
      constr:(@conj (@eq word v v) tl (@eq_refl word v) pl)
  end.
Ltac reads_imp_unfold R0 rds P :=
  lazymatch rds with
  | nil => P
  | (?r, ?v) :: ?l => let rest := reads_imp_unfold R0 l P in constr:(reg_get R0 r = v -> rest)
  end.
Ltac intro_reads rds :=
  lazymatch rds with
  | nil => idtac
  | _ :: ?l => let H := fresh "Hrd" in intro H; intro_reads l
  end.
Ltac use_reads R0 :=
  repeat match goal with
  | H : reg_get R0 _ = _ |- _ => try rewrite H; clear H
  end.

(* [comment removed for export] *)
Ltac slim_norm_state s rd :=
  let ST := type of s in
  let pf := constr:(ltac:(eexists; rd; simp_regs; reflexivity) : exists y : ST, s = y) in
  lazymatch pf with
  | ex_intro _ ?s' _ => s'
  end.

(* [comment removed for export] *)
Ltac is_plain_insn i :=
  lazymatch i with
  | Fari _ _ _ _ _ _ => fail | Fsqrt _ _ _ _ => fail | Fcmp _ _ _ _ _ => fail | Fminmax _ _ _ _ _ => fail
  | Fcvt _ _ _ _ _ => fail | Csr _ _ _ _ => fail | CsrI _ _ _ _ => fail
  | _ => idtac
  end.

Ltac fold_R31 R :=
  lazymatch R with
  | TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) =>
      constr:(R31 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
  end.

(* [comment removed for export] *)
Ltac step_f_lemma segs R Rf F pc fc rv m ro i sz rds :=
  lazymatch goal with
  | |- evt _ ?Q _ =>
      (lazymatch Rf with R => idtac | _ => change_no_check (evt segs Q (MS Rf F (Z_to_bv 64 pc) fc rv m ro)) end);
      eapply (evt_step_f segs Q Rf F (Z_to_bv 64 pc) fc rv m ro i sz rds);
      [ vm_compute; reflexivity | | | ]
  | |- aevtM _ ?mo ?Q _ =>
      (lazymatch Rf with R => idtac | _ => change_no_check (aevtM segs mo Q (MS Rf F (Z_to_bv 64 pc) fc rv m ro)) end);
      eapply (aevtM_step_f segs mo Q Rf F (Z_to_bv 64 pc) fc rv m ro i sz rds);
      [ eassumption | vm_compute; reflexivity | | | ]
  | |- ?g => fail "step: goal is neither evt nor aevtM"
  end.

Ltac step_core_r segs R F pc fc rv m ro w i sz :=
  let t := constr:(fun R0 : bvmap 5 word =>
             lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R0 F (Z_to_bv 64 pc) fc rv)) m)) in
  let t' := exec_eval t in
  let rds := collect_reads t' R constr:(@nil (bv 5 * word)) in
  let hasreads := lazymatch rds with nil => constr:(false) | _ => constr:(true) end in
  let Rf := match constr:(tt) with _ => fold_R31 R | _ => R end in
  step_f_lemma segs R Rf F pc fc rv m ro i sz rds;
  [ (* [comment removed for export] *)
    let R0 := fresh "R0" in
    intro R0;
    lazymatch goal with |- reads_imp _ _ ?P => let G := reads_imp_unfold R0 rds P in change_no_check G end;
    intro_reads rds;
    (tryif is_plain_insn i
     then (lazymatch goal with
           | |- @eq ?MT _ ?rhs => let b := eval cbv beta in (t' R0) in change_no_check (@eq MT b rhs)
           end)
     else (exec_pre i; exec_cbv));
    simp_is_x0;
    use_reads R0;
    simp_regs; vnorm_for i; try solve_load; try solve_store;
    lazymatch goal with
    | |- @eq ?MT (@MachineOk ?A ?s) (@MachineOk _ (?gg _)) =>
        let gt := eval pattern R0 in s in
        lazymatch gt with
        | ?f _ => unify gg f; exact_no_check (@eq_refl MT (@MachineOk A s))
        end
    end
  | (* [comment removed for export] *)
    let pf := reads_all_proof rds in exact_no_check pf
  | (* [comment removed for export] *)
    lazymatch goal with
    | |- ?HD (?gg _) =>
        let s := eval cbv beta in (gg R) in   (* [comment removed for export] *)
        let s' := lazymatch hasreads with
                  | true => slim_norm_state s map_cbv_get
                  | false => slim_norm_state s idtac
                  end in
        change_no_check (HD s')
    end;
    simp_regs; vnorm_for i; mem_after_store_opt; post_step i ].

(* [comment removed for export] *)
Ltac step_core_g segs R F pc fc rv m ro w i sz :=
  lazymatch goal with
  | |- evt _ ?Q _ =>
      eapply (evt_step_gen segs Q R F (Z_to_bv 64 pc) fc rv m ro w i sz);
      [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | ]
  | |- aevtM _ ?mo ?Q _ =>
      eapply (aevtM_step_gen segs mo Q R F (Z_to_bv 64 pc) fc rv m ro w i sz);
      [ eassumption | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | ]
  | |- ?g => fail "step: goal is neither evt nor aevtM"
  end;
  [ exec_pre i; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
    try solve_load; try solve_store; reflexivity
  | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ].

Ltac step_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        tryif is_concrete_map R
        then step_core_r segs R F pc fc rv m ro w i sz
        else step_core_g segs R F pc fc rv m ro w i sz
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac step :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m (seg_rom ?segs)) => step_core segs R F pc fc rv m (seg_rom segs)
  | |- _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* [comment removed for export] *)
Ltac unfold_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb].
(* [comment removed for export] *)
Ltac fold_lit_ux :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
      replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
      replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  end.
Ltac solve_cond_base :=
  first [ reflexivity
        | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Z.leb_le; lia | apply Z.leb_gt; lia
        | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ].
Ltac solve_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec
  | _ => solve_cond_base
  end.
Ltac solve_cond := unfold_cond; fold_lit_ux; solve_cond_rec.
Ltac if_true :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      replace c with true; [cbv_concl_iota| symmetry; solve_cond]
  end.
Ltac if_false :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      replace c with false; [cbv_concl_iota| symmetry; solve_cond]
  end.
Ltac if_true_by H :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      replace c with true; [cbv_concl_iota| symmetry; exact H]
  end.
Ltac if_false_by H :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      replace c with false; [cbv_concl_iota| symmetry; exact H]
  end.
(* [comment removed for export] *)
Ltac if_cases H :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      destruct c eqn:H; [ | ]
  end.

(* [comment removed for export] *)
Ltac fold_lit_ux_in H :=
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
      replace (bv_unsigned (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
  | context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
      replace (bv_signed (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
  end.
(* [comment removed for export] *)
Ltac zify_bool H :=
  lazymatch type of H with
  | negb _ = true => apply (proj1 (Bool.negb_true_iff _)) in H; zify_bool H
  | negb _ = false => apply (proj1 (Bool.negb_false_iff _)) in H; zify_bool H
  | Z.eqb (Z.b2z ?b) 0 = true => apply Z.eqb_eq in H; apply (proj1 (zb_b2z_zero b)) in H; zify_bool H
  | Z.eqb (Z.b2z ?b) 0 = false => apply Z.eqb_neq in H; apply (proj1 (zb_b2z_nonzero b)) in H; zify_bool H
  | Z.eqb _ _ = true => apply Z.eqb_eq in H
  | Z.eqb _ _ = false => apply Z.eqb_neq in H
  | Z.ltb _ _ = true => apply Z.ltb_lt in H
  | Z.ltb _ _ = false => apply Z.ltb_ge in H
  | Z.leb _ _ = true => apply Z.leb_le in H
  | Z.leb _ _ = false => apply Z.leb_gt in H
  | andb _ _ = true =>
      apply andb_true_iff in H;
      let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
  | orb _ _ = false =>
      apply orb_false_iff in H;
      let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
  | _ => idtac
  end.

Ltac zify_cond H :=
  rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H;
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; zsimp_in H;
  zify_bool H.

(* [comment removed for export] *)
Ltac concretize_regs :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F ?pc ?fc ?rv ?m (seg_rom ?segs)) =>
      let t := eval vm_compute in R in change R with t
  end.

(* [comment removed for export] *)
Ltac zstep := step; zsimp.

(* [comment removed for export] *)
Ltac det_selftest_one det t := assert_succeeds (assert (t = t); [ tryif det then fail 1 "detector blind for" t else reflexivity | ]).
Lemma det_selftest : True.
Proof.
  det_selftest_one det_vdefs_absent v_addi. det_selftest_one det_vdefs_absent v_add. det_selftest_one det_vdefs_absent v_sub.
  det_selftest_one det_vdefs_absent v_mul. det_selftest_one det_vdefs_absent v_andi. det_selftest_one det_vdefs_absent v_ori.
  det_selftest_one det_vdefs_absent v_xori. det_selftest_one det_vdefs_absent v_and. det_selftest_one det_vdefs_absent v_or.
  det_selftest_one det_vdefs_absent v_xor. det_selftest_one det_vdefs_absent v_slli. det_selftest_one det_vdefs_absent v_srli.
  det_selftest_one det_vdefs_absent v_srai. det_selftest_one det_vdefs_absent v_sll. det_selftest_one det_vdefs_absent v_srl.
  det_selftest_one det_vdefs_absent v_sra. det_selftest_one det_vdefs_absent v_lui. det_selftest_one det_vdefs_absent v_auipc.
  det_selftest_one det_vdefs_absent v_addiw. det_selftest_one det_vdefs_absent v_slliw. det_selftest_one det_vdefs_absent v_srliw.
  det_selftest_one det_vdefs_absent v_sraiw. det_selftest_one det_vdefs_absent v_addw. det_selftest_one det_vdefs_absent v_subw.
  det_selftest_one det_vdefs_absent v_sllw. det_selftest_one det_vdefs_absent v_srlw. det_selftest_one det_vdefs_absent v_sraw.
  det_selftest_one det_vdefs_absent v_mulh. det_selftest_one det_vdefs_absent v_mulhsu. det_selftest_one det_vdefs_absent v_mulhu.
  det_selftest_one det_vdefs_absent v_mulw. det_selftest_one det_vdefs_absent btgt.
  det_selftest_one det_isa_absent alu64. det_selftest_one det_isa_absent alu32. det_selftest_one det_isa_absent (@mul_div 64).
  det_selftest_one det_isa_absent (@sext 12 64).
  det_selftest_one det_vslt_absent v_sltu. det_selftest_one det_vslt_absent v_slt. det_selftest_one det_vslt_absent v_sltiu. det_selftest_one det_vslt_absent v_slti.
  det_selftest_one det_bitops_absent Z.shiftl. det_selftest_one det_bitops_absent Z.shiftr. det_selftest_one det_bitops_absent Z.land.
  det_selftest_one det_bitops_absent Z.lor. det_selftest_one det_bitops_absent Z.lxor. det_selftest_one det_bitops_absent Z.pow.
  det_selftest_one det_bitops_absent bv_wrap. det_selftest_one det_bitops_absent bv_swrap.
  exact I.
Qed.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem Cells Exec.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Export FP ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Lemma rw_cells_read : forall m A cs k c,
  rw_cells m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof. intros m A cs k c [H _]. apply cells_at_read. exact H. Qed.

Lemma ro_cells_read : forall m A cs k c,
  ro_cells m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof. intros m A cs k c H. apply cells_at_read. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma rw_cells_read_at : forall m A cs k c n a,
  rw_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a n = Some (cbytes c).
Proof. intros; subst; eapply rw_cells_read; eauto. Qed.

Lemma ro_cells_read_at : forall m A cs k c n a,
  ro_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a n = Some (cbytes c).
Proof. intros; subst; eapply ro_cells_read; eauto. Qed.

Lemma rw_cells_cb_split : forall m A cs cs2 k n,
  rw_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> rw_cells m A cs2.
Proof.
  intros m A cs cs2 k n [Hc Hw] Hok ->. split.
  - apply cells_at_cb_split; assumption.
  - rewrite cells_size_cb_split; [exact Hw| exact (cells_at_wf _ _ _ _ Hc) | exact Hok].
Qed.

Lemma ro_cells_cb_split : forall m A cs cs2 k n,
  ro_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> ro_cells m A cs2.
Proof. intros m A cs cs2 k n Hc Hok ->. apply cells_at_cb_split; assumption. Qed.

Lemma cell_at_bound : forall cs k c, cell_at cs k = Some c -> (k + csize c <= cells_size cs)%nat.
Proof.
  intros cs k c H. destruct (cell_at_split cs k c c H) as (pre & post & -> & Hsz & _).
  rewrite cells_size_app. cbn. lia.
Qed.

Lemma rw_cells_store_ok : forall m A cs k c (j : nat),
  rw_cells m A cs -> cell_at cs k = Some c -> j = csize c ->
  store_ok segs m (wa (A + Z.of_nat k)) j = true.
Proof.
  intros m A cs k c j [Hc Hw] Hk ->. pose proof (cell_at_bound _ _ _ Hk).
  apply (wr_at_store_ok segs m A (Z.of_nat (cells_size cs))); [exact Hw| lia | lia].
Qed.

Lemma rw_cells_store_ok_at : forall m A cs k c (j : nat) a,
  rw_cells m A cs -> cell_at cs k = Some c -> j = csize c -> a = wa (A + Z.of_nat k) ->
  store_ok segs m a j = true.
Proof. intros; subst. eapply rw_cells_store_ok; eauto. Qed.

Lemma rw_cells_write : forall m A cs k c c',
  rw_cells m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
  rw_cells (write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) A (cell_upd cs k c').
Proof.
  intros m A cs k c c' [Hc Hw] Hk Hsz Hwf. split.
  - eapply cells_at_write; eauto.
  - destruct (cell_at_split cs k c c' Hk) as (pre & post & -> & Hszp & ->).
    rewrite cells_size_app in *. cbn [cells_size] in *. rewrite Hsz. apply wr_at_write. exact Hw.
Qed.

Lemma rw_cells_frame : forall m A cs (a : Z) bs,
  rw_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  rw_cells (write_to_mem m (wa a) bs) A cs.
Proof.
  intros m A cs a bs [Hc Hw] Ha Hl Hd. split.
  - apply cells_at_frame; assumption.
  - apply wr_at_write. exact Hw.
Qed.

Lemma ro_cells_frame : forall m A cs (a : Z) bs,
  ro_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  ro_cells (write_to_mem m (wa a) bs) A cs.
Proof. intros. apply cells_at_frame; assumption. Qed.

Lemma rw_cells_bound : forall m A cs, rw_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. intros m A cs [H _]. eapply cells_at_bound; eauto. Qed.
Lemma ro_cells_bound : forall m A cs, ro_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. intros m A cs H. eapply cells_at_bound; eauto. Qed.

(* [comment removed for export] *)
Lemma mem_inv_store_cbytes : forall m a c',
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

(* [comment removed for export] *)

(* [comment removed for export] *)

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
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac slia := first [ exact I | lia | split; [lia|exact I] ].

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac fold_closed_in_goal :=
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
  end; cbv beta iota.

(* [comment removed for export] *)
Ltac is_concrete_map R := lazymatch R with TNode _ _ _ => idtac | TEmpty => idtac end.
Ltac map_cbv_get := cbv beta iota delta [tget].
Ltac map_cbv_set := cbv beta iota delta [tset].

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

Ltac exec_cbv :=
  cbv beta iota zeta delta [lift_result interp_eff0 exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s].

(* [comment removed for export] *)
Ltac vnorm_rw_for i :=
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

Ltac vnorm_tail :=
  (match goal with |- context [@bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 _)] => rewrite ?lit_add_lit | _ => idtac end);
  (match goal with |- context [w0] => rewrite ?w0_lit | _ => idtac end);
  (match goal with |- context [w1] => rewrite ?w1_lit | _ => idtac end);
  unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
         v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
         v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
         v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt;
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

Ltac addr_diff E A :=
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
Ltac addr_expr a :=
  lazymatch a with
  | Z_to_bv 64 ?E => E
  | wa ?E => E
  | _ => constr:(Z.add (bv_unsigned a) 0)
  end.
(* [comment removed for export] *)
Ltac addr_eq_tac := symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ].

(* [comment removed for export] *)
Ltac cells_cbv :=
  lazymatch goal with
  | |- ?G =>
      let G' := eval cbv beta iota zeta delta [cell_at cell_upd csize cells_size Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add cbytes] in G in
      change_no_check G'
  end.

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
             (* [comment removed for export] *)
             [ | exact_no_check (@eq_refl bool true) | exact_no_check (@eq_refl (list cell) cs2) ]
      end
  end.

Ltac eval_cell_at cs kn := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn).



(* [comment removed for export] *)
Ltac load_post :=
  cbv beta iota delta [cbytes];
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
                (* [comment removed for export] *)
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
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

Ltac simpl_sizes :=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].

Ltac transport_chunks segs m a bs :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac mem_after_store :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
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
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
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
    | Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv zeta
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
            rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
            simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | CsrI ?op ?rd ?uimm ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
            let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
            try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv iota
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
  | |- evt _ _ (MS _ _ _ ?fce _ _ _) =>
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
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
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
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; solve_cond]
  end.
Ltac if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; solve_cond]
  end.
Ltac if_true_by H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv iota| symmetry; exact H]
  end.
Ltac if_false_by H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv iota| symmetry; exact H]
  end.
(* [comment removed for export] *)
Ltac if_cases H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
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
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let t := eval vm_compute in R in change R with t
  end.

(* [comment removed for export] *)
Ltac zstep := step; zsimp.

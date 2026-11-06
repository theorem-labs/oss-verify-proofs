(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import FpLift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regfile : Type := list word.
Definition mem : Type := word -> option byte.

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

Fixpoint lget (l : regfile) (n : nat) : word :=
  match l, n with
  | x :: _, O => x
  | _ :: r, S k => lget r k
  | [], _ => Z_to_bv 64 0
  end.
Definition rget (l : regfile) (n : nat) : word :=
  match n with O => Z_to_bv 64 0 | _ => lget l n end.

Fixpoint lset (l : regfile) (n : nat) (v : word) : regfile :=
  match l, n with
  | _ :: r, O => v :: r
  | x :: r, S k => x :: lset r k v
  | [], _ => []
  end.
Definition rset (l : regfile) (n : nat) (v : word) : regfile :=
  match n with O => l | _ => lset l n v end.

Lemma lset_length : forall l n v, length (lset l n v) = length l.
Proof. induction l as [|x l IH]; intros [|n] v; cbn; auto. Qed.

Lemma rset_length : forall l n v, length (rset l n v) = length l.
Proof. intros l [|n] v; cbn [rset]; [reflexivity | apply lset_length]. Qed.

Lemma lget_lset_same : forall l n v, (n < length l)%nat -> lget (lset l n v) n = v.
Proof. induction l as [|x l IH]; intros [|n] v H; cbn in *; try lia; auto. apply IH. lia. Qed.

Lemma lget_lset_other : forall l n m v, n <> m -> lget (lset l n v) m = lget l m.
Proof.
  induction l as [|x l IH]; intros [|n] [|m] v H; cbn; try reflexivity; try congruence.
  apply IH. congruence.
Qed.

(* [comment removed for export] *)
Definition rrel (regs : bvmap 5 word) (l : regfile) : Prop :=
  length l = 32%nat /\ forall r : reg, getr regs r = rget l (ridx r).

Lemma ridx_lt : forall r : reg, (ridx r < 32)%nat.
Proof.
  intros r. unfold ridx. pose proof (bv_unsigned_in_range 5 r) as H.
  change (bv_modulus 5) with 32 in H. lia.
Qed.

Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof.
  intros r r' H. apply bv_eq. unfold ridx in H.
  pose proof (bv_unsigned_in_range 5 r). pose proof (bv_unsigned_in_range 5 r'). lia.
Qed.

Lemma ridx_0 : forall r : reg, ridx r = O -> r = 0%bv.
Proof. intros r H. apply ridx_inj. rewrite H. reflexivity. Qed.

Lemma rrel_set : forall regs l (rd : reg) v,
  rrel regs l ->
  rrel (if bv_eqb rd 0 then regs else regupd regs rd v) (rset l (ridx rd) v).
Proof.
  intros regs l rd v [Hlen Hr]. destruct (bv_eqb rd 0) eqn:E0.
  - assert (rd = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in E0; apply Z.eqb_eq in E0; exact E0).
    change (ridx 0%bv) with O. cbn [rset]. split; assumption.
  - assert (Hrd : rd <> 0%bv).
    { intros ->. unfold bv_eqb in E0. rewrite Z.eqb_refl in E0. discriminate. }
    assert (Hn : ridx rd <> O) by (intros H; apply Hrd, ridx_0, H).
    split; [rewrite rset_length; exact Hlen|].
    intros r. destruct (ridx rd) as [|k] eqn:Ek; [congruence|]. cbn [rset].
    destruct (Nat.eq_dec (ridx r) (S k)) as [Heq|Hne].
    + assert (r = rd) as -> by (apply ridx_inj; congruence).
      rewrite getr_same by exact Hrd. rewrite Ek. cbn [rget].
      rewrite lget_lset_same; [reflexivity|]. pose proof (ridx_lt rd). lia.
    + rewrite getr_other by (intros ->; congruence). rewrite Hr.
      unfold rget. destruct (ridx r) as [|j] eqn:Ej; [reflexivity|].
      rewrite lget_lset_other by congruence. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lof (regs : bvmap 5 word) : regfile :=
  map (fun k => getr regs (Z_to_bv 5 (Z.of_nat k))) (seq 0 32).

Lemma lget_map_seq : forall (f : nat -> word) n s k, (k < n)%nat ->
  lget (map f (seq s n)) k = f (s + k)%nat.
Proof.
  intros f n. induction n as [|n IH]; intros s k Hk; [lia|].
  cbn [seq map]. destruct k as [|k]; cbn [lget]; [f_equal; lia|].
  rewrite IH by lia. f_equal. lia.
Qed.

Lemma rrel_lof : forall regs, rrel regs (lof regs).
Proof.
  intros regs. split; [reflexivity|]. intros r. unfold rget.
  destruct (ridx r) as [|k] eqn:Ek.
  - rewrite (ridx_0 r Ek). reflexivity.
  - unfold lof. rewrite lget_map_seq by (pose proof (ridx_lt r); lia). cbn [Nat.add].
    f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- Ek. unfold ridx.
    pose proof (bv_unsigned_in_range 5 r) as H. rewrite Z2Nat.id by lia.
    symmetry. apply bv_wrap_small. exact H.
Qed.

Lemma rrel_getr : forall regs l (k : nat), rrel regs l -> (0 < k < 32)%nat ->
  getr regs (Z_to_bv 5 (Z.of_nat k)) = rget l k.
Proof.
  intros regs l k [_ H] Hk. rewrite H. f_equal. unfold ridx. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_small by (change (bv_modulus 5) with 32; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive pinstr : Type :=
| PConst (rd : nat) (z : Z)
| PMv (rd rs : nat)
| PImm (op : aluop) (rd rs : nat) (imm : Z)
| PSh (op : aluop) (rd rs : nat) (sh : Z)
| POp (op : aluop) (rd rs1 rs2 : nat)
| PImmW (rd rs : nat) (imm : Z)
| PShW (op : aluop) (rd rs : nat) (sh : Z)
| POpW (op : aluop) (rd rs1 rs2 : nat)
| PMul (op : mulop) (rd rs1 rs2 : nat)
| PMulW (op : mulop) (rd rs1 rs2 : nat)
| PBr (c : branch_cond) (rs1 rs2 : nat) (t : Z) (ti : option nat)
| PJal (rd : nat) (ret : Z) (t : Z) (ti : option nat)
| PJalr (rd rs : nat) (imm : Z) (ret : Z)
| PLoad (sz : msize) (sg : bool) (rd rs : nat) (imm : Z)
| PStore (sz : msize) (rs1 rs2 : nat) (imm : Z)
| PNop
| PBad.

(* [comment removed for export] *)
Definition ientry (segs : list Segment) (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => None
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (i, sz) => if Z.eqb sz 4 then Some i else None
              | None => None
              end
  end.

Lemma ientry_facts : forall segs pc ins, ientry segs pc = Some ins ->
  exists w, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false
            /\ decode_any w = Some (ins, 4).
Proof.
  intros segs pc ins H. unfold ientry in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|]; [|discriminate].
  destruct (is_ecall w) eqn:Ee; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Ed; [|discriminate].
  destruct (Z.eqb sz 4) eqn:Es; [|discriminate]. apply Z.eqb_eq in Es. subst sz.
  injection H as <-. exists w. auto.
Qed.

Definition tidx (base : Z) (n : nat) (t : Z) : option nat :=
  let d := t - base in
  if (0 <=? d) && (d <? 4 * Z.of_nat n) && (d mod 4 =? 0) then Some (Z.to_nat (d / 4)) else None.

Lemma tidx_spec : forall base n t j, tidx base n t = Some j ->
  (j < n)%nat /\ t = base + 4 * Z.of_nat j.
Proof.
  intros base n t j H. unfold tidx in H.
  destruct ((0 <=? t - base) && (t - base <? 4 * Z.of_nat n) && ((t - base) mod 4 =? 0)) eqn:E; [|discriminate].
  injection H as <-. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3.
  pose proof (Z.div_mod (t - base) 4 ltac:(lia)) as Hd. rewrite E3 in Hd.
  assert (0 <= (t - base) / 4) by (apply Z.div_pos; lia).
  split; [|rewrite Z2Nat.id by lia; lia]. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
Qed.

Definition pre (base : Z) (n : nat) (pc : Z) (ins : instr) : pinstr :=
  match ins with
  | Lui rd imm => PConst (ridx rd) (Z.shiftl (bv_signed imm) 12)
  | Auipc rd imm => PConst (ridx rd) (Z.shiftl (bv_signed imm) 12 + pc)
  | Jal rd imm => PJal (ridx rd) (pc + 4) (pc + bv_signed imm) (tidx base n (pc + bv_signed imm))
  | Jalr rd rs imm => PJalr (ridx rd) (ridx rs) (bv_signed imm) (pc + 4)
  | Branch c rs1 rs2 imm => PBr c (ridx rs1) (ridx rs2) (pc + bv_signed imm) (tidx base n (pc + bv_signed imm))
  | Load sz sg rd rs imm =>
      match sz, sg with
      | SZ8, false => PBad
      | _, _ => PLoad sz sg (ridx rd) (ridx rs) (bv_signed imm)
      end
  | Store sz rs1 rs2 imm => PStore sz (ridx rs1) (ridx rs2) (bv_signed imm)
  | OpImm op rd rs imm =>
      match op with
      | ALU_ADD =>
          if Z.eqb (bv_signed imm) 0 then PMv (ridx rd) (ridx rs)
          else if Nat.eqb (ridx rs) 0 then PConst (ridx rd) (bv_signed imm)
          else PImm op (ridx rd) (ridx rs) (bv_signed imm)
      | ALU_SLT | ALU_SLTU | ALU_XOR | ALU_OR | ALU_AND => PImm op (ridx rd) (ridx rs) (bv_signed imm)
      | _ => PBad
      end
  | ShiftImm op rd rs sh =>
      match op with
      | ALU_SLL | ALU_SRL | ALU_SRA => PSh op (ridx rd) (ridx rs) (bv_unsigned sh)
      | _ => PBad
      end
  | Op op rd rs1 rs2 => POp op (ridx rd) (ridx rs1) (ridx rs2)
  | OpImm32 rd rs imm => PImmW (ridx rd) (ridx rs) (bv_signed imm)
  | ShiftImm32 op rd rs sh =>
      match op with
      | ALU_SLL | ALU_SRL | ALU_SRA => PShW op (ridx rd) (ridx rs) (bv_unsigned sh)
      | _ => PBad
      end
  | Op32 op rd rs1 rs2 =>
      match op with
      | ALU_ADD | ALU_SUB | ALU_SLL | ALU_SRL | ALU_SRA => POpW op (ridx rd) (ridx rs1) (ridx rs2)
      | _ => PBad
      end
  | Mul op rd rs1 rs2 => PMul op (ridx rd) (ridx rs1) (ridx rs2)
  | Mul32 op rd rs1 rs2 =>
      match op with
      | M_MUL | M_DIV | M_DIVU | M_REM | M_REMU => PMulW op (ridx rd) (ridx rs1) (ridx rs2)
      | _ => PBad
      end
  | Fence _ _ _ _ _ => PNop
  | _ => PBad
  end.

Definition code : Type := list (Z * pinstr).

Definition centry (segs : list Segment) (base : Z) (n : nat) (i : nat) : Z * pinstr :=
  (base + 4 * Z.of_nat i,
   match ientry segs (base + 4 * Z.of_nat i) with
   | Some ins => pre base n (base + 4 * Z.of_nat i) ins
   | None => PBad
   end).

Definition mk_code (segs : list Segment) (base : Z) (n : nat) : code :=
  map (centry segs base n) (seq 0 n).

Lemma mk_code_nth : forall segs base n i e,
  nth_error (mk_code segs base n) i = Some e -> (i < n)%nat /\ e = centry segs base n i.
Proof.
  intros segs base n i e H. unfold mk_code in H.
  assert (Hi : (i < n)%nat).
  { assert (Hn : nth_error (map (centry segs base n) (seq 0 n)) i <> None) by (rewrite H; discriminate).
    apply nth_error_Some in Hn. rewrite length_map, length_seq in Hn. exact Hn. }
  split; [exact Hi|].
  rewrite nth_error_map, nth_error_seq in H.
  destruct (Nat.ltb i n) eqn:E; [|apply Nat.ltb_ge in E; lia].
  cbn in H. injection H as <-. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition val_imm (op : aluop) (a : word) (imm : Z) : word :=
  match op with
  | ALU_ADD => v_addi a imm | ALU_SLT => v_slti a imm | ALU_SLTU => v_sltiu a imm
  | ALU_XOR => v_xori a imm | ALU_OR => v_ori a imm | ALU_AND => v_andi a imm
  | _ => a
  end.
Definition val_sh (op : aluop) (a : word) (sh : Z) : word :=
  match op with
  | ALU_SLL => v_slli a sh | ALU_SRL => v_srli a sh | ALU_SRA => v_srai a sh
  | _ => a
  end.
Definition val_op (op : aluop) (a b : word) : word :=
  match op with
  | ALU_ADD => v_add a b | ALU_SUB => v_sub a b | ALU_SLL => v_sll a b | ALU_SLT => v_slt a b
  | ALU_SLTU => v_sltu a b | ALU_XOR => v_xor a b | ALU_SRL => v_srl a b | ALU_SRA => v_sra a b
  | ALU_OR => v_or a b | ALU_AND => v_and a b
  end.
Definition val_shw (op : aluop) (a : word) (sh : Z) : word :=
  match op with
  | ALU_SLL => v_slliw a sh | ALU_SRL => v_srliw a sh | ALU_SRA => v_sraiw a sh
  | _ => a
  end.
Definition val_opw (op : aluop) (a b : word) : word :=
  match op with
  | ALU_ADD => v_addw a b | ALU_SUB => v_subw a b | ALU_SLL => v_sllw a b
  | ALU_SRL => v_srlw a b | ALU_SRA => v_sraw a b
  | _ => a
  end.
Definition val_mul (op : mulop) (a b : word) : word :=
  match op with
  | M_MUL => v_mul a b | M_MULH => v_mulh a b | M_MULHSU => v_mulhsu a b | M_MULHU => v_mulhu a b
  | M_DIV => v_div a b | M_REM => v_rem a b
  | _ => mul_div op a b
  end.
Definition val_mulw (op : mulop) (a b : word) : word :=
  match op with
  | M_MUL => v_mulw a b | M_DIV => v_divw a b | M_DIVU => v_divuw a b
  | M_REM => v_remw a b | M_REMU => v_remuw a b
  | _ => a
  end.

(* [comment removed for export] *)
Definition br_yes (c : branch_cond) (a b : word) : Prop :=
  match c with
  | BC_EQ => bv_unsigned a = bv_unsigned b
  | BC_NE => bv_unsigned a <> bv_unsigned b
  | BC_LT => bv_signed a < bv_signed b
  | BC_GE => bv_signed b <= bv_signed a
  | BC_LTU => bv_unsigned a < bv_unsigned b
  | BC_GEU => bv_unsigned b <= bv_unsigned a
  end.
Definition br_no (c : branch_cond) (a b : word) : Prop :=
  match c with
  | BC_EQ => bv_unsigned a <> bv_unsigned b
  | BC_NE => bv_unsigned a = bv_unsigned b
  | BC_LT => bv_signed b <= bv_signed a
  | BC_GE => bv_signed a < bv_signed b
  | BC_LTU => bv_unsigned b <= bv_unsigned a
  | BC_GEU => bv_unsigned a < bv_unsigned b
  end.

Lemma br_dec : forall c a b,
  (branch_taken c a b = true /\ br_yes c a b) \/ (branch_taken c a b = false /\ br_no c a b).
Proof.
  intros c a b. unfold branch_taken, br_yes, br_no, bv_eqb, bv_lts, bv_ltu.
  destruct c.
  - destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)); [left|right]; auto.
  - destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)); [right|left]; auto.
  - destruct (Z.ltb_spec (bv_signed a) (bv_signed b)); [left|right]; auto.
  - destruct (Z.ltb_spec (bv_signed a) (bv_signed b)); [right|left]; auto.
  - destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b)); [left|right]; auto.
  - destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b)); [right|left]; auto.
Qed.

(* [comment removed for export] *)
Definition vaddr (a : word) (imm : Z) : word :=
  match imm with Z0 => a | _ => v_addi a imm end.
Lemma vaddr_eq : forall a imm, vaddr a imm = v_addi a imm.
Proof.
  intros a imm. destruct imm; try reflexivity. cbn [vaddr]. unfold v_addi.
  rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Definition szn (sz : msize) : nat := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end%nat.

Definition ext_load (sz : msize) (sg : bool) (v : word) : word :=
  match sz, sg with
  | SZ1, true => v_lb (Z_to_bv 8 (bv_unsigned v))
  | SZ2, true => v_lh v
  | SZ4, true => v_lw v
  | _, _ => v
  end.

(* [comment removed for export] *)
Definition pc_eqb : Z -> Z -> bool := Eval cbv in Z.eqb.
Lemma pc_eqb_eq : forall a b, pc_eqb a b = Z.eqb a b.
Proof. reflexivity. Qed.

Fixpoint in_stops (pc : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | x :: r => if pc_eqb pc x then true else in_stops pc r
  end.

Fixpoint cnth (c : code) (i : nat) : option (Z * pinstr) :=
  match c, i with
  | x :: _, O => Some x
  | _ :: r, S k => cnth r k
  | [], _ => None
  end.
Lemma cnth_nth_error : forall c i, cnth c i = nth_error c i.
Proof. induction c as [|x c IH]; intros [|i]; cbn; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WP.
Variable SEGS : list Segment.
Variable rom : mem.

(* [comment removed for export] *)
Definition load_ok (M : mem) (a : word) (n : nat) (v : word) : Prop :=
  exists bs, rdn SEGS M a n = Some bs /\ bytes_le_to_Z bs = bv_unsigned v.

Section Gen.
Variable C : code.
Variable stops : list Z.
Variable Q : word -> regfile -> mem -> Prop.

Fixpoint wp (fuel : nat) (first : bool) (i : nat) (l : regfile) (M : mem) {struct fuel} : Prop :=
  match fuel with
  | O => False
  | S f =>
    match cnth C i with
    | None => False
    | Some (pc, pi) =>
      if (if first then false else in_stops pc stops) then Q (Z_to_bv 64 pc) l M else
      match pi with
      | PConst rd z => wp f false (S i) (rset l rd (Z_to_bv 64 z)) M
      | PMv rd rs => wp f false (S i) (rset l rd (rget l rs)) M
      | PImm op rd rs imm => wp f false (S i) (rset l rd (val_imm op (rget l rs) imm)) M
      | PSh op rd rs sh => wp f false (S i) (rset l rd (val_sh op (rget l rs) sh)) M
      | POp op rd rs1 rs2 => wp f false (S i) (rset l rd (val_op op (rget l rs1) (rget l rs2))) M
      | PImmW rd rs imm => wp f false (S i) (rset l rd (v_addiw (rget l rs) imm)) M
      | PShW op rd rs sh => wp f false (S i) (rset l rd (val_shw op (rget l rs) sh)) M
      | POpW op rd rs1 rs2 => wp f false (S i) (rset l rd (val_opw op (rget l rs1) (rget l rs2))) M
      | PMul op rd rs1 rs2 => wp f false (S i) (rset l rd (val_mul op (rget l rs1) (rget l rs2))) M
      | PMulW op rd rs1 rs2 => wp f false (S i) (rset l rd (val_mulw op (rget l rs1) (rget l rs2))) M
      | PBr c rs1 rs2 t ti =>
          (br_yes c (rget l rs1) (rget l rs2) ->
             match ti with Some j => wp f false j l M | None => Q (Z_to_bv 64 t) l M end)
          /\ (br_no c (rget l rs1) (rget l rs2) -> wp f false (S i) l M)
      | PJal rd ret t ti =>
          match ti with
          | Some j => wp f false j (rset l rd (Z_to_bv 64 ret)) M
          | None => Q (Z_to_bv 64 t) (rset l rd (Z_to_bv 64 ret)) M
          end
      | PJalr rd rs imm ret => Q (v_jalr (rget l rs) imm) (rset l rd (Z_to_bv 64 ret)) M
      | PLoad sz sg rd rs imm =>
          exists v, load_ok M (vaddr (rget l rs) imm) (szn sz) v
                    /\ wp f false (S i) (rset l rd (ext_load sz sg v)) M
      | PStore sz rs1 rs2 imm =>
          store_ok SEGS M (vaddr (rget l rs1) imm) (szn sz) = true
          /\ wp f false (S i) l (wbytes M (vaddr (rget l rs1) imm) (word_to_le_bytes (szn sz) (rget l rs2)))
      | PNop => wp f false (S i) l M
      | PBad => False
      end
    end
  end.
End Gen.

(* [comment removed for export] *)
Definition reach (pcw : word) (l : regfile) (M : mem) (Post : word -> regfile -> mem -> Prop) : Prop :=
  forall regs F fc, rrel regs l ->
    exists pcw' regs' l' M',
      msteps SEGS (mkstF regs F fc pcw M rom) (mkstF regs' F fc pcw' M' rom) /\ rrel regs' l' /\ Post pcw' l' M'.

Lemma reach_done : forall pcw l M (Post : word -> regfile -> mem -> Prop),
  Post pcw l M -> reach pcw l M Post.
Proof. intros pcw l M Post H regs F fc HR. exists pcw, regs, l, M. split; [apply mst_refl | auto]. Qed.

Lemma reach_bind : forall pcw l M (Post : word -> regfile -> mem -> Prop),
  reach pcw l M (fun w' l' M' => reach w' l' M' Post) -> reach pcw l M Post.
Proof.
  intros pcw l M Post H regs F fc HR.
  destruct (H regs F fc HR) as (w1 & r1 & l1 & M1 & Hs1 & HR1 & H1).
  destruct (H1 r1 F fc HR1) as (w2 & r2 & l2 & M2 & Hs2 & HR2 & H2).
  exists w2, r2, l2, M2. split; [eapply msteps_trans; eassumption | auto].
Qed.

Lemma reach_weaken : forall pcw l M (P1 P2 : word -> regfile -> mem -> Prop),
  reach pcw l M P1 -> (forall w' l' M', P1 w' l' M' -> P2 w' l' M') -> reach pcw l M P2.
Proof.
  intros pcw l M P1 P2 H HW regs F fc HR.
  destruct (H regs F fc HR) as (w1 & r1 & l1 & M1 & Hs1 & HR1 & H1).
  exists w1, r1, l1, M1. auto.
Qed.

(* [comment removed for export] *)
Lemma reach_cont : forall pcw l M (P1 Post : word -> regfile -> mem -> Prop),
  reach pcw l M P1 -> (forall w' l' M', P1 w' l' M' -> reach w' l' M' Post) -> reach pcw l M Post.
Proof. intros. apply reach_bind. eapply reach_weaken; eassumption. Qed.

(* [comment removed for export] *)
Lemma reach_exF : forall pcw regs F fc M (Post : word -> regfile -> mem -> Prop),
  reach pcw (lof regs) M Post ->
  exists pcw' regs' l' M',
    msteps SEGS (mkstF regs F fc pcw M rom) (mkstF regs' F fc pcw' M' rom) /\ rrel regs' l' /\ Post pcw' l' M'.
Proof. intros pcw regs F fc M Post H. exact (H regs F fc (rrel_lof regs)). Qed.

(* [comment removed for export] *)
Lemma reach_ex : forall pcw regs M (Post : word -> regfile -> mem -> Prop),
  reach pcw (lof regs) M Post ->
  exists pcw' regs' l' M',
    msteps SEGS (mkst regs pcw M rom) (mkst regs' pcw' M' rom) /\ rrel regs' l' /\ Post pcw' l' M'.
Proof. intros pcw regs M Post H. exact (reach_exF pcw regs bvmap_empty (Z_to_bv 32 0) M Post H). Qed.

(* [comment removed for export] *)
Definition liftable (pcw : word) : Prop :=
  exists w ins sz, fetch_word SEGS pcw = Some w /\ is_ecall w = false /\ decode_any w = Some (ins, sz) /\ int_instr ins = true.

(* [comment removed for export] *)
Lemma reach_step : forall pcw l M pcw' l' M' (Post : word -> regfile -> mem -> Prop),
  liftable pcw ->
  (forall regs, rrel regs l ->
     exists regs', RiscvSemantics.step SEGS (mkst regs pcw M rom) = MachineOk (mkst regs' pcw' M' rom)
                   /\ rrel regs' l') ->
  reach pcw' l' M' Post -> reach pcw l M Post.
Proof.
  intros pcw l M pcw' l' M' Post (w & ins & sz & Hf & He & Hd & Hi) Hs Hr regs F fc HR.
  destruct (Hs regs HR) as (regs1 & Hst & HR1).
  destruct (Hr regs1 F fc HR1) as (w2 & r2 & l2 & M2 & Hms & HR2 & HP).
  exists w2, r2, l2, M2. split; [|auto].
  eapply mst_step; [reflexivity | exact (step_lift SEGS regs pcw M rom w ins sz regs1 pcw' M' F fc Hf He Hd Hi Hst) | exact Hms].
Qed.

(* [comment removed for export] *)
Lemma wrap_add_l : forall a b, bv_wrap 64 (bv_wrap 64 a + b) = bv_wrap 64 (a + b).
Proof. intros. unfold bv_wrap. apply Zplus_mod_idemp_l. Qed.

Lemma pc_next : forall pc k, v_addi (Z_to_bv 64 pc) k = Z_to_bv 64 (pc + k).
Proof.
  intros pc k. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. apply wrap_add_l.
Qed.

Lemma pc_btgt : forall pc k, btgt (Z_to_bv 64 pc) k = Z_to_bv 64 (pc + k).
Proof. intros. unfold btgt. apply pc_next. Qed.

Lemma pc_auipc : forall pc z, v_auipc (Z_to_bv 64 pc) z = Z_to_bv 64 (z + pc).
Proof.
  intros pc z. unfold v_auipc. apply bv_eq. rewrite !Z_to_bv_unsigned.
  rewrite (Z.add_comm z), wrap_add_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof. intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity. Qed.

Lemma load_ok_bound : forall M a n v, load_ok M a n v -> 0 <= bv_unsigned v < 2 ^ (8 * Z.of_nat n).
Proof.
  intros M a n v (bs & Hr & Hv). rewrite <- Hv.
  pose proof (rdn_length _ _ _ _ _ Hr) as Hl. pose proof (bytes_le_to_Z_bound bs) as Hb.
  pose proof (bytes_le_to_Z_nonneg bs). rewrite Hl in Hb. lia.
Qed.

Lemma load_ok_det : forall M a n v v', load_ok M a n v -> load_ok M a n v' -> v = v'.
Proof.
  intros M a n v v' (bs & Hr & Hv) (bs' & Hr' & Hv'). rewrite Hr in Hr'. injection Hr' as <-.
  apply bv_eq. congruence.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_fence_nop : forall segs0 regs0 pc0 mem0 rom0 w a b c d e,
  fetch_word segs0 pc0 = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step segs0 (mkst regs0 pc0 mem0 rom0) = MachineOk (mkst regs0 (v_addi pc0 4) mem0 rom0).
Proof.
  intros segs0 regs0 pc0 mem0 rom0 w a b c d e Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Section Sound.
Variables (base : Z) (n : nat) (stops : list Z).
Variable Post : word -> regfile -> mem -> Prop.

(* [comment removed for export] *)
Lemma step_rw : forall pcw, liftable pcw -> forall l M (rd : reg) (f : bvmap 5 word -> word) (v : word) pcw',
  (forall regs, rrel regs l ->
     RiscvSemantics.step SEGS (mkst regs pcw M rom)
       = MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (f regs)) pcw' M rom)
     /\ f regs = v) ->
  reach pcw' (rset l (ridx rd) v) M Post -> reach pcw l M Post.
Proof.
  intros pcw HL l M rd f v pcw' Hs Hr. eapply reach_step; [exact HL | |exact Hr].
  intros regs HR. destruct (Hs regs HR) as [Hst Hv]. eexists. split; [exact Hst|].
  rewrite Hv. apply rrel_set. exact HR.
Qed.

Lemma step_same : forall pcw, liftable pcw -> forall l M pcw' M',
  (forall regs, rrel regs l ->
     RiscvSemantics.step SEGS (mkst regs pcw M rom) = MachineOk (mkst regs pcw' M' rom)) ->
  reach pcw' l M' Post -> reach pcw l M Post.
Proof.
  intros pcw HL l M pcw' M' Hs Hr. eapply reach_step; [exact HL | |exact Hr].
  intros regs HR. exists regs. split; [apply Hs; exact HR | exact HR].
Qed.

Lemma load1_byte : forall M a v, load_ok M a 1 v ->
  rdn SEGS M a 1 = Some [Z_to_bv 8 (bv_unsigned v)] /\ bv_unsigned v < 256.
Proof.
  intros M a v H. pose proof (load_ok_bound _ _ _ _ H) as Hb. change (2 ^ (8 * Z.of_nat 1)) with 256 in Hb.
  destruct H as (bs & Hr & Hv). pose proof (rdn_length _ _ _ _ _ Hr) as Hl.
  destruct bs as [|b [|b' bs]]; try discriminate. rewrite bytes_le_1 in Hv.
  split; [|lia]. rewrite Hr. do 2 f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hv.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Theorem wp_sound : forall fuel first i l M,
  wp (mk_code SEGS base n) stops (fun w l' M' => reach w l' M' Post) fuel first i l M ->
  reach (Z_to_bv 64 (base + 4 * Z.of_nat i)) l M Post.
Proof.
  induction fuel as [|f IH]; intros first i l M H; [destruct H|].
  cbn [wp] in H. rewrite cnth_nth_error in H.
  destruct (nth_error (mk_code SEGS base n) i) as [[pc pi]|] eqn:En; [|destruct H].
  apply mk_code_nth in En as [Hi Ee]. unfold centry in Ee. injection Ee as Epc Epi.
  destruct (if first then false else in_stops pc stops); [subst pc; exact H|].
  destruct (ientry SEGS (base + 4 * Z.of_nat i)) as [ins|] eqn:Ei; [|subst pi; destruct H].
  apply ientry_facts in Ei as (w & Hf & He & Hd).
  rewrite <- Epc in *.
  assert (HL : int_instr ins = true -> liftable (Z_to_bv 64 pc)).
  { intros Hint. exists w, ins, 4. auto. }
  assert (Hnext : Z_to_bv 64 (base + 4 * Z.of_nat (S i)) = v_addi (Z_to_bv 64 pc) 4).
  { rewrite pc_next. f_equal. lia. }
  assert (HIH : forall l' M', wp (mk_code SEGS base n) stops (fun w l' M' => reach w l' M' Post) f false (S i) l' M' ->
                reach (v_addi (Z_to_bv 64 pc) 4) l' M' Post).
  { intros l' M' Hw. rewrite <- Hnext. eapply IH. exact Hw. }
  destruct ins; subst pi; cbn [pre] in H; try (destruct H; fail).
  - (* [comment removed for export] *)
    eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v_lui (Z.shiftl (bv_signed imm) 12))); [|apply HIH; exact H].
    intros regs HR. split; [|reflexivity]. exact (step_lui SEGS regs _ M rom w rd imm Hf He Hd).
  - (* [comment removed for export] *)
    eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v_auipc (Z_to_bv 64 pc) (Z.shiftl (bv_signed imm) 12))); [|apply HIH; exact H].
    intros regs HR. split; [|apply pc_auipc]. exact (step_auipc SEGS regs _ M rom w rd imm Hf He Hd).
  - (* [comment removed for export] *)
    assert (Hst : forall regs, RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 pc) M rom) =
              MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi (Z_to_bv 64 pc) 4))
                              (Z_to_bv 64 (pc + bv_signed imm)) M rom)).
    { intros regs. rewrite <- pc_btgt. exact (step_jal_link SEGS regs _ M rom w rd imm Hf He Hd). }
    eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v_addi (Z_to_bv 64 pc) 4) (Z_to_bv 64 (pc + 4))).
    + intros regs HR. split; [apply Hst | apply pc_next].
    + destruct (tidx base n (pc + bv_signed imm)) as [j|] eqn:Et; [|exact H].
      apply tidx_spec in Et as [Hj Et]. rewrite Et. eapply IH. exact H.
  - (* [comment removed for export] *)
    eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v_addi (Z_to_bv 64 pc) 4) (Z_to_bv 64 (pc + 4))); [|exact H].
    intros regs HR. split; [|apply pc_next].
    rewrite <- (proj2 HR rs1). exact (step_jalr SEGS regs _ M rom w rd rs1 imm Hf He Hd).
  - (* [comment removed for export] *)
    destruct H as [Hy Hn].
    destruct (br_dec c (rget l (ridx rs1)) (rget l (ridx rs2))) as [[Hb Hp]|[Hb Hp]].
    + specialize (Hy Hp).
      assert (Hr : reach (Z_to_bv 64 (pc + bv_signed imm)) l M Post).
      { destruct (tidx base n (pc + bv_signed imm)) as [j|] eqn:Et; [|exact Hy].
        apply tidx_spec in Et as [Hj Et]. rewrite Et. eapply IH. exact Hy. }
      eapply (step_same _ (HL eq_refl)); [|exact Hr]. intros regs HR. rewrite <- pc_btgt.
      apply (step_branch_tk_gen SEGS regs _ M rom w c rs1 rs2 imm Hf He Hd).
      rewrite (proj2 HR rs1), (proj2 HR rs2). exact Hb.
    + specialize (Hn Hp). eapply (step_same _ (HL eq_refl)); [|apply HIH; exact Hn]. intros regs HR.
      apply (step_branch_ft_gen SEGS regs _ M rom w c rs1 rs2 imm Hf He Hd).
      rewrite (proj2 HR rs1), (proj2 HR rs2). exact Hb.
  - (* [comment removed for export] *)
    destruct sz; destruct signed; try (destruct H; fail);
      rewrite vaddr_eq in H; destruct H as (v & Hl & Hw); pose proof Hl as (bs & Hrd & Hv); cbn [szn ext_load] in *.
    + (* [comment removed for export] *)
      destruct (load1_byte _ _ _ Hl) as [Hb _].
      eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v_lb (Z_to_bv 8 (bv_unsigned v)))); [|apply HIH; exact Hw].
      intros regs HR. split; [|reflexivity].
      apply (step_lb SEGS regs _ M rom w rd rs1 imm _ Hf He Hd). rewrite (proj2 HR rs1). exact Hb.
    + (* [comment removed for export] *)
      destruct (load1_byte _ _ _ Hl) as [Hb Hlt].
      eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (bv_unsigned v))))); [|apply HIH; exact Hw].
      intros regs HR. split.
      * apply (step_lbu SEGS regs _ M rom w rd rs1 imm _ Hf He Hd). rewrite (proj2 HR rs1). exact Hb.
      * rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 64 v) as Hr64.
        rewrite bv_wrap_small by (change (bv_modulus 8) with 256; lia). apply Z_to_bv_bv_unsigned.
    + eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v_lh v)); [|apply HIH; exact Hw].
      intros regs HR. split; [|reflexivity].
      apply (step_lh SEGS regs _ M rom w rd rs1 imm bs v Hf He Hd); [|exact Hv]. rewrite (proj2 HR rs1). exact Hrd.
    + eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v)); [|apply HIH; exact Hw].
      intros regs HR. split; [|reflexivity].
      apply (step_lhu SEGS regs _ M rom w rd rs1 imm bs v Hf He Hd); [|exact Hv]. rewrite (proj2 HR rs1). exact Hrd.
    + eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v_lw v)); [|apply HIH; exact Hw].
      intros regs HR. split; [|reflexivity].
      apply (step_lw SEGS regs _ M rom w rd rs1 imm bs v Hf He Hd); [|exact Hv]. rewrite (proj2 HR rs1). exact Hrd.
    + eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v)); [|apply HIH; exact Hw].
      intros regs HR. split; [|reflexivity].
      apply (step_lwu SEGS regs _ M rom w rd rs1 imm bs v Hf He Hd); [|exact Hv]. rewrite (proj2 HR rs1). exact Hrd.
    + eapply (step_rw _ (HL eq_refl) _ _ rd (fun _ => v)); [|apply HIH; exact Hw].
      intros regs HR. split; [|reflexivity].
      apply (step_ld SEGS regs _ M rom w rd rs1 imm bs v Hf He Hd); [|exact Hv]. rewrite (proj2 HR rs1). exact Hrd.
  - (* [comment removed for export] *)
    rewrite !vaddr_eq in H.
    destruct H as [Hok Hw].
    eapply (step_same _ (HL eq_refl)); [|apply HIH; exact Hw]. intros regs HR.
    destruct sz; cbn [szn] in *.
    + rewrite <- (proj2 HR rs1), <- (proj2 HR rs2) in *.
      apply (step_sb SEGS regs _ M rom w rs1 rs2 imm Hf He Hd). exact Hok.
    + rewrite <- (proj2 HR rs1), <- (proj2 HR rs2) in *.
      apply (step_sh_val SEGS regs _ M rom w rs1 rs2 imm Hf He Hd). exact Hok.
    + rewrite <- (proj2 HR rs1), <- (proj2 HR rs2) in *.
      apply (step_sw_val SEGS regs _ M rom w rs1 rs2 imm Hf He Hd). exact Hok.
    + rewrite <- (proj2 HR rs1), <- (proj2 HR rs2) in *.
      apply (step_sd_val SEGS regs _ M rom w rs1 rs2 imm Hf He Hd). exact Hok.
  - (* [comment removed for export] *)
    assert (HG : forall v, (forall regs, rrel regs l -> alu64 op (getr regs rs1) (sext 64 imm) = v) ->
                 wp (mk_code SEGS base n) stops (fun w l' M' => reach w l' M' Post) f false (S i) (rset l (ridx rd) v) M ->
                 reach (Z_to_bv 64 pc) l M Post).
    { intros v Hv Hw.
      eapply (step_rw _ (HL eq_refl) _ _ rd (fun regs => alu64 op (getr regs rs1) (sext 64 imm))); [|apply HIH; exact Hw].
      intros regs HR; split; [exact (step_opimm_gen SEGS regs _ M rom w _ rd rs1 imm Hf He Hd) | apply Hv, HR]. }
    destruct op; try (destruct H; fail).
    + (* [comment removed for export] *)
      destruct (Z.eqb (bv_signed imm) 0) eqn:E0.
      * apply Z.eqb_eq in E0. eapply HG; [|exact H]. intros regs HR.
        rewrite alu_addi, E0, (proj2 HR rs1). unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
      * destruct (Nat.eqb (ridx rs1) 0) eqn:E1.
        -- apply Nat.eqb_eq in E1. eapply HG; [|exact H]. intros regs HR.
           rewrite alu_addi, (proj2 HR rs1), E1. cbn [rget]. unfold v_addi.
           change (bv_unsigned (Z_to_bv 64 0)) with 0. reflexivity.
        -- eapply HG; [|exact H]. intros regs HR. rewrite (proj2 HR rs1). cbn [val_imm]. apply alu_addi.
    + eapply HG; [|exact H]. intros regs HR. rewrite (proj2 HR rs1). apply alu_slti.
    + eapply HG; [|exact H]. intros regs HR. rewrite (proj2 HR rs1). apply alu_sltiu.
    + eapply HG; [|exact H]. intros regs HR. rewrite (proj2 HR rs1). apply alu_xori.
    + eapply HG; [|exact H]. intros regs HR. rewrite (proj2 HR rs1). apply alu_ori.
    + eapply HG; [|exact H]. intros regs HR. rewrite (proj2 HR rs1). apply alu_andi.
  - (* [comment removed for export] *)
    destruct op; try (destruct H; fail);
      (eapply (step_rw _ (HL eq_refl) _ _ rd (fun regs => alu64 _ (getr regs rs1) (zext 64 shamt))); [|apply HIH; exact H];
       intros regs HR; split; [exact (step_shiftimm_gen SEGS regs _ M rom w _ rd rs1 shamt Hf He Hd)|];
       rewrite (proj2 HR rs1); cbn [val_sh]).
    + apply alu_slli. + apply alu_srli. + apply alu_srai.
  - (* [comment removed for export] *)
    eapply (step_rw _ (HL eq_refl) _ _ rd (fun regs => alu64 op (getr regs rs1) (getr regs rs2))); [|apply HIH; exact H].
    intros regs HR; split; [exact (step_op_gen SEGS regs _ M rom w op rd rs1 rs2 Hf He Hd)|].
    rewrite (proj2 HR rs1), (proj2 HR rs2). destruct op; cbn [val_op].
    + apply alu_add. + apply alu_sub. + apply alu_sll. + apply alu_slt. + apply alu_sltu.
    + apply alu_xor. + apply alu_srl. + apply alu_sra. + apply alu_or. + apply alu_and.
  - (* [comment removed for export] *)
    eapply (step_rw _ (HL eq_refl) _ _ rd (fun regs => sext 64 (alu32 ALU_ADD (low32 (getr regs rs1)) (sext 32 imm)))); [|apply HIH; exact H].
    intros regs HR; split; [exact (step_opimm32_gen SEGS regs _ M rom w rd rs1 imm Hf He Hd)|].
    rewrite (proj2 HR rs1). apply w_addiw.
  - (* [comment removed for export] *)
    destruct op; try (destruct H; fail);
      (eapply (step_rw _ (HL eq_refl) _ _ rd (fun regs => sext 64 (alu32 _ (low32 (getr regs rs1)) (zext 32 shamt)))); [|apply HIH; exact H];
       intros regs HR; split; [exact (step_shiftimm32_gen SEGS regs _ M rom w _ rd rs1 shamt Hf He Hd)|];
       rewrite (proj2 HR rs1); cbn [val_shw]).
    + apply w_slliw. + apply w_srliw. + apply w_sraiw.
  - (* [comment removed for export] *)
    destruct op; try (destruct H; fail);
      (eapply (step_rw _ (HL eq_refl) _ _ rd (fun regs => sext 64 (alu32 _ (low32 (getr regs rs1)) (low32 (getr regs rs2))))); [|apply HIH; exact H];
       intros regs HR; split; [exact (step_op32_gen SEGS regs _ M rom w _ rd rs1 rs2 Hf He Hd)|];
       rewrite (proj2 HR rs1), (proj2 HR rs2); cbn [val_opw]).
    + apply w_addw. + apply w_subw. + apply w_sllw. + apply w_srlw. + apply w_sraw.
  - (* [comment removed for export] *)
    eapply (step_same _ (HL eq_refl)); [|apply HIH; exact H]. intros regs HR.
    exact (step_fence_nop SEGS regs _ M rom w fm pred succ rd rs1 Hf He Hd).
  - (* [comment removed for export] *)
    eapply (step_rw _ (HL eq_refl) _ _ rd (fun regs => mul_div op (getr regs rs1) (getr regs rs2))); [|apply HIH; exact H].
    intros regs HR; split; [exact (step_mul_gen SEGS regs _ M rom w op rd rs1 rs2 Hf He Hd)|].
    rewrite (proj2 HR rs1), (proj2 HR rs2).
    destruct op; cbn [val_mul].
    + apply m_mul. + apply m_mulh. + apply m_mulhsu. + apply m_mulhu.
    + apply m_div. + exact eq_refl. + apply m_rem. + exact eq_refl.
  - (* [comment removed for export] *)
    destruct op; try (destruct H; fail);
      (eapply (step_rw _ (HL eq_refl) _ _ rd (fun regs => sext 64 (mul_div _ (low32 (getr regs rs1)) (low32 (getr regs rs2))))); [|apply HIH; exact H];
       intros regs HR; split; [exact (step_mul32_gen SEGS regs _ M rom w _ rd rs1 rs2 Hf He Hd)|];
       rewrite (proj2 HR rs1), (proj2 HR rs2); cbn [val_mulw]).
    + apply w_mulw. + apply w_divw. + apply w_divuw. + apply w_remw. + apply w_remuw.
Qed.

End Sound.
End WP.

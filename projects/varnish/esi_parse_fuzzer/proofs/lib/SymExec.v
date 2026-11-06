(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Foott1g.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive expr : Type :=
| ELit  (z : Z)
| EVar  (n : nat)
| EAlu  (op : aluop) (a b : expr)   (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)   (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)   (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr).  (* [comment removed for export] *)

Definition env := nat -> word.

Fixpoint edenot (E : env) (e : expr) : word :=
  match e with
  | ELit z => Z_to_bv 64 z
  | EVar n => E n
  | EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | EMd op a b => mul_div op (edenot E a) (edenot E b)
  | EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv64_wrap_l : forall a b, Z_to_bv 64 (bv_wrap 64 a + b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_l.
Qed.

Lemma Z_to_bv64_wrap_r : forall a b, Z_to_bv 64 (a + bv_wrap 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_r.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_addi_lit : forall p i, v_addi (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros p i. unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_l. Qed.

Lemma btgt_lit : forall p i, btgt (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros. apply v_addi_lit. Qed.

Lemma v_auipc_lit : forall p i, v_auipc (Z_to_bv 64 p) i = Z_to_bv 64 (i + p).
Proof.
  intros p i. unfold v_auipc. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_r.
Qed.

Lemma jalr_tgt_lit : forall z i,
  jalr_tgt (Z_to_bv 64 z) i = Z_to_bv 64 (Z.land (bv_wrap 64 z + i) (-2)).
Proof. intros z i. unfold jalr_tgt, jalr_tgtZ. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sext64_lit : forall {n} (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof. reflexivity. Qed.

Lemma zext64_lit : forall {n} (b : bv n), zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof. reflexivity. Qed.

Lemma bv_wrap_32_64 : forall z, bv_wrap 32 (bv_wrap 64 z) = bv_wrap 32 z.
Proof.
  intro z. rewrite bv_wrap32_mod, !bv_wrap64_mod, bv_wrap32_mod.
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia |].
  exists (2^32)%Z. reflexivity.
Qed.

Lemma low32_lit : forall z, low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
Proof.
  intro z. unfold low32. apply bv_eq.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
  apply bv_wrap_32_64.
Qed.

Lemma sext32_low32 : forall {n} (b : bv n), sext 32 b = low32 (Z_to_bv 64 (bv_signed b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.

Lemma zext32_low32 : forall {n} (b : bv n), zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkAlu (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD =>
      match b with
      | ELit y =>
          match a with
          | ELit x => ELit (x + y)
          | EAlu ALU_ADD a' (ELit x) => EAlu ALU_ADD a' (ELit (x + y))
          | _ => EAlu ALU_ADD a b
          end
      | _ => EAlu ALU_ADD a b
      end
  | ALU_SUB =>
      match b with
      | ELit y =>
          match a with
          | ELit x => ELit (x - y)
          | EAlu ALU_ADD a' (ELit x) => EAlu ALU_ADD a' (ELit (x - y))
          | _ => EAlu ALU_SUB a b
          end
      | _ => EAlu ALU_SUB a b
      end
  | _ => EAlu op a b
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_add_lit : forall (u : word) x,
  v_add u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u + x).
Proof.
  intros u x. unfold v_add. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_r.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sr_get (sr : list expr) (r : reg) : expr :=
  if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0).

(* [comment removed for export] *)
Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sbase : Type :=
| SBLit
| SBVar (n : nat).

Definition sbase_eqb (b1 b2 : sbase) : bool :=
  match b1, b2 with
  | SBLit, SBLit => true
  | SBVar n, SBVar m => Nat.eqb n m
  | _, _ => false
  end.

(* [comment removed for export] *)

Record saddr : Type := SA { a_base : sbase; a_off : Z }.

(* [comment removed for export] *)
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

Definition bdenot (E : env) (b : sbase) : word :=
  match b with SBLit => Z_to_bv 64 0 | SBVar n => E n end.

(* [comment removed for export] *)
Definition adenot (E : env) (a : saddr) : word :=
  v_addi (bdenot E (a_base a)) (a_off a).

(* [comment removed for export] *)
Definition to_saddr (e : expr) (i : Z) : option saddr :=
  match e with
  | ELit z => Some (SA SBLit (z + i))
  | EVar n => Some (SA (SBVar n) i)
  | EAlu ALU_ADD (EVar n) (ELit z) => Some (SA (SBVar n) (z + i))
  | EAlu ALU_ADD (ELit z) (EVar n) => Some (SA (SBVar n) (z + i))
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sym_state : Type := SS {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;
  s_next : nat
}.

(* [comment removed for export] *)
Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_next ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SS npc (s_regs ss) (s_log ss) (s_next ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_ok (E : env) (sr : list expr) (regs : bvmap 5 word) : Prop :=
  forall r : reg, getr regs r = edenot E (sr_get sr r).

(* [comment removed for export] *)
Fixpoint mem_denot (E : env) (base : word -> option byte)
                   (log : list sentry) : word -> option byte :=
  match log with
  | [] => base
  | SE a w v :: rest =>
      wbytes (mem_denot E base rest) (adenot E a)
             (word_to_le_bytes w (edenot E v))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint log_flat (E : env) (log : list sentry) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      (0 <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z
      /\ (bv_unsigned (bdenot E (a_base a)) + a_off a < 2^64)%Z
      /\ (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat w <= 2^64)%Z
      /\ log_flat E rest
  end.

(* [comment removed for export] *)
Definition st_ok (E : env) (base rom : word -> option byte)
                 (ss : sym_state) (ms : machine_state) : Prop :=
  exists regs, ms = mkst regs (Z_to_bv 64 (s_pc ss))
                          (mem_denot E base (s_log ss)) rom
            /\ regs_ok E (s_regs ss) regs
            /\ log_flat E (s_log ss).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sr_id : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7;
   EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15;
   EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

Definition E0 (regs : bvmap 5 word) : env :=
  fun n => getr regs (Z_to_bv 5 (Z.of_nat n)).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Eplus (regs : bvmap 5 word) (vals : list word) : env :=
  fun n => if Nat.ltb n 32
           then getr regs (Z_to_bv 5 (Z.of_nat n))
           else nth (n - 32) vals (Z_to_bv 64 0).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : nat)
| SCDisjoint (a1 : saddr) (n1 : nat) (a2 : saddr) (n2 : nat)
| SCStoreOk  (a : saddr) (n : nat)
| SCReadBase (a : saddr) (n : nat) (e : expr).

(* [comment removed for export] *)
Definition sc_flat (E : env) (a : saddr) (n : nat) : Prop :=
  (0 <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z
  /\ (bv_unsigned (bdenot E (a_base a)) + a_off a < 2^64)%Z
  /\ (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat n <= 2^64)%Z.

(* [comment removed for export] *)

Definition sc_denot (segs : list Segment) (base : word -> option byte)
                    (E : env) (s : sidecond) : Prop :=
  match s with
  | SCBr t c a b => branch_taken c (edenot E a) (edenot E b) = t
  | SCFlat a n => sc_flat E a n
  | SCDisjoint a1 n1 a2 n2 =>
      (bv_unsigned (adenot E a1) + Z.of_nat n1 <= 2^64)%Z
      /\ (bv_unsigned (adenot E a2) + Z.of_nat n2 <= 2^64)%Z
      /\ ((bv_unsigned (adenot E a1) + Z.of_nat n1 <= bv_unsigned (adenot E a2))%Z
          \/ (bv_unsigned (adenot E a2) + Z.of_nat n2 <= bv_unsigned (adenot E a1))%Z)
  | SCStoreOk a n => RiscvSemantics.store_ok segs base (adenot E a) n = true
  | SCReadBase a n e =>
      exists bs, rdn segs base (adenot E a) n = Some bs
                 /\ bytes_le_to_Z bs = bv_unsigned (edenot E e)
  end.

Definition scs_denot (segs : list Segment) (base : word -> option byte)
                     (E : env) (l : list sidecond) : Prop :=
  Forall (sc_denot segs base E) l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sm_lookup (log : list sentry) (b : sbase) (k : Z) (n : nat)
  : option (option expr * list sidecond) :=
  match log with
  | [] => Some (None, [])
  | SE (SA b' k') w v :: rest =>
      if sbase_eqb b b' then
        (if (Z.eqb k k' && Nat.eqb n 8 && Nat.eqb w 8)%bool
         then Some (Some v, [])
         else if (Z.leb (k + Z.of_nat n) k' || Z.leb (k' + Z.of_nat w) k)%bool
              then sm_lookup rest b k n
              else None)
      else
        match sm_lookup rest b k n with
        | Some (r, scs) =>
            Some (r, SCDisjoint (SA b k) n (SA b' k') w :: scs)
        | None => None
        end
  end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition mkSext32 (e : expr) : expr := EAluw ALU_ADD e (ELit 0).

(* [comment removed for export] *)
Definition sym_step (i : instr) (ss : sym_state) (rds : list expr)
  : option (sym_state * list sidecond * list expr) :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm =>
      Some (sset ss rd (mkAlu op (g rs) (ELit (bv_signed imm))) (p + 4), [], rds)
  | ShiftImm op rd rs sh =>
      Some (sset ss rd (mkAlu op (g rs) (ELit (bv_unsigned sh))) (p + 4), [], rds)
  | Op op rd rs1 rs2 =>
      Some (sset ss rd (mkAlu op (g rs1) (g rs2)) (p + 4), [], rds)
  | OpImm32 rd rs imm =>
      Some (sset ss rd (EAluw ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4), [], rds)
  | ShiftImm32 op rd rs sh =>
      Some (sset ss rd (EAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4), [], rds)
  | Op32 op rd rs1 rs2 =>
      Some (sset ss rd (EAluw op (g rs1) (g rs2)) (p + 4), [], rds)
  | Mul op rd rs1 rs2 =>
      Some (sset ss rd (EMd op (g rs1) (g rs2)) (p + 4), [], rds)
  | Mul32 op rd rs1 rs2 =>
      Some (sset ss rd (EMdw op (g rs1) (g rs2)) (p + 4), [], rds)
  | Lui rd imm =>
      Some (sset ss rd (ELit (Z.shiftl (bv_signed imm) 12)) (p + 4), [], rds)
  | Auipc rd imm =>
      Some (sset ss rd (ELit (Z.shiftl (bv_signed imm) 12 + p)) (p + 4), [], rds)
  | Jal rd imm =>
      Some (sset ss rd (ELit (p + 4)) (p + bv_signed imm), [], rds)
  | Jalr rd rs1 imm =>
      (* [comment removed for export] *)
      match g rs1 with
      | ELit z => Some (sset ss rd (ELit (p + 4))
                             (Z.land (bv_wrap 64 z + bv_signed imm) (-2)), [], rds)
      | _ => None
      end
  (* [comment removed for export] *)
  | Load sz sgn rd rs imm =>
      let n := msize_bytes sz in
      match to_saddr (g rs) (bv_signed imm) with
      | None => None
      | Some a =>
          match sm_lookup (s_log ss) (a_base a) (a_off a) n with
          | None => None
          | Some (Some v, scs) =>
              (* [comment removed for export] *)
              match sz, sgn with
              | SZ8, true => Some (sset ss rd v (p + 4), SCFlat a 8 :: scs, rds)
              | _, _ => None
              end
          | Some (None, scs) =>
              let i := s_next ss in
              let rv := match rds with [] => EVar i | e :: _ => e end in
              let rds' := match rds with [] => [] | _ :: t => t end in
              let scs' := SCFlat a n :: SCReadBase a n rv :: scs in
              let mk e := Some (SS (p + 4)
                                   (if bv_eqb rd 0 then s_regs ss
                                    else sr_upd (s_regs ss) (ridx rd) e)
                                   (s_log ss) (S i), scs', rds') in
              match sz, sgn with
              | SZ8, true => mk rv
              | SZ4, false => mk rv
              | SZ2, false => mk rv
              | SZ1, false => mk rv
              | SZ4, true => mk (mkSext32 rv)
              | _, _ => None
              end
          end
      end
  (* [comment removed for export] *)
  | Store sz rs1 rs2 imm =>
      match sz with
      | SZ1 | SZ4 | SZ8 =>
          let n := msize_bytes sz in
          match to_saddr (g rs1) (bv_signed imm) with
          | None => None
          | Some a =>
              Some (SS (p + 4) (s_regs ss)
                       (SE a n (g rs2) :: s_log ss) (s_next ss),
                    [SCFlat a n; SCStoreOk a n], rds)
          end
      | _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sym_exec (fuel : nat) (dirs : list bool) (rds : list expr)
                  (ss : sym_state) (acc : list sidecond)
  : sym_state * list sidecond :=
  match fuel with
  | O => (ss, acc)
  | S f =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => (ss, acc)
      | Some w =>
          if is_ecall w then (ss, acc) else
          match decode_any w with
          | None => (ss, acc)
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (ss, acc) else
              match i with
              | Branch c rs1 rs2 imm =>
                  match dirs with
                  | [] => (ss, acc)
                  | t :: dirs' =>
                      sym_exec f dirs' rds
                        (sjump ss (if t then (s_pc ss + bv_signed imm)%Z
                                   else (s_pc ss + 4)%Z))
                        (SCBr t c (sr_get (s_regs ss) rs1)
                                  (sr_get (s_regs ss) rs2) :: acc)
                  end
              | _ =>
                  match sym_step i ss rds with
                  | Some (ss', scs, rds') => sym_exec f dirs rds' ss' (scs ++ acc)
                  | None => (ss, acc)
                  end
              end
          end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sym_val_norm :=
  cbn [edenot sr_get nth ridx bv_eqb s_regs s_pc];
  rewrite ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slt, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra.

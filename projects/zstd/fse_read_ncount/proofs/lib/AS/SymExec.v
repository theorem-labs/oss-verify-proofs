(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import
PropExec CatExec CatSim SeqExec StoreOk.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Section WithFP1.
Context {fx : FPState}.
Inductive expr : Type :=
| ELit (z : Z)
| EVar (n : nat)
| EAlu (op : aluop) (a b : expr)
| EAluw (op : aluop) (a b : expr)
| EMd (op : mulop) (a b : expr)
| EMdw (op : mulop) (a b : expr).
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
#[using="Type"] Lemma Z_to_bv64_wrap_l : forall a b, Z_to_bv 64 (bv_wrap 64 a + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
apply Zplus_mod_idemp_l.
Qed.
#[using="Type"] Lemma Z_to_bv64_wrap_r : forall a b, Z_to_bv 64 (a + bv_wrap 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
apply Zplus_mod_idemp_r.
Qed.
#[using="Type"] Lemma Z_to_bv64_wrap_sub : forall a b,
Z_to_bv 64 (bv_wrap 64 a - bv_wrap 64 b) = Z_to_bv 64 (a - b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.
#[using="Type"] Lemma v_addi_lit : forall p i, v_addi (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros p i. unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_l. Qed.
#[using="Type"] Lemma btgt_lit : forall p i, btgt (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros. apply v_addi_lit. Qed.
#[using="Type"] Lemma v_auipc_lit : forall p i, v_auipc (Z_to_bv 64 p) i = Z_to_bv 64 (i + p).
Proof.
intros p i. unfold v_auipc. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_r.
Qed.
#[using="Type"] Lemma jalr_tgt_lit : forall z i,
jalr_tgt (Z_to_bv 64 z) i = Z_to_bv 64 (Z.land (bv_wrap 64 z + i) (-2)).
Proof. intros z i. unfold jalr_tgt, jalr_tgtZ. rewrite Z_to_bv_unsigned. reflexivity. Qed.
#[using="Type"] Lemma sext64_lit : forall {n} (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof. reflexivity. Qed.
#[using="Type"] Lemma zext64_lit : forall {n} (b : bv n), zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof. reflexivity. Qed.
#[using="Type"] Lemma bv_wrap_32_64 : forall z, bv_wrap 32 (bv_wrap 64 z) = bv_wrap 32 z.
Proof.
intro z. rewrite bv_wrap32_mod, !bv_wrap64_mod, bv_wrap32_mod.
rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia |].
exists (2^32)%Z. reflexivity.
Qed.
#[using="Type"] Lemma low32_lit : forall z, low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
Proof.
intro z. unfold low32. apply bv_eq.
rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
apply bv_wrap_32_64.
Qed.
#[using="Type"] Lemma sext32_low32 : forall {n} (b : bv n), sext 32 b = low32 (Z_to_bv 64 (bv_signed b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.
#[using="Type"] Lemma zext32_low32 : forall {n} (b : bv n), zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.
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
#[using="Type"] Lemma alu64_add_lit : forall x y,
alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
intros x y. rewrite alu_add. unfold v_add. rewrite !Z_to_bv_unsigned.
rewrite Z_to_bv64_wrap_l, Z_to_bv64_wrap_r. reflexivity.
Qed.
#[using="Type"] Lemma alu64_sub_lit : forall x y,
alu64 ALU_SUB (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
intros x y. rewrite alu_sub. unfold v_sub. rewrite !Z_to_bv_unsigned.
apply Z_to_bv64_wrap_sub.
Qed.
#[using="Type"] Lemma Z_to_bv64_wrap_sub_l : forall a b,
Z_to_bv 64 (bv_wrap 64 a - b) = Z_to_bv 64 (a - b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
apply Zminus_mod_idemp_l.
Qed.
#[using="Type"] Lemma Z_to_bv64_wrap_sub_r : forall a b,
Z_to_bv 64 (a - bv_wrap 64 b) = Z_to_bv 64 (a - b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
apply Zminus_mod_idemp_r.
Qed.
#[using="Type"] Lemma v_add_lit : forall (u : word) x,
v_add u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u + x).
Proof.
intros u x. unfold v_add. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_r.
Qed.
#[using="Type"] Lemma v_add_comm : forall x y : word, v_add x y = v_add y x.
Proof. intros x y. unfold v_add. f_equal. lia. Qed.
#[using="Type"] Lemma v_sub_lit : forall (u : word) x,
v_sub u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u - x).
Proof.
intros u x. unfold v_sub. rewrite Z_to_bv_unsigned.
apply Z_to_bv64_wrap_sub_r.
Qed.
#[using="Type"] Lemma alu64_add_add_lit : forall (u : word) x y,
alu64 ALU_ADD (alu64 ALU_ADD u (Z_to_bv 64 x)) (Z_to_bv 64 y)
= alu64 ALU_ADD u (Z_to_bv 64 (x + y)).
Proof.
intros u x y. rewrite !alu_add, !v_add_lit, Z_to_bv_unsigned,
Z_to_bv64_wrap_l. f_equal. lia.
Qed.
#[using="Type"] Lemma alu64_add_sub_lit : forall (u : word) x y,
alu64 ALU_SUB (alu64 ALU_ADD u (Z_to_bv 64 x)) (Z_to_bv 64 y)
= alu64 ALU_ADD u (Z_to_bv 64 (x - y)).
Proof.
intros u x y. rewrite alu_sub, !alu_add, !v_add_lit, !v_sub_lit,
!Z_to_bv_unsigned, !Z_to_bv64_wrap_sub_l. f_equal. lia.
Qed.
#[using="Type"] Lemma mkAlu_denot : forall E op a b,
edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b).
Proof.
intros E op a b. destruct op; try reflexivity;
(destruct b as [y| | | | | ]; [|reflexivity..]);
(destruct a as [x| |op' a1 a2| | | ]; [| | |reflexivity..]);
try reflexivity;
try (cbn [edenot]; auto using alu64_add_lit, alu64_sub_lit; fail);
destruct op'; try reflexivity;
(destruct a2 as [z| | | | | ]; [|reflexivity..]);
cbn [edenot]; auto using alu64_add_add_lit, alu64_add_sub_lit.
Qed.
Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).
#[using="Type"] Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof.
intros r r' H. apply bv_eq. unfold ridx in H.
pose proof (u5_range r). pose proof (u5_range r').
lia.
Qed.
Definition sr_get (sr : list expr) (r : reg) : expr :=
if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0).
Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
match n with
| O => match sr with [] => [e] | _ :: t => e :: t end
| S n' => match sr with
| [] => ELit 0 :: sr_upd [] n' e
| h :: t => h :: sr_upd t n' e
end
end.
#[using="Type"] Lemma nth_sr_upd : forall n sr e i,
nth i (sr_upd sr n e) (ELit 0) =
if Nat.eqb i n then e else nth i sr (ELit 0).
Proof.
induction n as [|n IH]; intros sr e i.
- destruct sr; destruct i; cbn; try reflexivity;
destruct i; reflexivity.
- destruct sr as [|h t]; destruct i as [|i]; cbn; try reflexivity.
+ rewrite IH. destruct (Nat.eqb i n); [reflexivity|].
destruct i; reflexivity.
+ apply IH.
Qed.
Inductive sbase : Type :=
| SBLit
| SBVar (n : nat).
Definition sbase_eqb (b1 b2 : sbase) : bool :=
match b1, b2 with
| SBLit, SBLit => true
| SBVar n, SBVar m => Nat.eqb n m
| _, _ => false
end.
Record saddr : Type := SA { a_base : sbase; a_off : Z }.
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.
Definition bdenot (E : env) (b : sbase) : word :=
match b with SBLit => Z_to_bv 64 0 | SBVar n => E n end.
Definition adenot (E : env) (a : saddr) : word :=
v_addi (bdenot E (a_base a)) (a_off a).
Definition to_saddr (e : expr) (i : Z) : option saddr :=
match e with
| ELit z => Some (SA SBLit (z + i))
| EVar n => Some (SA (SBVar n) i)
| EAlu ALU_ADD (EVar n) (ELit z) => Some (SA (SBVar n) (z + i))
| EAlu ALU_ADD (ELit z) (EVar n) => Some (SA (SBVar n) (z + i))
| _ => None
end.
#[using="Type"] Lemma u_Z_to_bv64_0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. rewrite Z_to_bv_unsigned. reflexivity. Qed.
#[using="Type"] Lemma to_saddr_denot : forall E e i a,
to_saddr e i = Some a -> adenot E a = v_addi (edenot E e) i.
Proof.
intros E e i a H. unfold adenot.
destruct e as [z|n|op e1 e2| | | ]; cbn in H;
try discriminate.
- injection H as <-. cbn [a_base a_off bdenot edenot].
unfold v_addi. rewrite u_Z_to_bv64_0, Z_to_bv_unsigned,
Z_to_bv64_wrap_l. f_equal; lia.
- injection H as <-. reflexivity.
- destruct op; cbn in H; try discriminate.
destruct e1; destruct e2; cbn in H; try discriminate;
injection H as <-; cbn [a_base a_off bdenot edenot]; rewrite alu_add.
+
rewrite v_add_comm, v_add_lit. unfold v_addi.
rewrite Z_to_bv_unsigned, Z_to_bv64_wrap_l. f_equal; lia.
+
rewrite v_add_lit. unfold v_addi.
rewrite Z_to_bv_unsigned, Z_to_bv64_wrap_l. f_equal; lia.
Qed.
Record sym_state : Type := SS {
s_pc : Z;
s_regs : list expr;
s_log : list sentry;
s_next : nat
}.
Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
(s_log ss) (s_next ss).
Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
SS npc (s_regs ss) (s_log ss) (s_next ss).
Definition regs_ok (E : env) (sr : list expr) (regs : bvmap 5 word) : Prop :=
forall r : reg, getr regs r = edenot E (sr_get sr r).
Fixpoint mem_denot (E : env) (base : word -> option byte)
(log : list sentry) : word -> option byte :=
match log with
| [] => base
| SE a w v :: rest =>
wbytes (mem_denot E base rest) (adenot E a)
(word_to_le_bytes w (edenot E v))
end.
#[using="Type"] Lemma mem_denot_grows : forall E base log, mem_grows base (mem_denot E base log).
Proof.
intros E base log. induction log as [|[a w v] rest IH]; cbn [mem_denot].
- apply mem_grows_refl.
- eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.
Fixpoint log_flat (E : env) (log : list sentry) : Prop :=
match log with
| [] => True
| SE a w _ :: rest =>
(0 <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z
/\ (bv_unsigned (bdenot E (a_base a)) + a_off a < 2^64)%Z
/\ (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat w <= 2^64)%Z
/\ log_flat E rest
end.
Definition st_ok (E : env) (base rom : word -> option byte)
(ss : sym_state) (ms : machine_state) : Prop :=
exists regs, ms = mkst regs (Z_to_bv 64 (s_pc ss))
(mem_denot E base (s_log ss)) rom
/\ regs_ok E (s_regs ss) regs
/\ log_flat E (s_log ss).
#[using="Type"] Lemma regs_ok_upd : forall E sr regs rd v e,
regs_ok E sr regs ->
edenot E e = v ->
regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
(if bv_eqb rd 0 then regs else regupd regs rd v).
Proof.
intros E sr regs rd v e Hr Hv.
destruct (bv_eqb rd 0) eqn:Hrd; [exact Hr|].
assert (Hne : rd <> 0).
{ intro Hc. subst rd. rewrite bv_eqb_refl in Hrd. discriminate. }
intro r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r. unfold getr. rewrite Hr0. reflexivity.
- rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r.
rewrite getr_same by exact Hne. exact (eq_sym Hv).
+ assert (Hrr : r <> rd).
{ intro Hc. subst r. rewrite Nat.eqb_refl in Hi. discriminate. }
rewrite getr_other by exact Hrr.
specialize (Hr r). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.
#[using="Type"] Lemma regs_ok_pin : forall E sr regs (r : reg) e,
regs_ok E sr regs ->
getr regs r = edenot E e ->
regs_ok E (sr_upd sr (ridx r) e) regs.
Proof.
intros E sr regs r e Hr Hv r'. unfold sr_get.
destruct (bv_eqb r' 0) eqn:Hr0.
- assert (r' = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
subst r'. unfold getr. rewrite Hr0. reflexivity.
- rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
+ apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
+ specialize (Hr r'). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.
Definition E0 (regs : bvmap 5 word) : env :=
fun n => getr regs (Z_to_bv 5 (Z.of_nat n)).
#[using="Type"] Lemma ridx_range : forall r : reg, (ridx r < 32)%nat.
Proof. intro r. unfold ridx. pose proof (u5_range r). lia. Qed.
#[using="Type"] Lemma ridx_roundtrip : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
intro r. apply bv_eq. unfold ridx. rewrite Z_to_bv_unsigned.
pose proof (u5_range r). rewrite Z2Nat.id by lia.
apply bv_wrap_bv_unsigned.
Qed.
Inductive sidecond : Type :=
| SCBr (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat (a : saddr) (n : nat)
| SCDisjoint (a1 : saddr) (n1 : nat) (a2 : saddr) (n2 : nat)
| SCStoreOk (a : saddr) (n : nat)
| SCReadBase (a : saddr) (n : nat) (e : expr).
Definition sc_flat (E : env) (a : saddr) (n : nat) : Prop :=
(0 <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z
/\ (bv_unsigned (bdenot E (a_base a)) + a_off a < 2^64)%Z
/\ (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat n <= 2^64)%Z.
#[using="Type"] Lemma flat_u : forall E a n, sc_flat E a n ->
bv_unsigned (adenot E a) = (bv_unsigned (bdenot E (a_base a)) + a_off a)%Z.
Proof.
intros E a n (H1 & H2 & H3). unfold adenot, v_addi.
rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia.
Qed.
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
Definition mkSext32 (e : expr) : expr := EAluw ALU_ADD e (ELit 0).
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
match g rs1 with
| ELit z => Some (sset ss rd (ELit (p + 4))
(Z.land (bv_wrap 64 z + bv_signed imm) (-2)), [], rds)
| _ => None
end
| Load sz sgn rd rs imm =>
let n := msize_bytes sz in
match to_saddr (g rs) (bv_signed imm) with
| None => None
| Some a =>
match sm_lookup (s_log ss) (a_base a) (a_off a) n with
| None => None
| Some (Some v, scs) =>
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
#[using="Type"] Lemma shiftr8_mod_pow2 : forall (k z : Z), (0 <= k)%Z ->
(Z.shiftr (z mod 2 ^ (k + 8)) 8 = (Z.shiftr z 8) mod 2 ^ k)%Z.
Proof.
intros k z Hk. apply Z.bits_inj'. intros i Hi.
rewrite Z.shiftr_spec by lia.
destruct (Z.ltb i k) eqn:Hlt.
- apply Z.ltb_lt in Hlt.
rewrite Z.mod_pow2_bits_low by lia.
rewrite Z.mod_pow2_bits_low by lia.
rewrite Z.shiftr_spec by lia. reflexivity.
- apply Z.ltb_ge in Hlt.
rewrite Z.mod_pow2_bits_high by lia.
rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
#[using="Type"] Lemma mod_pow2_low : forall (z k m : Z), (0 <= m <= k)%Z ->
((z mod 2 ^ k) mod 2 ^ m = z mod 2 ^ m)%Z.
Proof.
intros z k m Hm. apply Z.bits_inj'. intros i Hi.
destruct (Z.ltb i m) eqn:Hlt.
- apply Z.ltb_lt in Hlt.
rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- apply Z.ltb_ge in Hlt.
rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
#[using="Type"] Lemma Z_to_le_bytes_mod : forall (n : nat) (z : Z),
Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n))%Z = Z_to_le_bytes n z.
Proof.
induction n as [|n IH]; intro z; [reflexivity|].
cbn [Z_to_le_bytes]. f_equal.
- apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8)%Z.
apply mod_pow2_low. lia.
- replace (8 * Z.of_nat (S n))%Z with (8 * Z.of_nat n + 8)%Z by lia.
rewrite shiftr8_mod_pow2 by lia. apply IH.
Qed.
#[using="Type"] Lemma low32_le_bytes : forall v : word,
Z_to_le_bytes 4%nat (bv_unsigned (low32 v)) = word_to_le_bytes 4 v.
Proof.
intro v. unfold word_to_le_bytes, low32.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
change (bv_wrap 32 (bv_unsigned v)) with (bv_unsigned v mod 2 ^ 32)%Z.
exact (Z_to_le_bytes_mod 4 (bv_unsigned v)).
Qed.
#[using="Type"] Lemma step_sw_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
RiscvSemantics.store_ok segs mem
(v_addi (getr regs rs1) (bv_signed imm)) 4%nat = true ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst regs (v_addi pc 4)
(wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
(word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, low32_le_bytes, b_npc4.
reflexivity.
Qed.
Section WithSegs.
Variable segs : list Segment.
#[using="Type"] Lemma scs_denot_cons : forall base E s l,
scs_denot segs base E (s :: l) -> sc_denot segs base E s /\ scs_denot segs base E l.
Proof. intros base E s l H. inversion H; auto. Qed.
#[using="Type"] Lemma scs_denot_app : forall base E l1 l2,
scs_denot segs base E (l1 ++ l2) ->
scs_denot segs base E l1 /\ scs_denot segs base E l2.
Proof.
intros base E l1 l2 H. unfold scs_denot in *.
split; apply Forall_forall; intros x Hx;
rewrite Forall_forall in H; apply H, in_or_app; auto.
Qed.
End WithSegs.
End WithFP1.

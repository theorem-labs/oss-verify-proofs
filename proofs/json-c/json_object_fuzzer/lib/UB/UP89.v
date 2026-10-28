(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q91D.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Module GwI.
Definition segs := rsegs.
Definition base := 0x58ab4%Z.
Definition w_2 := 0xfffbb597%Z.
Definition w_3 := 0x98c5b787%Z.
Definition w_16 := 0xfffbb597%Z.
Definition w_17 := 0x9845b787%Z.
Definition hi_2 := (Z_to_bv 20 1048507).
Definition hi_16 := (Z_to_bv 20 1048507).
Definition lo_3 := (Z_to_bv 12 2444).
Definition lo_17 := (Z_to_bv 12 2436).
Definition G_107a8 := 0x13448%Z.
Definition G_107c8 := 0x13478%Z.
Lemma CODE : CodeAt.code_at rsegs 0x58ab4 (Q91D.Mq4.scalbn_code 0xfffbb597%Z 0x98c5b787%Z 0xfffbb597%Z 0x9845b787%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x58ab4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x58ab4 /\ 0x58ab4 + 152 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition scalbn_entry := 0x58ab4%Z.
Lemma gw_eq_scalbn_entry : @scalbn_entry = ltac:(GwInst.gw_term (@Q91D.Mq4.scalbn_entry 0x58ab4) (@scalbn_entry)). Proof. unfold scalbn_entry, Q91D.Mq4.scalbn_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scalbn_entry : gw_eqs.
Definition scalbn_tailpc := 0x58b30%Z.
Lemma gw_eq_scalbn_tailpc : @scalbn_tailpc = ltac:(GwInst.gw_term (@Q91D.Mq4.scalbn_tailpc 0x58ab4) (@scalbn_tailpc)). Proof. unfold scalbn_tailpc, Q91D.Mq4.scalbn_tailpc; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scalbn_tailpc : gw_eqs.

Definition two_p1023 : word := Z_to_bv 64 0x7FE0000000000000.
Lemma gw_eq_two_p1023 : @two_p1023 = ltac:(GwInst.gw_term (@Q91D.Mq4.two_p1023) (@two_p1023)). Proof. unfold two_p1023, Q91D.Mq4.two_p1023; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_two_p1023 : gw_eqs.
Definition two_m969  : word := Z_to_bv 64 0x0360000000000000.
Lemma gw_eq_two_m969 : @two_m969 = ltac:(GwInst.gw_term (@Q91D.Mq4.two_m969) (@two_m969)). Proof. unfold two_m969, Q91D.Mq4.two_m969; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_two_m969 : gw_eqs.

Definition scalbn_u (n : Z) : word := Z_to_bv 64 (Z.shiftl (1023 + n) 52).
Lemma gw_eq_scalbn_u : @scalbn_u = ltac:(GwInst.gw_term (@Q91D.Mq4.scalbn_u) (@scalbn_u)). Proof. unfold scalbn_u, Q91D.Mq4.scalbn_u; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scalbn_u : gw_eqs.

Definition scalbn_reduce (x : word) (n : Z) : word * Z :=
if (1023 <? n)%Z then
let y := fmul_d RNE x two_p1023 in let n := (n - 1023)%Z in
if (1023 <? n)%Z then
let y := fmul_d RNE y two_p1023 in let n := (n - 1023)%Z in
(y, if (1023 <? n)%Z then 1023%Z else n)
else (y, n)
else if (n <? -1022)%Z then
let y := fmul_d RNE x two_m969 in let n := (n + 969)%Z in
if (n <? -1022)%Z then
let y := fmul_d RNE y two_m969 in let n := (n + 969)%Z in
(y, if (n <? -1022)%Z then (-1022)%Z else n)
else (y, n)
else (x, n).
Lemma gw_eq_scalbn_reduce : @scalbn_reduce = ltac:(GwInst.gw_term (@Q91D.Mq4.scalbn_reduce) (@scalbn_reduce)). Proof. unfold scalbn_reduce, Q91D.Mq4.scalbn_reduce; rewrite ?gw_eq_two_p1023, ?gw_eq_two_m969; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scalbn_reduce : gw_eqs.

Definition scalbn_model (x : word) (n : Z) : word :=
let (y, n') := scalbn_reduce x n in fmul_d RNE y (scalbn_u n').
Lemma gw_eq_scalbn_model : @scalbn_model = ltac:(GwInst.gw_term (@Q91D.Mq4.scalbn_model) (@scalbn_model)). Proof. unfold scalbn_model, Q91D.Mq4.scalbn_model; rewrite ?gw_eq_scalbn_u, ?gw_eq_scalbn_reduce; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scalbn_model : gw_eqs.

Definition scalbn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(x : word) (n : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (f15 : word) fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (scalbn_model x n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'.
Lemma gw_eq_scalbn_post : @scalbn_post = ltac:(GwInst.gw_term (@Q91D.Mq4.scalbn_post rsegs) (@scalbn_post)). Proof. unfold scalbn_post, Q91D.Mq4.scalbn_post; rewrite ?gw_eq_scalbn_model; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scalbn_post : gw_eqs.

Lemma word_signed_cases : ltac2:(Q6nq.tyx '(@Q91D.Mq4.word_signed_cases) [[@gw_eq_scalbn_entry__3; @gw_eq_scalbn_entry__2; @gw_eq_scalbn_entry]; [@gw_eq_scalbn_tailpc__3; @gw_eq_scalbn_tailpc__2; @gw_eq_scalbn_tailpc]; [@gw_eq_two_p1023__3; @gw_eq_two_p1023__2; @gw_eq_two_p1023]; [@gw_eq_two_m969__3; @gw_eq_two_m969__2; @gw_eq_two_m969]; [@gw_eq_scalbn_u__3; @gw_eq_scalbn_u__2; @gw_eq_scalbn_u]; [@gw_eq_scalbn_reduce__3; @gw_eq_scalbn_reduce__2; @gw_eq_scalbn_reduce]; [@gw_eq_scalbn_model__3; @gw_eq_scalbn_model__2; @gw_eq_scalbn_model]; [@gw_eq_scalbn_post__3; @gw_eq_scalbn_post__2; @gw_eq_scalbn_post]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@Q91D.Mq4.word_signed_cases) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq4.word_signed_cases)]. Qed.

Lemma scalbn_pack : ltac2:(Q6nq.tyx '(@Q91D.Mq4.scalbn_pack) [[@gw_eq_scalbn_u]; [@gw_eq_scalbn_entry__3; @gw_eq_scalbn_entry__2; @gw_eq_scalbn_entry]; [@gw_eq_scalbn_tailpc__3; @gw_eq_scalbn_tailpc__2; @gw_eq_scalbn_tailpc]; [@gw_eq_two_p1023__3; @gw_eq_two_p1023__2; @gw_eq_two_p1023]; [@gw_eq_two_m969__3; @gw_eq_two_m969__2; @gw_eq_two_m969]; [@gw_eq_scalbn_reduce__3; @gw_eq_scalbn_reduce__2; @gw_eq_scalbn_reduce]; [@gw_eq_scalbn_model__3; @gw_eq_scalbn_model__2; @gw_eq_scalbn_model]; [@gw_eq_scalbn_post__3; @gw_eq_scalbn_post__2; @gw_eq_scalbn_post]] '([(-1023); 1023; 4607182418800017408]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_scalbn_u; first [GwInst.gw_exact (@Q91D.Mq4.scalbn_pack) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq4.scalbn_pack)]. Qed.

Lemma scalbn_tail : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (n' : Z) (Q : machine_state -> Prop),
mem_inv rsegs m -> frm0 fc -> bv_signed a0 = n' -> (-1022 <= n' <= 1023)%Z ->
(forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc',
frm0 fc' ->
Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (fmul_d RNE (reg_get Ft 10) (scalbn_u n')) (bvmap_set 15 (scalbn_u n') Ft))
(ret_pc ra) fc' None m (seg_rom rsegs))) ->
evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 0x58b30) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_scalbn_u; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq4.scalbn_tail) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq4.scalbn_tail)]. Qed.

Lemma signed_of_add : ltac2:(Q6nq.tyx '(@Q91D.Mq4.signed_of_add) [[@gw_eq_scalbn_entry__3; @gw_eq_scalbn_entry__2; @gw_eq_scalbn_entry]; [@gw_eq_scalbn_tailpc__3; @gw_eq_scalbn_tailpc__2; @gw_eq_scalbn_tailpc]; [@gw_eq_two_p1023__3; @gw_eq_two_p1023__2; @gw_eq_two_p1023]; [@gw_eq_two_m969__3; @gw_eq_two_m969__2; @gw_eq_two_m969]; [@gw_eq_scalbn_u__3; @gw_eq_scalbn_u__2; @gw_eq_scalbn_u]; [@gw_eq_scalbn_reduce__3; @gw_eq_scalbn_reduce__2; @gw_eq_scalbn_reduce]; [@gw_eq_scalbn_model__3; @gw_eq_scalbn_model__2; @gw_eq_scalbn_model]; [@gw_eq_scalbn_post__3; @gw_eq_scalbn_post__2; @gw_eq_scalbn_post]] '(@nil Z) 'Q6nq.gwt_nil).
Proof. first [GwInst.gw_exact (@Q91D.Mq4.signed_of_add) | autorewrite with gw_eqs; GwInst.gw_exact (@Q91D.Mq4.signed_of_add)]. Qed.

Ltac scalbn_close :=
intros; unfold scalbn_post;
repeat (lazymatch goal with |- ex _ => eexists end);
split;
[ simp_regs; f_equal; f_equal; unfold scalbn_model, scalbn_reduce, two_p1023, two_m969;
repeat match goal with
| |- context [Z.ltb ?a ?b] =>
first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
end;

repeat match goal with |- context [if Z.ltb ?a ?b then _ else _] => destruct (Z.ltb_spec0 a b) end;
match goal with |- fmul_d _ _ (scalbn_u ?a) = fmul_d _ _ (scalbn_u ?b) => replace b with a by lia end;
reflexivity
| repeat match goal with |- _ /\ _ => split end; assumption ].

Ltac scalbn_go_tail n' :=
lazymatch goal with
| |- evt _ _ (MS _ ?Ft _ _ _ ?m _) =>
eapply (scalbn_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft _ m n');
[ assumption | assumption | | lia | scalbn_close ]
end.

Lemma scalbn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
mem_inv rsegs m -> frm0 fc -> bv_signed a0 = n -> (-2^31 <= n < 2^31)%Z ->
evt rsegs (scalbn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (reg_get F 10) n m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x58ab4) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_scalbn_post; first [GwApply.gw_by_name GwI.segs (@Q91D.Mq4.scalbn_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q91D.Mq4.scalbn_spec)]. Qed.

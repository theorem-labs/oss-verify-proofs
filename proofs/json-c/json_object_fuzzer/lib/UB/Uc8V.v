(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4Eu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4Eu.
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Definition strtoull_entry := 0x5e220%Z.
Lemma gw_eq_strtoull_entry : @strtoull_entry = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtoull_entry 0x5e220) (@strtoull_entry)). Proof. unfold strtoull_entry, Q8QT.Mq1.strtoull_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtoull_entry : gw_eqs.
Definition strtoll_entry := 0x5e2d0%Z.
Lemma gw_eq_strtoll_entry : @strtoll_entry = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtoll_entry 0x5e220) (@strtoll_entry)). Proof. unfold strtoll_entry, Q8QT.Mq1.strtoll_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtoll_entry : gw_eqs.
Definition GOT_GUARD : Z := 0x659d0.
Definition GUARD : Z := 0x97e70.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5e220%Z.
Definition w_9 := 0x00007517%Z.
Definition w_10 := 0x78c53983%Z.
Definition w_19 := 0xbd4fd0ef%Z.
Definition w_24 := 0x270000ef%Z.
Definition w_43 := 0xd59f20ef%Z.
Definition w_54 := 0x00007517%Z.
Definition w_55 := 0x6d853983%Z.
Definition w_64 := 0xb20fd0ef%Z.
Definition w_69 := 0x1bc000ef%Z.
Definition w_89 := 0xca1f20ef%Z.
Definition hi_9 := (Z_to_bv 20 7).
Definition hi_54 := (Z_to_bv 20 7).
Definition lo_10 := (Z_to_bv 12 1932).
Definition lo_55 := (Z_to_bv 12 1752).
Definition joff_19 := (Z_to_bv 21 2085844).
Definition joff_24 := (Z_to_bv 21 624).
Definition joff_43 := (Z_to_bv 21 2043224).
Definition joff_64 := (Z_to_bv 21 2085664).
Definition joff_69 := (Z_to_bv 21 444).
Definition joff_89 := (Z_to_bv 21 2043040).
Definition GOT_GUARD := GOT_GUARD.
Definition GUARD := GUARD.
Definition ISTAB := ISTAB.
Definition RATP := 0x77c00%Z.
Definition RGLOBALS_TOP := 0x99000%Z.
Definition e_errno_loc := 0x50b60%Z.
Definition e_197bc := 0x51024%Z.
Definition e_shlim := 0x5b640%Z.
Definition e_intscan := 0x5e4f0%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5e220 (Q8QT.Mq1.strtolblk_code 0x00007517%Z 0x78c53983%Z 0xbd4fd0ef%Z 0x270000ef%Z 0xd59f20ef%Z 0x00007517%Z 0x6d853983%Z 0xb20fd0ef%Z 0x1bc000ef%Z 0xca1f20ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5e220 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5e220 /\ 0x5e220 + 360 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_e_shlim : CodeAt.code_at rsegs e_shlim Q8QT.Mq1.shlim_code.  Proof. StepGen.code_at_vm. Qed.
Definition intscan_spec := @intscan_spec.
End GwI.

Fixpoint ex_cells (sizes : list nat) (k : list cell -> Prop) : Prop :=
match sizes with
| [] => k []
| s :: r => exists q : list byte, ex_cells r (fun cs => k (CB s q :: cs))
end.
Lemma gw_eq_ex_cells : @ex_cells = ltac:(GwInst.gw_term (@Q8QT.Mq1.ex_cells) (@ex_cells)). Proof. unfold ex_cells, Q8QT.Mq1.ex_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ex_cells : gw_eqs.

Local Definition gwt_X : unit := Q6nq.gwt_nil.
Lemma ex_cells_mono : ltac2:(Q6nq.tyx '(@Q8QT.Mq1.ex_cells_mono) [[@gw_eq_ex_cells]; [@gw_eq_strtoull_entry__3; @gw_eq_strtoull_entry__2; @gw_eq_strtoull_entry]; [@gw_eq_strtoll_entry__3; @gw_eq_strtoll_entry__2; @gw_eq_strtoll_entry]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ex_cells; first [GwInst.gw_exact (@Q8QT.Mq1.ex_cells_mono) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.Mq1.ex_cells_mono)]. Qed.

Lemma rw_cells_CB_sizes : ltac2:(Q6nq.tyx '(@Q8QT.Mq1.rw_cells_CB_sizes) [[@gw_eq_ex_cells]; [@gw_eq_strtoull_entry__3; @gw_eq_strtoull_entry__2; @gw_eq_strtoull_entry]; [@gw_eq_strtoll_entry__3; @gw_eq_strtoll_entry__2; @gw_eq_strtoll_entry]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_ex_cells; first [GwInst.gw_exact (@Q8QT.Mq1.rw_cells_CB_sizes) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.Mq1.rw_cells_CB_sizes)]. Qed.

Lemma le8_read : forall segs m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof. first [GwInst.gw_exact (@Q8QT.Mq1.le8_read) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8QT.Mq1.le8_read)]. Qed.

Definition strtox_W (SP E : Z) : list ivl :=
[(SP - 368, SP); (E, E + 8); (0x77c00 - 164, 0x77c00 - 160)]%Z.
Lemma gw_eq_strtox_W : @strtox_W = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtox_W 0x77c00%Z) (@strtox_W)). Proof. unfold strtox_W, Q8QT.Mq1.strtox_W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtox_W : gw_eqs.

Definition strtox_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP A E lo : Z) (str : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x5 x6 x7 a0' a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (j : Z) (e' : word),
ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch (strtox_W SP E) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' E [C8 (Z_to_bv 64 (A + j))] /\ (0 <= j <= Z.of_nat (length str))%Z
/\ bytes_at rsegs m' A (str ++ [b0])
/\ rw_cells rsegs m' (0x77c00 - 164) [C4 e']
/\ stk rsegs m' lo SP.
Lemma gw_eq_strtox_post : @strtox_post = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtox_post rsegs 0x77c00%Z) (@strtox_post)). Proof. unfold strtox_post, Q8QT.Mq1.strtox_post; rewrite ?gw_eq_strtox_W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtox_post : gw_eqs.

Definition strtox_stmt (entry : Z) : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (str : list byte) (SP A E lo : Z) (e g ej : word),
bv_unsigned sp = SP -> bv_unsigned a0 = A -> bv_unsigned a1 = E -> a2 = Z_to_bv 64 10 ->
bytes_at rsegs m A (str ++ [b0]) -> ~ In b0 str -> (A + Z.of_nat (length str) + 2 <= 2^64)%Z ->
rw_cells rsegs m E [C8 ej] ->
rw_cells rsegs m (0x77c00 - 164) [C4 e] -> tp = Z_to_bv 64 0x77c00 ->
bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 g) ->
stk rsegs m lo SP -> (0x99000 <= lo)%Z -> (lo <= SP - 368)%Z ->
(0x99000 <= E)%Z ->
(E + 8 <= SP - 368 \/ SP <= E)%Z ->
(A + Z.of_nat (length str) + 1 <= SP - 368 \/ SP <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= E \/ E + 8 <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= 0x77c00 - 164 \/ 0x77c00 - 160 <= A)%Z ->
mem_inv rsegs m ->
evt rsegs (strtox_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP A E lo str m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).
Lemma gw_eq_strtox_stmt : @strtox_stmt = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtox_stmt rsegs GOT_GUARD GUARD 0x77c00%Z 0x99000%Z) (@strtox_stmt)). Proof. unfold strtox_stmt, Q8QT.Mq1.strtox_stmt; rewrite ?gw_eq_strtox_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtox_stmt : gw_eqs.

Ltac show_goal := match goal with |- evt _ _ ?ms => idtac "STATE" ms | |- ?g => idtac "GOAL" g end.
Ltac show_fr := match goal with H : rw_cells _ _ (bv_unsigned ?sp + -288)%Z ?c |- _ => idtac "FR" c end.
Ltac lit_store_fix :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)) end;
mem_after_store.

Lemma strtoull_spec : strtox_stmt strtoull_entry.
Proof. rewrite ?gw_eq_strtoull_entry, ?gw_eq_strtox_stmt; first [GwApply.gw_by_name GwI.segs (@Q8QT.Mq1.strtoull_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8QT.Mq1.strtoull_spec)]. Qed.

Lemma strtoll_spec : strtox_stmt strtoll_entry.
Proof. rewrite ?gw_eq_strtoll_entry, ?gw_eq_strtox_stmt; first [GwApply.gw_by_name GwI.segs (@Q8QT.Mq1.strtoll_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8QT.Mq1.strtoll_spec)]. Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTp6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSiI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSiI.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Definition strtoull_entry := 0xda738%Z.
Lemma gw_eq_strtoull_entry : @strtoull_entry = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtoull_entry 0xda738) (@strtoull_entry)). Proof. unfold strtoull_entry, Q8QT.Mq1.strtoull_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtoull_entry : gw_eqs.
Definition strtoll_entry := 0xda7e8%Z.
Lemma gw_eq_strtoll_entry : @strtoll_entry = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtoll_entry 0xda738) (@strtoll_entry)). Proof. unfold strtoll_entry, Q8QT.Mq1.strtoll_entry; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtoll_entry : gw_eqs.
Definition GOT_GUARD : Z := 0xe6b80.
Definition GUARD : Z := 0x642ea0.

Module GwI.
Definition segs := rsegs.
Definition base := 0xda738%Z.
Definition w_9 := 0x0000c517%Z.
Definition w_10 := 0x42453983%Z.
Definition w_19 := 0xb11fb0ef%Z.
Definition w_24 := 0xa78fe0ef%Z.
Definition w_43 := 0xbb9f10ef%Z.
Definition w_54 := 0x0000c517%Z.
Definition w_55 := 0x37053983%Z.
Definition w_64 := 0xa5dfb0ef%Z.
Definition w_69 := 0x9c4fe0ef%Z.
Definition w_89 := 0xb01f10ef%Z.
Definition hi_9 := (Z_to_bv 20 12).
Definition hi_54 := (Z_to_bv 20 12).
Definition lo_10 := (Z_to_bv 12 1060).
Definition lo_55 := (Z_to_bv 12 880).
Definition joff_19 := (Z_to_bv 21 2079504).
Definition joff_24 := (Z_to_bv 21 2089592).
Definition joff_43 := (Z_to_bv 21 2038712).
Definition joff_64 := (Z_to_bv 21 2079324).
Definition joff_69 := (Z_to_bv 21 2089412).
Definition joff_89 := (Z_to_bv 21 2038528).
Definition GOT_GUARD := GOT_GUARD.
Definition GUARD := GUARD.
Definition ISTAB := ISTAB.
Definition RATP := 0x622e60%Z.
Definition RGLOBALS_TOP := 0x645000%Z.
Definition e_errno_loc := 0xcc3a4%Z.
Definition e_197bc := 0xcc39c%Z.
Definition e_shlim := 0xd6294%Z.
Definition e_intscan := 0xd8a10%Z.
Lemma CODE : CodeAt.code_at rsegs 0xda738 (Q8QT.Mq1.strtolblk_code 0x0000c517%Z 0x42453983%Z 0xb11fb0ef%Z 0xa78fe0ef%Z 0xbb9f10ef%Z 0x0000c517%Z 0x37053983%Z 0xa5dfb0ef%Z 0x9c4fe0ef%Z 0xb01f10ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0xda738 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0xda738 /\ 0xda738 + 360 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
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
[(SP - 368, SP); (E, E + 8); (0x622e60 - 164, 0x622e60 - 160)]%Z.
Lemma gw_eq_strtox_W : @strtox_W = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtox_W 0x622e60%Z) (@strtox_W)). Proof. unfold strtox_W, Q8QT.Mq1.strtox_W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtox_W : gw_eqs.

Definition strtox_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP A E lo : Z) (str : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x5 x6 x7 a0' a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (j : Z) (e' : word),
ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch (strtox_W SP E) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' E [C8 (Z_to_bv 64 (A + j))] /\ (0 <= j <= Z.of_nat (length str))%Z
/\ bytes_at rsegs m' A (str ++ [b0])
/\ rw_cells rsegs m' (0x622e60 - 164) [C4 e']
/\ stk rsegs m' lo SP.
Lemma gw_eq_strtox_post : @strtox_post = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtox_post rsegs 0x622e60%Z) (@strtox_post)). Proof. unfold strtox_post, Q8QT.Mq1.strtox_post; rewrite ?gw_eq_strtox_W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_strtox_post : gw_eqs.

Definition strtox_stmt (entry : Z) : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (str : list byte) (SP A E lo : Z) (e g ej : word),
bv_unsigned sp = SP -> bv_unsigned a0 = A -> bv_unsigned a1 = E -> a2 = Z_to_bv 64 10 ->
bytes_at rsegs m A (str ++ [b0]) -> ~ In b0 str -> (A + Z.of_nat (length str) + 2 <= 2^64)%Z ->
rw_cells rsegs m E [C8 ej] ->
rw_cells rsegs m (0x622e60 - 164) [C4 e] -> tp = Z_to_bv 64 0x622e60 ->
bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 g) ->
stk rsegs m lo SP -> (0x645000 <= lo)%Z -> (lo <= SP - 368)%Z ->
(0x645000 <= E)%Z ->
(E + 8 <= SP - 368 \/ SP <= E)%Z ->
(A + Z.of_nat (length str) + 1 <= SP - 368 \/ SP <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= E \/ E + 8 <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= 0x622e60 - 164 \/ 0x622e60 - 160 <= A)%Z ->
mem_inv rsegs m ->
evt rsegs (strtox_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP A E lo str m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).
Lemma gw_eq_strtox_stmt : @strtox_stmt = ltac:(GwInst.gw_term (@Q8QT.Mq1.strtox_stmt rsegs GOT_GUARD GUARD 0x622e60%Z 0x645000%Z) (@strtox_stmt)). Proof. unfold strtox_stmt, Q8QT.Mq1.strtox_stmt; rewrite ?gw_eq_strtox_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
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

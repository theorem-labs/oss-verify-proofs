(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8Ie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Ie.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzOj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSCw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation mem := (word -> option byte).

Definition OUT_DEPTH : Z := 1024.
Lemma gw_eq_OUT_DEPTH : @OUT_DEPTH = ltac:(GwInst.gw_term (@Q8l1.Mq1.OUT_DEPTH) (@OUT_DEPTH)). Proof. unfold OUT_DEPTH, Q8l1.Mq1.OUT_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_OUT_DEPTH : gw_eqs.
Definition PC_DEPTH : Z := 5184.
Lemma gw_eq_PC_DEPTH : @PC_DEPTH = ltac:(GwInst.gw_term (@Q8l1.Mq1.PC_DEPTH) (@PC_DEPTH)). Proof. unfold PC_DEPTH, Q8l1.Mq1.PC_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_PC_DEPTH : gw_eqs.
Definition VF_DEPTH : Z := 5552.
Lemma gw_eq_VF_DEPTH : @VF_DEPTH = ltac:(GwInst.gw_term (@Q8l1.Mq1.VF_DEPTH) (@VF_DEPTH)). Proof. unfold VF_DEPTH, Q8l1.Mq1.VF_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_VF_DEPTH : gw_eqs.
Definition GLOBALS_TOP : Z := 0x99000.
Definition STATIC_SPLIT : Z := 0x62000.

Module GwI.
Definition segs := rsegs.
Definition base := 0x55624%Z.
Definition w_22 := 0x00010517%Z.
Definition w_25 := 0x35453603%Z.
Definition w_81 := 0xfb8ff0ef%Z.
Definition w_281 := 0xfffc1697%Z.
Definition w_282 := 0xc9068693%Z.
Definition w_332 := 0xfffc1597%Z.
Definition w_333 := 0xa7c58593%Z.
Definition w_360 := 0xfffbb597%Z.
Definition w_362 := 0x92f58593%Z.
Definition w_371 := 0xfffbb517%Z.
Definition w_372 := 0x90350513%Z.
Definition w_378 := 0xfffbd517%Z.
Definition w_379 := 0x76f50b93%Z.
Definition w_381 := 0xf49fa0ef%Z.
Definition w_383 := 0xf4dfa0ef%Z.
Definition w_389 := 0x1ec0a0ef%Z.
Definition w_395 := 0xfffbb617%Z.
Definition w_396 := 0x8a360613%Z.
Definition w_412 := 0xfffbb597%Z.
Definition w_413 := 0x85f58593%Z.
Definition w_426 := 0xfffc1597%Z.
Definition w_427 := 0x9e458593%Z.
Definition w_438 := 0xfffba597%Z.
Definition w_439 := 0x7f758893%Z.
Definition w_453 := 0xfffba517%Z.
Definition w_454 := 0x7bb50513%Z.
Definition w_467 := 0xfffba597%Z.
Definition w_468 := 0x78358713%Z.
Definition w_473 := 0xfffbd697%Z.
Definition w_474 := 0x71868693%Z.
Definition w_530 := 0x8b4ff0ef%Z.
Definition w_533 := 0xfffba597%Z.
Definition w_534 := 0x67b58593%Z.
Definition w_543 := 0xfffba597%Z.
Definition w_545 := 0x65358893%Z.
Definition w_627 := 0x1c9090ef%Z.
Definition w_639 := 0xf01fe0ef%Z.
Definition w_648 := 0xeddfe0ef%Z.
Definition w_655 := 0xec1fe0ef%Z.
Definition w_668 := 0x125090ef%Z.
Definition w_680 := 0xe5dfe0ef%Z.
Definition w_689 := 0xe39fe0ef%Z.
Definition w_701 := 0x0a1090ef%Z.
Definition w_713 := 0xdd9fe0ef%Z.
Definition w_722 := 0xdb5fe0ef%Z.
Definition w_729 := 0xd99fe0ef%Z.
Definition w_742 := 0x7fc090ef%Z.
Definition w_754 := 0xd35fe0ef%Z.
Definition w_762 := 0xd15fe0ef%Z.
Definition w_798 := 0x8c5fa0ef%Z.
Definition w_883 := 0xf70fa0ef%Z.
Definition w_907 := 0xbd5fa0ef%Z.
Definition hi_22 := (Z_to_bv 20 16).
Definition hi_281 := (Z_to_bv 20 1048513).
Definition hi_332 := (Z_to_bv 20 1048513).
Definition hi_360 := (Z_to_bv 20 1048507).
Definition hi_371 := (Z_to_bv 20 1048507).
Definition hi_378 := (Z_to_bv 20 1048509).
Definition hi_395 := (Z_to_bv 20 1048507).
Definition hi_412 := (Z_to_bv 20 1048507).
Definition hi_426 := (Z_to_bv 20 1048513).
Definition hi_438 := (Z_to_bv 20 1048506).
Definition hi_453 := (Z_to_bv 20 1048506).
Definition hi_467 := (Z_to_bv 20 1048506).
Definition hi_473 := (Z_to_bv 20 1048509).
Definition hi_533 := (Z_to_bv 20 1048506).
Definition hi_543 := (Z_to_bv 20 1048506).
Definition lo_25 := (Z_to_bv 12 852).
Definition lo_282 := (Z_to_bv 12 3216).
Definition lo_333 := (Z_to_bv 12 2684).
Definition lo_362 := (Z_to_bv 12 2351).
Definition lo_372 := (Z_to_bv 12 2307).
Definition lo_379 := (Z_to_bv 12 1903).
Definition lo_396 := (Z_to_bv 12 2211).
Definition lo_413 := (Z_to_bv 12 2143).
Definition lo_427 := (Z_to_bv 12 2532).
Definition lo_439 := (Z_to_bv 12 2039).
Definition lo_454 := (Z_to_bv 12 1979).
Definition lo_468 := (Z_to_bv 12 1923).
Definition lo_474 := (Z_to_bv 12 1816).
Definition lo_534 := (Z_to_bv 12 1659).
Definition lo_545 := (Z_to_bv 12 1619).
Definition joff_81 := (Z_to_bv 21 2095032).
Definition joff_381 := (Z_to_bv 21 2076488).
Definition joff_383 := (Z_to_bv 21 2076492).
Definition joff_389 := (Z_to_bv 21 41452).
Definition joff_530 := (Z_to_bv 21 2093236).
Definition joff_627 := (Z_to_bv 21 39368).
Definition joff_639 := (Z_to_bv 21 2092800).
Definition joff_648 := (Z_to_bv 21 2092764).
Definition joff_655 := (Z_to_bv 21 2092736).
Definition joff_668 := (Z_to_bv 21 39204).
Definition joff_680 := (Z_to_bv 21 2092636).
Definition joff_689 := (Z_to_bv 21 2092600).
Definition joff_701 := (Z_to_bv 21 39072).
Definition joff_713 := (Z_to_bv 21 2092504).
Definition joff_722 := (Z_to_bv 21 2092468).
Definition joff_729 := (Z_to_bv 21 2092440).
Definition joff_742 := (Z_to_bv 21 38908).
Definition joff_754 := (Z_to_bv 21 2092340).
Definition joff_762 := (Z_to_bv 21 2092308).
Definition joff_798 := (Z_to_bv 21 2074820).
Definition joff_883 := (Z_to_bv 21 2074480).
Definition joff_907 := (Z_to_bv 21 2075604).
Definition G_102fd := 0x104f3%Z.
Definition G_10741 := 0x1337b%Z.
Definition G_107e0 := 0x134a0%Z.
Definition G_11778 := 0x165d0%Z.
Definition G_11858 := 0x166b0%Z.
Definition G_118c0 := 0x16718%Z.
Definition got_ssp := got_ssp.
Definition GLOBALS_TOP := GLOBALS_TOP.
Definition STATIC_SPLIT := STATIC_SPLIT.
Definition ssp_guard := ssp_guard.
Definition e_194bc := 0x50b60%Z.
Definition e_194c8 := 0x50b6c%Z.
Definition e_197bc := 0x51024%Z.
Definition e_fwritex := 0x54f20%Z.
Definition e_memset := 0x5f9b8%Z.
Definition e_2596c := 0x5fe24%Z.
Lemma CODE : CodeAt.code_at rsegs 0x55624 (Q8l1.Mq1.printf_core_code 0x00010517%Z 0x35453603%Z 0xfb8ff0ef%Z 0xfffc1697%Z 0xc9068693%Z 0xfffc1597%Z 0xa7c58593%Z 0xfffbb597%Z 0x92f58593%Z 0xfffbb517%Z 0x90350513%Z 0xfffbd517%Z 0x76f50b93%Z 0xf49fa0ef%Z 0xf4dfa0ef%Z 0x1ec0a0ef%Z 0xfffbb617%Z 0x8a360613%Z 0xfffbb597%Z 0x85f58593%Z 0xfffc1597%Z 0x9e458593%Z 0xfffba597%Z 0x7f758893%Z 0xfffba517%Z 0x7bb50513%Z 0xfffba597%Z 0x78358713%Z 0xfffbd697%Z 0x71868693%Z 0x8b4ff0ef%Z 0xfffba597%Z 0x67b58593%Z 0xfffba597%Z 0x65358893%Z 0x1c9090ef%Z 0xf01fe0ef%Z 0xeddfe0ef%Z 0xec1fe0ef%Z 0x125090ef%Z 0xe5dfe0ef%Z 0xe39fe0ef%Z 0x0a1090ef%Z 0xdd9fe0ef%Z 0xdb5fe0ef%Z 0xd99fe0ef%Z 0x7fc090ef%Z 0xd35fe0ef%Z 0xd15fe0ef%Z 0x8c5fa0ef%Z 0xf70fa0ef%Z 0xbd5fa0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x55624 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x55624 /\ 0x55624 + 3632 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Section Sink.
Context {St : Type}.
Variables (Fp B BS : Z).
Variable SINK : mem -> St -> Prop.
Variable TOPOK : Z -> Prop.
Variable OUT : list Z -> M St unit.
Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

Definition SR : list (Z * Z) := [(Fp, Fp + 232); (B, B + BS)].
Lemma gw_eq_SR : @SR = ltac:(GwInst.gw_term (@Q8l1.Mq1.SR) (@SR)). Proof. unfold SR, Q8l1.Mq1.SR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_SR : gw_eqs.

Definition sink_frame_stmt : Prop :=
forall (W : list (Z * Z)) (m m' : mem) (st : St),
SINK m st -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv) W ->
Forall (fun iv => snd iv <= B \/ B + BS <= fst iv) W ->
SINK m' st.
Lemma gw_eq_sink_frame_stmt : @sink_frame_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.sink_frame_stmt rsegs) (@sink_frame_stmt)). Proof. unfold sink_frame_stmt, Q8l1.Mq1.sink_frame_stmt; ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_sink_frame_stmt : gw_eqs.

Definition sink_flags_stmt : Prop :=
forall m st, SINK m st -> exists fl : byte, rw_cells rsegs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0.
Lemma gw_eq_sink_flags_stmt : @sink_flags_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.sink_flags_stmt rsegs) (@sink_flags_stmt)). Proof. unfold sink_flags_stmt, Q8l1.Mq1.sink_flags_stmt; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_sink_flags_stmt : gw_eqs.

Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.
Lemma gw_eq_topok_stmt : @topok_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.topok_stmt) (@topok_stmt)). Proof. unfold topok_stmt, Q8l1.Mq1.topok_stmt; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_topok_stmt : gw_eqs.

Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at rsegs m' S (zb bs).
Lemma gw_eq_out_post : @out_post = ltac:(GwInst.gw_term (@Q8l1.Mq1.out_post rsegs got_ssp ssp_guard) (@out_post)). Proof. unfold out_post, Q8l1.Mq1.out_post; rewrite ?gw_eq_SR; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_out_post : gw_eqs.

Definition out_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
SINK m st ->
bytes_at rsegs m (bv_unsigned a0) (zb bs) ->
Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^31 ->
a1 = Z_to_bv 64 (zlength bs) ->
a2 = Z_to_bv 64 Fp ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv rsegs m ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
(bv_unsigned a0 + zlength bs <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
(bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
implM rsegs (OUT bs) st
(out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54f20) fc None m (seg_rom rsegs)).
Lemma gw_eq_out_stmt : @out_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.out_stmt rsegs got_ssp GLOBALS_TOP ssp_guard 0x54f20%Z) (@out_stmt)). Proof. unfold out_stmt, Q8l1.Mq1.out_stmt; rewrite ?gw_eq_OUT_DEPTH, ?gw_eq_out_post; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_out_stmt : gw_eqs.

Definition fpcall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary.
Lemma gw_eq_fpcall_post : @fpcall_post = ltac:(GwInst.gw_term (@Q8l1.Mq1.fpcall_post rsegs got_ssp ssp_guard) (@fpcall_post)). Proof. unfold fpcall_post, Q8l1.Mq1.fpcall_post; rewrite ?gw_eq_SR; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_fpcall_post : gw_eqs.

Definition fpcall_stmt (c : Z * Z * Z * Z * Z) : Prop :=
let '(y, w, p, fl, t) := c in
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
SINK m st ->
y = bv_unsigned a1 + 2^64 * bv_unsigned a2 ->
a0 = Z_to_bv 64 Fp -> a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t ->
bv_unsigned a7 <> 5 ->
(-2^31 <= w <= 1) -> (-2^31 <= p < 2^20) -> (0 <= fl < 2^32) -> (0 <= t < 256) -> Z.lor t 32 <> 97 ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary ->
mem_inv rsegs m -> frm0 fc ->
(Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
implM rsegs (OUTFP y w p fl t) st
(fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5665c) fc None m (seg_rom rsegs)).
Lemma gw_eq_fpcall_stmt : @fpcall_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.fpcall_stmt rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@fpcall_stmt)). Proof. unfold fpcall_stmt, Q8l1.Mq1.fpcall_stmt; rewrite ?gw_eq_fpcall_post; ltac2:(GwEq.gw_rw [[@gw_eq_FMT_FP_DEPTH__3; @gw_eq_FMT_FP_DEPTH__2; @gw_eq_FMT_FP_DEPTH]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_fpcall_stmt : gw_eqs.

Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
match a with
| PA_s s => exists slack : list byte,
bytes_at rsegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
/\ 0 < bv_unsigned slot
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned slot)
/\ (bv_unsigned slot + zlength s + 1 + zlength slack <= ap \/ ap + 8 <= bv_unsigned slot)
| PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
| PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
| PA_g d => bv_unsigned slot = d
| PA_li i => -2^63 <= i < 2^63 /\ bv_unsigned slot = i mod 2^64
| PA_lu u => 0 <= u < 2^64 /\ bv_unsigned slot = u
end.
Lemma gw_eq_arg_ok : @arg_ok = ltac:(GwInst.gw_term (@Q8l1.Mq1.arg_ok rsegs) (@arg_ok)). Proof. unfold arg_ok, Q8l1.Mq1.arg_ok; ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_arg_ok : gw_eqs.
Fixpoint args_ok (m : mem) (lo sp ap : Z) (slots : list word) (args : list parg) : Prop :=
match args with
| [] => True
| a :: args' => match slots with
| [] => False
| w :: slots' => arg_ok m lo sp ap w a /\ args_ok m lo sp ap slots' args'
end
end.
Lemma gw_eq_args_ok : @args_ok = ltac:(GwInst.gw_term (@Q8l1.Mq1.args_ok rsegs) (@args_ok)). Proof. unfold args_ok, Q8l1.Mq1.args_ok; rewrite ?gw_eq_arg_ok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_args_ok : gw_eqs.

Definition printf_core_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(AP lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch ((lo, bv_unsigned sp) :: (AP, AP + 8) :: SR) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ rw_cells rsegs m' AP [C8 apv]
/\ (0 <= r <= INT_MAX).
Lemma gw_eq_printf_core_post : @printf_core_post = ltac:(GwInst.gw_term (@Q8l1.Mq1.printf_core_post rsegs got_ssp ssp_guard) (@printf_core_post)). Proof. unfold printf_core_post, Q8l1.Mq1.printf_core_post; rewrite ?gw_eq_SR; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_printf_core_post : gw_eqs.

Definition printf_core_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
(fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
SINK m st ->
bytes_at rsegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
a0 = Z_to_bv 64 Fp ->
rw_cells rsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
va_area m VA slots -> 0 <= i -> args_ok m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
Forall fpcall_stmt (fp_calls (length fmt) fmt args) ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->

(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> (0 <= BS) ->
((416216 <= Fp /\ Fp + 232 <= 622192) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
((622200 <= B /\ B + BS <= lo) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
implM rsegs (printf_model OUT OUTFP fmt args) st
(printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x55624) fc None m (seg_rom rsegs)).
Lemma gw_eq_printf_core_stmt : @printf_core_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.printf_core_stmt rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@printf_core_stmt)). Proof. unfold printf_core_stmt, Q8l1.Mq1.printf_core_stmt; rewrite ?gw_eq_PC_DEPTH, ?gw_eq_fpcall_stmt, ?gw_eq_args_ok, ?gw_eq_printf_core_post; ltac2:(GwEq.gw_rw [[@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_printf_core_stmt : gw_eqs.
End Sink.
Lemma gw_eq_SR__2 : @SR = ltac:(GwInst.gw_term (@Q8l1.Mq1.SR) (@SR)). Proof. unfold SR, Q8l1.Mq1.SR; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SR__2 : gw_eqs.
Lemma gw_eq_sink_frame_stmt__2 : @sink_frame_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.sink_frame_stmt rsegs) (@sink_frame_stmt)). Proof. unfold sink_frame_stmt, Q8l1.Mq1.sink_frame_stmt; ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sink_frame_stmt__2 : gw_eqs.
Lemma gw_eq_sink_flags_stmt__2 : @sink_flags_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.sink_flags_stmt rsegs) (@sink_flags_stmt)). Proof. unfold sink_flags_stmt, Q8l1.Mq1.sink_flags_stmt; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sink_flags_stmt__2 : gw_eqs.
Lemma gw_eq_topok_stmt__2 : @topok_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.topok_stmt) (@topok_stmt)). Proof. unfold topok_stmt, Q8l1.Mq1.topok_stmt; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_topok_stmt__2 : gw_eqs.
Lemma gw_eq_out_post__2 : @out_post = ltac:(GwInst.gw_term (@Q8l1.Mq1.out_post rsegs got_ssp ssp_guard) (@out_post)). Proof. unfold out_post, Q8l1.Mq1.out_post; rewrite ?gw_eq_SR__2; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_out_post__2 : gw_eqs.
Lemma gw_eq_out_stmt__2 : @out_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.out_stmt rsegs got_ssp GLOBALS_TOP ssp_guard 0x54f20%Z) (@out_stmt)). Proof. unfold out_stmt, Q8l1.Mq1.out_stmt; rewrite ?gw_eq_OUT_DEPTH, ?gw_eq_out_post__2; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_out_stmt__2 : gw_eqs.
Lemma gw_eq_fpcall_post__2 : @fpcall_post = ltac:(GwInst.gw_term (@Q8l1.Mq1.fpcall_post rsegs got_ssp ssp_guard) (@fpcall_post)). Proof. unfold fpcall_post, Q8l1.Mq1.fpcall_post; rewrite ?gw_eq_SR__2; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fpcall_post__2 : gw_eqs.
Lemma gw_eq_fpcall_stmt__2 : @fpcall_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.fpcall_stmt rsegs 0x55624 got_ssp GLOBALS_TOP ssp_guard) (@fpcall_stmt)). Proof. unfold fpcall_stmt, Q8l1.Mq1.fpcall_stmt; rewrite ?gw_eq_fpcall_post__2; ltac2:(GwEq.gw_rw [[@gw_eq_FMT_FP_DEPTH__3; @gw_eq_FMT_FP_DEPTH__2; @gw_eq_FMT_FP_DEPTH]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fpcall_stmt__2 : gw_eqs.
Lemma gw_eq_arg_ok__2 : @arg_ok = ltac:(GwInst.gw_term (@Q8l1.Mq1.arg_ok rsegs) (@arg_ok)). Proof. unfold arg_ok, Q8l1.Mq1.arg_ok; ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_arg_ok__2 : gw_eqs.
Lemma gw_eq_args_ok__2 : @args_ok = ltac:(GwInst.gw_term (@Q8l1.Mq1.args_ok rsegs) (@args_ok)). Proof. unfold args_ok, Q8l1.Mq1.args_ok; rewrite ?gw_eq_arg_ok__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_args_ok__2 : gw_eqs.
Lemma gw_eq_printf_core_post__2 : @printf_core_post = ltac:(GwInst.gw_term (@Q8l1.Mq1.printf_core_post rsegs got_ssp ssp_guard) (@printf_core_post)). Proof. unfold printf_core_post, Q8l1.Mq1.printf_core_post; rewrite ?gw_eq_SR__2; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_printf_core_post__2 : gw_eqs.
Lemma gw_eq_printf_core_stmt__2 : @printf_core_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.printf_core_stmt rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@printf_core_stmt)). Proof. unfold printf_core_stmt, Q8l1.Mq1.printf_core_stmt; rewrite ?gw_eq_PC_DEPTH, ?gw_eq_fpcall_stmt__2, ?gw_eq_args_ok__2, ?gw_eq_printf_core_post__2; ltac2:(GwEq.gw_rw [[@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_printf_core_stmt__2 : gw_eqs.

Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary.
Lemma gw_eq_printf_core1_post : @printf_core1_post = ltac:(GwInst.gw_term (@Q8l1.Mq1.printf_core1_post rsegs got_ssp ssp_guard) (@printf_core1_post)). Proof. unfold printf_core1_post, Q8l1.Mq1.printf_core1_post; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_printf_core1_post : gw_eqs.

Definition printf_core1_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
bytes_at rsegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
pass1_ok fmt = true ->
a0 = Z_to_bv 64 0 ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m ->
(bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) ->
(bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
evt rsegs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x55624) fc None m (seg_rom rsegs)).
Lemma gw_eq_printf_core1_stmt : @printf_core1_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq1.printf_core1_stmt rsegs 0x55624 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@printf_core1_stmt)). Proof. unfold printf_core1_stmt, Q8l1.Mq1.printf_core1_stmt; rewrite ?gw_eq_PC_DEPTH, ?gw_eq_printf_core1_post; ltac2:(GwEq.gw_rw [[@gw_eq_pass1_ok__3; @gw_eq_pass1_ok__2; @gw_eq_pass1_ok]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_printf_core1_stmt : gw_eqs.

Section SnSink.

Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
Definition SN_CAP : Z := 80.
Lemma gw_eq_SN_CAP : @SN_CAP = ltac:(GwInst.gw_term (@Q8l1.Mq1.SN_CAP) (@SN_CAP)). Proof. unfold SN_CAP, Q8l1.Mq1.SN_CAP; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_SN_CAP : gw_eqs.

Definition SINK_sn (m : mem) (o : list Z) : Prop :=
exists junk : list byte,
wfile m Fp fl0 j1 j2 lbfw B (zb o) junk
/\ rw_cells rsegs m (Fp + 148) frest /\ Z.of_nat (cells_size frest) = 84
/\ zlength o + zlength junk = SN_CAP
/\ (B + SN_CAP <= Fp \/ Fp + 232 <= B)
/\ TOP <= Fp /\ TOP <= B.
Lemma gw_eq_SINK_sn : @SINK_sn = ltac:(GwInst.gw_term (@Q8l1.Mq1.SINK_sn rsegs) (@SINK_sn)). Proof. unfold SINK_sn, Q8l1.Mq1.SINK_sn; rewrite ?gw_eq_SN_CAP; ltac2:(GwEq.gw_rw [[@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_SINK_sn : gw_eqs.
Definition TOPOK_sn (sp : Z) : Prop := sp <= TOP.
Lemma gw_eq_TOPOK_sn : @TOPOK_sn = ltac:(GwInst.gw_term (@Q8l1.Mq1.TOPOK_sn) (@TOPOK_sn)). Proof. unfold TOPOK_sn, Q8l1.Mq1.TOPOK_sn; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_TOPOK_sn : gw_eqs.

Definition OUT_sn (bs : list Z) : M (list Z) unit :=
o <- mget ;; if zlength o + zlength bs <=? SN_CAP then mput (o ++ bs) else munr.
Lemma gw_eq_OUT_sn : @OUT_sn = ltac:(GwInst.gw_term (@Q8l1.Mq1.OUT_sn) (@OUT_sn)). Proof. unfold OUT_sn, Q8l1.Mq1.OUT_sn; rewrite ?gw_eq_SN_CAP; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_OUT_sn : gw_eqs.

Definition OUTFP_sn (y w p fl t : Z) : M (list Z) Z :=
o <- mget ;;
match fmt_fp o y w p fl t with
| Some (o1, r) => if zlength o1 <=? SN_CAP then (mput o1 ;;; mret r) else munr
| None => munr
end.
Lemma gw_eq_OUTFP_sn : @OUTFP_sn = ltac:(GwInst.gw_term (@Q8l1.Mq1.OUTFP_sn) (@OUTFP_sn)). Proof. unfold OUTFP_sn, Q8l1.Mq1.OUTFP_sn; rewrite ?gw_eq_SN_CAP; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_OUTFP_sn : gw_eqs.
End SnSink.
Lemma gw_eq_SN_CAP__2 : @SN_CAP = ltac:(GwInst.gw_term (@Q8l1.Mq1.SN_CAP) (@SN_CAP)). Proof. unfold SN_CAP, Q8l1.Mq1.SN_CAP; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SN_CAP__2 : gw_eqs.
Lemma gw_eq_SINK_sn__2 : @SINK_sn = ltac:(GwInst.gw_term (@Q8l1.Mq1.SINK_sn rsegs) (@SINK_sn)). Proof. unfold SINK_sn, Q8l1.Mq1.SINK_sn; rewrite ?gw_eq_SN_CAP__2; ltac2:(GwEq.gw_rw [[@gw_eq_wfile__3; @gw_eq_wfile__2; @gw_eq_wfile]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SINK_sn__2 : gw_eqs.
Lemma gw_eq_TOPOK_sn__2 : @TOPOK_sn = ltac:(GwInst.gw_term (@Q8l1.Mq1.TOPOK_sn) (@TOPOK_sn)). Proof. unfold TOPOK_sn, Q8l1.Mq1.TOPOK_sn; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_TOPOK_sn__2 : gw_eqs.
Lemma gw_eq_OUT_sn__2 : @OUT_sn = ltac:(GwInst.gw_term (@Q8l1.Mq1.OUT_sn) (@OUT_sn)). Proof. unfold OUT_sn, Q8l1.Mq1.OUT_sn; rewrite ?gw_eq_SN_CAP__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_OUT_sn__2 : gw_eqs.
Lemma gw_eq_OUTFP_sn__2 : @OUTFP_sn = ltac:(GwInst.gw_term (@Q8l1.Mq1.OUTFP_sn) (@OUTFP_sn)). Proof. unfold OUTFP_sn, Q8l1.Mq1.OUTFP_sn; rewrite ?gw_eq_SN_CAP__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_OUTFP_sn__2 : gw_eqs.

Definition TOPOK_none (sp : Z) : Prop := True.
Lemma gw_eq_TOPOK_none : @TOPOK_none = ltac:(GwInst.gw_term (@Q8l1.Mq1.TOPOK_none) (@TOPOK_none)). Proof. unfold TOPOK_none, Q8l1.Mq1.TOPOK_none; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_TOPOK_none : gw_eqs.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7zy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7zy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UD4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UD4E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfJh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfJh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULch.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis HGOT : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m 0x658d8 (le8 (wz JHEX_SLOT)).

Variables (sp gp : word) (m0 : word -> option byte) (md0 : Model) (LB : list blk) (pb lo : Z).
Let usp := bv_unsigned sp.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis HT : usp <= hi_top S4L HIx.
Notation ser_memx := (ser_mem HIx sp m0 md0 LB pb lo).

#[using="MEMMOVE HEXP HT63 HGOT LO HT"] Lemma ser_escape :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(FA : Z) (FR : list cell) (Sa n : Z) (src : list byte),
ser_memx FA FR m md ->
bytes_at rsegs m Sa src -> Z.of_nat (length src) = n -> 0 <= n < 2^31 -> 0 <= Sa -> Sa + n < 2^64 ->
src_cls LB n FA Sa src ->
lo <= FA - 192 - 8320 -> FA mod 16 = 0 -> FA <= usp -> 0 <= FA ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc -> Z.land (bv_unsigned a3) 16 = 0 ->
(forall m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
ser_memx FA FR m' md' -> fsaved F F' -> frm0 fc' -> bytes_at rsegs m' Sa src ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (wz FA) gp (wz TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom rsegs)) md') T) ->
realizes rsegs (mkCfg (MS (mkR (wz ret) (wz FA) x3 (wz TP) t0 t1 t2 x8 x9 (wz pb) (wz Sa) (wz n) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz ESCAPE) fcc None m (seg_rom rsegs)) md) T.
Proof.
intros until src. intros INV SB SBL Hn HSa HSan SBC LOS FAA FAU FA0 -> Hret Hret2 FS FRM FL K.
destruct INV as (A & buf & cap & bpos & content & errv & HP & PB & FRc & ERR & ST & HPR & VM).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
assert (U2 : bv_unsigned (wz FA) = FA) by (apply unsigned_lit; unfold usp in *; lia).
eapply (json_escape_str_cps HIx MEMMOVE HEXP HT63 HGOT) with (A := A) (LB := LB) (buf := buf) (bpos := bpos) (cap := cap)
(lo := lo) (content := content) (src := src) (errv := errv);
rewrite ?U2.
- exact HP.
- exact PB.
- exact SB.
- exact SBL.
- exact SBC.
- exact HSa.
- exact HSan.
- exact Hn.
- exact ST.
- exact LO.
- lia.
- exact FAA.
- unfold usp in *. lia.
- unfold ERRNO in ERR. exact ERR.
- reflexivity.
- rewrite unsigned_lit by lia. exact Hret2.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- exact FL.
- intros ms' md' POST.
destruct POST as (m' & A' & r & buf' & cap' & bpos' & content' & errv' & RS & VM' & ST' & HPR' & ERR' & HP' & PB' & SB').
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F' & fc' & -> & FS' & FR').
rewrite U2 in ST', HPR'.
replace (ret_pc (wz ret)) with (wz ret) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
apply K; [| eapply fsaved_trans; [exact FS | exact FS'] | exact (FR' FRM) | exact SB'].
exists A', buf', cap', bpos', content', errv'.
split; [exact HP'|]. split; [exact PB'|]. split; [| split; [unfold ERRNO; exact ERR' | split; [exact ST' | split]]].
+ eapply (heap_pres_rw_cells S4L); [exact HPR' | exact FRc | left; lia].
+ eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPR' | unfold usp in *; lia | auto]].
+ eapply model_vm_only_trans; [exact VM | exact VM'].
Qed.
End Ser.

End RC__1.

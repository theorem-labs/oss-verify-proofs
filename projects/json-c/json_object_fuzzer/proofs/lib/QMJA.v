(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv6q. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QD4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QD4E.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qio9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qio9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHXC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHXC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfe5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfe5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QId5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QId5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quoa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLch. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwKH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwKH.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ro_lit2 : forall a b1 b2,
In (a, b1, b2) [(0x129a3, 92, 98); (0x12c51, 92, 116); (0x1300c, 92, 110); (0x126e8, 92, 102);
(0x11525, 92, 114); (0x11ab6, 92, 34); (0x110e9, 92, 92); (0x10ebf, 92, 47)] ->
ro_bytes rsegs a [Z_to_bv 8 b1; Z_to_bv 8 b2].
Proof.
intros a b1 b2 H. cbn in H.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]; injection H as <- <- <-;
(cbn [ro_bytes]; split; [| split; [| exact I]]; split; vm_compute; reflexivity).
Qed.

Section Esc.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (pb Sa n lo : Z) (src : list byte).
Let usp := bv_unsigned sp.
Hypothesis SRCL : Z.of_nat (length src) = n.
Hypothesis SCL : src_cls LB n usp Sa src.
Hypothesis Hn : 0 < n < 2^31.
Hypothesis HSa : 0 <= Sa /\ Sa + n < 2^64.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - 192 - 8320.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.

Notation esc_memx := (esc_mem HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB pb Sa lo src).
Notation esc_postx := (esc_post HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb Sa lo src).
Notation st_loopx := (st_loop sp gp pb Sa n).
Notation loopKx := (loopK HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB pb Sa n lo src).
Let esc_appendx := esc_append HIx MEMMOVE ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB pb Sa n lo src SRCL SCL HSa LO LOS SPA HT.

Definition st_c (pc : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (cv : Z) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (pos : Z) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (usp + -192)) gp (wz 0x75e70) t0 t1 t2 (wz pb) (wz n) a0 a1 a2 a3 a4 a5 a6 a7
(wz Sa) (wz 0x1392c) (wz pos) (wz pos) (wz 0) (wz 47) (wz cv) (wz 0x129a3) (wz 140754668238592) (wz 26) t3 t4 t5 t6)
F' (wz pc) fc' None m (seg_rom rsegs).

Ltac prep INV HP FRc :=
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR; unfold usp in *; unfold_consts;
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK;
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI;
unfold escF in FRc.

#[using="MEMMOVE SRCL SCL Hn HSa LO LOS SPA HT esc_appendx"] Lemma esc_special_tail :
forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md pos (cv : Z) T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= pos < n ->
In cv [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_c 0x25ce4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 cv F' fc' m pos) md) T.
Proof.
intros until T. intros INV FS FR Hpos Hcv IH K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
unfold st_c. prep INV HP FRc.
cbn in Hcv.
destruct Hcv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
all: apply rz_evt; [exact MOK|].
all: symb_run 30%nat [MEMAPPEND] (@nil bool).
all: apply evt_RZ_done.
all: lazymatch goal with |- realizes _ (mkCfg (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?adr) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _) _ =>
eapply esc_appendx with (b := adr);
only 7: (right; apply ro_lit2; cbn; repeat (first [ left; reflexivity | right ]));
[ exact INV0
| apply ro_bytes_at; [exact MI | lia | cbn; lia | apply ro_lit2; cbn; repeat (first [ left; reflexivity | right ]) ]
| reflexivity | lia | lia | lia
| reflexivity | lia | reflexivity | exact FS | exact FR | ]
end.
all: intros m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _;
pose proof INV' as INV1;
destruct INV' as (A' & buf' & cap' & bpos' & content' & errv' & j1' & j2' & sbf' & HP' & PB' & FRc' & SRC' & ERR' & ST' & HPR' & VM');
pose proof (heap_model_ok _ _ _ _ _ _ HP') as MOK';
pose proof (heap_mem_inv _ _ _ _ _ _ HP') as MI'; cbn [hl_segs S4L] in MI'; unfold escF in FRc';
apply rz_evt; [exact MOK'|].
all: symb_run 4%nat [0x25ca4]%Z (@nil bool).
all: apply evt_RZ_done; eapply esc_join98; try eassumption; lia.
Qed.

#[using="MEMMOVE SRCL SCL Hn HSa LO LOS SPA HT esc_appendx"] Lemma esc_special_c4 :
forall x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md pos start (cv : Z) T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= start <= pos -> pos < n ->
In cv [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_c 0x25cd0 x1 t0 t1 t2 (wz start) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 cv F' fc' m pos) md) T.
Proof.
intros until T. intros INV FS FR Hst Hpos Hcv IH K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
unfold st_c. prep INV HP FRc.
apply rz_evt; [exact MOK|].
destruct (Z.lt_ge_cases start pos) as [LT|GE].
-
symb_run 8%nat [MEMAPPEND] [false].
replace (start + Sa) with (Sa + Z.of_nat (Z.to_nat start)) by lia.
replace (pos - start) with (Z.of_nat (Z.to_nat (pos - start))) by lia.
apply evt_RZ_done.
eapply esc_appendx with (sb := firstn (Z.to_nat (pos - start)) (skipn (Z.to_nat start) src));
[ exact INV0 | | | lia | lia | lia | | reflexivity | lia | reflexivity | exact FS | exact FR | ].
+ apply bytes_at_sub; [exact SRC | lia].
+ rewrite length_firstn, length_skipn. lia.
+ apply (src_cls_sub LB n usp Sa src); [exact SCL | exact SRCL | lia | lia].
+ intros m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
eapply esc_special_tail; eassumption || lia || exact Hcv.
- symb_run 8%nat [0x25ce4]%Z [true].
apply evt_RZ_done. eapply esc_special_tail; eassumption || lia || exact Hcv.
Qed.

#[using="MEMMOVE usp SRCL SCL Hn HSa LO LOS SPA HT esc_appendx"] Lemma esc_iter_special :
forall x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 F' fc' m md pos start (c : byte) T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= start <= pos -> pos < n ->
nth_error src (Z.to_nat pos) = Some c ->
In (bv_unsigned c) [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_loopx 0x25cb0 x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 F' fc' m pos pos start) md) T.
Proof.
intros until T. intros INV FS FR Hst Hpos Hc Hcv IH K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
unfold st_loop. prep INV HP FRc.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
apply rz_evt; [exact MOK|].

symb_run 2%nat [0x25cb8]%Z (@nil bool) extra [Z_to_bv 64 (bv_unsigned c)].

cbn in Hcv.
destruct Hcv as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; rewrite <- E.
all: symb_run 12%nat [0x25cd0]%Z (@nil bool).
all: apply evt_RZ_done; eapply esc_special_c4; try eassumption; try lia; cbn; tauto.
Qed.
End Esc.

End RC__1.

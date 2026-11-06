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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwKH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMJA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMJA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTea.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTea.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Esc.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Hypothesis HT63 : hi_top S4L HIx < 2^63.

Hypothesis HGOT : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m 0x63d90 (le8 (wz JHEX_SLOT)).

Section Loop.
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

#[using="MEMMOVE HEXP HT63 usp SRCL SCL Hn HSa LO LOS SPA HT"] Lemma esc_iter :
forall x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 F' fc' m md pos start (c : byte) T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= start <= pos -> pos < n ->
nth_error src (Z.to_nat pos) = Some c ->
loopKx T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_loopx 0x25cb0 x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 F' fc' m pos pos start) md) T.
Proof.
intros until T. intros INV FS FR Hst Hpos Hc IH K.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
destruct (in_dec Z.eq_dec (bv_unsigned c) [8; 9; 10; 12; 13; 34; 92; 47]) as [SP|NSP].
- eapply (esc_iter_special HIx MEMMOVE); eassumption.
- destruct (Z.lt_ge_cases (bv_unsigned c) 32) as [LT|GE].
+ eapply (esc_iter_ctrl HIx MEMMOVE); try eassumption. intros Hin. apply NSP. cbn in Hin |- *. tauto.
+ eapply (esc_iter_regular HIx MEMMOVE); try eassumption; cbn in NSP; lia.
Qed.

#[using="MEMMOVE HEXP HT63 usp SRCL SCL Hn HSa LO LOS SPA HT"] Lemma loopK_all : forall T k,
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
loopKx T (Z.of_nat k).
Proof.
intros T k K. unfold loopK. induction k as [|k IHk]; intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 F' fc' m md pos start INV FS FR Hst Hpos Hb.
- exfalso. cbn in Hb. lia.
- destruct (nth_error src (Z.to_nat pos)) as [c|] eqn:Hc; [| apply nth_error_None in Hc; lia].
eapply esc_iter; try eassumption.
unfold loopK. intros. eapply IHk; try eassumption. lia.
Qed.
End Loop.

#[using="MEMMOVE HEXP HT63 HGOT"] Theorem json_escape_str_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (pb buf bpos cap Sa n lo : Z) (content src : list byte) (errv : word),
HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m md ->
pbuf_core rsegs m pb buf bpos cap content ->
bytes_at rsegs m Sa src -> Z.of_nat (length src) = n -> src_cls LB n (bv_unsigned sp) Sa src ->
0 <= Sa -> Sa + n < 2^64 -> 0 <= n < 2^31 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 192 - 8320 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
tp = wz 0x75e70 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz pb -> a1 = wz Sa -> a2 = wz n -> Z.land (bv_unsigned a3) 16 = 0 ->
(forall ms' md', esc_post HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb Sa lo src ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz ESC_ENTRY) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP PB SRC SRCL SCL HSa0 HSan Hn ST LO LOS SPA HT ERR TP RA FRM A0 A1 A2 FL K.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
change (0x75e70 - 164) with 482764 in ERR.
pose proof (HGOT _ _ _ _ HP) as GOT. unfold JHEX_SLOT in GOT.
subst a0 a1 a2 tp. unfold ESC_ENTRY.
apply rz_evt; [exact MOK|].
destruct (Z.eq_dec n 0) as [N0|N1].
-
rewrite N0. symb_run 2%nat (@nil Z) (@nil bool).
step.
apply evt_RZ_done. apply K. unfold esc_post.
exists m, A. eexists. exists buf, cap, bpos, content, errv.
split; [apply ret_statew_same |].
split; [apply model_vm_only_refl|]. split; [exact ST|]. split; [apply heap_pres_refl|].
split; [exact ERR|]. split; [exact HP|]. split; [exact PB | exact SRC].
-
assert (SRCk : True -> bytes_at rsegs m Sa src) by (intros _; exact SRC). clear SRC.
pose proof (munch_refl [(bv_unsigned sp + -192, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi.
carve_frame 192%nat ST.
symb_run 80%nat [0x25cb0]%Z [false].
rewrite FL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.

lazymatch type of FR with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?rest) =>
change (rw_cells rsegs m1 A ([c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ ([c11] ++ rest))) in FR end.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FR as [FRa FRbc]. cbn [cells_size csize Nat.add] in FRbc. change (Z.of_nat 80) with 80 in FRbc.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRbc as [FRb FRd]. cbn [cells_size csize Nat.add] in FRd. change (Z.of_nat 8) with 8 in FRd.
destruct (rw_cells_CB_cut rsegs _ _ _ _ 1%nat FRb ltac:(lia)) as [FRb1 FRb7]. clear FRb.
assert (FRX : exists j1 j2 sb, rw_cells rsegs m1 (bv_unsigned sp + -192) (escF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j1 j2 sb)).
{ do 3 eexists. unfold escF.
lazymatch goal with |- rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?rest) =>
change (rw_cells rsegs m1 A ([c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ ([c11] ++ ([c12] ++ rest)))) end.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact FRa|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 80) with 80.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact FRb1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact FRb7|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 7) with 7.
replace (bv_unsigned sp + -192 + 80 + 1 + 7) with (bv_unsigned sp + -192 + 80 + 8) by lia. exact FRd. }
destruct FRX as (j1 & j2 & sb & FRX).
assert (HP1 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (SRC1 : bytes_at rsegs m1 Sa src).
{ destruct (src_cls_where _ _ _ _ _ SCL SRCL ltac:(lia) ltac:(lia) HIx _ _ _ _ HP ltac:(intros b Hb; right; right; exact Hb)) as [Z0|W1]; [lia|].
eapply (bytes_at_transport rsegs); [exact (SRCk I) | exact MU |]. cbn. rewrite SRCL. unfold_consts. slia. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
assert (INV1 : esc_mem HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB pb Sa lo src m1 md).
{ exists A, buf, cap, bpos, content, errv, j1, j2, sb.
split; [exact HP1|]. split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS|exact PBUF]|]. split; [exact FRX|]. split; [exact SRC1|]. split; [exact ERR|].
split; [exact ST|]. split; [exact HPR1 | apply model_vm_only_refl]. }
apply evt_RZ_done.
eapply (loopK_all ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB pb Sa n lo src) with (k := Z.to_nat n);
first [ exact INV1 | exact SCL | exact K | apply fsaved_refl | exact FRM | lia | assumption ].
Qed.
End Esc.

End RC__1.

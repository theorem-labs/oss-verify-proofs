(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7 QJjn QKQo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI Uu4M. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj QKdB QRUw QSL3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3jZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw QYIF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrIB Udgq Uzop. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Qfw3 Qc3B QlEo Lib.GwApply QsjA QZAi Ql2m QqdR QYTG QiVh UjdK U4l4 UxrO Um2h UDgQ UzOj QSCw Qbz7 UTru U3Uw U0Ae UTa4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3.Mq2 QWxq.Mq0 Qc3B QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0.

Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import QiVh.Mq0 QRjH.Mq3.
Import UjdK U4l4 UxrO Um2h UDgQ UzOj.
Import QSCw Qbz7.
Import UTru U3Uw.Mq0 U0Ae UTa4.
Import UEQM.
Import Qfw3.Mq1.
Import QCcH.
Import Uzop.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

Import Q6q3.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= rc_lia_prep; lia3. Local Ltac mkr__lia_4 := rc_lia_prep; lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section StaticRW.
Variable segs : list Segment.

#[using="Type"] Lemma image_bytes_rom : forall n A bs i, image_bytes segs A n = Some bs -> (i < n)%nat ->
seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
induction n as [|n IH]; intros A bs i H Hi; [lia|].
cbn [image_bytes] in H. destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E'; [|discriminate]. injection H as <-.
destruct i as [|i].
- cbn [nth_error]. rewrite <- E. f_equal. unfold wa. f_equal. lia.
- cbn [nth_error]. rewrite <- (IH (A + 1) bs' i E' ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Definition shown (m : word -> option byte) (bs : list byte) (A : Z) (i : nat) : byte :=
match m (wa (A + Z.of_nat i)) with Some b => b | None => nth i bs (Z_to_bv 8 0) end.

#[using="Type"] Lemma bss_rw_cells : forall m A n bs,
image_bytes segs A n = Some bs -> wseg_ok segs (Z_to_bv 64 A) n = true ->
0 <= A -> A + Z.of_nat n <= 2^64 ->
rw_cells segs m A [CB n (map (shown m bs A) (seq 0 n))].
Proof.
intros m A n bs IB WS H0 H1.
pose proof (image_bytes_length segs n A bs IB) as L.
split; [split|].
- cbn. rewrite length_map, length_seq. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact H0|]. rewrite length_map, length_seq. split; [exact H1|].
intros i Hi. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i n); [|lia]. cbn [option_map]. rewrite Nat.add_0_l.
unfold mrd, shown. destruct (m (wa (A + Z.of_nat i))) as [b|]; [reflexivity|].
rewrite (image_bytes_rom n A bs i IB Hi). rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by lia. reflexivity.
- cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [exact H0|]. split; [exact H1|].
intros k Hk. apply (store_ok_all segs m n (Z_to_bv 64 A) ltac:(rewrite unsigned_lit by lia; lia) (store_ok_wseg segs m _ _ WS) (wa (A + k))).
unfold wa. rewrite !unsigned_lit by lia. lia.
Qed.
End StaticRW.

Definition LASTERR_TXT : list Z :=
[106; 115; 111; 110; 95; 111; 98; 106; 101; 99; 116; 95; 99; 111; 112; 121; 95; 115; 101; 114; 105; 97; 108; 105;
122; 101; 114; 95; 100; 97; 116; 97; 58; 32; 111; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121; 10].
Definition LASTERR_FMTS : list Z := LASTERR_TXT ++ [0].

#[using="Type"] Lemma lasterr_fmt_bytes_P : forall m, mem_inv rsegs m -> bytes_at rsegs m LASTERR_FMT_P (zb LASTERR_FMTS).
Proof. intros m MI. apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold LASTERR_FMT_P; lia | unfold LASTERR_FMT_P, zlength; cbn; lia]. Qed.

#[using="Type"] Lemma fp_calls_lasterr : fp_calls (length LASTERR_FMTS) LASTERR_FMTS [] = [].
Proof. vm_compute. reflexivity. Qed.

Definition lasterr_img_P := Eval vm_compute in match image_bytes rsegs LASTERR_BUF_P 256 with Some bs => bs | None => [] end.
#[using="Type"] Lemma lasterr_buf_P : forall m, rw_cells rsegs m LASTERR_BUF_P [CB 256 (map (shown m lasterr_img_P LASTERR_BUF_P) (seq 0 256))].
Proof.
intros m. apply bss_rw_cells; [vm_compute; reflexivity | vm_compute; reflexivity | unfold LASTERR_BUF_P; lia | unfold LASTERR_BUF_P; cbn; lia].
Qed.

#[using="Type"] Theorem set_last_err_P : set_last_err_spec_P.
Proof.
unfold set_last_err_spec_P, LASTERR_P, LASTERR_STK. intros until canary.
intros -> ST LO LOS SPA SPH SSP MI FRM.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO. pose proof (@rc_ceil_range RC__) as RCR.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (lasterr_buf_P m) as DST. unfold LASTERR_BUF_P in *.
set (junkd := map _ (seq 0 256)) in DST. clearbody junkd.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (487356, 487356 + 256)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 80%nat ST.
do 18 zs.

apply (proj1 (rw_cells_app rsegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.

pose proof vsnprintf_proof as VS. unfold vsnprintf_stmt in VS. cbv zeta in VS.
eapply evt_cut.
{ eapply VS with (D := 487356) (n := 256) (A := LASTERR_FMT_P) (VA := bv_unsigned sp + -56) (dn := 256%nat) (junkd := junkd) (fmt := LASTERR_FMTS) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [])
(lo := lo) (canary := canary) (r := 48) (o := LASTERR_TXT);
clear VS; rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, got_ssp, ssp_guard, LASTERR_FMT_P, zlength; cbn [length].
all: try reflexivity.
all: try lia.
all: try eassumption.
all: lazymatch goal with
| |- bytes_at _ _ _ _ => apply lasterr_fmt_bytes_P; assumption
| |- Forall _ LASTERR_FMTS => unfold LASTERR_FMTS, LASTERR_TXT; cbn [app]; repeat (apply Forall_cons; [split; [apply Zle_0_pos + reflexivity | reflexivity] |]); apply Forall_nil
| |- Forall no_s [] => apply Forall_nil
| |- Forall _ (fp_calls _ _ _) => rewrite fp_calls_lasterr; apply Forall_nil
| |- ssp_cells _ _ => split; [exact SSP1 | exact SSP2]
| |- _ => unfold LASTERR_FMTS, LASTERR_TXT; rewrite ?length_app; cbn [length Nat.add]; lia
end. }
cbv beta. intros ms' P.
unfold vsnprintf_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.

zs. zs. zs.
lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?c1, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?c2 |- _ =>
assert (FALL : rw_cells rsegs mm (bv_unsigned sp + -80) (c1 ++ c2));
[ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
| clear FR VAC ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact ST3|].
split; [| exact FRM'].
intros k Hk. apply FOK. cbn [FSAVED In] in Hk.
repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; vm_compute; lia.
Qed.

End RC__1.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QR2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QR2u.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJ3T.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJ3T. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOfx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOfx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UoYh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UoYh.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrIB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udgq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udgq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uzop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uzop.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma concat_nth_split : forall {X} (bss : list (list X)) i bs,
nth_error bss i = Some bs -> concat bss = concat (firstn i bss) ++ bs ++ concat (skipn (S i) bss).
Proof.
intros X bss i bs H. rewrite (concat_firstn_skipn bss i) at 1. f_equal.
revert bss H. induction i as [|i IH]; intros [|b bss] H; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- apply IH. exact H.
Qed.

#[using="Type"] Lemma mod16_mod8 : forall x k, x mod 16 = 0 -> k mod 8 = 0 -> (x + k) mod 8 = 0.
Proof.
intros x k Hx Hk. rewrite Z.add_mod by lia. rewrite Hk, Z.add_0_r.
replace (x mod 8) with 0; [reflexivity|]. symmetry.
apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult.
Qed.

Section DcArr.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Hypothesis LASTERR : set_last_err_spec_P.
Hypothesis HT63 : hi_top S4L HIx < 2^63.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (T : TSet).
Variable kids : list (option jshape).
Let r : jroot := JRtree (Sarr kids).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - dc_stk (rdepth r).
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM0 : frm0 fc.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.
Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> dc_res HIx r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Hypothesis IH : forall s', In (Some s') kids -> dcopy_spec HIx (JRtree s').

Notation dc_inv := (dc_inv ra sp s0 s1 s2 s3 s4 s5 s6 s7 m0 md0 LB BS lo D).
Notation dc_cell := (dc_cell sp).
Ltac dc_hyps := try first [ exact Kont | exact JR0 | exact NN | exact DAL | exact DHI | exact SPD | exact FRM0 | exact RA | exact HT | exact SPA | exact LOS | exact LO | exact HT63 | exact LASTERR | exact PUTX | exact PUT | clia ].

#[using="PUT PUTX fc r LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont IH"] Lemma dc_arr_loop :
forall (n ii : nat) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (kids' : list (option jshape)) (CBS REM : list blk) (cj : list byte) (e : word)
(pb : Z) (PBS : list blk) (a : Z) (AL : list blk) (ps : list Z) (KBS : list (list blk)) (q : Z),
n = (length kids - ii)%nat -> (ii < length kids)%nat ->
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj -> rw_cells rsegs mc (0x77c00 - 164) [C4 e] ->
HEAPx A (BS ++ CBS ++ REM ++ LB) mc mdc ->
BS = ((p, 48) :: AL ++ concat KBS) ++ PBS -> opt_pbuf rsegs mc PBS pb ->
rw_cells rsegs mc p (jhdr_cells JT_ARRAY 1 (fn_arr_to_json_string S4F) pb 0 0 ++ [C8 (wz a)]) ->
alist rsegs S4F mc AL a ps -> length ps = length kids -> length KBS = length kids -> akids rsegs S4F mc kids ps KBS ->
q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> jval rsegs S4F (Sarr kids') mc CBS q 1 ->
length kids' = ii -> okmax kids' <= okmax kids ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) (wz (Z.of_nat (length kids))) (wz (Z.of_nat ii)) (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x26e7c) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
induction n as [|n IHn]; intros until q; intros Hn Hii INV FS FRM1 CELL ERR HP EBS OPB HDR HAL L1 L2 KIDS Hq DC JQ LK OK; [lia|].
pose proof INV as (VM & PRES & ST & FR & G).
unfold Uzop.dc_frame in FR. unfold Uzop.dc_cell in CELL. pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu.
rewrite sdepth_Sarr in LOSu. pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP) as HTB.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
assert (INp1 : In (p, 48) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp1) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp - 72)] mc) as MU.

assert (Hlen : Z.of_nat (length kids) < 2^64).
{ destruct HAL as (arr & size & junk & EAL & Hl & Hsz & _). lia. }
pose proof (al_nth_in ps (Z.of_nat ii) ltac:(lia)) as NTH. rewrite Nat2Z.id in NTH.
destruct (akids_nth rsegs S4F _ _ _ _ ii _ KIDS NTH) as (k & bs & Hk & Hbs & JOB).
stash G. stash OPB. stash KIDS. stash JQ. stash JOB.
assert (AGB : forall (A' : AS S4L HIx) L' ma mda mx, HEAPx A' L' ma mda -> munch [(bv_unsigned sp - 80, bv_unsigned sp - 72)] ma mx -> wmono rsegs ma mx -> agree_on rsegs L' ma mx).
{ intros A' L' ma mda mx HPx MUx WMx. eapply (agree_of_munch rsegs); [exact MUx | exact WMx |]. intros b bk Hb. cbn.
pose proof (heap_blk S4L HIx _ _ _ _ b bk HPx Hb) as (_ & _ & _ & Hbhi & _). unfold_consts. lia. }

assert (CELLW : forall (A' : AS S4L HIx) L' ma mda mx, HEAPx A' (BS ++ L') ma mda -> jc_glob_P ma -> heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 ma ->
incl LB L' -> munch [(bv_unsigned sp - 80, bv_unsigned sp - 72)] ma mx -> wmono rsegs ma mx -> mem_inv rsegs mx ->
HEAPx A' (BS ++ L') mx mda /\ jc_glob_P mx /\ heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mx /\ agree_on rsegs (BS ++ L') ma mx).
{ intros A' L' ma mda mx HPx Gx PRx HiL MUx WMx MIx. split; [| split; [| split]].
- eapply (heap_frame S4L HIx); [exact HPx | | exact WMx | exact MIx]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HPx MUx). solve_frameW_with HPx.
- eapply jc_glob_P_outside; [exact Gx | exact MUx | exact WMx |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
- eapply presxD_trans; [exact PRx|]. eapply presxD_of_munch; [exact MUx | exact WMx |]. intros b Hb Hc Hd.
eapply (client_outside S4L HIx) with (LB0 := BS ++ LB) (SP := bv_unsigned sp); [exact HPx | | clia | solve_clientW S4L HIx HPx | exact Hb | exact Hc].
intros bb Hbb. apply in_app_or in Hbb; destruct Hbb as [Hbb|Hbb]; [apply in_or_app; left; exact Hbb | apply in_or_app; right; apply HiL; exact Hbb].
- eapply AGB; [exact HPx | exact MUx | exact WMx]. }
assert (HiAL : incl AL (BS ++ CBS ++ REM ++ LB)) by (rewrite EBS; incl_tac).
apply rz_evt; [exact MOK|].
bstep. bstepz. bstep. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HALx : alist rsegs S4F mx AL a ps) by (eapply (alist_agree rsegs S4F); [exact HAL | eapply AGB; [exact HP | exact MU | exact WM] | exact HiAL]) end.
call (array_list_get_idx_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 _ AL a ps (Z.of_nat ii));
[ exact MI | exact HALx
| intros b bn Hb; destruct (heap_blk S4L HIx _ _ _ _ b bn HP (HiAL _ Hb)) as (_ & Hbal & Hblo & Hbhi & _); exact (conj Hblo (conj Hbal Hbhi))
| reflexivity | reflexivity | lia | ].
replace (Z.of_nat ii <? Z.of_nat (length ps)) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
try rename MI0 into MI.
set (v := al_nth ps (Z.of_nat ii)) in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : munch _ mc m1 |- _ => rename H into MU1 end.
match goal with H : wmono rsegs mc m1 |- _ => rename H into WM1 end.

unstash OPB. unstash KIDS. unstash JQ. unstash JOB. unstash G.
destruct (CELLW _ (CBS ++ REM ++ LB) _ _ m1 HP G PRES ltac:(incl_tac) MU1 WM1 MI) as (HP1 & G1 & PRES1 & AG1).
assert (Hibs : incl bs BS).
{ rewrite EBS. intros b Hb. apply in_or_app; left. right. apply in_or_app; right. apply in_concat. exists bs. split; [eapply nth_error_In; exact Hbs | exact Hb]. }
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG1 ltac:(rewrite EBS; incl_tac)) as OPB1.
pose proof (alist_agree rsegs S4F _ _ _ _ _ _ HAL AG1 HiAL) as HAL1.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDS AG1 ltac:(rewrite EBS; incl_tac)) as KIDS1.
pose proof (jval_agree rsegs S4F _ _ _ _ _ _ _ JQ AG1 ltac:(incl_tac)) as JQ1.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB AG1 ltac:(intros b Hb; apply in_or_app; left; apply Hibs; exact Hb)) as JOB1.
clear OPB HAL KIDS JQ JOB G AG1 HP MOK. try clear MU. try clear WM.
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK.
pose proof (wmono_refl rsegs m1) as WM. pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp - 72)] m1) as MU.

assert (AADD : forall (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F2 : bvmap 5 word) (fc2 : bv 32)
(m2 : word -> option byte) (md2 : Model) (A2 : AS S4L HIx) (jso : Z) (vs : option jshape) (VBS REM2 : list blk) (e2 : word),
dc_inv m2 md2 -> fsaved F F2 -> frm0 fc2 ->
rw_cells rsegs m2 (bv_unsigned sp + -80) [C8 (wz jso)] -> rw_cells rsegs m2 490332 [C4 e2] ->
HEAPx A2 (VBS ++ BS ++ CBS ++ REM2 ++ LB) m2 md2 ->
opt_pbuf rsegs m2 PBS pb -> rw_cells rsegs m2 p [C4 (wz JT_ARRAY); C4 (wz 1); C8 (wz (fn_arr_to_json_string S4F)); C8 (wz pb); C8 (wz 0); C8 (wz 0); C8 (wz a)] ->
alist rsegs S4F m2 AL a ps -> akids rsegs S4F m2 kids ps KBS ->
rw_cells rsegs m2 D [C8 (wz q)] -> jval rsegs S4F (Sarr kids') m2 CBS q 1 ->
jopt rsegs S4F vs m2 VBS jso -> odep vs <= okmax kids ->
realizes rsegs (mkCfg (MS (mkR x1' (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0' t1' t2' (wz p) (wz D) a0' a1' a2' a3' a4' a5' a6' a7'
(wz SH_ENTRY_P) (wz 1) (wz (Z.of_nat (length kids))) (wz (Z.of_nat ii)) (wz 0) s7 s8 s9 s10 s11 t3' t4' t5' t6')
F2 (wz 0x26ebc) fc2 None m2 (seg_rom rsegs)) md2) T).
{ intros until e2. intros INV2 FS2 FRM2 CELL2 ERR2 HP2 OPB2 HDR2 HAL2 KIDS2 DC2 JQ2 JOB2 ODEP.
pose proof INV2 as (VM2 & PRES2 & ST2 & FR2 & G2). unfold Uzop.dc_frame in FR2.
destruct (sarr_open rsegs S4F _ _ _ _ _ JQ2) as (pbq & PBSq & aq & ALq & psq & KBSq & EBSq & OPBq & HDRq & HALq & Lq1 & Lq2 & KIDSq).
pose proof HALq as (arrq & sizeq & ajunk & EALq & Hlenq & Hszq & _). subst ALq.
set (LBR := VBS ++ BS ++ ((q, 48) :: concat KBSq ++ PBSq) ++ REM2 ++ LB).
assert (HPa : HEAPx A2 ((aq, 32) :: (arrq, 8 * sizeq) :: LBR) m2 md2) by (eapply (heap_perm S4L HIx); [exact HP2 | unfold LBR; rewrite EBSq; perm]).
assert (HiBS : incl BS LBR) by (unfold LBR; incl_tac).
assert (HiV : incl VBS LBR) by (unfold LBR; incl_tac).
assert (INq : In (q, 48) LBR) by (unfold LBR; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
pose proof (jopt_val rsegs S4F S4L HIx _ _ _ _ vs VBS jso HPa ltac:(intros b Hb; right; right; apply HiV; exact Hb) JOB2) as [Hj0 Hj1].
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hj1.
pose proof (heap_blk S4L HIx _ _ _ _ q 48 HPa ltac:(right; right; exact INq)) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
unfold jhdr_cells in HDRq. cbn [app] in HDRq.
pose proof (heap_model_ok _ _ _ _ _ _ HPa) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HPa) as MI2. cbn [hl_segs S4L] in MI2.
pose proof (wmono_refl rsegs m2) as WM2. pose proof (munch_refl [] m2) as MU2.
stash OPB2. stash HAL2. stash KIDS2. stash JOB2. stash OPBq. stash KIDSq. stash G2. stash HALq.
apply rz_evt; [exact MOK2|].
bstep. bstep. bstep. bstep.
unstash OPB2. unstash HAL2. unstash KIDS2. unstash JOB2. unstash OPBq. unstash KIDSq. unstash G2. unstash HALq.

apply evt_RZ_done.
eapply (array_list_add_cps HIx _ _ gp _ _ _ _ _ _ (wz 0) s7 s8 s9 s10 s11 F2 fc2 m2 md2 LBR lo aq arrq sizeq jso psq T);
[ exact HPa | exact HALq | lia | rewrite unsigned_lit by lia; exact ST2 | clia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR2 | rewrite unsigned_lit by lia; reflexivity | reflexivity | reflexivity | ].
intros ms4 md4 (m4 & A4 & rr & e4 & arr' & size' & RS4 & VM4 & ST4 & HPR4 & ERR4 & HP4 & OUT4).
destruct RS4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR4 by lia.
assert (AG4 : agree_on rsegs LBR m2 m4) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR4 | reflexivity | apply incl_refl]).
assert (PRES4 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m4).
{ eapply presxD_trans; [exact PRES2|]. apply pres_presxD. eapply heap_pres_weaken; [exact HPR4 | lia | unfold LBR; incl_tac]. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR2; [| left; cbn; lia]. cbn [hl_segs S4L] in FR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in CELL2; [| left; cbn; lia]. cbn [hl_segs S4L] in CELL2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in DC2; [| left; cbn; lia]. cbn [hl_segs S4L] in DC2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in HDRq; [| eapply client_range_block; [exact INq | lia | cbn; lia]]. cbn [hl_segs S4L] in HDRq.
pose proof (rw_cells_agree rsegs _ _ _ _ _ HDR2 AG4 ltac:(exists p, 48; split; [apply HiBS; exact INp | cbn; lia])) as HDR4.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB2 AG4 ltac:(intros b Hb; apply HiBS; rewrite EBS; in_find Hb)) as OPB4.
pose proof (alist_agree rsegs S4F _ _ _ _ _ _ HAL2 AG4 ltac:(intros b Hb; apply HiBS; rewrite EBS; in_find Hb)) as HAL4.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDS2 AG4 ltac:(intros b Hb; apply HiBS; rewrite EBS; in_find Hb)) as KIDS4.
pose proof (jopt_agree rsegs S4F _ _ _ _ _ _ JOB2 AG4 HiV) as JOB4.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPBq AG4 ltac:(unfold LBR; incl_tac)) as OPBq4.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDSq AG4 ltac:(unfold LBR; incl_tac)) as KIDSq4.
pose proof (jc_glob_P_pres _ _ _ _ HPR4 G2) as G4.
apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz jso))]) in CELL2; [| cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity].
clear HDR2 OPB2 HAL2 KIDS2 JOB2 OPBq KIDSq G2 HPa HP2 MOK2 MI2 WM2 MU2. try clear MI MU WM MOK.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m4) as WM. pose proof (munch_refl [] m4) as MU.
stash OPB4. stash HAL4. stash KIDS4. stash JOB4. stash OPBq4. stash KIDSq4. stash G4. stash OUT4.
reenter MOK4.
unstash OUT4.
destruct OUT4 as [(-> & -> & -> & ALq4) | (-> & ALq4 & _)].
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bstep. if_true. bstep.
unstash OPB4. unstash HAL4. unstash KIDS4. unstash JOB4. unstash OPBq4. unstash KIDSq4. unstash G4.
apply evt_RZ_done.
eapply (dc_fail HIx PUT PUTX) with (q := q) (sq := Sarr kids') (CBS := CBS) (CBSc := VBS) (REM := REM2); dc_hyps.
all: first [ exact CELL2 | exact ERR4 | exact DC2 | exact Hq
| eapply fsaved_trans; [exact FS2 | exact FS4] | apply FRM4; exact FRM2
| eapply (heap_perm S4L HIx); [exact HP4 | unfold LBR; rewrite EBSq; perm]
| split; [eapply model_vm_only_trans; [exact VM2 | exact VM4] | split; [exact PRES4 | split; [exact ST4 | split; [exact FR2 | exact G4]]]]
| idtac ].
+ eapply (sarr_close rsegs S4F) with (AL := [(aq, 32); (arrq, 8 * sizeq)]) (KBS := KBSq) (PBS := PBSq) (pb := pbq); try eassumption; try reflexivity.
unfold jhdr_cells. cbn [app]. exact HDRq.
+ destruct vs as [s''|]; cbn [jopt] in JOB4.
* right; left. destruct JOB4 as [Hj J4]. split; [exact Hj | exists s''; exact J4].
* left. exact JOB4.
-
bstep. if_false. bstep. bstep.
unstash OPB4. unstash HAL4. unstash KIDS4. unstash JOB4. unstash OPBq4. unstash KIDSq4. unstash G4.
set (CBS' := ((q, 48) :: [(aq, 32); (arr', 8 * size')] ++ concat (KBSq ++ [VBS])) ++ PBSq).
assert (JQ4 : jval rsegs S4F (Sarr (kids' ++ [vs])) m4 CBS' q 1).
{ eapply (sarr_close rsegs S4F) with (ps := psq ++ [jso]); try reflexivity.
+ exact OPBq4.
+ unfold jhdr_cells. cbn [app]. exact HDRq.
+ exact ALq4.
+ rewrite !length_app. cbn [length]. lia.
+ rewrite !length_app. cbn [length]. lia.
+ apply akids_app; [exact KIDSq4 | apply akids_one; exact JOB4]. }
assert (HP4' : HEAPx A4 (BS ++ CBS' ++ REM2 ++ LB) m4 md4).
{ eapply (heap_perm S4L HIx); [exact HP4 |]. unfold CBS', LBR. rewrite concat_app. cbn [concat]. rewrite app_nil_r. perm. }
assert (OK4 : okmax (kids' ++ [vs]) <= okmax kids) by (rewrite okmax_app, okmax_single; lia).
destruct (Nat.eq_dec (S ii) (length kids)) as [Hlast | Hmore].
+
if_falsex.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in HDR4 as X. destruct X as [HDR6 _].
apply evt_RZ_done.
eapply (dc_tail0 HIx) with (d := JRtree (Sarr (kids' ++ [vs]))) (CBS := CBS') (REM := REM2) (np := 48); dc_hyps.
all: first [ exact CELL2 | exact ERR4 | exact HP4' | exact INp | exact HDR6 | exact DC2 | exact Hq
| eapply fsaved_trans; [exact FS2 | exact FS4] | apply FRM4; exact FRM2
| split; [eapply model_vm_only_trans; [exact VM2 | exact VM4] | split; [exact PRES4 | split; [exact ST4 | split; [exact FR2 | exact G4]]]]
| idtac ].
* cbn [copy_of]. eexists. split; [reflexivity|]. rewrite !sdepth_Sarr. lia.
* cbn [jroot_rep]. split; [exact Hq | exact JQ4].
+
if_truex.
replace (Z.of_nat ii + 1) with (Z.of_nat (S ii)) by lia.
apply evt_RZ_done.
eapply (IHn (S ii)) with (kids' := kids' ++ [vs]) (CBS := CBS') (REM := REM2); try first [ exact CELL2 | exact ERR4 | exact HP4' | exact EBS | exact OPB4 | exact HDR4 | exact HAL4 | exact L1 | exact L2 | exact KIDS4 | exact Hq | exact DC2 | exact JQ4 | exact OK4 ].
* lia.
* lia.
* split; [eapply model_vm_only_trans; [exact VM2 | exact VM4] | split; [exact PRES4 | split; [exact ST4 | split; [exact FR2 | exact G4]]]].
* eapply fsaved_trans; [exact FS2 | exact FS4].
* apply FRM4; exact FRM2.
* rewrite length_app. cbn [length]. lia. }

bstep.
destruct k as [s'|].
-
destruct JOB1 as [Hv J'].
destruct (jval_root_in rsegs S4F _ _ _ _ _ J') as (nv & INv & Hnv).
assert (INv1 : In (v, nv) (BS ++ CBS ++ REM ++ LB)) by (apply in_or_app; left; apply Hibs; exact INv).
pose proof (heap_blk S4L HIx _ _ _ _ v nv HP1 INv1) as (_ & Hval & Hvlo & Hvhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hvhi.
if_falsex. bstep. bstep. bstep. bstep. bstep. bstep.

pose proof (concat_nth_split KBS ii bs Hbs) as EK.
set (LBc := ((p, 48) :: AL ++ concat (firstn ii KBS) ++ concat (skipn (S ii) KBS)) ++ PBS ++ CBS ++ REM ++ LB).
assert (PERMc : Permutation (BS ++ CBS ++ REM ++ LB) (bs ++ LBc)) by (unfold LBc; rewrite EBS, EK; perm).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (CELLW _ (CBS ++ REM ++ LB) _ _ m2 HP1 G1 PRES1 ltac:(incl_tac) MU WM MI) as (HP2 & G2 & PRES2 & AG2).
pose proof (kdepth_in kids s' (nth_error_In _ _ Hk)) as DEP.
assert (OKK : okmax kids = kdepth kids) by (pose proof (sdepth_Sarr kids); pose proof (sdepth_arr kids); lia).
apply evt_RZ_done.
pose proof (IH s' (nth_error_In _ _ Hk)) as REC. unfold dcopy_spec in REC.
eapply REC with (BS := bs) (LB := LBc) (lo := lo) (p := v) (D := bv_unsigned sp + -80); clear REC;
[ eapply (heap_perm S4L HIx); [exact HP2 | exact PERMc]
| cbn [jroot_rep]; split; [exact Hv | eapply (jval_agree rsegs S4F); [exact J' | exact AG2 | intros b Hb; apply in_or_app; left; apply Hibs; exact Hb]]
| discriminate | exact G2 | exact CELL
| rewrite unsigned_lit by lia; lia | lia | apply mod16_mod8; [exact SPA | reflexivity]
| rewrite unsigned_lit by lia; exact ST | clia
| rewrite unsigned_lit by lia; cbn [rdepth]; unfold dc_stk, REC_P, DC_C; pose proof (sdepth_nonneg s'); nia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity | exact FRM1 | reflexivity | reflexivity | reflexivity | ].
intros ms3 md3 m3 rv3 (RS3 & VM3 & ST3 & HPR3 & [e3 ERR3]) G3 JR3 RES3.
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp hl_volatile S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.

assert (PRES3 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m3).
{ eapply presxD_trans; [exact PRES2|]. apply presx_presxD.
eapply heap_presx_weaken; [eapply (presxD_presx S4L HIx) with (SP' := bv_unsigned sp); [exact HPR3 | eapply (heap_perm S4L HIx); [exact HP2 | exact PERMc] | apply incl_refl | lia | lia | clia] | lia | | intros b Xb; exact Xb].
intros b Hb. apply (Permutation_in _ PERMc). apply in_app_or in Hb; destruct Hb as [Hb|Hb]; in_find Hb. }
assert (AG3 : agree_on rsegs (BS ++ CBS ++ REM ++ LB) m2 m3).
{ eapply (presxD_agree S4L HIx); [exact HPR3 | eapply (heap_perm S4L HIx); [exact HP2 | exact PERMc] | | apply incl_refl | clia].
intros b Hb. apply (Permutation_in _ PERMc). exact Hb. }
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia | cbn; lia].
apply (presxD_rw_cells S4L _ _ _ _ _ _ _ HPR3) in DC; [| left; cbn; lia | cbn; lia].
cbn [hl_segs S4L] in FR, DC.
pose proof (rw_cells_agree rsegs _ _ _ _ _ HDR AG3 ltac:(exists p, 48; split; [exact INp1 | cbn; lia])) as HDR3.
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB1 AG3 ltac:(rewrite EBS; incl_tac)) as OPB3.
pose proof (alist_agree rsegs S4F _ _ _ _ _ _ HAL1 AG3 HiAL) as HAL3.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDS1 AG3 ltac:(rewrite EBS; incl_tac)) as KIDS3.
pose proof (jval_agree rsegs S4F _ _ _ _ _ _ _ JQ1 AG3 ltac:(incl_tac)) as JQ3.
clear HDR OPB1 HAL1 KIDS1 JQ1 CELL MU WM MI MOK HP1 G1 PRES1 PRES2 AG2 G2 J'.
pose proof (wmono_refl rsegs m3) as WM. pose proof (munch_refl [] m3) as MU.
stash JR3. stash OPB3. stash HAL3. stash KIDS3. stash JQ3. stash G3.
destruct RES3 as [(-> & A3 & d3 & q3 & CBS3 & REM3 & CO3 & Hq3 & CELL3 & JD3 & HP3) | (-> & A3 & q3 & CBS3 & REM3 & CELL3 & FRES3 & HP3)]; cbn [hl_segs S4L] in CELL3.
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
stash JD3. stash CO3.
reenter MOK3.
bstep. if_false. ub_skip.
unstash JD3. unstash CO3. unstash JR3. unstash OPB3. unstash HAL3. unstash KIDS3. unstash JQ3. unstash G3.
destruct CO3 as (s3' & -> & DEP3). cbn [jroot_rep] in JD3.
apply evt_RZ_done.
eapply (AADD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 q3 (Some s3') CBS3 (REM3 ++ REM) e3);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR | exact G3]]]]
| eapply fsaved_trans; [exact FS | exact FS3] | apply FRM3; exact FRM1
| exact CELL3 | exact ERR3 | eapply (heap_perm S4L HIx); [exact HP3 | unfold LBc; rewrite EBS, EK; perm]
| exact OPB3 | exact HDR3 | exact HAL3 | exact KIDS3 | exact DC | exact JQ3 | exact JD3 | cbn [odep]; lia ].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
stash FRES3.
reenter MOK3.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
bstep. if_true. bstep.
unstash FRES3. unstash JR3. unstash JQ3. unstash G3.
apply (rw_cells_recast rsegs _ _ _ [CB 8 (le8 (wz q3))]) in CELL3; [| cbn [cells_wf cell_wf]; split; [apply length_le8 | exact I] | reflexivity | reflexivity].
apply evt_RZ_done.
eapply (dc_fail HIx PUT PUTX) with (q := q) (sq := Sarr kids') (CBS := CBS) (CBSc := CBS3) (REM := REM3 ++ REM); dc_hyps.
all: first [ exact CELL3 | exact ERR3 | exact DC | exact Hq | exact JQ3 | exact FRES3
| eapply fsaved_trans; [exact FS | exact FS3] | apply FRM3; exact FRM1
| eapply (heap_perm S4L HIx); [exact HP3 | unfold LBc; rewrite EBS, EK; perm]
| split; [eapply model_vm_only_trans; [exact VM | exact VM3] | split; [exact PRES3 | split; [exact ST3 | split; [exact FR | exact G3]]]] ].
-
destruct JOB1 as [Ev Ebs]. rewrite Ev. if_true. bstepz. ub_skip.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
destruct (CELLW _ (CBS ++ REM ++ LB) _ _ mx HP1 G1 PRES1 ltac:(incl_tac) MU WM MI) as (HP2 & G2 & PRES2 & AG2) end.
eapply (AADD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 _ mdc A 0 None [] REM e);
[ split; [exact VM | split; [exact PRES2 | split; [exact ST | split; [exact FR | exact G2]]]] | exact FS | exact FRM1
| exact CELL | exact ERR | cbn [app]; exact HP2 | | exact HDR | | | exact DC | | split; reflexivity | cbn; exact OK0 ].
+ eapply (opt_pbuf_agree rsegs); [exact OPB1 | exact AG2 | rewrite EBS; incl_tac].
+ eapply (alist_agree rsegs S4F); [exact HAL1 | exact AG2 | exact HiAL].
+ eapply (akids_agree rsegs S4F); [exact KIDS1 | exact AG2 | rewrite EBS; incl_tac].
+ eapply (jval_agree rsegs S4F); [exact JQ1 | exact AG2 | incl_tac].
Qed.

#[using="PUT PUTX fc LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont IH"] Lemma dc_arr :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (q : Z) (CBS : list blk) (cj : list byte) (e : word),
dc_inv mc mdc -> fsaved F F1 -> frm0 fc1 ->
dc_cell mc cj -> rw_cells rsegs mc (0x77c00 - 164) [C4 e] ->
HEAPx A (BS ++ CBS ++ LB) mc mdc -> q <> 0 -> rw_cells rsegs mc D [C8 (wz q)] -> scopy S4L S4F r mc CBS q ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) (wz 0) a1 a2 a3 a4 a5 a6 a7
(wz SH_ENTRY_P) (wz 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x26db4) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until e. intros INV FS FRM1 CELL ERR HP Hq DC SC. pose proof INV as (VM & PRES & ST & FR & G). clear HT63 LASTERR.
unfold Uzop.dc_frame in FR. unfold Uzop.dc_cell in CELL. pose proof LOS as LOSu. unfold dc_stk, REC_P, DC_C in LOSu. cbn [rdepth r] in LOSu.
rewrite sdepth_Sarr in LOSu. pose proof (okmax_nonneg kids) as OK0. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
cbn [scopy r] in SC.

destruct JR0 as [Hp J0].
assert (J : jval rsegs S4F (Sarr kids) mc BS p 1).
{ eapply (jval_agree rsegs S4F); [exact J0 | | apply incl_refl].
eapply (presxD_agree S4L HIx); [exact PRES | exact HP | incl_tac | incl_tac | clia]. }
clear J0.
destruct (sarr_open rsegs S4F _ _ _ _ _ J) as (pb & PBS & a & AL & ps & KBS & EBS & OPB & HDR & HAL & L1 & L2 & KIDS).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
assert (INp1 : In (p, 48) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP INp1) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
assert (Hlen : Z.of_nat (length kids) < 2^64).
{ destruct HAL as (arr & size & junk & EAL & Hl & Hsz & _). lia. }
unfold jhdr_cells in HDR. cbn [app] in HDR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash OPB. stash KIDS. stash SC. stash G.
apply rz_evt; [exact MOK|].
bstep. bstep. bstep. if_true.
bstep. bstep.

call (array_list_length_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 _ AL a ps);
[ exact MI | exact HAL
| intros b n Hb; destruct (heap_blk S4L HIx _ _ _ _ b n HP ltac:(apply in_or_app; left; rewrite EBS; apply in_or_app; left; right; apply in_or_app; left; exact Hb)) as (_ & Hbal & Hblo & Hbhi & _); exact (conj Hblo (conj Hbal Hbhi))
| reflexivity | ].
try rename MI0 into MI. rewrite L1.
unstash OPB. unstash KIDS. unstash SC. unstash G.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : munch [] mc m1 |- _ => rename H into MU1 end. match goal with H : wmono rsegs mc m1 |- _ => rename H into WM1 end.
assert (HP1 : HEAPx A (BS ++ CBS ++ LB) m1 mdc).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM1 | exact MI]. eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU1). apply Forall_nil. }
assert (G1 : jc_glob_P m1) by (eapply jc_glob_P_outside; [exact G | exact MU1 | exact WM1 | apply Forall_nil]).
assert (PRES1 : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 m1).
{ eapply presxD_trans; [exact PRES|]. eapply presxD_of_munch; [exact MU1 | exact WM1 | intros; exact I]. }
assert (AG1 : agree_on rsegs (BS ++ CBS ++ LB) mc m1) by (eapply (agree_of_munch rsegs); [exact MU1 | exact WM1 | intros; exact I]).
pose proof (opt_pbuf_agree rsegs _ _ _ _ _ OPB AG1 ltac:(rewrite EBS; incl_tac)) as OPB1.
pose proof (alist_agree rsegs S4F _ _ _ _ _ _ HAL AG1 ltac:(rewrite EBS; incl_tac)) as HAL1.
pose proof (akids_agree rsegs S4F _ _ _ _ _ _ KIDS AG1 ltac:(rewrite EBS; incl_tac)) as KIDS1.
pose proof (jval_agree rsegs S4F _ _ _ _ _ _ _ SC AG1 ltac:(incl_tac)) as SC1.
clear OPB HAL KIDS SC G PRES HP AG1.
bstep.
destruct (Nat.eq_dec (length kids) 0) as [L0 | L0].
-
rewrite L0. if_true.
apply (proj1 (rw_cells_app rsegs _ p [_; _; _; _; _; _] _)) in HDR as X. destruct X as [HDR6 _].
apply evt_RZ_done.
eapply (dc_tail0 HIx) with (d := JRtree (Sarr [])) (CBS := CBS) (REM := []) (np := 48); dc_hyps.
all: first [ exact CELL | exact ERR | exact INp | exact HDR6 | exact DC | exact Hq | exact FS | exact FRM1
| eapply (heap_perm S4L HIx); [exact HP1 | perm]
| split; [exact VM | split; [exact PRES1 | split; [exact ST | split; [exact FR | exact G1]]]]
| idtac ].
+ cbn [copy_of]. eexists. split; [reflexivity|]. rewrite !sdepth_Sarr. cbn. lia.
+ cbn [jroot_rep]. split; [exact Hq | exact SC1].
-
if_falsex. bstep. bstep. bstep.
pose proof (hi_top_bound2 _ _ _ _ _ _ HP1) as HTB. rewrite (unsigned_lit D) by lia. rewrite (ub_land7 D DAL).
apply evt_RZ_done.
replace (wz 0) with (wz (Z.of_nat 0)) by reflexivity.
eapply (dc_arr_loop (length kids) 0) with (kids' := []) (CBS := CBS) (REM := []);
try first [ exact CELL | exact ERR | exact EBS | exact OPB1 | exact HDR | exact HAL1 | exact L1 | exact L2 | exact KIDS1 | exact Hq | exact DC | exact SC1 | exact FS | exact FRM1 ].
+ lia.
+ lia.
+ split; [exact VM | split; [exact PRES1 | split; [exact ST | split; [exact FR | exact G1]]]].
+ eapply (heap_perm S4L HIx); [exact HP1 | perm].
+ reflexivity.
+ cbn. exact OK0.
Qed.
End DcArr.

End RC__1.

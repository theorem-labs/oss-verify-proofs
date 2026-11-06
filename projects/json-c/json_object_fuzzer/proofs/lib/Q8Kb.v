(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Qc27 Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs QCiC Qpj5 QCNF QoNr QdZp QHig Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho Qu3b QYyZ QFd5 QnRU QteI QQNJ QMPy QIG5 QC9y Qr5k QbPx_c1 QCqp Qi1S QHRw Qvzz Q0z1 QlES QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QYyZ.Mq2 QFd5.Mq0 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0 QQNJ.Mq3.
Import QMPy.
Import QIG5. Import QC9y.
Import Qr5k.Mq0 QbPx_c1.Mq0 QCqp.Mq0 Qr5k.Mq1 Qi1S.Mq1 QHRw.Mq0 Qvzz.Mq0.
Import Q0z1.
Import QlES.
Import QXE1.Mq0.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells asegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells asegs m A (pre ++ C4 v' :: post).
Proof.
intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
- destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
- rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.

Ltac c4_eqv H k v' :=
lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
let H' := fresh in
pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
end end.

Section VsnProof.
Context {BAND : Band}.
Variables (AFMT : Z) (fmt : list Z).
Hypothesis PCOMMON : pcommon_stmt AFMT.

Theorem vsnprintf_proof : vsnprintf_stmt AFMT fmt.
Proof using PCOMMON BAND.
unfold vsnprintf_stmt. intros until o. cbv zeta.
intros -> -> -> -> DST ISHm BY HF P1 VAA SAOK MODEL FPC ROOM Hn ST LO GLO QHI SSP MI FRM HA0 HA HSZ QVA VAHI DD1 DDV DAPP RD.
unfold VSN_DEPTH, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, vsnprintf_entry in *.
assert (CEIL : band_lo <= lo) by exact GLO.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *. unfold dapp in DAPP.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (ISHc : forall mm, munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m mm -> wmono asegs m mm -> ISH mm).
{ intros mm MUx WMx. eapply ISH_munch_app; [exact ISHm | exact MUx | exact WMx |].
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
pose proof ISHm as (ASH & RC & SB).
pose proof (rt_161720 _ RC) as K18. pose proof (rt_157bb0 _ RC) as K7. pose proof (rt_1f25bc _ RC) as K22. pose proof (rt_159c68 _ RC) as K17.
carve_frame 304%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 304 _ _ [232;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR.
do 12 zs.
zs. zs. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
zs. zs. zs. zs. zs.

replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
zs. zs. zs. zs. zs.
match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -304 + Z.of_nat 232)%Z with (bv_unsigned sp + -72)%Z in FRv by lia.

zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ISHc mc MU WM) as ISH1 end.
call_u (memset_icpt_spec (bv_unsigned sp + -304) 0 232 lo j0);
[ exact FZ | assumption | lia | lia | unsigned_lits; eassumption | exact CEIL | unsigned_lits; unfold MEMSET_ICPT_STACK; lia | unsigned_lits; lia
| exact (proj2 (proj2 ISH1)) | exact (proj1 (proj2 ISH1))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH1)); [unfold szone; right; left; lia | lia] |].
clear ISH1.
match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB _ (repeat _ _)] |- _ => rename H into FZ' end.

pose proof (rw_cells_recast _ _ _ (gfile_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) 0 ++ snfile_rest 0) FZ'
ltac:(cbn [cells_wf cell_wf gfile_cells snfile_rest app]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
unfold gfile_cells, snfile_rest in FC. cbn [app] in FC.
do 10 zs.
c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).

pose proof (rw_CB_length _ _ _ _ DST) as LJ.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST. clear DA2.
zs. zs. zs.

apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FC. destruct FC as [FH FR]. cbn [cells_size csize Nat.add app] in FR.
replace (bv_unsigned sp + -304 + Z.of_nat 148)%Z with (bv_unsigned sp + -304 + 148)%Z in FR by lia.
apply (proj1 (rw_cells_app asegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -72 + Z.of_nat 16)%Z with (bv_unsigned sp + -56)%Z in FRv by lia.
zs.
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. carve_frame 48%nat ST. rename FR0 into FRf.
do 9 istep.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. istep. step. if_lit. istep. istep. istep. istep. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ISHc mc MU WM) as ISH2 end.
pose proof PCOMMON as PCD. unfold pcommon_stmt, PCOMMON_STACK, pcommon_entry in PCD.
call_u PCD; [ exact ISH2 | assumption | unsigned_lits; exact ST | exact CEIL | unsigned_lits; lia |].
clear PCD.
clear ISH2.
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.

istep. istep. istep. istep. istep. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ISHc mc MU WM) as ISH3 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RD3 : (0 < Z.of_nat (length o))%Z -> rng_ok mc D (Z.of_nat (length o))) end.
{ intros K. eapply rng_ok_munch; [exact (RD K) | exact MU | exact WM |].
pose proof (proj1 (proj2 (RD K))) as D47.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }
pose proof vfprintf_sn_proof as VF. unfold vfprintf_sn_stmt in VF.
eapply evt_cut.
{ eapply VF with (Fp := bv_unsigned sp + -304) (CK := bv_unsigned sp + -72) (D := D) (n := n + -1) (bufp := bv_unsigned sp + -49) (A := AFMT) (VA := VA)
(dn := dn) (junkd := upd junkd (Z.to_nat 0) (Z_to_bv 8 0)) (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength, dapp.
all: try reflexivity.
all: try lia.
- unfold snfile_head, gfile_cells, sn_write_entry. exact FH.
- unfold snfile_rest. exact FR.
- exact CKC.
- exact DST.
- exact ISH3.
- exact BY.
- exact HF.
- exact P1.
- exact VAA.
- apply sargs_args_ok. exact SAOK.
- exact MODEL.
- exact FPC.
- exact ST.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM.
- exact HSZ.
- exact RD3. }
cbv beta. intros ms' P. clear VF.
unfold vfprintf_sn_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & fjunk & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3 & CK3 & FJ3).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
fix_ret.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

do 5 istep. step. release_frame FRf ST3 (bv_unsigned sp + -304).
try fix_ret.

lazymatch goal with H : rw_cells _ _ 6565536 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 7 zs.
lazymatch goal with FJ : rw_cells _ ?mm (bv_unsigned sp + -304)%Z _, CK : rw_cells _ ?mm (bv_unsigned sp + -72)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -56)%Z _ |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -304) ([CB 232 fjunk] ++ [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n + -1 - zlength o))] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FJ|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact CK | lia] |];
cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear FJ CK FR ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|].
split; [split; [exact SSP1 | exact SSP2]|].
rewrite upd_firstn_skipn in DST3 by (rewrite LJ; lia). change (Z.to_nat 0) with 0%nat in DST3.
change (firstn 0 junkd) with (@nil byte) in DST3. rewrite app_nil_l in DST3.
change (skipn (S (length o)) (Z_to_bv 8 0 :: skipn 1 junkd)) with (skipn (length o) (skipn 1 junkd)) in DST3.
rewrite skipn_skipn, Nat.add_1_r in DST3. exact DST3.
Qed.
End VsnProof.
End Mq0.
From Stdlib Require String Ascii.
From stdpp Require gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1.
Import Q0z1.
Import QlES.
Import Qr5k.Mq2 Qi1S.Mq2 Qvzz.Mq0.
Import QXE1.Mq0.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Lemma printf_common_ld_raw :
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - PCOMMON_STACK, bv_unsigned sp)] lo m
(fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x23700) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose_str FMT 0x23700 [37; 108; 100; 0] MI.
unfold pcommon_entry in *.
eapply evt_cut; [ eapply pc_setup_g4 with (c := 37) (l := [108; 100]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | left; reflexivity] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c640 [106; 122; 116; 76; 113].

run. call_strchr 0x146d7 [99; 67; 115; 83].

run. carve_frame 32%nat ST. bstep.
run. call_strchr 0x1d915 [100; 105; 111; 117; 120; 88; 110].

run. release_frame FR ST (bv_unsigned sp + -2240). call_strchr 0x16c7d [97; 65; 101; 69; 102; 70; 103; 71].

run.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of FRa with rw_cells _ _ ?A ?ca => lazymatch type of DIR with rw_cells _ _ _ ?cd => lazymatch type of FRb with rw_cells _ _ _ ?cb =>
assert (FR : rw_cells asegs mc A (ca ++ cd ++ cb))
by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRa|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; cbn [cells_size csize Nat.add app];
[eapply rwc_eq; [exact DIR| lia] | eapply rwc_eq; [exact FRb| lia]]);
clear FRa DIR FRb; cbn [app] in FR
end end end end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact I].
Qed.
End S.

Theorem printf_common_ld {BAND : Band} : pcommon_stmt 0x23700.
Proof. unfold pcommon_stmt. intros. apply printf_common_ld_raw; assumption. Qed.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1.
Import Q0z1.
Import QlES.
Import Qr5k.Mq2 Qi1S.Mq2 Qvzz.Mq0.
Import QXE1.Mq0.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Lemma printf_common_lu_raw :
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - PCOMMON_STACK, bv_unsigned sp)] lo m
(fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x23720) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose_str FMT 0x23720 [37; 108; 117; 0] MI.
unfold pcommon_entry in *.
eapply evt_cut; [ eapply pc_setup_g4 with (c := 37) (l := [108; 117]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | right; reflexivity] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c640 [106; 122; 116; 76; 113].

run. call_strchr 0x146d7 [99; 67; 115; 83].

run. carve_frame 32%nat ST. bstep.
run. call_strchr 0x1d915 [100; 105; 111; 117; 120; 88; 110].

run. release_frame FR ST (bv_unsigned sp + -2240). call_strchr 0x16c7d [97; 65; 101; 69; 102; 70; 103; 71].

run.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of FRa with rw_cells _ _ ?A ?ca => lazymatch type of DIR with rw_cells _ _ _ ?cd => lazymatch type of FRb with rw_cells _ _ _ ?cb =>
assert (FR : rw_cells asegs mc A (ca ++ cd ++ cb))
by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRa|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; cbn [cells_size csize Nat.add app];
[eapply rwc_eq; [exact DIR| lia] | eapply rwc_eq; [exact FRb| lia]]);
clear FRa DIR FRb; cbn [app] in FR
end end end end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact I].
Qed.
End S.

Theorem printf_common_lu {BAND : Band} : pcommon_stmt 0x23720.
Proof. unfold pcommon_stmt. intros. apply printf_common_lu_raw; assumption. Qed.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QteI.Mq1.
Import Q0z1.
Import QlES.
Import Qr5k.Mq2 Qi1S.Mq2 Qvzz.Mq0.
Import QXE1.Mq0.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).

Ltac dir_flat DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A ?cs =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A ([] ++ cs ++ [])) by (rewrite app_nil_r; exact DIR);
apply rw_cells_merge in D; cbn [cells_size csize cells_bytes cbytes app Nat.add] in D;
clear DIR; rename D into DIR end.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Lemma printf_common_u00cc_raw :
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - PCOMMON_STACK, bv_unsigned sp)] lo m
(fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x236a0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose_str FMT 0x236a0 [92; 117; 48; 48; 37; 99; 37; 99; 0] MI.
unfold pcommon_entry in *.
eapply evt_cut; [ eapply pc_setup_g9 with (c := 92) (l := [117; 48; 48; 37; 99; 37; 99]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 4%nat 0%nat [92; 117; 48; 48; 37; 99; 37; 99; 0] 0x236a0.

run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.
run. call_strchr 0x1c640 [106; 122; 116; 76; 113].
run. call_strchr 0x146d7 [99; 67; 115; 83].
run. call_strchr 0x1abb9 [67; 83].
run. call_strchr 0x1086e [99; 115; 91].
run. call_strchr 0x13f97 [115; 83].
run. call_strchr 0x16c7d [97; 65; 101; 69; 102; 70; 103; 71].

dir_flat DIR.
run. call_memset DIR.
run. call_strchr 0x15b57 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.
run. call_strchr 0x1c640 [106; 122; 116; 76; 113].
run. call_strchr 0x146d7 [99; 67; 115; 83].
run. call_strchr 0x1abb9 [67; 83].
run. call_strchr 0x1086e [99; 115; 91].
run. call_strchr 0x13f97 [115; 83].
run. call_strchr 0x16c7d [97; 65; 101; 69; 102; 70; 103; 71].

dir_flat DIR.
run.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of FRa with rw_cells _ _ ?A ?ca => lazymatch type of DIR with rw_cells _ _ _ ?cd => lazymatch type of FRb with rw_cells _ _ _ ?cb =>
assert (FR : rw_cells asegs mc A (ca ++ cd ++ cb))
by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRa|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; cbn [cells_size csize Nat.add app];
[eapply rwc_eq; [exact DIR| lia] | eapply rwc_eq; [exact FRb| lia]]);
clear FRa DIR FRb; cbn [app] in FR
end end end end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact I].
Qed.
End S.

Theorem printf_common_u00cc {BAND : Band} : pcommon_stmt 0x236a0.
Proof. unfold pcommon_stmt. intros. apply printf_common_u00cc_raw; assumption. Qed.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Qc27 Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QYyZ.Mq2 QFd5.Mq0 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0 QQNJ.Mq3.
Import QMPy.
Import QIG5. Import QC9y.
Import Qr5k.Mq0 QbPx_c1.Mq0 QCqp.Mq0 Qr5k.Mq1 Qi1S.Mq1 QHRw.Mq0 Qvzz.Mq0.
Import Q0z1.
Import QlES.
Import QXE1.Mq0.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).

Lemma qslow_loop_vsn : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a4', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz e) (wz e) (wz 0) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (0x54164 + 16)) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz p) (wz e) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x54164) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind;
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK;
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B;
step; stp; stp; step; destruct (Z_lt_le_dec (p + 1) e) as [X1|X1];
[ ifz; eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K]
| ifz; replace (p + 1) with e by lia; apply K ].
Qed.

Section T.
Context {BAND : Band}.
Variables (sp0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rs7 rs6 rs5 rs4 rs3 rs2 rs1 rs0 rra x1 x2 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : mem) (D n r AFMT : Z) (jA jB : list byte) (P : machine_state -> Prop).
Let w := Z.min n (r + 1).
Hypothesis SP0 : 2256 <= sp0 /\ sp0 <= 2^47.
Hypothesis RNG : rng_ok m D w.
Hypothesis W1 : 1 <= w <= 64.
Hypothesis Hr : 0 <= r < 2^31 - 1.
Hypothesis Hn : 1 <= n < 2^63.
Hypothesis SB : shadow_base asegs m.
Hypothesis MI : mem_inv asegs m.
Hypothesis FRi : rw_cells asegs m (sp0 + -2128)
[CB 1936 jA; C8 x1; C8 x2; CB 8 jB; C8 rs7; C8 rs6; C8 rs5; C8 rs4; C8 rs3; C8 rs2; C8 rs1; C8 rs0; C8 rra].
Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
evt asegs P (MS (mkR rra (wz (sp0 + -96)) gp tp t0' t1' t2' rs0 rs1 (wz r) a1' a2' a3' a4' a5' a6' a7' rs2 rs3 rs4 rs5 rs6 rs7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft (ret_pc rra) fc None m (seg_rom asegs)).

Lemma vsn_icpt_tail :
evt asegs P (MS (mkR (wz 344028) (wz (sp0 + -2256)) gp tp t0 t1 t2 (wz (sp0 + -96)) (wz AFMT) (wz r) a1 a2 a3 a4 a5 a6 a7
(wz D) (wz n) (wz 1578536) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (wz 344032) fc None m (seg_rom asegs)).
Proof.
destruct RNG as (P0 & P47 & SO & BIG & NB).
pose proof (SO ltac:(lia)) as SO2. destruct (NB ltac:(lia)) as [[w1 WD1] [w2 WD2]].
destruct SB as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step.
rewrite (unsigned_lit r) by lia. rewrite QDM6.swrap32_small by lia.
step.

assert (CHK : forall (b1 b2 b3 b4 b5 c5 : word),
evt asegs P (MS (mkR (wz 344028) (wz (sp0 + -2256)) gp tp t0 t1 t2 (wz (sp0 + -96)) (wz w) (wz r) b1 b2 b3 b4 b5 a6 a7
(wz D) (wz n) (wz 1578536) c5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (wz 0x53ffc) fc None m (seg_rom asegs))).
{ intros b1 b2 b3 b4 b5 c5.
step. step.
step. unfold_cond. fold_lit_ux. rewrite u_nm65 by lia.
replace (18446744073709551551 <? 18446744073709551551 + w) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
step. stp. step. stp. step. step. step. stp. stp.
rewrite (unsigned_lit D), (unsigned_lit (D + w + -1)) by lia.
replace (2147450880 + D ≫ 3) with (SH D) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (D + w + -1) ≫ 3) with (SH (D + w - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH D /\ SH D <= SH (D + w - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH D)), (unsigned_lit (SH (D + w - 1))) by lia. rewrite !land_m8 by lia.
replace (SH D - SH D mod 8) with (8 * (SH D / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (D + w - 1) - SH (D + w - 1) mod 8) with (8 * (SH (D + w - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.
destruct (shadow_ok_last _ D w SO2 ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ D w SO2 ltac:(lia)) as ZH.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a1'' a3'' a4'' a5'' : word,
ms1 = MS (@bvmap_set 5 word 11 a1'' (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 14 a4'' (@bvmap_set 5 word 15 a5'' R)))) FF (wz 0x54044) fcc rv mm ro))
end.
{ step. if_cases Hq.
-
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (D + w + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (D + w - 1)) (SH D)) as [X1|X1].
+ ifz. replace (SH D) with (SH (D + w - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_vsn (Z.to_nat (SH (D + w - 1) - SH D)) (SH D)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a4x. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a1'' & a3'' & a4'' & a5'' & ->). simp_regs.

istep. do 9 istep. istep. step.
apply K. }

step. unfold_cond. rewrite (unsigned_lit n), (unsigned_lit (r + 1)) by lia.
destruct (Z_le_gt_dec (r + 1) n) as [LE | GT].
-
replace (n <? r + 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
assert (EW : w = r + 1) by (unfold w; lia).
step. step. step. step.
step. rewrite (unsigned_lit D), zb_lxor_ones by lia. rewrite <- EW. ifz.
apply CHK.
-
replace (n <? r + 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
assert (EW : w = n) by (unfold w; lia).
step. step. step.
step. rewrite (unsigned_lit D), zb_lxor_ones by lia. ifz.
rewrite EW in CHK. apply CHK.
Qed.
End T.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb.
Import Q0z1.
Import QlES.
Import Qr5k.Mq4 Qi1S.Mq4 Qvzz.
Import QXE1.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Lemma printf_common_ld_raw :
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - PCOMMON_STACK, bv_unsigned sp)] lo m
(fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x23760) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose_str FMT 0x23760 [37; 108; 100; 0] MI.
unfold pcommon_entry in *.
eapply evt_cut; [ eapply pc_setup_g4 with (c := 37) (l := [108; 100]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | left; reflexivity] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c77b [106; 122; 116; 76; 113].

run. call_strchr 0x14816 [99; 67; 115; 83].

run. carve_frame 32%nat ST. bstep.
run. call_strchr 0x1da50 [100; 105; 111; 117; 120; 88; 110].

run. release_frame FR ST (bv_unsigned sp + -2240). call_strchr 0x16dde [97; 65; 101; 69; 102; 70; 103; 71].

run.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of FRa with rw_cells _ _ ?A ?ca => lazymatch type of DIR with rw_cells _ _ _ ?cd => lazymatch type of FRb with rw_cells _ _ _ ?cb =>
assert (FR : rw_cells asegs mc A (ca ++ cd ++ cb))
by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRa|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; cbn [cells_size csize Nat.add app];
[eapply rwc_eq; [exact DIR| lia] | eapply rwc_eq; [exact FRb| lia]]);
clear FRa DIR FRb; cbn [app] in FR
end end end end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact I].
Qed.
End S.

Theorem printf_common_ld {BAND : Band} : pcommon_stmt 0x23760.
Proof. unfold pcommon_stmt. intros. apply printf_common_ld_raw; assumption. Qed.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb.
Import Q0z1.
Import QlES.
Import Qr5k.Mq4 Qi1S.Mq4 Qvzz.
Import QXE1.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Lemma printf_common_lu_raw :
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - PCOMMON_STACK, bv_unsigned sp)] lo m
(fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x23780) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose_str FMT 0x23780 [37; 108; 117; 0] MI.
unfold pcommon_entry in *.
eapply evt_cut; [ eapply pc_setup_g4 with (c := 37) (l := [108; 117]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | right; reflexivity] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.

run. call_strchr 0x1c77b [106; 122; 116; 76; 113].

run. call_strchr 0x14816 [99; 67; 115; 83].

run. carve_frame 32%nat ST. bstep.
run. call_strchr 0x1da50 [100; 105; 111; 117; 120; 88; 110].

run. release_frame FR ST (bv_unsigned sp + -2240). call_strchr 0x16dde [97; 65; 101; 69; 102; 70; 103; 71].

run.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of FRa with rw_cells _ _ ?A ?ca => lazymatch type of DIR with rw_cells _ _ _ ?cd => lazymatch type of FRb with rw_cells _ _ _ ?cb =>
assert (FR : rw_cells asegs mc A (ca ++ cd ++ cb))
by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRa|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; cbn [cells_size csize Nat.add app];
[eapply rwc_eq; [exact DIR| lia] | eapply rwc_eq; [exact FRb| lia]]);
clear FRa DIR FRb; cbn [app] in FR
end end end end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact I].
Qed.
End S.

Theorem printf_common_lu {BAND : Band} : pcommon_stmt 0x23780.
Proof. unfold pcommon_stmt. intros. apply printf_common_lu_raw; assumption. Qed.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QteI.Mqb.
Import Q0z1.
Import QlES.
Import Qr5k.Mq4 Qi1S.Mq4 Qvzz.
Import QXE1.
Local Unset Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Local Notation wz := (Z_to_bv 64).

Ltac dir_flat DIR :=
lazymatch type of DIR with rw_cells _ ?mm ?A ?cs =>
let D := fresh "DIR" in
assert (D : rw_cells asegs mm A ([] ++ cs ++ [])) by (rewrite app_nil_r; exact DIR);
apply rw_cells_merge in D; cbn [cells_size csize cells_bytes cbytes app Nat.add] in D;
clear DIR; rename D into DIR end.

Section S.
Context {BAND : Band}.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
Hypothesis ISH0 : ISH m.
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CEIL : band_lo <= lo.
Hypothesis LO : lo <= bv_unsigned sp - PCOMMON_STACK.

Lemma printf_common_u00cc_raw :
evt asegs (rpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - PCOMMON_STACK, bv_unsigned sp)] lo m
(fun _ _ => True))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0x23700) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz pcommon_entry) fc None m (seg_rom asegs)).
Proof.
pose proof CEIL as CEIL'. unfold PCOMMON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose_str FMT 0x23700 [92; 117; 48; 48; 37; 99; 37; 99; 0] MI.
unfold pcommon_entry in *.
eapply evt_cut; [ eapply pc_setup_g9 with (c := 92) (l := [117; 48; 48; 37; 99; 37; 99]);
[exact ISH0 | exact ST | exact MI | exact CEIL | lia | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity] | ].
intros ms' (m' & junk1 & junk2 & -> & FRa & DIR & FRb & ST' & MUc & WMc & MIc).
transport_after_call asegs m m' MUc WMc. clear MUc WMc.
try clear ST. try clear MI. rename ST' into ST. rename MIc into MI.

scan_pct 4%nat 0%nat [92; 117; 48; 48; 37; 99; 37; 99; 0] 0x23700.

run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.
run. call_strchr 0x1c77b [106; 122; 116; 76; 113].
run. call_strchr 0x14816 [99; 67; 115; 83].
run. call_strchr 0x1acf4 [67; 83].
run. call_strchr 0x1088e [99; 115; 91].
run. call_strchr 0x140d6 [115; 83].
run. call_strchr 0x16dde [97; 65; 101; 69; 102; 70; 103; 71].

dir_flat DIR.
run. call_memset DIR.
run. call_strchr 0x15cb0 [39; 45; 43; 32; 35; 48]. dir_L2c DIR.
run. call_strchr 0x1c77b [106; 122; 116; 76; 113].
run. call_strchr 0x14816 [99; 67; 115; 83].
run. call_strchr 0x1acf4 [67; 83].
run. call_strchr 0x1088e [99; 115; 91].
run. call_strchr 0x140d6 [115; 83].
run. call_strchr 0x16dde [97; 65; 101; 69; 102; 70; 103; 71].

dir_flat DIR.
run.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of FRa with rw_cells _ _ ?A ?ca => lazymatch type of DIR with rw_cells _ _ _ ?cd => lazymatch type of FRb with rw_cells _ _ _ ?cb =>
assert (FR : rw_cells asegs mc A (ca ++ cd ++ cb))
by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRa|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; cbn [cells_size csize Nat.add app];
[eapply rwc_eq; [exact DIR| lia] | eapply rwc_eq; [exact FRb| lia]]);
clear FRa DIR FRb; cbn [app] in FR
end end end end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact I].
Qed.
End S.

Theorem printf_common_u00cc {BAND : Band} : pcommon_stmt 0x23700.
Proof. unfold pcommon_stmt. intros. apply printf_common_u00cc_raw; assumption. Qed.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mqc.
Import Qc27 Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF QoNr.Mq0. Import QdZp.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import Qu3b.Mq6.
Import QTVW.Mq8 Qu3b.Mq5 QYyZ.Mq9 QFd5 QnRU.Mqf QnRU QteI.Mqb.
Import QCNF.Mq2 QQNJ.Mq9.
Import QMPy.Mq0.
Import QFy3. Import QC9y.Mq0.
Import Qr5k.Mq3 QbPx_c1 QCqp Qr5k Qi1S.Mq3 QHRw Qvzz.
Import Q0z1.
Import QlES.
Import QXE1.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).

Lemma qslow_loop_vsn : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a4', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz e) (wz e) (wz 0) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz (0x5453c + 16)) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz p) (wz e) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x5453c) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind;
intros until P; intros ZR A0 C1 C2 EK HK K; rewrite ?KHI_eq in EK;
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B;
step; stp; stp; step; destruct (Z_lt_le_dec (p + 1) e) as [X1|X1];
[ ifz; eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K]
| ifz; replace (p + 1) with e by lia; apply K ].
Qed.

Section T.
Context {BAND : Band}.
Variables (sp0 : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rs7 rs6 rs5 rs4 rs3 rs2 rs1 rs0 rra x1 x2 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : mem) (D n r AFMT : Z) (jA jB : list byte) (P : machine_state -> Prop).
Let w := Z.min n (r + 1).
Hypothesis SP0 : 2256 <= sp0 /\ sp0 <= 2^47.
Hypothesis RNG : rng_ok m D w.
Hypothesis W1 : 1 <= w <= 64.
Hypothesis Hr : 0 <= r < 2^31 - 1.
Hypothesis Hn : 1 <= n < 2^63.
Hypothesis SB : shadow_base asegs m.
Hypothesis MI : mem_inv asegs m.
Hypothesis FRi : rw_cells asegs m (sp0 + -2128)
[CB 1936 jA; C8 x1; C8 x2; CB 8 jB; C8 rs7; C8 rs6; C8 rs5; C8 rs4; C8 rs3; C8 rs2; C8 rs1; C8 rs0; C8 rra].
Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
evt asegs P (MS (mkR rra (wz (sp0 + -96)) gp tp t0' t1' t2' rs0 rs1 (wz r) a1' a2' a3' a4' a5' a6' a7' rs2 rs3 rs4 rs5 rs6 rs7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft (ret_pc rra) fc None m (seg_rom asegs)).

Lemma vsn_icpt_tail :
evt asegs P (MS (mkR (wz 345012) (wz (sp0 + -2256)) gp tp t0 t1 t2 (wz (sp0 + -96)) (wz AFMT) (wz r) a1 a2 a3 a4 a5 a6 a7
(wz D) (wz n) (wz 1588456) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (wz 345016) fc None m (seg_rom asegs)).
Proof.
destruct RNG as (P0 & P47 & SO & BIG & NB).
pose proof (SO ltac:(lia)) as SO2. destruct (NB ltac:(lia)) as [[w1 WD1] [w2 WD2]].
destruct SB as [K5a K5]. unfold A_SHADOW_GOT, A_SHADOW_CELL, A_SHADOW_OFS in K5a, K5.
step.
rewrite (unsigned_lit r) by lia. rewrite QDM6.swrap32_small by lia.
step.

assert (CHK : forall (b1 b2 b3 b4 b5 c5 : word),
evt asegs P (MS (mkR (wz 345012) (wz (sp0 + -2256)) gp tp t0 t1 t2 (wz (sp0 + -96)) (wz w) (wz r) b1 b2 b3 b4 b5 a6 a7
(wz D) (wz n) (wz 1588456) c5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (wz 0x543d4) fc None m (seg_rom asegs))).
{ intros b1 b2 b3 b4 b5 c5.
step. step.
step. unfold_cond. fold_lit_ux. rewrite u_nm65 by lia.
replace (18446744073709551551 <? 18446744073709551551 + w) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
step. stp. step. stp. step. step. step. stp. stp.
rewrite (unsigned_lit D), (unsigned_lit (D + w + -1)) by lia.
replace (2147450880 + D ≫ 3) with (SH D) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (D + w + -1) ≫ 3) with (SH (D + w - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH D /\ SH D <= SH (D + w - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH D)), (unsigned_lit (SH (D + w - 1))) by lia. rewrite !land_m8 by lia.
replace (SH D - SH D mod 8) with (8 * (SH D / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (D + w - 1) - SH (D + w - 1) mod 8) with (8 * (SH (D + w - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.
destruct (shadow_ok_last _ D w SO2 ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ D w SO2 ltac:(lia)) as ZH.

lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a1'' a3'' a4'' a5'' : word,
ms1 = MS (@bvmap_set 5 word 11 a1'' (@bvmap_set 5 word 13 a3'' (@bvmap_set 5 word 14 a4'' (@bvmap_set 5 word 15 a5'' R)))) FF (wz 0x5441c) fcc rv mm ro))
end.
{ step. if_cases Hq.
-
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (D + w + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (D + w - 1)) (SH D)) as [X1|X1].
+ ifz. replace (SH D) with (SH (D + w - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop_vsn (Z.to_nat (SH (D + w - 1) - SH D)) (SH D)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a4x. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a1'' & a3'' & a4'' & a5'' & ->). simp_regs.

istep. do 9 istep. istep. step.
apply K. }

step. unfold_cond. rewrite (unsigned_lit n), (unsigned_lit (r + 1)) by lia.
destruct (Z_le_gt_dec (r + 1) n) as [LE | GT].
-
replace (n <? r + 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
assert (EW : w = r + 1) by (unfold w; lia).
step. step. step. step.
step. rewrite (unsigned_lit D), zb_lxor_ones by lia. rewrite <- EW. ifz.
apply CHK.
-
replace (n <? r + 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
assert (EW : w = n) by (unfold w; lia).
step. step. step.
step. rewrite (unsigned_lit D), zb_lxor_ones by lia. ifz.
rewrite EW in CHK. apply CHK.
Qed.
End T.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFd5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFd5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMPy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMPy.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFy3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFy3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5k.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbPx_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbPx_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5k. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi1S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi1S.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHRw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHRw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvzz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvzz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXE1.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells asegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells asegs m A (pre ++ C4 v' :: post).
Proof.
intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
- destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 [_ W2]]. apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
- rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.

Ltac c4_eqv H k v' :=
lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
let H' := fresh in
pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
end end.

Section VsnProof.
Context {BAND : Band}.
Variables (AFMT : Z) (fmt : list Z).
Hypothesis PCOMMON : pcommon_stmt AFMT.

Theorem vsnprintf_proof : vsnprintf_stmt AFMT fmt.
Proof using PCOMMON BAND.
unfold vsnprintf_stmt. intros until o. cbv zeta.
intros -> -> -> -> DST ISHm BY HF P1 VAA SAOK MODEL FPC ROOM Hn ST LO GLO QHI SSP MI FRM HA0 HA HSZ QVA VAHI DD1 DDV DAPP RD.
unfold VSN_DEPTH, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, vsnprintf_entry in *.
assert (CEIL : band_lo <= lo) by exact GLO.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *. unfold dapp in DAPP.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (ISHc : forall mm, munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m mm -> wmono asegs m mm -> ISH mm).
{ intros mm MUx WMx. eapply ISH_munch_app; [exact ISHm | exact MUx | exact WMx |].
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
pose proof ISHm as (ASH & RC & SB).
pose proof (rt_161720 _ RC) as K18. pose proof (rt_157bb0 _ RC) as K7. pose proof (rt_1f25bc _ RC) as K22. pose proof (rt_159c68 _ RC) as K17.
carve_frame 304%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 304 _ _ [232;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR.
do 12 zs.
zs. zs. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
zs. zs. zs. zs. zs.

replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
zs. zs. zs. zs. zs.
match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -304 + Z.of_nat 232)%Z with (bv_unsigned sp + -72)%Z in FRv by lia.

zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ISHc mc MU WM) as ISH1 end.
call_u (memset_icpt_spec (bv_unsigned sp + -304) 0 232 lo j0);
[ exact FZ | assumption | lia | lia | unsigned_lits; eassumption | exact CEIL | unsigned_lits; unfold MEMSET_ICPT_STACK; lia | unsigned_lits; lia
| exact (proj2 (proj2 ISH1)) | exact (proj1 (proj2 ISH1))
| apply (rng_ok_of_ash _ _ _ (proj1 ISH1)); [unfold szone; right; left; lia | lia] |].
clear ISH1.
match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB _ (repeat _ _)] |- _ => rename H into FZ' end.

pose proof (rw_cells_recast _ _ _ (gfile_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) 0 ++ snfile_rest 0) FZ'
ltac:(cbn [cells_wf cell_wf gfile_cells snfile_rest app]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
unfold gfile_cells, snfile_rest in FC. cbn [app] in FC.
do 10 zs.
c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).

pose proof (rw_CB_length _ _ _ _ DST) as LJ.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
pose proof (u8arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
pose proof (u8arr_write asegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST. clear DA2.
zs. zs. zs.

apply (proj1 (rw_cells_app asegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FC. destruct FC as [FH FR]. cbn [cells_size csize Nat.add app] in FR.
replace (bv_unsigned sp + -304 + Z.of_nat 148)%Z with (bv_unsigned sp + -304 + 148)%Z in FR by lia.
apply (proj1 (rw_cells_app asegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -72 + Z.of_nat 16)%Z with (bv_unsigned sp + -56)%Z in FRv by lia.
zs.
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. carve_frame 48%nat ST. rename FR0 into FRf.
do 9 istep.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. istep. step. if_lit. istep. istep. istep. istep. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ISHc mc MU WM) as ISH2 end.
pose proof PCOMMON as PCD. unfold pcommon_stmt, PCOMMON_STACK, pcommon_entry in PCD.
call_u PCD; [ exact ISH2 | assumption | unsigned_lits; exact ST | exact CEIL | unsigned_lits; lia |].
clear PCD.
clear ISH2.
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.

istep. istep. istep. istep. istep. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (ISHc mc MU WM) as ISH3 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RD3 : (0 < Z.of_nat (length o))%Z -> rng_ok mc D (Z.of_nat (length o))) end.
{ intros K. eapply rng_ok_munch; [exact (RD K) | exact MU | exact WM |].
pose proof (proj1 (proj2 (RD K))) as D47.
repeat (apply Forall_cons; [cbn [fst snd]; rewrite !SH_eq; Z.div_mod_to_equations; lia|]). apply Forall_nil. }
pose proof vfprintf_sn_proof as VF. unfold vfprintf_sn_stmt in VF.
eapply evt_cut.
{ eapply VF with (Fp := bv_unsigned sp + -304) (CK := bv_unsigned sp + -72) (D := D) (n := n + -1) (bufp := bv_unsigned sp + -49) (A := AFMT) (VA := VA)
(dn := dn) (junkd := upd junkd (Z.to_nat 0) (Z_to_bv 8 0)) (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength, dapp.
all: try reflexivity.
all: try lia.
- unfold snfile_head, gfile_cells, sn_write_entry. exact FH.
- unfold snfile_rest. exact FR.
- exact CKC.
- exact DST.
- exact ISH3.
- exact BY.
- exact HF.
- exact P1.
- exact VAA.
- apply sargs_args_ok. exact SAOK.
- exact MODEL.
- exact FPC.
- exact ST.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM.
- exact HSZ.
- exact RD3. }
cbv beta. intros ms' P. clear VF.
unfold vfprintf_sn_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & fjunk & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SSP3 & DST3 & CK3 & FJ3).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
fix_ret.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

do 5 istep. step. release_frame FRf ST3 (bv_unsigned sp + -304).
try fix_ret.

lazymatch goal with H : rw_cells _ _ 6575456 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 7 zs.
lazymatch goal with FJ : rw_cells _ ?mm (bv_unsigned sp + -304)%Z _, CK : rw_cells _ ?mm (bv_unsigned sp + -72)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -56)%Z _ |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -304) ([CB 232 fjunk] ++ [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n + -1 - zlength o))] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FJ|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact CK | lia] |];
cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear FJ CK FR ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|].
split; [split; [exact SSP1 | exact SSP2]|].
rewrite upd_firstn_skipn in DST3 by (rewrite LJ; lia). change (Z.to_nat 0) with 0%nat in DST3.
change (firstn 0 junkd) with (@nil byte) in DST3. rewrite app_nil_l in DST3.
change (skipn (S (length o)) (Z_to_bv 8 0 :: skipn 1 junkd)) with (skipn (length o) (skipn 1 junkd)) in DST3.
rewrite skipn_skipn, Nat.add_1_r in DST3. exact DST3.
Qed.
End VsnProof.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c8 X1bj X1cc X1bu X1bq X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require X1bk X1c5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1rd X1oc X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qr X0pv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1fd X1en X1fl X1ei. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1eh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fo X1ea X1jh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1jg. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fr X1fp X1gk X1je X1ji X1gl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1jf.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cb.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- X1qx.implM _ _ _ _ _ => unfold X1qx.implM; apply impl_from_evt | |- X1bs.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- X1bs.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (X1qx.implM rsegs c s Q ms) | _ => idtac end.

Section StderrSinkProofs.
Context {RCEIL : RunCeiling}.
Context {St : Type}.
Variable B : Z.
Let SINK := SINK_stderr (St:=St) B.

Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
Proof using .
unfold sink_frame_stmt. intros W m m' [buf st] sfH_; first [ sf_destruct 11%nat sfH_ as flags mode tail rest FC FL32 FL8 BUF LEN BHI BLO | sf_fb; destruct sfH_ as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO) ]; intros MU WM D1 D2.
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact (rest) | ] | sf_fb; exists flags, mode, tail, rest ].
split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | exact BLO]]]]]].
- eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
Proof using B.
unfold sink_flags_stmt. intros m [buf st] sfH_; first [ sf_destruct 7%nat sfH_ as flags mode tail rest FC FL32 _ | sf_fb; destruct sfH_ as (flags & mode & tail & rest & FC & FL32 & _) ].
exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
rewrite <- land_mod_low by lia. exact FL32.
Qed.
End StderrSinkProofs.

Lemma flags40_8 : forall f, Z.land f 40 = 0 -> Z.land f 8 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma flags40_32 : forall f, Z.land f 40 = 0 -> Z.land f 32 = 0.
Proof. intros f. apply land_sub_mask. reflexivity. Qed.
Lemma sflags_noerr_8 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 ->
Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_8. exact H.
Qed.
Lemma sflags_noerr_32 : forall (flags : word),
Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 32 = 0.
Proof.
intros flags. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 32) with 0. apply Z.land_0_r.
Qed.
Lemma sflags_olderr0 : forall (flags : word), Z.land (bv_unsigned flags) 40 = 0 -> Z.land (bv_unsigned (sx32 flags)) 32 = 0.
Proof. intros flags H. rewrite land_low7, sx32_mod128, <- land_low7 by lia. apply flags40_32. exact H. Qed.
Lemma sflags_final_40 : forall (flags2 : word), Z.land (bv_unsigned flags2) 32 = 0 -> Z.land (bv_unsigned flags2) 8 = 0 ->
Z.land (Z.lor (bv_unsigned (sx32 flags2)) 0) 40 = 0.
Proof.
intros flags2 H32 H8. rewrite Z.lor_0_r. rewrite land_low7, sx32_mod128, <- land_low7 by lia.
replace 40 with (Z.lor 32 8) by reflexivity. rewrite Z.land_lor_distr_r, H32, H8. reflexivity.
Qed.

Section Stderr.
Context {RCEIL : RunCeiling}.
Context {St : Type}.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ Fok10 F Ft
/\ stk rsegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary.

Definition vfprintf_stderr_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
stderr_wfile m ->
bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk rsegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
X1qx.implM rsegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3519c) fc None m (seg_rom rsegs)).

Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
Proof using FLS FWE.
unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [X1fd.rsegs] in SSP1, SSP2. fold X1ff.rsegs in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
first [ sf_destruct 7%nat SF as flags mode e wend tail FC FL40 | sf_fb; destruct SF as (flags & mode & e & wend & tail & FC & FL40) ]. unfold file_cells in FC.

apply (printf_model_outs rsegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
match goal with |- X1qx.implM _ _ _ ?Q _ => set (QQ := Q) end.
ienter.
carve_frame 368%nat ST.
do 12 zs. do 14 zs.

pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
eapply evt_cut.
{ eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
[ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
| unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
first [ sf_destruct 21%nat P as x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m' -> MUc WMc MIc STc SSPc | sf_fb; destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc) ].
rewrite !unsigned_lit in MUc, STc by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [X1fd.rsegs] in SSP1, SSP2. fold X1ff.rsegs in SSP1, SSP2.

zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
do 10 zs.
pose proof towrite_proof as TW. unfold towrite_stmt in TW.
eapply evt_cut.
{ eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
cbv beta. intros ms' P. clear TW.
first [ sf_destruct 21%nat P as x5' x6' x7' c1 c2 c3 c4 c5 c6 c7 x28' x29' x30' x31' mode' m'' -> MUc WMc MIt FCt | sf_fb; destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt) ].
rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. do 6 zs.
set (B := bv_unsigned sp + -352) in *.

match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
apply (rw_cells_split_CB rsegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).

ileave.
pose proof (printf_core_proof (list Z * St) RSTDERR B 80 (SINK_stderr B) TOPOK_none OUT_stderr (OUTFP_stderr (St:=St))
(stderr_sink_frame B) (stderr_sink_flags B) (topok_none) (FWE St B)) as PC2.
unfold printf_core_stmt in PC2.
assert (FR3 : 0 <= Z.land (bv_unsigned (sx32 flags)) 18446744073709551583 < 2^64).
{ pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
eapply implM_bind.
{ eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
all: try lia. all: try exact I.
- unfold SINK_stderr. cbn [fst].
first [ unshelve sf_eexists 4%nat; [ exact ((Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) | exact (mode') | exact (tail) | exact (jb) | ] | sf_fb; exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb ].
change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
split; [exact FCt|]. rewrite unsigned_lit by lia.
split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
unfold zlength. rewrite LJB. unfold GLOBALS_TOP. subst B. lia.
- exact BY.
- exact HF.
- reflexivity.
- exact APC.
- exact VAA.
- cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
- rewrite FPC. apply Forall_nil.
- exact STc.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM. }
cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
first [ sf_destruct 29%nat P as y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' apv m3 -> MUc WMc MI3 FRM' FOK ST3 SNK3 SSP3 APC3 Hr | sf_fb; destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr) ].
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc end.
ienter. fix_ret.
pose proof SNK3 as SNK3'. first [ sf_destruct 11%nat SNK3' as flags2 mode2 tail2 rest2 FC3 FL32 FL8 BUF3 LEN3 BHI3 BLO3 | sf_fb; destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3) ]. cbn [fst] in FC3, BUF3, LEN3.
unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [X1fd.rsegs] in SSP1, SSP2. fold X1ff.rsegs in SSP1, SSP2.

zs. zs. zs. if_lit.
zs. zs. zs. zs. zs.
ileave. unfold FLUSH_stderr, X1qx.implM. cbv beta iota.
pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 1024) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
eapply impl_ebind.
{ unfold X1qx.implM in FL.
eapply FL with (lo := bv_unsigned sp + -368 - 1024) (canary := canary); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
all: try lia.
- exact SNK3.
- reflexivity.
- reflexivity.
- reflexivity.
- exact ST4b.
- split; [exact SSP1 | exact SSP2].
- assumption. }
cbv beta. intros [[] st4] ms' P.
unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
first [ sf_destruct 23%nat P as z5 z6 z7 e0 e1 e2 e3 e4 e5 e6 e7 z28 z29 z30 z31 m4 -> MUc WMc MI4 ST4b' SNK4 SSP4 | sf_fb; destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4) ].
lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m4 MUc WMc; clear MUc WMc end.
apply impl_ret_intro. cbn [snd]. fix_ret.
cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
first [ sf_destruct 11%nat SNK4 as flags4 mode4 tail4 rest4 FC4 FL32' FL8' BUF4 LEN4 _ _ | sf_fb; destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _) ]. cbn [fst snd] in FC4, BUF4, LEN4.
unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [X1fd.rsegs] in SSP1, SSP2. fold X1ff.rsegs in SSP1, SSP2.

do 9 zs.

zs. zs. zs. zs. zs. zs. zs. zs. if_lit.

zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.

match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 1024)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 1024)%Z _ |- _ =>
pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
assert (FALL : rw_cells rsegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
[ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact A1|];
apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear A1 A2 BU FR ] end.
cbn [app] in FALL.
release_frame FALL ST5 (bv_unsigned sp).
apply evt_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST5|].
split.
{ first [ unshelve sf_eexists 5%nat; [ exact ((Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32)))) | exact (mode4) | exact (0) | exact (0) | exact (tail4) | ] | sf_fb; exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4 ].
split; [unfold file_cells; exact FC4|].
rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
split; [exact SSP1 | exact SSP2].
Qed.

Definition fprintf_gen_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
stderr_wfile m ->
bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (q - 80 - 352) 80 m lo q (q - 80 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk rsegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
X1qx.implM rsegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34aac) fc None m (seg_rom rsegs)).

Theorem fprintf_gen_proof : fprintf_gen_stmt.
Proof using FLS FWE.
unfold fprintf_gen_stmt. intros until canary. cbv zeta.
intros -> -> SF BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
unfold FPRINTF_DEPTH, VF_FRAME, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [X1fd.rsegs] in SSP1, SSP2. fold X1ff.rsegs in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
first [ sf_destruct 7%nat SF as flags mode e wend tail FC FL40 | sf_fb; destruct SF as (flags & mode & e & wend & tail & FC & FL40) ]. unfold file_cells in FC.
match goal with |- X1qx.implM _ _ _ ?Q _ => set (QQ := Q) end.
ienter.
carve_frame 80%nat ST.
do 17 zs.
apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.

ileave.
pose proof vfprintf_stderr_proof as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
eapply implM_post_evt.
{ eapply VF with (A := A) (VA := bv_unsigned sp + -48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
all: try reflexivity. all: try lia.
- first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [unfold file_cells; exact FC | exact FL40].
- exact BY.
- exact HF.
- exact P1.
- exact VAA.
- eapply args_ok_vf; [| | exact MU]; [|lia].
replace (bv_unsigned sp + -80 - 352)%Z with (bv_unsigned sp - 80 - 352)%Z by lia.
replace (bv_unsigned sp + -80 - 368)%Z with (bv_unsigned sp - 80 - 368)%Z by lia. exact AOK.
- exact PP.
- exact FPC.
- exact ST.
- split; [exact SSP1 | exact SSP2].
- exact MI.
- exact FRM. }
cbv beta. intros [] [b4 st4] ms' P. clear VF MU1. cbn [snd] in P.
unfold vfprintf_stderr_post in P. rewrite !unsigned_lit in P by lia.
first [ sf_destruct 27%nat P as y5 y6 y7 d0 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' m3 -> MUc WMc MI3 FRM' FOK ST3 SF3 SSP3 | sf_fb; destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3) ].
lazymatch type of MUc with munch _ ?mm _ => transport_after_call rsegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
change X1fd.rsegs with X1ff.rsegs in SSP1, SSP2.

zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
zs. zs. zs. zs.
lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -48)%Z ?rest |- _ =>
assert (FALL : rw_cells rsegs mm (bv_unsigned sp + -80) (hd ++ rest));
[ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
| clear FR VAC ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. subst QQ. cbn [fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|]. split; [exact SF3|]. split; [exact SSP1 | exact SSP2].
Qed.
End Stderr.

Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
intros l H. rewrite forallb_forall in H. apply Forall_forall. intros c Hc. specialize (H c Hc).
apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma vf_to_diag_post : forall St ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (st st' : St) ms,
vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms -> st' = st ->
fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt st' ms.
Proof.
intros until ms. intros sfH_; first [ sf_destruct 27%nat sfH_ as x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 Ft fc' m' E MU WM MI FRM FOK ST SF SSP | sf_fb; destruct sfH_ as (x5 & x6 & x7 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E & MU & WM & MI & FRM & FOK & ST & SF & SSP) ]; intros Est.
first [ unshelve sf_eexists 18%nat; [ exact (x5) | exact (x6) | exact (x7) | exact (a0) | exact (a1) | exact (a2) | exact (a3) | exact (a4) | exact (a5) | exact (a6) | exact (a7) | exact (x28) | exact (x29) | exact (x30) | exact (x31) | exact (Ft) | exact (fc') | exact (m') | ] | sf_fb; exists x5, x6, x7, a0, a1, a2, a3, a4, a5, a6, a7, x28, x29, x30, x31, Ft, fc', m' ].
repeat (split; [assumption|]). exact Est.
Qed.

Theorem fprintf_diag_proof : forall St : Type, @fprintf_diag_stmt St.
Proof.
intros St. unfold fprintf_diag_stmt. intros d. intros until canary. intros FWE FLS SF Ha0 DA ST LO GLO QHI SSP MI FRM.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
unfold FPRINTF_DEPTH, GLOBALS_TOP in *.

assert (BR : forall ps, X1qx.implM rsegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34aac) fc None m (seg_rom rsegs)) ->
X1qx.implM rsegs (stderr_fprintf ps) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34aac) fc None m (seg_rom rsegs))).
{ intros ps H. unfold stderr_fprintf, X1qx.implM in *.
eapply impl_epost_mono.
- eapply (stderr_bridge rsegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
eapply impl_mono; [eapply (impl_tforall rsegs (at_node rsegs) _ _ _ _ (outsk_flush_leaves ps [] st)); exact H|].
intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
- intros [[] s'] ms' H'. exact H'. }
pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG. unfold VF_FRAME, FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in FG.
destruct d as [argv0 | path | path | | | |]; cbn [diag_args] in DA; try contradiction; unfold s_diag; apply BR; clear BR.
- first [ sf_destruct 8%nat DA as Ha1 slack BY HF SLK LEN DJ GA | sf_fb; destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA) ]. unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length argv0) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
eapply FG with (fmt := FMT_usage) (args := [PA_s argv0]) (A := A_FMT_usage); clear FG;
first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
| apply printf_pieces_usage; unfold zlength, INT_MAX in *; lia
| apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_usage; lia | vm_compute; discriminate]
| apply forall_range_b; vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
| split; [exact (proj1 SSP) | exact (proj2 SSP)]
| lia
| reflexivity
| vm_compute; discriminate ].
- first [ sf_destruct 8%nat DA as Ha1 slack BY HF SLK LEN DJ GA | sf_fb; destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA) ]. unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
eapply FG with (fmt := FMT_cannot_open) (args := [PA_s path]) (A := A_FMT_cannot_open); clear FG;
first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
| apply printf_pieces_cannot_open; unfold zlength, INT_MAX in *; lia
| apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_cannot_open; lia | vm_compute; discriminate]
| apply forall_range_b; vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
| split; [exact (proj1 SSP) | exact (proj2 SSP)]
| lia
| reflexivity
| vm_compute; discriminate ].
- first [ sf_destruct 8%nat DA as Ha1 slack BY HF SLK LEN DJ GA | sf_fb; destruct DA as (Ha1 & slack & BY & HF & SLK & LEN & DJ & GA) ]. unfold GLOBALS_TOP in GA.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length path) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
eapply FG with (fmt := FMT_read_error) (args := [PA_s path]) (A := A_FMT_read_error); clear FG;
first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
| apply printf_pieces_read_error; unfold zlength, INT_MAX in *; lia
| apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_read_error; lia | vm_compute; discriminate]
| apply forall_range_b; vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
| split; [exact (proj1 SSP) | exact (proj2 SSP)]
| lia
| reflexivity
| vm_compute; discriminate ].
- destruct DA as [Ha1 Hu]. pose proof (bv_unsigned_in_range 64 a2) as R2.
eapply FG with (fmt := FMT_too_big) (args := [PA_u 67108864]) (A := A_FMT_too_big); clear FG;
first [ exact Ha0 | exact Ha1 | exact SF | exact ST | exact MI | exact FRM
| apply printf_pieces_too_big
| apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_too_big; lia | vm_compute; discriminate]
| apply forall_range_b; vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [split; [lia | exact Hu] | exact I]
| split; [exact (proj1 SSP) | exact (proj2 SSP)]
| lia
| reflexivity
| vm_compute; discriminate ].
Qed.

Section StderrConsumers.
Context {RCEIL : RunCeiling}.
Context {St : Type}.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

#[using="FWE FLS"] Theorem fprintf_stderr_proof :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z) (lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A ->
stderr_wfile m ->
bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (q - 80 - 352) 80 m lo q (q - 80 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk rsegs m lo q -> (lo <= q - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
X1qx.implM rsegs (stderr_fprintf ps) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34aac) fc None m (seg_rom rsegs)).
Proof.
intros until canary. cbv zeta. intros Ha0 Ha1 SF BY HF P1 AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA.
unfold stderr_fprintf, X1qx.implM.
eapply impl_epost_mono.
- eapply (stderr_bridge rsegs ps [] st (fun s' ms' => fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st tt s' ms')).
eapply impl_mono; [eapply (impl_tforall rsegs (at_node rsegs) _ _ _ _ (outsk_flush_leaves ps [] st))|].
+ pose proof (@fprintf_gen_proof St FWE FLS) as FG. unfold fprintf_gen_stmt in FG. cbv zeta in FG.
eapply FG; eassumption.
+ intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. eapply vf_to_diag_post; [exact H1 | exact H2].
- intros [[] s'] ms' H'. exact H'.
Qed.

Definition cstr_arg (m : mem) (w : word) (s : list Z) (lo sp : Z) : Prop :=
exists slack : list byte,
bytes_at rsegs m (bv_unsigned w) (zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned w + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s < INT_MAX - 256)
/\ (0 < bv_unsigned w)
/\ (bv_unsigned w + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned w)
/\ (GLOBALS_TOP <= bv_unsigned w \/ bv_unsigned w + zlength s + 1 + zlength slack <= STATIC_SPLIT).

Ltac fmt_static A_FMT FMT :=
apply fmt_bytes_at; [eassumption | vm_compute; reflexivity | unfold A_FMT; lia | unfold A_FMT, FMT, zlength; cbn - [Z.add Z.le]; lia].

#[using="FWE FLS"] Theorem fprintf_notify_proof :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (s : list Z) (lo : Z) (canary : word),
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A_FMT_notify -> cstr_arg m a2 s lo (bv_unsigned sp) ->
stderr_wfile m ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
X1qx.implM rsegs (s_notify s) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34aac) fc None m (seg_rom rsegs)).
Proof.
intros until canary. intros Ha0 Ha1 sfH_; first [ sf_destruct 8%nat sfH_ as slack BY HF SLK LEN POS DJ GA | sf_fb; destruct sfH_ as (slack & BY & HF & SLK & LEN & POS & DJ & GA) ]; intros SF ST LO GLO QHI SSP MI FRM.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length s) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
unfold s_notify.
eapply fprintf_stderr_proof with (fmt := FMT_notify) (args := [PA_s s]) (A := A_FMT_notify);
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, VF_FRAME, zlength;
[ exact Ha0 | exact Ha1 | exact SF
| fmt_static A_FMT_notify FMT_notify
| apply forall_range_b; vm_compute; reflexivity
| vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
| apply printf_pieces_notify; unfold zlength, INT_MAX in *; lia
| vm_compute; reflexivity
| exact ST | lia | lia | lia | exact SSP | exact MI | exact FRM
| unfold A_FMT_notify; lia
| unfold A_FMT_notify, FMT_notify, zlength; cbn -[Z.add Z.le]; lia ].
Qed.

#[using="FWE FLS"] Theorem fprintf_warning_proof :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (s : list Z) (lo : Z) (canary : word),
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A_FMT_warning -> cstr_arg m a2 s lo (bv_unsigned sp) ->
stderr_wfile m ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
X1qx.implM rsegs (s_warning s) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34aac) fc None m (seg_rom rsegs)).
Proof.
intros until canary. intros Ha0 Ha1 sfH_; first [ sf_destruct 8%nat sfH_ as slack BY HF SLK LEN POS DJ GA | sf_fb; destruct sfH_ as (slack & BY & HF & SLK & LEN & POS & DJ & GA) ]; intros SF ST LO GLO QHI SSP MI FRM.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length s) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
unfold s_warning.
eapply fprintf_stderr_proof with (fmt := FMT_warning) (args := [PA_s s]) (A := A_FMT_warning);
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, VF_FRAME, zlength;
[ exact Ha0 | exact Ha1 | exact SF
| fmt_static A_FMT_warning FMT_warning
| apply forall_range_b; vm_compute; reflexivity
| vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [|exact I]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
| apply printf_pieces_warning; unfold zlength, INT_MAX in *; lia
| vm_compute; reflexivity
| exact ST | lia | lia | lia | exact SSP | exact MI | exact FRM
| unfold A_FMT_warning; lia
| unfold A_FMT_warning, FMT_warning, zlength; cbn -[Z.add Z.le]; lia ].
Qed.

#[using="FWE FLS"] Theorem fprintf_warning_int_proof :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (s : list Z) (i : Z) (lo : Z) (canary : word),
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A_FMT_warning_int -> cstr_arg m a2 s lo (bv_unsigned sp) ->
(-2^31 <= i < 2^31) -> (bv_unsigned a3 mod 2^32 = i mod 2^32) ->
stderr_wfile m ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
X1qx.implM rsegs (s_warning_int s i) st
(fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34aac) fc None m (seg_rom rsegs)).
Proof.
intros until canary. intros Ha0 Ha1 sfH_; first [ sf_destruct 8%nat sfH_ as slack BY HF SLK LEN POS DJ GA | sf_fb; destruct sfH_ as (slack & BY & HF & SLK & LEN & POS & DJ & GA) ]; intros Hi Ha3 SF ST LO GLO QHI SSP MI FRM.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length s) as LZS. rewrite length_app, LZS in AB. cbn [length] in AB. unfold zlength in *.
unfold s_warning_int.
eapply fprintf_stderr_proof with (fmt := FMT_warning_int) (args := [PA_s s; PA_i i]) (A := A_FMT_warning_int);
unfold FPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, VF_FRAME, zlength;
[ exact Ha0 | exact Ha1 | exact SF
| fmt_static A_FMT_warning_int FMT_warning_int
| apply forall_range_b; vm_compute; reflexivity
| vm_compute; reflexivity
| cbn [args_ok arg_ok]; split; [| split; [split; [exact Hi | exact Ha3] | exact I]]; exists slack; unfold zlength; repeat (split; [first [exact BY | exact HF | exact SLK | lia] |]); lia
| apply printf_pieces_warning_int; [unfold zlength, INT_MAX in *; lia | exact Hi]
| vm_compute; reflexivity
| exact ST | lia | lia | lia | exact SSP | exact MI | exact FRM
| unfold A_FMT_warning_int; lia
| unfold A_FMT_warning_int, FMT_warning_int, zlength; cbn -[Z.add Z.le]; lia ].
Qed.
End StderrConsumers.

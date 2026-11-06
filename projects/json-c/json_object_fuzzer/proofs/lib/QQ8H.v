(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs QCiC Qpj5 QCNF QoNr QdZp Qk8e QHig Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho Qu3b QnRU QteI QoBx Qs9x QC9y QQNJ Q8zl QnaW QcfN QkZz QpzM Q0z1 QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp Qk8e.Mq0.
Import QHig QwAs.Mq2 Q0Do.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0.
Import QoBx Qu3b.Mq0.
Import Qs9x QC9y.
Import QQNJ.Mq1 Q8zl.Mq0 QnaW.Mq0.
Import QcfN.
Import QkZz.Mq0.
Import QpzM.Mq9.
Import QvG1.
Import Q0z1.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
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
Ltac ienter := lazymatch goal with |- Qpj5.Mq1.implM _ _ _ _ _ => unfold Qpj5.Mq1.implM; apply impl_from_evt | |- Qc6I.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- Qc6I.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Qpj5.Mq1.implM asegs c s Q ms) | _ => idtac end.

Ltac name_towers_vf H :=
repeat match type of H with
| context [CB ?n ?j] =>
lazymatch j with
| firstn _ _ => idtac | skipn _ _ => idtac
end;
let x := fresh "jk" in set (x := j) in H; clearbody x
end.
Ltac vf_split :=
lazymatch goal with FR : rw_cells _ _ _ [CB 368 _] |- _ =>
apply (rw_cells_split_CB asegs _ _ [] 368 _ _ [8;8;80;168;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
name_towers_vf FR end.

Section StderrSinkProofs.
Context {BAND : Band}.
Context {St : Type}.
Variable B : Z.
Let SINK := SINK_stderr (St:=St) B.

Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
Proof using  BAND.
unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO & B47 & ISHm) MU WM D1 D2 D3.
exists flags, mode, tail, rest.
split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | split; [exact BLO | split; [exact B47|]]]]]]]].
3:{ eapply ISH_munch; [exact ISHm| exact MU| exact WM|]. eapply Forall_impl; [| exact D3]. cbv beta. intros [lo' hi'] H. cbn in H |- *. unfold GLOBALS_TOP in H. idtac. lia. }
- eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
Proof using B BAND.
unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO & B47 & ISHm).
exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|]. split; [| exact ISHm].
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
Context {BAND : Band}.
Context {St : Type}.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary.

Definition vfprintf_stderr_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
stderr_wfile m -> ISH m ->
bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
Qpj5.Mq1.implM asegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd385c) fc None m (seg_rom asegs)).

Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
Proof using FLS FWE BAND.
unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
intros -> -> -> SF ISHm BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.

apply (printf_model_outs asegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
match goal with |- Qpj5.Mq1.implM _ _ _ ?Q _ => set (QQ := Q) end.
ienter.

call vf_saves; [exact ST | clear - LO GLO; unfold VF_DEPTH, PC_DEPTH in *; lia | exact GLO | exact MI | exact SSP1 | exact SSP2 | ].
lazymatch goal with H : stk _ ?mm lo (bv_unsigned sp + -368) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -368) (C8 _ :: _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into FR end.
try rename MI0 into MI.

pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
eapply evt_cut.
{ eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
[ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
| unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | unfold szone; lia | lia | lia ]. }
cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
rewrite !unsigned_lit in MUc, STc by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
do 10 zs.
pose proof towrite_proof as TW. unfold towrite_stmt in TW.
eapply evt_cut.
{ eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
cbv beta. intros ms' P. clear TW.
destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. do 6 zs.
set (B := bv_unsigned sp + -352) in *.

match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
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
exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
split; [exact FCt|]. rewrite unsigned_lit by lia.
split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
unfold zlength. rewrite LJB. unfold GLOBALS_TOP. repeat match goal with |- _ /\ _ => split end; try (subst B; lia).
eapply ISH_munch_zone; [exact ISHm| exact MU| exact WM| subst B; zforalls].
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
- exact FRM.
- unfold szone. lia. }
cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
ienter. fix_ret.
pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3 & B473 & ISH3). cbn [fst] in FC3, BUF3, LEN3.
unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. zs. zs. if_lit.
zs. zs. zs. zs. zs.
ileave. unfold FLUSH_stderr, Qpj5.Mq1.implM. cbv beta iota.
pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 3264) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
eapply impl_ebind.
{ unfold Qpj5.Mq1.implM in FL.
eapply FL with (lo := bv_unsigned sp + -368 - 3264) (canary := canary); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
all: try lia.
- exact SNK3.
- reflexivity.
- reflexivity.
- exact ST4b.
- split; [exact SSP1 | exact SSP2].
- assumption. }
cbv beta. intros [[] st4] ms' P.
unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc end.
apply impl_ret_intro. cbn [snd]. fix_ret.
cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

do 9 zs.

zs. zs. zs. zs. zs. zs. zs. zs. if_lit.

lazymatch goal with H : rw_cells _ _ 6565536 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.

match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 3264)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 3264)%Z _ |- _ =>
pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact A1|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear A1 A2 BU FR ] end.
cbn [app] in FALL.
release_frame FALL ST5 (bv_unsigned sp).
apply evt_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST5|].
split.
{ exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
split; [unfold file_cells; exact FC4|].
rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
split; [exact SSP1 | exact SSP2].
Qed.

End Stderr.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 QK3t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Qk8e.Mq0 Q6sh QKTr.
Import QTVW.Mq5 Qs9x QcfN. Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5.
Import Q9Ho.Mq0.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1 Qu3b.Mq0 QQNJ.Mq1 QnaW.Mq0 QkZz.Mq0 QpzM.Mq9 QQNJ.Mq3 QK3t.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Definition vprintf_stub : Z := 0x4f98c.
Definition vprintf_icpt_entry : Z := 0x53330.
Definition vfprintf_stub : Z := 0x4f990.
Definition vfprintf_icpt_entry : Z := 0x53e94.

Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono asegs m m' -> 0x6439e8 <= lo -> stdout_file m' so.
Proof.
intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
- eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.

Lemma out_pieces_outsk : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps,
out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. intros St get_so set_so ps. induction ps as [|p ps IH]; cbn [out_pieces outsk]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma ssp_cells_munch : forall m m' W canary, ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W -> ssp_cells m' canary.
Proof.
intros m m' W canary [G1 G2] MU WM HW. split.
- eapply rw_cells_apart; [exact G1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [H _]. cbn in *. lia.
- eapply rw_cells_apart; [exact G2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [_ H]. cbn in *. lia.
Qed.

Section Emit.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Theorem emit_printf_proof : emit_printf_stmt get_so set_so.
Proof.
unfold emit_printf_stmt. intros until v. intros GS SS FWX SF ISH0 HV HA1 ST LO GLO QHI SSP MI FRM.
unfold EMIT_DEPTH, GLOBALS_TOP in *.
assert (CEIL : band_lo <= lo) by (idtac; exact GLO).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m) as MU.
pose proof ISH0 as (ASH & RC & SB).

unfold s_emit, stdout_vprintf. rewrite out_pieces_outsk.
rewrite <- (outsk_OUT_stdout get_so set_so (pieces_emit_d v) (mret tt))
by (eapply Forall_impl; [| apply pieces_emit_d_short; exact HV]; cbv beta; intros; unfold OUT_MAX; lia).
eapply (implM_evt asegs). 2:{ intros ms' H; exact H. } cbv beta.

carve_frame 80%nat ST.
do 15 istep. rename FR into FRe.

step. carve_frame 48%nat ST. rename FR into FRv.
do 7 istep.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof printf_common_emit_d as PCD. unfold PCOMMON_STACK, pcommon_entry in PCD.
pose proof (rt_161720 _ RCc) as K18. pose proof (rt_157bb0 _ RCc) as K7. pose proof (rt_1f25bc _ RCc) as K22. pose proof (rt_159c68 _ RCc) as K17.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. istep. step. if_lit. istep. istep. istep. istep. step.

call_u PCD;
[ eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]
| assumption | unsigned_lits; exact ST | exact CEIL | unsigned_lits; lia |].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.

istep. istep. istep. istep. step.
do 7 istep.

step. carve_frame 48%nat ST. rename FR into FRf.
do 9 istep.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. istep. step. if_lit. istep. istep. istep. istep. step.
call_u PCD;
[ eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]
| assumption | unsigned_lits; exact ST | exact CEIL | unsigned_lits; lia |].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.

istep. istep. istep. istep. istep. step.
apply evt_done.
lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
assert (SFA : stdout_file mA (get_so st)) by (eapply stdout_file_stk; [exact SF| exact MUs| exact WM| lia]).
assert (SSPA : ssp_cells mA canary) by (eapply ssp_cells_munch; [exact SSP| exact MUs| exact WM| unfold got_ssp, ssp_guard; apply Forall_cons; [cbn; lia| apply Forall_nil]]).
assert (ISHA : ISH mA) by (eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]).
clear MUs SF SSP K18 K7 K22 K17 RCc PCD.

pose proof FRe as VAC. apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in VAC. destruct VAC as [_ VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -80 + Z.of_nat 24) with (bv_unsigned sp + -56) in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA. clear VAC.
change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
eapply (implM_post_evt asegs).
{ eapply VF with (A := 0x14e05) (VA := bv_unsigned sp + -56) (fmt := FMT_emit_d) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i v])
(r := d_count v + 1) (lo := lo) (canary := canary);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
all: try reflexivity. all: try lia.
all: first [ exact SFA | exact ISHA
| apply fmt_bytes_at; [assumption | vm_compute; reflexivity | lia | vm_compute; discriminate]
| unfold FMT_emit_d; forall_range
| exact VAA
| cbn [args_ok arg_ok]; split; [|exact I]; split; [exact HV | exact HA1]
| rewrite printf_pieces_emit_d, d_pieces_emit by exact HV; reflexivity
| apply fp_calls_emit_d
| exact ST | exact SSPA | assumption | exact FRM
| unfold FMT_emit_d; cbn [length]; lia ]. }
cbv beta. intros [] st' ms' P. clear VF.
unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
transport_after_call asegs mA m3 MUc WMc. clear MUc WMc.
fixret.

do 5 istep. step. release_frame FRf ST3 (bv_unsigned sp + -128).
do 4 istep. step. release_frame FRv ST3 (bv_unsigned sp + -80).
do 2 istep. step. release_frame FRe ST3 (bv_unsigned sp).
apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed.
End Emit.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp Qsn5 QQwg QvDJ QUxU QOJv QqLk QmP7 QYyZ QpME QkJ4 QRfV QEEn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QOJv.Mq5 Qu3b.Mq2 QnaW.Mq1 QYyZ.Mq5 QYyZ.Mq3.
Import QpY2.Mq2.
Import QpME.Mq1 QkJ4 QQNJ.Mq4 QQNJ.Mq5 QRfV QEEn.Mq0.
Import QcfN.Mq1.
Import QlES.
Export QteI.Mq6.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition malloc_icpt_entry : Z := 0x634a8.
Definition asan_malloc_entry : Z := 0x3f00c.

Definition MALLOC_STACK : Z := 3296.

Lemma bst_assemble : forall m obj (j0 j1 : list byte) (bpw : word),
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz 0); CB 80 j0] ->
rw_cells asegs m (obj + 96) [CB 1960 j1; C8 bpw] ->
exists (q0 q1 q2 q3 q4 : word) (rest : list byte),
rw_cells asegs m obj (unw_obj obj 0 [q0; q1; q2; q3; q4] rest (bv_unsigned bpw)).
Proof.
intros m obj j0 j1 bpw H0 H1.
assert (L0 : length j0 = 80%nat) by (destruct H0 as [[WF _] _]; cbn in WF; tauto).
assert (L1 : length j1 = 1960%nat) by (destruct H1 as [[WF _] _]; cbn in WF; tauto).
assert (H : rw_cells asegs m obj ([C8 (wz (obj + 16)); C8 (wz 0); CB 80 j0] ++ [CB 1960 j1; C8 bpw])).
{ apply (proj2 (rw_cells_app asegs m obj _ _)). cbn [cells_size csize Nat.add]. split; [exact H0| exact H1]. }
do 40 (let b := fresh "y" in destruct j0 as [|b j0]; [cbn in L0; lia|]). cbn in L0.
match type of H with context [CB 80 (?y0 :: ?y1 :: ?y2 :: ?y3 :: ?y4 :: ?y5 :: ?y6 :: ?y7 :: ?z0 :: ?z1 :: ?z2 :: ?z3 :: ?z4 :: ?z5 :: ?z6 :: ?z7 ::
?u0 :: ?u1 :: ?u2 :: ?u3 :: ?u4 :: ?u5 :: ?u6 :: ?u7 :: ?v0 :: ?v1 :: ?v2 :: ?v3 :: ?v4 :: ?v5 :: ?v6 :: ?v7 ::
?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: j0)] =>
exists (wz (bytes_le_to_Z [y0; y1; y2; y3; y4; y5; y6; y7])), (wz (bytes_le_to_Z [z0; z1; z2; z3; z4; z5; z6; z7])),
(wz (bytes_le_to_Z [u0; u1; u2; u3; u4; u5; u6; u7])), (wz (bytes_le_to_Z [v0; v1; v2; v3; v4; v5; v6; v7])),
(wz (bytes_le_to_Z [x0; x1; x2; x3; x4; x5; x6; x7])), (j0 ++ j1)
end.
eapply rw_cells_recast'; [exact H| |].
- unfold unw_obj. cbn. rewrite length_app. lia.
- unfold unw_obj. cbn [map app cells_bytes cbytes]. rewrite Z_to_bv_bv_unsigned.
rewrite (le8_split32 0) by lia. rewrite !le8_of_bytes by reflexivity.
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.

Definition micpt_W (bp T : Z) : list (Z * Z) := [(bp - 2128 - 144, bp); (T + 3168, T + 3169)].

Lemma malloc_icpt_pre : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo n : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - MALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
0 <= n < 2^64 ->
(forall m' (u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 : word) (sz : Z) (q : list word) (rest junk8 : list byte),
munch (micpt_W bp (rl_T X)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bp - 2128) ->
rw_cells asegs m' (bp - 2128) (unw_obj (bp - 2128) sz q rest bp) -> length q = 5%nat ->
1 <= sz <= 30 ->
rw_cells asegs m' (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
RTconst RE X m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] ->
evt asegs Q (MS (mkR (wz 0x635dc) (wz (bp + -2128)) gp (wz A_TP) u0 u1 u2 (wz bp) (wz n) (wz n) (wz (bp + -2128)) u3 u4 u5 u6 u7 u8
(wz 0x63570) (wz 1) (wz (bp + -2128)) (wz (bp + -81)) s6 s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz asan_malloc_entry) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x632c8) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL TU MI ST CEIL LO BPR UNW Hn CONT.
pose proof CEIL as CEIL'. idtac. unfold MALLOC_STACK in LO.
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
pose proof (munch_refl (micpt_W bp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold micpt_W in MU.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2128 - 144, bp); (rl_T X + 3168, rl_T X + 3169)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
unfold A_INSTANCE in *.
step.
carve_frame 2032%nat ST.
do 8 step.
step.
step.
carve_frame 96%nat ST.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_ch (try_asan_init_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2128)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
step. if_lit.
step. step. step. step. step.
stf.
step.
stf.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT2.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
stp. step. if_lit.
step. call0 (get_current_pc_spec); []. subst_words.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
stp.
step.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
step. stp. stp.
step.
rewrite (unsigned_lit bp), and_all_ones by lia.
stp.
step.
step. if_lit.
step. step. step. step. stp. step.

apply (proj1 (rw_cells_app asegs _ _ [CB 1960 _; C8 (wz bp)] _)) in FR as [FRa FRb].
lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bp + -64) in FRb by (cbn; lia) end.
replace (bp + -2032) with (bp + -2128 + 96) in FRa by lia.
replace (bp + -2112) with (bp + -2128 + 16) in FR0 by lia.
destruct (bst_assemble _ _ _ _ _ FR0 FRa) as (q0 & q1 & q2 & q3 & q4 & rest & OBJ). rewrite (unsigned_lit bp) in OBJ by lia. clear FR0 FRa.
pose proof FRb as FRc. apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FRc as [_ FRc].
lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bp - 16) in FRc by (cbn; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT4 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (URD : unw_readable asegs RE mc (bp - 16)) end.
{ eapply (unw_readable_prologue RE _ m _ bp s0 ra); [exact MU| intros z Hz; cbn [outside]; lia| exact FRc| exact UNW]. }
step.
call_ch (unwind_impl_spec RE X) ltac:(fun PO => unfold unwind_stack in PO; rewrite !(unsigned_lit (bp + -2128)) in PO by lia);
[exact RT4| exact RL| assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold unwind_stack; lia
| exact OBJ| exact TU| exact URD| lia| rewrite unsigned_lit by lia; lia| lia| lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST2 end.
destruct POST as (sz & q & rest' & OBJ2 & LQ & TU2 & SZR & RT5).
clear URD FRc RT4.
step. step. step.
step.
lazymatch type of FRb with rw_cells _ _ _ (CB 8 ?j8 :: _) =>
eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ sz q rest' j8); [exact MU| exact WM| assumption| exact ST2| exact OBJ2| exact LQ| exact SZR| exact FRb| exact RT5| exact TU2] end.
Qed.

Definition malloc_W (bp : Z) (c au : Z) : list (Z * Z) :=
(bp - MALLOC_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W RE X (bp - 2144) c au).

Definition malloc_post (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (n lo : Z) (m : word -> option byte)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ munch (malloc_W bp (class_of n) (c_alloc_user (cls a (class_of n)))) m m'
/\ qframe a a1 /\ gstep RE X a a1 G G1 /\ RPrim a1 G1 RE X m'
| (Some p, a2) => exists a1 i,
p = APrim (as_next a1) n /\ a2 = set_next (N.succ (as_next a1)) a1 /\ qframe a a1
/\ gstep RE X a a1 G G1 /\ tag_at G1 (class_of n) i = Some TCached /\ 0 <= i
/\ a0 = wz (slot_beg RE (class_of n) i + rz_size n)
/\ munch (malloc_W bp (class_of n) (c_alloc_user (cls a (class_of n))) ++ slot_W RE (class_of n) i) m m'
/\ (forall t, tag_prim t = false -> RPrim a1 (set_tag (class_of n) i t G1) RE X m')
/\ chunk_mem m' (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (slot_beg RE (class_of n) i + rz_size n) n
/\ hjunk m' (slot_beg RE (class_of n) i + rz_size n) (slot_beg RE (class_of n) i + class_size (class_of n))
end.

Lemma malloc_icpt_spec : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (lo n dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - MALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
0 <= n -> from_primary n = true ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(malloc_post ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G n lo m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x632c8) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RP RD MI ST CEIL LO BPR UNW DNH DCAP Hn HP.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold MALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 D02. pd_pair PD 0 2 D03. clear PD.
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (class_of_facts n Hn HP) as (Hc & _). cbv zeta in Hc. set (c := class_of n) in *.
pose proof (needed_facts n Hn) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (QSsj.rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC. idtac. rewrite ?KHI_eq in NK.
pose proof (QSsj.rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC. idtac. rewrite ?KHI_eq in BK.
pose proof (munch_refl (malloc_W bp c (c_alloc_user (cls a c))) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
apply aimplT_from_evt.
eapply malloc_icpt_pre; [exact RT| exact RL| exact (RDepot_unw RE X _ RD)| exact MI| exact ST| exact CEIL'| unfold MALLOC_STACK; lia| exact BPR| exact UNW| lia|].
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 sz q rest junk8 MU1 WM1 MI1 ST1 OBJ LQ SZR FR RT1 TU1.
unfold micpt_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RP1 : RPrim a G RE X m1).
{ eapply RPrim_frame; [exact RP| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside].
pose proof (fp_RPrim_lt_ceil G RE X z RL Fz). idtac.
split; [lia|]. split; [| exact I]. assert (z <> rl_T X + 3168) by (intros ->; exact (fpP_RDepot _ _ _ _ _ _ GC _ Fz ltac:(do 3 right; reflexivity))). lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RP RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_malloc_entry. carve_frame 16%nat ST1.
match goal with H : rw_cells asegs _ (bp + -2128 + -16) _ |- _ => replace (bp + -2128 + -16) with (bp + -2144) in H by lia end.
replace (bp + -2128 + -16) with (bp + -2144) in ST1 by lia.
pose proof (munch_refl [(bp - 2144, bp - 2128)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step.
step. step. step. stp. stp. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & FP & FD);
pose proof (FT RT1) as RT2; pose proof (FP RP1) as RP2; pose proof (FD RD1) as RD2;
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FP FD RT1 RP1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 967832) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_prim_spec L RE X _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 1 lo (bp + -2128) sz dn q30 GC RT2 RS2 RP2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post in PO. rewrite !(unsigned_lit (bp + -2144)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 258104)) with (wz 258104) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END in REST. rewrite ?KS, ?KO in REST.
change (536870912 / 8) with 67108864 in REST. change (3758096384 / 8) with 469762048 in REST.
fold c in REST.
clear OBJh TRQ RT2 RP2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2128) (unw_obj (bp + -2128) sz q rest bp) ->
rw_cells asegs mx (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2128) (unw_obj (bp + -2128) sz q rest bp ++ [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O1 O2. apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app]. replace (bp + -2128 + Z.of_nat 2064) with (bp + -64) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (aa & i & -> & -> & QF & GS & TI & I0 & -> & MUk & RPF & CM & HJU).
pose proof GS as (_ & _ & _ & GCT). pose proof (GCT LB FS GC) as GC1.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (_ & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
assert (SHS : SH (reg_beg (ae_L RE) c) <= SH (slot_beg RE c i) /\ SH (slot_beg RE c i) + class_size c / 8 <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048).
rewrite <- SH_plus8. replace (8 * (class_size c / 8)) with (class_size c) by (clear - CS2; Z.div_mod_to_equations; lia). apply SH_le. lia. }
hide CS2.
apply (munch_weaken _ (malloc_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i)) in MU.
2:{ unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
cbn [app] in MUk. phase_done MU m2 m3 MUk WM3.
step. unfold_cond; cond_unsig; if_false.
step. step. step.
release_frame FR0 ST3 (bp + -2128).
step.
replace (ret_pc (wz 407004)) with (wz 407004) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 7 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold malloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT3|]. split; [exact RS3|]. split; [exact RD3|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists aa, i. split; [reflexivity|]. split; [reflexivity|]. split; [exact QF|]. split; [exact GS|]. split; [exact TI|]. split; [exact I0|].
split; [reflexivity|]. split; [| split; [exact RPF| split; [exact CM| exact HJU]]].
unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. exact MU.
-
destruct REST as (-> & MUk & QF & GS & RPk).
phase_done MU m2 m3 MUk WM3.
step. if_lit.
step.
pose proof (munch_refl [(bp - 2160, bp - 2144); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a' LB FS G1 m3 mm _ (proj2 (proj2 (proj2 GS)) LB FS GC) MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & FP & FD) end.
pose proof (FT RT3) as RT4. pose proof (FP RPk) as RP4. pose proof (FD RD3) as RD4. clear FT FP FD MUe WMe RT3 RPk RD3 RS3.
step.
step. step. step.
release_frame FR0 ST4 (bp + -2128).
step.
replace (ret_pc (wz 407004)) with (wz 407004) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 7 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold malloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [| split; [exact QF| split; [exact GS| exact RP4]]].
unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. exact MU.
Qed.
End S.

End Mq2.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUnM QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QOJv.Mq4 QmP7.Mq0 QYyZ.Mq0 QnRU.Mq0 Q9Ho.Mq1 QOJv.Mq5.
Import QpY2.Mq2.
Import QUnM QpME.Mq0.
Import QYyZ.Mq5.
Import Qu3b.Mq2 QnRU.Mq8 QmvA.Mq3 QkZz.Mq1 QteI.Mq9 QcfN.Mq1.
Import QlES.
Import QnRU.Mq6.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac rlia := first [ lia_relh0 | lia_relh1 | lia ].
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition put_entry : Z := 0x4350c.

Definition PUT_STACK : Z := 80 + DRAIN_STACK.

Lemma land_mask8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
intros x Hx.
assert (E : 18446744073709551608 = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3) with 8. pose proof (Z.div_mod x 8). lia.
Qed.

Lemma NoDup_app_In {A} : forall (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn in ND. inversion ND; subst.
destruct H1 as [<-|H1]; [apply H3; apply in_app_iff; right; exact H2| exact (IH l2 x H4 H1 H2)].
Qed.

Lemma qwf_nonneg : forall q, qwf q -> 0 <= q_bytes q.
Proof. intros q W. pose proof (qwf_length_bound q W). pose proof kq_consts as (_ & KBB & _). lia. Qed.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Hypothesis recycle_spec : recycle_stmt C RE X L.

Lemma enq_W_zone : forall a LB0 FS0 G (sp lo hi x : Z),
gcons a LB0 FS0 G RE X -> band_lo <= sp - ENQ_STACK ->
In (lo, hi) (enq_W RE X sp a) -> lo <= x < hi ->
(band_lo <= x < sp) \/ (rl_T X + 80 <= x < rl_T X + 112) \/ fp_RPrim G RE X x \/ in_iv (rl_T X + 2800, 368) x.
Proof.
intros a LB0 FS0 G sp lo hi x GC CE Hin Hx. pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof kconsts as (KR & KO & KS & K32 & KP & _). pose proof kq_consts as (K24 & _).
pose proof (gc_bounds a LB0 FS0 G RE X GC 24 ltac:(rewrite K32; lia)) as (B1 & B2 & B3).
pose proof (region_in_prim RE 24 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X 24 RL) as (RAL & _ & FAL).
unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr in Hin. cbn [tl app In] in Hin. unfold ENQ_STACK, QPOP_STACK in CE.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-.
- left. lia.
- right; left. lia.
- right; right. destruct (Z.lt_ge_cases x (rl_T X + 2800)) as [LT|GE].
+ left. right; left. split; cbn [fst snd]; lia.
+ right. split; cbn [fst snd]; lia.
- do 2 right; left. left. unfold region_info in *. split; cbn [fst snd]; lia.
- do 2 right; left. do 2 right; left. exists 24. rewrite K32. split; [lia| lia].
- do 2 right; left. do 3 right; left. exists 24. rewrite K32. split; [lia|]. split; cbn [fst snd]; lia.
- do 2 right; left. do 4 right; left. split.
+ exists 24. rewrite K32. split; [lia| lia].
+ intros (c' & i' & t' & Ht' & _ & [S1 S2]). cbn [fst snd] in S1, S2.
pose proof (tag_slot a LB0 FS0 G RE X GC c' i' t' Ht') as (C1 & I1 & N1 & R1 & R2 & _).
pose proof (region_in_prim RE c' C1) as (Q1' & Q2' & Q3' & Q4').
assert (c' = 24 \/ c' + 1 <= 24 \/ 24 + 1 <= c') as [->|[D|D]] by lia; [(first [ clear - R1 R2 S1 S2 i' B1 Hx x a RE BAND; lia | lia ])| |];
pose proof (gc_bounds a LB0 FS0 G RE X GC c' ltac:(rewrite K32; lia)) as (B1' & B2' & B3'); rewrite KO in *; (first [ clear - B2' B1' D Q4' R2 S2 i' c' Q4 B1 Hx x a RE BAND R1 S1; lia | lia ]).
- do 2 right; left. do 5 right. split.
+ exists 24. rewrite K32. split; [lia|]. split; cbn [fst snd]; unfold SH, A_SHADOW_OFS in *; Z.div_mod_to_equations; (first [ clear - H23 H22 H21 H20 H19 q3 H14 q2 H5 H4 r0 H q FAL r2 RAL r Q2 B3 r3 B1 KO Hx q1 q0 x a RE BAND H26 H25 H15 r4; lia | lia ]).
+ intros (c' & i' & t' & Ht' & _ & [S1 S2]). cbn [fst snd] in S1, S2.
pose proof (tag_slot a LB0 FS0 G RE X GC c' i' t' Ht') as (C1 & I1 & N1 & R1 & R2 & _ & _ & SZ & SM & _).
pose proof (slot_beg_align RE X c' i' RL C1) as [_ SAL].
pose proof (region_in_prim RE c' C1) as (Q1' & Q2' & Q3' & Q4').
unfold SH, A_SHADOW_OFS in *.
assert (c' = 24 \/ c' + 1 <= 24 \/ 24 + 1 <= c') as [->|[D|D]] by lia;
[| pose proof (gc_bounds a LB0 FS0 G RE X GC c' ltac:(rewrite K32; lia)) as (B1' & B2' & B3')
| pose proof (gc_bounds a LB0 FS0 G RE X GC c' ltac:(rewrite K32; lia)) as (B1' & B2' & B3')];
rewrite KO in *; Z.div_mod_to_equations; (first [ clear - H38 H37 H36 H35 H34 q6 H29 q5 H24 q4 H10 H9 r1 H5 H4 r0 H R1 R2 SZ SAL r Q2' S2 q0 q i' FAL r4 RAL r5 B3 r6 B1 Hx q2 q1 x a RE BAND H41 H40 H23 H22 H21 H20 H19 q3 B3' r3 B2' B1' D Q4' c' Q4 r7 H15 H14 r2 S1; lia | lia ]).
Qed.

Lemma put_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (p : aptr) (A lo : Z),
QRUN C 0 QB QB [(p, A)] a LB0 FS0 G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - PUT_STACK ->
0 <= aptr_req p <= 2^26 ->
qroom a p ->
aimplT atn (tbind (enqueue (ae_L RE) a p) (fun s1 => if kQMaxCache <? q_bytes (as_tq s1) then drain (ae_L RE) s1 else tret s1)) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m (free_keep asegs))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz QOBJ) (wz (TQ X)) (wz (rl_T X + 208)) a3 (wz (A - 16)) (wz (aptr_used p)) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz put_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros QR MI ST CEIL LO HN QRM.
pose proof CEIL as CEIL'. idtac. unfold PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
destruct QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
apply QOTH_split in QO as (RT & RS & RP & QRE).
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND). unfold QB in BND.
apply Forall_cons_iff in PQA as [EQA _]. cbn [fst snd] in EQA.
assert (HU : 1 <= aptr_used p <= 2^26 + 1) by (unfold aptr_used, used_size; lia).
set (u := aptr_used p) in *. set (n := aptr_req p) in *.

pose proof (REP p ltac:(left; reflexivity)) as REPp.
assert (PC0 : exists lo_ hi_, qchunk_mem m lo_ hi_ A n
/\ (forall x, lo_ <= x < hi_ \/ in_sh (lo_, hi_ - lo_) x -> fp_RQuar a LB0 G RE X x)
/\ match p with
| APrim id n0 => exists i, tag_at G (class_of n0) i = Some (TQuar p) /\ lo_ = slot_beg RE (class_of n0) i /\ hi_ = lo_ + class_size (class_of n0)
| ASec mb n0 => In (mkSec mb (sec_map_size n0) n0) (as_reg a) /\ lo_ = mb + kPage /\ hi_ = mb + sec_map_size n0
end).
{ destruct p as [id n0|mb n0]; cbn [qptr_rep] in REPp; subst n; cbn [aptr_req] in *.
- destruct REPp as (i & Ht & Hpr & HQA & QM). rewrite EQA in QM. exists (slot_beg RE (class_of n0) i), (slot_beg RE (class_of n0) i + class_size (class_of n0)).
split; [exact QM|]. split; [| exists i; auto].
intros x [Hx|Hx]; [do 5 right; left| do 6 right; left]; exists (class_of n0), i, (TQuar (APrim id n0)); (split; [exact Ht|]); (split; [reflexivity|]).
+ split; cbn [fst snd]; lia.
+ replace (slot_beg RE (class_of n0) i + class_size (class_of n0) - slot_beg RE (class_of n0) i) with (class_size (class_of n0)) in Hx by lia. exact Hx.
- destruct REPp as (Hin & Hnl & Hpr & HQA & QM). rewrite EQA in QM. exists (mb + kPage), (mb + sec_map_size n0).
split; [exact QM|]. split; [| auto].
intros x [Hx|Hx]; [do 7 right; left| do 8 right]; exists (mkSec mb (sec_map_size n0) n0); cbn [se_beg se_size se_req]; (split; [exact Hin|]); (split; [exact Hnl|]).
+ lia.
+ replace (mb + sec_map_size n0 - (mb + kPage)) with (sec_map_size n0 - kPage) in Hx by lia. exact Hx. }
destruct PC0 as (plo & phi & QMp & PZ & PWHERE).
pose proof (qchunk_geom _ _ _ _ _ QMp) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & q & g & r & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
rewrite ?KHI_eq in G3. idtac. apply appr_to_lia in G3; [| lia| lia].
destruct QMp as (LEFTp & (b1 & idw & Hb1 & HDRp) & JUNKp & (sj & SHDp) & PUREp). unfold qhdr_cells in HDRp.

apply (proj1 (rw_cells_app asegs m (SH plo) [CB (Z.to_nat ((A - plo) / 8)) (fas ((A - plo) / 8))] _)) in SHDp as [SHL SHDp].
apply (proj1 (rw_cells_app asegs m _ [CB (Z.to_nat (ngran (used_size n))) sj] _)) in SHDp as [SHMp SHR].
cbn [cells_size csize] in SHMp, SHR. rewrite !Nat.add_0_r, !Z2Nat.id in SHMp, SHR by lia.
assert (SHA : SH plo + (A - plo) / 8 = SH A) by (unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; (first [ clear - H34 q7 H10 H9 r2 q2 H5 H4 r1 H0 H r0 q0 Q5 Q3 Q1 g q G2 G1 PUREp r7 r6 r5 r4 q1 phi plo PK TK n A p X RE BAND; lia | lia ])). rewrite SHA in SHMp, SHR.
assert (SHAB : 0x7fff8000 <= SH plo /\ SH A + g + r <= SH band_lo /\ SH plo + q = SH A) by (unfold SH, A_SHADOW_OFS in *; Z.div_mod_to_equations; (first [ clear - H39 q8 H15 H14 r3 H10 H9 r2 q2 H0 H r0 SHA Q8 Q7 Q5 Q1 r g q G4 G3 G1 PUREp r8 r7 r6 r5 q1 q3 q0 phi plo PK TK n A p X RE BAND; lia | lia ])).
pose proof SH_band as SHBD0.
pose proof (used_size_pos n ltac:(lia)) as [U1 U2].
assert (UN : used_size n = u) by (subst u n; reflexivity).
rewrite UN in *.
rtc RT 26%nat K26. rtc RT 19%nat K19. rtc RT 12%nat K12.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned sp - 80 - 64, bv_unsigned sp - 80); (SH A, SH A + g)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold put_entry, QOBJ, TQ, GQ, QMUT, A_INSTANCE in *.
change (967832 + 888) with 968720 in *. change (967832 + 880) with 968712 in *. change (967832 + 728) with 968560 in *.
change (967832 + 792) with 968624 in *.
pose proof HM as HM0. hide HM0.
apply aimplT_from_evt.
carve_frame 80%nat ST.
do 9 step.
step.
step. step.
step.
step.
step. if_false.
step.
step. ifz.
step. step. step.
step. step.
step.
step. if_lit.
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small u) by lia.
step.
replace (A - 16 + 16) with A by lia.
step. step.
rewrite (unsigned_lit u) by lia. rewrite Z.lor_0_l.
step. step.
rewrite (unsigned_lit (u + 7)) by lia. rewrite land_mask8 by lia.
replace (u + 7 - (u + 7) mod 8) with (8 * g) by (unfold round_up in Q3; Z.div_mod_to_equations; (first [ clear - H10 H9 r2 H0 H r0 q0 U1 Q8 Q6 Q4 Q3 q2 Q1 r g q G2 G1 phi plo HU u PK TK A p X RE BAND; lia | lia ])).
step. step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM|
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [apply (rt_avoid_gap RE X RL); rewrite ?KHI_eq; lia| constructor]]]]) end.
hide MU.
rewrite Q4 in SHMp.
eapply evt_cut.
{ eapply (poison_shadow_spec_lh RE X); try eassumption; rewrite ?unsigned_lit by lia.
- exact ST.
- lia.
- Z.div_mod_to_equations; (first [ clear - H29 q6 H0 H r0 q0 Q5 Q3 G2 G1 PUREp r6 r5 r4 r3 g phi plo u PK TK n A p X RE BAND; lia | lia ]).
- Z.div_mod_to_equations; (first [ clear - H0 H r0 q0 Q5 Q4 Q3 G2 G1 g phi plo u PK TK A p X RE BAND; lia | lia ]).
- lia.
- rewrite ?KHI_eq; change (2^47) with 140737488355328; (first [ clear - SHAB SHA Q6 Q5 Q4 Q3 Q1 r q G4 G3 G2 G1 g phi plo u A p BAND; lia | lia ]).
- lia.
- left; lia.
- rewrite (Z.mul_comm 8 g), Z.div_mul by lia. exact SHMp. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MUp & WMp & MIp & STp & RTp & SHM2).
rewrite (Z.mul_comm 8 g), Z.div_mul in MUp, SHM2 by lia. rewrite !(unsigned_lit (bv_unsigned sp + -80)) in MUp, STp by lia.
clear SHMp. unhide MU.
lazymatch type of MUp with munch _ ?mx _ =>
apply (munch_chain' _ _ m2 _ m MUp) in MU; [| sub_fp_solve];
transport_after_call asegs mx m2 MUp WMp; clear MUp end.
replace (SH A + Z.of_nat (Z.to_nat (ngran u) + 0)) with (SH A + g) in SHR by (rewrite Nat.add_0_r, Z2Nat.id; lia).
replace (ret_pc (wz 276120)) with (wz 276120) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
do 5 step.
step.
apply evt_done.

set (Qs' := qptrs (as_tq a) ++ qptrs (as_gq a)) in *.
assert (EQQ : qall [(p, A)] a = p :: Qs') by reflexivity.
assert (NDQ : List.NoDup (p :: Qs')) by (rewrite <- EQQ; exact NDP).
assert (NIp : ~ In p Qs') by (inversion NDQ; assumption).
assert (REP' : forall q', In q' Qs' -> qptr_rep a LB0 G RE m QA q') by (intros q' Hq; apply REP; rewrite EQQ; right; exact Hq).
pose proof HT as (TQC & BMT & FJT & QWT). pose proof HG as (GQC & BMG & FJG & QWG).
assert (FJ : Forall (fun j => tag_at G 24 j = Some TQOwn) (JT ++ JG)) by (apply Forall_app; split; assumption).

assert (AG1 : agree_on asegs (fun x => rq_keep G RE (JT ++ JG) Qs' x \/ rl_T X + 80 <= x < rl_T X + 112) m m2).
{ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Kx _. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- destruct Kx as [Kx|Kx]; [| lia]. exact (keep_pzoneP a LB0 FS0 G RE X GC QA (JT ++ JG) Qs' FJ m REP' x ltac:(right; right; lia) Kx).
- destruct Kx as [Kx|Kx]; [| lia]. exact (keep_pzoneP a LB0 FS0 G RE X GC QA (JT ++ JG) Qs' FJ m REP' x ltac:(right; right; lia) Kx).
- destruct Kx as [Kx|Kx]; [| (first [ clear - Y2 Y1 Kx x SHBD0 SHAB SHA Q8 Q5 Q3 Q1 r q G7 G6 G2 G1 PUREp g phi plo u PK TK n A p X RE BAND; lia | lia ])].
destruct p as [id n0|mb n0]; cbn [aptr_req] in *.
+ destruct PWHERE as (i & Ht & Elo & Ehi).
refine (keep_slot a LB0 FS0 G RE X GC QA (JT ++ JG) Qs' FJ m REP' (class_of n0) i _ x Ht _ _ _ Kx).
* intros E24 Hi. pose proof (proj1 (List.Forall_forall _ _) FJ i Hi) as Ti. rewrite E24, Ti in Ht. discriminate.
* intros id' n' E Hq. injection E as <- <-. exact (NIp Hq).
* right. rewrite <- Elo. replace (class_size (class_of n0)) with (phi - plo) by lia.
split; cbn [fst snd]; [lia|]. rewrite Q8, (Z.mul_comm 8), Z.div_mul by lia. lia.
+ destruct PWHERE as (Hin & Elo & Ehi).
refine (keep_sec a LB0 FS0 G RE X GC QA (JT ++ JG) Qs' FJ m REP' (mkSec mb (sec_map_size n0) n0) x Hin _ _ Kx); cbn [se_beg se_size].
* intros n' Hq. pose proof (REP' _ Hq) as (Hin' & _). cbn [qptr_rep] in Hin'.
pose proof (NoDup_map_In_inj se_beg (as_reg a) _ _ (gc_sec_nodup a LB0 FS0 G RE X GC) Hin Hin' eq_refl) as E. injection E as En. subst n'. exact (NIp Hq).
* right. rewrite <- Elo. replace (sec_map_size n0 - kPage) with (phi - plo) by lia.
split; cbn [fst snd]; [lia|]. rewrite Q8, (Z.mul_comm 8), Z.div_mul by lia. lia. }

assert (RS2 : RStats RE X m2).
{ eapply RStats_munch; [exact RS| exact MU| exact WM|]. unfold A_ERRNO in *.
constructor; [st_avoid_solve|]. constructor; [st_avoid_solve|].
constructor; [st_avoid_solve| constructor]. }
assert (PSH : forall x, SH A <= x < SH A + g -> in_sh (plo, phi - plo) x).
{ intros x Hx. split; cbn [fst snd]; [lia|]. rewrite Q8, (Z.mul_comm 8), Z.div_mul by lia. lia. }
assert (RP2 : RPrim a G RE X m2).
{ eapply RPrim_frame; [exact RP| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx _. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- apply (fpQ_RPrim a LB0 FS0 G RE X GC x); [apply PZ; right; apply PSH; lia| exact Fx]. }
assert (QT2 : qrep RE G m2 QA (rl_T X + 80) (as_tq a) JT).
{ eapply qrep_agree; [exact AG1| exact HT| intros x Hx; right; lia| |].
- intros j x Hj Hx. left. do 4 right; left. exists j. split; [apply in_app_iff; left; exact Hj| left; exact Hx].
- intros j x Hj Hx. left. do 4 right; left. exists j. split; [apply in_app_iff; left; exact Hj| right; exact Hx]. }

assert (REPall : forall q', In q' (p :: Qs') -> qptr_rep a LB0 G RE m QA q') by (intros q' Hq; apply REP; rewrite EQQ; exact Hq).
destruct (rq_transport a LB0 G RE QA JG Qs' m m2 (as_gq a) 0) as (GQ2 & HM2 & HI2 & REP2).
{ eapply agree_on_mono; [exact AG1|]. intros x Kx. left. revert Kx. unfold rq_keep. intros [K|[K|[K|[K|[K|[K|K]]]]]]; try (clear - K; tauto).
do 4 right; left. destruct K as (j & Hj & K). exists j. split; [apply in_app_iff; right; exact Hj| exact K]. }
{ exact HG. } { unhide HM0. exact HM0. } { exact HI. } { exact REP'. }
clear HM HM0.

assert (QMp2 : qchunk_mem m2 plo phi A n).
{ assert (AGp : agree_on asegs (fun x => (plo <= x < phi) \/ (SH plo <= x < SH A) \/ (SH A + g <= x < SH A + g + r)) m m2).
{ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Hx _. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; rlia. }
split; [| split; [| split; [| split; [| exact PUREp]]]].
- intros Hrz. destruct (LEFTp Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AGp| exact L1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia.
+ eapply hjunk_agree; [exact AGp| exact L2|]. intros x Hx. left. lia.
- exists b1, idw. split; [exact Hb1| exact HDRp].
- eapply hjunk_wmono; [exact JUNKp| exact WM].
- exists (repeat (b8 253) (Z.to_nat g)). rewrite UN.
apply (proj2 (rw_cells_app asegs m2 (SH plo) [CB (Z.to_nat ((A - plo) / 8)) (fas ((A - plo) / 8))] _)). split; [exact SHL|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id, SHA by lia.
apply (proj2 (rw_cells_app asegs m2 (SH A) [CB (Z.to_nat (ngran u)) (repeat (b8 253) (Z.to_nat g))] _)). rewrite Q4. split; [exact SHM2|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact SHR. }
clear HDRp SHL SHM2 SHR JUNKp LEFTp.

eapply aimplT_bind.
{ eapply aimplT_tall; [apply (enqueue_qptrs (ae_L RE)); lia|].
replace (wz (A - 16)) with (wz (QA p - 16)) by (rewrite EQA; reflexivity).
eapply (enqueue_spec L RE X); try eassumption; rewrite ?unsigned_lit by lia.
- exact STp.
- unfold ENQ_STACK, QPOP_STACK. lia.
- exact (NoDup_app_remove_r _ _ ND).
- rewrite EQA. lia.
- lia. }
cbv beta. intros a1 s' ms' [QF PO].
destruct QF as (EQP & BY1 & Egq & Ereg & Enres & Espent & Enext).
destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & G' & JT' & Wx
& -> & -> & MUq & WMq & MI3 & ST3 & HWx & RT3 & RS3 & RP3 & QT3 & QF3 & EG).
rewrite !(unsigned_lit (bv_unsigned sp + -80)) in MUq, ST3 by lia.
clear STp MIp RTp RT1 RS2 RP2 QT2.
destruct EG as (SLV & TQI & TOT & GCT & JTC).
pose proof (GCT LB0 FS0 GC) as GC'.

assert (JNG : forall j, In j JT' -> In j JG -> False).
{ intros j Hj HjG. destruct JTC as [[-> _]|(jn & -> & Tn' & Tn & _)].
- exact (NoDup_app_In JT JG j ND Hj HjG).
- apply in_app_iff in Hj as [Hj|[<-|[]]]; [exact (NoDup_app_In JT JG j ND Hj HjG)|].
apply Tn. exact (proj1 (List.Forall_forall _ _) FJG jn HjG). }
assert (FJG' : Forall (fun j => tag_at G' 24 j = Some TQOwn) JG).
{ apply List.Forall_forall. intros j Hj. pose proof (proj1 (List.Forall_forall _ _) FJG j Hj) as Tj.
destruct JTC as [[_ TQO2]|(jn & EJ & Tn' & Tn & TQO2)]; [apply TQO2; exact Tj|].
apply TQO2; [| exact Tj]. right. intros ->. exact (Tn Tj). }
pose proof QT3 as (TQC3 & BMT3 & FJT3 & QWT3). unfold TQ in TQC3.
assert (REPall' : forall q', In q' (p :: Qs') -> qptr_rep a1 LB0 G' RE m QA q').
{ intros q' Hq. eapply qptr_rep_ext; [exact (REPall q' Hq)| exact Ereg| exact TQI]. }

assert (WXB : forall lo' hi' x, In (lo', hi') Wx -> lo' <= x < hi' -> al_space_beg (ae_L RE) <= x < al_space_beg (ae_L RE) + 2^37 + 4096
/\ exists j, In j JT' /\ tag_at G' 24 j = Some TQOwn /\ in_iv (slot_beg RE 24 j, class_size 24) x).
{ intros lo' hi' x Hin Hx. pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as (j & Hj & B1 & B2). cbn [fst snd] in B1, B2.
pose proof (proj1 (List.Forall_forall _ _) FJT3 j Hj) as Tj.
pose proof (slot_prim _ _ _ _ _ _ GC' 24 j TQOwn Tj) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2. rewrite class_size_24 in P2.
split; [lia|]. exists j. split; [exact Hj|]. split; [exact Tj|]. split; cbn [fst snd]; rewrite ?class_size_24; lia. }
lazymatch type of FR with rw_cells _ _ ?fa ?cs => assert (FR3 : rw_cells asegs m3 fa cs) end.
{ eapply rw_cells_agree; [| exact FR|].
- eapply agree_on_of_munch; [exact MUq| exact WMq|]. intros x Hx _; exact Hx.
- intros x Hx; cbn [cells_size csize Nat.add] in Hx. apply outside_intro. intros lo' hi' Hin Hy.
apply in_app_iff in Hin as [Hin|Hin].
+ destruct (enq_W_zone a LB0 FS0 G (bv_unsigned sp + -80) lo' hi' x GC ltac:(unfold ENQ_STACK, QPOP_STACK; rlia) Hin Hy) as [Z|[Z|[Z|Z]]];
[ rlia | rlia | pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Z); rlia | assert (Z' : fp_RStats RE X x) by (left; exact Z); pose proof (fp_lt_ceil a LB0 FS0 G RE X GC x ltac:(first [ clear - Z'; tauto | tauto ])); rlia ].
+ destruct (WXB lo' hi' x Hin Hy) as [B _]. lia. }
clear FR.

assert (REPp2 : qptr_rep a1 LB0 G' RE m2 QA p).
{ pose proof (REP p ltac:(left; reflexivity)) as R. destruct p as [id n0|mb n0]; cbn [qptr_rep aptr_req] in R |- *; subst n.
- destruct R as (i & Ht & Hpr & HQA & _). destruct PWHERE as (i' & Ht' & Elo & Ehi).
pose proof (gc_unique a LB0 FS0 G RE X GC _ _ _ _ (APrim id n0) _ _ Ht Ht' ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
exists i. split; [apply TQI; exact Ht|]. split; [exact Hpr|]. split; [exact HQA|]. rewrite EQA. subst plo phi. exact QMp2.
- destruct R as (Hin & Hnl & Hpr & HQA & _). destruct PWHERE as (_ & Elo & Ehi). cbn [as_reg set_gq set_tq] in *. rewrite Ereg.
split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|]. rewrite EQA. subst plo phi. exact QMp2. }
assert (REP2' : forall q', In q' (p :: Qs') -> qptr_rep a1 LB0 G' RE m2 QA q').
{ intros q' [<-|Hq]; [exact REPp2|]. eapply qptr_rep_ext; [exact (REP2 q' Hq)| exact Ereg| exact TQI]. }
assert (GQ2' : qrep RE G' m2 QA 968720 (as_gq a) JG).
{ destruct GQ2 as (C1 & B1 & _ & W1). split; [exact C1|]. split; [exact B1|]. split; [exact FJG'| exact W1]. }

destruct (rq_transport a1 LB0 G' RE QA JG (p :: Qs') m2 m3 (as_gq a) 0) as (GQ3 & HM3 & HI3 & REP3).
{ eapply agree_on_of_munch; [exact MUq| exact WMq|]. intros x Kx _. apply outside_intro. intros lo' hi' Hin Hy.
apply in_app_iff in Hin as [Hin|Hin].
- pose proof (rq_keep_tags G' G RE JG (p :: Qs') x ltac:(intros; symmetry; apply TQI) Kx) as KxG.
destruct (enq_W_zone a LB0 FS0 G (bv_unsigned sp + -80) lo' hi' x GC ltac:(unfold ENQ_STACK, QPOP_STACK; lia) Hin Hy) as [Z|[Z|[Z|Z]]].
+ exact (keep_pzoneP a LB0 FS0 G RE X GC QA JG (p :: Qs') FJG m REPall x ltac:(right; right; lia) KxG).
+ exact (keep_TQ a LB0 FS0 G RE X GC QA JG (p :: Qs') FJG m REPall x ltac:(lia) KxG).
+ exact (keep_pzoneP a LB0 FS0 G RE X GC QA JG (p :: Qs') FJG m REPall x ltac:(left; exact Z) KxG).
+ exact (keep_pzoneP a LB0 FS0 G RE X GC QA JG (p :: Qs') FJG m REPall x ltac:(right; left; left; exact Z) KxG).
- destruct (WXB lo' hi' x Hin Hy) as (_ & j & Hj & Tj & Hx).
refine (keep_slot a1 LB0 FS0 G' RE X GC' QA JG (p :: Qs') FJG' m REPall' 24 j TQOwn x Tj _ _ (or_introl Hx) Kx).
+ intros _ HjG. exact (JNG j Hj HjG).
+ intros id' n' E _. discriminate E. }
{ exact GQ2'. } { exact HM2. } { exact HI2. } { exact REP2'. }
clear GQ2 GQ2' HM2 HI2 REP2 REP2' REPp2 QMp2.

assert (EQ1 : qptrs (as_tq a1) = qptrs (as_tq a) ++ [p]) by (unfold qptrs; exact EQP).
assert (PERM : Permutation (qall [] a1) (p :: Qs')).
{ unfold qall. cbn [map app]. rewrite EQ1, Egq. subst Qs'. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
assert (CLOSE : forall bt, q_bytes (as_tq a1) <= bt -> RQuarM 0 bt QB [] a1 LB0 G' RE X m3).
{ intros bt Hbt. exists JT', JG, QA.
split; [exact QT3|]. split; [rewrite Egq; exact GQ3|]. split; [exact HM3|]. split; [exact HI3|].
split.
{ destruct JTC as [[-> _]|(jn & -> & Tn' & Tn & _)]; [exact ND|].
apply (Permutation_NoDup (l := jn :: JT ++ JG)); [rewrite <- app_assoc; cbn [app]; apply Permutation_middle|].
constructor; [| exact ND]. intros Hin. apply Tn. exact (proj1 (List.Forall_forall _ _) FJ jn Hin). }
split.
{ intros j Tj'. destruct JTC as [[-> TQO2]|(jn & -> & Tn' & Tn & TQO2)].
- apply TQO. apply TQO2. exact Tj'.
- destruct (Z.eq_dec j jn) as [->|NE]; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity|].
pose proof (TQO j (proj2 (TQO2 24 j (or_intror NE)) Tj')) as IN. rewrite <- app_assoc. cbn [app].
apply in_app_iff in IN. apply in_app_iff. destruct IN as [IN|IN]; [left; exact IN| right; right; exact IN]. }
split.
{ intros c j Tj'. destruct (Z.eq_dec c 24) as [E|NE]; [exact E|]. exfalso. apply NE.
destruct JTC as [[_ TQO2]|(jn & _ & Tn' & Tn & TQO2)]; [exact (C24 c j (proj2 (TQO2 c j) Tj'))| exact (C24 c j (proj2 (TQO2 c j (or_introl NE)) Tj'))]. }
split; [eapply Permutation_NoDup; [apply Permutation_sym; exact PERM| exact NDQ]|].
split; [intros q' Hq; apply REP3; eapply Permutation_in; [exact PERM| exact Hq]|].
split.
{ intros c i q' Ht'. pose proof (TQP c i q' (proj2 (TQI c i q') Ht')) as [IN CL]. split; [| exact CL].
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. rewrite <- EQQ. exact IN. }
split; [constructor|]. rewrite Egq. pose proof (qwf_nonneg _ QWT3). unfold QB in *. lia. }

assert (MU3 : munch ([(bv_unsigned sp + -80, bv_unsigned sp); (bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (SH A, SH A + g)]
++ (enq_W RE X (bv_unsigned sp + -80) a ++ Wx)) m m3).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUq]];
intros x Hx; apply outside_app in Hx as [Hx1 Hx2]; [exact Hx1| exact Hx2]. }
pose proof (wmono_trans asegs _ _ _ WM WMq) as WM3.
assert (WZ3 : forall lo' hi' x, In (lo', hi') ([(bv_unsigned sp + -80, bv_unsigned sp); (bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (SH A, SH A + g)]
++ (enq_W RE X (bv_unsigned sp + -80) a ++ Wx)) -> lo' <= x < hi' -> wzone a LB0 G RE X (bv_unsigned sp) x).
{ intros lo' hi' x Hin Hx. unfold wzone. apply in_app_iff in Hin as [Hin|Hin]; [| apply in_app_iff in Hin as [Hin|Hin]].
- cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; [do 3 right; lia| do 3 right; lia|].
left. apply PZ. right. apply PSH. lia.
- destruct (enq_W_zone a LB0 FS0 G (bv_unsigned sp + -80) lo' hi' x GC ltac:(unfold ENQ_STACK, QPOP_STACK; rlia) Hin Hx) as [Z|[Z|[Z|Z]]];
[do 3 right; rlia| left; left; split; cbn [fst snd]; rlia| first [ clear - Z; tauto | tauto ]| right; right; left; left; exact Z].
- destruct (WXB lo' hi' x Hin Hx) as (_ & j & Hj & Tj & Hxj).
destruct JTC as [[EJ _]|(jn & EJ & Tn' & Tn & _)].
+ left. do 5 right; left. exists 24, j, TQOwn. split; [rewrite EJ in Hj; exact (proj1 (List.Forall_forall _ _) FJT j Hj)|]. split; [reflexivity| exact Hxj].
+ rewrite EJ in Hj. apply in_app_iff in Hj as [Hj|[<-|[]]].
* left. do 5 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) FJT j Hj)|]. split; [reflexivity| exact Hxj].
*
right; left. do 4 right; left.
pose proof (slot_prim _ _ _ _ _ _ GC' 24 jn TQOwn Tj) as (P1 & P2 & P3 & P4 & C1 & R1 & R2 & _). pose proof kconsts as (_ & _ & _ & K32' & _).
destruct Hxj as [X1 X2]; cbn [fst snd] in X1, X2.
split; [exists 24; rewrite K32'; split; [lia| (first [ clear - R2 R1 X2 X1 x jn Enext a1 SHAB SHA Q6 Q5 Q4 Q3 Q1 r q G3 G2 G1 g phi plo u A p a RE BAND; lia | lia ])]|].
intros (c' & i' & t' & Ht' & NP & [Y1 Y2]). cbn [fst snd] in Y1, Y2.
destruct (TOT c' i' t' Ht') as [t'' Ht''].
destruct (decide (c' = 24 /\ i' = jn)) as [[-> ->]|NE].
-- destruct t' as [| |q'|q'|]; cbn in NP; try discriminate.
++ pose proof (proj1 (SLV 24 jn (TLive q') eq_refl) Ht') as L'. rewrite Tj in L'. discriminate.
++ pose proof (proj1 (TQI 24 jn q') Ht') as L'. rewrite Tj in L'. discriminate.
++ exact (Tn Ht').
-- pose proof (slots_disjoint _ _ _ _ _ _ GC' c' i' t'' 24 jn TQOwn Ht'' Tj ltac:(clear - NE; lia)) as SDJ. clear - SDJ Y1 Y2 X1 X2; lia. }
assert (EZ3 : forall lo' hi' x, In (lo', hi') ([(bv_unsigned sp + -80, bv_unsigned sp); (bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (SH A, SH A + g)]
++ (enq_W RE X (bv_unsigned sp + -80) a ++ Wx)) -> lo' <= x < hi' -> ezone a LB0 G RE X x).
{ intros lo' hi' x Hin Hx. unfold ezone. apply in_app_iff in Hin as [Hin|Hin]; [| apply in_app_iff in Hin as [Hin|Hin]].
- cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; [do 5 right; lia| do 5 right; lia|].
left. apply PZ. right. apply PSH. lia.
- destruct (enq_W_zone a LB0 FS0 G (bv_unsigned sp + -80) lo' hi' x GC ltac:(unfold ENQ_STACK, QPOP_STACK; rlia) Hin Hx) as [Z|[Z|[Z|Z]]];
[do 5 right; rlia| left; left; split; cbn [fst snd]; rlia| right; left; exact Z| right; right; left; exact Z].
- destruct (WXB lo' hi' x Hin Hx) as (_ & j & Hj & Tj & Hxj).
destruct JTC as [[EJ _]|(jn & EJ & Tn' & Tn & _)].
+ left. do 5 right; left. exists 24, j, TQOwn. split; [rewrite EJ in Hj; exact (proj1 (List.Forall_forall _ _) FJT j Hj)|]. split; [reflexivity| exact Hxj].
+ rewrite EJ in Hj. apply in_app_iff in Hj as [Hj|[<-|[]]].
* left. do 5 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) FJT j Hj)|]. split; [reflexivity| exact Hxj].
*
right; left. do 4 right; left.
pose proof (slot_prim _ _ _ _ _ _ GC' 24 jn TQOwn Tj) as (P1 & P2 & P3 & P4 & C1 & R1 & R2 & _). pose proof kconsts as (_ & _ & _ & K32' & _).
destruct Hxj as [X1 X2]; cbn [fst snd] in X1, X2.
split; [exists 24; rewrite K32'; split; [lia| (first [ clear - R2 R1 X2 X1 x jn Enext a1 SHAB SHA Q6 Q5 Q4 Q3 Q1 r q G3 G2 G1 g phi plo u A p a RE BAND; lia | lia ])]|].
intros (c' & i' & t' & Ht' & NP & [Y1 Y2]). cbn [fst snd] in Y1, Y2.
destruct (TOT c' i' t' Ht') as [t'' Ht''].
destruct (decide (c' = 24 /\ i' = jn)) as [[-> ->]|NE].
-- destruct t' as [| |q'|q'|]; cbn in NP; try discriminate.
++ pose proof (proj1 (SLV 24 jn (TLive q') eq_refl) Ht') as L'. rewrite Tj in L'. discriminate.
++ pose proof (proj1 (TQI 24 jn q') Ht') as L'. rewrite Tj in L'. discriminate.
++ exact (Tn Ht').
-- pose proof (slots_disjoint _ _ _ _ _ _ GC' c' i' t'' 24 jn TQOwn Ht'' Tj ltac:(clear - NE; lia)) as SDJ. clear - SDJ Y1 Y2 X1 X2; lia. }
assert (QRE3 : QREST C a1 LB0 FS0 G' RE X m3).
{ eapply (QREST_ext C a); [| exact Ereg| exact Enres| exact Espent| exact SLV].
eapply QREST_munch; [exact GC| exact QRE| exact MU3| exact WM3|]. intros lo' hi' x Hin Hx. eapply wzone_pzone. exact (WZ3 lo' hi' x Hin Hx). }

replace (ret_pc (wz 276144)) with (wz 276144) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply aimplT_from_evt.
step.
step.
pose proof (qwf_nonneg _ QWT3) as TQN.
destruct (Z.ltb_spec0 kQMaxCache (q_bytes (as_tq a1))) as [DR|NDR]; rewrite KMC in *.
2:{
ifz. step.
do 8 step. step. step.
release_frame FR3 ST3 (bv_unsigned sp).
apply evt_done. replace (kQMaxCache <? q_bytes (as_tq a1)) with false by (symmetry; apply Z.ltb_ge; rewrite KMC; (first [ clear - NDR Enext a1 phi plo A p a BAND; lia | lia ])).
apply aimplT_ret. apply evt_done.
unfold qret_post. do 15 eexists. exists m3, G'. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI3|]. split; [exact ST3|].
split; [eapply aheap_presA_of_munch_w; [exact GC| apply Permutation_refl| apply Permutation_refl| lia| exact MU3| exact WM3| exact WZ3]|].
split; [split; [eapply (depot_keep_of_pzone a LB0 FS0 G RE X m m3 _ GC MU3 WM3); intros lo' hi' x Hin Hx; eapply wzone_pzone; eapply WZ3; eassumption| eapply (errno_keep_of_ezone a LB0 FS0 G RE X m m3 _ GC MU3 WM3); exact EZ3]|].
split; [exact GC'|]. split; [apply QOTH_split; split; [exact RT3| split; [exact RS3| split; [exact RP3| exact QRE3]]]|].
apply (CLOSE QB). unfold QB. (first [ clear - NDR Enext a1 phi plo A p a BAND; lia | lia ]). }

ifz.
step. step.
step. step.
step.
apply evt_done. replace (kQMaxCache <? q_bytes (as_tq a1)) with true by (symmetry; apply Z.ltb_lt; rewrite KMC; lia).
eapply aimplT_then.
{ eapply (drain_spec C L RE X); [| exact MI3| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; unfold DRAIN_STACK, RECYCLE_STACK; lia
| unfold qroom in QRM; rewrite Egq; subst u; clear - QRM BY1; lia ].
split; [exact GC'|]. split; [apply QOTH_split; split; [exact RT3| split; [exact RS3| split; [exact RP3| exact QRE3]]]|].
apply (CLOSE (2 * QB)). unfold QB in *. lia. }
cbv beta. intros ar s'' ms'' PO. unfold qret_post in PO.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m4 & Gd & -> & -> & MI4 & ST4 & AP4 & DK4 & QR4).
rewrite !(unsigned_lit (bv_unsigned sp + -80)) in ST4, AP4 by lia.
lazymatch type of FR3 with rw_cells _ _ ?fa ?cs => assert (FR4 : rw_cells asegs m4 fa cs) end.
{ eapply rw_cells_agree; [exact AP4| exact FR3|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
replace (ret_pc (wz 275944)) with (wz 275944) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
do 8 step. step. step.
release_frame FR4 ST4 (bv_unsigned sp).
apply evt_done.
unfold qret_post. do 15 eexists. exists m4, Gd. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI4|]. split; [exact ST4|]. split; [| split; [| exact QR4]].
2:{  destruct DK4 as [DK4 EK4]. split.
- intros n0 H0. apply DK4. eapply (depot_keep_of_pzone a LB0 FS0 G RE X m m3 _ GC MU3 WM3); [| exact H0]. intros lo' hi' x Hin Hx. eapply wzone_pzone. eapply WZ3; eassumption.
- eapply errno_keep_trans; [| exact EK4]. eapply (errno_keep_of_ezone a LB0 FS0 G RE X m m3 _ GC MU3 WM3); exact EZ3. }
eapply aheap_presA_trans.
- eapply aheap_presA_of_munch_w; [exact GC| apply Permutation_refl| apply Permutation_refl| lia| exact MU3| exact WM3| exact WZ3].
- eapply aheap_presA_weaken; [exact AP4| lia| intros b Hb; exact Hb| intros f Hf; exact Hf].
Qed.
End S.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWHo QZzg Q61C QbcP_c1 QWRO QFQR QKBN QN4c QzdP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf QVsB QJFf.Mq0.
Import QCiC.Mq1 Qpj5.Mq1 QdZp Qk8e.Mq0 Q6sh QKTr.
Import QTVW.Mqc QWHo QcfN.Mq2. Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QpY2.Mqf.
Import Q9Ho.
Import QTVW.Mq8 Qu3b.Mq5 QnRU.Mqf QnRU QteI.Mqb Qu3b.Mq4 QQNJ.Mq8 QnaW QkZz QpzM.Mql QQNJ.Mq9 QzdP.
Import Q0z1.
Import QlES.
Local Unset Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_1 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_2 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.

Definition vprintf_stub : Z := 0x4fd64.
Definition vprintf_icpt_entry : Z := 0x53708.
Definition vfprintf_stub : Z := 0x4fd68.
Definition vfprintf_icpt_entry : Z := 0x5426c.

Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono asegs m m' -> 0x6460a8 <= lo -> stdout_file m' so.
Proof.
intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
- eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.

Lemma out_pieces_outsk : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps,
out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. intros St get_so set_so ps. induction ps as [|p ps IH]; cbn [out_pieces outsk]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma ssp_cells_munch : forall m m' W canary, ssp_cells m canary -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (snd iv <= got_ssp \/ got_ssp + 8 <= fst iv) /\ (snd iv <= ssp_guard \/ ssp_guard + 8 <= fst iv)) W -> ssp_cells m' canary.
Proof.
intros m m' W canary [G1 G2] MU WM HW. split.
- eapply rw_cells_apart; [exact G1| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [H _]. cbn in *. lia.
- eapply rw_cells_apart; [exact G2| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] [_ H]. cbn in *. lia.
Qed.

Section Emit.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

Theorem emit_printf_proof : emit_printf_stmt get_so set_so.
Proof.
unfold emit_printf_stmt. intros until v. intros GS SS FWX SF ISH0 HV HA1 ST LO GLO QHI SSP MI FRM.
unfold EMIT_DEPTH, GLOBALS_TOP in *.
assert (CEIL : band_lo <= lo) by (idtac; exact GLO).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m) as MU.
pose proof ISH0 as (ASH & RC & SB).

unfold s_emit, stdout_vprintf. rewrite out_pieces_outsk.
rewrite <- (outsk_OUT_stdout get_so set_so (pieces_emit_d v) (mret tt))
by (eapply Forall_impl; [| apply pieces_emit_d_short; exact HV]; cbv beta; intros; unfold OUT_MAX; lia).
eapply (implM_evt asegs). 2:{ intros ms' H; exact H. } cbv beta.

carve_frame 80%nat ST.
do 15 istep. rename FR into FRe.

step. carve_frame 48%nat ST. rename FR into FRv.
do 7 istep.
pose proof (rt_consts_at_munch _ _ _ RC MUs WM ltac:(rt_wzones)) as RCc.
pose proof printf_common_emit_d as PCD. unfold PCOMMON_STACK, pcommon_entry in PCD.
pose proof (rt_161720 _ RCc) as K18. pose proof (rt_157bb0 _ RCc) as K7. pose proof (rt_1f25bc _ RCc) as K22. pose proof (rt_159c68 _ RCc) as K17.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. istep. step. if_lit. istep. istep. istep. istep. step.

call_u PCD;
[ eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]
| assumption | unsigned_lits; exact ST | exact CEIL | unsigned_lits; lia |].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.

istep. istep. istep. istep. step.
do 7 istep.

step. carve_frame 48%nat ST. rename FR into FRf.
do 9 istep.
step. call_u tryinit_spec7; [exact K18| assumption| unsigned_lits; exact ST| exact CEIL| unsigned_lits; lia|].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.
step. if_lit. istep. istep. istep. istep. istep. step. if_lit. istep. istep. istep. istep. step.
call_u PCD;
[ eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]
| assumption | unsigned_lits; exact ST | exact CEIL | unsigned_lits; lia |].
match goal with H : stk asegs ?mc lo _ |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename H into ST end.

istep. istep. istep. istep. istep. step.
apply evt_done.
lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
assert (SFA : stdout_file mA (get_so st)) by (eapply stdout_file_stk; [exact SF| exact MUs| exact WM| lia]).
assert (SSPA : ssp_cells mA canary) by (eapply ssp_cells_munch; [exact SSP| exact MUs| exact WM| unfold got_ssp, ssp_guard; apply Forall_cons; [cbn; lia| apply Forall_nil]]).
assert (ISHA : ISH mA) by (eapply ISH_munch; [exact ISH0| exact MUs| exact WM| zforalls]).
clear MUs SF SSP K18 K7 K22 K17 RCc PCD.

pose proof FRe as VAC. apply (proj1 (rw_cells_app asegs _ _ [_;_;_] _)) in VAC. destruct VAC as [_ VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -80 + Z.of_nat 24) with (bv_unsigned sp + -56) in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA. clear VAC.
change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
eapply (implM_post_evt asegs).
{ eapply VF with (A := 0x14f44) (VA := bv_unsigned sp + -56) (fmt := FMT_emit_d) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i v])
(r := d_count v + 1) (lo := lo) (canary := canary);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
all: try reflexivity. all: try lia.
all: first [ exact SFA | exact ISHA
| apply fmt_bytes_at; [assumption | vm_compute; reflexivity | lia | vm_compute; discriminate]
| unfold FMT_emit_d; forall_range
| exact VAA
| cbn [args_ok arg_ok]; split; [|exact I]; split; [exact HV | exact HA1]
| rewrite printf_pieces_emit_d, d_pieces_emit by exact HV; reflexivity
| apply fp_calls_emit_d
| exact ST | exact SSPA | assumption | exact FRM
| unfold FMT_emit_d; cbn [length]; lia ]. }
cbv beta. intros [] st' ms' P. clear VF.
unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
transport_after_call asegs mA m3 MUc WMc. clear MUc WMc.
fixret.

do 5 istep. step. release_frame FRf ST3 (bv_unsigned sp + -128).
do 4 istep. step. release_frame FRv ST3 (bv_unsigned sp + -80).
do 2 istep. step. release_frame FRe ST3 (bv_unsigned sp).
apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [assumption|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed.
End Emit.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g QV3O QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QOJv.Mqc Qu3b QnaW.Mq3 QYyZ.Mqc QYyZ.Mqa.
Import QpY2.Mqc.
Import QpME.Mq8 QpF1 QQNJ.Mqa QQNJ.Mqb QRfV.Mq2 QEEn.
Import QcfN.Mq4.
Import QlES.
Export QteI.Mqf.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition malloc_icpt_entry : Z := 0x63880.
Definition asan_malloc_entry : Z := 0x3f238.

Definition MALLOC_STACK : Z := 3296.

Lemma bst_assemble : forall m obj (j0 j1 : list byte) (bpw : word),
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz 0); CB 80 j0] ->
rw_cells asegs m (obj + 96) [CB 1960 j1; C8 bpw] ->
exists (q0 q1 q2 q3 q4 : word) (rest : list byte),
rw_cells asegs m obj (unw_obj obj 0 [q0; q1; q2; q3; q4] rest (bv_unsigned bpw)).
Proof.
intros m obj j0 j1 bpw H0 H1.
assert (L0 : length j0 = 80%nat) by (destruct H0 as [[WF _] _]; cbn in WF; tauto).
assert (L1 : length j1 = 1960%nat) by (destruct H1 as [[WF _] _]; cbn in WF; tauto).
assert (H : rw_cells asegs m obj ([C8 (wz (obj + 16)); C8 (wz 0); CB 80 j0] ++ [CB 1960 j1; C8 bpw])).
{ apply (proj2 (rw_cells_app asegs m obj _ _)). cbn [cells_size csize Nat.add]. split; [exact H0| exact H1]. }
do 40 (let b := fresh "y" in destruct j0 as [|b j0]; [cbn in L0; lia|]). cbn in L0.
match type of H with context [CB 80 (?y0 :: ?y1 :: ?y2 :: ?y3 :: ?y4 :: ?y5 :: ?y6 :: ?y7 :: ?z0 :: ?z1 :: ?z2 :: ?z3 :: ?z4 :: ?z5 :: ?z6 :: ?z7 ::
?u0 :: ?u1 :: ?u2 :: ?u3 :: ?u4 :: ?u5 :: ?u6 :: ?u7 :: ?v0 :: ?v1 :: ?v2 :: ?v3 :: ?v4 :: ?v5 :: ?v6 :: ?v7 ::
?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: j0)] =>
exists (wz (bytes_le_to_Z [y0; y1; y2; y3; y4; y5; y6; y7])), (wz (bytes_le_to_Z [z0; z1; z2; z3; z4; z5; z6; z7])),
(wz (bytes_le_to_Z [u0; u1; u2; u3; u4; u5; u6; u7])), (wz (bytes_le_to_Z [v0; v1; v2; v3; v4; v5; v6; v7])),
(wz (bytes_le_to_Z [x0; x1; x2; x3; x4; x5; x6; x7])), (j0 ++ j1)
end.
eapply rw_cells_recast'; [exact H| |].
- unfold unw_obj. cbn. rewrite length_app. lia.
- unfold unw_obj. cbn [map app cells_bytes cbytes]. rewrite Z_to_bv_bv_unsigned.
rewrite (le8_split32 0) by lia. rewrite !le8_of_bytes by reflexivity.
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.

Definition micpt_W (bp T : Z) : list (Z * Z) := [(bp - 2128 - 144, bp); (T + 3168, T + 3169)].

Lemma malloc_icpt_pre : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo n : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - MALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
0 <= n < 2^64 ->
(forall m' (u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 : word) (sz : Z) (q : list word) (rest junk8 : list byte),
munch (micpt_W bp (rl_T X)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bp - 2128) ->
rw_cells asegs m' (bp - 2128) (unw_obj (bp - 2128) sz q rest bp) -> length q = 5%nat ->
1 <= sz <= 30 ->
rw_cells asegs m' (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
RTconst RE X m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] ->
evt asegs Q (MS (mkR (wz 0x639b4) (wz (bp + -2128)) gp (wz A_TP) u0 u1 u2 (wz bp) (wz n) (wz n) (wz (bp + -2128)) u3 u4 u5 u6 u7 u8
(wz 0x63948) (wz 1) (wz (bp + -2128)) (wz (bp + -81)) s6 s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz asan_malloc_entry) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x636a0) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL TU MI ST CEIL LO BPR UNW Hn CONT.
pose proof CEIL as CEIL'. idtac. unfold MALLOC_STACK in LO.
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
pose proof (munch_refl (micpt_W bp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold micpt_W in MU.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2128 - 144, bp); (rl_T X + 3168, rl_T X + 3169)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
unfold A_INSTANCE in *.
step.
carve_frame 2032%nat ST.
do 8 step.
step.
step.
carve_frame 96%nat ST.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_ch (try_asan_init_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2128)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
step. if_lit.
step. step. step. step. step.
stf.
step.
stf.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT2.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
stp. step. if_lit.
step. call0 (get_current_pc_spec); []. subst_words.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
stp.
step.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
step. stp. stp.
step.
rewrite (unsigned_lit bp), and_all_ones by lia.
stp.
step.
step. if_lit.
step. step. step. step. stp. step.

apply (proj1 (rw_cells_app asegs _ _ [CB 1960 _; C8 (wz bp)] _)) in FR as [FRa FRb].
lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bp + -64) in FRb by (cbn; lia) end.
replace (bp + -2032) with (bp + -2128 + 96) in FRa by lia.
replace (bp + -2112) with (bp + -2128 + 16) in FR0 by lia.
destruct (bst_assemble _ _ _ _ _ FR0 FRa) as (q0 & q1 & q2 & q3 & q4 & rest & OBJ). rewrite (unsigned_lit bp) in OBJ by lia. clear FR0 FRa.
pose proof FRb as FRc. apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FRc as [_ FRc].
lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bp - 16) in FRc by (cbn; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT4 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (URD : unw_readable asegs RE mc (bp - 16)) end.
{ eapply (unw_readable_prologue RE _ m _ bp s0 ra); [exact MU| intros z Hz; cbn [outside]; lia| exact FRc| exact UNW]. }
step.
call_ch (unwind_impl_spec RE X) ltac:(fun PO => unfold unwind_stack in PO; rewrite !(unsigned_lit (bp + -2128)) in PO by lia);
[exact RT4| exact RL| assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold unwind_stack; lia
| exact OBJ| exact TU| exact URD| lia| rewrite unsigned_lit by lia; lia| lia| lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST2 end.
destruct POST as (sz & q & rest' & OBJ2 & LQ & TU2 & SZR & RT5).
clear URD FRc RT4.
step. step. step.
step.
lazymatch type of FRb with rw_cells _ _ _ (CB 8 ?j8 :: _) =>
eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ sz q rest' j8); [exact MU| exact WM| assumption| exact ST2| exact OBJ2| exact LQ| exact SZR| exact FRb| exact RT5| exact TU2] end.
Qed.

Definition malloc_W (bp : Z) (c au : Z) : list (Z * Z) :=
(bp - MALLOC_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W RE X (bp - 2144) c au).

Definition malloc_post (ra : word) (bp : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (n lo : Z) (m : word -> option byte)
(r : option aptr * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo bp
/\ RTconst RE X m' /\ RStats RE X m' /\ RDepot RE X m' /\ depot_step m m'
/\ match r with
| (None, a1) => a0 = wz 0 /\ munch (malloc_W bp (class_of n) (c_alloc_user (cls a (class_of n)))) m m'
/\ qframe a a1 /\ gstep RE X a a1 G G1 /\ RPrim a1 G1 RE X m'
| (Some p, a2) => exists a1 i,
p = APrim (as_next a1) n /\ a2 = set_next (N.succ (as_next a1)) a1 /\ qframe a a1
/\ gstep RE X a a1 G G1 /\ tag_at G1 (class_of n) i = Some TCached /\ 0 <= i
/\ a0 = wz (slot_beg RE (class_of n) i + rz_size n)
/\ munch (malloc_W bp (class_of n) (c_alloc_user (cls a (class_of n))) ++ slot_W RE (class_of n) i) m m'
/\ (forall t, tag_prim t = false -> RPrim a1 (set_tag (class_of n) i t G1) RE X m')
/\ chunk_mem m' (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (slot_beg RE (class_of n) i + rz_size n) n
/\ hjunk m' (slot_beg RE (class_of n) i + rz_size n) (slot_beg RE (class_of n) i + class_size (class_of n))
end.

Lemma malloc_icpt_spec : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PStateA) (a : AState) (G : ghost) (LB : list ablock) (FS : list fframe) (lo n dn : Z),
gcons a LB FS G RE X ->
RTconst RE X m -> RStats RE X m -> RPrim a G RE X m -> RDepot RE X m -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - MALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
0 <= n -> from_primary n = true ->
aimplT atn (asan_malloc (ae_L RE) a n) s
(malloc_post ra bp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G n lo m)
(MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x636a0) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros GC RT RS RP RD MI ST CEIL LO BPR UNW DNH DCAP Hn HP.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof CEIL as CEIL'. idtac. unfold MALLOC_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 D02. pd_pair PD 0 2 D03. clear PD.
pose proof HP as HP'. apply from_primary_iff in HP'. unfold kMaxSize in HP'.
pose proof (class_of_facts n Hn HP) as (Hc & _). cbv zeta in Hc. set (c := class_of n) in *.
pose proof (needed_facts n Hn) as NF. pose proof (rz_size_range n) as [RZ1 RZ2].
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof (gc_bounds _ _ _ _ _ _ GC c ltac:(rewrite K32; lia)) as (AU1 & AU2 & AU3). rewrite KO in AU2.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL AU3.
pose proof (QKBN.rlay_obj_facts RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC. idtac. rewrite ?KHI_eq in NK.
pose proof (QKBN.rlay_obj_facts RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC. idtac. rewrite ?KHI_eq in BK.
pose proof (munch_refl (malloc_W bp c (c_alloc_user (cls a c))) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
apply aimplT_from_evt.
eapply malloc_icpt_pre; [exact RT| exact RL| exact (RDepot_unw RE X _ RD)| exact MI| exact ST| exact CEIL'| unfold MALLOC_STACK; lia| exact BPR| exact UNW| lia|].
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 sz q rest junk8 MU1 WM1 MI1 ST1 OBJ LQ SZR FR RT1 TU1.
unfold micpt_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RP1 : RPrim a G RE X m1).
{ eapply RPrim_frame; [exact RP| exact WM1|]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z Fz _. cbn [outside].
pose proof (fp_RPrim_lt_ceil G RE X z RL Fz). idtac.
split; [lia|]. split; [| exact I]. assert (z <> rl_T X + 3168) by (intros ->; exact (fpP_RDepot _ _ _ _ _ _ GC _ Fz ltac:(do 3 right; reflexivity))). lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RP RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_malloc_entry. carve_frame 16%nat ST1.
match goal with H : rw_cells asegs _ (bp + -2128 + -16) _ |- _ => replace (bp + -2128 + -16) with (bp + -2144) in H by lia end.
replace (bp + -2128 + -16) with (bp + -2144) in ST1 by lia.
pose proof (munch_refl [(bp - 2144, bp - 2128)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step.
step. step. step. stp. stp. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X a LB FS G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & FP & FD);
pose proof (FT RT1) as RT2; pose proof (FP RP1) as RP2; pose proof (FD RD1) as RD2;
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FP FD RT1 RP1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 977752) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_prim_spec L RE X _ _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s a G LB FS n 1 lo (bp + -2128) sz dn q30 GC RT2 RS2 RP2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post in PO. rewrite !(unsigned_lit (bp + -2144)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & G1 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 258660)) with (wz 258660) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END in REST. rewrite ?KS, ?KO in REST.
change (536870912 / 8) with 67108864 in REST. change (3758096384 / 8) with 469762048 in REST.
fold c in REST.
clear OBJh TRQ RT2 RP2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2128) (unw_obj (bp + -2128) sz q rest bp) ->
rw_cells asegs mx (bp + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2128) (unw_obj (bp + -2128) sz q rest bp ++ [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O1 O2. apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app]. replace (bp + -2128 + Z.of_nat 2064) with (bp + -64) by lia. exact O2. }
destruct r as [p|].
-
destruct REST as (aa & i & -> & -> & QF & GS & TI & I0 & -> & MUk & RPF & CM & HJU).
pose proof GS as (_ & _ & _ & GCT). pose proof (GCT LB FS GC) as GC1.
pose proof (tag_slot _ _ _ _ _ _ GC1 c i TCached TI) as (_ & _ & _ & SL1 & SL2 & SL3 & SL4 & _). rewrite KO in SL4.
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
assert (SHS : SH (reg_beg (ae_L RE) c) <= SH (slot_beg RE c i) /\ SH (slot_beg RE c i) + class_size c / 8 <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048).
rewrite <- SH_plus8. replace (8 * (class_size c / 8)) with (class_size c) by (clear - CS2; Z.div_mod_to_equations; lia). apply SH_le. lia. }
hide CS2.
apply (munch_weaken _ (malloc_W bp c (c_alloc_user (cls a c)) ++ slot_W RE c i)) in MU.
2:{ unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. intros z Hz. cbn [outside] in Hz |- *. clear - Hz. tauto. }
unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO in MU. cbn [tl app] in MU. rewrite ?KS, ?KO in MU.
change (536870912 / 8) with 67108864 in MU. change (3758096384 / 8) with 469762048 in MU.
cbn [app] in MUk. phase_done MU m2 m3 MUk WM3.
step. unfold_cond; cond_unsig; if_false.
step. step. step.
release_frame FR0 ST3 (bp + -2128).
step.
replace (ret_pc (wz 407988)) with (wz 407988) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 7 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
apply evt_done. unfold malloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST3|].
split; [exact RT3|]. split; [exact RS3|]. split; [exact RD3|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. exists aa, i. split; [reflexivity|]. split; [reflexivity|]. split; [exact QF|]. split; [exact GS|]. split; [exact TI|]. split; [exact I0|].
split; [reflexivity|]. split; [| split; [exact RPF| split; [exact CM| exact HJU]]].
unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, slot_W, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. exact MU.
-
destruct REST as (-> & MUk & QF & GS & RPk).
phase_done MU m2 m3 MUk WM3.
step. if_lit.
step.
pose proof (munch_refl [(bp - 2160, bp - 2144); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X a' LB FS G1 m3 mm _ (proj2 (proj2 (proj2 GS)) LB FS GC) MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & FP & FD) end.
pose proof (FT RT3) as RT4. pose proof (FP RPk) as RP4. pose proof (FD RD3) as RD4. clear FT FP FD MUe WMe RT3 RPk RD3 RS3.
step.
step. step. step.
release_frame FR0 ST4 (bp + -2128).
step.
replace (ret_pc (wz 407988)) with (wz 407988) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. do 7 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
apply evt_done. unfold malloc_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|].
split; [exact RT4|]. split; [exact RS4|]. split; [exact RD4|]. split; [eapply (depot_step_intro m _ dn); [exact DNH| unfold DEPOT_CAP in DCAP; lia| exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]]|].
cbn [fst snd]. split; [reflexivity|]. split; [| split; [exact QF| split; [exact GS| exact RP4]]].
unfold malloc_W, MALLOC_STACK, alloc_W, ALLOC_STACK, ri_addr, SS_BASE, DP_END, A_ERRNO. cbn [tl app]. rewrite ?KS, ?KO.
change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048. fold c. exact MU.
Qed.
End S.

End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QOJv.Mqb QmP7.Mq1 QYyZ.Mq8 QnRU.Mqc Q9Ho.Mq3 QOJv.Mqc.
Import QpY2.Mqc.
Import QXcn QpME.Mq7.
Import QYyZ.Mqc.
Import Qu3b QnRU.Mqj QmvA QkZz.Mq2 QteI.Mqi QcfN.Mq4.
Import QlES.
Import QnRU.Mqh.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac rlia := first [ lia_relh0 | lia_relh1 | lia ].
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition put_entry : Z := 0x43738.

Definition PUT_STACK : Z := 80 + DRAIN_STACK.

Lemma land_mask8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
intros x Hx.
assert (E : 18446744073709551608 = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3) with 8. pose proof (Z.div_mod x 8). lia.
Qed.

Lemma NoDup_app_In {A} : forall (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn in ND. inversion ND; subst.
destruct H1 as [<-|H1]; [apply H3; apply in_app_iff; right; exact H2| exact (IH l2 x H4 H1 H2)].
Qed.

Lemma qwf_nonneg : forall q, qwf q -> 0 <= q_bytes q.
Proof. intros q W. pose proof (qwf_length_bound q W). pose proof kq_consts as (_ & KBB & _). lia. Qed.

Section S.
Context {BAND : Band}.
Variables (C : arun_components) (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Hypothesis recycle_spec : recycle_stmt C RE X L.

Lemma enq_W_zone : forall a LB0 FS0 G (sp lo hi x : Z),
gcons a LB0 FS0 G RE X -> band_lo <= sp - ENQ_STACK ->
In (lo, hi) (enq_W RE X sp a) -> lo <= x < hi ->
(band_lo <= x < sp) \/ (rl_T X + 80 <= x < rl_T X + 112) \/ fp_RPrim G RE X x \/ in_iv (rl_T X + 2800, 368) x.
Proof.
intros a LB0 FS0 G sp lo hi x GC CE Hin Hx. pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof kconsts as (KR & KO & KS & K32 & KP & _). pose proof kq_consts as (K24 & _).
pose proof (gc_bounds a LB0 FS0 G RE X GC 24 ltac:(rewrite K32; lia)) as (B1 & B2 & B3).
pose proof (region_in_prim RE 24 ltac:(lia)) as (Q1 & Q2 & Q3 & Q4). pose proof (reg_beg_align RE X 24 RL) as (RAL & _ & FAL).
unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr in Hin. cbn [tl app In] in Hin. unfold ENQ_STACK, QPOP_STACK in CE.
destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-.
- left. lia.
- right; left. lia.
- right; right. destruct (Z.lt_ge_cases x (rl_T X + 2800)) as [LT|GE].
+ left. right; left. split; cbn [fst snd]; lia.
+ right. split; cbn [fst snd]; lia.
- do 2 right; left. left. unfold region_info in *. split; cbn [fst snd]; lia.
- do 2 right; left. do 2 right; left. exists 24. rewrite K32. split; [lia| lia].
- do 2 right; left. do 3 right; left. exists 24. rewrite K32. split; [lia|]. split; cbn [fst snd]; lia.
- do 2 right; left. do 4 right; left. split.
+ exists 24. rewrite K32. split; [lia| lia].
+ intros (c' & i' & t' & Ht' & _ & [S1 S2]). cbn [fst snd] in S1, S2.
pose proof (tag_slot a LB0 FS0 G RE X GC c' i' t' Ht') as (C1 & I1 & N1 & R1 & R2 & _).
pose proof (region_in_prim RE c' C1) as (Q1' & Q2' & Q3' & Q4').
assert (c' = 24 \/ c' + 1 <= 24 \/ 24 + 1 <= c') as [->|[D|D]] by lia; [(first [ clear - R1 R2 S1 S2 i' B1 Hx x a RE BAND; lia | lia ])| |];
pose proof (gc_bounds a LB0 FS0 G RE X GC c' ltac:(rewrite K32; lia)) as (B1' & B2' & B3'); rewrite KO in *; (first [ clear - B2' B1' D Q4' R2 S2 i' c' Q4 B1 Hx x a RE BAND R1 S1; lia | lia ]).
- do 2 right; left. do 5 right. split.
+ exists 24. rewrite K32. split; [lia|]. split; cbn [fst snd]; unfold SH, A_SHADOW_OFS in *; Z.div_mod_to_equations; (first [ clear - H23 H22 H21 H20 H19 q3 H14 q2 H5 H4 r0 H q FAL r2 RAL r Q2 B3 r3 B1 KO Hx q1 q0 x a RE BAND H26 H25 H15 r4; lia | lia ]).
+ intros (c' & i' & t' & Ht' & _ & [S1 S2]). cbn [fst snd] in S1, S2.
pose proof (tag_slot a LB0 FS0 G RE X GC c' i' t' Ht') as (C1 & I1 & N1 & R1 & R2 & _ & _ & SZ & SM & _).
pose proof (slot_beg_align RE X c' i' RL C1) as [_ SAL].
pose proof (region_in_prim RE c' C1) as (Q1' & Q2' & Q3' & Q4').
unfold SH, A_SHADOW_OFS in *.
assert (c' = 24 \/ c' + 1 <= 24 \/ 24 + 1 <= c') as [->|[D|D]] by lia;
[| pose proof (gc_bounds a LB0 FS0 G RE X GC c' ltac:(rewrite K32; lia)) as (B1' & B2' & B3')
| pose proof (gc_bounds a LB0 FS0 G RE X GC c' ltac:(rewrite K32; lia)) as (B1' & B2' & B3')];
rewrite KO in *; Z.div_mod_to_equations; (first [ clear - H38 H37 H36 H35 H34 q6 H29 q5 H24 q4 H10 H9 r1 H5 H4 r0 H R1 R2 SZ SAL r Q2' S2 q0 q i' FAL r4 RAL r5 B3 r6 B1 Hx q2 q1 x a RE BAND H41 H40 H23 H22 H21 H20 H19 q3 B3' r3 B2' B1' D Q4' c' Q4 r7 H15 H14 r2 S1; lia | lia ]).
Qed.

Lemma put_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (p : aptr) (A lo : Z),
QRUN C 0 QB QB [(p, A)] a LB0 FS0 G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - PUT_STACK ->
0 <= aptr_req p <= 2^26 ->
qroom a p ->
aimplT atn (tbind (enqueue (ae_L RE) a p) (fun s1 => if kQMaxCache <? q_bytes (as_tq s1) then drain (ae_L RE) s1 else tret s1)) s
(qret_post C RE X ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 FS0 lo m (free_keep asegs))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz QOBJ) (wz (TQ X)) (wz (rl_T X + 208)) a3 (wz (A - 16)) (wz (aptr_used p)) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz put_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros QR MI ST CEIL LO HN QRM.
pose proof CEIL as CEIL'. idtac. unfold PUT_STACK, DRAIN_STACK, RECYCLE_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kq_consts as (K24 & KBB & KBC & KMX & KMN & KMC). pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
destruct QR as (GC & QO & RQ). pose proof (gc_rlay _ _ _ _ _ _ GC) as RL.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PC & _). unfold prim_hi, prim_lo in PK, PC, TD. rewrite ?KHI_eq in PK. idtac.
apply QOTH_split in QO as (RT & RS & RP & QRE).
destruct RQ as (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND). unfold QB in BND.
apply Forall_cons_iff in PQA as [EQA _]. cbn [fst snd] in EQA.
assert (HU : 1 <= aptr_used p <= 2^26 + 1) by (unfold aptr_used, used_size; lia).
set (u := aptr_used p) in *. set (n := aptr_req p) in *.

pose proof (REP p ltac:(left; reflexivity)) as REPp.
assert (PC0 : exists lo_ hi_, qchunk_mem m lo_ hi_ A n
/\ (forall x, lo_ <= x < hi_ \/ in_sh (lo_, hi_ - lo_) x -> fp_RQuar a LB0 G RE X x)
/\ match p with
| APrim id n0 => exists i, tag_at G (class_of n0) i = Some (TQuar p) /\ lo_ = slot_beg RE (class_of n0) i /\ hi_ = lo_ + class_size (class_of n0)
| ASec mb n0 => In (mkSec mb (sec_map_size n0) n0) (as_reg a) /\ lo_ = mb + kPage /\ hi_ = mb + sec_map_size n0
end).
{ destruct p as [id n0|mb n0]; cbn [qptr_rep] in REPp; subst n; cbn [aptr_req] in *.
- destruct REPp as (i & Ht & Hpr & HQA & QM). rewrite EQA in QM. exists (slot_beg RE (class_of n0) i), (slot_beg RE (class_of n0) i + class_size (class_of n0)).
split; [exact QM|]. split; [| exists i; auto].
intros x [Hx|Hx]; [do 5 right; left| do 6 right; left]; exists (class_of n0), i, (TQuar (APrim id n0)); (split; [exact Ht|]); (split; [reflexivity|]).
+ split; cbn [fst snd]; lia.
+ replace (slot_beg RE (class_of n0) i + class_size (class_of n0) - slot_beg RE (class_of n0) i) with (class_size (class_of n0)) in Hx by lia. exact Hx.
- destruct REPp as (Hin & Hnl & Hpr & HQA & QM). rewrite EQA in QM. exists (mb + kPage), (mb + sec_map_size n0).
split; [exact QM|]. split; [| auto].
intros x [Hx|Hx]; [do 7 right; left| do 8 right]; exists (mkSec mb (sec_map_size n0) n0); cbn [se_beg se_size se_req]; (split; [exact Hin|]); (split; [exact Hnl|]).
+ lia.
+ replace (mb + sec_map_size n0 - (mb + kPage)) with (sec_map_size n0 - kPage) in Hx by lia. exact Hx. }
destruct PC0 as (plo & phi & QMp & PZ & PWHERE).
pose proof (qchunk_geom _ _ _ _ _ QMp) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & q & g & r & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
rewrite ?KHI_eq in G3. idtac. apply appr_to_lia in G3; [| lia| lia].
destruct QMp as (LEFTp & (b1 & idw & Hb1 & HDRp) & JUNKp & (sj & SHDp) & PUREp). unfold qhdr_cells in HDRp.

apply (proj1 (rw_cells_app asegs m (SH plo) [CB (Z.to_nat ((A - plo) / 8)) (fas ((A - plo) / 8))] _)) in SHDp as [SHL SHDp].
apply (proj1 (rw_cells_app asegs m _ [CB (Z.to_nat (ngran (used_size n))) sj] _)) in SHDp as [SHMp SHR].
cbn [cells_size csize] in SHMp, SHR. rewrite !Nat.add_0_r, !Z2Nat.id in SHMp, SHR by lia.
assert (SHA : SH plo + (A - plo) / 8 = SH A) by (unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; (first [ clear - H34 q7 H10 H9 r2 q2 H5 H4 r1 H0 H r0 q0 Q5 Q3 Q1 g q G2 G1 PUREp r7 r6 r5 r4 q1 phi plo PK TK n A p X RE BAND; lia | lia ])). rewrite SHA in SHMp, SHR.
assert (SHAB : 0x7fff8000 <= SH plo /\ SH A + g + r <= SH band_lo /\ SH plo + q = SH A) by (unfold SH, A_SHADOW_OFS in *; Z.div_mod_to_equations; (first [ clear - H39 q8 H15 H14 r3 H10 H9 r2 q2 H0 H r0 SHA Q8 Q7 Q5 Q1 r g q G4 G3 G1 PUREp r8 r7 r6 r5 q1 q3 q0 phi plo PK TK n A p X RE BAND; lia | lia ])).
pose proof SH_band as SHBD0.
pose proof (used_size_pos n ltac:(lia)) as [U1 U2].
assert (UN : used_size n = u) by (subst u n; reflexivity).
rewrite UN in *.
rtc RT 26%nat K26. rtc RT 19%nat K19. rtc RT 12%nat K12.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (bv_unsigned sp - 80 - 64, bv_unsigned sp - 80); (SH A, SH A + g)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
unfold put_entry, QOBJ, TQ, GQ, QMUT, A_INSTANCE in *.
change (977752 + 888) with 978640 in *. change (977752 + 880) with 978632 in *. change (977752 + 728) with 978480 in *.
change (977752 + 792) with 978544 in *.
pose proof HM as HM0. hide HM0.
apply aimplT_from_evt.
carve_frame 80%nat ST.
do 9 step.
step.
step. step.
step.
step.
step. if_false.
step.
step. ifz.
step. step. step.
step. step.
step.
step. if_lit.
step. step.
change (zx16 (wz 0)) with (wz 0). rewrite (zx32_small u) by lia.
step.
replace (A - 16 + 16) with A by lia.
step. step.
rewrite (unsigned_lit u) by lia. rewrite Z.lor_0_l.
step. step.
rewrite (unsigned_lit (u + 7)) by lia. rewrite land_mask8 by lia.
replace (u + 7 - (u + 7) mod 8) with (8 * g) by (unfold round_up in Q3; Z.div_mod_to_equations; (first [ clear - H10 H9 r2 H0 H r0 q0 U1 Q8 Q6 Q4 Q3 q2 Q1 r g q G2 G1 phi plo HU u PK TK A p X RE BAND; lia | lia ])).
step. step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM|
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [apply (rt_avoid_gap RE X RL); rewrite ?KHI_eq; lia| constructor]]]]) end.
hide MU.
rewrite Q4 in SHMp.
eapply evt_cut.
{ eapply (poison_shadow_spec_lh RE X); try eassumption; rewrite ?unsigned_lit by lia.
- exact ST.
- lia.
- Z.div_mod_to_equations; (first [ clear - H29 q6 H0 H r0 q0 Q5 Q3 G2 G1 PUREp r6 r5 r4 r3 g phi plo u PK TK n A p X RE BAND; lia | lia ]).
- Z.div_mod_to_equations; (first [ clear - H0 H r0 q0 Q5 Q4 Q3 G2 G1 g phi plo u PK TK A p X RE BAND; lia | lia ]).
- lia.
- rewrite ?KHI_eq; change (2^47) with 140737488355328; (first [ clear - SHAB SHA Q6 Q5 Q4 Q3 Q1 r q G4 G3 G2 G1 g phi plo u A p BAND; lia | lia ]).
- lia.
- left; lia.
- rewrite (Z.mul_comm 8 g), Z.div_mul by lia. exact SHMp. }
cbv beta. intros ms' PO.
destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MUp & WMp & MIp & STp & RTp & SHM2).
rewrite (Z.mul_comm 8 g), Z.div_mul in MUp, SHM2 by lia. rewrite !(unsigned_lit (bv_unsigned sp + -80)) in MUp, STp by lia.
clear SHMp. unhide MU.
lazymatch type of MUp with munch _ ?mx _ =>
apply (munch_chain' _ _ m2 _ m MUp) in MU; [| sub_fp_solve];
transport_after_call asegs mx m2 MUp WMp; clear MUp end.
replace (SH A + Z.of_nat (Z.to_nat (ngran u) + 0)) with (SH A + g) in SHR by (rewrite Nat.add_0_r, Z2Nat.id; lia).
replace (ret_pc (wz 276676)) with (wz 276676) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
do 5 step.
step.
apply evt_done.

set (Qs' := qptrs (as_tq a) ++ qptrs (as_gq a)) in *.
assert (EQQ : qall [(p, A)] a = p :: Qs') by reflexivity.
assert (NDQ : List.NoDup (p :: Qs')) by (rewrite <- EQQ; exact NDP).
assert (NIp : ~ In p Qs') by (inversion NDQ; assumption).
assert (REP' : forall q', In q' Qs' -> qptr_rep a LB0 G RE m QA q') by (intros q' Hq; apply REP; rewrite EQQ; right; exact Hq).
pose proof HT as (TQC & BMT & FJT & QWT). pose proof HG as (GQC & BMG & FJG & QWG).
assert (FJ : Forall (fun j => tag_at G 24 j = Some TQOwn) (JT ++ JG)) by (apply Forall_app; split; assumption).

assert (AG1 : agree_on asegs (fun x => rq_keep G RE (JT ++ JG) Qs' x \/ rl_T X + 80 <= x < rl_T X + 112) m m2).
{ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Kx _. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- destruct Kx as [Kx|Kx]; [| lia]. exact (keep_pzoneP a LB0 FS0 G RE X GC QA (JT ++ JG) Qs' FJ m REP' x ltac:(right; right; lia) Kx).
- destruct Kx as [Kx|Kx]; [| lia]. exact (keep_pzoneP a LB0 FS0 G RE X GC QA (JT ++ JG) Qs' FJ m REP' x ltac:(right; right; lia) Kx).
- destruct Kx as [Kx|Kx]; [| (first [ clear - Y2 Y1 Kx x SHBD0 SHAB SHA Q8 Q5 Q3 Q1 r q G7 G6 G2 G1 PUREp g phi plo u PK TK n A p X RE BAND; lia | lia ])].
destruct p as [id n0|mb n0]; cbn [aptr_req] in *.
+ destruct PWHERE as (i & Ht & Elo & Ehi).
refine (keep_slot a LB0 FS0 G RE X GC QA (JT ++ JG) Qs' FJ m REP' (class_of n0) i _ x Ht _ _ _ Kx).
* intros E24 Hi. pose proof (proj1 (List.Forall_forall _ _) FJ i Hi) as Ti. rewrite E24, Ti in Ht. discriminate.
* intros id' n' E Hq. injection E as <- <-. exact (NIp Hq).
* right. rewrite <- Elo. replace (class_size (class_of n0)) with (phi - plo) by lia.
split; cbn [fst snd]; [lia|]. rewrite Q8, (Z.mul_comm 8), Z.div_mul by lia. lia.
+ destruct PWHERE as (Hin & Elo & Ehi).
refine (keep_sec a LB0 FS0 G RE X GC QA (JT ++ JG) Qs' FJ m REP' (mkSec mb (sec_map_size n0) n0) x Hin _ _ Kx); cbn [se_beg se_size].
* intros n' Hq. pose proof (REP' _ Hq) as (Hin' & _). cbn [qptr_rep] in Hin'.
pose proof (NoDup_map_In_inj se_beg (as_reg a) _ _ (gc_sec_nodup a LB0 FS0 G RE X GC) Hin Hin' eq_refl) as E. injection E as En. subst n'. exact (NIp Hq).
* right. rewrite <- Elo. replace (sec_map_size n0 - kPage) with (phi - plo) by lia.
split; cbn [fst snd]; [lia|]. rewrite Q8, (Z.mul_comm 8), Z.div_mul by lia. lia. }

assert (RS2 : RStats RE X m2).
{ eapply RStats_munch; [exact RS| exact MU| exact WM|]. unfold A_ERRNO in *.
constructor; [st_avoid_solve|]. constructor; [st_avoid_solve|].
constructor; [st_avoid_solve| constructor]. }
assert (PSH : forall x, SH A <= x < SH A + g -> in_sh (plo, phi - plo) x).
{ intros x Hx. split; cbn [fst snd]; [lia|]. rewrite Q8, (Z.mul_comm 8), Z.div_mul by lia. lia. }
assert (RP2 : RPrim a G RE X m2).
{ eapply RPrim_frame; [exact RP| exact WM|]. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Fx _. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- apply (fpQ_RPrim a LB0 FS0 G RE X GC x); [apply PZ; right; apply PSH; lia| exact Fx]. }
assert (QT2 : qrep RE G m2 QA (rl_T X + 80) (as_tq a) JT).
{ eapply qrep_agree; [exact AG1| exact HT| intros x Hx; right; lia| |].
- intros j x Hj Hx. left. do 4 right; left. exists j. split; [apply in_app_iff; left; exact Hj| left; exact Hx].
- intros j x Hj Hx. left. do 4 right; left. exists j. split; [apply in_app_iff; left; exact Hj| right; exact Hx]. }

assert (REPall : forall q', In q' (p :: Qs') -> qptr_rep a LB0 G RE m QA q') by (intros q' Hq; apply REP; rewrite EQQ; exact Hq).
destruct (rq_transport a LB0 G RE QA JG Qs' m m2 (as_gq a) 0) as (GQ2 & HM2 & HI2 & REP2).
{ eapply agree_on_mono; [exact AG1|]. intros x Kx. left. revert Kx. unfold rq_keep. intros [K|[K|[K|[K|[K|[K|K]]]]]]; try (clear - K; tauto).
do 4 right; left. destruct K as (j & Hj & K). exists j. split; [apply in_app_iff; right; exact Hj| exact K]. }
{ exact HG. } { unhide HM0. exact HM0. } { exact HI. } { exact REP'. }
clear HM HM0.

assert (QMp2 : qchunk_mem m2 plo phi A n).
{ assert (AGp : agree_on asegs (fun x => (plo <= x < phi) \/ (SH plo <= x < SH A) \/ (SH A + g <= x < SH A + g + r)) m m2).
{ eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Hx _. apply outside_intro. intros lo' hi' Hin [Y1 Y2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; rlia. }
split; [| split; [| split; [| split; [| exact PUREp]]]].
- intros Hrz. destruct (LEFTp Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AGp| exact L1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia.
+ eapply hjunk_agree; [exact AGp| exact L2|]. intros x Hx. left. lia.
- exists b1, idw. split; [exact Hb1| exact HDRp].
- eapply hjunk_wmono; [exact JUNKp| exact WM].
- exists (repeat (b8 253) (Z.to_nat g)). rewrite UN.
apply (proj2 (rw_cells_app asegs m2 (SH plo) [CB (Z.to_nat ((A - plo) / 8)) (fas ((A - plo) / 8))] _)). split; [exact SHL|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id, SHA by lia.
apply (proj2 (rw_cells_app asegs m2 (SH A) [CB (Z.to_nat (ngran u)) (repeat (b8 253) (Z.to_nat g))] _)). rewrite Q4. split; [exact SHM2|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact SHR. }
clear HDRp SHL SHM2 SHR JUNKp LEFTp.

eapply aimplT_bind.
{ eapply aimplT_tall; [apply (enqueue_qptrs (ae_L RE)); lia|].
replace (wz (A - 16)) with (wz (QA p - 16)) by (rewrite EQA; reflexivity).
eapply (enqueue_spec L RE X); try eassumption; rewrite ?unsigned_lit by lia.
- exact STp.
- unfold ENQ_STACK, QPOP_STACK. lia.
- exact (NoDup_app_remove_r _ _ ND).
- rewrite EQA. lia.
- lia. }
cbv beta. intros a1 s' ms' [QF PO].
destruct QF as (EQP & BY1 & Egq & Ereg & Enres & Espent & Enext).
destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & G' & JT' & Wx
& -> & -> & MUq & WMq & MI3 & ST3 & HWx & RT3 & RS3 & RP3 & QT3 & QF3 & EG).
rewrite !(unsigned_lit (bv_unsigned sp + -80)) in MUq, ST3 by lia.
clear STp MIp RTp RT1 RS2 RP2 QT2.
destruct EG as (SLV & TQI & TOT & GCT & JTC).
pose proof (GCT LB0 FS0 GC) as GC'.

assert (JNG : forall j, In j JT' -> In j JG -> False).
{ intros j Hj HjG. destruct JTC as [[-> _]|(jn & -> & Tn' & Tn & _)].
- exact (NoDup_app_In JT JG j ND Hj HjG).
- apply in_app_iff in Hj as [Hj|[<-|[]]]; [exact (NoDup_app_In JT JG j ND Hj HjG)|].
apply Tn. exact (proj1 (List.Forall_forall _ _) FJG jn HjG). }
assert (FJG' : Forall (fun j => tag_at G' 24 j = Some TQOwn) JG).
{ apply List.Forall_forall. intros j Hj. pose proof (proj1 (List.Forall_forall _ _) FJG j Hj) as Tj.
destruct JTC as [[_ TQO2]|(jn & EJ & Tn' & Tn & TQO2)]; [apply TQO2; exact Tj|].
apply TQO2; [| exact Tj]. right. intros ->. exact (Tn Tj). }
pose proof QT3 as (TQC3 & BMT3 & FJT3 & QWT3). unfold TQ in TQC3.
assert (REPall' : forall q', In q' (p :: Qs') -> qptr_rep a1 LB0 G' RE m QA q').
{ intros q' Hq. eapply qptr_rep_ext; [exact (REPall q' Hq)| exact Ereg| exact TQI]. }

assert (WXB : forall lo' hi' x, In (lo', hi') Wx -> lo' <= x < hi' -> al_space_beg (ae_L RE) <= x < al_space_beg (ae_L RE) + 2^37 + 4096
/\ exists j, In j JT' /\ tag_at G' 24 j = Some TQOwn /\ in_iv (slot_beg RE 24 j, class_size 24) x).
{ intros lo' hi' x Hin Hx. pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as (j & Hj & B1 & B2). cbn [fst snd] in B1, B2.
pose proof (proj1 (List.Forall_forall _ _) FJT3 j Hj) as Tj.
pose proof (slot_prim _ _ _ _ _ _ GC' 24 j TQOwn Tj) as (P1 & P2 & _). unfold prim_hi, prim_lo in P1, P2. rewrite class_size_24 in P2.
split; [lia|]. exists j. split; [exact Hj|]. split; [exact Tj|]. split; cbn [fst snd]; rewrite ?class_size_24; lia. }
lazymatch type of FR with rw_cells _ _ ?fa ?cs => assert (FR3 : rw_cells asegs m3 fa cs) end.
{ eapply rw_cells_agree; [| exact FR|].
- eapply agree_on_of_munch; [exact MUq| exact WMq|]. intros x Hx _; exact Hx.
- intros x Hx; cbn [cells_size csize Nat.add] in Hx. apply outside_intro. intros lo' hi' Hin Hy.
apply in_app_iff in Hin as [Hin|Hin].
+ destruct (enq_W_zone a LB0 FS0 G (bv_unsigned sp + -80) lo' hi' x GC ltac:(unfold ENQ_STACK, QPOP_STACK; rlia) Hin Hy) as [Z|[Z|[Z|Z]]];
[ rlia | rlia | pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Z); rlia | assert (Z' : fp_RStats RE X x) by (left; exact Z); pose proof (fp_lt_ceil a LB0 FS0 G RE X GC x ltac:(first [ clear - Z'; tauto | tauto ])); rlia ].
+ destruct (WXB lo' hi' x Hin Hy) as [B _]. lia. }
clear FR.

assert (REPp2 : qptr_rep a1 LB0 G' RE m2 QA p).
{ pose proof (REP p ltac:(left; reflexivity)) as R. destruct p as [id n0|mb n0]; cbn [qptr_rep aptr_req] in R |- *; subst n.
- destruct R as (i & Ht & Hpr & HQA & _). destruct PWHERE as (i' & Ht' & Elo & Ehi).
pose proof (gc_unique a LB0 FS0 G RE X GC _ _ _ _ (APrim id n0) _ _ Ht Ht' ltac:(unfold holds; apply aptr_eqb_refl') ltac:(unfold holds; apply aptr_eqb_refl')) as [_ <-].
exists i. split; [apply TQI; exact Ht|]. split; [exact Hpr|]. split; [exact HQA|]. rewrite EQA. subst plo phi. exact QMp2.
- destruct R as (Hin & Hnl & Hpr & HQA & _). destruct PWHERE as (_ & Elo & Ehi). cbn [as_reg set_gq set_tq] in *. rewrite Ereg.
split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|]. rewrite EQA. subst plo phi. exact QMp2. }
assert (REP2' : forall q', In q' (p :: Qs') -> qptr_rep a1 LB0 G' RE m2 QA q').
{ intros q' [<-|Hq]; [exact REPp2|]. eapply qptr_rep_ext; [exact (REP2 q' Hq)| exact Ereg| exact TQI]. }
assert (GQ2' : qrep RE G' m2 QA 978640 (as_gq a) JG).
{ destruct GQ2 as (C1 & B1 & _ & W1). split; [exact C1|]. split; [exact B1|]. split; [exact FJG'| exact W1]. }

destruct (rq_transport a1 LB0 G' RE QA JG (p :: Qs') m2 m3 (as_gq a) 0) as (GQ3 & HM3 & HI3 & REP3).
{ eapply agree_on_of_munch; [exact MUq| exact WMq|]. intros x Kx _. apply outside_intro. intros lo' hi' Hin Hy.
apply in_app_iff in Hin as [Hin|Hin].
- pose proof (rq_keep_tags G' G RE JG (p :: Qs') x ltac:(intros; symmetry; apply TQI) Kx) as KxG.
destruct (enq_W_zone a LB0 FS0 G (bv_unsigned sp + -80) lo' hi' x GC ltac:(unfold ENQ_STACK, QPOP_STACK; lia) Hin Hy) as [Z|[Z|[Z|Z]]].
+ exact (keep_pzoneP a LB0 FS0 G RE X GC QA JG (p :: Qs') FJG m REPall x ltac:(right; right; lia) KxG).
+ exact (keep_TQ a LB0 FS0 G RE X GC QA JG (p :: Qs') FJG m REPall x ltac:(lia) KxG).
+ exact (keep_pzoneP a LB0 FS0 G RE X GC QA JG (p :: Qs') FJG m REPall x ltac:(left; exact Z) KxG).
+ exact (keep_pzoneP a LB0 FS0 G RE X GC QA JG (p :: Qs') FJG m REPall x ltac:(right; left; left; exact Z) KxG).
- destruct (WXB lo' hi' x Hin Hy) as (_ & j & Hj & Tj & Hx).
refine (keep_slot a1 LB0 FS0 G' RE X GC' QA JG (p :: Qs') FJG' m REPall' 24 j TQOwn x Tj _ _ (or_introl Hx) Kx).
+ intros _ HjG. exact (JNG j Hj HjG).
+ intros id' n' E _. discriminate E. }
{ exact GQ2'. } { exact HM2. } { exact HI2. } { exact REP2'. }
clear GQ2 GQ2' HM2 HI2 REP2 REP2' REPp2 QMp2.

assert (EQ1 : qptrs (as_tq a1) = qptrs (as_tq a) ++ [p]) by (unfold qptrs; exact EQP).
assert (PERM : Permutation (qall [] a1) (p :: Qs')).
{ unfold qall. cbn [map app]. rewrite EQ1, Egq. subst Qs'. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
assert (CLOSE : forall bt, q_bytes (as_tq a1) <= bt -> RQuarM 0 bt QB [] a1 LB0 G' RE X m3).
{ intros bt Hbt. exists JT', JG, QA.
split; [exact QT3|]. split; [rewrite Egq; exact GQ3|]. split; [exact HM3|]. split; [exact HI3|].
split.
{ destruct JTC as [[-> _]|(jn & -> & Tn' & Tn & _)]; [exact ND|].
apply (Permutation_NoDup (l := jn :: JT ++ JG)); [rewrite <- app_assoc; cbn [app]; apply Permutation_middle|].
constructor; [| exact ND]. intros Hin. apply Tn. exact (proj1 (List.Forall_forall _ _) FJ jn Hin). }
split.
{ intros j Tj'. destruct JTC as [[-> TQO2]|(jn & -> & Tn' & Tn & TQO2)].
- apply TQO. apply TQO2. exact Tj'.
- destruct (Z.eq_dec j jn) as [->|NE]; [apply in_app_iff; left; apply in_app_iff; right; left; reflexivity|].
pose proof (TQO j (proj2 (TQO2 24 j (or_intror NE)) Tj')) as IN. rewrite <- app_assoc. cbn [app].
apply in_app_iff in IN. apply in_app_iff. destruct IN as [IN|IN]; [left; exact IN| right; right; exact IN]. }
split.
{ intros c j Tj'. destruct (Z.eq_dec c 24) as [E|NE]; [exact E|]. exfalso. apply NE.
destruct JTC as [[_ TQO2]|(jn & _ & Tn' & Tn & TQO2)]; [exact (C24 c j (proj2 (TQO2 c j) Tj'))| exact (C24 c j (proj2 (TQO2 c j (or_introl NE)) Tj'))]. }
split; [eapply Permutation_NoDup; [apply Permutation_sym; exact PERM| exact NDQ]|].
split; [intros q' Hq; apply REP3; eapply Permutation_in; [exact PERM| exact Hq]|].
split.
{ intros c i q' Ht'. pose proof (TQP c i q' (proj2 (TQI c i q') Ht')) as [IN CL]. split; [| exact CL].
eapply Permutation_in; [apply Permutation_sym; exact PERM|]. rewrite <- EQQ. exact IN. }
split; [constructor|]. rewrite Egq. pose proof (qwf_nonneg _ QWT3). unfold QB in *. lia. }

assert (MU3 : munch ([(bv_unsigned sp + -80, bv_unsigned sp); (bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (SH A, SH A + g)]
++ (enq_W RE X (bv_unsigned sp + -80) a ++ Wx)) m m3).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUq]];
intros x Hx; apply outside_app in Hx as [Hx1 Hx2]; [exact Hx1| exact Hx2]. }
pose proof (wmono_trans asegs _ _ _ WM WMq) as WM3.
assert (WZ3 : forall lo' hi' x, In (lo', hi') ([(bv_unsigned sp + -80, bv_unsigned sp); (bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (SH A, SH A + g)]
++ (enq_W RE X (bv_unsigned sp + -80) a ++ Wx)) -> lo' <= x < hi' -> wzone a LB0 G RE X (bv_unsigned sp) x).
{ intros lo' hi' x Hin Hx. unfold wzone. apply in_app_iff in Hin as [Hin|Hin]; [| apply in_app_iff in Hin as [Hin|Hin]].
- cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; [do 3 right; lia| do 3 right; lia|].
left. apply PZ. right. apply PSH. lia.
- destruct (enq_W_zone a LB0 FS0 G (bv_unsigned sp + -80) lo' hi' x GC ltac:(unfold ENQ_STACK, QPOP_STACK; rlia) Hin Hx) as [Z|[Z|[Z|Z]]];
[do 3 right; rlia| left; left; split; cbn [fst snd]; rlia| first [ clear - Z; tauto | tauto ]| right; right; left; left; exact Z].
- destruct (WXB lo' hi' x Hin Hx) as (_ & j & Hj & Tj & Hxj).
destruct JTC as [[EJ _]|(jn & EJ & Tn' & Tn & _)].
+ left. do 5 right; left. exists 24, j, TQOwn. split; [rewrite EJ in Hj; exact (proj1 (List.Forall_forall _ _) FJT j Hj)|]. split; [reflexivity| exact Hxj].
+ rewrite EJ in Hj. apply in_app_iff in Hj as [Hj|[<-|[]]].
* left. do 5 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) FJT j Hj)|]. split; [reflexivity| exact Hxj].
*
right; left. do 4 right; left.
pose proof (slot_prim _ _ _ _ _ _ GC' 24 jn TQOwn Tj) as (P1 & P2 & P3 & P4 & C1 & R1 & R2 & _). pose proof kconsts as (_ & _ & _ & K32' & _).
destruct Hxj as [X1 X2]; cbn [fst snd] in X1, X2.
split; [exists 24; rewrite K32'; split; [lia| (first [ clear - R2 R1 X2 X1 x jn Enext a1 SHAB SHA Q6 Q5 Q4 Q3 Q1 r q G3 G2 G1 g phi plo u A p a RE BAND; lia | lia ])]|].
intros (c' & i' & t' & Ht' & NP & [Y1 Y2]). cbn [fst snd] in Y1, Y2.
destruct (TOT c' i' t' Ht') as [t'' Ht''].
destruct (decide (c' = 24 /\ i' = jn)) as [[-> ->]|NE].
-- destruct t' as [| |q'|q'|]; cbn in NP; try discriminate.
++ pose proof (proj1 (SLV 24 jn (TLive q') eq_refl) Ht') as L'. rewrite Tj in L'. discriminate.
++ pose proof (proj1 (TQI 24 jn q') Ht') as L'. rewrite Tj in L'. discriminate.
++ exact (Tn Ht').
-- pose proof (slots_disjoint _ _ _ _ _ _ GC' c' i' t'' 24 jn TQOwn Ht'' Tj ltac:(clear - NE; lia)) as SDJ. clear - SDJ Y1 Y2 X1 X2; lia. }
assert (EZ3 : forall lo' hi' x, In (lo', hi') ([(bv_unsigned sp + -80, bv_unsigned sp); (bv_unsigned sp + -80 - 64, bv_unsigned sp + -80); (SH A, SH A + g)]
++ (enq_W RE X (bv_unsigned sp + -80) a ++ Wx)) -> lo' <= x < hi' -> ezone a LB0 G RE X x).
{ intros lo' hi' x Hin Hx. unfold ezone. apply in_app_iff in Hin as [Hin|Hin]; [| apply in_app_iff in Hin as [Hin|Hin]].
- cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; [do 5 right; lia| do 5 right; lia|].
left. apply PZ. right. apply PSH. lia.
- destruct (enq_W_zone a LB0 FS0 G (bv_unsigned sp + -80) lo' hi' x GC ltac:(unfold ENQ_STACK, QPOP_STACK; rlia) Hin Hx) as [Z|[Z|[Z|Z]]];
[do 5 right; rlia| left; left; split; cbn [fst snd]; rlia| right; left; exact Z| right; right; left; exact Z].
- destruct (WXB lo' hi' x Hin Hx) as (_ & j & Hj & Tj & Hxj).
destruct JTC as [[EJ _]|(jn & EJ & Tn' & Tn & _)].
+ left. do 5 right; left. exists 24, j, TQOwn. split; [rewrite EJ in Hj; exact (proj1 (List.Forall_forall _ _) FJT j Hj)|]. split; [reflexivity| exact Hxj].
+ rewrite EJ in Hj. apply in_app_iff in Hj as [Hj|[<-|[]]].
* left. do 5 right; left. exists 24, j, TQOwn. split; [exact (proj1 (List.Forall_forall _ _) FJT j Hj)|]. split; [reflexivity| exact Hxj].
*
right; left. do 4 right; left.
pose proof (slot_prim _ _ _ _ _ _ GC' 24 jn TQOwn Tj) as (P1 & P2 & P3 & P4 & C1 & R1 & R2 & _). pose proof kconsts as (_ & _ & _ & K32' & _).
destruct Hxj as [X1 X2]; cbn [fst snd] in X1, X2.
split; [exists 24; rewrite K32'; split; [lia| (first [ clear - R2 R1 X2 X1 x jn Enext a1 SHAB SHA Q6 Q5 Q4 Q3 Q1 r q G3 G2 G1 g phi plo u A p a RE BAND; lia | lia ])]|].
intros (c' & i' & t' & Ht' & NP & [Y1 Y2]). cbn [fst snd] in Y1, Y2.
destruct (TOT c' i' t' Ht') as [t'' Ht''].
destruct (decide (c' = 24 /\ i' = jn)) as [[-> ->]|NE].
-- destruct t' as [| |q'|q'|]; cbn in NP; try discriminate.
++ pose proof (proj1 (SLV 24 jn (TLive q') eq_refl) Ht') as L'. rewrite Tj in L'. discriminate.
++ pose proof (proj1 (TQI 24 jn q') Ht') as L'. rewrite Tj in L'. discriminate.
++ exact (Tn Ht').
-- pose proof (slots_disjoint _ _ _ _ _ _ GC' c' i' t'' 24 jn TQOwn Ht'' Tj ltac:(clear - NE; lia)) as SDJ. clear - SDJ Y1 Y2 X1 X2; lia. }
assert (QRE3 : QREST C a1 LB0 FS0 G' RE X m3).
{ eapply (QREST_ext C a); [| exact Ereg| exact Enres| exact Espent| exact SLV].
eapply QREST_munch; [exact GC| exact QRE| exact MU3| exact WM3|]. intros lo' hi' x Hin Hx. eapply wzone_pzone. exact (WZ3 lo' hi' x Hin Hx). }

replace (ret_pc (wz 276700)) with (wz 276700) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply aimplT_from_evt.
step.
step.
pose proof (qwf_nonneg _ QWT3) as TQN.
destruct (Z.ltb_spec0 kQMaxCache (q_bytes (as_tq a1))) as [DR|NDR]; rewrite KMC in *.
2:{
ifz. step.
do 8 step. step. step.
release_frame FR3 ST3 (bv_unsigned sp).
apply evt_done. replace (kQMaxCache <? q_bytes (as_tq a1)) with false by (symmetry; apply Z.ltb_ge; rewrite KMC; (first [ clear - NDR Enext a1 phi plo A p a BAND; lia | lia ])).
apply aimplT_ret. apply evt_done.
unfold qret_post. do 15 eexists. exists m3, G'. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI3|]. split; [exact ST3|].
split; [eapply aheap_presA_of_munch_w; [exact GC| apply Permutation_refl| apply Permutation_refl| lia| exact MU3| exact WM3| exact WZ3]|].
split; [split; [eapply (depot_keep_of_pzone a LB0 FS0 G RE X m m3 _ GC MU3 WM3); intros lo' hi' x Hin Hx; eapply wzone_pzone; eapply WZ3; eassumption| eapply (errno_keep_of_ezone a LB0 FS0 G RE X m m3 _ GC MU3 WM3); exact EZ3]|].
split; [exact GC'|]. split; [apply QOTH_split; split; [exact RT3| split; [exact RS3| split; [exact RP3| exact QRE3]]]|].
apply (CLOSE QB). unfold QB. (first [ clear - NDR Enext a1 phi plo A p a BAND; lia | lia ]). }

ifz.
step. step.
step. step.
step.
apply evt_done. replace (kQMaxCache <? q_bytes (as_tq a1)) with true by (symmetry; apply Z.ltb_lt; rewrite KMC; lia).
eapply aimplT_then.
{ eapply (drain_spec C L RE X); [| exact MI3| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; unfold DRAIN_STACK, RECYCLE_STACK; lia
| unfold qroom in QRM; rewrite Egq; subst u; clear - QRM BY1; lia ].
split; [exact GC'|]. split; [apply QOTH_split; split; [exact RT3| split; [exact RS3| split; [exact RP3| exact QRE3]]]|].
apply (CLOSE (2 * QB)). unfold QB in *. lia. }
cbv beta. intros ar s'' ms'' PO. unfold qret_post in PO.
destruct PO as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m4 & Gd & -> & -> & MI4 & ST4 & AP4 & DK4 & QR4).
rewrite !(unsigned_lit (bv_unsigned sp + -80)) in ST4, AP4 by lia.
lazymatch type of FR3 with rw_cells _ _ ?fa ?cs => assert (FR4 : rw_cells asegs m4 fa cs) end.
{ eapply rw_cells_agree; [exact AP4| exact FR3|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
replace (ret_pc (wz 276500)) with (wz 276500) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
do 8 step. step. step.
release_frame FR4 ST4 (bv_unsigned sp).
apply evt_done.
unfold qret_post. do 15 eexists. exists m4, Gd. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI4|]. split; [exact ST4|]. split; [| split; [| exact QR4]].
2:{  destruct DK4 as [DK4 EK4]. split.
- intros n0 H0. apply DK4. eapply (depot_keep_of_pzone a LB0 FS0 G RE X m m3 _ GC MU3 WM3); [| exact H0]. intros lo' hi' x Hin Hx. eapply wzone_pzone. eapply WZ3; eassumption.
- eapply errno_keep_trans; [| exact EK4]. eapply (errno_keep_of_ezone a LB0 FS0 G RE X m m3 _ GC MU3 WM3); exact EZ3. }
eapply aheap_presA_trans.
- eapply aheap_presA_of_munch_w; [exact GC| apply Permutation_refl| apply Permutation_refl| lia| exact MU3| exact WM3| exact WZ3].
- eapply aheap_presA_weaken; [exact AP4| lia| intros b Hb; exact Hb| intros f Hf; exact Hf].
Qed.
End S.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qk8e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qk8e.Mq0.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoBx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoBx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWHo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWHo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8zl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8zl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnaW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnaW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkZz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkZz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpzM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpzM.Mql.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A.
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
Ltac ienter := lazymatch goal with |- Qpj5.Mq1.implM _ _ _ _ _ => unfold Qpj5.Mq1.implM; apply impl_from_evt | |- Qc6I.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- Qc6I.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Qpj5.Mq1.implM asegs c s Q ms) | _ => idtac end.

Ltac name_towers_vf H :=
repeat match type of H with
| context [CB ?n ?j] =>
lazymatch j with
| firstn _ _ => idtac | skipn _ _ => idtac
end;
let x := fresh "jk" in set (x := j) in H; clearbody x
end.
Ltac vf_split :=
lazymatch goal with FR : rw_cells _ _ _ [CB 368 _] |- _ =>
apply (rw_cells_split_CB asegs _ _ [] 368 _ _ [8;8;80;168;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
name_towers_vf FR end.

Section StderrSinkProofs.
Context {BAND : Band}.
Context {St : Type}.
Variable B : Z.
Let SINK := SINK_stderr (St:=St) B.

Lemma stderr_sink_frame : sink_frame_stmt RSTDERR B 80 SINK.
Proof using  BAND.
unfold sink_frame_stmt. intros W m m' [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO & B47 & ISHm) MU WM D1 D2 D3.
exists flags, mode, tail, rest.
split; [|split; [exact FL32 | split; [exact FL8 | split; [| split; [exact LEN | split; [exact BHI | split; [exact BLO | split; [exact B47|]]]]]]]].
3:{ eapply ISH_munch; [exact ISHm| exact MU| exact WM|]. eapply Forall_impl; [| exact D3]. cbv beta. intros [lo' hi'] H. cbn in H |- *. unfold GLOBALS_TOP in H. idtac. lia. }
- eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma stderr_sink_flags : sink_flags_stmt RSTDERR SINK.
Proof using B BAND.
unfold sink_flags_stmt. intros m [buf st] (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BLO & B47 & ISHm).
exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|]. split; [| exact ISHm].
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
Context {BAND : Band}.
Context {St : Type}.
Hypothesis FWE : fwritex_stderr_stmt.
Hypothesis FLS : stdio_write_flush_stmt.

Definition vfprintf_stderr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stderr_wfile m'
/\ ssp_cells m' canary.

Definition vfprintf_stderr_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDERR -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
stderr_wfile m -> ISH m ->
bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok RSTDERR (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
Qpj5.Mq1.implM asegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
(fun _ bs ms' => vfprintf_stderr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5f20) fc None m (seg_rom asegs)).

Theorem vfprintf_stderr_proof : vfprintf_stderr_stmt.
Proof using FLS FWE BAND.
unfold vfprintf_stderr_stmt. intros until canary. cbv zeta.
intros -> -> -> SF ISHm BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU1.
destruct SF as (flags & mode & e & wend & tail & FC & FL40). unfold file_cells in FC.

apply (printf_model_outs asegs OUT_stderr (OUTFP_stderr (St:=St)) fmt args ps r (fun _ => FLUSH_stderr) _ _ _ PP).
match goal with |- Qpj5.Mq1.implM _ _ _ ?Q _ => set (QQ := Q) end.
ienter.

call vf_saves; [exact ST | clear - LO GLO; unfold VF_DEPTH, PC_DEPTH in *; lia | exact GLO | exact MI | exact SSP1 | exact SSP2 | ].
lazymatch goal with H : stk _ ?mm lo (bv_unsigned sp + -368) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
lazymatch goal with H : rw_cells _ ?mm (bv_unsigned sp + -368) (C8 _ :: _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into FR end.
try rename MI0 into MI.

pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
eapply evt_cut.
{ eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
[ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
| unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | unfold szone; lia | lia | lia ]. }
cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
rewrite !unsigned_lit in MUc, STc by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit.
do 10 zs.
pose proof towrite_proof as TW. unfold towrite_stmt in TW.
eapply evt_cut.
{ eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
rewrite unsigned_lit; [apply sflags_noerr_8; exact FL40|].
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
cbv beta. intros ms' P. clear TW.
destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. do 6 zs.
set (B := bv_unsigned sp + -352) in *.

match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
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
exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, jb.
change (zlength (@nil Z)) with 0. rewrite Z.add_0_r. cbn [zb map app].
split; [exact FCt|]. rewrite unsigned_lit by lia.
split; [apply sflags_noerr_32|]. split; [apply sflags_noerr_8; exact FL40|]. split; [exact BUFc|].
unfold zlength. rewrite LJB. unfold GLOBALS_TOP. repeat match goal with |- _ /\ _ => split end; try (subst B; lia).
eapply ISH_munch_zone; [exact ISHm| exact MU| exact WM| subst B; zforalls].
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
- exact FRM.
- unfold szone. lia. }
cbv beta. intros r' [buf3 st3] ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
ienter. fix_ret.
pose proof SNK3 as SNK3'. destruct SNK3' as (flags2 & mode2 & tail2 & rest2 & FC3 & FL32 & FL8 & BUF3 & LEN3 & BHI3 & BLO3 & B473 & ISH3). cbn [fst] in FC3, BUF3, LEN3.
unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. zs. zs. if_lit.
zs. zs. zs. zs. zs.
ileave. unfold FLUSH_stderr, Qpj5.Mq1.implM. cbv beta iota.
pose proof (FLS St B) as FL. unfold stdio_write_flush_stmt in FL.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 3264) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
eapply impl_ebind.
{ unfold Qpj5.Mq1.implM in FL.
eapply FL with (lo := bv_unsigned sp + -368 - 3264) (canary := canary); clear FL; rewrite ?unsigned_lit by lia; unfold OUT_DEPTH, GLOBALS_TOP.
all: try lia.
- exact SNK3.
- reflexivity.
- reflexivity.
- exact ST4b.
- split; [exact SSP1 | exact SSP2].
- assumption. }
cbv beta. intros [[] st4] ms' P.
unfold stdio_write_flush_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (z5 & z6 & z7 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & SNK4 & SSP4).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m4 MUc WMc; clear MUc WMc end.
apply impl_ret_intro. cbn [snd]. fix_ret.
cbn [fst snd] in SNK4 |- *. clear SNK3 FL.
destruct SNK4 as (flags4 & mode4 & tail4 & rest4 & FC4 & FL32' & FL8' & BUF4 & LEN4 & _ & _). cbn [fst snd] in FC4, BUF4, LEN4.
unfold file_cells in FC4. change (zlength (@nil Z)) with 0 in FC4. rewrite Z.add_0_r in FC4.
clear SSP1 SSP2. destruct SSP4 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

do 9 zs.

zs. zs. zs. zs. zs. zs. zs. zs. if_lit.

lazymatch goal with H : rw_cells _ _ 6575456 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.

match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 3264)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 3264)%Z _ |- _ =>
pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
pose proof (rw_CB_length _ _ _ _ BUF4) as LB4.
lazymatch goal with A1 : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, A2 : rw_cells _ ?mm (bv_unsigned sp + -360)%Z _,
BU : rw_cells _ ?mm B [CB 80 ?bb], FR : rw_cells _ ?mm (bv_unsigned sp + -272)%Z ?rest |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ [C8 (Z_to_bv 64 VA)] ++ [CB 80 bb] ++ rest));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact A1|];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact A2 | lia] |];
apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact BU | subst B; lia] |];
cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear A1 A2 BU FR ] end.
cbn [app] in FALL.
release_frame FALL ST5 (bv_unsigned sp).
apply evt_done. subst QQ. cbn [epost fst snd]. unfold vfprintf_stderr_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST5|].
split.
{ exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags4)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode4, 0, 0, tail4.
split; [unfold file_cells; exact FC4|].
rewrite (sflags_olderr0 flags FL40). rewrite unsigned_lit; [apply sflags_final_40; [exact FL32' | exact FL8']|].
rewrite Z.lor_0_r. pose proof (bv_unsigned_in_range 64 (sx32 flags4)) as R4. unfold bv_modulus in R4. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R4. lia. }
split; [exact SSP1 | exact SSP2].
Qed.

End Stderr.

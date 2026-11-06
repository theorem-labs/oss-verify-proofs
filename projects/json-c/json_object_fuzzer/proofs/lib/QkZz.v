(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs QCiC Qpj5 QCNF QoNr QdZp Qk8e QHig Q0Do Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho Qu3b QnRU QteI QoBx Qs9x QC9y QQNJ Q8zl QnaW QcfN QpzM Q0z1 QlES.
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

Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
Z.land (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32)) 72 = 0.
Proof.
intros flags2 flags H. rewrite Z.land_lor_distr_l. rewrite <- (Z.land_assoc _ 32 72). change (Z.land 32 72) with 0. rewrite Z.land_0_r, Z.lor_0_r.
rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.

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

Section StdoutSinkProofs.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Let SINK := SINK_stdout (St:=St) get_so.

Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
Proof using get_so BAND.
unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & ISHm) MU WM D1 D2 D3.
split; [exact ACT|]. exists flags, mode, tail, bufbytes.
split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN|]]]]].
3:{ eapply ISH_munch; [exact ISHm| exact MU| exact WM|]. eapply Forall_impl; [| exact D3]. cbv beta. intros [lo' hi'] H. cbn in H |- *. unfold GLOBALS_TOP in H. idtac. lia. }
- eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
rw_cells asegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
rw_cells asegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
Proof using .
intros until tail. intros FC. unfold file_cells in FC.
apply (proj1 (rw_cells_app asegs m A [_] _)) in FC. destruct FC as [F0 _].
pose proof (rw_cells_recast m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
apply (proj1 (rw_cells_app asegs m A [_] _)) in F1. exact (proj1 F1).
Qed.

Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
Proof using get_so.
unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & ISHm).
exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|]. split; [| exact ISHm].
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
Qed.

Lemma topok_none : topok_stmt TOPOK_none.
Proof using . unfold topok_stmt, TOPOK_none. intros. lia. Qed.

End StdoutSinkProofs.

Lemma implM_upd_l {St B} : forall (f : St -> St) (k : unit -> M St B) s Q ms,
Qpj5.Mq1.implM asegs (k tt) (f s) Q ms -> Qpj5.Mq1.implM asegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

Section Stdout.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis GS : forall x so, get_so (set_so so x) = so.
Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
Hypothesis FWX : fwritex_stdout_stmt.

Let OUT := OUT_stdout get_so set_so.
Let SINK := SINK_stdout (St:=St) get_so.

Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stdout_file m' (get_so st')
/\ ssp_cells m' canary.

Definition vfprintf_stdout_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
stdout_file m (get_so st) -> ISH m ->
bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
Qpj5.Mq1.implM asegs (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
(vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd385c) fc None m (seg_rom asegs)).

Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
Proof using FWX GS SS BAND.
unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
intros -> -> -> SF ISHm BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
pose proof (rw_CB_length _ _ _ _ BUF) as LBB.

unfold stdout_towrite, upd_so. apply implM_upd_l.
apply (printf_model_outs asegs OUT (OUTFP_stdout (St:=St)) fmt args ps r (fun _ => mret tt) _ _ _ PP).
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

zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
destruct (so_active (get_so st)) eqn:ACT.
-
if_lit. cbv beta iota in FC.
zs. zs. zs. zs. zs. zs.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
ileave.
pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
(stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
unfold printf_core_stmt in PC2.
assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
{ rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
eapply implM_bind.
{ eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
all: try lia. all: try exact I.
- unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | split; [exact BLEN|]].
eapply ISH_munch_zone; [exact ISHm| exact MU| exact WM| zforalls].
- exact BY.
- exact HF.
- reflexivity.
- replace (VA + 8 * 0) with VA by lia. exact APC.
- exact VAA.
- cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
- rewrite FPC. apply Forall_nil.
- exact STc.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM.
- unfold szone. lia. }
cbv beta. intros r' st' ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
apply implM_ret. fix_ret.
destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3 & ISH3). unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. zs. zs. if_lit.
zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
lazymatch goal with H : rw_cells _ _ 6565536 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.

replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.

lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear AP FR ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|].
split.
{ exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
rewrite ACT3. split; [unfold file_cells; exact FC3|].
split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
split; [apply Z.lor_nonneg; lia|].
apply (lor_lt_pow2 _ _ 64); lia. }
split; [exact SSP1 | exact SSP2].
-
if_lit. cbv beta iota in FC. zs. zs. zs.
pose proof towrite_proof as TW. unfold towrite_stmt in TW.
eapply evt_cut.
{ eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
cbv beta. intros ms' P. clear TW.
destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. zs. zs. zs. zs. zs. zs.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
ileave.
pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
(stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
unfold printf_core_stmt in PC2.
assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
{ rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
eapply implM_bind.
{ eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
all: try lia. all: try exact I.
- unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | split; [lia|]].
eapply ISH_munch_zone; [exact ISHm| exact MU| exact WM| zforalls].
- exact BY.
- exact HF.
- reflexivity.
- replace (VA + 8 * 0) with VA by lia. exact APC.
- exact VAA.
- cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
- rewrite FPC. apply Forall_nil.
- exact STc.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM.
- unfold szone. lia. }
cbv beta. intros r' st' ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
apply implM_ret. fix_ret.
destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3 & ISH3). unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. zs. zs. if_lit.
zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
lazymatch goal with H : rw_cells _ _ 6565536 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.

replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.

lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear AP FR ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|].
split.
{ exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
rewrite ACT3. split; [unfold file_cells; exact FC3|].
split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
split; [apply Z.lor_nonneg; lia|].
apply (lor_lt_pow2 _ _ 64); lia. }
split; [exact SSP1 | exact SSP2].
Qed.
End Stdout.

End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 QBrp Qsn5 QQwg QUxU QmP7 QYyZ QOJv QUnM QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QmP7.Mq0 QYyZ.Mq0 QnRU.Mq0 Q9Ho.Mq1 QOJv.Mq5 QnaW.Mq2.
Import QpY2.Mq2.
Import QUnM QpME.Mq0.
Import Qu3b.Mq2.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Ltac ins_pick := lazymatch goal with
| |- (?lo <= ?a /\ _) \/ _ => first [ lazymatch a with context [lo] => left; solve [Q0z1.tslia] end | right; ins_pick ]
| |- _ => idtac
end.
Local Ltac tslia_ins2 := lazymatch goal with
| |- (_ /\ _) \/ _ => first [ solve [ ins_pick; Q0z1.tslia ] | Q0z1.tslia ]
| |- _ => Q0z1.tslia
end.
Local Ltac Q0z1.transport_lia ::= tslia_ins2. Local Ltac mkr__transport_lia_3 := tslia_ins2.

Local Notation wz := (Z_to_bv 64).

Definition enqueue_entry : Z := 0x436bc.
Definition ENQ_STACK : Z := 64 + QPOP_STACK.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Let qpop24_spec : qpop24_stmt RE X L := qpop24_spec L RE X.

Definition enq_W (sp : Z) (a : AState) : list (Z * Z) :=
(sp - ENQ_STACK, sp) :: (TQ X, TQ X + 32) :: tl (qpop_W RE X (sp - 64) a).

Definition enq_ghost (a a1 : AState) (G G' : ghost) (JT JT' : list Z) : Prop :=
same_tags is_live G G'
/\ (forall c i p, tag_at G c i = Some (TQuar p) <-> tag_at G' c i = Some (TQuar p))
/\ (forall c i t, tag_at G c i = Some t -> exists t', tag_at G' c i = Some t')
/\ (forall LB FS, gcons a LB FS G RE X -> gcons a1 LB FS G' RE X)
/\ ( (JT' = JT /\ forall c i, tag_at G c i = Some TQOwn <-> tag_at G' c i = Some TQOwn)
\/ (exists j, JT' = JT ++ [j] /\ tag_at G' 24 j = Some TQOwn /\ tag_at G 24 j <> Some TQOwn
/\ forall c i, (c <> 24 \/ i <> j) -> (tag_at G c i = Some TQOwn <-> tag_at G' c i = Some TQOwn)) ).

Definition enq_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (QA : aptr -> Z) (JT : list Z) (lo : Z) (m : word -> option byte)
(a1 : AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1r a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G' JT' Wx,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1r a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (enq_W (bv_unsigned sp) a ++ Wx) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ Forall (fun iv => exists j, In j JT' /\ slot_beg RE 24 j <= fst iv /\ snd iv <= slot_beg RE 24 j + 8192) Wx
/\ RTconst RE X m' /\ RStats RE X m' /\ RPrim a1 G' RE X m'
/\ qrep RE G' m' QA (TQ X) (as_tq a1) JT'
/\ qframe a (set_tq (as_tq a) a1) /\ enq_ghost a a1 G G' JT JT'.

Lemma enqueue_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (QA : aptr -> Z) (JT : list Z) (p : aptr) (lo : Z),
let u := aptr_used p in
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ENQ_STACK ->
qrep RE G m QA (TQ X) (as_tq a) JT -> List.NoDup JT ->
0 <= aptr_req p <= 2^26 -> 0 <= QA p - 16 < 2^64 -> q_bytes (as_tq a) <= 2^40 ->
aimplT atn (enqueue (ae_L RE) a p) s
(enq_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G QA JT lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz (TQ X)) (wz (rl_T X + 208)) a2 (wz (QA p - 16)) (wz u) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz enqueue_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros u RT RL RS RP MI ST CEIL LO QT ND HN HH HQB.
pose proof CEIL as CEIL'. idtac. unfold ENQ_STACK, QPOP_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kq_consts as (K24 & KBB & KBC & _). pose proof kconsts as (KR & KO & KS & K32 & _).
assert (HU : 1 <= u <= 2^26 + 1) by (subst u; unfold aptr_used, used_size; lia).
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (reg_geom RE X RL 24 ltac:(lia)) as (RB & FB & PAL & PK & PH & PHE & RI).
pose proof (alloc_user_bounds _ _ _ _ _ 24 RP ltac:(lia)) as (AU0 & AU1 & AU2). rewrite KO in AU2.
assert (SHB : 0x2008fff7000 <= SH (fa_beg (ae_L RE) 24) /\ SH (fa_beg (ae_L RE) 24) + 67108864 <= SH band_lo
/\ 0x2008fff7000 <= SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)) /\ SH (reg_beg (ae_L RE) 24 + 3758096384) <= SH band_lo
/\ SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)) <= SH (reg_beg (ae_L RE) 24 + 3758096384)).
{ rewrite FB, RB. unfold SH, A_SHADOW_OFS. unfold prim_lo, prim_hi in *. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBDq.
destruct QT as (TQC & BM & FJ & QW). pose proof QW as [FB0 QB].
pose proof (munch_refl (enq_W (bv_unsigned sp) a) m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU2.
unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, ri_addr in MU. cbn [tl app] in MU. unfold TQ in *.
rewrite RI, KS, KO in MU. change (536870912 / 8) with 67108864 in MU.
assert (FWrt : forall Wx, Forall (fun iv => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) Wx ->
Forall (rt_avoid RE X) (enq_W (bv_unsigned sp) a ++ Wx)).
{ intros Wx HWx. unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr. cbn [tl app]. rewrite RI, FB, RB, KS, KO.
change (536870912 / 8) with 67108864.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia| rewrite ?KHI_eq; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia| rewrite ?KHI_eq; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia]|].
apply List.Forall_forall. intros [lo' hi'] Hin. pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as [B1 B2]. cbn [fst snd] in B1, B2.
apply rt_avoid_prim; [exact RL| exact B1| exact B2]. }
assert (FWst : forall Wx, Forall (fun iv => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) Wx -> Forall st_avoid (enq_W (bv_unsigned sp) a ++ Wx)).
{ intros Wx HWx. unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr. cbn [tl app]. rewrite RI, FB, RB.
repeat (apply Forall_cons; [first [apply st_avoid_above; unfold A_ERRNO, SH, A_SHADOW_OFS; unfold prim_lo, prim_hi in *; Z.div_mod_to_equations; lia| eapply st_avoid_T; [eassumption| lia| lia]]|]).
apply List.Forall_forall. intros [lo' hi'] Hin. pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as [B1 B2]. cbn [fst snd] in B1, B2.
apply st_avoid_above. unfold A_ERRNO. cbn [fst]. unfold prim_lo in *. lia. }
unfold enqueue_entry, enqueue.
pose proof (split_last_spec (q_list (as_tq a))) as SL.
pose proof (batches_mem_nx_length _ _ _ _ _ _ BM) as LEN.
destruct (split_last (q_list (as_tq a))) as [[front b]|] eqn:ESL.
2:{
rewrite SL in *. destruct JT as [|j0 JT']; [| cbn in LEN; discriminate]. cbn [length Z.of_nat] in *.
apply aimplT_from_evt.
carve_frame 64%nat ST.
do 8 step.
step. step. ifz.
unfold new_batch. apply evt_done.

lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT0 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| rewrite <- (app_nil_r _); apply (FWrt []); constructor]);
assert (RS0 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| rewrite <- (app_nil_r _); apply (FWst []); constructor]);
assert (RP0 : RPrim a G RE X mc) by (eapply RPrim_stack; [exact RP| exact RL| exact MU2| exact WM| constructor; [cbn [fst]; lia| constructor]])
end.
clear MU2.
eapply aimplT_bind.
{ eapply aimplT_tall; [apply cache_alloc_qframe|].
eapply (qpop24_spec ra _ gp); try eassumption; rewrite unsigned_lit by lia; [exact ST| unfold QPOP_STACK; lia]. }
cbv beta. intros [ok a1] s' ms' [QF PO]. cbn [fst snd] in QF, PO |- *.
destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0'' & a1r & a3'' & a4'' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & t3' & t4' & t5' & t6' & m1 & G1 &
-> & -> & MUq & WMq & MI1 & ST1 & RT1 & RS1 & QG & BR).
rewrite !(unsigned_lit (bv_unsigned sp + -64)) in * by lia.
unfold qpop_W, QPOP_STACK, ri_addr in MUq. rewrite RI, KS, KO in MUq. change (536870912 / 8) with 67108864 in MUq.

apply (munch_chain' _ _ m1 _ m MUq) in MU; [| sub_fp_solve].
transport_after_call asegs m0 m1 MUq WMq. clear MUq WMq MI. rename MI1 into MI.
destruct ok; cbn [negb fst snd] in *.
2:{
apply aimplT_from_evt. rtc RT1 20%nat K20. rtc RT1 11%nat K11.
step. step. step. if_lit. step. step. step. step. if_lit.
apply evt_done. apply aimplT_spin. apply evt_done. at_spin. }

destruct BR as (-> & -> & -> & i & TC & -> & RPf & HJB & SHD).
set (G' := set_tag 24 i TQOwn G1) in *.
assert (RP1 : RPrim a1 G' RE X m1) by (apply RPf; reflexivity).
assert (TQ1 : tag_at G' 24 i = Some TQOwn) by (subst G'; eapply tag_at_set_tag_eq; exact TC).
pose proof (slot24_geom a1 G' RE X m1 i TQOwn RP1 RL TQ1) as SG. cbv zeta in SG.
destruct SG as (I0 & EB & B1 & B2 & AU1' & AU2' & RB1 & PK1 & PH1 & PHE1 & BAL & _).
rewrite KO in AU2'. rewrite ?KHI_eq in PK1. idtac.
set (B := slot_beg RE 24 i) in *.
assert (SHBB : 0x2008fff7000 <= SH B /\ SH B + 1024 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD0.

lazymatch type of MU with munch ?W _ _ =>
apply (munch_weaken W (W ++ [(B, B + 8192)])) in MU; [| unfold sub_fp; cbn [outside app]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; tauto] end.
cbn [app] in MU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (rl_T X + 80, rl_T X + 112); (B, B + 8192)] m1) as MU3.
pose proof (wmono_refl asegs m1) as WM3.

destruct (hjunk_split _ _ (B + 32) _ HJB ltac:(lia)) as [HJ4 HJR].
destruct (hjunk_C8x4 m1 B HJ4) as (w0 & w1 & w2 & w3 & BC).
apply aimplT_from_evt.
step. step. step.
step.
stf. step. stf. step.
step. if_lit.
step. stf. step.
step. step. step.
do 7 step. step. step.
release_frame FR ST1 (bv_unsigned sp).
apply evt_done. apply aimplT_ret. apply evt_done.

assert (MUf : munch (enq_W (bv_unsigned sp) a ++ [(B, B + 8192)]) m m3).
{ unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr. cbn [tl app]. rewrite RI, KS, KO. change (536870912 / 8) with 67108864. exact MU. }
assert (WxOK : Forall (fun iv : Z * Z => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) [(B, B + 8192)]) by (constructor; [cbn [fst snd]; lia| constructor]).
destruct QF as (Etq & Egq & Ereg & Enres & Espent & Enext).
destruct QG as (QG1 & QG2 & QG3 & QG4).
cbn in QB.
unfold enq_post. do 15 eexists. exists m3, G', [i], [(B, B + 8192)].
split; [reflexivity|]. split; [reflexivity|].
split; [exact MUf|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST1|].
split; [constructor; [exists i; cbn [fst snd]; split; [left; reflexivity| lia]| constructor]|].
split; [eapply RTconst_munch; [exact RT| exact MUf| exact WM| apply FWrt; exact WxOK]|].
split; [eapply RStats_munch; [exact RS| exact MUf| exact WM| apply FWst; exact WxOK]|].
split.
{ eapply RPrim_ext; [| intros; reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl].
eapply RPrim_frame; [exact RP1| exact WM3|].
eapply agree_on_of_munch; [exact MU3| exact WM3|]. intros x Fx Hx. apply outside_intro. intros lo' hi' Hin [H1 H2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- apply (fp_RPrim_not_Tq _ _ _ _ RL Fx). lia.
- destruct (fp_RPrim_not_slot a1 G' RE X m1 24 i TQOwn x RP1 RL TQ1 eq_refl Fx) as [NS _]. apply NS. split; cbn [fst snd]; rewrite ?class_size_24; subst B; lia. }
split.
{
cbn [as_tq set_tq]. rewrite Etq. unfold q_push_back. rewrite SL. cbn [app q_list q_bytes].
apply (proj1 (rw_cells_app asegs m3 B [C8 (wz 0); C8 (wz (u + 8192)); C8 (wz 1)] [C8 (wz (QA p - 16))])) in BC as [BC3 BC4].
cbn [cells_size csize Nat.add Z.of_nat] in BC4.
split; [| split; [| split]].
- cbn [length Z.of_nat Pos.of_succ_nat q_first q_last last]. rewrite KBB. exact TQC.
- unfold batches_mem. cbn [batches_mem_nx]. split; [| exact I]. unfold batch_mem. cbn [b_size b_count b_chunks map].
split; [rewrite KBB; exact BC3|]. split; [apply rw_cells_C8_u64arr1; exact BC4|].
split; [| exact SHD].
lazymatch goal with |- hjunk _ ?x ?y => replace x with (B + 32) by (subst B; lia); replace y with (B + 8192) by (subst B; lia) end.
eapply hjunk_wmono; [exact HJR| exact WM3].
- constructor; [exact TQ1| constructor].
- split; [| cbn; lia]. constructor; [| constructor]. unfold bwf. cbn [b_count b_chunks b_size length Z.of_nat map fold_right]. rewrite KBC.
split; [reflexivity|]. split; [lia|]. split; [lia|]. constructor; [exact HN| constructor]. }
split; [unfold qframe; cbn; repeat split; congruence|].

split.
{ intros c j t Hf. etransitivity; [apply QG2; exact Hf|]. subst G'. apply (same_tags_set_tag is_live G1 24 i TQOwn TCached TC eq_refl eq_refl). exact Hf. }
split.
{ intros c j q. etransitivity; [apply QG1; reflexivity|]. subst G'.
apply (same_tags_set_tag (fun t => match t with TQuar _ => true | _ => false end) G1 24 i TQOwn TCached TC eq_refl eq_refl). reflexivity. }
split.
{ intros c j t Ht. destruct (QG3 c j t Ht) as [t' Ht']. subst G'.
destruct (Z.eq_dec c 24) as [->|NC]; [destruct (Z.eq_dec j i) as [->|NJ]|].
- exists TQOwn. exact TQ1.
- exists t'. rewrite tag_at_set_tag_ne by lia. exact Ht'.
- exists t'. rewrite tag_at_set_tag_ne by lia. exact Ht'. }
split.
{ intros LB FS GC. eapply gcons_ext; [| intros; reflexivity| intros; reflexivity| reflexivity| cbn; lia].
subst G'. eapply gcons_retag_nonlive; [apply QG4; exact GC| exact TC| reflexivity| intros; reflexivity| reflexivity]. }
right. exists i. split; [reflexivity|]. split; [exact TQ1|]. split.
{ intros E. pose proof (proj1 (QG1 24 i TQOwn eq_refl) E) as E1. rewrite TC in E1. discriminate. }
intros c j Hcj. etransitivity; [apply QG1; reflexivity|]. subst G'. rewrite tag_at_set_tag_ne by (first [ clear - I0 Enext a1 LEN B i p a RE BAND Hcj j c BAL PK1 RB1 B1 EB PK PAL TK X; lia | lia ]). (first [ clear - Hcj j c SHBD0 SHBB G1 SHBDq SHB TD TK HU SPR HH HN B i u p QA a sp X RE BAND; tauto | tauto ]). }

pose proof (qwf_length_bound _ QW) as QLB. rewrite KBB in QLB.
destruct (split_last JT) as [[JF jl]|] eqn:ESJ; pose proof (split_last_spec JT) as SLJ; rewrite ESJ in SLJ.
2:{ exfalso. subst JT. rewrite SL, length_app in LEN. cbn in LEN. lia. }
subst JT. rewrite SL in LEN, BM, FB0, QB, TQC, QLB.
replace (Z.of_nat (length (front ++ [b]))) with (Z.of_nat (length front) + 1) in TQC, QLB by (rewrite length_app; cbn [length]; lia).
rewrite length_app in LEN. cbn [length] in LEN.
rewrite q_last_snoc in TQC.
apply Forall_app in FJ as [FJF FJl]. apply Forall_cons_iff in FJl as [Tjl _].
apply Forall_app in FB0 as [FBF FBl]. apply Forall_cons_iff in FBl as [Bwf _].
pose proof Bwf as (BW1 & BW2 & BW3 & BW4). rewrite KBC in BW2.
rewrite (length_app JF [jl]) in LEN. cbn [length] in LEN.
unfold batches_mem in BM. apply batches_mem_nx_snoc_inv in BM as [BMF BL]; [| lia].
destruct BL as (BCl & BAl & BJl & BSl).
pose proof (slot24_geom a G RE X m jl TQOwn RP RL Tjl) as SGl. cbv zeta in SGl.
destruct SGl as (Il0 & EBl & Bl1 & Bl2 & _ & _ & _ & _ & _ & _ & BlAL & _).
set (Bl := slot_beg RE 24 jl) in *.
assert (SHBl : 0x2008fff7000 <= SH Bl /\ SH Bl + 1024 <= SH band_lo /\ SH Bl + 1024 <= SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24))
/\ SH Bl + 1024 <= SH (fa_beg (ae_L RE) 24)) by (rewrite FB, RB in *; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
assert (NJF : forall j, In j JF -> j <> jl).
{ intros j Hj ->. pose proof (NoDup_remove_2 JF [] jl ND) as NI. apply NI. rewrite app_nil_r. exact Hj. }
remember (map (fun q : aptr => wz (QA q - 16)) (b_chunks b)) as ws eqn:Ews.
assert (LWS : Z.of_nat (length ws) = b_count b) by (subst ws; rewrite length_map; lia).
apply aimplT_from_evt.
carve_frame 64%nat ST.
do 8 step.
step. step. ifz.
step.
step.
step. step.
rewrite KBC. destruct (Z.eqb_spec (b_count b) 1021) as [FULL|NFULL].
2:{
ifz. step. ifz.

lazymatch type of MU with munch ?W _ _ =>
apply (munch_weaken W (W ++ [(Bl, Bl + 8192)])) in MU; [| unfold sub_fp; cbn [outside app]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; tauto] end.
cbn [app] in MU.
apply (munch_weaken _ [(bv_unsigned sp - 64, bv_unsigned sp); (rl_T X + 80, rl_T X + 112); (Bl, Bl + 8192)]) in MU2;
[| unfold sub_fp; cbn [outside]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; tauto].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
destruct (hjunk_split mc _ (Bl + 24 + 8 * b_count b + 8) _ (hjunk_wmono _ _ _ _ BJl WM) ltac:(lia)) as [HJ8 BJl'];
replace (Bl + 24 + 8 * b_count b) with (Bl + 24 + 8 * Z.of_nat (length ws)) in HJ8 by lia;
destruct (u64arr_snoc_junk mc (Bl + 24) ws BAl HJ8) as [wj BA2]
end.
clear BAl BJl' HJ8.
assert (LWS2 : Z.of_nat (length (ws ++ [wj])) = b_count b + 1) by (rewrite length_app; cbn [length]; lia).
step. step. step. step. step.
rewrite (unsigned_lit (b_count b)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_store_ok asegs mc (Bl + 24) (ws ++ [wj]) (b_count b) (wa (Bl + b_count b * 8 + 24)) BA2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u64arr_write asegs mc (Bl + 24) (ws ++ [wj]) (b_count b) (wz (QA p - 16)) BA2 ltac:(lia)) as BA3;
replace (wa (Bl + 24 + 8 * b_count b)) with (wa (Bl + b_count b * 8 + 24)) in BA3 by (unfold wa; f_equal; lia) end.
clear BA2. store_done.
assert (UPD : upd (ws ++ [wj]) (Z.to_nat (b_count b)) (wz (QA p - 16)) = ws ++ [wz (QA p - 16)]) by (rewrite <- LWS, Nat2Z.id; apply upd_snoc).
rewrite UPD in BA3. clear UPD.
step.
step. step. step.
do 7 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. apply aimplT_ret. apply evt_done.

lazymatch goal with |- enq_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mf end || idtac.
lazymatch type of MU with munch _ m ?mc =>
assert (MUf : munch (enq_W (bv_unsigned sp) a ++ [(Bl, Bl + 8192)]) m mc) by
(unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr; cbn [tl app]; rewrite RI, KS, KO; change (536870912 / 8) with 67108864; exact MU) end.
assert (WxOK : Forall (fun iv : Z * Z => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) [(Bl, Bl + 8192)]).
{ constructor; [cbn [fst snd]| constructor]. pose proof (reg_geom RE X RL 24 ltac:(lia)) as (RB' & _ & _ & _ & _ & PHE' & _). lia. }
cbn in QB.
unfold enq_post. do 15 eexists. eexists. exists G, (JF ++ [jl]), [(Bl, Bl + 8192)].
split; [reflexivity|]. split; [reflexivity|].
split; [exact MUf|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [constructor; [exists jl; cbn [fst snd]; split; [apply in_or_app; right; left; reflexivity| lia]| constructor]|].
split; [eapply RTconst_munch; [exact RT| exact MUf| exact WM| apply FWrt; exact WxOK]|].
split; [eapply RStats_munch; [exact RS| exact MUf| exact WM| apply FWst; exact WxOK]|].
split.
{ eapply RPrim_ext; [| intros; reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl].
eapply RPrim_frame; [exact RP| exact WM|].
eapply agree_on_of_munch; [exact MU2| exact WM|]. intros x Fx Hx. apply outside_intro. intros lo' hi' Hin [H1 H2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- apply (fp_RPrim_not_Tq _ _ _ _ RL Fx). lia.
- destruct (fp_RPrim_not_slot a G RE X m 24 jl TQOwn x RP RL Tjl eq_refl Fx) as [NS _]. apply NS. split; cbn [fst snd]; rewrite ?class_size_24; subst Bl; lia. }
split.
{ cbn [as_tq set_tq]. split; [| split; [| split]].
- cbn [q_list q_bytes]. rewrite length_app, q_last_snoc. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. exact TQC.
- cbn [q_list]. unfold batches_mem. apply batches_mem_nx_snoc.
+ lazymatch type of MUf with munch ?Wf _ _ =>
eapply (batches_mem_nx_keep (fun x => outside Wf x)); [exact BMF| exact FBF| eapply agree_on_of_munch; [exact MUf| exact WM| intros x Hx _; exact Hx]| exact WM|] end.
intros j x Hj Hx. pose proof (proj1 (List.Forall_forall _ _) FJF j Hj) as Tj.
pose proof (slot24_geom a G RE X m j TQOwn RP RL Tj) as SGj. cbv zeta in SGj. rewrite class_size_24 in Hx.
destruct SGj as (Ij0 & EBj & Bj1 & Bj2 & _). pose proof (NJF j Hj) as NEj.
assert (SHj : 0x2008fff7000 <= SH (slot_beg RE 24 j) /\ SH (slot_beg RE 24 j) + 1024 <= SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)) /\
SH (slot_beg RE 24 j) + 1024 <= SH (fa_beg (ae_L RE) 24))
by (rewrite FB, RB in *; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; (first [ clear - H19 q3 H10 H9 r1 q1 H5 H4 r0 q0 H0 H r q NEj Bj2 Bj1 EBj j wj NFULL Bl2 EBl BW2 LEN AU2 AU1 PK PAL r3 TD TK ws front JF Bl b jl p a X RE BAND; lia | lia ])).
assert (DJ : slot_beg RE 24 j + 8192 <= Bl \/ Bl + 8192 <= slot_beg RE 24 j) by (rewrite EBj, EBl; nia).
apply outside_intro. intros lo' hi' Hin [H1 H2].
unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr in Hin. cbn [tl app] in Hin. rewrite RI, KS, KO in Hin. change (536870912 / 8) with 67108864 in Hin.
destruct Hx as [[X1 X2]|[X1 X2]]; cbn [fst snd] in X1, X2;
[| change (8192 / 8) with 1024 in X2];
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; unfold prim_lo, prim_hi in *; first [ clear - X1 X2 H1 H2 EBj Bj1 Bj2 Ij0 RB FB PK PH PHE RI AU0 AU1 AU2 SHB SHBDq SHj DJ EBl CEIL LO SPR TK TB TD KS KO; (first [ clear - H1 Bj2 X2 x j AU2 AU1 PH RB LO CEIL jl lo a sp RE BAND H2 Bj1 X1 PK TD TK X FB SHBDq SHB DJ Bl SHj; lia | lia ]) | lia ]|]); destruct Hin.
+ unfold batch_mem. cbn [b_size b_count b_chunks]. split; [exact BCl|]. split; [rewrite map_app; cbn [map]; rewrite <- Ews; exact BA3|].
split; [| assumption].
lazymatch goal with |- hjunk _ ?x ?y => replace x with (Bl + 24 + 8 * b_count b + 8) by lia end.
eapply hjunk_wmono; [| exact WM]. exact (proj2 (hjunk_split _ _ (Bl + 24 + 8 * b_count b + 8) _ BJl ltac:(lia))).
- apply Forall_app. split; [exact FJF| constructor; [exact Tjl| constructor]].
- pose proof (qwf_append_last front b p (q_bytes (as_tq a)) ltac:(rewrite <- SL; exact QW) ltac:(rewrite KBC; lia) HN) as QW'. exact QW'. }
split; [unfold qframe; cbn; repeat split; reflexivity|].

split; [apply same_tags_refl|]. split; [intros; (first [ clear - p0 i c SHBl BW2 SHBDq SHB TD TK HU SPR HH HN Bl b u p QA G a sp X RE BAND; tauto | tauto ])|]. split; [intros c j t Ht; exists t; exact Ht|].
split; [intros LB FS GC; eapply gcons_ext; [exact GC| intros; reflexivity| intros; reflexivity| reflexivity| cbn; lia]|].
left. split; [reflexivity| intros; (first [ clear - i c SHBl BW2 SHBDq SHB TD TK HU SPR HH HN Bl b u p QA G a sp X RE BAND; tauto | tauto ])]. }

ifz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT0 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| rewrite <- (app_nil_r _); apply (FWrt []); constructor]);
assert (RS0 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| rewrite <- (app_nil_r _); apply (FWst []); constructor]);
assert (RP0 : RPrim a G RE X mc) by (eapply RPrim_stack; [exact RP| exact RL| exact MU2| exact WM| constructor; [cbn [fst]; lia| constructor]])
end.
clear MU2.
unfold new_batch. apply evt_done.
eapply aimplT_bind.
{ eapply aimplT_tall; [apply cache_alloc_qframe|].
eapply (qpop24_spec ra _ gp); try eassumption; rewrite unsigned_lit by lia; [exact ST| unfold QPOP_STACK; lia]. }
cbv beta. intros [ok a1] s' ms' [QF PO]. cbn [fst snd] in QF, PO |- *.
destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0'' & a1r & a3'' & a4'' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & t3' & t4' & t5' & t6' & m1 & G1 &
-> & -> & MUq & WMq & MI1 & ST1 & RT1 & RS1 & QG & BR).
rewrite !(unsigned_lit (bv_unsigned sp + -64)) in * by lia.
unfold qpop_W, QPOP_STACK, ri_addr in MUq. rewrite RI, KS, KO in MUq. change (536870912 / 8) with 67108864 in MUq.
apply (munch_chain' _ _ m1 _ m MUq) in MU; [| sub_fp_solve].
transport_after_call asegs m0 m1 MUq WMq. clear MUq WMq MI. rename MI1 into MI.
destruct ok; cbn [negb fst snd] in *.
2:{
apply aimplT_from_evt. rtc RT1 20%nat K20. rtc RT1 11%nat K11.
step. step. step. if_lit. step. step. step. step. if_lit.
apply evt_done. apply aimplT_spin. apply evt_done. at_spin. }
destruct BR as (-> & -> & -> & i & TC & -> & RPf & HJB & SHD).
set (G' := set_tag 24 i TQOwn G1) in *.
assert (RP1 : RPrim a1 G' RE X m1) by (apply RPf; reflexivity).
assert (TQ1 : tag_at G' 24 i = Some TQOwn) by (subst G'; eapply tag_at_set_tag_eq; exact TC).
pose proof (slot24_geom a1 G' RE X m1 i TQOwn RP1 RL TQ1) as SG. cbv zeta in SG.
destruct SG as (I0 & EB & B1 & B2 & AU1' & AU2' & RB1 & PK1 & PH1 & PHE1 & BAL & _).
rewrite KO in AU2'. rewrite ?KHI_eq in PK1. idtac.
set (B := slot_beg RE 24 i) in *.
assert (SHBB : 0x2008fff7000 <= SH B /\ SH B + 1024 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD1.

destruct QG as (QG1 & QG2 & QG3 & QG4).
assert (NEW : forall j, tag_at G 24 j = Some TQOwn -> j <> i).
{ intros j Tj ->. pose proof (proj1 (QG1 24 i TQOwn eq_refl) Tj) as E1. rewrite TC in E1. discriminate. }
pose proof (NEW jl Tjl) as NEWl.
assert (DlB : Bl + 8192 <= B \/ B + 8192 <= Bl) by (rewrite EB, EBl; (first [ clear - NEWl BAL PK1 RB1 EB B i Bl1 EBl LEN PK PAL TK ws Bl b front jl JF p X RE BAND; nia | nia ])).

lazymatch type of MU with munch ?W _ _ =>
apply (munch_weaken W (W ++ [(Bl, Bl + 8192); (B, B + 8192)])) in MU; [| unfold sub_fp; cbn [outside app]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; tauto] end.
cbn [app] in MU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (rl_T X + 80, rl_T X + 112); (Bl, Bl + 8192); (B, B + 8192)] m1) as MU3.
pose proof (wmono_refl asegs m1) as WM3.
destruct (hjunk_split _ _ (B + 32) _ HJB ltac:(lia)) as [HJ4 HJR].
destruct (hjunk_C8x4 m1 B HJ4) as (w0 & w1 & w2 & w3 & BC).
apply aimplT_from_evt.
step. step. step.
step.
stf. step. stf. step.
step. ifz.
step. step.
step. step.
step. step.
step. step. step.
do 7 step. step. step.
release_frame FR ST1 (bv_unsigned sp).
apply evt_done. apply aimplT_ret. apply evt_done.

lazymatch type of MU with munch _ m ?mc =>
assert (MUf : munch (enq_W (bv_unsigned sp) a ++ [(Bl, Bl + 8192); (B, B + 8192)]) m mc) by
(unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr; cbn [tl app]; rewrite RI, KS, KO; change (536870912 / 8) with 67108864; exact MU) end.
assert (WxOK : Forall (fun iv : Z * Z => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) [(Bl, Bl + 8192); (B, B + 8192)]).
{ constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (Tjl' : tag_at G' 24 jl = Some TQOwn).
{ subst G'. rewrite tag_at_set_tag_ne by (first [ clear - I0 LEN ws B i Bl b front jl JF p RE BAND NEWl BAL PK1 RB1 B1 EB EBl PK PAL TK X; lia | lia ]). apply (proj1 (QG1 24 jl TQOwn eq_refl)). exact Tjl. }
destruct QF as (Etq & Egq & Ereg & Enres & Espent & Enext).
cbn in QB.
unfold enq_post. do 15 eexists. eexists. exists G', ((JF ++ [jl]) ++ [i]), [(Bl, Bl + 8192); (B, B + 8192)].
split; [reflexivity|]. split; [reflexivity|].
split; [exact MUf|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST1|].
split.
{ constructor; [exists jl; cbn [fst snd]; split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity| lia]|].
constructor; [exists i; cbn [fst snd]; split; [apply in_or_app; right; left; reflexivity| lia]| constructor]. }
split; [eapply RTconst_munch; [exact RT| exact MUf| exact WM| apply FWrt; exact WxOK]|].
split; [eapply RStats_munch; [exact RS| exact MUf| exact WM| apply FWst; exact WxOK]|].
split.
{ eapply RPrim_ext; [| intros; reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl].
eapply RPrim_frame; [exact RP1| exact WM3|].
eapply agree_on_of_munch; [exact MU3| exact WM3|]. intros x Fx Hx. apply outside_intro. intros lo' hi' Hin [H1 H2]. cbn in Hin.
destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- apply (fp_RPrim_not_Tq _ _ _ _ RL Fx). lia.
- destruct (fp_RPrim_not_slot a1 G' RE X m1 24 jl TQOwn x RP1 RL Tjl' eq_refl Fx) as [NS _]. apply NS. split; cbn [fst snd]; rewrite ?class_size_24; subst Bl; lia.
- destruct (fp_RPrim_not_slot a1 G' RE X m1 24 i TQOwn x RP1 RL TQ1 eq_refl Fx) as [NS _]. apply NS. split; cbn [fst snd]; rewrite ?class_size_24; subst B; lia. }
split.
{ cbn [as_tq set_tq]. rewrite Etq. unfold q_push_back. rewrite SL. cbn [q_list q_bytes].
split; [| split; [| split]].
- unfold TQ. cbn [q_list q_bytes b_size]. rewrite q_last_snoc, q_first_snoc, !length_app. cbn [length].
rewrite !Nat2Z.inj_add. change (Z.of_nat 1) with 1.
replace (Z.of_nat (length front) + 1 + 1) with (Z.of_nat (length front) + 2) by lia.
rewrite KBB. destruct JF; cbn [app q_first] in TQC |- *; exact TQC.
- unfold batches_mem. apply batches_mem_nx_snoc; [apply batches_mem_nx_snoc|].
+ lazymatch type of MUf with munch ?Wf _ _ =>
eapply (batches_mem_nx_keep (fun x => outside Wf x)); [exact BMF| exact FBF| eapply agree_on_of_munch; [exact MUf| exact WM| intros x Hx _; exact Hx]| exact WM|] end.
intros j x Hj Hx. pose proof (proj1 (List.Forall_forall _ _) FJF j Hj) as Tj.
pose proof (slot24_geom a G RE X m j TQOwn RP RL Tj) as SGj. cbv zeta in SGj. rewrite class_size_24 in Hx.
destruct SGj as (Ij0 & EBj & Bj1 & Bj2 & _). pose proof (NJF j Hj) as NEj. pose proof (NEW j Tj) as NEi.
assert (SHj : 0x2008fff7000 <= SH (slot_beg RE 24 j) /\ SH (slot_beg RE 24 j) + 1024 <= SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)) /\
SH (slot_beg RE 24 j) + 1024 <= SH (fa_beg (ae_L RE) 24))
by (rewrite FB, RB in *; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; (first [ clear - H24 q4 H10 H9 r1 q1 H5 H4 r0 q0 H0 H r q NEi NEj Bj2 Bj1 EBj j DlB NEWl PK1 AU2' AU1' B2 EB Enext a1 Bl2 EBl LEN AU2 AU1 PAL r4 TD TK ws B i Bl b front jl JF p a X RE BAND; lia | lia ])).
assert (DJ : slot_beg RE 24 j + 8192 <= Bl \/ Bl + 8192 <= slot_beg RE 24 j) by (rewrite EBj, EBl; (first [ clear - NEj j DlB NEWl BAL PK1 RB1 B1 EB Enext a1 Bl1 EBl LEN PK TK ws B i Bl b front jl JF p a X RE BAND; nia | nia ])).
assert (DJB : slot_beg RE 24 j + 8192 <= B \/ B + 8192 <= slot_beg RE 24 j) by (rewrite EBj, EB; (first [ clear - DJ NEi EBj j DlB NEWl BAL PK1 RB1 B1 EB Enext a1 Bl1 EBl LEN PK TK ws B i Bl b front jl JF p a X RE BAND; nia | nia ])).
apply outside_intro. intros lo' hi' Hin [H1 H2].
unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr in Hin. cbn [tl app] in Hin. rewrite RI, KS, KO in Hin. change (536870912 / 8) with 67108864 in Hin.
destruct Hx as [[X1 X2]|[X1 X2]]; cbn [fst snd] in X1, X2;
[| change (8192 / 8) with 1024 in X2];
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; unfold prim_lo, prim_hi in *; first [ clear - X1 X2 H1 H2 EBj Bj1 Bj2 Ij0 RB FB PK PH PHE RI AU0 AU1 AU2 SHB SHBDq SHj DJ DJB EB EBl CEIL LO SPR TK TB TD KS KO; (first [ clear - H1 Bj2 X2 x j AU2 AU1 PH RB i jl LO CEIL lo a sp RE BAND H2 Bj1 X1 PK TD TK X FB SHBDq SHB DJ Bl DJB B SHj; lia | lia ]) | lia ]|]); destruct Hin.
+ unfold batch_mem. split; [exact BCl|]. split; [rewrite <- Ews; exact BAl|]. split; [| exact BSl].
eapply hjunk_wmono; [exact BJl| exact WM].
+ unfold batch_mem. cbn [b_size b_count b_chunks map].
apply (proj1 (rw_cells_app asegs _ B [C8 (wz 0); C8 (wz (u + 8192)); C8 (wz 1)] [C8 (wz (QA p - 16))])) in BC as [BC3 BC4].
cbn [cells_size csize Nat.add Z.of_nat] in BC4.
split; [rewrite KBB; exact BC3|]. split; [apply rw_cells_C8_u64arr1; exact BC4|]. split; [| exact SHD].
lazymatch goal with |- hjunk _ ?x ?y => replace x with (B + 32) by (subst B; lia); replace y with (B + 8192) by (subst B; lia) end.
eapply hjunk_wmono; [exact HJR| exact WM3].
- apply Forall_app. split; [| constructor; [exact TQ1| constructor]].
apply List.Forall_forall. intros j Hj. subst G'.
assert (Tj : tag_at G 24 j = Some TQOwn).
{ apply in_app_or in Hj as [Hj|[<-|[]]]; [exact (proj1 (List.Forall_forall _ _) FJF j Hj)| exact Tjl]. }
rewrite tag_at_set_tag_ne by (pose proof (NEW j Tj); (first [ clear - I0 Enext a1 LEN ws B i Bl b front jl JF p a RE BAND H j DlB NEWl BAL PK1 RB1 B1 EB Bl1 EBl PK PAL TK X; lia | lia ])). apply (proj1 (QG1 24 j TQOwn eq_refl)). exact Tj.
- rewrite <- SL. change (qwf (q_push_back (as_tq a) (mkB [p] 1 (u + kBatchBytes)))). apply qwf_push_back; [exact QW| apply bwf_single; exact HN]. }
split; [unfold qframe; cbn; repeat split; congruence|].

split.
{ intros c j t Hf. etransitivity; [apply QG2; exact Hf|]. subst G'. apply (same_tags_set_tag is_live G1 24 i TQOwn TCached TC eq_refl eq_refl). exact Hf. }
split.
{ intros c j q. etransitivity; [apply QG1; reflexivity|]. subst G'.
apply (same_tags_set_tag (fun t => match t with TQuar _ => true | _ => false end) G1 24 i TQOwn TCached TC eq_refl eq_refl). reflexivity. }
split.
{ intros c j t Ht. destruct (QG3 c j t Ht) as [t' Ht']. subst G'.
destruct (Z.eq_dec c 24) as [->|NC]; [destruct (Z.eq_dec j i) as [->|NJ]|].
- exists TQOwn. exact TQ1.
- exists t'. rewrite tag_at_set_tag_ne by (first [ clear - I0 Enext a1 LEN ws B i Bl b front jl JF p a RE BAND NJ j DlB NEWl BAL PK1 RB1 B1 EB Bl1 EBl PK PAL TK X; lia | lia ]). exact Ht'.
- exists t'. rewrite tag_at_set_tag_ne by (first [ clear - I0 Enext a1 LEN ws B i Bl b front jl JF p a RE BAND NC j c DlB NEWl BAL PK1 RB1 B1 EB Bl1 EBl PK PAL TK X; lia | lia ]). exact Ht'. }
split.
{ intros LB FS GC. eapply gcons_ext; [| intros; reflexivity| intros; reflexivity| reflexivity| cbn; lia].
subst G'. eapply gcons_retag_nonlive; [apply QG4; exact GC| exact TC| reflexivity| intros; reflexivity| reflexivity]. }
right. exists i. split; [reflexivity|]. split; [exact TQ1|]. split.
{ intros E. pose proof (proj1 (QG1 24 i TQOwn eq_refl) E) as E1. rewrite TC in E1. discriminate. }
intros c j Hcj. etransitivity; [apply QG1; reflexivity|]. subst G'. rewrite tag_at_set_tag_ne by (first [ clear - I0 Enext a1 LEN ws B i Bl b front jl JF p a RE BAND Hcj j c DlB NEWl BAL PK1 RB1 B1 EB Bl1 EBl PK PAL TK X; lia | lia ]). first [ reflexivity | tauto ].
Qed.
End S.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QmP7.Mq1 QYyZ.Mq8 QnRU.Mqc Q9Ho.Mq3 QOJv.Mqc QnaW.Mq4.
Import QpY2.Mqc.
Import QXcn QpME.Mq7.
Import Qu3b.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_zb segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_zb segs m a bs.
Import Q0z1.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_zb_only m a bs. Local Ltac mkr__transport_chunks_extra_2 m a bs n Hn Ha Hl := transport_zb_only m a bs.

Local Ltac ins_pick := lazymatch goal with
| |- (?lo <= ?a /\ _) \/ _ => first [ lazymatch a with context [lo] => left; solve [Q0z1.tslia] end | right; ins_pick ]
| |- _ => idtac
end.
Local Ltac tslia_ins2 := lazymatch goal with
| |- (_ /\ _) \/ _ => first [ solve [ ins_pick; Q0z1.tslia ] | Q0z1.tslia ]
| |- _ => Q0z1.tslia
end.
Local Ltac Q0z1.transport_lia ::= tslia_ins2. Local Ltac mkr__transport_lia_3 := tslia_ins2.

Local Notation wz := (Z_to_bv 64).

Definition enqueue_entry : Z := 0x438e8.
Definition ENQ_STACK : Z := 64 + QPOP_STACK.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Let qpop24_spec : qpop24_stmt RE X L := qpop24_spec L RE X.

Definition enq_W (sp : Z) (a : AState) : list (Z * Z) :=
(sp - ENQ_STACK, sp) :: (TQ X, TQ X + 32) :: tl (qpop_W RE X (sp - 64) a).

Definition enq_ghost (a a1 : AState) (G G' : ghost) (JT JT' : list Z) : Prop :=
same_tags is_live G G'
/\ (forall c i p, tag_at G c i = Some (TQuar p) <-> tag_at G' c i = Some (TQuar p))
/\ (forall c i t, tag_at G c i = Some t -> exists t', tag_at G' c i = Some t')
/\ (forall LB FS, gcons a LB FS G RE X -> gcons a1 LB FS G' RE X)
/\ ( (JT' = JT /\ forall c i, tag_at G c i = Some TQOwn <-> tag_at G' c i = Some TQOwn)
\/ (exists j, JT' = JT ++ [j] /\ tag_at G' 24 j = Some TQOwn /\ tag_at G 24 j <> Some TQOwn
/\ forall c i, (c <> 24 \/ i <> j) -> (tag_at G c i = Some TQOwn <-> tag_at G' c i = Some TQOwn)) ).

Definition enq_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (QA : aptr -> Z) (JT : list Z) (lo : Z) (m : word -> option byte)
(a1 : AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1r a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G' JT' Wx,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1r a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (enq_W (bv_unsigned sp) a ++ Wx) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ Forall (fun iv => exists j, In j JT' /\ slot_beg RE 24 j <= fst iv /\ snd iv <= slot_beg RE 24 j + 8192) Wx
/\ RTconst RE X m' /\ RStats RE X m' /\ RPrim a1 G' RE X m'
/\ qrep RE G' m' QA (TQ X) (as_tq a1) JT'
/\ qframe a (set_tq (as_tq a) a1) /\ enq_ghost a a1 G G' JT JT'.

Lemma enqueue_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (QA : aptr -> Z) (JT : list Z) (p : aptr) (lo : Z),
let u := aptr_used p in
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - ENQ_STACK ->
qrep RE G m QA (TQ X) (as_tq a) JT -> List.NoDup JT ->
0 <= aptr_req p <= 2^26 -> 0 <= QA p - 16 < 2^64 -> q_bytes (as_tq a) <= 2^40 ->
aimplT atn (enqueue (ae_L RE) a p) s
(enq_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G QA JT lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz (TQ X)) (wz (rl_T X + 208)) a2 (wz (QA p - 16)) (wz u) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz enqueue_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros u RT RL RS RP MI ST CEIL LO QT ND HN HH HQB.
pose proof CEIL as CEIL'. idtac. unfold ENQ_STACK, QPOP_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof kq_consts as (K24 & KBB & KBC & _). pose proof kconsts as (KR & KO & KS & K32 & _).
assert (HU : 1 <= u <= 2^26 + 1) by (subst u; unfold aptr_used, used_size; lia).
pose proof (rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (reg_geom RE X RL 24 ltac:(lia)) as (RB & FB & PAL & PK & PH & PHE & RI).
pose proof (alloc_user_bounds _ _ _ _ _ 24 RP ltac:(lia)) as (AU0 & AU1 & AU2). rewrite KO in AU2.
assert (SHB : 0x2008fff7000 <= SH (fa_beg (ae_L RE) 24) /\ SH (fa_beg (ae_L RE) 24) + 67108864 <= SH band_lo
/\ 0x2008fff7000 <= SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)) /\ SH (reg_beg (ae_L RE) 24 + 3758096384) <= SH band_lo
/\ SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)) <= SH (reg_beg (ae_L RE) 24 + 3758096384)).
{ rewrite FB, RB. unfold SH, A_SHADOW_OFS. unfold prim_lo, prim_hi in *. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBDq.
destruct QT as (TQC & BM & FJ & QW). pose proof QW as [FB0 QB].
pose proof (munch_refl (enq_W (bv_unsigned sp) a) m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU2.
unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, ri_addr in MU. cbn [tl app] in MU. unfold TQ in *.
rewrite RI, KS, KO in MU. change (536870912 / 8) with 67108864 in MU.
assert (FWrt : forall Wx, Forall (fun iv => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) Wx ->
Forall (rt_avoid RE X) (enq_W (bv_unsigned sp) a ++ Wx)).
{ intros Wx HWx. unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr. cbn [tl app]. rewrite RI, FB, RB, KS, KO.
change (536870912 / 8) with 67108864.
constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia| rewrite ?KHI_eq; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia]|].
constructor; [apply rt_avoid_prim; [exact RL| unfold prim_lo in *; lia| unfold prim_hi, prim_lo in *; lia]|].
constructor; [apply rt_avoid_gap; [exact RL| unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia| rewrite ?KHI_eq; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia]|].
apply List.Forall_forall. intros [lo' hi'] Hin. pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as [B1 B2]. cbn [fst snd] in B1, B2.
apply rt_avoid_prim; [exact RL| exact B1| exact B2]. }
assert (FWst : forall Wx, Forall (fun iv => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) Wx -> Forall st_avoid (enq_W (bv_unsigned sp) a ++ Wx)).
{ intros Wx HWx. unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr. cbn [tl app]. rewrite RI, FB, RB.
repeat (apply Forall_cons; [first [apply st_avoid_above; unfold A_ERRNO, SH, A_SHADOW_OFS; unfold prim_lo, prim_hi in *; Z.div_mod_to_equations; lia| eapply st_avoid_T; [eassumption| lia| lia]]|]).
apply List.Forall_forall. intros [lo' hi'] Hin. pose proof (proj1 (List.Forall_forall _ _) HWx _ Hin) as [B1 B2]. cbn [fst snd] in B1, B2.
apply st_avoid_above. unfold A_ERRNO. cbn [fst]. unfold prim_lo in *. lia. }
unfold enqueue_entry, enqueue.
pose proof (split_last_spec (q_list (as_tq a))) as SL.
pose proof (batches_mem_nx_length _ _ _ _ _ _ BM) as LEN.
destruct (split_last (q_list (as_tq a))) as [[front b]|] eqn:ESL.
2:{
rewrite SL in *. destruct JT as [|j0 JT']; [| cbn in LEN; discriminate]. cbn [length Z.of_nat] in *.
apply aimplT_from_evt.
carve_frame 64%nat ST.
do 8 step.
step. step. ifz.
unfold new_batch. apply evt_done.

lazymatch goal with |- aimplT _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT0 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| rewrite <- (app_nil_r _); apply (FWrt []); constructor]);
assert (RS0 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| rewrite <- (app_nil_r _); apply (FWst []); constructor]);
assert (RP0 : RPrim a G RE X mc) by (eapply RPrim_stack; [exact RP| exact RL| exact MU2| exact WM| constructor; [cbn [fst]; lia| constructor]])
end.
clear MU2.
eapply aimplT_bind.
{ eapply aimplT_tall; [apply cache_alloc_qframe|].
eapply (qpop24_spec ra _ gp); try eassumption; rewrite unsigned_lit by lia; [exact ST| unfold QPOP_STACK; lia]. }
cbv beta. intros [ok a1] s' ms' [QF PO]. cbn [fst snd] in QF, PO |- *.
destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0'' & a1r & a3'' & a4'' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & t3' & t4' & t5' & t6' & m1 & G1 &
-> & -> & MUq & WMq & MI1 & ST1 & RT1 & RS1 & QG & BR).
rewrite !(unsigned_lit (bv_unsigned sp + -64)) in * by lia.
unfold qpop_W, QPOP_STACK, ri_addr in MUq. rewrite RI, KS, KO in MUq. change (536870912 / 8) with 67108864 in MUq.

apply (munch_chain' _ _ m1 _ m MUq) in MU; [| sub_fp_solve].
transport_after_call asegs m0 m1 MUq WMq. clear MUq WMq MI. rename MI1 into MI.
destruct ok; cbn [negb fst snd] in *.
2:{
apply aimplT_from_evt. rtc RT1 20%nat K20. rtc RT1 11%nat K11.
step. step. step. if_lit. step. step. step. step. if_lit.
apply evt_done. apply aimplT_spin. apply evt_done. at_spin. }

destruct BR as (-> & -> & -> & i & TC & -> & RPf & HJB & SHD).
set (G' := set_tag 24 i TQOwn G1) in *.
assert (RP1 : RPrim a1 G' RE X m1) by (apply RPf; reflexivity).
assert (TQ1 : tag_at G' 24 i = Some TQOwn) by (subst G'; eapply tag_at_set_tag_eq; exact TC).
pose proof (slot24_geom a1 G' RE X m1 i TQOwn RP1 RL TQ1) as SG. cbv zeta in SG.
destruct SG as (I0 & EB & B1 & B2 & AU1' & AU2' & RB1 & PK1 & PH1 & PHE1 & BAL & _).
rewrite KO in AU2'. rewrite ?KHI_eq in PK1. idtac.
set (B := slot_beg RE 24 i) in *.
assert (SHBB : 0x2008fff7000 <= SH B /\ SH B + 1024 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD0.

lazymatch type of MU with munch ?W _ _ =>
apply (munch_weaken W (W ++ [(B, B + 8192)])) in MU; [| unfold sub_fp; cbn [outside app]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; tauto] end.
cbn [app] in MU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (rl_T X + 80, rl_T X + 112); (B, B + 8192)] m1) as MU3.
pose proof (wmono_refl asegs m1) as WM3.

destruct (hjunk_split _ _ (B + 32) _ HJB ltac:(lia)) as [HJ4 HJR].
destruct (hjunk_C8x4 m1 B HJ4) as (w0 & w1 & w2 & w3 & BC).
apply aimplT_from_evt.
step. step. step.
step.
stf. step. stf. step.
step. if_lit.
step. stf. step.
step. step. step.
do 7 step. step. step.
release_frame FR ST1 (bv_unsigned sp).
apply evt_done. apply aimplT_ret. apply evt_done.

assert (MUf : munch (enq_W (bv_unsigned sp) a ++ [(B, B + 8192)]) m m3).
{ unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr. cbn [tl app]. rewrite RI, KS, KO. change (536870912 / 8) with 67108864. exact MU. }
assert (WxOK : Forall (fun iv : Z * Z => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) [(B, B + 8192)]) by (constructor; [cbn [fst snd]; lia| constructor]).
destruct QF as (Etq & Egq & Ereg & Enres & Espent & Enext).
destruct QG as (QG1 & QG2 & QG3 & QG4).
cbn in QB.
unfold enq_post. do 15 eexists. exists m3, G', [i], [(B, B + 8192)].
split; [reflexivity|]. split; [reflexivity|].
split; [exact MUf|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST1|].
split; [constructor; [exists i; cbn [fst snd]; split; [left; reflexivity| lia]| constructor]|].
split; [eapply RTconst_munch; [exact RT| exact MUf| exact WM| apply FWrt; exact WxOK]|].
split; [eapply RStats_munch; [exact RS| exact MUf| exact WM| apply FWst; exact WxOK]|].
split.
{ eapply RPrim_ext; [| intros; reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl].
eapply RPrim_frame; [exact RP1| exact WM3|].
eapply agree_on_of_munch; [exact MU3| exact WM3|]. intros x Fx Hx. apply outside_intro. intros lo' hi' Hin [H1 H2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- apply (fp_RPrim_not_Tq _ _ _ _ RL Fx). lia.
- destruct (fp_RPrim_not_slot a1 G' RE X m1 24 i TQOwn x RP1 RL TQ1 eq_refl Fx) as [NS _]. apply NS. split; cbn [fst snd]; rewrite ?class_size_24; subst B; lia. }
split.
{
cbn [as_tq set_tq]. rewrite Etq. unfold q_push_back. rewrite SL. cbn [app q_list q_bytes].
apply (proj1 (rw_cells_app asegs m3 B [C8 (wz 0); C8 (wz (u + 8192)); C8 (wz 1)] [C8 (wz (QA p - 16))])) in BC as [BC3 BC4].
cbn [cells_size csize Nat.add Z.of_nat] in BC4.
split; [| split; [| split]].
- cbn [length Z.of_nat Pos.of_succ_nat q_first q_last last]. rewrite KBB. exact TQC.
- unfold batches_mem. cbn [batches_mem_nx]. split; [| exact I]. unfold batch_mem. cbn [b_size b_count b_chunks map].
split; [rewrite KBB; exact BC3|]. split; [apply rw_cells_C8_u64arr1; exact BC4|].
split; [| exact SHD].
lazymatch goal with |- hjunk _ ?x ?y => replace x with (B + 32) by (subst B; lia); replace y with (B + 8192) by (subst B; lia) end.
eapply hjunk_wmono; [exact HJR| exact WM3].
- constructor; [exact TQ1| constructor].
- split; [| cbn; lia]. constructor; [| constructor]. unfold bwf. cbn [b_count b_chunks b_size length Z.of_nat map fold_right]. rewrite KBC.
split; [reflexivity|]. split; [lia|]. split; [lia|]. constructor; [exact HN| constructor]. }
split; [unfold qframe; cbn; repeat split; congruence|].

split.
{ intros c j t Hf. etransitivity; [apply QG2; exact Hf|]. subst G'. apply (same_tags_set_tag is_live G1 24 i TQOwn TCached TC eq_refl eq_refl). exact Hf. }
split.
{ intros c j q. etransitivity; [apply QG1; reflexivity|]. subst G'.
apply (same_tags_set_tag (fun t => match t with TQuar _ => true | _ => false end) G1 24 i TQOwn TCached TC eq_refl eq_refl). reflexivity. }
split.
{ intros c j t Ht. destruct (QG3 c j t Ht) as [t' Ht']. subst G'.
destruct (Z.eq_dec c 24) as [->|NC]; [destruct (Z.eq_dec j i) as [->|NJ]|].
- exists TQOwn. exact TQ1.
- exists t'. rewrite tag_at_set_tag_ne by lia. exact Ht'.
- exists t'. rewrite tag_at_set_tag_ne by lia. exact Ht'. }
split.
{ intros LB FS GC. eapply gcons_ext; [| intros; reflexivity| intros; reflexivity| reflexivity| cbn; lia].
subst G'. eapply gcons_retag_nonlive; [apply QG4; exact GC| exact TC| reflexivity| intros; reflexivity| reflexivity]. }
right. exists i. split; [reflexivity|]. split; [exact TQ1|]. split.
{ intros E. pose proof (proj1 (QG1 24 i TQOwn eq_refl) E) as E1. rewrite TC in E1. discriminate. }
intros c j Hcj. etransitivity; [apply QG1; reflexivity|]. subst G'. rewrite tag_at_set_tag_ne by (first [ clear - I0 Enext a1 LEN B i p a RE BAND Hcj j c BAL PK1 RB1 B1 EB PK PAL TK X; lia | lia ]). (first [ clear - Hcj j c SHBD0 SHBB G1 SHBDq SHB TD TK HU SPR HH HN B i u p QA a sp X RE BAND; tauto | tauto ]). }

pose proof (qwf_length_bound _ QW) as QLB. rewrite KBB in QLB.
destruct (split_last JT) as [[JF jl]|] eqn:ESJ; pose proof (split_last_spec JT) as SLJ; rewrite ESJ in SLJ.
2:{ exfalso. subst JT. rewrite SL, length_app in LEN. cbn in LEN. lia. }
subst JT. rewrite SL in LEN, BM, FB0, QB, TQC, QLB.
replace (Z.of_nat (length (front ++ [b]))) with (Z.of_nat (length front) + 1) in TQC, QLB by (rewrite length_app; cbn [length]; lia).
rewrite length_app in LEN. cbn [length] in LEN.
rewrite q_last_snoc in TQC.
apply Forall_app in FJ as [FJF FJl]. apply Forall_cons_iff in FJl as [Tjl _].
apply Forall_app in FB0 as [FBF FBl]. apply Forall_cons_iff in FBl as [Bwf _].
pose proof Bwf as (BW1 & BW2 & BW3 & BW4). rewrite KBC in BW2.
rewrite (length_app JF [jl]) in LEN. cbn [length] in LEN.
unfold batches_mem in BM. apply batches_mem_nx_snoc_inv in BM as [BMF BL]; [| lia].
destruct BL as (BCl & BAl & BJl & BSl).
pose proof (slot24_geom a G RE X m jl TQOwn RP RL Tjl) as SGl. cbv zeta in SGl.
destruct SGl as (Il0 & EBl & Bl1 & Bl2 & _ & _ & _ & _ & _ & _ & BlAL & _).
set (Bl := slot_beg RE 24 jl) in *.
assert (SHBl : 0x2008fff7000 <= SH Bl /\ SH Bl + 1024 <= SH band_lo /\ SH Bl + 1024 <= SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24))
/\ SH Bl + 1024 <= SH (fa_beg (ae_L RE) 24)) by (rewrite FB, RB in *; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
assert (NJF : forall j, In j JF -> j <> jl).
{ intros j Hj ->. pose proof (NoDup_remove_2 JF [] jl ND) as NI. apply NI. rewrite app_nil_r. exact Hj. }
remember (map (fun q : aptr => wz (QA q - 16)) (b_chunks b)) as ws eqn:Ews.
assert (LWS : Z.of_nat (length ws) = b_count b) by (subst ws; rewrite length_map; lia).
apply aimplT_from_evt.
carve_frame 64%nat ST.
do 8 step.
step. step. ifz.
step.
step.
step. step.
rewrite KBC. destruct (Z.eqb_spec (b_count b) 1021) as [FULL|NFULL].
2:{
ifz. step. ifz.

lazymatch type of MU with munch ?W _ _ =>
apply (munch_weaken W (W ++ [(Bl, Bl + 8192)])) in MU; [| unfold sub_fp; cbn [outside app]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; tauto] end.
cbn [app] in MU.
apply (munch_weaken _ [(bv_unsigned sp - 64, bv_unsigned sp); (rl_T X + 80, rl_T X + 112); (Bl, Bl + 8192)]) in MU2;
[| unfold sub_fp; cbn [outside]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; tauto].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
destruct (hjunk_split mc _ (Bl + 24 + 8 * b_count b + 8) _ (hjunk_wmono _ _ _ _ BJl WM) ltac:(lia)) as [HJ8 BJl'];
replace (Bl + 24 + 8 * b_count b) with (Bl + 24 + 8 * Z.of_nat (length ws)) in HJ8 by lia;
destruct (u64arr_snoc_junk mc (Bl + 24) ws BAl HJ8) as [wj BA2]
end.
clear BAl BJl' HJ8.
assert (LWS2 : Z.of_nat (length (ws ++ [wj])) = b_count b + 1) by (rewrite length_app; cbn [length]; lia).
step. step. step. step. step.
rewrite (unsigned_lit (b_count b)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u64arr_store_ok asegs mc (Bl + 24) (ws ++ [wj]) (b_count b) (wa (Bl + b_count b * 8 + 24)) BA2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u64arr_write asegs mc (Bl + 24) (ws ++ [wj]) (b_count b) (wz (QA p - 16)) BA2 ltac:(lia)) as BA3;
replace (wa (Bl + 24 + 8 * b_count b)) with (wa (Bl + b_count b * 8 + 24)) in BA3 by (unfold wa; f_equal; lia) end.
clear BA2. store_done.
assert (UPD : upd (ws ++ [wj]) (Z.to_nat (b_count b)) (wz (QA p - 16)) = ws ++ [wz (QA p - 16)]) by (rewrite <- LWS, Nat2Z.id; apply upd_snoc).
rewrite UPD in BA3. clear UPD.
step.
step. step. step.
do 7 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. apply aimplT_ret. apply evt_done.

lazymatch goal with |- enq_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mf end || idtac.
lazymatch type of MU with munch _ m ?mc =>
assert (MUf : munch (enq_W (bv_unsigned sp) a ++ [(Bl, Bl + 8192)]) m mc) by
(unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr; cbn [tl app]; rewrite RI, KS, KO; change (536870912 / 8) with 67108864; exact MU) end.
assert (WxOK : Forall (fun iv : Z * Z => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) [(Bl, Bl + 8192)]).
{ constructor; [cbn [fst snd]| constructor]. pose proof (reg_geom RE X RL 24 ltac:(lia)) as (RB' & _ & _ & _ & _ & PHE' & _). lia. }
cbn in QB.
unfold enq_post. do 15 eexists. eexists. exists G, (JF ++ [jl]), [(Bl, Bl + 8192)].
split; [reflexivity|]. split; [reflexivity|].
split; [exact MUf|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [constructor; [exists jl; cbn [fst snd]; split; [apply in_or_app; right; left; reflexivity| lia]| constructor]|].
split; [eapply RTconst_munch; [exact RT| exact MUf| exact WM| apply FWrt; exact WxOK]|].
split; [eapply RStats_munch; [exact RS| exact MUf| exact WM| apply FWst; exact WxOK]|].
split.
{ eapply RPrim_ext; [| intros; reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl].
eapply RPrim_frame; [exact RP| exact WM|].
eapply agree_on_of_munch; [exact MU2| exact WM|]. intros x Fx Hx. apply outside_intro. intros lo' hi' Hin [H1 H2]. cbn in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- apply (fp_RPrim_not_Tq _ _ _ _ RL Fx). lia.
- destruct (fp_RPrim_not_slot a G RE X m 24 jl TQOwn x RP RL Tjl eq_refl Fx) as [NS _]. apply NS. split; cbn [fst snd]; rewrite ?class_size_24; subst Bl; lia. }
split.
{ cbn [as_tq set_tq]. split; [| split; [| split]].
- cbn [q_list q_bytes]. rewrite length_app, q_last_snoc. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. exact TQC.
- cbn [q_list]. unfold batches_mem. apply batches_mem_nx_snoc.
+ lazymatch type of MUf with munch ?Wf _ _ =>
eapply (batches_mem_nx_keep (fun x => outside Wf x)); [exact BMF| exact FBF| eapply agree_on_of_munch; [exact MUf| exact WM| intros x Hx _; exact Hx]| exact WM|] end.
intros j x Hj Hx. pose proof (proj1 (List.Forall_forall _ _) FJF j Hj) as Tj.
pose proof (slot24_geom a G RE X m j TQOwn RP RL Tj) as SGj. cbv zeta in SGj. rewrite class_size_24 in Hx.
destruct SGj as (Ij0 & EBj & Bj1 & Bj2 & _). pose proof (NJF j Hj) as NEj.
assert (SHj : 0x2008fff7000 <= SH (slot_beg RE 24 j) /\ SH (slot_beg RE 24 j) + 1024 <= SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)) /\
SH (slot_beg RE 24 j) + 1024 <= SH (fa_beg (ae_L RE) 24))
by (rewrite FB, RB in *; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; (first [ clear - H19 q3 H10 H9 r1 q1 H5 H4 r0 q0 H0 H r q NEj Bj2 Bj1 EBj j wj NFULL Bl2 EBl BW2 LEN AU2 AU1 PK PAL r3 TD TK ws front JF Bl b jl p a X RE BAND; lia | lia ])).
assert (DJ : slot_beg RE 24 j + 8192 <= Bl \/ Bl + 8192 <= slot_beg RE 24 j) by (rewrite EBj, EBl; nia).
apply outside_intro. intros lo' hi' Hin [H1 H2].
unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr in Hin. cbn [tl app] in Hin. rewrite RI, KS, KO in Hin. change (536870912 / 8) with 67108864 in Hin.
destruct Hx as [[X1 X2]|[X1 X2]]; cbn [fst snd] in X1, X2;
[| change (8192 / 8) with 1024 in X2];
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; unfold prim_lo, prim_hi in *; first [ clear - X1 X2 H1 H2 EBj Bj1 Bj2 Ij0 RB FB PK PH PHE RI AU0 AU1 AU2 SHB SHBDq SHj DJ EBl CEIL LO SPR TK TB TD KS KO; (first [ clear - H1 Bj2 X2 x j AU2 AU1 PH RB LO CEIL jl lo a sp RE BAND H2 Bj1 X1 PK TD TK X FB SHBDq SHB DJ Bl SHj; lia | lia ]) | lia ]|]); destruct Hin.
+ unfold batch_mem. cbn [b_size b_count b_chunks]. split; [exact BCl|]. split; [rewrite map_app; cbn [map]; rewrite <- Ews; exact BA3|].
split; [| assumption].
lazymatch goal with |- hjunk _ ?x ?y => replace x with (Bl + 24 + 8 * b_count b + 8) by lia end.
eapply hjunk_wmono; [| exact WM]. exact (proj2 (hjunk_split _ _ (Bl + 24 + 8 * b_count b + 8) _ BJl ltac:(lia))).
- apply Forall_app. split; [exact FJF| constructor; [exact Tjl| constructor]].
- pose proof (qwf_append_last front b p (q_bytes (as_tq a)) ltac:(rewrite <- SL; exact QW) ltac:(rewrite KBC; lia) HN) as QW'. exact QW'. }
split; [unfold qframe; cbn; repeat split; reflexivity|].

split; [apply same_tags_refl|]. split; [intros; (first [ clear - p0 i c SHBl BW2 SHBDq SHB TD TK HU SPR HH HN Bl b u p QA G a sp X RE BAND; tauto | tauto ])|]. split; [intros c j t Ht; exists t; exact Ht|].
split; [intros LB FS GC; eapply gcons_ext; [exact GC| intros; reflexivity| intros; reflexivity| reflexivity| cbn; lia]|].
left. split; [reflexivity| intros; (first [ clear - i c SHBl BW2 SHBDq SHB TD TK HU SPR HH HN Bl b u p QA G a sp X RE BAND; tauto | tauto ])]. }

ifz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT0 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| rewrite <- (app_nil_r _); apply (FWrt []); constructor]);
assert (RS0 : RStats RE X mc) by (eapply RStats_munch; [exact RS| exact MU| exact WM| rewrite <- (app_nil_r _); apply (FWst []); constructor]);
assert (RP0 : RPrim a G RE X mc) by (eapply RPrim_stack; [exact RP| exact RL| exact MU2| exact WM| constructor; [cbn [fst]; lia| constructor]])
end.
clear MU2.
unfold new_batch. apply evt_done.
eapply aimplT_bind.
{ eapply aimplT_tall; [apply cache_alloc_qframe|].
eapply (qpop24_spec ra _ gp); try eassumption; rewrite unsigned_lit by lia; [exact ST| unfold QPOP_STACK; lia]. }
cbv beta. intros [ok a1] s' ms' [QF PO]. cbn [fst snd] in QF, PO |- *.
destruct PO as (ra' & t0' & t1' & t2' & s0' & s1' & a0'' & a1r & a3'' & a4'' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & t3' & t4' & t5' & t6' & m1 & G1 &
-> & -> & MUq & WMq & MI1 & ST1 & RT1 & RS1 & QG & BR).
rewrite !(unsigned_lit (bv_unsigned sp + -64)) in * by lia.
unfold qpop_W, QPOP_STACK, ri_addr in MUq. rewrite RI, KS, KO in MUq. change (536870912 / 8) with 67108864 in MUq.
apply (munch_chain' _ _ m1 _ m MUq) in MU; [| sub_fp_solve].
transport_after_call asegs m0 m1 MUq WMq. clear MUq WMq MI. rename MI1 into MI.
destruct ok; cbn [negb fst snd] in *.
2:{
apply aimplT_from_evt. rtc RT1 20%nat K20. rtc RT1 11%nat K11.
step. step. step. if_lit. step. step. step. step. if_lit.
apply evt_done. apply aimplT_spin. apply evt_done. at_spin. }
destruct BR as (-> & -> & -> & i & TC & -> & RPf & HJB & SHD).
set (G' := set_tag 24 i TQOwn G1) in *.
assert (RP1 : RPrim a1 G' RE X m1) by (apply RPf; reflexivity).
assert (TQ1 : tag_at G' 24 i = Some TQOwn) by (subst G'; eapply tag_at_set_tag_eq; exact TC).
pose proof (slot24_geom a1 G' RE X m1 i TQOwn RP1 RL TQ1) as SG. cbv zeta in SG.
destruct SG as (I0 & EB & B1 & B2 & AU1' & AU2' & RB1 & PK1 & PH1 & PHE1 & BAL & _).
rewrite KO in AU2'. rewrite ?KHI_eq in PK1. idtac.
set (B := slot_beg RE 24 i) in *.
assert (SHBB : 0x2008fff7000 <= SH B /\ SH B + 1024 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD1.

destruct QG as (QG1 & QG2 & QG3 & QG4).
assert (NEW : forall j, tag_at G 24 j = Some TQOwn -> j <> i).
{ intros j Tj ->. pose proof (proj1 (QG1 24 i TQOwn eq_refl) Tj) as E1. rewrite TC in E1. discriminate. }
pose proof (NEW jl Tjl) as NEWl.
assert (DlB : Bl + 8192 <= B \/ B + 8192 <= Bl) by (rewrite EB, EBl; (first [ clear - NEWl BAL PK1 RB1 EB B i Bl1 EBl LEN PK PAL TK ws Bl b front jl JF p X RE BAND; nia | nia ])).

lazymatch type of MU with munch ?W _ _ =>
apply (munch_weaken W (W ++ [(Bl, Bl + 8192); (B, B + 8192)])) in MU; [| unfold sub_fp; cbn [outside app]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; clear - Hx; tauto] end.
cbn [app] in MU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (rl_T X + 80, rl_T X + 112); (Bl, Bl + 8192); (B, B + 8192)] m1) as MU3.
pose proof (wmono_refl asegs m1) as WM3.
destruct (hjunk_split _ _ (B + 32) _ HJB ltac:(lia)) as [HJ4 HJR].
destruct (hjunk_C8x4 m1 B HJ4) as (w0 & w1 & w2 & w3 & BC).
apply aimplT_from_evt.
step. step. step.
step.
stf. step. stf. step.
step. ifz.
step. step.
step. step.
step. step.
step. step. step.
do 7 step. step. step.
release_frame FR ST1 (bv_unsigned sp).
apply evt_done. apply aimplT_ret. apply evt_done.

lazymatch type of MU with munch _ m ?mc =>
assert (MUf : munch (enq_W (bv_unsigned sp) a ++ [(Bl, Bl + 8192); (B, B + 8192)]) m mc) by
(unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr; cbn [tl app]; rewrite RI, KS, KO; change (536870912 / 8) with 67108864; exact MU) end.
assert (WxOK : Forall (fun iv : Z * Z => prim_lo RE <= fst iv /\ snd iv <= prim_hi RE) [(Bl, Bl + 8192); (B, B + 8192)]).
{ constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (Tjl' : tag_at G' 24 jl = Some TQOwn).
{ subst G'. rewrite tag_at_set_tag_ne by (first [ clear - I0 LEN ws B i Bl b front jl JF p RE BAND NEWl BAL PK1 RB1 B1 EB EBl PK PAL TK X; lia | lia ]). apply (proj1 (QG1 24 jl TQOwn eq_refl)). exact Tjl. }
destruct QF as (Etq & Egq & Ereg & Enres & Espent & Enext).
cbn in QB.
unfold enq_post. do 15 eexists. eexists. exists G', ((JF ++ [jl]) ++ [i]), [(Bl, Bl + 8192); (B, B + 8192)].
split; [reflexivity|]. split; [reflexivity|].
split; [exact MUf|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST1|].
split.
{ constructor; [exists jl; cbn [fst snd]; split; [apply in_or_app; left; apply in_or_app; right; left; reflexivity| lia]|].
constructor; [exists i; cbn [fst snd]; split; [apply in_or_app; right; left; reflexivity| lia]| constructor]. }
split; [eapply RTconst_munch; [exact RT| exact MUf| exact WM| apply FWrt; exact WxOK]|].
split; [eapply RStats_munch; [exact RS| exact MUf| exact WM| apply FWst; exact WxOK]|].
split.
{ eapply RPrim_ext; [| intros; reflexivity| reflexivity| apply same_len_refl| apply same_tags_refl].
eapply RPrim_frame; [exact RP1| exact WM3|].
eapply agree_on_of_munch; [exact MU3| exact WM3|]. intros x Fx Hx. apply outside_intro. intros lo' hi' Hin [H1 H2]. cbn in Hin.
destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-.
- pose proof (fp_RPrim_lt_ceil _ _ _ _ RL Fx). lia.
- apply (fp_RPrim_not_Tq _ _ _ _ RL Fx). lia.
- destruct (fp_RPrim_not_slot a1 G' RE X m1 24 jl TQOwn x RP1 RL Tjl' eq_refl Fx) as [NS _]. apply NS. split; cbn [fst snd]; rewrite ?class_size_24; subst Bl; lia.
- destruct (fp_RPrim_not_slot a1 G' RE X m1 24 i TQOwn x RP1 RL TQ1 eq_refl Fx) as [NS _]. apply NS. split; cbn [fst snd]; rewrite ?class_size_24; subst B; lia. }
split.
{ cbn [as_tq set_tq]. rewrite Etq. unfold q_push_back. rewrite SL. cbn [q_list q_bytes].
split; [| split; [| split]].
- unfold TQ. cbn [q_list q_bytes b_size]. rewrite q_last_snoc, q_first_snoc, !length_app. cbn [length].
rewrite !Nat2Z.inj_add. change (Z.of_nat 1) with 1.
replace (Z.of_nat (length front) + 1 + 1) with (Z.of_nat (length front) + 2) by lia.
rewrite KBB. destruct JF; cbn [app q_first] in TQC |- *; exact TQC.
- unfold batches_mem. apply batches_mem_nx_snoc; [apply batches_mem_nx_snoc|].
+ lazymatch type of MUf with munch ?Wf _ _ =>
eapply (batches_mem_nx_keep (fun x => outside Wf x)); [exact BMF| exact FBF| eapply agree_on_of_munch; [exact MUf| exact WM| intros x Hx _; exact Hx]| exact WM|] end.
intros j x Hj Hx. pose proof (proj1 (List.Forall_forall _ _) FJF j Hj) as Tj.
pose proof (slot24_geom a G RE X m j TQOwn RP RL Tj) as SGj. cbv zeta in SGj. rewrite class_size_24 in Hx.
destruct SGj as (Ij0 & EBj & Bj1 & Bj2 & _). pose proof (NJF j Hj) as NEj. pose proof (NEW j Tj) as NEi.
assert (SHj : 0x2008fff7000 <= SH (slot_beg RE 24 j) /\ SH (slot_beg RE 24 j) + 1024 <= SH (reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)) /\
SH (slot_beg RE 24 j) + 1024 <= SH (fa_beg (ae_L RE) 24))
by (rewrite FB, RB in *; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; (first [ clear - H24 q4 H10 H9 r1 q1 H5 H4 r0 q0 H0 H r q NEi NEj Bj2 Bj1 EBj j DlB NEWl PK1 AU2' AU1' B2 EB Enext a1 Bl2 EBl LEN AU2 AU1 PAL r4 TD TK ws B i Bl b front jl JF p a X RE BAND; lia | lia ])).
assert (DJ : slot_beg RE 24 j + 8192 <= Bl \/ Bl + 8192 <= slot_beg RE 24 j) by (rewrite EBj, EBl; (first [ clear - NEj j DlB NEWl BAL PK1 RB1 B1 EB Enext a1 Bl1 EBl LEN PK TK ws B i Bl b front jl JF p a X RE BAND; nia | nia ])).
assert (DJB : slot_beg RE 24 j + 8192 <= B \/ B + 8192 <= slot_beg RE 24 j) by (rewrite EBj, EB; (first [ clear - DJ NEi EBj j DlB NEWl BAL PK1 RB1 B1 EB Enext a1 Bl1 EBl LEN PK TK ws B i Bl b front jl JF p a X RE BAND; nia | nia ])).
apply outside_intro. intros lo' hi' Hin [H1 H2].
unfold enq_W, qpop_W, ENQ_STACK, QPOP_STACK, TQ, ri_addr in Hin. cbn [tl app] in Hin. rewrite RI, KS, KO in Hin. change (536870912 / 8) with 67108864 in Hin.
destruct Hx as [[X1 X2]|[X1 X2]]; cbn [fst snd] in X1, X2;
[| change (8192 / 8) with 1024 in X2];
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; unfold prim_lo, prim_hi in *; first [ clear - X1 X2 H1 H2 EBj Bj1 Bj2 Ij0 RB FB PK PH PHE RI AU0 AU1 AU2 SHB SHBDq SHj DJ DJB EB EBl CEIL LO SPR TK TB TD KS KO; (first [ clear - H1 Bj2 X2 x j AU2 AU1 PH RB i jl LO CEIL lo a sp RE BAND H2 Bj1 X1 PK TD TK X FB SHBDq SHB DJ Bl DJB B SHj; lia | lia ]) | lia ]|]); destruct Hin.
+ unfold batch_mem. split; [exact BCl|]. split; [rewrite <- Ews; exact BAl|]. split; [| exact BSl].
eapply hjunk_wmono; [exact BJl| exact WM].
+ unfold batch_mem. cbn [b_size b_count b_chunks map].
apply (proj1 (rw_cells_app asegs _ B [C8 (wz 0); C8 (wz (u + 8192)); C8 (wz 1)] [C8 (wz (QA p - 16))])) in BC as [BC3 BC4].
cbn [cells_size csize Nat.add Z.of_nat] in BC4.
split; [rewrite KBB; exact BC3|]. split; [apply rw_cells_C8_u64arr1; exact BC4|]. split; [| exact SHD].
lazymatch goal with |- hjunk _ ?x ?y => replace x with (B + 32) by (subst B; lia); replace y with (B + 8192) by (subst B; lia) end.
eapply hjunk_wmono; [exact HJR| exact WM3].
- apply Forall_app. split; [| constructor; [exact TQ1| constructor]].
apply List.Forall_forall. intros j Hj. subst G'.
assert (Tj : tag_at G 24 j = Some TQOwn).
{ apply in_app_or in Hj as [Hj|[<-|[]]]; [exact (proj1 (List.Forall_forall _ _) FJF j Hj)| exact Tjl]. }
rewrite tag_at_set_tag_ne by (pose proof (NEW j Tj); (first [ clear - I0 Enext a1 LEN ws B i Bl b front jl JF p a RE BAND H j DlB NEWl BAL PK1 RB1 B1 EB Bl1 EBl PK PAL TK X; lia | lia ])). apply (proj1 (QG1 24 j TQOwn eq_refl)). exact Tj.
- rewrite <- SL. change (qwf (q_push_back (as_tq a) (mkB [p] 1 (u + kBatchBytes)))). apply qwf_push_back; [exact QW| apply bwf_single; exact HN]. }
split; [unfold qframe; cbn; repeat split; congruence|].

split.
{ intros c j t Hf. etransitivity; [apply QG2; exact Hf|]. subst G'. apply (same_tags_set_tag is_live G1 24 i TQOwn TCached TC eq_refl eq_refl). exact Hf. }
split.
{ intros c j q. etransitivity; [apply QG1; reflexivity|]. subst G'.
apply (same_tags_set_tag (fun t => match t with TQuar _ => true | _ => false end) G1 24 i TQOwn TCached TC eq_refl eq_refl). reflexivity. }
split.
{ intros c j t Ht. destruct (QG3 c j t Ht) as [t' Ht']. subst G'.
destruct (Z.eq_dec c 24) as [->|NC]; [destruct (Z.eq_dec j i) as [->|NJ]|].
- exists TQOwn. exact TQ1.
- exists t'. rewrite tag_at_set_tag_ne by (first [ clear - I0 Enext a1 LEN ws B i Bl b front jl JF p a RE BAND NJ j DlB NEWl BAL PK1 RB1 B1 EB Bl1 EBl PK PAL TK X; lia | lia ]). exact Ht'.
- exists t'. rewrite tag_at_set_tag_ne by (first [ clear - I0 Enext a1 LEN ws B i Bl b front jl JF p a RE BAND NC j c DlB NEWl BAL PK1 RB1 B1 EB Bl1 EBl PK PAL TK X; lia | lia ]). exact Ht'. }
split.
{ intros LB FS GC. eapply gcons_ext; [| intros; reflexivity| intros; reflexivity| reflexivity| cbn; lia].
subst G'. eapply gcons_retag_nonlive; [apply QG4; exact GC| exact TC| reflexivity| intros; reflexivity| reflexivity]. }
right. exists i. split; [reflexivity|]. split; [exact TQ1|]. split.
{ intros E. pose proof (proj1 (QG1 24 i TQOwn eq_refl) E) as E1. rewrite TC in E1. discriminate. }
intros c j Hcj. etransitivity; [apply QG1; reflexivity|]. subst G'. rewrite tag_at_set_tag_ne by (first [ clear - I0 Enext a1 LEN ws B i Bl b front jl JF p a RE BAND Hcj j c DlB NEWl BAL PK1 RB1 B1 EB Bl1 EBl PK PAL TK X; lia | lia ]). first [ reflexivity | tauto ].
Qed.
End S.
End Mq2.

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

Lemma land_mod_low : forall f c k, 0 <= k -> 0 <= c < 2^k -> Z.land f c = Z.land (f mod 2^k) c.
Proof.
intros f c k Hk Hc. rewrite <- (Z.land_ones f k) by lia. rewrite <- Z.land_assoc, (Z.land_comm (Z.ones k) c), Z.land_ones by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma land_sub_mask : forall u a b, Z.land a b = b -> Z.land u a = 0 -> Z.land u b = 0.
Proof. intros u a b Hab Hu. rewrite <- Hab, Z.land_assoc, Hu. apply Z.land_0_l. Qed.
Lemma mod_128_of_32 : forall a, (a mod 2^32) mod 128 = a mod 128.
Proof.
intros a. change 128 with (2^7). rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma sx32_mod128 : forall w : word, bv_unsigned (sx32 w) mod 128 = bv_unsigned w mod 128.
Proof.
intros w. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq. pose proof (bv_unsigned_in_range 64 w) as R.
unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in R. change (2^64)%Z with 18446744073709551616%Z.
rewrite <- (mod_128_of_32 (bv_unsigned w)). change (2^32) with 4294967296.
Z.div_mod_to_equations. lia.
Qed.
Lemma land_low7 : forall a c, 0 <= c < 128 -> Z.land a c = Z.land (a mod 128) c.
Proof. intros a c Hc. change 128 with (2^7). apply land_mod_low; lia. Qed.

Lemma flags_noerr_nowr : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 8 = 0.
Proof.
intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 8) with 8.
rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.
Lemma flags_noerr_104 : forall (flags : word), Z.land (bv_unsigned flags) 72 = 0 ->
Z.land (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583) 104 = 0.
Proof.
intros flags H. rewrite <- Z.land_assoc. change (Z.land 18446744073709551583 104) with 72.
rewrite land_low7, sx32_mod128, <- land_low7 by lia. exact H.
Qed.
Lemma flags_olderr_72 : forall (flags2 flags : word), Z.land (bv_unsigned flags2) 104 = 0 ->
Z.land (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32)) 72 = 0.
Proof.
intros flags2 flags H. rewrite Z.land_lor_distr_l. rewrite <- (Z.land_assoc _ 32 72). change (Z.land 32 72) with 0. rewrite Z.land_0_r, Z.lor_0_r.
rewrite land_low7, sx32_mod128, <- land_low7 by lia. revert H. apply land_sub_mask. reflexivity.
Qed.

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

Section StdoutSinkProofs.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Let SINK := SINK_stdout (St:=St) get_so.

Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
Proof using get_so BAND.
unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & ISHm) MU WM D1 D2 D3.
split; [exact ACT|]. exists flags, mode, tail, bufbytes.
split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN|]]]]].
3:{ eapply ISH_munch; [exact ISHm| exact MU| exact WM|]. eapply Forall_impl; [| exact D3]. cbv beta. intros [lo' hi'] H. cbn in H |- *. unfold GLOBALS_TOP in H. idtac. lia. }
- eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
Qed.

Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
rw_cells asegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
rw_cells asegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
Proof using .
intros until tail. intros FC. unfold file_cells in FC.
apply (proj1 (rw_cells_app asegs m A [_] _)) in FC. destruct FC as [F0 _].
pose proof (rw_cells_recast m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
apply (proj1 (rw_cells_app asegs m A [_] _)) in F1. exact (proj1 F1).
Qed.

Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
Proof using get_so.
unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & ISHm).
exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|]. split; [| exact ISHm].
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
Qed.

Lemma topok_none : topok_stmt TOPOK_none.
Proof using . unfold topok_stmt, TOPOK_none. intros. lia. Qed.

End StdoutSinkProofs.

Lemma implM_upd_l {St B} : forall (f : St -> St) (k : unit -> M St B) s Q ms,
Qpj5.Mq1.implM asegs (k tt) (f s) Q ms -> Qpj5.Mq1.implM asegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.

Section Stdout.
Context {BAND : Band}.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis GS : forall x so, get_so (set_so so x) = so.
Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
Hypothesis FWX : fwritex_stdout_stmt.

Let OUT := OUT_stdout get_so set_so.
Let SINK := SINK_stdout (St:=St) get_so.

Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk asegs m' lo (bv_unsigned sp)
/\ stdout_file m' (get_so st')
/\ ssp_cells m' canary.

Definition vfprintf_stdout_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
stdout_file m (get_so st) -> ISH m ->
bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk asegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q + 16 <= 2^47) ->
ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
Qpj5.Mq1.implM asegs (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
(vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5f20) fc None m (seg_rom asegs)).

Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
Proof using FWX GS SS BAND.
unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
intros -> -> -> SF ISHm BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
pose proof (rw_CB_length _ _ _ _ BUF) as LBB.

unfold stdout_towrite, upd_so. apply implM_upd_l.
apply (printf_model_outs asegs OUT (OUTFP_stdout (St:=St)) fmt args ps r (fun _ => mret tt) _ _ _ PP).
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

zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
destruct (so_active (get_so st)) eqn:ACT.
-
if_lit. cbv beta iota in FC.
zs. zs. zs. zs. zs. zs.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
ileave.
pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
(stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
unfold printf_core_stmt in PC2.
assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
{ rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
eapply implM_bind.
{ eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
all: try lia. all: try exact I.
- unfold SINK, SINK_stdout. rewrite GS, ACT. split; [reflexivity|].
exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode, tail, bufbytes.
split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | split; [exact BLEN|]].
eapply ISH_munch_zone; [exact ISHm| exact MU| exact WM| zforalls].
- exact BY.
- exact HF.
- reflexivity.
- replace (VA + 8 * 0) with VA by lia. exact APC.
- exact VAA.
- cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
- rewrite FPC. apply Forall_nil.
- exact STc.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM.
- unfold szone. lia. }
cbv beta. intros r' st' ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
apply implM_ret. fix_ret.
destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3 & ISH3). unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. zs. zs. if_lit.
zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
lazymatch goal with H : rw_cells _ _ 6575456 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.

replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.

lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear AP FR ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|].
split.
{ exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
rewrite ACT3. split; [unfold file_cells; exact FC3|].
split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
split; [apply Z.lor_nonneg; lia|].
apply (lor_lt_pow2 _ _ 64); lia. }
split; [exact SSP1 | exact SSP2].
-
if_lit. cbv beta iota in FC. zs. zs. zs.
pose proof towrite_proof as TW. unfold towrite_stmt in TW.
eapply evt_cut.
{ eapply TW; clear TW; rewrite ?unsigned_lit by lia; [ exact FC | | lia | lia | lia | assumption ].
rewrite unsigned_lit; [apply flags_noerr_nowr; exact FL72|].
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
cbv beta. intros ms' P. clear TW.
destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FCt).
rewrite !unsigned_lit in MUc, FCt by lia. clear FC.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. zs. zs. zs. zs. zs. zs.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
replace (bv_unsigned sp + -368 + Z.of_nat 8) with (bv_unsigned sp + -360) in FR by lia.
ileave.
pose proof (printf_core_proof St RSTDOUT RSTDOUT_BUF 1024 SINK TOPOK_none OUT (OUTFP_stdout (St:=St))
(stdout_sink_frame get_so) (stdout_sink_flags get_so) topok_none (FWX St get_so set_so GS SS)) as PC2.
unfold printf_core_stmt in PC2.
assert (FL' : Z.land (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583))) 104 = 0).
{ rewrite unsigned_lit. apply flags_noerr_104. exact FL72.
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 18446744073709551583). pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R3.
unfold bv_modulus in R3. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R3. lia. }
eapply implM_bind.
{ eapply PC2 with (i := 0%Z) (slots := slots) (lo := lo) (VA := VA) (canary := canary) (args := args) (fmt := fmt);
clear PC2; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_none, zlength.
all: try lia. all: try exact I.
- unfold SINK, SINK_stdout. rewrite GS. cbn [so_active so_buf so_lbf_nl so_first]. split; [reflexivity|].
exists (Z_to_bv 64 (Z.land (bv_unsigned (sx32 flags)) 18446744073709551583)), mode', tail, bufbytes.
change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | split; [lia|]].
eapply ISH_munch_zone; [exact ISHm| exact MU| exact WM| zforalls].
- exact BY.
- exact HF.
- reflexivity.
- replace (VA + 8 * 0) with VA by lia. exact APC.
- exact VAA.
- cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia | exact MU1].
- rewrite FPC. apply Forall_nil.
- exact STc.
- split; [exact SSP1 | exact SSP2].
- assumption.
- exact FRM.
- unfold szone. lia. }
cbv beta. intros r' st' ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
apply implM_ret. fix_ret.
destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3 & ISH3). unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

zs. zs. zs. if_lit.
zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
lazymatch goal with H : rw_cells _ _ 6575456 _ |- _ => move H at bottom end.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.

replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.

lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
assert (FALL : rw_cells asegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
[ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
| clear AP FR ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold vfprintf_stdout_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|].
split.
{ exists (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags2)) (Z.land (bv_unsigned (sx32 flags)) 32))), mode2, tail2, bufbytes2.
rewrite ACT3. split; [unfold file_cells; exact FC3|].
split; [| split; [exact BUF3 | split; [exact PFX3 | split; [exact BLEN3 | intros; discriminate]]]].
rewrite unsigned_lit; [apply flags_olderr_72; exact FL3|].
pose proof (bv_unsigned_in_range 64 (sx32 flags2)) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2.
unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R1, R2.
pose proof (Z_land_range (bv_unsigned (sx32 flags)) 32).
split; [apply Z.lor_nonneg; lia|].
apply (lor_lt_pow2 _ _ 64); lia. }
split; [exact SSP1 | exact SSP2].
Qed.
End Stdout.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio Driver.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_memset F_memcpy Stdio_kit F_syscalls StdioFiles.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_printf_iface F_printf_core F_vfprintf.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_pieces Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX Stdio_kit2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import StoreFast.
Import ListNotations.
Import ITree.Exc.
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
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM usegs c s Q ms) | _ => idtac end.
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
Section StdoutSinkProofs.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Let SINK := SINK_stdout (St:=St) get_so.
Lemma stdout_sink_frame : sink_frame_stmt RSTDOUT RSTDOUT_BUF 1024 SINK.
Proof using get_so.
unfold sink_frame_stmt. intros W m m' st (ACT & flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN) MU WM D1 D2.
split; [exact ACT|]. exists flags, mode, tail, bufbytes.
split; [|split; [exact FL | split; [| split; [exact PFX | exact LEN]]]].
- eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size file_cells csize Nat.add]; lia | cbn [cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
Qed.
Lemma file_cells_flags_byte : forall m A flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
rw_cells usegs m A (file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail) ->
rw_cells usegs m A [CB 1 [Z_to_bv 8 (bv_unsigned flags)]].
Proof using .
intros until tail. intros FC. unfold file_cells in FC.
apply (proj1 (rw_cells_app usegs m A [_] _)) in FC. destruct FC as [F0 _].
pose proof (rw_cells_recast3 m A _ [CB 1 [Z_to_bv 8 (bv_unsigned flags)]; CB 3 (Z_to_le_bytes 3 (Z.shiftr (bv_unsigned flags) 8))] F0
ltac:(cbn; repeat split) ltac:(reflexivity)) as F1.
apply (proj1 (rw_cells_app usegs m A [_] _)) in F1. exact (proj1 F1).
Qed.
Lemma stdout_sink_flags : sink_flags_stmt RSTDOUT SINK.
Proof using get_so.
unfold sink_flags_stmt. intros m st (ACT & flags & mode & tail & bufbytes & FC & FL & _).
exists (Z_to_bv 8 (bv_unsigned flags)). split; [eapply file_cells_flags_byte; exact FC|].
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (bv_unsigned flags)) with ((bv_unsigned flags) mod 2^8).
rewrite <- land_mod_low by lia. eapply land_sub_mask; [|exact FL]. reflexivity.
Qed.
Lemma topok_none : topok_stmt TOPOK_none.
Proof using . unfold topok_stmt, TOPOK_none. intros. exact I. Qed.
End StdoutSinkProofs.
Lemma implM_upd_l {St B} : forall (f : St -> St) (k : unit -> M St B) s Q ms,
Monad.implM usegs (k tt) (f s) Q ms -> Monad.implM usegs (mbind (mupd f) k) s Q ms.
Proof. intros. exact H. Qed.
Section Stdout.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis GS : forall x so, get_so (set_so so x) = so.
Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.
Hypothesis FWX : fwritex_stdout_stmt.
Let OUT := stdout_fwritex get_so set_so.
Let SINK := SINK_stdout (St:=St) get_so.
Definition vfprintf_stdout_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom usegs)
/\ munch [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk usegs m' lo (bv_unsigned sp)
/\ stdout_file m' (get_so st')
/\ ssp_cells m' canary.
Definition vfprintf_stdout_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(A VA : Z) (fmt : list Z) (slots : list word) (args : list parg) (ps : list (list Z)) (r : Z)
(lo : Z) (canary : word),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
stdout_file m (get_so st) ->
bytes_at usegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok RSTDOUT RSTDOUT_BUF 1024 m lo q (q - VF_FRAME) slots args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
stk usegs m lo q -> (lo <= q - VF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^47) ->
ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
Monad.implM usegs (stdout_towrite get_so set_so ;;; outsk OUT ps (mret tt)) st
(vfprintf_stdout_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x17770) fc None m (seg_rom usegs)).
Theorem vfprintf_stdout_proof : vfprintf_stdout_stmt.
Proof using FWX GS SS.
unfold vfprintf_stdout_stmt. intros until canary. cbv zeta.
intros -> -> -> SF BY HF P1 VAA AOK PP FPC ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI.
unfold VF_FRAME, VF_DEPTH, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU1.
destruct SF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & PFX & BLEN & INACT). unfold file_cells in FC.
pose proof (rw_CB_length _ _ _ _ BUF) as LBB.
unfold stdout_towrite, upd_so. apply implM_upd_l.
apply (printf_model_outs usegs OUT (OUTFP_stdout (St:=St)) fmt args ps r (fun _ => mret tt) _ _ _ PP).
ienter.
carve_frame 368%nat ST.
do 12 zs. do 14 zs.
pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
eapply evt_cut.
{ eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
[ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
| unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
rewrite !unsigned_lit in MUc, STc by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
zs. if_lit. zs. zs. if_lit. zs. zs. zs. zs. zs. zs. if_lit. zs. zs. zs.
destruct (so_active (get_so st)) eqn:ACT.
-
if_lit. cbv beta iota in FC.
zs. zs. zs. zs. zs. zs.
apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
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
split; [unfold file_cells; exact FC|]. split; [exact FL'|]. split; [exact BUF|]. split; [exact PFX | exact BLEN].
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
- exact FRM. }
cbv beta. intros r' st' ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
apply implM_ret. fix_ret.
destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
zs. zs. zs. if_lit.
zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.
replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
[ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
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
lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. zs. zs. zs. zs. zs. zs.
apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FR. destruct FR as [APC FR]. cbn [cells_size csize Nat.add app] in FR.
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
split; [exact FCt|]. split; [exact FL'|]. split; [exact BUF|]. split; [reflexivity | lia].
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
- exact FRM. }
cbv beta. intros r' st' ms' P. clear PC2 MU1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc end.
apply implM_ret. fix_ret.
destruct SNK3 as (ACT3 & flags2 & mode2 & tail2 & bufbytes2 & FC3 & FL3 & BUF3 & PFX3 & BLEN3). unfold file_cells in FC3.
clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. cbv delta [usegs] in SSP1, SSP2. fold usegs in SSP1, SSP2.
zs. zs. zs. if_lit.
zs. zs. zs. zs. zs. zs. zs. zs. if_lit.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 9 zs.
replace (Z.land (bv_unsigned (sx32 flags2)) 32) with 0
by (rewrite land_low7, sx32_mod128, <- land_low7 by lia; symmetry; revert FL3; apply land_sub_mask; reflexivity).
change (Z.b2z (0 <? 1) + -1) with 0. change (Z.land (bv_swrap 32 0) 18446744073709551615) with 0.
rewrite land_W64_small by (unfold INT_MAX in Hr; lia). rewrite Z.lor_0_l.
lazymatch goal with AP : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -360)%Z ?rest |- _ =>
assert (FALL : rw_cells usegs mm (bv_unsigned sp + -368) ([C8 apv] ++ rest));
[ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact AP|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
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
Lemma stdout_file_stk : forall m m' so lo hi, stdout_file m so -> munch [(lo, hi)] m m' -> wmono usegs m m' -> GLOBALS_TOP <= lo -> stdout_file m' so.
Proof.
unfold GLOBALS_TOP.
intros m m' so lo hi (flags & mode & tail & bufbytes & FC & FL & BUF & PFX & LEN & INACT) MU WM Hlo.
exists flags, mode, tail, bufbytes. split; [|split; [exact FL | split; [| split; [exact PFX | split; [exact LEN | exact INACT]]]]].
- eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells csize Nat.add]; lia].
- eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.
Lemma out_pieces_outsk : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) ps,
out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. intros St get_so set_so ps. induction ps as [|p ps IH]; cbn [out_pieces outsk]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Theorem emit_printf_proof : forall (St : Type) (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St),
emit_printf_stmt get_so set_so.
Proof.
intros St get_so set_so. unfold emit_printf_stmt. intros until v. intros GS SS FWX SF VR VA1 ST LO GLO QHI SSP MI FRM.
unfold EMIT_DEPTH, GLOBALS_TOP in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
pose proof (munch_refl [(lo, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (RSTDOUT_BUF, RSTDOUT_BUF + 1024)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
unfold s_emit, stdout_vprintf.
rewrite (out_pieces_outsk St get_so set_so (pieces_pct_d v)).
ienter.
carve_frame 80%nat ST.
do 15 zs.
do 7 zs.
apply (proj1 (rw_cells_app usegs _ _ [_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
ileave.
pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
eapply implM_post_evt.
{ eapply VF with (A := A_FMT_pct_d) (VA := bv_unsigned sp + -56) (fmt := FMT_pct_d) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i v])
(r := pct_d_len v) (lo := lo) (canary := canary);
clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, VF_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
all: try reflexivity. all: try lia.
- eapply stdout_file_stk; [exact SF | exact MU1 | exact WM | unfold GLOBALS_TOP; lia].
- apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_pct_d; lia | vm_compute; discriminate].
- unfold FMT_pct_d. forall_range.
- exact VAA.
- cbn [args_ok arg_ok]. split; [|exact I]. split; [lia | exact VA1].
- apply printf_pieces_pct_d. lia.
- exact ST.
- split; [exact SSP1 | exact SSP2].
- exact MI.
- exact FRM.
- unfold A_FMT_pct_d, FMT_pct_d. cbn [length]. lia.
- unfold A_FMT_pct_d, FMT_pct_d. cbn [length]. lia. }
cbv beta. intros [] st' ms' P. clear MU1.
unfold vfprintf_stdout_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
lazymatch type of MUc with munch _ ?mm _ => transport_after_call usegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
zs. zs. zs.
lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z ?hd, VAC : rw_cells _ ?mm (bv_unsigned sp + -56)%Z ?rest |- _ =>
assert (FALL : rw_cells usegs mm (bv_unsigned sp + -80) (hd ++ rest));
[ apply (proj2 (rw_cells_app usegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
| clear FR VAC ] end.
cbn [app] in FALL.
release_frame FALL ST3 (bv_unsigned sp).
apply evt_done. unfold emit_printf_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
split; [exact ST3|]. split; [exact SF3|]. exact SSP3.
Qed.

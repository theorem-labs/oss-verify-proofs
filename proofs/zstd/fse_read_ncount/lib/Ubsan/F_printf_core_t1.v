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
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_memset F_memcpy F_memchr F_strnlen Stdio_kit F_syscalls StdioFiles.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import Printf_zfacts F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_printf_core_common.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import StoreFast.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
Section PrintfCore.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^47)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.
Hypothesis HA : (A + zlength fmt <= 118784)%Z.
Hypothesis SEP_F : ((121784 <= Fp /\ Fp + 232 <= 324000) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((324008 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.
Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_postq := (F_printf_core_common.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation tinv := (F_printf_core_common.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (F_printf_core_common.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (F_printf_core_common.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Ltac hush := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 121776 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 324000 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call usegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [usegs usegs] in *; fold usegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp);
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.
Hypothesis HS_T2 : S_T2.
Lemma L_T1 : S_T1.
Proof using BS0 GLO HA HAP HOUT HS_T2 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw Hfl0.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
replace (Z.land fl 73728 =? 0)%Z with true by (rewrite Hfl0; reflexivity). cbn [negb orb].
ienter. zs. zs. brf K2.
-
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.
apply (rw_cells_split_CB usegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app usegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. callx (eapply memset_callZ; [exact PADa | exact MI | lia | lia | lia | lia]).
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells usegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.

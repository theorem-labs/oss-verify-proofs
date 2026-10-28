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
Local Notation POST := (F_printf_core_common.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (F_printf_core_common.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (F_printf_core_common.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
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
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
Hypothesis HS_FMTU2 : S_FMTU2.
Hypothesis HS_DLOOP : S_DLOOP.
Lemma L_FMTU : S_FMTU.
Proof using BS0 GLO HA HAP HS_DLOOP HS_FMTU2 HVA LO SEP_B SEP_F SFR.
intros fuel HH x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x prefix PFXA pfx s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (dec_digits_length x) as LDX.
stmt (HS_FMTU2 fuel HH) as NX.
ienter.
zs. zs. zs. brf K.
-
zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (d := x) (jj := 24%Z) (W := []) (prefix := prefix) (PFXA := PFXA) (pre := digs));
[ mk_finv | exact LOW | rewrite app_nil_r; exact DIG | zl | lia
| destruct (Z.eq_dec x 0) as [-> | NZ]; [left; split; [reflexivity|]; split; [reflexivity|]; apply dec_digits_0 | right; split; [lia|]; apply dec_digits_small; lia]
| exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
-
zs.
stmt HS_DLOOP as NL.
callx (eapply NL with (j := 24%Z) (ds := digs); [ exact MI | exact DIG | lia | unfold zlength; lia | f_equal; lia ]).
destruct_ands POST.
match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ => rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := x) (prefix := prefix) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG' | unfold zlength in *; rewrite length_firstn, LDS; lia | unfold zlength in *; lia
| right; split; [assumption | assumption]
| exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.
End PrintfCore.

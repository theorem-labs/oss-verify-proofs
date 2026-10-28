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
Local Notation Fok := (F_printf_core_common.Fok F).
Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation arg_ok_W := (F_printf_core_common.arg_ok_W Fp B BS q lo fmt AP slots).
Local Notation lo_cells14 := (F_printf_core_common.lo_cells14 AP nla nlt).
Local Notation lo_split := (F_printf_core_common.lo_split q AP nla nlt).
Local Notation lo_join := (F_printf_core_common.lo_join q AP nla nlt).
Local Notation pop_arg_callq := (F_printf_core_common.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
Local Notation S_CONV := (F_printf_core_common.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation S_CV_D := (F_printf_core_common.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (F_printf_core_common.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (F_printf_core_common.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
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
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
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
Hypothesis HS_CV_D : S_CV_D.
Hypothesis HS_CV_U : S_CV_U.
Hypothesis HS_CV_X : S_CV_X.
Hypothesis HS_CV_S : S_CV_S.
Hypothesis HS_CV_FP : S_CV_FP.
Lemma L_CONV : S_CONV.
Proof using BS0 GLO HA HAP HF HS_CV_D HS_CV_FP HS_CV_S HS_CV_U HS_CV_X HVA LO QHI SEP_B SEP_F SFL SFR VAHI.
intros fuel HH x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c d a args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Ht CT Hfl Hw Hp XP Hc.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
cbn [args_ok] in AOK. destruct (skipn (Z.to_nat k) slots) as [|slot slots'] eqn:ESK; [destruct AOK|]. destruct AOK as [AOK1 AOK].
assert (NTH : nth_error slots (Z.to_nat k) = Some slot).
{ rewrite <- (Nat.add_0_r (Z.to_nat k)), <- nth_error_skipn, ESK. reflexivity. }
assert (ESK' : skipn (Z.to_nat (k + 1)) slots = slots').
{ replace (Z.to_nat (k + 1)) with (1 + Z.to_nat k)%nat by lia. rewrite <- skipn_skipn, ESK. reflexivity. }
rewrite <- ESK' in AOK.
destruct (lo_split _ _ _ _ _ _ _ _ _ _ LOW) as (LOW14 & ARGC & J128). unfold lo_cells14, ssp_guard in LOW14. clear LOW.
pose proof (conv_type_cases _ _ CT) as CASES. pose proof (conv_type_range _ _ CT) as TR.
pose proof (land_bound' (d_fl d) 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq (d_fl d)) in FLB by lia.
unfold conv. cbv zeta. unfold LEFT_ADJ, ZERO_PAD.
destruct a as [sv | iv | uv | dd];
[ destruct (Z.eqb_spec (d_ty d) T_PTR) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_INT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_UINT) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l]
| destruct (Z.eqb_spec (d_ty d) T_DBL) as [ETY|NTY]; [cbn [negb] | cbn [negb]; apply implM_unr_l] ].
1: assert (T115 : d_t d = 115%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
2: assert (TDI : (d_t d = 100 \/ d_t d = 105)%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
3: assert (TUX : (d_t d = 117 \/ (d_t d = 120 \/ d_t d = 88))%Z) by (unfold T_PTR, T_INT, T_UINT, T_DBL in CASES, ETY; lia).
4: assert (TFP : conv_type (d_t d) = Some T_DBL) by (rewrite <- ETY; exact CT).
4: pose proof (proj1 (conv_type_dbl _ TFP)) as TFR.
3: destruct TUX as [T117 | TX];
[ rewrite (proj2 (Z.eqb_eq _ _) T117) | replace (d_t d =? 117)%Z with false by (symmetry; apply Z.eqb_neq; lia) ].
all: ienter; zs; br K; zs; zs; zs; zs.
all: callx (eapply pop_arg_callq; [lia | exact APC | exact VAA | exact NTH | lia | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL; lia]).
all: idtac.
all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi F_pop_arg.T_PTR F_pop_arg.T_INT F_pop_arg.T_UINT F_pop_arg.T_DBL T_PTR T_INT T_UINT T_DBL Z.eqb Pos.eqb] in ARGC' end.
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: zs.
all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; br K1; clear FLC.
all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
all: zsto 0x17e24%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br K2a; zsto 0x17e38%Z; rewrite (nzmask_eq (d_fl d)) by lia; zs; brf K2;
[ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
| assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; lia);
rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
all: zsto 0x17e48%Z; zs; br K3; zsto 0x17e5c%Z.
all: replace (Z.shiftl (d_t d + -65) 2 + 68928)%Z with (68928 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
all: first [ the_mi ltac:(fun M => pose proof (jt1_read_s _ _ M T115) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_d _ _ M TDI) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_u _ _ M T117) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_x _ _ M TX) as RD1)
| the_mi ltac:(fun M => pose proof (jt1_read_fp _ _ M TFP) as RD1) ].
all: zs; zs; zs.
all: let s8v := getreg 24%Z in lazymatch s8v with Z_to_bv 64 ?f => set (fl' := f) in |- * end.
all: assert (Hfl' : (0 <= fl' < 131072)%Z) by (subst fl'; lia).
all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mm _) =>
lazymatch pc with
| 98048%Z =>
rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
match goal with MUc : munch _ m0 mm |- _ =>
destruct (arg_ok_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4 & SD5) end;
stmt (HS_CV_S fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
(xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact SD1 | exact SD2 | exact SD3 | exact SD5
| subst fl'; rewrite ?land_land_same; reflexivity ]
| 97976%Z =>
destruct AOK1 as [Hiv Emod];
rewrite (sx32_int slot iv Hiv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_D fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Hiv ]
| 98288%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_U fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv ]
| 98408%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_X fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact Huv | exact TX ]
| 97896%Z =>
cbn [arg_ok] in AOK1; rewrite AOK1 in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
unfold LEFT_ADJ, ZERO_PAD in FPC1;
first [ rewrite (proj2 (Z.eqb_eq _ _) K2) in FPC1 | rewrite (proj2 (Z.eqb_neq _ _) K2') in FPC1 ]; rewrite ?ift, ?iff in FPC1;
stmt (HS_CV_FP fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (y := f128_of_d dd) (t := d_t d));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | lia | exact AOK | subst fl'; exact FPC1 | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | apply f128_of_d_range | exact TFP ]
end end.
Qed.
End PrintfCore.

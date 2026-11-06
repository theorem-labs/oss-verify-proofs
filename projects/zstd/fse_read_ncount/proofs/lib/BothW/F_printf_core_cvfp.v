(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import Stdio_kit Stdio_kitI F_syscalls StdioFiles MonadF MonadF2 RtCells Strnlen_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_pop_arg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import Printf_zfacts F_printf_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_printf_core_common.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
Section CANSEC1. Context {rc : runConstT}.
Section PrintfCore.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= lazymatch goal with |- acc_in _ (wa ?e, ?n) => change (wa e) with (Z_to_bv 64 e : word); solve_acc1 end.
Local Ltac acc_enrich ::=
repeat match goal with
| H : nth_error ?l ?k = Some ?x |- _ =>
lazymatch goal with _ : (k < length l)%nat |- _ => fail | _ => pose proof (nth_error_some_bound l k x H) end
end;
rewrite ?u32s_length, ?u64s_length, ?length_app, ?repeat_length, ?zb_length in *; cbn [length] in *; unfold zlength in *.
Context {St : Type}.
Variables (Fp B BS : Z) (RB : region) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS RB SINK TOPOK OUT.
Hypothesis HSTRN : strnlen_a_stmt.
Variables (RNG : footprint) (rstk rfmt : region).
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^47)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.
Hypothesis HA : (A + zlength fmt <= 626688)%Z.
Hypothesis SEP_F : ((636800 <= Fp /\ Fp + 232 <= 664888) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6247704 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.
Hypothesis KH : (KHIGH <= lo)%Z.
Hypothesis RSK : (r_lo rstk <= lo /\ q <= r_hi rstk)%Z.
Hypothesis RFM : inreg rfmt A (zlength fmt).
Hypothesis RPF : inreg rfmt 68452 9.
Hypothesis RBI : inreg RB B BS.
Hypothesis RG_stk : rng RNG lo (q - lo).
Hypothesis RG_img : rng_aimg RNG.
Hypothesis RG_ap : rng RNG AP 8.
Hypothesis RG_va : rng RNG VA (8 * zlength slots).
Hypothesis RG_F : rng RNG Fp 232.
Hypothesis RG_B : rng RNG B BS.
Hypothesis RG_fmt : rng RNG A (zlength fmt).
Hypothesis RR_stk : rrng RNG rstk.
Hypothesis RR_fmt : rrng RNG rfmt.
Hypothesis RR_B : rrng RNG RB.
Hypothesis ENV0 : ashenv m0.
Hypothesis RC_stk : rclean m0 rstk.
Hypothesis RC_fmt : rclean m0 rfmt.
Hypothesis RC_B : rclean m0 RB.
Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
Local Notation Fok := (F_printf_core_common.Fok F).
Local Notation Fok_trans := (F_printf_core_common.Fok_trans F).
Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (F_printf_core_common.out_callq (St:=St) Fp B BS RB SINK TOPOK OUT TOK HOUT RNG q gp tp m0 lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
Local Notation fp_postq := (F_printf_core_common.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation fp_callq := (F_printf_core_common.fp_callq (St:=St) Fp B BS RB SINK TOPOK OUTFP TOK RNG q gp tp m0 lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation S_CV_FP := (F_printf_core_common.S_CV_FP (St:=St) Fp B BS RB SINK TOPOK OUT OUTFP RNG rstk rfmt ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Ltac hush := idtac.
Ltac len_norm := unfold zlength, zrepeat; rewrite ?repeat_length, ?zb_length, ?length_map, ?length_firstn, ?length_skipn, ?length_app; cbn [length]; try rewrite !Z2Nat.id by lia.
Ltac inreg_side := solve [ unfold inreg in *; len_norm; unfold zlength in *; lia ].
Ltac rng_side :=
lazymatch goal with |- rng ?RNG0 ?lo' ?len' =>
first [ assumption
| match goal with H : rng RNG0 ?lo ?len |- _ => apply (rng_sub' RNG0 lo len lo' len' H); solve [len_norm; unfold zlength in *; lia] end ]
end.
Ltac hypMU := match goal with H : munch _ m0 _ |- _ => exact H end.
Ltac hypWM := match goal with H : wmono _ m0 _ |- _ => exact H end.
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
Tactic Notation "jump" tactic3(tac) := eapply evtF_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evtF _ _ _ _ => apply evtF_done | _ => idtac end);
eapply implAM_eq_ms; [ | tac ]; [ mseq | .. ].
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
Ltac out_call_with r :=
ileave; eapply implAM_bind;
[ eapply (out_callq r);
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 632224 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 6247696 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | |
| hypMU | hypWM
| first [ assumption | idtac ]
| first [ inreg_side | idtac ]
| first [ rng_side | idtac ]
| first [ assumption | idtac ] ]
| cbv beta ].
Tactic Notation "out_call" constr(r) := out_call_with r.
Tactic Notation "out_call" := out_call_with rfmt.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
#[using="TOK LO GLO QHI TQ HA SEP_F SEP_B HAP HVA BS0 KH RBI RG_stk RG_img RG_F RG_B RR_B ENV0 RC_B"] Lemma L_CV_FP : S_CV_FP.
Proof.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp y t pfx s2s za pl plp j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Hfl Hw Hc XP Hy CT.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (conv_type_dbl t CT) as [Ht Hta].
pose proof (lo64_range y) as RL. pose proof (hi64_range y) as RH.
ienter.
assert (XF : (xp && (p <? 0))%bool = false).
{ destruct XP as [[-> ->] | [-> Hp]]; [reflexivity|]. cbn [andb]. apply Z.ltb_ge. lia. }
rewrite XF.
Local Ltac2 Set LiaHints.tbl := fun () => "00<0?1496497250.163 29010569984.18029010569984.18231156070898.16536722663379.16236722663379.16444809696627.16344809696639.16146271681011.16346271681020.16266201836243.16366201836243.16400000100?00M00X00`00h01301>01I01T01\01dFS3LZB2LU2RP2RSS3LZB2LU2RP2RSS2Hp3LZB2LUS3LZB2LUS3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS2LO3LZB2LUS3LZB2LUS3LZB2LU".
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z];
[ zs; zs; rewrite Z.land_0_l; zs; if_lit
| zs; zs;
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia);
cbn [Z.b2z Z.land]; zs; if_lit ].
all: destruct (Z.ltb_spec0 1 w) as [W1|W1]; [cbn [orb]; ileave; apply implAM_unr_l|].
all: match goal with |- context [if (?a || ?b)%bool then munr else _] =>
destruct b eqn:P20; [ileave; apply implAM_unr_l | cbn [orb]] end.
all: match goal with P20 : (?a <=? ?pp)%Z = false |- _ => apply Z.leb_gt in P20 end.
all: zs; zs; zs; zs; zs; zs; zs; zs.
all: ileave; massocF; eapply implAM_bind;
[ eapply fp_callq;
[ exact FPC1 | exact HS | rewrite !unsigned_lit by lia; symmetry; apply lo64_hi64; lia | rewrite unsigned_lit by lia; lia | lia | lia | lia | lia | exact Hta
| exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | exact MI | exact FRM | hypMU | hypWM ]
| cbv beta ].
all: intros r st'; lazymatch goal with |- context [fp_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => post_call bsegs mm end.
all: try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end).
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: unfold INT_MAX in *.
all: destruct (Z.lt_ge_cases r 0) as [RN|RP];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; left; apply Z.ltb_lt; exact RN); apply implAM_unr_l | ].
all: destruct (Z.lt_ge_cases 2147483647 r) as [RBg|RS];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; right; apply Z.ltb_lt; lia); apply implAM_unr_l | ].
all: replace (r <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia); cbn [orb].
all: destruct (Z.ltb_spec0 (2147483647 - c) r) as [OV|OV]; [apply implAM_unr_l|].
all: apply implAM_ret_l.
all: ienter;
try (lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
all: zs; zs; brf KR; [ | exfalso; try rewrite unsigned_lit in KR by lia; try rewrite land_M64_id in KR by lia; lia ].
all: stmt HH as NXH.
all: jumpM (eapply NXH with (i := i4) (cnt := c) (l := r) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; hyp | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC
| assumption | exact FOK2 | lia | lia | lia | unfold INT_MAX; lia ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PrintfCore.
End CANSEC1.

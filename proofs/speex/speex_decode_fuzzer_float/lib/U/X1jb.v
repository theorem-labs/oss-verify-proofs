(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c8 X1bj X1cc X1bu X1bq X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require X1bk X1c5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1rd X1oc X1ri X1rl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1fd X1fc X1gi X1en X1fl X1ei. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1eh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fo X1ea X1jh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1jg. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1jj X1fr.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fq.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cb.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.

Module F_printf_core_conv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation Fok := (X1fq.Fok F).
Local Notation Fok_trans := (X1fq.Fok_trans F).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation arg_ok_W := (X1fq.arg_ok_W Fp B BS q lo fmt AP slots).
Local Notation lo_cells14 := (X1fq.lo_cells14 AP nla nlt).
Local Notation lo_split := (X1fq.lo_split q AP nla nlt).
Local Notation lo_join := (X1fq.lo_join q AP nla nlt).
Local Notation pop_arg_callq := (X1fq.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_CONV := (X1fq.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (X1fq.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (X1fq.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (X1fq.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (X1fq.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (X1fq.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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
all: callx (eapply pop_arg_callq; [(clear - q; lia) | exact APC | exact VAA | exact NTH | (clear - Hk k; lia) | exact ARGC | exact ST | exact MI | rewrite ETY; unfold T_PTR, T_INT, T_UINT, T_DBL; lia]).
all: idtac.
all: match goal with H : rw_cells _ _ (q + -544 + 112)%Z _ |- _ => rename H into ARGC'; rewrite ETY in ARGC'; cbn [pop_arg_lo pop_arg_hi X1fo.T_PTR X1fo.T_INT X1fo.T_UINT X1fo.T_DBL T_PTR T_INT T_UINT T_DBL Z.eqb Pos.eqb] in ARGC' end.
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: zs.
all: match goal with H : SINK ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (SFL _ _ H) as (fb & FLC & FB) end; zs; zs; zs; br K1; clear FLC.
all: rd_fmt (i4 - 1)%Z; zs; fix_u8 (i4 - 1)%Z; rewrite Ht.
all: zsto 0x35850%Z; change (Z.b2z (0 <? 0)) with 0%Z; rewrite Z.land_0_l; zs; br K2a; zsto 0x35864%Z; rewrite (nzmask_eq (d_fl d)) by (clear - Hfl d; lia); zs; brf K2;
[ apply (proj1 (fl_shl50 _ Hfl)) in K2; rewrite (proj2 (Z.eqb_eq _ _) K2); rewrite ?ift
| assert (K2' : Z.land (d_fl d) 8192 <> 0%Z) by (intros E; apply (proj2 (fl_shl50 _ Hfl)) in E; (clear - E K2 LU LZB d slots fmt; lia));
rewrite (proj2 (Z.eqb_neq _ _) K2'); rewrite ?iff; zs ].
all: zsto 0x35874%Z; zs; br K3; zsto 0x35888%Z.
all: replace (Z.shiftl (d_t d + -65) 2 + 99120)%Z with (99120 + 4 * (d_t d - 65))%Z by (rewrite Z.shiftl_mul_pow2; lia).
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
| 219436%Z =>
rewrite <- (Z_to_bv_bv_unsigned slot) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
match goal with MUc : munch _ m0 mm |- _ =>
first [ pose proof (arg_ok_W _ _ _ _ AOK1 MUc) as sfP_; sf_destruct 9%nat sfP_ as slack STR SRNG SPAD P0 SD1 SD2 SD3 SD4 | sf_fb; destruct (arg_ok_W _ _ _ _ AOK1 MUc) as (slack & STR & SRNG & SPAD & P0 & SD1 & SD2 & SD3 & SD4) ] end;
stmt (HS_CV_S fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (fl10 := Z.land (d_fl d) (Z.lnot 65536))
(xp := d_xp d) (P := bv_unsigned slot) (s := sv) (slack := slack));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; (clear - Hw d; lia) | unfold INT_MAX; (clear - Hc c; lia) | exact XP | exact STR | exact SRNG | exact SPAD | exact P0 | exact SD1 | exact SD2 | exact SD3
| subst fl'; rewrite ?land_land_same; reflexivity ]
| 219364%Z =>
destruct AOK1 as [Hiv Emod];
rewrite (sx32_int slot iv Hiv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_D fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (i := iv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; (clear - Hw d; lia) | unfold INT_MAX; (clear - Hc c; lia) | exact XP | exact Hiv ]
| 219676%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_U fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; (clear - Hw d; lia) | unfold INT_MAX; (clear - Hc c; lia) | exact XP | exact Huv ]
| 219796%Z =>
destruct AOK1 as [Huv Emod];
rewrite (zx32_uint slot uv Emod) in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
stmt (HS_CV_X fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (u := uv) (t := d_t d));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; (clear - Hw d; lia) | unfold INT_MAX; (clear - Hc c; lia) | exact XP | exact Huv | exact TX ]
| 219284%Z =>
cbn [arg_ok] in AOK1; rewrite AOK1 in ARGC';
pose proof (lo_join _ _ _ _ _ _ _ _ _ _ LOW14 ARGC' J128) as LOW';
unfold LEFT_ADJ, ZERO_PAD in FPC1;
first [ rewrite (proj2 (Z.eqb_eq _ _) K2) in FPC1 | rewrite (proj2 (Z.eqb_neq _ _) K2') in FPC1 ]; rewrite ?ift, ?iff in FPC1;
stmt (HS_CV_FP fuel HH) as NX;
jumpM (eapply NX with (i4 := i4) (k := (k + 1)%Z) (c := c) (args := args) (fl := fl') (w := d_w d) (p := d_p d) (xp := d_xp d) (y := f128_of_d dd) (t := d_t d));
[ mk_finv | exact LOW' | hyp | hyp | hyp | hyp | (clear - Hk k; lia) | exact AOK | subst fl'; exact FPC1 | exact FPC | exact FRM | exact FOK2
| zl | exact Hfl' | unfold INT_MAX; (clear - Hw d; lia) | unfold INT_MAX; (clear - Hc c; lia) | exact XP | apply f128_of_d_range | exact TFP ]
end end.
Qed.
End PrintfCore.
End F_printf_core_conv.

Module F_printf_core_intc2.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation S_TAIL := (X1fq.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (X1fq.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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

Hypothesis HS_TAIL : S_TAIL.

Lemma L_INTC2 : S_INTC2.
Proof using GLO HAP HS_TAIL LO QHI SEP_B SEP_F.
intros fuel HH x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc Hargi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (zb_length body) as LB.
set (n := Z.of_nat (length body)) in *.
stmt (HS_TAIL fuel HH) as NX.
ienter.
zs. zs. brf K1.
-
replace (argi =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite ?if_false_Z, ?Z.add_0_r.
zs. zs. zs. zs. replace (argi <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite ?Z.add_0_r.
zs. brf K2; [ | zs ]; zs; zs.
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p n) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
| unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | (clear - PF0 PFXA; lia) | zl | zl | zl | (clear - Hfl fl; lia) | unfold INT_MAX; (clear - Hw w; lia) | unfold INT_MAX; (clear - K2 LB BLEN BEND BA body p q Hp; lia) | unfold INT_MAX; (clear - Hc c; lia) ].
-
replace (argi =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb]. rewrite ?if_true_Z.
zs. brf K3.
+
assert (Hp0 : p <> 0%Z) by (intros E; apply K3; apply (proj2 (landM64_zero p ltac:(lia))); exact E).
replace (p =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hp0).
zs. zs. zs. zs. replace (argi <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
zs. brf K2; [ | zs ]; zs; zs.
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := Z.max p (n + 1)) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG
| unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | (clear - PF0 PFXA; lia) | zl | zl | zl | (clear - Hfl fl; lia) | unfold INT_MAX; (clear - Hw w; lia) | unfold INT_MAX; (clear - K2 Hp0 LB BLEN BEND BA body p q Hp; lia) | unfold INT_MAX; (clear - Hc c; lia) ].
+
assert (Hp0 : p = 0%Z) by (apply (proj1 (landM64_zero p ltac:(lia))); exact K3).
replace (p =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact Hp0).
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (prefix := prefix) (body := []) (BA := (q + -368)%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| apply bytes_at_nil; lia | apply Forall_nil
| unfold body_loc; zl | zl | unfold INT_MAX; zl | exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.
End F_printf_core_intc2.

Module F_printf_core_t1.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_postq := (X1fq.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (X1fq.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (X1fq.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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
apply (rw_cells_split_CB rsegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. callx (eapply memset_callZ; [exact PADa | exact MI | (clear - K2 LP LB LU LZB body prefix pl pq wq w QHI GLO LO slots fmt lo q; lia) | (clear - K2 LP LB LU LZB body prefix pl pq wq w QHI GLO LO slots fmt lo q; lia) | lia | (clear - N256 K2 LP Hwq body prefix pl pq wq w; lia)]).
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; (clear - K4 K3 LP LB LU LZB n4 body prefix pl pq wq w slots fmt; lia)].
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
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells rsegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T2 fuel HH) as NX2.
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.
End F_printf_core_t1.

Module F_printf_core_cvx.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation POST := (X1fq.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (X1fq.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_XLOOP := (X1fq.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (X1fq.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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

Hypothesis HS_INTC : S_INTC.
Hypothesis HS_XLOOP : S_XLOOP.

Lemma L_CV_X : S_CV_X.
Proof using BS0 GLO HA HAP HS_INTC HS_XLOOP HVA LO QHI SEP_B SEP_F SFR.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u t pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu Ht.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
stmt (HS_INTC fuel HH) as NX.
unfold ALT_FORM.
assert (Hl : (Z.land t 32 = 0 \/ Z.land t 32 = 32)%Z) by (destruct Ht as [-> | ->]; [right | left]; reflexivity).
pose proof (hex_digits_length (Z.land t 32) u) as LH.
assert (HRNG : Forall (fun c0 => 0 <= c0 < 256)%Z (hex_digits (Z.land t 32) u)).
{ eapply Forall_impl; [|apply hex_digits_range; exact Hl]. cbv beta. intros. lia. }
ienter.
zs. zs. zs. zs. brf K0.
-
replace (u =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K0). cbn [negb andb].
zs. zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := []) (BA := (q + -368)%Z) (PFXA := 66274%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite K0, hex_digits_0; apply bytes_at_nil; lia | exact HRNG | rewrite K0, hex_digits_0; zl | zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
- replace (u =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K0). cbn [negb andb].
zs. zs.
replace (Z.land t 32) with (Z.land t 32) by reflexivity.
stmt HS_XLOOP as NL.
callx (eapply NL with (l := Z.land t 32) (x := u) (j := 24%Z) (ds := digs);
[ exact MI | exact DIG | (clear - K0 Hu u; lia) | exact Hl | unfold zlength; (clear - LH t u; lia) | f_equal; (clear - q; lia) ]).
destruct_ands POST. cbv zeta in *.
match goal with H : rw_cells _ _ (q + -392)%Z [CB 24 ?l] |- _ =>
rewrite (skipn_all2 digs) in H by (rewrite LDS; lia); rewrite app_nil_r in H; rename H into DIG' end.
pose proof (rw_cells_bytes_at' _ _ _ _ DIG') as BODY. cbn [cells_bytes cbytes app] in BODY. rewrite app_nil_r in BODY.
apply bytes_at_app in BODY. destruct BODY as [_ BODY]. rewrite length_firstn, LDS in BODY.
replace (Z.of_nat (Nat.min (Z.to_nat (24 - zlength (hex_digits (Z.land t 32) u))) 24)) with (24 - zlength (hex_digits (Z.land t 32) u))%Z in BODY by (unfold zlength in *; lia).
zs. zs. brf K1.
+
replace (Z.land fl 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact K1). cbn [negb andb].
zs. zs. zs. zs. zs. zs. zs. zs.
destruct Ht as [-> | ->]; cbn [Z.eqb Pos.eqb].
* jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 120]%Z)
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land 120 32) u)))%Z) (PFXA := 66281%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 7 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
* jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [48; 88]%Z)
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land 88 32) u)))%Z) (PFXA := 66279%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 5 2 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
+
replace (Z.land fl 8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact K1). cbn [negb andb].
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := u) (prefix := [])
(BA := (q + -392 + (24 - zlength (hex_digits (Z.land t 32) u)))%Z) (PFXA := 66274%Z));
[ mk_finv | exact LOW | exact DIG' | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact BODY | exact HRNG | unfold zlength in *; lia | zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.
End PrintfCore.
End F_printf_core_cvx.

Module F_printf_core_cvfp.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation Fok := (X1fq.Fok F).
Local Notation Fok_trans := (X1fq.Fok_trans F).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation fp_postq := (X1fq.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation fp_callq := (X1fq.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (X1fq.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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

Lemma L_CV_FP : S_CV_FP.
Proof using GLO HA HAP HVA LO QHI SEP_B SEP_F TOK TQ.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp y t pfx s2s za pl plp j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC1 FPC FRM FOK Hi4 Hfl Hw Hc XP Hy CT.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (conv_type_dbl t CT) as [Ht Hta].
pose proof (lo64_range y) as RL. pose proof (hi64_range y) as RH.
ienter.

assert (XF : (xp && (p <? 0))%bool = false).
{ destruct XP as [[-> ->] | [-> Hp]]; [reflexivity|]. cbn [andb]. apply Z.ltb_ge. lia. }
rewrite XF.
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z];
[ zs; zs; rewrite Z.land_0_l; zs; if_lit
| zs; zs;
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by (clear - Hp p; lia); rewrite Z.mod_small by (clear - Hp p; lia); (clear - Hp p; lia));
cbn [Z.b2z Z.land]; zs; if_lit ].

all: destruct (Z.ltb_spec0 1 w) as [W1|W1]; [cbn [orb]; ileave; apply implM_unr_l|].
all: match goal with |- context [if (?a || ?b)%bool then munr else _] =>
destruct b eqn:P20; [ileave; apply implM_unr_l | cbn [orb]] end.
all: match goal with P20 : (?a <=? ?pp)%Z = false |- _ => apply Z.leb_gt in P20 end.
all: zs; zs; zs; zs; zs; zs; zs; zs.
all: ileave; massoc; eapply implM_bind;
[ eapply fp_callq;
[ exact FPC1 | exact HS | rewrite !unsigned_lit by lia; symmetry; apply lo64_hi64; lia | rewrite unsigned_lit by lia; lia | lia | lia | lia | lia | exact Hta
| exact ST | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | exact MI | exact FRM ]
| cbv beta ].
all: intros r st'; lazymatch goal with |- context [fp_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => post_call rsegs mm end.
all: try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end).
all: match goal with H : Fokd ?F1 ?F2, G : Fok ?F1 |- _ => pose proof (Fok_trans _ _ G H) as FOK2 end.
all: unfold INT_MAX in *.

all: destruct (Z.lt_ge_cases r 0) as [RN|RP];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; left; apply Z.ltb_lt; exact RN); apply implM_unr_l | ].
all: destruct (Z.lt_ge_cases 2147483647 r) as [RB|RS];
[ replace ((r <? 0) || (2147483647 - c <? r))%bool with true by (symmetry; apply orb_true_iff; right; apply Z.ltb_lt; lia); apply implM_unr_l | ].
all: replace (r <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia); cbn [orb].
all: destruct (Z.ltb_spec0 (2147483647 - c) r) as [OV|OV]; [apply implM_unr_l|].
all: apply implM_ret_l.
all: ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
all: zs; zs; brf KR; [ | exfalso; try rewrite unsigned_lit in KR by lia; try rewrite land_M64_id in KR by lia; lia ].
all: stmt HH as NXH.
all: jumpM (eapply NXH with (i := i4) (cnt := c) (l := r) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; hyp | hyp | hyp | hyp | hyp | lia | exact AOK | exact FPC
| assumption | exact FOK2 | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.
End F_printf_core_cvfp.

Module F_printf_core_t2.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_postq := (X1fq.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (X1fq.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (X1fq.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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

Hypothesis HS_T3 : S_T3.

Lemma L_T2 : S_T2.
Proof using BS0 GLO HA HAP HOUT HS_T3 HVA LO QHI SEP_B SEP_F SFL TOK TQ.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
ienter.
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
out_call.
1:{ apply HPFX. exact MI. }
1:{ exact PRNG. }
1:{ rewrite Hpl. reflexivity. }
1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
stmt (HS_T3 fuel HH) as NX3.
jumpM (eapply NX3 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.
End F_printf_core_t2.

Module F_printf_core_fmtu2.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (X1fq.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (X1fq.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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

Hypothesis HS_INTC : S_INTC.

Lemma L_FMTU2 : S_FMTU2.
Proof using BS0 GLO HA HAP HS_INTC HVA LO QHI SEP_B SEP_F SFR.
intros fuel HH x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp x d jj W prefix PFXA pfx s2s za plp ahi j128 pre pad _
FI LOW DIG Hjj Hjj1 HD PAD HS APC Hk AOK FPC FRM FOK HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hx.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (rw_CB_length _ _ _ _ DIG) as LDS. rewrite length_app, zb_length in LDS.
pose proof (dec_digits_length x) as LDX.
stmt (HS_INTC fuel HH) as NX.
ienter.
zs. zs. brf K1.
-
destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [|exfalso; lia].
rewrite app_nil_r in DIG.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -368)%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite DX; apply bytes_at_nil; lia | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; lia | rewrite DX; zl | rewrite DX; zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
-
destruct HD as [(Hd0 & -> & DX) | (Hd & DX)]; [exfalso; lia|].
assert (LW : (Z.of_nat (length W) + 1 <= 20)%Z) by (rewrite DX in LDX; cbn [length] in LDX; lia).
zs. rewrite lor48_digit by lia. zs.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA. clear DIG.
pose proof (u8arr_store_ok rsegs _ _ _ (jj - 1)%Z (wa (q + -392 + jj + -1)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_small by lia. replace (q + -392 + jj + -1)%Z with (q + -392 + (jj - 1))%Z by lia.
pose proof (u8arr_write rsegs _ _ _ (jj - 1)%Z (Z_to_bv 8 (48 + d)) DA ltac:(rewrite length_app, zb_length; unfold zlength in *; lia)) as DA2. clear DA. store_done.
assert (EU : upd (pre ++ zb W) (Z.to_nat (jj - 1)) (Z_to_bv 8 (48 + d)) = firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W)).
{ rewrite upd_firstn_skipn by (rewrite length_app, zb_length; unfold zlength in *; lia).
rewrite firstn_app. replace (Z.to_nat (jj - 1) - length pre)%nat with 0%nat by (unfold zlength in *; lia). cbn [firstn]. rewrite app_nil_r.
replace (S (Z.to_nat (jj - 1))) with (length pre) by (unfold zlength in *; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
rewrite EU in DA2.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG.
replace (length (firstn (Z.to_nat (jj - 1)) pre ++ zb ((48 + d)%Z :: W))) with 24%nat in DIG
by (rewrite length_app, length_firstn, zb_length; cbn [length]; unfold zlength in *; lia).
pose proof (proj1 DA2) as BODY. apply bytes_at_app in BODY. destruct BODY as [_ BODY].
rewrite length_firstn in BODY. replace (Z.of_nat (Nat.min (Z.to_nat (jj - 1)) (length pre))) with (jj - 1)%Z in BODY by (unfold zlength in *; lia).
zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (argi := x) (prefix := prefix) (body := dec_digits x) (BA := (q + -392 + (jj - 1))%Z) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK
| rewrite DX; exact BODY | eapply Forall_impl; [|apply dec_digits_range]; cbv beta; intros; (clear - H a; lia) | rewrite DX; zl | rewrite DX; zl
| exact HPFX | exact PRNG | (clear - PF0 PFXA; lia) | zl | zl | zl | (clear - Hfl fl; lia) | unfold INT_MAX; (clear - Hw w; lia) | unfold INT_MAX; (clear - Hc c; lia) | exact XP | (clear - Hx x; lia) ].
Qed.
End PrintfCore.
End F_printf_core_fmtu2.

Module F_printf_core_exit.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation POST := (X1fq.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_EXIT := (X1fq.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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

Lemma L_EXIT : S_EXIT.
Proof using LO.
intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _ FI LOW DIG PAD HS APC FRM FOK Hr.
dest_finv FI. unfold lo_cells, ssp_guard in LOW.
zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 14 zstep.
zstep. zstep.

release_frame LOW ST (q + -392)%Z.
release_frame DIG ST (q + -368)%Z.
release_frame PAD ST (q + -112)%Z.
release_frame FRhi ST q.
apply evt_done. unfold POST.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact FOK|].
split; [exact ST|]. split; [exact HS|]. split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2]|]. split; [exact APC|]. exact Hr.
Qed.
End PrintfCore.
End F_printf_core_exit.

Module F_printf_core_fmtu.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation POST := (X1fq.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DLOOP := (X1fq.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (X1fq.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (X1fq.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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
callx (eapply NL with (j := 24%Z) (ds := digs); [ exact MI | exact DIG | (clear - K Hx x; lia) | unfold zlength; (clear - LDX x; lia) | f_equal; (clear - q; lia) ]).
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
End F_printf_core_fmtu.

Module F_printf_core_end.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_EXIT := (X1fq.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (X1fq.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
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
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
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

Hypothesis HS_EXIT : S_EXIT.

Lemma L_END : S_END.
Proof using GLO HAP HS_EXIT LO SEP_F VAHI.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m st r pfx s2s za pl plp l10n alo ahi j128 digs pad apv _
FI LOW DIG PAD HS APC FRM FOK Hr.
pose proof FI as FI'. dest_finv FI.
zs. br K.
stmt HS_EXIT as NX. jump (eapply NX; [exact FI' | exact LOW | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | exact Hr]).
Qed.
End PrintfCore.
End F_printf_core_end.

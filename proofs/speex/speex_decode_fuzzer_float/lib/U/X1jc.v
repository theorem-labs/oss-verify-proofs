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

Module F_printf_core_tail.
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

Hypothesis HS_T1 : S_T1.
Hypothesis HS_T2 : S_T2.

Lemma conv_tail_k : forall (a1 a2 a3 a4 a5 a6 : M St unit) (v : Z) (k : Z -> M St Z) s Q ms,
implM rsegs (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; k v) s Q ms ->
implM rsegs (x <- (a1 ;;; a2 ;;; a3 ;;; a4 ;;; a5 ;;; a6 ;;; mret v) ;; k x) s Q ms.
Proof using .
clear. intros a1 a2 a3 a4 a5 a6 v k s Q ms H.
Ltac kstep H := apply implM_assoc; eapply implM_bind_ext; [ | exact H ]; cbv beta;
let x := fresh "x" in let s' := fresh "s'" in let ms' := fresh "ms'" in let H' := fresh "H" in
intros x s' ms' H'.
kstep H. kstep H0. kstep H1. kstep H2. kstep H3. kstep H4. apply implM_ret_l. exact H5.
Qed.

Lemma L_TAIL : S_TAIL.
Proof using BS0 GLO HA HAP HS_T1 HS_T2 HVA LO QHI SEP_B SEP_F SFR VAHI.
intros fuel HH x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p prefix body BA PFXA s2s za plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BLOC BHI BIM HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hp Hc.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW. unfold body_loc in BLOC.
pose proof (bytes_at_bound _ _ _ _ BODY) as BB. pose proof (zb_length body) as LB. rewrite LB in BB.
set (n := Z.of_nat (length body)) in *. set (pl := Z.of_nat (length prefix)) in *.
unfold conv_tail. unfold zlength. fold n. fold pl. cbv zeta.
ienter.
zs. rewrite (sextw_small p) by lia. zs. replace (BA + n - BA)%Z with n by lia. zs. zs. zs.
brf K1; [ | zs ].

all: zs; try rewrite (sextw_small p) by lia; fixr; zs; zs; fixr; zs; brf K2;
[ replace (INT_MAX - pl <? Z.max p n)%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; (clear - K2 K1 LB PL2 body prefix p; lia)); ileave; apply implM_unr_l
| replace (INT_MAX - pl <? Z.max p n)%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; (clear - K2 K1 LB PL2 body prefix p; lia)) ].

all: zs; zs; zs; fixr; zs; zs; zs; brf K3; [ | zs ].

all: zs; brf K4;
[ replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with true by (symmetry; apply Z.ltb_lt; unfold INT_MAX; (clear - K4 K1 LB body prefix p w c K3; lia)); ileave; apply implM_unr_l
| replace (INT_MAX - c <? Z.max w (pl + Z.max p n))%Z with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; (clear - K4 K3 K1 LB body prefix p w c; lia)) ].

all: zs; zs; zs; zs; brf K5.
all: ileave; apply conv_tail_k.
all: match goal with
| K : Z.land ?flv 73728 <> 0%Z |- _ =>
unfold mpad at 1; change (Z.lor LEFT_ADJ ZERO_PAD) with 73728%Z; rewrite (proj2 (Z.eqb_neq _ 0) K); cbn [negb orb]; apply implM_ret_l;
stmt (HS_T2 fuel HH) as NX2;
jumpM (eapply NX2 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | (clear - Hc c; lia) | (clear - K1 LB Hw body prefix p w; lia) | (clear - pl n p w; lia) | unfold INT_MAX; (clear - K4 K3 K1 LB body prefix p w c; lia) ]
| K : Z.land ?flv 73728 = 0%Z |- _ =>
stmt (HS_T1 fuel HH) as NX1;
jumpM (eapply NX1 with (k := k) (i4 := i4) (c := c) (w := w) (wq := Z.max w (pl + Z.max p n)) (pq := Z.max p n) (args := args)
(PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | (clear - Hc c; lia) | (clear - K1 LB Hw body prefix p w; lia) | (clear - pl n p w; lia) | unfold INT_MAX; (clear - K4 K3 K1 LB body prefix p w c; lia) | exact K ]
end.
Qed.
End PrintfCore.
End F_printf_core_tail.

Module F_printf_core_head.
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
Local Notation S_SCAN := (X1fq.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (X1fq.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (X1fq.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (X1fq.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (X1fq.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Notation sfx := (sfx fmt).
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

Hypothesis HS_SCAN : S_SCAN.
Hypothesis HS_DIR : S_DIR.
Hypothesis HS_CONV : S_CONV.
Hypothesis HS_END : S_END.

Lemma L_HEAD : forall fuel, S_HEAD fuel.
Proof using A0 BS0 GLO HA HAP HF HOUT HS_CONV HS_DIR HS_END HS_SCAN HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI.
induction fuel as [|fuel IH]; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 Ft fc m st i cnt l k args pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi Hcnt Hl Hcl.
{ cbn [printf_loop]. apply implM_unr. }
rewrite printf_loop_S. rewrite fp_calls_S in FPC.
destruct (sfx i) as [|c s'] eqn:Es. { apply implM_unr. }
destruct (sfx_cons_inv fmt i c s' Hi Es) as (Hilt & Ec & Es').
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (fmt_rng i ltac:(zl)) as RGi.
destruct (Z.eqb_spec c 0) as [C0|C0].
{
apply implM_ret.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. rewrite <- Ec, C0. zs. fixr. zs. if_lit.
stmt HS_END as NX. jump (eapply NX; [exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | exact FRM | exact FOK | unfold INT_MAX; lia]). }
rewrite <- Es in *. cbv zeta. cbv zeta in FPC.
pose proof (lit_run_sfx fmt i Hi) as sfP_; first [ sf_destruct 4%nat sfP_ as Hn Hs1 LIT Hlit | sf_fb; destruct sfP_ as (Hn & Hs1 & LIT & Hlit) ]. cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (lit := lit_run (sfx i)) in *. set (n := Z.of_nat (length lit)) in *.
rewrite Hs1. rewrite Hs1 in FPC.
assert (Hn0 : (0 <= n)%Z) by (unfold n; lia).
destruct (sfx (i + n)) as [|c1 s2] eqn:Es1. { apply implM_unr. }
destruct (sfx_cons_inv fmt (i + n) c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
match goal with |- context [if ?b then munr else _] => destruct b eqn:PCT; [apply implM_unr|] end.

assert (TERM : (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z).
{ pose proof (lit_run_stop (sfx i) c1 s2 Hs1) as ST12. rewrite <- Ec1.
destruct ST12 as [E0|E37]; [left; exact E0 | right]. split; [exact E37|].
rewrite E37, Z.eqb_refl in PCT. cbn [andb] in PCT. destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (i + n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
split; [exact Hin1|]. rewrite <- Ec2. apply Z.eqb_neq. exact PCT. }
stmt HS_SCAN as NXS.
destruct (0 <? n) eqn:En; try rewrite En in FPC; [apply Z.ltb_lt in En; rename En into Npos | apply Z.ltb_ge in En; rename En into Nz].
-
destruct (Z.ltb_spec0 (2147483647 - (cnt + l)) n) as [|Hncl]; [apply implM_unr|].
ienter.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
jump (eapply NXS with (i := i) (n := n) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | exact LIT | exact TERM | left; exact Npos | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.

zs. br K1.
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
zs. zs. zs. zs.
ileave. eapply implM_bind.
{ eapply out_callq; try exact HS; try exact ST; try exact MI.
- rewrite Hlit, zb_firstn. unfold sfx. rewrite zb_skipn. replace (A + i)%Z with (A + Z.of_nat (Z.to_nat i))%Z by lia. apply bytes_at_sub; [exact BY | zl].
- rewrite Hlit. unfold sfx. apply Forall_sub. exact HF.
- unfold n, zlength. reflexivity.
- unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
- lia. - zl. - zl. - zl. - zl. - unfold INT_MAX in *; zl. }
cbv beta. intros [] st'. post_call rsegs m. rename MI0 into MI.
ienter. replace (ret_pc (Z_to_bv 64 218260)) with (Z_to_bv 64 218260) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
zs. zs. br K3.

rewrite <- Es1. rewrite <- Es1 in FPC.
stmt IH as NXH.
jumpM (eapply NXH with (i := (i + n)%Z) (cnt := (cnt + l)%Z) (l := n) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
-
assert (En0 : n = 0%Z) by lia. rewrite En0 in *.
assert (C37 : znth fmt i = 37%Z).
{ destruct TERM as [E0 | [E37 _]]; rewrite Z.add_0_r in *; [|exact E37]. exfalso. apply C0. rewrite Ec. exact E0. }
replace (i + 0 + 1)%Z with (i + 1)%Z in Es2 by lia.
destruct (parse_dir s2) as [[d s3]|] eqn:PD; [|apply implM_unr].
destruct args as [|a args']; [apply implM_unr|].
ienter.
zs. zs. zs. br K. zs. rd_fmt i. zs. fix_u8 i. zs. fixr. rewrite <- Ec. zs. br K0. rewrite Ec.
jump (eapply NXS with (i := i) (n := 0%Z) (cnt' := (cnt + l)%Z); [exact FI' | lia | lia | zl | intros j Hj; lia | rewrite !Z.add_0_r in TERM |- *; exact TERM | right; exact C37 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2.

zs. br K1.
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K2. clear FLC.
zs. zs. zs. zs.
ileave. eapply implM_bind.
{ eapply out_callq; try exact HS; try exact ST; try exact MI.
- apply bytes_at_nil; zl.
- constructor.
- reflexivity.
- unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
- lia. - zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; zl. - change (zlength (@nil Z)) with 0%Z; lia. }
cbv beta. intros [] st'. post_call rsegs m. rename MI0 into MI.
ienter. replace (ret_pc (Z_to_bv 64 218260)) with (Z_to_bv 64 218260) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
zs. zs. br K3.

stmt HS_DIR as NXD.
jump (eapply NXD with (i := i) (d := d) (rest := s3)); [mk_finv | unfold lo_cells, ssp_guard; exact LOW | lia | zl | rewrite <- Es2; exact PD | ].
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp. subst s3.

stmt (HS_CONV fuel IH) as NXC.
jumpM (eapply NXC with (i4 := k4) (k := k) (c := (cnt + l)%Z) (d := d) (a := a) (args := args'));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact PC0 | exact APC | lia | exact AOK
| | | exact FRM | exact FOK | lia | exact Ht | | lia | exact Hw | exact Hp | exact (parse_dir_xp _ _ _ PD) | unfold INT_MAX; lia ].
+ destruct a; try exact I. exact (Forall_inv FPC).
+ destruct a; try exact FPC. exact (Forall_inv_tail FPC).
+ exact (parse_dir_conv_type _ _ _ PD).
Qed.
End PrintfCore.
End F_printf_core_head.

Module F_printf_core_t4.
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
Local Notation S_T5 := (X1fq.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (X1fq.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_T5 : S_T5.

Lemma L_T4 : S_T4.
Proof using BS0 GLO HA HAP HOUT HS_T5 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. change (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z with true. cbn [negb orb].
ienter.
pose proof (c8_read4 _ _ [C8 (Z_to_bv 64 PFXA); C8 (Z_to_bv 64 (Z.land fl 73728))] (Z_to_bv 64 n) _ _ LOW eq_refl) as RD4. cbn [cells_size csize Nat.add] in RD4.
zs. rewrite (sx32_lit n) by lia. zs. brf K2.
-
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T5 fuel HH) as NX5.
jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (pq - n)) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (pq - n)%Z) in *.
zs. zs. zs. try rewrite (swrap32_small (pq - n)) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.
apply (rw_cells_split_CB rsegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. callx (eapply memset_callZ; [exact PADa | exact MI | (clear - LP LB LU LZB body prefix pl n pq w QHI GLO LO slots fmt lo q; lia) | (clear - LP LB LU LZB body prefix pl n pq w QHI GLO LO slots fmt lo q; lia) | lia | (clear - N256 K2 LB body prefix pl n pq w; lia)]).
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 48 256) in PADa by lia.
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
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.

match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells rsegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T5 fuel HH) as NX5.
jumpM (eapply NX5 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.
End F_printf_core_t4.

Module F_printf_core_prec.
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
Local Notation S_PLOOP := (X1fq.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (X1fq.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
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

Lemma L_PLOOP : S_PLOOP.
Proof using HF.
intros x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc p s3 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x13 x14 x15 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by zl. rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.
assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
zs. zs. br K.
zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. try rewrite Z.lor_0_l.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z. zs. zs. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. zs. zs. zs.
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
- assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k3 a1' a3' a4' Hk3 Hs3 Hnd Hp. apply HK; try assumption. zl.
Qed.

Lemma L_PREC : S_PLOOP -> S_PREC.
Proof using HF.
intros HPL x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k2 k3 p xp pfx s2s za pl plp alo ahi j128 _
FI LOW Hk2 PX HK.
pose proof FI as FI'. dest_finv FI.
rd_fmt k2. zs. fix_u8 k2. zs. zs.
destruct PX as [(N46 & Hp & Hxp & Hk3) | (E46 & Hxp & Hk21 & N42 & G & Hk3)].
- br K. subst p xp k3. do 6 zs. jump (apply HK; unfold INT_MAX; lia).
- br K. rd_fmt (k2 + 1)%Z. zs. fix_u8 (k2 + 1)%Z. zs. zs. br K1.
subst xp. zsto 0x356e4%Z.
pose proof (fmt_rng (k2 + 1) ltac:(zl)) as RG3.
zs. brf K3.
+
assert (ND : is_digit (znth fmt (k2 + 1)) = false).
{ destruct (is_digit (znth fmt (k2 + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG3)) in E. lia. }
rewrite (sfx_cons fmt (k2 + 1)) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ep Es. subst p.
assert (k3 = k2 + 1)%Z.
{ pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (k2 + 1)) in L2 by zl. rewrite Es in L2. lia. }
subst k3. zs. zs. zs. jump (apply HK; unfold INT_MAX; lia).
+ assert (D3 : is_digit (znth fmt (k2 + 1)) = true) by (apply (proj1 (digit_test _ RG3)); lia).
zs. zs.
stmt HPL as NXL. jump (eapply NXL with (pos := (k2 + 1)%Z) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact D3 | exact G | | ]).
{ intros E. pose proof (sfx_length fmt k3 ltac:(zl)) as L. rewrite E in L. change (zlength (@nil Z)) with 0%Z in L. zl. }
intros k3' a1' a3' a4' Hk3' Hs3 Hnd Hp.
assert (k3' = k3)%Z.
{ pose proof (sfx_length fmt k3 ltac:(zl)) as L1. pose proof (sfx_length fmt k3' ltac:(zl)) as L2. rewrite <- Hs3 in L2. lia. }
subst k3'. apply HK. lia.
Qed.
End PrintfCore.
End F_printf_core_prec.

Module F_printf_core_p1.
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
Local Notation S_SCAN := (X1fq.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (X1fq.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_EXIT1 := (X1fq.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (X1fq.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation sfx := (sfx fmt).
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

Hypothesis HS_SCAN : S_SCAN.
Hypothesis HS_DIR : S_DIR.
Hypothesis HS_EXIT1 : S_EXIT1.

Lemma L_P1 : S_P1.
Proof using HF HS_DIR HS_EXIT1 HS_SCAN.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 m pfx s2s za pl plp alo ahi j128 digs pad _
FI MU1 LOW DIG PAD P1.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
stmt HS_EXIT1 as NXE. stmt HS_SCAN as NXS. stmt HS_DIR as NXD.
unfold pass1_ok in P1. apply andb_true_iff in P1. destruct P1 as [LITB P1]. apply Z.leb_le in LITB. unfold INT_MAX in LITB.
pose proof (lit_run_sfx fmt 0 ltac:(lia)) as sfP_; first [ sf_destruct 4%nat sfP_ as Hn Hs1 LIT Hlit | sf_fb; destruct sfP_ as (Hn & Hs1 & LIT & Hlit) ]. change (sfx 0) with fmt in Hn, Hs1, LIT, Hlit.
cbv zeta in Hn, Hs1, LIT, Hlit. unfold zlength in *.
set (n := Z.of_nat (length (lit_run fmt))) in *.
rewrite Hs1 in P1. rewrite !Z.add_0_l in *.
destruct (sfx n) as [|c1 s2] eqn:Es1; [discriminate|].
destruct (sfx_cons_inv fmt n c1 s2 ltac:(lia) Es1) as (Hin & Ec1 & Es2). unfold zlength in Hin.
pose proof (lit_run_stop fmt c1 s2 Hs1) as C1.
assert (TERM : (znth fmt n = 0 \/ (znth fmt n = 37 /\ n + 1 < Z.of_nat (length fmt) /\ znth fmt (n + 1) <> 37))%Z
/\ (znth fmt n <> 0%Z -> exists d rest, parse_dir (sfx (n + 1)) = Some (d, rest))).
{ rewrite <- Ec1. destruct (Z.eqb_spec c1 0) as [E0|E0]; [split; [left; exact E0 | intros X; exfalso; exact (X E0)]|].
destruct s2 as [|c2 s2q]; [discriminate|].
destruct (sfx_cons_inv fmt (n + 1) c2 s2q ltac:(lia) (eq_sym Es2)) as (Hin1 & Ec2 & Es2q).
apply andb_true_iff in P1. destruct P1 as [P37 PD]. destruct (Z.eqb_spec c2 37) as [|N37]; [discriminate|].
split. { right. split; [lia|]. split; [unfold zlength in Hin1; exact Hin1|]. rewrite <- Ec2. exact N37. }
intros _. rewrite <- Es2. destruct (parse_dir (c2 :: s2q)) as [[d rest]|]; [|discriminate]. exists d, rest. reflexivity. }
destruct TERM as [TERM PDX].

zs. zs. zs. br K. zs. rd_fmt 0%Z. rewrite Z.add_0_r in RD. zs. fix_u8 0%Z. zs. fixr. zs. brf K0.
-
assert (n = 0)%Z as N0. { destruct (Z.eq_dec n 0); [assumption|]. exfalso. destruct (LIT 0%Z ltac:(lia)) as [X _]. apply X. exact K0. }
zs. if_lit. zs. zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
-
jump (eapply NXS with (i := 0%Z) (n := n) (cnt' := 0%Z);
[ exact FI' | lia | lia | zl | intros j Hj; rewrite Z.add_0_l; apply LIT; exact Hj | rewrite Z.add_0_l; exact TERM
| destruct (Z.lt_ge_cases 0 n); [left; assumption | right; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1 | exact C1]]
| unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1 a2. rewrite !Z.add_0_r.
zs. if_lit. zs. brf K1.
+
assert (N0 : n = 0%Z) by lia.
destruct C1 as [C1|C1]; [exfalso; apply K0; replace (znth fmt 0) with c1 by (rewrite Ec1; f_equal; lia); exact C1|].
destruct (PDX ltac:(rewrite <- Ec1, C1; lia)) as (d & rest & PD).
rewrite N0 in PD.
jump (eapply NXD with (i := 0%Z) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
+
zs. zs. zs. br K2. zs. rd_fmt n. zs. fix_u8 n. zs. fixr. zs. brf K3.
*
zs. if_lit. zs. zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
*
destruct C1 as [C1|C1]; [exfalso; apply K3; rewrite <- Ec1, C1; reflexivity|].
destruct (PDX K3) as (d & rest & PD).
jump (eapply NXS with (i := n) (n := 0%Z) (cnt' := n);
[ exact FI' | lia | lia | zl | intros j Hj; exfalso; lia | rewrite Z.add_0_r; exact TERM
| right; rewrite <- Ec1; exact C1 | unfold INT_MAX; lia | unfold INT_MAX; lia | ]).
intros a1' a2''. rewrite !Z.add_0_r.
zs. if_lit. zs. if_lit.
jump (eapply NXD with (i := n) (d := d) (rest := rest); [exact FI' | exact LOW' | lia | zl | exact PD | ]).
intros k4 a2' a3' a4' t1' Hk4 Hrest Ht Hfl Hw Hp.
zs. if_lit. zs. zs.
jump (eapply NXE; [exact FI' | exact MU1 | exact LOW' | exact DIG | exact PAD | lia]).
Qed.
End PrintfCore.
End F_printf_core_p1.

Module F_printf_core_width.
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
Local Notation S_WLOOP := (X1fq.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (X1fq.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
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

Lemma L_WLOOP : S_WLOOP.
Proof using HF.
intros x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q pos acc w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hpos Hacc DG G NE HK.
remember (Z.to_nat (zlength fmt - pos)) as kk eqn:Hkk.
revert pos acc x5 x6 x12 x14 x15 x16 x17 Hpos Hacc DG G HK Hkk.
induction kk as [|kk IH]; intros; [unfold zlength in *; exfalso; lia|].
pose proof FI as FI'. dest_finv FI. unfold lo_cells, ssp_guard in LOW.
pose proof (proj1 (digit_range _) DG) as DGR.
rewrite (sfx_cons fmt pos) in G by (unfold zlength in *; lia). rewrite (getint_cons_digit _ _ _ DG) in G.
destruct (214748364 <? acc) eqn:OV1; [discriminate|]. destruct (INT_MAX - 10 * acc <? znth fmt pos - 48) eqn:OV2; [discriminate|]. cbn [orb] in G.
apply Z.ltb_ge in OV1. apply Z.ltb_ge in OV2. unfold INT_MAX in OV2.

assert (Hnx : (pos + 1 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (pos + 1) (zlength fmt)) as [|Hge]; [assumption|]. exfalso.
rewrite sfx_nil in G by lia. cbn in G. injection G as _ <-. apply NE. reflexivity. }
zs. zs. br K.
zs. zs. try rewrite (swrap32_small (acc * 10)) by lia.
zs. rewrite Z.add_0_r, (swrap32_small (znth fmt pos + -48)) by lia.
rd_fmt (pos + 1)%Z. zs. fix_u8 (pos + 1)%Z.
zs. try rewrite (lxor_imax (acc * 10)) by lia.
zs. try rewrite (swrap32_small (acc * 10 + (znth fmt pos + -48))) by lia.
zs. try rewrite (proj2 (Z.ltb_ge (2147483647 - acc * 10) (znth fmt pos + -48))) by lia. cbn [Z.b2z].
zs. try change (bv_swrap 32 (0 - 0)) with 0%Z.
zs. zs. zs. try rewrite Z.lor_0_l. zs. zs. brf K2.
-
assert (ND : is_digit (znth fmt (pos + 1)) = false).
{ destruct (is_digit (znth fmt (pos + 1))) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG)) in E. lia. }
rewrite (sfx_cons fmt (pos + 1)) in G by (unfold zlength in *; lia). rewrite (getint_cons_nondigit _ _ _ ND) in G.
injection G as Ew Es2.
zs. br K3.
jump (apply (HK (pos + 1)%Z); [zl | | exact ND | unfold INT_MAX; zl]).
rewrite (sfx_cons fmt (pos + 1)) by zl. symmetry. exact Es2.
-
assert (D2 : is_digit (znth fmt (pos + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
jump (apply (IH (pos + 1)%Z (10 * acc + (znth fmt pos - 48))%Z); [zl | zl | exact D2 | exact G | | zl]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed.

Lemma L_WIDTH : S_WLOOP -> S_WIDTH.
Proof using HF.
intros HWL x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k1 w s2 pfx s2s za pl plp alo ahi j128 _
FI LOW Hk1 G NE HK.
pose proof FI as FI'. dest_finv FI.
pose proof (fmt_rng k1 ltac:(zl)) as RG1.
zs. zs. zs. zs. brf K.
-
assert (ND : is_digit (znth fmt k1) = false).
{ destruct (is_digit (znth fmt k1)) eqn:E; [|reflexivity]. exfalso. apply (proj2 (digit_test _ RG1)) in E. lia. }
rewrite (sfx_cons fmt k1) in G by zl. rewrite (getint_cons_nondigit _ _ _ ND) in G. injection G as Ew Es2.
subst w. jump (apply (HK k1); [zl | | exact ND | unfold INT_MAX; lia]).
rewrite (sfx_cons fmt k1) by zl. symmetry. exact Es2.
- assert (DG : is_digit (znth fmt k1) = true) by (apply (proj1 (digit_test _ RG1)); lia).
zs. zs.
stmt HWL as NXL. jump (eapply NXL with (pos := k1) (acc := 0%Z); [exact FI' | exact LOW | zl | lia | exact DG | exact G | exact NE | ]).
intros k2 t0' t1' a1' a3' a4' a5' a6' a7' Hk2 Hs2 Hnd Hw. apply HK; try assumption. zl.
Qed.
End PrintfCore.
End F_printf_core_width.

Module F_printf_core_t5.
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
Local Notation S_T6 := (X1fq.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (X1fq.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_T6 : S_T6.

Lemma L_T5 : S_T5.
Proof using BS0 GLO HA HAP HOUT HS_T6 HVA LO QHI SEP_B SEP_F SFL TOK TQ VAHI.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
ienter.
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
out_call.
1:{ exact BODY. }
1:{ exact BRNG. }
1:{ rewrite Hn. reflexivity. }
1:{ lia. } 1:{ lia. } 1:{ zl. } 1:{ zl. } 1:{ zl. } 1:{ zl. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
stmt (HS_T6 fuel HH) as NX6.
jumpM (eapply NX6 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.
End F_printf_core_t5.

Module F_printf_core_dloop.
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
Local Notation dloop_post := (X1fq.dloop_post q gp tp).
Local Notation S_DLOOP := (X1fq.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI.
intros x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x11 x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x11 x12 x13 x23 m j ds _ MI DIG Hx Hj ->.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (dec_digits_step x ltac:(lia)) as DS.
pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0.
pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R0.
assert (Q1 : (x / 10 < 1844674407370955162)%Z) by (apply Z.div_lt_upper_bound; lia).
assert (LD : (2 <= zlength (dec_digits x))%Z).
{ rewrite DS. unfold zlength. rewrite length_app. cbn [length].
destruct (Z.lt_ge_cases (x / 10) 10).
- rewrite dec_digits_small by lia. cbn. lia.
- rewrite (dec_digits_step (x / 10)) by lia. rewrite length_app. cbn [length]. lia. }
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
zs. zs. zs. zs. zs.
rewrite (land_W64_small (Z.shiftr (x * 14757395258967641293) 64)) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite div10_magic by lia. zs. zs. zs.
replace (bv_swrap 32 (x - x / 10 * 10)) with (x mod 10)%Z by (rewrite swrap32_small by lia; lia).
rewrite (land_W64_small (x mod 10)) by lia. rewrite lor48_digit by lia.
set (c := (48 + x mod 10)%Z) in *.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
pose proof (u8arr_store_ok rsegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write rsegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 10)) ltac:(lia) (x / 10)%Z eq_refl); [ exact MI | exact DIG1 | lia | | reflexivity ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. first [ sf_destruct 13%nat P as a2' a3' xq W' m' -> MU' WM' MI' DIG' Hxq HD HW | sf_fb; destruct P as (a2' & a3' & xq & W' & m' & -> & MU' & WM' & MI' & DIG' & Hxq & HD & HW) ].
unfold dloop_post. first [ unshelve sf_eexists 5%nat; [ exact (a2') | exact (a3') | exact (xq) | exact ((W' ++ [c])) | exact (m') | ] | sf_fb; exists a2', a3', xq, (W' ++ [c]), m' ].
assert (EL : zlength (W' ++ [c]) = (zlength W' + 1)%Z) by (unfold zlength; rewrite length_app; cbn [length]; lia).
rewrite EL.
split; [ mseq | ].
split; [ eapply munch_trans; [exact MU | exact MU'] | ].
split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
split; [ exact MI' | ].
split.
{ replace (firstn (Z.to_nat (j - (zlength W' + 1))) ds ++ zb (W' ++ [c]) ++ skipn (Z.to_nat j) ds)
with (firstn (Z.to_nat (j - 1 - zlength W')) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb W' ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
replace (Z.to_nat (j - 1 - zlength W')) with (Z.to_nat (j - (zlength W' + 1))) by lia.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
rewrite zb_app, <- !app_assoc. reflexivity. }
split; [ exact Hxq | ]. split; [ rewrite DS, HD; reflexivity | ]. unfold zlength in *. lia.
-
zs. apply evt_done.
unfold dloop_post. eexists (Z_to_bv 64 x), (Z_to_bv 64 c), (x / 10)%Z, [c], _.
split; [ mseq | ].
split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
split.
{ replace (firstn (Z.to_nat (j - zlength [c])) ds ++ zb [c] ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
rewrite upd_firstn_skipn by (rewrite LDS; lia). cbn [zb map app zlength length Z.of_nat Pos.of_succ_nat].
replace (Z.to_nat (j - 1)) with (Z.to_nat (j - 1)) by reflexivity.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
split; [ lia | ]. split; [ rewrite DS, dec_digits_small by lia; reflexivity | ]. zl.
Qed.
End PrintfCore.
End F_printf_core_dloop.

Module F_printf_core_exit1.
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
Local Notation POST1 := (X1fq.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (X1fq.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Lemma L_EXIT1 : S_EXIT1.
Proof using LO.
intros x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
m r pfx s2s za pl plp l10n alo ahi j128 digs pad _ FI MU1 LOW DIG PAD Hr.
dest_finv FI. unfold lo_cells, ssp_guard in LOW.
zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
do 14 zstep.
zstep. zstep.
release_frame LOW ST (q + -392)%Z.
release_frame DIG ST (q + -368)%Z.
release_frame PAD ST (q + -112)%Z.
release_frame FRhi ST q.
apply evt_done. unfold POST1.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU1|]. split; [exact WM|]. split; [exact MI|].
split; [exact ST|]. unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2].
Qed.
End PrintfCore.
End F_printf_core_exit1.

Module F_printf_core_intc.
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
Local Notation S_INTC2 := (X1fq.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (X1fq.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_INTC2 : S_INTC2.

Lemma L_INTC : S_INTC.
Proof using HS_INTC2.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp argi prefix body BA PFXA s2s za plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK BODY BRNG BEND BLEN HPFX PRNG PF0 PF1 PL2 Hi4 Hfl Hw Hc XP Hargi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_INTC2 fuel HH) as NX.
unfold conv_int.
ienter.
destruct XP as [[-> ->] | [-> Hp]]; cbn [Z.b2z].
-
replace (false && (-1 <? 0))%bool with false by reflexivity.
zs. zs. rewrite Z.land_0_l. zs. if_lit. zs. if_lit.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := (-1)%Z) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
-
replace (true && (p <? 0))%bool with false by (cbn; symmetry; apply Z.ltb_ge; lia).
zs. zs.
replace (Z.lxor p 9223372036854775808 <? 9223372036854775808)%Z with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; lia).
cbn [Z.b2z Z.land]. zs. if_lit. zs. if_lit. zs. zs.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB.
rewrite (nzmask_eq fl) in FLB |- * by lia.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := p) (argi := argi) (prefix := prefix) (body := body) (BA := BA) (PFXA := PFXA));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK | exact BODY | exact BRNG | zl | zl
| exact HPFX | exact PRNG | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia | lia ].
Qed.
End PrintfCore.
End F_printf_core_intc.

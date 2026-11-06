(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1db X1cg X1dh X1cs X1cn X1cq X1d0 X1cl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1ch X1d7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rv X1ry X1sa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1dz X1e4.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X01y X02b X02a X028 X052 X023 X02e X03c.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1ry.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X02g.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0hi X03z X058 X01z.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0sx X0ta X0t9 X0t7 X0w0 X0t2 X0td X0ub.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0tf.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X183 X0ux X0sy.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0td OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ub.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA.X1ry.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0tf.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X058.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sy.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg.
Import ListNotations.
Import X1cq.Exc.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 1011712)%Z.

Hypothesis SEP_F : ((1049936 <= Fp /\ Fp + 232 <= 1061376) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6655200 <= B /\ B + BS <= lo /\ B + BS <= 6664192) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Hypothesis RIP : rip_stmt.
Hypothesis HA0 : aext m0 lo q A fmt B BS.

Local Notation ctx_all := (X0tf.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (X0tf.W Fp B BS q lo AP).
Local Notation Fok := (X0tf.Fok F).
Local Notation Fok_refl := (X0tf.Fok_refl F).
Local Notation Fok_trans := (X0tf.Fok_trans F).
Local Notation POST := (X0tf.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (X0tf.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X0tf.lo_cells AP nla nlt).
Local Notation finv := (X0tf.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X0tf.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X0tf.implM_eq_ms (St:=St)).
Local Notation sink_store := (X0tf.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X0tf.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation arg_ok_W := (X0tf.arg_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
Local Notation args_ok_W := (X0tf.args_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
Local Notation lo_cells14 := (X0tf.lo_cells14 AP nla nlt).
Local Notation lo_split := (X0tf.lo_split q AP nla nlt).
Local Notation lo_join := (X0tf.lo_join q AP nla nlt).
Local Notation pop_arg_callq := (X0tf.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
Local Notation strnlen_callq := (X0tf.strnlen_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
Local Notation out_postq := (X0tf.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (X0tf.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0 HA0).
Local Notation memset_callq := (X0tf.memset_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
Local Notation memset_postq := (X0tf.memset_postq q gp tp lo).
Local Notation chkr_W := (X0tf.chkr_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
Local Notation ictx_W := (X0tf.ictx_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
Local Notation hsh := (X0tf.hsh B BS q m0 lo A fmt HA0).
Local Notation chkr_stack0 := (X0tf.chkr_stack0 B BS q m0 lo A fmt HA0).
Local Notation chkr_fmt0 := (X0tf.chkr_fmt0 B BS q m0 lo A fmt HA0).
Local Notation chkr_pfx0 := (X0tf.chkr_pfx0 B BS q m0 lo A fmt HA0).
Local Notation chkr_xdig0 := (X0tf.chkr_xdig0 B BS q m0 lo A fmt HA0).
Local Notation chkr_nulls0 := (X0tf.chkr_nulls0 B BS q m0 lo A fmt HA0).
Local Notation arg_ok_chk := (X0tf.arg_ok_chk Fp B BS).
Local Notation chkr_buf0 := (X0tf.chkr_buf0 B BS q m0 lo A fmt HA0).
Local Notation fp_postq := (X0tf.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation fp_callq := (X0tf.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
Local Notation S_EXIT := (X0tf.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (X0tf.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (X0tf.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (X0tf.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (X0tf.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (X0tf.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (X0tf.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (X0tf.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (X0tf.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (X0tf.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (X0tf.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (X0tf.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X0tf.body_loc Fp B BS q lo).
Local Notation S_TAIL := (X0tf.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (X0tf.tregs Fp q gp tp A).
Local Notation tinv := (X0tf.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (X0tf.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (X0tf.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (X0tf.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (X0tf.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (X0tf.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (X0tf.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (X0tf.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (X0tf.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation dloop_post := (X0tf.dloop_post q gp tp).
Local Notation S_DLOOP := (X0tf.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (X0tf.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (X0tf.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (X0tf.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (X0tf.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation xloop_post := (X0tf.xloop_post q gp tp).
Local Notation S_XLOOP := (X0tf.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (X0tf.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (X0tf.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation nullstr_arg_ok := (X0tf.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
Local Notation S_CV_S2 := (X0tf.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (X0tf.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (X0tf.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (X0tf.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (X0tf.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (X0tf.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation sfx := (sfx fmt).
Notation qq := (q + -544)%Z.
Notation SPv := (Z_to_bv 64 (q + -544)).
Notation FPv := (Z_to_bv 64 Fp).
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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
Ltac chk0_tac :=
first [ apply chkr_stack0; try unfold zrepeat; unfold zlength in *; rewrite ?repeat_length, ?Z2Nat.id by lia; lia
| apply chkr_fmt0; unfold zlength in *; lia
| apply chkr_pfx0; unfold PFX_A, zlength in *; lia
| apply chkr_xdig0; unfold XDIG_A, zlength in *; lia
| match goal with H : chkr m0 ?b ?n |- chkr m0 _ _ => apply (chkr_sub m0 b n _ _ H); unfold zlength in *; lia end ].
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : ro_cells _ _ 1035864 _ |- _ => exact H end
| match goal with H : ro_cells _ _ 6655192 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | |
| match goal with H : munch _ m0 _ |- _ => exact H end
| match goal with H : wmono _ m0 _ |- _ => exact H end
| chk0_tac ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call bsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := idtac.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp & BCHK);
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
subst xp. zsto 0xee478%Z.
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
End B_TWIN.

Import ListNotations.
Import X1cq.Exc.
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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 978944)%Z.

Hypothesis SEP_F : ((1014992 <= Fp /\ Fp + 232 <= 1024512) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((6620320 <= B /\ B + BS <= lo /\ B + BS <= 6627328) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Hypothesis RIP : rip_stmt.
Hypothesis HA0 : aext m0 lo q A fmt B BS.

Local Notation ctx_all := (X02g.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (X02g.W Fp B BS q lo AP).
Local Notation Fok := (X02g.Fok F).
Local Notation Fok_refl := (X02g.Fok_refl F).
Local Notation Fok_trans := (X02g.Fok_trans F).
Local Notation POST := (X02g.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (X02g.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X02g.lo_cells AP nla nlt).
Local Notation finv := (X02g.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X02g.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X02g.implM_eq_ms (St:=St)).
Local Notation sink_store := (X02g.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X02g.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation arg_ok_W := (X02g.arg_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
Local Notation args_ok_W := (X02g.args_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
Local Notation lo_cells14 := (X02g.lo_cells14 AP nla nlt).
Local Notation lo_split := (X02g.lo_split q AP nla nlt).
Local Notation lo_join := (X02g.lo_join q AP nla nlt).
Local Notation pop_arg_callq := (X02g.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
Local Notation strnlen_callq := (X02g.strnlen_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
Local Notation out_postq := (X02g.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (X02g.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0 HA0).
Local Notation memset_callq := (X02g.memset_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
Local Notation memset_postq := (X02g.memset_postq q gp tp lo).
Local Notation chkr_W := (X02g.chkr_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
Local Notation ictx_W := (X02g.ictx_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
Local Notation hsh := (X02g.hsh B BS q m0 lo A fmt HA0).
Local Notation chkr_stack0 := (X02g.chkr_stack0 B BS q m0 lo A fmt HA0).
Local Notation chkr_fmt0 := (X02g.chkr_fmt0 B BS q m0 lo A fmt HA0).
Local Notation chkr_pfx0 := (X02g.chkr_pfx0 B BS q m0 lo A fmt HA0).
Local Notation chkr_xdig0 := (X02g.chkr_xdig0 B BS q m0 lo A fmt HA0).
Local Notation chkr_nulls0 := (X02g.chkr_nulls0 B BS q m0 lo A fmt HA0).
Local Notation arg_ok_chk := (X02g.arg_ok_chk Fp B BS).
Local Notation chkr_buf0 := (X02g.chkr_buf0 B BS q m0 lo A fmt HA0).
Local Notation fp_postq := (X02g.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation fp_callq := (X02g.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
Local Notation S_EXIT := (X02g.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (X02g.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (X02g.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (X02g.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (X02g.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (X02g.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (X02g.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (X02g.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (X02g.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (X02g.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (X02g.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (X02g.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X02g.body_loc Fp B BS q lo).
Local Notation S_TAIL := (X02g.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (X02g.tregs Fp q gp tp A).
Local Notation tinv := (X02g.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (X02g.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (X02g.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (X02g.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (X02g.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (X02g.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (X02g.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (X02g.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (X02g.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation dloop_post := (X02g.dloop_post q gp tp).
Local Notation S_DLOOP := (X02g.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (X02g.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (X02g.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (X02g.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (X02g.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation xloop_post := (X02g.xloop_post q gp tp).
Local Notation S_XLOOP := (X02g.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (X02g.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (X02g.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation nullstr_arg_ok := (X02g.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
Local Notation S_CV_S2 := (X02g.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (X02g.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (X02g.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (X02g.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (X02g.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (X02g.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation sfx := (sfx fmt).
Notation qq := (q + -544)%Z.
Notation SPv := (Z_to_bv 64 (q + -544)).
Notation FPv := (Z_to_bv 64 Fp).
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
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
Ltac chk0_tac :=
first [ apply chkr_stack0; try unfold zrepeat; unfold zlength in *; rewrite ?repeat_length, ?Z2Nat.id by lia; lia
| apply chkr_fmt0; unfold zlength in *; lia
| apply chkr_pfx0; unfold PFX_A, zlength in *; lia
| apply chkr_xdig0; unfold XDIG_A, zlength in *; lia
| match goal with H : chkr m0 ?b ?n |- chkr m0 _ _ => apply (chkr_sub m0 b n _ _ H); unfold zlength in *; lia end ].
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : ro_cells _ _ 1000920 _ |- _ => exact H end
| match goal with H : ro_cells _ _ 6620312 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | |
| match goal with H : munch _ m0 _ |- _ => exact H end
| match goal with H : wmono _ m0 _ |- _ => exact H end
| chk0_tac ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call asegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := idtac.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq Z _ _ => zl | |- @eq nat _ _ => zl end | progress f_equal ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp & BCHK);
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
subst xp. zsto 0xe5c04%Z.
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

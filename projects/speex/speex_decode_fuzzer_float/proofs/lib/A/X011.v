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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X01y X02b X02a X028 X052 X023 X02e X01t.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1ry.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X00x.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0hi X03z X058 X01z.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0sx X0ta X0t9 X0t7 X0w0 X0t2 X0td X0ss.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0rw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X183 X0ux X0sy.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0td OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ss.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA.X1ry.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rw.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X058.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sy.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg.
Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Module DJ.
Import Ltac2.
Ltac2 prune_reld () : unit :=
let bad := SF2.bad_heads () in
let gv := SF2.vars_of [] (Control.goal ()) in
SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).

Module DJR.
Import Ltac2.
Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
Ltac2 unhide_rel () : unit :=
let gv := SF2.vars_of [] (Control.goal ()) in
let rm := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None =>
match is_hidden ty with
| Some p => if SF2.meets (SF2.vars_of [] p) gv
then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
else Some id
| None => None
end
end) (Control.hyps ()) in
match rm with [] => () | _ :: _ => Std.clear rm end.
Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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

Local Notation ctx_all := (X0rw.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (X0rw.W Fp B BS q lo AP).
Local Notation Fok := (X0rw.Fok F).
Local Notation Fok_refl := (X0rw.Fok_refl F).
Local Notation Fok_trans := (X0rw.Fok_trans F).
Local Notation POST := (X0rw.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (X0rw.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X0rw.lo_cells AP nla nlt).
Local Notation finv := (X0rw.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X0rw.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X0rw.implM_eq_ms (St:=St)).
Local Notation sink_store := (X0rw.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X0rw.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation arg_ok_W := (X0rw.arg_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
Local Notation args_ok_W := (X0rw.args_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
Local Notation lo_cells14 := (X0rw.lo_cells14 AP nla nlt).
Local Notation lo_split := (X0rw.lo_split q AP nla nlt).
Local Notation lo_join := (X0rw.lo_join q AP nla nlt).
Local Notation pop_arg_callq := (X0rw.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
Local Notation strnlen_callq := (X0rw.strnlen_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
Local Notation out_postq := (X0rw.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (X0rw.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0 HA0).
Local Notation memset_callq := (X0rw.memset_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
Local Notation memset_postq := (X0rw.memset_postq q gp tp lo).
Local Notation chkr_W := (X0rw.chkr_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
Local Notation ictx_W := (X0rw.ictx_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
Local Notation hsh := (X0rw.hsh B BS q m0 lo A fmt HA0).
Local Notation chkr_stack0 := (X0rw.chkr_stack0 B BS q m0 lo A fmt HA0).
Local Notation chkr_fmt0 := (X0rw.chkr_fmt0 B BS q m0 lo A fmt HA0).
Local Notation chkr_pfx0 := (X0rw.chkr_pfx0 B BS q m0 lo A fmt HA0).
Local Notation chkr_xdig0 := (X0rw.chkr_xdig0 B BS q m0 lo A fmt HA0).
Local Notation chkr_nulls0 := (X0rw.chkr_nulls0 B BS q m0 lo A fmt HA0).
Local Notation arg_ok_chk := (X0rw.arg_ok_chk Fp B BS).
Local Notation chkr_buf0 := (X0rw.chkr_buf0 B BS q m0 lo A fmt HA0).
Local Notation fp_postq := (X0rw.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation fp_callq := (X0rw.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
Local Notation S_EXIT := (X0rw.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (X0rw.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (X0rw.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (X0rw.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (X0rw.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (X0rw.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (X0rw.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (X0rw.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (X0rw.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (X0rw.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (X0rw.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (X0rw.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X0rw.body_loc Fp B BS q lo).
Local Notation S_TAIL := (X0rw.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (X0rw.tregs Fp q gp tp A).
Local Notation tinv := (X0rw.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (X0rw.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (X0rw.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (X0rw.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (X0rw.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (X0rw.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (X0rw.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (X0rw.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (X0rw.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation dloop_post := (X0rw.dloop_post q gp tp).
Local Notation S_DLOOP := (X0rw.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (X0rw.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (X0rw.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (X0rw.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (X0rw.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation xloop_post := (X0rw.xloop_post q gp tp).
Local Notation S_XLOOP := (X0rw.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (X0rw.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (X0rw.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation nullstr_arg_ok := (X0rw.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
Local Notation S_CV_S2 := (X0rw.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (X0rw.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (X0rw.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (X0rw.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (X0rw.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (X0rw.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_TAIL : S_TAIL.

Lemma L_CV_S2 : S_CV_S2.
Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI HA0 RIP.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SD1 SD2 SD3 E10 CHK0.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
assert (LSB : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = (Z.of_nat (length s) + 1 + Z.of_nat (length slack))%Z)
by (rewrite length_app, zb_length; cbn [length]; lia).
pose proof (zb_nonul s SRNG) as NONUL. pose proof (zb_length s) as LZS.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
assert (BRNG : forall n, Forall (fun c0 => 0 <= c0 < 256)%Z (firstn n s)).
{ intros n. rewrite <- (skipn_O s). apply Forall_sub. eapply Forall_impl; [|exact SRNG]. cbv beta. intros. lia. }
stmt (HS_TAIL fuel HH) as NX.
set (len := Z.of_nat (length s)) in *.
unfold ZERO_PAD.
ienter.
destruct XP as [[-> ->] | [-> Hp]].
-
cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implM_unr_l|].
rewrite ?ift, ?iff.
zs. zs. if_lit. zs. zs. zs.
callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z) (L := (zlength s + 1)%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia | match goal with H : munch _ m0 _ |- _ => exact H end | match goal with H : wmono _ m0 _ |- _ => exact H end | exact CHK0 | unfold zlength; lia | match goal with |- (strnlen_chk ?nn _ <= _)%Z => pose proof (strnlen_chk_cstr s slack nn SRNG ltac:(lia)); lia end ]).
rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
zs. zs. if_lit.
assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
{ rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
pose proof (u8ro_read bsegs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at bsegs mm P (zb s)) end.
{ pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := 69460%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; lia
| unfold body_loc; zl | zl | unfold INT_MAX; zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia
| apply (chkr_sub m0 P (zlength s + 1) _ _ CHK0); solve [lia | rewrite ?LF; lia | unfold zlength in *; rewrite ?length_firstn; lia] ].
match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
-
replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
zs. zs. brf K1; [ | zs ].

all: zs; zs.
all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (L := (zlength s + 1)%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia | match goal with H : munch _ m0 _ |- _ => exact H end | match goal with H : wmono _ m0 _ |- _ => exact H end | exact CHK0 | unfold zlength; lia | match goal with |- (strnlen_chk ?nn _ <= _)%Z => pose proof (strnlen_chk_cstr s slack nn SRNG ltac:(lia)); lia end ]).
all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
all: zs; zs; br K2; zs; zs; zs; zs; zs; zs; zs.
all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at bsegs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := 69460%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | apply BRNG
| unfold body_loc; rewrite LF; lia | rewrite LF; lia | rewrite LF; unfold INT_MAX; lia
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia
| apply (chkr_sub m0 P (zlength s + 1) _ _ CHK0); solve [lia | rewrite ?LF; lia | unfold zlength in *; rewrite ?length_firstn; lia] ].
all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
Qed.

Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI HA0 RIP.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp PV P s slack pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD PVP SD1 SD2 SD3 E10 CHK0.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
stmt (L_CV_S2 fuel HH) as NX.
ienter.
destruct PVP as [[-> P0] | [-> ->]].
-
zs. zs. br K0.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (fl10 := fl10) (xp := xp) (P := P) (s := s) (slack := slack));
[ exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | lia | exact SD1 | exact SD2 | exact SD3 | exact E10 | exact CHK0 ].
-
zs. zs. br K0.
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (fl10 := fl10) (xp := xp) (P := A_NULLSTR) (s := s) (slack := slack));
[ exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | unfold A_NULLSTR; lia | exact SD1 | exact SD2 | exact SD3 | exact E10 | exact CHK0 ].
Qed.
End PrintfCore.
End B_TWIN.

Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Module DJ.
Import Ltac2.
Ltac2 prune_reld () : unit :=
let bad := SF2.bad_heads () in
let gv := SF2.vars_of [] (Control.goal ()) in
SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).

Module DJR.
Import Ltac2.
Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
Ltac2 unhide_rel () : unit :=
let gv := SF2.vars_of [] (Control.goal ()) in
let rm := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None =>
match is_hidden ty with
| Some p => if SF2.meets (SF2.vars_of [] p) gv
then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
else Some id
| None => None
end
end) (Control.hyps ()) in
match rm with [] => () | _ :: _ => Std.clear rm end.
Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
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

Local Notation ctx_all := (X00x.ctx_all ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation W := (X00x.W Fp B BS q lo AP).
Local Notation Fok := (X00x.Fok F).
Local Notation Fok_refl := (X00x.Fok_refl F).
Local Notation Fok_trans := (X00x.Fok_trans F).
Local Notation POST := (X00x.POST (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 lo canary AP).
Local Notation hi_cells := (X00x.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X00x.lo_cells AP nla nlt).
Local Notation finv := (X00x.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X00x.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X00x.implM_eq_ms (St:=St)).
Local Notation sink_store := (X00x.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X00x.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation arg_ok_W := (X00x.arg_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
Local Notation args_ok_W := (X00x.args_ok_W Fp B BS q m0 lo A fmt AP VA slots LO SEP_F SEP_B HAP HA0).
Local Notation lo_cells14 := (X00x.lo_cells14 AP nla nlt).
Local Notation lo_split := (X00x.lo_split q AP nla nlt).
Local Notation lo_join := (X00x.lo_join q AP nla nlt).
Local Notation pop_arg_callq := (X00x.pop_arg_callq q gp tp lo fmt AP VA slots LO GLO QHI HAP HVA).
Local Notation strnlen_callq := (X00x.strnlen_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
Local Notation out_postq := (X00x.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (X00x.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp m0 lo canary A fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0 HA0).
Local Notation memset_callq := (X00x.memset_callq Fp B BS q gp tp m0 lo A fmt AP VA LO GLO QHI SEP_F SEP_B HAP RIP HA0).
Local Notation memset_postq := (X00x.memset_postq q gp tp lo).
Local Notation chkr_W := (X00x.chkr_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
Local Notation ictx_W := (X00x.ictx_W Fp B BS q m0 lo A fmt AP VA LO SEP_F SEP_B HAP HA0).
Local Notation hsh := (X00x.hsh B BS q m0 lo A fmt HA0).
Local Notation chkr_stack0 := (X00x.chkr_stack0 B BS q m0 lo A fmt HA0).
Local Notation chkr_fmt0 := (X00x.chkr_fmt0 B BS q m0 lo A fmt HA0).
Local Notation chkr_pfx0 := (X00x.chkr_pfx0 B BS q m0 lo A fmt HA0).
Local Notation chkr_xdig0 := (X00x.chkr_xdig0 B BS q m0 lo A fmt HA0).
Local Notation chkr_nulls0 := (X00x.chkr_nulls0 B BS q m0 lo A fmt HA0).
Local Notation arg_ok_chk := (X00x.arg_ok_chk Fp B BS).
Local Notation chkr_buf0 := (X00x.chkr_buf0 B BS q m0 lo A fmt HA0).
Local Notation fp_postq := (X00x.fp_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation fp_callq := (X00x.fp_callq (St:=St) Fp B BS SINK TOPOK OUTFP TOK q gp tp lo canary AP VA LO GLO QHI TQ SEP_F SEP_B HAP).
Local Notation S_EXIT := (X00x.S_EXIT (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_SCAN := (X00x.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FLAGS := (X00x.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WLOOP := (X00x.S_WLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (X00x.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PLOOP := (X00x.S_PLOOP Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (X00x.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (X00x.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (X00x.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_END := (X00x.S_END (St:=St) Fp B BS SINK ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_HEAD := (X00x.S_HEAD (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CONV := (X00x.S_CONV (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X00x.body_loc Fp B BS q lo).
Local Notation S_TAIL := (X00x.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (X00x.tregs Fp q gp tp A).
Local Notation tinv := (X00x.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (X00x.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T5 := (X00x.S_T5 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (X00x.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (X00x.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T2 := (X00x.S_T2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T1 := (X00x.S_T1 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC2 := (X00x.S_INTC2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_INTC := (X00x.S_INTC (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation dloop_post := (X00x.dloop_post q gp tp).
Local Notation S_DLOOP := (X00x.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU2 := (X00x.S_FMTU2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (X00x.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (X00x.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (X00x.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation xloop_post := (X00x.xloop_post q gp tp).
Local Notation S_XLOOP := (X00x.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_X := (X00x.S_CV_X (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (X00x.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation nullstr_arg_ok := (X00x.nullstr_arg_ok Fp B BS q lo AP VA LO GLO SEP_F SEP_B HAP).
Local Notation S_CV_S2 := (X00x.S_CV_S2 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_FP := (X00x.S_CV_FP (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation POST1 := (X00x.POST1 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary).
Local Notation S_EXIT1 := (X00x.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (X00x.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (X00x.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

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

Hypothesis HS_TAIL : S_TAIL.

Lemma L_CV_S2 : S_CV_S2.
Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI HA0 RIP.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp alo ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SD1 SD2 SD3 E10 CHK0.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
assert (LSB : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = (Z.of_nat (length s) + 1 + Z.of_nat (length slack))%Z)
by (rewrite length_app, zb_length; cbn [length]; lia).
pose proof (zb_nonul s SRNG) as NONUL. pose proof (zb_length s) as LZS.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
assert (BRNG : forall n, Forall (fun c0 => 0 <= c0 < 256)%Z (firstn n s)).
{ intros n. rewrite <- (skipn_O s). apply Forall_sub. eapply Forall_impl; [|exact SRNG]. cbv beta. intros. lia. }
stmt (HS_TAIL fuel HH) as NX.
set (len := Z.of_nat (length s)) in *.
unfold ZERO_PAD.
ienter.
destruct XP as [[-> ->] | [-> Hp]].
-
cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implM_unr_l|].
rewrite ?ift, ?iff.
zs. zs. if_lit. zs. zs. zs.
callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z) (L := (zlength s + 1)%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia | match goal with H : munch _ m0 _ |- _ => exact H end | match goal with H : wmono _ m0 _ |- _ => exact H end | exact CHK0 | unfold zlength; lia | match goal with |- (strnlen_chk ?nn _ <= _)%Z => pose proof (strnlen_chk_cstr s slack nn SRNG ltac:(lia)); lia end ]).
rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
zs. zs. if_lit.
assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
{ rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
pose proof (u8ro_read asegs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at asegs mm P (zb s)) end.
{ pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := 69436%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; lia
| unfold body_loc; zl | zl | unfold INT_MAX; zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia
| apply (chkr_sub m0 P (zlength s + 1) _ _ CHK0); solve [lia | rewrite ?LF; lia | unfold zlength in *; rewrite ?length_firstn; lia] ].
match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
-
replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
zs. zs. brf K1; [ | zs ].

all: zs; zs.
all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (L := (zlength s + 1)%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia | match goal with H : munch _ m0 _ |- _ => exact H end | match goal with H : wmono _ m0 _ |- _ => exact H end | exact CHK0 | unfold zlength; lia | match goal with |- (strnlen_chk ?nn _ <= _)%Z => pose proof (strnlen_chk_cstr s slack nn SRNG ltac:(lia)); lia end ]).
all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
all: zs; zs; br K2; zs; zs; zs; zs; zs; zs; zs.
all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at asegs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := 69436%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | apply BRNG
| unfold body_loc; rewrite LF; lia | rewrite LF; lia | rewrite LF; unfold INT_MAX; lia
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia
| apply (chkr_sub m0 P (zlength s + 1) _ _ CHK0); solve [lia | rewrite ?LF; lia | unfold zlength in *; rewrite ?length_firstn; lia] ].
all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
Qed.

Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI HA0 RIP.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp PV P s slack pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD PVP SD1 SD2 SD3 E10 CHK0.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
stmt (L_CV_S2 fuel HH) as NX.
ienter.
destruct PVP as [[-> P0] | [-> ->]].
-
zs. zs. br K0.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (fl10 := fl10) (xp := xp) (P := P) (s := s) (slack := slack));
[ exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | lia | exact SD1 | exact SD2 | exact SD3 | exact E10 | exact CHK0 ].
-
zs. zs. br K0.
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (fl10 := fl10) (xp := xp) (P := A_NULLSTR) (s := s) (slack := slack));
[ exact FI' | exact LOW' | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | exact STR | exact SRNG | exact SPAD | unfold A_NULLSTR; lia | exact SD1 | exact SD2 | exact SD3 | exact E10 | exact CHK0 ].
Qed.
End PrintfCore.

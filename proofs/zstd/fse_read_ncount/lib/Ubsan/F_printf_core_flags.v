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
Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
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
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
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
Lemma L_FLAGS : S_FLAGS.
Proof using HF.
intros x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q p k fl b w3 FL s1 _
FI Hp Hk Hpk Hw3 Hfl Hb PF NE HK.
remember (Z.to_nat (zlength fmt - (p + k))) as kk eqn:Hkk.
revert k fl b w3 x11 x12 x15 Hk Hpk Hw3 Hfl Hb PF HK Hkk.
induction kk as [|kk IH]; intros.
{ rewrite sfx_nil in PF by (unfold zlength in *; lia). cbn in PF. injection PF as _ <-. exfalso. apply NE. reflexivity. }
assert (Hlt : (p + k < zlength fmt)%Z) by (unfold zlength in *; lia).
pose proof FI as FI'. dest_finv FI.
zs. rd_fmt (p + k)%Z. zs. fix_u8 (p + k)%Z. zs. zs. rewrite Hw3. zs. brf K.
-
assert (NF : flag_bit (znth fmt (p + k)) = None).
{ destruct (flag_bit (znth fmt (p + k))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (p + k)) ltac:(congruence)) as R.
pose proof (proj2 (sp_test (znth fmt (p + k)) RG) R). lia. }
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
- assert (Hc : (32 <= znth fmt (p + k) < 64)%Z) by (apply (proj1 (sp_test _ RG)); exact K).
rewrite (land_M64_id (znth fmt (p + k) + -32)) in * by lia.
zs. zs. zs. zs. brf K2.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
destruct (flag_bit (znth fmt (p + k))) as [b'|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb'].
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
replace (A + p + k + 1)%Z with (A + p + (k + 1))%Z by lia.
rewrite Z.lor_comm.
eapply (IH (k + 1)%Z (Z.lor fl b) b'); try lia.
{ rewrite unsigned_lit_land. exact Hfw. }
{ apply lor_bound17; lia. }
{ replace (p + (k + 1))%Z with (p + k + 1)%Z by lia. exact PF. }
{ intros k' c' a3 a4 a5 Hk' Hs1 Hc' HN HFL. eapply HK; try eassumption; lia. }
all: unfold zlength in *; lia.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
assert (NF : flag_bit (znth fmt (p + k)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
Qed.
End PrintfCore.

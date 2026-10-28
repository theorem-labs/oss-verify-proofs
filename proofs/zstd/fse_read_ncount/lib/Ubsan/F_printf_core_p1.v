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
Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation S_EXIT1 := (F_printf_core_common.S_EXIT1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_P1 := (F_printf_core_common.S_P1 Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Notation sfx := (sfx fmt).
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
pose proof (lit_run_sfx fmt 0 ltac:(lia)) as (Hn & Hs1 & LIT & Hlit). change (sfx 0) with fmt in Hn, Hs1, LIT, Hlit.
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

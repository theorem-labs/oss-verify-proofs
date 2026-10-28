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
Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation S_SCAN := (F_printf_core_common.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Notation SPv := (Z_to_bv 64 (q + -544)).
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
Lemma L_LOOP1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n : Z) (Q : machine_state -> Prop) (k : nat) (j : Z),
finv m ->
k = Z.to_nat (n - j) -> (0 <= j)%Z -> (j < n \/ (j = n /\ znth fmt (i + n) = 37))%Z ->
(0 <= i)%Z -> (i + n < zlength fmt)%Z ->
(forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
(znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
(forall a0, evt usegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (if (znth fmt (i + n) =? 0)%Z then 0x17a04 else 0x17a0c)) fc None m (seg_rom usegs))) ->
evt usegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt (i + j))) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + j)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x179f4) fc None m (seg_rom usegs)).
Proof using HF.
intros until k. induction k as [|k IH]; intros j FI Hk Hj Hjn Hi Hin LIT TERM HK.
-
assert (j = n) by lia. subst j. destruct Hjn as [|[_ T37]]; [lia|].
dest_finv FI. unfold INT_MAX in *.
zs. rewrite T37. if_lit. specialize (HK (Z_to_bv 64 37)). rewrite T37, (proj2 (Z.eqb_neq 37 0)) in HK by lia. exact HK.
- destruct Hjn as [Hjn|[Hjn _]]; [|exfalso; lia].
pose proof (LIT j ltac:(lia)) as [NZ N37].
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
pose proof (fmt_rng (i + j) ltac:(unfold zlength in *; lia)) as RG0.
zs. br K.
rd_fmt (i + j + 1)%Z. zs. fix_u8 (i + j + 1)%Z. zs. zs.
destruct (Z.lt_ge_cases (j + 1) n) as [Hlt|Hge].
+
pose proof (LIT (j + 1)%Z ltac:(lia)) as [NZ1 _]. replace (i + j + 1)%Z with (i + (j + 1))%Z in * by lia.
br K1. replace (A + i + j + 1)%Z with (A + i + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z FI'); try lia; try assumption.
+ assert (j + 1 = n)%Z by lia. replace (i + j + 1)%Z with (i + n)%Z in * by lia.
replace (A + i + j + 1)%Z with (A + i + n)%Z by lia.
destruct TERM as [T0 | (T37 & Hn1 & T1)].
* rewrite T0. if_lit. specialize (HK (Z_to_bv 64 0)). rewrite T0, Z.eqb_refl in HK. exact HK.
* br K1. eapply (IH n FI'); try lia; try assumption.
Qed.
Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF.
intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i n cnt' Q _
FI Hi Hn Hin LIT TERM Hnz Hc Hnc HK.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
assert (NZ0 : znth fmt i <> 0%Z).
{ destruct Hnz as [Hp|H37]; [|rewrite H37; lia]. pose proof (LIT 0%Z ltac:(lia)) as [X _]. rewrite Z.add_0_r in X. exact X. }
pose proof (fmt_rng i ltac:(unfold zlength in *; lia)) as RGi.
zs. zs. br K.
eapply evt_eq; [ | eapply L_LOOP1 with (i := i) (n := n) (k := Z.to_nat (n - 0)) (j := 0%Z); try exact FI'; try lia; try assumption ].
{ cbv delta [mkR]. rewrite !Z.add_0_r. reflexivity. }
{ destruct Hnz as [Hp|H37]; [left; lia|]. destruct (Z.lt_ge_cases 0 n); [left; lia|]. right. split; [lia|]. replace (i + n)%Z with i by lia. exact H37. }
intros a0.
assert (TL : forall a1 a2, evt usegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x17a38) fc None m (seg_rom usegs))).
{ intros a1 a2. zs. replace (A + i + n - (A + i))%Z with n by lia. zs. fixr. zs. br K1. zs. fixr. apply HK. }
destruct TERM as [T0 | (T37 & Hn1 & T1)].
- rewrite T0, Z.eqb_refl. zs. zs. apply TL.
- rewrite T37. cbn [Z.eqb Pos.eqb]. zs. zs. rd_fmt (i + n + 1)%Z. zs. fix_u8 (i + n + 1)%Z. zs. br K1. zs. apply TL.
Qed.
End PrintfCore.

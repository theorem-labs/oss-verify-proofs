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
Local Notation finv := (F_printf_core_common.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation strnlen_callq := (F_printf_core_common.strnlen_callq q gp tp lo LO GLO QHI).
Local Notation body_loc := (F_printf_core_common.body_loc Fp B BS q lo).
Local Notation S_TAIL := (F_printf_core_common.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation S_CV_S := (F_printf_core_common.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
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
Hypothesis HS_TAIL : S_TAIL.
Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SD1 SD2 SD3 SD5 E10.
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
zs. zs. brf K0; [|exfalso; lia].
destruct XP as [[-> ->] | [-> Hp]].
-
cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implM_unr_l|].
rewrite ?ift, ?iff.
zs. zs. if_lit. zs. zs. zs.
callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia ]).
rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
zs. zs. if_lit.
assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
{ rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
pose proof (u8ro_read usegs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at usegs mm P (zb s)) end.
{ pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := 66256%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; lia
| unfold body_loc; zl | zl | unfold INT_MAX; zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
-
replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
zs. zs. brf K1; [ | zs ].
all: zs; zs.
all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; lia] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; lia | lia | lia ]).
all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
all: zs; zs; br K2; zs; zs; zs; zs; zs; zs; zs.
all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at usegs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := 66256%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | apply BRNG
| unfold body_loc; rewrite LF; lia | rewrite LF; lia | rewrite LF; unfold INT_MAX; lia
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | unfold INT_MAX; lia ].
all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
Qed.
End PrintfCore.

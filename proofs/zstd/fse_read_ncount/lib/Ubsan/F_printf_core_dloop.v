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
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Local Notation dloop_post := (F_printf_core_common.dloop_post q gp tp).
Local Notation S_DLOOP := (F_printf_core_common.S_DLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Ltac hush := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
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
Lemma L_DLOOP : S_DLOOP.
Proof using GLO LO QHI.
intros x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x11 x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x11 x12 x13 x23 m j ds _ MI DIG Hx Hj ->.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
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
pose proof (u8arr_store_ok usegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write usegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 10)) ltac:(lia) (x / 10)%Z eq_refl); [ exact MI | exact DIG1 | lia | | reflexivity ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. destruct P as (a2' & a3' & xq & W' & m' & -> & MU' & WM' & MI' & DIG' & Hxq & HD & HW).
unfold dloop_post. exists a2', a3', xq, (W' ++ [c]), m'.
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

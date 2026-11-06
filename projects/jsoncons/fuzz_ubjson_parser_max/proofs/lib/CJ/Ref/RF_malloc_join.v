(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp F_malloc_enf F_malloc_join.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_A RMalloc_fp RF_malloc_enf RAllocSlot_iface.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_malloc_join () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.Malloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMalloc_fp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1list"; "1option"; "2and"; "2or"; "3Z"; "0RUNp"; "4mem"; "5mrel"; "6cell"; "7alloc_ceiling"; "8rw_cells"; "9rsegs"; ":RCTX"; ":rmrep"]; [";rauxv_ok"; ";rpres_except"; "<rmalloc_fp"; "=mstate"; ">add"; ">le"; ">lt"; "0a"; "0cs"; "0lo"; "0m"; "0m'"; "0m0"; "0m2"; "0sp"; "0sp'"]; ["0sp1"; "0sp2"; "0st"; "0st2"; "0sta"; "0stb"; "?bv"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition renf_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
(t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
(forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
0 <= c_mmap_counter (ctx st2) < 2^32 ->
slot_ok st2 g b r idx n ->
(expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 (Some (g, idx))) s' Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9ba48) fc None m1 (seg_rom rsegs)).
Definition rfail_hyp {R} (K : mstate -> option (aptr * Z) -> Malloc.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st2 m1 -> ticks_ok st2 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 None) s' Q
(MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs)).
Section SE.
Local Abbreviation SEC_T_rmalloc_fp_cases := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_join "Q:'C'6'Q6yR0%211'3y8%511%311p051&?v7r7r3%43321&Br9r8r6%46832716'5'4&Er4%2271&F%123>%6231&;%11B%5271%;241p0=1p0C1p0D1pQ@Q21pQLK1pQJL1pQNQ51pQDQ61pR8Q81pR6Q91")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases) 0%nat 0%nat).
Variable st2 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases) 1%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases) 3%nat 0%nat).
Variable m0 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases) 4%nat 0%nat).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases) 5%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_cases) 6%nat 0%nat).
Lemma rmalloc_fp_cases : ltac:(sec_stmt2 constr:(SEC_T_rmalloc_fp_cases) 7%nat 0%nat).
Proof.
intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
pose_ceil.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold RCTX in H. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
- right. pose_ceil. lia.
Qed.
End SE.
Lemma rframe_after_call : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_join "QH'C'6'Q6yR0%211'3y8%511%311p051&8'2':%211&?v7r:r6%43321r4%63541&A&Br<r;r9%45;32:1r7%7321;&<&=r8r5%44321>&E%12;B&;%11F%421;%:49G8<p021p061p091p0?1p0H1p0K1pQBQ11p2Q>1pQLQ71pQHQ71pQFQ81pQJQ:1pR0QC1pQDQD1pR8QF1pR6QG1").
Proof. intros st st2 lo sp' m0 m m' m2 A cs.
intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.
Lemma rmalloc_fp_sp_mono : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_join "G'C'6&Er3r2%3221&Bv7r7r6r5r4%66543218r8%8671653;p031p0;1pQ@@1pR4A1pR2B1pQDC1pR8E1pR6F1").
Proof. intros st st2 lo sp1 sp2 a.
intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.
Lemma rmalloc_fp_st_mono : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_join "G'C'6'9r5r4%3221&Bv7r7r6r3r2%66543821r8%86715;:4p031p0;1pQ@@1pQNA1pQDB1pR<D1pR:E1pR6F1").
Proof. intros st sta stb lo sp a. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.
Section SE.
Local Abbreviation SEC_T_rmalloc_fp_image := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_join "QJ'C'6'Q6yR0%211'3y8%511%311p051&?v7r7r3%43321&Br9r8r6%46832716&E&;%11;%3216'4+elP0r5%7221&F+mTP0%2241%7241'5&>%>21@&D+m0%2241%:2D1%?251+hnmL%E21G+hnn0%?2I1%D231%=261p0?1p0H1p0M1p0Q31p0Q41pQ@QB1pQLQ;1pQJQ<1pQNQE1pQDQF1pR8QH1pR6QI1")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image) 0%nat 0%nat).
Variable st2 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image) 1%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image) 3%nat 0%nat).
Variable m0 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image) 4%nat 0%nat).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image) 5%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_rmalloc_fp_image) 6%nat 0%nat).
Lemma rmalloc_fp_image : ltac:(sec_stmt2 constr:(SEC_T_rmalloc_fp_image) 7%nat 0%nat).
Proof.
intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
pose_ceil.
assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
/\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
{ intros P. split; intros rid r Hr Ha.
- destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
- destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
-
exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.
End SE.
Lemma rauxv_ok_malloc_fp : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_join "QB'C'6'Q6yR0%211'3y8%511%311p051&8&?v7r9r5%43321&@r3%23641&A&Br<r;r:%45<321;r6%7321<&E&;%11A%3218%4296r8r7%B3F21p041p061p0;1p0D1p0H1p0I1p4Q81pQHQ01pQFQ11pQLQ31pQJQ41pQNQ=1pQDQ>1pR8Q@1pR6QA1").
Proof. intros st st2 lo sp m0 m2 m m' B.
intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
- intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
destruct AUX as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). pose_ceil. lia.
- intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.
End CEIL_WRAP_1.

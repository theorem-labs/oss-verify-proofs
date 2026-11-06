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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocBlocks.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_A RMalloc_fp RF_malloc_enf RAllocSlot_iface RF_malloc_entry RF_malloc_join RF_malloc_small.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_malloc_core () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocBlocks."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_malloc_core.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_malloc_join."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "3N"; "3Z"; "0F"; "0LB"; "4bvmap"; "0RUNp"; "5AREACH_from"]; ["5block"; "6MFACTS_g"; "7brk_link_ps"; "7mem"; "8C4"; "8cell"; "9mkR"; "9stk"; ":MS"; ";mem_inv"; "<alloc_ceiling"; "=rw_cells"; ">rsegs"; "?rcoreQ"; "@renf_hyp"; "@rfail_hyp"]; ["ARATP"; "Aref_reserved"; "Armalloc_entry"; "Armrep"; "Brauxv_ok"; "BrimplT"; "Captr"; "Cfull_lay"; "Cmalloc_core"; "Cmstate"; "Cret"; "Cs_tick"; "Cset_tick"; "DPState"; "Eseg_rom"; "Flt"]; ["Gadd"; "Gle"; "Glt"; "Gpow"; "Gsub"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0errv"; "0fc"; "0gp"]; ["0lo"; "0m"; "0m0"; "0n"; "0o"; "0r"; "0ra"; "0s"; "0s0"; "0s0v"; "0s1"; "0s10"; "0s11"; "0s1v"; "0s2"; "0s2v"]; ["0s3"; "0s3v"; "0s4"; "0s4v"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "0st1"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0t"]; ["0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Notation RAREACH := (AREACH_from ref_reserved).
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rcoreQ (o m0 : mem) (st : mstate) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
match res with
| (st2, Some (g, idx)) =>
exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9ba48) fc None m1 (seg_rom rsegs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a)
/\ 0 <= c_mmap_counter (ctx st2) < 2^32
/\ slot_ok st2 g b r idx n
/\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
| (st2, None) =>
exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp)
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
end.
Lemma renf_hyp_ret : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_core "R=&C'Q9'Q='RMyR0%211&=y5%2213yQ0%711':&Nv>'6'4&Q6%3216%311%52B1&Q:(5r2r1%34G621%5261qT<81qUHJ1rHrGrFrE&MrDrCrBrAr@r?r>r=r<r;r:r9r8r7r6r5r4r3%CHGFEDBA@?>=<;:987654321ML%Q8LQ7Q1IHGFE1CBA@?>=<;:98765432NMpT2Q:1pT8Q;1pSNQ=1pHQ@1pU8QD1pU4QE1pU0QF1pTLQG1pTDQH1pTJQI1pTHQJ1pUBQK1pU@QL1pU>QM1pU<QN1pU:QO1pV@R01pT0R11pUDR21pT>R31pT@R71pUFR91pT6R;1pT:R<1").
Proof. intros o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists b, r, m1, errv. do 17 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
Lemma rfail_hyp_ret : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_core "R=&C'Q9'Q='RMyR0%211&=y5%2213yQ0%711':&Ov>'6'4&Q6%3216%311%52B1&Q:(5r2r1%34G621%5261qT<81qUHJ1rHrGrFrE&MrDrCrBrAr@r?r>r=r<r;r:r9r8r7r6r5r4r3%CHGFEDBA@?>=<;:987654321ML%Q8KQ7Q1IHGFE1CBA@?>=<;:98765432MpT2Q:1pT8Q;1pSNQ=1pHQ@1pU8QD1pU4QE1pU0QF1pTLQG1pTDQH1pTJQI1pTHQJ1pUBQK1pU@QL1pU>QM1pU<QN1pU:QO1pV@R01pT0R11pUDR21pT>R31pT@R71pUFR91pT6R;1pT:R<1").
Proof. intros o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists m1, errv. do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
Definition rbig_stmt : Prop :=
forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
(m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
let st1 := set_tick t st in
RAREACH st LB -> RMFACTS st LB -> rmrep st m0 -> tp = Z_to_bv 64 RATP ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RAM_STACK -> MMAP_THRESHOLD <= n < 2^32 -> brk_link_ps st s ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_core full_lay st1 n) s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9b798) fc None m1 (seg_rom rsegs)).
Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.
Lemma rmalloc_core_implT : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_malloc_core "V@'RMyR0%211&=y5%2213yQ0%711&C'Q9'2&@%211'Q=':'9'?v>&Q1r7r6%544321'Ar8%23615&Q3r9r:%33;21&B%1237&Q4r<&RNrQ<%22Q21%53C41&G&Lr=rQ=%82Q81%5443C1&QA&J%11L%321D&QDrQ?%@2Q@1+XP0%4221%92I1&Kr@&Q@rQ>%H2QH1-U4%4221(1'E(D%11Q4(3%114%63531%>4M=81&IrA%22Q01'8rQ@&RL&Q0%22R:1%53R:41rQ;r?%62R>1%93R>31'7z%Q821M&QB&QC+2+Q0%3221%52Q31%9271&Q?&Q;rD%211r>%5221&Q5'6'4&Q6%321RG%311%52RN1rF&Q8&Q7&Q<rE%22O1rB%64RN521rC&MrQGrQFrQErQDrQ3rQ2rQ1rQ0rOrNrMrQ6rQ5rQ4rHrG%AHJJFB@?>=<;:9876QJRB54321DQM&H&FrQCrQBrQArQ:rQ9rQ8rQ7rLrKrJrI%<ONMLK;:9R8S0RHS8S>R38765CBAJIHGFED4321&Q2%R92TA1(0%11TB&Q>%11S@%D77G5F3Q?1%QG7T7QAQ@Q9Q8F1p0QI1p0R01p0R;1p0R@1p0RG1p0RK1p0S;1p0SB1p0SG1p0SN1p0T51p0T81p0T=1p0TA1pV0TH1pSLU61pT2TK1pT8TL1pT@TN1pJU01pUFU41pT4U61pSNU81pHU;1pV>U?1pV<U@1pV:UA1pV8UB1pTJUC1pTHUD1pUBUE1pU@UF1pU>UG1pU<UH1pU:UI1pU6UJ1pU2UK1pTNUL1pSJUM1pSHUN1pSFUO1pSDV01pSBV11pS@V21pS>V31pS<V41pTFV51pTBV61pV6V71pV4V81pV2V91pV@V:1pT0V;1pUDV<1pT>V=1").
Proof.
intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge 0) as ASG.
assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). pose_ceil. lia. }
pose proof MR as (WF0 & CX0 & GL0 & _). destruct GL0 as (_ & NL & _).
assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
{ intros m1 MU WM. pose_ceil.
split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; pose_ceil; lia]. }
split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
split. { eapply unk_agree_munch; [| exact MU| |].
- eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
- intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
- intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
-
riprefixT. eapply evt_cut.
{ eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| pose_ceil; lia| lia| exact MI]. }
intros ms' (a1' & m1 & -> & FR & ST1 & MU & WM & MI1).
destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
apply evt_done.
eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
+ unfold RAM_STACK. lia.
+ lia.
-
unfold malloc_core.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
riprefixT. eapply evt_cut.
{ eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| pose_ceil; lia| lia| exact MI| exact NL]. }
intros ms' (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1).
destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
apply evt_done.
eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
all: try eassumption.
+ apply renf_hyp_ret.
+ apply rfail_hyp_ret.
+ unfold RAS_STACK. lia.
+ reflexivity.
+ intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.
End CEIL_WRAP_1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import F_syscalls RMallocRep RF_get_meta.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc Monad.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_aligned () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_aligned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_aligned.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_aligned.CEIL_WRAP_3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1None"; "1Some"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "2and"; "2eq"; "2not"; "2or"; "3lt"; "4Z"; "0EE"]; ["0F"; "5machine_state"; "5write_to_mem"; "6bvmap"; "0P"; "0QQ"; "0R"; "0RUNp"; "7b8"; "7wz"; "8C1"; "8C2"; "8C4"; "8C8"; "8CB"; "8cell"]; ["9evt"; "9mstep"; ":mkR"; ":stk"; ";MS"; ";ret_pc"; "<bytes_at"; "<le1"; "<le4"; "<mem_inv"; "<wa"; "=at_node"; "=node"; ">alloc_ceiling"; "?rw_cells"; "@rsegs"]; ["BRAA_RET"; "BRAA_SYM"; "Braa_pre_post"; "Craa_fin_post"; "ARAA_RET"; "DRCTX"; "Eseg_rom"; "Fnth_error"; "Gadd"; "Gland"; "Gle"; "Glor"; "Glt"; "Gmin"; "Gmodulo"; "Gmul"]; ["Gof_nat"; "Gopp"; "Gpow"; "Gsub"; "0a"; "0a0"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0b"; "0b3"; "0bs"]; ["0fc"; "0gp"; "0i"; "0idx"; "0junk"; "0lo"; "0m"; "0ms"; "0ms'"; "0ms1"; "0n"; "0off16"; "0pc"; "0r"; "0ra"; "0rao"]; ["0res"; "0ro"; "0s0"; "0s0o"; "0s1"; "0s10"; "0s11"; "0s1o"; "0s2"; "0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"]; ["0sp"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0stride"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0w"; "0x"; "0z"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma write_to_mem_same : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "QI'5'SBy8%211%411yR0%511'8%115pWN31'>&QJzr1%3221&QHr2&R0&4r4%22A1%411%7261&R2+2+R0%3221%@251'6&=r6%=2L1%32C1':&Q:r5%C1D%F221%411%911&QGr7%23Q71J%:3Q341p0<1pU6A1p0Q8Q6&B%>1M%23>1C%A341?p061p0I1p0Q71pT:Q<1pU>Q>1pU0QD1").
Proof.
intros bs m a Ha Hl H. extensionality x.
rewrite write_to_mem_spec by lia.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
rewrite <- (H (Z.to_nat (bv_unsigned x - a))) by lia.
replace (a + Z.of_nat (Z.to_nat (bv_unsigned x - a))) with (bv_unsigned x) by lia.
unfold wa. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma bytes_at_overlay : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "QF'SByR0%211'8y8%511%311p051'>'5%115&Q6&Q?r3r2r1%544321'<&QJ&QH&R0&4%12A8%311%52;1+RPP0%8221+mXP0%:21?%<231'6&=r4%<2L1%32C1':r7&Q:r6%C1I%E221%411%611&QGr5%23Q81O%;3Q841p0=1pU6B1p0D1p0Q21pU0Q91pT:Q<1pU>Q>1").
Proof.
intros m a bs (A0 & Ahi & BA) OUT i Hi. rewrite <- (BA i Hi). symmetry. apply ref_mrd_overlay.
rewrite wa_unsigned by lia. lia.
Qed.
Lemma rw_cells_overlay1 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "Q>'SByR0%211'8y8%511%311p051'>&Q>&Q?r3r2(3'O(Jr1%211(7%115%73631%<4;:91'<&QJ&QH+1%22?1+RPP0%5221+mXP0%721C%9231':r5&Q:r4%211%411(2%12Q2L%83Q231p0:1p0E1pTLQ61pT:Q41pU>Q61").
Proof.
intros m a b [[_ BA] _] OUT. cbn [cells_bytes cbytes app] in BA.
pose proof (bytes_at_overlay m a [b] BA OUT 0%nat ltac:(cbn; lia)) as H. rewrite Z.add_0_r in H. exact H.
Qed.
Lemma rw_cells_overlay4 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "QJ'SByR0%211'8y8%511%311p051'>&Q>&Q?r3r2(3'O(Lr1%211(7%115%73631%<4;:91'<&QJ&QH+4%22?1+RPP0%5221+mXP0%721C%9231'6&=u4%22C1':r7&Q:r6&R0%11M%B231%511%711&QG&Q8r5%211%43Q<1Q5%>3Q<61p0@1pU6D1p0F1p0Q11pWLQE1pT:Q@1pU>QB1").
Proof.
intros m a w [[_ BA] _] OUT. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
intros i Hi. apply (bytes_at_overlay m a (le4 w) BA); rewrite ?length_le4; [exact OUT| exact Hi].
Qed.
Section AFTER.
Lemma evt_after_step : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "G'A!p021&Q0&Q?r3r2%43321&Q1%13543r5r4%211r6%113p031%=3<35p021p091p0<1pUDD1pU@E1pQ:D1").
Proof.
intros P ms ms1 (ms' & Hs & HP) ST HPP. inversion Hs; subst.
- apply evt_done. apply HPP. exact HP.
- pose proof (mstep_det rsegs _ _ _ ST H) as ->. exists ms'. split; assumption.
Qed.
Lemma impl_after_step : forall {R} (t : itree node R) Q ms ms1,
impl rsegs (at_node rsegs) t Q ms -> mstep rsegs ms ms1 ->
(forall r, Q r ms -> Q r ms1) -> (forall n, ~ at_node rsegs n ms) ->
impl rsegs (at_node rsegs) t Q ms1.
Proof.
intros R t Q ms ms1 H ST HQ HN. destruct t as [r|n k]; cbn [impl] in *.
- eapply evt_after_step; [exact H| exact ST| apply HQ].
- eapply evt_after_step; [exact H| exact ST|]. intros [Hat _]. exfalso. exact (HN n Hat).
Qed.
Lemma implM_after_step : forall {TS A : Type} (c : Monad.M TS A) (s : TS) Q ms ms1,
implM rsegs c s Q ms -> mstep rsegs ms ms1 ->
(forall a s', Q a s' ms -> Q a s' ms1) -> (forall n, ~ at_node rsegs n ms) ->
implM rsegs c s Q ms1.
Proof.
intros TS A c s Q ms ms1 H ST HQ HN. unfold implM in *. eapply impl_after_step; [exact H| exact ST| | exact HN].
intros [|[a s']]; cbn [epost]; [trivial| apply HQ].
Qed.
Lemma impl_post_evt : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
impl rsegs (at_node rsegs) t Q ms -> (forall r ms', Q r ms' -> evt rsegs (Q' r) ms') -> impl rsegs (at_node rsegs) t Q' ms.
Proof.
intros R t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn [impl] in *.
- eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk| exact HQ].
Qed.
Lemma implM_post_evt : forall {TS A : Type} (c : Monad.M TS A) (s : TS) (Q Q' : A -> TS -> machine_state -> Prop) ms,
implM rsegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt rsegs (Q' a s') ms') -> implM rsegs c s Q' ms.
Proof.
intros TS A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt; [exact H|].
intros [|[a s']] ms'; cbn [epost fst snd]; [intros _; apply evt_done; exact I| apply HQ].
Qed.
End AFTER.
Lemma at_node_svc_none : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "Q5'Q<&Cy5'SByR0%211%5241yQ0%511'8y8%811%311p081&;&Q;&Q?r7&Q4r6r5r4r3(1%11Cr2r1%978765321%=3<;1%?11pV4A1pU>B1pU2H1pUJL1pQ2L1pQ>M1pUFQ41").
Proof.
intros n R F pc fc m ro H. destruct n; cbn [at_node ms_svc_pending MS] in H;
repeat match type of H with _ /\ _ => destruct H as [H _] | _ \/ _ => destruct H as [H|H] end; discriminate H.
Qed.
Definition RAA_SYM : Z := 0x9bb0c.
Definition RMALLOC_IMPL : Z := 0x9c778.
Definition RAA_RET : Z := 0x9bbac.
Definition raa_pre_post (sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (n : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (junk : list byte) m',
ms' = MS (mkR (wz RAA_RET) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz 16) (wz n) (wz n) (wz n) (wz 16) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_IMPL) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra].
Section SE.
Local Abbreviation SEC_T_raa_pre_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "U1'SByR0%211&Cy5%2213yQ0%711'8y8%:11%311p0:1'>&Q3&Q?r3r2&SCrQ3%22C1%746541&QJ&Q=vG%211%421:r4&R3rQ5%<2M1+Q0%4221%;261&Q9r6%22E1&Q>r7&QH&QE+m0%3221(3'O(L&Iz%211%411(7%117%93831%:3941%A4Q7@<1':rQ0+@%<11%43QI31%>1F%63QK51'9r8%Q:2A1&R2+2%221Q4%Q>251%7251&Q0&QBrQ;rQ:rQ9rQ8rQ7rQ6rQ4rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@r?r>rQ<r9r=r<r;%OQ0NMLKJIR9HQ>GFEDCBA@?>=<;:987654321&Q4&Q2rQ2rQ1%3O:Q3Q2Q1Q0ONR>MRH21QCLKJIHGFEDCBA@?>=<;&SA&QA%22S=1(1%11S>&QF%11S3%<78@5?3>1%Q>3S5>1p0Q@1p0QI1p0QL1p0R21p0RE1p0RI1p0S11p0S71pUFS@1pU<SA1pU>SC1pU2SI1pQ2SL1pWHT01pWFT11pWDT21pWBT31pV>T41pV<T51pW0T61pVNT71pVLT81pVJT91pVHT:1pVFT;1pVDT<1pVBT=1pTJT>1pTHT?1pTFT@1pTDTA1pTBTB1pT@TC1pT>TD1pT<TE1pV:TF1pV6TG1pW@TH1pW>TI1pW<TJ1pWJTK1pU4TL1pW2TM1pUNTN1")) (only parsing).
Variable ra : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 1%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 2%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 3%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 4%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 5%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 6%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 7%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 8%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 9%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 10%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 11%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 12%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 13%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 14%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 15%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 16%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 17%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 18%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 19%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 20%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 21%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 22%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 23%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 24%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 25%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 26%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 27%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 28%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 29%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 30%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 31%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 32%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 33%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 34%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_raa_pre_walk) 35%nat 0%nat).
Lemma raa_pre_walk : ltac:(sec_stmt2 constr:(SEC_T_raa_pre_walk) 36%nat 0%nat).
Proof.
intros ST CLO LO MI REPL -> -> Hn. unfold RAA_SYM. pose_ceil. unfold RCTX in REPL. replace (954560 + 928) with 955488 in REPL by reflexivity.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 32%nat ST.
step. step. step. step.
step. step. step. if_false.
step. step. if_false.
step. step. if_cases K; zify_cond K.
{ exfalso. revert K. rewrite !wz_unsigned by lia. change (Z.lxor 16 18446744073709551615) with 18446744073709551599. lia. }
step. step. step. if_true.
step. step. if_false. step. step. step. step. step. step.
replace (16 + n + -16) with n by lia. unfold raa_pre_post. finish. exact FR.
Qed.
End SE.
Lemma raa_null_walk : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "T>'SByR0%211&Cy5%2213yQ0%711'8y8%:11%311p0:1'5%114'>&Q>&Q?r6&SCrQ3%22D1(3'O(Nu8r5%3221(Mr4%211r3%411r2%611(7%11=%?3>31%@3?61%A3@91%B3A=1%I4HGD1&Q0'A':r1&Q4&Q2&I&QHrQ5%Q02QB1+Q0%4221%611rQ4rQ2rQ1rQ0z%<11rOrNrMrLrKrJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;%Q3OQELKQNJIHQHR0FEDCBA@?>=<;:987654321r:&Q5%11QHr9(1%11RFr8&QF%11R:%Q>7:976431%QA3QBQ@1qUBQC1&Q@%Q@11+@%QB11%QC1R2%QEO4Q=R@Q<Q;Q:Q721Q8Q6Q5Q4Q3Q2Q1Q0ONMLKJIHGFEDCA&SA%12S57r7%QJ74B2?@1=%QO3RH;1p0R11pUFRL1pV0S:1pV8S;1pV@S<1pU:S11pU>S41pU2S:1pQ2S=1pWHSA1pWFSB1pWDSC1pWBSD1pV>SE1pV<SF1pW0SG1pVNSH1pVLSI1pVJSJ1pVHSK1pVFSL1pVDSM1pVBSN1pTJSO1pTHT01pTFT11pTDT21pTBT31pT@T41pT>T51pW@T61pW>T71pW<T81pWJT91pU4T:1pW2T;1").
Proof.
intros until n. intros FR. unfold RAA_RET at 2.
step. if_true. step. step. step. step. step. apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma lor_hdr : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "J'>'9&QJzr1%3221&QL+Q0%2241%8241r3%9281':&QK&QOr4%2219%4217&QH%52<4%22:1%93E41p0;1p0>1pU8H1pULI1").
Proof.
intros r idx Hi Hr.
assert (D : Z.land (r * 32) idx = 0).
{ apply Z.bits_inj'. intros i Hi0. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 5) as [L|L].
- change 32 with (2^5). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite andb_false_iff. right.
destruct (Z.eq_dec idx 0) as [->|NZ]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
rewrite <- Z.lxor_lor by exact D. pose proof (Z.add_nocarry_lxor _ _ D). lia.
Qed.
Lemma le1_wz : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "E'>':'5'SBy8%211%411&Q7&SAyR0r1%3221%511(3&H%115(7%11<%53=31%B3=71pX0D1").
Proof.
intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
Z.div_mod_to_equations. lia.
Qed.
End CEIL_WRAP_2.
Local Ltac mem_after_store_opt ::= idtac.
Ltac restore_mem E :=
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
replace (write_to_mem m a bs) with m;
[| symmetry; replace a with (wa E) by (unfold wa; f_equal; lia);
apply write_to_mem_same; [lia| cbn [length]; rewrite ?length_le4; lia|] ]
end.
Section CEIL_WRAP_3.
Context {RUNp : RunP}.
Definition raa_fin_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR rao (wz (bv_unsigned sp + 32)) gp tp t0 t1 t2 s0o s1o a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc rao) fc None m (seg_rom rsegs).
Section SE.
Local Abbreviation SEC_T_raa_fin_walk := (ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_aligned "Z;'SByR0%211&Cy5%2213yQ0%711'8y8%:11%311p0:1'5%114'>&Q>&Q?r?&SCrQ8%22D1(3'O(Nu8r>%3221(Mr=%211r<%411r;%611(7%11=%?3>31%@3?61%A3@91%B3A=1%I4HGD1&QJ&Q=vG%211rQ9%L2Q>1%6231&QHrQ:%Q02QB1+Q0%4221&R2+2+R0%3221%@251':rE%Q:2QL1%33Q?1O&QLz%221Q4&QN+@%22Q:1%:3QF15+4%F2Q:1%N2QF1rFrI%QH2R:1-4%L221(J&H%11@%311r:%411%611(K&Ir9%211%411%R43R31QF%R53R471%R63R5;1%R=4R<D@1'9%QE2OQN+X0%Q22R01%4231%QI2Q3A%Q52BQ@%7221&QI+O%22R;1%Q>3RJR81r@%R12Q;1rC&R3rD%QN21Q<&QOrA+1%R22RF1%4231%R4261%921Q@%QL3S8;1%R>2QHQLrGrH%R:221%R13S=>1%@2QDR1%R33S?B1rJ%RF2R01%R;2R:J%R32R61%Q52;1%RC2QJQN%RK21RH&QM+5%22?1%I2RE1%RI2L1%R@3SLR21%R=2R<B&;%RC3SOR47%211rQ5rL%SL3SKR1S>%T34T2321p051p091%S<2?R<rM-5%S8221(L%R51L%211%T73T61SI%T83T7R=1%T?4T>?61p0:1&Q:rO+3%QG221%411%F11(2%RI1RN%22TO1%S?3TO41rK%S=2S<1rQ7%R12<M%>11%311%:2U7S1%SG3U721p071%T:2Q=Q3rQ0%R921Q?%F11%U411%SN3U>18p061%TA2QDQ4'6&=r1u4%3221rQ;rQ3%RF21SM&R0r2%211%TF241%Q711%811&QG&Q8%SF1G%211%43V419%TD3V461p0@1pU6E1p0G1&Q0&QCrR2rR1rR0rQJrQIrQHrQGrQFrQErQDrQCrQBrQArQ<rQ6%@D?>=<;:98765432QG1RDQ3UBUF&Q4&Q2&QD%TB11rQOrQN&SA&R1%VJ2W<;%211%UN2U?1%52W?1%TK1U>rQ4%TM11rQMrQLrQ2%U111rQK%>2WHRG%V92R?T8%@2WJ1rQ@rQ?rQ>rQ=%JOHQ;Q:Q9GF@?=N<=;9875Q8Q7Q6Q5Q4Q3Q2Q1Q0O4321+c_VD%G2X11(1%11X2&QF%11WE%Q277R65VE3VI1%QE3WGQ41p0QG1p0R@1p0RH1p0S21p0S=1p0SI1p0T41p0T;1p0T>1p0TB1p0TE1p0TH1p0TM1p0TO1p0U<1p0U?1p0UD1p0UH1p0UN1p0VD1p0VH1p0VM1p0W11p0W61p0WA1p0WI1pU8XD1pUHXE1pTNXF1pV2XG1pW:XH1pQ<XI1pQ0XJ1p2XK1pQ:XL1pUFXM1pV0Y;1pV8Y<1pV@Y=1pU:Y21pU>Y51pU2Y;1pQ2Y>1pT<YB1pWHYC1pWFYD1pWDYE1pWBYF1pV>YG1pV<YH1pW0YI1pVNYJ1pVLYK1pVJYL1pVHYM1pVFYN1pVDYO1pVBZ01pTFZ11pTBZ21pT>Z31pW>Z41pW<Z51pWJZ61pU4Z71pW2Z81")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 4%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 5%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 6%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 7%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 8%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 9%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 10%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 11%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 12%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 13%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 14%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 15%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 16%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 17%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 18%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 19%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 20%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 21%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 22%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 23%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 24%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 25%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 26%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 27%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 28%nat 0%nat).
Variable rao : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 29%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 30%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 31%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 32%nat 0%nat).
Variable EE : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 33%nat 0%nat).
Variable QQ : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 34%nat 0%nat).
Variable stride : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 35%nat 0%nat).
Variable res : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 36%nat 0%nat).
Variable b3 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 37%nat 0%nat).
Variable off16 : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 38%nat 0%nat).
Variable idx : ltac:(sec_ty2 constr:(SEC_T_raa_fin_walk) 39%nat 0%nat).
Lemma raa_fin_walk : ltac:(sec_stmt2 constr:(SEC_T_raa_fin_walk) 40%nat 0%nat).
Proof.
intros FR CSP SPH HP P0 AL PEE HDR B3 IDX HIDX STR0 HEE HB0 HQQ HRES Hn RES EEH HB3 TZ T5 O3 OZ O5 O4.
pose_ceil.
assert (STR : 0 <= stride * (idx + 1) <= EE) by nia.
assert (ONE1 : forall (a : Z) (b : byte), m (wa a) = Some b -> forall i, (i < length [b])%nat -> m (wa (a + Z.of_nat i)) = nth_error [b] i).
{ intros a b Hb i Hi. destruct i; [rewrite Z.add_0_r; exact Hb| cbn in Hi; lia]. }
st1. st1. st1. st1. st1. st1.
replace (Z.land 15 (bv_unsigned (Z_to_bv 64 (0 + - bv_unsigned a0)))) with 0.
2:{ rewrite HP. rewrite unsigned_lit_wrap by lia. change 15 with (2^4 - 1). rewrite zb_land_mask_l by lia. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with 18446744073709551616. change (2^4) with 16. clear -AL P0. Z.div_mod_to_equations. lia. }
replace (B + 16 + stride * (idx + 1) + -4) with EE by lia.
replace (B + 16 + stride * (idx + 1)) with (EE + 4) by lia.
st1. if_cases K13; zify_cond K13. 2:{ exfalso. rewrite ?wz_unsigned in K13 by lia. lia. }
st1. st1. rewrite <- HP in HQQ. replace (n + bv_unsigned a0) with QQ by lia.
replace (bv_swrap 32 (EE - QQ)) with res. 2:{ rewrite <- HRES. symmetry. rewrite swrap32_eq'. rewrite Z.mod_small; lia. }
st1. if_cases K14; zify_cond K14.
-
rewrite ?wz_unsigned in K14 by lia.
st1. st1. st1. st1.
rewrite (Z.shiftl_mul_pow2 res 5) by lia. change (2^5) with 32. rewrite <- HIDX.
replace (bv_unsigned (Z_to_bv 64 (res * 32))) with (res * 32) by (symmetry; apply unsigned_lit; lia).
replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
replace (Z.lor (res * 32) idx) with b3 by (rewrite HB3, K14, Z.mul_0_l, Z.lor_0_l; lia).
st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
st1. st1. st1. st1. st1. st1.
unfold raa_fin_post. finish.
-
rewrite ?wz_unsigned in K14 by lia.
st1. replace (bv_swrap 32 (EE - QQ)) with res by (rewrite <- HRES; symmetry; rewrite swrap32_eq'; rewrite Z.mod_small; lia).
st1. st1. st1.
replace (bv_swrap 32 (0 - res)) with (- res) by (symmetry; rewrite swrap32_eq'; rewrite Z.mod_small; lia).
destruct (Z.eq_dec res 5) as [R5|R5].
+
specialize (T5 ltac:(lia)). clear TZ.
replace (EE + - res) with (EE + -5) by lia.
st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
st1. if_cases K15; zify_cond K15. { exfalso. rewrite signed_wz_small in K15 by lia. lia. }
st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
st1. restore_mem (EE - 4). 2:{ exact (O4 ltac:(lia)). }
st1.
st1. st1. st1. st1. rewrite <- HIDX.
replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
replace (Z.lor 160 idx) with b3 by (rewrite HB3, R5; change 160 with (5 * 32); rewrite lor_hdr by lia; lia).
st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
st1. st1. st1. st1. st1. st1.
unfold raa_fin_post. finish.
+ replace (EE + - res) with QQ by lia.
specialize (TZ ltac:(lia) R5).
destruct (Z_lt_le_dec res 5) as [R4|R6].
*
clear T5.
st1. rewrite le1_wz. restore_mem (EE - res). 2:{ exact (ONE1 _ _ (OZ ltac:(lia))). }
st1. if_cases K15; zify_cond K15. 2:{ exfalso. rewrite signed_wz_small in K15 by lia. lia. }
st1. st1. st1. st1. st1. rewrite <- HIDX.
rewrite (Z.shiftl_mul_pow2 res 5) by lia. change (2^5) with 32.
replace (bv_unsigned (Z_to_bv 64 (res * 32))) with (res * 32) by (symmetry; apply unsigned_lit; lia).
replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
replace (Z.lor (res * 32) idx) with b3 by (rewrite HB3; rewrite lor_hdr by lia; lia).
st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
st1. st1. st1. st1. st1. st1.
unfold raa_fin_post. finish.
*
specialize (T5 R6).
st1. rewrite le1_wz. restore_mem (EE - res). 2:{ exact (ONE1 _ _ (OZ ltac:(lia))). }
st1. if_cases K15; zify_cond K15. { exfalso. rewrite signed_wz_small in K15 by lia. lia. }
st1. rewrite le1_wz. restore_mem (EE - 5). 2:{ exact (ONE1 _ _ (O5 ltac:(lia))). }
st1. restore_mem (EE - 4). 2:{ exact (O4 ltac:(lia)). }
st1.
st1. st1. st1. st1. rewrite <- HIDX.
replace (bv_unsigned (Z_to_bv 64 idx)) with idx by (symmetry; apply unsigned_lit; lia).
replace (Z.lor 160 idx) with b3 by (rewrite HB3; replace (res `min` 5) with 5 by lia; change 160 with (5 * 32); rewrite lor_hdr by lia; lia).
st1. rewrite le1_wz. restore_mem (P - 3). 2:{ exact (ONE1 _ _ O3). }
st1. st1. st1. st1. st1. st1.
unfold raa_fin_post. finish.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_raa_tail_walk := (forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
(junk : list byte) (s1o s0o rao : word)
(n P G B AR EE QQ stride res : Z) (b3 off16 avail freed last_idx freeable sc maplen secret : Z) (prev next : word), let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
rw_cells rsegs m (bv_unsigned sp) [CB 8 junk; C8 s1o; C8 s0o; C8 rao] ->
alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 32 <= 2^64 ->
bv_unsigned a0 = P -> 0 < P -> P mod 16 = 0 -> 16 * off16 + 16 <= P ->
B = P - 16 * off16 - 16 -> AR = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
rw_cells rsegs m (bv_unsigned a0 + -4) [C1 (b8 0); C1 (b8 b3); C2 (wz off16)] ->
ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes rsegs m (wa AR) 8 = Some (le8 (wz secret)) ->
ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63 /\ last_idx = 0 /\ maplen <> 0) ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
stride = (if (last_idx =? 0) && negb (maplen =? 0) then maplen * 4096 - 16 else 16 * size_class sc) ->
EE = B + 16 + stride * (idx + 1) - 4 -> QQ = P + n -> res = EE - QQ ->
0 <= n -> 0 <= res < 2^31 -> EE + 4 <= alloc_ceiling -> P <= EE + 4 ->
b3 = idx + 32 * Z.min res 5 ->
(0 < res -> res <> 5 -> rw_cells rsegs m QQ [C1 (b8 0)]) ->
(5 <= res -> rw_cells rsegs m (EE + -5) [C1 (b8 0); C4 (wz res)]) ->
m (wa (P - 3)) = Some (b8 b3) ->
(0 < res -> m (wa (EE - res)) = Some (b8 0)) ->
(5 <= res -> m (wa (EE - 5)) = Some (b8 0)) ->
(5 <= res -> forall i, (i < 4)%nat -> m (wa (EE - 4 + Z.of_nat i)) = nth_error (le4 (wz res)) i) ->
evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
(MS (mkR (wz RAA_RET) sp gp tp t0 t1 t2 (wz 16) (wz n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RAA_RET) fc None m (seg_rom rsegs))) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 5%nat 0%nat).
Variable a0 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 6%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 7%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 8%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 9%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 10%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 11%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 12%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 13%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 27%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 28%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 29%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 30%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 31%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 32%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 33%nat 0%nat).
Variable rao : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 34%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 35%nat 0%nat).
Variable P : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 36%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 37%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 38%nat 0%nat).
Variable AR : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 39%nat 0%nat).
Variable EE : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 40%nat 0%nat).
Variable QQ : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 41%nat 0%nat).
Variable stride : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 42%nat 0%nat).
Variable res : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 43%nat 0%nat).
Variable b3 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 44%nat 0%nat).
Variable off16 : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 45%nat 0%nat).
Variable avail : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 46%nat 0%nat).
Variable freed : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 47%nat 0%nat).
Variable last_idx : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 48%nat 0%nat).
Variable freeable : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 49%nat 0%nat).
Variable sc : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 50%nat 0%nat).
Variable maplen : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 51%nat 0%nat).
Variable secret : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 52%nat 0%nat).
Variable prev : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 53%nat 0%nat).
Variable next : ltac:(sec_ty2 constr:(SEC_T_raa_tail_walk) 54%nat 0%nat).
Lemma raa_tail_walk : ltac:(sec_stmt2 constr:(SEC_T_raa_tail_walk) 55%nat 0%nat).
Proof.
intros idx mword FR CSP SPH HP P0 AL PLO HB HA GLO GHI HDR RG MM RA RC RS B3 O16 AV FRD SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63 Hml HST HEE HQQ HRES Hn RES EEH PEE HB3 TZ T5 O3 OZ O5 O4. unfold RAA_RET at 2.
pose proof CSP as CSP'. pose proof EEH as EEH'. pose_ceil.
assert (PHI : P + 16 <= 2^64) by nia.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
pose proof (size_class_range sc) as SZR.
assert (STR : 0 <= stride).
{ rewrite HST. destruct ((last_idx =? 0) && negb (maplen =? 0)) eqn:E.
- apply andb_prop in E as [_ E]. destruct (maplen =? 0) eqn:M0; [discriminate|]. apply Z.eqb_neq in M0. lia.
- destruct (Z_lt_le_dec sc 48); [specialize (SZR ltac:(lia)); lia|].
destruct (Hsc63 ltac:(lia)) as (-> & E1 & E2). rewrite E1 in E. cbn in E. destruct (maplen =? 0) eqn:M0; [|discriminate]. apply Z.eqb_eq in M0. lia. }
st1. if_cases K0; zify_cond K0. { exfalso. lia. }
st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
st1. st1. st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
st1.
assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
{ replace (P - off16 * 16 + -16) with B by lia. exact RG. }
st1. clear RG'.
set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
st1. st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
st1. st1. rewrite MW1. fold idx. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
st1. rewrite sx32_wz_sxv by lia. st1. st1.
rewrite sllw1_word' by lia.
assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
pose proof (sxv_range freed) as SXF.
st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. st1. unfold RCTX in RC. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
assert (MW3 : Z.shiftr mword 12 = maplen).
{ subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia. }
assert (MW4 : mword - mword mod 4096 = 4096 * maplen).
{ subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia. }
assert (FIN : forall (t0' t1' a1' a3' a5' t3' t4' t5' t6' : word) (m' : word -> option byte),
m' = m ->
evt rsegs (raa_fin_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 s1o s0o rao F fc m)
(MS (mkR (wz RAA_RET) sp gp tp t0' t1' (Z_to_bv 64 (0 + - bv_unsigned a0)) (wz 16) (wz n)
a0 a1' (wz n) a3' (wz B) a5' (Z_to_bv 64 stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 0x9bcd4) fc None m' (seg_rom rsegs))).
{ intros t0' t1' a1' a3' a5' t3' t4' t5' t6' m' ->.
eapply (raa_fin_walk sp gp tp t0' t1' a1' a3' a5' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' a0 F fc m junk s1o s0o rao
n P B EE QQ stride res b3 off16 idx); try eassumption; try lia; try reflexivity. }
st1. st1. st1. st1. rewrite MW2. st1. st1. st1. st1. if_cases K8; zify_cond K8.
-
destruct (Hsc63 ltac:(rewrite ?wz_unsigned in K8 by lia; lia)) as (Hsc63' & HLI0 & HML0).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned in K9 by lia. lia. }
st1. rewrite MW3. st1. st1. if_cases K10; zify_cond K10. { exfalso. rewrite ?wz_unsigned in K10 by lia. lia. }
st1. st1. st1. if_cases K11; zify_cond K11.
2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K11 by lia. change (2^8) with 256 in K11. change 18446744073709551615 with (Z.ones 64) in K11.
rewrite Z.land_ones, ?wz_unsigned in K11 by lia. rewrite Z.mod_small in K11 by lia. specialize (Hml HML0). lia. }
st1. if_cases K12; zify_cond K12. 2:{ exfalso. rewrite ?wz_unsigned in K12 by lia. lia. }
st1. st1. rewrite land_pgmask by lia. rewrite MW4. st1. st1.
assert (HSTR : stride = 4096 * maplen - 16). { rewrite HST, HLI0. cbn [Z.eqb andb]. destruct (Z.eqb_spec maplen 0); [lia| cbn; lia]. }
replace (4096 * maplen + -16) with stride by lia. apply FIN. reflexivity.
-
assert (SC48 : sc < 48) by (rewrite ?wz_unsigned in K8 by lia; lia).
specialize (RS SC48). specialize (Hsc SC48). specialize (SZR ltac:(lia)).
st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2.
assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (110048 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (110048 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
st1. try rewrite (Z.mod_small (size_class sc)) by lia. fold idx.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1.
st1. rewrite MW3. st1. st1. if_cases K12; zify_cond K12.
+
rewrite ?wz_unsigned in K12 by lia.
assert (HSTR : stride = 16 * size_class sc). { rewrite HST, K12. cbn [Z.eqb negb andb]. rewrite andb_false_r. reflexivity. }
st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. replace (size_class sc * 16) with stride by lia.
apply FIN. reflexivity.
+
rewrite ?wz_unsigned in K12 by lia.
st1. st1. st1. if_cases K13; zify_cond K13.
2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K13 by lia. change (2^8) with 256 in K13. change 18446744073709551615 with (Z.ones 64) in K13.
rewrite Z.land_ones, ?wz_unsigned in K13 by lia. rewrite Z.mod_small in K13 by lia. specialize (Hml K12). lia. }
st1. if_cases K14; zify_cond K14.
*
rewrite ?wz_unsigned in K14 by lia.
st1. st1. rewrite land_pgmask by lia. rewrite MW4. st1. st1.
assert (HSTR : stride = 4096 * maplen - 16). { rewrite HST, K14. cbn [Z.eqb andb]. destruct (Z.eqb_spec maplen 0); [lia| cbn; lia]. }
replace (4096 * maplen + -16) with stride by lia. apply FIN. reflexivity.
* rewrite ?wz_unsigned in K14 by lia.
assert (HSTR : stride = 16 * size_class sc). { rewrite HST. destruct (Z.eqb_spec last_idx 0); [lia|]. reflexivity. }
st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. st1.
rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. replace (size_class sc * 16) with stride by lia.
apply FIN. reflexivity.
Qed.
End SE.
End CEIL_WRAP_3.

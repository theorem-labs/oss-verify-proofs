(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_free_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Tgt_RF_free_B () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_free."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RF_free_B.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocKit_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Tgt.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1bool"; "1cons"; "1false"; "1list"; "1nil"; "1option"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3N"; "3Z"; "0F"; "4machine_state"]; ["5bvmap"; "0RUNp"; "6sxv"; "7meta_slot"; "7wz"; "8C8"; "8CB"; "8cell"; "9evt"; ":mkR"; ":stk"; ";MS"; "<mem_inv"; "=alloc_ceiling"; ">rw_cells"; "?aptr"]; ["?area"; "?bit"; "?conc"; "?get_meta_rec"; "?m_avail"; "?m_freed"; "?m_last_idx"; "?m_set_freed"; "?mask_upto"; "?meta"; "?mstate"; "?region"; "?s_areas"; "?s_regions"; "?upd_meta"; "@rsegs"]; ["Arftriv_post"; "Brfree_fp"; "Crmrep"; "Dseg_rom"; "Eadd"; "Ele"; "Elor"; "Elt"; "Epow"; "Esub"; "Etestbit"; "0a"; "0a0"; "0a5"; "0a6"; "0a7"]; ["0fc"; "0g"; "0gp"; "0idx"; "0junk"; "0lo"; "0m"; "0mr"; "0ms'"; "0q"; "0ra"; "0s0"; "0s1"; "0s10"; "0s11"; "0s2"]; ["0s3"; "0s4"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "0st'"; "0st0"; "FZ_to_bv"; "Fbv"; "Fbv_unsigned"; "GN_countable"; "GZ_countable"]; ["Gprod_countable"; "Hprod_eq_dec"; "Igmap"; "Jeq_dec"; "Keq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0x1"; "0x2"; "0x3"]; ["0x4"; "0x5"; "0x6"; "0x7"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma rfree_fp_meta0 : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_B "QJ'Q:'RLyR0%211'6y8%511%311p051'=&O&QBvAr7r5%43321&Cr8r3%3221'8'S2'<&S3&RN'Q;%544321&Q=%11;r9%311%;3531'7&QE&Q2r:%221Fr4%5221&QG&QD+Q8%2261%4261%<261&QA%14;MQ1Q0p031p0A1p0N1p0Q31pSHQ:1pTDQ:1pU@Q<1pT<Q=1pT>Q?1pUFQH1pUBQI1").
Proof.
intros st st0 m lo sp q a MR (ar & arr & k & Har & Hk & Eq) ER Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply rfree_fp_region; [rewrite ER; exact Hra | exact NK | lia].
Qed.
Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except C m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.
#[using="Type"] Lemma rfree_triv : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_B "Y;'RLyR0%211&@y5%2213yQ0%711'6y8%:11%311p0:1'4%114'='Q:&O'Q9&Q3r3r2%3221&Q>&Q7&QD&Q5r1%211&Q1%119%6231%811r4%;3>21&QBvAr5r9%43321&L&Q?r:%3221&Cr7r6%3221'8'S2'<&S3&RN'Q;%544321&Q=r8%211%31D%;3521&S1&S4%24<;Q?1&S0&RO%26?>=QB41'Q0%B4QB521&Q<%11O%21L%G3421'7&QEz%QA1N%3221&QG&QH+2+Q0%3221%5271%;271&Q4%11M%=2<1%:226%@221&Q6%11QD%B2A1%?22<%E221r;%F2E1%71QF%H231%J231'1&QJ%R;17r<%3221(3%QI3621%F14r=%8221%QM3:15&:%RE14%R03S11Q6%311&QFr>%RJ11%Q112%4221r?%RK11%S0231&Q8%Q218%211%R=3S>41%@11&NrF&RMrQC%22T21-Q@%S<221(2'G(Fu8rE%3221(ErQ6%211rQ7%411rQ<%611rQ=%811rQD%:11(5%11A%C3B31%D3C61%E3D91%F3E<1%G3F?1%H3GC1%Q04SFOJ1&JrG%Q12U1=%T:21O%44SK3J1&M%11T2%RN21Q7&QIrQF%Q92U91+Q@%4221%S42<1&H&Q@rQHrQGrQErQArQ@rQ;rQ:rQ9rQ8rQ5rQ4rQ3rQ2rLrKrH&QA%R02V0@%23Q131rJrB%FFEDLCBA@?>=QFQH<;:9876321&K&IrM&RK%UA29R6%22V:1rQBrD%52V=1rQ?&D&Q2%12RBR8%311+L%UL231%=2VE1&B%T:2T9;%211%:11rC%T311+1%V5221%TA2T@1%QH213%:11%B11+mSg<%K2W31rQ>rQ1rQ0rOrN%Q3OQ2OR1QHRES8NLKGD@865RGRIQEQDQCQBRKRMQAQ@Q?Q>4321+c_g@%Q32W;1(0%11W<&QC%11V7%Q;77QD5QC3Q>1%R43V9Q=1p0R61p0R=1p0RA1p0RG1p0SI1p0T71p0T<1p0TA1p0TI1p0TO1p0U51p0U;1p0UH1p0V51p0VB1p0VG1p0VL1tUDWDW21tT@WCW?1pT8WG1pT4WF1pUBWH1pUFWI1pT<WK1pT:WM1pT>X01pT2X61pNX91pVLX=1pVHX>1pVFX?1pVDX@1pVBXA1pTNXB1pTLXC1pU>XD1pU<XE1pU:XF1pU8XG1pU6XH1pU4XI1pU2XJ1pU0XK1pT0XL1pSNXM1pSLXN1pSJXO1pTJY01pTHY11pV@Y21pV>Y31pV<Y41pVJY51pT6Y61pU@Y71pTFY81").
Proof.
intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl rsegs m) as WM.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
(pose_ceil; unfold RNEED_LOCKS in *).
step. step. rewrite !sx32_wz_sxv by lia.
step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
step. if_true.
st1.
step. if_cases K2; zify_cond K2.
{ exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [exact K2 | rewrite wz_unsigned in K2 by assumption; exact K2]. }
clear K2.
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
{ exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
rewrite !wz_unsigned in K3 by apply sxv_range. exact K3. }
clear K3 RSUM.
step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
clear K4 RL.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep st' mX) end.
{ unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUg | exact WM |].
rewrite HG in MM.
eapply rw_cells_congr; [ | | | exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
- reflexivity.
- cbn. tauto. }
clear MUg MM.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
pose proof (wmono_refl rsegs mX) as WMs end.
step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply rfree_fp_stack. lia.
- intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [exact MR | exact MSL | symmetry; exact ER | lia]. }
finish.
Qed.
#[using="Type"] Lemma rfree_tocall : ltac2:(TCodec.tc2 tcn__CJ_Tgt_RF_free_B "WB'RLyR0%211&@y5%2213yQ0%711'6y8%:11%311p0:1'Q:&O'='Q9&Q3r3r2%3221&QBvAr4r5%43321&L&Q?r6%3221&C%1237'7&QEz&Q5%11=%4231&QG&QH+2+Q0%3221%5271%<271&Q4%11F%>2=1%:226%A221&Q6%11G%C2B1%?22<%F221r8%G2F1r7%811%J241%L241'8'1&QJ%M19r9%3221(3%73621%H14r:%8221%;3:15';%Q714%>3QL1Q9&QD&QF%Q118%2251&Q1r;%211%7241&Q8%Q31?%211%J3R841%?2=1&H'?'9&K&I&RK+c_k0%22RO1&RMrQC%22S21-Q@%I221%82S51rQBrQArQ@rQ?rQ>rC%?2S<1rQ;&Q2rErD%3221%E2SB1r1rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJ%Q6OQ3MLKJIHFE@FS7S;S<SAS@?>=<;:987654321rH+c`V8%Q82T51rG(0%11T7rF&QC%11SA%QA7:976431%RA3QDRE1qW8T=1%QE2T>1qW6T?1%QG2T@1qW4TA1%QI2TB1qW2TC1%QK2TD1qW0TE1%QM2TF1qVNTG1%QO2TH1qTBR11rBrQ<%QM2TM1%RC21QK%R22TO1rQ:rQ9rQ8r<%R72U41&Dr>r=%QJ221%411+L%S0231%R?2U<1&B%T82T7;%211%;11&QI%T11S2+1%S9221%T?2T>1%5213%:11%C11+mSg<%RM2UJ1rI%S0OQ1MR?LKJR8HR5C@<42R4R3R2R1R0QOQNQMQLQK1QIQFQCR=R<RArA+c_g@%S22UO1r@r?%S776532QJ1QG%S;3U9Q91p0S=1p0SN1p0T31p0T<1p0TC1p0TI1p0TO1p0U=1p0U@1p0UE1tT@UOUK1pT8V11pT4V31pUBV51pT>V71pT2V=1pNV@1pVLVD1pVHVE1pVFVF1pVDVG1pVBVH1pTNVI1pTLVJ1pU>VK1pU<VL1pU:VM1pU8VN1pU6VO1pU4W01pU2W11pU0W21pT0W31pSNW41pSLW51pSJW61pTJW71pTHW81pV@W91pV>W:1pV<W;1pVJW<1pT6W=1pU@W>1pTFW?1").
Proof.
intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
(pose_ceil; unfold RNEED_LOCKS in *).
step. step. rewrite !sx32_wz_sxv by lia.
step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).
step. if_true. st1.
step. if_cases K2; zify_cond K2.
-
st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
-
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
+ st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
+ exfalso. destruct HNT as [Hz|Hall].
* apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
* apply K3. rewrite ?wz_unsigned by apply sxv_range.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
unfold bit, mask_upto in Hall. exact Hall.
Qed.
End CEIL_WRAP_1.

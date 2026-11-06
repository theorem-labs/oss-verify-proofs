(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RF_am_A () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_am_A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocModel_B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RF_am_A.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1Some"; "1list"; "1option"; "2and"; "2eq"; "2iff"; "2not"; "3N"; "3Z"; "0F"; "4bvmap"; "0RUNp"; "5am_took"; "6clr_links"; "7lr_lo"]; ["7meta_slot"; "8evt"; "9mkR"; "9stk"; ":MS"; ";mem_inv"; "<alloc_ceiling"; "=rw_cells"; ">rsegs"; "?ram_fp"; "?ram_frame"; "?ram_ret_post"; "@RCTX"; "@RMLOCK"; "@RSSP_GUARD"; "@rmrep"]; ["@rregions_wf"; "Aralloc_fp"; "BRKGroup"; "Baptr"; "Barea"; "Bconc"; "Bmstate"; "Br_base"; "Br_kind"; "Br_len"; "Bregion"; "Brkind"; "Bround_up_pg"; "Bs_areas"; "Bs_regions"; "Bupd_meta"]; ["Cseg_rom"; "Dadd"; "Dle"; "Dlt"; "Dpow"; "Dsub"; "0a"; "0a1"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"; "0ak"; "0ar"]; ["0cnt"; "0fc"; "0gp"; "0junk"; "0k"; "0lo"; "0m"; "0q"; "0r"; "0raw"; "0rid"; "0s0"; "0s0o"; "0s1"; "0s10"; "0s11"]; ["0s1o"; "0s2o"; "0s3"; "0s3o"; "0s4"; "0s4o"; "0s5"; "0s6"; "0s7"; "0s8"; "0s9"; "0sp"; "0st"; "0st'"; "Elookup"; "FZ_to_bv"]; ["Fbv"; "Fbv_unsigned"; "GN_countable"; "GZ_countable"; "Gprod_countable"; "Hprod_eq_dec"; "Igmap"; "Igmap_lookup"; "Jeq_dec"; "Keq_dec"; "0t0"; "0t1"; "0t2"; "0t3"; "0t4"; "0t5"]; ["0t6"; "0tp"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition ram_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).
#[using="Type"] Lemma ram_fp_alloc_fp : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "G'Q6'9&Ir4r3r2r1%544321&Q1'Q;&7'5(Q2%23471%411qT:61r5%9521>=<p0;1pS>B1pUHC1pT<D1pUJF1").
Proof. intros st lo sp a. unfold ram_fp, ralloc_fp. tauto. Qed.
#[using="Type"] Lemma ram_fp_stack : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "D'Q6'9'4&QBr3r1%3221&QCr2%2241%8241&Ir5r4%3421:6p051pS>?1pUH@1pT<A1pUJC1").
Proof. intros st lo sp a. intros; left; assumption. Qed.
#[using="Type"] Lemma ram_fp_ctx : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "H'Q6'9'4&QB&Lr1%3221&QC&QA+m0%2261%4261%:261&Ir5r4r3r2%544321p071pS>C1pUHD1pT<E1pUJG1").
Proof. intros st lo sp a. intros; right; left; assumption. Qed.
#[using="Type"] Lemma ram_fp_region : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "QN'Q6'9'8'Q:'5'3%113&RN'S6&S8&S2%349218&S7%14;43:r2&Q>r6%211%;6@?7541(1r1%22B1%B3@41&7'Q;&Q8%11<(Q2%H3421%611'4&QB&?r3%211r5%5221&QC&QA&Q7%117&Q<&Q9%11:%311%7251%92;1%A2;1&Ir9r8r7%44321Q4p061p0I1p0Q11pTBQE1pTFQG1pS>QI1pUHQJ1pT<QK1pUJQM1").
Proof. intros st lo sp a rid r. intros; right; right. exists rid, r. auto. Qed.
Section SE.
Local Abbreviation SEC_T_ram_fp_not_errno := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "Q9'Q6'9&Ir4r3r2r1%544321&Q0v<r5%3221&QB&F%115%3215&7'4&QA&S1yR0&RO+hoS0%2231%5241-U4%8221%?21H&QC+4%<241%32L1%?251%A11p0C1p0H1p0M1pS>Q41pUHQ51pT<Q61pUJQ81")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ram_fp_not_errno) 0%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_ram_fp_not_errno) 1%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ram_fp_not_errno) 2%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_ram_fp_not_errno) 3%nat 0%nat).
Lemma ram_fp_not_errno : ltac:(sec_stmt2 constr:(SEC_T_ram_fp_not_errno) 4%nat 0%nat).
Proof using Type st lo sp a.
intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; (pose_ceil; unfold RCTX in *); rewrite ?unsigned_lit by lia; try lia.
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (_ & _ & D23 & D2).
pose proof (lr_lo_ge r). pose_ceil. lia.
Qed.
End SE.
#[using="Type"] Lemma ram_fp_meta : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "Q='Q6'S0yR0%211'3y8%511%311p051'9&Q3&Ov<r6r5%43321&@r7r3%3221'4&QB&Q5r8r4%3221%5218&QC&QA+Q8%2251%42=1%<261&Ir9%241BF;p041p0B1p0G1pS>N1pT@N1pUHQ01pT<Q11pT>Q31pUJQ<1").
Proof.
intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
#[using="Type"] Lemma ram_fp_area : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "R4'Q6'S0yR0%211'3y8%511%311p051'9&Q3'Q4&Ov<r7r6%43321'5%>17&RN'S6&S5'8&S8&S9%4432@1&S4&S2&S3%36762D51%:4D51C&S7%14F73Er4&Q=r8%211%B6KJ7541(1r3%22M1%H3G41'4&QB&Q5r9r5%3221%5219&QC&QA+TP0%2251%42>1%<261&Ir:%241FQ;Hp041p0B1p0Q<1pS>QD1pT0QC1pSNQE1pUHQG1pT<QH1pT>QJ1pUJR31").
Proof.
intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st ak ar ra WF Har Hra).
eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
#[using="Type"] Lemma ram_fp_same : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "M'Q6'9'5'S6'8&S8&S2'Q:%544321&Q>r4%211r5%411%<3631&6&Ir3r2%347921r6%541;43%7231p091pS>G1pUHH1pT<I1pULK1pUJL1").
Proof. intros st st' lo sp a. intros ER. unfold ram_fp. rewrite ER. tauto. Qed.
Definition ram_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except (ram_fp stF lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.
Definition ram_frame (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 junk; C8 (wz canary_val); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Section SE.
Local Abbreviation SEC_T_ram_tail := (ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "U;'S0yR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'2%114'9'Q6&Q3&Ov<r2r5%43321&E&Hr6%3221&@r4r3%3221&Gr8&QA&S1rQ=%22Q31-R0%5221&Jr7r;r<r=r>r?r@%877654321%A4H@:1&Cr9rQ>%B2QC1%D21@%54N4>1&QB&F%11Q6%321J&QErQ@%K2QL1+R0%4221%92>1&A&KrDrQArQ?rCrBrArQ0rOrNrMrLrKrJr:&Q?&>%23QC1Q1&RO&Q5%12Q4QF%32RF1%FGEDLCBA@Q:Q;?>=<;:9Q<Q=8Q6Q>51&D&BrE%QJ2RKH%QL21QH%:2RM1rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3&N%F2S91rQ2rQ1rIrHrGrF%GOFCQEQ<QNR>BA@J?>=<;:9765Q8Q7Q6Q5Q4Q3Q24321+c]f0%O2SB1(0%11SC&Q@%11RO%O77R<5R=3R>1%QH3S1Q11p0QJ1p0R11p0R61p0R=1p0S01p0S51p0S:1pT@S@1pUJSB1pT<SD1pT8SF1pT>SI1pT4SO1pFT21pU<T61pU8T71pU4T81pU2T91pTJT:1pTDT;1pW6T<1pW2T=1pW0T>1pVNT?1pVLT@1pU0TA1pTNTB1pUFTC1pUDTD1pUBTE1pU@TF1pU>TG1pU:TH1pU6TI1pSLTJ1pSJTK1pSHTL1pSFTM1pSDTN1pSBTO1pS@U01pTLU11pTHU21pVJU31pVHU41pVFU51pW4U61pT6U71pUHU81")) (only parsing).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 0%nat 0%nat).
Variable gp : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 1%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 2%nat 0%nat).
Variable t0 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 3%nat 0%nat).
Variable t1 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 4%nat 0%nat).
Variable t2 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 5%nat 0%nat).
Variable s0 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 6%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 7%nat 0%nat).
Variable a1 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 8%nat 0%nat).
Variable a2 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 9%nat 0%nat).
Variable a3 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 10%nat 0%nat).
Variable a4 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 11%nat 0%nat).
Variable a5 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 12%nat 0%nat).
Variable a6 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 13%nat 0%nat).
Variable a7 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 14%nat 0%nat).
Variable s3 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 15%nat 0%nat).
Variable s4 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 16%nat 0%nat).
Variable s5 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 17%nat 0%nat).
Variable s6 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 18%nat 0%nat).
Variable s7 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 19%nat 0%nat).
Variable s8 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 20%nat 0%nat).
Variable s9 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 21%nat 0%nat).
Variable s10 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 22%nat 0%nat).
Variable s11 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 23%nat 0%nat).
Variable t3 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 24%nat 0%nat).
Variable t4 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 25%nat 0%nat).
Variable t5 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 26%nat 0%nat).
Variable t6 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 27%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 28%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 29%nat 0%nat).
Variable s0o : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 30%nat 0%nat).
Variable s1o : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 31%nat 0%nat).
Variable s2o : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 32%nat 0%nat).
Variable s3o : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 33%nat 0%nat).
Variable s4o : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 34%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 35%nat 0%nat).
Variable fc : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 36%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 37%nat 0%nat).
Variable junk : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 38%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 39%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 40%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_ram_tail) 41%nat 0%nat).
Lemma ram_tail : ltac:(sec_stmt2 constr:(SEC_T_ram_tail) 42%nat 0%nat).
Proof using Type sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o F fc m junk lo st q.
intros MR MI MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
rmeta_chunk MR MSq CH.
(pose_ceil; unfold RSSP_GUARD, ram_frame in *).
rmeta_open (conc st q) MUq WMq.
st1. st1.
rmeta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
rewrite <- upd_meta_put in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl rsegs mX) as WMs end.
st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta q clr_links st) mX)
by (eapply rmrep_transport_high; [exact MR2 | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply ram_fp_stack. lia.
- intros x Hx. eapply ram_fp_meta; [exact MR | exact MSq | lia]. }
apply evt_done. unfold ram_ret_post. do 15 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR3.
Qed.
End SE.
#[using="Type"] Lemma ram_b0 : ltac2:(TCodec.tc2 tcn__CJ_Ref_RF_am_A "UD'S0yR0%211&;y5%2213yQ0%711'3y8%:11%311p0:1'2%114'9'Q6&Q3&Ov<r2r6%43321&E&Hr7%3221&@r4r3%3221'4&QBz%221=&QC&QD+2+R0%3221%52C1%:271&Gr:&QA&S1rQ=%22Q>1-R0%5221&Jr9r=r>r?r@rArB%877654321%A4Q3@:1&Cr;rQ>%B2QN1%D21@%54Q94>1&F%11Q@%Q421I&QErQ@%J2R61%321Q2%Q92<1&A&KrFrQArQ?rErDrCrQ2rQ1rQ0rOrNrMrLr<&=%13Q@Q8N&RO&Q5%12QCQ;%32RN1%EGDCJBA@?Q7Q8>=<;:98Q9Q:7QEQ;51&D&BrG%QG2S3G%QI21QE%:2S51rQ<rQ;rQ:%>2S9Q=rQ9rQ8rQ7rQ6rQ5rQ4&N%F2SA1&M%H2SC1rQ3rKrJrIrH%HOGDQDQ<QLR<CBAK@?>=<;:865Q8Q7Q6Q5Q4Q3Q24321+c]eD%Q02SK1(0%11SL&Q@%11S8%Q077R:5R;3R<1%QH3S:Q21p0QJ1p0R01p0R41p0R;1p0RN1p0S:1p0S?1p0SD1pT@SJ1pUJSL1pT2SN1pT<SO1pT8T11pT>T41pT4T:1pFT=1pU<TA1pU8TB1pU4TC1pU2TD1pTJTE1pTDTF1pW6TG1pW2TH1pW0TI1pVNTJ1pVLTK1pU0TL1pTNTM1pUFTN1pUDTO1pUBU01pU@U11pU>U21pU:U31pSLU41pSJU51pSHU61pSFU71pSDU81pSBU91pTLU:1pTHU;1pVJU<1pVHU=1pVFU>1pW4U?1pT6U@1pUHUA1").
Proof.
intros until q. intros MR MI MSq HC FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _). pose_ceil.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1.
(pose_ceil; unfold RCTX, RMLOCK in *).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 24, RCTX + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.
st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
rewrite (conc_aadd st q META_SIZE) by (destruct MSq as (a & ar & k & Ha & Hk & ->); cbn; pose proof MR as (WF' & _);
destruct (rarea_conc st a ar WF' Ha) as (ra & Hra & _); rewrite Hra; eauto).
unfold META_SIZE, wz. exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
change (conc st q) with (conc st1 q).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
[exact MR1 | assumption | exact MSq | exact FR | exact ST | pose_ceil; lia | lia]. }
intros ms' RP. unfold ram_ret_post in RP |- *.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
do 15 eexists. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st st1 lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. split; [|split; [|exact I]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End CEIL_WRAP_1.

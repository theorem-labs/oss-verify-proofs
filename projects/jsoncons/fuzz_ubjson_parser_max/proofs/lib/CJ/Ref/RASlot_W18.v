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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W18.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RASlot_W2 RASlot_W4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RASlot_W18 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W18."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_W18.CEIL_WRAP_2.FAILM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_W2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.decidable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1None"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "3N"; "3Z"; "0F"; "0G"; "4machine_state"; "4write_to_mem"; "5bvmap"; "0RUNp"; "6as_fm_st"]; ["7pw"; "8evt"; "9mkR"; "9munch"; "9wmono"; ":MS"; ";le8"; ";mem_inv"; ";wa"; "<alloc_ceiling"; "=rw_cells"; ">rsegs"; "?rfailW"; "@rta_frame"; "ARCTX"; "ARMLOCK"]; ["Armrep"; "Baptr"; "Barea"; "Bctx"; "Bget_meta_rec"; "Bget_shadow"; "Bghdr"; "Bmctx"; "Bmeta"; "Bmstate"; "Boptr"; "Bregion"; "Bs_areas"; "Bs_groups"; "Bs_regions"; "Bs_reserved"]; ["Bset_free_meta_head"; "Bshadow"; "Bupd_ctx"; "Cseg_rom"; "Dadd"; "Dle"; "Dsub"; "0a0"; "0a1"; "0a1'"; "0a2"; "0a3"; "0a4"; "0a5"; "0a6"; "0a7"]; ["0fc"; "0gp"; "0junk"; "0junk'"; "0m"; "0m'"; "0ms'"; "0mt"; "0q"; "0rav"; "0rid"; "0s0"; "0s0v"; "0s10"; "0s11"; "0s1v"]; ["0s2"; "0s2v"; "0s3"; "0s3v"; "0s4"; "0s4v"; "0s5"; "0s5v"; "0s6'"; "0s6v"; "0s7"; "0s7v"; "0s8"; "0s8v"; "0s9"; "0s9v"]; ["0sp"; "0st"; "0stX"; "0stY"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "FN_countable"; "FZ_countable"; "Fprod_countable"; "Gprod_eq_dec"; "Hgmap"; "Ieq_dec"; "Jeq_dec"; "0t0"; "0t1"]; ["0t2"; "0t3"; "0t4"; "0t5"; "0t6"; "0tp"; "0v"; "0x1"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
#[using="Type"] Lemma rmrep_set_free_head : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W18 "Q5'Q9'S5yR0%211'2y8%511%311p051&Q:&Q0v>r3r2%43321&QB&Q@%114r4%4221&<&H&QD&N+@%3221%511&F&@%12;@%311%;3C51%F3E=1p0C1pW>I1pT:K1pV4Q41").
Proof.
intros st m v MR. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le8 (pw st v)) as L8.
pose proof (munch_write [(RCTX + 16, RCTX + 24)] m m (RCTX + 16) (le8 (pw st v)) (munch_refl _ m)
ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
pose proof (wmono_write rsegs m m (wa (RCTX + 16)) (le8 (pw st v)) (wmono_refl rsegs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia.
- left.
pose proof (rw_cells_write rsegs m RCTX (ctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
cbn [cbytes cell_upd ctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
exact W.
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
- right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.
#[using="Type"] Lemma rmrep_extW : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W18 "RI'Q9'S5yR0%211'2y8%511%311p051&Q0v>r3r1%43321'5'S;'7&S<&S7'Q;%544321&Q>%11;r4%311%;3531'Q7&Q3%115r5%311%A3531&Q1'Q8&Q4r6%221Hr7%421J%I3631pTB81&S:'8&S=%34LK21&S9&S8%26ONM541'Q2%Q24A521&Q<%11@%21?%Q73421'Q6%Q84G;81&Q=%11Dr8%311%Q>3531'QA&Q5r9%221QDr:%421QF%QE3631pTFQD1'1'3%12MM%311&Q?%11;%21:%QN3421%R43R3<>p021p0;1p0D1p0L1p0Q:1p0QD1p0QK1p0R81pT:R>1pV8RG1pV6RH1").
Proof.
intros stX stY m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
- eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.
End CEIL_WRAP_1.
Ltac rraw_store_finishF A bs' FR MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
apply (wmono_write rsegs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv rsegs mX |- _ =>
apply (mem_inv_store rsegs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.
Definition rfailW (spv : Z) : list (Z * Z) :=
(spv - 144, spv) :: (G, G + 40) :: (RCTX + 16, RCTX + 24)
:: match c_free_meta_head (ctx st) with
| Some h => (conc st h, conc st h + 40)
:: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
| None => []
end.
#[using="MST FL"] Lemma rfailm1_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W18 "V9'S5yR0%211&=y5%2213yQ0%711'2y8%:11%311p0:1'1%114&Q0v>vS1r2%43321&G&Kr3%3221&Jr4&QD&S6rQ>%22L1-T@%5221&MrAr@r?r>r=r<r;r:r9r8r7%<=LF;:987654321%E4HD>1&QE&I%11Q0&QFrQ?%H2QB1+T@%4221%8261&A';'6'4'5r5&E&BrI&S4rQE%Q72R11%Q921Q5%42R31rQDrQCrQBrQArQ@v:%;2R:1-1%=2R<1rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJ%Q3OQ2MLKJIHQ?FDR8CBA@?>=<;:R;987654321+c`gD%Q32S21(0%11S3&QC%11RB%Q;77R35R23RF1%Q>3QAQ=1r1rHrGrFrErDrCrB%RB=S287654321RAR@R?R>%RK4RNS1Q@1&C&L%11QD%331R@S5&D%13S4RBS7%S62S5S8&?vR7%22S<1%S?3S>1S<%R5251%R6271%R72:1%R82?1%R92J1qT8SF1%R<2SG1qT<SJ1%R>2SK1qUBT61%R@2T71qSDT81%RB2T91qT>RD1%SB2T<R4%SD21S@%R?2T>1rQ=&O%RB2TA1%REOQ44S1SG3R5R4R3R8R2R1R0QOQNQMQLQKQJQIQHQG1QFQEQDQCRDQ8Q7Q6Q5+c_g<%RE2TD1r6%RJ74S=2S<QB1Q@%S13T3<1p0S31p0S=1p0T41p0T91pT6T?1pT:TB1pT2TH1pDTK1pTDTO1pTJU01pU0U11pU4U21pU8U31pU<U41pU@U51pUDU61pUHU71pULU81pV0U91pW@U:1pW:U;1pW8U<1pW6U=1pW4U>1pTNU?1pTLU@1pUNUA1pUJUB1pUFUC1pU>UD1pU:UE1pU6UF1pU2UG1pT0UH1pSNUI1pSLUJ1pSJUK1pSHUL1pSFUM1pSBUN1pS@UO1pTHV01pW2V11pW0V21pVNV31pW<V41pT4V51pV2V61").
Proof.
intros until junk. intros MR MI FR SPC.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). pose_ceil. fold G in Gpos, GC, GI, G4.
unfold rfailW. (pose_ceil; unfold RCTX, RMLOCK, rta_frame in *).
assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
evt rsegs (fun ms' => exists m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 950376) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9bf48) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 (wz canary_val); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (put_meta mt meta0 st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 950376) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9beec) fc None m (seg_rom rsegs))).
{ intros W HW1 HW2.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
rmchunk MR MST CH. fold G in CH.
lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
[ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
| clear CH ] end.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
st1. st1. st1. st1. st1.
lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
clear MUs.
rmeta_open G MUb WMb.
step. st1. step. st1. step. st1. step. st1. step. st1.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR0 : rmrep (put_meta mt meta0 st) mX);
[ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
| clear H MUb WMb ] end.
lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 (wz canary_val); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
[ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
| cbn [cells_size csize] in WR |- *; exact WR]
| clear H ] end.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
split; [assumption|]. split; [assumption| exact MR0]. }
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
-
destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _). pose_ceil.
pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _). pose_ceil.
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (950384 + 16, 950384 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
unfold pw. cbn [oconc]. unfold wz.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rewrite HP in CH. cbn [oconc] in CH.
step. clear CH.
rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
rmeta_open G MUb WMb.
st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
[ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
| clear MUb WMb H ] end.
set (st2 := put_meta mt _ st1) in MR2.
assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rmeta_open (conc st p) MUc WMc.
st1.
lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
[ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st2 mt) with G; reflexivity
| clear MUc WMc H ] end.
set (st3 := put_meta p _ st2) in MR3.
assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
change (conc st mt) with G in CH.
step. clear CH.
rmchunk MR3 MSh3 CH.
rmeta_open (conc st h) MUd WMd.
st1.
lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
[ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st3 mt) with G; reflexivity
| clear MUd WMd H ] end.
step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
eapply (rmrep_extW _ _ _ MR4); try reflexivity.
intros q. unfold st3, st2, st1, st0, upd_meta.
destruct (decide (q = h)) as [->|NQh].
{ rewrite !get_meta_rec_put_same. f_equal.
destruct (decide (h = p)) as [<-|NHp].
- rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
- rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
destruct (decide (q = p)) as [->|NQp].
{ rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
-
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (950384 + 16, 950384 + 24)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
unfold pw. cbn [oconc]. unfold wz.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1. st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
step.
pose proof MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (950376 + 24)) CX1 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
rraw_store_finishF (950384 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
step.
apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_single. cbn [set_head].
eapply (rmrep_extW _ _ _ MR2); try reflexivity.
intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
#[using="MST FL"] Lemma rfailm2_walk : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_W18 "V5'S5yR0%211&=y5%2213yQ0%711'2y8%:11%311p0:1'1%114&Q0v>vS1r2%43321&G&Kr3%3221&Jr4&QD&S6rQ>%22L1-T@%5221&MrAr@r?r>r=r<r;r:r9r8r7%<=LF;:987654321%E4HD>1&QE&I%11Q0&QFrQ?%H2QB1+T@%4221%8261&A';'6'4'5&E&BrH&S4rQD%Q62R01%Q821Q4%42R21rQCrQBrQArQ@v:%:2R81-1%<2R:1rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrI%Q3OQ2MLKJIQ>R4GEDCBA@?>=<;:R:987654321+c`gD%Q32S11(0%11S2&QC%11RA%Q;77R15R03RE1%Q=3Q@R?1r1rGrFrErDrCrB%R@=S07654321R?R>R=R<R;%RI4RLROQ?1&C&L%11QC%331R=S3&D%13S2R?S5%S42S3S6&?vR7%22S:1%S=3S<1S:%R3251%R4271%R52:1%R62?1%R72I1qT8SD1%R:2SE1qT<SH1%R<2SI1qUBT41%R>2T51qT>R@1%S>2T8R2%S@21S<%R<2T:1rQ=&O%R?2T=1%RBOQ24RMSC3R3R2R1R6R0QOQNQMQLQKQJQIQHQGQFQE1QDQCQBQAQ@RAQ5Q4Q3+c`c<%RB2T@1r6%RG74S92S8Q?1Q=%RM3SO<1p0RO1p0S91p0T01p0T51pT6T;1pT:T>1pT2TD1pDTG1pTDTK1pTJTL1pU0TM1pU4TN1pU8TO1pU<U01pU@U11pUDU21pUHU31pULU41pV0U51pW@U61pW:U71pW8U81pW6U91pW4U:1pTNU;1pTLU<1pUNU=1pUJU>1pUFU?1pU>U@1pU:UA1pU6UB1pU2UC1pT0UD1pSNUE1pSLUF1pSJUG1pSHUH1pSFUI1pSBUJ1pS@UK1pTHUL1pW2UM1pW0UN1pVNUO1pW<V01pT4V11pV2V21").
Proof.
intros until junk. intros MR MI FR SPC.
pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _). pose_ceil. fold G in Gpos, GC, GI, G4.
unfold rfailW. (pose_ceil; unfold RCTX, RMLOCK, rta_frame in *).
assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
evt rsegs (fun ms' => exists m' junk',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 950376) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c2c4) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 (wz canary_val); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ rmrep (put_meta mt meta0 st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 950376) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9c26c) fc None m (seg_rom rsegs))).
{ intros W HW1 HW2.
pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
rmchunk MR MST CH. fold G in CH.
lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
[ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
| clear CH ] end.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
st1. st1. st1. st1. st1.
lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRs : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
clear MUs.
rmeta_open G MUb WMb.
step. st1. step. st1. step. st1. step. st1. step. st1.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR0 : rmrep (put_meta mt meta0 st) mX);
[ eapply rmrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| cbn; tauto]
| clear H MUb WMb ] end.
lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 (wz canary_val); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
[ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; cbn; tauto| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
| cbn [cells_size csize] in WR |- *; exact WR]
| clear H ] end.
apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
split; [assumption|]. split; [assumption| exact MR0]. }
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
-
destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp). rewrite HP.
pose proof (rmeta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _). pose_ceil.
pose proof (rmeta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _). pose_ceil.
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (950384 + 16, 950384 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
unfold pw. cbn [oconc]. unfold wz.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
rmchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rewrite HP in CH. cbn [oconc] in CH.
step. clear CH.
rmchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
rmeta_open G MUb WMb.
st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
[ eapply rmrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
| clear MUb WMb H ] end.
set (st2 := put_meta mt _ st1) in MR2.
assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
rmchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
rmeta_open (conc st p) MUc WMc.
st1.
lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
[ eapply rmrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st2 mt) with G; reflexivity
| clear MUc WMc H ] end.
set (st3 := put_meta p _ st2) in MR3.
assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
rmchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
change (conc st mt) with G in CH.
step. clear CH.
step.
rmchunk MR3 MSh3 CH.
rmeta_open (conc st h) MUd WMd.
st1.
lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR4 : rmrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
[ eapply rmrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
change (conc st3 mt) with G; reflexivity
| clear MUd WMd H ] end.
step.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
eapply (rmrep_extW _ _ _ MR4); try reflexivity.
intros q. unfold st3, st2, st1, st0, upd_meta.
destruct (decide (q = h)) as [->|NQh].
{ rewrite !get_meta_rec_put_same. f_equal.
destruct (decide (h = p)) as [<-|NHp].
- rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
- rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
destruct (decide (q = p)) as [->|NQp].
{ rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
-
eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (950384 + 16, 950384 + 24)]%Z); cbn; tauto|]. cbv beta.
intros ms' (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0). clear PRE WM.
set (st0 := put_meta mt meta0 st) in *.
assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
unfold pw. cbn [oconc]. unfold wz.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
rmchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
change (conc st mt) with G in CH.
rmeta_open G MUa WMa.
st1. st1.
lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
[ eapply rmrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
| clear MUa WMa H ] end.
set (st1 := put_meta mt _ st0) in MR1.
step.
pose proof MR1 as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold RCTX in CX1.
pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (950376 + 24)) CX1 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold RCTX in MR2 end.
unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
rraw_store_finishF (950384 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
step.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
unfold as_fm_single. cbn [set_head].
eapply (rmrep_extW _ _ _ MR2); try reflexivity.
intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
destruct (decide (q = mt)) as [->|NQm].
{ rewrite !get_meta_rec_put_same. reflexivity. }
rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
End FAILM.
End CEIL_WRAP_2.

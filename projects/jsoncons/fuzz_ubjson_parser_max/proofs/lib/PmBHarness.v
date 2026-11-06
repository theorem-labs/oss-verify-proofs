(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface LibIfaceAJ
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsAB0
L5CoreAB0 L5StepARB0 L5CoreBRB0 L5ADetailHRB0 L5AFrameKRB0 HeapIfaceAJx LibIfaceAJ PmLayout PmLayoutA PmModel PmModelFacts PmModelFactsA PmStatics PmStaticsA
PmSpecsA PmSpecsAb PmSpecsBX PmStepAB0 PmTopAL StrictOfJ PmBHarnessStmts PmBHarnessKit PmBHarnessKit2 PmBHarnessSK
PmBHarness1 PmBHarness2 PmBHarness3 PmBHarness4 PmBHarness5 PmBHarness7 PmBHarness8 PmBHarness9 PmBHarness10 PmBHarness11.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBHarness () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LibIfaceAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepAB0.PMKB."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["1O"; "1app"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "3add"; "4le"; "5Forall"; "5map"]; ["6Z"; "0F"; "0FF"; "0HIR"; "0HV"; "0L"; "0LK"; "0LKc"; "0M"; "7ar_sptop"; "7ar_stack_top"; "7ff_addr"; "7ff_cap"; "7ff_class"; "7ff_count"; "7fframe"]; ["7hl_b_lin"; "7hl_b_overhead"; "7hl_k_per_malloc"; "7shadow_zero"; "8strict_of"; ":outside"; "9SCFG"; ";credit_le"; ";credit_sub"; "<lib_call_okA"; "=CREDIT"; "=FRAMES"; "=Lay"; "=STK"; "=WF"; ">AADDR_B"]; [">ADDR_B"; "?CHUNK"; "?cost1"; "?credit_add"; "?pot_parser"; "@credit_le"; "@ffroomA"; "@loc_W"; "@parser_init"; "@pst_reset"; "@scA"; "ATopLSA"; "Bwapp"; "Cloaded_segments"; "0SCFG_P"; "DIn"]; ["Dincl"; "Eadd"; "Ediv"; "Ele"; "Emax"; "Eof_nat"; "Epow"; "Esub"; "0a"; "0ar"; "0b"; "0cr"; "0cr4"; "0cr5"; "0cr6"; "0cr9"]; ["0f"; "0k"; "0l"; "0l'"; "0n"; "0qc"; "0rs"; "0sp"; "FNoDup"; "Gbv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHA.
Import L5A. Import L5CA. Import L5SAR. Import PMHAS.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Lemma ffc_app : ltac2:(TCodec.tc2 tcn__PmBHarness "E'@'3&O%211':'4&Nr3&1r2r1%33921%6251&<%8275%9285%3221%=3<51pU8?1pU6@1pU4D1").
Proof. intros k l l'. unfold ff_count. rewrite list_basics.list.filter_app. apply length_app. Qed.
Lemma ffc_zero : ltac2:(TCodec.tc2 tcn__PmBHarness "Q4'@'3&O%211'>&QO&Mr1%211(2+1+2+3(5%11>%63?31%73@51%83A71%=3B:1qU2A1%@3B1=&;r3%B3G16%311':'4&Nr4%2217(0%63521p081p0=1pU6O1pU4Q31").
Proof. intros k l.
intros HF Hk. induction HF as [|f l Hf HF IH]; [reflexivity|]. unfold ff_count in *. rewrite list_basics.list.filter_cons.
destruct (base.decide _) as [X|X]; [| exact IH]. exfalso. destruct (Z.eqb (ff_class f) k) eqn:E; [| exact X]. apply Z.eqb_eq in E. rewrite E in Hf. contradiction.
Qed.
Lemma ffc_incl : ltac2:(TCodec.tc2 tcn__PmBHarness "F'@'3&O%211'RHr2%2241&R0r3%23714'=&Nr5r4%3221%4237%6221p081p0<1pU8@1pU6A1pU4E1").
Proof. intros k l l'.
intros ND HI. unfold ff_count. apply list_relations.list.submseteq_length. apply list_relations.list.NoDup_submseteq. apply list_relations.list.NoDup_filter. exact ND.
intros x Hx. apply list_basics.list.list_elem_of_filter in Hx. apply list_basics.list.list_elem_of_filter. destruct Hx as [P Hx]. split. exact P.
apply base.list_elem_of_In. apply HI. apply base.list_elem_of_In. exact Hx.
Qed.
Lemma nodup_lk : ltac2:(TCodec.tc2 tcn__PmBHarness "A'3&O%211'RH'@&?&K&1r2r1%33921%64:751%9281%:2<5p021pQ>=1pQ6>1").
Proof. intros FF LK. intros ND. apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. apply NoDup_map_inv in ND. apply NoDup_app_remove_l in ND. exact ND. Qed.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section TOP.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HIR : asan_iface) (IL : icpt_layout).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HIR.
Hypothesis ICok : aicpt_ok L ar IL SCFG HIR.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Hypothesis STR : PMB.str_ctor_spec L ar HIR.
Hypothesis ISS : PMB.iss_ctor_spec L ar HIR.
Hypothesis RDC : PMB.reader_ctor_spec L ar HIR.
Hypothesis SYS : PMB.syscat_spec L ar HIR.
Hypothesis RRD : PMBX.reader_read_spec L ar HIR.
Hypothesis VDT : PMB.vec_dtor_spec L ar HIR.
Hypothesis OPD : PMB.opdel_spec L ar HIR.
Hypothesis SRCD : PMB.src_dtor_spec L ar HIR.
Hypothesis LCD : PMB.locale_dtor_spec L ar HIR.
Hypothesis IOD : PMB.ios_dtor_spec L ar HIR.
Lemma wapp_WF : ltac2:(TCodec.tc2 tcn__PmBHarness "3&QL&Q>%211").
Proof. intros r Hr. unfold WF, PMTAL.foot_b, PMTAL.ATEXIT_b in Hr. cbn in Hr. unfold BIGSHADOW_LO, BIGSHADOW_HI. repeat (destruct Hr as [<-|Hr]; [cbn; lia|]). destruct Hr. Qed.
Lemma wloc_WF : ltac2:(TCodec.tc2 tcn__PmBHarness "<'@&Q5&Q>r1%3221&QG&Q@%211r2%8221p061pTB;1").
Proof.
intros a Ho r Hr. apply Ho. unfold PMSPA.loc_W in Hr. cbn in Hr. unfold WF, PMTAL.foot_b, PMTAL.ATEXIT_b. cbn.
destruct Hr as [<-|[<-|[]]]; [right; right; left; reflexivity| right; right; right; left; reflexivity].
Qed.
Lemma wsys_WF : ltac2:(TCodec.tc2 tcn__PmBHarness "C'@&Q5&Q>r1%3221(2'8%1277(7+V]lg@+2%34;;21(5%116%93731r2%?221p0=1pTBB1").
Proof. intros a Ho r [<-|[]]. apply Ho. unfold WF, PMTAL.foot_b, PMTAL.ATEXIT_b. cbn. right; left; reflexivity. Qed.
Lemma werr_WF : ltac2:(TCodec.tc2 tcn__PmBHarness "G'@&Q5&Q>r1%3221(2'8%1277(7+V]lV0+2%34;;21+VbRh@+a0%64>>21(5%119%<3:31%=3;71r2%C221p0A1pTBF1").
Proof.
intros a Ho r Hr. apply Ho. unfold WF, PMTAL.foot_b, PMTAL.ATEXIT_b. cbn.
destruct Hr as [<-|[<-|[]]]; [left; reflexivity| right; right; right; right; left; reflexivity].
Qed.
Lemma room_of : ltac2:(TCodec.tc2 tcn__PmBHarness "R8'3&O%211'@&QOr1(2z+1+2+3+4(5%11:%83;31%93<51%:3=71%;3>91%<3?;1%?3@>1&R3&R1&R5&Nr2&1r6r5%33K21%6251%811&Q;%118%<231&L%11;%@231p0B1pU4Q31&R0%13Q7Q3='RH&?&K'8%12Q:Q:%221Q;(7%14Q=Q=EQ5r4%345Q?21r7%K3QC1L%Q?3731%<4QEQC;1%>2QD1&QF+;%;4QGQGQ0Q?%<4>QH1Q0r8%QG3?21r3%73621p091p0I1pQ@R01p0M1pU>R11pQ4R21pQ>R41pQ6R51").
Proof. intros FF LK F rs.
intros RM LKc INC ND k Hk. cbn [app].
assert (ND' : base.NoDup (FF ++ LKc)).
{ apply base.NoDup_ListNoDup. apply base.NoDup_ListNoDup in ND. apply NoDup_map_inv in ND. inversion ND; assumption. }
assert (INC' : incl (FF ++ LKc) (FF ++ LK)) by (intros x Hx; apply in_app_or in Hx; apply in_or_app; destruct Hx as [Hx|Hx]; [left; exact Hx| right; apply INC; exact Hx]).
assert (HD : ff_count k (((F, 4, rs) : fframe) :: FF ++ LKc) = ((if Z.eqb 4 k then 1 else 0) + ff_count k (FF ++ LKc))%nat).
{ unfold ff_count. rewrite list_basics.list.filter_cons. cbn [ff_class fst snd]. destruct (base.decide _) as [X|X]; destruct (Z.eqb 4 k) eqn:E; cbn [length]; try reflexivity; exfalso; first [exact X | exact (X I)]. }
rewrite HD. pose proof (ffc_incl k _ _ ND' INC') as LE. pose proof (RM k Hk) as X. unfold FRAMES in X.
destruct (Z.eqb 4 k) eqn:E; cbn [Nat.add]; rewrite ?Nat2Z.inj_succ; lia.
Qed.
Lemma stksh_of : ltac2:(TCodec.tc2 tcn__PmBHarness "Q6'RIyR0%211'6y8%511%311p051'@&R3r1&IvR9%211%5241&Q3r3&R7r2&Q=%3221&R2&R4&J%11<%32<1%9216+8%7221%>3=91r4%>2?<+T`0%B3321p051p0E1pU@L1pQBN1").
Proof. intros M sp.
intros H SZ j Hj. apply SZ. split; [lia|]. unfold STK in *.
assert (4608 <= (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 36864)) / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.
Section Credit.
Variables (n : Z) (cr cr4 cr5 cr6 cr9 : credit) (qc b : Z).
Hypothesis NR : 0 <= n < 2 ^ 26.
Hypothesis C0 : credit_le (CREDIT n) cr.
Let HV := PMSPA.HV L ar.
Lemma cr_facts : ltac2:(TCodec.tc2 tcn__PmBHarness "E'9':'@&Q2vE%211+8%63521&Q0%115+3%:3921&Q1%119&R6+2+E%3221%A3@51%C281%D2=1").
Proof. exact (PMB.ly_cost L C LY). Qed.
Ltac crt := pose proof cr_facts as (KP & BL & BO); pose proof (PMF.pot_call_le HV n ltac:(cbn; lia) ltac:(cbn; lia) NR) as (PC1 & PC2);
unfold PMSPA.credit_le, PMSPA.credit_keep, PMSPA.scA, PMSPA.cr0, credit_le, credit_sub, CREDIT, PM.pot_call, PM.pot_parser, PMSPA.pst_reset, PMSPA.parser_init,
PM.credit_add, PM.cost1, PM.pot_stack, PM.pot_text, PM.vs_cap in *;
cbn [fst snd PM.p_k PM.p_tb PM.p_tg PM.p_src PM.p_b] in *; subst HV; cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead LibIfaceAJ.heap_view PMSPA.HV] in *;
rewrite ?KP, ?BL, ?BO in *; lia.
Lemma cr2 : ltac2:(TCodec.tc2 tcn__PmBHarness "=&QE&QJvE&QBvD&R1vRD+@%3221%6251%9281vR;%<221").
Proof. crt. Qed.
Hypothesis K2 : PMSPA.credit_keep cr cr4 (PMSPA.scA L (PM.cost1 HV (n + 16))) PMSPA.cr0.
Lemma cr3 : ltac2:(TCodec.tc2 tcn__PmBHarness "=&QE&QJvE&QBvD&R1vRD+Q0%3221%6251%9281vR<%<221").
Proof. crt. Qed.
Hypothesis K3 : PMSPA.credit_keep cr4 cr5 (PMSPA.scA L (PM.cost1 HV (n + 32))) PMSPA.cr0.
Lemma cr4' : ltac2:(TCodec.tc2 tcn__PmBHarness ">&QE&QJvE&QC&QBvD&QA%3221+Q0%5241%7231%:291vR=%=221").
Proof. crt. Qed.
Hypothesis K4 : PMSPA.credit_keep cr5 cr6 (PMSPA.scA L (PM.credit_add (PM.cost1 HV PM.CHUNK) (PM.cost1 HV 32))) PMSPA.cr0.
Lemma cr7 : ltac2:(TCodec.tc2 tcn__PmBHarness "?&QE&QJvE&QDvD&QI&QHvREvR:%3221%511%8271%;2:1vR>%>221").
Proof. crt. Qed.
Hypothesis K7 : PMSPA.credit_keep cr6 cr9 (PMSPA.scA L (PM.pot_parser HV (PMSPA.pst_reset (PMSPA.parser_init qc b)))) PMSPA.cr0.
Lemma crF : ltac2:(TCodec.tc2 tcn__PmBHarness "9&Q7&Q8vR;&Q:vRD%211%5241vR?%8221").
Proof. crt. Qed.
End Credit.
Local Notation LSt := (PMSTA.TopLSA RSEGS PMB.AD PMB.AAD).
Theorem harness_call_okA : ltac2:(TCodec.tc2 tcn__PmBHarness "A&Q9&Q<vE%211vR9&Q6vQN%211&Q4vC%211&QK&QM&Q@&Q?%43321%@5=<961").
Proof.
unfold lib_call_okA. intros fx g LB FF LK cr A sp ptr ra payload R M model K PRE HHs HALT MI HK KONT.
destruct PRE as [pra praok psp pgp ptp pa0 pa1 plen pptr ppay pstack pcredit pffroom pffrs pstksh pstat].
cbn [lla_L lla_gp lla_empty lla_stack lla_frames lla_credit Lay PMTAL.TopLayA_b] in *.
destruct HHs as (HH & SBLK & CLS13).
destruct pstack as (A16 & SLO & SHI & SPT & DSCR & DUP).
set (n := Z.of_nat (length payload)) in *.
assert (NR : 0 <= n < 2 ^ 26) by (subst n; clear - plen; lia).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WFF & _ & _ & _ & _ & _ & _ & _ & TOP47 & NDB & NDF & _).
assert (DRG : 0 <= ptr < 2 ^ 64).
{ destruct pptr as [(P0 & PE)|(P0 & INB)]; [rewrite PE; unfold PMTAL.TopLayA_b; cbn; lia|].
destruct (WB _ INB) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. clear - Q0 Q4 SPT. lia. }
unfold lib_cfgA in KONT |- *. cbn [lla_L lla_entry Lay PMTAL.TopLayA_b] in KONT |- *. rewrite (L5A.aly_segs L C LYa) in *.
change (mkCfg (@mkst fx R (Z_to_bv 64 0xa791c) M (seg_rom RSEGS)) model) with (@L5A.cfg fx R 0xa791c M model).
assert (FF4 : ff_room 4 FF LK).
{ unfold ff_room. pose proof (pffroom 4 ltac:(cbn; tauto)) as X. unfold FRAMES in X. lia. }
apply (PMHA1.entry L ar C HIR LY HIok WF fx R M model K LB FF LK cr A ptr n sp ra g HH (conj HALT MI) HK).
- exact pa0.
- exact pa1.
- exact NR.
- exact DRG.
- exact pra.
- exact praok.
- exact psp.
- exact A16.
- exact ptp.
- split; [exact A16|]. split; [exact SLO|]. split; [exact SHI|]. split; [exact SPT|]. split; [exact DSCR| exact DUP].
- exact FF4.
- exact pffrs.
- exact pstat.
- intros V2 cls F fl LK2 M2 model2 fx3 R3 M3 model3 G SE CLS V2A V2R V2S BI3 RI3 Q1 Q10 Q11 Q12 Q21 Q22 Q23 SZS FAL LS3.
assert (GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMB.AD)) by (rewrite <- L5K.rl3; exact pgp).
assert (TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L)) by (rewrite <- L5K.rl4; exact ptp).
assert (FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f) by (intros f Hf; rewrite <- SE; exact (pffrs f Hf)).
assert (ROOM : forall LKc, incl LKc LK -> base.NoDup (map ff_addr ((F, 4, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 4, V2 - 128 + 32) :: FF) LKc)
by exact (room_of FF LK F (V2 - 128 + 32) (fun k Hk => pffroom k Hk)).
assert (STKSH : shadow_zero M (V2 + cls - 36864) 4608) by (rewrite <- SE; exact (stksh_of M sp SHI pstksh)).
assert (UR1 : U R 1 = ra) by (apply U_of; [rewrite <- L5K.rl1; exact pra| destruct praok; lia]).
assert (RAok : L5.ra_ok (U R 1)) by (rewrite UR1; exact praok).
assert (G2R : getr R (reg 2) = Z_to_bv 64 (V2 + cls)) by (rewrite <- SE, <- L5K.rl2; exact psp).
assert (SRCB : n = 0 \/ (exists B m, In (B, m) LB /\ B <= ptr /\ ptr + n <= B + m)).
{ destruct pptr as [(P0 & _)|(P0 & INB)]; [left; subst n; rewrite P0; reflexivity| right; exists ptr, n; split; [exact INB| lia]]. }
assert (ACCd : aacc M3 ptr n).
{ destruct pptr as [(P0 & _)|(P0 & INB)]; [subst n; rewrite P0; intros x Hx; cbn in Hx; lia|].
pose proof BI3 as (_ & _ & _ & _ & _ & _ & EK3 & _).
destruct (WB _ INB) as ((B0 & _ & B3 & B4 & B5 & B6) & _). cbn [fst snd] in *. unfold app_mem in B6.
rewrite Forall_forall in SBLK. pose proof (SBLK _ INB) as SB0. cbn [fst snd] in SB0.
apply (PMFA.accA_agree M M3 ptr n); [| apply (L5CBR.aacc_of_blk M ptr n ptr n SB0); [apply PMKB.mod16_8'; exact B3| lia| lia| lia]].
intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. apply EK3. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split.
- do 6 right. exists (ptr, n). split; [exact INB|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
- intros rr Hr Hin. unfold WF, PMTAL.foot_b, PMTAL.ATEXIT_b in Hr. cbn in Hr. unfold L5.in_rng in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hin; lia|]). destruct Hr. }
apply (PMHA2.stage2 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF STR fx3 R3 M3 model3 K ptr n g BI3 RI3 HK LS3 Q1 Q10 Q11 Q12 Q21 Q22 Q23 SZS NR DRG SRCB ACCd (cr2 n cr NR pcredit)).
intros fx4 R4 M4 model4 LK4 cr4 A4 s BI4 RI4 S1 S10 S11 S12 S21 S22 S23 VSTR SIZE SSH SLG CK2 SZ4 LS4.
assert (LONG : forall c n0 p, s = PM.VLong c n0 p -> 23 <= n0).
{ intros c n0 p E. destruct (Z_le_gt_dec n 22) as [X|X]; [rewrite (SSH X) in E; discriminate|]. rewrite E in SIZE. cbn in SIZE. lia. }
apply (PMHA3.stage3 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF wloc_WF ISS fx4 R4 M4 model4 K LK4 cr4 A4 s ptr n g BI4 RI4 HK LS4 S1 S10 S11 S12 S21 S22 S23 VSTR SIZE LONG NR DRG
(cr3 n cr cr4 NR pcredit CK2) SZ4).
intros fx5 R5 M5 model5 LK5 cr5 A5 s' sm BI5 RI5 LS5 P1 P10 P11 P12 P13 P21 P22 P23 P26 VS5 IS5 SIZE5 SMG SMST CK3 V432 O928 O936 O944 O952 O956 SZV SZP SZO SZI.
apply (PMHA4.stage4 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL RDC fx5 R5 M5 model5 K LK5 cr5 A5 s s' sm n (PMST.ST true (PMST.st_sys g) (PMST.st_err g)) BI5 RI5 HK eq_refl LS5
P1 P10 P11 P12 P13 P21 P22 P23 P26 ltac:(lia) VS5 IS5 (cr4' n cr cr4 cr5 NR pcredit CK2 CK3) V432 O928 O936 O952 SZV SZP SZO SZI).
intros fx6 R6 M6 model6 LK6 cr6 A6 qc b BI6 RI6 LS6 T1 T21 T22 T23 T26 VS6 IS6 PA6 CK4 V432' SZV' REF6 EC6 SZE6 SZI6 SZR6.
set (g1 := PMST.ST true (PMST.st_sys g) (PMST.st_err g)) in *.
apply (PMHA5.stage5 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF wsys_WF SYS fx6 R6 M6 model6 K LK6 cr6 A6 s s' sm (PMSPA.parser_init qc b) g1 BI6 RI6 HK LS6 T1 T21 T22 T23 T26
(conj VS6 (conj IS6 (conj V432' (conj SZV' SZI6)))) (conj PA6 REF6) EC6 SZE6 SZR6).
intros fx7 R7 M7 model7 LK7 A7 BI7 RI7 LS7 U1 U10 U11 U21 U22 U23 U26 HB7 HQ7 HE7 SZR7.
set (g2 := PMST.ST (PMST.st_loc g1) true (PMST.st_err g1)) in *.
assert (TBOK : PM.tb_ok (PM.p_tb (PMSPA.parser_init qc b)) (PM.p_tg (PMSPA.parser_init qc b))).
{ unfold PM.tb_ok. cbn. split; [lia|]. split; [lia| reflexivity]. }
assert (UNR : PM.unread (PM.p_src (PMSPA.parser_init qc b)) sm < 2 ^ 26).
{ pose proof HB7 as (_ & ISX & _). destruct ISX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IE1 & IE2).
unfold PM.unread, PMSPA.parser_init. cbn [PM.p_src PM.sr_rem]. rewrite IE1, SMG. replace (F + 96 + 80) with (F + 96 + 80) by lia. rewrite SIZE5. lia. }
apply (PMHA7.stage7 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF FAL werr_WF RRD fx7 R7 M7 model7 K LK7 cr6 A7 s s' sm (PMSPA.parser_init qc b) g2 (pa_syscat_obj PMB.AD)
BI7 RI7 HK LS7 U1 U10 U11 U21 U22 U23 U26 HB7 HQ7 HE7 ltac:(cbn; lia) SZR7 UNR TBOK (cr7 n cr cr4 cr5 cr6 qc b NR pcredit CK2 CK3 CK4)).
intros fx9 R9 M9 model9 LK9 cr9 A9 ps' sm' e' BI9 RI9 LS9 EIMP X1 X10 X21 X22 X23 X26 HB9 HS9 TB9 HV9 FT9 CK7.
set (g3 := PMST.ST (PMST.st_loc g2) (PMST.st_sys g2) e') in *.
apply (PMHA8.stage8 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF VDT OPD fx9 R9 M9 model9 K LK9 cr9 A9 s s' (PM.p_tb ps') sm' (PM.p_src ps') (PM.p_b ps') (PM.p_k ps') (PM.p_stk ps') g3
BI9 RI9 HK LS9 X1 X10 X21 X22 X23 X26 HB9 HS9 TB9 HV9 FT9).
intros fx10 R10 M10 model10 LK10 A10 BI10 RI10 LS10 Y1 Y10 Y21 Y22 Y23 Y26 HB10 HS10.
apply (PMHA9.stage9 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF IL ICok ILY SRCD OPD fx10 R10 M10 model10 K LK10 cr9 A10 s s' sm' (PM.p_src ps') g3 BI10 RI10 HK LS10 Y1 Y10 Y21 Y22 Y23 Y26 HB10 HS10).
intros fx11 R11 M11 model11 LK11 A11 BI11 RI11 LS11 Z1 Z10 Z21 Z22 Z23 Z26 HF11.
apply (PMHA10.stage10 L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A GP TP FFRS ROOM STKSH wapp_WF LCD IOD OPD fx11 R11 M11 model11 K LK11 cr9 A11 s (PM.sm_st sm') g3 BI11 RI11 HK LS11 Z1 Z10 Z21 Z22 Z23 Z26 HF11).
intros fx12 R12 M12 model12 LK12 A12 BI12 RI12 LS12 V21 V22 V23 V26.
apply (PMHA11.harness_tail L ar C HIR LY HIok M model LB FF LK A R V2 cls F fl LK2 M2 model2 cr WF G CLS V2R V2S V2A FFRS STKSH RAok G2R
fx12 R12 M12 model12 [] LK12 cr9 A12 K BI12 RI12 V21 V22 V23 V26).
intros fxf Rf Mf modelf RPf A0f FRMf AHf RTf AMf HHf.
pose proof BI12 as (BB1 & BB2 & BB3 & BB4 & BB5 & BB6 & BB7 & BB8 & BB9 & BB10).
cbn [app] in HHf.
assert (LSf : PMSTA.ls_okA RSEGS PMB.AD PMB.AAD (PMST.ST true true e') Mf).
{ apply (PMHAK.ls_piece _ M12 Mf (L5AFKR.Wret F fl 4) FRMf); [| exact LS12].
pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ FS1 FS2 FCEIL _ FLP _ _ _ FR F8 FBIG _ _ FLR _ _ _].
intros a Wa. unfold L5AFKR.Wret in Wa. change (ff_bytes 4) with 1024 in *. change (1024 / 8) with 128 in Wa. unfold HeapIfaceA.SB in Wa.
clear - Wa FR FLR. lia. }
rewrite UR1.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDf & _).
apply (KONT fxf (PMST.ST true true e') Rf Mf modelf cr9 LK12 A12).
+ constructor.
* rewrite L5K.rl10. exact A0f.
* exact RPf.
* cbn [lla_credit Lay PMTAL.TopLayA_b]. fold n. exact (crF n cr cr4 cr5 cr6 cr9 qc b NR CK2 CK3 CK4 CK7).
* intros a Ha Hc NF NJ. apply (proj1 AHf). split; [exact Ha|]. split; [rewrite <- SE; exact Hc|].
intros rr Hr Hin. apply NF. unfold WF in Hr. apply in_map_iff in Hr. destruct Hr as (iv & <- & Hiv).
exists iv. split; [exact Hiv|]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
* cbn [lla_stack Lay PMTAL.TopLayA_b]. rewrite SE. exact (proj1 (proj2 AHf)).
* intros a Ha Hc. rewrite SE in Hc. exact (proj2 (proj2 AHf) a Ha Hc).
* cbn [lla_stack Lay PMTAL.TopLayA_b] in *. intros j Hj. unfold byte_at. rewrite (proj1 AHf); [exact (pstksh j Hj)|].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (AR : HeapIfaceA.S (ahl_ceil ar) <= HeapIfaceA.S (sp - STK) + j <= HeapIfaceA.S (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1)
/\ 2147450880 <= HeapIfaceA.S (sp - STK) + j < 2 ^ 64).
{ unfold HeapIfaceA.S, HeapIfaceA.SB, STK in *. clear - Hj SLO SHI SPT TOP47. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
split; [clear - AR; lia|]. split; [rewrite <- SE; right; right; right; right; left; exact (proj1 AR)|].
intros rr Hr X. unfold WF, PMTAL.foot_b, PMTAL.ATEXIT_b in Hr. cbn in Hr. unfold L5.in_rng in X. destruct AR as [_ AR].
repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in X; clear - X AR; lia|]). destruct Hr.
* exact LSf.
+ exact RTf.
+ exact BB4.
+ exact (proj1 AMf).
+ exact (proj2 AMf).
+ intros k Hk. cbn [lla_leak Lay PMTAL.TopLayA_b]. unfold LEAK.
pose proof (ffc_incl k LK12 LK (nodup_lk FF LK12 NDf) BB5) as X. lia.
+ split; [exact HHf|]. split.
* apply (sj_keep L ar LB FF LK12 M Mf).
-- pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHf) as (WBf & WFf & W3 & _ & _ & _ & _ & _ & (_ & _ & WW9 & WW10) & _).
split; [|split; [|split; [exact W3|exact (conj WW9 WW10)]]].
++ intros bb Hb. destruct (WBf bb Hb) as (Q1' & _ & _ & _ & _ & Q6 & _). exact (conj Q1' Q6).
++ intros f Hf. destruct (WFf f Hf) as (Q1' & Q2' & Q3' & Q4' & _). exact (conj Q1' (conj Q2' (conj Q3' Q4'))).
-- intros bb a Hb Ha. destruct (WB bb Hb) as ((Y0 & _ & _ & Y4 & _ & Y6) & _). unfold app_mem in Y6.
assert (SR : BIGSHADOW_LO <= a < BIGSHADOW_HI).
{ unfold in_shadow_of in Ha. pose proof (PMKB.S_in_shadow (fst bb) ltac:(lia)) as SS1. pose proof (PMKB.S_in_shadow (fst bb + snd bb - 1) ltac:(lia)) as SS2. lia. }
apply (proj1 AHf). split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SR; lia|]. split.
++ rewrite <- SE. do 6 right. exists bb. split; [exact Hb| exact Ha].
++ intros rr Hr X. unfold WF, PMTAL.foot_b, PMTAL.ATEXIT_b in Hr. cbn in Hr. unfold L5.in_rng in X. unfold BIGSHADOW_LO, BIGSHADOW_HI in SR.
repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in X; clear - X SR; lia|]). destruct Hr.
-- exact SBLK.
* rewrite Forall_forall in *. intros f Hf. apply CLS13. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf|Hf]; [left; exact Hf| right; apply BB5; exact Hf].
Qed.
End TOP.
End SCFG_1.
End PMHA.

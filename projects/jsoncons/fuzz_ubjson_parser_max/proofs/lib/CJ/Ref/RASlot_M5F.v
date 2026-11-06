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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W18 ASlot_I ASlot_M0 ASlot_M5D.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W18 RASlot_W19 RASlot_M0 RASlot_M2 RASlot_M5D.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require MallocFacts_inv4.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Ref_RASlot_M5F () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_M5F.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RASlot_W18."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Ref.RMallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2or"; "3Forall"; "4Z"; "0RUNp"; "5meta_slot"; "6disjoint_from"; "7alloc_ceiling"; "8rlowW"; "8rmetaW"]; ["9rfailW"; ":RCTX"; ":rmrep"; ";aptr"; ";c_free_meta_head"; ";conc"; ";ctx"; ";get_meta_rec"; ";m_prev"; ";mstate"; ";optr"; "<add"; "<le"; "<sub"; "0W"; "0a"]; ["0h"; "0m'"; "0mt"; "0n"; "0p"; "0q"; "0spv"; "0st"; "=bv"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto. Local Ltac tauto := first [ solve [ repeat (lazymatch goal with |- _ /\ _ => split | |- True => exact I end) ] | L5FastTauto.ptauto ].
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition rlowW (spv : Z) (iv : Z * Z) : Prop :=
(0 <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0xe9000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928)))
\/ iv = (spv - 144, spv).
#[using="Type"] Lemma rlowW_meta : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M5F "Q4'9'I'Q8yR0%211'2y8%511%311p051&C&Bv:r3r2%43321&;r4%2214&>r6(3&Er5%221;&K+Q8%2231%74LL41%:291p0<1p0@1pR<F1pR4H1pR@Q11pR>Q31").
Proof. intros spv st m' q.
intros MR MS. destruct (rmeta_slot_bounds st m' q MR MS) as (Gpos & GC & GI & _). pose_ceil. left. pose_ceil. cbn [fst snd]. lia.
Qed.
Definition rmetaW (spv : Z) (st : mstate) (iv : Z * Z) : Prop :=
(exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (RCTX + 16, RCTX + 24) \/ iv = (spv - 144, spv).
#[using="Type"] Lemma rfailW_shape : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M5F "Q@'I&C'9&;r3r2%3221'6&J&D&Fr5%211%411(0r1%22?1%:3941'5r6%A21?&H&Gr7%221D%411%C3B1:r8%I21Gp031pR:M1%=2;1p0?1pR2Q01'8'4%12Q2Q2&?%12Q2K&@r4%23N1Q5%83641p0:1p0Q61pR>Q;1pR6Q=1pR@Q?1").
Proof. intros st mt spv.
intros MS FL. unfold rfailW.
constructor; [right; right; reflexivity|].
constructor; [left; exists mt; auto|].
constructor; [right; left; reflexivity|].
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; [|constructor].
destruct (FL h eq_refl) as [MSh FP].
constructor; [left; exists h; auto|].
destruct (m_prev (get_meta_rec st h)) as [p|] eqn:HP; [|constructor].
constructor; [left; exists p; auto| constructor].
Qed.
#[using="Type"] Lemma rfailW_low : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M5F "QO'I&C'Q8yR0%211'2y8%511%311p051'9&Bv:r4r2%43321&;r5%2215'6&J&D&Fr7%211%411(0r1%22K1%:3941'5r8%@21B&H&Gr9r3%3221%511%D3C1;r:%I21Kp031pR:Q:1%>2<1p0@1pR2Q=1'8'4%12Q7Q7&>%11Q6&@r6%23O1Q9%83641p0:1p0Q71p0Q;1pR>QA1pR4QC1pR6QL1pR@QN1").
Proof. intros st mt m' spv.
intros MR MS FL. eapply Forall_impl; [| exact (rfailW_shape st mt spv MS FL)].
intros [lo hi] [(q & MSq & E1 & E2)|[E|E]]; [cbn in E1, E2; subst; eapply rlowW_meta; eassumption| inversion E; subst; left; (pose_ceil; unfold RCTX); cbn; lia| inversion E; subst; right; reflexivity].
Qed.
#[using="Type"] Lemma rlowW_disjoint : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M5F "Q4'9'1'4%1233%311'8&>r4%211r3%53721&L&=v:%211%4216'7&K%12;9&Mr6+T@%3221%<251%=24A%9221&<r5%2381Ep041p0?1p0E1pR8Q01pR0Q11pQNN1pR>Q31").
Proof. intros spv W a n. intros FW Ha Hs. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(H1 & H2 & H3)|E]; [cbn in *; lia| inversion E; subst; lia]. Qed.
#[using="Type"] Lemma rlowW_disjoint_img : ltac2:(TCodec.tc2 tcn__CJ_Ref_RASlot_M5F "Q@'9'1'4%1233%311'8&>r4%211r3%53721&L+RPP0%2214&K%1286+mTP0%6221'7r5%621=&A%;221+m0%:231%>216%8241&=v:%211&Mr8+T@%3221%G251&<r7r6%33721p051p0>1p0H1p0M1p0Q11pR8Q<1pR0Q=1pQNQ:1pR>Q?1").
Proof. intros spv W a n. intros FW H1 H2 H3 H4. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(X1 & X2 & X3)|E]; [cbn in *; pose_ceil; lia| inversion E; subst; pose_ceil; lia]. Qed.
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
#[using="LB req errv AR IS ER SC RQ MR AUX CLO LO ERR TP HK"] Lemma rnfail_ok : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof.
intros st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC.
destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
& PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. pose_ceil.
pose proof (rerrno_lit5 tp TP) as EA.
destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), (-1); split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 (-1) AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
pose proof (rmeta_slot_bounds st2 m4 mm MR4 MSL) as (Gpos & GC & GI & _). pose_ceil.
pose proof (lf_freelist _ (isf_lf _ _ F3)) as FFL. change (fact_freelist (strip st3)) with (fact_freelist st3) in FFL.
assert (FL : forall h, c_free_meta_head (ctx st3) = Some h ->
meta_slot st3 h /\ h <> mm /\ exists p, m_prev (get_meta_rec st3 h) = Some p /\ meta_slot st3 p /\ p <> mm).
{ intros h Hh. destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp). destruct (NFL h Hh) as [NE1 NE2].
change (meta_slot (strip st3) h) in MSh. change (get_meta_rec (strip st3) h) with (get_meta_rec st3 h) in MEMh, NXh, HP.
change (meta_slot (strip st3) p) in MSp.
split; [exact MSh|]. split; [exact NE1|]. exists p. split; [exact HP|]. split; [exact MSp|]. intros ->. apply NE2. exact HP. }
rewrite as_free_meta_eq. cbn [as_kq].
riprefixT. unfold rnest_regs.
eapply evt_cut.
{ rewrite <- GE. unfold rFRM in FR''. replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) in FR'' by lia.
eapply (rfailm1_walk st3 mm MS3 FL); [exact MR''| exact MI''| exact FR''| lia]. }
cbv beta. intros ms' (a1x & s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7).
assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW st3 mm (bv_unsigned sp))).
{ eapply (rfailW_low st3 mm m'' _ MR'' MS3). intros h Hh. destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _).
split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
assert (ST7 : stk rsegs m7 lo (bv_unsigned sp + -144)).
{ eapply stk_transport_disjoint; [| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]].
replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
assert (ERR7 : rw_cells rsegs m7 (errno_addr tp) [C4 errv'']).
{ eapply rw_cells_transport; [exact ERR''| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
cbv beta. intros ms' (a1y & a2y & -> & ST8). apply evt_done.
set (stF := as_fm_st st3 mm) in *.
destruct (fm_proj st3 mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
assert (FS : Forall (rmetaW (bv_unsigned sp) st3) (rfailW st3 mm (bv_unsigned sp))).
{ apply (rfailW_shape st3 mm _ MS3). intros h Hh; destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
{ eapply rpres_except_trans.
- eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr.
destruct (mrel_regions _ _ MREL'' rid r Hr) as (r' & Hr' & K' & B' & L'). exists r'. rewrite PF1. auto.
- eapply rpres_except_trans.
+ eapply rpres_except_mono; [exact PE''|]. intros a Ha. eapply (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia)); [| exact Ha].
intros rid r Hr. exists r. rewrite PF1. repeat split; auto. lia.
+ eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
* cbn in E1, E2. subst lo' hi'. left. do 3 right.
assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. split; [exact H0|]. split; [exact K0|].
assert (EC : conc stF q = conc st3 q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
* inversion E; subst. left. right. right. left. unfold RCTX in *. lia.
* inversion E; subst. left. left. lia. }
apply HK. unfold ras_post2.
do 14 eexists. exists m7, errv''. split; [reflexivity|].
split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
split; [exact MR7|].
split; [eapply ticks_ok_same; [rewrite PF2; reflexivity| rewrite PF6; reflexivity| exact TK'']|].
split. { eapply (unk_agree_xfer o st3 m'' stF m7 UA'').
- exact PF2.
- intros rid r Hk Hr. rewrite PF1 in Hr. exact Hr.
- intros b. rewrite PF3. tauto.
- intros rid r off h Hr Hk Ho Hc NG.
pose proof MR'' as (WF3 & _). pose proof WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). pose_ceil.
destruct (rregion_facts st3 m'' rid r MR'' Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
+ cbn in E1, E2. subst lo' hi'.
destruct (rmeta_chunk_facts st3 m'' q MR'' MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
+ inversion E; subst. unfold RCTX in Ha. lia.
+ inversion E; subst. lia. }
split; [exact PE07|].
split. { split.
- intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _).
destruct (mrel_regions _ _ MREL'' rid r' H') as (r'' & H'' & K'' & B'' & L''). exists r''. rewrite PF1. repeat split; auto; [congruence| congruence| lia].
- rewrite PF7. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
- rewrite PF8, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
split. { unfold brk_link_ps in BL'' |- *. rewrite PF11. destruct (c_brk (ctx st3)) as [| |brid boff]; auto.
unfold conc, get_region. rewrite PF1. exact BL''. }
split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
split. { constructor.
- intros c' Hc'. rewrite PF9, (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
- intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
- rewrite PF6, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
- intros H; exfalso; lia.
- intros _ H; exfalso; lia. }
split; [rewrite PF12; exact CTR''|].
left. reflexivity.
Qed.
End LEVEL.
End CEIL_WRAP_1.

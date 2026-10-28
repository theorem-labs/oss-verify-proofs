(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0 ASlot_M1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RAllocSlot_iface HP_RASlot_I HP_RASlot_W9 HP_RASlot_M0.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Virgin.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RASlot_M1 () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "Corelib.Numbers.BinNums.N"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.slot_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_stride"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.free_slot_addr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_I.ras_post2"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W0.ta_rel"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W9.gmf"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.lowbit"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_avail"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RASlot_W9.rta_fp"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W1.as_k"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.full_lay"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].



(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : RISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

#[using="hRP LBK"] Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. rceilb. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

#[using="hRP LB sc F ER SC RQ FIT TR GM MSK K0 LBK"] Lemma rta_slot_ok : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M1 ()) "(0.$1.Lb,$1.(0.$2.Lr,$2.(3.(4.$5.(6.(7.Vst,Vg,))(8.$1.R2.))(3.(4.(9.$2.)(:.$;.$2.(<.$;.$=.$>.$2.)(?.$;.$=.$>.$2.)(10.$;.$11.R2.)(12.Vst,))(8.$2.R1.))(3.(4.(9.$2.)(:.$;.$2.(<.$;.$=.$>.$2.)(?.$;.$=.$>.$2.)(10.$;.$11.R2.)(12.Vst',))(8.$2.R1.))(3.(4.$13.(14.R1.)$15.)(3.(16.Vst',Vg,R2.R1.Vk,Vreq,)(3.(4.$11.(17.(7.Vst',Vg,))(17.(7.Vst,Vg,)))Pa,$11.P,(3.(18.(19.(1:.(1:.(1:.(1;.R2.)(1<.$;.$11.R3.))+10.)(1=.(17.(7.Vst',Vg,))Vk,))+4.)R1.)(1>.R1.(19.(1:.(1:.(1:.(1:.(1;.R2.)(1<.$;.$11.R3.))+10.)(1=.(17.(7.Vst',Vg,))Vk,))(17.(7.Vst',Vg,)))+4.)))(1?.Vst0,R2.)))))))))")
(* [comment removed for export] *).
Proof. rceilb.
  pose proof (isf_mf _ _ F) as MF.
  pose proof (gmf_cls _ _ _ GM) as GSC.
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  ddestruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  (* [comment removed for export] *)
  destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
  assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
  assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
  assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
  { rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }
  (* [comment removed for export] *)
  assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| exact LBK]).
  assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
  { apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  ddestruct (FM g b Hmem) as (FM1 & FM2 & _).
  assert (KLI : k <= m_last_idx (get_meta_rec st g)).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
    cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
  assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; exact TBst])) as FC.
  cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
  { pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
    exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
  pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
  pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
  unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
  destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
  assert (P2k : 0 < 2 ^ k <= msk).
  { split; [apply Z.pow_pos_nonneg; lia|]. ddestruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE'). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. exact LE'. }
  exists b, r.
  split; [exact Hmem|]. split; [exact Hr|].
  split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); exact Hr|]. split; [exact Hk|].
  split; [| split; [exact ST'|]].
  - pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4).
    assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; exact ST').
    constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      rewrite ?ST2; fold mr; rewrite ?EM, ?EL, ?EF, ?ES, ?EP, ?STX.
    + exact Hmem.
    + unfold st'. cbn. rewrite (tr_regions _ _ _ TR). exact Hr.
    + exact Hk.
    + exact B0.
    + exact B16.
    + lia.
    + lia.
    + exact SPAN.
    + unfold UNIT in S16. lia.
    + unfold UNIT in SMOD. exact SMOD.
    + lia.
    + exact RQ.
    + lia.
    + intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
      destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _). exact (NOGRP b' gh1 Hb1 Hf').
    + unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). exact K4.
    + intros off O0 OF.
      assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
      assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
    + unfold st'. cbn. rewrite (tr_slots _ _ _ TR). exact SSL.
    + unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSL]. apply (tr_areas _ _ _ TR).
    + unfold msk, mr in *. lia.
    + unfold mr. lia.
    + lia.
    + lia.
    + left. lia.
  - intros a Ha. rewrite ST' in Ha.
    destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
    assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; exact Hmem).
    ddestruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
    dexists g, b, r, k. split; [exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); exact Hr|]. split; [exact Hk|]. split; [lia|].
    split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
    + pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; exact TB0].
    + assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
        by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
      assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
      lia.
Qed.
End TASLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
Hypothesis CLO : rceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M1 ()) "Pst1,$20.Pidx,$11.Ps',$21.Pms',$22.P,(23.VhRP,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vo,Vm,Vst0,Vst,Vs,Vlo,Vsc,Vreq,R4.R3.R2.R1.)(24.VR,Vo,A2.Vk,R5.R4.R3.VQ,R2.)")
(* [comment removed for export] *).
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

#[using="hRP R k o s Q ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req errv ERR TP HK"] Lemma rerrno_lit : errno_addr tp = 0x5d024.
Proof. rceilb. subst tp. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="st0 LB errv AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK F0"] Lemma rhk1_ok : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_M1 ()) "PstX,$20.Pg3,$1.Pmsk,$11.Pkk,$11.Pm',P,(25.&40.)(9.(25.&8.))Pt0',(25.&40.)Pt1',(25.&40.)Pa1',(25.&40.)Pa2',(25.&40.)Pa3',(25.&40.)Pa4',(25.&40.)Pa5',(25.&40.)Pa6',(25.&40.)Pa7',(25.&40.)P,(26.Vsc,Vst,R>.)P,(4.$5.(27.R?.Vsc,)(8.$1.R>.))P,(28.Vst,Vsc,R?.)P,(4.$11.R?.(29.(7.R11.R10.)))P,(3.(1>.=R10.)(1>.R10.(2:.+2.+20.)))P,(4.$11.(2;.R11.)(2:.+2.R10.))P,(3.(18.=R11.)(1>.R11.+20.))P,(2<.VhRP,(2=.R14.(2>.(19.R13.(2;.R13.)))R15.)R11.)P,(2?.$30.R12.)P,(31.$30.R13.Vlo,(32.&40.Vsp,))P,(33.(34.Vst,Vlo,(32.&40.Vsp,))Vm,R14.)(24.VR,Vo,(35.VR,$36.Vf,Vsc,Vreq,Vk,Vbail,(2=.R18.(2>.(19.R17.(2;.R17.)))R19.)(2;.R17.))Vs,VQ,(37.(38.Vra,Vsp,Vgp,Vtp,R14.R13.Vt2,Vs0,Vs1,(39.R16.)R12.R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(3:.Vra,)Vfc,(3;.(25.&40.))R15.(3<.$30.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
  unfold as_k. replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
  cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
  pose proof rerrno_lit as EA. pose proof (RAS_STACK_ge sc) as ASG.
  pose proof (isf_mf _ _ F0) as MF.
  set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
  subst msk.
  ddestruct (rta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
    as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA).
  fold st' in Hr', SO, STR, FSA.
  (* [comment removed for export] *)
  pose proof MR as (WF & _). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
  assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).
  (* [comment removed for export] *)
  assert (FPC : forall a, rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 st' lo (bv_unsigned sp) a).
  { intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - left. left. exact X.
    - left. right. right. left. exact X.
    - left. do 3 right. ddestruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
      dexists rid0, r0. rewrite REGX. split; [exact H0|]. split; [exact K0|]. lia.
    - do 3 right. left. ddestruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct ER as [_ EG EGR _ _ _ _ _].
      destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
      dexists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
      pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
  assert (PE' : rpres_except (rmalloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply rpres_except_mono; [exact PE| exact FPC]).
  (* [comment removed for export] *)
  assert (NIMG : forall a, 0x10000 <= a < 0x7e000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a).
  { intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - rceilb. lia.
    - exact (Hc X).
    - ddestruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
    - ddestruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _). ddestruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
      pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
  apply HK. unfold ras_post2.
  dexists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
  split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| unfold RCTX; lia]. }
  split. { eapply rauxv_ok_pres; [exact AUX| exact PE| |].
           - intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
             + lia. + unfold RCTX in X. rceilb. lia.
             + ddestruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). rceilb. lia.
             + ddestruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). rceilb. lia.
           - intros a Ha. apply NIMG; unfold RAUXV_CELL, RCTX in *; lia. }
  split; [exact MR'|].
  split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
  split. { (* [comment removed for export] *)
    intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
    assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
    { revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
    assert (NG0 : ~ grp_hdr_cov st rid off).
    { (intros dd_H; ddestruct dd_H as (bq & gh & Hbq & Hf & Hoff)). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
      destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. dexists bq, gh1. unfold st'. cbn. auto. }
    rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
    refine (proj1 (PE (r_base rr + off) _ _)).
    { destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). rceilb. lia. }
    intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). lia.
    - ddestruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
    - ddestruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid rr Hrr Kr); lia.
    - ddestruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct (N.eq_dec (fst bq) rid) as [E|NE].
      + apply NG0. dexists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
      + pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
  split; [exact PE'|].
  split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
           intros rid rr Hrr. exists rr. rewrite REGX. repeat split; auto. lia. }
  split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
           unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. exact BL. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { (* [comment removed for export] *) constructor.
    - intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
    - intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). exact Ha.
    - unfold st'. cbn. apply (tr_tick _ _ _ TR).
    - intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
      unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
      destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
      exact (AC rid sh o' v t Esh Hc).
    - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
    - (* [comment removed for export] *)
      intros _ g' b' HA' Hmem' UND. exfalso.
      unfold st' in HA'. rewrite active_upd_meta, HA in HA'. injection HA' as <-.
      revert UND. unfold undersized, st'. rewrite get_meta_rec_upd_same.
      destruct (tr_geom _ _ _ TR g3) as (GMX & GLX & GFX & GCX & GPX).
      assert (GSX : forall v, get_stride (m_set_avail v (get_meta_rec stX g3)) = get_stride (get_meta_rec st g3)).
      { intros v. unfold get_stride. destruct (get_meta_rec stX g3); cbn in *. rewrite GLX, GCX, GPX. reflexivity. }
      rewrite GSX. replace (m_sizeclass (m_set_avail _ (get_meta_rec stX g3))) with (m_sizeclass (get_meta_rec st g3))
        by (destruct (get_meta_rec stX g3); cbn in *; rewrite GCX; reflexivity).
      intros UND.
      destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
      destruct (gmf_grp _ _ _ GM) as (bg & ghg & Hmemg & _).
      assert (Hmem0 : m_mem (get_meta_rec st0 g3) = Some bg) by (rewrite <- EME0; exact Hmemg).
      ddestruct (EGE0 g3 ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
      pose proof (gmf_cls _ _ _ GM) as CLS.
      destruct (areach_under st0 LB AR g3 bg Hmem0 ltac:(rewrite <- GC0'; lia) ltac:(rewrite <- GS0', <- GC0'; apply UND; lia)) as [AV0 FR0].
      pose proof (lowbit_testbit _ kk ltac:(lia) LBK) as TBX.
      pose proof (tr_bits _ _ _ TR g3 kk ltac:(lia) ltac:(rewrite TBX; reflexivity)) as TBst.
      pose proof (EB0 g3 kk ltac:(lia) TBst) as TB0. rewrite AV0, FR0, Z.bits_0 in TB0. discriminate. }
  split. { unfold st', ctx. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
           pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
  right. split; [lia|]. dexists g3, b, r.
  split; [unfold st'; rewrite active_upd_meta; exact HA|]. split; [exact SO|]. split.
  - intros a Ha. do 2 right. left. apply FSA. exact Ha.
  - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed.
End LEVEL.

End RP_1.

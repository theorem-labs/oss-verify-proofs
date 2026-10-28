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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 ASlot_W9 F_ntf_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RF_enframe HP_RF_malloc_entry HP_RF_malloc_small HP_RF_ntf_A HP_RF_ntf_C HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RASlot_W2 HP_RASlot_W4 HP_RASlot_W3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RASlot_W9 () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W0.ta_rel"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W9.gmf"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_avail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.lowbit"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_avail"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RP_1.rta_fp"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ta_fin"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W1.ta_avz"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_freed"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_next"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W1.ta_act"; "RP_1.PHASE.rnclosed"; "RocqVerifyHarness.AgentSubmission.Heap.ASlot_W1.ta_m"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AS.ta_fail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.try_avail"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ralloc_slot_entry"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W9 ()) "(0.(1.(2.O3.O1.)(3.O1.O2.))(0.(1.(2.$4.O1.)(3.O1.(5.$4.+3:0.)))(0.(6.$7.Lq,$7.(1.(8.O4.R1.)(1.(2.(9.O4.R1.)O1.)(3.O1.(5.(9.O4.R1.)+28.)))))(6.$7.Lb,$7.(6.$:.Lgh,$:.(1.(;.(<.$:.)(=.$7.$:.(>.$7.(?.$10.$11.$12.$13.)(14.$10.$11.$15.$12.$13.$16.)$:.)(17.$7.(?.$10.$11.$12.$13.)(14.$10.$11.$15.$12.$13.$16.)$:.)R2.(18.O4.))(19.$:.R1.))(1.(2.(9.O4.R2.)O1.)(3.O1.(5.(9.O4.R2.)+9.)))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma rta_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rta_fp st lo sp a. Proof. intros; right; left; assumption. Qed.
#[using="hRP"] Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof. rceilb. intros; do 2 right; left. exists q; auto. Qed.
#[using="hRP"] Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof. rceilb. intros; do 3 right. dexists b, gh; auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
(* [comment removed for export] *)
Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : rceil <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
  rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
Hypothesis HK1 : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W9 ()) "PstX,$1:.Pg3,$7.Pmsk,$12.Pk,$12.Pm',P,(1;.&40.)(<.(1;.&8.))Pt0',(1;.&40.)Pt1',(1;.&40.)Pa1',(1;.&40.)Pa2',(1;.&40.)Pa3',(1;.&40.)Pa4',(1;.&40.)Pa5',(1;.&40.)Pa6',(1;.&40.)Pa7',(1;.&40.)P,(1<.Vsc,Vst,R>.)P,(;.$1=.(1>.R?.Vsc,)(19.$7.R>.))P,(1?.Vst,Vsc,R?.)P,(;.$12.R?.(20.(21.R11.R10.)))P,(1.(3.=R10.)(3.R10.(22.+2.+20.)))P,(;.$12.(23.R11.)(22.+2.R10.))P,(1.(2.=R11.)(3.R11.+20.))P,(24.VhRP,(25.R14.(26.(27.R13.(23.R13.)))R15.)R11.)P,(28.$29.R12.)P,(2:.$29.R13.Vlo,Vspv,)P,(2;.(2<.Vst,Vlo,Vspv,)Vm,R14.)(2=.VR,Vo,A2.VK,(25.R18.(26.(27.R17.(23.R17.)))R19.)(23.R17.)Vs,VQ,(2>.(2?.Vra,Vsp,Vgp,Vtp,R14.R13.Vt2,Vs0,Vs1,(30.R16.)R12.R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(31.Vra,)Vfc,(32.(1;.&40.))R15.(33.$29.)))")
(* [comment removed for export] *).

#[using="CLO LO HK1"] Lemma rfin_block : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W9 ()) "PstX,$1:.Pg3,$7.Pmsk,$12.PmZ,P,(1;.&40.)(<.(1;.&8.))Pt0,(1;.&40.)Pt1,(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pjunk,(34.(1;.&8.))P,(1<.Vsc,Vst,R=.)P,(;.$1=.(1>.R>.Vsc,)(19.$7.R=.))P,(1?.Vst,Vsc,R>.)P,(;.$12.R>.(20.(21.R10.R?.)))P,(1.(3.=R?.)(3.R?.(22.+2.+20.)))P,(24.VhRP,R12.R?.)P,(28.$29.R10.)P,(35.$29.R11.(5.Vspv,-90.)A1.VFRM,R8.)P,(2:.$29.R12.Vlo,(5.Vspv,-90.))P,(2;.(2<.Vst,Vlo,Vspv,)Vm,R13.)(2=.VR,Vo,(36.VR,R17.R16.R15.VK,)Vs,VQ,(2>.A:.VRR,R13.R12.(37.&40.(9.Vst,R16.))(30.(38.R15.))R11.R10.R?.R>.R=.R<.VF,(37.&40.+40:78.)Vfc,(32.(1;.&40.))R14.(33.$29.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros TR HA GM HM MR0 MRZ MIZ FRZ STZ PEZ.
  ddestruct (gmf_geom st stX sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds st m g3) as GB0.
  dpose (rmeta_slot_bounds stX mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
  ddestruct (lowbit_facts msk ltac:(lia)) as (k & Hk & LB).
  unfold ta_fin. riprefixT. unfold RR, rt1_regs.
  eapply evt_mono.
  { eapply (rfin_walk stX mZ g3 msk lo MRZ MSZ ltac:(lia) CLO); [| exact FRZ| exact STZ| unfold spv; lia| exact MIZ].
    rewrite unsigned_lit by lia. symmetry; exact ECONC. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1' & a2' & a3' & m' & k' & Hk' & LB' & -> & MU & WM & MI' & ST' & MR')).
  assert (k' = k) by (rewrite LB in LB'; apply Z.pow_inj_r in LB'; lia). subst k'.
  eapply (HK1 stX g3 msk k m'); try eassumption; try lia.
  eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
  cbn [ivs_covered]. split; [|split; [|exact I]].
  - intros x Hx. apply rta_fp_stack. unfold spv in *; lia.
  - intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
Qed.

#[using="TAF SC CLO LO HK1"] Lemma ravz_block : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W9 ()) "Ppc,$12.PstZ,$1:.Pg3,$7.PmZ,P,(1;.&40.)(<.(1;.&8.))Pt0,(1;.&40.)Pt1,(1;.&40.)Pa1',(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pjunk,(34.(1;.&8.))P,(0.(;.$12.R>.+409?4.)(;.$12.R>.+40:00.))P,(1<.Vsc,Vst,R>.)P,(;.$1=.(1>.R?.Vsc,)(19.$7.R>.))P,(1?.Vst,Vsc,R?.)P,(24.VhRP,R11.R?.)P,(28.$29.R10.)P,(35.$29.R11.(5.Vspv,-90.)A1.VFRM,R7.)P,(2:.$29.R12.Vlo,(5.Vspv,-90.))P,(2;.(2<.Vst,Vlo,Vspv,)Vm,R13.)(2=.VR,Vo,(39.VR,VK,Vbail,R16.R15.)Vs,VQ,(2>.A:.VRR,R13.R12.(37.&40.(9.Vst,R15.))R11.R10.R?.R>.R=.R<.R;.VF,(37.&40.R17.)Vfc,(32.(1;.&40.))R14.(33.$29.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros PC TR HA GM MRZ MIZ FRZ STZ PEZ.
  ddestruct (gmf_geom st stZ sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
  dpose (rmeta_slot_bounds stZ mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
  destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
  pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & _ & _).
  assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
  unfold ta_avz, activate_group.
  destruct (m_avail (get_meta_rec stZ g3) =? 0) eqn:AV0; [|unfold guard; apply rimplT_undef].
  apply Z.eqb_eq in AV0. unfold guard at 1. cbv beta.
  rewrite EM, Hmem. cbn [default].
  replace (group_active_idx stZ b) with (g_active_idx gh1).
  2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  set (act := mask_upto (g_active_idx gh1)). set (f := m_freed (get_meta_rec stZ g3)).
  destruct (Z.land f act =? 0) eqn:MZ; unfold guard; cbn [negb]; [apply rimplT_undef|].
  apply Z.eqb_neq in MZ.
  rewrite get_meta_rec_upd_same. cbn [m_sizeclass m_set_avail m_set_freed].
  assert (EMb : m_mem (get_meta_rec stZ g3) = Some b) by (rewrite EM; exact Hmem).
  assert (HG : bv_unsigned (Z_to_bv 64 (conc st g3)) = conc stZ g3) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).
  (* [comment removed for export] *)
  unfold RR.
  eapply (rimplT_evt o _ _ _ (fun ms' => exists a1x : word, ms' = MS (rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st g3)) a1x a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40a00) fc None mZ (seg_rom rsegs))).
  { destruct PC as [-> | ->].
    - eapply evt_mono. { eapply (ravz_pre_walk stZ mZ g3 sc MRZ MSZ AV0); [exact HG| exact MIZ]. } cbv beta. intros ms' ->. eexists. reflexivity.
    - apply evt_done. eexists. reflexivity. }
  intros ms0 [a1x ->].
  riprefixT. eapply evt_mono.
  { eapply (ravz_walk stZ mZ g3 b gh1 sc MRZ MSZ AV0 EMb Hgh1 AI1R RFZ MWZ MZ); [| exact SC| exact HG| exact MIZ].
    intros i. pose proof (taf_bnc _ _ TAF i) as B0. pose proof (tr_bounces _ _ _ TR i ltac:(lia)). lia. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5)).
  set (st4 := upd_meta g3 (fun r : meta => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) stZ) in *.
  set (st5 := decay_bounces (m_sizeclass (get_meta_rec stZ g3)) st4) in *.
  assert (TR4 : ta_rel sc st st4).
  { eapply ta_rel_trans; [exact TR|]. unfold st4. rewrite upd_meta_put. apply ta_rel_put_meta.
    - repeat split; reflexivity.
    - cbn [m_avail m_freed m_set_avail m_set_freed]. intros i Hi Hb. fold f.
      apply orb_prop in Hb. rewrite AV0, Z.bits_0. cbn [orb].
      destruct Hb as [Hb|Hb]; [rewrite Z.land_spec in Hb| rewrite Z.ldiff_spec in Hb]; apply andb_prop in Hb; destruct Hb as [Hb _]; exact Hb.
    - cbn [m_avail m_freed m_set_avail m_set_freed]. fold f. intros _ Hf.
      pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
      pose proof (ldiff_le f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
      pose proof (Z.ldiff_nonneg f act). lia. }
  assert (TR5 : ta_rel sc st st5).
  { eapply ta_rel_trans; [exact TR4|]. unfold st5. apply ta_rel_decay.
    pose proof (taf_bnc _ _ TAF (m_sizeclass (get_meta_rec stZ g3) - 7)). pose proof (tr_bounces _ _ _ TR4 (m_sizeclass (get_meta_rec stZ g3) - 7) ltac:(lia)). lia. }
  assert (FR5 : rw_cells rsegs m5 (spv + -144) (FRM junk)).
  { eapply rw_cells_transport; [exact FRZ| exact MU| exact WM|]. apply (disjoint_high rceil); [|unfold spv in *; lia].
    intros lo' hi' [E|[E|[]]]; inversion E; subst; rceilb; unfold RCTX in *; lia. }
  assert (ST5 : stk rsegs m5 lo (spv + -144)).
  { eapply stk_transport_disjoint; [exact STZ| exact MU| exact WM|]. apply (disjoint_high rceil); [|lia].
    intros lo' hi' [E|[E|[]]]; inversion E; subst; rceilb; unfold RCTX in *; lia. }
  eapply (rfin_block st5 g3 (Z.land f act) m5 t0 t1 a2' a3' a4' a5' a6' a7' junk);
    [exact TR5| | exact GM| | | exact MR5| exact MI5| exact FR5| exact ST5|].
  - unfold st5. rewrite active_decay. unfold st4. rewrite active_upd_meta. exact HA.
  - unfold st5. rewrite rec_decay. unfold st4. rewrite get_meta_rec_upd_same. reflexivity.
  - pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)). lia.
  - eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    + intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
    + intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.

#[using="TAF SC CLO LO HK1"] Lemma ract_block : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W9 ()) "PstY,$1:.Pg2,$7.Pmsk,$12.PmY,P,(1;.&40.)(<.(1;.&8.))Pt0,(1;.&40.)Pt1,(1;.&40.)Pa1',(1;.&40.)Pa2,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pjunk,(34.(1;.&8.))P,(1<.Vsc,Vst,R<.)P,(;.$1=.(1>.R=.Vsc,)(19.$7.R<.))P,(1?.Vst,Vsc,R=.)P,(;.$12.R=.(3:.(21.R?.R>.)))P,Pmn,$7.P,(;.$1=.(3;.(21.R11.R10.))(19.$7.R1.))(1?.Vst,Vsc,R2.)P,(3<.(;.$1=.(3;.(21.R11.R10.))(32.$7.)))P,(24.VhRP,R12.R?.)P,(28.$29.R10.)P,(35.$29.R11.(5.Vspv,-90.)A1.VFRM,R9.)P,(2:.$29.R12.Vlo,(5.Vspv,-90.))P,(2;.(2<.Vst,Vlo,Vspv,)Vm,R13.)(2=.VR,Vo,(3=.VR,Vsc,VK,Vbail,R17.R16.R15.)Vs,VQ,(2>.A:.VRR,R13.R12.(37.&40.(9.Vst,R16.))R11.R10.(30.(38.R15.))(37.&40.+2.)R?.R>.R=.VF,(37.&40.+409<<.)Vfc,(32.(1;.&40.))R14.(33.$29.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros TR HA GM HM GN NN MRY MIY FRY STY PEY.
  ddestruct (gmf_geom st stY sc g2 TR GM) as (MSY & RAY & RFY & MWY & EM & ELI & ESC & EFB & ECONC).
  dpose (rmeta_slot_bounds stY mY g2 MRY MSY) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
  destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
  pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & SCR0 & _).
  assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
  assert (EMb : m_mem (get_meta_rec stY g2) = Some b) by (rewrite EM; exact Hmem).
  assert (MSKR : 0 <= msk < 2^32) by (rewrite HM; exact RFY).
  assert (HG : bv_unsigned (Z_to_bv 64 (conc st g2)) = conc stY g2) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).
  unfold ta_act. rewrite EMb. cbn [default].
  replace (group_active_idx stY b) with (g_active_idx gh1).
  2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold RR.
  destruct (Z.land msk (mask_upto (g_active_idx gh1)) =? 0) eqn:ZR.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in ZR.
    destruct (m_next (get_meta_rec stY g2)) as [mn|] eqn:GNY; [|exfalso; apply NN; reflexivity].
    cbn [optr_eqb]. destruct (aptr_eqb mn g2) eqn:EQ; cbn [negb].
    + (* [comment removed for export] *)
      apply aptr_eqb_eq in EQ. subst mn.
      destruct (Z.eq_dec (m_sizeclass (get_meta_rec st g2)) 0) as [SCZ|SCNZ].
      * (* [comment removed for export] *)
        assert (AIE : g_active_idx gh1 = m_last_idx (get_meta_rec st g2)).
        { destruct AI1 as [E|[_ P]]; [rewrite E; apply SC0; exact SCZ| exfalso; exact (P g2 GMg SCZ)]. }
        assert (MZ : msk = 0).
        { apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
          destruct (Z.testbit msk i) eqn:Ti; [|reflexivity]. exfalso.
          assert (IL : i <= m_last_idx (get_meta_rec st g2)).
          { pose proof (tr_bits _ _ _ TR g2 i Hi) as TB. rewrite <- HM, Ti in TB. rewrite orb_true_r in TB. specialize (TB eq_refl).
            apply orb_prop in TB. destruct TB as [TB|TB]; [exact (gmf_abits _ _ _ GM i Hi TB)| exact (gmf_fbits _ _ _ GM i Hi TB)]. }
          assert (TB2 : Z.testbit (Z.land msk (mask_upto (g_active_idx gh1))) i = true).
          { rewrite Z.land_spec, Ti. unfold mask_upto. replace (2 ^ (g_active_idx gh1 + 1) - 1) with (Z.ones (g_active_idx gh1 + 1)) by (rewrite Z.ones_equiv; lia).
            rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. apply Z.ltb_lt. lia. }
          rewrite ZR, Z.bits_0 in TB2. discriminate. }
        (* [comment removed for export] *)
        cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai.
        destruct (m_avail (get_meta_rec stY g2) =? 0); unfold guard; [|apply rimplT_undef].
        cbv beta. rewrite <- HM, MZ, Z.land_0_l. cbn [Z.eqb negb]. apply rimplT_undef.
      * (* [comment removed for export] *)
        destruct (m_avail (get_meta_rec stY g2) =? 0) eqn:AV0.
        2:{ cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai, AV0. unfold guard. apply rimplT_undef. }
        apply Z.eqb_eq in AV0.
        assert (SCY : 1 <= m_sizeclass (get_meta_rec stY g2) < 48) by (rewrite ESC; pose proof (gmf_sc48 _ _ _ GM); lia).
        rewrite <- ECONC. riprefixT. eapply evt_mono.
        { eapply (ract_span_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R); [exact ZR| exact GNY| exact MWY| exact SCY| | rewrite GM1; exact GMg| exact AV0| exact MIY].
          intros o' Ho'. rewrite (tr_get_shadow _ _ _ _ TR). apply UNK. exact Ho'. }
        cbv beta. (intros ms' dd_H; ddestruct dd_H as (t0' & t1' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5)).
        cbv zeta iota beta.
        match goal with |- rimplT _ (ta_avz _ _ ?st3 _) _ _ _ => set (stG := st3) in * end.
        assert (TRG : ta_rel sc st stG).
        { eapply ta_rel_trans; [exact TR|]. apply ta_rel_set_gai.
          - apply land31_range.
          - intros h g' Hh Hg'. rewrite Hgh1 in Hh. inversion Hh; subst h. rewrite GM1 in Hg'. rewrite GMg in Hg'. inversion Hg'; subst g'. lia. }
        rewrite (tr_conc _ _ _ g2 TR).
        eapply (ravz_block 0x40a00 stG g2 m5); [right; reflexivity| exact TRG| | exact GM| exact MR5| exact MI5| | |].
        -- unfold stG. rewrite active_set_gai. exact HA.
        -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply (disjoint_high rceil); [|unfold spv in *; lia].
           dpose (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; rceilb; lia.
        -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply (disjoint_high rceil); [|lia].
           dpose (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; rceilb; lia.
        -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
           cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply (rta_fp_grp st lo spv x b gh Hgh). rewrite <- (tr_conc _ _ _ b TR). lia.
    + (* [comment removed for export] *)
      assert (NE : mn <> g2) by (intros ->; rewrite (proj2 (aptr_eqb_eq g2 g2) eq_refl) in EQ; discriminate).
      pose proof (GN mn eq_refl) as GMn.
      ddestruct (gmf_geom st stY sc mn TR GMn) as (MSn & _ & _ & _ & _ & _ & _ & _ & ECONCn).
      rewrite <- ECONC. riprefixT. eapply evt_mono.
      { eapply (ract_next_walk stY mY g2 b gh1 sc msk MRY MSY SC EMb Hgh1 AI1R); [exact ZR| exact GNY| exact NE| exact MSn| exact MIY]. }
      cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1'' & a2' & a3' & a4' & m5 & -> & MU & WM & MI5 & MR5)).
      assert (TRN : ta_rel sc st (set_active sc (Some mn) stY)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
      rewrite ECONCn.
      eapply (ravz_block 0x409f4 (set_active sc (Some mn) stY) mn m5); [left; reflexivity| exact TRN| | exact GMn| exact MR5| exact MI5| | |].
      -- rewrite active_set_active, Z.eqb_refl. reflexivity.
      -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply (disjoint_high rceil); [|unfold spv in *; lia].
         intros lo' hi' [E|[]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
      -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply (disjoint_high rceil); [|lia].
         intros lo' hi' [E|[]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
      -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
         cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
  - (* [comment removed for export] *)
    apply Z.eqb_neq in ZR.
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (ract_skip_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R MSKR); [exact ZR| exact MIY]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1'' & a2' & a3' & a4' & ->)). rewrite ECONC.
    eapply (ravz_block 0x409f4 stY g2 mY); [left; reflexivity| ..]; eassumption.
Qed.

(* [comment removed for export] *)
Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

#[using="TAF SC CLO LO HK1"] Lemma rm_block : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W9 ()) "PstX,$1:.Pg1,$7.PmX,P,(1;.&40.)(<.(1;.&8.))PP,P,$7.SpPt0,(1;.&40.)Pt1,(1;.&40.)Pa1',(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)Pjunk,(34.(1;.&8.))P,(1<.Vsc,Vst,R>.)P,(;.$1=.(1>.R?.Vsc,)(19.$7.R>.))P,(3>.R10.R=.)P,A1.R>.R10.P,(24.VhRP,R12.R10.)P,(28.$29.R11.)P,(35.$29.R12.(5.Vspv,-90.)A1.VFRM,R7.)P,(2:.$29.R13.Vlo,(5.Vspv,-90.))P,(2;.(2<.Vst,Vlo,Vspv,)Vm,R14.)(2=.VR,Vo,(3?.VR,Vsc,VK,Vbail,R17.R16.)Vs,VQ,(2>.A:.VRR,R13.R12.(37.&40.(9.Vst,R16.))R11.R10.R?.R>.R=.R<.R;.VF,(37.&40.+409:0.)Vfc,(32.(1;.&40.))R15.(33.$29.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until junk. intros TR HA NC P1 MRX MIX FRX STX PEX.
  ddestruct (NC g1 P1) as (GM & mn & GN1 & Pmn).
  ddestruct (gmf_geom st stX sc g1 TR GM) as (MSX & RAX & RFX & MWX & EM & ELI & ESC & EFB & ECONC).
  dpose (rmeta_slot_bounds stX mX g1 MRX MSX) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  pose proof (gmf_mw _ _ _ GM) as (LI0 & FB0 & SCR0 & _).
  unfold ta_m, RR.
  set (f := m_freed (get_meta_rec stX g1)).
  destruct ((f =? mask_upto (m_last_idx (get_meta_rec stX g1))) && negb (m_freeable (get_meta_rec stX g1) =? 0)) eqn:FSK.
  - (* [comment removed for export] *)
    pose proof FSK as FSK'. apply andb_prop in FSK'. destruct FSK' as [FE FB]. apply Z.eqb_eq in FE. apply Bool.negb_true_iff in FB. apply Z.eqb_neq in FB.
    rewrite GN1.
    ddestruct (NC mn Pmn) as (GMn & mn2 & GN2 & Pmn2).
    ddestruct (gmf_geom st stX sc mn TR GMn) as (MSn & RAn & RFn & MWn & EMn & _ & _ & _ & ECONCn).
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_skip_walk stX mX g1 sc MRX MSX SC RFX MWX); [exact FSK| exact GN1| exact MSn| exact RFn| exact MIX]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1'' & a2' & m5 & -> & MU & WM & MI5 & MR5)).
    assert (TRN : ta_rel sc st (set_active sc (Some mn) stX)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
    rewrite ECONCn.
    eapply (ract_block (set_active sc (Some mn) stX) mn (m_freed (get_meta_rec stX mn)) m5); try eassumption.
    + rewrite active_set_active, Z.eqb_refl. reflexivity.
    + reflexivity.
    + intros q Hq. rewrite rec_set_active in Hq. rewrite GN2 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn2)).
    + rewrite rec_set_active, GN2. discriminate.
    + eapply rw_cells_transport; [exact FRX| exact MU| exact WM|]. apply (disjoint_high rceil); [|unfold spv in *; lia].
      intros lo' hi' [E|[]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
    + eapply stk_transport_disjoint; [exact STX| exact MU| exact WM|]. apply (disjoint_high rceil); [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
    + eapply rpres_except_trans; [exact PEX|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
  - (* [comment removed for export] *)
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_act_walk stX mX g1 sc MRX MSX RFX MWX); [exact FSK| exact MIX]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1'' & a2' & ->)). rewrite ECONC.
    eapply (ract_block stX g1 f mX); try eassumption.
    + reflexivity.
    + intros q Hq. rewrite GN1 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn)).
    + rewrite GN1. discriminate.
Qed.

(* [comment removed for export] *)
#[using="TAF SC CLO LO HK1"] Lemma rta_phase : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W9 ()) "Pt0,(1;.&40.)Pt1,(1;.&40.)Pa0,(1;.&40.)Pa2,(1;.&40.)Pa3,(1;.&40.)Pa4,(1;.&40.)Pa5,(1;.&40.)Pa6,(1;.&40.)Pa7,(1;.&40.)P,(;.(1;.&40.)R7.(37.&40.Vsc,))P,(24.VhRP,Vst,Vm,)P,(28.$29.Vm,)P,(2:.$29.Vm,Vlo,Vspv,)P,Pst1,$1:.Pm',P,(1;.&40.)(<.(1;.&8.))Pt0',(1;.&40.)Pt1',(1;.&40.)Pa0',(1;.&40.)Pa1',(1;.&40.)Pa2',(1;.&40.)Pa3',(1;.&40.)Pa4',(1;.&40.)Pa5',(1;.&40.)Pa6',(1;.&40.)Pa7',(1;.&40.)Pjunk,(34.(1;.&8.))P,(40.Vsc,Vst,R=.)P,(1<.Vsc,Vst,R>.)P,(;.$1=.(1>.R?.Vsc,)(32.$7.))P,(24.VhRP,R10.R?.)P,(28.$29.R10.)P,(35.$29.R11.(5.Vspv,-90.)A1.VFRM,R6.)P,(2:.$29.R12.Vlo,(5.Vspv,-90.))P,(2;.(2<.Vst,Vlo,Vspv,)Vm,R13.)(2=.VR,Vo,A2.VK,R15.=Vs,VQ,(2>.A:.VRR,R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.VF,(37.&40.+40:;8.)Vfc,(32.(1;.&40.))R14.(33.$29.)))(2=.VR,Vo,(41.VR,Vsc,Vst,VK,Vbail,)Vs,VQ,(2>.(2?.Vra,Vsp,Vgp,Vtp,R>.R=.Vt2,Vs0,Vs1,R<.Va1,R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(37.&40.$42.)Vfc,(32.(1;.&40.))Vm,(33.$29.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until a7. intros A0 MR MI ST HK0.
  assert (AMS : forall g, active st sc = Some g -> meta_slot st g) by (intros g Hg; exact (gmf_slot _ _ _ (proj1 (taf_head _ _ TAF g Hg)))).
  riprefixT. eapply evt_mono.
  { eapply (ras_entry_walk st m sc lo MR SC CLO AMS); [exact A0| exact ST| exact LO| exact MI]. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1x & m1 & junk & -> & FR1 & ST1 & MU1 & WM1 & MI1 & MR1)).
  assert (PE1 : rpres_except (rta_fp st lo spv) m m1).
  { eapply rpres_except_of_munch_cov; [exact MU1| exact WM1|]. cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_stack. unfold spv; lia. }
  clear MU1 WM1.
  rewrite (try_avail_eq sc K bail st).
  destruct (active st sc) as [g|] eqn:HA.
  2:{ (* [comment removed for export] *)
      eapply (HK0 st m1); [| apply ta_rel_refl| exact HA| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      unfold ta_fail, try_avail. rewrite HA. reflexivity. }
  destruct (taf_head _ _ TAF g HA) as [GM GSC].
  pose proof (gmf_slot _ _ _ GM) as MSg. pose proof (gmf_avail _ _ _ GM) as RAg. pose proof (gmf_freed _ _ _ GM) as RFg.
  dpose (rmeta_slot_bounds st m1 g MR1 MSg) as (Gpos & GC & GI & _ & _).
  unfold pw. cbn [oconc]. unfold wz.
  destruct (m_avail (get_meta_rec st g) =? 0) eqn:AV; cbn [negb].
  2:{ (* [comment removed for export] *)
      apply Z.eqb_neq in AV.
      riprefixT. eapply evt_mono.
      { eapply (rt1_fin_walk st m1 g sc MR1 MSg RAg); [exact AV| exact MI1]. }
      cbv beta. intros ms' ->.
      eapply (rfin_block st g (m_avail (get_meta_rec st g)) m1); [apply ta_rel_refl| exact HA| exact GM| reflexivity| lia| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1]. }
  apply Z.eqb_eq in AV.
  destruct (gmf_links _ _ _ GM) as (nx & pv & GN & GP).
  destruct (taf_next _ _ TAF g nx GM GN) as (GMn & SCn & PRn).
  destruct (taf_prev _ _ TAF g pv GM GP) as (GMp & NXp).
  destruct (m_freed (get_meta_rec st g) =? 0) eqn:FZ.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in FZ.
    riprefixT. eapply evt_mono.
    { eapply (rt1_deq_walk st m1 g sc MR1 MSg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. intros ms' ->.
    destruct (decide (nx = g)) as [->|NEn].
    + (* [comment removed for export] *)
      rewrite (dequeue_self_eq sc g st GN).
      replace (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (@None aptr)
        by (change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc); rewrite active_set_active, Z.eqb_refl; reflexivity).
      cbn [Z.eqb].
      riprefixT. eapply evt_mono.
      { eapply (rdeq_self_walk st m1 g sc MR1 MSg SC); [exact GN| exact MI1]. }
      cbv beta. (intros ms' dd_H; ddestruct dd_H as (m2 & -> & MU & WM & MI2 & MR2)).
      eapply (HK0 _ m2).
      * unfold ta_fail. rewrite (try_avail_eq sc kS bS st), HA, AV, FZ. cbn [Z.eqb negb].
        rewrite (dequeue_self_eq sc g st GN).
        change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
        rewrite active_set_active, Z.eqb_refl. reflexivity.
      * eapply ta_rel_trans; [apply ta_rel_set_active|]. unfold clr.
        replace (get_meta_rec st g) with (get_meta_rec (set_active sc None st) g) by reflexivity. apply ta_rel_put_links.
      * change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
        rewrite active_set_active, Z.eqb_refl. reflexivity.
      * exact MR2.
      * exact MI2.
      * eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply (disjoint_high rceil); [|unfold spv in *; lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply (disjoint_high rceil); [|lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|exact I]]; intros x Hx; [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]].
    + (* [comment removed for export] *)
      assert (NEp : pv <> g).
      { intros ->. rewrite NXp in GN. inversion GN. subst nx. apply NEn. reflexivity. }
      rewrite (dequeue_other_eq sc g nx pv st GN GP NEn NEp HA). cbv zeta.
      match goal with |- context [active ?stq sc] => set (st1 := stq) in * end.
      assert (HA1 : active st1 sc = Some nx).
      { unfold st1. unfold active, put_meta, set_metas, set_active, upd_ctx. cbn [s_ctx ctx c_active set_active_map]. apply lookup_insert_eq. }
      rewrite HA1.
      pose proof (gmf_slot _ _ _ GMn) as MSn. pose proof (gmf_slot _ _ _ GMp) as MSp.
      riprefixT. eapply evt_mono.
      { eapply (rdeq_other_walk st m1 g sc MR1 MSg SC HA); [exact GN| exact GP| exact NEn| exact NEp| exact MSn| exact MSp| exact MI1]. }
      cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1'' & m2 & -> & MU & WM & MI2 & MR2)). fold st1 in MR2.
      assert (TR1 : ta_rel sc st st1).
      { unfold st1.
        lazymatch goal with |- ta_rel _ _ (put_meta _ _ ?sC) =>
          lazymatch sC with set_active _ _ ?sB =>
            lazymatch sB with put_meta _ _ ?sA =>
              apply (ta_rel_trans sc st sC); [apply (ta_rel_trans sc st sB); [apply (ta_rel_trans sc st sA); [apply ta_rel_put_next| apply ta_rel_put_prev] | apply ta_rel_set_active] |];
              unfold clr; replace (get_meta_rec st g) with (get_meta_rec sC g); [apply ta_rel_put_links|]
            end end end.
        rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
        rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
      (* [comment removed for export] *)
      assert (REC1 : forall q, q <> g -> get_meta_rec st1 q =
                 if aptr_eqb q nx then m_set_prev (Some pv) (if aptr_eqb nx pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st nx)
                 else if aptr_eqb q pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st q).
      { intros q Hq. unfold st1. rewrite (get_meta_rec_put_other _ g) by exact Hq. rewrite rec_set_active.
        rewrite get_meta_rec_put. destruct (aptr_eqb q nx) eqn:E1.
        - apply aptr_eqb_eq in E1. subst q. f_equal. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv) eqn:E2; [apply aptr_eqb_eq in E2; subst; reflexivity| reflexivity].
        - rewrite get_meta_rec_put. reflexivity. }
      eapply (rm_block st1 nx m2 (fun q => gmf st sc q /\ q <> g)); [exact TR1| exact HA1| | split; [exact GMn| exact NEn] | exact MR2| exact MI2| | |].
      * intros q [GMq NEq]. split; [exact GMq|]. rewrite (REC1 q NEq).
        destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP). destruct (taf_next _ _ TAF q qn GMq QN) as (GMqn & _ & PRqn).
        destruct (aptr_eqb q nx) eqn:E1.
        -- apply aptr_eqb_eq in E1. subst q. cbn [m_next m_set_prev].
           destruct (aptr_eqb nx pv) eqn:E2.
           ++ exists nx. cbn. split; [reflexivity|]. split; [exact GMn| exact NEn].
           ++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->.
              rewrite PRqn in GP. inversion GP. subst pv. rewrite (proj2 (aptr_eqb_eq nx nx) eq_refl) in E2. discriminate.
        -- destruct (aptr_eqb q pv) eqn:E2.
           ++ apply aptr_eqb_eq in E2. subst q. cbn. exists nx. split; [reflexivity|]. split; [exact GMn| exact NEn].
           ++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->. rewrite PRqn in GP. inversion GP. subst pv.
              rewrite (proj2 (aptr_eqb_eq q q) eq_refl) in E2. discriminate.
      * eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply (disjoint_high rceil); [|unfold spv in *; lia].
        dpose (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). dpose (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply (disjoint_high rceil); [|lia].
        dpose (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). dpose (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]]; intros x Hx;
          [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]| eapply rta_fp_meta; [exact MSp| lia]| eapply rta_fp_meta; [exact MSn| lia]].
  - (* [comment removed for export] *)
    apply Z.eqb_neq in FZ. rewrite GN.
    riprefixT. eapply evt_mono.
    { eapply (rt1_next_walk st m1 g sc MR1 MSg SC RFg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (m2 & -> & MU & WM & MI2 & MR2)). rewrite GN in MR2 |- *. unfold pw. cbn [oconc]. unfold wz.
    eapply (rm_block (set_active sc (Some nx) st) nx m2 (gmf st sc)); [| | | exact GMn| exact MR2| exact MI2| | |].
    + apply ta_rel_set_active.
    + rewrite active_set_active, Z.eqb_refl. reflexivity.
    + intros q GMq. split; [exact GMq|]. rewrite rec_set_active. destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP).
      exists qn. split; [exact QN|]. exact (proj1 (taf_next _ _ TAF q qn GMq QN)).
    + eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply (disjoint_high rceil); [|unfold spv in *; lia].
      intros lo' hi' [E|[]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
    + eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply (disjoint_high rceil); [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; rceilb; unfold RCTX in *; lia.
    + eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.
End PHASE.


End RP_1.

(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export Malloc_fp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_enframe HP_RMallocKit_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RMalloc_fp () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ranges_free"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr8"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr16"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le2"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.wr32"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.enframe_at"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_enframe.renframe_tail_mem"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_enframe.renframe_off_mem"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.unk_agree"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.grp_hdr_cov"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_enframe.rdv"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.pans_mem"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_cells"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.ralloc_fp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.new_reg_addr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.free_slot_addr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.grp_hdr_addr"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rfresh_addr"; "RP_1.rmalloc_fp"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_fp.slot_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_stride"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_mem"].


Notation RMFACTS := (@MFACTS_g ref_reserved).

(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59264726735.600000;S1b1n2Hn2H0". (* [comment removed for export] *)
#[using="Type"] Lemma rreserved_disjoint2 : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pb,$0.Pn,$0.P,(1.$2.(3.$4.R2.R1.)$5.)P,(6.=R2.)(7.(8.(9.(:.R4.R3.)+10000.)(9.+48000.R4.))(8.(9.(:.R4.R3.)+48000.)(9.+7>000.R4.)))")
(* [comment removed for export] *).
Proof. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof.
  intros Hf Hs.
  assert (E : forall (a b : aptr) x y s, fst a = fst b -> snd a <> snd b ->
     wr8 a x (wr8 b y s) = set_shadow (<[fst a := mkShadow (<[snd a := (Z.land x 255, s_tick s)]> (<[snd b := (Z.land y 255, s_tick s)]> (r_cells (get_shadow s (fst a))))) (r_hav (get_shadow s (fst a))) (r_havp (get_shadow s (fst a)))]> (s_shadow s)) s).
  { intros a b x y s Ef Ns. unfold wr8 at 1. unfold upd_shadow. rewrite Ef, get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
    rewrite s_shadow_wr8, <- Ef. change (s_tick (wr8 b y s)) with (s_tick s). rewrite insert_insert_eq. reflexivity. }
  rewrite (E p q), (E q p) by (congruence || (symmetry; congruence) || auto). rewrite Hf.
  rewrite (insert_insert_ne _ (snd p) (snd q)) by exact Hs. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pb',(;.$<.$0.)Pgh,$=.P,(1.(>.$=.)(?.(;.$<.$0.)$=.(10.$11.(12.$<.$13.$0.$14.)(15.$<.$13.$16.$0.$14.$17.)$=.)(18.$11.(12.$<.$13.$0.$14.)(15.$<.$13.$16.$0.$14.$17.)$=.)R2.(19.Vst2,))(1:.$=.R1.))P,(1.$<.(1;.$<.$0.R3.)(1;.$<.$0.Vb,))(8.(9.(:.(1<.$<.$0.R4.)+9.)(1=.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))+4.))(9.(1=.(:.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))Vstride,)+4.)(1<.$<.$0.R4.)))")
(* [comment removed for export] *).
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

#[using="Hr"] Lemma rconc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18588176547.28L51792621753.2800000S012S3st21b1k3off2mr6stride1B2P02K03S16S3st21b1k3off2mr6stride1B2P02K0". (* [comment removed for export] *)
#[using="b off B P0 K0 S16"] Lemma rsk_nonneg : 0 <= stride * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L10336122861.44L46170967393.3900000]01MS3st21b1k3off2mr6stride1B2P02K01o2Ho2b'2Hf2H0S3st21b1r1k3off2mr6stride1B2P02B02K04SPAN1o2Ho1H". (* [comment removed for export] *)
#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr8_rep : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pstx,$1?.Pmx,P,(20.&40.)(>.(20.&8.))Po,$0.Pv,$0.P,(21.VhRP,R4.R3.)P,(22.R5.)P,(1.(10.$<.$13.$16.$23.)(24.R6.)(24.Vst2,))P,(1.(10.$11.(12.$<.$13.$0.$14.)(15.$<.$13.$16.$0.$14.$17.)$=.)(19.R7.)(19.Vst2,))P,(7.(9.(1=.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))+4.)R6.)(6.R6.(1=.(:.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))Vstride,)+4.)))P,(7.(9.=R6.)(6.R6.+100.))(7.(21.VhRP,(25.(26.$<.$0.(1;.$<.$0.Vb,)R8.)R7.R:.)(27.R9.(28.(:.(29.Vr,)R8.))(2:.(20.&8.)(2;.R7.)(2<.(20.&8.)))))(22.(25.(26.$<.$0.(1;.$<.$0.Vb,)R8.)R7.R:.)))")
(* [comment removed for export] *).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr8; exact TKx].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L62034908776.40L64362796846.45L8943377619.40 00000\01M026S3st21b1r1k3off2mr6stride1B2P02K04SPAN1o3Ho2S3st21b1k3off2mr6stride1B2P02K01o2Ho2b'2Hf2H03Ho2S3st21b1k3off2mr6stride1B2P02B02K01o2Ho1H". (* [comment removed for export] *)
#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr16_rep : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pstx,$1?.Pmx,P,(20.&40.)(>.(20.&8.))Po,$0.Pv,$0.P,(21.VhRP,R4.R3.)P,(22.R5.)P,(1.(10.$<.$13.$16.$23.)(24.R6.)(24.Vst2,))P,(1.(10.$11.(12.$<.$13.$0.$14.)(15.$<.$13.$16.$0.$14.$17.)$=.)(19.R7.)(19.Vst2,))P,(9.(1=.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))+4.)R6.)P,(9.(:.R7.+2.)(1=.(:.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))Vstride,)+4.))P,(7.(9.=R7.)(6.R7.+10000.))(7.(21.VhRP,(2=.(26.$<.$0.(1;.$<.$0.Vb,)R9.)R8.R;.)(27.R:.(28.(:.(29.Vr,)R9.))(2>.(2?.R8.))))(22.(2=.(26.$<.$0.(1;.$<.$0.Vb,)R9.)R8.R;.)))")
(* [comment removed for export] *).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho2 Hv. pose proof rsk_nonneg.
  split; [|apply ticks_ok_wr16; exact TKx].
  apply (rmrep_wr16 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L28745634254.45L45564601928.40L8943377619.40 00000a01M026S3st21b1k3off2mr6stride1B2P02K01o2Ho2b'2Hf2H03Ho4S3st21b1r1k3off2mr6stride1B2P02K04SPAN1o3Ho4S3st21b1k3off2mr6stride1B2P02B02K01o2Ho1H". (* [comment removed for export] *)
#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr32_rep : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pstx,$1?.Pmx,P,(20.&40.)(>.(20.&8.))Po,$0.Pv,$0.P,(21.VhRP,R4.R3.)P,(22.R5.)P,(1.(10.$<.$13.$16.$23.)(24.R6.)(24.Vst2,))P,(1.(10.$11.(12.$<.$13.$0.$14.)(15.$<.$13.$16.$0.$14.$17.)$=.)(19.R7.)(19.Vst2,))P,(9.(1=.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))+4.)R6.)P,(9.(:.R7.+4.)(1=.(:.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))Vstride,)+4.))P,(7.(9.=R7.)(6.R7.(30.+2.+20.)))(7.(21.VhRP,(31.(26.$<.$0.(1;.$<.$0.Vb,)R9.)R8.R;.)(27.R:.(28.(:.(29.Vr,)R9.))(32.(2?.R8.))))(22.(31.(26.$<.$0.(1;.$<.$0.Vb,)R9.)R8.R;.)))")
(* [comment removed for export] *).
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof rsk_nonneg.
  apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L66153604003.36L9307245548.36 00000\01BS3st21b1k3off2mr6stride1B2P02K01p1q2Hf2H02H1S3st21b1k3off2mr6stride1B2P02K01p1q2Hf". (* [comment removed for export] *)
#[using="st2 g b k off mr stride B P0 K0"] Lemma wr16_wr8_comm p q v w st : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "P,(1.$<.(1;.$<.$0.O5.)(1;.$<.$0.O4.))P,(33.(1.$0.(1<.$<.$0.O4.)(1<.$<.$0.O5.)))P,(33.(1.$0.(1<.$<.$0.O4.)(:.(1<.$<.$0.O5.)+1.)))(1.$1?.(25.O4.O2.(2=.O5.O3.O1.))(2=.O5.O3.(25.O4.O2.O1.)))")
(* [comment removed for export] *).
Proof.
  intros Hf H0 H1. unfold wr16.
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L2457154115.35 L51950852914.35L57151117299.35L66153604003.35L9307245548.35 00000Y01B01k02T03:S3st21b1k3off2mr6stride1B2P02K01p1q2Hf2H1S3st21b1k3off2mr6stride1B2P02K01p1q2Hf2H1S3st21b1k3off2mr6stride1B2P02K01p1q2Hf2H1S3st21b1k3off2mr6stride1B2P02K01p1q2Hf2H1S3st21b1k3off2mr6stride1B2P02K01p1q2Hf". (* [comment removed for export] *)
#[using="st2 g b k off mr stride B P0 K0"] Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
  wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof.
  intros Hf H1. unfold wr32.
  rewrite (wr8_comm q (aadd p 3)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 2)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q (aadd p 1)) by (unfold aadd; cbn; lia || auto).
  rewrite (wr8_comm q p) by (auto || lia). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00c0?L10908052872.33L12523728919.39L13573381461.35L13914994076.46L15868994903.40L16224964385.37L16365402129.31L1687920188.48 L17939814727.42L17939817200.33L20389260129.37L22161312990.38L22671763568.56L2359842792.44 L24486973918.64L27465610844.31L28153479485.40L29315430951.61L32886679841.37L33066566632.42L33066580063.33L33549961934.50L35459439440.58L39131325723.42L40040186195.61L40134639569.56L45386294671.31L45437569413.40L45437731729.62L45437782784.31L46062788656.37L51118273987.62L51792416230.61L54254711694.40L5512517439.56 L55763663808.54L55996951438.39L56606127779.54L57020063676.54L57020096444.48L57020458249.35L5894134728.44 L59087287440.58L6181677823.54 L62625299421.31L62625332189.54L62625544536.40L6440626553.58 L65502243693.39L67710181982.45L7222656071.61 00000[01=02103003R04604U05`06[07>07b08D08l09\0:D0:c0;E0;m0<Q0=A0=`0>]0?W0@<0@d0AT0B30C30D70DZ0EA0FF0Fn0GP0H<0Hh0I[0JC0Jk0KS0L20Lb0M\0NK0Nj0OR0P40P\0Q>0Qf0RNS3st21b1k3off2mr6stride1B2P02K04OFF03Q162SKS3st21b1k3off2mr6stride1B2P02K02poS3st21b1k1n3off2mr6stride1B2P02K03S164OFF02N03FIT2SKS3st21b1r1k1n3off2mr6stride1B2P02K04OFF03FIT2CB2po3Epo3rsv4ErsvS3st21b1k3off2mr6stride1B2P02K02poS3st21b1r1k3off2mr6stride1B2P02K02CBS3st21b1k3off2mr6stride1B2P02K0S3st21b1r1k1n3off2mr6stride1B2P02K04OFF02N02CB2SK2po3Epo2Eq3rsv4Ersv3RSV2NES3st21b1r1k1n3off2mr6stride1B2P02K03S162N03FIT2CB2SK2po3EpoS3st21b1k3off2mr6stride1B2P02K03S16S3st21b1r1k3off2mr6stride1B2P02K02CBS3st21b1k3off2mr6stride1B2P02K02poS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1r1k3off2mr6stride1B2P02K04OFF02CB2po3EpoS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k3off2mr6stride1B2P02K0S3st21b1k3off2mr6stride1B2P02K02poS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1r1k3off2mr6stride1B2P02K02CBS3st21b1r1k3off2mr6stride1B2P02K04OFF02CB2po3EpoS3st21b1k3off2mr6stride1B2P02K0S3st21b1r1k1n3off2mr6stride1B2P02K02CB2SK2po3Epo3rsv4Ersv3RSVS3st21b1r1k1n3off2mr6stride1B2P02K02CB2po3Epo3rsv4Ersv3RSVS3st21b1k3off2mr6stride1B2P02K02po2QBS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k1n3off2mr6stride1B2P02K03S312po3rsv3RSVS3st21b1k3off2mr6stride1B2P02K0S3st21b1r1k1n3off2mr6stride1B2P02K03S164OFF02N03FIT2CB2SK2po3EpoS3st21b1r1k1n3off2mr6stride1B2P02K03S162N02CB2SK2po3Epo3rsv4Ersv3RSVS3st21b1k3off2mr6stride1B2P02K03S16S3st21b1r1k3off2mr6stride1B2P02K02CB2poS3st21b1r1k1n3off2mr6stride1B2P02K02CB2SK2po3Epo3rsv4Ersv3RSV2r22R21HS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k3off2mr6stride1B2P02K02poS3st21b1k1n3off2mr6stride1B2P02K03S162po3rsvS3st21b1k1n3off2mr6stride1B2P02K03S162po3rsvS3st21b1r1k3off2mr6stride1B2P02K04OFF02CB2SK2po3EpoS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k3off2mr6stride1B2P02K0S3st21b1r1k3off2mr6stride1B2P02K04OFF02CB2po3EpoS3st21b1r1k1n3off2mr6stride1B2P02K02CB2po3Epo3rsv4Ersv3RSVS3st21b1k1n3off2mr6stride1B2P02K02po3rsv3RSV2GTS3st21b1k3off2mr6stride1B2P02K0S3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k3off2mr6stride1B2P02K02poS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k3off2mr6stride1B2P02K02poS3st21b1k1n3off2mr6stride1B2P02K02po3rsvS3st21b1k1n3off2mr6stride1B2P02K02po3rsv". (* [comment removed for export] *)
#[using="r MR TK Hmem Hr Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16"] Lemma renframe_mrep : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Zres,(;.$1?.$11.)(34.Vst2,Vg,Vk,Vn,Voff,)(7.(21.VhRP,(1;.$1?.$11.R1.)(35.(36.Vm4,VP0,Voff,)(:.VP0,(1>.+10.Voff,))(1=.(:.VP0,Vstride,)+4.)Vn,Vk,(37.(1=.(1=.(:.VP0,(1>.+10.Voff,))VB,)+10.)+10.)))(7.(22.(1;.$1?.$11.R1.))(7.(1.$0.(38.Vst2,(1<.$1?.$11.R1.))(:.VP0,(1>.+10.Voff,)))(7.(1.$<.(1;.$<.$0.(1<.$1?.$11.R1.))(1;.$<.$0.Vb,))(1.$0.(1<.$<.$0.(1<.$1?.$11.R1.))(:.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vk,))(1>.+10.Voff,)))))))")
(* [comment removed for export] *).
Proof.
  pose proof rconc_b as CB. pose proof rsk_nonneg as SK.
  cbv zeta. unfold enframe_at. fold mr. fold stride. rewrite Hmem. cbn [default from_option id fst snd].
  unfold aadd. cbn [fst snd].
  (* [comment removed for export] *)
  set (stC := if negb (off =? 0) then _ else _).
  assert (PRE : rmrep (fst stC) (renframe_off_mem m4 P0 off) /\ ticks_ok (fst stC)
                /\ snd stC = (fst b, snd b + (UNIT + stride * k) + UNIT * off)
                /\ s_regions (fst stC) = s_regions st2 /\ s_groups (fst stC) = s_groups st2
                /\ (forall q, conc (fst stC) q = conc st2 q)).
  { subst stC. unfold renframe_off_mem. destruct (Z.eqb_spec off 0) as [E|NE]; cbn [negb fst snd].
    - subst off. rewrite Z.mul_0_r, Z.add_0_r.
      split; [exact MR|]. split; [exact TK|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity.
    - (* [comment removed for export] *)
      rewrite (wr16_wr8_comm (fst b, snd b + (UNIT + stride * k) + -2) (fst b, snd b + (UNIT + stride * k) + -3)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep st2 m4 (snd b + (UNIT + stride * k) + -3) 224 MR TK eq_refl eq_refl) as [M1 T1]; [unfold UNIT; lia| lia|].
      destruct (rwr16_rep _ _ (snd b + (UNIT + stride * k) + -2) off M1 T1 eq_refl eq_refl) as [M2 T2]; [unfold UNIT; lia| unfold UNIT; lia| lia|].
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + UNIT * off + -4) 0 M2 T2 eq_refl eq_refl) as [M3 T3]; [unfold UNIT; lia| lia|].
      unfold UNIT in *.
      replace (P0 - 2) with (r_base r + (snd b + (16 + stride * k) + -2)) by (unfold P0; lia).
      replace (P0 - 3) with (r_base r + (snd b + (16 + stride * k) + -3)) by (unfold P0; lia).
      replace (P0 + 16 * off - 4) with (r_base r + (snd b + (16 + stride * k) + 16 * off + -4)) by (unfold P0; lia).
      split; [exact M3|]. split; [exact T3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros; reflexivity. }
  clearbody stC. destruct stC as [stc p']. cbn [fst snd] in PRE. ddestruct PRE as (MC & TC & -> & ERc & EGc & CONCc).
  cbn [fst snd].
  unfold renframe_tail_mem. cbv zeta.
  (* [comment removed for export] *)
  set (po := snd b + (UNIT + stride * k) + UNIT * off).
  assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
  assert (Eq : (P0 + 16 * off - B - 16) / 16 = (po - (snd b + UNIT)) / UNIT).
  { unfold po, P0, UNIT. f_equal; lia. }
  rewrite Eq.
  assert (QB : 0 <= (po - (snd b + UNIT)) / UNIT < 65536).
  { unfold po, UNIT. replace (snd b + (16 + stride * k) + 16 * off - (snd b + 16)) with (stride * k + 16 * off) by lia.
    split; [apply Z.div_pos; lia| exact Q16]. }
  (* [comment removed for export] *)
  rewrite (wr16_wr8_comm (fst b, po + -2) (fst b, po + -3)) by (cbn; lia || reflexivity).
  destruct (rwr8_rep _ _ (po + -3) k MC TC ERc EGc) as [MD TD]; [unfold po, UNIT; lia| lia|].
  destruct (rwr16_rep _ _ (po + -2) ((po - (snd b + UNIT)) / UNIT) MD TD ERc EGc) as [ME TE]; [unfold po, UNIT; lia| unfold po, UNIT; lia| lia|].
  replace (P0 + 16 * off - 2) with (r_base r + (po + -2)) by lia.
  replace (P0 + 16 * off - 3) with (r_base r + (po + -3)) by lia.
  (* [comment removed for export] *)
  unfold set_size, aadd. cbn [fst snd id].
  set (rsv := snd b + (UNIT + stride * k) + (stride - IB) - po - n).
  assert (Ersv : P0 + stride - 4 - (P0 + 16 * off) - n = rsv) by (unfold rsv, po, P0, UNIT, IB; lia).
  rewrite Ersv.
  assert (RSV : 0 <= rsv <= stride - 4 - n) by (unfold rsv, po, UNIT, IB; lia).
  set (stF := if negb (rsv =? 0) then _ else _).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb].
    - split; [exact ME|]. split; [exact TE|]. split; assumption.
    - destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + - rsv) 0 ME TE ERc EGc) as [MF TF]; [unfold rsv, po, UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - rsv) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + - rsv)) by (unfold P0, UNIT, IB; lia).
      split; [exact MF|]. split; [exact TF|]. split; assumption. }
  clearbody stF mF. ddestruct PF as (MF & TF & ERf & EGf).
  set (stG := if 5 <=? rsv then _ else _).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
                /\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
    - (* [comment removed for export] *)
      rewrite (wr32_wr8_comm (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -4) (fst b, snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -5) 0 MF TF ERf EGf) as [M1 T1]; [unfold UNIT, IB; lia| lia|].
      destruct (rwr32_rep _ _ (snd b + (UNIT + stride * k) + (stride - IB) + -4) rsv M1 T1 ERf EGf) as [M2 T2]; [unfold UNIT, IB; lia| unfold UNIT, IB; lia| lia|].
      replace (P0 + stride - 4 - 4) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -4)) by (unfold P0, UNIT, IB; lia).
      replace (P0 + stride - 4 - 5) with (r_base r + (snd b + (UNIT + stride * k) + (stride - IB) + -5)) by (unfold P0, UNIT, IB; lia).
      split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  ddestruct PG as (MG & TG & -> & R2 & ERg & EGg).
  assert (KV : 0 <= Z.land k 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land k 31 <= k) by (split; [apply Z.land_nonneg; lia| apply land_le_l; lia]). lia. }
  destruct (rwr8_rep _ _ (po + -3) (Z.land k 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH]; [unfold po, UNIT; lia| exact KV|].
  split; [exact MH|]. split; [exact TH|].
  split; [|split; [reflexivity| unfold po, UNIT; lia]].
  rewrite (conc_region' st2 (fst b, po) r Hr). cbn [snd]. exact (eq_sym Epo).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End ENFRAME.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L15001278315.28L15003380563.21L15003380563.22L15003380563.26L15003380563.31L17317660645.19L21472299690.26L31033904341.19L32805229776.19L38911633110.29L38912055157.20L44076581204.24L45508904211.20L45509014704.29L46133491348.24L46539283258.26L48819153349.20L4886104128.19 L58630455040.19L59338250307.20L60242812106.26L6175532259.26 L64024432250.26L64026472518.19L6434264131.26 00000T01501V02>02c02j03B03I03i04F04V05605Q06006L06n07>07^07n08I08k09F09^0:90:NS2P06stride3off1n4OFF02N03rsv1H1x2H0S2P06stride3off1n4OFF02N03FIT1x1HS2P06stride3off1n4OFF02N03FIT1x1HS2P06stride3off1n4OFF02N03FIT3rsv2n01x1HS2P06stride3off1n4OFF02N03FIT3rsv1x1HS2P02P4S2P06stride3off1n2PS3rsvS2P02P4S2P06stride3off1n4OFF02N03FIT2PSS2P06stride3off1n4OFF02P43rsvS2P03off4OFF02P4S2P06stride3off1n4OFF02N02P43rsvS2P06stride3off1n2N03FIT2PSS2P06stride3off1n2N03FIT2PS3rsvS2P06stride3off1n3FIT2PS3rsvS2P06stride3off1n4OFF02N02P43rsv1HS2P03off4OFF02P4S2P06stride3off1n4OFF02N03FIT2PSS2P03off4OFF02P4S2P06stride3off1n2N03FIT2PSS2P06stride3off1n4OFF02N02P43rsv1HS2P06stride3off1n3FIT3rsv1HS2P06stride3off1n2PS3rsvS2P06stride3off1n2N03FIT2PSS2P06stride3off1n3rsv". (* [comment removed for export] *)
#[using="Type"] Lemma rpres_enframe : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "PC,P,$0.SpPm0,$39.Pm4,$39.PP0,$0.Pstride,$0.Poff,$0.Pn,$0.Pk,$0.PB,$0.P,(3:.R9.R8.R7.)P,(9.=R5.)P,(9.=R5.)P,(9.(:.(:.(1>.+10.R7.)R6.)+4.)R8.)P,(9.+4.R:.)P,(9.(:.R;.R:.)(30.+2.+40.))P,Px,$0.P,(7.(9.(1=.R=.+4.)R1.)(6.R1.(1=.(:.R=.R<.)+4.)))A1.R11.R2.(3:.R10.R?.(35.(36.R>.R=.R;.)(:.R=.(1>.+10.R;.))(1=.(:.R=.R<.)+4.)R:.R9.(37.(1=.(1=.(:.R=.(1>.+10.R;.))R8.)+10.)+10.)))")
(* [comment removed for export] *).
Proof.
  intros C m0 m4 P0 stride off n k B HP OFF0 N0 FIT P4 PS HC.
  assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  assert (HO : rpres_except C m0 (renframe_off_mem m4 P0 off)).
  { unfold renframe_off_mem. destruct (off =? 0); [exact HP|].
    apply rpres_write; [| lia | cbn; lia | cbn; intros; apply HC; lia].
    apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  unfold renframe_tail_mem. cbv zeta.
  set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
  assert (HE : rpres_except C m0 mE).
  { subst mE. apply rpres_write; [| lia | rewrite L2; lia | rewrite L2; intros; apply HC; lia].
    apply rpres_write; [exact HO| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mE.
  set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
  set (mF := if rsv =? 0 then _ else _).
  assert (HF : rpres_except C m0 mF).
  { subst mF. destruct (Z.eqb_spec rsv 0); [exact HE|]. apply rpres_write; [exact HE| lia | cbn; lia | cbn; intros; apply HC; lia]. }
  clearbody mF.
  set (mG := if 5 <=? rsv then _ else _).
  assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
  { subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
    - split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply HC; lia].
      apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply HC; lia].
    - split; [exact HF| lia]. }
  clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
  apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros; apply HC; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L15045125444.18L2740264792.22 L36942846886.18L44956394699.20L55688452560.16L62717045481.23L8931505686.23 00000100900:00@00A00K00cSS1q1r2HoSS1v2HvSS1q1r2Ho1DS3hRP1q1r2Ho3RB03RBC3RCB". (* [comment removed for export] *)
#[using="Type"] Lemma rrdv_agree : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pst,$1?.Pm1,$39.Po,$39.Pq,$11.Pr,$23.Px,(20.&8.)P,(21.VhRP,R6.R5.)P,(3;.R7.R5.R6.)P,(1.(>.$23.)(?.$<.$23.(10.$<.$13.$16.$23.)(18.$<.$13.$16.$23.)(1;.$<.$0.R5.)(24.R8.))(1:.$23.R4.))P,(1.$3<.(3=.R5.)$3>.)P,(7.(9.=(1<.$<.$0.R7.))(6.(1<.$<.$0.R7.)(3?.(40.R6.))))P,(33.(41.R;.(1;.$<.$0.R8.)(1<.$<.$0.R8.)))P,(42.$43.R;.(:.(29.R8.)(1<.$<.$0.R9.))(2:.(20.&8.)R7.(2<.(20.&8.))))(1.$0.(44.$39.$45.R;.R=.R:.)(46.&8.R8.))")
(* [comment removed for export] *).
Proof.
  intros st m1 o q r x MR UA Hr Hk Ho NG Hb.
  unfold rdv. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st m1 (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read rsegs m1 _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    ddestruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite <- (UA (fst q) r (snd q) h Hr Hk Ho E NG).
    destruct (m1 (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. dpose MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). rceilb.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L26371996543.30L28123924413.30L43507363276.37L46509638698.30L5587264083.28 L6644413695.30 00000a01I02602R02m03QS1a2kk3Hkk1G3rga3Sa03Sa13SaL4RaB04RaAL3DA13DA22HGS3hRP1a2kk3Hkk1G3rga3Sa03Sa14RaB03RaC2HGS1a2kk3Hkk1G3rga3Sa04RaB03LRa2HG2r'1H3Sa13LR'S1a2kk3Hkk1G3rga3Sa04RaB02HGS2st1g1a1G3rga3Sa03Sa14RaB0S1a2kk3Hkk1G3rga3Sa03Sa14RaB03LRa2HG". (* [comment removed for export] *)
#[using="Type"] Lemma rmeta_chunk_facts : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pst,$1?.Pm,P,(20.&40.)(>.(20.&8.))Pg,$11.P,(21.VhRP,R3.R2.)P,(47.R4.R2.)ZG,$0.(38.R5.R3.)(7.(48.$43.R5.R1.(49.R6.(4:.R6.R4.)))(7.(6.=R1.)(7.(9.(:.R1.+28.)(4;.VhRP,))(7.(8.(9.(:.R1.+28.)+10000.)(9.+48000.R1.))(7.(8.(9.(:.R1.+28.)+48000.)(9.+7>000.R1.))(7.Prid',$<.Pr',$23.P,(1.(>.$23.)(?.$<.$23.(10.$<.$13.$16.$23.)(18.$<.$13.$16.$23.)R2.(24.R8.))(1:.$23.R1.))P,(1.$3<.(3=.R2.)$3>.)(8.(9.(:.R5.+28.)(29.R3.))(9.(:.(29.R3.)(3?.(40.R3.)))R5.))(4<.$<.Lrid0,$<.(4<.$23.Lr0,$23.(7.(1.(>.$23.)(?.$<.$23.(10.$<.$13.$16.$23.)(18.$<.$13.$16.$23.)R2.(24.R8.))(1:.$23.R1.))(7.(33.(1.$3<.(3=.R1.)$3>.))(7.(9.(4=.R1.)R3.)(9.(:.R3.+28.)(:.(29.R1.)(3?.(40.R1.)))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros st m g MR MS G.
  split; [apply rmrep_meta_chunk; assumption|].
  pose proof MR as (WF & _). dpose WF as (_ & WR & DISJ & _).
  ddestruct MS as (a & ara & kk & Ha & Hkk & Eg).
  ddestruct (rarea_conc st a ara WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RaB0 & RaAL & RaC).
  pose proof (rarea_lr_lo st a ara rga WF Ha Hra) as LRa.
  ddestruct (WR (fst a) rga Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint2 _ _ RFa ltac:(pose proof (round_up_pg_ge (r_len rga)); lia)) as [DA1 DA2].
  assert (HG : G = r_base rga + snd a + (AREA_HDR + META_SIZE * kk)).
  { subst G. rewrite Eg, conc_aadd by (rewrite Hra; eauto). rewrite (conc_region' st a rga Hra). reflexivity. }
  unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk. clearbody G.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  - intros rid' r' Hr' Hk'. pose proof (lr_lo_group r' Hk') as LR'.
    assert (NE : rid' <> fst a) by (intros ->; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    destruct (DISJ rid' r' (fst a) rga Hr' Hra NE); lia.
  - dexists (fst a), rga. split; [exact Hra|]. split; [exact NK|]. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L48777195949.1900000CS1r3RB02r04RBAL1q1H". (* [comment removed for export] *)
#[using="Type"] Lemma rregion_facts : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pst,$1?.Pm,P,(20.&40.)(>.(20.&8.))Prid,$<.Pr,$23.P,(21.VhRP,R4.R3.)P,(1.(>.$23.)(?.$<.$23.(10.$<.$13.$16.$23.)(18.$<.$13.$16.$23.)R3.(24.R5.))(1:.$23.R2.))(7.(9.+1000.(29.R3.))(7.(1.$0.(4>.(29.R3.)+1000.)=)(7.(9.(:.(29.R3.)(3?.(40.R3.)))(4;.VhRP,))(7.P,(6.=(3?.(40.R3.)))(8.(9.(:.(29.R4.)(3?.(40.R4.)))+10000.)(9.+48000.(29.R4.)))P,(6.=(3?.(40.R3.)))(8.(9.(:.(29.R4.)(3?.(40.R4.)))+48000.)(9.+7>000.(29.R4.)))))))")
(* [comment removed for export] *).
Proof.
  intros st m rid r (WF & _) Hr. dpose WF as (_ & WR & _).
  ddestruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| split; intros Hn; destruct (rreserved_disjoint2 _ _ RFr Hn); assumption]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "Pb',(;.$<.$0.)Pgh,$=.P,(1.(>.$=.)(?.(;.$<.$0.)$=.(10.$11.(12.$<.$13.$0.$14.)(15.$<.$13.$16.$0.$14.$17.)$=.)(18.$11.(12.$<.$13.$0.$14.)(15.$<.$13.$16.$0.$14.$17.)$=.)R2.(19.Vst,))(1:.$=.R1.))P,(1.$<.(1;.$<.$0.R3.)(1;.$<.$0.Vb,))(8.(9.(:.(1<.$<.$0.R4.)+9.)(1=.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vidx,))+4.))(9.(1=.(:.(:.(:.(1<.$<.$0.Vb,)+10.)(1>.Vstride,Vidx,))Vstride,)+4.)(1<.$<.$0.R4.)))")
(* [comment removed for export] *).
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

Local Ltac2 Set LiaOrc.tbl := fun () => "00\0?L10633947089.49L1065730742.49 L11802115489.48L13072842158.49L14789919395.39L1603629458.49 L16233624900.49L18586380311.33L19552178008.46L22878330790.37L24893064173.15L25888422806.50L2742543465.49 L27550839556.49L27893251492.39L29245549895.49L29786706907.40L29920600182.40L30226908626.47L34002134913.49L3407134468.49 L36635884945.49L4245580456.48 L44445786337.49L4600666923.48 L46493120819.49L5013670869.49 L50239149504.49L5325102278.49 L56456628197.46L56456641618.47L56456642517.48L56897696694.37L57235885631.49L58623704396.49L59310676310.41L61619511679.49L63215677055.47L64162715952.49L6433336498.49 L65841136949.50L68022693192.38L8394274504.48 L8534399788.33 00000N01601Z02G02i03V04404V05>05i06906g07T08208P09>09\0:a0;E0;c0<A0<_0=M0=k0>T0?20?Z0@B0@j0A_0BT0CI0D60DT0E=0F80Fe0GM0H10H^0IG0J40J\0K>S2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B03S162R42CBS2st1b1r3idx2mr6stride1B2P02B02x22HiS2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42SKS2st1b1r3idx2mr6stride1B2P02B03S16S2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42SKS2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B03S16S2st1b1r3idx2mr6stride1B2P02B03S162R42SKS2st1b1r3idx2mr6stride1B2P02B03S162R42CB2SKS1b2mr6stride2b'S2st1b1r3idx2mr6stride1B2P02B03S162R42CB2x12HiS2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42SKS2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B03S162R42CB2x22HiS2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B04SPAN3S163B164SMOD2R43RAL3RI13RI22CB2SKS2st1b1r3idx2mr6stride1B2P02B02x32HiS2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B03S162R42CB2x32HiS2st1b1r3idx2mr6stride1B2P02B0S2st2m11b1r3idx2mr6stride1B2P02B02x31i2HiS2st1b1r3idx2mr6stride1B2P02B0S2st1b1r3idx2mr6stride1B2P02B03S162R42CBS2st1b1r3idx2mr6stride1B2P02B03S162R42CBS2st1b1r3idx2mr6stride1B2P02B03S162R42CBS3hRP2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42RC3RCBS3hRP2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42RC3RCBS3hRP2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42RC3RCBS2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42CBS2st1b1r3idx2mr6stride1B2P02B0S2st2m11b1r3idx2mr6stride1B2P02B02x21i2HiS1b3idx2mr6stride2r13B161d2Hd2b'2Hc2r03AL'1q2Hq2q12H42q22H9S2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42CBS2st1b1r3idx2mr6stride1B2P02B03S162R42SKS2st1b1r3idx2mr6stride1B2P02B02x12HiS2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42SKS2st2m11b1r3idx2mr6stride1B2P02B02x11i2HiS2st1b1r3idx2mr6stride1B2P02B04SPAN3S162R42SKS2st1b1r3idx2mr6stride1B2P02B03S162R42SKS2st1b1r3idx2mr6stride1B2P02B03IDX". (* [comment removed for export] *)
#[using="MR UA Hr Hk B0 IDX SPAN S16 B16 SMOD HDR0"] Lemma rslot_facts : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "(4<.(20.&8.)Lx3,(20.&8.)(4<.(20.&8.)Lx2,(20.&8.)(4<.(20.&8.)Lx1,(20.&8.)(7.(4?.$43.Vm1,(1=.VP0,+4.)Vstride,)(7.(42.$43.Vm1,(1=.VP0,+4.)(2:.(20.&8.)(2;.=)(2:.(20.&8.)(2;.(46.&8.R3.))(2:.(20.&8.)(2;.(46.&8.R2.))(2:.(20.&8.)(2;.(46.&8.R1.))(2<.(20.&8.)))))))(7.(1.$0.(44.$39.$45.Vo,Vst,(26.$<.$0.(1;.$<.$0.Vb,)(:.(:.(1<.$<.$0.Vb,)(:.+10.(1>.Vstride,Vidx,)))-3.)))(46.&8.R3.))(7.(1.$0.(44.$39.$45.Vo,Vst,(26.$<.$0.(1;.$<.$0.Vb,)(:.(:.(1<.$<.$0.Vb,)(:.+10.(1>.Vstride,Vidx,)))-2.)))(46.&8.R2.))(7.(1.$0.(44.$39.$45.Vo,Vst,(26.$<.$0.(1;.$<.$0.Vb,)(:.(:.(:.(1<.$<.$0.Vb,)(:.+10.(1>.Vstride,Vidx,)))-2.)+1.)))(46.&8.R1.))(7.(1.$0.VB,(:.(29.Vr,)(1<.$<.$0.Vb,)))(7.(9.+1000.(29.Vr,))(7.(9.(:.VP0,Vstride,)(:.(29.Vr,)(3?.(40.Vr,))))(7.(9.(:.(29.Vr,)(3?.(40.Vr,)))(4;.VhRP,))(8.(9.(:.(29.Vr,)(3?.(40.Vr,)))+10000.)(9.+48000.(29.Vr,)))))))))))))))")
(* [comment removed for export] *).
Proof.
  dpose (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). rceilb.
  assert (CB : B = r_base r + snd b) by (apply conc_region'; exact Hr).
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  dpose MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr Hk) as [HWr HB].
  assert (WRs : wr_at rsegs m1 (P0 - 4) stride) by (eapply wr_at_sub; [exact HWr| unfold P0; lia| unfold P0; lia]).
  destruct (HB (snd b + 16 + stride * idx - 4) 0 ltac:(lia) HDR0) as [Y4 _].
  assert (WR3 : wr_at rsegs m1 (P0 - 3) 3) by (eapply wr_at_sub; [exact WRs|lia|lia]).
  ddestruct (rwr_at_bytes_exist m1 (P0 - 3) 3 WR3 ltac:(lia) ltac:(unfold P0; lia)) as (bs & Lbs & Ybs).
  destruct bs as [|x3 [|x2 [|x1 [|? ?]]]]; try discriminate. clear Lbs.
  dexists x3, x2, x1.
  assert (NG : forall d, 1 <= d <= 3 -> ~ grp_hdr_cov st (fst b) (snd b + 16 + stride * idx - d)).
  { (intros d Hd dd_H; ddestruct dd_H as (b' & gh & Hb' & Hf & Hc)).
    pose proof MR as (WF' & _). ddestruct WF' as (_ & _ & _ & _ & WG). ddestruct (WG b' gh Hb') as (r' & _ & _ & _ & _ & AL').
    clear - Hd Hc AL' B16 SMOD IDX S16.
    destruct (Z.mod_divide stride 16 ltac:(lia)) as [D _]. destruct (D SMOD) as [q Hq].
    assert (E : stride * idx = 16 * (q * idx)) by (rewrite Hq; ring).
    set (w := q * idx) in E. clearbody w. Z.div_mod_to_equations. lia. }
  dpose Ybs as (_ & _ & YB).
  assert (Y3 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 3)) [x3]).
  { split; [lia|]. split; [change (Z.of_nat (length [x3])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 0%nat ltac:(cbn; lia)) as YB0. cbn [nth_error Z.of_nat] in YB0 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 3) + 0) with (P0 - 3 + 0) by (unfold P0; lia). exact YB0. }
  assert (Y2 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 2)) [x2]).
  { split; [lia|]. split; [change (Z.of_nat (length [x2])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 1%nat ltac:(cbn; lia)) as YB1. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB1 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 2) + 0) with (P0 - 3 + 1) by (unfold P0; lia). exact YB1. }
  assert (Y1 : bytes_at rsegs m1 (r_base r + (snd b + 16 + stride * idx - 1)) [x1]).
  { split; [lia|]. split; [change (Z.of_nat (length [x1])) with 1; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia].
    pose proof (YB 2%nat ltac:(cbn; lia)) as YB2. cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ] in YB2 |- *.
    replace (r_base r + (snd b + 16 + stride * idx - 1) + 0) with (P0 - 3 + 2) by (unfold P0; lia). exact YB2. }
  split; [exact WRs|].
  split.
  { rewrite !b8_of_byte. change [b8 0; x3; x2; x1] with ([b8 0] ++ ([x3] ++ ([x2] ++ [x1]))).
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y4); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y3); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat].
    apply bytes_at_app. split; [eapply (bytes_at_at _ _ _ _ _ Y2); unfold P0; lia|]. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
    eapply (bytes_at_at _ _ _ _ _ Y1); unfold P0; lia. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x3 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -3) with (snd b + 16 + stride * idx - 3) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y3| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x2 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2) with (snd b + 16 + stride * idx - 2) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y2| lia]. }
  split.
  { apply (rrdv_agree st m1 o (fst b, _) r x1 MR UA Hr Hk); cbn [fst snd]; [lia| |].
    - replace (snd b + (16 + stride * idx) + -2 + 1) with (snd b + 16 + stride * idx - 1) by lia. apply NG; lia.
    - eapply bytes_at_at; [exact Y1| lia]. }
  split; [exact CB|]. split; [exact R4|]. split; [unfold P0; lia|]. split; [exact RC| apply RI1; unfold P0 in *; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SLOT.

(* [comment removed for export] *)
Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "(8.(50.Lk,$3<.(33.(1.$3<.R1.$3>.))O4.O3.O2.O1.)(8.(51.O5.O4.O1.)(8.(52.O5.O1.)(8.(53.O5.O1.)(54.VhRP,O5.O1.)))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L60907383215.2000000DS1a1r2Ha2r'2B'3LRE1H". (* [comment removed for export] *)
#[using="Type"] Lemma rmalloc_fp_mono st sta stb lo sp a : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "P,Prid,$<.Pr,$23.P,(1.(>.$23.)(?.$<.$23.(10.$<.$13.$16.$23.)(18.$<.$13.$16.$23.)R2.(24.O5.))(1:.$23.R1.))(4<.$23.Lr',$23.(7.(1.(>.$23.)(?.$<.$23.(10.$<.$13.$16.$23.)(18.$<.$13.$16.$23.)R4.(24.O4.))(1:.$23.R1.))(7.(1.$3<.(3=.R1.)(3=.R3.))(7.(1.$0.(29.R1.)(29.R3.))(9.(40.R3.)(40.R1.))))))P,(55.O6.O5.O3.O2.O1.)(55.O6.O4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros HR [H|[H|H]]; [| right; left | right; right; exact H].
  - destruct H as [H|[H|[H|(rid & r & Hr & Hk & Ha)]]]; [left; left; exact H| left; right; left; exact H| left; right; right; left; exact H|].
    ddestruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    left. right. right. right. dexists rid, r'. split; [exact Hr'|]. split; [congruence|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
  - ddestruct H as (rid & r & Hr & Hn & Ha). ddestruct (HR rid r Hr) as (r' & Hr' & K' & B' & L').
    dexists rid, r'. split; [exact Hr'|]. split; [exact Hn|].
    assert (LRE : lr_lo r' = lr_lo r) by (unfold lr_lo; rewrite K', B'; reflexivity).
    pose proof (round_up_pg_mono (r_len r) (r_len r') L'). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

#[using="Type"] Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. unfold st2. rewrite get_meta_rec_upd_same. reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L11065263809.58L1227632238.55 L15371125219.58L16046084485.55L21381334151.59L2493336169.55 L28223197268.57L28223197268.59L28225291711.56L31084497720.52L32291209103.55L37185405350.47L39542225681.55L41418039500.48L43149772559.55L47404385131.60L49735958931.49L51792458685.48L51796692231.57L52278251594.55L52566885022.55L540560938.56  L61966796934.55L62062374277.50L64967714191.55L65100845346.55L65502415534.60L66515803890.55L8201950506.55 00000S00o01M01g02C02Q02`02o03>03Z03i04E04P04[04j05O05m06;06I06g07907U07d08K08Z08o09:09X09jS1k2mr2K01b1r2B04SPAN3S161a2Ha1H2H0S1k2mr2K01b2ai2AI2B03S163KAIS1n1k2mr2K02N01b2B03S163off2OFS1k2mr2K01b3AVr2B03S163P2kS1k2mr2K01b2ai2AI2B03S163KAIS1k2mr1b2LI2B0S1k2mr1b2B03S16S1k2mr1b2B03S16S1k2mr1b2B03S16S1k2mr2K01b2ai2AI2B03S163KAIS1k2mr1b3MPL2B0S1k2mr1b2LI2ai2AI2B03S163KAIS1k2mr1b2B0S1k2mr1b2B0S1k2mr1b3FRr2B0S1n1k2mr2K02N01b2B03S163S203off2OF2H0S2sc1k2mr2K04SC483GSC1b2B03S16S1k2mr2K01b2B0S1k2mr2K01b2B0S2sc1n1k2mr2K04NFIT1b2B03S161US1k2mr1b2LI3GS02B0S1k2mr2K01b2ai2AI2B03S163KAIS1k2mr1b2B03B16S2st1n1g1k2mr3st22K01b3E632B03S165GSC48S1k2mr1b2B03S16S1k2mr2K01b2FB2B03S16S1k2mr1b2B0S1n1k2mr2K02N01b2LI2B03S163S20S1k2mr1b1r2B04SPAN". (* [comment removed for export] *)
#[using="LB sc MF ACT AV K0 LBK N0 NFIT"] Lemma rfast_slot_ok : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_fp ()) "(4<.$11.Lb,$11.(4<.$23.Lr,$23.(7.(56.Vst2,Vg,R2.R1.Vk,Vn,)(7.Pa,$0.P,(7.(9.(1=.(:.(:.(:.(29.R2.)(1<.$<.$0.R3.))+10.)(1>.(57.Vmr,)Vk,))+4.)R1.)(6.R1.(1=.(:.(:.(:.(:.(29.R2.)(1<.$<.$0.R3.))+10.)(1>.(57.Vmr,)Vk,))(57.Vmr,))+4.)))(52.Vst,R2.)(7.(6.Vk,+20.)(7.(1.$58.(59.Vmr,)(1:.$11.R2.))(1.(>.$23.)(?.$<.$23.(10.$<.$13.$16.$23.)(18.$<.$13.$16.$23.)(1;.$<.$0.R2.)(24.Vst,))(1:.$23.R1.))))))))")
(* [comment removed for export] *).
Proof.
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  ddestruct (FA sc g ACT) as (SC48 & GSC & MEMnn). change (get_meta_rec st g) with mr in GSC, MEMnn.
  destruct (m_mem mr) as [b|] eqn:Hmem; [|congruence]. clear MEMnn.
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). change (get_meta_rec st g) with mr in FG. cbv zeta in FG.
  ddestruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  unfold UNIT, IB in *.
  assert (TBk : Z.testbit (m_avail mr) k = true) by (apply lowbit_testbit; assumption).
  pose proof (AVAI k K0 TBk) as KAI.
  assert (K32 : k < 32) by lia.
  assert (P2k : 0 < 2 ^ k <= m_avail mr).
  { split; [apply Z.pow_pos_nonneg; lia|]. ddestruct (lowbit_pow2 (m_avail mr) AV) as (k' & _ & E' & LE'). unfold lowbit in LBK.
    rewrite LBK in E'. rewrite E'. exact LE'. }
  assert (GSC48 : m_sizeclass mr < 48) by lia. specialize (S31 GSC48).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem K0 (or_introl TBk)) as FC. cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with mr in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(change (get_meta_rec st g) with mr; lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4.
  change (get_meta_rec st g) with mr in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  dexists b, r. pose proof rget_meta_rec_st2 as E2.
  split; [|split; [|split; [exact K32| split; [reflexivity| exact Hr]]]].
  - pose proof (UND GSC48 k K0 TBk) as U. rewrite GSC in U. specialize (S20 GSC48).
    constructor; rewrite ?E2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      try change (get_stride (m_set_avail (m_avail mr - 2 ^ k) mr)) with (get_stride mr);
      first [ exact Hmem | exact Hr | exact Hk | exact MSL | exact K4 | exact NOGRP | exact N0 | exact SMOD
            | (pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with mr; lia)) as SC;
               change (get_meta_rec (strip st) g) with mr in SC; unfold sstart_of in SC; rewrite Hmem in SC;
               cbn [default from_option id snd] in SC; unfold UNIT in SC; exact SC)
            | (intros off O0 OF;
               assert (get_stride mr * k + 16 * off < get_stride mr * (k + 1)) by lia;
               assert (get_stride mr * (k + 1) <= get_stride mr * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia);
               apply Z.div_lt_upper_bound; lia)
            | lia ].
  - intros a Ha. dexists g, b, r, k. split; [exact Hmem|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact K0|]. split; [left; exact TBk|].
    unfold sstart_of. rewrite Hmem. cbn [default from_option id snd]. unfold UNIT, IB. fold mr.
    assert (get_stride mr * k + get_stride mr <= get_stride mr * m_last_idx mr + get_stride mr) by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= get_stride mr * k) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End FASTFACTS.


End RP_1.

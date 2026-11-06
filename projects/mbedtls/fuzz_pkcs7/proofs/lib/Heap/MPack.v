(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KStepC
  MI_Kit MI_Inv MI_List MI_Contracts VirginDefs KReach MReach MStrat KCost MAll.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MPack () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.mkGhdr"; "OSSVerify.KrLib.Heap.MAll.GOODm"; "OSSVerify.KrLib.Heap.MI_Inv.MR"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Heap.Malloc.okay_to_free"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Heap.MAll.DRVc"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Heap.KStep.OWN"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.KCost.sall"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Malloc.cmalloc"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "OSSVerify.KrLib.Heap.KCost.eall"; "OSSVerify.KrLib.Heap.Prog.bptr"; "OSSVerify.KrLib.Heap.Prog.PState"; "OSSVerify.KrLib.Heap.Prog.raw_malloc"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.KCost.kgrow"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Heap.Malloc.cfree"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.Heap.Prog.raw_free"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FromINVL.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL x0 st L BL LS.

Let IR : inv_R x0 st L := proj1 INV.
Let IA : inv_A st := proj1 (proj2 INV).
Let IM : inv_M x0 st LS := proj1 (proj2 (proj2 INV)).
Let IL : inv_L st LS := proj1 (proj2 (proj2 (proj2 INV))).
Let IG : inv_G x0 st LS := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS : inv_S x0 st BL := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="L BL LS INV IR"] Lemma inv_shift_nonneg : 0 <= shift st.
Proof. unfold shift, ctx. exact (proj1 (ir_shift _ _ _ IR)). Qed.

(* [comment removed for export] *)
#[using="L BL LS INV IM"] Lemma inv_group_mem b m ai : s_groups st !! b = Some (mkGhdr (Some m) ai) -> m_mem (MR st m) = Some b.
Proof.
  intros H. destruct (im_hdr _ _ _ IM b _ H) as (m' & E & Hm & _). cbn in E. injection E as <-. exact Hm.
Qed.

(* [comment removed for export] *)
#[using="L BL LS INV IG"] Lemma GOODm_facts b m ai : ltac2:(CDefT.buildp (gd_tbl_MPack ()) "P,(0.(1.$2.)(3.$4.$2.(5.$4.(6.$7.$8.$9.$:.)(;.$7.$8.$<.$9.$:.$=.)$2.)(>.$4.(6.$7.$8.$9.$:.)(;.$7.$8.$<.$9.$:.$=.)$2.)O3.(?.Vst,))(10.$2.(11.(10.$4.O2.)O1.)))P,(12.(13.Vst,O2.))(14.(0.$9.(15.(13.Vst,O2.))=)(14.(16.(0.$9.(17.(13.Vst,O2.))=))(0.$18.(19.Vst,O2.)$1:.)))")
(* [comment removed for export] *).
Proof.
  intros Hb [GU GB]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  pose proof (g_freeable _ _ _ _ _ _ GO) as FR. unfold undersized in GU. unfold MR in *.
  destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(Hsc & Hli & Hml & _)]; unfold MR in *.
  - specialize (GU ltac:(lia)). unfold get_stride in GU.
    destruct (Z.eqb_spec (m_last_idx (get_meta_rec st m)) 0) as [Hli|Hli]; [| cbn [andb] in GU; lia].
    destruct (Z.eqb_spec (m_maplen (get_meta_rec st m)) 0) as [Hml|Hml]; [cbn [andb negb] in GU; lia|].
    cbn [andb negb] in GU. split; [exact Hli|]. split; [exact Hml|].
    unfold okay_to_free. rewrite FR. cbn [Z.eqb]. unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Hli), (proj2 (Z.eqb_neq _ _) Hml). cbn [andb negb].
    rewrite (proj2 (Z.ltb_lt _ _) GU). rewrite orb_true_r. reflexivity.
  - split; [exact Hli|]. split; [exact Hml|]. unfold okay_to_free. rewrite FR. cbn [Z.eqb]. unfold MR in Hsc. rewrite Hsc. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="L BL LS INV IM IG"] Lemma inv_UND : DRVc st -> UND st.
Proof.
  intros D m. destruct (m_mem (MR st m)) as [b|] eqn:Hm.
  - destruct (im_group _ _ _ IM m b Hm) as [[ai Hb]|[]].
    pose proof (D _ _ _ Hb) as [GU GB]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
    destruct (Z_lt_le_dec (m_sizeclass (MR st m)) 48) as [LT|GE].
    + unfold undersized in GU. exact (g_under _ _ _ _ _ _ GO ltac:(discriminate) LT (GU LT)).
    + exact (GB GE).
  - pose proof (im_zero _ _ _ IM m Hm) as E. rewrite E. cbn. auto.
Qed.

(* [comment removed for export] *)
#[using="L LS INV IM IG IS"] Lemma inv_free_facts (c : cptr) off n : ltac2:(CDefT.buildp (gd_tbl_MPack ()) "P,(1;.Vst,)P,(1<.(1=.(1=.$1>.$9.)$9.)(1?.(1=.$1>.$9.)$9.(1?.$1>.$9.O3.O2.)O1.)VBL,)(20.$4.Lg,$4.(20.$4.Lb,$4.(14.(0.(1.(1=.$4.$9.))(3.$1>.(1=.$4.$9.)(5.$4.(6.$7.$8.$9.$:.)(;.$7.$8.$<.$9.$:.$=.)(1=.$4.$9.))(>.$4.(6.$7.$8.$9.$:.)(;.$7.$8.$<.$9.$:.$=.)(1=.$4.$9.))O3.(21.Vst,))(10.(1=.$4.$9.)(1?.$4.$9.R2.=)))(14.(0.$9.(15.(13.Vst,R2.))=)(14.(0.$18.(19.Vst,R2.)$1:.)(14.(0.$22.(23.(13.Vst,R2.))(10.$4.R1.))(16.(0.$9.(17.(13.Vst,R2.))=))))))))")
(* [comment removed for export] *).
Proof.
  intros D Hin. destruct (is_blocks _ _ _ IS _ Hin) as (g & i & Hs & _). cbn [bslot fst] in Hs.
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b [ai Hb]] & Hi & _).
  pose proof (GOODm_facts b g ai Hb (D _ _ _ Hb)) as (Hli & Hml & Hok).
  dexists g, b. assert (i = 0) by lia. subst i. split; [exact Hs|]. split; [exact Hli|]. split; [exact Hok|].
  split; [exact (inv_group_mem _ _ _ Hb)| exact Hml].
Qed.

(* [comment removed for export] *)
#[using="L BL LS INV IL"] Lemma inv_nosmall_active44 : nosmallc st -> active st 44 = None.
Proof.
  intros NS. change (active st 44) with (get_head st (LActive 44)). rewrite (il_head _ _ IL).
  destruct (LS (LActive 44)) as [|m l] eqn:E; [reflexivity|]. exfalso.
  destruct (il_active _ _ IL 44 m ltac:(rewrite E; left; reflexivity)) as (_ & [b [ai Hb]] & Hsc).
  pose proof (NS _ _ _ Hb). unfold MR in *. lia.
Qed.

#[using="Type"] Lemma zsum_zero l : Forall (fun x => x = 0) l -> zsum l = 0.
Proof. intros H. induction H as [|x l Hx H IH]; [reflexivity|]. unfold zsum in *. cbn. lia. Qed.

#[using="L BL LS INV IA"] Lemma inv_nosmall_usage44 : nosmallc st -> usage st 44 = 0.
Proof.
  intros NS. rewrite (ia_usage _ IA 44) by lia. unfold gcnt. apply zsum_zero. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as ([b [gm ai]] & <- & Hin). cbn [snd g_meta].
  destruct gm as [m|]; [| reflexivity].
  apply (proj2 (list_elem_of_In _ _)) in Hin. apply elem_of_map_to_list in Hin.
  pose proof (NS _ _ _ Hin). destruct (Z.eqb_spec (m_sizeclass (MR st m)) 44); [lia| reflexivity].
Qed.
End FromINVL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Pack.
Variables (X : list bptr) (G : PState -> Model -> Prop).
Hypothesis HG : frame_ok G.

#[using="HG"] Lemma raw_malloc_eall n s mo (Q : mstate * option cptr -> Prop) K C : ltac2:(CDefT.buildp (gd_tbl_MPack ()) "P,(24.VX,VG,O5.O4.)P,(25.=O6.)P,(26.(1=.$27.(1.$1>.))O3.O2.O1.(28.(29.O5.)O6.))(2:.(1=.(1.$2;.)$2<.)(2=.O6.O5.)O4.Lp,(1=.(1.$2;.)$2<.)Lmo',$2>.(14.(20.$27.Lst,$27.(20.(1.$1>.)Lr,(1.$1>.)(14.A1.O3.(1?.$27.(1.$1>.)R2.R1.)(0.$27.(29.(2?.(1.$2;.)$2<.R4.))R2.))))(30.O2.O1.O4.R1.)))")
(* [comment removed for export] *).
Proof.
  intros OW Hn SA. dpose OW as [(L & Hc & HK & Hi) [Hnd HGs]].
  unfold raw_malloc. change (mbind mget ?f s) with (f s s).
  eapply eall_mbind; [apply (membed_kall Q G HG (cmalloc (ps_m s) n) K C L _ s mo SA (cmalloc_contract_proof _ _ _ Hc Hn) HK HGs)|].
  cbn beta. (intros [st' r] s1 mo1 dd_H; ddestruct dd_H as (HQ & KG & _)). cbn [fst snd] in HQ.
  exact (conj (ex_intro _ st' (ex_intro _ r (conj HQ eq_refl))) KG).
Qed.

#[using="HG"] Lemma raw_free_eall (p : bptr) s mo (Q : mstate -> Prop) K C : ltac2:(CDefT.buildp (gd_tbl_MPack ()) "P,(24.(31.$2;.O6.VX,)VG,O5.O4.)P,(26.$27.O3.O2.O1.(32.(29.O5.)(10.$1>.(33.$1>.$9.O6.))))(2:.(1=.$34.$2<.)(35.O6.O5.)O4.Lq,(1=.$34.$2<.)Lmo',$2>.(14.A1.O3.(29.(2?.$34.$2<.R2.))(30.O2.O1.O4.R1.)))")
(* [comment removed for export] *).
Proof.
  intros OW SA. dpose OW as [(L & Hc & HK & Hi) [Hnd HGs]].
  unfold raw_free. change (mbind mget ?f s) with (f s s).
  eapply eall_mbind; [apply (membed_kall Q G HG (cfree (ps_m s) (Some (fst p))) K C L _ s mo SA (cfree_contract_proof _ _ _ Hc (Hi _ (or_introl eq_refl))) HK HGs)|].
  cbn beta. (intros st' s1 mo1 dd_H; ddestruct dd_H as (HQ & KG & _)). cbn [fst snd] in HQ. exact (conj HQ KG).
Qed.
End Pack.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Sim MI_Contracts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocRep MallocTree MallocBlocks MallocFacts_A MallocFacts_inv MallocFacts_inv2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export VirginDefs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_Virgin () : Init.string Init.list := ["OSSVerify.KrLib.Heap.VirginDefs.span_virgin"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.wr8"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.prod"; "Stdlib.Lists.List.In"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.Heap.MI_WGroup.wrs"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.IB"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.enframe_at"; "Corelib.Init.Datatypes.pair"].


(* [comment removed for export] *)
Section MF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list MI_Inv.blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

#[using="X L BL LS INV ZB NFR"] Lemma f_under : fact_under st.
Proof.
  intros g b H SC STR.
  dpose INV as (IR & IA & IM & IL & IG & IS & ISH).
  ddestruct (hosts_GO X st L BL LS INV b g (mem_hosts X st L BL LS INV ZB g b H)) as (ai & Hb & GO).
  apply (g_under _ _ _ _ _ _ GO); [rewrite NFR; discriminate| exact SC| exact STR].
Qed.
End MF.

Theorem areach_under {resv} st LB : AREACH_from resv st LB -> fact_under st.
Proof.
  intros AR. ddestruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _).
  exact (f_under _ _ _ _ _ INV eq_refl eq_refl).
Qed.

Lemma fact_under_strip st : fact_under st -> fact_under (strip st).
Proof. intros F g b. rewrite !get_meta_rec_strip. apply F. Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MI_WGroup MI_WEnframe.

Lemma span_virgin_wr8 st rid S len p v : ltac2:(CDefT.buildp (gd_tbl_Virgin ()) "P,(0.O6.O5.O4.O3.)P,(1.(2.(3.$4.(5.$4.$6.O2.)O5.)(2.(7.O4.(8.$4.$6.O2.))(9.(8.$4.$6.O2.)(:.O4.O3.)))))(0.(;.O2.O1.O6.)O5.O4.O3.)")
(* [comment removed for export] *).
Proof.
  intros V N o Ho. destruct (N.eq_dec rid (fst p)) as [->|NE].
  - rewrite get_shadow_wr8_same. cbn [r_cells r_hav r_havp].
    rewrite lookup_insert_ne by (intros E; apply N; split; [reflexivity| lia]). apply V. exact Ho.
  - rewrite get_shadow_wr8_other by exact NE. apply V. exact Ho.
Qed.

Lemma span_virgin_wrs l : ltac2:(CDefT.buildp (gd_tbl_Virgin ()) "Pst,$<.Prid,$4.PS,$6.Plen,$6.P,(0.R4.R3.R2.R1.)P,Pa,(=.$4.$6.)P,(>.(=.$4.$6.)R1.(?.(=.(=.$4.$6.)$6.)(=.$4.$6.)(5.(=.$4.$6.)$6.)O1.))(1.(2.(3.$4.(5.$4.$6.R2.)R6.)(2.(7.R5.(8.$4.$6.R2.))(9.(8.$4.$6.R2.)(:.R5.R4.)))))(0.(10.O1.R6.)R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  induction l as [|[a v] l IH]; intros st rid S len V N; cbn [wrs]; [exact V|].
  apply IH; [apply span_virgin_wr8; [exact V| apply N; left; reflexivity]|].
  intros a' Ha'. apply N. right. exact Ha'.
Qed.

Lemma enframe_at_virgin st g b idx n off : ltac2:(CDefT.buildp (gd_tbl_Virgin ()) "Zstride,$6.(11.(12.O6.O5.))ZS,$6.(:.(:.(8.$4.$6.O4.)+10.)(13.R1.O3.))P,(3.$14.(15.(12.O6.O5.))(16.(=.$4.$6.)O4.))P,(7.=O1.)P,(7.=O2.)P,(7.(:.(:.(13.$17.O1.)O2.)$18.)R5.)P,(0.O6.(5.$4.$6.O4.)R5.(19.R6.+4.))(2.(0.(5.$<.$1:.(1;.O6.O5.O3.O2.O1.))(5.$4.$6.O4.)(:.R6.(13.$17.O1.))O2.)(3.$1:.(8.$<.$1:.(1;.O6.O5.O3.O2.O1.))(1<.$4.$6.(5.$4.$6.O4.)(:.R6.(13.$17.O1.)))))")
(* [comment removed for export] *).
Proof.
  intros stride S Hmem Ho Hn FIT V. rewrite enframe_at_eq. cbn [fst snd]. split.
  - apply span_virgin_wrs; [eapply span_virgin_sub; [exact V| unfold UNIT; lia| unfold UNIT, IB in *; lia]|].
    intros a Hin. unfold ef_list in Hin. rewrite Hmem in Hin. cbn [default from_option id] in Hin. fold stride in Hin.
    destruct (Z.eqb_spec off 0) as [O0|O0];
    match type of Hin with context [if negb (?x =? 0) then _ else _] => destruct (Z.eqb_spec x 0) as [R0|R0] end;
    match type of Hin with context [if 5 <=? ?x then _ else _] => destruct (Z.leb_spec 5 x) as [R5|R5] end;
      cbn [negb app map fst In] in Hin; unfold aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
      repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; cbn [fst snd]; intros [_ R]; subst S stride; lia.
  - unfold aadd. rewrite Hmem. cbn [default from_option id fst snd]. destruct (Z.eqb_spec off 0) as [->|O0]; cbn [fst snd]; f_equal; subst S stride; unfold UNIT; lia.
Qed.

(* [comment removed for export] *)
Lemma hh0_virgin st rid S len : (s_shadow st) !! rid = None -> 16 <= S ->
  span_virgin (hdr_havoc (rid, 0) st) rid S len.
Proof.
  intros SH HS o Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  rewrite !lookup_empty. change (0 / 16) with 0.
  rewrite lookup_insert_ne by (Z.div_mod_to_equations; lia). rewrite lookup_empty. repeat split; reflexivity.
Qed.

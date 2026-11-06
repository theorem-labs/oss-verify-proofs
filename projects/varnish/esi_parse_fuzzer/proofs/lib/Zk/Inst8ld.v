(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux Mall5lv Mallj6y Mallrkx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malllim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall5lv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallrkx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.Mallt6e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Mall1es Mall79j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_free_K RF_free.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.RF_ntf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_free_K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree Mallkgx Mall1es Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_free_K RF_free.

Module RF_fiok.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux Mall5lv Mallj6y Mallrkx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malllim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall5lv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallrkx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.Mallt6e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Mall1es Mall79j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_free_K RF_free.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.RF_ntf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_free_K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree Mallkgx Mall1es Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require F_free_K RF_free.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.RF_ntf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_free_K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep MRepAux MTree.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.
Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.
Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
  intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
  unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
  destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
  - pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
  - tauto.
Qed.
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL.

(* [comment removed for export] *)

Section FP.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : mrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : pres_except (fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 270516 <= a < 270520) m m'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 270516 <= a < 270520.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="SHR BLKR LO MR C m Rr Clg"] Lemma fp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof.
  intros Hb' Hab. pose proof MR as (WF & _). (first [ pose proof (WF) as dR_14; dand5 dR_14 as Hres WR DJ WA WG | pose proof WF as (Hres & WR & DJ & WA & WG) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  (first [ pose proof ((WR _ _ Hrg)) as dR_15; dand5 dR_15 as _ _ _ RGC RGF | destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF) ]). pose proof (reserved_disjoint _ _ RGF) as (?&?&?&?). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold CTX in X. lia.
    + (first [ dex2 X as rid r; dand3 X as Hr NK Hin | dand5 X as rid r Hr NK Hin | destruct X as (rid & r & Hr & NK & Hin) ]).
      assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
      destruct (DJ _ _ _ _ Hr Hrg NE); lia.
    + (first [ dex2 X as b gh; destruct X as [Hb Hin] | dand4 X as b gh Hb Hin | destruct X as (b & gh & Hb & Hin) ]). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
      * specialize (HD b gh Hb E). unfold IB in HD. lia.
      * (first [ pose proof ((group_conc st b gh WF Hb)) as dR_18; dex1 dR_18 as rb; dand6 dR_18 as Hrb Cb Krb Sb0 Sb1 _ | pose proof ((group_conc st b gh WF Hb)) as dR_18; dand7 dR_18 as rb Hrb Cb Krb Sb0 Sb1 _ | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _) ]).
        pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
    + (first [ dex3 X as rid r v; dand4 X as Hr Kr Hin HC | dand7 X as rid r v Hr Kr Hin HC | destruct X as (rid & r & v & Hr & Kr & Hin & HC) ]). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
      * rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
      * pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - (first [ dex2 DR as rid r; dand4 DR as Hr Hr' Kr Hin | dand6 DR as rid r Hr Hr' Kr Hin | destruct DR as (rid & r & Hr & Hr' & Kr & Hin) ]).
    destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
    assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
    pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
End FP.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL2.
End RF_fiok.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free.RF_ntf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.F_free_K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_free OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Inst8ld.RF_fiok.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep MRepAux MTree.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition hz (a : Z) : Prop := 4096 <= a < alloc_ceiling /\ ~ (0x10000 <= a < 0x63000).

Lemma region_hz st m rid r a :
  mrep st m -> (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> hz a.
Proof.
  intros (WF & _) Hr Ha. (first [ pose proof (WF) as dR_1; dand3 dR_1 as _ WR _ | pose proof WF as (_ & WR & _) ]). (first [ pose proof ((WR _ _ Hr)) as dR_2; dand5 dR_2 as RB0 RBAL RL0 RBC RFr | destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr) ]).
  pose proof (reserved_disjoint1 _ _ RFr) as D. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold hz.
  split; [| lia]. split; [| lia]. Z.div_mod_to_equations. lia.
Qed.

End CEIL.

Section FP2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : mrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : pres_except (fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 270516 <= a < 270520) m m'.

Let FPT := fun a => free_fp st lo sp a \/ DROPPED st st' a \/ 270516 <= a < 270520.

(* [comment removed for export] *)
Lemma fp_where a : FPT a -> lo <= a < sp \/ CTX <= a < CTX + 928 \/ 270516 <= a < 270520 \/ hz a.
Proof.
  pose proof MR as (WF & _). (first [ pose proof (WF) as dR_3; dand5 dR_3 as Hres WR DJ WA WG | pose proof WF as (Hres & WR & DJ & WA & WG) ]).
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + left; exact X.
    + right; left; exact X.
    + (first [ dex2 X as rid r; dand3 X as Hr _ Hin | dand5 X as rid r Hr _ Hin | destruct X as (rid & r & Hr & _ & Hin) ]). right; right; right. eapply (region_hz st m rid r a MR Hr). pose proof (lr_lo_ge r). lia.
    + (first [ dex2 X as b gh; destruct X as [Hb Hin] | dand4 X as b gh Hb Hin | destruct X as (b & gh & Hb & Hin) ]). (first [ pose proof ((group_conc st b gh WF Hb)) as dR_6; dex1 dR_6 as rb; dand6 dR_6 as Hrb Cb _ Sb0 Sb1 _ | pose proof ((group_conc st b gh WF Hb)) as dR_6; dand7 dR_6 as rb Hrb Cb _ Sb0 Sb1 _ | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _) ]).
      right; right; right. eapply (region_hz st m (fst b) rb a MR Hrb). lia.
    + (first [ dex3 X as rid r v; dand4 X as Hr _ Hin _ | dand7 X as rid r v Hr _ Hin _ | destruct X as (rid & r & v & Hr & _ & Hin & _) ]). right; right; right. eapply (region_hz st m rid r a MR Hr). lia.
  - (first [ dex2 DR as rid r; dand4 DR as Hr _ _ Hin | dand6 DR as rid r Hr _ _ Hin | destruct DR as (rid & r & Hr & _ & _ & Hin) ]). right; right; right. eapply (region_hz st m rid r a MR Hr). lia.
  - right; right; left; exact ER.
Qed.

(* [comment removed for export] *)
Lemma free_unchanged a : 0 <= a < 2^64 ->
  ~ (lo <= a < sp) -> ~ (CTX <= a < CTX + 928) -> ~ (270516 <= a < 270520) ->
  (hz a -> exists blk', In blk' (lbrm LB0 blk) /\ blk_addr blk' <= a < blk_addr blk' + blk_size blk') ->
  m' (wa a) = m (wa a).
Proof.
  intros Ha N1 N2 N3 HB. apply PE; [exact Ha|]. intros F.
  destruct (fp_where a F) as [X|[X|[X|X]]]; [tauto|tauto|tauto|].
  (first [ pose proof ((HB X)) as dR_9; dex1 dR_9 as blk'; destruct dR_9 as [Hin Hab] | pose proof ((HB X)) as dR_9; dand3 dR_9 as blk' Hin Hab | destruct (HB X) as (blk' & Hin & Hab) ]).
  exact (fp_not_block st st' LB0 blk lo sp m C MR LO BLKR SHR blk' a Hin Hab F).
Qed.
End FP2.

(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition free_postF (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (b : block) (lo : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ HEAP s' (lb_remove (blk_id b) LB) m'
    /\ (forall a, 0 <= a < 2^64 ->
          ~ (lo <= a < bv_unsigned sp) -> ~ (CTX <= a < CTX + 928) -> ~ (PERRNO <= a < PERRNO + 4) ->
          (hz a -> exists blk', In blk' (lb_remove (blk_id b) LB) /\ blk_addr blk' <= a < blk_addr blk' + blk_size blk') ->
          m' (wa a) = m (wa a)).

Theorem p0_free_implM :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (b : block) (lo : Z) (errv : word),
  HEAP s LB m -> In b LB ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - FREE_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 PTP ->
  a0 = Z_to_bv 64 (blk_addr b) ->
  implM rsegs (raw_free (blk_id b)) s
        (free_postF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b lo errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_SYM) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB b lo errv
         HP Hin ST LO SLO ERR MI TP A0.
  destruct b as [[p A] n]. cbn [blk_id blk_addr fst snd] in *.
  (first [ dex1 HP as st; dand5 HP as LB0 PERM Hst MR [BL AR] | dand6 HP as st LB0 PERM Hst MR [BL AR] | destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]) ]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (Mallx0l.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls6g.Mallttr.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
  (* [comment removed for export] *)
  eapply (implM_evt rsegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 free_entry) fc None m (seg_rom rsegs))).
  { unfold FREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (raw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => free_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - exact Hst.
  - exact HOK.
  - apply implT_reach.
    apply (libc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold FREE_STACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    (first [ dex16 FE as w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m'; dand10 FE as -> MI' ST' ERR' MR' PE SHR BLKR EB BRKR | dand26 FE as w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m' -> MI' ST' ERR' MR' PE SHR BLKR EB BRKR | destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR) ]).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold FREE_STACK in SLO; lia).
    unfold free_postF. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
    split; [reflexivity|]. split; [reflexivity|].
    cbn [blk_id fst snd]. rewrite ELB.
    split.
    + exists st', (lbrm LB0 (p, A, n)). split; [apply lbrm_perm; exact PERM|].
      split; [reflexivity|]. split; [exact MR'|]. split.
      * (* [comment removed for export] *) unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
        destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
        rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
      * (first [ dex2 LEAF as ans o'; rename LEAF into FO | dand3 LEAF as ans o' FO | destruct LEAF as (ans & o' & FO) ]).
        eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
        cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
        cbn [fst]. rewrite <- FB. (first [ pose proof ((go_region _ _ _ (ci_gmetas _ _ C b g HBg))) as dR_13; dex1 dR_13 as r; destruct dR_13 as [Hr _] | pose proof ((go_region _ _ _ (ci_gmetas _ _ C b g HBg))) as dR_13; dand3 dR_13 as r Hr _ | destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _) ]). rewrite Hr. eexists; reflexivity.
    + intros a Ha N1 N2 N3 HB.
      apply (free_unchanged st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO BLKR SHR PE a Ha N1 N2);
        [unfold PERRNO in N3; exact N3|].
      intros X. (first [ pose proof ((HB X)) as dR_14; dex1 dR_14 as blk'; destruct dR_14 as [Hb' Hab] | pose proof ((HB X)) as dR_14; dand3 dR_14 as blk' Hb' Hab | destruct (HB X) as (blk' & Hb' & Hab) ]). exists blk'. split; [| exact Hab].
      eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb'].
Qed.

End CEIL2.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn FxHandoff FxHoBuild FxHandoff2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan CxPlanSound CxOpt.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrRev BrRevLedger BrClass.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Rev.
Variable segs : list Segment.
Variable IM : fimage.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.

Variable TT : ttab_e.
Variable n : int.
Variable shapes : list rshape.
Variable cuts : list (int * list Z).     (* [comment removed for export] *)
Variable classes : list (int * rclass).   (* [comment removed for export] *)
Variable CS : CAP.acs.

Local Notation kn := (CAP.kn CS).

(* [comment removed for export] *)
Definition rb_M : itrie region := iof_list (map (fun s => (sh_tag s, sh_region s)) shapes).
Local Notation M := rb_M.

Definition opt_list {T : Type} (o : option T) : list T := match o with Some x => [x] | None => [] end.

Definition cuts_of (t : int) : list Z :=
  match List.find (fun p => (fst p =? t)%uint63) cuts with Some p => snd p | None => [] end.

Definition rb_rfacts : list hfact :=
  map (fun s => HRegion (sh_tag s) (sh_lo s) (sh_len s) (sh_al s)) shapes.

Definition cls (t : int) : option rclass :=
  match List.find (fun p => (fst p =? t)%uint63) classes with Some p => Some (snd p) | None => None end.

Definition cls_neq (r r' : rshape) : bool :=
  match cls (sh_tag r), cls (sh_tag r') with Some c, Some c' => class_neq c c' | _, _ => false end.

Definition cls_chk (s : rshape) : bool :=
  match cls (sh_tag s) with
  | Some c => class_chk A CS TT (sh_tag s) (sh_lo s) (sh_len s) c && (to_Z (sh_lo s) <? to_Z (sh_len s))
  | None => true
  end.

Definition rb_dfact (r r' : rshape) : list hfact :=
  if (sh_tag r =? sh_tag r')%uint63 then []
  else if cls_neq r r' then [HDisj (sh_tag r) (sh_lo r) (sh_len r) (sh_tag r') (sh_lo r') (sh_len r')]
  else if disj_chk TT kn (cuts_of (sh_tag r)) (cuts_of (sh_tag r')) (sh_tag r) (sh_lo r) (sh_len r) (sh_tag r') (sh_lo r') (sh_len r')
       then [HDisj (sh_tag r) (sh_lo r) (sh_len r) (sh_tag r') (sh_lo r') (sh_len r')] else [].

Fixpoint rb_pairs (l : list rshape) : list hfact :=
  match l with
  | [] => []
  | r :: rest => flat_map (rb_dfact r) rest ++ rb_pairs rest
  end.

Definition rb_gfacts : list hfact :=
  flat_map (fun i => opt_list (fact_of_reg TT (AX2.s_regs (CAP.a_ss CS)) i)) (seq 1 31).

Definition rb_kfacts : list hfact :=
  flat_map (fun K => opt_list (fact_of_kentry TT M (CAP.img_lo A) (CAP.img_hi A) K)) kn.

Definition rb_facts : list hfact := rb_rfacts ++ rb_pairs shapes ++ rb_gfacts ++ rb_kfacts.

(* [comment removed for export] *)
Definition rb_fillcov : list (int * Z * Z * Z) := flat_map (fill_cov1 TT M) kn.

(* [comment removed for export] *)
Definition rb_state : sdesc := FxHandoff2.ho_build2 IM rb_facts (of_Z (AX2.s_pc (CAP.a_ss CS))) shapes.

(* [comment removed for export] *)
Definition rb_check_with (F : list hfact) (d : sdesc) : bool :=
  tt_wf TT
  && match classes with [] => true | _ => CAP.no_fog (CAP.a_maps CS) && CxOpt.ledger_pos kn (CAP.a_maps CS) && forallb cls_chk shapes end   (* [comment removed for export] *)
  && forallb (fun s => region_chk TT kn (sh_tag s) (sh_lo s) (sh_len s) (sh_al s)) shapes
  && ho_check2 IM F d                (* [comment removed for export] *)
  && forallb (fact_tags_lt n) F
  && (AX2.s_pc (CAP.a_ss CS) =? to_Z (sd_pc d)).
Definition rb_check (d : sdesc) : bool := rb_check_with rb_facts d.

Variable d : sdesc.
Variable E : AX2.env.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hchk : rb_check d = true.

Local Notation rho := (rho_of TT E).
Local Notation H := (CXS.hid A argH E CS m).
Local Notation ms := (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)).

Lemma rb_parts :
  tt_wf TT = true
  /\ forallb (fun s => region_chk TT kn (sh_tag s) (sh_lo s) (sh_len s) (sh_al s)) shapes = true
  /\ ho_check2 IM rb_facts d = true
  /\ forallb (fact_tags_lt n) rb_facts = true
  /\ AX2.s_pc (CAP.a_ss CS) = to_Z (sd_pc d).
Proof.
  unfold rb_check, rb_check_with in Hchk. apply andb_prop in Hchk as [Hc Hpc]. apply andb_prop in Hc as [Hc Hlt].
  apply andb_prop in Hc as [Hc Hho]. apply andb_prop in Hc as [Hc Hrg]. apply andb_prop in Hc as [Hwf _].
  apply Z.eqb_eq in Hpc. tauto.
Qed.

Lemma rb_know : AX2S.know_ok segs E (mrestrict H FULL) kn.
Proof. exact (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS). Qed.

Lemma rb_cls : classes <> [] -> CxOpt.ledger_exact E (CAP.a_maps CS) /\ forallb cls_chk shapes = true.
Proof.
  intros Hne. unfold rb_check, rb_check_with in Hchk. apply andb_prop in Hchk as [Hc _]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hcl].
  destruct classes; [contradiction|]. apply andb_prop in Hcl as [Hcl Hsh]. apply andb_prop in Hcl as [Hnf0 Hpos].
  split; [|exact Hsh]. exact (CxOpt.ledger_exact_intro segs E _ kn rb_know _ Hnf0 Hpos).
Qed.


Lemma rb_noseg : forall x, H x = true -> PropExec.seg_rom segs x = None.
Proof.
  intros x Hx. pose proof (CXS.H_off_segments_cs segs A SEGS_in_hull HULL_ok argH ISP argH_high E CS m x Hx) as Hn.
  unfold PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Hn. reflexivity.
Qed.

Lemma rb_hull : forall a, CAP.img_lo A <= a < CAP.img_hi A -> H (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. destruct HULL_ok as (H0 & _ & _ & Hk). unfold CAP.KHI in Hk.
  assert (Eu : bv_unsigned (Z_to_bv 64 a) = a) by (apply br_lit_small; lia).
  unfold CXS.hid. apply orb_false_iff. split.
  - destruct (argH E (Z_to_bv 64 a)) eqn:Ea; [|reflexivity].
    destruct (argH_high E _ Ea) as [Hc _]. rewrite Eu in Hc. unfold CAP.CEIL in Hc. lia.
  - apply negb_false_iff. unfold CXS.vis. rewrite Eu. unfold CXS.in_hull.
    replace (CAP.img_lo A <=? a) with true by (symmetry; apply Z.leb_le; lia).
    replace (a <? CAP.img_hi A) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma rb_HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Proof.
  intros t rg Hg. destruct rb_parts as (_ & Hrg & _).
  unfold rb_M in Hg.
  destruct (iget_iof_list_map_In sh_tag sh_region _ _ _ Hg) as (r & Hr & Ht & ->). subst t.
  rewrite forallb_forall in Hrg. specialize (Hrg r Hr).
  exact (region_chk_sound segs E TT kn _ rb_know _ _ _ _ Hrg).
Qed.

(* [comment removed for export] *)
Lemma cls_neq_sound r r' : In r shapes -> In r' shapes -> cls_neq r r' = true ->
  hholds segs rho ms (HDisj (sh_tag r) (sh_lo r) (sh_len r) (sh_tag r') (sh_lo r') (sh_len r')).
Proof.
  intros Hr Hr' Hn. unfold cls_neq in Hn.
  destruct (cls (sh_tag r)) as [c|] eqn:Ec; [|discriminate]. destruct (cls (sh_tag r')) as [c'|] eqn:Ec'; [|discriminate].
  assert (Hne : classes <> []).
  { intros E0. unfold cls in Ec. rewrite E0 in Ec. discriminate. }
  destruct (rb_cls Hne) as [Hnf Hcl]. rewrite forallb_forall in Hcl.
  pose proof (Hcl r Hr) as H1. pose proof (Hcl r' Hr') as H2. unfold cls_chk in H1, H2. rewrite Ec in H1. rewrite Ec' in H2.
  apply andb_prop in H1 as [H1 L1]. apply andb_prop in H2 as [H2 L2]. apply Z.ltb_lt in L1, L2.
  assert (Hnw : forall s, In s shapes -> bv_unsigned (rho (sh_tag s)) + to_Z (sh_len s) < 2 ^ 63).
  { intros s Hs. destruct rb_parts as (_ & Hrg & _). rewrite forallb_forall in Hrg.
    destruct (region_chk_sound segs E TT kn _ rb_know _ _ _ _ (Hrg s Hs)) as (_ & _ & Hb & _). exact Hb. }
  pose proof (class_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hnf TT _ _ _ c H1 (Hnw r Hr)) as S1.
  pose proof (class_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hnf TT _ _ _ c' H2 (Hnw r' Hr')) as S2.
  cbn [hholds].
  destruct (Z_le_gt_dec (bv_unsigned (rho (sh_tag r)) + to_Z (sh_len r)) (bv_unsigned (rho (sh_tag r')) + to_Z (sh_lo r'))) as [Ha|Ha]; [left; exact Ha|].
  destruct (Z_le_gt_dec (bv_unsigned (rho (sh_tag r')) + to_Z (sh_len r')) (bv_unsigned (rho (sh_tag r)) + to_Z (sh_lo r))) as [Hb|Hb]; [right; exact Hb|].
  exfalso.
  set (x := Z.max (bv_unsigned (rho (sh_tag r)) + to_Z (sh_lo r)) (bv_unsigned (rho (sh_tag r')) + to_Z (sh_lo r'))).
  exact (class_apart segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hnf HULL_ok c c' x Hn
           (S1 x ltac:(unfold x; lia)) (S2 x ltac:(unfold x; lia))).
Qed.

Lemma rb_pairs_sound : forall l f, (forall s, In s l -> In s shapes) -> In f (rb_pairs l) -> hholds segs rho ms f.
Proof.
  induction l as [|r rest IH]; intros f Hsub Hin; [destruct Hin|].
  cbn [rb_pairs] in Hin. apply in_app_or in Hin as [Hin|Hin]; [|exact (IH f (fun s Hs => Hsub s (or_intror Hs)) Hin)].
  apply in_flat_map in Hin as (r' & Hr' & Hf). unfold rb_dfact in Hf.
  destruct (sh_tag r =? sh_tag r')%uint63; [destruct Hf|].
  destruct (cls_neq r r') eqn:Hcn.
  { destruct Hf as [<-|[]]. exact (cls_neq_sound r r' (Hsub r (or_introl eq_refl)) (Hsub r' (or_intror Hr')) Hcn). }
  destruct (disj_chk TT kn (cuts_of (sh_tag r)) (cuts_of (sh_tag r')) (sh_tag r) (sh_lo r) (sh_len r) (sh_tag r') (sh_lo r') (sh_len r')) eqn:Hd; [|destruct Hf].
  destruct Hf as [<-|[]]. cbn [hholds].
  exact (disj_chk_sound segs E TT kn _ rb_know _ _ _ _ _ _ _ _ Hd).
Qed.

Theorem rb_facts_hold : Forall (hholds segs rho ms) rb_facts.
Proof.
  destruct rb_parts as (Hwf & Hrg & _).
  apply Forall_forall. intros f Hin. unfold rb_facts in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  { unfold rb_rfacts in Hin. apply in_map_iff in Hin as (r & <- & Hr).
    rewrite forallb_forall in Hrg. cbn [hholds].
    exact (region_chk_sound segs E TT kn _ rb_know _ _ _ _ (Hrg r Hr)). }
  apply in_app_or in Hin as [Hin|Hin]; [exact (rb_pairs_sound _ f (fun s Hs => Hs) Hin)|].
  apply in_app_or in Hin as [Hin|Hin].
  - unfold rb_gfacts in Hin. apply in_flat_map in Hin as (i & _ & Hf).
    destruct (fact_of_reg TT (AX2.s_regs (CAP.a_ss CS)) i) as [f'|] eqn:Hfr; [|destruct Hf].
    destruct Hf as [<-|[]].
    apply (fact_of_reg_sound segs E TT M ms Hwf rb_HM _ i f' Hfr).
    exact (CXS.co_regs _ _ _ _ _ _ _ _ _ _ _ _ HCS).
  - unfold rb_kfacts in Hin. apply in_flat_map in Hin as (K & HK & Hf).
    destruct (fact_of_kentry TT M (CAP.img_lo A) (CAP.img_hi A) K) as [f'|] eqn:Hfk; [|destruct Hf].
    destruct Hf as [<-|[]].
    apply (fact_of_sound segs E TT M H ms Hwf rb_noseg (CAP.img_lo A) (CAP.img_hi A) rb_hull rb_HM K f' Hfk).
    exact (proj1 (Forall_forall _ _) rb_know K HK).
Qed.

Theorem rb_fillcov_hold : Forall (fill_ok segs E TT ms) rb_fillcov.
Proof.
  destruct rb_parts as (Hwf & _).
  apply Forall_forall. intros q Hin. unfold rb_fillcov in Hin. apply in_flat_map in Hin as (K & HK & Hq).
  apply (fill_cov1_sound segs E TT M H ms Hwf rb_noseg rb_HM K q Hq).
  exact (proj1 (Forall_forall _ _) rb_know K HK).
Qed.

Theorem rb_Rn : Rn segs IM n rho (state_of d) ms.
Proof.
  destruct rb_parts as (_ & _ & Hho & Hlt & Hpc).
  apply (handoff_Rn2 segs IM HIM HWR rb_facts d n rho ms Hho Hlt (rho_of_0 TT E) rb_facts_hold).
  - cbn [ms_pc_val PropExec.mkst]. rewrite Hpc. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

End Rev.

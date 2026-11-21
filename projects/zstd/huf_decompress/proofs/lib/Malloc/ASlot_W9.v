(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (gmf_geom, ta_fp_meta, ta_fp_grp and 5 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W9 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ASlot_W06ta_rel00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib6Malloc8ASlot_W93gmf00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_geomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib6Malloc>MallocFacts_AS5mw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W99gmf_availC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W99gmf_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W09tr_mrangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W96gmf_mwC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Malloc8ASlot_W08tr_areasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W98gmf_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABDmeta_slot_same_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Malloc8ASlot_W0:tr_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic2ex00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W9;decay_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ CTX <= a < CTX + 928
  \/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

(* [comment removed for export] *)
Record gmf (st : mstate) (sc : Z) (g : aptr) : Prop := mkGMF {
  gmf_slot : meta_slot st g;
  gmf_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  gmf_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  gmf_mw : mw_ok (get_meta_rec st g);
  gmf_sc48 : m_sizeclass (get_meta_rec st g) < 48;
  gmf_cls : m_sizeclass (get_meta_rec st g) = sc;
  gmf_grp : exists b gh, m_mem (get_meta_rec st g) = Some b /\ (s_groups st) !! b = Some gh /\ g_meta gh = Some g
             /\ 0 <= g_active_idx gh <= m_last_idx (get_meta_rec st g)
             /\ (m_sizeclass (get_meta_rec st g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec st g))
             /\ (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h);
  gmf_fbits : forall i, 0 <= i -> Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_abits : forall i, 0 <= i -> Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_links : exists n p, m_next (get_meta_rec st g) = Some n /\ m_prev (get_meta_rec st g) = Some p
}.

(* [comment removed for export] *)
Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
  taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
  taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
               gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
  taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
               gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
  taf_bnc : forall i, 0 <= bounces st i < 256
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gmf_geom st st1 sc g : ta_rel sc st st1 -> gmf st sc g ->
  meta_slot st1 g /\ 0 <= m_avail (get_meta_rec st1 g) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 g) < 2^32
  /\ mw_ok (get_meta_rec st1 g)
  /\ m_mem (get_meta_rec st1 g) = m_mem (get_meta_rec st g)
  /\ m_last_idx (get_meta_rec st1 g) = m_last_idx (get_meta_rec st g)
  /\ m_sizeclass (get_meta_rec st1 g) = m_sizeclass (get_meta_rec st g)
  /\ m_freeable (get_meta_rec st1 g) = m_freeable (get_meta_rec st g)
  /\ conc st1 g = conc st g.
Proof.
  intros TR GM. destruct (tr_geom _ _ _ TR g) as (E1 & E2 & E3 & E4 & E5).
  destruct (tr_mrange _ _ _ TR g (gmf_avail _ _ _ GM) (gmf_freed _ _ _ GM)) as [RA RF].
  pose proof (gmf_mw _ _ _ GM) as MW. unfold mw_ok in *. rewrite E2, E3, E4, E5.
  split; [eapply meta_slot_same_areas; [apply (tr_areas _ _ _ TR)| apply (gmf_slot _ _ _ GM)]|].
  repeat (split; [first [assumption| lia| reflexivity]|]).
  unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity.
Qed.

Lemma ta_fp_stack st lo sp a : lo <= a < sp -> ta_fp st lo sp a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "h01ah12loh22sph32sth41bh52ghh61qp;2p;1p;4p;6p;3g00EJj24Tg00=cj23Tg00F_j21Tg00Dej12Tg00;Kj10Tg00<0j16Tg00Tlj27Tg009Tj2=Tg00??j28Tg00a5j25Tg00`Sj1<Tg00aOj4;Tg00amj6:Tg00Qmj4DTg002:j4CTg00bNj1BTg002ej6ATg00cGj2@Tg00PBj3?Tg00cij29Tg00dCj3>Tg00YlR0g00WYR1f2R2f0R3'4f1R4,33'1f3R5/441342'1g00d]R6/44g00ZeR7#2#2#0#2#0#0#0#0#0#6,76,34'1g0000R6f5R8/=31883R8/42%07R7#2#0#0#0#6,78,32'1'1X66'5g00eVR8%<8P6P8P6g00XUR9g00_\R:P1g00fMR;C;R<P9P:g00`5P1P;g00ffE:R;P8CDP6P<P;P8CCP4f6R;#BEA1@833?18;4R;/45%07#2#6,7;,35'1'1X58'5X46,56'9'9;>3UX01X21X11X30P5P2P4P3O4X01X21W1W3o"). Qed.
Lemma ta_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> ta_fp st lo sp a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "h01ah12loh22sph32sth41bh52ghh61qp;2p;1p;4p;6p;3g00EJj24Tg00Dej13Tg00;Kj10Tg00<0j15Tg00Tlj27Tg00=cj22Tg00F_j21Tg009Tj2=Tg00??j28Tg00a5j26Tg00`Sj1<Tg00aOj4;Tg00amj6:Tg00Qmj4ETg002:j4DTg00bNj1CTg002ej6ATg00cGj2@Tg00PBj3?Tg00cij29Tg00dCj3>Tg00gDj3BTg00YlR0g00WYR1g00d]R2f0R3'4g00ZeR4#3#3#0#3#0#0#0#0#0#5,72R5,23'1f3R6f1R7'4f2R8,27'114271275'1R5g0000R2f5R9/=31893R9/48%04R4#3#0#0#0#5,79,28'1'1X62'6g00eVR9%<9P2P9P2g00XUR:g00_\R;P1g00fMR<C;R=P:P;g00`5P1P<g00ffE:R<P9CEP2P=P<P9CDP7f6R<#CEA1@933?18<7R</46%04#3#5,7<,26'1'1X59'6X42,62'9R2'9A>5233BUX01X21X11X30P6P8P7P3O4X01X21W1W3o"). Qed.
Lemma ta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> ta_fp st lo sp a.
Proof. intros; do 2 right; left. exists q; auto. Qed.
Lemma ta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> ta_fp st lo sp a.
Proof. intros; do 3 right. exists b, gh; auto. Qed.

(* [comment removed for export] *)
Lemma disjoint_high W A n : (forall lo hi, In (lo, hi) W -> hi <= ATOP) -> ATOP <= A -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros HW HA; cbn; [exact I|].
  split; [pose proof (HW lo hi ltac:(left; reflexivity)); lia|]. apply IH; [|exact HA]. intros lo' hi' Hin. apply (HW lo' hi'). right. exact Hin.
Qed.


(* [comment removed for export] *)
Lemma decay_cases c st : decay_bounces c st = st \/ exists v, decay_bounces c st = set_bounce (c - 7) v st.
Proof. unfold decay_bounces. destruct (_ && _); [right; eexists; reflexivity| left; reflexivity]. Qed.
Lemma active_decay c st i : active (decay_bounces c st) i = active st i.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma rec_decay c st q : get_meta_rec (decay_bounces c st) q = get_meta_rec st q.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma active_upd_meta g f st i : active (upd_meta g f st) i = active st i.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
Variables (ra sp gp tp t0 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Let spv := bv_unsigned sp.

(* [comment removed for export] *)
Definition nclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.
End PHASE.


End CANSEC1.

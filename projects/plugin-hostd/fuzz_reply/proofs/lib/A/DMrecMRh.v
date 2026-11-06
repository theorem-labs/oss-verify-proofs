(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrecM.v (commit 67fc7ef5787, lane B1 drain composition, DoRecycle chain; the chain's two function pairs, Quarantine::DoRecycle and LocalCache::Deallocate, re-checked EQUAL-mod-pcrel by cmpkit 4bbd3a74be89 strictcmp2 16982e3ef42b; file sha256 9d6395314d60) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/DMrecM.v; 60 of its 125 lines of code are new or changed and 76 lines of the source are left out. *)
(* F1 priming row R3 (re-hide at a secondary recycle): Quarantine::DoRecycle (0x33cf8), its two loops and its walk
   over YG0dH.amreal' at YGcfRehidePost.RZ_cf, made from lib/A/DMrecM.v (ITEMS_r, LOOP_r, dorecycle_arm_r).  The
   loops are DMrecM's, step for step, at DMrecLRh's states, with these changes only:
   - each step's continuation is YG0dH.amreal' (amreal'_mbind / amreal'_SRr_pre / amreal'_ret), each machine
     segment lifted by YA0nH.SRr_SRr';
   - the Recycle call is DIfaceRh.de_rchunk_m_rh_t (its leaf states YGcfRehidePost.acall_post_x_rh), and the
     CacheDealloc call is the released MnRecycle.de_cdealloc_m_t, lifted by YG0dH.amreal_amreal';
   - at each call the model's step fact is added to the leaf by YG0dHc.amreal'_apost
     (YGcfRecStep.recycle_chunk_rec_step / cache_dealloc_rec_step), which DMrecT4Rh.RC_post_rh / CD_post_rh read;
   - the walk's leaf is DMwalkIFRh.dr_leaf_rh: the empty list's return is DMrecT2.RETE_r lifted by
     DMwalkIFRh.dr_leaf_rh_of, and the first state is DMrecT2.T_E_r's, lifted by DMrecLRh.OSTrh_of (the entry is
     its own model state: DMrecLRh.rs_refl).
   The item step [HT_R] and the count-0 step [HT_O0] are Section hypotheses here, as in DMrecM; DMrecFRh.v proves
   both (DMrecT5Rh.T_R_rh, DMrecT6Rh.T_O0_rh).  A new file, so that DMrecM.v stays byte-unchanged.
   rule 24: proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (loops
   at the re-hide twins). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH YG0dHc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFf2 AFh9 AFha AFhc AFhb.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFhf AFhd AFhl AFhg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply DIfaceR DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MnRecycle DMwalkIF DMrecL DMrecT2 DMrecM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost YGcfRecStep DIfaceRh DMwalkIFRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMrecLRh DMrecT3Rh DMrecT4Rh.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.
Hypothesis TB : TfibSyms B.
Hypothesis HRM : DMwalkIF.rmaxd_ok RMAXD.
Hypothesis RV : DMwalkIF.di_rview_x_t B ARXr DRq RMAXD.
Hypothesis FR : di_frame_t ARXr AOX.
Variables (ly : alayout) (X0 : astate) (P0 : list batch) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE : DMwalkIF.dr_pre_r B ARXr AOX DRq (as_inst B) ly X0 P0 W0 regs0 mem0 md0.
Local Notation RZ := YGcfRehidePost.RZ_cf.
Local Notation zlen := (@AFhd.zlen _).
Local Notation sp1 := (AFhd.sp1 regs0).
Local Notation ostrh := (DMrecLRh.ostrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation rstrh := (DMrecLRh.rstrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation OSTrh := (DMrecLRh.OSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation RCSTrh := (DMrecLRh.RCSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation RSTrh := (DMrecLRh.RSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation CDSTrh := (DMrecLRh.CDSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation QSTrh := (DMrecLRh.QSTrh B ARXr AOX DRq ly X0 W0 regs0 mem0 md0).
Local Notation FINh := (DMwalkIFRh.dr_leaf_rh B ARXr AOX DRq (as_inst B) ly X0 W0 regs0 mem0 md0).
Definition postRIrh (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W' : world tfibsegs) (c' : config) : Prop :=
match its with [] => CDSTrh X b t W' c' | _ :: _ => RCSTrh X b t its i W' c' end.
(* the item-loop step (AFhk.segYR from the Recycle return) and the count-0 step (DMrecZ.segZ from the pop) *)
Hypothesis HT_R : forall X b t its i lz qb W regs mem md, rstrh X b t its i lz qb W regs mem md ->
SRr tfibsegs W (cfg_at tfibsegs 0x33dbc regs mem md) (postRIrh X b t its i).
Hypothesis HT_O0 : forall X b t lz qb W regs mem md, ostrh X (b :: t) lz qb W regs mem md -> b_items b = [] ->
SRr tfibsegs W (cfg_at tfibsegs 0x33d70 regs mem md) (CDSTrh X b t).
Hypothesis RCH : DIfaceRh.de_rchunk_m_rh_t B ARXr AOX DRq.
Hypothesis CDH : MnRecycle.de_cdealloc_m_t B ARXr AOX DRq.

Lemma ITEMS_rh : forall b t its i fuel X W c, RCSTrh X b t its i W c -> (length its <= fuel)%nat ->
amreal' tfibsegs RZ (recycle_items fuel its X) W c (fun r W' c' => CDSTrh (snd r) b t W' c').
Proof.
intros b t its. induction its as [|k ks IH]; intros i fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. pose proof ST as [_ _ _ _ NE]. exact (NE eq_refl).
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [recycle_items].
apply (amreal'_mbind tfibsegs RZ (recycle_chunk k) (fun _ => recycle_items f ks) X W c (fun r W' c' => RSTrh (snd r) b t ks (S i) W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
destruct (DMrecT4Rh.RC_pre_rh B ARXr AOX DRq RMAXD TB RV ly X0 P0 W0 regs0 mem0 md0 PRE X b t k ks i lz qb W regs mem md ST) as [RP DQ].
eapply amreal'_mono; [| exact (amreal'_apost tfibsegs RZ _ _ W _ _ (YGcfRecStep.recycle_chunk_rec_step ly k X)
  (RCH (as_inst B) ly X k (ks ++ flat_map b_items t) (b_self b :: map b_self t) (sp1 + 8) W regs mem md RP DQ))].
intros r W' c' [STP HL].
exact (DMrecT4Rh.RC_post_rh B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE X b t k ks i lz qb W regs mem md r W' c' ST STP HL).
+ intros [] X1 W1 c1 ST1. destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
eapply amreal'_SRr_pre; [exact (SRr_SRr' tfibsegs RZ _ _ _ (HT_R X1 b t ks (S i) lz qb W1 regs mem md ST1))|].
intros W2 c2 _ HP. unfold postRIrh in HP. destruct ks as [|k' ks'].
* destruct f; cbn [recycle_items]; apply amreal'_ret; cbn [snd]; exact HP.
* apply (IH (S i) f X1 W2 c2 HP). cbn in Hfuel |- *. lia.
Qed.

Lemma LOOP_rh : forall rest fuel X W c, OSTrh X rest W c -> (length rest <= fuel)%nat ->
amreal' tfibsegs RZ (do_recycle fuel rest X) W c FINh.
Proof.
induction rest as [|b t IH]; intros fuel X W c ST Hfuel.
- destruct ST as (lz & qb & regs & mem & md & -> & ST). exfalso. pose proof ST as [_ _ _ NE]. exact (NE eq_refl).
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [do_recycle].
apply (amreal'_mbind tfibsegs RZ (recycle_items 1100 (b_items b)) (fun _ => YG00.bind (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t)) X W c
(fun r W' c' => CDSTrh (snd r) b t W' c')).
+ destruct ST as (lz & qb & regs & mem & md & -> & ST).
destruct (b_items b) as [|k0 ks] eqn:Hk.
* (* the COUNT-0 arm *)
eapply amreal'_SRr_pre; [exact (SRr_SRr' tfibsegs RZ _ _ _ (HT_O0 X b t lz qb W regs mem md ST Hk))|].
intros W1 c1 _ H1. cbn [recycle_items]. apply amreal'_ret. cbn [snd]. exact H1.
* eapply amreal'_SRr_pre; [exact (SRr_SRr' tfibsegs RZ _ _ _
  (DMrecT3Rh.T_O_rh B ARXr AOX DRq RMAXD TB HRM RV FR ly X0 P0 W0 regs0 mem0 md0 PRE X b t lz qb W regs mem md k0 ks ST Hk))|].
intros W1 c1 _ [H1 _]. rewrite <- Hk. apply (ITEMS_rh b t (b_items b) 0 1100 X W1 c1 H1).
destruct H1 as (lz1 & qb1 & regs1 & mem1 & md1 & _ & ST1). pose proof ST1 as [_ _ _ _ _ BL]. unfold kBatchSlots in BL. cbn in BL. lia.
+ intros [] X1 W1 c1 ST1.
apply (amreal'_mbind tfibsegs RZ (cache_dealloc kBatchClass (b_self b)) (fun _ => do_recycle f t) X1 W1 c1 (fun r W' c' => QSTrh (snd r) t W' c')).
* destruct ST1 as (lz & qb & regs & mem & md & -> & ST1).
destruct (DMrecT4Rh.CD_pre_rh B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE X1 b t lz qb W1 regs mem md ST1) as [CP DQ].
eapply amreal'_mono; [| exact (amreal'_apost tfibsegs RZ _ _ W1 _ _ (YGcfRecStep.cache_dealloc_rec_step ly (b_self b) X1)
  (amreal_amreal' tfibsegs RZ _ _ _ _ (CDH (as_inst B) ly X1 (flat_map b_items t) (b_self b) (map b_self t) W1 regs mem md CP DQ)))].
intros r W' c' [STP HL].
exact (DMrecT4Rh.CD_post_rh B ARXr AOX DRq RMAXD TB HRM RV ly X0 P0 W0 regs0 mem0 md0 PRE X1 b t lz qb W1 regs mem md r W' c' ST1 STP HL).
* intros [] X2 W2 c2 ST2. destruct ST2 as (lz & qb & regs & mem & md & -> & ST2).
eapply amreal'_SRr_pre; [exact (SRr_SRr' tfibsegs RZ _ _ _
  (DMrecT4Rh.T_Q_rh B ARXr AOX DRq TB FR ly X0 P0 W0 regs0 mem0 md0 PRE X2 t lz qb W2 regs mem md ST2))|].
intros W3 c3 _ [HP _]. unfold DMrecT4Rh.postQOrh in HP. destruct t as [|b' t'].
-- destruct f; cbn [do_recycle]; apply amreal'_ret; exact HP.
-- apply (IH f X2 W3 c3 HP). cbn in Hfuel |- *. lia.
Qed.

Theorem dorecycle_arm_rh : amreal' tfibsegs RZ (do_recycle (length P0) P0 X0) W0 (cfg_at tfibsegs A_DoRecycle regs0 mem0 md0) FINh.
Proof.
pose proof (DMrecM.walk_E_r B ARXr AOX DRq TB ly X0 P0 W0 regs0 mem0 md0 PRE) as WALK. unfold AFh9.postE in WALK.
assert (CASES : P0 = [] \/ exists b t, P0 = b :: t) by (clear; destruct P0 as [|b t]; [left; reflexivity | right; exists b, t; reflexivity]).
destruct CASES as [EP|(b & t & EP)].
- rewrite EP in WALK |- *. rewrite zlen_nil, Z.eqb_refl in WALK. unfold amreal'. cbn [length do_recycle amrealG ret].
eapply SRrG_mono; [exact (SRr_SRr' tfibsegs RZ _ _ _ WALK)|]. intros W' c' _ HP.
apply DMwalkIFRh.dr_leaf_rh_of. exact (DMrecT2.RETE_r B ARXr AOX DRq TB FR ly X0 P0 W0 regs0 mem0 md0 PRE 0 W' c' EP HP).
- replace (zlen P0 =? 0) with false in WALK by (symmetry; apply Z.eqb_neq; rewrite EP, zlen_cons; unfold AFhd.zlen; lia).
eapply amreal'_SRr_pre; [exact (SRr_SRr' tfibsegs RZ _ _ _ WALK)|]. intros W' c' _ HP.
apply (LOOP_rh P0 (length P0) X0 W' c'); [|lia].
apply (DMrecLRh.OSTrh_of B ARXr AOX DRq ly X0 W0 regs0 mem0 md0 X0 P0 W' c'); [|apply DMrecLRh.rs_refl].
exact (DMrecT2.T_E_r B ARXr AOX DRq RMAXD TB HRM RV FR ly X0 P0 W0 regs0 mem0 md0 PRE W' c' HP).
Qed.
End e.
End c.

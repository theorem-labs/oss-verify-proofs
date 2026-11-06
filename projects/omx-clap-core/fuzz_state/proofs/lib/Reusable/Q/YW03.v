(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO0q YO15 YO10 YO0t YO0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.Q Require Import YW02 RzInv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN03.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma big_block_direct A g am idx fr :
WF A -> usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr ->
MMAP_THRESHOLD < fr_n fr ->
am_sc am = 63 /\ idx = 0 /\ am_last am = 0 /\ 1 <= am_maplen am /\
stride_of am = am_maplen am * 4096 - UNIT /\
UNIT * fr_off fr + fr_n fr <= am_maplen am * 4096 - UNIT - IB.
Proof.
intros HW Hu Hidx Hfr Hbig.
pose proof (inv_groups HW g am Hu) as ((Glast & _ & Glen & _) & Gml & Gsl & Gcl & Gmp & _).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (F1 & F2 & F3 & _) & _).
destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & _) | (C1 & C2 & C3 & C4)].
- assert (Hs : stride_of am = am_maplen am * 4096 - UNIT).
{ unfold stride_of. rewrite C2. cbn [Z.eqb andb]. destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
rewrite Hs in F3. repeat split; auto; lia.
- exfalso. pose proof (class_size_bounds (am_sc am) C1) as Hcs.
assert (Hst : stride_of am <= 131056).
{ unfold stride_of in *. destruct ((am_last am =? 0) && negb (am_maplen am =? 0)) eqn:E; [|lia].
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. destruct (am_maplen am =? 0) eqn:E3; [discriminate|]. apply Z.eqb_neq in E3.
destruct (Gmp ltac:(lia)) as (r & rg & _ & _ & _ & _ & _ & _ & Hsmall).
pose proof (Hsmall E1 ltac:(lia)) as Hsm. unfold page_round, PGSZ, UNIT in Hsm.
pose proof (Z.mul_div_le (class_size (am_sc am) + 16 + 4096 - 1) 4096 ltac:(lia)). unfold UNIT. lia. }
unfold MMAP_THRESHOLD, UNIT, IB in *. lia.
Qed.
Section b.
Variables (A : astate) (g : sptr) (am : ameta) (fr : frame) (n : Z).
Hypothesis HW : WF A.
Hypothesis Hu : usedX [] A g am.
Hypothesis Hfr : ss_fr (nth_slot am 0) = Some fr.
Hypothesis H63 : am_sc am = 63.
Hypothesis Hlast : am_last am = 0.
Hypothesis Hn : MMAP_THRESHOLD <= n.
Hypothesis Hn62 : n < 2 ^ 62.
Definition p : sptr := frame_ptr am 0 fr.
Definition needed : Z := page_round (n + UNIT * fr_off fr + UNIT + IB).
Definition old_len : Z := am_maplen am * 4096.
Definition rid : nat := prid (am_mem am).
Definition am_eq : ameta := upd_slot am 0 (resize_slot (stride_of am) 0 (nth_slot am 0) (fr_off fr) n).
Definition A_eq : astate := upd_meta g (MUsed am_eq) A.
Definition r' : nat := length (st_regions A).
Definition A1 : astate := set_regions (st_regions A ++ [mkRegion RkMap needed [] true]) A.
Definition am_ok : ameta := remap_am am r' (needed / 4096) 0 (fr_off fr) n.
Definition A2 : astate := upd_meta g (MUsed am_ok) A1.
Definition A_ok : astate :=
set_regions (lupd (st_regions A2) rid (mkRegion RkMap (rg_len (nth rid (st_regions A2) (mkRegion RkMap 0 [] false))) [] false)) A2.
Definition p_ok : sptr := padd (slot_start am_ok 0) (UNIT * fr_off fr).
Lemma Hff : find_frame_in (st_metas A) p = Some (g, 0).
Proof. apply (find_frame_in_spec [] None U0 A HW g am 0 fr Hu); [rewrite Hlast; lia | exact Hfr]. Qed.
Lemma Mg : mlookup (st_metas A) g = Some (MUsed am).
Proof. exact (proj1 (usedX_MT _ _ _ _ Hu)). Qed.
Lemma realloc_tree :
realloc (Some p) n A =
if old_len =? needed then IRet (Some p, A_eq)
else IAsk (KMremap rid old_len needed) A
(fun z => if negb (z =? 0) then IRet (Some p_ok, A_ok) else realloc_move p n A).
Proof.
unfold realloc.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
unfold bind at 1. unfold find_frame. unfold bind at 1. unfold get. cbn [ibind]. rewrite Hff.
unfold ret at 1. cbn [ibind fst snd].
unfold bind at 1. unfold getm at 1. unfold bind at 1. unfold get. cbn [ibind]. rewrite Mg. unfold ret at 1. cbn [ibind].
rewrite Hfr.
replace (n <? MMAP_THRESHOLD) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. cbn [andb].
rewrite H63. cbn [Z.leb Z.compare Pos.compare Pos.compare_cont]. rewrite (proj2 (Z.leb_le _ _) Hn). cbn [andb].
unfold bind at 1. unfold massert. cbn [Z.eqb Pos.eqb]. unfold ret at 1. cbn [ibind].
fold needed. fold old_len. fold rid.
destruct (old_len =? needed).
- unfold bind, setm, modify, ret. cbn [ibind]. reflexivity.
- unfold bind at 1. unfold ask. cbn [ibind]. f_equal.
apply FunctionalExtensionality.functional_extensionality. intros z.
destruct (negb (z =? 0)); [|reflexivity].
unfold bind, new_region, bind, get, put, setm, modify, upd_region, ret. cbn [ibind]. reflexivity.
Qed.
Lemma needed_facts : n + UNIT * fr_off fr + UNIT + IB <= needed /\ needed mod PGSZ = 0 /\ 0 < needed < 2 ^ 63.
Proof.
pose proof (page_round_ge (n + UNIT * fr_off fr + UNIT + IB)) as H1. pose proof (page_round_mod (n + UNIT * fr_off fr + UNIT + IB)) as H2.
fold needed in H1, H2.
pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & _). pose proof (Gsl 0 ltac:(rewrite Hlast; lia)) as (_ & _ & S3).
rewrite Hfr in S3. destruct S3 as (_ & _ & (_ & F2 & _) & _).
repeat split; try assumption.
- unfold MMAP_THRESHOLD, UNIT, IB in *. lia.
- unfold needed, page_round, PGSZ, UNIT, IB, MMAP_THRESHOLD in *.
pose proof (Z.mul_div_le (n + 16 * fr_off fr + 16 + 4 + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.


End b.
Section c.
Variable segs : list Segment.
Lemma SR_step_inv : forall ms model ms' Q,
m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
SR segs (mkCfg ms model) Q -> SR segs (mkCfg ms' model) Q.
Proof.
intros ms model ms' Q Hh Hlz Hsvc Hstep H. exact (SR_det_inv segs ms model ms' Q Hh Hlz Hsvc Hstep H).
Qed.
Lemma mreal_step_inv {R} : forall ms model ms' (t : itree astate R) Q,
m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
mreal segs (mkCfg ms model) t Q -> mreal segs (mkCfg ms' model) t Q.
Proof.
intros ms model ms' t Q Hh Hlz Hsvc Hstep H. destruct t as [r | q snap k | f]; cbn in *.
- eapply SR_step_inv; eauto.
- eapply SR_step_inv; eauto.
- exact I.
Qed.
End c.
End a.

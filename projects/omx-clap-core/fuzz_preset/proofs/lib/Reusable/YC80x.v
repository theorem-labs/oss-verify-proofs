(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the position-abstract-listing runner of
   proofs/cgif/cgif_file_fuzzer/lib/YC80.v (origin/ossv/recipes c8557374ad2e :52-140) restated over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp threaded as YCbqG.v's SRr_chain_tok_AJx does,
   program statics PST); plus mixed-write twins (suffix m) whose write premise also admits the program's own statics PST,
   from the journal lemma ajournal_x_exec_mixed below. Generic: no image class, no address, no ledger.
   SK (YI16.sink_head) is a Context parameter of every lemma here. Global sink_head instances exist in this tree
   (YI5b.v src0_sink_head, YE2k.v / AE2k.v tfib_sink_head): pass SK explicitly at every use, never let it be inferred. *)
(* Theorem Labs, 2026-10: a memory invariant P : (word -> option byte) -> Prop carried across the runner; the generic
   part, moved here from YSRrMemnorm.v (which keeps P's memnorm instance over YAkMemnorm and srr_inv_laws_imp;
   YSRrMemnormJ.v holds the YAjMemnorm instance, YC1fPx.v the runners paj_run_*_inv and their tactics).
   rule 24: no function proved. rule 24: proves no function (kind: engine lemmas).
   WHY: a walk proves an SRr goal (YA0n.v:35, CPS over srealizes), and SRr does not show the reached state, so
   SRr W c Q -> SRr W c (Q /\ P ..) has no generic proof. The runner reaches every end state through one primitive,
   YA0n.SRr_msteps (:149), whose continuation receives mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model'.
   WHAT:
   - Record srr_inv_laws: P survives the three memory changes of one SRr_msteps run: the restriction YK04.mrestrict
     (the ms_mem of YK04.restrict, YK04.v:28), a machine-step run YK0i.msteps, and the merge YK04.munrestrict (the
     ms_mem of YK04.unrestrict, YK04.v:36). srr_inv_laws_true: the trivial P.
   - SRr_msteps_inv / SRr_step_inv: YA0n.SRr_msteps (:149) / SRr_step (:133, one hand step) with the premise
     P (ms_mem ms) and the continuation premise P on the end memory. Each applies the original, it does not re-prove
     it; one step is an msteps run of length one (YK0i.msteps_one), and `change` checks the two memory equalities.
   - No twin of SRr_node / SRr_nodeI (YA0n.v:105-129): P on node_ok's nx i needs P kept by every silent sstep_cfg
     step (R/Cfg.v), the universal form avoided here; the walk states P of its own nx.
   - Section ei, inside Section e (its lemmas take Section e's binders, then P and its laws PLAW):
     run_post_pi_tok_AJx_inv, run_post_pi_tok_AJx with the premise P (ms_mem ms') after the journal, and the _inv
     forms of the six runner lemmas, with the premise P (ms_mem ms) right after the journal premise (AJ).
   - Section e's six runner lemmas are their R forms at wle, and those are the _invR forms at P := fun _ => True;
     their statements are unchanged.
     run_post_pi_tok_AJx stays its own definition: the _inv one at True has one more premise.
   No lib/Lib/Mem.v and no lia redefinition (lib/Lib/LiaTwx2.v) enters this file's Require closure. *)
(* Modified by Theorem Labs, 2026-10: the forms over a world relation R (suffix R). A free or realloc of a live block
   can hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle (YA0nH.wle' at a
   zone). run_post_pi_tok_AJxR / run_post_pi_tok_AJx_invR are the posts with the journal at R (YCbqG.v ajournal_xR)
   and the conclusion SRrG segs R. Each runner lemma has an R form whose first arguments (after the Section's) are R
   and its two laws (reflexive, transitive), so a runner applied to them has the plain runner's binders in the plain
   order and the tactics of YC1fPx.v apply it unchanged. SRr_msteps_invR / SRr_step_invR (over YSRrG.v's
   SRrG_msteps / SRrG_step) and ajournal_x_exec_mixedR (over YCbqG.v's ajournal_x_execR / ajournal_x_pst_writeR) are
   the step and journal lemmas they rest on. Each plain lemma is its R form at wle (wle_refl / wle_trans); its
   statement is unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* Numerals in this file, all as cgif YC80.v / YCbqG.v state them: 64 and 32 (WORD: bit widths), 2 ^ 40 and 2 ^ 64
   (LENGTH: code-span bound, word range), 4 (LENGTH: instruction bytes; text alignment), 0 (DERIVED: listing start offset;
   lower bound). No ADDRESS. *)
(* Membership of an address in a list of ranges is decidable (in_zr is YG0n.v:197). *)
Lemma Exists_in_zr_dec : forall (R : list (Z * Z)) (a : Z), {Exists (in_zr a) R} + {~ Exists (in_zr a) R}.
Proof.
intros R a. apply Exists_dec. intros r. unfold in_zr.
destruct (Z_le_dec (fst r) a) as [H1|H1]; [destruct (Z_lt_dec a (fst r + snd r)) as [H2|H2]|].
- left. lia.
- right. lia.
- right. lia.
Qed.
(* The three memory changes of one SRr_msteps run that P must survive. *)
Record srr_inv_laws (segs : list Segment) (P : (word -> option byte) -> Prop) : Prop := {
  sil_mrestrict : forall (H : word -> bool) (m : word -> option byte), P m -> P (YK04.mrestrict H m);
  sil_msteps : forall ms ms', YK0i.msteps segs ms ms' -> P (ms_mem ms) -> P (ms_mem ms');
  sil_munrestrict : forall (H : word -> bool) (full m' : word -> option byte),
    P full -> P m' -> P (YK04.munrestrict H full m') }.
(* The trivial invariant: Section e's runner lemmas are the _inv forms at it. *)
Lemma srr_inv_laws_true : forall segs : list Segment, srr_inv_laws segs (fun _ => True).
Proof.
intros segs. split; intros; exact I.
Qed.
Section s.
Variable segs : list Segment.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
(* YSRrG.SRrG_msteps over a world relation R, with P on the start memory and P on the end memory. *)
Lemma SRr_msteps_invR : forall (R : world segs -> world segs -> Prop) W ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
P (ms_mem ms) ->
(forall model', same_but_materialized model model' ->
hclean (w_H W) msr' ->
P (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) ->
SRrG segs R W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRrG segs R W (mkCfg ms model) Q.
Proof.
intros R W ms msr' model Q Hms HPm Hk.
apply (SRrG_msteps segs R Hwx W ms msr' model Q Hms).
intros model' Hsame Hcl. apply (Hk model' Hsame Hcl).
change (P (YK04.munrestrict (w_H W) (ms_mem ms) (ms_mem msr'))).
apply (@sil_munrestrict segs P PLAW); [exact HPm|].
apply (@sil_msteps segs P PLAW (restrict (w_H W) ms) msr' Hms).
change (P (YK04.mrestrict (w_H W) (ms_mem ms))).
apply (@sil_mrestrict segs P PLAW). exact HPm.
Qed.
(* YA0n.SRr_msteps (:149) with P on the start memory and P on the end memory. *)
Lemma SRr_msteps_inv : forall W ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
P (ms_mem ms) ->
(forall model', same_but_materialized model model' ->
hclean (w_H W) msr' ->
P (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) ->
SRr segs W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr segs W (mkCfg ms model) Q.
Proof. exact (SRr_msteps_invR (@wle segs)). Qed.
(* YSRrG.SRrG_step over a world relation R (one hand step), with P on the start memory and P on the end memory. *)
Lemma SRr_step_invR : forall (R : world segs -> world segs -> Prop) W ms msr' model Q,
ms_svc_pending ms = None ->
RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
P (ms_mem ms) ->
(forall model', same_but_materialized model model' ->
P (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) ->
SRrG segs R W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRrG segs R W (mkCfg ms model) Q.
Proof.
intros R W ms msr' model Q Hsvc Hs HPm Hk.
apply (SRrG_step segs R Hwx W ms msr' model Q Hsvc Hs).
intros model' Hsame. apply (Hk model' Hsame).
change (P (YK04.munrestrict (w_H W) (ms_mem ms) (ms_mem msr'))).
apply (@sil_munrestrict segs P PLAW); [exact HPm|].
apply (@sil_msteps segs P PLAW (restrict (w_H W) ms) msr').
- apply (msteps_one segs (restrict (w_H W) ms) msr'); [exact Hsvc | exact Hs].
- change (P (YK04.mrestrict (w_H W) (ms_mem ms))).
  apply (@sil_mrestrict segs P PLAW). exact HPm.
Qed.
(* YA0n.SRr_step (:133), one hand step, with P on the start memory and P on the end memory. *)
Lemma SRr_step_inv : forall W ms msr' model Q,
ms_svc_pending ms = None ->
RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
P (ms_mem ms) ->
(forall model', same_but_materialized model model' ->
P (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) ->
SRr segs W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr segs W (mkCfg ms model) Q.
Proof. exact (SRr_step_invR (@wle segs)). Qed.
End s.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section j.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* ajournal_x_exec_mixed below over a world relation R: the same split at memi, over ajournal_x_execR and
   ajournal_x_pst_writeR (YCbqG.v). *)
Lemma ajournal_x_exec_mixedR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Hfr Hgr Hhid Hsame HW.
unfold mem_grows, mrestrict in Hgr. unfold mrestrict in Hfr.
pose (memi := fun x : word => if Exists_in_zr_dec PST (bv_unsigned x) then memc x else memc' x).
assert (HJi : ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memi mdc' k).
{ apply (ajournal_x_execR segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memi mdc'
(fun a => Wr a /\ ~ Exists (in_zr a) PST) HJ).
- intros x Hx. specialize (Hfr x). revert Hfr. unfold mrestrict, memi. destruct (w_H Wc x); intros Hfr; [reflexivity|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [reflexivity|].
apply Hfr. intros Hw. exact (Hx (conj Hw Hq)).
- unfold mem_grows, mrestrict, memi. intros x. specialize (Hgr x). revert Hgr. destruct (w_H Wc x); intros Hgr; [exact (fun H => H)|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact (fun H => H) | exact Hgr].
- intros x Hh. unfold memi. destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [reflexivity | exact (Hhid x Hh)].
- exact Hsame.
- intros a [Hw Hq]. destruct (HW a Hw) as [Hb|Hb]; [exact Hb | contradiction]. }
apply (ajournal_x_pst_writeR segs B PST ARx LAWS segs_low PST_ok R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memi mdc' k memc' mdc' HJi).
- intros x Hx. unfold mrestrict, memi. destruct (w_H Wc x); [reflexivity|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [contradiction | reflexivity].
- unfold mem_grows, mrestrict, memi. intros x. specialize (Hgr x). revert Hgr. destruct (w_H Wc x); intros Hgr; [exact (fun H => H)|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact Hgr | exact (fun H => H)].
- intros x Hh. unfold memi. destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact (Hhid x Hh) | reflexivity].
- apply same_but_materialized_refl.
Qed.
(* YCbqG.v's ajournal_x_exec (:365) with a write set Wr that may also cover the program's own statics PST: a function's
   straight-line code writes its own frame and its statics between two calls. The memory change splits at an
   intermediate memory memi (memc' off PST, memc on PST): memc -> memi is ajournal_x_exec over Wr minus PST, and
   memi -> memc' is ajournal_x_pst_write (YCbqG.v:402). No premise beyond ajournal_x_exec's and PST_ok. *)
Lemma ajournal_x_exec_mixed : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof. exact (ajournal_x_exec_mixedR (@wle segs)). Qed.
End j.
Section e.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis Hwx : wx_segs_nowrap segs.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Variable tw0 : ctable.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Hypothesis Htw : tw_of 0 listing = tw0.
Local Notation AJ := (ajournal_x segs B PST ARx).
Local Notation AJR R := (ajournal_xR segs B PST ARx R).
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).
(* cgif YC80.v:52-68 (origin/ossv/recipes) over ajournal_x, Hp after S and Hpc after Sc. *)
Definition run_post_pi_tok_AJx (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(r : ptrun_status psym)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) (restrict (w_H W) ms')
| _ => st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
end ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* run_post_pi_tok_AJx over a world relation R: the journal at R and the conclusion SRrG segs R. *)
Definition run_post_pi_tok_AJxR (R : world segs -> world segs -> Prop) (W : world segs) (E : env) (K : nat) (Bx : sv)
(SH : list shent) (ss : sstate) (st' : shst)
(r : ptrun_status psym)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) (restrict (w_H W) ms')
| _ => st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
end ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRrG segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* The invariant forms (suffix _inv): Section e's binders, then P and its laws PLAW. *)
Section ei.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
(* run_post_pi_tok_AJx with the premise P (ms_mem ms') after the journal. *)
Definition run_post_pi_tok_AJx_inv (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(r : ptrun_status psym)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) (restrict (w_H W) ms')
| _ => st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
end ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
P (ms_mem ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* run_post_pi_tok_AJx_inv over a world relation R: the journal at R and the conclusion SRrG segs R. *)
Definition run_post_pi_tok_AJx_invR (R : world segs -> world segs -> Prop) (W : world segs) (E : env) (K : nat) (Bx : sv)
(SH : list shent) (ss : sstate) (st' : shst)
(r : ptrun_status psym)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) (restrict (w_H W) ms')
| _ => st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
end ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
P (ms_mem ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRrG segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* SRr_chain_pi_tok_AJx_inv below over a world relation R; the journal step is ajournal_x_execR, the run step
   SRr_msteps_invR. *)
Lemma SRr_chain_pi_tok_AJx_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx_invR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (SRr_msteps_invR segs Hwx P PLAW R W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_execR segs B PST ARx LAWS segs_low R) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
(* cgif YC80.v:69-102 (origin/ossv/recipes) over ajournal_x; the journal step is YCbqG.v's ajournal_x_exec, the run
   step SRr_msteps_inv. *)
Lemma SRr_chain_pi_tok_AJx_inv : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx_inv W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_pi_tok_AJx_invR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_pi_tok_AJx_inv below over a world relation R. *)
Lemma SRr_run_pi_tok_AJx_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx_invR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJx_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
(* cgif YC80.v:103-121 (origin/ossv/recipes) over ajournal_x. *)
Lemma SRr_run_pi_tok_AJx_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx_inv W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_pi_tok_AJx_invR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_pi_tok_AJx_inv below over a world relation R. *)
Lemma SRr_run_to_pi_tok_AJx_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx_invR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJx_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
(* cgif YC80.v:122-140 (origin/ossv/recipes) over ajournal_x. *)
Lemma SRr_run_to_pi_tok_AJx_inv : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx_inv W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_tok_AJx_invR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_chain_pi_tok_AJxm_inv below over a world relation R; the journal step is ajournal_x_exec_mixedR. *)
Lemma SRr_chain_pi_tok_AJxm_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx_invR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (SRr_msteps_invR segs Hwx P PLAW R W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_mixedR segs B PST ARx LAWS segs_low PST_ok R) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
(* Mixed-write twins: the straight-line stretch may write, besides the bytes awr_byte admits (its frame, its own
   blocks), the program's own statics PST. The journal step is ajournal_x_exec_mixed above; otherwise
   cgif YC80.v:69-140 (origin/ossv/recipes) as the three lemmas above. *)
Lemma SRr_chain_pi_tok_AJxm_inv : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx_inv W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_pi_tok_AJxm_invR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
Lemma SRr_run_pi_tok_AJxm_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx_invR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJxm_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_run_pi_tok_AJxm_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx_inv W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_pi_tok_AJxm_invR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
Lemma SRr_run_to_pi_tok_AJxm_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx_invR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJxm_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_run_to_pi_tok_AJxm_inv : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx_inv W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_tok_AJxm_invR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End ei.
(* SRr_chain_pi_tok_AJx_invR at P := fun _ => True. *)
Lemma SRr_chain_pi_tok_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJxR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_chain_pi_tok_AJx_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ I Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* SRr_chain_pi_tok_AJxR at wle. *)
Lemma SRr_chain_pi_tok_AJx : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_pi_tok_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_pi_tok_AJx_invR at P := fun _ => True. *)
Lemma SRr_run_pi_tok_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJxR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
apply (SRr_run_pi_tok_AJx_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ I Hobl Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* SRr_run_pi_tok_AJxR at wle. *)
Lemma SRr_run_pi_tok_AJx : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_pi_tok_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_pi_tok_AJx_invR at P := fun _ => True. *)
Lemma SRr_run_to_pi_tok_AJxR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJxR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
apply (SRr_run_to_pi_tok_AJx_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ I Hobl Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* SRr_run_to_pi_tok_AJxR at wle. *)
Lemma SRr_run_to_pi_tok_AJx : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_tok_AJxR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* Mixed-write twins (write premise awr_byte \/ PST) over a world relation R: SRr_chain_pi_tok_AJxm_invR at
   P := fun _ => True. *)
Lemma SRr_chain_pi_tok_AJxmR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJxR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_chain_pi_tok_AJxm_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ I Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* Mixed-write twins (write premise awr_byte \/ PST): SRr_chain_pi_tok_AJxmR at wle. *)
Lemma SRr_chain_pi_tok_AJxm : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_pi_tok_AJxmR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_pi_tok_AJxm_invR at P := fun _ => True. *)
Lemma SRr_run_pi_tok_AJxmR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJxR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
apply (SRr_run_pi_tok_AJxm_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ I Hobl Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* SRr_run_pi_tok_AJxmR at wle. *)
Lemma SRr_run_pi_tok_AJxm : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_pi_tok_AJxmR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_pi_tok_AJxm_invR at P := fun _ => True. *)
Lemma SRr_run_to_pi_tok_AJxmR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJxR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
apply (SRr_run_to_pi_tok_AJxm_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ I Hobl Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* SRr_run_to_pi_tok_AJxmR at wle. *)
Lemma SRr_run_to_pi_tok_AJxm : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_tok_AJxmR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End e.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Ltac norm_fd32 :=
repeat match goal with
| |- context [fd32 AT_FDCWD] =>
change (fd32 AT_FDCWD) with AT_FDCWD32
| H : context [fd32 AT_FDCWD] |- _ =>
change (fd32 AT_FDCWD) with AT_FDCWD32 in H
| |- context [fd32 ?x] => change (fd32 x) with x
| H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
end.
Ltac fd32_ok :=
solve [ reflexivity
| assumption
| apply fd32_lt31; assumption
| apply fd32_id; assumption
| apply fd32_lt31; lia
| apply fd32_id; lia ].
Lemma star_inv (segs : list Segment) (Inv : config -> Prop)
(Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c') :
forall c tr c', Inv c -> star segs c tr c' -> Inv c'.
Proof.
intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
apply IHHstar. eapply Hstep; eauto.
Qed.
Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
(Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
(Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
forall c, Inv c -> ~ reaches_error segs c.
Proof.
intros c HInv (tr & c' & evs & Hstar & Hss).
eapply Hnoerr; [| exact Hss].
eapply star_inv; eauto.
Qed.
Lemma inv_coexec (segs : list Segment) (Inv : config -> Prop)
(Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
(Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
forall c, Inv c -> OmniRun.coexec segs c never_errors.
Proof.
cofix CH. intros c HInv.
destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
- apply coexec_halt; [rewrite Hh; discriminate | exact (fun h => h)].
- apply coexec_step; [exact Hh | |].
+ intros evs Hss. exfalso. exact (Hnoerr c evs HInv Hss).
+ intros evs c' Hss. exact (CH c' (Hstep c evs c' HInv Hss)).
Qed.
Lemma no_error_run_corun :
forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
(lim : Z) (inp : ProcInput),
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp H. cbn [omni_corun].
apply no_error_coexec, H.
Qed.
Lemma no_error_run_modeled :
forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
(lim : Z) (inp : ProcInput),
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp H.
apply modeled_iff. cbn [img_segments].
eapply coexec_conseq; [apply no_error_run_corun, H | apply never_errors_covered].
Qed.

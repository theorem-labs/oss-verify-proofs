(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import PropExec ShapeAlg SpinAlg AsanPlanCore BothPlanImages AsanInit B0Img MainEntryBoth.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Mem.
Import ListNotations.
Open Scope Z_scope.

Definition H_MAIN_B0 (inp : ProcInput) (en : ExecEntry) (ms : machine_state) (mo : Model) : Prop := bmain_at en inp ms mo.

Definition cfgB0 (en : ExecEntry) (inp : ProcInput) : config :=
  match en with mkEntry sp brk mb rnd => init_config bsegs b_init_pc b_phdrs sp brk mb rnd target_alloc_limit inp end.

Theorem b0_handoff : forall inp en,
  valid_input inp -> valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp ->
  forall Tm : TSet, Tm [] ->
  (forall c, H_MAIN_B0 inp en (cfg_ms c) (cfg_model c) -> srealizes bsegs c Tm) ->
  srealizes bsegs (cfgB0 en inp) Tm.
Proof.
  intros inp [sp brk0 mbase rdraw] Hi Hv Tm Tnil MAINA.
  pose proof Hi as (Hva & Hve & Hfs & Hrel & [Huid Hgid] & Hnof & Hsigm & Hhw & Habt & Hvasz & Hurnd).
  rewrite (valid_entry_sv48 _ _ _ Hvasz) in Hv. destruct Hv as (Hsp & Hbrk & Hmb & Hfit).
  destruct inp as [argv envp fs stdin uid gid groups net nof sigm hw abt vasz urnd tmp].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz, Habt. subst vasz.
  unfold cfgB0.
  exact (both_main_boot sp brk0 mbase rdraw argv envp (fs_seed_tmp fs tmp) stdin uid gid groups net nof sigm hw abt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw
           Tm Tnil (fun ms mo Hat => MAINA (mkCfg ms mo) Hat)).
Qed.

Lemma b0_rw_image_wr_at : forall (m : word -> option byte) a n,
  0xaa000 <= a -> a + n <= 0x609000 -> wr_at bsegs m a n.
Proof.
  intros m a n Ha Hn. split; [lia|]. split; [lia|]. intros i Hi.
  apply (both_rw_window m (wa (a + i))). rewrite wa_unsigned by lia. lia.
Qed.

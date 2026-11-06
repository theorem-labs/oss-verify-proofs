(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState ITree Nodes NodesM Decode DecodeM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep KStepC.

Set Keyed Unification.
Import ListNotations.
Local Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma reserved_top_ge : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

Lemma m_vmmaps_init_model : forall r b mb sp lim inp,
  m_vmmaps (init_model r b mb sp lim inp) = mkVmMapsFull r [] [] b b lim mb sp.
Proof. reflexivity. Qed.

Lemma m_halted_init_model : forall r b mb sp lim inp, m_halted (init_model r b mb sp lim inp) = None.
Proof. reflexivity. Qed.

Lemma KL_init : forall segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  ceil_ok (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) ->
  KL (led_init (reservedZ segs)) 0 (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hpos Hceil Hck.
  constructor; rewrite ?m_vmmaps_init_model, ?m_halted_init_model; try exact Hck;
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live led_init].
  - reflexivity.
  - reflexivity.
  - split; [intros e []| apply pwdisj_nil].
  - intros e [].
  - reflexivity.
  - intros e Hin. pose proof (reserved_top_ge _ _ Hin). unfold ehi. lia.
  - unfold PGSZ in *. unfold page_size in Hal. lia.
  - intros b l [].
  - intros b l k [].
  - apply List.NoDup_nil.
  - intros b l H. discriminate.
  - split; reflexivity.
  - intros e He. destruct He.
Qed.

Lemma OWN_init : forall (G : PState -> Model -> Prop) segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  ceil_ok (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) ->
  G (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp) ->
  OWN [] G (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros G segs brk0 mbase sp lim inp Hv Hpos Hceil Hck HG. unfold OWN. split; [|split; [apply List.NoDup_nil| exact HG]].
  exists (led_init (reservedZ segs)). split; [apply creach_init; apply ctx_secret_range'|]. split; [|intros c []].
  change (ps_brk (ps_init (reservedZ segs))) with 0. apply KL_init; assumption.
Qed.

End CEIL.

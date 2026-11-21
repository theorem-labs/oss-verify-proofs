(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start ledger holds the vdso/vvar pair after the image's reservations; KL_init states the launch's mmap_base bound it needs). *)
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

(* [State.init_model] seeds the ledger with [State.init_reserved], which is the
   image's reservations FOLLOWED BY the vdso/vvar pair [execve] installed above
   them, not the bare argument.  Stated as the model states it; still
   [reflexivity]. *)
Lemma m_vmmaps_init_model : forall r b mb sp lim inp,
  m_vmmaps (init_model r b mb sp lim inp)
  = mkVmMapsFull (init_reserved r mb sp (in_kernel inp)) [] [] b b lim mb sp.
Proof. reflexivity. Qed.

Lemma m_halted_init_model : forall r b mb sp lim inp, m_halted (init_model r b mb sp lim inp) = None.
Proof. reflexivity. Qed.

(* The vDSO pair sits under [min mmap_base alloc_top] ([State.vdso_top]); the launch's mmap_base is at least
   [mmap_base_min] ([Run.valid_mmap_base]) and the pair is at most twenty pages ([State.vdso_len_bounds]), so
   with the image's brk room below [mmap_base_min] the pair is four pages clear of the brk start. *)
Lemma KL_init : forall segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  ceil_ok (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) ->
  valid_mmap_base mbase ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 26 * PGSZ <= mmap_base_min ->
  KL (led_init (reservedZ segs)) 0 (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hpos Hceil Hck (Hmb1 & Hmb2 & Hmb3) Hroom.
  constructor; rewrite ?m_vmmaps_init_model, ?m_halted_init_model; try exact Hck;
    cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live led_init].
  - reflexivity.
  - reflexivity.
  - split; [intros e []| apply pwdisj_nil].
  - intros e [].
  - eexists. unfold init_reserved. rewrite map_app. reflexivity.
  - intros e Hin. unfold init_reserved in Hin. apply in_app_or in Hin as [Hin|Hin].
    + left. pose proof (reserved_top_ge _ _ Hin). unfold ehi. lia.
    + right. destruct e as [a n]. unfold ceil_ok, alloc_top in Hck. rewrite ?m_vmmaps_init_model in Hck. cbn [vm_init_sp] in Hck.
      set (x := Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)) in *.
      pose proof (bv_unsigned_in_range _ mbase) as Rm. pose proof (bv_unsigned_in_range _ sp) as Rs.
      unfold bv_modulus in Rm, Rs. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rm, Rs.
      assert (Hx : mmap_base_min <= x).
      { subst x. pose_ceil. unfold mmap_base_min, stack_max_size, sp_window_lo in *. lia. }
      assert (Hpr : x - 4095 <= page_round_down_Z x <= x).
      { unfold page_round_down_Z, page_size. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)). pose proof (Z_div_mod_eq_full x 4096). lia. }
      destruct (vdso_reserved_above (in_kernel inp) (page_round_down_Z x) a n ltac:(unfold two_pow_64; unfold stack_max_size in *; lia) Hin) as [V1 _].
      pose proof (vdso_len_bounds (in_kernel inp)) as VL.
      unfold elo. cbn [fst]. unfold brk_aslr_max, PGSZ, page_size, vdso_len, vdso_vvar_pages, mmap_base_min in *. lia.
  - unfold PGSZ in *. unfold page_size in Hal. lia.
  - intros b l [].
  - intros b l k [].
  - apply List.NoDup_nil.
  - intros b l H. discriminate.
  - split; reflexivity.
  - intros e He. destruct He.
  - intros e [].
  - unfold vdso_in. rewrite vm_reserved_init_model. apply incl_appr, incl_refl.
Qed.

Lemma OWN_init : forall (G : PState -> Model -> Prop) segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling ->
  ceil_ok (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)) ->
  valid_mmap_base mbase ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 26 * PGSZ <= mmap_base_min ->
  G (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp) ->
  OWN [] G (ps_init (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
  intros G segs brk0 mbase sp lim inp Hv Hpos Hceil Hck Hmb Hroom HG. unfold OWN. split; [|split; [apply List.NoDup_nil| exact HG]].
  exists (led_init (reservedZ segs)). split; [apply creach_init; apply ctx_secret_range'|]. split; [|intros c []].
  change (ps_brk (ps_init (reservedZ segs))) with 0. apply KL_init; assumption.
Qed.

End CEIL.

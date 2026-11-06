(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the WORLD-LAYER STEP half of retiring aj_memnorm (h-hpreset-7's journal
   obligation, given to h-rw-man-8 05:26Z). aj_memnorm m := Lib.Mem.mem_inv segs m /\ MemNorm.task_mem segs m
   (lib/Reusable/YStrtodRowX.v:344, origin/cold/h-verbs-1-preset-strtodB 5a1376f3c69); the lemmas here are stated over
   that conjunction directly (memnorm below is the same body), so they apply to it by conversion.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).

   (ii) STEP PRESERVATION: a write into the overlay at addresses where wview is defined keeps both conjuncts. Two forms,
   for the two ways a walk changes memory:
   - memnorm_store / memnorm_store_cbytes: one store (write_to_mem under store_ok, the instruction-level form; the
     mem_inv half is Lib/Mem.v mem_inv_store and Lib/Step.v mem_inv_store_cbytes, reused; the task_mem half is new);
   - memnorm_munch: a frame-level write (Lib/Frame.v munch W m m', every address of W wview-defined in m), the form a
     callee's post gives; the task_mem half is the port of libreac fuzz_disco lib/Prog/tj_lemmas.v:221
     task_mem_munch (c8557374ad2e), with its rsegs generalised to segs.
   - memnorm_mrestrict: restricting the overlay (YK04.v mrestrict, the journal's view) keeps both.
   THE START-UP SIDE: the INIT case is memnorm_wrap_mem below (LPS's initial overlay). At main, the mem_inv half is
   lib/A/AjMemInvMainA.v mem_inv_at_main (image A, by computation over AB01); the task_mem half is NOT decided by the
   start-up record (open-world realization) and is to be carried by the start-up invariant from memnorm_wrap_mem through
   the start-up steps with the step lemmas here (route R1, PresetStartupA's step list).
   WHY THIS SURVIVES THE HARNESS FIX: everything here is world layer (LPS's overlay, segments, store_ok, munch); no
   harness function and no allocator state appears, so the bound fix's re-pin changes nothing in this file.

   Reuse search (2026-10-29 ~05:35Z): `git grep -n -E '(Lemma|Theorem) [a-z_]*task_mem[a-z_]*'` over the release
   c8557374ad2e proofs/ and origin/cold/{h-verbs-1-preset-strtodB,h-mani-a8-preset-alloc,h-pre-b1-cwd2}: hits are
   task_mem_same_cj, task_mem_norm, task_mem_back, task_mem_rel, task_mem_munch (fuzz_disco); none for a store, none
   for the conjunction. mem_inv_store exists (lib/Lib/Mem.v:306) and is reused. Control: the same grep finds
   MemNorm.v:950 task_mem_same_cj. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK04 YK11 YK0h YK0c YK0e.
Import ListNotations.
Open Scope bv_scope.

Section MemnormStep.
Variable segs : list Segment.

Definition memnorm (m : word -> option byte) : Prop := mem_inv segs m /\ MemNorm.task_mem segs m.

(* an overlay byte made where wview is defined lies in some segment (wview of an absent byte outside every segment
   is None) *)
Lemma wview_absent_seg : forall m a, wview segs m a <> None -> m a = None ->
  find_segment segs (bv_unsigned a) 1 <> None.
Proof.
  intros m a W E. unfold wview in W. rewrite E in W.
  destruct (find_segment segs (bv_unsigned a) 1); [discriminate|]. exfalso. apply W. reflexivity.
Qed.

Lemma task_mem_store : forall m a bs,
  MemNorm.task_mem segs m -> store_ok segs m a (length bs) = true ->
  MemNorm.task_mem segs (write_to_mem m a bs).
Proof.
  intros m a bs Ht Hok x b Hx.
  destruct (write_to_mem_some _ _ _ _ _ Hx) as [H | (i & Hi & ->)].
  - exact (Ht _ _ H).
  - pose proof (store_ok_wview _ _ _ _ _ Hok Hi) as W.
    destruct (m (wa (bv_unsigned a + Z.of_nat i))) eqn:E.
    + exact (Ht _ _ E).
    + left. exact (wview_absent_seg _ _ W E).
Qed.

Lemma memnorm_store : forall m a bs,
  memnorm m -> store_ok segs m a (length bs) = true -> memnorm (write_to_mem m a bs).
Proof.
  intros m a bs (Hi & Ht) Hok. split.
  - exact (mem_inv_store segs m a bs Hi Hok).
  - exact (task_mem_store m a bs Ht Hok).
Qed.

Lemma memnorm_store_cbytes : forall m a c',
  memnorm m -> cell_wf c' -> store_ok segs m a (csize c') = true -> memnorm (write_to_mem m a (cbytes c')).
Proof.
  intros m a c' Hm Hwf Hok. apply memnorm_store; [exact Hm|].
  rewrite cbytes_length by exact Hwf. exact Hok.
Qed.

(* the frame-level form: libreac fuzz_disco tj_lemmas.v:221 task_mem_munch, generalised, with the mem_inv twin *)
Lemma memnorm_munch : forall W m m',
  memnorm m -> munch W m m' -> (forall a : word, ~ outside W (bv_unsigned a) -> wview segs m a <> None) ->
  memnorm m'.
Proof.
  intros W m m' (Hi & Ht) MU HW. split.
  - intros a b E. destruct (m a) as [b0|] eqn:E0; [exact (Hi a b0 E0)|].
    assert (HI : ~ outside W (bv_unsigned a)) by (intros Ho; rewrite (MU a Ho), E0 in E; discriminate).
    exact (wview_not_ro segs m a (HW a HI) E0).
  - intros a b E. destruct (m a) as [b0|] eqn:E0; [exact (Ht a b0 E0)|].
    assert (HI : ~ outside W (bv_unsigned a)) by (intros Ho; rewrite (MU a Ho), E0 in E; discriminate).
    left. exact (wview_absent_seg m a (HW a HI) E0).
Qed.

(* the journal reads memory through mrestrict (w_H W): restricting only removes overlay bytes *)
Lemma memnorm_mrestrict : forall (H : word -> bool) m, memnorm m -> memnorm (YK04.mrestrict H m).
Proof.
  intros H m (Hi & Ht). unfold YK04.mrestrict. split.
  - intros a b E. destruct (H a); [discriminate|]. exact (Hi a b E).
  - intros a b E. destruct (H a); [discriminate|]. exact (Ht a b E).
Qed.

(* and the empty overlay (the loader's starting point, before any store) *)
Lemma memnorm_empty : memnorm (fun _ => None).
Proof. split; intros a b E; discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* R1 STEP LEMMAS, the list PresetStartupA gave (a Theorem Labs lane's internal file R1-step-lemmas.md,
   07:00Z), one per kind of memory a start-up step makes:
   (2)/(3) a symbolic block or havoc cell, FULL' := munrestrict H FULL X: memnorm_munrestrict, with
           memnorm_mem_denot for X = mem_denot E' MR log (each log entry stored under store_ok on the block's base);
   (4)     brk / munmap / mmap grant, slice, dest (M' agrees with M outside [lo, hi), hi <= TASK_SIZE, no new byte at a
           read-only address): memnorm_frame_range. *)

(* the kept part and the new part, each memnorm, give memnorm of the union (YK04.munrestrict) *)
Lemma memnorm_munrestrict : forall (H : word -> bool) full m',
  memnorm full -> memnorm m' -> memnorm (YK04.munrestrict H full m').
Proof.
  intros H full m' (Fi & Ft) (Mi & Mt). unfold YK04.munrestrict. split.
  - intros a b E. destruct (H a); [exact (Fi a b E) | exact (Mi a b E)].
  - intros a b E. destruct (H a); [exact (Ft a b E) | exact (Mt a b E)].
Qed.

(* a write only adds bytes: an absent byte after the write was absent before *)
Lemma write_to_mem_none : forall bs m a x, write_to_mem m a bs x = None -> m x = None.
Proof.
  induction bs as [|b0 bs IH]; intros m a x H; cbn in H; [exact H|].
  pose proof (IH _ _ _ H) as H1. cbv beta in H1. destruct (bv_eqb x a); [discriminate | exact H1].
Qed.

(* so wview stays defined across a write *)
Lemma wview_write_mono : forall bs m a x,
  wview segs m x <> None -> wview segs (write_to_mem m a bs) x <> None.
Proof.
  intros bs m a x W. unfold wview in *. destruct (write_to_mem m a bs x) eqn:E; [discriminate|].
  rewrite (write_to_mem_none bs m a x E) in W. exact W.
Qed.

(* a write at addresses where wview is defined keeps memnorm (the wview form of memnorm_store) *)
Lemma memnorm_write_wview : forall m a bs,
  memnorm m -> (forall i, (i < length bs)%nat -> wview segs m (wa (bv_unsigned a + Z.of_nat i)) <> None) ->
  memnorm (write_to_mem m a bs).
Proof.
  intros m a bs (Hi & Ht) HW. split.
  - intros x b Hx. destruct (write_to_mem_some _ _ _ _ _ Hx) as [H | (i & Hlt & ->)]; [exact (Hi _ _ H)|].
    destruct (m (wa (bv_unsigned a + Z.of_nat i))) eqn:E; [exact (Hi _ _ E)|].
    exact (wview_not_ro segs m _ (HW i Hlt) E).
  - intros x b Hx. destruct (write_to_mem_some _ _ _ _ _ Hx) as [H | (i & Hlt & ->)]; [exact (Ht _ _ H)|].
    destruct (m (wa (bv_unsigned a + Z.of_nat i))) eqn:E; [exact (Ht _ _ E)|].
    left. exact (wview_absent_seg m _ (HW i Hlt) E).
Qed.

(* (4) a change confined to [lo, hi) below TASK_SIZE that puts no byte at a read-only address *)
Lemma memnorm_frame_range : forall m m' lo hi,
  memnorm m -> (forall x, ~ (lo <= bv_unsigned x < hi)%Z -> m' x = m x) -> (hi <= TASK_SIZE)%Z ->
  (forall x b, (lo <= bv_unsigned x < hi)%Z -> m' x = Some b -> ro_addr segs x = false) ->
  memnorm m'.
Proof.
  intros m m' lo hi (Hi & Ht) Hout Hhi Hro. split.
  - intros x b E. destruct (Z_le_dec lo (bv_unsigned x)) as [H1|H1];
      [destruct (Z_lt_dec (bv_unsigned x) hi) as [H2|H2]|].
    + exact (Hro x b (conj H1 H2) E).
    + rewrite (Hout x ltac:(lia)) in E. exact (Hi x b E).
    + rewrite (Hout x ltac:(lia)) in E. exact (Hi x b E).
  - intros x b E. destruct (Z_le_dec lo (bv_unsigned x)) as [H1|H1];
      [destruct (Z_lt_dec (bv_unsigned x) hi) as [H2|H2]|].
    + right. lia.
    + rewrite (Hout x ltac:(lia)) in E. exact (Ht x b E).
    + rewrite (Hout x ltac:(lia)) in E. exact (Ht x b E).
Qed.

(* removing bytes keeps memnorm (munmap / sec_dealloc / unfill: every byte present after was present before) *)
Lemma memnorm_sub : forall m m',
  memnorm m -> (forall a b, m' a = Some b -> exists b0, m a = Some b0) -> memnorm m'.
Proof.
  intros m m' (Hi & Ht) Hs. split.
  - intros a b E. destruct (Hs a b E) as (b0 & E0). exact (Hi a b0 E0).
  - intros a b E. destruct (Hs a b E) as (b0 & E0). exact (Ht a b0 E0).
Qed.
End MemnormStep.

(* (2) the symbolic block's new part: mem_denot over the block's store log (YK0e.v:517), each entry stored under
   store_ok on the block's base (its SCStoreOk side condition). YK0h.wbytes is LPS's write_to_mem, body for body. *)
Lemma wbytes_write_to_mem : forall bs m a,
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0h.wbytes m a bs = write_to_mem m a bs.
Proof. induction bs as [|b bs IH]; intros m a; [reflexivity|]. cbn. apply IH. Qed.

Section MemDenot.
Variable segs : list Segment.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0c.AX2.

(* every entry of the log is stored where the block's base allows it (its SCStoreOk side condition) *)
Definition log_store_ok (E : env) (base : word -> option byte) (log : list sentry) : Prop :=
  Forall (fun e => store_ok segs base (adenot E (e_addr e)) (e_width e) = true) log.

Lemma wview_mem_denot_mono : forall E base log x,
  wview segs base x <> None ->
  wview segs (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0e.AX2S.mem_denot E base log) x <> None.
Proof.
  intros E base log x W. induction log as [|[a w v] log IH]; [exact W|].
  cbn [OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0e.AX2S.mem_denot].
  rewrite wbytes_write_to_mem. apply wview_write_mono. exact IH.
Qed.

Lemma memnorm_mem_denot : forall E base log,
  memnorm segs base -> log_store_ok E base log ->
  memnorm segs (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0e.AX2S.mem_denot E base log).
Proof.
  intros E base log Hb Hl. induction log as [|[a w v] log IH]; [exact Hb|].
  inversion Hl as [|? ? Hs Hl']; subst. cbn [e_addr e_width] in Hs.
  cbn [OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0e.AX2S.mem_denot].
  rewrite wbytes_write_to_mem. apply memnorm_write_wview; [exact (IH Hl')|].
  intros i Hi. assert (HL : length (word_to_le_bytes w (edenot E v)) = w)
    by apply OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0h.length_N_to_le_bytes.
  rewrite HL in Hi. apply wview_mem_denot_mono. exact (store_ok_wview segs base _ w i Hs Hi).
Qed.

(* (2) in full: the symbolic block's FULL' := munrestrict H FULL (mem_denot E' (mrestrict H FULL) log) *)
Lemma memnorm_block : forall (H : word -> bool) E full log,
  memnorm segs full -> log_store_ok E (YK04.mrestrict H full) log ->
  memnorm segs (YK04.munrestrict H full
    (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0e.AX2S.mem_denot E (YK04.mrestrict H full) log)).
Proof.
  intros H E full log Hf Hl. apply memnorm_munrestrict; [exact Hf|].
  apply memnorm_mem_denot; [apply memnorm_mrestrict; exact Hf | exact Hl].
Qed.
End MemDenot.

(* ---------------------------------------------------------------------- *)
(* (i0) the LPS INITIAL overlay satisfies memnorm: YK11.wrap_mem (= init_machine_state's ms_mem, YK11.init_mkst; lps
   Run.v:1074-1087) holds bytes only at [sp - stack_max_size, sp) (zeros) and [sp, entry_page_top) (the entry stack
   image), and entry_stack_fits keeps entry_page_top <= sp_window_hi = TASK_SIZE (YK11.entry_page_top_within_window;
   lps State.v:113, :331). Given that no image segment reaches up to sp - stack_max_size, no initial byte is in a
   segment, so mem_inv holds (no read-only byte) and task_mem holds below TASK_SIZE. This is the base case of route
   R1 (memnorm carried by the start-up invariant); it is NOT the at-main fact, which needs the start-up steps. *)
Section Init.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState}.
Lemma memnorm_wrap_mem : forall segs ph (sp : word) argv envp uid hw rnd,
  entry_stack_fits sp argv envp ->
  (forall a : word, (bv_unsigned sp - stack_max_size <= bv_unsigned a)%Z -> find_segment segs (bv_unsigned a) 1 = None) ->
  memnorm segs (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.wrap_mem ph sp argv envp uid hw rnd).
Proof.
  intros segs ph sp argv envp uid hw rnd Hfit Hseg.
  pose proof (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.entry_page_top_within_window
                ph sp argv envp uid hw rnd Hfit) as Htop.
  pose proof (entry_stack_image_top ph sp argv envp uid hw rnd) as Himg.
  assert (Hsupp : forall a b,
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.wrap_mem ph sp argv envp uid hw rnd a = Some b ->
    (bv_unsigned sp - stack_max_size <= bv_unsigned a < TASK_SIZE)%Z).
  { intros a b E. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.wrap_mem, stack_to_mem in E.
    unfold sp_window_hi in Htop. unfold TASK_SIZE.
    destruct (Z.leb_spec (bv_unsigned sp) (bv_unsigned a)) as [H1|H1].
    - destruct (Z.ltb_spec (bv_unsigned a - bv_unsigned sp)
                  (Z.of_nat (length (entry_stack_image ph sp argv envp uid hw rnd)))) as [H2|H2].
      + unfold stack_max_size. lia.
      + destruct (andb _ _) eqn:Hb; [|discriminate].
        apply andb_prop in Hb as [_ Hb]. apply Z.ltb_lt in Hb. lia.
    - destruct (andb _ _) eqn:Hb; [|discriminate].
      apply andb_prop in Hb as [Hb _]. apply Z.leb_le in Hb. lia. }
  split.
  - intros a b E. destruct (Hsupp a b E) as [Hlo _]. unfold ro_addr. rewrite (Hseg a Hlo). reflexivity.
  - intros a b E. destruct (Hsupp a b E) as [_ Hhi]. right. exact Hhi.
Qed.
End Init.

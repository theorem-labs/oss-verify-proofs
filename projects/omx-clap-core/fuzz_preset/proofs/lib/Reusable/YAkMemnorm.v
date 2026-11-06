(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, route R1 (h-hpreset-7): memnorm, the overlay normal form, as the start-up kit
   carries it, with the step lemmas each start-up step uses.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).

   memnorm here has the body of YAjMemnorm.memnorm (= Lib.Mem.mem_inv /\ MemNorm.task_mem), written out over LPS
   only; YAkMemnormJ.v gives the conversion. WHY A SECOND COPY: YAjMemnorm.v requires lib/Lib/Mem.v, which requires
   lib/Lib/PropExec.v, which exports lib/Lib/LiaTwx2.v, and LiaTwx2.v:187 redefines `lia` globally (Ltac lia ::=).
   A kit file that requires YAjMemnorm gets that lia in every proof after the Require. Measured on a build VM: with
   `Require YAjMemnorm` in YA0e.v, APSG.A_wf_allowA lost its five section arguments HS XN XE XB KC, and YA09.v's
   `Let vis_add_sound' := APSG.vis_add_sound SEGS A LIMIT TOP HS XN XE XB ...` failed (HS where top_ok TOP was
   expected). This file requires only libraries the kit (YA0e.v) already loads, so no kit proof changes.

   The lemmas, one per kind of memory a start-up step makes (they mirror YAjMemnorm.v's step lemmas):
   - memnorm_msteps: the end overlay of a run of machine steps (symbolic block, call and scan nodes). LPS's step
     changes the overlay only in interp_eff's EStore, after store_ok holds on the bytes it writes
     (RiscvSemantics.interp_eff_accesses); the proof follows YI04.v step_mem_grows.
   - memnorm_mrestrict, memnorm_munrestrict: the hidden/visible split and the merge after a restricted run.
   - memnorm_frame_off_segs: a change confined to [lo, hi) below TASK_SIZE where no segment lies (brk zfill, mmap
     grant and slice); the twin of YAjMemnorm.memnorm_frame_range with "no read-only byte" from "no segment".
   - memnorm_sub: an overlay that only drops bytes (munmap unfill, mmap dest).
   - memnorm_wrap_mem: the loader's overlay (the entry case), the twin of YAjMemnorm.memnorm_wrap_mem. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK04 YK0i YK11 YP00.
Import ListNotations.
Open Scope Z_scope.

Section S.
Variable segs : list Segment.

Definition ro_addr (a : word) : bool :=
  match find_segment segs (bv_unsigned a) 1 with
  | Some seg => negb (seg_writable seg)
  | None => false
  end.

Definition memnorm (m : word -> option byte) : Prop :=
  (forall a b, m a = Some b -> ro_addr a = false)
  /\ (forall a b, m a = Some b -> find_segment segs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE).

Lemma memnorm_mrestrict : forall (H : word -> bool) m, memnorm m -> memnorm (YK04.mrestrict H m).
Proof.
  intros H m (Hi & Ht). unfold YK04.mrestrict. split.
  - intros a b E. destruct (H a); [discriminate|]. exact (Hi a b E).
  - intros a b E. destruct (H a); [discriminate|]. exact (Ht a b E).
Qed.

Lemma memnorm_munrestrict : forall (H : word -> bool) full m',
  memnorm full -> memnorm m' -> memnorm (YK04.munrestrict H full m').
Proof.
  intros H full m' (Fi & Ft) (Mi & Mt). unfold YK04.munrestrict. split.
  - intros a b E. destruct (H a); [exact (Fi a b E) | exact (Mi a b E)].
  - intros a b E. destruct (H a); [exact (Ft a b E) | exact (Mt a b E)].
Qed.

Lemma memnorm_sub : forall m m',
  memnorm m -> (forall (x : word) b, m' x = Some b -> m x = Some b) -> memnorm m'.
Proof.
  intros m m' (Hi & Ht) Hs. split; intros x b E; [exact (Hi x b (Hs x b E)) | exact (Ht x b (Hs x b E))].
Qed.

Lemma memnorm_frame_off_segs : forall m m' lo hi,
  memnorm m ->
  (forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> m' x = m x) ->
  hi <= TASK_SIZE ->
  (forall x : word, lo <= bv_unsigned x < hi -> find_segment segs (bv_unsigned x) 1 = None) ->
  memnorm m'.
Proof.
  intros m m' lo hi (Hi & Ht) Hout Hhi Hseg. split; intros x b E;
    (destruct (Z_lt_le_dec (bv_unsigned x) lo) as [H1|H1];
     [| destruct (Z_lt_le_dec (bv_unsigned x) hi) as [H2|H2]]).
  - rewrite (Hout x (or_introl H1)) in E. exact (Hi x b E).
  - unfold ro_addr. rewrite (Hseg x (conj H1 H2)). reflexivity.
  - rewrite (Hout x (or_intror H2)) in E. exact (Hi x b E).
  - rewrite (Hout x (or_introl H1)) in E. exact (Ht x b E).
  - right. lia.
  - rewrite (Hout x (or_intror H2)) in E. exact (Ht x b E).
Qed.

(* one store byte, at an address where wview is defined *)
Lemma memnorm_upd : forall m (a : word) b,
  memnorm m -> wview segs m a <> None -> memnorm (fun x => if bv_eqb x a then Some b else m x).
Proof.
  intros m a b (Hi & Ht) W.
  assert (Ha : ro_addr a = false /\ (find_segment segs (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE)).
  { unfold wview in W. revert W. destruct (m a) as [b0|] eqn:E; intros W; [exact (conj (Hi a b0 E) (Ht a b0 E))|].
    unfold ro_addr. revert W.
    destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; intros W; [|exfalso; exact (W eq_refl)].
    revert W. destruct (seg_writable seg); intros W; [|exfalso; exact (W eq_refl)].
    split; [reflexivity | left; discriminate]. }
  destruct Ha as [Ha1 Ha2].
  split; intros x c E; cbv beta in E; revert E; destruct (bv_eqb x a) eqn:Ex; intros E.
  - unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. unfold ro_addr in *. rewrite Ex. exact Ha1.
  - exact (Hi x c E).
  - unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. rewrite Ex. exact Ha2.
  - exact (Ht x c E).
Qed.

Lemma store_ok_upd_mono : forall n m (a : word) b (c : word),
  store_ok segs m c n = true -> store_ok segs (fun y => if bv_eqb y a then Some b else m y) c n = true.
Proof.
  induction n as [|n IH]; intros m a b c H; [reflexivity|].
  set (m1 := fun y : word => if bv_eqb y a then Some b else m y).
  cbn [store_ok] in H |- *. revert H. destruct (wview segs m c) eqn:W; intros H; [|discriminate].
  destruct (wview segs m1 c) eqn:W1.
  - exact (IH m a b _ H).
  - exfalso. unfold wview, m1 in W1. cbv beta in W1. revert W1. destruct (bv_eqb c a); intros W1; [discriminate|].
    change (wview segs m c = None) in W1. rewrite W1 in W. discriminate.
Qed.

(* a store under store_ok, the form of LPS's EStore *)
Lemma memnorm_write : forall bs m (a : word),
  memnorm m -> store_ok segs m a (length bs) = true -> memnorm (write_to_mem m a bs).
Proof.
  induction bs as [|b bs IH]; intros m a Hm Hs; [exact Hm|].
  cbn [write_to_mem]. cbn [length store_ok] in Hs. revert Hs.
  destruct (wview segs m a) eqn:W; intros Hs; [|discriminate].
  apply IH.
  - apply memnorm_upd; [exact Hm | rewrite W; discriminate].
  - apply store_ok_upd_mono. exact Hs.
Qed.

Lemma memnorm_interp_eff0 : forall t m c m',
  memnorm m -> YP00.interp_eff0 segs t m = MachineOk (c, m') -> memnorm m'.
Proof.
  induction t as [c0| | | | | |n a k IH|n a v k IH]; intros m c1 m' Hm H; cbn [YP00.interp_eff0] in H;
    try discriminate.
  - injection H as <- <-. exact Hm.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    exact (IH _ m c1 m' Hm H).
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hs; [|discriminate].
    refine (IH _ c1 m' _ H). apply memnorm_write; [exact Hm|].
    rewrite length_Z_to_le_bytes. exact Hs.
Qed.

Lemma memnorm_decode_exec : forall st w st',
  memnorm (ms_mem st) -> decode_exec segs st w = MachineOk st' -> memnorm (ms_mem st').
Proof.
  intros st w st' Hm H. rewrite YP00.decode_exec_compat in H.
  destruct (is_ecall w).
  - injection H as <-. exact Hm.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    destruct (YP00.interp_eff0 segs _ (ms_mem st)) as [[c m']| |] eqn:Hi; try discriminate.
    injection H as <-. exact (memnorm_interp_eff0 _ _ _ _ Hm Hi).
Qed.

Lemma fetch_failure_never_ok : forall m a st', fetch_failure segs m a = MachineOk st' -> False.
Proof.
  intros m a st' H. unfold fetch_failure in H.
  destruct (negb _); [discriminate|]. destruct (_ || _ || _)%bool; discriminate.
Qed.

Lemma memnorm_step : forall st st',
  memnorm (ms_mem st) -> RiscvSemantics.step segs st = MachineOk st' -> memnorm (ms_mem st').
Proof.
  intros st st' Hm H. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc st)) as [w|].
  { eapply memnorm_decode_exec; [exact Hm|]. unfold decode_exec. exact H. }
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|].
  { eapply memnorm_decode_exec; [exact Hm|]. unfold decode_exec. exact H. }
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|].
  { eapply memnorm_decode_exec; [exact Hm|]. unfold decode_exec. exact H. }
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:Hf; try discriminate.
  exfalso. eapply fetch_failure_never_ok. exact Hf.
Qed.

(* the end overlay of an msteps run (YK0i.v), the form runTX_sound and the node run lemmas give *)
Lemma memnorm_msteps : forall ms ms',
  YK0i.msteps segs ms ms' -> memnorm (ms_mem ms) -> memnorm (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hp Hs Hr IH]; intros Hm; [exact Hm|].
  apply IH. exact (memnorm_step ms ms1 Hm Hs).
Qed.
End S.

(* the loader's overlay: YK11.wrap_mem (= init_machine_state's ms_mem) holds bytes only in
   [sp - stack_max_size, entry_page_top), and entry_page_top <= sp_window_hi = TASK_SIZE; given no segment at or above
   sp - stack_max_size, memnorm holds. The proof is YAjMemnorm.memnorm_wrap_mem's. *)
Lemma memnorm_wrap_mem : forall segs ph (sp : word) argv envp uid hw rnd,
  entry_stack_fits sp argv envp ->
  (forall a : word, bv_unsigned sp - stack_max_size <= bv_unsigned a -> find_segment segs (bv_unsigned a) 1 = None) ->
  memnorm segs (YK11.wrap_mem ph sp argv envp uid hw rnd).
Proof.
  intros segs ph sp argv envp uid hw rnd Hfit Hseg.
  pose proof (YK11.entry_page_top_within_window ph sp argv envp uid hw rnd Hfit) as Htop.
  pose proof (entry_stack_image_top ph sp argv envp uid hw rnd) as Himg.
  assert (Hsupp : forall a b, YK11.wrap_mem ph sp argv envp uid hw rnd a = Some b ->
    bv_unsigned sp - stack_max_size <= bv_unsigned a < TASK_SIZE).
  { intros a b E. unfold YK11.wrap_mem, stack_to_mem in E.
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

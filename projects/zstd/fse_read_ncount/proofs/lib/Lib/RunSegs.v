(* SPDX-License-Identifier: MIT *)
(* LPS 08b1429 runs a binary over [run_segments segs inp sp mbase] = segs ++ the
   vDSO pair.  This file lifts a walk proved over the binary's own segments to
   the run's segment list.  Only SUCCESSFUL steps are transported: a fetch, a
   load or a store that succeeds over [segs] succeeds, with the same answer,
   over [segs ++ tail] ([find_segment] answers with the first segment that
   covers the range).  A failure proved over [segs] is NOT transported (a read
   that faults over [segs] may succeed in the vDSO pair).  The one side
   condition is that the tail lies above the image: every tail segment starts
   at or above [segs_top segs + 8], which the vDSO pair does for every valid
   launch ([vdso_segments_high]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes InitMem.
Import ListNotations.
Open Scope Z_scope.

Lemma find_segment_app : forall l1 l2 a n,
  find_segment (l1 ++ l2) a n = match find_segment l1 a n with Some s => Some s | None => find_segment l2 a n end.
Proof.
  induction l1 as [|s l1 IH]; intros l2 a n; [reflexivity|].
  cbn [app find_segment]. destruct (_ && _)%bool; [reflexivity|]. apply IH.
Qed.

Lemma find_segment_some_app : forall l1 l2 a n s,
  find_segment l1 a n = Some s -> find_segment (l1 ++ l2) a n = Some s.
Proof. intros l1 l2 a n s H. rewrite find_segment_app, H. reflexivity. Qed.

Lemma find_segment_below : forall l a n,
  (forall s, In s l -> a < Z.of_N (seg_base s)) -> find_segment l a n = None.
Proof.
  induction l as [|s l IH]; intros a n H; [reflexivity|]. cbn [find_segment].
  replace (Z.of_N (seg_base s) <=? a) with false by (symmetry; apply Z.leb_gt; apply H; left; reflexivity).
  cbn [andb]. apply IH. intros s' Hs'. apply H. right. exact Hs'.
Qed.

Lemma memory_read_some_app : forall l1 l2 a n bs,
  memory_read l1 a n = Some bs -> memory_read (l1 ++ l2) a n = Some bs.
Proof.
  intros l1 l2 a n bs H. unfold memory_read in *.
  destruct (find_segment l1 (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|discriminate].
  rewrite (find_segment_some_app l1 l2 _ _ s E). exact H.
Qed.

Lemma seg_rom_some_app : forall l1 l2 a b,
  seg_rom l1 a = Some b -> seg_rom (l1 ++ l2) a = Some b.
Proof.
  intros l1 l2 a b H. unfold seg_rom in *.
  destruct (memory_read l1 a 1) as [bs|] eqn:E; [|discriminate].
  rewrite (memory_read_some_app l1 l2 a 1 bs E). exact H.
Qed.

Lemma mrd_some_app : forall l1 l2 m a b,
  mrd l1 m a = Some b -> mrd (l1 ++ l2) m a = Some b.
Proof.
  intros l1 l2 m a b H. unfold mrd in *. destruct (m a); [exact H|]. apply seg_rom_some_app. exact H.
Qed.

Lemma wview_some_app : forall l1 l2 m a b,
  wview l1 m a = Some b -> wview (l1 ++ l2) m a = Some b.
Proof.
  intros l1 l2 m a b H. unfold wview in *. destruct (m a); [exact H|].
  destruct (find_segment l1 (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate].
  rewrite (find_segment_some_app l1 l2 _ _ s E). exact H.
Qed.

Lemma wview_ne_app : forall l1 l2 m a,
  wview l1 m a <> None -> wview (l1 ++ l2) m a <> None.
Proof.
  intros l1 l2 m a H. destruct (wview l1 m a) as [b|] eqn:E; [|contradiction].
  rewrite (wview_some_app l1 l2 m a b E). discriminate.
Qed.

Lemma store_ok_app : forall l1 l2 m n a,
  store_ok l1 m a n = true -> store_ok (l1 ++ l2) m a n = true.
Proof.
  intros l1 l2 m n. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [store_ok] in *. destruct (wview l1 m a) as [b|] eqn:E; [|discriminate].
  rewrite (wview_some_app l1 l2 m a b E). apply IH. exact H.
Qed.

Lemma ov_read_bytes_app : forall l1 l2 m n a bs,
  ov_read_bytes l1 m a n = Some bs -> ov_read_bytes (l1 ++ l2) m a n = Some bs.
Proof.
  intros l1 l2 m n. induction n as [|n IH]; intros a bs H; [exact H|].
  cbn [ov_read_bytes] in *. destruct (m a) as [b|].
  - destruct (ov_read_bytes l1 m (a + 1)%bv n) as [rest|] eqn:E; [|discriminate].
    rewrite (IH _ _ E). exact H.
  - destruct (memory_read l1 a 1) as [[|b rs]|] eqn:Em; try discriminate.
    rewrite (memory_read_some_app l1 l2 a 1 _ Em).
    destruct (ov_read_bytes l1 m (a + 1)%bv n) as [rest|] eqn:E; [|discriminate].
    rewrite (IH _ _ E). exact H.
Qed.

Lemma interp_eff_accesses_app : forall l1 l2 t m r,
  interp_eff_accesses l1 t m = MachineOk r -> interp_eff_accesses (l1 ++ l2) t m = MachineOk r.
Proof.
  intros l1 l2 t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r H; try exact H; try discriminate H.
  - cbn [interp_eff_accesses] in *.
    destruct (ov_read_bytes l1 m a (width_bytes n)) as [bs|] eqn:E;
      [|destruct (range_meets_vvar l1 a (width_bytes n)); discriminate H].
    rewrite (ov_read_bytes_app l1 l2 m _ a bs E).
    destruct (interp_eff_accesses l1 (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:E2; try discriminate H.
    rewrite (IH _ _ _ E2). exact H.
  - cbn [interp_eff_accesses] in *.
    destruct (store_ok l1 m a (width_bytes n)) eqn:E; [|discriminate H].
    rewrite (store_ok_app l1 l2 m _ a E).
    destruct (interp_eff_accesses l1 k _) as [rep| |] eqn:E2; try discriminate H.
    rewrite (IH _ _ E2). exact H.
Qed.

Lemma decode_exec_accesses_app : forall l1 l2 st w r,
  decode_exec_accesses l1 st w = MachineOk r -> decode_exec_accesses (l1 ++ l2) st w = MachineOk r.
Proof.
  intros l1 l2 st w r H. unfold decode_exec_accesses in *.
  destruct (is_ecall w); [exact H|]. destruct (decode_any w) as [[i isz]|]; [|exact H].
  match type of H with context [interp_eff_accesses l1 ?t ?m] =>
    destruct (interp_eff_accesses l1 t m) as [rep| |] eqn:E; try discriminate H;
    rewrite (interp_eff_accesses_app l1 l2 t m rep E) end.
  exact H.
Qed.

Lemma fetch_failure_not_ok : forall l m a st, fetch_failure l m a <> MachineOk st.
Proof.
  intros l m a st. unfold fetch_failure. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Section Tail.
Variables segs tail : list Segment.
Hypothesis TAIL : forall s, In s tail -> segs_top segs + 8 <= Z.of_N (seg_base s).

Lemma find_segment_app_low : forall a n,
  a < segs_top segs + 8 -> find_segment (segs ++ tail) a n = find_segment segs a n.
Proof.
  intros a n Ha. rewrite find_segment_app. destruct (find_segment segs a n); [reflexivity|].
  apply find_segment_below. intros s Hs. pose proof (TAIL s Hs). lia.
Qed.

Lemma bv_unsigned_add_le : forall (x y : word), bv_unsigned (x + y)%bv <= bv_unsigned x + bv_unsigned y.
Proof.
  intros x y. rewrite bv_add_unsigned. unfold bv_wrap.
  pose proof (bv_unsigned_in_range 64 x) as [R0 R1]. pose proof (bv_unsigned_in_range 64 y) as [S0 S1].
  assert (Hm : 0 < bv_modulus 64) by (unfold bv_modulus; lia).
  apply Z.mod_le; lia.
Qed.

Lemma step_accesses_app : forall st r,
  step_accesses segs st = MachineOk r -> step_accesses (segs ++ tail) st = MachineOk r.
Proof.
  intros st r H. set (pc := ms_pc st) in *.
  destruct (Z_lt_le_dec (bv_unsigned pc) (segs_top segs)) as [Hlo|Hhi].
  - assert (P0 : bv_unsigned pc < segs_top segs + 8) by lia.
    assert (P2 : bv_unsigned (pc + 2)%bv < segs_top segs + 8).
    { pose proof (bv_unsigned_add_le pc 2) as HA.
      assert (H2 : bv_unsigned (2 : word) = 2) by reflexivity. lia. }
    assert (EW : fetch_word (segs ++ tail) pc = fetch_word segs pc).
    { unfold fetch_word, code_read. rewrite find_segment_app_low by exact P0. reflexivity. }
    assert (EO : fetch_word_ov (segs ++ tail) (ms_mem st) pc = fetch_word_ov segs (ms_mem st) pc).
    { unfold fetch_word_ov, code_read_ov. rewrite find_segment_app_low by exact P0. reflexivity. }
    assert (ET : fetch_tail_any (segs ++ tail) (ms_mem st) pc = fetch_tail_any segs (ms_mem st) pc).
    { unfold fetch_tail_any, fetch_half_any, fetch_half, fetch_half_ov, code_read, code_read_ov.
      rewrite !find_segment_app_low by first [exact P0 | exact P2]. reflexivity. }
    unfold step_accesses in *. fold pc in H |- *. rewrite EW, EO, ET.
    destruct (fetch_word segs pc) as [w|]; [apply decode_exec_accesses_app; exact H|].
    destruct (fetch_word_ov segs (ms_mem st) pc) as [w|]; [apply decode_exec_accesses_app; exact H|].
    destruct (fetch_tail_any segs (ms_mem st) pc) as [w|]; [apply decode_exec_accesses_app; exact H|].
    destruct (fetch_failure segs (ms_mem st) pc) as [st'| |] eqn:F; try discriminate H.
    exfalso. exact (fetch_failure_not_ok _ _ _ _ F).
  - exfalso. unfold step_accesses in H. fold pc in H.
    assert (EW : fetch_word segs pc = None).
    { unfold fetch_word, code_read. rewrite find_segment_high by lia. destruct (negb _); reflexivity. }
    assert (EO : fetch_word_ov segs (ms_mem st) pc = None).
    { unfold fetch_word_ov, code_read_ov. rewrite find_segment_high by lia. destruct (negb _); reflexivity. }
    assert (ET : fetch_tail_any segs (ms_mem st) pc = None).
    { unfold fetch_tail_any, fetch_half_any, fetch_half, fetch_half_ov, code_read, code_read_ov.
      rewrite (find_segment_high segs (bv_unsigned pc)) by lia. destruct (negb _); reflexivity. }
    rewrite EW, EO, ET in H.
    destruct (fetch_failure segs (ms_mem st) pc) as [st'| |] eqn:F; try discriminate H.
    exact (fetch_failure_not_ok _ _ _ _ F).
Qed.

(* The machine state with its read-only backing replaced: [step] never
   reads [ms_rom] and passes it through. *)
Definition with_rom (ms : machine_state) (r : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := r |}.

Lemma step_accesses_with_rom : forall l st r ro,
  step_accesses l st = MachineOk r ->
  step_accesses l (with_rom st ro) = MachineOk (@mkAccessReport _ (with_rom (@access_value _ r) ro) (@accessed_ranges _ r)).
Proof.
  intros l st r ro H.
  assert (D : forall w r0, decode_exec_accesses l st w = MachineOk r0 ->
                decode_exec_accesses l (with_rom st ro) w
                = MachineOk (@mkAccessReport _ (with_rom (@access_value _ r0) ro) (@accessed_ranges _ r0))).
  { intros w r0 Hd. unfold decode_exec_accesses in *. cbn [with_rom ms_regs ms_fregs ms_pc_val ms_resv ms_fcsr ms_mem ms_rom].
    destruct (is_ecall w); [injection Hd as <-; reflexivity|].
    destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate Hd].
    match type of Hd with context [interp_eff_accesses l ?t ?m] =>
      destruct (interp_eff_accesses l t m) as [rep| |]; try discriminate Hd end.
    destruct (@access_value _ rep) as [c m']. injection Hd as <-. reflexivity. }
  unfold step_accesses in *. cbn [with_rom ms_pc ms_pc_val ms_mem] in *. unfold ms_pc in *. cbn [ms_pc_val] in *.
  destruct (fetch_word l (ms_pc_val st)) as [w|]; [apply D; exact H|].
  destruct (fetch_word_ov l (ms_mem st) (ms_pc_val st)) as [w|]; [apply D; exact H|].
  destruct (fetch_tail_any l (ms_mem st) (ms_pc_val st)) as [w|]; [apply D; exact H|].
  destruct (fetch_failure l (ms_mem st) (ms_pc_val st)) as [st'| |] eqn:F; try discriminate H.
  exfalso. exact (fetch_failure_not_ok _ _ _ _ F).
Qed.

Lemma step_lift : forall ms ms' ro,
  RiscvSemantics.step segs ms = MachineOk ms' ->
  RiscvSemantics.step (segs ++ tail) (with_rom ms ro) = MachineOk (with_rom ms' ro).
Proof.
  intros ms ms' ro H. unfold RiscvSemantics.step in *.
  destruct (step_accesses segs ms) as [r| |] eqn:E; cbn [drop_access_report] in H; try discriminate H.
  injection H as <-.
  rewrite (step_accesses_with_rom (segs ++ tail) ms r ro (step_accesses_app ms r E)). reflexivity.
Qed.

Lemma mstep_lift : forall ms ms' ro, mstep segs ms ms' -> mstep (segs ++ tail) (with_rom ms ro) (with_rom ms' ro).
Proof. intros ms ms' ro [Hs Hst]. split; [exact Hs| apply step_lift; exact Hst]. Qed.

Lemma msteps_lift : forall ms ms' ro, msteps segs ms ms' -> msteps (segs ++ tail) (with_rom ms ro) (with_rom ms' ro).
Proof.
  intros ms ms' ro H. induction H as [ms|ms ms1 ms2 H1 H2 IH].
  - apply msteps_refl.
  - eapply msteps_cons; [apply mstep_lift; exact H1| exact IH].
Qed.

Lemma evt_lift : forall (Q : machine_state -> Prop) ms ro,
  evt segs Q ms -> evt (segs ++ tail) (fun ms' => exists ms0, ms' = with_rom ms0 ro /\ Q ms0) (with_rom ms ro).
Proof.
  intros Q ms ro (ms1 & Hs & HQ). exists (with_rom ms1 ro). split; [apply msteps_lift; exact Hs|]. exists ms1. auto.
Qed.

Lemma bytes_at_lift : forall m a bs, bytes_at segs m a bs -> bytes_at (segs ++ tail) m a bs.
Proof.
  intros m a bs (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  apply mrd_some_app. rewrite H by exact Hi. exact E.
Qed.

Lemma wr_at_lift : forall m a n, wr_at segs m a n -> wr_at (segs ++ tail) m a n.
Proof.
  intros m a n (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. apply wview_ne_app. apply H. exact Hi.
Qed.

Lemma areg_with_rom : forall ms ro r, areg (with_rom ms ro) r = areg ms r.
Proof. reflexivity. Qed.

Lemma at_node_lift : forall n ms,
  at_node segs n ms -> at_node (segs ++ tail) n (with_rom ms (seg_rom (segs ++ tail))).
Proof.
  intros n ms H. destruct n; cbn [at_node] in *; rewrite ?areg_with_rom; cbn [with_rom ms_svc_pending ms_mem ms_rom].
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8).
    refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj eq_refl _))))))).
    apply bytes_at_lift. exact H8.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & iovs & H9 & H10).
    refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj eq_refl _)))))))).
    exists iovs. split; [apply bytes_at_lift; exact H9|].
    eapply Forall2_impl; [|exact H10]. intros iov bs (A & B & C). split; [exact A|]. split; [exact B|]. apply bytes_at_lift. exact C.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8).
    refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj eq_refl _))))))).
    apply bytes_at_lift. exact H8.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 _))))))).
    apply wr_at_lift. exact H8.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
Qed.

Lemma nret_with_rom : forall ms rsp ro, nret (with_rom ms ro) rsp = with_rom (nret ms rsp) ro.
Proof. intros [] rsp ro. reflexivity. Qed.

(* THE BRIDGE: a tree walk proved over the binary's segments is a walk over
   the run's segment list, from the same state with the run's read-only
   backing. *)
Theorem impl_lift : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms,
  impl segs (at_node segs) t Q ms ->
  impl (segs ++ tail) (at_node (segs ++ tail)) t
       (fun r ms' => exists ms0, ms' = with_rom ms0 (seg_rom (segs ++ tail)) /\ Q r ms0)
       (with_rom ms (seg_rom (segs ++ tail))).
Proof.
  intros R t. induction t as [r|n k IH]; intros Q ms H; cbn [impl] in *.
  - apply evt_lift. exact H.
  - unfold evt in H |- *. destruct H as (ms1 & Hs & Hat & Hk).
    exists (with_rom ms1 (seg_rom (segs ++ tail))). split; [apply msteps_lift; exact Hs|].
    split; [apply at_node_lift; exact Hat|].
    intros rsp. rewrite nret_with_rom. apply IH. apply Hk.
Qed.
End Tail.

(* The vDSO pair lies far above any binary image this tree verifies. *)
Lemma page_round_down_Z_ge : forall z, z - 4095 <= page_round_down_Z z.
Proof. intros z. unfold page_round_down_Z, page_size. Z.div_mod_to_equations. lia. Qed.
Lemma page_round_down_Z_le : forall z, page_round_down_Z z <= z.
Proof. intros z. unfold page_round_down_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Local Transparent vdso_segments.

Lemma vdso_segments_high : forall kb (sp mbase : word) B,
  valid_sp sp -> valid_mmap_base mbase -> B <= 0x100000000 ->
  forall s, In s (vdso_segments kb sp mbase) -> B <= Z.of_N (seg_base s).
Proof.
  intros kb sp mbase B Hsp Hmb HB.
  unfold vdso_segments. cbv zeta.
  (* LPS b84e73ef: the pair's top and the text's start are named ([vdso_pair_top], [vdso_text_base]);
     the text's start is a word, read back below the address space's top *)
  unfold vdso_text_base, vdso_pair_top.
  destruct (_ <? page_size)%Z eqn:E; [intros s []|].
  apply Z.ltb_ge in E.
  pose proof (vdso_len_bounds kb) as VL. pose proof (vdso_text_pages_le kb) as VT1. pose proof (vdso_text_pages_pos kb) as VT2.
  destruct Hsp as (S1 & S2 & _). destruct Hmb as (M1 & M2 & _).
  unfold mmap_base_max, sp_window_lo, sp_window_hi, mmap_base_min, stack_max_size, page_size in *.
  pose proof (page_round_down_Z_ge (bv_unsigned sp - 8 * 1024 * 1024)) as P1.
  pose proof (page_round_down_Z_ge (Z.min (bv_unsigned mbase) (page_round_down_Z (bv_unsigned sp - 8 * 1024 * 1024)))) as P2.
  pose proof (page_round_down_Z_le (Z.min (bv_unsigned mbase) (page_round_down_Z (bv_unsigned sp - 8 * 1024 * 1024)))) as P3.
  intros s [<-|[<-|[]]]; cbn [seg_base]; rewrite ?unsigned_lit by lia; rewrite Z2N.id by lia; lia.
Qed.

(* The run's segment list reserves what the image reserves: the vDSO pair is kernel-mapped. *)
Lemma segments_reserved_cons : forall s l,
  segments_reserved (s :: l)
  = if seg_kernel_map s then segments_reserved l
    else segment_reservation s :: segments_reserved l.
Proof.
  intros s l. unfold segments_reserved.
  destruct (seg_kernel_map s) eqn:E.
  - rewrite list_basics.list.filter_cons_False by (rewrite E; intros []). reflexivity.
  - rewrite list_basics.list.filter_cons_True by (rewrite E; exact I). reflexivity.
Qed.

Lemma segments_reserved_kernel_nil : forall l,
  (forall s, List.In s l -> seg_kernel_map s = true) -> segments_reserved l = [].
Proof.
  induction l as [|s l IH]; intros H; [reflexivity|].
  rewrite segments_reserved_cons, (H s (or_introl eq_refl)).
  apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma segments_reserved_app_kernel : forall l t,
  (forall s, List.In s t -> seg_kernel_map s = true) ->
  segments_reserved (l ++ t) = segments_reserved l.
Proof.
  induction l as [|s l IH]; intros t H; cbn [List.app].
  - apply segments_reserved_kernel_nil. exact H.
  - rewrite !segments_reserved_cons, (IH t H). reflexivity.
Qed.

Lemma vdso_segments_kernel : forall kb (sp mb : word) s,
  List.In s (vdso_segments kb sp mb) -> seg_kernel_map s = true.
Proof.
  intros kb sp mb s Hin. unfold vdso_segments in Hin. cbv zeta in Hin.
  lazymatch type of Hin with context [if ?b then _ else _] => destruct b end;
    cbn [List.In] in Hin; [destruct Hin|].
  destruct Hin as [<-|[<-|[]]]; reflexivity.
Qed.

Lemma segments_reserved_vdso_app : forall segs kb (sp mb : word),
  segments_reserved (segs ++ vdso_segments kb sp mb) = segments_reserved segs.
Proof.
  intros segs kb sp mb. apply segments_reserved_app_kernel.
  apply vdso_segments_kernel.
Qed.

(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 20f40762): every step of the model's run relation keeps "the memory
   overlay holds no byte of the window [vlo, vhi), and the window sits inside an entry of the
   launch's vDSO/vvar pair, which is in the reserved ledger" ([MmVdso.vc_cfg]), for every segment
   list with no writable segment over the window ([Hnw], as in [VdsoClean]).

   [pc_step] takes a step of [Run.sstep_cfg] (Run.v:2250-2342) under any spurious-failure
   configuration.  Its arms:
     - [sstep_cfg_instr]: the memory is [RiscvSemantics.step]'s ([Run.mi_account_step_projects],
       Run.v:454-468), kept by [VdsoClean.step_clean]; the first-touch accounting
       ([Run.mi_account_step], Run.v:439-449) changes the model only, through
       [State.materialize_model_accesses] (State.v:6850-6856), which rebuilds the model with
       [with_vm_backing] and so keeps [m_kernel] and [m_vmmaps] ([pc_mat_frame]).
     - [sstep_cfg_vdso_call]: [Run.vdso_post] (Run.v:623-635) writes the draw's frame through
       [Run.vdso_write_frame] (Run.v:563-573), which skips every address whose writable view
       ([RiscvSemantics.wview], RiscvSemantics.v:616-628) is [None]; over the window that view
       is [None] ([VdsoClean.wview_none_of_clean]), so the frame write misses it
       ([pc_vwf_clean]).  The effect is then applied; the six numbers a vDSO entry hands the
       dispatcher (Vdso.v:121-131) are clean here ([pc_vdso_ok]).
     - [sstep_cfg_syscall], [sstep_cfg_exit], [sstep_cfg_killed]: the step premise
       [pc_step_ok] asks that every outcome of the pending call be clean ([pc_out_ok]): its
       writes land where the input's writable view is defined, its zero-fills and copy
       destinations miss the window, and [m_kernel], [vm_reserved], [vm_mmap_base] and
       [alloc_top] are kept, which is what [MmVdso.mm_vinv_frame] reads.  [Run.apply_effect]
       (Run.v:176-189) erases, zero-fills, copies and writes exactly those ranges.

   The premise is discharged per syscall number through the model's executable checkers:
   [Checks/ExecutableSpecs.v]'s [check_syscall_complete_ok] turns an outcome of
   [Specs.syscall_spec] into an accepted checker call, [Checks/Sys/DispatchCompute.v] names the
   checker each number reaches, and one walk ([pcl_walk]) splits that checker at every branch.
   The ledger fields come from the model's own frame lemmas: [Checks/VmMapsDisjoint.v]'s
   [check_*_frame] ([m_vmmaps] untouched) for the calls that do not touch the address space, and
   [Checks/MmapTopFrame.v]'s [check_*_top_frame] ([vm_mmap_base], [vm_init_sp], hence
   [alloc_top]) for the memory calls.  A zero-fill is placed off the window by the gate the
   checker tests: [region_free] against [vm_reserved] (Checks/Sys/Mm/Mmap.v:171-343) or against
   the pair itself (Checks/Sys/Mm/Mprotect.v:35-37), the placement search
   ([Placement.linux_place_admissible], Checks/Placement.v:801-806), or the brk grow gate
   ([MmVdso.grow_zeros_off]).  The numbers proved are [pc_proved_nos]; [pc_step_proved] and
   [pc_star_proved] are the step and run statements for calls among them, and
   [pc_step_of_table] / [pc_star_of_table] the statements for every number, given one obligation
   per arm of Sys/SyscallTable.v ([pc_arm_ok]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs MemImageType RiscvSemantics State Monad Specs Run Vdso.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require VmMapsDisjoint MmapTopFrame.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmVdso.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section PairClean.
  Variable segs : list Segment.
  Variables vlo vhi : Z.
  (* no writable segment of [segs] holds a byte of the window *)
  Hypothesis Hnw : forall (x : word) s, vlo <= bv_unsigned x < vhi ->
    find_segment segs (bv_unsigned x) 1 = Some s -> seg_writable s = false.

  (** * What a clean outcome is *)

  (** A view that holds no byte of the window. *)
  Definition pc_win_none (wm : word -> option byte) : Prop :=
    forall x : word, vlo <= bv_unsigned x < vhi -> wm x = None.

  (** A write [(a, bs)] leaves every byte the view [wm] does not define alone. *)
  Definition pc_wcov (wm : word -> option byte) (w : word * list byte) : Prop :=
    forall (m : word -> option byte) (x : word), wm x = None -> write_to_mem m (fst w) (snd w) x = m x.

  (** One syscall outcome [(eff, mo')] at input [i] from model [mo]: writes inside the input's
      writable view, zero-fills and copy destinations off the window, and the four model fields
      [mm_vinv] reads unchanged. *)
  Definition pc_out_ok (i : SyscallInput) (mo : Model) (eff : SyscallEffect) (mo' : Model) : Prop :=
    Forall (pc_wcov (in_wmem i)) (eff_writes eff)
    /\ Forall (range_off vlo vhi) (eff_zeros eff)
    /\ Forall (fun c => range_off vlo vhi (copy_dst c, copy_len c)) (eff_copies eff)
    /\ m_kernel mo' = m_kernel mo
    /\ vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo)
    /\ vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo)
    /\ alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).

  (** From a model where the window sits in the reserved pair, every outcome the specification
      admits at [i] is clean.  The pair premise is what places a fresh grant off the window. *)
  Definition pc_spec_ok (i : SyscallInput) (mo : Model) : Prop :=
    mm_vinv vlo vhi mo ->
    forall eff mo' evs, syscall_spec i mo (Ok eff mo' evs) -> pc_out_ok i mo eff mo'.

  (** The step premise: the call pending at [c], if any, is clean. *)
  Definition pc_step_ok (c : config) : Prop :=
    forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
      pc_spec_ok (sys_input segs (cfg_ms c) x8) (cfg_model c).

  (** * Memory: [Run.apply_effect]'s four ledgers *)

  Lemma pc_unmaps_clean : forall m us, vclean vlo vhi m -> vclean vlo vhi (apply_unmaps m us).
  Proof.
    intros m us C x Hx. destruct us as [|u us]; cbn [apply_unmaps]; [exact (C x Hx)|].
    destruct (zeros_cover (u :: us) x); [reflexivity | exact (C x Hx)].
  Qed.

  Lemma pc_zeros_clean : forall m zs, Forall (range_off vlo vhi) zs ->
    vclean vlo vhi m -> vclean vlo vhi (apply_zeros m zs).
  Proof.
    intros m zs Hz C x Hx. destruct zs as [|z zs]; cbn [apply_zeros]; [exact (C x Hx)|].
    rewrite (zeros_cover_off vlo vhi (z :: zs) x Hx Hz). exact (C x Hx).
  Qed.

  Lemma pc_copies_clean : forall before cs m,
    Forall (fun c => range_off vlo vhi (copy_dst c, copy_len c)) cs ->
    vclean vlo vhi m -> vclean vlo vhi (apply_copies before m cs).
  Proof.
    intros before cs. induction cs as [|c cs IH]; intros m Hc C; cbn [apply_copies]; [exact C|].
    apply IH; [exact (Forall_inv_tail Hc)|].
    assert (H1 : range_off vlo vhi (copy_dst c, copy_len c)) by exact (Forall_inv Hc).
    unfold range_off in H1. cbn [fst snd] in H1.
    intros x Hx. unfold apply_copy. cbv beta.
    destruct (Z.leb_spec (bv_unsigned (copy_dst c)) (bv_unsigned x));
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned (copy_dst c) + bv_unsigned (copy_len c)));
      cbn [andb]; first [exact (C x Hx) | exfalso; lia].
  Qed.

  Lemma pc_writes_clean : forall wm ws m, pc_win_none wm -> Forall (pc_wcov wm) ws ->
    vclean vlo vhi m -> vclean vlo vhi (apply_writes m ws).
  Proof.
    intros wm ws. induction ws as [|[a bs] ws IH]; intros m Hwm Hws C; cbn [apply_writes]; [exact C|].
    apply IH; [exact Hwm | exact (Forall_inv_tail Hws) |].
    assert (H1 : forall (m0 : word -> option byte) (x : word),
               wm x = None -> write_to_mem m0 a bs x = m0 x) by exact (Forall_inv Hws).
    intros x Hx. rewrite (H1 m x (Hwm x Hx)). exact (C x Hx).
  Qed.

  (** [Run.apply_effect]'s memory, in the order it applies the ledgers (Run.v:183-188). *)
  Lemma pc_mem_effect_clean : forall wm m eff, pc_win_none wm ->
    Forall (pc_wcov wm) (eff_writes eff) ->
    Forall (range_off vlo vhi) (eff_zeros eff) ->
    Forall (fun c => range_off vlo vhi (copy_dst c, copy_len c)) (eff_copies eff) ->
    vclean vlo vhi m ->
    vclean vlo vhi (apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps eff))
                                                   (eff_zeros eff)) (eff_copies eff))
                                 (eff_writes eff)).
  Proof.
    intros wm m eff Hwm Hw Hz Hc C.
    apply (pc_writes_clean wm); [exact Hwm | exact Hw |].
    apply pc_copies_clean; [exact Hc |].
    apply pc_zeros_clean; [exact Hz |].
    apply pc_unmaps_clean. exact C.
  Qed.

  Lemma pc_mem_set_reg : forall s r v, ms_mem (set_reg s r v) = ms_mem s.
  Proof.
    intros s r v. unfold set_reg.
    first [ (match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity)
          | reflexivity ].
  Qed.

  Lemma pc_mem_apply_effect : forall s eff,
    ms_mem (apply_effect s eff)
    = apply_writes (apply_copies (ms_mem s) (apply_zeros (apply_unmaps (ms_mem s) (eff_unmaps eff))
                                               (eff_zeros eff)) (eff_copies eff))
                   (eff_writes eff).
  Proof.
    intros s eff. unfold apply_effect. cbv beta zeta. rewrite !pc_mem_set_reg. reflexivity.
  Qed.

  Lemma pc_mem_advance : forall s, ms_mem (advance_past_svc s) = ms_mem s.
  Proof. reflexivity. Qed.

  Lemma pc_mem_vdso_set_pc : forall s pc, ms_mem (vdso_set_pc s pc) = ms_mem s.
  Proof. reflexivity. Qed.

  Lemma pc_mem_vdso_with_mem : forall s m, ms_mem (vdso_with_mem s m) = m.
  Proof. reflexivity. Qed.

  Lemma pc_mem_vdso_write_regs : forall rs vs s, ms_mem (vdso_write_regs s rs vs) = ms_mem s.
  Proof.
    induction rs as [|r rs IH]; intros vs s; destruct vs as [|v vs]; cbn [vdso_write_regs];
      try reflexivity.
    rewrite IH. apply pc_mem_set_reg.
  Qed.

  (** The vDSO frame write stores only where the writable view is defined (Run.v:563-573). *)
  Lemma pc_vwf_clean : forall bs m a, vclean vlo vhi m -> vclean vlo vhi (vdso_write_frame segs m a bs).
  Proof.
    induction bs as [|b bs IH]; intros m a C; cbn [vdso_write_frame]; [exact C|].
    apply IH.
    destruct (wview segs m a) as [b0|] eqn:Ew; [|exact C].
    intros x Hx. cbv beta iota.
    destruct (bv_eqb x a) eqn:Exa; [|exact (C x Hx)].
    exfalso. apply bv_eqb_eq in Exa. subst x.
    rewrite (VdsoClean.wview_none_of_clean segs vlo vhi Hnw m a C Hx) in Ew. discriminate Ew.
  Qed.

  (** [Run.vdso_post] (Run.v:623-635): registers, then the frame, then the effect, then pc. *)
  Lemma pc_vdso_post_clean : forall ms model f eff,
    Forall (pc_wcov (wview segs (ms_mem ms))) (eff_writes eff) ->
    Forall (range_off vlo vhi) (eff_zeros eff) ->
    Forall (fun c => range_off vlo vhi (copy_dst c, copy_len c)) (eff_copies eff) ->
    vclean vlo vhi (ms_mem ms) ->
    vclean vlo vhi (ms_mem (vdso_post segs ms model f eff)).
  Proof.
    intros ms model f eff Hw Hz Hc C.
    unfold vdso_post. cbv beta zeta.
    rewrite pc_mem_vdso_set_pc, pc_mem_apply_effect, pc_mem_vdso_with_mem, pc_mem_vdso_write_regs.
    apply (pc_mem_effect_clean (wview segs (ms_mem ms))); [ | exact Hw | exact Hz | exact Hc | ].
    - intros x Hx. exact (VdsoClean.wview_none_of_clean segs vlo vhi Hnw (ms_mem ms) x C Hx).
    - apply pc_vwf_clean. exact C.
  Qed.

  (** * The model half *)

  Lemma pc_mat_frame : forall m acc m', materialize_model_accesses m acc = Some m' ->
    m_kernel m' = m_kernel m /\ m_vmmaps m' = m_vmmaps m.
  Proof.
    intros m acc m' H. unfold materialize_model_accesses in H.
    destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m)
                (vm_backing_used m) (vm_limit (m_vmmaps m)) acc) as [pages|];
      cbv beta iota in H; [|discriminate H].
    injection H as <-. split; reflexivity.
  Qed.

  Lemma pc_acct_frame : forall ms model ms' model',
    mi_account_step segs ms model = MachineOk (ms', model') ->
    m_kernel model' = m_kernel model /\ m_vmmaps model' = m_vmmaps model.
  Proof.
    intros ms model ms' model' H. unfold mi_account_step in H. cbv beta zeta in H.
    destruct (RiscvSemantics.step_accesses segs ms) as [report| |]; cbv beta iota in H;
      [|discriminate H|discriminate H].
    destruct (materialize_model_accesses model (@accessed_ranges _ report)) as [m1|] eqn:E;
      cbv beta iota in H; [|discriminate H].
    injection H as _ Hm. subst m1.
    exact (pc_mat_frame _ _ _ E).
  Qed.

  Lemma pc_vinv_eq : forall mo mo', m_kernel mo' = m_kernel mo -> m_vmmaps mo' = m_vmmaps mo ->
    mm_vinv vlo vhi mo -> mm_vinv vlo vhi mo'.
  Proof. intros mo mo' Ek Ev VI. unfold mm_vinv in *. rewrite Ek, Ev. exact VI. Qed.

  Lemma pc_vinv_out : forall i mo eff mo', pc_out_ok i mo eff mo' ->
    mm_vinv vlo vhi mo -> mm_vinv vlo vhi mo'.
  Proof.
    intros i mo eff mo' (_ & _ & _ & Ek & Er & Eb & Et) VI.
    exact (mm_vinv_frame vlo vhi mo mo' Ek Er Eb Et VI).
  Qed.

  (** * Building clean outcomes *)

  Lemma pc_out_ok_vm : forall i mo eff mo',
    Forall (pc_wcov (in_wmem i)) (eff_writes eff) ->
    Forall (range_off vlo vhi) (eff_zeros eff) ->
    Forall (fun c => range_off vlo vhi (copy_dst c, copy_len c)) (eff_copies eff) ->
    m_kernel mo' = m_kernel mo -> m_vmmaps mo' = m_vmmaps mo ->
    pc_out_ok i mo eff mo'.
  Proof.
    intros i mo eff mo' Hw Hz Hc Ek Ev. unfold pc_out_ok. rewrite Ev.
    exact (conj Hw (conj Hz (conj Hc (conj Ek (conj eq_refl (conj eq_refl eq_refl)))))).
  Qed.

  (** The unit's mm nodes: [MmVdso.mm_shape] plus [alloc_top] ([MmNodes.nstep_mm_post]). *)
  Lemma pc_out_ok_of_mm_shape : forall i mo rsp mo',
    mm_shape vlo vhi mo rsp mo' -> alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo) ->
    pc_out_ok i mo rsp mo'.
  Proof.
    intros i mo rsp mo' (Hw & Hc & Hz & Ek & Er & Eb) Et.
    unfold pc_out_ok. rewrite Hw, Hc.
    exact (conj (Forall_nil _) (conj Hz (conj (Forall_nil _) (conj Ek (conj Er (conj Eb Et)))))).
  Qed.

  (** What a call that does not touch the address space owes beside [m_vmmaps]: covered
      writes, no zero-fill, no copy, the kernel build kept. *)
  Definition pc_nm (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) : Prop :=
    Forall (pc_wcov (in_wmem i)) (eff_writes eff) /\ eff_zeros eff = [] /\ eff_copies eff = []
    /\ m_kernel m' = m_kernel m.

  Lemma pc_out_of_nm : forall i m eff m', pc_nm i m eff m' -> m_vmmaps m' = m_vmmaps m ->
    pc_out_ok i m eff m'.
  Proof.
    intros i m eff m' (Hw & Hz & Hc & Hk) Hv.
    apply pc_out_ok_vm; [exact Hw | rewrite Hz; constructor | rewrite Hc; constructor
                        | exact Hk | exact Hv].
  Qed.

  (** What a memory call owes beside [vm_mmap_base] and [vm_init_sp]
      ([MmapTopFrame.top_fields_kept]). *)
  Definition pc_mm (i : SyscallInput) (m : Model) (eff : SyscallEffect) (m' : Model) : Prop :=
    Forall (pc_wcov (in_wmem i)) (eff_writes eff)
    /\ Forall (range_off vlo vhi) (eff_zeros eff)
    /\ Forall (fun c => range_off vlo vhi (copy_dst c, copy_len c)) (eff_copies eff)
    /\ m_kernel m' = m_kernel m
    /\ vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m).

  Lemma pc_out_of_mm : forall i m eff m', pc_mm i m eff m' ->
    MmapTopFrame.top_fields_kept (m_vmmaps m) (m_vmmaps m') -> pc_out_ok i m eff m'.
  Proof.
    intros i m eff m' (Hw & Hz & Hc & Hk & Hr) (Hb & Hs).
    unfold pc_out_ok. refine (conj Hw (conj Hz (conj Hc (conj Hk (conj Hr (conj Hb _)))))).
    unfold alloc_top. rewrite Hs. reflexivity.
  Qed.

  (** * Writes inside the writable view *)

  (** A write whose every byte the view defines. *)
  Lemma pc_wcov_of_aux : forall bs (wm : word -> option byte) (a : word),
    read_bytes_aux wm a (length bs) <> None ->
    forall (m : word -> option byte) (x : word), wm x = None -> write_to_mem m a bs x = m x.
  Proof.
    induction bs as [|b bs IH]; intros wm a H m x Hx; [reflexivity|].
    cbn [length read_bytes_aux] in H. cbn [write_to_mem].
    destruct (wm a) as [b0|] eqn:Ea; [|exfalso; apply H; reflexivity].
    match goal with
    | |- context [write_to_mem _ ?nw bs _] =>
        match type of H with
        | context [read_bytes_aux wm ?ns (length bs)] =>
            assert (Hn : read_bytes_aux wm nw (length bs) <> None)
              by (replace nw with ns by reflexivity;
                  destruct (read_bytes_aux wm ns (length bs)); [discriminate | exact H]);
            rewrite (IH wm nw Hn _ x Hx)
        end
    end.
    cbv beta. destruct (bv_eqb x a) eqn:Exa; [|reflexivity].
    exfalso. apply bv_eqb_eq in Exa. subst x.
    rewrite Ea in Hx. discriminate Hx.
  Qed.

  (** A write no longer than a range the checker read through the view. *)
  Lemma pc_wcov_rb : forall (wm : word -> option byte) (a n : word) (w bs : list byte),
    read_bytes_map wm a n = Some w -> Z.of_nat (length bs) <= bv_unsigned n -> pc_wcov wm (a, bs).
  Proof.
    intros wm a n w bs Hr Hl m x Hx. cbn [fst snd].
    rewrite read_bytes_map_eq in Hr.
    assert (Hk : (length bs <= word_to_nat n)%nat).
    { unfold word_to_nat. pose proof (word_unsigned_range n) as Hn. lia. }
    pose proof (read_bytes_aux_prefix (length bs) (word_to_nat n) wm a w Hk Hr) as Hp.
    apply (pc_wcov_of_aux bs wm a); [|exact Hx].
    rewrite Hp. discriminate.
  Qed.

  Lemma pc_wcov_wok : forall (i : SyscallInput) (a n : word) (bs : list byte),
    wmem_ok i a n = true -> Z.of_nat (length bs) <= bv_unsigned n -> pc_wcov (in_wmem i) (a, bs).
  Proof.
    intros i a n bs Hw Hl. apply wmem_ok_true in Hw.
    destruct (read_bytes_map (in_wmem i) a n) as [w|] eqn:Hr; [|exfalso; exact (Hw eq_refl)].
    exact (pc_wcov_rb (in_wmem i) a n w bs Hr Hl).
  Qed.

  (** The same through [State.copy_bytes_map] (State.v:1408-1410). *)
  Lemma pc_wcov_cb : forall (wm : word -> option byte) (a : word) (k : Z) (w bs : list byte),
    copy_bytes_map wm a k = Some w -> 0 <= k < two_pow_64 -> Z.of_nat (length bs) <= k ->
    pc_wcov wm (a, bs).
  Proof.
    intros wm a k w bs Hc Hk Hl. unfold copy_bytes_map in Hc.
    destruct (access_okb a k); cbv beta iota in Hc; [|discriminate Hc].
    apply (pc_wcov_rb wm a (Z_to_bv 64 k) w bs Hc).
    rewrite (bv_unsigned_Z_to_bv_u64 k Hk). exact Hl.
  Qed.

  (** [Uaccess.delivered_writes] (Sys/Uaccess.v:571-575): the delivery read through the view. *)
  Lemma pc_cov_delivered : forall (wm : word -> option byte) (buf : word) (del w : list byte),
    read_bytes_map wm buf (len_word del) = Some w -> Z.of_nat (length del) < two_pow_64 ->
    Forall (pc_wcov wm) (delivered_writes buf del).
  Proof.
    intros wm buf del w Hr Hb. unfold delivered_writes.
    destruct del as [|d ds]; [constructor|].
    constructor; [|constructor].
    apply (pc_wcov_rb wm buf (len_word (d :: ds)) w (d :: ds) Hr).
    rewrite (len_word_unsigned (d :: ds) Hb). lia.
  Qed.

  (** A file read is no longer than its count ([Fs.file_read_unguarded], Fs.v:519-521). *)
  Lemma pc_file_read_len : forall data off cnt,
    Z.of_nat (length (file_read data off cnt)) <= bv_unsigned cnt.
  Proof.
    intros data off cnt. rewrite file_read_unguarded, length_firstn.
    unfold word_to_nat. pose proof (word_unsigned_range cnt) as Hc. lia.
  Qed.

  (** [Ioctl.ifreq_with_index] (Sys/Fs/Ioctl.v:158-159) keeps a 40-byte [struct ifreq] 40 bytes
      long, and a 40-byte copy-in is 40 bytes. *)
  Lemma pc_ifreq_len : forall ifr idx, length ifr = 40%nat ->
    length (ifreq_with_index ifr idx) = 40%nat.
  Proof.
    intros ifr idx H. unfold ifreq_with_index.
    rewrite !length_app, length_firstn, length_skipn, H. reflexivity.
  Qed.

  Lemma pc_copy40_len : forall (mp : word -> option byte) (a : word) (w : list byte),
    copy_bytes_map mp a IFREQ_SIZE = Some w -> length w = 40%nat.
  Proof.
    intros mp a w H. unfold copy_bytes_map in H.
    destruct (access_okb a IFREQ_SIZE); cbv beta iota in H; [|discriminate H].
    apply read_bytes_map_length in H.
    rewrite bv_unsigned_Z_to_bv_u64 in H by (unfold IFREQ_SIZE, two_pow_64; lia).
    unfold IFREQ_SIZE in H. lia.
  Qed.

  (** * The kernel build survives the post-models that branch or recurse *)

  Lemma pcl_k_raise : forall m, m_kernel (raise_sigpipe m) = m_kernel m.
  Proof.
    intros m. unfold raise_sigpipe.
    destruct (negb (m_sigpipe_default m)); [reflexivity|].
    destruct (sigpipe_blocked (m_sigmask m)); reflexivity.
  Qed.

  Lemma pcl_k_sigmask : forall new m, m_kernel (sigmask_deliver_model new m) = m_kernel m.
  Proof.
    intros new m. unfold sigmask_deliver_model.
    destruct (m_sigabrt_pending m && negb (sigabrt_blocked new))%bool; [reflexivity|].
    destruct (m_sigpipe_pending m && negb (sigpipe_blocked new))%bool; reflexivity.
  Qed.

  Lemma pcl_k_forget : forall rs m, m_kernel (forget_vm_ranges rs m) = m_kernel m.
  Proof.
    induction rs as [|[a n] rs IH]; intros m; [reflexivity|].
    cbn [forget_vm_ranges]. rewrite IH. reflexivity.
  Qed.

  Lemma pcl_k_brk : forall m req r, m_kernel (with_brk_next m req r) = m_kernel m.
  Proof. intros m req r. unfold with_brk_next. cbv zeta. rewrite pcl_k_forget. reflexivity. Qed.

  Lemma pcl_k_backing : forall flags a n m, m_kernel (with_mmap_backing flags a n m) = m_kernel m.
  Proof.
    intros flags a n m. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity.
  Qed.

  Lemma pcl_k_repl : forall flags a n m, m_kernel (with_mmap_replacement flags a n m) = m_kernel m.
  Proof. intros flags a n m. unfold with_mmap_replacement. rewrite pcl_k_backing. reflexivity. Qed.

  (** * Zero-fills off the window *)

  (** Free against [vm_reserved] alone: the pair is in it ([MmVdso.mm_vinv]). *)
  Lemma pc_off_res0 : forall mo (a n : word), mm_vinv vlo vhi mo ->
    region_free (vm_reserved (m_vmmaps mo)) a n = true -> range_off vlo vhi (a, n).
  Proof.
    intros mo a n VI Hf. unfold mm_vinv, win_in in VI.
    destruct VI as [(r & Hin & Hlo & Hhi) Hinc].
    exact (off_of_free vlo vhi _ a n r Hf (Hinc r Hin) Hlo Hhi).
  Qed.

  (** A fresh grant the placement search chose ([Checks.Sys.Mm.Mmap.mmap_grant_len_ok],
      Checks/Sys/Mm/Mmap.v:25-34; [Placement.linux_place_is_iff], Checks/Placement.v:1019-1022;
      [Placement.linux_place_admissible], :801-806). *)
  Lemma pc_place_off : forall mo thp hint len r, mm_vinv vlo vhi mo -> w_is0 len = false ->
    linux_place_is (m_vmmaps mo) thp hint (page_round_up_Z (bv_unsigned len)) r = true ->
    range_off vlo vhi (r, Z_to_bv 64 (page_round_up_Z (bv_unsigned len))).
  Proof.
    intros mo thp hint len r VI Hl Hp.
    destruct (mmap_grant_len_ok len Hl) as [Hpos Hal].
    apply (linux_place_is_iff _ _ _ _ _ Hpos Hal) in Hp.
    destruct (linux_place_admissible _ _ _ _ _ Hpos Hal Hp) as (_ & _ & _ & Hf).
    pose proof (vinv_off_res vlo vhi mo _ _ VI Hf) as Ho.
    unfold range_off in Ho |- *. cbn [fst snd] in Ho |- *.
    rewrite (bv_unsigned_Z_to_bv_u64 (bv_unsigned r) (word_unsigned_range r)) in Ho.
    exact Ho.
  Qed.

  (** * The checker walk *)

  (* The shared acceptors every checker reaches, and the effect's projections. *)
  Ltac pcl_unfold H :=
    cbv beta iota zeta delta [check_ret_only check_ret_only_copyins clear_copyins with_copyins
      check_copyins check_copyins_after check_copyin_prefix strip_copyin_prefix eff_is_errno
      check_efault_or check_access_ok_zero check_sigpipe_write check_sigpipe_writev
      check_new_fd_result check_open_result
      eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins] in H.

  (* Split the checker hypothesis [H] at every [if] and [match] whose scrutinee is a variable or
     an application (so never itself a [match]: the innermost test goes first), until no branch
     is left to split; the refusals are then closed by [discriminate].  The effect is destructed
     before the walk, so its fields are variables. *)
  Ltac pcl_walk H :=
    repeat (cbv beta iota zeta delta [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
                                      eff_copyins] in H;
            match type of H with
            | context [match ?x with _ => _ end] =>
                first [ is_var x; destruct x
                      | lazymatch x with _ _ => destruct x eqn:? end ]
            end);
    try discriminate H.

  (* The accepting guard of a leaf, split and turned into equations. *)
  Ltac pcl_norm :=
    repeat match goal with
    | Hb : andb _ _ = true |- _ => apply andb_prop in Hb; destruct Hb
    | Hb : orb _ _ = false |- _ => apply orb_false_elim in Hb; destruct Hb
    | Hb : negb _ = true |- _ => apply negb_true_iff in Hb
    | Hb : negb _ = false |- _ => apply negb_false_iff in Hb
    | Hb : bv_eqb _ _ = true |- _ => apply bv_eqb_eq in Hb
    | Hb : listN_eqb _ _ = true |- _ => apply listN_eqb_eq in Hb
    | Hb : listNN_eqb _ _ = true |- _ => apply listNN_eqb_eq in Hb
    | Hb : writes_eqb _ _ = true |- _ => apply writes_eqb_eq in Hb
    | Hb : listCopy_eqb _ _ = true |- _ => apply listCopy_eqb_eq in Hb
    | Hb : access_ranges_eqb _ _ = true |- _ => apply access_ranges_eqb_eq in Hb
    | Hb : Z.leb _ _ = true |- _ => apply Z.leb_le in Hb
    | Hb : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hb
    | Hb : Z.leb _ _ = false |- _ => apply Z.leb_gt in Hb
    | Hb : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in Hb
    | Hb : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hb
    | Hb : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hb
    (* a field the walk already split, against the list the guard names *)
    | Hb : @cons _ _ _ = @cons _ _ _ |- _ => injection Hb; clear Hb; intros
    | Hb : @pair _ _ _ _ = @pair _ _ _ _ |- _ => injection Hb; clear Hb; intros
    | Hb : @nil _ = @cons _ _ _ |- _ => discriminate Hb
    | Hb : @cons _ _ _ = @nil _ |- _ => discriminate Hb
    end; subst.

  (* [Z.of_nat (length L) < two_pow_64], from the transfer bound in context: the count clamp
     (posed as [rw_count_clamp_range] by the arms that read a count), a file read
     ([pc_file_read_len]) or a pipe take ([State.pipe_take_length], State.v:5799-5800). *)
  Ltac pcl_bound :=
    try match goal with
        | E : ?t = ?L |- context [length ?L] =>
            lazymatch L with _ :: _ => rewrite <- E end
        end;
    first
      [ (unfold two_pow_64, MAX_RW_COUNT in *; lia)
      | (eapply Z.le_lt_trans; [apply pc_file_read_len | exact (proj2 (word_unsigned_range _))])
      | (match goal with |- context [length (pipe_take ?q ?k)] => pose proof (pipe_take_length q k) end;
         unfold two_pow_64, MAX_RW_COUNT in *; lia) ].

  (* [Z.of_nat (length bs) <= bv_unsigned n]. *)
  Ltac pcl_len :=
    first
      [ (rewrite len_word_unsigned; [lia | pcl_bound])
      | (cbn [length word_le8 word_le4];
         rewrite bv_unsigned_Z_to_bv_u64 by (unfold two_pow_64; lia); lia)
      | (unfold two_pow_64, MAX_RW_COUNT in *; lia) ].

  (* One write, against a range the checker read through the view. *)
  Ltac pcl_cov :=
    match goal with
    | Hr : read_bytes_map (in_wmem ?i) ?a ?n = Some _ |- pc_wcov (in_wmem ?i) (?a, ?bs) =>
        apply (pc_wcov_rb (in_wmem i) a n _ bs Hr); pcl_len
    | Hw : wmem_ok ?i ?a ?n = true |- pc_wcov (in_wmem ?i) (?a, ?bs) =>
        apply (pc_wcov_wok i a n bs Hw); pcl_len
    | Hc : copy_bytes_map (in_wmem ?i) ?a ?k = Some _ |- pc_wcov (in_wmem ?i) (?a, ?bs) =>
        apply (pc_wcov_cb (in_wmem i) a k _ bs Hc); [unfold two_pow_64; lia | pcl_len]
    end.

  (* A leaf's write list; a write [pcl_cov] does not close is left for [pcl_close]. *)
  Ltac pcl_ws :=
    repeat first [ apply Forall_nil | (apply Forall_cons; [try pcl_cov |]) ].

  Ltac pcl_kern :=
    first
      [ reflexivity
      | (rewrite ?pcl_k_raise, ?pcl_k_sigmask, ?pcl_k_forget, ?pcl_k_brk, ?pcl_k_backing,
           ?pcl_k_repl; reflexivity)
      | (repeat (match goal with
                 | |- context [match ?x with _ => _ end] =>
                     first [ is_var x; destruct x | lazymatch x with _ _ => destruct x end ]
                 end; cbv beta iota);
         rewrite ?pcl_k_raise, ?pcl_k_sigmask, ?pcl_k_forget, ?pcl_k_brk, ?pcl_k_backing,
           ?pcl_k_repl; reflexivity) ].

  (* A leaf of a call that does not touch the address space.  [pcl_norm] closes a leaf whose guard
     contradicts the effect's split fields (a [nil] against a [cons]), so the rest runs only on the
     goals it leaves. *)
  Ltac pcl_nleaf H :=
    injection H as <- <-; pcl_norm;
    (unfold pc_nm; cbn [eff_writes eff_zeros eff_copies];
     refine (conj _ (conj eq_refl (conj eq_refl _))); [pcl_ws | pcl_kern]).

  (* The writes [pcl_ws] left: a delivery, and the SIOCGIFINDEX write-back. *)
  Ltac pcl_close :=
    first
      [ pcl_cov
      | match goal with
        | Hr : read_bytes_map (in_wmem ?i) ?buf (len_word ?del) = Some _
          |- Forall (pc_wcov (in_wmem ?i)) (delivered_writes ?buf ?del) =>
            apply (pc_cov_delivered (in_wmem i) buf del _ Hr); pcl_bound
        end
      | match goal with
        | Hc : copy_bytes_map (in_mem ?i) ?a IFREQ_SIZE = Some ?ifr,
          Hr : read_bytes_map (in_wmem ?i) ?a (Z_to_bv 64 IFREQ_SIZE) = Some _
          |- pc_wcov (in_wmem ?i) (?a, ifreq_with_index ?ifr ?k) =>
            apply (pc_wcov_rb (in_wmem i) a (Z_to_bv 64 IFREQ_SIZE) _ _ Hr);
            rewrite (pc_ifreq_len ifr k (pc_copy40_len _ _ _ Hc));
            rewrite bv_unsigned_Z_to_bv_u64 by (unfold IFREQ_SIZE, two_pow_64; lia);
            unfold IFREQ_SIZE; lia
        end ].

  (* One zero-filled range, off the window by the gate the checker tested. *)
  Ltac pcl_off VI :=
    match goal with
    | Hf : region_free (vm_reserved (m_vmmaps ?mo) ++ vm_maps (m_vmmaps ?mo)) ?a ?n = true
      |- range_off _ _ (?a, ?n) => exact (vinv_off_res vlo vhi mo a n VI Hf)
    | Hf : region_free (vm_reserved (m_vmmaps ?mo)) ?a ?n = true
      |- range_off _ _ (?a, ?n) => exact (pc_off_res0 mo a n VI Hf)
    | Hf : region_free (vdso_reserved (m_kernel ?mo) (vdso_top (m_vmmaps ?mo))) ?a ?n = true
      |- range_off _ _ (?a, ?n) => exact (vinv_off_vdso vlo vhi mo a n VI Hf)
    | Hp : linux_place_is (m_vmmaps ?mo) _ _ (page_round_up_Z (bv_unsigned ?len)) ?a = true,
      Hl : w_is0 ?len = false
      |- range_off _ _ (?a, _) => exact (pc_place_off mo _ _ len a VI Hl Hp)
    end.

  Ltac pcl_zeros VI :=
    first
      [ apply Forall_nil
      | match goal with
        | Hb : brk_r_ok ?mo ?q ?r = true |- Forall _ (brk_zeros ?q ?r _) =>
            exact (grow_zeros_off vlo vhi mo q r VI Hb)
        end
      | (apply Forall_cons; [pcl_off VI | apply Forall_nil]) ].

  (* [vm_reserved] of a memory call's post-model (the wrappers: Checks/MmapTopFrame.v:62-74). *)
  Ltac pcl_res :=
    rewrite ?MmapTopFrame.m_vmmaps_with_mmap_backing, ?MmapTopFrame.m_vmmaps_with_mmap_replacement,
      ?MmapTopFrame.m_vmmaps_with_brk_next; reflexivity.

  (* A leaf of a memory call. *)
  Ltac pcl_mleaf H VI :=
    injection H as <- <-; pcl_norm;
    unfold pc_mm; cbn [eff_writes eff_zeros eff_copies];
    refine (conj _ (conj _ (conj _ (conj _ _))));
    [ pcl_ws | pcl_zeros VI | apply Forall_nil | pcl_kern | pcl_res ].

  (** * The arms, checker by checker *)

  (* close (57): Checks/Sys/Fs/Open.v:524-530. *)
  Lemma pcn_close : forall i fd eff m m' evs,
    check_close fd eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_close] in H. pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
  Qed.

  (* exit and exit_group (93, 94): Checks/Sys/Kernel/Exit.v:19-22. *)
  Lemma pcn_exit : forall i code eff m m' evs,
    check_exit code eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i code [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_exit] in H. pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
  Qed.

  (* set_tid_address (96): Checks/Sys/Kernel/Fork.v:19-31. *)
  Lemma pcn_set_tid_address : forall i eff m m' evs,
    check_set_tid_address eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_set_tid_address] in H. pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
  Qed.

  (* clock_gettime (113): Checks/Sys/Kernel/Time/PosixTimers.v:41-91; the three predicates
     open with [Nat.eqb (length bs) 16] (Sys/Kernel/Time/PosixTimers.v:89-92, :149-152,
     :227-230). *)
  Lemma pcn_clock_gettime : forall i clkid tp eff m m' evs,
    check_clock_gettime i clkid tp eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i clkid tp [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_clock_gettime realtime_ok_b cputime_ok_b timespec_ok_b] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
    all: pcl_close.
  Qed.

  (* clock_getres (114): Checks/Sys/Kernel/Time/PosixTimers.v:294-303 and :379-395; the
     destination test is Sys/Kernel/Time/PosixTimers.v:685-690. *)
  Lemma pcn_clock_getres : forall i clkid tp eff m m' evs,
    check_clock_getres i clkid tp eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i clkid tp [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_clock_getres check_clock_getres_result
      clock_getres_resolution_b clock_getres_dst_ok_b] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
    all: pcl_close.
  Qed.

  (* gettimeofday (169): Checks/Sys/Kernel/Time/Time.v:31-49; [timeval_ok_b] opens with the
     length test (Sys/Kernel/Time/Time.v:57-60). *)
  Lemma pcn_gettimeofday : forall i tv tz eff m m' evs,
    check_gettimeofday i tv tz eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i tv tz [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_gettimeofday timeval_ok_b] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
    all: pcl_close.
  Qed.

  (* read (63): Checks/Sys/Fs/ReadWrite.v:1442-1713, with its helpers at :25-60, :466-479,
     :537-545, :627-653 and :1153-1179.  Every delivery is read through [in_wmem] first:
     [wmem_ok] on the delivered prefix (:1473, :1529), or [read_bytes_map] of the delivery
     (:49, :634, :1561, :1593, :1647, :1692) or of the eight counter bytes (:1163). *)
  Lemma pcn_read : forall i fd buf count eff m m' evs,
    check_read i fd buf count eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd buf count [ret ws zs us cs ci] m m' evs H.
    pose proof (rw_count_clamp_range count) as Rc.
    cbv beta iota zeta delta [check_read check_read_urandom check_socket_pending_error
      check_eventfd_read check_stream_read check_stream_read_empty check_stream_read_reset] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
    all: pcl_close.
  Qed.

  (* write (64): Checks/Sys/Fs/ReadWrite.v:1787-2031 with :1726-1773, :802-837, :1040-1045 and
     :1326; no arm writes user memory. *)
  Lemma pcn_write : forall i fd buf count eff m m' evs,
    check_write i fd buf count eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd buf count [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_write check_write_fault_extend check_eventfd_write
      check_anon_write_fault check_anon_fault_extend anon_place_fds check_stream_write
      check_stream_send] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
  Qed.

  (* writev (66): Checks/Sys/Fs/ReadWrite.v:5228-5528 with :5183-5186; no arm writes user
     memory. *)
  Lemma pcn_writev : forall i fd iov iovcnt eff m m' evs,
    check_writev i fd iov iovcnt eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd iov iovcnt [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_writev check_write_fault_extend check_anon_write_fault
      check_anon_fault_extend anon_place_fds check_stream_send] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
  Qed.

  (* openat (56): Checks/Sys/Fs/Open.v:507-513 and the bodies at :110-481; the effect is a
     return and the pathname copy-in only. *)
  Lemma pcn_openat : forall i dirfd pathp flags eff m m' evs,
    check_openat i dirfd pathp flags eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i dirfd pathp flags [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_openat Open.check_openat_body Open.check_openat_resolved
      Open.check_openat_sep Open.check_openat_localtime Open.check_openat_devnull
      Open.check_open_devnull Open.check_openat_urandom Open.check_open_urandom
      Open.check_openat_procfd Open.check_openat_tmp Open.check_openat_read
      Open.check_openat_create Open.check_openat_excl Open.check_openat_dir
      Open.check_openat_append Open.check_openat_rdwr Open.check_openat_rdwr_excl
      check_create_wronly check_open_append check_open_rdwr] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
  Qed.

  (* ioctl (29): Checks/Sys/Fs/Ioctl.v:181-196 with :22-30 and :71-89; the one write is the
     40-byte write-back behind the 40-byte [read_bytes_map] (:78-80). *)
  Lemma pcn_ioctl : forall i fd req eff m m' evs,
    check_ioctl i fd req eff m = CheckOk m' evs -> pc_nm i m eff m'.
  Proof.
    intros i fd req [ret ws zs us cs ci] m m' evs H.
    cbv beta iota zeta delta [check_ioctl check_siocgifindex check_ifreq_writeback] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_nleaf H.
    all: pcl_close.
  Qed.

  (* brk (214): Checks/Sys/Mm/Mmap.v:64-74; the grow zero-fill is [MmVdso.grow_zeros_off]. *)
  Lemma pcm_brk : forall i req eff m m' evs, mm_vinv vlo vhi m ->
    check_brk req eff m = CheckOk m' evs -> pc_mm i m eff m'.
  Proof.
    intros i req [ret ws zs us cs ci] m m' evs VI H.
    cbv beta iota zeta delta [check_brk] in H. pcl_unfold H. pcl_walk H.
    all: pcl_mleaf H VI.
  Qed.

  (* mmap (222): Checks/Sys/Mm/Mmap.v:79-424.  The zero-filled grants: the placement search
     (:118-120), [region_free] against [vm_reserved] (:256-257, :311) or against
     [vm_reserved ++ vm_maps] (:289-290, :396). *)
  Lemma pcm_mmap : forall i addr len prot flags fd off eff m m' evs, mm_vinv vlo vhi m ->
    check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> pc_mm i m eff m'.
  Proof.
    intros i addr len prot flags fd off [ret ws zs us cs ci] m m' evs VI H.
    cbv beta iota zeta delta [check_mmap check_mmap_fixed_overflow] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_mleaf H VI.
  Qed.

  (* munmap (215): Checks/Sys/Mm/Mmap.v:426-467; no zero-fill, only unmaps. *)
  Lemma pcm_munmap : forall i addr len eff m m' evs, mm_vinv vlo vhi m ->
    check_munmap addr len eff m = CheckOk m' evs -> pc_mm i m eff m'.
  Proof.
    intros i addr len [ret ws zs us cs ci] m m' evs VI H.
    cbv beta iota zeta delta [check_munmap] in H. pcl_unfold H. pcl_walk H.
    all: pcl_mleaf H VI.
  Qed.

  (* mprotect (226): Checks/Sys/Mm/Mprotect.v:19-59; the exposed pages are zero-filled behind
     [region_free] against the pair (:35-37). *)
  Lemma pcm_mprotect : forall i addr len prot eff m m' evs, mm_vinv vlo vhi m ->
    check_mprotect addr len prot eff m = CheckOk m' evs -> pc_mm i m eff m'.
  Proof.
    intros i addr len prot [ret ws zs us cs ci] m m' evs VI H.
    cbv beta iota zeta delta [check_mprotect] in H. pcl_unfold H. pcl_walk H.
    all: pcl_mleaf H VI.
  Qed.

  (* madvise (233): Checks/Sys/Mm/Madvise.v:24-43; the zapped range is [region_free] against
     [vm_reserved] ([Madvise.madvise_dontneed_ok], Sys/Mm/Madvise.v:171-174). *)
  Lemma pcm_madvise : forall i addr len advice eff m m' evs, mm_vinv vlo vhi m ->
    check_madvise addr len advice eff m = CheckOk m' evs -> pc_mm i m eff m'.
  Proof.
    intros i addr len advice [ret ws zs us cs ci] m m' evs VI H.
    cbv beta iota zeta delta [check_madvise madvise_dontneed_ok] in H.
    pcl_unfold H. pcl_walk H.
    all: pcl_mleaf H VI.
  Qed.

  (** * Clean outcomes, with the ledger frame of each checker *)

  Lemma pco_close : forall i fd eff m m' evs,
    check_close fd eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i fd eff m m' evs H. apply pc_out_of_nm;
      [exact (pcn_close i fd eff m m' evs H) | exact (VmMapsDisjoint.check_close_frame fd eff m m' evs H)].
  Qed.

  Lemma pco_exit : forall i code eff m m' evs,
    check_exit code eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i code eff m m' evs H. apply pc_out_of_nm;
      [exact (pcn_exit i code eff m m' evs H) | exact (VmMapsDisjoint.check_exit_frame code eff m m' evs H)].
  Qed.

  Lemma pco_set_tid_address : forall i eff m m' evs,
    check_set_tid_address eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_set_tid_address i eff m m' evs H)
      | exact (VmMapsDisjoint.check_set_tid_address_frame eff m m' evs H) ].
  Qed.

  Lemma pco_clock_gettime : forall i clkid tp eff m m' evs,
    check_clock_gettime i clkid tp eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i clkid tp eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_clock_gettime i clkid tp eff m m' evs H)
      | exact (VmMapsDisjoint.check_clock_gettime_frame i clkid tp eff m m' evs H) ].
  Qed.

  Lemma pco_clock_getres : forall i clkid tp eff m m' evs,
    check_clock_getres i clkid tp eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i clkid tp eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_clock_getres i clkid tp eff m m' evs H)
      | exact (VmMapsDisjoint.check_clock_getres_frame i clkid tp eff m m' evs H) ].
  Qed.

  Lemma pco_gettimeofday : forall i tv tz eff m m' evs,
    check_gettimeofday i tv tz eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i tv tz eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_gettimeofday i tv tz eff m m' evs H)
      | exact (VmMapsDisjoint.check_gettimeofday_frame i tv tz eff m m' evs H) ].
  Qed.

  Lemma pco_read : forall i fd buf count eff m m' evs,
    check_read i fd buf count eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i fd buf count eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_read i fd buf count eff m m' evs H)
      | exact (VmMapsDisjoint.check_read_frame i fd buf count eff m m' evs H) ].
  Qed.

  Lemma pco_write : forall i fd buf count eff m m' evs,
    check_write i fd buf count eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i fd buf count eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_write i fd buf count eff m m' evs H)
      | exact (VmMapsDisjoint.check_write_frame i fd buf count eff m m' evs H) ].
  Qed.

  Lemma pco_writev : forall i fd iov iovcnt eff m m' evs,
    check_writev i fd iov iovcnt eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i fd iov iovcnt eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_writev i fd iov iovcnt eff m m' evs H)
      | exact (VmMapsDisjoint.check_writev_frame i fd iov iovcnt eff m m' evs H) ].
  Qed.

  Lemma pco_openat : forall i dirfd pathp flags eff m m' evs,
    check_openat i dirfd pathp flags eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i dirfd pathp flags eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_openat i dirfd pathp flags eff m m' evs H)
      | exact (VmMapsDisjoint.check_openat_frame i dirfd pathp flags eff m m' evs H) ].
  Qed.

  Lemma pco_ioctl : forall i fd req eff m m' evs,
    check_ioctl i fd req eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i fd req eff m m' evs H. apply pc_out_of_nm;
      [ exact (pcn_ioctl i fd req eff m m' evs H)
      | exact (VmMapsDisjoint.check_ioctl_frame i fd req eff m m' evs H) ].
  Qed.

  Lemma pco_brk : forall i req eff m m' evs, mm_vinv vlo vhi m ->
    check_brk req eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i req eff m m' evs VI H. apply pc_out_of_mm;
      [ exact (pcm_brk i req eff m m' evs VI H)
      | exact (MmapTopFrame.check_brk_top_frame req eff m m' evs H) ].
  Qed.

  Lemma pco_mmap : forall i addr len prot flags fd off eff m m' evs, mm_vinv vlo vhi m ->
    check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i addr len prot flags fd off eff m m' evs VI H. apply pc_out_of_mm;
      [ exact (pcm_mmap i addr len prot flags fd off eff m m' evs VI H)
      | exact (MmapTopFrame.check_mmap_top_frame addr len prot flags fd off eff m m' evs H) ].
  Qed.

  Lemma pco_munmap : forall i addr len eff m m' evs, mm_vinv vlo vhi m ->
    check_munmap addr len eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i addr len eff m m' evs VI H. apply pc_out_of_mm;
      [ exact (pcm_munmap i addr len eff m m' evs VI H)
      | exact (MmapTopFrame.check_munmap_top_frame addr len eff m m' evs H) ].
  Qed.

  Lemma pco_mprotect : forall i addr len prot eff m m' evs, mm_vinv vlo vhi m ->
    check_mprotect addr len prot eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i addr len prot eff m m' evs VI H. apply pc_out_of_mm;
      [ exact (pcm_mprotect i addr len prot eff m m' evs VI H)
      | exact (MmapTopFrame.check_mprotect_top_frame addr len prot eff m m' evs H) ].
  Qed.

  Lemma pco_madvise : forall i addr len advice eff m m' evs, mm_vinv vlo vhi m ->
    check_madvise addr len advice eff m = CheckOk m' evs -> pc_out_ok i m eff m'.
  Proof.
    intros i addr len advice eff m m' evs VI H. apply pc_out_of_mm;
      [ exact (pcm_madvise i addr len advice eff m m' evs VI H)
      | exact (MmapTopFrame.check_madvise_top_frame addr len advice eff m m' evs H) ].
  Qed.

  (** * The premise, number by number *)

  (** Through the executable checker: [ExecutableSpecs.check_syscall_complete_ok]
      (Checks/ExecutableSpecs.v:132-134). *)
  Lemma pc_spec_of_check : forall i mo,
    (forall eff mo' evs, mm_vinv vlo vhi mo -> check_syscall i eff mo = CheckOk mo' evs ->
       pc_out_ok i mo eff mo') ->
    pc_spec_ok i mo.
  Proof.
    intros i mo H VI eff mo' evs Hs.
    exact (H eff mo' evs VI (check_syscall_complete_ok i eff mo mo' evs Hs)).
  Qed.

  (* [Checks/Sys/DispatchCompute.v] has no lemma for 114; this is its proof shape. *)
  Lemma pc_cs_114 : forall i eff m, bv_unsigned (in_sysno i) = 114 ->
    check_syscall i eff m = check_clock_getres i (clockid32 (in_arg i 0)) (in_arg i 1) eff m.
  Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.

  Lemma pc_spec_ok_29 : forall i mo, bv_unsigned (in_sysno i) = 29 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_ioctl i eff mo Hn) in H. exact (pco_ioctl _ _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_56 : forall i mo, bv_unsigned (in_sysno i) = 56 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_openat i eff mo Hn) in H. exact (pco_openat _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_57 : forall i mo, bv_unsigned (in_sysno i) = 57 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_close i eff mo Hn) in H. exact (pco_close _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_63 : forall i mo, bv_unsigned (in_sysno i) = 63 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_read i eff mo Hn) in H. exact (pco_read _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_64 : forall i mo, bv_unsigned (in_sysno i) = 64 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_write i eff mo Hn) in H. exact (pco_write _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_66 : forall i mo, bv_unsigned (in_sysno i) = 66 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_writev i eff mo Hn) in H. exact (pco_writev _ _ _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_93 : forall i mo, bv_unsigned (in_sysno i) = 93 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_exit i eff mo Hn) in H. exact (pco_exit _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_94 : forall i mo, bv_unsigned (in_sysno i) = 94 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_exit_group i eff mo Hn) in H. exact (pco_exit _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_96 : forall i mo, bv_unsigned (in_sysno i) = 96 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_set_tid_address i eff mo Hn) in H.
    exact (pco_set_tid_address _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_113 : forall i mo, bv_unsigned (in_sysno i) = 113 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_clock_gettime i eff mo Hn) in H.
    exact (pco_clock_gettime _ _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_114 : forall i mo, bv_unsigned (in_sysno i) = 114 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (pc_cs_114 i eff mo Hn) in H. exact (pco_clock_getres _ _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_169 : forall i mo, bv_unsigned (in_sysno i) = 169 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs _ H.
    rewrite (check_syscall_gettimeofday i eff mo Hn) in H.
    exact (pco_gettimeofday _ _ _ _ _ _ _ H).
  Qed.

  Lemma pc_spec_ok_214 : forall i mo, bv_unsigned (in_sysno i) = 214 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs VI H.
    rewrite (check_syscall_brk i eff mo Hn) in H. exact (pco_brk _ _ _ _ _ _ VI H).
  Qed.

  Lemma pc_spec_ok_215 : forall i mo, bv_unsigned (in_sysno i) = 215 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs VI H.
    rewrite (check_syscall_munmap i eff mo Hn) in H. exact (pco_munmap _ _ _ _ _ _ _ VI H).
  Qed.

  Lemma pc_spec_ok_222 : forall i mo, bv_unsigned (in_sysno i) = 222 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs VI H.
    rewrite (check_syscall_mmap i eff mo Hn) in H.
    exact (pco_mmap _ _ _ _ _ _ _ _ _ _ _ VI H).
  Qed.

  Lemma pc_spec_ok_226 : forall i mo, bv_unsigned (in_sysno i) = 226 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs VI H.
    rewrite (check_syscall_mprotect i eff mo Hn) in H. exact (pco_mprotect _ _ _ _ _ _ _ _ VI H).
  Qed.

  Lemma pc_spec_ok_233 : forall i mo, bv_unsigned (in_sysno i) = 233 -> pc_spec_ok i mo.
  Proof.
    intros i mo Hn. apply pc_spec_of_check. intros eff mo' evs VI H.
    rewrite (check_syscall_madvise i eff mo Hn) in H. exact (pco_madvise _ _ _ _ _ _ _ _ VI H).
  Qed.

  (** A number with no arm admits no outcome (Run.v:2730-2739). *)
  Lemma pc_spec_ok_unarmed : forall i mo,
    LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.lookup_arm
      LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable.spec_table
      (bv_unsigned (in_sysno i)) = None ->
    pc_spec_ok i mo.
  Proof.
    intros i mo E _ eff mo' evs Hs. exfalso. exact (syscall_spec_unarmed i mo eff mo' evs E Hs).
  Qed.

  (** The numbers proved here. *)
  Definition pc_proved_nos : list Z :=
    [29; 56; 57; 63; 64; 66; 93; 94; 96; 113; 114; 169; 214; 215; 222; 226; 233].

  Lemma pc_spec_ok_proved : forall i mo,
    In (bv_unsigned (in_sysno i)) pc_proved_nos -> pc_spec_ok i mo.
  Proof.
    intros i mo Hin. unfold pc_proved_nos in Hin. cbn [In] in Hin.
    repeat match type of Hin with _ \/ _ => destruct Hin as [Hin | Hin] end.
    all: first
      [ contradiction
      | (symmetry in Hin;
         first
           [ exact (pc_spec_ok_29 i mo Hin) | exact (pc_spec_ok_56 i mo Hin)
           | exact (pc_spec_ok_57 i mo Hin) | exact (pc_spec_ok_63 i mo Hin)
           | exact (pc_spec_ok_64 i mo Hin) | exact (pc_spec_ok_66 i mo Hin)
           | exact (pc_spec_ok_93 i mo Hin) | exact (pc_spec_ok_94 i mo Hin)
           | exact (pc_spec_ok_96 i mo Hin) | exact (pc_spec_ok_113 i mo Hin)
           | exact (pc_spec_ok_114 i mo Hin) | exact (pc_spec_ok_169 i mo Hin)
           | exact (pc_spec_ok_214 i mo Hin) | exact (pc_spec_ok_215 i mo Hin)
           | exact (pc_spec_ok_222 i mo Hin) | exact (pc_spec_ok_226 i mo Hin)
           | exact (pc_spec_ok_233 i mo Hin) ]) ].
  Qed.

  (** Every number a vDSO entry hands the dispatcher (Vdso.v:121-131): 113, 114 and 169 are
      proved above, and 168, 258 and 259 have no arm. *)
  Lemma pc_vdso_ok : forall ms model fn n, vdso_fn_sysno fn = Some n ->
    pc_spec_ok (sys_input segs ms (Z_to_bv 64 n)) model.
  Proof.
    intros ms model fn n Hn.
    destruct fn; cbn in Hn; try discriminate Hn; injection Hn as <-;
      first
        [ apply pc_spec_ok_113; reflexivity
        | apply pc_spec_ok_114; reflexivity
        | apply pc_spec_ok_169; reflexivity
        | apply pc_spec_ok_unarmed; reflexivity ].
  Qed.

  (** * The step lemma *)

  Theorem pc_step : forall cfg c evs c',
    sstep_cfg segs cfg c evs (SNext c') -> pc_step_ok c ->
    vc_cfg vlo vhi c -> vc_cfg vlo vhi c'.
  Proof.
    intros cfg c0 evs0 c' H. remember (SNext c') as st eqn:Est. revert Est.
    destruct H as [ms model ms' model' Hh Hp Ha
                 | ms model Hh Hp Ha
                 | ms model Hh Hp Ha Hv
                 | ms model fn n eff model' model'' evs Hh Hp Ha Hv Hn Hs Hf Hh' Hm
                 | ms model fn n eff model' evs Hh Hp Ha Hv Hn Hs Hf Hh' Hm
                 | ms model fn Hh Hp Ha Hv Hu
                 | ms model x8 eff model' model'' evs Hh Hp Hs Hsp Hh' Hm
                 | ms model x8 eff model' evs Hh Hp Hs Hsp Hh' Hm
                 | ms model x8 eff model' evs code Hh Hp Hs Hh' Hk
                 | ms model x8 eff model' evs sg Hh Hp Hs Hk
                 | ms model x8 Hh Hp Hs ];
      intros Est; try discriminate Est; injection Est as Ec; subst c';
      intros SCs VC; unfold vc_cfg in VC |- *; cbn [cfg_ms cfg_model] in VC |- *;
      destruct VC as [C VI].
    - (* a machine step and its first-touch accounting *)
      destruct (pc_acct_frame ms model ms' model' Ha) as [Ek Ev]. split.
      + exact (VdsoClean.step_clean segs vlo vhi Hnw ms ms'
                 (mi_account_step_projects segs ms model ms' model' Ha) C).
      + exact (pc_vinv_eq model model' Ek Ev VI).
    - (* a vDSO call *)
      pose proof (pc_vdso_ok ms model fn n Hn VI eff model' evs Hs) as OK.
      destruct (pc_mat_frame model' (syscall_effect_accesses eff) model'' Hm) as [Ek Ev].
      assert (VI' : mm_vinv vlo vhi model') by exact (pc_vinv_out _ _ _ _ OK VI).
      destruct OK as (Hw & Hz & Hc & _).
      split.
      + exact (pc_vdso_post_clean ms model (vdso_frame segs) eff Hw Hz Hc C).
      + apply (pc_vinv_eq model'' (with_vdso_bump model'')); [reflexivity | reflexivity |].
        exact (pc_vinv_eq model' model'' Ek Ev VI').
    - (* a system call that returns *)
      pose proof (SCs x8 Hp VI eff model' evs Hs) as OK. cbn [cfg_ms cfg_model] in OK.
      destruct (pc_mat_frame model' (syscall_effect_accesses eff) model'' Hm) as [Ek Ev].
      assert (VI' : mm_vinv vlo vhi model') by exact (pc_vinv_out _ _ _ _ OK VI).
      destruct OK as (Hw & Hz & Hc & _).
      split.
      + rewrite pc_mem_advance, pc_mem_apply_effect.
        apply (pc_mem_effect_clean (in_wmem (sys_input segs ms x8)));
          [ | exact Hw | exact Hz | exact Hc | exact C ].
        intros x Hx. exact (VdsoClean.wview_none_of_clean segs vlo vhi Hnw (ms_mem ms) x C Hx).
      + exact (pc_vinv_eq model' model'' Ek Ev VI').
    - (* exit: the memory is the pre-call one *)
      pose proof (SCs x8 Hp VI eff model' evs Hs) as OK. cbn [cfg_ms cfg_model] in OK.
      split; [exact C | exact (pc_vinv_out _ _ _ _ OK VI)].
    - (* killed: the same *)
      pose proof (SCs x8 Hp VI eff model' evs Hs) as OK. cbn [cfg_ms cfg_model] in OK.
      split; [exact C | exact (pc_vinv_out _ _ _ _ OK VI)].
  Qed.

  Corollary pc_step_the_scfg {SC : StepCfg} : forall c evs c',
    sstep_cfg segs the_scfg c evs (SNext c') -> pc_step_ok c ->
    vc_cfg vlo vhi c -> vc_cfg vlo vhi c'.
  Proof. intros c evs c'. exact (pc_step the_scfg c evs c'). Qed.

  (** Along a run, for any invariant [P] the steps keep that gives the step premise. *)
  Lemma pc_star : forall cfg (P : config -> Prop),
    (forall d evs d', P d -> sstep_cfg segs cfg d evs (SNext d') -> P d') ->
    (forall d, P d -> pc_step_ok d) ->
    forall c tr c', star_cfg segs cfg c tr c' -> P c -> vc_cfg vlo vhi c ->
    P c' /\ vc_cfg vlo vhi c'.
  Proof.
    intros cfg P HP Hok c0 tr0 c1 Hs.
    induction Hs as [d | d1 evs1 d2 tr1 d3 Hst Hs1 IH]; intros Hp Hv.
    - split; assumption.
    - apply IH; [exact (HP d1 evs1 d2 Hp Hst) | exact (pc_step cfg d1 evs1 d2 Hst (Hok d1 Hp) Hv)].
  Qed.

  (** The step and the run for a call among [pc_proved_nos]: no premise on the outcome. *)
  Theorem pc_step_proved : forall cfg c evs c',
    sstep_cfg segs cfg c evs (SNext c') ->
    (forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> In (bv_unsigned x8) pc_proved_nos) ->
    vc_cfg vlo vhi c -> vc_cfg vlo vhi c'.
  Proof.
    intros cfg c evs c' H Hn VC. apply (pc_step cfg c evs c' H); [|exact VC].
    intros x8 Hp. apply pc_spec_ok_proved. exact (Hn x8 Hp).
  Qed.

  Corollary pc_star_proved : forall cfg (P : config -> Prop),
    (forall d evs d', P d -> sstep_cfg segs cfg d evs (SNext d') -> P d') ->
    (forall d x8, P d -> ms_svc_pending (cfg_ms d) = Some x8 -> In (bv_unsigned x8) pc_proved_nos) ->
    forall c tr c', star_cfg segs cfg c tr c' -> P c -> vc_cfg vlo vhi c -> vc_cfg vlo vhi c'.
  Proof.
    intros cfg P HP Hn c tr c' Hs Hp Hv.
    refine (proj2 (pc_star cfg P HP _ c tr c' Hs Hp Hv)).
    intros d Hd x8 Hx. apply pc_spec_ok_proved. exact (Hn d x8 Hd Hx).
  Qed.

  (** * Every number, by the dispatcher's arms *)

  Definition pc_arm_ok (a : LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.SpecArm) : Prop :=
    forall i mo eff mo' evs, mm_vinv vlo vhi mo ->
      LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.sa_spec a i mo (Ok eff mo' evs) ->
      pc_out_ok i mo eff mo'.

  Lemma pc_lookup_in : forall t n (a : LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.SpecArm),
    LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.lookup_arm t n = Some a -> In a t.
  Proof.
    induction t as [|b r IH]; intros n a H;
      cbn [LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.lookup_arm] in H; [discriminate H|].
    destruct (Z.eqb (LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.sa_no b) n);
      [injection H as <-; left; reflexivity | right; exact (IH n a H)].
  Qed.

  (** One number: the arm the dispatcher picks ([Dispatch.dispatch_arm], Sys/Dispatch.v:71-74). *)
  Lemma pc_spec_ok_of_arm : forall i mo a,
    LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.lookup_arm
      LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable.spec_table
      (bv_unsigned (in_sysno i)) = Some a ->
    pc_arm_ok a -> pc_spec_ok i mo.
  Proof.
    intros i mo a E Ha VI eff mo' evs Hs.
    exact (Ha i mo eff mo' evs VI
             (proj1 (LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.dispatch_arm
                       _ i mo _ a E) Hs)).
  Qed.

  (** Every number: every arm of the table. *)
  Lemma pc_spec_ok_of_table :
    Forall pc_arm_ok LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable.spec_table ->
    forall i mo, pc_spec_ok i mo.
  Proof.
    intros HT i mo.
    destruct (LinuxProcessSemantics.LinuxProcessSem.Sys.Dispatch.lookup_arm
                LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable.spec_table
                (bv_unsigned (in_sysno i))) as [a|] eqn:E.
    - rewrite Forall_forall in HT. exact (pc_spec_ok_of_arm i mo a E (HT a (pc_lookup_in _ _ _ E))).
    - exact (pc_spec_ok_unarmed i mo E).
  Qed.

  Corollary pc_step_of_table : forall cfg c evs c',
    Forall pc_arm_ok LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable.spec_table ->
    sstep_cfg segs cfg c evs (SNext c') ->
    vc_cfg vlo vhi c -> vc_cfg vlo vhi c'.
  Proof.
    intros cfg c evs c' HT H VC. apply (pc_step cfg c evs c' H); [|exact VC].
    intros x8 _. exact (pc_spec_ok_of_table HT _ _).
  Qed.

  Corollary pc_star_of_table : forall cfg c tr c',
    Forall pc_arm_ok LinuxProcessSemantics.LinuxProcessSem.Sys.SyscallTable.spec_table ->
    star_cfg segs cfg c tr c' -> vc_cfg vlo vhi c -> vc_cfg vlo vhi c'.
  Proof.
    intros cfg c tr c' HT Hs Hv.
    refine (proj2 (pc_star cfg (fun _ => True) (fun _ _ _ _ _ => I) _ c tr c' Hs I Hv)).
    intros d _ x8 _. exact (pc_spec_ok_of_table HT _ _).
  Qed.
End PairClean.

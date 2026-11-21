(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput; the launch premises valid_launch and entry_launch_ok_va; the channel-reader premise of writev; the run's segment list run_segments; RomBase.sys_rob at the system-call nodes; the launch's reservations with the vDSO pair; the model's m_kernel field; the conjuncts of valid_input_either). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk DriverCfg ShapeSet RealizesCfg RealizesAbort FxLin FxCore FxSound FxStep FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RomBase RomStable.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require RefStartup RefStartupRz PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvHeap PDrvHeap2 PDrvRead PDir POpen1 PUsage PMain2H.
Import OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupRz OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap OSSVerify.Proofs.fast_float.from_chars.lib.PDrvHeap2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvRead OSSVerify.Proofs.fast_float.from_chars.lib.PDir OSSVerify.Proofs.fast_float.from_chars.lib.POpen1 OSSVerify.Proofs.fast_float.from_chars.lib.PUsage OSSVerify.Proofs.fast_float.from_chars.lib.PMain2H.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PLoopCert PLoopInv PLoop1 PLoop2 PLoop4 PRefused PFile PEof1 PEof3 PTgt3 PTgt9 PDrvHeapI PHeapIGlue Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation munch := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.munch.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SPEC (inp : ProcInput) : TSet := spec (in_argv inp) (in_fs inp).

(* [comment removed for export] *)
Definition NK (T : TSet) : Prop := forall tr sig fs, T tr -> ~ In (KillEv sig fs) tr.
Lemma prefix_in : forall {A} (l1 l2 : list A) x, is_prefix l1 l2 -> In x l1 -> In x l2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 x H Hx; [destruct Hx|].
  destruct l2 as [|b l2]; [destruct H|]. destruct H as [-> H]. destruct Hx as [->|Hx]; [left; reflexivity | right; exact (IH l2 x H Hx)].
Qed.
Lemma nk_emit : forall evs T, (forall sig fs, ~ In (KillEv sig fs) evs) -> NK T -> NK (t_emit evs T).
Proof.
  intros evs T He HT tr sig fs [Hp | (tr' & -> & Htr')] Hin.
  - exact (He sig fs (prefix_in tr evs _ Hp Hin)).
  - apply in_app_iff in Hin as [Hin|Hin]; [exact (He sig fs Hin) | exact (HT tr' sig fs Htr' Hin)].
Qed.
Lemma nk_nil : NK t_nil. Proof. intros tr sig fs -> Hin. destruct Hin. Qed.
Lemma nk_exit : forall c fs, NK (t_exit c fs).
Proof. intros c fs. apply nk_emit; [|exact nk_nil]. intros sig fs' [Hc|[]]. discriminate Hc. Qed.
Lemma nk_alt2 : forall A B, NK A -> NK B -> NK (t_alt2 A B).
Proof. intros A B HA HB tr sig fs [H|H]; [exact (HA tr sig fs H) | exact (HB tr sig fs H)]. Qed.
Lemma nk_W : forall ch s sig fs, ~ In (KillEv sig fs) (W ch s).
Proof. intros ch s sig fs Hin. unfold W in Hin. apply in_map_iff in Hin as (b & Hb & _). discriminate Hb. Qed.
Lemma nk_die : forall msg fs, NK (t_die msg fs).
Proof. intros msg fs. unfold t_die. apply nk_emit; [apply nk_W | apply nk_exit]. Qed.
Lemma nk_body : forall data fs, NK (t_body data fs).
Proof.
  intros data fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data)); [apply nk_die|].
  destruct (length data <? 6)%nat; [apply nk_die|].
  destruct (length data <? 6 + config_len data)%nat; [apply nk_die|].
  apply nk_emit; [apply nk_W | apply nk_exit].
Qed.
Theorem no_kill_SPEC : no_kill SPEC.
Proof.
  intros inp tr sig fs H. unfold SPEC, spec in H.
  destruct (in_argv inp) as [|a0 [|path [|a2 r]]]; try exact (nk_die _ _ tr sig fs H).
  destruct (4096 <=? length path)%nat; [exact (nk_die _ _ tr sig fs H)|].
  destruct (path_eqb path []); [exact (nk_die _ _ tr sig fs H)|].
  destruct (path_is_dirref path); [exact (nk_alt2 _ _ (nk_die _ _) (nk_die _ _) tr sig fs H)|].
  destruct (fs_lookup (in_fs inp) path) as [data|]; [exact (nk_alt2 _ _ (nk_die _ _) (nk_body _ _) tr sig fs H) | exact (nk_die _ _ tr sig fs H)].
Qed.

Section Top.
(* [comment removed for export] *)
Variable STATIC : list ivl.
Hypothesis HSTATX : forall x, ~ ioutside EXGX x -> ioutside STATIC x.
Hypothesis HSTATI : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC x.
Hypothesis HSTATR : forall x, RSX x -> ioutside STATIC x.
Hypothesis HSRO : forall x, 0x10000 <= x < 0x22000 \/ 0x64de0 <= x < 0x64de4 -> ~ KRO x -> ioutside STATIC x.
(* [comment removed for export] *)
Variable HIF : Z -> heap_iface.
Definition HTR (HTOP : Z) : Prop := 2 ^ 20 <= HTOP < 2 ^ 47.
Hypothesis HOK : forall HTOP, HTR HTOP ->
  heap_ok PSEGS DCFG (HIF HTOP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) 0x10000 0x97000 HTOP STATIC CELLS_NE 0x51310 8192 0x511d0 8192.
Hypothesis HERR : forall HTOP hs m m' md, hi_Heap (HIF HTOP) hs m md -> munch ERRC m m' -> mem_grows m m' -> hi_Heap (HIF HTOP) hs m' md.
Hypothesis HCELL : forall HTOP hs m m' md, hi_Heap (HIF HTOP) hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> hi_Heap (HIF HTOP) hs m' md.
Hypothesis HNL : forall HTOP hs m md, hi_Heap (HIF HTOP) hs m md -> NL m.
Hypothesis HMV : forall HTOP hs m md md', hi_Heap (HIF HTOP) hs m md -> m_vmmaps md' = m_vmmaps md -> m_kernel md' = m_kernel md -> m_halted md' = None -> m_vm_lazy md' = [] ->
  hi_Heap (HIF HTOP) hs m md'.
Hypothesis HKRO : forall HTOP hs m md, hi_Heap (HIF HTOP) hs m md -> pristine m 0x16100 0x16120 /\ pristine m 0x182a8 0x18327.
(* [comment removed for export] *)
Variable HeapIF : forall HTOP, hi_HS (HIF HTOP) -> (word -> option byte) -> Model -> Prop.
Variable INITF : forall HTOP, hi_HS (HIF HTOP) -> list ivl.
Hypothesis HOKI : forall HTOP, HTR HTOP ->
  heap_init_ok PSEGS DCFG (HIF HTOP) (HeapIF HTOP) (INITF HTOP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0) HTOP CELLS_NE 0x51310 8192.
Hypothesis HOWNI : forall HTOP hs m md, HeapIF HTOP hs m md -> forall x, ~ ioutside (hi_owned (HIF HTOP) hs) x ->
  0 <= x < HTOP /\ (~ ioutside STATIC x \/ x < 0x10000 \/ 0x97000 <= x).
Hypothesis HERRI : forall HTOP hs m m' md, HeapIF HTOP hs m md -> munch ERRC m m' -> mem_grows m m' -> HeapIF HTOP hs m' md.
Hypothesis HCELLI : forall HTOP hs m m' md, HeapIF HTOP hs m md -> munch CELLS_NE m m' -> mem_grows m m' ->
  (forall a, 0x63da0 <= a < 0x63da8 \/ 0x95e40 <= a < 0x95e48 -> mrd PSEGS m' (Z_to_bv 64 a) = mrd PSEGS m (Z_to_bv 64 a)) -> HeapIF HTOP hs m' md.
Hypothesis HMVI : forall HTOP hs m md md', HeapIF HTOP hs m md -> m_vmmaps md' = m_vmmaps md -> m_kernel md' = m_kernel md -> m_halted md' = None -> m_vm_lazy md' = [] ->
  HeapIF HTOP hs m md'.
(* LPS 08b1429: the heap-init hypothesis is stated over the launch ([inp], [mbase],
   [entry], [brk], with [Hvl]/[Hlau]) that [main_entry] now names, exactly as
   PHeapInst's [heapI_main] discharges it. *)
Hypothesis HINIT : forall inp mbase entry sp0 brk tid rdraw regs mem lim,
  valid_sp sp0 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp ->
  entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
  valid_brk PSEGS brk -> valid_mmap_base mbase -> 2 ^ 31 <= lim ->
  main_entry inp mbase entry sp0 rdraw tid regs mem ->
  exists hs, HeapIF (bv_unsigned sp0 - stack_max_size) hs mem (with_tid tid (init_model (segments_reserved PSEGS) brk mbase sp0 lim inp)) /\
    INITO inp sp0 rdraw (HIF (bv_unsigned sp0 - stack_max_size)) (INITF (bv_unsigned sp0 - stack_max_size)) hs.
(* [comment removed for export] *)
Hypothesis HFZ : forall HTOP, HTR HTOP ->
  fuzz_contract PSEGS DCFG (hi_HS (HIF HTOP)) (hi_Heap (HIF HTOP)) (hi_blocks (HIF HTOP)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x75bd0)
    0x10000 0x97000 HTOP STATIC CELLS_NE 0x22b18 8496 PRO.

#[using="Type"] Lemma HIMGc : 0x10000 <= 0x10000 /\ 0x97000 <= 0x97000. Proof. LiaFast.lf_pins LiaFast.u0. lia. Qed.

(* [comment removed for export] *)
#[using="STATIC HSTATX HSTATI HSTATR HSRO HOK HERR HCELL HNL HMV HKRO HOKI HOWNI HERRI HCELLI HMVI HFZ"] Theorem plain_main : forall HTOP inp mbase entry sp0 brk tid rdraw regs mem model hs,
  HTR HTOP -> HTOP <= bv_unsigned sp0 - 65536 ->
  valid_sp sp0 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp ->
  entry_stack_fits sp0 (in_argv inp) (in_envp inp) -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry inp mbase entry sp0 rdraw tid regs mem ->
  m_halted model = None -> m_vm_lazy model = [] -> m_fds model = FDS0 -> m_channel_reader model = true -> U model <= UB0 -> HeapIF HTOP hs mem model ->
  INITO inp sp0 rdraw (HIF HTOP) (INITF HTOP) hs ->
  realizes PSEGS (mkCfg (mkst (fx := fx0) regs (Z_to_bv 64 0x22638) mem (seg_rom PSEGS)) model) (spec (in_argv inp) (m_fs model)).
Proof. LiaFast.lf_pins (fun (STATIC HSTATX HSTATI HSTATR HSRO HOK HERR HCELL HNL HMV HKRO HOKI HOWNI HERRI HCELLI HMVI HFZ : LiaFast.U) => LiaFast.u0).
  intros HTOP inp mbase entry sp0 brk tid rdraw regs mem model hs HR HTOPB Hsp Hva Hve Hvl Hlau Hfits Htid ME Hh Hl Hfds Hrdr HU0 HINIT0 HIO.
  set (HI := HIF HTOP) in *.
  pose proof (HOK HTOP HR) as HOK'. pose proof (HERR HTOP) as HERR'. pose proof (HCELL HTOP) as HCELL'. pose proof (HNL HTOP) as HNL'.
  pose proof (HMV HTOP) as HMV'. pose proof (HKRO HTOP) as HKRO'. pose proof (HFZ HTOP HR) as HFZ'.
  pose proof (HOKI HTOP HR) as HOKI'. pose proof (HOWNI HTOP) as HOWNI'. pose proof (HERRI HTOP) as HERRI'. pose proof (HCELLI HTOP) as HCELLI'.
  pose proof (HMVI HTOP) as HMVI'.
  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hargc2|Hargc].
  - apply (main_argc2H inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Hfits Htid ME Hargc2 model Hh Hl Hfds Hrdr 0x10000 0x97000 HTOP STATIC
             HTOPB HIMGc HSTATX HI HOK' HNL' HSTATI (HeapIF HTOP) (INITF HTOP) HOKI' HOWNI' HERRI' HCELLI' HMVI' hs HINIT0 HIO HU0).
    intros data Hdir Hlk E2 ms2 Ha2 Hd2 Hrom2 Hmf2 Hh2.
    apply (file_path inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc2 0x10000 0x97000 HTOP STATIC HTOPB HIMGc HSTATX HI
             HOK' HERR' HCELL' HNL' HSTATI HMV' HSTATR (HeapIF HTOP) (INITF HTOP) HOKI' HOWNI' HERRI' HCELLI' data (m_fs model) Hlk model E2 ms2 hs Hh Hl eq_refl Hrdr HU0 Ha2 Hd2 Hrom2 Hmf2 Hh2 HIO).
    intros E3 ms3 md3 hs3 len3 cap3 buf3 HC3.
    apply (eof_entry inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc2 0x10000 0x97000 HTOP STATIC HTOPB HIMGc HSTATX HI
             HOK' HERR' HCELL' HNL' HSTATI HMV' data (m_fs model) E3 ms3 md3 hs3 len3 cap3 buf3 HC3).
    intros E4 ms4 md4 HD4.
    apply (header_entry inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc2 0x10000 0x97000 HTOP STATIC HTOPB HIMGc HSTATX HI
             HOK' HERR' HCELL' HNL' HSTATI data (m_fs model) E4 ms4 md4 hs3 len3 cap3 buf3 HD4).
    intros E5 ms5 HT5.
    exact (target_phase inp mbase entry sp0 brk tid rdraw regs mem Hsp Hva Hve Hvl Hlau Htid ME Hargc2 0x10000 0x97000 HTOP STATIC HTOPB HIMGc HSTATX HI
             HOK' HERR' HCELL' HNL' HSTATI data (m_fs model) HFZ' HSRO HKRO' E5 ms5 md4 hs3 len3 cap3 buf3 HT5).
  - assert (Hsp' : spec (in_argv inp) (m_fs model) = t_die (msg_usage (nth 0 (in_argv inp) [])) (m_fs model)).
    { unfold spec. destruct (in_argv inp) as [|a0 [|a1 [|a2 r]]]; cbn in Hargc |- *; try reflexivity. exfalso. exact (Hargc eq_refl). }
    rewrite Hsp'.
    apply (usage_path inp mbase entry sp0 brk tid rdraw regs mem model Hsp Hva Hve Hvl Hlau Hfits Htid ME Hargc Hh Hl).
    rewrite Hfds. vm_compute. reflexivity.
    exact Hrdr.
Qed.

(* [comment removed for export] *)
#[using="STATIC HSTATX HSTATI HSTATR HSRO HIF HOK HERR HCELL HNL HMV HKRO HeapIF INITF HOKI HOWNI HERRI HCELLI HMVI HINIT HFZ"] Theorem plain_realizes_lim : forall lim, 2 ^ 31 <= lim ->
  image_realizes_cfg_e DCFG PSEGS Plain.M.init_pc
  Plain.M.phdrs lim SPEC.
Proof. LiaFast.lf_pins (fun (STATIC HSTATX HSTATI HSTATR HSRO HIF HOK HERR HCELL HNL HMV HKRO HeapIF INITF HOKI HOWNI HERRI HCELLI HMVI HINIT HFZ : LiaFast.U) => LiaFast.u0).
  intros lim Hlim sp brk0 mb rnd inp Hven Hinp.
  (* LPS 727298f3: [image_realizes_cfg_e] gives [valid_input_either], which has no named
     accessors.  Its conjuncts are taken by type (a destruct to full depth, then
     [assumption]), so an inserted conjunct does not move them. *)
  assert (Hrdi : in_channel_reader inp = true)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hva : valid_argv (in_argv inp))
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hvenv : valid_envp (in_envp inp))
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hvl : valid_launch inp)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  assert (Hsv : in_va_size inp = Sv48)
    by (clear - Hinp; red in Hinp; repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption).
  apply (valid_entry_sv48 _ _ _ Hsv) in Hven. destruct Hven as (Hsp & Hbrk & Hmb & Hfits & Hlau).
  apply (ref_startup_rz DCFG (SPEC inp) sp brk0 mb rnd lim inp Hsp Hva Hvenv Hvl Hlau).
  intros tid regs mem Htid ME.
  (* LPS 08b1429: the start-up walk is over the run's segment list [run_segments PSEGS inp sp mb];
     [plain_main] is a walk over the binary's own segments and backing, lifted at the entry of
     [main] ([RomStable.realizes_cfg_lift_run]).  The model there is the binary's start model
     ([RomStable.init_model_run_segments]). *)
  rewrite RomStable.init_model_run_segments.
  set (md := with_tid tid (cfg_model (init_config PSEGS Plain.M.init_pc Plain.M.phdrs sp brk0 mb rnd lim inp))).
  lazymatch goal with
  | |- realizes_cfg _ _ (mkCfg (@mkst ?fx ?r ?p ?m _) _) ?T =>
      change (realizes_cfg (run_segments PSEGS inp sp mb) DCFG
                (mkCfg (RomBase.wrom (@mkst fx r p m (seg_rom PSEGS)) (RomStable.seg_rom1 (run_segments PSEGS inp sp mb))) md) T)
  end.
  apply RomStable.realizes_cfg_lift_run; [reflexivity | reflexivity |].
  destruct (HINIT inp mb (0x224ec : word) sp brk0 tid rnd regs mem lim Hsp Hva Hvenv Hvl Hlau Hfits Hbrk Hmb Hlim ME) as (hs & Hh0 & HIO).
  set (md0 := with_tid tid (init_model (segments_reserved PSEGS) brk0 mb sp lim inp)) in *.
  (* [HINIT] names the model without the vDSO run state; [HMVI] moves the heap invariant to
     [md], which differs from it only there *)
  assert (Hh : HeapIF (bv_unsigned sp - stack_max_size) hs mem md).
  { apply (HMVI _ hs mem md0 md Hh0); [reflexivity | reflexivity | | reflexivity].
    change (m_halted md) with (m_halted md0). unfold md0. rewrite m_halted_with_tid, m_halted_init_model. reflexivity. }
  assert (Hfs : m_fs md = in_fs inp)
    by (change (m_fs md) with (m_fs md0); unfold md0; rewrite m_fs_with_tid, m_fs_init_model; reflexivity).
  unfold SPEC. rewrite <- Hfs.
  replace (0x22638%bv : word) with (Z_to_bv 64 0x22638) by (apply bv_eq; reflexivity).
  pose proof (sp0_lo sp Hsp) as SL. pose proof (sp0_hi sp Hsp) as SH.
  apply (plain_main (bv_unsigned sp - stack_max_size) inp mb (0x224ec : word) sp brk0 tid rnd regs mem md hs
           ltac:(unfold HTR, stack_max_size; lia) ltac:(unfold stack_max_size; lia) Hsp Hva Hvenv Hvl Hlau Hfits
           ltac:(unfold PID_MAX_ENVELOPE in Htid; lia) ME).
  - change (m_halted md) with (m_halted md0). unfold md0. rewrite m_halted_with_tid, m_halted_init_model. reflexivity.
  - reflexivity.
  - change (m_fds md) with (m_fds md0). unfold md0. rewrite m_fds_with_tid, m_fds_init_model. reflexivity.
  - transitivity (in_channel_reader inp); [reflexivity | exact Hrdi].
  - unfold U. change (vm_backing_used md) with (vm_backing_used (init_model (segments_reserved PSEGS) brk0 mb sp lim inp)).
    rewrite vm_backing_used_init_model. change (m_vmmaps md) with (mkVmMapsFull (init_reserved (segments_reserved PSEGS) mb sp (in_kernel inp)) [] [] brk0 brk0 lim mb sp).
    cbn [vm_reserved vm_maps]. rewrite app_nil_r. unfold init_reserved. rewrite length_app.
    (* LPS 727298f3: the ledger ends with the vDSO pair, whose place is symbolic here; it has at
       most two entries, and the segments' part is computed alone (no [vm_compute] over the
       symbolic launch) *)
    set (V := vdso_reserved _ _).
    assert (Hv2 : (length V <= 2)%nat) by (unfold V, vdso_reserved; cbv zeta; destruct (_ <? _)%Z; cbn [length]; lia).
    assert (Hs : (4096 * Z.of_nat (length (segments_reserved PSEGS)) + 8192 <= UB0)%Z) by (apply Z.leb_le; vm_compute; reflexivity).
    clearbody V. lia.
  - exact Hh.
  - exact HIO.
Qed.

(* [comment removed for export] *)
#[using="STATIC HSTATX HSTATI HSTATR HSRO HIF HOK HERR HCELL HNL HMV HKRO HeapIF INITF HOKI HOWNI HERRI HCELLI HMVI HINIT HFZ"] Theorem plain_realizes : image_realizes_cfg_e DCFG PSEGS Plain.M.init_pc
  Plain.M.phdrs source_alloc_limit SPEC.
Proof. LiaFast.lf_pins (fun (STATIC HSTATX HSTATI HSTATR HSRO HIF HOK HERR HCELL HNL HMV HKRO HeapIF INITF HOKI HOWNI HERRI HCELLI HMVI HINIT HFZ : LiaFast.U) => LiaFast.u0). apply plain_realizes_lim. unfold source_alloc_limit. lia. Qed.

End Top.

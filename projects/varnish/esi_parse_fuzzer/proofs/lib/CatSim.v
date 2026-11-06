(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SimInv.

Module ExitSim.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import SimInv.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietlt6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietlt6.dlia_stock.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok : forall i m,
  is_exit_no (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
  intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
  is_exit_no (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence.
Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

(* [comment removed for export] *)
Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* [comment removed for export] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *) congruence.
Qed.

(* [comment removed for export] *)
Lemma sstep_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (Heff & Hm & Hevs);
      rewrite in_arg0_sys_input in Hm;
      subst evs0 model';
      assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        by (autorewrite with model in H6; congruence);
      subst code
    end.
    cbn. split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
      H2 : ms_svc_pending ms = Some ?x |- _ =>
      eapply exit_dispatch_no_unmodeled; [| exact H3];
      rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
    end.
Qed.

(* [comment removed for export] *)
Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. destruct c as [ms model]. cbn in Hh.
    inversion Hss; subst; cbn in Hh; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition overlay_argc_bytes (sp : word) (argc : nat)
    (base_mem : word -> option byte) : word -> option byte :=
  let bytes := word_le8 (nat_to_word argc) in
  fun addr =>
    if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
    else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
    else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
    else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
    else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
    else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
    else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
    else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
    else base_mem addr.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
    (init_sp : word) (init_rnd : EntryDraw) (argc : nat)
    (base : word -> option byte) (uid : word)
    (hw : word) : machine_state :=
  {| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fregs := ms_fregs (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw); ms_fcsr := ms_fcsr (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw);
     ms_mem        := overlay_argc_bytes init_sp argc base;
     ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp init_rnd nil nil uid hw) |}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End ExitSim.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim.

Module DU_cg5g.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2b03c : bv 32 := 0x0036f793.
Lemma F_2b03c : fetch_word Ubsan.M.loaded_segments (0x2b03c : word) = Some W_2b03c.
Proof. vm_refl. Qed.
Lemma D_2b03c : decode_any W_2b03c = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b040 : bv 32 := 0x0c078a63.
Lemma F_2b040 : fetch_word Ubsan.M.loaded_segments (0x2b040 : word) = Some W_2b040.
Proof. vm_refl. Qed.
Lemma D_2b040 : decode_any W_2b040 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b044 : bv 32 := 0x02000713.
Lemma F_2b044 : fetch_word Ubsan.M.loaded_segments (0x2b044 : word) = Some W_2b044.
Proof. vm_refl. Qed.
Lemma D_2b044 : decode_any W_2b044 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b048 : bv 32 := 0x02e67063.
Lemma F_2b048 : fetch_word Ubsan.M.loaded_segments (0x2b048 : word) = Some W_2b048.
Proof. vm_refl. Qed.
Lemma D_2b048 : decode_any W_2b048 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b04c : bv 32 := 0x01000713.
Lemma F_2b04c : fetch_word Ubsan.M.loaded_segments (0x2b04c : word) = Some W_2b04c.
Proof. vm_refl. Qed.
Lemma D_2b04c : decode_any W_2b04c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b050 : bv 32 := 0x24e67863.
Lemma F_2b050 : fetch_word Ubsan.M.loaded_segments (0x2b050 : word) = Some W_2b050.
Proof. vm_refl. Qed.
Lemma D_2b050 : decode_any W_2b050 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b054 : bv 32 := 0x00867713.
Lemma F_2b054 : fetch_word Ubsan.M.loaded_segments (0x2b054 : word) = Some W_2b054.
Proof. vm_refl. Qed.
Lemma D_2b054 : decode_any W_2b054 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b058 : bv 32 := 0x2c071e63.
Lemma F_2b058 : fetch_word Ubsan.M.loaded_segments (0x2b058 : word) = Some W_2b058.
Proof. vm_refl. Qed.
Lemma D_2b058 : decode_any W_2b058 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b05c : bv 32 := 0x00467713.
Lemma F_2b05c : fetch_word Ubsan.M.loaded_segments (0x2b05c : word) = Some W_2b05c.
Proof. vm_refl. Qed.
Lemma D_2b05c : decode_any W_2b05c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b060 : bv 32 := 0x32071463.
Lemma F_2b060 : fetch_word Ubsan.M.loaded_segments (0x2b060 : word) = Some W_2b060.
Proof. vm_refl. Qed.
Lemma D_2b060 : decode_any W_2b060 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b064 : bv 32 := 0x3500006f.
Lemma F_2b064 : fetch_word Ubsan.M.loaded_segments (0x2b064 : word) = Some W_2b064.
Proof. vm_refl. Qed.
Lemma D_2b064 : decode_any W_2b064 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b068 : bv 32 := 0x0005a703.
Lemma F_2b068 : fetch_word Ubsan.M.loaded_segments (0x2b068 : word) = Some W_2b068.
Proof. vm_refl. Qed.
Lemma D_2b068 : decode_any W_2b068 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b06c : bv 32 := 0x00300813.
Lemma F_2b06c : fetch_word Ubsan.M.loaded_segments (0x2b06c : word) = Some W_2b06c.
Proof. vm_refl. Qed.
Lemma D_2b06c : decode_any W_2b06c = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b070 : bv 32 := 0x11078e63.
Lemma F_2b070 : fetch_word Ubsan.M.loaded_segments (0x2b070 : word) = Some W_2b070.
Proof. vm_refl. Qed.
Lemma D_2b070 : decode_any W_2b070 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b074 : bv 32 := 0x00200813.
Lemma F_2b074 : fetch_word Ubsan.M.loaded_segments (0x2b074 : word) = Some W_2b074.
Proof. vm_refl. Qed.
Lemma D_2b074 : decode_any W_2b074 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b078 : bv 32 := 0x19079c63.
Lemma F_2b078 : fetch_word Ubsan.M.loaded_segments (0x2b078 : word) = Some W_2b078.
Proof. vm_refl. Qed.
Lemma D_2b078 : decode_any W_2b078 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b07c : bv 32 := 0x00875793.
Lemma F_2b07c : fetch_word Ubsan.M.loaded_segments (0x2b07c : word) = Some W_2b07c.
Proof. vm_refl. Qed.
Lemma D_2b07c : decode_any W_2b07c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b080 : bv 32 := 0xffe60613.
Lemma F_2b080 : fetch_word Ubsan.M.loaded_segments (0x2b080 : word) = Some W_2b080.
Proof. vm_refl. Qed.
Lemma D_2b080 : decode_any W_2b080 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b084 : bv 32 := 0x00e68023.
Lemma F_2b084 : fetch_word Ubsan.M.loaded_segments (0x2b084 : word) = Some W_2b084.
Proof. vm_refl. Qed.
Lemma D_2b084 : decode_any W_2b084 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b088 : bv 32 := 0x00f680a3.
Lemma F_2b088 : fetch_word Ubsan.M.loaded_segments (0x2b088 : word) = Some W_2b088.
Proof. vm_refl. Qed.
Lemma D_2b088 : decode_any W_2b088 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b08c : bv 32 := 0x00268693.
Lemma F_2b08c : fetch_word Ubsan.M.loaded_segments (0x2b08c : word) = Some W_2b08c.
Proof. vm_refl. Qed.
Lemma D_2b08c : decode_any W_2b08c = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b090 : bv 32 := 0x01058593.
Lemma F_2b090 : fetch_word Ubsan.M.loaded_segments (0x2b090 : word) = Some W_2b090.
Proof. vm_refl. Qed.
Lemma D_2b090 : decode_any W_2b090 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b094 : bv 32 := 0x01100793.
Lemma F_2b094 : fetch_word Ubsan.M.loaded_segments (0x2b094 : word) = Some W_2b094.
Proof. vm_refl. Qed.
Lemma D_2b094 : decode_any W_2b094 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b098 : bv 32 := 0x0107581b.
Lemma F_2b098 : fetch_word Ubsan.M.loaded_segments (0x2b098 : word) = Some W_2b098.
Proof. vm_refl. Qed.
Lemma D_2b098 : decode_any W_2b098 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b09c : bv 32 := 0xff45a883.
Lemma F_2b09c : fetch_word Ubsan.M.loaded_segments (0x2b09c : word) = Some W_2b09c.
Proof. vm_refl. Qed.
Lemma D_2b09c : decode_any W_2b09c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0a0 : bv 32 := 0xff85a283.
Lemma F_2b0a0 : fetch_word Ubsan.M.loaded_segments (0x2b0a0 : word) = Some W_2b0a0.
Proof. vm_refl. Qed.
Lemma D_2b0a0 : decode_any W_2b0a0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0a4 : bv 32 := 0xffc5a303.
Lemma F_2b0a4 : fetch_word Ubsan.M.loaded_segments (0x2b0a4 : word) = Some W_2b0a4.
Proof. vm_refl. Qed.
Lemma D_2b0a4 : decode_any W_2b0a4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0a8 : bv 32 := 0x0005a703.
Lemma F_2b0a8 : fetch_word Ubsan.M.loaded_segments (0x2b0a8 : word) = Some W_2b0a8.
Proof. vm_refl. Qed.
Lemma D_2b0a8 : decode_any W_2b0a8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0ac : bv 32 := 0x01089393.
Lemma F_2b0ac : fetch_word Ubsan.M.loaded_segments (0x2b0ac : word) = Some W_2b0ac.
Proof. vm_refl. Qed.
Lemma D_2b0ac : decode_any W_2b0ac = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0b0 : bv 32 := 0x0108d89b.
Lemma F_2b0b0 : fetch_word Ubsan.M.loaded_segments (0x2b0b0 : word) = Some W_2b0b0.
Proof. vm_refl. Qed.
Lemma D_2b0b0 : decode_any W_2b0b0 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0b4 : bv 32 := 0x0103e833.
Lemma F_2b0b4 : fetch_word Ubsan.M.loaded_segments (0x2b0b4 : word) = Some W_2b0b4.
Proof. vm_refl. Qed.
Lemma D_2b0b4 : decode_any W_2b0b4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0b8 : bv 32 := 0x01029393.
Lemma F_2b0b8 : fetch_word Ubsan.M.loaded_segments (0x2b0b8 : word) = Some W_2b0b8.
Proof. vm_refl. Qed.
Lemma D_2b0b8 : decode_any W_2b0b8 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0bc : bv 32 := 0x0102d29b.
Lemma F_2b0bc : fetch_word Ubsan.M.loaded_segments (0x2b0bc : word) = Some W_2b0bc.
Proof. vm_refl. Qed.
Lemma D_2b0bc : decode_any W_2b0bc = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0c0 : bv 32 := 0x0113e8b3.
Lemma F_2b0c0 : fetch_word Ubsan.M.loaded_segments (0x2b0c0 : word) = Some W_2b0c0.
Proof. vm_refl. Qed.
Lemma D_2b0c0 : decode_any W_2b0c0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0c4 : bv 32 := 0x01031393.
Lemma F_2b0c4 : fetch_word Ubsan.M.loaded_segments (0x2b0c4 : word) = Some W_2b0c4.
Proof. vm_refl. Qed.
Lemma D_2b0c4 : decode_any W_2b0c4 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0c8 : bv 32 := 0x0103531b.
Lemma F_2b0c8 : fetch_word Ubsan.M.loaded_segments (0x2b0c8 : word) = Some W_2b0c8.
Proof. vm_refl. Qed.
Lemma D_2b0c8 : decode_any W_2b0c8 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0cc : bv 32 := 0x0053e2b3.
Lemma F_2b0cc : fetch_word Ubsan.M.loaded_segments (0x2b0cc : word) = Some W_2b0cc.
Proof. vm_refl. Qed.
Lemma D_2b0cc : decode_any W_2b0cc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0d0 : bv 32 := 0x01071393.
Lemma F_2b0d0 : fetch_word Ubsan.M.loaded_segments (0x2b0d0 : word) = Some W_2b0d0.
Proof. vm_refl. Qed.
Lemma D_2b0d0 : decode_any W_2b0d0 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0d4 : bv 32 := 0x0063e333.
Lemma F_2b0d4 : fetch_word Ubsan.M.loaded_segments (0x2b0d4 : word) = Some W_2b0d4.
Proof. vm_refl. Qed.
Lemma D_2b0d4 : decode_any W_2b0d4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0d8 : bv 32 := 0xff060613.
Lemma F_2b0d8 : fetch_word Ubsan.M.loaded_segments (0x2b0d8 : word) = Some W_2b0d8.
Proof. vm_refl. Qed.
Lemma D_2b0d8 : decode_any W_2b0d8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0dc : bv 32 := 0x0106a023.
Lemma F_2b0dc : fetch_word Ubsan.M.loaded_segments (0x2b0dc : word) = Some W_2b0dc.
Proof. vm_refl. Qed.
Lemma D_2b0dc : decode_any W_2b0dc = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0e0 : bv 32 := 0x0116a223.
Lemma F_2b0e0 : fetch_word Ubsan.M.loaded_segments (0x2b0e0 : word) = Some W_2b0e0.
Proof. vm_refl. Qed.
Lemma D_2b0e0 : decode_any W_2b0e0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0e4 : bv 32 := 0x0056a423.
Lemma F_2b0e4 : fetch_word Ubsan.M.loaded_segments (0x2b0e4 : word) = Some W_2b0e4.
Proof. vm_refl. Qed.
Lemma D_2b0e4 : decode_any W_2b0e4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0e8 : bv 32 := 0x0066a623.
Lemma F_2b0e8 : fetch_word Ubsan.M.loaded_segments (0x2b0e8 : word) = Some W_2b0e8.
Proof. vm_refl. Qed.
Lemma D_2b0e8 : decode_any W_2b0e8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0ec : bv 32 := 0x01068693.
Lemma F_2b0ec : fetch_word Ubsan.M.loaded_segments (0x2b0ec : word) = Some W_2b0ec.
Proof. vm_refl. Qed.
Lemma D_2b0ec : decode_any W_2b0ec = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0f0 : bv 32 := 0x01058593.
Lemma F_2b0f0 : fetch_word Ubsan.M.loaded_segments (0x2b0f0 : word) = Some W_2b0f0.
Proof. vm_refl. Qed.
Lemma D_2b0f0 : decode_any W_2b0f0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0f4 : bv 32 := 0xfac7e2e3.
Lemma F_2b0f4 : fetch_word Ubsan.M.loaded_segments (0x2b0f4 : word) = Some W_2b0f4.
Proof. vm_refl. Qed.
Lemma D_2b0f4 : decode_any W_2b0f4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0f8 : bv 32 := 0xff258593.
Lemma F_2b0f8 : fetch_word Ubsan.M.loaded_segments (0x2b0f8 : word) = Some W_2b0f8.
Proof. vm_refl. Qed.
Lemma D_2b0f8 : decode_any W_2b0f8 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0fc : bv 32 := 0x01000713.
Lemma F_2b0fc : fetch_word Ubsan.M.loaded_segments (0x2b0fc : word) = Some W_2b0fc.
Proof. vm_refl. Qed.
Lemma D_2b0fc : decode_any W_2b0fc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b100 : bv 32 := 0xf4e66ae3.
Lemma F_2b100 : fetch_word Ubsan.M.loaded_segments (0x2b100 : word) = Some W_2b100.
Proof. vm_refl. Qed.
Lemma D_2b100 : decode_any W_2b100 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b104 : bv 32 := 0x19c0006f.
Lemma F_2b104 : fetch_word Ubsan.M.loaded_segments (0x2b104 : word) = Some W_2b104.
Proof. vm_refl. Qed.
Lemma D_2b104 : decode_any W_2b104 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b108 : bv 32 := 0x00050693.
Lemma F_2b108 : fetch_word Ubsan.M.loaded_segments (0x2b108 : word) = Some W_2b108.
Proof. vm_refl. Qed.
Lemma D_2b108 : decode_any W_2b108 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b10c : bv 32 := 0x00357793.
Lemma F_2b10c : fetch_word Ubsan.M.loaded_segments (0x2b10c : word) = Some W_2b10c.
Proof. vm_refl. Qed.
Lemma D_2b10c : decode_any W_2b10c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b110 : bv 32 := 0xf2079ae3.
Lemma F_2b110 : fetch_word Ubsan.M.loaded_segments (0x2b110 : word) = Some W_2b110.
Proof. vm_refl. Qed.
Lemma D_2b110 : decode_any W_2b110 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b114 : bv 32 := 0x01000713.
Lemma F_2b114 : fetch_word Ubsan.M.loaded_segments (0x2b114 : word) = Some W_2b114.
Proof. vm_refl. Qed.
Lemma D_2b114 : decode_any W_2b114 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b118 : bv 32 := 0x02e66c63.
Lemma F_2b118 : fetch_word Ubsan.M.loaded_segments (0x2b118 : word) = Some W_2b118.
Proof. vm_refl. Qed.
Lemma D_2b118 : decode_any W_2b118 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b11c : bv 32 := 0x00f00713.
Lemma F_2b11c : fetch_word Ubsan.M.loaded_segments (0x2b11c : word) = Some W_2b11c.
Proof. vm_refl. Qed.
Lemma D_2b11c : decode_any W_2b11c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b120 : bv 32 := 0x0005a783.
Lemma F_2b120 : fetch_word Ubsan.M.loaded_segments (0x2b120 : word) = Some W_2b120.
Proof. vm_refl. Qed.
Lemma D_2b120 : decode_any W_2b120 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b124 : bv 32 := 0x0045a803.
Lemma F_2b124 : fetch_word Ubsan.M.loaded_segments (0x2b124 : word) = Some W_2b124.
Proof. vm_refl. Qed.
Lemma D_2b124 : decode_any W_2b124 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b128 : bv 32 := 0x0085a883.
Lemma F_2b128 : fetch_word Ubsan.M.loaded_segments (0x2b128 : word) = Some W_2b128.
Proof. vm_refl. Qed.
Lemma D_2b128 : decode_any W_2b128 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b12c : bv 32 := 0x00c5a283.
Lemma F_2b12c : fetch_word Ubsan.M.loaded_segments (0x2b12c : word) = Some W_2b12c.
Proof. vm_refl. Qed.
Lemma D_2b12c : decode_any W_2b12c = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b130 : bv 32 := 0x01058593.
Lemma F_2b130 : fetch_word Ubsan.M.loaded_segments (0x2b130 : word) = Some W_2b130.
Proof. vm_refl. Qed.
Lemma D_2b130 : decode_any W_2b130 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b134 : bv 32 := 0xff060613.
Lemma F_2b134 : fetch_word Ubsan.M.loaded_segments (0x2b134 : word) = Some W_2b134.
Proof. vm_refl. Qed.
Lemma D_2b134 : decode_any W_2b134 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b138 : bv 32 := 0x00f6a023.
Lemma F_2b138 : fetch_word Ubsan.M.loaded_segments (0x2b138 : word) = Some W_2b138.
Proof. vm_refl. Qed.
Lemma D_2b138 : decode_any W_2b138 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b13c : bv 32 := 0x0106a223.
Lemma F_2b13c : fetch_word Ubsan.M.loaded_segments (0x2b13c : word) = Some W_2b13c.
Proof. vm_refl. Qed.
Lemma D_2b13c : decode_any W_2b13c = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b140 : bv 32 := 0x0116a423.
Lemma F_2b140 : fetch_word Ubsan.M.loaded_segments (0x2b140 : word) = Some W_2b140.
Proof. vm_refl. Qed.
Lemma D_2b140 : decode_any W_2b140 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b144 : bv 32 := 0x0056a623.
Lemma F_2b144 : fetch_word Ubsan.M.loaded_segments (0x2b144 : word) = Some W_2b144.
Proof. vm_refl. Qed.
Lemma D_2b144 : decode_any W_2b144 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b148 : bv 32 := 0x01068693.
Lemma F_2b148 : fetch_word Ubsan.M.loaded_segments (0x2b148 : word) = Some W_2b148.
Proof. vm_refl. Qed.
Lemma D_2b148 : decode_any W_2b148 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b14c : bv 32 := 0xfcc76ae3.
Lemma F_2b14c : fetch_word Ubsan.M.loaded_segments (0x2b14c : word) = Some W_2b14c.
Proof. vm_refl. Qed.
Lemma D_2b14c : decode_any W_2b14c = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b150 : bv 32 := 0x00800713.
Lemma F_2b150 : fetch_word Ubsan.M.loaded_segments (0x2b150 : word) = Some W_2b150.
Proof. vm_refl. Qed.
Lemma D_2b150 : decode_any W_2b150 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b154 : bv 32 := 0x00e66e63.
Lemma F_2b154 : fetch_word Ubsan.M.loaded_segments (0x2b154 : word) = Some W_2b154.
Proof. vm_refl. Qed.
Lemma D_2b154 : decode_any W_2b154 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b158 : bv 32 := 0x0005a703.
Lemma F_2b158 : fetch_word Ubsan.M.loaded_segments (0x2b158 : word) = Some W_2b158.
Proof. vm_refl. Qed.
Lemma D_2b158 : decode_any W_2b158 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b15c : bv 32 := 0x0045a783.
Lemma F_2b15c : fetch_word Ubsan.M.loaded_segments (0x2b15c : word) = Some W_2b15c.
Proof. vm_refl. Qed.
Lemma D_2b15c : decode_any W_2b15c = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b160 : bv 32 := 0x00e6a023.
Lemma F_2b160 : fetch_word Ubsan.M.loaded_segments (0x2b160 : word) = Some W_2b160.
Proof. vm_refl. Qed.
Lemma D_2b160 : decode_any W_2b160 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b164 : bv 32 := 0x00f6a223.
Lemma F_2b164 : fetch_word Ubsan.M.loaded_segments (0x2b164 : word) = Some W_2b164.
Proof. vm_refl. Qed.
Lemma D_2b164 : decode_any W_2b164 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b168 : bv 32 := 0x00868693.
Lemma F_2b168 : fetch_word Ubsan.M.loaded_segments (0x2b168 : word) = Some W_2b168.
Proof. vm_refl. Qed.
Lemma D_2b168 : decode_any W_2b168 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b16c : bv 32 := 0x00858593.
Lemma F_2b16c : fetch_word Ubsan.M.loaded_segments (0x2b16c : word) = Some W_2b16c.
Proof. vm_refl. Qed.
Lemma D_2b16c : decode_any W_2b16c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b170 : bv 32 := 0x00467713.
Lemma F_2b170 : fetch_word Ubsan.M.loaded_segments (0x2b170 : word) = Some W_2b170.
Proof. vm_refl. Qed.
Lemma D_2b170 : decode_any W_2b170 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b174 : bv 32 := 0x24070063.
Lemma F_2b174 : fetch_word Ubsan.M.loaded_segments (0x2b174 : word) = Some W_2b174.
Proof. vm_refl. Qed.
Lemma D_2b174 : decode_any W_2b174 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b178 : bv 32 := 0x0005a703.
Lemma F_2b178 : fetch_word Ubsan.M.loaded_segments (0x2b178 : word) = Some W_2b178.
Proof. vm_refl. Qed.
Lemma D_2b178 : decode_any W_2b178 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b17c : bv 32 := 0x00458593.
Lemma F_2b17c : fetch_word Ubsan.M.loaded_segments (0x2b17c : word) = Some W_2b17c.
Proof. vm_refl. Qed.
Lemma D_2b17c : decode_any W_2b17c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b180 : bv 32 := 0x00e6a023.
Lemma F_2b180 : fetch_word Ubsan.M.loaded_segments (0x2b180 : word) = Some W_2b180.
Proof. vm_refl. Qed.
Lemma D_2b180 : decode_any W_2b180 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b184 : bv 32 := 0x00468693.
Lemma F_2b184 : fetch_word Ubsan.M.loaded_segments (0x2b184 : word) = Some W_2b184.
Proof. vm_refl. Qed.
Lemma D_2b184 : decode_any W_2b184 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b188 : bv 32 := 0x22c0006f.
Lemma F_2b188 : fetch_word Ubsan.M.loaded_segments (0x2b188 : word) = Some W_2b188.
Proof. vm_refl. Qed.
Lemma D_2b188 : decode_any W_2b188 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b18c : bv 32 := 0x00e68023.
Lemma F_2b18c : fetch_word Ubsan.M.loaded_segments (0x2b18c : word) = Some W_2b18c.
Proof. vm_refl. Qed.
Lemma D_2b18c : decode_any W_2b18c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b190 : bv 32 := 0x00168693.
Lemma F_2b190 : fetch_word Ubsan.M.loaded_segments (0x2b190 : word) = Some W_2b190.
Proof. vm_refl. Qed.
Lemma D_2b190 : decode_any W_2b190 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b194 : bv 32 := 0xfff60613.
Lemma F_2b194 : fetch_word Ubsan.M.loaded_segments (0x2b194 : word) = Some W_2b194.
Proof. vm_refl. Qed.
Lemma D_2b194 : decode_any W_2b194 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b198 : bv 32 := 0x01058593.
Lemma F_2b198 : fetch_word Ubsan.M.loaded_segments (0x2b198 : word) = Some W_2b198.
Proof. vm_refl. Qed.
Lemma D_2b198 : decode_any W_2b198 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b19c : bv 32 := 0x01200793.
Lemma F_2b19c : fetch_word Ubsan.M.loaded_segments (0x2b19c : word) = Some W_2b19c.
Proof. vm_refl. Qed.
Lemma D_2b19c : decode_any W_2b19c = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1a0 : bv 32 := 0x0087581b.
Lemma F_2b1a0 : fetch_word Ubsan.M.loaded_segments (0x2b1a0 : word) = Some W_2b1a0.
Proof. vm_refl. Qed.
Lemma D_2b1a0 : decode_any W_2b1a0 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1a4 : bv 32 := 0xff45a883.
Lemma F_2b1a4 : fetch_word Ubsan.M.loaded_segments (0x2b1a4 : word) = Some W_2b1a4.
Proof. vm_refl. Qed.
Lemma D_2b1a4 : decode_any W_2b1a4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1a8 : bv 32 := 0xff85a283.
Lemma F_2b1a8 : fetch_word Ubsan.M.loaded_segments (0x2b1a8 : word) = Some W_2b1a8.
Proof. vm_refl. Qed.
Lemma D_2b1a8 : decode_any W_2b1a8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1ac : bv 32 := 0xffc5a303.
Lemma F_2b1ac : fetch_word Ubsan.M.loaded_segments (0x2b1ac : word) = Some W_2b1ac.
Proof. vm_refl. Qed.
Lemma D_2b1ac : decode_any W_2b1ac = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1b0 : bv 32 := 0x0005a703.
Lemma F_2b1b0 : fetch_word Ubsan.M.loaded_segments (0x2b1b0 : word) = Some W_2b1b0.
Proof. vm_refl. Qed.
Lemma D_2b1b0 : decode_any W_2b1b0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1b4 : bv 32 := 0x01889393.
Lemma F_2b1b4 : fetch_word Ubsan.M.loaded_segments (0x2b1b4 : word) = Some W_2b1b4.
Proof. vm_refl. Qed.
Lemma D_2b1b4 : decode_any W_2b1b4 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1b8 : bv 32 := 0x0088d89b.
Lemma F_2b1b8 : fetch_word Ubsan.M.loaded_segments (0x2b1b8 : word) = Some W_2b1b8.
Proof. vm_refl. Qed.
Lemma D_2b1b8 : decode_any W_2b1b8 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1bc : bv 32 := 0x0103e833.
Lemma F_2b1bc : fetch_word Ubsan.M.loaded_segments (0x2b1bc : word) = Some W_2b1bc.
Proof. vm_refl. Qed.
Lemma D_2b1bc : decode_any W_2b1bc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1c0 : bv 32 := 0x01829393.
Lemma F_2b1c0 : fetch_word Ubsan.M.loaded_segments (0x2b1c0 : word) = Some W_2b1c0.
Proof. vm_refl. Qed.
Lemma D_2b1c0 : decode_any W_2b1c0 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1c4 : bv 32 := 0x0082d29b.
Lemma F_2b1c4 : fetch_word Ubsan.M.loaded_segments (0x2b1c4 : word) = Some W_2b1c4.
Proof. vm_refl. Qed.
Lemma D_2b1c4 : decode_any W_2b1c4 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1c8 : bv 32 := 0x0113e8b3.
Lemma F_2b1c8 : fetch_word Ubsan.M.loaded_segments (0x2b1c8 : word) = Some W_2b1c8.
Proof. vm_refl. Qed.
Lemma D_2b1c8 : decode_any W_2b1c8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1cc : bv 32 := 0x01831393.
Lemma F_2b1cc : fetch_word Ubsan.M.loaded_segments (0x2b1cc : word) = Some W_2b1cc.
Proof. vm_refl. Qed.
Lemma D_2b1cc : decode_any W_2b1cc = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1d0 : bv 32 := 0x0083531b.
Lemma F_2b1d0 : fetch_word Ubsan.M.loaded_segments (0x2b1d0 : word) = Some W_2b1d0.
Proof. vm_refl. Qed.
Lemma D_2b1d0 : decode_any W_2b1d0 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1d4 : bv 32 := 0x0053e2b3.
Lemma F_2b1d4 : fetch_word Ubsan.M.loaded_segments (0x2b1d4 : word) = Some W_2b1d4.
Proof. vm_refl. Qed.
Lemma D_2b1d4 : decode_any W_2b1d4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1d8 : bv 32 := 0x01871393.
Lemma F_2b1d8 : fetch_word Ubsan.M.loaded_segments (0x2b1d8 : word) = Some W_2b1d8.
Proof. vm_refl. Qed.
Lemma D_2b1d8 : decode_any W_2b1d8 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1dc : bv 32 := 0x0063e333.
Lemma F_2b1dc : fetch_word Ubsan.M.loaded_segments (0x2b1dc : word) = Some W_2b1dc.
Proof. vm_refl. Qed.
Lemma D_2b1dc : decode_any W_2b1dc = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1e0 : bv 32 := 0xff060613.
Lemma F_2b1e0 : fetch_word Ubsan.M.loaded_segments (0x2b1e0 : word) = Some W_2b1e0.
Proof. vm_refl. Qed.
Lemma D_2b1e0 : decode_any W_2b1e0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1e4 : bv 32 := 0x0106a023.
Lemma F_2b1e4 : fetch_word Ubsan.M.loaded_segments (0x2b1e4 : word) = Some W_2b1e4.
Proof. vm_refl. Qed.
Lemma D_2b1e4 : decode_any W_2b1e4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1e8 : bv 32 := 0x0116a223.
Lemma F_2b1e8 : fetch_word Ubsan.M.loaded_segments (0x2b1e8 : word) = Some W_2b1e8.
Proof. vm_refl. Qed.
Lemma D_2b1e8 : decode_any W_2b1e8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1ec : bv 32 := 0x0056a423.
Lemma F_2b1ec : fetch_word Ubsan.M.loaded_segments (0x2b1ec : word) = Some W_2b1ec.
Proof. vm_refl. Qed.
Lemma D_2b1ec : decode_any W_2b1ec = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1f0 : bv 32 := 0x0066a623.
Lemma F_2b1f0 : fetch_word Ubsan.M.loaded_segments (0x2b1f0 : word) = Some W_2b1f0.
Proof. vm_refl. Qed.
Lemma D_2b1f0 : decode_any W_2b1f0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1f4 : bv 32 := 0x01068693.
Lemma F_2b1f4 : fetch_word Ubsan.M.loaded_segments (0x2b1f4 : word) = Some W_2b1f4.
Proof. vm_refl. Qed.
Lemma D_2b1f4 : decode_any W_2b1f4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1f8 : bv 32 := 0x01058593.
Lemma F_2b1f8 : fetch_word Ubsan.M.loaded_segments (0x2b1f8 : word) = Some W_2b1f8.
Proof. vm_refl. Qed.
Lemma D_2b1f8 : decode_any W_2b1f8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b1fc : bv 32 := 0xfac7e2e3.
Lemma F_2b1fc : fetch_word Ubsan.M.loaded_segments (0x2b1fc : word) = Some W_2b1fc.
Proof. vm_refl. Qed.
Lemma D_2b1fc : decode_any W_2b1fc = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b200 : bv 32 := 0xff158593.
Lemma F_2b200 : fetch_word Ubsan.M.loaded_segments (0x2b200 : word) = Some W_2b200.
Proof. vm_refl. Qed.
Lemma D_2b200 : decode_any W_2b200 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b204 : bv 32 := 0x01000713.
Lemma F_2b204 : fetch_word Ubsan.M.loaded_segments (0x2b204 : word) = Some W_2b204.
Proof. vm_refl. Qed.
Lemma D_2b204 : decode_any W_2b204 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b208 : bv 32 := 0xe4e666e3.
Lemma F_2b208 : fetch_word Ubsan.M.loaded_segments (0x2b208 : word) = Some W_2b208.
Proof. vm_refl. Qed.
Lemma D_2b208 : decode_any W_2b208 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b20c : bv 32 := 0x0940006f.
Lemma F_2b20c : fetch_word Ubsan.M.loaded_segments (0x2b20c : word) = Some W_2b20c.
Proof. vm_refl. Qed.
Lemma D_2b20c : decode_any W_2b20c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b210 : bv 32 := 0x00875793.
Lemma F_2b210 : fetch_word Ubsan.M.loaded_segments (0x2b210 : word) = Some W_2b210.
Proof. vm_refl. Qed.
Lemma D_2b210 : decode_any W_2b210 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b214 : bv 32 := 0x01075813.
Lemma F_2b214 : fetch_word Ubsan.M.loaded_segments (0x2b214 : word) = Some W_2b214.
Proof. vm_refl. Qed.
Lemma D_2b214 : decode_any W_2b214 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b218 : bv 32 := 0xffd60613.
Lemma F_2b218 : fetch_word Ubsan.M.loaded_segments (0x2b218 : word) = Some W_2b218.
Proof. vm_refl. Qed.
Lemma D_2b218 : decode_any W_2b218 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b21c : bv 32 := 0x00e68023.
Lemma F_2b21c : fetch_word Ubsan.M.loaded_segments (0x2b21c : word) = Some W_2b21c.
Proof. vm_refl. Qed.
Lemma D_2b21c : decode_any W_2b21c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b220 : bv 32 := 0x00f680a3.
Lemma F_2b220 : fetch_word Ubsan.M.loaded_segments (0x2b220 : word) = Some W_2b220.
Proof. vm_refl. Qed.
Lemma D_2b220 : decode_any W_2b220 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b224 : bv 32 := 0x01068123.
Lemma F_2b224 : fetch_word Ubsan.M.loaded_segments (0x2b224 : word) = Some W_2b224.
Proof. vm_refl. Qed.
Lemma D_2b224 : decode_any W_2b224 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b228 : bv 32 := 0x00368693.
Lemma F_2b228 : fetch_word Ubsan.M.loaded_segments (0x2b228 : word) = Some W_2b228.
Proof. vm_refl. Qed.
Lemma D_2b228 : decode_any W_2b228 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b22c : bv 32 := 0x01058593.
Lemma F_2b22c : fetch_word Ubsan.M.loaded_segments (0x2b22c : word) = Some W_2b22c.
Proof. vm_refl. Qed.
Lemma D_2b22c : decode_any W_2b22c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b230 : bv 32 := 0x01000793.
Lemma F_2b230 : fetch_word Ubsan.M.loaded_segments (0x2b230 : word) = Some W_2b230.
Proof. vm_refl. Qed.
Lemma D_2b230 : decode_any W_2b230 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b234 : bv 32 := 0x0187581b.
Lemma F_2b234 : fetch_word Ubsan.M.loaded_segments (0x2b234 : word) = Some W_2b234.
Proof. vm_refl. Qed.
Lemma D_2b234 : decode_any W_2b234 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b238 : bv 32 := 0xff45a883.
Lemma F_2b238 : fetch_word Ubsan.M.loaded_segments (0x2b238 : word) = Some W_2b238.
Proof. vm_refl. Qed.
Lemma D_2b238 : decode_any W_2b238 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b23c : bv 32 := 0xff85a283.
Lemma F_2b23c : fetch_word Ubsan.M.loaded_segments (0x2b23c : word) = Some W_2b23c.
Proof. vm_refl. Qed.
Lemma D_2b23c : decode_any W_2b23c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b240 : bv 32 := 0xffc5a303.
Lemma F_2b240 : fetch_word Ubsan.M.loaded_segments (0x2b240 : word) = Some W_2b240.
Proof. vm_refl. Qed.
Lemma D_2b240 : decode_any W_2b240 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b244 : bv 32 := 0x0005a703.
Lemma F_2b244 : fetch_word Ubsan.M.loaded_segments (0x2b244 : word) = Some W_2b244.
Proof. vm_refl. Qed.
Lemma D_2b244 : decode_any W_2b244 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b248 : bv 32 := 0x00889393.
Lemma F_2b248 : fetch_word Ubsan.M.loaded_segments (0x2b248 : word) = Some W_2b248.
Proof. vm_refl. Qed.
Lemma D_2b248 : decode_any W_2b248 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b24c : bv 32 := 0x0188d89b.
Lemma F_2b24c : fetch_word Ubsan.M.loaded_segments (0x2b24c : word) = Some W_2b24c.
Proof. vm_refl. Qed.
Lemma D_2b24c : decode_any W_2b24c = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b250 : bv 32 := 0x0103e833.
Lemma F_2b250 : fetch_word Ubsan.M.loaded_segments (0x2b250 : word) = Some W_2b250.
Proof. vm_refl. Qed.
Lemma D_2b250 : decode_any W_2b250 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b254 : bv 32 := 0x00829393.
Lemma F_2b254 : fetch_word Ubsan.M.loaded_segments (0x2b254 : word) = Some W_2b254.
Proof. vm_refl. Qed.
Lemma D_2b254 : decode_any W_2b254 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b258 : bv 32 := 0x0182d29b.
Lemma F_2b258 : fetch_word Ubsan.M.loaded_segments (0x2b258 : word) = Some W_2b258.
Proof. vm_refl. Qed.
Lemma D_2b258 : decode_any W_2b258 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b25c : bv 32 := 0x0113e8b3.
Lemma F_2b25c : fetch_word Ubsan.M.loaded_segments (0x2b25c : word) = Some W_2b25c.
Proof. vm_refl. Qed.
Lemma D_2b25c : decode_any W_2b25c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b260 : bv 32 := 0x00831393.
Lemma F_2b260 : fetch_word Ubsan.M.loaded_segments (0x2b260 : word) = Some W_2b260.
Proof. vm_refl. Qed.
Lemma D_2b260 : decode_any W_2b260 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b264 : bv 32 := 0x0183531b.
Lemma F_2b264 : fetch_word Ubsan.M.loaded_segments (0x2b264 : word) = Some W_2b264.
Proof. vm_refl. Qed.
Lemma D_2b264 : decode_any W_2b264 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b268 : bv 32 := 0x0053e2b3.
Lemma F_2b268 : fetch_word Ubsan.M.loaded_segments (0x2b268 : word) = Some W_2b268.
Proof. vm_refl. Qed.
Lemma D_2b268 : decode_any W_2b268 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b26c : bv 32 := 0x00871393.
Lemma F_2b26c : fetch_word Ubsan.M.loaded_segments (0x2b26c : word) = Some W_2b26c.
Proof. vm_refl. Qed.
Lemma D_2b26c : decode_any W_2b26c = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b270 : bv 32 := 0x0063e333.
Lemma F_2b270 : fetch_word Ubsan.M.loaded_segments (0x2b270 : word) = Some W_2b270.
Proof. vm_refl. Qed.
Lemma D_2b270 : decode_any W_2b270 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b274 : bv 32 := 0xff060613.
Lemma F_2b274 : fetch_word Ubsan.M.loaded_segments (0x2b274 : word) = Some W_2b274.
Proof. vm_refl. Qed.
Lemma D_2b274 : decode_any W_2b274 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b278 : bv 32 := 0x0106a023.
Lemma F_2b278 : fetch_word Ubsan.M.loaded_segments (0x2b278 : word) = Some W_2b278.
Proof. vm_refl. Qed.
Lemma D_2b278 : decode_any W_2b278 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b27c : bv 32 := 0x0116a223.
Lemma F_2b27c : fetch_word Ubsan.M.loaded_segments (0x2b27c : word) = Some W_2b27c.
Proof. vm_refl. Qed.
Lemma D_2b27c : decode_any W_2b27c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b280 : bv 32 := 0x0056a423.
Lemma F_2b280 : fetch_word Ubsan.M.loaded_segments (0x2b280 : word) = Some W_2b280.
Proof. vm_refl. Qed.
Lemma D_2b280 : decode_any W_2b280 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b284 : bv 32 := 0x0066a623.
Lemma F_2b284 : fetch_word Ubsan.M.loaded_segments (0x2b284 : word) = Some W_2b284.
Proof. vm_refl. Qed.
Lemma D_2b284 : decode_any W_2b284 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b288 : bv 32 := 0x01068693.
Lemma F_2b288 : fetch_word Ubsan.M.loaded_segments (0x2b288 : word) = Some W_2b288.
Proof. vm_refl. Qed.
Lemma D_2b288 : decode_any W_2b288 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b28c : bv 32 := 0x01058593.
Lemma F_2b28c : fetch_word Ubsan.M.loaded_segments (0x2b28c : word) = Some W_2b28c.
Proof. vm_refl. Qed.
Lemma D_2b28c : decode_any W_2b28c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b290 : bv 32 := 0xfac7e2e3.
Lemma F_2b290 : fetch_word Ubsan.M.loaded_segments (0x2b290 : word) = Some W_2b290.
Proof. vm_refl. Qed.
Lemma D_2b290 : decode_any W_2b290 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b294 : bv 32 := 0xff358593.
Lemma F_2b294 : fetch_word Ubsan.M.loaded_segments (0x2b294 : word) = Some W_2b294.
Proof. vm_refl. Qed.
Lemma D_2b294 : decode_any W_2b294 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b298 : bv 32 := 0x01000713.
Lemma F_2b298 : fetch_word Ubsan.M.loaded_segments (0x2b298 : word) = Some W_2b298.
Proof. vm_refl. Qed.
Lemma D_2b298 : decode_any W_2b298 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b29c : bv 32 := 0xdae66ce3.
Lemma F_2b29c : fetch_word Ubsan.M.loaded_segments (0x2b29c : word) = Some W_2b29c.
Proof. vm_refl. Qed.
Lemma D_2b29c : decode_any W_2b29c = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2a0 : bv 32 := 0x0005c703.
Lemma F_2b2a0 : fetch_word Ubsan.M.loaded_segments (0x2b2a0 : word) = Some W_2b2a0.
Proof. vm_refl. Qed.
Lemma D_2b2a0 : decode_any W_2b2a0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2a4 : bv 32 := 0x0015c783.
Lemma F_2b2a4 : fetch_word Ubsan.M.loaded_segments (0x2b2a4 : word) = Some W_2b2a4.
Proof. vm_refl. Qed.
Lemma D_2b2a4 : decode_any W_2b2a4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2a8 : bv 32 := 0x0025c803.
Lemma F_2b2a8 : fetch_word Ubsan.M.loaded_segments (0x2b2a8 : word) = Some W_2b2a8.
Proof. vm_refl. Qed.
Lemma D_2b2a8 : decode_any W_2b2a8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2ac : bv 32 := 0x0035c883.
Lemma F_2b2ac : fetch_word Ubsan.M.loaded_segments (0x2b2ac : word) = Some W_2b2ac.
Proof. vm_refl. Qed.
Lemma D_2b2ac : decode_any W_2b2ac = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2b0 : bv 32 := 0x0045c283.
Lemma F_2b2b0 : fetch_word Ubsan.M.loaded_segments (0x2b2b0 : word) = Some W_2b2b0.
Proof. vm_refl. Qed.
Lemma D_2b2b0 : decode_any W_2b2b0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2b4 : bv 32 := 0x0055c303.
Lemma F_2b2b4 : fetch_word Ubsan.M.loaded_segments (0x2b2b4 : word) = Some W_2b2b4.
Proof. vm_refl. Qed.
Lemma D_2b2b4 : decode_any W_2b2b4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2b8 : bv 32 := 0x0065c383.
Lemma F_2b2b8 : fetch_word Ubsan.M.loaded_segments (0x2b2b8 : word) = Some W_2b2b8.
Proof. vm_refl. Qed.
Lemma D_2b2b8 : decode_any W_2b2b8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2bc : bv 32 := 0x0075ce03.
Lemma F_2b2bc : fetch_word Ubsan.M.loaded_segments (0x2b2bc : word) = Some W_2b2bc.
Proof. vm_refl. Qed.
Lemma D_2b2bc : decode_any W_2b2bc = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2c0 : bv 32 := 0x00e68023.
Lemma F_2b2c0 : fetch_word Ubsan.M.loaded_segments (0x2b2c0 : word) = Some W_2b2c0.
Proof. vm_refl. Qed.
Lemma D_2b2c0 : decode_any W_2b2c0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2c4 : bv 32 := 0x00f680a3.
Lemma F_2b2c4 : fetch_word Ubsan.M.loaded_segments (0x2b2c4 : word) = Some W_2b2c4.
Proof. vm_refl. Qed.
Lemma D_2b2c4 : decode_any W_2b2c4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2c8 : bv 32 := 0x01068123.
Lemma F_2b2c8 : fetch_word Ubsan.M.loaded_segments (0x2b2c8 : word) = Some W_2b2c8.
Proof. vm_refl. Qed.
Lemma D_2b2c8 : decode_any W_2b2c8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2cc : bv 32 := 0x011681a3.
Lemma F_2b2cc : fetch_word Ubsan.M.loaded_segments (0x2b2cc : word) = Some W_2b2cc.
Proof. vm_refl. Qed.
Lemma D_2b2cc : decode_any W_2b2cc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2d0 : bv 32 := 0x0085c703.
Lemma F_2b2d0 : fetch_word Ubsan.M.loaded_segments (0x2b2d0 : word) = Some W_2b2d0.
Proof. vm_refl. Qed.
Lemma D_2b2d0 : decode_any W_2b2d0 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2d4 : bv 32 := 0x0095c783.
Lemma F_2b2d4 : fetch_word Ubsan.M.loaded_segments (0x2b2d4 : word) = Some W_2b2d4.
Proof. vm_refl. Qed.
Lemma D_2b2d4 : decode_any W_2b2d4 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2d8 : bv 32 := 0x00a5c803.
Lemma F_2b2d8 : fetch_word Ubsan.M.loaded_segments (0x2b2d8 : word) = Some W_2b2d8.
Proof. vm_refl. Qed.
Lemma D_2b2d8 : decode_any W_2b2d8 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2dc : bv 32 := 0x00b5c883.
Lemma F_2b2dc : fetch_word Ubsan.M.loaded_segments (0x2b2dc : word) = Some W_2b2dc.
Proof. vm_refl. Qed.
Lemma D_2b2dc : decode_any W_2b2dc = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2e0 : bv 32 := 0x00568223.
Lemma F_2b2e0 : fetch_word Ubsan.M.loaded_segments (0x2b2e0 : word) = Some W_2b2e0.
Proof. vm_refl. Qed.
Lemma D_2b2e0 : decode_any W_2b2e0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2e4 : bv 32 := 0x006682a3.
Lemma F_2b2e4 : fetch_word Ubsan.M.loaded_segments (0x2b2e4 : word) = Some W_2b2e4.
Proof. vm_refl. Qed.
Lemma D_2b2e4 : decode_any W_2b2e4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2e8 : bv 32 := 0x00768323.
Lemma F_2b2e8 : fetch_word Ubsan.M.loaded_segments (0x2b2e8 : word) = Some W_2b2e8.
Proof. vm_refl. Qed.
Lemma D_2b2e8 : decode_any W_2b2e8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2ec : bv 32 := 0x01c683a3.
Lemma F_2b2ec : fetch_word Ubsan.M.loaded_segments (0x2b2ec : word) = Some W_2b2ec.
Proof. vm_refl. Qed.
Lemma D_2b2ec : decode_any W_2b2ec = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2f0 : bv 32 := 0x00c5c283.
Lemma F_2b2f0 : fetch_word Ubsan.M.loaded_segments (0x2b2f0 : word) = Some W_2b2f0.
Proof. vm_refl. Qed.
Lemma D_2b2f0 : decode_any W_2b2f0 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2f4 : bv 32 := 0x00d5c303.
Lemma F_2b2f4 : fetch_word Ubsan.M.loaded_segments (0x2b2f4 : word) = Some W_2b2f4.
Proof. vm_refl. Qed.
Lemma D_2b2f4 : decode_any W_2b2f4 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2f8 : bv 32 := 0x00e5c383.
Lemma F_2b2f8 : fetch_word Ubsan.M.loaded_segments (0x2b2f8 : word) = Some W_2b2f8.
Proof. vm_refl. Qed.
Lemma D_2b2f8 : decode_any W_2b2f8 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2fc : bv 32 := 0x00f5ce03.
Lemma F_2b2fc : fetch_word Ubsan.M.loaded_segments (0x2b2fc : word) = Some W_2b2fc.
Proof. vm_refl. Qed.
Lemma D_2b2fc : decode_any W_2b2fc = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b300 : bv 32 := 0x01058593.
Lemma F_2b300 : fetch_word Ubsan.M.loaded_segments (0x2b300 : word) = Some W_2b300.
Proof. vm_refl. Qed.
Lemma D_2b300 : decode_any W_2b300 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b304 : bv 32 := 0x00e68423.
Lemma F_2b304 : fetch_word Ubsan.M.loaded_segments (0x2b304 : word) = Some W_2b304.
Proof. vm_refl. Qed.
Lemma D_2b304 : decode_any W_2b304 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b308 : bv 32 := 0x00f684a3.
Lemma F_2b308 : fetch_word Ubsan.M.loaded_segments (0x2b308 : word) = Some W_2b308.
Proof. vm_refl. Qed.
Lemma D_2b308 : decode_any W_2b308 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b30c : bv 32 := 0x01068523.
Lemma F_2b30c : fetch_word Ubsan.M.loaded_segments (0x2b30c : word) = Some W_2b30c.
Proof. vm_refl. Qed.
Lemma D_2b30c : decode_any W_2b30c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b310 : bv 32 := 0x011685a3.
Lemma F_2b310 : fetch_word Ubsan.M.loaded_segments (0x2b310 : word) = Some W_2b310.
Proof. vm_refl. Qed.
Lemma D_2b310 : decode_any W_2b310 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b314 : bv 32 := 0x01068713.
Lemma F_2b314 : fetch_word Ubsan.M.loaded_segments (0x2b314 : word) = Some W_2b314.
Proof. vm_refl. Qed.
Lemma D_2b314 : decode_any W_2b314 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b318 : bv 32 := 0x00568623.
Lemma F_2b318 : fetch_word Ubsan.M.loaded_segments (0x2b318 : word) = Some W_2b318.
Proof. vm_refl. Qed.
Lemma D_2b318 : decode_any W_2b318 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b31c : bv 32 := 0x006686a3.
Lemma F_2b31c : fetch_word Ubsan.M.loaded_segments (0x2b31c : word) = Some W_2b31c.
Proof. vm_refl. Qed.
Lemma D_2b31c : decode_any W_2b31c = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b320 : bv 32 := 0x00768723.
Lemma F_2b320 : fetch_word Ubsan.M.loaded_segments (0x2b320 : word) = Some W_2b320.
Proof. vm_refl. Qed.
Lemma D_2b320 : decode_any W_2b320 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b324 : bv 32 := 0x01c687a3.
Lemma F_2b324 : fetch_word Ubsan.M.loaded_segments (0x2b324 : word) = Some W_2b324.
Proof. vm_refl. Qed.
Lemma D_2b324 : decode_any W_2b324 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b328 : bv 32 := 0x00070693.
Lemma F_2b328 : fetch_word Ubsan.M.loaded_segments (0x2b328 : word) = Some W_2b328.
Proof. vm_refl. Qed.
Lemma D_2b328 : decode_any W_2b328 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b32c : bv 32 := 0x00867713.
Lemma F_2b32c : fetch_word Ubsan.M.loaded_segments (0x2b32c : word) = Some W_2b32c.
Proof. vm_refl. Qed.
Lemma D_2b32c : decode_any W_2b32c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b330 : bv 32 := 0xd20706e3.
Lemma F_2b330 : fetch_word Ubsan.M.loaded_segments (0x2b330 : word) = Some W_2b330.
Proof. vm_refl. Qed.
Lemma D_2b330 : decode_any W_2b330 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b334 : bv 32 := 0x0005c703.
Lemma F_2b334 : fetch_word Ubsan.M.loaded_segments (0x2b334 : word) = Some W_2b334.
Proof. vm_refl. Qed.
Lemma D_2b334 : decode_any W_2b334 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b338 : bv 32 := 0x0015c783.
Lemma F_2b338 : fetch_word Ubsan.M.loaded_segments (0x2b338 : word) = Some W_2b338.
Proof. vm_refl. Qed.
Lemma D_2b338 : decode_any W_2b338 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b33c : bv 32 := 0x0025c803.
Lemma F_2b33c : fetch_word Ubsan.M.loaded_segments (0x2b33c : word) = Some W_2b33c.
Proof. vm_refl. Qed.
Lemma D_2b33c : decode_any W_2b33c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b340 : bv 32 := 0x0035c883.
Lemma F_2b340 : fetch_word Ubsan.M.loaded_segments (0x2b340 : word) = Some W_2b340.
Proof. vm_refl. Qed.
Lemma D_2b340 : decode_any W_2b340 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b344 : bv 32 := 0x0045c283.
Lemma F_2b344 : fetch_word Ubsan.M.loaded_segments (0x2b344 : word) = Some W_2b344.
Proof. vm_refl. Qed.
Lemma D_2b344 : decode_any W_2b344 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b348 : bv 32 := 0x0055c303.
Lemma F_2b348 : fetch_word Ubsan.M.loaded_segments (0x2b348 : word) = Some W_2b348.
Proof. vm_refl. Qed.
Lemma D_2b348 : decode_any W_2b348 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b34c : bv 32 := 0x0065c383.
Lemma F_2b34c : fetch_word Ubsan.M.loaded_segments (0x2b34c : word) = Some W_2b34c.
Proof. vm_refl. Qed.
Lemma D_2b34c : decode_any W_2b34c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b350 : bv 32 := 0x0075ce03.
Lemma F_2b350 : fetch_word Ubsan.M.loaded_segments (0x2b350 : word) = Some W_2b350.
Proof. vm_refl. Qed.
Lemma D_2b350 : decode_any W_2b350 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b354 : bv 32 := 0x00858593.
Lemma F_2b354 : fetch_word Ubsan.M.loaded_segments (0x2b354 : word) = Some W_2b354.
Proof. vm_refl. Qed.
Lemma D_2b354 : decode_any W_2b354 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b358 : bv 32 := 0x00e68023.
Lemma F_2b358 : fetch_word Ubsan.M.loaded_segments (0x2b358 : word) = Some W_2b358.
Proof. vm_refl. Qed.
Lemma D_2b358 : decode_any W_2b358 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b35c : bv 32 := 0x00f680a3.
Lemma F_2b35c : fetch_word Ubsan.M.loaded_segments (0x2b35c : word) = Some W_2b35c.
Proof. vm_refl. Qed.
Lemma D_2b35c : decode_any W_2b35c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b360 : bv 32 := 0x01068123.
Lemma F_2b360 : fetch_word Ubsan.M.loaded_segments (0x2b360 : word) = Some W_2b360.
Proof. vm_refl. Qed.
Lemma D_2b360 : decode_any W_2b360 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b364 : bv 32 := 0x011681a3.
Lemma F_2b364 : fetch_word Ubsan.M.loaded_segments (0x2b364 : word) = Some W_2b364.
Proof. vm_refl. Qed.
Lemma D_2b364 : decode_any W_2b364 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b368 : bv 32 := 0x00868713.
Lemma F_2b368 : fetch_word Ubsan.M.loaded_segments (0x2b368 : word) = Some W_2b368.
Proof. vm_refl. Qed.
Lemma D_2b368 : decode_any W_2b368 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b36c : bv 32 := 0x00568223.
Lemma F_2b36c : fetch_word Ubsan.M.loaded_segments (0x2b36c : word) = Some W_2b36c.
Proof. vm_refl. Qed.
Lemma D_2b36c : decode_any W_2b36c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b370 : bv 32 := 0x006682a3.
Lemma F_2b370 : fetch_word Ubsan.M.loaded_segments (0x2b370 : word) = Some W_2b370.
Proof. vm_refl. Qed.
Lemma D_2b370 : decode_any W_2b370 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b374 : bv 32 := 0x00768323.
Lemma F_2b374 : fetch_word Ubsan.M.loaded_segments (0x2b374 : word) = Some W_2b374.
Proof. vm_refl. Qed.
Lemma D_2b374 : decode_any W_2b374 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b378 : bv 32 := 0x01c683a3.
Lemma F_2b378 : fetch_word Ubsan.M.loaded_segments (0x2b378 : word) = Some W_2b378.
Proof. vm_refl. Qed.
Lemma D_2b378 : decode_any W_2b378 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b37c : bv 32 := 0x00070693.
Lemma F_2b37c : fetch_word Ubsan.M.loaded_segments (0x2b37c : word) = Some W_2b37c.
Proof. vm_refl. Qed.
Lemma D_2b37c : decode_any W_2b37c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b380 : bv 32 := 0x00467713.
Lemma F_2b380 : fetch_word Ubsan.M.loaded_segments (0x2b380 : word) = Some W_2b380.
Proof. vm_refl. Qed.
Lemma D_2b380 : decode_any W_2b380 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b384 : bv 32 := 0x02070863.
Lemma F_2b384 : fetch_word Ubsan.M.loaded_segments (0x2b384 : word) = Some W_2b384.
Proof. vm_refl. Qed.
Lemma D_2b384 : decode_any W_2b384 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b388 : bv 32 := 0x0005c703.
Lemma F_2b388 : fetch_word Ubsan.M.loaded_segments (0x2b388 : word) = Some W_2b388.
Proof. vm_refl. Qed.
Lemma D_2b388 : decode_any W_2b388 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b38c : bv 32 := 0x0015c783.
Lemma F_2b38c : fetch_word Ubsan.M.loaded_segments (0x2b38c : word) = Some W_2b38c.
Proof. vm_refl. Qed.
Lemma D_2b38c : decode_any W_2b38c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b390 : bv 32 := 0x0025c803.
Lemma F_2b390 : fetch_word Ubsan.M.loaded_segments (0x2b390 : word) = Some W_2b390.
Proof. vm_refl. Qed.
Lemma D_2b390 : decode_any W_2b390 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b394 : bv 32 := 0x0035c883.
Lemma F_2b394 : fetch_word Ubsan.M.loaded_segments (0x2b394 : word) = Some W_2b394.
Proof. vm_refl. Qed.
Lemma D_2b394 : decode_any W_2b394 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b398 : bv 32 := 0x00458593.
Lemma F_2b398 : fetch_word Ubsan.M.loaded_segments (0x2b398 : word) = Some W_2b398.
Proof. vm_refl. Qed.
Lemma D_2b398 : decode_any W_2b398 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b39c : bv 32 := 0x00468293.
Lemma F_2b39c : fetch_word Ubsan.M.loaded_segments (0x2b39c : word) = Some W_2b39c.
Proof. vm_refl. Qed.
Lemma D_2b39c : decode_any W_2b39c = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3a0 : bv 32 := 0x00e68023.
Lemma F_2b3a0 : fetch_word Ubsan.M.loaded_segments (0x2b3a0 : word) = Some W_2b3a0.
Proof. vm_refl. Qed.
Lemma D_2b3a0 : decode_any W_2b3a0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3a4 : bv 32 := 0x00f680a3.
Lemma F_2b3a4 : fetch_word Ubsan.M.loaded_segments (0x2b3a4 : word) = Some W_2b3a4.
Proof. vm_refl. Qed.
Lemma D_2b3a4 : decode_any W_2b3a4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3a8 : bv 32 := 0x01068123.
Lemma F_2b3a8 : fetch_word Ubsan.M.loaded_segments (0x2b3a8 : word) = Some W_2b3a8.
Proof. vm_refl. Qed.
Lemma D_2b3a8 : decode_any W_2b3a8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3ac : bv 32 := 0x011681a3.
Lemma F_2b3ac : fetch_word Ubsan.M.loaded_segments (0x2b3ac : word) = Some W_2b3ac.
Proof. vm_refl. Qed.
Lemma D_2b3ac : decode_any W_2b3ac = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3b0 : bv 32 := 0x00028693.
Lemma F_2b3b0 : fetch_word Ubsan.M.loaded_segments (0x2b3b0 : word) = Some W_2b3b0.
Proof. vm_refl. Qed.
Lemma D_2b3b0 : decode_any W_2b3b0 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3b4 : bv 32 := 0x00267713.
Lemma F_2b3b4 : fetch_word Ubsan.M.loaded_segments (0x2b3b4 : word) = Some W_2b3b4.
Proof. vm_refl. Qed.
Lemma D_2b3b4 : decode_any W_2b3b4 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3b8 : bv 32 := 0x00071863.
Lemma F_2b3b8 : fetch_word Ubsan.M.loaded_segments (0x2b3b8 : word) = Some W_2b3b8.
Proof. vm_refl. Qed.
Lemma D_2b3b8 : decode_any W_2b3b8 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3bc : bv 32 := 0x00167613.
Lemma F_2b3bc : fetch_word Ubsan.M.loaded_segments (0x2b3bc : word) = Some W_2b3bc.
Proof. vm_refl. Qed.
Lemma D_2b3bc : decode_any W_2b3bc = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3c0 : bv 32 := 0x02061663.
Lemma F_2b3c0 : fetch_word Ubsan.M.loaded_segments (0x2b3c0 : word) = Some W_2b3c0.
Proof. vm_refl. Qed.
Lemma D_2b3c0 : decode_any W_2b3c0 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3c4 : bv 32 := 0x00008067.
Lemma F_2b3c4 : fetch_word Ubsan.M.loaded_segments (0x2b3c4 : word) = Some W_2b3c4.
Proof. vm_refl. Qed.
Lemma D_2b3c4 : decode_any W_2b3c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3c8 : bv 32 := 0x0005c703.
Lemma F_2b3c8 : fetch_word Ubsan.M.loaded_segments (0x2b3c8 : word) = Some W_2b3c8.
Proof. vm_refl. Qed.
Lemma D_2b3c8 : decode_any W_2b3c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3cc : bv 32 := 0x0015c783.
Lemma F_2b3cc : fetch_word Ubsan.M.loaded_segments (0x2b3cc : word) = Some W_2b3cc.
Proof. vm_refl. Qed.
Lemma D_2b3cc : decode_any W_2b3cc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3d0 : bv 32 := 0x00258593.
Lemma F_2b3d0 : fetch_word Ubsan.M.loaded_segments (0x2b3d0 : word) = Some W_2b3d0.
Proof. vm_refl. Qed.
Lemma D_2b3d0 : decode_any W_2b3d0 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3d4 : bv 32 := 0x00268813.
Lemma F_2b3d4 : fetch_word Ubsan.M.loaded_segments (0x2b3d4 : word) = Some W_2b3d4.
Proof. vm_refl. Qed.
Lemma D_2b3d4 : decode_any W_2b3d4 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3d8 : bv 32 := 0x00e68023.
Lemma F_2b3d8 : fetch_word Ubsan.M.loaded_segments (0x2b3d8 : word) = Some W_2b3d8.
Proof. vm_refl. Qed.
Lemma D_2b3d8 : decode_any W_2b3d8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3dc : bv 32 := 0x00f680a3.
Lemma F_2b3dc : fetch_word Ubsan.M.loaded_segments (0x2b3dc : word) = Some W_2b3dc.
Proof. vm_refl. Qed.
Lemma D_2b3dc : decode_any W_2b3dc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3e0 : bv 32 := 0x00080693.
Lemma F_2b3e0 : fetch_word Ubsan.M.loaded_segments (0x2b3e0 : word) = Some W_2b3e0.
Proof. vm_refl. Qed.
Lemma D_2b3e0 : decode_any W_2b3e0 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3e4 : bv 32 := 0x00167613.
Lemma F_2b3e4 : fetch_word Ubsan.M.loaded_segments (0x2b3e4 : word) = Some W_2b3e4.
Proof. vm_refl. Qed.
Lemma D_2b3e4 : decode_any W_2b3e4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3e8 : bv 32 := 0xfc060ee3.
Lemma F_2b3e8 : fetch_word Ubsan.M.loaded_segments (0x2b3e8 : word) = Some W_2b3e8.
Proof. vm_refl. Qed.
Lemma D_2b3e8 : decode_any W_2b3e8 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3ec : bv 32 := 0x0005c583.
Lemma F_2b3ec : fetch_word Ubsan.M.loaded_segments (0x2b3ec : word) = Some W_2b3ec.
Proof. vm_refl. Qed.
Lemma D_2b3ec : decode_any W_2b3ec = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3f0 : bv 32 := 0x00b68023.
Lemma F_2b3f0 : fetch_word Ubsan.M.loaded_segments (0x2b3f0 : word) = Some W_2b3f0.
Proof. vm_refl. Qed.
Lemma D_2b3f0 : decode_any W_2b3f0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3f4 : bv 32 := 0x00008067.
Lemma F_2b3f4 : fetch_word Ubsan.M.loaded_segments (0x2b3f4 : word) = Some W_2b3f4.
Proof. vm_refl. Qed.
Lemma D_2b3f4 : decode_any W_2b3f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3f8 : bv 32 := 0x0e060a63.
Lemma F_2b3f8 : fetch_word Ubsan.M.loaded_segments (0x2b3f8 : word) = Some W_2b3f8.
Proof. vm_refl. Qed.
Lemma D_2b3f8 : decode_any W_2b3f8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3fc : bv 32 := 0x00b50023.
Lemma F_2b3fc : fetch_word Ubsan.M.loaded_segments (0x2b3fc : word) = Some W_2b3fc.
Proof. vm_refl. Qed.
Lemma D_2b3fc : decode_any W_2b3fc = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b400 : bv 32 := 0x00c506b3.
Lemma F_2b400 : fetch_word Ubsan.M.loaded_segments (0x2b400 : word) = Some W_2b400.
Proof. vm_refl. Qed.
Lemma D_2b400 : decode_any W_2b400 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b404 : bv 32 := 0x00300713.
Lemma F_2b404 : fetch_word Ubsan.M.loaded_segments (0x2b404 : word) = Some W_2b404.
Proof. vm_refl. Qed.
Lemma D_2b404 : decode_any W_2b404 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b408 : bv 32 := 0xfeb68fa3.
Lemma F_2b408 : fetch_word Ubsan.M.loaded_segments (0x2b408 : word) = Some W_2b408.
Proof. vm_refl. Qed.
Lemma D_2b408 : decode_any W_2b408 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b40c : bv 32 := 0x0ee66063.
Lemma F_2b40c : fetch_word Ubsan.M.loaded_segments (0x2b40c : word) = Some W_2b40c.
Proof. vm_refl. Qed.
Lemma D_2b40c : decode_any W_2b40c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b410 : bv 32 := 0x00b500a3.
Lemma F_2b410 : fetch_word Ubsan.M.loaded_segments (0x2b410 : word) = Some W_2b410.
Proof. vm_refl. Qed.
Lemma D_2b410 : decode_any W_2b410 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b414 : bv 32 := 0x00b50123.
Lemma F_2b414 : fetch_word Ubsan.M.loaded_segments (0x2b414 : word) = Some W_2b414.
Proof. vm_refl. Qed.
Lemma D_2b414 : decode_any W_2b414 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b418 : bv 32 := 0x00700713.
Lemma F_2b418 : fetch_word Ubsan.M.loaded_segments (0x2b418 : word) = Some W_2b418.
Proof. vm_refl. Qed.
Lemma D_2b418 : decode_any W_2b418 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b41c : bv 32 := 0xfeb68ea3.
Lemma F_2b41c : fetch_word Ubsan.M.loaded_segments (0x2b41c : word) = Some W_2b41c.
Proof. vm_refl. Qed.
Lemma D_2b41c : decode_any W_2b41c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b420 : bv 32 := 0xfeb68f23.
Lemma F_2b420 : fetch_word Ubsan.M.loaded_segments (0x2b420 : word) = Some W_2b420.
Proof. vm_refl. Qed.
Lemma D_2b420 : decode_any W_2b420 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b424 : bv 32 := 0x0ce66463.
Lemma F_2b424 : fetch_word Ubsan.M.loaded_segments (0x2b424 : word) = Some W_2b424.
Proof. vm_refl. Qed.
Lemma D_2b424 : decode_any W_2b424 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b428 : bv 32 := 0x00b501a3.
Lemma F_2b428 : fetch_word Ubsan.M.loaded_segments (0x2b428 : word) = Some W_2b428.
Proof. vm_refl. Qed.
Lemma D_2b428 : decode_any W_2b428 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b42c : bv 32 := 0x00900793.
Lemma F_2b42c : fetch_word Ubsan.M.loaded_segments (0x2b42c : word) = Some W_2b42c.
Proof. vm_refl. Qed.
Lemma D_2b42c : decode_any W_2b42c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b430 : bv 32 := 0xfeb68e23.
Lemma F_2b430 : fetch_word Ubsan.M.loaded_segments (0x2b430 : word) = Some W_2b430.
Proof. vm_refl. Qed.
Lemma D_2b430 : decode_any W_2b430 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b434 : bv 32 := 0x0af66c63.
Lemma F_2b434 : fetch_word Ubsan.M.loaded_segments (0x2b434 : word) = Some W_2b434.
Proof. vm_refl. Qed.
Lemma D_2b434 : decode_any W_2b434 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b438 : bv 32 := 0x40a006bb.
Lemma F_2b438 : fetch_word Ubsan.M.loaded_segments (0x2b438 : word) = Some W_2b438.
Proof. vm_refl. Qed.
Lemma D_2b438 : decode_any W_2b438 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b43c : bv 32 := 0x03859813.
Lemma F_2b43c : fetch_word Ubsan.M.loaded_segments (0x2b43c : word) = Some W_2b43c.
Proof. vm_refl. Qed.
Lemma D_2b43c : decode_any W_2b43c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b440 : bv 32 := 0x101015b7.
Lemma F_2b440 : fetch_word Ubsan.M.loaded_segments (0x2b440 : word) = Some W_2b440.
Proof. vm_refl. Qed.
Lemma D_2b440 : decode_any W_2b440 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b444 : bv 32 := 0x0036f693.
Lemma F_2b444 : fetch_word Ubsan.M.loaded_segments (0x2b444 : word) = Some W_2b444.
Proof. vm_refl. Qed.
Lemma D_2b444 : decode_any W_2b444 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b448 : bv 32 := 0x00459713.
Lemma F_2b448 : fetch_word Ubsan.M.loaded_segments (0x2b448 : word) = Some W_2b448.
Proof. vm_refl. Qed.
Lemma D_2b448 : decode_any W_2b448 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b44c : bv 32 := 0x40d60633.
Lemma F_2b44c : fetch_word Ubsan.M.loaded_segments (0x2b44c : word) = Some W_2b44c.
Proof. vm_refl. Qed.
Lemma D_2b44c : decode_any W_2b44c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b450 : bv 32 := 0x00d505b3.
Lemma F_2b450 : fetch_word Ubsan.M.loaded_segments (0x2b450 : word) = Some W_2b450.
Proof. vm_refl. Qed.
Lemma D_2b450 : decode_any W_2b450 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b454 : bv 32 := 0x10070693.
Lemma F_2b454 : fetch_word Ubsan.M.loaded_segments (0x2b454 : word) = Some W_2b454.
Proof. vm_refl. Qed.
Lemma D_2b454 : decode_any W_2b454 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b458 : bv 32 := 0xffc67713.
Lemma F_2b458 : fetch_word Ubsan.M.loaded_segments (0x2b458 : word) = Some W_2b458.
Proof. vm_refl. Qed.
Lemma D_2b458 : decode_any W_2b458 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b45c : bv 32 := 0x02d83633.
Lemma F_2b45c : fetch_word Ubsan.M.loaded_segments (0x2b45c : word) = Some W_2b45c.
Proof. vm_refl. Qed.
Lemma D_2b45c : decode_any W_2b45c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b460 : bv 32 := 0x00c5a023.
Lemma F_2b460 : fetch_word Ubsan.M.loaded_segments (0x2b460 : word) = Some W_2b460.
Proof. vm_refl. Qed.
Lemma D_2b460 : decode_any W_2b460 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b464 : bv 32 := 0x00e586b3.
Lemma F_2b464 : fetch_word Ubsan.M.loaded_segments (0x2b464 : word) = Some W_2b464.
Proof. vm_refl. Qed.
Lemma D_2b464 : decode_any W_2b464 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b468 : bv 32 := 0xfec6ae23.
Lemma F_2b468 : fetch_word Ubsan.M.loaded_segments (0x2b468 : word) = Some W_2b468.
Proof. vm_refl. Qed.
Lemma D_2b468 : decode_any W_2b468 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b46c : bv 32 := 0x08f76063.
Lemma F_2b46c : fetch_word Ubsan.M.loaded_segments (0x2b46c : word) = Some W_2b46c.
Proof. vm_refl. Qed.
Lemma D_2b46c : decode_any W_2b46c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b470 : bv 32 := 0x00c5a223.
Lemma F_2b470 : fetch_word Ubsan.M.loaded_segments (0x2b470 : word) = Some W_2b470.
Proof. vm_refl. Qed.
Lemma D_2b470 : decode_any W_2b470 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b474 : bv 32 := 0x00c5a423.
Lemma F_2b474 : fetch_word Ubsan.M.loaded_segments (0x2b474 : word) = Some W_2b474.
Proof. vm_refl. Qed.
Lemma D_2b474 : decode_any W_2b474 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b478 : bv 32 := 0x01900793.
Lemma F_2b478 : fetch_word Ubsan.M.loaded_segments (0x2b478 : word) = Some W_2b478.
Proof. vm_refl. Qed.
Lemma D_2b478 : decode_any W_2b478 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b47c : bv 32 := 0xfec6aa23.
Lemma F_2b47c : fetch_word Ubsan.M.loaded_segments (0x2b47c : word) = Some W_2b47c.
Proof. vm_refl. Qed.
Lemma D_2b47c : decode_any W_2b47c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b480 : bv 32 := 0xfec6ac23.
Lemma F_2b480 : fetch_word Ubsan.M.loaded_segments (0x2b480 : word) = Some W_2b480.
Proof. vm_refl. Qed.
Lemma D_2b480 : decode_any W_2b480 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b484 : bv 32 := 0x06f76463.
Lemma F_2b484 : fetch_word Ubsan.M.loaded_segments (0x2b484 : word) = Some W_2b484.
Proof. vm_refl. Qed.
Lemma D_2b484 : decode_any W_2b484 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b488 : bv 32 := 0x00c5a623.
Lemma F_2b488 : fetch_word Ubsan.M.loaded_segments (0x2b488 : word) = Some W_2b488.
Proof. vm_refl. Qed.
Lemma D_2b488 : decode_any W_2b488 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b48c : bv 32 := 0x00c5a823.
Lemma F_2b48c : fetch_word Ubsan.M.loaded_segments (0x2b48c : word) = Some W_2b48c.
Proof. vm_refl. Qed.
Lemma D_2b48c : decode_any W_2b48c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b490 : bv 32 := 0x00c5aa23.
Lemma F_2b490 : fetch_word Ubsan.M.loaded_segments (0x2b490 : word) = Some W_2b490.
Proof. vm_refl. Qed.
Lemma D_2b490 : decode_any W_2b490 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b494 : bv 32 := 0x00c5ac23.
Lemma F_2b494 : fetch_word Ubsan.M.loaded_segments (0x2b494 : word) = Some W_2b494.
Proof. vm_refl. Qed.
Lemma D_2b494 : decode_any W_2b494 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b498 : bv 32 := 0x0045f793.
Lemma F_2b498 : fetch_word Ubsan.M.loaded_segments (0x2b498 : word) = Some W_2b498.
Proof. vm_refl. Qed.
Lemma D_2b498 : decode_any W_2b498 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b49c : bv 32 := 0x02000813.
Lemma F_2b49c : fetch_word Ubsan.M.loaded_segments (0x2b49c : word) = Some W_2b49c.
Proof. vm_refl. Qed.
Lemma D_2b49c : decode_any W_2b49c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4a0 : bv 32 := 0x01878793.
Lemma F_2b4a0 : fetch_word Ubsan.M.loaded_segments (0x2b4a0 : word) = Some W_2b4a0.
Proof. vm_refl. Qed.
Lemma D_2b4a0 : decode_any W_2b4a0 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4a4 : bv 32 := 0x40f70733.
Lemma F_2b4a4 : fetch_word Ubsan.M.loaded_segments (0x2b4a4 : word) = Some W_2b4a4.
Proof. vm_refl. Qed.
Lemma D_2b4a4 : decode_any W_2b4a4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4a8 : bv 32 := 0xfec6a223.
Lemma F_2b4a8 : fetch_word Ubsan.M.loaded_segments (0x2b4a8 : word) = Some W_2b4a8.
Proof. vm_refl. Qed.
Lemma D_2b4a8 : decode_any W_2b4a8 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4ac : bv 32 := 0xfec6a423.
Lemma F_2b4ac : fetch_word Ubsan.M.loaded_segments (0x2b4ac : word) = Some W_2b4ac.
Proof. vm_refl. Qed.
Lemma D_2b4ac : decode_any W_2b4ac = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4b0 : bv 32 := 0xfec6a623.
Lemma F_2b4b0 : fetch_word Ubsan.M.loaded_segments (0x2b4b0 : word) = Some W_2b4b0.
Proof. vm_refl. Qed.
Lemma D_2b4b0 : decode_any W_2b4b0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4b4 : bv 32 := 0xfec6a823.
Lemma F_2b4b4 : fetch_word Ubsan.M.loaded_segments (0x2b4b4 : word) = Some W_2b4b4.
Proof. vm_refl. Qed.
Lemma D_2b4b4 : decode_any W_2b4b4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4b8 : bv 32 := 0x03076a63.
Lemma F_2b4b8 : fetch_word Ubsan.M.loaded_segments (0x2b4b8 : word) = Some W_2b4b8.
Proof. vm_refl. Qed.
Lemma D_2b4b8 : decode_any W_2b4b8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4bc : bv 32 := 0x02061613.
Lemma F_2b4bc : fetch_word Ubsan.M.loaded_segments (0x2b4bc : word) = Some W_2b4bc.
Proof. vm_refl. Qed.
Lemma D_2b4bc : decode_any W_2b4bc = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4c0 : bv 32 := 0x00f585b3.
Lemma F_2b4c0 : fetch_word Ubsan.M.loaded_segments (0x2b4c0 : word) = Some W_2b4c0.
Proof. vm_refl. Qed.
Lemma D_2b4c0 : decode_any W_2b4c0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4c4 : bv 32 := 0x02065693.
Lemma F_2b4c4 : fetch_word Ubsan.M.loaded_segments (0x2b4c4 : word) = Some W_2b4c4.
Proof. vm_refl. Qed.
Lemma D_2b4c4 : decode_any W_2b4c4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4c8 : bv 32 := 0x00d66633.
Lemma F_2b4c8 : fetch_word Ubsan.M.loaded_segments (0x2b4c8 : word) = Some W_2b4c8.
Proof. vm_refl. Qed.
Lemma D_2b4c8 : decode_any W_2b4c8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4cc : bv 32 := 0x01f00693.
Lemma F_2b4cc : fetch_word Ubsan.M.loaded_segments (0x2b4cc : word) = Some W_2b4cc.
Proof. vm_refl. Qed.
Lemma D_2b4cc : decode_any W_2b4cc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4d0 : bv 32 := 0x00c5b023.
Lemma F_2b4d0 : fetch_word Ubsan.M.loaded_segments (0x2b4d0 : word) = Some W_2b4d0.
Proof. vm_refl. Qed.
Lemma D_2b4d0 : decode_any W_2b4d0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4d4 : bv 32 := 0x00c5b423.
Lemma F_2b4d4 : fetch_word Ubsan.M.loaded_segments (0x2b4d4 : word) = Some W_2b4d4.
Proof. vm_refl. Qed.
Lemma D_2b4d4 : decode_any W_2b4d4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4d8 : bv 32 := 0x00c5b823.
Lemma F_2b4d8 : fetch_word Ubsan.M.loaded_segments (0x2b4d8 : word) = Some W_2b4d8.
Proof. vm_refl. Qed.
Lemma D_2b4d8 : decode_any W_2b4d8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4dc : bv 32 := 0x00c5bc23.
Lemma F_2b4dc : fetch_word Ubsan.M.loaded_segments (0x2b4dc : word) = Some W_2b4dc.
Proof. vm_refl. Qed.
Lemma D_2b4dc : decode_any W_2b4dc = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4e0 : bv 32 := 0xfe070713.
Lemma F_2b4e0 : fetch_word Ubsan.M.loaded_segments (0x2b4e0 : word) = Some W_2b4e0.
Proof. vm_refl. Qed.
Lemma D_2b4e0 : decode_any W_2b4e0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4e4 : bv 32 := 0x02058593.
Lemma F_2b4e4 : fetch_word Ubsan.M.loaded_segments (0x2b4e4 : word) = Some W_2b4e4.
Proof. vm_refl. Qed.
Lemma D_2b4e4 : decode_any W_2b4e4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4e8 : bv 32 := 0xfee6e4e3.
Lemma F_2b4e8 : fetch_word Ubsan.M.loaded_segments (0x2b4e8 : word) = Some W_2b4e8.
Proof. vm_refl. Qed.
Lemma D_2b4e8 : decode_any W_2b4e8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b4ec : bv 32 := 0x00008067.
Lemma F_2b4ec : fetch_word Ubsan.M.loaded_segments (0x2b4ec : word) = Some W_2b4ec.
Proof. vm_refl. Qed.
Lemma D_2b4ec : decode_any W_2b4ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7bc : bv 32 := 0xfe010113.
Lemma F_2b7bc : fetch_word Ubsan.M.loaded_segments (0x2b7bc : word) = Some W_2b7bc.
Proof. vm_refl. Qed.
Lemma D_2b7bc : decode_any W_2b7bc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7c0 : bv 32 := 0x00113c23.
Lemma F_2b7c0 : fetch_word Ubsan.M.loaded_segments (0x2b7c0 : word) = Some W_2b7c0.
Proof. vm_refl. Qed.
Lemma D_2b7c0 : decode_any W_2b7c0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7c4 : bv 32 := 0x00813823.
Lemma F_2b7c4 : fetch_word Ubsan.M.loaded_segments (0x2b7c4 : word) = Some W_2b7c4.
Proof. vm_refl. Qed.
Lemma D_2b7c4 : decode_any W_2b7c4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7c8 : bv 32 := 0x00913423.
Lemma F_2b7c8 : fetch_word Ubsan.M.loaded_segments (0x2b7c8 : word) = Some W_2b7c8.
Proof. vm_refl. Qed.
Lemma D_2b7c8 : decode_any W_2b7c8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7cc : bv 32 := 0x00058413.
Lemma F_2b7cc : fetch_word Ubsan.M.loaded_segments (0x2b7cc : word) = Some W_2b7cc.
Proof. vm_refl. Qed.
Lemma D_2b7cc : decode_any W_2b7cc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7d0 : bv 32 := 0x00050493.
Lemma F_2b7d0 : fetch_word Ubsan.M.loaded_segments (0x2b7d0 : word) = Some W_2b7d0.
Proof. vm_refl. Qed.
Lemma D_2b7d0 : decode_any W_2b7d0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7d4 : bv 32 := 0x00000593.
Lemma F_2b7d4 : fetch_word Ubsan.M.loaded_segments (0x2b7d4 : word) = Some W_2b7d4.
Proof. vm_refl. Qed.
Lemma D_2b7d4 : decode_any W_2b7d4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7d8 : bv 32 := 0x00040613.
Lemma F_2b7d8 : fetch_word Ubsan.M.loaded_segments (0x2b7d8 : word) = Some W_2b7d8.
Proof. vm_refl. Qed.
Lemma D_2b7d8 : decode_any W_2b7d8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7dc : bv 32 := 0xf1cff0ef.
Lemma F_2b7dc : fetch_word Ubsan.M.loaded_segments (0x2b7dc : word) = Some W_2b7dc.
Proof. vm_refl. Qed.
Lemma D_2b7dc : decode_any W_2b7dc = Some (Jal 1 2094876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7e0 : bv 32 := 0x00050463.
Lemma F_2b7e0 : fetch_word Ubsan.M.loaded_segments (0x2b7e0 : word) = Some W_2b7e0.
Proof. vm_refl. Qed.
Lemma D_2b7e0 : decode_any W_2b7e0 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7e4 : bv 32 := 0x40950433.
Lemma F_2b7e4 : fetch_word Ubsan.M.loaded_segments (0x2b7e4 : word) = Some W_2b7e4.
Proof. vm_refl. Qed.
Lemma D_2b7e4 : decode_any W_2b7e4 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7e8 : bv 32 := 0x00040513.
Lemma F_2b7e8 : fetch_word Ubsan.M.loaded_segments (0x2b7e8 : word) = Some W_2b7e8.
Proof. vm_refl. Qed.
Lemma D_2b7e8 : decode_any W_2b7e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7ec : bv 32 := 0x01813083.
Lemma F_2b7ec : fetch_word Ubsan.M.loaded_segments (0x2b7ec : word) = Some W_2b7ec.
Proof. vm_refl. Qed.
Lemma D_2b7ec : decode_any W_2b7ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7f0 : bv 32 := 0x01013403.
Lemma F_2b7f0 : fetch_word Ubsan.M.loaded_segments (0x2b7f0 : word) = Some W_2b7f0.
Proof. vm_refl. Qed.
Lemma D_2b7f0 : decode_any W_2b7f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7f4 : bv 32 := 0x00813483.
Lemma F_2b7f4 : fetch_word Ubsan.M.loaded_segments (0x2b7f4 : word) = Some W_2b7f4.
Proof. vm_refl. Qed.
Lemma D_2b7f4 : decode_any W_2b7f4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7f8 : bv 32 := 0x02010113.
Lemma F_2b7f8 : fetch_word Ubsan.M.loaded_segments (0x2b7f8 : word) = Some W_2b7f8.
Proof. vm_refl. Qed.
Lemma D_2b7f8 : decode_any W_2b7f8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b7fc : bv 32 := 0x00008067.
Lemma F_2b7fc : fetch_word Ubsan.M.loaded_segments (0x2b7fc : word) = Some W_2b7fc.
Proof. vm_refl. Qed.
Lemma D_2b7fc : decode_any W_2b7fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b800 : bv 32 := 0x00037597.
Lemma F_2b800 : fetch_word Ubsan.M.loaded_segments (0x2b800 : word) = Some W_2b800.
Proof. vm_refl. Qed.
Lemma D_2b800 : decode_any W_2b800 = Some (Auipc 11 55, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b804 : bv 32 := 0xf8b58683.
Lemma F_2b804 : fetch_word Ubsan.M.loaded_segments (0x2b804 : word) = Some W_2b804.
Proof. vm_refl. Qed.
Lemma D_2b804 : decode_any W_2b804 = Some (Load SZ1 true 13 11 3979, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b808 : bv 32 := 0x1e068863.
Lemma F_2b808 : fetch_word Ubsan.M.loaded_segments (0x2b808 : word) = Some W_2b808.
Proof. vm_refl. Qed.
Lemma D_2b808 : decode_any W_2b808 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b9f8 : bv 32 := 0x00008067.
Lemma F_2b9f8 : fetch_word Ubsan.M.loaded_segments (0x2b9f8 : word) = Some W_2b9f8.
Proof. vm_refl. Qed.
Lemma D_2b9f8 : decode_any W_2b9f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ba88 : bv 32 := 0x00052583.
Lemma F_2ba88 : fetch_word Ubsan.M.loaded_segments (0x2ba88 : word) = Some W_2ba88.
Proof. vm_refl. Qed.
Lemma D_2ba88 : decode_any W_2ba88 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ba8c : bv 32 := 0x0005c463.
Lemma F_2ba8c : fetch_word Ubsan.M.loaded_segments (0x2ba8c : word) = Some W_2ba8c.
Proof. vm_refl. Qed.
Lemma D_2ba8c : decode_any W_2ba8c = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ba90 : bv 32 := 0x00008067.
Lemma F_2ba90 : fetch_word Ubsan.M.loaded_segments (0x2ba90 : word) = Some W_2ba90.
Proof. vm_refl. Qed.
Lemma D_2ba90 : decode_any W_2ba90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End DU_cg5g.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_aux_read_byte : forall ms k a,
  read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k.
Proof.
  intros ms. induction k as [|k IH]; intro a; [reflexivity|].
  cbn [read_bytes_aux ms_read_bytes_aux].
  destruct (ms_read_byte ms a) as [b|]; [rewrite IH|]; reflexivity.
Qed.

Lemma read_bytes_map_read_byte : forall ms a len,
  read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len.
Proof. intros. rewrite read_bytes_map_eq. unfold ms_read_bytes.
  apply read_aux_read_byte. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma apply_effect_no_write : forall ms r,
  apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof.
  intros ms r. unfold apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
  reflexivity.
Qed.

Lemma apply_effect_copyins_no_write : forall ms r copyins,
  apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r.
Proof.
  intros ms r copyins. unfold with_copyins, apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_unmaps apply_zeros apply_copies apply_writes].
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

(* [comment removed for export] *)
Definition buf_modeled (b : list byte) : Prop :=
  (Z.of_nat (length b) <= rw_bytes_max)%Z.

Definition bufs_modeled (bufs : list (list byte)) : Prop :=
  Forall buf_modeled bufs.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
  is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
  induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents_ch (ch : word) (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv ch) buf ++ wevents_ch ch rest
  end.

Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
    (1 <= n)%nat -> (n <= length buf)%nat ->
    wpick ch bufs tr ->
    wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit ms' bufs code ->
    to_wexit ms bufs code.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    msteps ms' ms'' ->
    msteps ms ms''.

(* [comment removed for export] *)

Lemma msteps_trans : forall ms ms' ms'',
  msteps ms ms' -> msteps ms' ms'' -> msteps ms ms''.
Proof.
  intros ms ms' ms'' H; induction H; [auto|].
  intro H2. eapply mst_step; eauto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false.

(* [comment removed for export] *)

(* [comment removed for export] *)


Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit_ch ms' bufs code ->
    to_wexit_ch ms bufs code.

(* [comment removed for export] *)

Hypothesis Hfd32 : fd32 fd = fd.


End WithSegsCh.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

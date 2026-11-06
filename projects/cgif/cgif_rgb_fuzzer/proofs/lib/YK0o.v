(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK16.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Definition is_exit_no (no : word) : Prop :=
bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.
Lemma syscall_spec_exit : forall i m o,
is_exit_no (in_sysno i) ->
syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.
Lemma exit_dispatch_ok : forall i m,
is_exit_no (in_sysno i) ->
syscall_spec i m
(Ok (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
[], []. repeat split; reflexivity.
Qed.
Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
is_exit_no (in_sysno i) ->
syscall_spec i m (Ok eff m' evs) ->
eff = mkEffect (Z_to_bv 64 0) [] [] /\
m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
intros i m eff m' evs Hno Hspec.
apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.
Lemma exit_dispatch_no_unmodeled : forall i m,
is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
intros i m Hno Hspec.
apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
sys_destruct.
Qed.
Lemma in_arg0_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_sysno_sys_input : forall segs ms x8,
in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Section a.
Variable segs : list Segment.
Variable code : word.
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




Lemma sstep_instr_inv : forall ms model ms' evs st,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
inversion Hss; subst.
-
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; inversion H; subst end.
split; reflexivity.
-
match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; discriminate end.
-
match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
rewrite Hstep in H; discriminate end.
-   congruence.
-   congruence.
-   congruence.
-   congruence.
-   congruence.
Qed.
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
-
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
-
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
-
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
-
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
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
H2 : ms_svc_pending ms = Some ?x |- _ =>
eapply exit_dispatch_no_unmodeled; [| exact H3];
rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
end.
Qed.
Lemma star_halted_nil : forall c tr c',
m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
- split; reflexivity.
- exfalso. destruct c as [ms model]. cbn in Hh.
inversion Hss; subst; cbn in Hh; congruence.
Qed.
Definition exit_post (fs : Fs.Fs) : post :=
fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
/\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.



Definition on_path (c : config) : Prop :=
(m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
to_exit (cfg_ms c))
\/ m_halted (cfg_model c) <> None.




End a.
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









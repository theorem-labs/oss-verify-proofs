(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16.
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
Lemma sim_c_to_exit : forall fuel ms, sim_c fuel ms = true -> to_exit ms.
Proof.
induction fuel as [|fuel IH]; intros ms H; [discriminate|].
cbn in H. destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
- apply andb_true_iff in H as [Hx8 Hgpr].
apply bv_eqb_eq in Hgpr.
eapply te_here; eauto.
apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
[left|right]; exact H.
- destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
[|discriminate|discriminate].
eapply te_step; eauto.
Qed.
Lemma sim_step : forall fuel ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
sim_c fuel ms' = true ->
sim_c (S fuel) ms = true.
Proof.
intros fuel ms ms' Hsvc Hstep Hrec.
cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hstep. exact Hrec.
Qed.
Lemma sim_c_exit_now : forall fuel ms x8,
ms_svc_pending ms = Some x8 ->
((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z) = true ->
bv_eqb (ms_gpr ms 0) code = true ->
sim_c (S fuel) ms = true.
Proof.
intros fuel ms x8 Hsvc Hx8 Hcode.
cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hx8. cbn [andb]. exact Hcode.
Qed.
Lemma sim_ecall_exit : forall fuel ms,
ms_svc_pending ms = None ->
fetch_word segs (ms_pc ms) = Some 0x73 ->
((bv_unsigned (ms_reg ms 17) =? 93)%Z || (bv_unsigned (ms_reg ms 17) =? 94)%Z) = true ->
bv_eqb (ms_gpr ms 0) code = true ->
sim_c (S (S fuel)) ms = true.
Proof.
intros fuel ms Hsvc Hfetch Hcheck Hcode.
set (ms1 := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
ms_mem := ms_mem ms; ms_rom := ms_rom ms |}).
apply (sim_step (S fuel) ms ms1 Hsvc).
- change (drop_access_report (step_accesses segs ms) = MachineOk ms1).
unfold step_accesses. rewrite Hfetch. unfold ms1. reflexivity.
- apply (sim_c_exit_now fuel ms1 (ms_reg ms 17)).
+ subst ms1. reflexivity.
+ exact Hcheck.
+ exact Hcode.
Qed.
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
Lemma to_exit_exec : forall ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
to_exit ms ->
OmniRun.exec segs (mkCfg ms model) (exit_post (m_fs model)).
Proof.
intros ms model Hh Hlazy Hte.
induction Hte as [ms x8 Hsvc Hx8 Hgpr | ms ms' Hsvc Hstep Hte IH].
-
apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold exit_post. cbn beta. rewrite app_nil_r, Hgpr. split; [reflexivity |].
cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact IH |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma to_exit_star_only : forall ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
to_exit ms ->
forall tr c, star segs (mkCfg ms model) tr c ->
tr = [] \/ tr = [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)].
Proof.
intros ms model Hh Hlazy Hte tr c Hstar.
destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_exit_exec ms model Hh Hlazy Hte) Hstar))
as (tr' & o & _ & HQ).
unfold exit_post in HQ. cbn beta in HQ. destruct HQ as (Heq & _).
destruct (app_eq_unit _ _ Heq) as [(-> & _) | (-> & _)]; [left | right]; reflexivity.
Qed.
Lemma to_exit_star_admits : forall ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
to_exit ms ->
exists c, star segs (mkCfg ms model)
[ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] c.
Proof.
intros ms model Hh Hlazy Hte.
destruct (exec_realizes _ _ _ (to_exit_exec ms model Hh Hlazy Hte))
as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
exists c'. exact Hstar.
Qed.
Definition on_path (c : config) : Prop :=
(m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
to_exit (cfg_ms c))
\/ m_halted (cfg_model c) <> None.
Lemma on_path_step : forall c evs c',
on_path c -> sstep segs c evs (SNext c') -> on_path c'.
Proof.
intros [ms model] evs [ms' model'] Hop Hss.
unfold on_path in *; cbn in Hop |- *.
destruct Hop as [[Hh [Hlazy Hte]] | Hh].
- destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
+
destruct (sstep_exit_inv ms0 model x8 evs (SNext (mkCfg ms' model'))
Hh Hsvc Hx8 Hss) as [_ Hc'].
inversion Hc'; subst. right. cbn. discriminate.
+
destruct (sstep_instr_inv ms0 model ms0' evs (SNext (mkCfg ms' model'))
Hlazy Hsvc Hstep Hss) as [_ Hc'].
inversion Hc'; subst. left. repeat split; assumption.
-
exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.
Lemma on_path_no_error : forall c evs, on_path c -> ~ sstep segs c evs SError.
Proof.
intros [ms model] evs Hop Hss.
unfold on_path in *; cbn in Hop.
destruct Hop as [[Hh [Hlazy Hte]] | Hh].
- destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
+ destruct (sstep_exit_inv ms0 model x8 evs SError Hh Hsvc Hx8 Hss) as [_ Hc'].
discriminate.
+ destruct (sstep_instr_inv ms0 model ms0' evs SError Hlazy Hsvc Hstep Hss) as [_ Hc'].
discriminate.
- inversion Hss; subst; cbn in Hh; congruence.
Qed.
Lemma star_on_path : forall c tr c',
on_path c -> star segs c tr c' -> on_path c'.
Proof. exact (star_inv segs on_path on_path_step). Qed.
Lemma to_exit_no_error : forall ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
to_exit ms ->
~ reaches_error segs (mkCfg ms model).
Proof.
intros ms model Hh Hlazy Hte. apply exec_no_error.
eapply exec_conseq; [exact (to_exit_exec ms model Hh Hlazy Hte) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
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
Lemma stm_at (sp : word) (bytes : list byte) (addr : word) (i : nat) :
(i < length bytes)%nat ->
bv_unsigned addr = (bv_unsigned sp + Z.of_nat i)%Z ->
stack_to_mem sp bytes addr = nth_error bytes i.
Proof.
intros Hi Haddr. unfold stack_to_mem. rewrite Haddr. cbv beta zeta.
destruct (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) eqn:E1.
2: { apply Z.leb_gt in E1; lia. }
replace (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)%Z with (Z.of_nat i) by lia.
destruct (Z.ltb (Z.of_nat i) (Z.of_nat (length bytes))) eqn:E2.
- rewrite Nat2Z.id. reflexivity.
- apply Z.ltb_ge in E2. lia.
Qed.
Lemma build_stack_starts_with_argc :
forall ph sp argv envp uid hw rnd,
exists rest,
build_stack_bytes ph sp argv envp uid hw rnd =
word_le8 (nat_to_word (length argv)) ++ rest.
Proof.
intros ph sp argv envp uid hw rnd. unfold build_stack_bytes, len_word, nat_to_word.
destruct (string_addrs _ argv) as [? ?]. destruct (string_addrs _ envp) as [? ?].
eexists. exact (eq_sym (app_assoc _ _ _)).
Qed.
Lemma word_le8_length : forall v, length (word_le8 v) = 8%nat.
Proof. intro v. reflexivity. Qed.
Lemma build_stack_min_length : forall ph sp argv envp uid hw rnd,
(8 <= length (build_stack_bytes ph sp argv envp uid hw rnd))%nat.
Proof.
intros ph sp argv envp uid hw rnd.
destruct (build_stack_starts_with_argc ph sp argv envp uid hw rnd) as [rest Hr].
rewrite Hr, length_app, word_le8_length. lia.
Qed.
Lemma init_first8 :
forall segs init_pc ph init_sp init_rnd argv envp addr i uid hw, (i < 8)%nat ->
bv_unsigned addr = (bv_unsigned init_sp + Z.of_nat i)%Z ->
ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) addr =
nth_error (word_le8 (nat_to_word (length argv))) i.
Proof.
intros segs init_pc ph init_sp init_rnd argv envp addr i uid hw Hi Haddr.
assert (Hstk : stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr
= nth_error (word_le8 (nat_to_word (length argv))) i).
{ rewrite stack_to_mem_image_in_block
by (pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd);
unfold entry_block_top; lia).
rewrite (stm_at init_sp _ addr i);
[ | pose proof (build_stack_min_length ph init_sp argv envp uid hw init_rnd); lia
| exact Haddr ].
destruct (build_stack_starts_with_argc ph init_sp argv envp uid hw init_rnd) as [rest Hr].
rewrite Hr. apply nth_error_app1. rewrite word_le8_length. lia. }
change (ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) addr)
with (match stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr with
| Some b => Some b
| None =>
if andb (Z.leb (bv_unsigned init_sp - stack_max_size)
(bv_unsigned addr))
(Z.ltb (bv_unsigned addr) (bv_unsigned init_sp))
then Some (Z_to_bv 8 0) else None
end).
rewrite Hstk.
destruct (nth_error (word_le8 (nat_to_word (length argv))) i) eqn:E; [reflexivity|].
apply nth_error_None in E. rewrite word_le8_length in E. lia.
Qed.
Lemma actual_mem_is_overlay :
forall segs init_pc ph init_sp init_rnd argv envp uid hw,
ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw) =
overlay_argc_bytes init_sp (length argv)
(ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)).
Proof.
intros segs init_pc ph init_sp init_rnd argv envp uid hw.
apply functional_extensionality. intro addr.
unfold overlay_argc_bytes.
destruct ((bv_unsigned addr =? bv_unsigned init_sp)%Z) eqn:E0;
[ apply Z.eqb_eq in E0;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 0 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 1)%Z) eqn:E1;
[ apply Z.eqb_eq in E1;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 1 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 2)%Z) eqn:E2;
[ apply Z.eqb_eq in E2;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 2 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 3)%Z) eqn:E3;
[ apply Z.eqb_eq in E3;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 3 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 4)%Z) eqn:E4;
[ apply Z.eqb_eq in E4;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 4 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 5)%Z) eqn:E5;
[ apply Z.eqb_eq in E5;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 5 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 6)%Z) eqn:E6;
[ apply Z.eqb_eq in E6;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 6 uid hw); lia | ].
destruct ((bv_unsigned addr =? bv_unsigned init_sp + 7)%Z) eqn:E7;
[ apply Z.eqb_eq in E7;
apply (init_first8 segs init_pc ph init_sp init_rnd argv envp addr 7 uid hw); lia | ].
reflexivity.
Qed.
Lemma machine_state_eta : forall ms : machine_state,
ms = {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Proof. intros []; reflexivity. Qed.
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
Lemma init_eq_enum_state :
forall segs init_pc ph init_sp init_rnd argv envp uid hw,
init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw =
enum_state segs init_pc ph init_sp init_rnd (length argv)
(ms_mem (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)) uid hw.
Proof.
intros segs init_pc ph init_sp init_rnd argv envp uid hw. unfold enum_state.
rewrite (machine_state_eta (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw)) at 1.
f_equal; try reflexivity. apply actual_mem_is_overlay.
Qed.
Lemma exit_omni_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
(exit_post code (in_fs inp)).
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F Hsim.
cbn [omni_run]. unfold init_config.
exact (to_exit_exec segs code
(init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(init_model (segments_reserved segs) brk0 mb sp lim inp)
eq_refl eq_refl (sim_c_to_exit segs code F _ Hsim)).
Qed.
Lemma exit_obs_iff : forall segs pc ph sp brk0 mb rnd lim code inp F,
sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
<-> is_prefix tr [ExitEv (bv_and code (Z_to_bv 64 255)) (in_fs inp)].
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F Hsim tr.
apply exec_obs_iff.
eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.
Lemma exit_no_error_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply exec_no_error.
eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma exit_must_exit_with : forall segs pc ph sp brk0 mb rnd lim code inp F,
sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
must_exit_with (bv_and code (Z_to_bv 64 255)) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply must_exit_with_iff.
eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
intros tr o (_ & Hx). exact Hx.
Qed.
Lemma exit_omni_run_code_unique : forall segs pc ph sp brk0 mb rnd lim code inp F code',
sim_c segs code F (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
code' = bv_and code (Z_to_bv 64 255).
Proof.
intros segs pc ph sp brk0 mb rnd lim code inp F code' Hsim Hex.
pose proof (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) as Hrun.
cbn [omni_run] in Hrun, Hex.
destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.
Lemma exit_omni_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA,
sim_c source_segs code FR
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
sim_c target_segs code FA
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA
Hsource Htarget.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource) |].
intros tr o (_ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource tr).
rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget).
Qed.
Lemma exit_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA,
sim_c source_segs code FR
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
sim_c target_segs code FA
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) = true ->
Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
(run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
Hsource Htarget.
split.
{ apply no_error_run_modeled.
apply (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource). }
right. split.
- intro tr. cbn.
rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource tr).
rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA Htarget tr).
reflexivity.
- cbn. apply (exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA Htarget).
Qed.

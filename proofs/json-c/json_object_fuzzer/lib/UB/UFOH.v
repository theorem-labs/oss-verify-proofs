(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QSpR QRjH QBxa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QSpR.Mq3 QRjH.Mq0 QBxa.Mq6.
Import UFeQ Udbv.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Ubsan.M.phdrs.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition D_main_cells : list (Z * nat) :=
[(0x77b30%Z, 8%nat); (0x97e98%Z, 8%nat); (0x97ef8%Z, 8%nat); (0x97ec0%Z, 8%nat); (0x97e88%Z, 8%nat); (0x97e80%Z, 8%nat);
(0x97c18%Z, 8%nat); (0x97c20%Z, 8%nat); (0x97c30%Z, 8%nat); (0x97ea0%Z, 8%nat); (0x97eb8%Z, 8%nat);
(0x97c28%Z, 8%nat); (0x97c38%Z, 8%nat); (0x97ea8%Z, 8%nat); (0x97eb0%Z, 8%nat); (0x77c18%Z, 8%nat); (0x77c10%Z, 8%nat);
(0x77bf8%Z, 8%nat); (0x77b38%Z, 8%nat); (0x97e90%Z, 1%nat); (0x77b60%Z, 4%nat); (0x77b58%Z, 4%nat); (0x77bd0%Z, 8%nat);
(0x77bb0%Z, 8%nat); (0x77b40%Z, 8%nat); (0x77b48%Z, 8%nat); (0x77b50%Z, 8%nat); (0x97e70%Z, 4%nat); (0x97e74%Z, 4%nat);
(0x97e71%Z, 1%nat); (0x77bf0%Z, 8%nat); (0x66f30%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x99000)%Z.

Definition djw (P : Prop) : Prop := P.

#[using="Type"] Lemma range_disjoint_djw : forall a n c,
range_disjoint_b a n c = true ->
djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.
End FPGEN1.

Section Facts.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av ev : list (list byte).
Variable tid : word.
Hypothesis Hva : valid_argv av.
Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

Let D := D_main sp0 av ev tid.

#[using="Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

#[using="Type"] Lemma D_main_tid : forall segs,
rdn segs D (Z_to_bv 64 0x77b58) 4 = Some (word_to_le_bytes 4 tid).
Proof.
intros segs. pose proof (u64_range tid). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
Qed.

#[using="Type"] Lemma D_main_guard : forall segs,
rdn segs D (Z_to_bv 64 0x97e70) 8 = Some (word_to_le_bytes 8 ssp_canary).
Proof.
intros segs. pose proof (u64_range tid). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
rewrite ssp_canary_bytes. unfold canary_bytes. apply rdn_guard3; lia.
Qed.

#[using="Hva"] Lemma D_main_pagesize : forall segs,
rdn segs D (Z_to_bv 64 0x97ec0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
Proof.
intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

#[using="Type"] Lemma D_main_self : forall segs,
rdn segs D (Z_to_bv 64 0x77b38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x77b38)).
Proof.
intros segs. pose proof (u64_range tid). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

#[using="Type"] Lemma D_main_canary : forall segs,
rdn segs D (Z_to_bv 64 0x77bf0) 8 = Some (word_to_le_bytes 8 ssp_canary).
Proof.
intros segs. pose proof (u64_range tid). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis ME : main_entry sp0 av ev tid regs mem.

#[using="AMB sp0 av ev Hlo D regs ME"] Lemma main_entry_tid : forall segs,
rdn segs mem (Z_to_bv 64 0x77b58) 4 = Some (word_to_le_bytes 4 tid).
Proof.
intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
Qed.

#[using="sp0 av ev tid Hlo D regs ME"] Lemma main_entry_guard : forall segs,
rdn segs mem (Z_to_bv 64 0x97e70) 8 = Some (word_to_le_bytes 8 ssp_canary).
Proof.
intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
Qed.

End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QwNp QsV0 QsRG Qnhz Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QwNp QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG QRjH QBxa.Mq4 QBxa.Mq0 Q9ox.Mq0 QSpR.Mq3.
Import UFeQ Udbv.
Import ListNotations.
Open Scope bv_scope.

#[local] Existing Instance fp0F.
#[local] Existing Instance fp0C.

Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

Lemma bwd_rz : forall segs model K,
m_halted model = None -> m_vm_lazy model = [] ->
bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.

Section SetTid.
Variable segs : list Segment.

Definition tid_I0 : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

#[using="Type"] Lemma one_tid_ok0 : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

#[using="Type"] Lemma node_set_tid0 : forall ms model x8,
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
m_tid model = None ->
node_ok segs (mkCfg ms model) tid_I0 (fun _ => [])
(fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Htid.
assert (Hchk : forall o, syscall_spec (sys_input segs ms x8) model o <->
exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\ o = Ok (mkEffect t [] []) (with_tid t model) []).
{ intros o. rewrite (syscall_spec_96 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
apply set_tid_fresh_outcome. exact Htid. }
pose (effs := fun i : tid_I0 => mkEffectU (proj1_sig i) [] [] [] [] []).
assert (Enx : forall i : tid_I0,
mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
= mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
{ intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
assert (Hnode : node_ok segs (mkCfg ms model) tid_I0 (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
{ apply (node_family segs ms model x8 tid_I0 effs (fun i => with_tid (proj1_sig i) model) (fun _ => []) _
Hh Hsvc Hchk).
- intros [t Ht]. exists t. split; [exact Ht|reflexivity].
- intros o (t & Ht & ->). exists (exist _ t Ht). reflexivity.
- intros i. exact Hh.
- intros i. exact Hlazy.
- intros i. apply not_spurious_sysno. rewrite in_sysno_sys_input, Hno. vm_compute. intuition discriminate. }
destruct Hnode as [Hn1 Hn2]. split.
- intros i. rewrite Enx. apply Hn1.
- intros e st Hss. destruct (Hn2 e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.

#[using="Type"] Lemma rz_set_tid0 : forall regs (pc : word) mem rom model K w,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
apply (rz_conseq segs _ (t_alt (fun _ : tid_I0 => K)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok0); exact Ht]].
eapply rz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok0)
| eapply node_set_tid0; [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.
End SetTid.

Theorem ref_startup : forall sp brk mbase rnd lim inp K (Hsp : valid_sp sp),
valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
(forall tid regs mem,
(0 < bv_unsigned tid < 2^22)%Z ->
@main_entry (amb_of inp rnd sp Hsp) sp (in_argv inp) (in_envp inp) tid regs mem ->
realizes rsegs (mkCfg (mkst regs (0x20b84 : word) mem (seg_rom rsegs))
(with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
realizes rsegs (init_config rsegs rpc rph sp brk mbase rnd lim inp) K.
Proof.
intros sp brk mbase rnd lim inp K Hsp Hbrk Hva Hve HK.
change (realizes rsegs ?c K)
with ((fun st model => realizes rsegs (mkCfg st model) K) (cfg_ms c) (cfg_model c)).
apply (startup (fun st model => realizes rsegs (mkCfg st model) K)) with (Hsp := Hsp).
- intros model Hh Hlazy. apply bwd_rz; assumption.
- intros regs pc mem model w HF HE Hh Hlazy H17 Htid Hk.
eapply rz_set_tid0; eassumption.
- exact Hva.
- exact Hve.
- exact HK.
Qed.
End Mq1.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEVk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMOs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMOs.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require USPu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import USPu. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UU2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UU2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8LG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8LG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZSc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZSc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UsN4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UsN4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlKb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlKb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U39n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U39n. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U12p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U12p. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ucqj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ucqj.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition sw_regs_but (regs regs' : bvmap 5 word) : Prop :=
getr regs' 2 = getr regs 2 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
/\ getr regs' 21 = getr regs 21
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

#[using="Type"] Lemma sw_c1_eq : forall regs mem rom (k : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
(0 <= k < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x55268 : word) mem rom) (mkst regs' (0x55270 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k Ha0 Hs6 K.
eexists. split.
- stepn F_5348c D_5348c.
stepn F_4f250 D_4f250.
stepn F_4f254 D_4f254.
stepb_tk F_4f258 D_4f258 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_4f284 D_4f284 (0x5526c : word) ltac:(bveq).
stepb_ft F_53490 D_53490 ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

#[using="Type"] Lemma sw_c1_ne : forall regs mem rom (k rem : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
(0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
exists regs',
msteps RSEGS (mkst regs (0x55268 : word) mem rom) (mkst regs' (0x552fc : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k rem Ha0 Hs6 K REM NE.
eexists. split.
- stepn F_5348c D_5348c.
stepn F_4f250 D_4f250.
stepn F_4f254 D_4f254.
stepb_tk F_4f258 D_4f258 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_4f284 D_4f284 (0x5526c : word) ltac:(bveq).
stepb_tk F_53490 D_53490 ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

#[using="Type"] Lemma sw_c2_eq : forall regs mem rom (k : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 k ->
(0 <= k < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x552f0 : word) mem rom) (mkst regs' (0x55270 : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k Ha0 Hs6 K.
eexists. split.
- stepn F_53514 D_53514.
stepn F_4f250 D_4f250.
stepn F_4f254 D_4f254.
stepb_tk F_4f258 D_4f258 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_4f284 D_4f284 (0x552f4 : word) ltac:(bveq).
stepn F_53518 D_53518.
stepb_tk F_5351c D_5351c ltac:(rewrite Ha0, Hs6; apply c_eq_refl).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

#[using="Type"] Lemma sw_c2_ne : forall regs mem rom (k rem : Z),
getr regs 10 = Z_to_bv 64 k -> getr regs 22 = Z_to_bv 64 rem ->
(0 <= k < 2147483648)%Z -> (0 <= rem < 2^64)%Z -> k <> rem ->
exists regs',
msteps RSEGS (mkst regs (0x552f0 : word) mem rom) (mkst regs' (0x552fc : word) mem rom)
/\ getr regs' 10 = Z_to_bv 64 k /\ getr regs' 19 = getr regs 20 /\ getr regs' 20 = getr regs 20
/\ getr regs' 18 = getr regs 18 /\ getr regs' 22 = getr regs 22
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom k rem Ha0 Hs6 K REM NE.
eexists. split.
- stepn F_53514 D_53514.
stepn F_4f250 D_4f250.
stepn F_4f254 D_4f254.
stepb_tk F_4f258 D_4f258 ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; apply Z.ltb_lt; u_norm; lia).
stepret F_4f284 D_4f284 (0x552f4 : word) ltac:(bveq).
stepn F_53518 D_53518.
stepb_ft F_5351c D_5351c ltac:(rewrite Ha0, Hs6, c_eq_Z by lia; apply Z.eqb_neq; lia).
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity. exact Ha0.
Qed.

#[using="Type"] Lemma sw_retry_a : forall regs mem rom (su f fd io ic cnt n0 rem : Z) (b0 : word),
getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 ic ->
getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0x66000 <= f)%Z -> (f + 232 <= 0x97e70)%Z ->
(su - 104 <= io)%Z -> (io + 16 <= su - 72)%Z ->
(1 <= ic <= 2)%Z ->
(1 <= cnt <= n0)%Z -> (n0 < 2^62)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z ->
(bv_unsigned b0 + n0 <= 2^64)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
rdn RSEGS mem (Z_to_bv 64 io) 8%nat = Some (word_to_le_bytes 8 b0) ->
rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
(0 < fd < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x552fc : word) mem rom)
(mkst regs' (0x552ec : word)
(wbytes (wbytes mem (Z_to_bv 64 io) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b0 + cnt))))
(Z_to_bv 64 (io + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n0 - cnt)))) rom)
/\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 io /\ getr regs' 12 = Z_to_bv 64 ic
/\ getr regs' 18 = Z_to_bv 64 ic /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 io
/\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom su f fd io ic cnt n0 rem b0
Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi IC CNT N0 CR REM B0 SOK Mb0 Mn0 Mfd FD.
pose proof (u64_range b0) as Hb0.
eexists. split.
-
stepb_ft F_53520 D_53520 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).

stepLD8 F_53524 D_53524 (Z_to_bv 64 n0).

stepn F_53528 D_53528. rewrite Ha0, (sltu_ge n0 cnt) by lia.

stepn F_5352c D_5352c.
stepn F_53530 D_53530. rewrite Hs3.

stepLD8 F_53534 D_53534 b0.

stepn F_53538 D_53538.
stepn F_5353c D_5353c. rewrite v_and_0_l.
stepn F_53540 D_53540. rewrite Ha0, (v_sub_Z cnt 0) by lia. rewrite Z.sub_0_r.

stepn F_53544 D_53544. rewrite (v_add_wZ b0 cnt) by lia.

stepST F_53548 D_53548 (Z_to_bv 64 io) (Z_to_bv 64 (bv_unsigned b0 + cnt)) ltac:(sok_frame SOK).

stepb_tk F_5354c D_5354c ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).

stepn F_534e4 D_534e4.
stepn F_534e8 D_534e8.
stepn F_534ec D_534ec. rewrite Hs3, (v_add_ZZ' io 8) by lia.

stepLD8 F_534f0 D_534f0 (Z_to_bv 64 n0).

stepn F_534f4 D_534f4. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.

stepLD F_534f8 D_534f8 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.

stepn F_534fc D_534fc. rewrite Hs2, (v_subw_small_lit ic 0) by lia. rewrite Z.sub_0_r.

stepn F_53500 D_53500. rewrite (v_sub_Z n0 cnt) by lia.
stepST F_53504 D_53504 (Z_to_bv 64 (io + 8)) (Z_to_bv 64 (n0 - cnt)) ltac:(sok_frame SOK).

stepn F_53508 D_53508.
stepn F_5350c D_5350c.
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

#[using="Type"] Lemma sw_retry_b : forall regs mem rom (su f fd io cnt n0 n1 rem : Z) (b1 : word),
getr regs 10 = Z_to_bv 64 cnt -> getr regs 19 = Z_to_bv 64 io -> getr regs 18 = Z_to_bv 64 2 ->
getr regs 22 = Z_to_bv 64 rem -> getr regs 9 = Z_to_bv 64 f -> getr regs 2 = Z_to_bv 64 (su - 112) ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0x66000 <= f)%Z -> (f + 232 <= 0x97e70)%Z ->
(su - 104 <= io)%Z -> (io + 32 <= su - 72)%Z ->
(0 <= n0 < cnt)%Z -> (cnt <= rem)%Z -> (rem < 2^62)%Z -> (cnt - n0 <= n1)%Z -> (n1 < 2^62)%Z ->
(bv_unsigned b1 + n1 <= 2^64)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
rdn RSEGS mem (Z_to_bv 64 (io + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n0)) ->
rdn RSEGS mem (Z_to_bv 64 (io + 16)) 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn RSEGS mem (Z_to_bv 64 (io + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 n1)) ->
rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
(0 < fd < 2147483648)%Z ->
exists regs',
msteps RSEGS (mkst regs (0x552fc : word) mem rom)
(mkst regs' (0x552ec : word)
(wbytes (wbytes mem (Z_to_bv 64 (io + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0)))))
(Z_to_bv 64 (io + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (n1 - (cnt - n0))))) rom)
/\ getr regs' 17 = Z_to_bv 64 66 /\ getr regs' 10 = Z_to_bv 64 fd
/\ getr regs' 11 = Z_to_bv 64 (io + 16) /\ getr regs' 12 = Z_to_bv 64 1
/\ getr regs' 18 = Z_to_bv 64 1 /\ getr regs' 19 = Z_to_bv 64 io /\ getr regs' 20 = Z_to_bv 64 (io + 16)
/\ getr regs' 22 = Z_to_bv 64 (rem - cnt)
/\ sw_regs_but regs regs'.
Proof.
intros regs mem rom su f fd io cnt n0 n1 rem b1
Ha0 Hs3 Hs2 Hs6 Hs1 Hsp SUlo SUhi Flo Fhi IOlo IOhi N0 CR REM N1 N1hi B1 SOK Mn0 Mb1 Mn1 Mfd FD.
pose proof (u64_range b1) as Hb1.
eexists. split.
-
stepb_ft F_53520 D_53520 ltac:(rewrite Ha0; apply c_lts_pos_0; lia).

stepLD8 F_53524 D_53524 (Z_to_bv 64 n0).

stepn F_53528 D_53528. rewrite Ha0, (sltu_lt n0 cnt) by lia.

stepn F_5352c D_5352c.
stepn F_53530 D_53530. rewrite Hs3, (v_add_ZZ' io 16) by lia.

stepLD8 F_53534 D_53534 b1.

stepn F_53538 D_53538.
stepn F_5353c D_5353c. rewrite (v_and_m1_l n0) by lia.
stepn F_53540 D_53540. rewrite Ha0, (v_sub_Z cnt n0) by lia.

stepn F_53544 D_53544. rewrite (v_add_wZ b1 (cnt - n0)) by lia.

stepST F_53548 D_53548 (Z_to_bv 64 (io + 16)) (Z_to_bv 64 (bv_unsigned b1 + (cnt - n0))) ltac:(sok_frame SOK).

stepb_ft F_5354c D_5354c ltac:(rewrite Ha0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).

stepn F_53550 D_53550.
stepn F_53554 D_53554.
stepn F_534e8 D_534e8.
stepn F_534ec D_534ec. rewrite Hs3, (v_add_ZZ' io 24) by lia.

stepLD8 F_534f0 D_534f0 (Z_to_bv 64 n1).

stepn F_534f4 D_534f4. rewrite Hs6, Ha0, (v_sub_Z rem cnt) by lia.

stepLD F_534f8 D_534f8 (word_to_le_bytes 4 (Z_to_bv 64 fd)) (Z_to_bv 64 fd)
ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
rewrite (v_lw_small fd) by lia.

stepn F_534fc D_534fc. rewrite Hs2. vals_lit.

stepn F_53500 D_53500. rewrite (v_sub_Z n1 (cnt - n0)) by lia.
stepST F_53504 D_53504 (Z_to_bv 64 (io + 24)) (Z_to_bv 64 (n1 - (cnt - n0))) ltac:(sok_frame SOK).

stepn F_53508 D_53508.
stepn F_5350c D_5350c.
apply mst_refl.
- unfold sw_regs_but; repeat split; gres; try reflexivity; try assumption.
Qed.

Definition mem_sw2 (mem1 : word -> option byte) (f : Z) (bufp bufsz : word) :=
wbytes (wbytes (wbytes mem1
(Z_to_bv 64 (f + 32)) (word_to_le_bytes 8 (v_add bufp bufsz)))
(Z_to_bv 64 (f + 40)) (word_to_le_bytes 8 bufp))
(Z_to_bv 64 (f + 56)) (word_to_le_bytes 8 bufp).

#[using="Type"] Lemma sw_done : forall regs mem rom (su f : Z) (l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v : word),
getr regs 2 = Z_to_bv 64 (su - 112) ->
getr regs 8 = l -> getr regs 9 = Z_to_bv 64 f ->
getr regs 21 = Z_to_bv 64 0x97e70 ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0x66000 <= f)%Z -> (f + 232 <= 0x97e70)%Z ->
ret_ok ret ->
rdn RSEGS mem (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret) ->
rdn RSEGS mem (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 s0v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 s1v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 s2v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 s3v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 s4v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 s5v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 s6v) ->
rdn RSEGS mem (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can) ->
rdn RSEGS mem (Z_to_bv 64 0x97e70) 8%nat = Some (word_to_le_bytes 8 can) ->
rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp) ->
rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz) ->
exists regs',
msteps RSEGS (mkst regs (0x55270 : word) mem rom)
(mkst regs' ret (mem_sw2 mem f bufp bufsz) rom)
/\ getr regs' 10 = l /\ getr regs' 2 = Z_to_bv 64 su /\ getr regs' 1 = ret
/\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
/\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
/\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
/\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
/\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
intros regs mem rom su f l bufp bufsz can ret s0v s1v s2v s3v s4v s5v s6v
Hsp Hs0 Hs1 Hs5 SUlo SUhi Flo Fhi Hret
M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz.
unfold mem_sw2. eexists. split.
-
stepLD F_53494 D_53494 (word_to_le_bytes 8 bufp) bufp ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_53498 D_53498 (word_to_le_bytes 8 bufsz) bufsz ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepn F_5349c D_5349c.

stepST F_534a0 D_534a0 (Z_to_bv 64 (f + 32)) (v_add bufp bufsz) ltac:(sok_data).
stepST F_534a4 D_534a4 (Z_to_bv 64 (f + 40)) bufp ltac:(sok_data).
stepST F_534a8 D_534a8 (Z_to_bv 64 (f + 56)) bufp ltac:(sok_data).

stepn F_534ac D_534ac. rewrite Hs0.
stepLD F_534b0 D_534b0 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_534b4 D_534b4 (word_to_le_bytes 8 can) can ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_534b8 D_534b8 ltac:(apply c_eq_refl).

stepLD F_534bc D_534bc (word_to_le_bytes 8 ret) ret ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_534c0 D_534c0 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_534c4 D_534c4 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_534c8 D_534c8 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_534cc D_534cc (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_534d0 D_534d0 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_534d4 D_534d4 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepLD F_534d8 D_534d8 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).
stepn F_534dc D_534dc. rewrite Hsp. sp_renorm.
replace (su - 0)%Z with su by lia.
stepret F_534e0 D_534e0 ret ltac:(reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

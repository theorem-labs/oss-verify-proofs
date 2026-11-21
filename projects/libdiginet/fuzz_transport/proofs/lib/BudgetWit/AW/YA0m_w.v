(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0m.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA0m.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run_segments lift and the system-call ROM robustness; the writev node's robustness to a larger read-only backing); internal commit ids in comments replaced by public commits or removed. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/YA0m.v by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK0p YK02 YK15.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP0n YK04 YA0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import RomBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Section g.
Context {fx : FPState}.
Section h.
Variable segs : list Segment.
Variable H : word -> bool.
Variable A : list (Z * Z).
Lemma eager_used_vmmaps : forall m m',
m_vmmaps m' = m_vmmaps m -> m_vm_lazy m' = m_vm_lazy m -> eager_used m' = eager_used m.
Proof. intros m m' H1 H2. unfold eager_used. rewrite H1, H2. reflexivity. Qed.
Lemma AI_ledgers : forall md md',
AI segs H A md ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> m_vm_materialized md' = m_vm_materialized md ->
m_halted md' = None -> AI segs H A md'.
Proof.
intros md md' HAI Hv Hl Hm Hh. apply (AI_transport segs H A md md' HAI Hm Hl Hh).
rewrite (eager_used_vmmaps md md' Hv Hl), Hv. exact (minv_budget _ _ (AI_MInv segs H A md HAI)).
Qed.
Lemma node_chk_lazy : forall ms model x8 (I : Type) (i0 : I)
(ef : I -> SyscallEffect) (md : I -> Model) (ev : I -> list event),
AI segs H A model ->
ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (ef i) model = CheckOk (md i) (ev i)) ->
(forall i, m_halted (md i) = None) ->
(forall i, m_vmmaps (md i) = m_vmmaps model /\ m_vm_lazy (md i) = m_vm_lazy model
/\ m_vm_materialized (md i) = m_vm_materialized model) ->
(forall i, ranges_avoid H (syscall_effect_accesses (ef i))) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
exists i, eff = ef i /\ m' = md i /\ evs = ev i) ->
(forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (ef i)) ->
sys_rob segs (mkCfg ms model) ->
node_ok segs (mkCfg ms model) I ev
(fun i => mkCfg (advance_past_svc (apply_effect ms (ef i)))
(materialized_succ (md i) (syscall_effect_accesses (ef i))))
/\ (forall i, AI segs H A (materialized_succ (md i) (syscall_effect_accesses (ef i)))
/\ same_but_materialized (md i) (materialized_succ (md i) (syscall_effect_accesses (ef i)))).
Proof.
intros ms model x8 I i0 ef md ev HAI Hsvc Hok Hhl Hled Hav Hinv Hns Hrob.
assert (HAIi : forall i, AI segs H A (md i)).
{ intros i. destruct (Hled i) as (Hv & Hl & Hm). exact (AI_ledgers model (md i) HAI Hv Hl Hm (Hhl i)). }
destruct HAI as (HH & Hwf & Hcov & Hinv0 & Hh).
destruct (node_syscall_restricted segs H A ms model x8 I ef md ev Hwf Hh Hsvc) as [Hsucc Hnode].
- intros i. apply check_syscall_ok_iff. apply Hok.
- intros r Hr. destruct r as [eff m' evs|].
+ apply check_syscall_ok_iff in Hr. destruct (Hinv eff m' evs Hr) as (i & -> & -> & ->). exists i. reflexivity.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (ef i0)) in Hr. rewrite (Hok i0) in Hr. discriminate Hr.
- exact Hhl.
- exact Hns.
- intros i. destruct (HAIi i) as (_ & _ & Hc & _). exact Hc.
- intros i. exact (AI_MInv segs H A (md i) (HAIi i)).
- exact Hav.
- exact Hrob.
- split; [exact Hnode|]. intros i. destruct (Hsucc i) as [Hm Hs]. split; [|exact Hs].
exact (AI_same segs H A (md i) _ (HAIi i) Hs Hm).
Qed.
Lemma node_ok_ext : forall c (I : Type) (evs : I -> list event) (nx nx' : I -> config),
node_ok segs c I evs nx -> (forall i, nx i = nx' i) -> node_ok segs c I evs nx'.
Proof.
intros c I evs nx nx' [H1 [H2 H3]] He. split; [| split; [| exact H3]].
- intros i. rewrite <- He. apply H1.
- intros e st Hs. destruct (H2 e st Hs) as (i & -> & ->). exists i. rewrite He. auto.
Qed.
Lemma ledgers_same : forall m : Model,
m_vmmaps m = m_vmmaps m /\ m_vm_lazy m = m_vm_lazy m /\ m_vm_materialized m = m_vm_materialized m.
Proof. intros m. repeat split; reflexivity. Qed.
Lemma node_chk1_lazy : forall regs pc mem rom model eff m' evs,
AI segs H A model ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model = CheckOk m' evs ->
m_halted m' = None ->
m_vmmaps m' = m_vmmaps model /\ m_vm_lazy m' = m_vm_lazy model /\ m_vm_materialized m' = m_vm_materialized model ->
ranges_avoid H (syscall_effect_accesses eff) ->
(forall eff2 m2 evs2,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff2 model = CheckOk m2 evs2 ->
eff2 = eff /\ m2 = m' /\ evs2 = evs) ->
sys_rob segs (mkCfg (pend_at regs pc mem rom) model) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => evs)
(fun _ => mkCfg (mkst (regupd regs 10 (eff_ret eff)) (v_addi pc 4) (effmem mem eff) rom)
(materialized_succ m' (syscall_effect_accesses eff)))
/\ AI segs H A (materialized_succ m' (syscall_effect_accesses eff))
/\ same_but_materialized m' (materialized_succ m' (syscall_effect_accesses eff)).
Proof.
intros regs pc mem rom model eff m' evs HAI Hok Hh' Hled Hav Huniq Hrob.
destruct (node_chk_lazy (pend_at regs pc mem rom) model (getr regs 17) unit tt
(fun _ => eff) (fun _ => m') (fun _ => evs) HAI eq_refl
(fun _ => Hok) (fun _ => Hh') (fun _ => Hled) (fun _ => Hav)) as [Hn Hs].
- intros eff2 m2 evs2 H2. exists tt. apply Huniq. exact H2.
- intros []. apply nonspurious_of_unique. intros eff2 m2 evs2 Hs2.
apply check_syscall_ok_iff in Hs2. apply Huniq in Hs2 as (-> & _ & _). reflexivity.
- exact Hrob.
- split; [|exact (Hs tt)]. eapply node_ok_ext; [exact Hn|]. intros []. cbn beta. rewrite adv_pend. reflexivity.
Qed.
Lemma node_ret_only_copyins_lazy : forall regs pc mem rom model reads r m' evs,
AI segs H A model ->
(forall eff, check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_ret_only_copyins reads eff r m' evs) ->
m_halted m' = None ->
m_vmmaps m' = m_vmmaps model /\ m_vm_lazy m' = m_vm_lazy model /\ m_vm_materialized m' = m_vm_materialized model ->
ranges_avoid H reads ->
sys_rob segs (mkCfg (pend_at regs pc mem rom) model) ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => evs)
(fun _ => mkCfg (mkst (regupd regs 10 r) (v_addi pc 4) mem rom) (materialized_succ m' reads))
/\ AI segs H A (materialized_succ m' reads) /\ same_but_materialized m' (materialized_succ m' reads).
Proof.
intros regs pc mem rom model reads r m' evs HAI Hchk Hh' Hled Hav Hrob.
assert (Hacc : syscall_effect_accesses (with_copyins reads (mkEffect r [] [])) = reads).
{ cbn. apply app_nil_r. }
destruct (node_chk1_lazy regs pc mem rom model (with_copyins reads (mkEffect r [] [])) m' evs HAI) as (Hn & HA & Hs).
- rewrite Hchk. apply check_ret_only_copyins_refl.
- exact Hh'.
- exact Hled.
- rewrite Hacc. exact Hav.
- intros eff2 m2 evs2 H2. rewrite Hchk in H2. apply check_ret_only_copyins_ok_iff. exact H2.
- exact Hrob.
- rewrite Hacc in Hn, HA, Hs. cbn [eff_ret with_copyins] in Hn. rewrite effmem_copyins_ret_only in Hn.
exact (conj Hn (conj HA Hs)).
Qed.
Lemma node_writev_lazy : forall regs pc mem rom model fd ch iovs bs,
AI segs H A model ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
(forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs n)) ->
let accs := fun i : wr_index bs =>
writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs (proj1_sig i) in
node_ok segs (mkCfg (pend_at regs pc mem rom) model) (wr_index bs)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) bs))
(fun i => mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat (proj1_sig i)))) (v_addi pc 4) mem rom)
(materialized_succ model (accs i)))
/\ (forall i, AI segs H A (materialized_succ model (accs i)) /\ same_but_materialized model (materialized_succ model (accs i))).
Proof.
intros regs pc mem rom model fd ch iovs bs HAI Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hav accs.
pose proof (AI_halted segs H A model HAI) as Hh.
pose proof (writev_chk_canon segs regs pc mem rom model fd ch iovs bs Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb)
as Hchk.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
assert (HMv : MAX_RW_COUNT = 0x7ffff000%Z) by reflexivity.
set (mp := ms_read_byte (pend_at regs pc mem rom)) in *.
pose (ef := fun i : wr_index bs => writev_eff mp (getr regs 11) (getr regs 12) iovs (proj1_sig i)).
assert (Hacc : forall i, syscall_effect_accesses (ef i) = accs i) by (intros i; cbn; apply app_nil_r).
destruct (node_chk_lazy (pend_at regs pc mem rom) model (getr regs 17) (wr_index bs) (wr_full bs Hnb)
ef (fun _ => model) (fun i => map (WriteEv ch) (firstn (proj1_sig i) bs)) HAI eq_refl) as [Hn Hs].
- intros [n [Hn1 Hn2]]. unfold ef, writev_eff; cbn [proj1_sig]. rewrite Hchk.
assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat n)) = Z.of_nat n).
{ rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia. }
rewrite Hu, Nat2Z.id.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat n))) with false
by (symmetry; unfold addr_is_error_b; apply Z.ltb_ge; rewrite Hu; unfold two_pow_64; lia).
rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
- intros _. exact Hh.
- intros _. apply ledgers_same.
- intros [n [Hn1 Hn2]]. rewrite Hacc. unfold accs; cbn [proj1_sig]. apply Hav; assumption.
- intros [ret ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate].
destruct (((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? Z.of_nat (length bs))%Z) &&
negb (addr_is_error_b ret) && access_ranges_eqb ci _) eqn:E; [|discriminate].
injection Hk as <- <-.
apply andb_prop in E as [E Hci]. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Hci.
assert (Hr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
exists (exist _ (Z.to_nat (bv_unsigned ret)) Hr). unfold ef, writev_eff; cbn [proj1_sig].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_bv_unsigned, Hci. auto.
- exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- exact (writev_rob_pend segs regs pc mem rom model fd ch iovs bs Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb).
- split.
+ eapply node_ok_ext; [exact Hn|]. intros i. cbn beta. rewrite adv_pend, Hacc.
unfold ef. rewrite effmem_writev_eff. unfold writev_eff; cbn [eff_ret]. reflexivity.
+ intros i. rewrite <- (Hacc i). exact (Hs i).
Qed.
Lemma srz_exit_lazy : forall regs pc mem rom model,
m_halted model = None -> is_exit_no (getr regs 17) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model)
(t_exit (bv_and (getr regs 10) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs pc mem rom model Hh Hx8. rewrite <- (pend_gpr0 regs pc mem rom).
exact (srz_exit segs (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl Hx8).
Qed.
Lemma srz_exit_small_lazy : forall regs pc mem rom model (c : word),
m_halted model = None -> is_exit_no (getr regs 17) ->
getr regs 10 = c -> (bv_unsigned c < 256)%Z ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) (t_exit c (m_fs model)).
Proof.
intros regs pc mem rom model c Hh Hx8 Hc Hsmall.
rewrite <- (land_255_small c Hsmall), <- Hc. apply srz_exit_lazy; assumption.
Qed.
End h.
End g.

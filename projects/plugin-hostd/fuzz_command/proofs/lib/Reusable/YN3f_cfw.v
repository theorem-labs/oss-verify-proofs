(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YN3f.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YN3f_cfw.v, with its module paths and addresses changed; 2 of its 437 lines of code are new or changed and 2 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP02 YH00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YO0d YH02 YN3f YK15_cfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import SlotAgree AgreeLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_writev_dep : forall regs pc mem rom model fd ch iovs bs (T : nat -> TSet),
m_halted model = None -> m_vm_lazy model = [] ->
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
crealizes B (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom)
model) (T n)) ->
crealizes B (mkCfg (pend_at regs pc mem rom) model)
(t_alt (fun i : wr_index bs => t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof using.
intros regs pc mem rom model fd ch iovs bs T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hc.
pose proof (writev_chk_canon segs regs pc mem rom model fd ch iovs bs Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb)
as Hchk.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
assert (HMv : MAX_RW_COUNT = 0x7ffff000%Z) by reflexivity.
set (mp := ms_read_byte (pend_at regs pc mem rom)) in *.
pose (ef := fun i : wr_index bs => writev_eff mp (getr regs 11) (getr regs 12) iovs (proj1_sig i)).
apply (crz_node_sys B (pend_at regs pc mem rom) model (getr regs 17) (wr_index bs)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) bs))
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) model)
(fun i => T (proj1_sig i)) (wr_full bs Hnb) eq_refl ltac:(rewrite Hno; reflexivity)).
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) (wr_index bs) (wr_full bs Hnb)
ef (fun _ => model) (fun i => map (WriteEv ch) (firstn (proj1_sig i) bs)) Hh eq_refl).
+ intros [n [Hn1 Hn2]]. unfold ef, writev_eff; cbn [proj1_sig]. rewrite Hchk.
assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat n)) = Z.of_nat n).
{ rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia. }
rewrite Hu, Nat2Z.id.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat n))) with false
by (symmetry; unfold addr_is_error_b; apply Z.ltb_ge; rewrite Hu; unfold two_pow_64; lia).
rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
+ intros _. exact Hh.
+ intros _. exact Hlz.
+ intros [ret ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
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
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- intros [n [Hn1 Hn2]]. unfold ef; cbn [proj1_sig]. rewrite adv_pend.
rewrite effmem_writev_eff. unfold writev_eff; cbn [eff_ret]. apply Hc; assumption.
Qed.
Lemma crz_writev2_wall : forall regs pc mem rom model fd ch (b0 l0 b1 l1 : word) bs0 bs1 T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 2 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 16)) = Some b1 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 24)) = Some l1 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
ms_read_bytes (pend_at regs pc mem rom) b1 l1 = Some bs1 ->
access_okb (getr regs 11) 32 = true ->
access_okb b0 (bv_unsigned l0) = true -> access_okb b1 (bv_unsigned l1) = true ->
(1 <= bv_unsigned l0 + bv_unsigned l1 <= MAX_RW_COUNT)%Z ->
(forall n, (1 <= n)%nat -> (n <= length (bs0 ++ bs1))%nat ->
crealizes B (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
(t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T)) ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof using.
intros regs pc mem rom model fd ch b0 l0 b1 l1 bs0 bs1 T
Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hc.
rewrite <- read_bytes_map_read_byte in Hbs0, Hbs1.
pose proof (gather_iovecs_2 _ _ _ _ _ _ _ Hbs0 Hbs1) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0). pose proof (read_bytes_map_length _ _ _ _ Hbs1).
unfold MAX_RW_COUNT in Htot.
assert (Hnb : (1 <= length (bs0 ++ bs1))%nat) by lia.
eapply crz_conseq; [| apply (t_alt_wall' ch (bs0 ++ bs1) T Hnb)].
eapply (crz_writev_dep regs pc mem rom model fd ch [(b0, l0); (b1, l1)] (bs0 ++ bs1)
(fun n => t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T) Hh Hlz Hno Hfdc H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 2))) with 2%nat.
apply copy_iovecs_2; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0, Hok1. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hc.
Qed.
Lemma crz_writev1_wall : forall regs pc mem rom model fd ch (b0 l0 : word) bs0 T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 (bv_unsigned l0) = true ->
(1 <= bv_unsigned l0 <= MAX_RW_COUNT)%Z ->
(forall n, (1 <= n)%nat -> (n <= length bs0)%nat ->
crealizes B (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
(t_emit (map (WriteEv ch) (skipn n bs0)) T)) ->
crealizes B (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) bs0) T).
Proof using.
intros regs pc mem rom model fd ch b0 l0 bs0 T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hc.
rewrite <- read_bytes_map_read_byte in Hbs0.
pose proof (gather_iovecs_1 _ _ _ _ Hbs0) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0).
unfold MAX_RW_COUNT in Htot.
assert (Hnb : (1 <= length bs0)%nat) by lia.
eapply crz_conseq; [| apply (t_alt_wall' ch bs0 T Hnb)].
eapply (crz_writev_dep regs pc mem rom model fd ch [(b0, l0)] bs0
(fun n => t_emit (map (WriteEv ch) (skipn n bs0)) T) Hh Hlz Hno Hfdc H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 1))) with 1%nat.
apply copy_iovecs_1; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hc.
Qed.
End e.
Section a0.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlz : m_vm_lazy model = [].
Variables (fd ch : word).
Hypothesis Hfdc : fdchan fd ch model.
Hypothesis H32 : fd32 fd = fd.
Hypothesis Hfd31 : bv_unsigned fd < 2^31.
Variables (SP F : Z) (fdbs : list byte) (mem0 : word -> option byte) (regsK : bvmap 5 word) (T : TSet).
Hypothesis HSP : 0 <= SP /\ SP + 40 <= 2^47.
Hypothesis HF : 0 <= F /\ F + 124 <= 2^64.
Hypothesis HFW : F + 124 <= SP + 8 \/ SP + 40 <= F + 120.
Hypothesis Hfd : rdn src0segs mem0 (Z_to_bv 64 (F + 120)) 4 = Some fdbs.
Hypothesis Hfdv : bytes_le_to_Z fdbs = bv_unsigned fd.
Hypothesis HK : forall regs' mem',
(forall r, wl_kept r -> getr regs' r = getr regsK r) ->
getr regs' 17 = Z_to_bv 64 66 ->
(forall a, ~ inW SP a -> mem' a = mem0 a) ->
store_ok src0segs mem' (Z_to_bv 64 (SP + 8)) 32 = true ->
crealizes src0_msyms (mkCfg (mkst regs' (Z_to_bv 64 0x1ada8) mem' (seg_rom src0segs)) model) T.
Let rom := seg_rom src0segs.
Let INV := wl_inv fd SP F mem0 regsK.
Ltac access_ok_tac :=
unfold access_okb, TASK_SIZE; rewrite ?u_Z2bv by lia;
apply andb_true_intro; split; apply Z.leb_le; lia.
Lemma wl_node_cf : forall ri pc regs mem c b0 l0 b1 l1 bs0 bs1 (TT : nat -> TSet),
INV ri regs mem c b0 l0 b1 l1 bs0 bs1 ->
(forall n, (1 <= n)%nat -> (n <= length (bs0 ++ bs1))%nat ->
crealizes src0_msyms (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
(t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T)) ->
crealizes src0_msyms (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof using F H32 HSP Hfdc Hh Hlz mem0 regsK.
intros ri pc regs mem c b0 l0 b1 l1 bs0 bs1 TT HI Hc.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & Rri & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1).
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (Hrd1 : rdn src0segs mem (Z_to_bv 64 b1) (Z.to_nat l1) = Some bs1).
{ apply (rdn_agree mem mem0); [lia|lia| |exact Hbs1]. intros x Hx. apply Hout. unfold inW. lia. }
destruct Hc12 as [-> | ->].
-
cbn in Hrem, R22, Hlen0. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
eapply (crz_writev1_wall src0_msyms regs pc mem rom model fd ch (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs1 T Hh Hlz).
+ rewrite R17. reflexivity.
+ exact Hfdc. + exact H32. + exact R10. + exact R12.
+ rewrite R11. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 1) with (SP + 24) by lia. exact Hm1.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 1 + 8) with (SP + 32) by lia. exact Hl1.
+ apply ms_read_bytes_of_rdn. rewrite word_to_nat_zv by lia. exact Hrd1.
+ rewrite R11. access_ok_tac.
+ access_ok_tac.
+ rewrite u_Z2bv by lia. unfold MAX_RW_COUNT. lia.
+ exact Hc.
- cbn in Hrem, R22, Hlen0. destruct (Hiov0 eq_refl) as [Hm0 Hl0].
assert (Hrd0 : rdn src0segs mem (Z_to_bv 64 b0) (Z.to_nat l0) = Some bs0).
{ apply (rdn_agree mem mem0); [lia|lia| |exact (Hbs0 eq_refl)]. intros x Hx. apply Hout. unfold inW. lia. }
eapply (crz_writev2_wall src0_msyms regs pc mem rom model fd ch (Z_to_bv 64 b0) (Z_to_bv 64 l0) (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs0 bs1 T Hh Hlz).
+ rewrite R17. reflexivity.
+ exact Hfdc. + exact H32. + exact R10. + exact R12.
+ rewrite R11. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 2) with (SP + 8) by lia. exact Hm0.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 2 + 8) with (SP + 16) by lia. exact Hl0.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 2 + 16) with (SP + 24) by lia. exact Hm1.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 2 + 24) with (SP + 32) by lia. exact Hl1.
+ apply ms_read_bytes_of_rdn. rewrite word_to_nat_zv by lia. exact Hrd0.
+ apply ms_read_bytes_of_rdn. rewrite word_to_nat_zv by lia. exact Hrd1.
+ rewrite R11. access_ok_tac.
+ access_ok_tac.
+ access_ok_tac.
+ rewrite !u_Z2bv by lia. unfold MAX_RW_COUNT. lia.
+ exact Hc.
Qed.
Lemma wl_done_cf : forall regs mem (l : list byte) n,
(forall r, wl_kept r -> getr regs r = getr regsK r) -> getr regs 17 = Z_to_bv 64 66 ->
(forall a, ~ inW SP a -> mem a = mem0 a) -> store_ok src0segs mem (Z_to_bv 64 (SP + 8)) 32 = true ->
(length l <= n)%nat ->
crealizes src0_msyms (mkCfg (mkst regs (Z_to_bv 64 0x1ada8) mem rom) model) (t_emit (map (WriteEv ch) (skipn n l)) T).
Proof using HK.
intros regs mem l n Hk H17 Hout Hst Hn.
pose proof (HK regs mem Hk H17 Hout Hst) as HR.
rewrite skipn_all_nil by exact Hn. cbn [map].
apply (crealizes_emit_nil src0_msyms). exact HR.
Qed.
Lemma wl_loop2_cf : forall k regs mem c b0 l0 b1 l1 bs0 bs1,
(length (bs0 ++ bs1) <= k)%nat ->
INV 20%bv regs mem c b0 l0 b1 l1 bs0 bs1 ->
crealizes src0_msyms (mkCfg (mkst regs (Z_to_bv 64 0x1ae24) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof using H32 HF HFW HK HSP Hfd Hfd31 Hfdc Hfdv Hh Hlz.
induction k as [|k IH]; intros regs mem c b0 l0 b1 l1 bs0 bs1 Hlen HI.
{ exfalso. rewrite length_app in Hlen.
destruct HI as (Hc12 & _ & _ & _ & _ & _ & _ & _ & _ & Hrem & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl0 & Hl1).
destruct Hc12 as [-> | ->]; cbn in Hrem, Hl0; lia. }
pose proof HI as HI'.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & R20 & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1).
replace (Z_to_bv 64 0x1ae24 : word) with (0x1ae24%bv : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (crz_step src0_msyms); [exact Hh | exact Hlz | reflexivity | apply (step_ecall _ _ _ _ _ _ F_17c1c eq_refl) |].
change (crealizes src0_msyms (mkCfg (pend_at regs (0x1ae24%bv : word) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T)).
eapply (wl_node_cf 20%bv _ regs mem c b0 l0 b1 l1 bs0 bs1 (fun _ => T) HI').
intros n Hn1 Hn2. replace (v_addi (0x1ae24%bv : word) 4) with (Z_to_bv 64 0x1ae28 : word) by (apply bv_eq; vm_compute; reflexivity).
set (rem := (if c =? 2 then l0 else 0) + l1) in *.
assert (Hlenall : Z.of_nat (length (bs0 ++ bs1)) = rem) by (rewrite length_app; lia).
destruct (after_w2 (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) mem rom (Z.of_nat n) rem
ltac:(lia) ltac:(lia) ltac:(gr; reflexivity) ltac:(gr; exact R22))
as (regs1 & Hms1 & R19a & R10a & Hfr1).
eapply (crealizes_msteps src0_msyms); [exact Hh | exact Hlz | exact Hms1 |].
destruct (Z.eqb_spec (Z.of_nat n) rem) as [Heq | Hne].
{
apply wl_done_cf; [ | | exact Hout | exact Hst | lia].
- intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr.
- rewrite Hfr1 by reg_neq_tac. rewrite getr_other by reg_neq_tac. exact R17. }
assert (R2a : getr regs1 2 = Z_to_bv 64 SP) by (rewrite Hfr1 by reg_neq_tac; gr; exact R2).
assert (R9a : getr regs1 9 = Z_to_bv 64 F) by (rewrite Hfr1 by reg_neq_tac; gr; exact R9).
assert (R18a : getr regs1 18 = Z_to_bv 64 c) by (rewrite Hfr1 by reg_neq_tac; gr; exact R18).
assert (R19b : getr regs1 19 = Z_to_bv 64 (SP + 40 - 16 * c)) by (rewrite R19a; gr; exact R20).
assert (R22a : getr regs1 22 = Z_to_bv 64 rem) by (rewrite Hfr1 by reg_neq_tac; gr; exact R22).
assert (Hfd' : rdn src0segs mem (Z_to_bv 64 (F + 120)) 4 = Some fdbs).
{ apply (rdn_agree mem mem0); [lia|cbn; lia| |exact Hfd]. intros x Hx. apply Hout. unfold inW. cbn in Hx. lia. }
assert (Hkept1 : forall r, wl_kept r -> getr regs1 r = getr regsK r).
{ intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr. }
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (HiovM : iov_mem mem SP c b0 l0 b1 l1) by (split; [exact Hiov0| split; assumption]).
destruct Hc12 as [-> | ->].
-
cbn in Hrem, R22, Hlen0, rem. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
assert (HP : body_pre regs1 mem SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (body_C regs1 mem rom SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl)
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (crealizes_msteps src0_msyms); [exact Hh | exact Hlz | exact Hms2 |].
change (skipn n bs1) with ([] ++ skipn n bs1).
apply (IH regs2 mem2 1 0 0 (b1 + Z.of_nat n) (l1 - Z.of_nat n) [] (skipn n bs1)).
+ cbn [app]. rewrite length_skipn. lia.
+ unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ]
| apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]]
| match goal with |- ?g => idtac "LEFT:" g end ].
-
cbn in Hrem, R22, Hlen0, rem.
assert (HP : body_pre regs1 mem SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (Z_le_gt_dec (Z.of_nat n) l0) as [Hle | Hgt].
+
destruct (body_A regs1 mem rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (crealizes_msteps src0_msyms); [exact Hh | exact Hlz | exact Hms2 |].
rewrite skipn_app. replace (n - length bs0)%nat with 0%nat by lia. cbn [skipn].
apply (IH regs2 mem2 2 (b0 + Z.of_nat n) (l0 - Z.of_nat n) b1 l1 (skipn n bs0) bs1).
* rewrite length_app, length_skipn in *. lia.
* unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ]
| apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]]
| match goal with |- ?g => idtac "LEFT:" g end ].
+
destruct (body_B regs1 mem rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (crealizes_msteps src0_msyms); [exact Hh | exact Hlz | exact Hms2 |].
rewrite skipn_app. rewrite (skipn_all_nil n bs0) by lia. cbn [app].
change (skipn (n - length bs0) bs1) with ([] ++ skipn (n - length bs0) bs1).
apply (IH regs2 mem2 1 0 0 (b1 + (Z.of_nat n - l0)) (l1 - (Z.of_nat n - l0)) [] (skipn (n - length bs0) bs1)).
* cbn [app]. rewrite length_app, length_skipn in *. lia.
* unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | replace (Z.of_nat n - l0) with (Z.of_nat (n - length bs0)) by lia; apply rdn_advance; [lia|lia|lia|lia| exact Hbs1] ]
| replace (Z.of_nat n - l0) with (Z.of_nat (n - length bs0)) by lia; apply rdn_advance; [lia|lia|lia|lia| exact Hbs1]
| match goal with |- ?g => idtac "LEFT:" g end ].
Qed.
Lemma wl_entry_pend_cf : forall regs mem c b0 l0 b1 l1 bs0 bs1,
INV 19%bv regs mem c b0 l0 b1 l1 bs0 bs1 ->
crealizes src0_msyms (mkCfg (pend_at regs (Z_to_bv 64 0x1ad9c) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof using H32 HF HFW HK HSP Hfd Hfd31 Hfdc Hfdv Hh Hlz.
intros regs mem c b0 l0 b1 l1 bs0 bs1 HI.
pose proof HI as HI'.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & R19 & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1).
eapply (wl_node_cf 19%bv _ regs mem c b0 l0 b1 l1 bs0 bs1 (fun _ => T) HI').
intros n Hn1 Hn2. replace (v_addi (Z_to_bv 64 0x1ad9c : word) 4) with (Z_to_bv 64 0x1ada0 : word) by (apply bv_eq; vm_compute; reflexivity).
set (rem := (if c =? 2 then l0 else 0) + l1) in *.
assert (Hlenall : Z.of_nat (length (bs0 ++ bs1)) = rem) by (rewrite length_app; lia).
destruct (after_w1 (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) mem rom (Z.of_nat n) rem
ltac:(lia) ltac:(lia) ltac:(gr; reflexivity) ltac:(gr; exact R22))
as (regs1 & Hms1 & R10a & Hfr1).
eapply (crealizes_msteps src0_msyms); [exact Hh | exact Hlz | exact Hms1 |].
assert (Hkept1 : forall r, wl_kept r -> getr regs1 r = getr regsK r).
{ intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr. }
destruct (Z.eqb_spec (Z.of_nat n) rem) as [Heq | Hne].
{ apply wl_done_cf; [ exact Hkept1 | | exact Hout | exact Hst | lia].
rewrite Hfr1 by reg_neq_tac. rewrite getr_other by reg_neq_tac. exact R17. }
assert (R2a : getr regs1 2 = Z_to_bv 64 SP) by (rewrite Hfr1 by reg_neq_tac; gr; exact R2).
assert (R9a : getr regs1 9 = Z_to_bv 64 F) by (rewrite Hfr1 by reg_neq_tac; gr; exact R9).
assert (R18a : getr regs1 18 = Z_to_bv 64 c) by (rewrite Hfr1 by reg_neq_tac; gr; exact R18).
assert (R19b : getr regs1 19 = Z_to_bv 64 (SP + 40 - 16 * c)) by (rewrite Hfr1 by reg_neq_tac; gr; exact R19).
assert (R22a : getr regs1 22 = Z_to_bv 64 rem) by (rewrite Hfr1 by reg_neq_tac; gr; exact R22).
assert (Hfd' : rdn src0segs mem (Z_to_bv 64 (F + 120)) 4 = Some fdbs).
{ apply (rdn_agree mem mem0); [lia|cbn; lia| |exact Hfd]. intros x Hx. apply Hout. unfold inW. cbn in Hx. lia. }
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (HiovM : iov_mem mem SP c b0 l0 b1 l1) by (split; [exact Hiov0| split; assumption]).
destruct Hc12 as [-> | ->].
- cbn in Hrem, R22, Hlen0, rem. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
assert (HP : body_pre regs1 mem SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (body_C regs1 mem rom SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl)
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (crealizes_msteps src0_msyms); [exact Hh | exact Hlz | exact Hms2 |].
change (skipn n bs1) with ([] ++ skipn n bs1).
apply (wl_loop2_cf (length bs1) regs2 mem2 1 0 0 (b1 + Z.of_nat n) (l1 - Z.of_nat n) [] (skipn n bs1)).
+ cbn [app]. rewrite length_skipn. lia.
+ unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ]
| apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ].
- cbn in Hrem, R22, Hlen0, rem.
assert (HP : body_pre regs1 mem SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (Z_le_gt_dec (Z.of_nat n) l0) as [Hle | Hgt].
+ destruct (body_A regs1 mem rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (crealizes_msteps src0_msyms); [exact Hh | exact Hlz | exact Hms2 |].
rewrite skipn_app. replace (n - length bs0)%nat with 0%nat by lia. cbn [skipn].
apply (wl_loop2_cf (length (bs0 ++ bs1)) regs2 mem2 2 (b0 + Z.of_nat n) (l0 - Z.of_nat n) b1 l1 (skipn n bs0) bs1).
* rewrite !length_app, length_skipn in *. lia.
* unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ]
| apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ].
+ destruct (body_B regs1 mem rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (crealizes_msteps src0_msyms); [exact Hh | exact Hlz | exact Hms2 |].
rewrite skipn_app. rewrite (skipn_all_nil n bs0) by lia. cbn [app].
change (skipn (n - length bs0) bs1) with ([] ++ skipn (n - length bs0) bs1).
apply (wl_loop2_cf (length bs1) regs2 mem2 1 0 0 (b1 + (Z.of_nat n - l0)) (l1 - (Z.of_nat n - l0)) [] (skipn (n - length bs0) bs1)).
* cbn [app]. rewrite length_skipn. lia.
* unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; lia
| replace (Z.of_nat n - l0) with (Z.of_nat (n - length bs0)) by lia; apply rdn_advance; [lia|lia|lia|lia| exact Hbs1] ].
Qed.
End a0.
End d.

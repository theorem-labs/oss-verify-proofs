(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import Gap04.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import
SimInv ExitSim PropExec CatExec CatSim SeqExec MmapSim AllocSim FileSim
ShapeAlg Nodes StoreOk AgentLib AgentNodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg.
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From Stdlib Require Import Zify.
Local Ltac Stdlib.micromega.Lia.lia ::=
first [ intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
| Zify.zify; xlia zchecker ].
Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.
Lemma with_vmmaps_eta : forall m,
with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.
Lemma vmmaps_eta : forall h,
mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.
Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma vm_forget_range_halted : forall lo hi m,
m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.
Section WithSegs.
Variable segs : list Segment.
#[using="Type"] Lemma mmap_check : forall ms x8 model eff,
bv_unsigned x8 = 222%Z ->
check_syscall (sys_input segs ms x8) eff model
= check_mmap (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.
#[using="Type"] Lemma munmap_check : forall ms x8 model eff,
bv_unsigned x8 = 215%Z ->
check_syscall (sys_input segs ms x8) eff model = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.
Inductive three : Type := T1 | T2 | T3.
#[using="Type"] Lemma adv_ret_epend : forall regs pc mem rom x8 r,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.
#[using="Type"] Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
intros. unfold epend.
assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
{ cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.
#[using="Type"] Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
= mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
intros. unfold epend.
assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
{ cbn [apply_writes apply_zeros].
apply functional_extensionality. intro x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity. }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.
#[using="Type"] Lemma brk_r_ok_grow_cases : forall m req r,
let h := m_vmmaps m in
(0 < bv_unsigned req)%Z ->
(bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
(bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
brk_resolution_ok m req r <->
(r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
intros m req r h Hpos Hs Hb.
unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
assert (E0 : w_is0 req = false).
{ unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
rewrite E0. unfold min_brk.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
rewrite (proj2 (Z.ltb_ge _ _)) by lia.
rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
- intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
- intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.
#[using="Type"] Lemma brk_model_keep : forall m req,
brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
intros m req. unfold brk_model, with_brk_next. cbv zeta.
rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
unfold brk_model_next, brk_maps_next.
rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.
#[using="Type"] Lemma brk_model_grow_eq : forall m (d : Z),
let h := m_vmmaps m in
let b := vm_brk h in
(0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
(bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
= with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h)
(Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
intros m d h b Hd Hb0 Hnw Hbal Hdal.
pose proof (u64_range b) as Hbr.
set (req := Z_to_bv 64 (bv_unsigned b + d)).
assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
assert (Hreq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
unfold brk_model_next, brk_maps_next. fold b.
rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
cbn [app maps_subtract_ranges fold_left].
replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
apply bv_eq. rewrite bv_sub_unsigned, Hureq.
rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.
Definition brk_adm (model : Model) (req r : word) : Prop :=
brk_resolution_ok model req r
/\ (brk_refusal_b model req r = true ->
forall r', brk_resolution_ok model req r' -> brk_refusal_b model req r' = true).
#[using="Type"] Lemma brk_adm_of_unique : forall model req r,
brk_resolution_ok model req r ->
(forall r', brk_resolution_ok model req r' -> r' = r) ->
brk_adm model req r.
Proof. intros model req r Hr Hu. split; [exact Hr|]. intros E r' Hr'. rewrite (Hu r' Hr'). exact E. Qed.
#[using="Type"] Lemma refusal_b_brk_ms : forall ms x8 model r,
bv_unsigned x8 = 214%Z ->
refusal_b (sys_input segs ms x8) model r = brk_refusal_b model (ms_gpr ms 0) r.
Proof. intros ms x8 model r Hno. rewrite (refusal_b_214 (sys_input segs ms x8) model r Hno). reflexivity. Qed.
#[using="Type"] Lemma refusal_b_mmap_sys : forall ms x8 model r,
bv_unsigned x8 = 222%Z ->
refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r.
Proof. intros ms x8 model r Hno. rewrite (refusal_b_222 (sys_input segs ms x8) model r Hno). reflexivity. Qed.
#[using="Type"] Lemma refusal_b_mprotect_sys : forall ms x8 model r,
bv_unsigned x8 = 226%Z ->
refusal_b (sys_input segs ms x8) model r = errno_ret_in mprotect_errnos r.
Proof. intros ms x8 model r Hno. rewrite (refusal_b_226 (sys_input segs ms x8) model r Hno). reflexivity. Qed.
#[using="Type"] Lemma mm_refusal_spurious : forall ms x8 model eff effS mS evS,
(bv_unsigned x8 = 222%Z \/ bv_unsigned x8 = 226%Z) ->
check_syscall (sys_input segs ms x8) effS model = CheckOk mS evS ->
refusal_b (sys_input segs ms x8) model (eff_ret effS) = false ->
refusal_b (sys_input segs ms x8) model (eff_ret eff) = true ->
spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff.
Proof.
intros ms x8 model eff effS mS evS Hno HcS HnS Hr.
apply (refusal_spurious_of_grant ACFG _ model eff effS mS evS); [| exact Hr | apply check_syscall_ok_iff; exact HcS | exact HnS].
destruct Hno as [E | E]; [apply (acfg_family_off_222 (sys_input segs ms x8) E) | apply (acfg_family_off_226 (sys_input segs ms x8) E)].
Qed.
#[using="Type"] Lemma brk_refusal_b_move : forall m req r,
req <> Z_to_bv 64 0 ->
(bv_unsigned (vm_start_brk (m_vmmaps m)) <= bv_unsigned req)%Z ->
req <> vm_brk (m_vmmaps m) ->
brk_refusal_b m req r = bv_eqb r (vm_brk (m_vmmaps m)).
Proof.
intros m req r H0 Hs Hb. unfold brk_refusal_b, min_brk. cbv zeta.
assert (E0 : w_is0 req = false) by (unfold w_is0; apply bv_eqb_neq; exact H0).
rewrite E0, (proj2 (Z.ltb_ge _ _) Hs), (bv_eqb_neq _ _ Hb). reflexivity.
Qed.
#[using="Type"] Lemma brk_adm_nonspurious : forall ms x8 model eff,
bv_unsigned x8 = 214%Z -> brk_adm model (ms_gpr ms 0) (eff_ret eff) ->
~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff.
Proof.
intros ms x8 model eff Hno [Hok Hf] (_ & Hr & eff' & m' & evs' & Hspec & Hnr).
rewrite (refusal_b_brk_ms ms x8 model _ Hno) in Hr. rewrite (refusal_b_brk_ms ms x8 model _ Hno) in Hnr.
apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hspec as (_ & _ & Hok' & _).
rewrite (Hf Hr _ Hok') in Hnr. discriminate.
Qed.
#[using="Type"] Lemma brk_nonspurious_adm : forall ms x8 model eff,
bv_unsigned x8 = 214%Z -> brk_resolution_ok model (ms_gpr ms 0) (eff_ret eff) ->
~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff ->
brk_adm model (ms_gpr ms 0) (eff_ret eff).
Proof.
intros ms x8 model eff Hno Hok Hns. split; [exact Hok|]. intros Hr r' Hr'.
destruct (brk_refusal_b model (ms_gpr ms 0) r') eqn:E; [reflexivity|]. exfalso. apply Hns.
eapply (refusal_spurious_of_grant ACFG (sys_input segs ms x8) model eff).
- exact (acfg_family_off_214 (sys_input segs ms x8) Hno).
- rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact Hr.
- exact (brk_ok_intro segs ms x8 model r' Hno Hr').
- cbn [eff_ret]. rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact E.
Qed.
Definition noaccess_model (a n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
((a, n) :: vm_maps (m_vmmaps m))
((a, n) :: vm_noaccess (m_vmmaps m))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
#[using="Type"] Lemma grant_ok_na_unpack : forall hint m a n,
grant_ok_na hint m a n = true ->
(bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
(bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true /\ True.
Proof.
intros hint m a n H. unfold grant_ok_na in H.
rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. repeat split; assumption.
Qed.
#[using="Type"] Lemma grant_na_not_errno : forall hint model a n,
(0 <= n)%Z -> grant_ok_na hint model a n = true -> errno_ret_in mmap_errnos a = false.
Proof.
intros hint model a n Hn Hg. unfold grant_ok_na in Hg.
apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Hce]. apply Z.leb_le in Hce.
apply errno_ret_in_below; [reflexivity|].
pose proof (alloc_top_room (m_vmmaps model)). unfold two_pow_64, stack_max_size in *. lia.
Qed.
Definition mprotect_model (addr n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
#[using="Type"] Lemma check_syscall_226 : forall ms x8 eff m,
bv_unsigned x8 = 226%Z ->
check_syscall (sys_input segs ms x8) eff m
= check_mprotect (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.
#[using="Type"] Lemma mprotect_check : forall ms x8 model eff (addr : word) (len : Z),
bv_unsigned x8 = 226%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
ms_gpr ms 2 = Z_to_bv 64 3 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mprotect_errnos r
then match zs with [] => CheckOk model [] | _ => CheckReject end
else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
then CheckOk (mprotect_model addr n model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
rewrite (check_syscall_226 ms x8 eff model Hno). unfold check_mprotect.
rewrite H0, H2, Hu1.
replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
cbv beta iota zeta. fold n. rewrite Hna, Hma. cbn [andb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct us; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
destruct cs; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
destruct ci; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
reflexivity.
Qed.
#[using="Type"] Lemma check_syscall_96 : forall ms x8 eff m,
bv_unsigned x8 = 96%Z ->
check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.
Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.
#[using="Type"] Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.
End WithSegs.
Local Open Scope Z_scope.
Lemma region_free_app : forall l1 l2 (lo n : word),
region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.
Lemma region_free_In : forall l (lo n b s : word),
region_free l lo n = true -> In (b, s) l ->
bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
apply region_free_cons in Hrf as [Hd Hrf].
destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.
Lemma region_free_intro : forall l (lo n : word),
(forall b s, In (b, s) l ->
bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
region_free l lo n = true.
Proof.
induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.
Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

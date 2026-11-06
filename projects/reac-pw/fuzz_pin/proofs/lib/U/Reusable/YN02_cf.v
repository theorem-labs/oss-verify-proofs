(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN02.v, with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Export YN02.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YM06_cf YO0d_cf YN2c PlaceCapW YM01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require AgreeLim Uniform.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require RoomShapesDraft PolicyFit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable segs : list Segment.
Lemma mreal_cf_ask {R} : forall c q snap (k : Z -> itree astate R) Q,
SR_cfv segs c (fun c1 => knode_cf segs c1 q snap (fun z c2 => mreal_cf segs c2 (k z) Q)) ->
mreal_cf segs c (IAsk q snap k) Q.
Proof. intros. exact H. Qed.
Lemma mreal_cf_leaf {R} : forall c (r : R) Q, SR_cfv segs c (Q r) -> mreal_cf segs c (IRet r) Q.
Proof. intros. exact H. Qed.

Lemma kcf_vml_node : forall c (I : Type) evs (nx : I -> config),
  node_ok segs c I evs nx -> (forall i, vml (nx i) = vml c) ->
  forall e c2, sstep_cfg segs ACFG c e (SNext c2) -> vml c2 = vml c.
Proof using.
  intros c I evs nx [_ Hc] HV e c2 Hs. destruct (Hc e (SNext c2) Hs) as (i & _ & E). injection E as ->. apply HV.
Qed.

Lemma kcf_not_refused : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_vm_lazy m' = []) ->
  alloc_budget_refused_b (sys_input segs ms x8) model = false ->
  ~ budget_refused_at segs (mkCfg ms model).
Proof using.
  intros ms model x8 Hh Hsvc Hlz Hb Hr.
  rewrite (budget_refused_at_no_lazy_syscall segs ms model x8 Hh Hsvc Hlz) in Hr. congruence.
Qed.

Lemma kcf_backing_le_maps : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= State.live_bytes (vm_maps (m_vmmaps m)).
Proof using.
  intros m Hl Hm. unfold vm_backing_used, vm_backed_maps. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat].
  pose proof (maps_subtract_all_le (vm_noaccess (m_vmmaps m)) (vm_maps (m_vmmaps m))). lia.
Qed.

Lemma kcf_brk_vml : forall req r m, vm_limit (m_vmmaps (brk_model req r m)) = vm_limit (m_vmmaps m).
Proof using.
  intros req r m. unfold brk_model, with_brk_next. cbv zeta.
  assert (H : forall rs m0, m_vmmaps (forget_vm_ranges rs m0) = m_vmmaps m0).
  { induction rs as [|[a n] rs IH]; intros m0; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. }
  rewrite H. reflexivity.
Qed.

Lemma kcf_brk_nx_vml : forall regs pc mem rom model i,
  vml (brk_nx segs regs pc mem rom model i) = vml (mkCfg (pend_at regs pc mem rom) model).
Proof using.
  intros regs pc mem rom model i. unfold vml, brk_nx. cbv zeta. cbn [cfg_model]. apply kcf_brk_vml.
Qed.

(* The policy's window count from the slot room of a placement request: the ledger's entries are the image's
   reserved segments (at most KRES) and one map per slot; its bytes, the reserved ones (2^30) and the live ones. *)
Lemma win_room_of_slots : forall h p st n K B, RoomShapesDraft.policy_ok p ->
  page_round_down_Z (alloc_top h) <= st -> 140735332483072 <= alloc_top h ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= K -> ivs_bytes (vm_reserved h ++ vm_maps h) <= B ->
  B <= AgreeLim.LIM_AG + 2 ^ 30 -> 0 < n <= MG_REQ -> page_round n = n -> K <= slot_capW n ->
  PolicyFit.win_room h p st n.
Proof using.
intros h p st n K B Hp Hst Hc HK HB HBl Hn Hr Hs.
apply (PolicyFit.win_room_of_counts h p st n K B Hp Hst Hc ltac:(lia) HK HB).
pose proof (slot_capW_mul n K ltac:(lia) Hs) as M. rewrite Hr in M.
assert (W : PolicyFit.WNUM = 105367440015360) by (vm_compute; reflexivity).
rewrite W. rewrite AgreeLim.LIM_AG_eq in HBl. unfold WCAPN, MG_REQ, PGSZ in *. unfold page_size. lia.
Qed.

(* At a non-placement request the policy's step is any step. *)
Lemma kcf_fit_nonplacement : forall regs pc mem rom model,
  RoomShapesDraft.placement_len (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model = None ->
  Uniform.canon_fit_at segs (mkCfg (pend_at regs pc mem rom) model).
Proof using.
intros regs pc mem rom model H. apply PolicyFit.canon_fit_svc_nonplacement.
intros x8 Hx. rewrite pend_svc in Hx. injection Hx as <-. exact H.
Qed.

Lemma knode_cf_brk_query : forall regs pc mem rom model snap (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 214 -> getr regs 10 = Z_to_bv 64 0 ->
Kont 1 (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom)
(brk_model (Z_to_bv 64 0) (vm_brk (m_vmmaps model)) model)) ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) KBrkQuery snap Kont.
Proof using.
intros regs pc mem rom model snap Kont Hh Hlz Hno H0 HK.
split; [exact (knode_brk_query segs regs pc mem rom model snap Kont Hh Hlz Hno H0 HK)|]. split; [|split; [|split]].
- intros _. apply (kcf_not_refused (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl).
  + intros eff m' evs Hs. apply (brk_ok_iff segs _ _ model eff m' evs Hno) in Hs.
    destruct Hs as (_ & _ & _ & ->). apply brk_model_lazy. exact Hlz.
  + unfold alloc_budget_refused_b. cbv zeta. rewrite si_sysno, Hno, si_arg0, H0. reflexivity.
- apply (kcf_vml_node _ _ _ _ (node_brk segs regs pc mem rom model Hh Hlz Hno)). intros i. apply kcf_brk_nx_vml.
- cbn [cfg_ms pend_at]. discriminate.
- intros _ _. exact (PolicyFit.canon_fit_brk segs regs pc mem rom model Hh Hlz Hno).
Qed.

Lemma knode_cf_brk_grow : forall regs pc mem rom model snap (npages : Z) (Kont : Z -> config -> Prop),
let b := vm_brk (m_vmmaps model) in
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 214 ->
bv_unsigned (getr regs 10) = bv_unsigned b + PGSZ * npages ->
0 < npages -> 0 < bv_unsigned b -> bv_unsigned b mod page_size = 0 ->
bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned b ->
Kont 0 (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) (brk_model (getr regs 10) b model)) ->
(Mmap.brk_grow_ok model (getr regs 10) (getr regs 10) = true ->
Kont 1 (mkCfg (mkst (regupd regs 10 (getr regs 10)) (v_addi pc 4)
(apply_zeros mem [(b, Z_to_bv 64 (PGSZ * npages))]) rom)
(brk_model (getr regs 10) (getr regs 10) model))) ->
(mgrant snap (KBrkGrow npages) -> Mmap.brk_grow_ok model (getr regs 10) (getr regs 10) = true) ->
m_vm_materialized model = [] ->
State.live_bytes (vm_maps (m_vmmaps model)) <= live_bytes snap ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KBrkGrow npages) snap Kont.
Proof using.
intros regs pc mem rom model snap npages Kont b Hh Hlz Hno Hreq Hn Hb0 Hbal Hs HK0 HK1 HG Hmat Hlb.
pose proof (knode_brk_grow segs regs pc mem rom model snap npages Kont Hh Hlz Hno Hreq Hn Hb0 Hbal Hs HK0 HK1 HG) as Hk0.
subst b. split; [exact Hk0|].
split; [|split; [|split]].
- intros Hroom. specialize (Hroom eq_refl). cbn [req_len] in Hroom. unfold vml in Hroom. cbn [cfg_model] in Hroom.
  pose proof (kcf_backing_le_maps model Hlz Hmat) as Hbk.
  apply (kcf_not_refused (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl).
  + intros eff m' evs Hsp. apply (brk_ok_iff segs _ _ model eff m' evs Hno) in Hsp.
    destruct Hsp as (_ & _ & _ & ->). apply brk_model_lazy. exact Hlz.
  + assert (Hok : Mmap.brk_budget_ok model (getr regs 10) = true).
    { unfold Mmap.brk_budget_ok. cbv zeta. apply Z.leb_le.
      rewrite bv_sub_unsigned_nowrap by (unfold PGSZ in *; lia). unfold PGSZ in *. lia. }
    unfold alloc_budget_refused_b. cbv zeta. rewrite si_sysno, Hno, si_arg0.
    unfold Mmap.brk_budget_refused_b. rewrite Hok. rewrite !andb_false_r. reflexivity.
- apply (kcf_vml_node _ _ _ _ (node_brk segs regs pc mem rom model Hh Hlz Hno)). intros i. apply kcf_brk_nx_vml.
- cbn [cfg_ms pend_at]. discriminate.
- intros _ _. exact (PolicyFit.canon_fit_brk segs regs pc mem rom model Hh Hlz Hno).
Qed.

Lemma knode_cf_mmap_rw : forall regs pc mem rom model snap (len : Z) (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 63 -> getr regs 12 = Z_to_bv 64 3 ->
getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(forall a, grant_ok (getr regs 10) model a (page_round len) = true ->
Kont 1 (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (apply_zeros mem [(a, Z_to_bv 64 (page_round len))]) rom)
(mmap_model a (Z_to_bv 64 (page_round len)) model))) ->
(mgrant snap (KMmapRW len) -> vm_backing_used model + page_round len <= vm_limit (m_vmmaps model) ->
exists a, grant_ok (getr regs 10) model a (page_round len) = true) ->
m_vm_materialized model = [] ->
State.live_bytes (vm_maps (m_vmmaps model)) <= live_bytes snap ->
Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) <= nslots snap + KRES ->
ivs_bytes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= live_bytes snap + 2 ^ 30 ->
140735332483072 <= alloc_top (m_vmmaps model) ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KMmapRW len) snap Kont.
Proof using.
intros regs pc mem rom model snap len Kont Hh Hlz Hno Hlen Hrange Hprot Hflags Hfd Hoff HK0 HK1 HG Hmat Hlb Hcnt Hbyt Hceil.
split; [exact (knode_mmap_rw segs regs pc mem rom model snap len Kont Hh Hlz Hno Hlen Hrange Hprot Hflags Hfd Hoff HK0 HK1 HG)|].
assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0).
{ rewrite Hlen. intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  change (bv_wrap 64 0) with 0 in E. rewrite bv_wrap_small in E; [lia | change (bv_modulus 64) with (2 ^ 64); lia]. }
assert (Hru : page_round_up_Z (bv_unsigned (getr regs 11)) = page_round len).
{ rewrite Hlen, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold page_round_up_Z, page_round, page_size, PGSZ. reflexivity. }
assert (Hargs : mmap_args_ok (pend_at regs pc mem rom)).
{ unfold mmap_args_ok. rewrite pend_gpr1, pend_gpr2, pend_gpr3, pend_gpr4, pend_gpr5. auto. }
split; [|split; [|split]].
- intros Hroom. specialize (Hroom eq_refl). cbn [req_len] in Hroom. unfold vml in Hroom. cbn [cfg_model] in Hroom.
  pose proof (kcf_backing_le_maps model Hlz Hmat) as Hbk.
  apply (kcf_not_refused (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl).
  + intros eff m' evs Hsp. destruct (mmap_ok_inv segs _ _ model eff m' evs Hno Hargs Hsp) as (_ & [(e & _ & _ & ->) | (a & _ & _ & ->)]);
    [exact Hlz | rewrite mmap_model_lazy; exact Hlz].
  + assert (Hw : w_is0 (getr regs 11) = false) by (unfold w_is0; apply bv_eqb_neq; exact Hlen0).
    assert (Hnb : Mmap.mmap_noreserve_backed_ok (Z_to_bv 64 34) model (page_round len) = true).
    { unfold Mmap.mmap_noreserve_backed_ok. replace (Mmap.mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
      cbv beta iota. apply Z.leb_le. lia. }
    unfold alloc_budget_refused_b. cbv zeta.
    rewrite si_sysno, Hno, si_arg0, si_arg1, si_arg2, si_arg3, si_arg4, si_arg5, Hprot, Hflags, Hfd, Hoff.
    unfold Mmap.mmap_budget_refused_b. cbv zeta. rewrite Hw, Hru, Hnb. reflexivity.
- apply (kcf_vml_node _ _ _ _ (node_mmap_rw segs regs pc mem rom model Hh Hlz Hno Hlen0 Hprot Hflags Hfd Hoff)).
  intros [|]; reflexivity.
- cbn [cfg_ms pend_at]. discriminate.
- intros _ Hsl. apply (PolicyFit.canon_fit_mmap_rw segs regs pc mem rom model Hh Hlz Hno Hlen0 Hprot Hflags Hfd Hoff).
  intros p st Hp Hst Hlim. rewrite Hru.
  destruct (Hsl eq_refl Hlim) as (Hlv & Hns & Hrq). cbn [req_len] in Hns, Hrq.
  change (vml (mkCfg (pend_at regs pc mem rom) model)) with (vm_limit (m_vmmaps model)) in Hlv.
  apply (win_room_of_slots _ p st (page_round len) (nslots snap + KRES) (live_bytes snap + 2 ^ 30) Hp Hst Hceil Hcnt Hbyt);
    [lia | exact Hrq | apply page_round_idem | exact Hns].
Qed.

Lemma knode_cf_munmap : forall regs pc mem rom model snap (r : nat) (len : Z) (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 215 ->
bv_unsigned (getr regs 10) mod page_size = 0 -> getr regs 11 <> Z_to_bv 64 0 ->
bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= TASK_SIZE ->
map_has (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
Kont 1 (munmap_nx regs pc mem rom model tt) ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KMunmap r len) snap Kont.
Proof using.
intros regs pc mem rom model snap r len Kont Hh Hlz Hno Hal Hlen Hnw Hhas HK.
split; [exact (knode_munmap segs regs pc mem rom model snap r len Kont Hh Hlz Hno Hal Hlen Hnw Hhas HK)|].
assert (Hargs : munmap_args_ok (pend_at regs pc mem rom) model).
{ unfold munmap_args_ok. rewrite pend_gpr0, pend_gpr1. auto. }
split; [|split; [|split]].
- intros _. apply (kcf_not_refused (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl).
  + intros eff m' evs Hsp. destruct (munmap_ok_inv segs _ _ model eff m' evs Hno Hargs Hsp) as (_ & -> & _).
    apply munmap_model_no_lazy. exact Hlz.
  + unfold alloc_budget_refused_b. cbv zeta. rewrite si_sysno, Hno. reflexivity.
- apply (kcf_vml_node _ _ _ _ (node_munmap segs regs pc mem rom model Hh Hlz Hno Hal Hlen Hnw Hhas)).
  intros []. reflexivity.
- cbn [cfg_ms pend_at]. discriminate.
- intros _ _. apply kcf_fit_nonplacement. unfold RoomShapesDraft.placement_len. cbv zeta.
  rewrite si_sysno, Hno. reflexivity.
Qed.

Lemma knode_cf_mmap_none : forall regs pc mem rom model snap (len : Z) (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 63 -> getr regs 12 = Z_to_bv 64 0 ->
getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(forall a, place_ok (getr regs 10) model a (page_round len) = true ->
Kont 1 (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (apply_unmaps mem [(a, Z_to_bv 64 (page_round len))]) rom)
(mmap_none_model a (Z_to_bv 64 (page_round len)) model))) ->
(mgrant snap (KMmapNone len) -> exists a, place_ok (getr regs 10) model a (page_round len) = true) ->
Z.of_nat (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) <= nslots snap + KRES ->
ivs_bytes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= live_bytes snap + 2 ^ 30 ->
140735332483072 <= alloc_top (m_vmmaps model) ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KMmapNone len) snap Kont.
Proof using.
intros regs pc mem rom model snap len Kont Hh Hlz Hno Hlen Hrange H2 H3 H4 H5 HK0 HK1 HG Hcnt Hbyt Hceil.
split; [exact (knode_mmap_none segs regs pc mem rom model snap len Kont Hh Hlz Hno Hlen Hrange H2 H3 H4 H5 HK0 HK1 HG)|].
assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0).
{ rewrite Hlen. intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  change (bv_wrap 64 0) with 0 in E. rewrite bv_wrap_small in E; [lia | change (bv_modulus 64) with (2 ^ 64); lia]. }
assert (Hru : page_round_up_Z (bv_unsigned (getr regs 11)) = page_round len).
{ rewrite Hlen, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold page_round_up_Z, page_round, page_size, PGSZ. reflexivity. }
split; [|split; [|split]].
- intros _. apply (kcf_not_refused (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl).
  + intros eff m' evs Hsp. apply check_syscall_ok_iff in Hsp.
    rewrite (chk_mmap_none04 segs regs pc mem rom model Hno Hlen0 H2 H3 H4 H5) in Hsp.
    destruct eff as [rv ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos rv).
    * destruct us; [|discriminate]. injection Hsp as <- _. exact Hlz.
    * destruct (_ && _); [|discriminate]. injection Hsp as <- _. rewrite mmap_none_model_lazy. exact Hlz.
  + assert (Hw : w_is0 (getr regs 11) = false) by (unfold w_is0; apply bv_eqb_neq; exact Hlen0).
    unfold alloc_budget_refused_b. cbv zeta.
    rewrite si_sysno, Hno, si_arg0, si_arg1, si_arg2, si_arg3, si_arg4, si_arg5, H2, H3, H4, H5.
    unfold Mmap.mmap_budget_refused_b. cbv zeta. rewrite Hw. reflexivity.
- apply (kcf_vml_node _ _ _ _ (node_mmap_none segs regs pc mem rom model Hh Hlz Hno Hlen0 H2 H3 H4 H5)).
  intros [|]; reflexivity.
- cbn [cfg_ms pend_at]. discriminate.
- intros _ Hsl. apply (PolicyFit.canon_fit_mmap_none segs regs pc mem rom model Hh Hlz Hno Hlen0 H2 H3 H4 H5).
  intros p st Hp Hst Hlim. rewrite Hru.
  destruct (Hsl eq_refl Hlim) as (Hlv & Hns & Hrq). cbn [req_len] in Hns, Hrq.
  change (vml (mkCfg (pend_at regs pc mem rom) model)) with (vm_limit (m_vmmaps model)) in Hlv.
  apply (win_room_of_slots _ p st (page_round len) (nslots snap + KRES) (live_bytes snap + 2 ^ 30) Hp Hst Hceil Hcnt Hbyt);
    [lia | exact Hrq | apply page_round_idem | exact Hns].
Qed.

Lemma knode_cf_mprotect : forall regs pc mem rom model snap (p : sptr) (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 226 ->
bv_unsigned (getr regs 10) mod page_size = 0 ->
getr regs 11 = Z_to_bv 64 4096 ->
bv_unsigned (getr regs 10) + 4096 < two_pow_64 ->
getr regs 12 = Z_to_bv 64 3 ->
map_contains (vm_noaccess (m_vmmaps model)) (getr regs 10) (Z_to_bv 64 4096) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (Z_to_bv 64 4096) = true ->
(forall e, In e mprotect_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(mprotect_budget_ok model (getr regs 10) (Z_to_bv 64 4096) = true ->
Kont 1 (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (apply_zeros mem [(getr regs 10, Z_to_bv 64 4096)]) rom)
(mprotect_model (getr regs 10) (Z_to_bv 64 4096) model))) ->
m_vm_materialized model = [] ->
State.live_bytes (vm_maps (m_vmmaps model)) <= live_bytes snap ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) (KMprotect p) snap Kont.
Proof using.
intros regs pc mem rom model snap p Kont Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma HK0 HK1 Hmat Hlb.
split; [exact (knode_mprotect segs regs pc mem rom model snap p Kont Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma HK0 HK1)|].
assert (Hpr : page_round_up (getr regs 11) = Z_to_bv 64 4096) by (rewrite Hlen; reflexivity).
assert (HprZ : page_round_up_Z (bv_unsigned (getr regs 11)) = 4096) by (rewrite Hlen; reflexivity).
assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0) by (rewrite Hlen; discriminate).
assert (Hnw' : bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) < two_pow_64) by (rewrite HprZ; exact Hnw).
assert (Hna' : map_contains (vm_noaccess (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true) by (rewrite Hpr; exact Hna).
assert (Hma' : map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true) by (rewrite Hpr; exact Hma).
split; [|split; [|split]].
- intros Hroom. specialize (Hroom eq_refl). cbn [req_len] in Hroom. unfold vml in Hroom. cbn [cfg_model] in Hroom.
  apply (kcf_not_refused (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl).
  + intros eff m' evs Hsp. apply check_syscall_ok_iff in Hsp.
    rewrite (chk_mprotect_rw04 segs regs pc mem rom model Hno Hal Hlen0 Hnw' Hprot Hna' Hma') in Hsp.
    destruct eff as [rv ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    destruct (errno_ret_in mprotect_errnos rv).
    * destruct zs; [|discriminate]. injection Hsp as <- _. exact Hlz.
    * destruct (_ && _ && _); [|discriminate]. injection Hsp as <- _. rewrite mprotect_model_lazy. exact Hlz.
  + assert (Hb : mprotect_budget_ok model (getr regs 10) (Z_to_bv 64 4096) = true).
    { unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
      pose proof (kcf_backing_le_maps (mprotect_model_next model (getr regs 10) (Z_to_bv 64 4096)) Hlz Hmat) as Hbk.
      change (vm_maps (m_vmmaps (mprotect_model_next model (getr regs 10) (Z_to_bv 64 4096)))) with (vm_maps (m_vmmaps model)) in Hbk.
      change (vm_limit (m_vmmaps (mprotect_model_next model (getr regs 10) (Z_to_bv 64 4096)))) with (vm_limit (m_vmmaps model)).
      unfold PGSZ in Hroom. lia. }
    unfold alloc_budget_refused_b. cbv zeta.
    rewrite si_sysno, Hno, si_arg0, si_arg1, si_arg2, Hlen, Hprot.
    unfold Mprotect.mprotect_budget_refused_b. cbv zeta.
    change (page_round_up_Z (bv_unsigned (Z_to_bv 64 4096))) with 4096.
    rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.leb_gt _ _) Hnw), Hna, Hma, Hb. reflexivity.
- apply (kcf_vml_node _ _ _ _ (node_mprotect_rw segs regs pc mem rom model Hh Hlz Hno Hal Hlen0 Hnw' Hprot Hna' Hma')).
  intros [|]; reflexivity.
- cbn [cfg_ms pend_at]. discriminate.
- intros _ _. apply kcf_fit_nonplacement. unfold RoomShapesDraft.placement_len. cbv zeta.
  rewrite si_sysno, Hno. reflexivity.
Qed.

Lemma knode_cf_guard : forall regs pc mem rom model snap (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 = Z_to_bv 64 4096 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
bv_unsigned (getr regs 10) mod page_size = 0 -> 0 < bv_unsigned (getr regs 10) ->
bv_unsigned (getr regs 10) + 4096 <= alloc_top (m_vmmaps model) ->
region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (Z_to_bv 64 4096) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (Z_to_bv 64 4096) = true ->
(forall i : fixed_J, Kont 1 (fixed_nx regs pc mem rom model i)) ->
knode_cf segs (mkCfg (pend_at regs pc mem rom) model) KGuard snap Kont.
Proof using.
intros regs pc mem rom model snap Kont Hh Hlz Hno Hlen H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont HK.
split; [exact (knode_guard segs regs pc mem rom model snap Kont Hh Hlz Hno Hlen H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont HK)|].
assert (Hpr : page_round_up (getr regs 11) = Z_to_bv 64 4096) by (rewrite Hlen; reflexivity).
assert (HprZ : page_round_up_Z (bv_unsigned (getr regs 11)) = 4096) by (rewrite Hlen; reflexivity).
assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0) by (rewrite Hlen; discriminate).
assert (Hceil' : bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= alloc_top (m_vmmaps model)) by (rewrite HprZ; exact Hceil).
assert (Hfree' : region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true) by (rewrite Hpr; exact Hfree).
assert (Hcont' : map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true) by (rewrite Hpr; exact Hcont).
split; [|split; [|split]].
- intros _. apply (kcf_not_refused (pend_at regs pc mem rom) model (getr regs 17) Hh eq_refl).
  + intros eff m' evs Hsp. apply check_syscall_ok_iff in Hsp.
    rewrite (chk_mmap_fixed_none04 segs regs pc mem rom model Hno Hlen0 H2 H3 H4 H5 Hal Hpos Hceil' Hfree' Hcont') in Hsp.
    destruct eff as [rv ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos rv).
    * destruct us; [injection Hsp as <- _; exact Hlz|].
      destruct (listNN_eqb _ _); [|discriminate]. injection Hsp as <- _. apply mmap_fixed_destroyed_model_lazy. exact Hlz.
    * destruct (_ && _); [|discriminate]. injection Hsp as <- _. apply mmap_fixed_model_lazy. exact Hlz.
  + assert (Hw : w_is0 (getr regs 11) = false) by (unfold w_is0; apply bv_eqb_neq; exact Hlen0).
    unfold alloc_budget_refused_b. cbv zeta.
    rewrite si_sysno, Hno, si_arg0, si_arg1, si_arg2, si_arg3, si_arg4, si_arg5, H2, H3, H4, H5.
    unfold Mmap.mmap_budget_refused_b. cbv zeta. rewrite Hw. reflexivity.
- apply (kcf_vml_node _ _ _ _ (node_mmap_fixed_none segs regs pc mem rom model Hh Hlz Hno Hlen0 H2 H3 H4 H5 Hal Hpos Hceil' Hfree' Hcont')).
  intros i. reflexivity.
- cbn [cfg_ms pend_at]. discriminate.
- intros _ _. apply kcf_fit_nonplacement. unfold RoomShapesDraft.placement_len. cbv zeta.
  rewrite si_sysno, Hno, si_arg3, H3.
  match goal with |- context [andb ?a ?b] => replace (andb a b) with false by (vm_compute; reflexivity) end.
  reflexivity.
Qed.
End f.
End d.

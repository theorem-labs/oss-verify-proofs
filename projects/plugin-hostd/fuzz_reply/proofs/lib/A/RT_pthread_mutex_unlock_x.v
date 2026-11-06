(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract of musl's pthread_mutex_unlock on fuzz_reply.asan,
   W_sites.v's aunlock_realizes at PB_fr and fr_sigma WS_pthread_mutex_unlock (0x98d28), in the vocabulary of
   proofs/cgif/cgif_file_fuzzer/lib/A/AF0r.v + AF0s.v (a symbolic run on a code table of frsegs, SRr_ret_at for
   the ret, the allocator's frame law for AR after the writes).  The functional template is fuzz_reply's own plain
   proof of the same code, lib/Prog/pthread_mutex_unlock.v.  The path (objdump lines 109220-109323): the 96-byte
   frame saves ra, s0-s9; waiters (A+8) = 0 and type (A) = 0 send the normal-mutex arm to 0x98e18, where
   lr.w/sc.w on the lock word A+4 (16) store 0; with waiters 0 no futex wake is made; a0 = 0; the frame is
   restored and the function returns.  Every branch on the path is decided from the literals of the pre. *)
(* Modified by Theorem Labs, 2026-10-29: from lib/A/RT_pthread_mutex_unlock.v, as the module RT_pthread_mutex_unlock_x: cut to the proof of rt_pthread_mutex_unlock (the helper lemmas are used by Import) and restated over a generic allocator invariant ARx under lib/Rt/RTx.v's rt_laws (rt_pthread_mutex_unlock_x); the corollaries rt_pthread_mutex_unlock_of_x (rt_pthread_mutex_unlock's statement, unchanged) and rt_pthread_mutex_unlock_cf added. *)
(* lib/A/RT_pthread_mutex_unlock.v's runtime contract rt_pthread_mutex_unlock
   restated over a generic allocator invariant ARx (ghost head set Hp threaded) under the five-law record rt_laws of
   lib/Rt/RTx.v (a Theorem Labs lane's, the one record for both images: rtl_frame, rtl_stack, rtl_const, rtl_layout,
   rtl_const_cells). RT_pthread_mutex_unlock.v is not edited; its helper lemmas are used by Import. The statement is
   W_sites_x.v's aunlock_realizes_x; the proof of rt_pthread_mutex_unlock_x is RT_pthread_mutex_unlock.v's with AR ->
   ARx (am_layout of proj1 HAR -> rtl_layout, al_frame / al_stack -> rtl_frame / rtl_stack, RT_kit / RT_post's AR
   lemmas -> their _x forms there).
   Measured (lines at a working branch 9b1367c7fe1): the original reads AR through
   al_frame (:187), al_stack (:192) and the ARm field am_layout (:123), the layout law here; a Theorem Labs lane's three-law
   note (RESUME.md:116-122 sha256 704eb9d3afa6; internal record) did not count the ARm fields, hence the record's rtl_layout and rtl_const_cells.
   At the end: rt_pthread_mutex_unlock_cf, the twin at ARx := ARcf with the laws from AR_laws_cf (RTx.rt_laws_cf).
   QMm W1 (2026-10-31): aunlock_realizes_x now takes the not-kept premise on the lock word, which the cgif rule
   does not, so rt_pthread_mutex_unlock_of_x (the cgif statement from this twin) no longer follows and had no user;
   it is gone. RT_pthread_mutex_unlock.v still proves the cgif statement itself. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_kit W_journal W_contract W_sites W_tbl W_place W_img AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_pthread_mutex_unlock.
Open Scope Z_scope.
(* the libraries Required above (FCiface -> YF0v; the cf files) set Zify's euclidean-division flag to false
   globally (e.g. Reusable/Q/YW06_cf.v:26); the original's lia steps need it on, as in the original's own build *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module FCI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Module CFN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Module NCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Module DCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module WSX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_sites_x.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- THE SITE CONTRACT over ARx ---- *)
Theorem rt_pthread_mutex_unlock_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx ->
WSX.aunlock_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_pthread_mutex_unlock).
Proof.
intros B ARx LAWS. unfold WSX.aunlock_realizes_x.
intros ly S hps W regs mem md A HPRE H10 HA0 HA4 HA12 V0 V4 V8 HIN HDEST _.
change (@pa_segs _ _ PB_fr) with frsegs in *.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Hshi & Hpres & Hgp & Htp).
pose proof (RTX.rtl_layout _ _ _ LAWS ly S hps W mem md HAR) as HLY.
pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi. unfold ESTACK in *.
remember (Ereg regs []) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite HE; exact (ew_Ereg_nat regs [] 2 2%bv eq_refl)).
assert (E10 : ew E 10 = w64 A) by (rewrite HE, <- H10; exact (ew_Ereg_nat regs [] 10 10%bv eq_refl)).
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = A) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (VB2 : base_val E (Some 2%nat) = spZ regs) by exact U2.
assert (VB10 : base_val E (Some 10%nat) = A) by exact U10.
pose proof (proj2 (HIN A ltac:(lia))) as N0. pose proof (proj2 (HIN (A + 11) ltac:(lia))) as N11.
pose proof (entry_st_ok_full frsegs UNL_ENTRY sr_atoms regs [] unl_regions unl_facts (mrestrict (w_H W) mem)) as ENT.
rewrite <- HE in ENT.
assert (HS0 : st_ok frsegs E ss_unl (restrict (w_H W) (mkst regs (Z_to_bv 64 UNL_ENTRY) mem (seg_rom frsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_unl. apply ENT.
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold unl_regions. repeat apply Forall_cons; try apply Forall_nil.
    + apply (region_ok_stack frsegs E _ 2 (spZ regs) (-96)); [exact U2 | lia | lia |].
      intros a Ha. apply (apresent_writable frsegs). apply Hpres. lia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite VB10. split; [lia|]. split; [lia|]. split.
      * intros o Ho. exact (proj1 (HDEST (A + o) ltac:(lia))).
      * repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val frsegs E _ A 0 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
           rewrite Z.add_0_r. exact V0.
        -- apply (chunk_ok_val frsegs E _ A 4 4 (SLit 16) 16); [reflexivity | cbn; lia | cbn; lia | exact V4].
        -- apply (chunk_ok_val frsegs E _ A 8 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V8].
  - apply pairwise_disjoint_of_extents. unfold unl_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB2, VB10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; exact I]. cbn [unl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U10. change (2 ^ 4) with 16. change (2 ^ 2) with 4.
    repeat split; lia. }
unfold cfg_at. change (w64 (fr_sigma WS_pthread_mutex_unlock)) with (Z_to_bv 64 UNL_ENTRY).
apply (SRr_run_stop_grows W 200%N E ss_unl e_unl (SR_jalr (SOff 1 0))
  (mkst regs (Z_to_bv 64 UNL_ENTRY) mem (seg_rom frsegs)) md _ HS0 r_unl).
intros ms1 mat1 HS1 HF HG. cbn [ms_mem mkst] in HF, HG.
(* the memory after the run: outside the frame and the lock word it is the entry's *)
assert (MEQ : forall x : word, ~ (spZ regs - 96 <= bv_unsigned x < spZ regs) -> ~ (A + 4 <= bv_unsigned x < A + 8) ->
  ms_mem ms1 x = mem x).
{ intros x Hx1 Hx2. apply HF. intros Hin.
  destruct (unl_wrange E (spZ regs) A (bv_unsigned x) U2 U10 Hin) as [Hw|Hw]; contradiction. }
assert (AVQ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) -> ~ (A + 4 <= a < A + 8) ->
  aview frsegs (w_H W) (ms_mem ms1) a = aview frsegs (w_H W) mem a).
{ intros a Ha Hn1 Hn2. apply (aview_eq_of frsegs). unfold mrestrict.
  rewrite MEQ; [reflexivity | |]; rewrite unsigned_lit_small by lia; assumption. }
assert (RD : forall r, getr (ms_regs ms1) r = sv_denot E (sr_get (ss_regs e_unl) r))
  by (intros r; exact (st_ok_restrict_reg frsegs (w_H W) E e_unl ms1 r HS1)).
assert (R1 : getr (ms_regs ms1) 1 = getr regs 1).
{ rewrite RD. replace (sr_get (ss_regs e_unl) 1) with (SOff 1 0) by (vm_compute; reflexivity).
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E1. }
assert (R10 : getr (ms_regs ms1) 10 = w64 0).
{ rewrite RD. replace (sr_get (ss_regs e_unl) 10) with (SLit 0) by (vm_compute; reflexivity). reflexivity. }
eapply (SRr_ret_at frsegs tbl_unl tbl_unl_ok fr_wx W E e_unl ms1 _ _ HS1); [reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse.
unfold WSX.aentry_post_x. split; [reflexivity|].
exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split.
{ unfold cfg_at, raZ, w64. rewrite R1, Hra, Z_to_bv_bv_unsigned. reflexivity. }
split.
{ (* ARx after the writes, by the allocator's frame law: the frame is stack, the lock word is not owned *)
  apply (RTX.rtl_frame _ _ _ LAWS ly S hps W mem md); [exact HAR | | | reflexivity | reflexivity | reflexivity |].
  - intros a Ha Hown.
    assert (CS : (spZ regs - 96 <= a < spZ regs) \/ (A + 4 <= a < A + 8) \/
      (~ (spZ regs - 96 <= a < spZ regs) /\ ~ (A + 4 <= a < A + 8))) by lia.
    destruct CS as [Hs|[Hl|[Hn1 Hn2]]].
    + exfalso. exact (RTX.rtl_stack _ _ _ LAWS ly S hps W mem md a HAR ltac:(lia) Hown).
    + exfalso. exact (proj1 (proj2 (HDEST a ltac:(lia))) Hown).
    + exact (AVQ a Ha Hn1 Hn2).
  - intros a Hv. exact (aview_grows_mr (w_H W) mem (ms_mem ms1) a HG Hv).
  - intros a _ Hh. apply MEQ.
    + intros Hw. pose proof (proj1 (Hpres (bv_unsigned (w64 a)) ltac:(lia))) as Hv.
      rewrite Z_to_bv_bv_unsigned in Hv. congruence.
    + intros Hw. pose proof (proj1 (HDEST (bv_unsigned (w64 a)) ltac:(lia))) as Hwr.
      unfold writable_at in Hwr. rewrite Z_to_bv_bv_unsigned in Hwr.
      rewrite (wview_restrict frsegs (w_H W) (w_Hoff W)) in Hwr. rewrite Hh in Hwr. exact (Hwr eq_refl). }
split.
{ exact (aregs_preserved_of_st_ok frsegs (w_H W) E e_unl ms1 regs [] HS1 ltac:(rewrite HE; apply env_agree_refl)
    ltac:(vm_compute; reflexivity)). }
split; [apply with_vm_backing_same|].
split.
{ split; [exact R10|].
  pose proof (st_ok_mem_ok frsegs E e_unl _ HS1) as (_ & ROK & _).
  pose proof (proj1 (Forall_forall _ _) ROK rA_end rA_end_in) as OKA.
  unfold region_ok in OKA. destruct OKA as (_ & _ & _ & CH).
  pose proof (proj1 (Forall_forall _ _) CH _ (proj2 rA_end_shape)) as C4.
  rewrite (proj1 rA_end_shape) in C4. cbn [base_val] in C4. rewrite U10 in C4.
  exact (val_of_chunk_ok frsegs E _ A 4 4 (SLit 0) 0 C4 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
split.
{ intros a Ha Hn1 Hn2. apply AVQ; [exact Ha | intros Hs; apply Hn2; lia | exact Hn1]. }
intros a Hp. exact (apresent_grows (w_H W) mem (ms_mem ms1) a HG Hp).
Qed.



(* ---- the instance at ARcf, the laws from AR_laws_cf ---- *)
Section cf. Context {ci : CFN.CfImg} {cp : CFN.CfParams}.
Corollary rt_pthread_mutex_unlock_cf : forall B, DCF.AR_laws_cf frsegs B ->
  WSX.aunlock_realizes_x (PI := PB_fr) B (NCF.ARcf frsegs B) (fr_sigma WS_pthread_mutex_unlock).
Proof.
  intros B L.
  exact (rt_pthread_mutex_unlock_x B (NCF.ARcf frsegs B) (RTX.rt_laws_cf frsegs B L)).
Qed.
End cf.

End core.

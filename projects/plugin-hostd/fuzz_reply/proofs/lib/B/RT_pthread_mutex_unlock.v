(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract of musl's pthread_mutex_unlock on fuzz_reply.asan-ubsan,
   W_sites.v's aunlock_realizes at PB_fr and fr_sigma WS_pthread_mutex_unlock (0x992a8), in the vocabulary of
   proofs/cgif/cgif_file_fuzzer/lib/A/AF0r.v + AF0s.v (a symbolic run on a code table of frsegs, SRr_ret_at for
   the ret, the allocator's frame law for AR after the writes).  The functional template is fuzz_reply's own plain
   proof of the same code, lib/Prog/pthread_mutex_unlock.v.  The path (objdump lines 109556-109659): the 96-byte
   frame saves ra, s0-s9; waiters (A+8) = 0 and type (A) = 0 send the normal-mutex arm to 0x99398, where
   lr.w/sc.w on the lock word A+4 (16) store 0; with waiters 0 no futex wake is made; a0 = 0; the frame is
   restored and the function returns.  Every branch on the path is decided from the literals of the pre. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_pthread_mutex_unlock.v at commit f1fb3bc1169, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (15 numerals; per-numeral report). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_kit W_journal W_contract W_sites W_tbl W_place W_img YE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition UNL_ENTRY : Z := 0x992a8.
(* The code table: pthread_mutex_unlock's 122 words, 0x992a8 .. 0x9948c. *)
Definition tbl_unl : ctable := Eval vm_compute in build_table frsegs UNL_ENTRY 122 TEmpty.
Lemma tbl_unl_eq : tbl_unl = build_table frsegs UNL_ENTRY 122 TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_unl). Qed.
Lemma tbl_unl_ok : table_ok frsegs tbl_unl.
Proof. rewrite tbl_unl_eq. apply build_table_ok0. cbv. discriminate. Qed.

(* Build identity: ofl_head of the ASan-UBSan build, the first words of main (0x81ea4, addi sp,sp,-80) and of
   LLVMFuzzerTestOneInput (0x84408, addi sp,sp,-320) in frsegs, the site address, and the first word of the
   entry (addi sp,sp,-96). *)
Lemma rt_unlock_build_id :
(A_ofl_head, clookup (build_table frsegs 0x81ea4 1 TEmpty) 0x81ea4,
 clookup (build_table frsegs 0x84408 1 TEmpty) 0x84408, fr_sigma WS_pthread_mutex_unlock, clookup tbl_unl UNL_ENTRY)
= (0x5fa0e8, Some 0xfb010113, Some 0xec010113, UNL_ENTRY, Some 0xfa010113).
Proof. vm_compute. reflexivity. Qed.

(* The entry state: the frame [sp-96, sp) and the mutex's three words at A (type 0, lock 16, waiters 0), of which
   only the lock word [A+4, A+8) is writable. *)
Definition unl_regions : smem :=
[ YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 [];
  YP09.mkRegion (Some 10%nat) 0 12 4 8
  [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 4 (CVal 4 (SLit 16)); YP09.mkChunk 8 (CVal 4 (SLit 0))] ].
Definition unl_facts : facts :=
mkFacts [ (2%nat, mkAF 4096 (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 63 - 12) 2) ] [] [].
Definition ss_unl : sstate := mkSS UNL_ENTRY sr_atoms unl_regions None unl_facts.
Definition e_unl : sstate := Eval vm_compute in fst (sym_runN frsegs tbl_unl 200 ss_unl).
(* The run stops at the ret (0x99440), whose target ra is the atom of register 1. *)
Lemma r_unl : sym_runN frsegs tbl_unl 200 ss_unl = (e_unl, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Definition rA_end : YP09.region := Eval vm_compute in nth 1 (ss_mem e_unl) (YP09.mkRegion None 0 0 0 0 []).
Lemma rA_end_in : In rA_end (ss_mem e_unl).
Proof. vm_compute. right. left. reflexivity. Qed.
Lemma rA_end_shape : YP09.r_base rA_end = Some 10%nat /\ In (YP09.mkChunk 4 (CVal 4 (SLit 0))) (YP09.r_chunks rA_end).
Proof. split; [reflexivity | vm_compute; left; reflexivity]. Qed.

Lemma unl_wrange : forall E sp A x, bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 10) = A ->
in_wrange E unl_regions x -> (sp - 96 <= x < sp) \/ (A + 4 <= x < A + 8).
Proof.
intros E sp A x H2 H10 (r & Hin & Hr). unfold unl_regions in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
[rewrite H2 in Hr | rewrite H10 in Hr]; lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma aview_grows_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> aview frsegs H m a <> None -> aview frsegs H m' a <> None.
Proof.
intros H m m' a Hg. unfold aview, mbyte.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E1.
- intros _. destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|] eqn:E2; [cbn; discriminate|].
  exfalso. apply (Hg (Z_to_bv 64 a)); [rewrite E1; discriminate | exact E2].
- intros Hv. destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|]; [cbn; discriminate | exact Hv].
Qed.

(* YA0o.v's SRr_run_gen for a run that stops, which also hands on that the visible memory only grew (the
   concrete steps only write), so presence and visibility survive the writes to the windows. *)
Lemma SRr_run_stop_grows : forall W n E ss ss' why ms model Q,
st_ok frsegs E ss (restrict (w_H W) ms) ->
sym_runN frsegs tbl_unl n ss = (ss', RS_stopped why) ->
(forall ms' mat', st_ok frsegs E ss' (restrict (w_H W) ms') ->
 frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
 mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
 SRr frsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q) ->
SRr frsegs W (mkCfg ms model) Q.
Proof.
intros W n E ss ss' why ms model Q HS Hrun Hk.
destruct (msteps_run_gen frsegs tbl_unl tbl_unl_ok n E ss ss' (RS_stopped why) _ HS Hrun) as (msr' & Hms & HS' & Hfr).
pose proof (msteps_mem_grows frsegs _ _ Hms) as Hg.
apply (SRr_msteps frsegs fr_wx W ms msr' model Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
  with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
  rewrite Hrr. exact Hg.
Qed.

Theorem rt_pthread_mutex_unlock : forall B, AR_laws frsegs B ->
aunlock_realizes (PI := PB_fr) B (fr_sigma WS_pthread_mutex_unlock).
Proof.
intros B LAWS. unfold aunlock_realizes.
intros ly S W regs mem md A HPRE H10 HA0 HA4 HA12 V0 V4 V8 HIN HDEST.
change (@pa_segs _ _ PB_fr) with frsegs in *.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Hshi & Hpres & Hgp & Htp).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
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
unfold aentry_post. split; [reflexivity|].
exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split.
{ unfold cfg_at, raZ, w64. rewrite R1, Hra, Z_to_bv_bv_unsigned. reflexivity. }
split.
{ (* AR after the writes, by the allocator's frame law: the frame is stack, the lock word is not owned *)
  apply (al_frame _ _ LAWS ly S W mem md); [exact HAR | | | reflexivity | reflexivity | reflexivity |].
  - intros a Ha Hown.
    assert (CS : (spZ regs - 96 <= a < spZ regs) \/ (A + 4 <= a < A + 8) \/
      (~ (spZ regs - 96 <= a < spZ regs) /\ ~ (A + 4 <= a < A + 8))) by lia.
    destruct CS as [Hs|[Hl|[Hn1 Hn2]]].
    + exfalso. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
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

End a.

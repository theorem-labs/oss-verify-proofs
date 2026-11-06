(* reac-pw/fuzz_link, image A: kernel's chunk-loop LATCH, kin_latch (+0x2100) -> kin_head (+0x51c) / kin_exit (+0x2140)
   (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 4; cuts in kernel_defs.v).

   WHAT THE CODE DOES HERE (listing (internal path) (internal record, sha256 7bc02d6772b3)):
     +0x2100  addiw s6, s6, 1        s6 := ci + 1
     +0x2104  ld    a0, 0x60(s1)      a0 := c (spill slot KS_C)
     +0x2108  beq   s6, a0, +0x2140   the last chunk: kin_exit
     +0x210c  j     +0x51c            the next chunk: kin_head at ci + 1 < c
   No store, no call, no instrumented check.

   THE PROOF. The state at +0x2100 is rebuilt symbolically from kin_latch: registers `sr_atoms` over the env
   `Eimg (Ereg regs [c])`, one read-only region, the slot KS_C at s1 + 0x60 holding atom 32 = c. The engine runs to
   the `beq` (s6 = SAluw ALU_ADD (SOff 22 0) (SLit 1)), the branch splits on ci + 1 = c, and each arm runs to its
   cut. The run has no writable window, so the memory at the cut is the memory at +0x2100 (kn_mem_eq), and
   kn_kat_move carries every memory clause of `kat` (saved words, F, its shadow, the slots, the journal's
   bookkeeping, the kept clauses, the cursor, g_nl, long_alias) across unchanged; the registers are read off the
   symbolic state (kn_regs_kept, kn_denot_inc).
   Section hypotheses: LAWS : AR_laws pa_segs B (the lib/A frame), for the run instances paj_run_x / paj_run_to_x.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK1g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the symbolic state at +0x2100: the slot KS_C (s1 + 0x60) holds atom 32 = c; no writable window ---- *)
Definition kn_lt_Bx : sv := SOff 20 0.
Definition kn_lt_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition kn_lt_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) KS_C (KS_C + 8) 0 0 [YP09.mkChunk KS_C (CVal 8 (SOff 32 0))].
Definition kn_lt_ss : sstate := mkSS (kpc KP_LATCH) sr_atoms [kn_lt_slot] None (mkFacts [] [] []).

(* the registers the latch does not write (those of kregs0 and kregs_chunk but s6) *)
Definition kn_lt_keptz : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25].
Definition kn_lt_kept : list (bv 5) := map (Z_to_bv 5) kn_lt_keptz.
Lemma kn_lt_in_kept : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) kn_lt_keptz = true -> In r kn_lt_kept.
Proof.
  intros r Hr. apply existsb_exists in Hr. destruct Hr as (z & Hz & Hq). apply Z.eqb_eq in Hq.
  unfold kn_lt_kept.
  replace r with (Z_to_bv 5 z)
    by (rewrite <- Hq; first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned]).
  apply in_map. exact Hz.
Qed.

(* A region list with no writable window has no byte in a writable range. *)
Lemma kn_no_wrange : forall E rs a,
  in_wrange E rs a -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> False.
Proof.
  intros E rs a (r & Hin & Hr) Hrs. rewrite forallb_forall in Hrs. specialize (Hrs r Hin).
  apply Z.leb_le in Hrs. lia.
Qed.

(* A run with no writable window keeps the memory: frame_of on every byte. *)
Lemma kn_mem_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> m' = m.
Proof.
  intros E rs m m' Hfr Hrs. apply functional_extensionality. intros x. apply Hfr.
  intros Hx. exact (kn_no_wrange E rs _ Hx Hrs).
Qed.

(* s6 after `addiw s6, s6, 1` from s6 = ci *)
Lemma kn_denot_inc : forall E (ci : Z), ew E 22%nat = w64 ci -> 0 <= ci < 2 ^ 30 ->
  sv_denot E (SAluw ALU_ADD (SOff 22 0) (SLit 1)) = Z_to_bv 64 (ci + 1).
Proof.
  intros E ci H Hci.
  assert (U : bv_unsigned (w64 ci) = ci) by (unfold w64; apply unsigned_lit_small; lia).
  cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned, YK1g.aluw_addi_lit.
  apply bv_eq. rewrite (v_addiw_small (w64 ci) 1) by (try rewrite U; lia). rewrite U.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* `beq` on two values *)
Lemma kn_beq_val : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold branch_taken, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.

(* A machine state at a cut is the one `mkst` builds. *)
Lemma kn_ms_shape : forall (ms : machine_state) (pc : Z),
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (w64 pc) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros [rg fr pcv sv rv fc mm rm] pc H1 H2 H3 H4 H5 H6.
  cbn in H1, H2, H3, H4, H5, H6. subst. reflexivity.
Qed.

(* THE STATE MOVE for a phase that writes no memory: a cut at pc with registers rl and slots sl gives the cut at pc'
   with registers rl' and any sub-list of the slots, at a machine state with the same memory and a model with the
   same descriptors and file system. *)
Lemma kn_kat_move : forall cx fpos pc pc' rl rl' sl sl' sh live adv g k2 ly3 S3 W3 ms3 md3 ms' md',
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms' -> ms_mem ms' = ms_mem ms3 -> kregs0 cx ms' -> kregs_eq ms' rl' -> incl sl' sl ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos pc pc' rl rl' sl sl' sh live adv g k2 ly3 S3 W3 ms3 md3 ms' md'
    (_ & _ & _ & HSV & HFRM & HSH & HSL & HJB & HKP & HCU & HGN & HLA) HMS HM HR0 HRL Hsl Hfds Hfs.
  unfold kat. unfold ksaved, kframe, kshadow, kslots_eq, kkept, kcursor, kgnl_at, kla_at in *.
  rewrite HM.
  split; [exact HMS|]. split; [exact HR0|]. split; [exact HRL|]. split; [exact HSV|].
  split; [exact HFRM|]. split; [exact HSH|].
  split; [rewrite Forall_forall in HSL |- *; intros ov Hov; exact (HSL ov (Hsl ov Hov))|].
  split.
  { unfold kjbk in HJB |- *. destruct HJB as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
    refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj (eq_trans Hfds H6) (eq_trans Hfs H7))))))). }
  split; [exact HKP|]. split; [exact HCU|]. split; [exact HGN | exact HLA].
Qed.

(* The registers the latch does not write are the ones at +0x2100. *)
Lemma kn_regs_kept : forall E (regs0 : bvmap 5 word) extra ss (ms : machine_state) (H : word -> bool),
  YP06.env_agree 32 (Ereg regs0 extra) E ->
  st_ok_pi SEGS pa_val E ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) kn_lt_kept = true ->
  forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) kn_lt_keptz = true ->
  getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros E regs0 extra ss ms H HA HS Hl r Hr.
  exact (regs_kept_of_st_ok_pi E ss (restrict H ms) regs0 extra kn_lt_kept HS HA Hl r (kn_lt_in_kept r Hr)).
Qed.

Theorem kn_latch : forall POST (Rc Rc' : kcx -> Z -> Prop),
  (forall cx v, Rc cx v -> 2 <= v -> Rc' cx (v - 1)) ->
  kfrom SK B POST (kin_head B Rc') -> kfrom SK B POST (kin_exit B) -> kfrom SK B POST (kin_latch B Rc).
Proof.
intros POST Rc Rc' HRc Hhead Hexit.
intros cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
pose proof HK as (HMS & HR0 & HRL & _ & _ & _ & HSL & _).
pose proof HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
unfold kregs_eq, kregs_chunk in HRL. rewrite !Forall_cons_iff in HRL.
destruct HRL as (R19 & R21 & R22 & R24 & R25 & _). cbn [fst snd] in R19, R21, R22, R24, R25.
(* the slot KS_C *)
assert (HSLC : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + KS_C) = Some c).
{ unfold kslots_eq in HSL. rewrite Forall_forall in HSL. apply (HSL (KS_C, c)).
  unfold kslots_setup. cbn [In]. repeat (first [left; reflexivity | right]). }
(* s1 lies in the stack, far from 0 and from 2 ^ 64 *)
pose proof HB as (HPRE & _).
pose proof HPRE as (HJ0 & HGok & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
assert (Hceil : alloc_ceiling <= k_sp0 cx - k_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ0).
pose proof asan_consts as ((C1a & C1b) & _).
assert (HAK : KERNEL_AK = 4640) by reflexivity.
assert (Hspw : 0 <= spZ (k_regs cx) < 2 ^ 64) by (unfold spZ; apply getr_rng).
assert (Hsp1 : 0 <= ksp1 cx /\ ksp1 cx + 0x68 <= 2 ^ 64).
{ clear - Hwlo Hceil C1a HAK Hspw. unfold ksp1, ksp1_of, ksp, KN_MFRAME. rewrite HAK in Hwlo. lia. }
(* the env: registers, atom 32 = c *)
remember (Eimg (Ereg (ms_regs ms3) [w64 c])) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 c]) E).
{ subst E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (E9 : ew E 9%nat = w64 (ksp1 cx)).
{ subst E. rewrite <- A9. apply ew_Eimg_Ereg_nat. reflexivity. }
assert (E22 : ew E 22%nat = w64 ci).
{ subst E. rewrite <- R22. apply ew_Eimg_Ereg_nat. reflexivity. }
assert (E32 : ew E 32%nat = w64 c).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ms_regs ms3) [w64 c] 0). }
(* the symbolic state at +0x2100 *)
assert (HS : st_ok_pi SEGS pa_val E kn_lt_ss (restrict (w_H W3) ms3)).
{ rewrite (kn_ms_shape ms3 (BASE + kpc KP_LATCH) Hpc Hrv Hsvc Hrom Hfr Hfc).
  rewrite restrict_mkst_fx. unfold kn_lt_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold kn_lt_slot, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
    split; [unfold KS_C; lia|]. split; [unfold KS_C; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val pa_segs E _ (ksp1 cx) KS_C 8%N (SOff 32 0) c).
    + exact (sv_off0 E 32 c E32).
    + cbn; lia.
    + cbn; lia.
    + exact (val_mem_of_rdword pa_segs (w_H W3) (ms_mem ms3) _ _ HSLC).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [cbn; exact I | split; [exact I | exact I]]. }
assert (SHOK : sh_ok SEGS kn_lt_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
pose (BR := paj_branch (PI := PI)).
(* +0x2100 .. +0x2104: s6 := ci + 1, a0 := c; the engine stops at the `beq` *)
paj_run_tok RUN HS HJ SHOK kn_lt_span.
{ intros a Ha. exfalso. apply (kn_no_wrange _ _ a Ha). vm_compute. reflexivity. }
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
  assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kn_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
(* +0x2108: beq s6, a0 *)
psrr_branch_tok RUN BR HS SHOK kn_lt_span.
- (* taken: ci + 1 = c, the last chunk: on to +0x2140 *)
  rewrite (kn_denot_inc E ci E22 ltac:(lia)), (sv_off0 E 32 c E32), (kn_beq_val (ci + 1) c ltac:(lia) ltac:(lia))
    in Hc.
  apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK kn_lt_span (kpc KP_EXIT).
  { intros a Ha. exfalso. apply (kn_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms1) (ms_mem ms2) |- _ =>
    assert (HM2 : ms_mem ms2 = ms_mem ms3)
      by (rewrite <- HM1; eapply kn_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  assert (KEEP : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) kn_lt_keptz = true ->
                   getr (ms_regs ms2) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (kn_regs_kept E (ms_regs ms3) [w64 c] _ ms2 (w_H W3) HAG HS
                              ltac:(vm_compute; reflexivity) r Hr)).
  assert (HMS2 : kms KP_EXIT ms2).
  { pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms2 HS eq_refl) as Hsh.
    unfold kms. rewrite Hsh. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ss_pc].
    repeat split; try reflexivity. }
  repeat rewrite wvb_collapse in HJ.
  apply (Hexit cx fpos k2 ly3 S3 W3 ms2 _ HB HJ Hfrm).
  unfold kin_exit. exists j, adv. split; [lia|].
  eapply kn_kat_move; [exact HK | exact HMS2 | exact HM2 | | | | |].
  + unfold kregs0. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite KEEP by (vm_compute; reflexivity); assumption.
  + unfold kregs_eq. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    rewrite KEEP by (vm_compute; reflexivity). exact R24.
  + intros ov Hov. unfold kslots_setup. cbn [In] in Hov |- *. tauto.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
- (* not taken: ci + 1 < c, the next chunk: +0x210c j +0x51c *)
  rewrite (kn_denot_inc E ci E22 ltac:(lia)), (sv_off0 E 32 c E32), (kn_beq_val (ci + 1) c ltac:(lia) ltac:(lia))
    in Hc.
  apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK kn_lt_span (kpc KP_HEAD).
  { intros a Ha. exfalso. apply (kn_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms1) (ms_mem ms2) |- _ =>
    assert (HM2 : ms_mem ms2 = ms_mem ms3)
      by (rewrite <- HM1; eapply kn_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  assert (KEEP : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) kn_lt_keptz = true ->
                   getr (ms_regs ms2) r = getr (ms_regs ms3) r)
    by (intros r Hr; exact (kn_regs_kept E (ms_regs ms3) [w64 c] _ ms2 (w_H W3) HAG HS
                              ltac:(vm_compute; reflexivity) r Hr)).
  assert (R22' : getr (ms_regs ms2) (Z_to_bv 5 (Z.of_nat 22)) = sv_denot E (SAluw ALU_ADD (SOff 22 0) (SLit 1))).
  { rewrite (st_ok_pi_restrict_reg (w_H W3) E _ ms2 _ HS). f_equal; vm_compute; reflexivity. }
  assert (HMS2 : kms KP_HEAD ms2).
  { pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms2 HS eq_refl) as Hsh.
    unfold kms. rewrite Hsh. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ss_pc].
    repeat split; try reflexivity. }
  repeat rewrite wvb_collapse in HJ.
  apply (Hhead cx fpos k2 ly3 S3 W3 ms2 _ HB HJ Hfrm).
  unfold kin_head. exists c, (ci + 1), j, adv.
  split; [replace (c - (ci + 1)) with (c - ci - 1) by lia; apply HRc; [exact HRcv | lia]|].
  split; [lia|]. split; [lia|]. split; [lia|].
  eapply kn_kat_move; [exact HK | exact HMS2 | exact HM2 | | | apply incl_refl | |].
  + unfold kregs0. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite KEEP by (vm_compute; reflexivity); assumption.
  + unfold kregs_eq, kregs_chunk. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    * rewrite KEEP by (vm_compute; reflexivity). exact R19.
    * rewrite KEEP by (vm_compute; reflexivity). exact R21.
    * rewrite R22'. exact (kn_denot_inc E ci E22 ltac:(lia)).
    * rewrite KEEP by (vm_compute; reflexivity). exact R24.
    * rewrite KEEP by (vm_compute; reflexivity). exact R25.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
Qed.

End b.
End a.

Print Assumptions kn_latch.

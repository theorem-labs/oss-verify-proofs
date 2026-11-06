(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v, with its module paths and module names changed; 231 of its 286 lines of code are new or changed and 183 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YE00 YC5d YO09 YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i ACj1 DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntRecCut DiscoEntRec2Kit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac e2_ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Definition e2_fa : list (nat * afact) := [(541%nat, mkAF 4096 (2 ^ 64 - 1) 0); (555%nat, mkAF 0 65535 0)].
Definition e2_acs : list YP09.chunk := [YP09.mkChunk 248 (CVal 8 (SOff (AT_X + 32) 0))].
Definition e2_cz : list acond := [mkAC BC_NE (SOff 541 0) (SLit 0); mkAC BC_EQ (SOff 555 0) (SLit 0)].
Definition e2_cn : list acond := [mkAC BC_NE (SOff 541 0) (SLit 0); mkAC BC_NE (SOff 555 0) (SLit 0)].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma e2_want_range : forall (pl : list byte) (n : Z), 0 <= rec_want (rest_of pl n) < 65536.
Proof.
  intros pl n. unfold rec_want, rdb.
  pose proof (bv_unsigned_in_range _ (nth 0 (rest_of pl n) (Z_to_bv 8 0))) as Q0.
  pose proof (bv_unsigned_in_range _ (nth 1 (rest_of pl n) (Z_to_bv 8 0))) as Q1.
  change (bv_modulus 8) with 256 in Q0, Q1. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.

Theorem r2_e2 : r2_e2_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold r2_e2_spec.
intros cx h i n now op fr W c Hst.
destruct Hst as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs)).
pose proof alloc_ceiling_val as Hac.
destruct HR as (H10 & H27 & H24 & H23 & H19 & H22 & H26).
destruct HX as (Hfr0 & (Hop0 & Hop3) & H408 & H248 & H392).
pose proof Hbody as (T & G & Lk & H & Hfrm & Hshd & Hobj & Hbl & Hinp & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
assert (Hfrr : 4096 <= fr < 2 ^ 64).
{ destruct Hbl as (Hperm & _).
  assert (Hin : In (fr, r2_len cx n) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
  pose proof (proj1 HJ) as HAR.
  destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 _ _ HAR Hin) as (_ & Hb4096 & Hble & _ & _ & _ & Hbn).
  pose proof (req_size_pos _ (proj1 Hbn)) as Hrq. lia. }
pose proof (e2_want_range (c_pl cx) n) as Hwant.
assert (Hlen : 0 <= r2_len cx n < 65536).
{ unfold r2_len, rec_len, rec_rem, rec_take. lia. }
assert (Rcur : 0 <= d_cur cx (rec_rem n) < 2 ^ 64).
{ pose proof Hbase as ((_ & _ & _ & _ & Hpn & _) & _ & _).
  pose proof Hinp as (Hn7 & _ & _).
  destruct Hgeo as (_ & _ & _ & _ & _ & _ & _ & G8).
  unfold d_cur, rec_rem, rec_take.
  destruct Hpn as [(HN & HP) | (HN & _)].
  - rewrite HN in Hn7. rewrite HN, HP. unfold A_EMPTY. lia.
  - destruct (G8 ltac:(lia)) as (GP0 & GPN & _). lia. }
assert (CH : forall E0 : env,
  YP09.chunk_ok SEGS (d_env cx E0 (r2_vals regs [w64 (d_cur cx (rec_rem n))])) (rd W mem3) (d_A cx)
    (YP09.mkChunk 248 (CVal 8 (SOff (AT_X + 32) 0)))).
{ intros E0. apply (chunk_ok_val SEGS _ _ (d_A cx) 248 8 _ (d_cur cx (rec_rem n)));
    [| exact Rcur | lia | exact H248].
  cbn [sv_denot].
  rewrite (r2_env_ex cx E0 regs [w64 (d_cur cx (rec_rem n))] 0%nat (AT_X + 32)%nat eq_refl
    ltac:(cbn [length]; lia)).
  cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (HAT : forall E0 : env, atoms_ok (d_env cx E0 (r2_vals regs [w64 (d_cur cx (rec_rem n))])) e2_fa).
{ intros E0. unfold e2_fa. cbn [atoms_ok]. split; [|split; [|exact I]]; unfold afact_ok;
    cbn [af_lo af_hi af_al2].
  - rewrite (r2_env_reg cx E0 regs [w64 (d_cur cx (rec_rem n))] 10%bv 541%nat
      ltac:(vm_compute; reflexivity)), H10.
    unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  - rewrite (r2_env_reg cx E0 regs [w64 (d_cur cx (rec_rem n))] 24%bv 555%nat
      ltac:(vm_compute; reflexivity)), H24.
    unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
assert (HC10 : forall E0 : env,
  acond_ok (d_env cx E0 (r2_vals regs [w64 (d_cur cx (rec_rem n))])) (mkAC BC_NE (SOff 541 0) (SLit 0))).
{ intros E0. unfold acond_ok. cbn [ac_c ac_a ac_b]. cbn [sv_denot branch_taken].
  rewrite (r2_env_reg cx E0 regs [w64 (d_cur cx (rec_rem n))] 10%bv 541%nat
    ltac:(vm_compute; reflexivity)), H10.
  unfold w64. rewrite unsigned_lit_small by lia.
  apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
  rewrite !unsigned_lit_small by lia. lia. }
destruct (Z.eq_dec (r2_len cx n) 0) as [Hz | Hz].
- assert (HCS : forall E0 : env, conds_ok (d_env cx E0 (r2_vals regs [w64 (d_cur cx (rec_rem n))])) e2_cz).
  { intros E0. unfold e2_cz. cbn [conds_ok]. split; [exact (HC10 E0)|]. split; [|exact I].
    unfold acond_ok. cbn [ac_c ac_a ac_b]. cbn [sv_denot branch_taken].
    rewrite (r2_env_reg cx E0 regs [w64 (d_cur cx (rec_rem n))] 24%bv 555%nat
      ltac:(vm_compute; reflexivity)), H24, Hz.
    unfold w64. rewrite unsigned_lit_small by lia.
    unfold bv_eqb. apply Z.eqb_eq. rewrite !unsigned_lit_small by lia. lia. }
  destruct (r2_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx RA_MAL h n [(fr, r2_len cx n)]
    dsh_loop ly3 S3 W regs mem3 md3 k [w64 (d_cur cx (rec_rem n))] e2_acs [] [] e2_fa e2_cz HC HrL Hbody
    ltac:(intros E0 HE0; split; [exact (HAT E0)|]; split; [exact (HCS E0)|];
      split; [unfold e2_acs; apply Forall_cons; [exact (CH E0) | apply Forall_nil]|];
      split; [apply Forall_nil|]; split; [apply Forall_nil|]; split; [exact I | apply Forall_nil])
    ltac:(vm_compute; reflexivity)) as (E & HdE & HS).
  pose proof (r2_regs_ok B cx E regs [w64 (d_cur cx (rec_rem n))] HdE HrL) as HRO.
  unfold ss_d in HS.
  e2_ro_base HS 516%nat. e2_ro_base HS 529%nat. e2_ro_base HS 60%nat.
  pose proof (r2_env_img cx E (r2_vals regs [w64 (d_cur cx (rec_rem n))]) HdE) as HEI.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (r2_vals regs [w64 (d_cur cx (rec_rem n))]))
    (rd W mem3)) by constructor.
  pose (RUNTO := paj_run_to (fx := fq) B LAWS).
  unfold cfg_at. change (w64 (BASE + RA_MAL)) with (Z_to_bv 64 (BASE + RA_MAL)).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan RA_CPY.
  { intros a Ha. exfalso. revert Ha. apply r2_nowin. vm_compute. reflexivity. }
  apply SRr_ret. right.
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (d_S cx <= a < d_S cx) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha _. lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
    exact (r2_kept_frame Ex rsx (w_H W) mem3 (ms_mem ms) 0 0 HFr
      (fun a' Ha' => False_ind _ (r2_nowin Ex rsx a' ltac:(vm_compute; reflexivity) Ha')) a Ha ltac:(lia)) end. }
  pose proof (r2_kept_all (w_H W) mem3 (ms_mem ms) (fun x Hx => HK x Hx ltac:(lia))) as HKA.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssF _ =>
    assert (RG : forall r r0 : bv 5, sr_get (ss_regs ssF) r = sr_get r2_sr r0 ->
      getr (ms_regs ms) r = getr regs r0)
      by (intros r r0 Heq; rewrite (st_ok_pi_restrict_reg (w_H W) Ex ssF ms r HS), Heq;
          symmetry; exact (HRO r0))
  end.
  destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
  destruct Hsp0 as (Hs232 & Hs344).
  unfold q_cpy.
  apply (r2_land_rt B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx _ (EV_HEAD i + 1) h i n n now
    [(fr, r2_len cx n)] _ _ W ly3 S3 mem3 _ k acc (d_env cx E (r2_vals regs [w64 (d_cur cx (rec_rem n))]))
    _ ms (d_S cx) (d_S cx) HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HS eq_refl).
  + vm_compute. reflexivity.
  + exact (d_E_env cx E _ HdE).
  + exact (d_env_fl cx E _).
  + vm_compute. reflexivity.
  + unfold LLVMF_STK. lia.
  + lia.
  + exact HK.
  + intros a _. exact (r2_present_grows (w_H W) mem3 (ms_mem ms) HG a).
  + intros a _ Ha. lia.
  + split; [unfold spZ; rewrite (RG 2%bv 2%bv ltac:(vm_compute; reflexivity)); exact Hsp|].
    rewrite (RG 3%bv 3%bv ltac:(vm_compute; reflexivity)), (RG 4%bv 4%bv ltac:(vm_compute; reflexivity)),
      (RG 8%bv 8%bv ltac:(vm_compute; reflexivity)), (RG 9%bv 9%bv ltac:(vm_compute; reflexivity)),
      (RG 18%bv 18%bv ltac:(vm_compute; reflexivity)), (RG 20%bv 20%bv ltac:(vm_compute; reflexivity)),
      (RG 25%bv 25%bv ltac:(vm_compute; reflexivity)).
    repeat split; assumption.
  + unfold r2_rk.
    rewrite (RG 27%bv 10%bv ltac:(vm_compute; reflexivity)), (RG 24%bv 24%bv ltac:(vm_compute; reflexivity)),
      (RG 23%bv 23%bv ltac:(vm_compute; reflexivity)), (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)),
      (RG 22%bv 22%bv ltac:(vm_compute; reflexivity)), (RG 26%bv 26%bv ltac:(vm_compute; reflexivity)).
    repeat split; assumption.
  + unfold r2_pure, r2_mem, r2_frame.
    split; [lia|]. split; [split; [exact Hop0 | exact Hop3]|]. split.
    * split; [eapply (r2_val_mem_all W mem3 (ms_mem ms)); [exact HKA | exact H408]|].
      split; [eapply (r2_val_mem_all W mem3 (ms_mem ms)); [exact HKA | exact H248]|].
      eapply (r2_val_mem_all W mem3 (ms_mem ms)); [exact HKA | exact H392].
    * rewrite Hz. cbn [Z.to_nat firstn map]. apply garr8_nil.
  + split; (eapply (r2_val_mem_all W mem3 (ms_mem ms)); [exact HKA | eassumption]).
- assert (HCS : forall E0 : env, conds_ok (d_env cx E0 (r2_vals regs [w64 (d_cur cx (rec_rem n))])) e2_cn).
  { intros E0. unfold e2_cn. cbn [conds_ok]. split; [exact (HC10 E0)|]. split; [|exact I].
    unfold acond_ok. cbn [ac_c ac_a ac_b]. cbn [sv_denot branch_taken].
    rewrite (r2_env_reg cx E0 regs [w64 (d_cur cx (rec_rem n))] 24%bv 555%nat
      ltac:(vm_compute; reflexivity)), H24.
    unfold w64. rewrite unsigned_lit_small by lia.
    apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq.
    rewrite !unsigned_lit_small by lia. lia. }
  destruct (r2_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx RA_MAL h n [(fr, r2_len cx n)]
    dsh_loop ly3 S3 W regs mem3 md3 k [w64 (d_cur cx (rec_rem n))] e2_acs [] [] e2_fa e2_cn HC HrL Hbody
    ltac:(intros E0 HE0; split; [exact (HAT E0)|]; split; [exact (HCS E0)|];
      split; [unfold e2_acs; apply Forall_cons; [exact (CH E0) | apply Forall_nil]|];
      split; [apply Forall_nil|]; split; [apply Forall_nil|]; split; [exact I | apply Forall_nil])
    ltac:(vm_compute; reflexivity)) as (E & HdE & HS).
  pose proof (r2_regs_ok B cx E regs [w64 (d_cur cx (rec_rem n))] HdE HrL) as HRO.
  pose proof (proj1 (proj2 (proj2 HdE))) as HEIE.
  unfold ss_d in HS.
  e2_ro_base HS 516%nat. e2_ro_base HS 529%nat. e2_ro_base HS 60%nat.
  pose proof (r2_env_img cx E (r2_vals regs [w64 (d_cur cx (rec_rem n))]) HdE) as HEI.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (r2_vals regs [w64 (d_cur cx (rec_rem n))]))
    (rd W mem3)) by constructor.
  pose (RUN := paj_run (fx := fq) B LAWS).
  unfold cfg_at. change (w64 (BASE + RA_MAL)) with (Z_to_bv 64 (BASE + RA_MAL)).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { intros a Ha. exfalso. revert Ha. apply r2_nowin. vm_compute. reflexivity. }
  apply SRr_ret. left.
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (d_S cx <= a < d_S cx) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha _. lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
    exact (r2_kept_frame Ex rsx (w_H W) mem3 (ms_mem ms) 0 0 HFr
      (fun a' Ha' => False_ind _ (r2_nowin Ex rsx a' ltac:(vm_compute; reflexivity) Ha')) a Ha ltac:(lia)) end. }
  pose proof (r2_kept_all (w_H W) mem3 (ms_mem ms) (fun x Hx => HK x Hx ltac:(lia))) as HKA.
  lazymatch type of HS with st_ok _ ?Ex (setpc ?ssF (SIGMA ?s)) _ =>
    pose proof (r2_pcall_pi fq Ex ssF _ s HS) as HSp;
    assert (RG : forall r r0 : bv 5, sr_get (ss_regs (setpc ssF (SIGMA s))) r = sr_get r2_sr r0 ->
      getr (ms_regs ms) r = getr regs r0)
      by (intros r r0 Heq; rewrite (st_ok_restrict_reg SEGS _ _ _ ms r HS), Heq; symmetry; exact (HRO r0))
  end.
  pose proof (st_ok_restrict_reg SEGS _ _ _ ms 1%bv HS) as Hra.
  lazymatch type of Hra with _ = sv_denot _ (sr_get ?sr _) =>
    let v := eval vm_compute in (sr_get sr 1%bv) in change (sr_get sr 1%bv) with v in Hra end.
  cbn [sv_denot] in Hra. rewrite d_env_old in Hra by (cbv; lia).
  rewrite (HEIE 240%nat ltac:(cbv; lia)) in Hra.
  pose proof (st_ok_restrict_reg SEGS _ _ _ ms 11%bv HS) as Ha1.
  lazymatch type of Ha1 with _ = sv_denot _ (sr_get ?sr _) =>
    let v := eval vm_compute in (sr_get sr 11%bv) in change (sr_get sr 11%bv) with v in Ha1 end.
  cbn [sv_denot] in Ha1.
  rewrite (r2_env_ex cx E regs [w64 (d_cur cx (rec_rem n))] 0%nat 563%nat eq_refl
    ltac:(cbn [length]; lia)) in Ha1.
  cbn [nth] in Ha1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Ha1.
  destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
  destruct Hsp0 as (Hs232 & Hs344).
  unfold p_cpy.
  apply (r2_land_rt B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx _ (EV_HEAD i + 1) h i n n now
    [(fr, r2_len cx n)] _ _ W ly3 S3 mem3 _ k acc (d_env cx E (r2_vals regs [w64 (d_cur cx (rec_rem n))]))
    _ ms (d_S cx) (d_S cx) HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HSp eq_refl).
  + cbn [ss_pc setpc]. reflexivity.
  + exact (d_E_env cx E _ HdE).
  + exact (d_env_fl cx E _).
  + vm_compute. reflexivity.
  + unfold LLVMF_STK. lia.
  + lia.
  + exact HK.
  + intros a _. exact (r2_present_grows (w_H W) mem3 (ms_mem ms) HG a).
  + intros a _ Ha. lia.
  + split; [unfold spZ; rewrite (RG 2%bv 2%bv ltac:(vm_compute; reflexivity)); exact Hsp|].
    rewrite (RG 3%bv 3%bv ltac:(vm_compute; reflexivity)), (RG 4%bv 4%bv ltac:(vm_compute; reflexivity)),
      (RG 8%bv 8%bv ltac:(vm_compute; reflexivity)), (RG 9%bv 9%bv ltac:(vm_compute; reflexivity)),
      (RG 18%bv 18%bv ltac:(vm_compute; reflexivity)), (RG 20%bv 20%bv ltac:(vm_compute; reflexivity)),
      (RG 25%bv 25%bv ltac:(vm_compute; reflexivity)).
    repeat split; assumption.
  + unfold r2_rk.
    rewrite (RG 10%bv 10%bv ltac:(vm_compute; reflexivity)), (RG 12%bv 24%bv ltac:(vm_compute; reflexivity)),
      (RG 27%bv 10%bv ltac:(vm_compute; reflexivity)), (RG 24%bv 24%bv ltac:(vm_compute; reflexivity)),
      (RG 23%bv 23%bv ltac:(vm_compute; reflexivity)), (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)),
      (RG 22%bv 22%bv ltac:(vm_compute; reflexivity)), (RG 26%bv 26%bv ltac:(vm_compute; reflexivity)).
    split; [unfold w64, RA_CPY; exact Hra|].
    split; [exact H10|]. split; [exact Ha1|].
    repeat split; assumption.
  + unfold r2_pure, r2_mem.
    split; [lia|]. split; [lia|]. split; [split; [exact Hop0 | exact Hop3]|].
    split; [eapply (r2_val_mem_all W mem3 (ms_mem ms)); [exact HKA | exact H408]|].
    split; [eapply (r2_val_mem_all W mem3 (ms_mem ms)); [exact HKA | exact H248]|].
    eapply (r2_val_mem_all W mem3 (ms_mem ms)); [exact HKA | exact H392].
  + split; (eapply (r2_val_mem_all W mem3 (ms_mem ms)); [exact HKA | eassumption]).
Qed.

End h.
End f.
End d.

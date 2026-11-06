(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_exit.v, with its module paths and module names changed; 291 of its 335 lines of code are new or changed and 599 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the message path's queueing
   (kin_qmsg +0x1e9c -> kin_latch +0x2100): the lane's own cuts and the steps through its two calls. Listing
   (internal path) (internal record, sha256 7bc02d6772b3):
     +0x1ee4  jal checked_memcpy(g_nl + 4096 j, w2, n)   (0x52d78), returns at +0x1ee8
     +0x1f24  jal meta_fill_f8(shadow(w2), 0x202)        (0x55f94), returns at +0x1f28
     +0x1f28  ld s6, 0x78(s1); j +0x2100                  s6 := ci (slot KS_CI)
   THE CUTS (kat of kernel_defs.v at a private pc; the slots kslots_setup and KS_CI):
     kin_qcpy +0x1ee4  a0 = g_nl + 4096 j, a1 = w2, a2 = s11 = n (1..4096), s6 = g_nl; j chunks queued; kfsh f8 00 f3
     kin_qcnt +0x1ee8  s6 = g_nl, s11 = n; j chunks queued (chunk j's bytes are w2's: kgnl keeps no chunk byte)
     kin_qfil +0x1f24  a0 = shadow(w2), a1 = 0x202; j' <= ci + 1 chunks queued
     kin_qret +0x1f28  both buffers poisoned again (kfsh f8 f8 f3)
   THE PROOF of each step: the state is rebuilt from the cut with no region (kq_ss0), the engine runs the `jal` (no
   store), the call is kernel_qmsg_kit.v kq_call_gcpy (link_ajkit.v aj_gx_intrin_at over AMEMCPY) or kq_call_mf
   (LinkWalkSide.v aj_gx_set_shadow_at over ASSF8), and the cut after it is kq_kat_g + kq_gnl_keep (the copy wrote
   chunk j and the callee's window) or kq_land_mf + kq_kshadow_w2 (the fill wrote w2's 0x202 shadow bytes).
   kq_qe (+0x1f28 -> kin_latch): one run with the slot KS_CI as a read-only region; no store.
   Section hypotheses: LAWS, LV (the callees' pcs, g_nl's atom), TB (the read set's shadow at a cut), KI (g_nl's
   writability), AMEMCPY, ASSF8.
   Proves no function (kind: segment lemma of kernel's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_kit kernel_next kernel_qmsg_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the state of a step through a call: the registers, no region *)
Definition kq_ss0 (pc : Z) : sstate := mkSS (kpc pc) sr_atoms [] None (mkFacts [] [] []).
(* the slot KS_CI as a read-only region (atom 32 = ci) *)
Definition qe_ss : sstate :=
  mkSS (kpc 0x1f28) sr_atoms [YP09.mkRegion (Some 9%nat) KS_CI (KS_CI + 8) 0 0 [YP09.mkChunk KS_CI (CVal 8 (SOff 32 0))]]
    None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.                                (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                              (* kernel_img_syms at the image *)
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.   (* checked_memcpy: AE2q.v asan_memcpy_realizes *)
Hypothesis ASSF8 : aset_shadow_realizes pa_segs B 0x55f94 0xf8. (* meta_fill_f8: SetShadow.v link_set_shadow_f8 *)

(* ---- the lane's cuts ---- *)
Definition kq_sl (cx : kcx) (fpos c ci : Z) : list (Z * Z) := kslots_setup cx fpos c ++ [(KS_CI, ci)].
Definition kq_rl_cpy (cx : kcx) (fpos j n : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
   (22%nat, LA_G_NL); (27%nat, n); (10%nat, LA_G_NL + 4096 * j); (11%nat, kW2 cx fpos); (12%nat, n)].
Definition kq_rl_cnt (cx : kcx) (fpos n : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
   (22%nat, LA_G_NL); (27%nat, n)].
Definition kq_rl_fil (cx : kcx) (fpos : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
   (10%nat, kFSH cx fpos + 0x226); (11%nat, 0x202)].
Definition kq_rl_ret (cx : kcx) (fpos : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)].

Definition kin_qcpy (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j n adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= n <= 4096 /\
  kat B cx fpos 0x1ee4 (kq_rl_cpy cx fpos j n) (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kin_qcnt (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j n adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= n <= 4096 /\
  kat B cx fpos 0x1ee8 (kq_rl_cnt cx fpos n) (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kin_qfil (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci + 1 /\
  kat B cx fpos 0x1f24 (kq_rl_fil cx fpos) (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.
Definition kin_qret (Rc : kcx -> Z -> Prop) :
  kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci + 1 /\
  kat B cx fpos 0x1f28 (kq_rl_ret cx fpos) (kq_sl cx fpos c ci) (kfsh 0xf8 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.

Lemma kq_sl_ok : forall cx fpos c ci, kslots_okb (kq_sl cx fpos c ci) = true.
Proof. intros cx fpos c ci. reflexivity. Qed.

(* the state at a cut with no region *)
Lemma kq_seat0 : forall cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 (E : env),
  E = Eimg (Ereg (ms_regs ms3) []) ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  st_ok_pi SEGS pa_val E (kq_ss0 pc) (restrict (w_H W3) ms3).
Proof.
  intros cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 E HE HK.
  pose proof HK as (HMS & _). destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  rewrite (km_ms_shape ms3 (BASE + kpc pc) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
  unfold kq_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint]. exact I.
  - split; [exact I | split; [exact I | exact I]].
Qed.

(* ---- +0x1f28 -> kin_latch +0x2100: s6 := ci ---- *)
Theorem kq_qe : forall POST Rc, kfrom SK B POST (kin_latch B Rc) -> kfrom SK B POST (kin_qret Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & _ & _ & HSL & _).
  pose proof HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1a & Hs1b & _ & Hsp47 & _).
  assert (HSLC : rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + KS_CI) = Some ci)
    by (apply (kn_slot_of cx W3 ms3 _ KS_CI ci HSL); unfold kq_sl; apply in_or_app; right; left; reflexivity).
  remember (Eimg (Ereg (ms_regs ms3) [w64 ci])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 ci]) E)
    by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9%nat = w64 (ksp1 cx)) by (subst E; rewrite <- A9; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (E32 : ew E 32%nat = w64 ci) by (subst E; apply (kq_E_32 SK B LAWS TB KI AMEMCPY LV)).
  assert (HS : st_ok_pi SEGS pa_val E qe_ss (restrict (w_H W3) ms3)).
  { rewrite (km_ms_shape ms3 (BASE + kpc 0x1f28) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
    unfold qe_ss. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
      split; [unfold KS_CI; lia|]. split; [unfold KS_CI; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val pa_segs E _ (ksp1 cx) KS_CI 8%N (SOff 32 0) ci).
      + exact (sv_off0 E 32 ci E32).
      + cbn; lia.
      + cbn; lia.
      + exact (val_mem_of_rdword pa_segs (w_H W3) (ms_mem ms3) _ _ HSLC).
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - split; [cbn; exact I | split; [exact I | exact I]]. }
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc KP_LATCH).
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  assert (KEEP : forall r, In r nx_keep0 -> getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by exact (regs_kept_of_st_ok_pi E _ _ _ _ nx_keep0 HS HAG ltac:(vm_compute; reflexivity)).
  assert (KEEPN : forall r, In r (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 25]%nat) ->
            getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by exact (regs_kept_of_st_ok_pi E _ _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 25]%nat)
                HS HAG ltac:(vm_compute; reflexivity)).
  assert (HMS1 : kms KP_LATCH ms1) by (apply (kn_kms_of _ E _ ms1 KP_LATCH HS); vm_compute; reflexivity).
  assert (R22 : getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat 22)) = w64 ci).
  { rewrite (st_ok_pi_restrict_reg _ E _ ms1 _ HS).
    lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ =>
      let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.
    exact (sv_off0 E 32 ci E32). }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdn) _ => apply (HNEXT cx fpos k2 ly3 S3 W3 ms1 mdn HB HJ Hfrm) end.
  exists c, ci, j, adv. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  apply (kat_frame_0 B cx fpos _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 _ _ _ ms1 _ HK HMS1).
  - exact (kregs0_keep cx ms3 ms1 KEEP HR0).
  - unfold kregs_eq, kregs_chunk. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite (KEEPN _ (kn_in_map5 19 [19; 21; 24; 25]%nat ltac:(kn_in))). apply (kn_reg_of ms3 _ _ _ HRL).
      unfold kq_rl_ret. kn_in.
    + rewrite (KEEPN _ (kn_in_map5 21 [19; 21; 24; 25]%nat ltac:(kn_in))). apply (kn_reg_of ms3 _ _ _ HRL).
      unfold kq_rl_ret. kn_in.
    + exact R22.
    + rewrite (KEEPN _ (kn_in_map5 24 [19; 21; 24; 25]%nat ltac:(kn_in))). apply (kn_reg_of ms3 _ _ _ HRL).
      unfold kq_rl_ret. kn_in.
    + rewrite (KEEPN _ (kn_in_map5 25 [19; 21; 24; 25]%nat ltac:(kn_in))). apply (kn_reg_of ms3 _ _ _ HRL).
      unfold kq_rl_ret. kn_in.
  - exact HM1.
  - intros x Hx. unfold kq_sl. apply in_or_app. left. exact Hx.
  - exact (proj1 (wvb_fds_fs _ _ _)).
  - exact (proj2 (wvb_fds_fs _ _ _)).
Qed.

(* ---- +0x1f24 -> +0x1f28: meta_fill_f8(shadow(w2), 0x202) ---- *)
Theorem kq_qd : forall POST Rc, kfrom SK B POST (kin_qret Rc) -> kfrom SK B POST (kin_qfil Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & _ & HJB & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10%nat = w64 (kFSH cx fpos + 0x226)).
  { rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] 10 (Z_to_bv 5 (Z.of_nat 10)) eq_refl).
    apply (kn_reg_of ms3 _ 10 _ HRL). unfold kq_rl_fil. kn_in. }
  assert (E11 : ew E 11%nat = w64 0x202).
  { rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] 11 (Z_to_bv 5 (Z.of_nat 11)) eq_refl).
    apply (kn_reg_of ms3 _ 11 _ HRL). unfold kq_rl_fil. kn_in. }
  pose proof (kq_seat0 cx fpos 0x1f24 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 E HEdef HK) as HS.
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK kq_span.
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  pose proof (km_reg_same E (kq_ss0 0x1f24) _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_set_shadow_f8) with 0x55f94.
  rewrite HM1. rewrite HM1 in HJ.
  eapply (kq_call_mf SK B LAWS TB KI AMEMCPY LV 0x55f94 0xf8 ASSF8 cx fpos k2 ly3 S3 W3 (ms_mem ms3) _
            (ms_regs ms1) _ 0x226 (POST cx) HB HJ);
    [ lia | lia
    | rewrite R10; exact E10
    | rewrite R11; exact E11
    | rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)
    | rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))
    | rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 Hf8 Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 (mkst regs2 _ mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrm).
  exists c, ci, j, adv. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  apply (kq_land_mf SK B LAWS TB KI AMEMCPY LV 0x226 cx fpos 0x1f24 (kq_rl_fil cx fpos) (kq_sl cx fpos c ci)
           (kfsh 0xf8 0 0xf3) (kfsh 0xf8 0xf8 0xf3) adv (Some j) k2 ly3 S3 W3 ms3 md3 _ md2 0x1f28
           (kq_rl_ret cx fpos) HB HK (kq_sl_ok cx fpos c ci) ltac:(lia) ltac:(lia)).
  - intros a Ha Hn. exact (Hkeep a Ha Hn).
  - intros a Ha. exact (Hpres a Ha).
  - apply (kq_kshadow_w2 SK B LAWS TB KI AMEMCPY LV cx fpos W3 ms3 _ 0xf8 0 0xf3 0xf8 HSH).
    + intros i Hi Hn. destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
      apply Hkeep; [unfold kHighMemBeg, SHADOW_OFF in *; lia | lia].
    + intros i Hi. exact (Hf8 i Hi).
  - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
  - unfold kregs0. cbn [ms_regs mkst]. destruct HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite (km_pres _ _ _ HP2) by reflexivity; rewrite KEEP by reflexivity; assumption.
  - unfold kregs_eq, kq_rl_ret. cbn [ms_regs mkst]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      rewrite (km_pres _ _ _ HP2) by (vm_compute; reflexivity); rewrite KEEP by (vm_compute; reflexivity);
      apply (kn_reg_of ms3 _ _ _ HRL); unfold kq_rl_fil; kn_in.
Qed.

(* ---- +0x1ee4 -> +0x1ee8: checked_memcpy(g_nl + 4096 j, w2, n) ---- *)
Theorem kq_qb : forall POST Rc, kfrom SK B POST (kin_qcnt Rc) -> kfrom SK B POST (kin_qcpy Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & n & adv & HRcv & Hcr & Hci & Hj & Hn & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & HFR & HSH & _ & HJB & _ & _ & HGN & _).
  pose proof HFR as (_ & _ & _ & _ & Hpf & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & Hs1a & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10%nat = w64 (LA_G_NL + 4096 * j)).
  { rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] 10 (Z_to_bv 5 (Z.of_nat 10)) eq_refl).
    apply (kn_reg_of ms3 _ 10 _ HRL). unfold kq_rl_cpy. kn_in. }
  assert (E11 : ew E 11%nat = w64 (kW2 cx fpos)).
  { rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] 11 (Z_to_bv 5 (Z.of_nat 11)) eq_refl).
    apply (kn_reg_of ms3 _ 11 _ HRL). unfold kq_rl_cpy. kn_in. }
  assert (E12 : ew E 12%nat = w64 n).
  { rewrite HEdef, (ew_Eimg_Ereg_nat (ms_regs ms3) [] 12 (Z_to_bv 5 (Z.of_nat 12)) eq_refl).
    apply (kn_reg_of ms3 _ 12 _ HRL). unfold kq_rl_cpy. kn_in. }
  assert (HRA : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (kW2 cx fpos) n).
  { pose proof (kn_w2_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HW2.
    intros y Hy. apply HW2. unfold NW_SIZE. lia. }
  pose proof (kq_seat0 cx fpos 0x1ee4 _ _ _ true adv (Some j) k2 ly3 S3 W3 ms3 md3 E HEdef HK) as HS.
  pose proof HS as HS0.
  assert (SHOK : sh_ok SEGS kq_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK kq_span.
  { intros a Ha. exfalso. apply (kq_no_wrange _ _ a Ha). vm_compute. reflexivity. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
    assert (HM1 : ms_mem ms1 = ms_mem ms3) by (eapply kq_mem_eq; [exact Hx | vm_compute; reflexivity]) end.
  pose proof (km_reg_same E (kq_ss0 0x1ee4) _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
  prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memcpy) with 0x52d78.
  rewrite HM1. rewrite HM1 in HJ.
  lazymatch type of HJ with ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdR _ =>
    assert (HKR : kat B cx fpos 0x1ee4 (kq_rl_cpy cx fpos j n) (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv
                    (Some j) k2 ly3 S3 W3 ms3 mdR)
      by (apply (kat_frame_0 B cx fpos _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 _ _ _ ms3 mdR HK HMS HR0 HRL eq_refl
                   (incl_refl _));
          [repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
          | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity]) end.
  eapply (kq_call_gcpy SK B LAWS TB KI AMEMCPY LV cx fpos 0x1ee4 (kq_rl_cpy cx fpos j n) (kq_sl cx fpos c ci)
            (kfsh 0xf8 0 0xf3) adv (Some j) k2 ly3 S3 W3 ms3 _ (ms_regs ms1) _ j n (kW2 cx fpos) (POST cx) HB HJ HKR);
    [ lia | lia | unfold kW2, KN_W2; lia | unfold kW2, KN_W2, KN_FSZ; lia | exact HRA
    | rewrite R10; exact E10
    | rewrite R11; exact E11
    | rewrite R12; exact E12
    | rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)
    | rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))
    | rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 Hcp Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 (mkst regs2 _ mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrm).
  exists c, ci, j, n, adv. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  split; [exact Hn|].
  apply (kq_kat_g SK B LAWS TB KI AMEMCPY LV (fun a => ksp1 cx - ESTACK <= a < ksp1 cx)
           (fun a => LA_G_NL + 4096 * j <= a < LA_G_NL + 4096 * j + n) cx fpos 0x1ee4 (kq_rl_cpy cx fpos j n)
           (kq_sl cx fpos c ci) (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 0x1ee8
           (kq_rl_cnt cx fpos n) (kq_sl cx fpos c ci) (Some j) W3 _ md2 HB HK).
  - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
  - unfold kregs0. cbn [ms_regs mkst]. destruct HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite (km_pres _ _ _ HP2) by reflexivity; rewrite KEEP by reflexivity; assumption.
  - unfold kregs_eq, kq_rl_cnt. cbn [ms_regs mkst]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      rewrite (km_pres _ _ _ HP2) by (vm_compute; reflexivity); rewrite KEEP by (vm_compute; reflexivity);
      apply (kn_reg_of ms3 _ _ _ HRL); unfold kq_rl_cpy; kn_in.
  - apply incl_refl.
  - apply kfsh_fits.
  - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - intros a Ha Ho Hg. exact (Hkeep a Ha Hg Ho).
  - intros a Ha. exact (Hpres a Ha).
  - intros a Ha. exact (kX_in_win SK B cx fpos a HB Ha).
  - apply (kX_miss_win SK B LAWS cx fpos k2 ly3 S3 md3 (kq_sl cx fpos c ci) _ _ HB HJB (kq_sl_ok cx fpos c ci));
      [rewrite kfsh_length; lia | intros a Ha; exact Ha].
  - intros a Ha. unfold NK_OPEN. lia.
  - apply (kq_gnl_keep SK B LAWS TB KI AMEMCPY LV cx W3 ms3 _ j HGN ltac:(lia)).
    + intros i Hi. cbn [ms_mem mkst].
      pose proof (kq_gnl_vis SK B LAWS TB KI AMEMCPY LV cx W3 ms3 (Some j) HGN i Hi) as Hv3.
      destruct (Z.lt_ge_cases i (4096 * j)) as [H1 | H1];
        [| destruct (Z.lt_ge_cases i (4096 * j + n)) as [H2 | H2]].
      * rewrite Hkeep; [exact Hv3 | unfold LA_G_NL, NK_SIZE in *; lia | lia | unfold ESTACK, LA_G_NL, NK_SIZE in *; lia].
      * replace (LA_G_NL + i) with (LA_G_NL + 4096 * j + (i - 4096 * j)) by lia.
        rewrite (Hcp (i - 4096 * j) ltac:(lia)). apply (kq_aview_some SK B LAWS TB KI AMEMCPY LV). apply Hpf.
        rewrite kn_fsb8.
        unfold kW2, KN_W2. lia.
      * rewrite Hkeep; [exact Hv3 | unfold LA_G_NL, NK_SIZE in *; lia | lia | unfold ESTACK, LA_G_NL, NK_SIZE in *; lia].
    + intros i Hi. cbn [ms_mem mkst].
      apply Hkeep; [unfold LA_G_NL, NK_SIZE, NK_CHUNK_LEN in *; lia | unfold NK_CHUNK_LEN in Hi; lia
                   | unfold ESTACK, LA_G_NL, NK_SIZE, NK_CHUNK_LEN in *; lia].
Qed.

End b.
End a.

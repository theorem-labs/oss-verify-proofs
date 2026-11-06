(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 666 of its 732 lines of code are new or changed and 1212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntHobsS3.v; 194 of its 272 lines of code are new or changed and 654 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_frame_clean_len_c slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_hunt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require RoleOf CheckTable CheckSighting.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntHobsCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac hb_s4_ro HS bn :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs bn in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Definition hb_s4_fcs : list YP09.chunk := [YP09.mkChunk 3000 (CVal 4 (SOff 563 0))].

Lemma hb_s4_role_rng : forall A : list byte, disco_classify_c.sighting_ok A ->
  0 <= u_at A 8 4 < 2 ^ 32 /\ u_at A 8 4 = s_role A /\ 0 <= s_role A <= 2.
Proof.
intros A HA. pose proof (slot_known.u4_rng A 8) as R.
pose proof (proj1 (slot_hunt.sf4a A) (proj1 (proj2 HA))) as HR.
split; [exact R|].
split; [symmetry; apply CheckTable.ct_s32_small; [exact R | unfold s_role, s32_at in HR; lia]|].
exact HR.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma hb_s4_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j Hj. unfold d_env.
replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma hb_s4_aview_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' HM a. unfold aview, mbyte, mrestrict. rewrite HM. reflexivity. Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.

Lemma hb_s4_land : forall (fq : YK11.FPState) cx h i n now op nb fr len ly3 S3 (W : world SEGS)
  mem3 md' k acc (E0 : env) (ss : sstate) (ms : machine_state),
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL E0 ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = HB_P4 ->
  (forall x, ms_mem ms x = mem3 x) ->
  d_rL B cx (ms_regs ms) -> d_sp0 cx i now W mem3 -> hb_X cx op nb fr len W mem3 ->
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W mem3 ->
  hb_R4 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W (mkCfg ms md').
Proof.
intros fq cx h i n now op nb fr len ly3 S3 W mem3 md' k acc E0 ss ms
  Hbase Hfrm0 HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow HS Hrv Hpc MEQ HrL Hsp0 HXb Hbody.
assert (HC4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md' k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md' k HC4)
  as (_ & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof asan_consts as (C1 & _).
pose proof (cl_A_range cx ltac:(clear - Hlo C1; unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & _).
assert (Hav : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
  by exact (hb_s4_aview_ext (w_H W) mem3 (ms_mem ms) MEQ).
assert (VM : forall a m0 v0, val_mem SEGS (rd W mem3) a m0 v0 -> val_mem SEGS (rd W (ms_mem ms)) a m0 v0)
  by (intros a m0 v0 Hv; eapply YC88.val_mem_aview_kept_x; [intros x _; exact (Hav x) | exact Hv]).
assert (GM : forall p L, garr8 SEGS (rd W mem3) p L -> garr8 SEGS (rd W (ms_mem ms)) p L)
  by (intros p L HG; eapply YC88.garr8_aview_kept; [intros a _; exact (Hav a) | exact HG]).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
assert (Hframe4 : d_frame cx h dsh_rec W (ms_mem ms))
  by exact (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W mem3 ly3 S3 W (ms_mem ms) md' k
    HC4 Hframe (fun a _ => Hav a)).
assert (Hshadow4 : d_shadow cx dsh_rec W (ms_mem ms))
  by exact (cl_shadow_keep cx dsh_rec W W mem3 (ms_mem ms) Hshadow (fun a _ => Hav a)).
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (BRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx)
    (fun _ => False) Hbody).
  - clear - HA1 Hlo C1. unfold MFRAME, LLVMF_STK in *. lia.
  - clear - HA1 Hlo C1. unfold MFRAME, LLVMF_STK in *. lia.
  - intros a [].
  - intros a _ _. exact (Hav a).
  - intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite MEQ. exact Hb.
  - exact Hframe4.
  - exact Hshadow4.
  - clear - Hn. lia. }
destruct HXb as (Hop4 & Hop & Hfrm & Hrec & Hopv & Hl1 & Hl2).
destruct Hfrm as (F1 & F2 & F3 & F4).
destruct Hrec as (P200 & P328 & P368 & P408).
destruct Hopv as (Q360 & Q352).
destruct Hsp0 as (S208 & S320).
pose proof (st_ok_pi_restrict_mkst (w_H W) E0 ss ms HS Hrv) as Hms.
unfold hb_R4, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact Hfrm0|].
split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split; [exact HrL|]. split; [exact I|].
split.
- split; [exact Hop4|]. split; [exact Hop|].
  split; [exact (conj F1 (conj F2 (conj F3 (GM _ _ F4))))|].
  split; [exact (conj (VM _ _ _ P200) (conj (VM _ _ _ P328) (conj (VM _ _ _ P368) (VM _ _ _ P408))))|].
  split; [exact (conj (VM _ _ _ Q360) (VM _ _ _ Q352))|].
  split; [exact Hl1 | exact Hl2].
- split; [exact (conj (VM _ _ _ S208) (VM _ _ _ S320)) | exact Hbody4].
Qed.

Theorem hb_L4 : hb_L4_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len v W c Hin.
unfold hb_R3, d_arm_at_pf, d_at in Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
destruct HR as (R22 & R23).
destruct HX as (HXb & Hvr & A & HSg & HA2).
destruct HSg as (LA & GA & HSF).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(clear - Hlo C1; unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA32).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (clear - HA1 Hlo Hhi C1; unfold MFRAME, LLVMF_STK in *; lia).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & V184 & V120 & V136 & V376 & V280 & V232 & V264).
destruct (hb_s4_role_rng A (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HSF))))))) as (Hu32 & Hus & Hrl2).
set (vals := cl_vals regs [w64 (s_role A)]) in *.
assert (LV : length vals = 33%nat)
  by (clear; unfold vals, cl_vals; rewrite length_app, length_map, length_seq; reflexivity).
assert (A563 : ew (d_env cx E vals) 563%nat = w64 (s_role A)).
{ change 563%nat with (AT_X + 32)%nat.
  rewrite (hb_s4_env_x cx E vals 32%nat ltac:(clear - LV; rewrite LV; lia)).
  clear - LV. unfold vals, cl_vals. rewrite app_nth2; rewrite length_map, length_seq; [reflexivity | lia]. }
assert (D563 : sv_denot (d_env cx E vals) (SOff 563 0) = Z_to_bv 64 (s_role A))
  by (rewrite sv_denot_SOff0; exact A563).
assert (R3000 : d_FB cx + 3000 = d_obj cx OS + 8) by (clear; unfold d_obj; cbn [dobj_off]; ring).
assert (HVM : val_mem SEGS (rd W mem3) (d_FB cx + 3000) 4 (s_role A)).
{ rewrite R3000, <- Hus.
  exact (RoleOf.ro_val_mem4_garr8 (rd W mem3) (d_obj cx OS) A 8 GA ltac:(clear; lia)
    ltac:(clear - LA; rewrite LA; lia)). }
assert (HFCS : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) hb_s4_fcs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS (d_env cx E vals) (rd W mem3) (d_FB cx) 3000 4%N (SOff 563 0) (s_role A));
    [exact D563 | change (2 ^ (8 * Z.of_N 4)) with 4294967296; clear - Hrl2; lia | clear; lia | exact HVM]. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HB_P3 cl_sr vals [] hb_s4_fcs [] (d_facts [] [])
  HC HdE Hregs Hflag (cl_regs_ok B cx E regs [w64 (s_role A)] HdE HrL HAr2)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HC HdE I I)
  (Forall_nil _) HFCS (Forall_nil _) I (Forall_nil _) ltac:(clear; vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hb_s4_ro HS 60%nat. hb_s4_ro HS 516%nat. hb_s4_ro HS 529%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env.
  rewrite ew_havoc_old by (clear - Ha; unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof (cl_regs_ok B cx E regs [w64 (s_role A)] HdE HrL HAr2) as HROK.
fold vals in HROK.
assert (D554 : sv_denot (d_env cx E vals) (SOff 554 0) = w64 v).
{ pose proof (HROK (23%bv : bv 5)) as Q.
  let e := eval vm_compute in (sr_get cl_sr (23%bv : bv 5)) in change (sr_get cl_sr (23%bv : bv 5)) with e in Q.
  rewrite <- Q. exact R23. }
assert (D553 : sv_denot (d_env cx E vals) (SOff 553 0) = w64 1).
{ pose proof (HROK (22%bv : bv 5)) as Q.
  let e := eval vm_compute in (sr_get cl_sr (22%bv : bv 5)) in change (sr_get cl_sr (22%bv : bv 5)) with e in Q.
  rewrite <- Q. exact R22. }
unfold cfg_at. change (w64 (BASE + HB_P3)) with (Z_to_bv 64 (BASE + HB_P3)).
psrr_branch_tok RUN BR HS SHOK cl_span.
- clear Hc. paj_run_to_tok RUNTO HS HJ SHOK cl_span HB_P4.
  { awr_ok_tac. }
  pose proof (cl_ro_pt _ _ _ _ HF ltac:(clear; vm_compute; reflexivity)) as M1.
  clear HF HFr HG.
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), (HROK r).
    cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
  apply SRr_ret.
  apply (hb_s4_land fq cx h i n now op nb fr len ly3 S3 W mem3 _ k acc _ _ ms
    Hbase Hfrm0 HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow HS eq_refl eq_refl M1);
    [| exact Hsp0 | exact HXb | exact Hbody].
  destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  unfold d_rL, spZ in *. rewrite !RG by (clear; cbv; tauto).
  split; [exact Hsp|]. split; [exact Hgp|]. split; [exact Htp|]. split; [exact H8|].
  split; [exact H9|]. split; [exact H19|]. split; [exact H18|]. split; [exact H20 | exact H27].
- rewrite branch_ne_U in Hc. unfold U in Hc. rewrite D554, D553 in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hv1 : v = 1)
    by (clear - Hc Hvr; destruct Hvr as [->|[->|[->| ->]]]; try reflexivity; vm_compute in Hc; discriminate).
  pose proof (HA2 Hv1) as HRne2. clear Hc.
  paj_run_tok RUN HS HJ SHOK cl_span.
  { awr_ok_tac. }
  pose proof (cl_ro_pt _ _ _ _ HF ltac:(clear; vm_compute; reflexivity)) as M1.
  clear HF HFr HG.
  assert (USE : U (d_env cx E vals) (SExt true 32 (SOff 563 0)) = s_role A).
  { rewrite U_SExt. cbv iota.
    rewrite (U_atom (d_env cx E vals) 563%nat (s_role A) A563 ltac:(clear - Hrl2; lia)).
    change (2 ^ Z.of_N 32) with 4294967296.
    rewrite (Z.mod_small (s_role A) 4294967296) by (clear - Hrl2; lia).
    unfold bv_swrap, bv_wrap.
    change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
    rewrite (Z.mod_small (s_role A + 2147483648) 4294967296) by (clear - Hrl2; lia).
    replace (s_role A + 2147483648 - 2147483648) with (s_role A) by ring.
    apply zcanon_id. unfold M64. clear - Hrl2. lia. }
  psrr_branch_tok RUN BR HS SHOK cl_span.
  + clear Hc. paj_run_to_tok RUNTO HS HJ SHOK cl_span HB_P4.
    { awr_ok_tac. }
    pose proof (cl_ro_pt _ _ _ _ HF ltac:(clear; vm_compute; reflexivity)) as M2.
    clear HF HFr HG.
    pose proof (fun x => eq_trans (M2 x) (M1 x)) as MEQ.
    assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms0) r = getr regs r).
    { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms0 r HS), (HROK r).
      cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
    apply SRr_ret.
    apply (hb_s4_land fq cx h i n now op nb fr len ly3 S3 W mem3 _ k acc _ _ ms0
      Hbase Hfrm0 HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow HS eq_refl eq_refl MEQ);
      [| exact Hsp0 | exact HXb | exact Hbody].
    destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
    unfold d_rL, spZ in *. rewrite !RG by (clear; cbv; tauto).
    split; [exact Hsp|]. split; [exact Hgp|]. split; [exact Htp|]. split; [exact H8|].
    split; [exact H9|]. split; [exact H19|]. split; [exact H18|]. split; [exact H20 | exact H27].
  + exfalso. rewrite branch_ne_U, USE in Hc.
    rewrite (U_lit (d_env cx E vals) 2 ltac:(clear; lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. exact (HRne2 Hc).
Qed.

End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths changed; 216 of its 242 lines of code are new or changed and 1252 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3 DiscoArm3TailK DiscoArm3AgeSt DiscoArm3AgeKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
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
Hypothesis DBKEEP : d_body_keep_stmt B.
Hypothesis DBRT : d_body_rt_stmt B.

Theorem a3_e_chk : e_chk_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold e_chk_spec.
intros cx h i n now op W0 c0 T0 T1 removed W c [Hfrom Hst].
destruct Hst as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs)).
destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx P_AGE_RA h n [] dsh_loop ly3 S3 W regs mem3 md3 k
  [] [] [] [] [] [] HC HrL Hbody
  (fun E _ => conj I (conj I (conj (Forall_nil _) (conj (Forall_nil _) (conj (Forall_nil _) (conj I (Forall_nil _)))))))
  ltac:(vm_compute; reflexivity)) as (E & HdE & HS).
pose proof (a3_regs_ok B cx E regs [] HdE HrL) as HRO.
pose proof (proj1 (proj2 (proj2 HdE))) as HEIE.
unfold ss_d in HS.
ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
pose proof (a3_env_img cx E (a3_vals regs []) HdE) as HEI.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (a3_vals regs [])) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + P_AGE_RA)) with (Z_to_bv 64 (BASE + P_AGE_RA)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ intros a Ha. exfalso. revert Ha. apply a3_nowin. vm_compute. reflexivity. }
apply SRr_ret. split; [exact Hfrom|].
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (d_S cx <= a < d_S cx) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha _. lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
  exact (a3_kept_frame Ex rsx (w_H W) mem3 (ms_mem ms) 0 0 HFr
    (fun a' Ha' => False_ind _ (a3_nowin Ex rsx a' ltac:(vm_compute; reflexivity) Ha')) a Ha ltac:(lia)) end. }
pose proof (a3_kept_all (w_H W) mem3 (ms_mem ms) (fun x Hx => HK x Hx ltac:(lia))) as HKA.
lazymatch type of HS with st_ok _ ?Ex (setpc ?ssF (SIGMA ?s)) _ =>
  pose proof (a3_pcall_pi fq Ex ssF _ s HS) as HSp;
  assert (RG : forall r r0 : bv 5, sr_get (ss_regs (setpc ssF (SIGMA s))) r = sr_get a3_sr r0 ->
    getr (ms_regs ms) r = getr regs r0)
    by (intros r r0 Heq; rewrite (st_ok_restrict_reg SEGS _ _ _ ms r HS), Heq; symmetry; exact (HRO r0))
end.
pose proof (st_ok_restrict_reg SEGS _ _ _ ms 1%bv HS) as Hra.
lazymatch type of Hra with _ = sv_denot _ (sr_get ?sr _) =>
  let v := eval vm_compute in (sr_get sr 1%bv) in change (sr_get sr 1%bv) with v in Hra end.
cbn [sv_denot] in Hra. rewrite d_env_old in Hra by (cbv; lia).
rewrite (HEIE 240%nat ltac:(cbv; lia)) in Hra.
destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
destruct HR as (H10 & H23' & H22' & H25' & H24' & H26' & H27').
destruct HX as (HSP1 & HAGED & HOP).
apply (a3_land_keep B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBKEEP fq cx AF_both3_check_table (EV_HEAD i) h i n n now
  _ _ W ly3 S3 mem3 _ k acc (d_env cx E (a3_vals regs [])) _ ms (d_S cx) (d_S cx) Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi
  ltac:(lia) Hnow Hbody HSp eq_refl).
- cbn [ss_pc setpc]. rewrite pa_sigma_check_table. lia.
- exact (d_E_env cx E _ HdE).
- exact (d_env_fl cx E _).
- vm_compute. reflexivity.
- unfold LLVMF_STK. lia.
- lia.
- exact HK.
- intros a _. exact (a3_present_grows (w_H W) mem3 (ms_mem ms) HG a).
- intros a _ Ha. lia.
- split; [unfold spZ; rewrite (RG 2%bv 2%bv ltac:(vm_compute; reflexivity)); exact Hsp|].
  rewrite (RG 3%bv 3%bv ltac:(vm_compute; reflexivity)), (RG 4%bv 4%bv ltac:(vm_compute; reflexivity)),
    (RG 8%bv 8%bv ltac:(vm_compute; reflexivity)), (RG 9%bv 9%bv ltac:(vm_compute; reflexivity)),
    (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)), (RG 18%bv 18%bv ltac:(vm_compute; reflexivity)),
    (RG 20%bv 20%bv ltac:(vm_compute; reflexivity)), (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)).
  repeat split; assumption.
- unfold a3_age_regs.
  rewrite (RG 10%bv 24%bv ltac:(vm_compute; reflexivity)), (RG 21%bv 10%bv ltac:(vm_compute; reflexivity)),
    (RG 23%bv 23%bv ltac:(vm_compute; reflexivity)), (RG 22%bv 22%bv ltac:(vm_compute; reflexivity)),
    (RG 25%bv 25%bv ltac:(vm_compute; reflexivity)), (RG 24%bv 24%bv ltac:(vm_compute; reflexivity)),
    (RG 26%bv 26%bv ltac:(vm_compute; reflexivity)), (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)).
  split; [unfold w64, P_CHK_RA; exact Hra|].
  repeat split; assumption.
- destruct HSP1 as ((H208 & H320) & H192 & H200). destruct HAGED as (Hage & Hpost & HT1).
  destruct HOP as (H360 & H352).
  refine (conj (conj (conj _ _) (conj _ _)) (conj (conj Hage (conj Hpost _)) (conj _ _))).
  all: first [ eapply (a3_val_mem_all W mem3 (ms_mem ms)); [exact HKA | eassumption]
             | eapply (a3_garr8_all W mem3 (ms_mem ms)); [exact HKA | eassumption] ].
- destruct Hsp0 as (H208' & H320').
  split; (eapply (a3_val_mem_all W mem3 (ms_mem ms)); [exact HKA | eassumption]).
Qed.

Theorem a3_e_tj : e_tj_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold e_tj_spec.
intros cx h i n now op W0 c0 T0 T1 buf W c [Hfrom Hst].
destruct Hst as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC) as (_ & _ & _ & HFB0 & HFB1 & _).
pose proof alloc_ceiling_val as Hac.
pose proof Hsp0 as (H208 & H320).
destruct HR as (H10 & H21 & H27').
destruct HX as (Hb4 & ((H208' & H320') & H192 & H200) & Hage & HT1).
assert (Hbuf : buf < 2 ^ 64).
{ pose proof Hbody as (T & G & Lk & H & _ & _ & _ & (Hperm & _) & _).
  assert (Hin : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
  pose proof (proj1 HJ) as HAR.
  destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 _ _ HAR Hin) as (_ & _ & Hle & _ & _ & _ & Hn0).
  pose proof (req_size_pos _ (proj1 Hn0)) as Hrq. lia. }
assert (CH : forall E, d_E cx E -> YP09.chunk_ok SEGS (d_env cx E (a3_vals regs [Z_to_bv 64 now])) (rd W mem3) (d_A cx)
  (YP09.mkChunk 320 (CVal 8 (SOff (AT_X + 32) 0)))).
{ intros E0 _. apply (chunk_ok_val SEGS _ _ (d_A cx) 320 8 _ now); [| exact Hnow | lia | exact H320].
  cbn [sv_denot]. rewrite (d_env_x cx E0 _ 32) by (unfold a3_vals; rewrite length_app, length_map, length_seq; cbn; lia).
  unfold a3_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia). rewrite length_map, length_seq.
  cbn [Nat.sub nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx P_MAL_RA h n (a3_xb buf op) dsh_loop ly3 S3 W regs
  mem3 md3 k [Z_to_bv 64 now] [YP09.mkChunk 320 (CVal 8 (SOff (AT_X + 32) 0))] [] [] [] [] HC HrL Hbody
  (fun E HE => conj I (conj I (conj (Forall_cons _ _ _ (CH E HE) (Forall_nil _))
    (conj (Forall_nil _) (conj (Forall_nil _) (conj I (Forall_nil _)))))))
  ltac:(vm_compute; reflexivity)) as (E & HdE & HS).
pose proof (a3_regs_ok B cx E regs [Z_to_bv 64 now] HdE HrL) as HRO.
pose proof (proj1 (proj2 (proj2 HdE))) as HEIE.
pose proof HdE as (_ & _ & _ & _ & EF & _).
unfold ss_d in HS.
ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
pose proof (a3_env_img cx E (a3_vals regs [Z_to_bv 64 now]) HdE) as HEI.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (a3_vals regs [Z_to_bv 64 now])) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + P_MAL_RA)) with (Z_to_bv 64 (BASE + P_MAL_RA)).
psrr_branch_tok RUN BR HS SHOK Bspan.
2: { exfalso. change (SOff 541 0) with (sr_get a3_sr 10%bv) in Hc. rewrite <- (HRO 10%bv), H10 in Hc.
     cbn [sv_denot branch_taken] in Hc. apply negb_false_iff in Hc. unfold bv_eqb in Hc. apply Z.eqb_eq in Hc.
     unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ intros a Ha. exfalso. revert Ha. apply a3_nowin. vm_compute. reflexivity. }
apply SRr_ret. split; [exact Hfrom|].
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (d_S cx <= a < d_S cx) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha _. lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
  exact (a3_kept_frame Ex rsx (w_H W) mem3 (ms_mem ms) 0 0 HFr
    (fun a' Ha' => False_ind _ (a3_nowin Ex rsx a' ltac:(vm_compute; reflexivity) Ha')) a Ha ltac:(lia)) end. }
pose proof (a3_kept_all (w_H W) mem3 (ms_mem ms) (fun x Hx => HK x Hx ltac:(lia))) as HKA.
lazymatch type of HS with st_ok _ ?Ex (setpc ?ssF (SIGMA ?s)) _ =>
  pose proof (a3_pcall_pi fq Ex ssF _ s HS) as HSp;
  assert (RG : forall r r0 : bv 5, sr_get (ss_regs (setpc ssF (SIGMA s))) r = sr_get a3_sr r0 ->
    getr (ms_regs ms) r = getr regs r0)
    by (intros r r0 Heq; rewrite (st_ok_restrict_reg SEGS _ _ _ ms r HS), Heq; symmetry; exact (HRO r0))
end.
pose proof (st_ok_restrict_reg SEGS _ _ _ ms 1%bv HS) as Hra.
lazymatch type of Hra with _ = sv_denot _ (sr_get ?sr _) =>
  let v := eval vm_compute in (sr_get sr 1%bv) in change (sr_get sr 1%bv) with v in Hra end.
cbn [sv_denot] in Hra. rewrite d_env_old in Hra by (cbv; lia).
rewrite (HEIE 240%nat ltac:(cbv; lia)) in Hra.
pose proof (st_ok_restrict_reg SEGS _ _ _ ms 10%bv HS) as Ha0.
lazymatch type of Ha0 with _ = sv_denot _ (sr_get ?sr _) =>
  let v := eval vm_compute in (sr_get sr 10%bv) in change (sr_get sr 10%bv) with v in Ha0 end.
cbn [sv_denot] in Ha0. rewrite d_env_old in Ha0 by (cbv; lia). change 516%nat with AT_F in Ha0. rewrite EF in Ha0.
unfold w64 in Ha0. rewrite unsigned_lit_small in Ha0 by lia.
pose proof (st_ok_restrict_reg SEGS _ _ _ ms 11%bv HS) as Ha1.
lazymatch type of Ha1 with _ = sv_denot _ (sr_get ?sr _) =>
  let v := eval vm_compute in (sr_get sr 11%bv) in change (sr_get sr 11%bv) with v in Ha1 end.
cbn [sv_denot] in Ha1. change 563%nat with (AT_X + 32)%nat in Ha1.
rewrite (d_env_x cx E _ 32) in Ha1 by (unfold a3_vals; rewrite length_app, length_map, length_seq; cbn; lia).
unfold a3_vals in Ha1. rewrite app_nth2 in Ha1 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq in Ha1. cbn [Nat.sub nth] in Ha1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Ha1.
destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
apply (a3_land_rt B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx AF_both3_reac_disco_table_json (EV_HEAD i + 1)
  h i n n now (a3_xb buf op) _ _ W ly3 S3 mem3 _ k acc (d_env cx E (a3_vals regs [Z_to_bv 64 now])) _ ms (d_S cx) (d_S cx)
  Hfrm Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HSp eq_refl).
- cbn [ss_pc setpc]. rewrite pa_sigma_reac_disco_table_json. lia.
- exact (d_E_env cx E _ HdE).
- exact (d_env_fl cx E _).
- vm_compute. reflexivity.
- unfold LLVMF_STK. lia.
- lia.
- exact HK.
- intros a _. exact (a3_present_grows (w_H W) mem3 (ms_mem ms) HG a).
- intros a _ Ha. lia.
- split; [unfold spZ; rewrite (RG 2%bv 2%bv ltac:(vm_compute; reflexivity)); exact Hsp|].
  rewrite (RG 3%bv 3%bv ltac:(vm_compute; reflexivity)), (RG 4%bv 4%bv ltac:(vm_compute; reflexivity)),
    (RG 8%bv 8%bv ltac:(vm_compute; reflexivity)), (RG 9%bv 9%bv ltac:(vm_compute; reflexivity)),
    (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)), (RG 18%bv 18%bv ltac:(vm_compute; reflexivity)),
    (RG 20%bv 20%bv ltac:(vm_compute; reflexivity)), (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)).
  repeat split; assumption.
- rewrite (RG 12%bv 10%bv ltac:(vm_compute; reflexivity)), (RG 13%bv 21%bv ltac:(vm_compute; reflexivity)),
    (RG 21%bv 21%bv ltac:(vm_compute; reflexivity)), (RG 24%bv 10%bv ltac:(vm_compute; reflexivity)),
    (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)).
  split; [unfold w64, P_TJ_RA; exact Hra|].
  split; [rewrite Ha0; unfold w64, d_obj, dobj_off; reflexivity|].
  split; [exact Ha1|].
  repeat split; assumption.
- split; [exact Hb4|]. split; [split; [split|split]|split; [exact Hage|]].
  all: eapply (a3_val_mem_all W mem3 (ms_mem ms)) || eapply (a3_garr8_all W mem3 (ms_mem ms)); [exact HKA | eassumption].
- split; (eapply (a3_val_mem_all W mem3 (ms_mem ms)); [exact HKA | eassumption]).
Qed.

End h.
End f.
End d.

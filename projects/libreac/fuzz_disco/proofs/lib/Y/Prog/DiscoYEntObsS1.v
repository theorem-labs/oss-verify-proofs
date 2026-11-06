(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v, with its module paths changed; 107 of its 187 lines of code are new or changed and 908 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt FindEntry DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac oy_inr := repeat (first [left; reflexivity | right]).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis BCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TFIND : FindEntry.tfind_entry_spec B.

Theorem ob_s01 : ob_seg01 B MT XM_LIB RLO RHI tfib_K.
Proof using LAWS TL SEAT FACTS BRT PX.
unfold ob_seg01. intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & T & HOC & H360).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof alloc_ceiling_val as Hac.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OBS_OFF obs_sr (obs_vals regs) [] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (regs_ok_obs B cx E regs HdE HrL HAr2)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs) [] [] HctxD HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
pose proof (oy_d_E_env cx E (obs_vals regs) HdE) as HdE'.
pose proof HdE' as (_ & _ & HEI & _).
assert (EFB : ew (d_env cx E (obs_vals regs)) 516%nat = Z_to_bv 64 (d_FB cx)).
{ rewrite oy_d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & _ & HF & _). exact HF. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs)) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS).
unfold cfg_at. change (w64 (BASE + OBS_OFF)) with (Z_to_bv 64 (BASE + OBS_OFF)).
paj_run_tok RUN HS HJ SHOK OBspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
rewrite (pa_sigma_find_entry (PI := PI)) in HS.
pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hpt.
pose proof (oy_frame_eq _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as Hptr.
clear HF HFr HG.
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms.
cbn [ss_pc setpc] in Hms.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (regs_ok_obs B cx E regs HdE HrL HAr2 r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R2 := RG 2%bv ltac:(oy_inr)). assert (R3 := RG 3%bv ltac:(oy_inr)). assert (R4 := RG 4%bv ltac:(oy_inr)).
assert (R8 := RG 8%bv ltac:(oy_inr)). assert (R9 := RG 9%bv ltac:(oy_inr)). assert (R18 := RG 18%bv ltac:(oy_inr)).
assert (R19 := RG 19%bv ltac:(oy_inr)). assert (R20 := RG 20%bv ltac:(oy_inr)). assert (R27 := RG 27%bv ltac:(oy_inr)).
assert (HrL' : d_rL B cx (ms_regs ms)).
{ unfold d_rL, spZ in HrL |- *. rewrite R2, R3, R4, R8, R9, R19, R18, R20, R27. exact HrL. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?md |} _ =>
  apply SRr_ret; unfold ob_c1, d_at; exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md, k, acc end.
split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
exists T.
split; [exact (oy_oc_pt B cx h i n now op nb fr len Sg T regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) BRT Hpt HrL' HOC)|].
split; [exact (oy_val_mem_pt _ _ _ _ _ Hptr H360)|].
split; [|split; [|split]].
- rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64, OB_FE_RET. exact (codeptr_val _ 4080 HEI).
- rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EFB, oy_w64_add_w. reflexivity.
- rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EFB, oy_w64_add_w. reflexivity.
- rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 23%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EFB, oy_w64_add_w. reflexivity.
Qed.

Theorem ob_s12 : ob_seg12 B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold ob_seg12. intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & T & HOC & H360 &
  Hra & Ha0 & Ha1 & Ha23).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
assert (Hc3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HrL as (Hsp & _).
assert (FB8 : d_FB cx mod 8 = 0) by lia.
pose proof (oy_pre8 B MT XM_LIB RLO RHI tfib_K cx regs ly3 S3 W mem3 md3 k TFIND_ENTRY_STK OB_FE_RET LAWS Hc3 HrL Hra
  ltac:(unfold OB_FE_RET; lia) ltac:(unfold OB_FE_RET; reflexivity) ltac:(unfold TFIND_ENTRY_STK, ESTACK; lia)
  ltac:(unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia)) as HPRE.
eapply SRr_mono.
{ apply (TFIND fq ly3 S3 W regs mem3 md3 [] (d_obj cx OT) (d_obj cx OS) T (s_mac Sg) HPRE Himg Ha0 Ha1).
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - exact HTl.
  - exact HT.
  - change (length (firstn 6 Sg) = 6%nat). rewrite length_firstn, HSgl. reflexivity.
  - change (garr8 SEGS (mrestrict (w_H W) mem3) (d_obj cx OS) (map bv_unsigned (firstn 6 Sg))). rewrite <- firstn_map.
    replace (d_obj cx OS) with (d_obj cx OS + Z.of_nat 0) by lia.
    exact (garr8_sub_x SEGS _ _ _ 0 6 HSg ltac:(rewrite length_map; lia)).
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - exact (oy_ra_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => oy_dsh_rec_t kk ltac:(lia))).
  - exact (oy_hull_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (oy_ra_frame cx dsh_rec W mem3 2992 6 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => oy_dsh_rec_s kk ltac:(lia))).
  - exact (oy_hull_frame cx dsh_rec W mem3 2992 6 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - left. rewrite Hsp. unfold d_obj, dobj_off, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
  - unfold off_img in *. unfold d_obj, dobj_off. lia.
  - left. rewrite Hsp. unfold d_obj, dobj_off, TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *. lia.
  - exact (proj1 HTok). }
cbv beta. intros W2 c2 _ HQ. unfold tfind_entry_post, apost_base in HQ.
destruct HQ as (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & HFxr & HFxc & HJ1 & HP & HPm & (r & Hr10 & Hfind) & Hkept).
assert (HFRM1 : lib.Lib.FP.frm0 (@YK11.fp_csr fx')) by (destruct HFxc as [Ec|Ec]; [rewrite Ec; exact HFRM0 | exact Ec]).
rewrite Hsp in HJ1, Hkept.
pose proof (oy_post B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k TFIND_ENTRY_STK ly4 S4 W2 mem4 md4 LAWS Hc3
  ltac:(unfold TFIND_ENTRY_STK, ESTACK; lia) ltac:(unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia) HJ1) as Hc4.
pose proof (oy_oc_call_keep B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg T regs ly3 S3 W mem3 md3 k
  regs4 ly4 S4 W2 mem4 md4 (k + 0) TFIND_ENTRY_STK LAWS BCK Hc3 Hc4 HOC
  ltac:(unfold TFIND_ENTRY_STK, ESTACK; lia) ltac:(unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK; lia) Hkept HPm HP) as HOC4.
assert (H360' : val_mem SEGS (rd W2 mem4) (d_A cx + 360) 8 op).
{ apply (oy_val_mem_keep W W2 mem3 mem4 _ 8 _); [|exact H360]. intros j Hj.
  apply Hkept; unfold TFIND_ENTRY_STK, ESTACK, LLVMF_STK in *; lia. }
unfold ob_c2. rewrite Hra.
apply (oy_dat B MT XM_LIB RLO RHI tfib_K cx OB_FE_RET kmax accmax _ fx' ly4 S4 regs4 mem4 md4 (k + 0) acc W2 MT_TRIV HFRM1 Hc4
  ltac:(lia) Hacc).
cbv beta. exists T, r.
split; [exact HOC4|]. split; [exact H360'|].
split; [transitivity (getr regs 23%bv); [exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact Ha23]|].
split; [exact Hr10 | exact Hfind].
Qed.

End h.
End f.
End d.

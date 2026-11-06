(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v, with its module paths and module names changed; 259 of its 296 lines of code are new or changed and 201 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YC1i YC88 YI67 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonJs DiscoArm3JsonK DiscoArm3JsonBDefs DiscoArm3JsonB1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition yb2_acs : list YP09.chunk :=
  [YP09.mkChunk 320 (CVal 8 (SOff 564 0)); YP09.mkChunk 352 (CVal 8 (SOff 553 0));
   YP09.mkChunk 376 (CVal 8 (SOff 563 0))].
Definition yb2_cs : list acond := [mkAC BC_NE (SOff 541 0) (SLit 0)].
Definition yb2_rs : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 296 416 (dslot_chunks ++ yb2_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 dfhdr_chunks;
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_scr)].

Lemma yb2_sub : forall pc sr G, submem yb2_rs (ss_mem (ss_d pc sr dsh_scr yb2_acs [] [] G)).
Proof.
  intros pc sr G. cbn [ss_d ss_mem d_kregions app]. unfold yb2_rs, fshadow_region.
  apply submem_keep; [apply yb_subregion; [lia | intros c Hc; exact Hc]|].
  apply submem_keep; [apply yb_subregion; [lia | intros c Hc; exact Hc]|].
  apply submem_keep; [apply yb_subregion; [lia | intros c Hc; rewrite app_nil_r; exact Hc]|].
  apply submem_keep; [apply yb_subregion; [lia | intros c Hc; exact Hc]|].
  apply submem_nil.
Qed.

Ltac yb_vb := first [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) | idtac];
  first [change (Z.of_N 8) with 8 | idtac]; lia.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.

Theorem a3j_B2 : jseg_B2 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad j kk ks kl W cf Hjs HM.
unfold jsc_out, jcut, d_arm_at_pf, d_at in HM.
destruct HM as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & accm & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & (R10 & (R22 & R23))) &
  (HSP1 & HTAB & HBUF & (HX & K448 & K456 & K464)) & HSP0 & HBODY).
destruct HX as (HFIN & Hii & Hcount & Hlacc & HPF & HMEM & M352).
unfold JSC_KEY_OFF in K448, K456, K464.
replace (d_A cx + 448 + 8) with (d_A cx + 456) in K456 by lia.
replace (d_A cx + 448 + 16) with (d_A cx + 464) in K464 by lia.
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HFIN as (HJR & Hfinb & HNOWS & HTLEN & HTOKS).
pose proof HBUF as (Hcap & HGARR).
pose proof HMEM as (Mlen & Mpad & Mobjs & Mall).
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFSpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _ & _ & _).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = slot_ser_defs.ser_cap op).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hreq in Hbufceil, Hbufapp.
pose proof (jpairs_from_count _ _ _ _ _ _ HPF) as Hcnt.
destruct (jpairs_from_step _ _ _ _ _ _ HPF) as (j' & kk' & ks' & kl' & j2 & vk & vs & vl & c' & Hjs' & _ & H58 & _).
rewrite Hjs in Hjs'. injection Hjs' as <- <- <- <-.
pose proof (jscalar_lt (a3_text T1 now) (ii + 1) j kk ks kl ltac:(lia) Hjs) as Hjlt.
rewrite (json_ws_id _ j HNOWS ltac:(lia)) in H58.
apply at_byte_true in H58 as (Hjlen & _).
assert (Hj969 : j < 969) by (unfold jlen in Hjlen; lia).
assert (HL1 : length T1 = 400%nat).
{ destruct HTAB as ((removed & _ & Hpost) & _). exact (proj1 Hpost). }
assert (Hlo : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad (acc ++ [jobj_empty]))))
  = 144 * (count + 1)).
{ rewrite length_map, (jb_objs_bytes_len buf vpad (acc ++ [jobj_empty]) Mlen Mall), length_app, Hlacc.
  cbn [length]. lia. }
assert (HJC : jcur cx count = d_FB cx + 240 + 144 * count) by (unfold jcur, d_obj, dobj_off; lia).
pose proof (d_hslots_of_frame cx h dsh_scr W mem3 HFRM) as (H184 & H120 & H136 & H376 & H280 & H232 & H264).
pose proof HSP1 as ((H208 & H320) & H192 & H200).
assert (HOG : 0 <= dnot (d_obj cx OG) < 2 ^ 64) by (unfold dnot, d_obj, dobj_off; lia).
set (ex := [Z_to_bv 64 (dnot (d_obj cx OG)); Z_to_bv 64 now]).
set (vals := jk_vals regs ex).
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
  by (intros nn Hnn; apply d_env_old; exact Hnn).
assert (EOG : ew (d_env cx E vals) 563 = Z_to_bv 64 (dnot (d_obj cx OG))) by exact (jk_xe cx E regs ex 0 ltac:(cbn; lia)).
assert (ENOW : ew (d_env cx E vals) 564 = Z_to_bv 64 now) by exact (jk_xe cx E regs ex 1 ltac:(cbn; lia)).
assert (X3 : ew (d_env cx E vals) 534 = getr regs 3) by exact (jk_x cx E regs ex 3 ltac:(lia)).
assert (X4 : ew (d_env cx E vals) 535 = getr regs 4) by exact (jk_x cx E regs ex 4 ltac:(lia)).
assert (X10 : ew (d_env cx E vals) 541 = getr regs 10) by exact (jk_x cx E regs ex 10 ltac:(lia)).
assert (X18 : ew (d_env cx E vals) 549 = getr regs 18) by exact (jk_x cx E regs ex 18 ltac:(lia)).
assert (X20 : ew (d_env cx E vals) 551 = getr regs 20) by exact (jk_x cx E regs ex 20 ltac:(lia)).
assert (X22 : ew (d_env cx E vals) 553 = getr regs 22) by exact (jk_x cx E regs ex 22 ltac:(lia)).
assert (X23 : ew (d_env cx E vals) 554 = getr regs 23) by exact (jk_x cx E regs ex 23 ltac:(lia)).
assert (X24 : ew (d_env cx E vals) 555 = getr regs 24) by exact (jk_x cx E regs ex 24 ltac:(lia)).
assert (X25 : ew (d_env cx E vals) 556 = getr regs 25) by exact (jk_x cx E regs ex 25 ltac:(lia)).
assert (X26 : ew (d_env cx E vals) 557 = getr regs 26) by exact (jk_x cx E regs ex 26 ltac:(lia)).
assert (HCS : conds_ok (d_env cx E vals) yb2_cs).
{ unfold yb2_cs. cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ne_U, (U_atom _ 541 j (eq_trans X10 R10)), U_lit by lia.
  split; [apply negb_true_iff, Z.eqb_neq; lia | exact I]. }
assert (HAC : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) yb2_acs).
{ unfold yb2_acs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 320 8 (SOff 564 0) now);
      [apply jk_den0; [exact ENOW | lia] | yb_vb | yb_vb | exact H320].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 352 8 (SOff 553 0) count);
      [apply jk_den0; [rewrite X22, R22; reflexivity | lia] | yb_vb | yb_vb | exact M352].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 376 8 (SOff 563 0) (dnot (d_obj cx OG)));
      [apply jk_den0; [exact EOG | lia] | yb_vb | yb_vb | exact H376]. }
pose proof (DSEAT LAWS PAL fq cx dsh_scr ly3 S3 W regs mem3 md3 k E JSC_KEY_RA jk_sr vals yb2_acs [] []
  (d_facts [] yb2_cs) HCTX HE HREG HFLAG (jk_regs_ok B cx E regs ex HE HRL)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] yb2_cs HCTX HE I HCS)
  HAC (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ yb2_rs HS0 (yb2_sub _ _ _) ltac:(vm_compute; reflexivity)) as HS.
clear HS0. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS.
norm_ss HS.
assert (B2 : bv_unsigned (ew (d_env cx E vals) 2) = d_S cx)
  by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (B60 : bv_unsigned (ew (d_env cx E vals) 60) = d_A cx)
  by (rewrite EO by (unfold AT_FL; lia); change 60%nat with AT_A; rewrite E60; apply unsigned_lit_small; lia).
assert (U2w : ew (d_env cx E vals) 2 = w64 (d_S cx))
  by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (U60w : ew (d_env cx E vals) 60 = w64 (d_A cx))
  by (rewrite EO by (unfold AT_FL; lia); exact E60).
assert (U32w : ew (d_env cx E vals) 32 = w64 SHADOW_OFF)
  by (rewrite EO by (unfold AT_FL; lia); exact E32).
assert (U529w : ew (d_env cx E vals) 529 = w64 (shadow_addr (d_FB cx)))
  by (rewrite EO by (unfold AT_FL; lia); exact ESH).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals) (rd W mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
unfold cfg_at, w64.
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) PAIR_OFF.
{ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
    [reflexivity | rewrite B60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  assert (HWR : forall a, in_wrange (d_env cx E vals) rs a -> d_A cx + 296 <= a < d_A cx + 416) end.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 296 <= a < d_A cx + 416) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
  by (intros a Ha Hna; apply (aview_eq_of SEGS); apply HFr; rewrite unsigned_lit_small by lia;
      intros Hw; exact (Hna (HWR a Hw))).
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 296 <= a < d_A cx + 416) ->
  mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a)
  by (intros a Ha Hna; apply (mbyte_of_aview SEGS); apply KM; assumption).
assert (KV : forall a (nn : nat) v, 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
  (a + Z.of_nat nn <= d_A cx + 296 \/ d_A cx + 416 <= a) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v)
  by (intros a nn v H0 H1 H2 Hv; apply (val_mem_frame SEGS (rd W mem3)); [intros x Hx; apply KB; lia | exact Hv]).
assert (KG : forall a l, 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (a + Z.of_nat (length l) <= d_A cx + 296 \/ d_A cx + 416 <= a) ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l)
  by (intros a l H0 H1 H2 Hg; apply (garr8_frame SEGS (rd W mem3)); [exact Hg | intros x Hx; apply KB; lia]).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RA.
cbn [ms_mem restrict] in RA.
assert (H554 : ew (d_env cx E vals) 554 = Z_to_bv 64 (jcur cx count)) by (rewrite X23, R23; reflexivity).
assert (Hjc : 0 <= jcur cx count < 2 ^ 64) by lia.
assert (F408 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 408) 8 (jcur cx count + 24))
  by exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 296 416 408 8%N (SOff 554 24) _ RA B60
    ltac:(apply jk_in; vm_compute; reflexivity) (jk_den _ 554 _ 24 H554 Hjc) ltac:(yb_vb) ltac:(yb_vb)).
assert (F368 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 (jcur cx count + 48))
  by exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 296 416 368 8%N (SOff 554 48) _ RA B60
    ltac:(apply jk_in; vm_compute; reflexivity) (jk_den _ 554 _ 48 H554 Hjc) ltac:(yb_vb) ltac:(yb_vb)).
assert (F360 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 360) 8 (jcur cx count + 72))
  by exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 296 416 360 8%N (SOff 554 72) _ RA B60
    ltac:(apply jk_in; vm_compute; reflexivity) (jk_den _ 554 _ 72 H554 Hjc) ltac:(yb_vb) ltac:(yb_vb)).
assert (F328 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 328) 8 (jcur cx count + 96))
  by exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 296 416 328 8%N (SOff 554 96) _ RA B60
    ltac:(apply jk_in; vm_compute; reflexivity) (jk_den _ 554 _ 96 H554 Hjc) ltac:(yb_vb) ltac:(yb_vb)).
assert (F296 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 296) 8 (jcur cx count + 120))
  by exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 296 416 296 8%N (SOff 554 120) _ RA B60
    ltac:(apply jk_in; vm_compute; reflexivity) (jk_den _ 554 _ 120 H554 Hjc) ltac:(yb_vb) ltac:(yb_vb)).
assert (F352 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 352) 8 count)
  by exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 296 416 352 8%N (SOff 553 0) _ RA B60
    ltac:(apply jk_in; vm_compute; reflexivity) ltac:(apply jk_den0; [rewrite X22, R22; reflexivity | lia])
    ltac:(yb_vb) ltac:(yb_vb)).
assert (F376 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 376) 8 (dnot (d_obj cx OG)))
  by exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 296 416 376 8%N (SOff 563 0) _ RA B60
    ltac:(apply jk_in; vm_compute; reflexivity) ltac:(apply jk_den0; [exact EOG | lia])
    ltac:(yb_vb) ltac:(yb_vb)).
assert (F320 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 320) 8 now)
  by exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 296 416 320 8%N (SOff 564 0) _ RA B60
    ltac:(apply jk_in; vm_compute; reflexivity) ltac:(apply jk_den0; [exact ENOW | lia])
    ltac:(yb_vb) ltac:(yb_vb)).
assert (HHS1 : d_hslots cx h W (ms_mem ms)).
{ split; [yb_kv KV|]. split; [yb_kv KV|]. split; [yb_kv KV|]. split; [exact F376|].
  split; [yb_kv KV|]. split; [yb_kv KV | yb_kv KV]. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssf _ =>
  assert (Hchk : d_land_chk dsh_scr (ss_mem ssf) = true) by (vm_compute; reflexivity) end.
assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_scr ly3 S3 W (ms_mem ms)).
{ apply (yb_land_body B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx h n (a3_xb buf op) dsh_scr ly3 S3 W
    mem3 md' k _ _ ms (d_A cx + 296) (d_A cx + 416) HBASE HJ HFR HBODY (d_E_env cx E vals HE) (d_env_fl cx E vals)
    HS Hchk HHS1 KM HG); unfold LLVMF_STK; lia. }
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
rregU HS (22%bv : bv 5) (jcur cx count mod 8)
  ltac:(rewrite U_and_lit by lia; rewrite (U_atom _ 554 (jcur cx count) H554) by lia;
        change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity) Q22.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret.
unfold jpair_in, jcut. split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, accm.
split; [unfold cfg_at, w64, PAIR_OFF; reflexivity|].
split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|].
split; [exact HMO|]. split; [exact Hacc|]. split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ; rewrite Q2; exact B60|].
  split; [rewrite Q3, X3; exact Rgp|]. split; [rewrite Q4, X4; exact Rtp|].
  split; [rewrite Q8; exact U2w|]. split; [rewrite Q9; exact U60w|].
  split; [rewrite Q19; exact U32w|]. split; [rewrite Q18, X18; exact Rs18|].
  split; [rewrite Q20, X20; exact Rs20|]. rewrite Q27; exact U529w. }
split.
{ split; [rewrite Q26, X26; exact R26|]. split; [rewrite Q24, X24; exact R24|].
  split; [rewrite Q25, X25; exact R25|].
  split; [rewrite Q10, X10; exact R10|].
  split; [exact Q22 | rewrite Q23, X23; exact R23]. }
split.
{ split.
  { split; [split; [yb_kv KV | exact F320]|]. split; yb_kv KV. }
  split.
  { split; [exact (proj1 HTAB)|].
    apply KG; [unfold d_obj, dobj_off; lia | rewrite length_map, HL1; unfold d_obj, dobj_off; lia
              | rewrite length_map, HL1; unfold d_obj, dobj_off; lia | exact (proj2 HTAB)]. }
  split.
  { split; [exact Hcap|].
    apply KG; [lia | rewrite length_app; cbn [length]; unfold a3_r in *; lia
              | rewrite length_app; cbn [length]; unfold a3_r in *; lia | exact HGARR]. }
  split; [exact HFIN|]. split; [lia|]. split; [exact Hcount|]. split; [exact Hlacc|].
  split; [exact Hjs|]. split; [exact HPF|]. split; [reflexivity|].
  split; [exact (jb_empty_in (a3_text T1 now))|].
  split.
  { split; [exact Mlen|].
    split.
    { apply KG; [lia | rewrite length_map, Mlen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                | rewrite length_map, Mlen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Mpad]. }
    split; [|exact Mall].
    apply KG; [unfold d_obj, dobj_off; lia | rewrite Hlo; unfold d_obj, dobj_off; lia
              | rewrite Hlo; unfold d_obj, dobj_off; lia | exact Mobjs]. }
  split.
  { split; [exact F408|]. split; [exact F368|]. split; [exact F360|]. split; [exact F328|].
    split; [exact F296 | exact F352]. }
  split; [yb_kv KV|]. split; [yb_kv KV | yb_kv KV]. }
split; [split; [yb_kv KV | exact F320] | exact HBODY1].
Qed.

End h.
End f.
End d.

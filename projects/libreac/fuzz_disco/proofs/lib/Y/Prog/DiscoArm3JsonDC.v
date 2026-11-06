(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v, with its module paths and module names changed; 318 of its 358 lines of code are new or changed and 198 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45 YC1h YC1i YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonK DiscoArm3JsonDDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition jdc_sx (r : nat) : sv :=
  match r with
  | 10%nat => SLit 93 | 26%nat => SOff (AT_X + 11) 1
  | _ => jk_sx r
  end.
Definition jdc_sr : list sv := map jdc_sx (seq 0 32).
Definition jdc_rs0 : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 360 368 dslot_chunks;
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 dfhdr_chunks;
   fshadow_region AT_SH DFRAME_CLASS 4 22 (dsh_chunks dsh_scr);
   got_regionP; bcell_regionP 32].

Lemma jdc_subregion : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.

Lemma jdc_submem : forall pc sr G, submem jdc_rs0 (ss_mem (ss_d pc sr dsh_scr [] [] [] G)).
Proof.
  intros pc sr G. cbn [ss_d ss_mem]. unfold d_kregions, jdc_rs0, fshadow_region. rewrite !app_nil_r.
  apply submem_keep; [apply jdc_subregion; lia|].
  apply submem_keep; [apply jdc_subregion; lia|].
  apply submem_keep; [apply jdc_subregion; lia|].
  apply submem_keep; [apply jdc_subregion; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply jdc_subregion; lia|].
  apply submem_keep; [apply jdc_subregion; lia|].
  apply submem_nil.
Qed.

Lemma jdc_inw : forall E a, in_wrange E jdc_rs0 a ->
  (base_val E (Some AT_A) + 360 <= a < base_val E (Some AT_A) + 368) \/
  (base_val E (Some AT_SH) + 4 <= a < base_val E (Some AT_SH) + 22).
Proof.
  intros E a (r & Hin & Hr). unfold jdc_rs0 in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP, fshadow_region in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.

Lemma jdc_aluw : forall (E : env) (q : nat) v, ew E q = Z_to_bv 64 v -> 0 <= v <= 7 ->
  sv_denot E (SAluw ALU_ADD (SOff q 0) (SLit 1)) = Z_to_bv 64 (v + 1).
Proof.
  intros E q v Hq Hv. cbn [sv_denot]. rewrite Hq, unsigned_lit_small by lia. rewrite Z.add_0_r.
  assert (Hc : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma jdc_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t L. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, L. reflexivity.
Qed.

Lemma jdc_concat_len : forall {A} (f : A -> list byte) L l, Forall (fun x => length (f x) = L) l ->
  length (concat (map f l)) = (L * length l)%nat.
Proof.
  intros A f L l H. induction H as [|x l Hx H IH]; cbn [map concat length]; [lia|].
  rewrite length_app, Hx, IH. lia.
Qed.

Lemma jdc_objs_len : forall buf vpad os, length vpad = 4%nat -> Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os L H. unfold slot_ser_defs.objs_bytes. apply jdc_concat_len. eapply Forall_impl; [|exact H].
  intros o Ho. unfold slot_ser_defs.obj_bytes. rewrite (jdc_concat_len _ 24); [rewrite Ho; reflexivity|].
  apply Forall_forall. intros t _. apply jdc_slot24_len. exact L.
Qed.

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

Lemma jdc_regs_ok : forall cx E regs p,
  d_E cx E -> d_rL B cx regs ->
  getr regs 10 = Z_to_bv 64 93 -> getr regs 11 = w64 (p + 1) -> getr regs 26 = w64 (p + 2) -> 0 <= p < 2 ^ 32 ->
  regs_ok (d_env cx E (jk_vals regs [])) jdc_sr regs.
Proof.
  intros cx E regs p HE HL H10 H11 H26 Hp.
  assert (X11 : ew (d_env cx E (jk_vals regs [])) 542 = getr regs 11) by exact (jk_x cx E regs [] 11 ltac:(lia)).
  destruct HE as (HER & H32 & _ & HA60 & _ & HSH).
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
  assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx))
    by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
  { rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  apply regs_ok_by_cases. intros r Hr.
  cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | exact H10
    | rewrite X11, H11, H26; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
    | rewrite Z.add_0_r; unfold d_env;
      first
      [ rewrite ew_havoc_old by (cbv; lia);
        first [ change AT_A with 60%nat in HA60; rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
              | change AT_STK with 2%nat; rewrite HS2, Z_to_bv_bv_unsigned; exact H8
              | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
              | change AT_SH with 529%nat in HSH; rewrite HSH; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27 ]
      | unfold havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth jk_vals map seq app Nat.add AT_X AT_FL];
        match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
          let y := eval vm_compute in x in change x with y end;
        rewrite Z_to_bv_bv_unsigned; reflexivity ] ].
Qed.

Theorem a3j_D_C : jd_C_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c Hb93 Hr2 Hfin HM.
subst fin.
destruct HM as [HFROM HAT].
destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & accm & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  HP).
destruct HP as (Hi & Hn & Hnow & HrL & (R26 & R24 & R25 & R10 & R11 & R22) & (Hsp1 & Htab & Hbuf & HX) & Hsp0 & Hbody).
destruct HX as (HFIN & Hp0 & Hpr & Hcnt & Hlen & HAF & Hcur6 & Hcurin & HJM).
destruct HJM as (Hvpad & M444 & MOO & M6).
pose proof Hbody as (T & G & Lk & H & Hframe & Hshadow & Hobjs & Hblocks & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof HFIN as (Hjr & _ & _ & Hlen969 & _).
apply at_byte_true in Hb93 as (_ & Hj93).
assert (H10 : getr regs 10 = Z_to_bv 64 93) by (rewrite R10, Hj93; reflexivity).
assert (H26 : getr regs 26 = w64 (p + 2)) by (rewrite R26, Hr2; reflexivity).
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
pose proof (DSEAT LAWS PAL fq cx dsh_scr ly3 S3 W regs mem3 md3 k E MID_OFF jdc_sr (jk_vals regs []) [] [] []
  (d_facts [] []) HCTX HdE Hregs Hflag (jdc_regs_ok cx E regs p HdE HrL H10 R11 H26 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (jk_vals regs []) [] [] HCTX HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ jdc_rs0 HS0 (jdc_submem _ _ _) ltac:(vm_compute; reflexivity)) as HS.
clear HS0.
cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTKpres & GAR & GFin & GEFA & GEFL).
pose proof HdE as (HER & HE32 & HEIE & HE60 & HE516 & HE529).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA2).
assert (HSHr : kLowMemEnd <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 <= kHighShadowEnd).
{ pose proof (YCbq.shadow_addr_bounds (d_FB cx) ltac:(lia)) as Q1.
  pose proof (YCbq.shadow_addr_bounds (d_FB cx + 4096) ltac:(lia)) as Q2.
  pose proof (YCbq.shadow_range_end (d_FB cx) 4096 ltac:(lia)) as Q3. change (4096 / 8) with 512 in Q3. lia. }
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
remember (d_env cx E (jk_vals regs [])) as E1 eqn:HE1 in HS.
assert (HEI : img_env VAL A_LIM E1) by (rewrite HE1; exact (proj1 (proj2 (proj2 (d_E_env cx E _ HdE))))).
assert (HdE1 : d_E cx E1) by (rewrite HE1; apply d_E_env; exact HdE).
assert (HFL1 : ew E1 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))) by (rewrite HE1; apply d_env_fl).
assert (E1sh : ew E1 529 = Z_to_bv 64 (shadow_addr (d_FB cx))).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE529. }
assert (E1a : ew E1 60 = Z_to_bv 64 (d_A cx)).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE60. }
assert (E1s : ew E1 2 = Z_to_bv 64 (d_S cx)).
{ rewrite HE1, d_env_old by (cbv; lia). rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (E132 : ew E1 32 = Z_to_bv 64 SHADOW_OFF).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE32. }
assert (U60 : bv_unsigned (ew E1 AT_A) = d_A cx).
{ change AT_A with 60%nat. rewrite E1a. apply unsigned_lit_small. lia. }
assert (USH : bv_unsigned (ew E1 AT_SH) = shadow_addr (d_FB cx)).
{ change AT_SH with 529%nat. rewrite E1sh. apply unsigned_lit_small. lia. }
assert (X3 : ew E1 534 = getr regs 3) by (rewrite HE1; exact (jk_x cx E regs [] 3 ltac:(lia))).
assert (X4 : ew E1 535 = getr regs 4) by (rewrite HE1; exact (jk_x cx E regs [] 4 ltac:(lia))).
assert (X18 : ew E1 549 = getr regs 18) by (rewrite HE1; exact (jk_x cx E regs [] 18 ltac:(lia))).
assert (X20 : ew E1 551 = getr regs 20) by (rewrite HE1; exact (jk_x cx E regs [] 20 ltac:(lia))).
assert (X22 : ew E1 553 = getr regs 22) by (rewrite HE1; exact (jk_x cx E regs [] 22 ltac:(lia))).
assert (X24 : ew E1 555 = getr regs 24) by (rewrite HE1; exact (jk_x cx E regs [] 24 ltac:(lia))).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PI := PI) B LAWS) as RUNTOP.
unfold cfg_at, w64.
paj_run_to_shc RUNTOP HS HJ R12_OFF.
{ cbn [ss_mem]. unfold jdc_rs0.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ AT_A (d_A cx - d_S cx));
    [reflexivity | rewrite U60; lia | cbn [YP09.r_wlo]; unfold LLVMF_STK; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx))).
  - reflexivity.
  - rewrite E1sh. apply unsigned_lit_small. lia.
  - unfold fshadow_region. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite GEFA. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
    apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|]. apply awr_ok_nil. }
pose (WR := fun a : Z => d_A cx + 360 <= a < d_A cx + 368 \/
  shadow_addr (d_FB cx) + 4 <= a < shadow_addr (d_FB cx) + 22).
assert (KD : d_kept WR W mem3 W (ms_mem ms)).
{ intros a Ha Hna. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia.
  intros Hw. apply Hna. apply jdc_inw in Hw.
  change (base_val E1 (Some AT_A)) with (bv_unsigned (ew E1 AT_A)) in Hw.
  change (base_val E1 (Some AT_SH)) with (bv_unsigned (ew E1 AT_SH)) in Hw.
  rewrite U60, USH in Hw. exact Hw. }
assert (KV : forall off v, 0 <= off -> off + 8 <= 360 \/ (368 <= off /\ off + 8 <= 472) ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v).
{ intros off v H0 H1 Hv. apply (jk_val_mem_kept WR W mem3 W (ms_mem ms)); [exact KD | lia | lia | | exact Hv].
  intros x Hx. unfold WR. change (Z.of_nat 8) with 8 in Hx. zlia. }
assert (NWF : forall x, d_FB cx <= x < d_FB cx + 4096 -> ~ WR x) by (intros x Hx; unfold WR; zlia).
assert (NWB : forall b len x, in_app b len -> b <= x < b + len -> ~ WR x) by (intros b len x Hb Hx; unfold WR; zlia).
pose proof (d_hslots_of_frame cx h dsh_scr W mem3 Hframe) as (S184 & S120 & S136 & S376 & S280 & S232 & S264).
assert (HHS1 : d_hslots cx h W (ms_mem ms)).
{ split; [apply KV; [lia | lia | exact S184]|].
  split; [apply KV; [lia | lia | exact S120]|].
  split; [apply KV; [lia | lia | exact S136]|].
  split; [apply KV; [lia | lia | exact S376]|].
  split; [apply KV; [lia | lia | exact S280]|].
  split; [apply KV; [lia | lia | exact S232]|].
  apply KV; [lia | lia | exact S264]. }
assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms)
  (with_vm_backing (m_vm_lazy md3) mat md3) k) by exact (conj Hbase (conj HJ Hfrs)).
pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_ser ly3 S3 W _ k E1 _ ms HCTX1 HdE1 HFL1 HS
  ltac:(vm_compute; reflexivity) HHS1) as (HFRM4 & HSHD4).
assert (HhA : in_app h (req_size HUNT_SIZE)).
{ destruct Hblocks as (HPm & _).
  assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. right. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hin))))). }
assert (HbA : in_app buf (req_size (Z.max (slot_ser_defs.ser_cap op) 1))).
{ destruct Hblocks as (HPm & _).
  assert (Hin : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPm)). unfold a3_xb. cbn [app]. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hin))))). }
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. pose proof Hbase as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low;
    [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (HBODY4 : d_body B cx h n (a3_xb buf op) dsh_ser ly3 S3 W (ms_mem ms)).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_scr dsh_ser ly3 S3 W mem3 (ms_mem ms) (d_A cx + 360) (d_A cx + 368)
    WR Hbody).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. unfold WR in Ha. destruct Ha as [Ha | Ha]; [left; exact Ha | right]. intros Hr.
    unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hr.
    change (req_size HUNT_SIZE) with 480 in HhA. unfold HUNT_SIZE in Hr.
    destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
    + zlia.
    + zlia.
    + zlia.
    + zlia.
    + zlia.
    + specialize (HpA Hc). unfold req_size in HpA. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. zlia.
    + specialize (Hro a (proj1 Hr)). zlia.
    + unfold FF_canary in Hr. zlia.
  - exact KD.
  - intros a _ Ha. eapply apresent_grows; [exact HG | exact Ha].
  - exact HFRM4.
  - exact HSHD4.
  - lia. }
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RA.
cbn [ms_mem restrict] in RA.
assert (V360 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 360) 8 (count + 1)).
{ exact (field_of_region E1 _ AT_A (d_A cx) _ 0 472 360 368 360 8%N _ (count + 1) RA U60
    ltac:(cbn [In]; left; reflexivity) (jdc_aluw E1 553 count (eq_trans X22 R22) ltac:(lia))
    ltac:(cbn; lia) ltac:(cbn; lia)). }
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2.
prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4. prreg HS (24%bv : bv 5) Rs8.
prreg HS (27%bv : bv 5) Rs11.
pmkst HS.
apply SRr_ret. unfold jr12. exists (count + 1), (acc ++ [cur]), vpad.
unfold r12_in. split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms). eexists. exists k, accm.
split; [unfold cfg_at, w64, R12_OFF; reflexivity|].
split; [exact Hfrm0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
pose proof HrL as (L2 & L3 & L4 & L8 & L9 & L19 & L18 & L20 & L27).
split.
{ split; [unfold spZ; rewrite Rsp, E1a; apply unsigned_lit_small; lia|].
  split; [rewrite Rgp, X3; exact L3|].
  split; [rewrite Rtp, X4; exact L4|].
  split; [rewrite Rs0, E1s; reflexivity|].
  split; [rewrite Rs1, E1a; reflexivity|].
  split; [rewrite Rs3, E132; reflexivity|].
  split; [rewrite Rs2, X18; exact L18|].
  split; [rewrite Rs4, X20; exact L20|].
  rewrite Rs11, E1sh; reflexivity. }
split.
{ split; [rewrite Rs8, X24; exact R24|]. rewrite Rs11, E1sh; reflexivity. }
split.
{ split.
  { destruct Hsp1 as ((Q208 & Q320) & Q192 & Q200).
    split; [split|split]; apply KV; first [lia | assumption]. }
  split.
  { destruct Htab as (Hage & HT1). split; [exact Hage|].
    destruct Hage as (removed & Hm & Hpost). pose proof (proj1 Hpost) as HL1.
    apply (jk_garr8_kept WR W mem3 W (ms_mem ms) (d_obj cx OT) _ KD).
    + unfold d_obj, dobj_off. lia.
    + rewrite length_map, HL1. unfold d_obj, dobj_off. lia.
    + intros x Hx. rewrite length_map, HL1 in Hx. apply NWF. unfold d_obj, dobj_off in Hx. lia.
    + exact HT1. }
  split.
  { destruct Hbuf as (Hbr & HbG). split; [exact Hbr|].
    replace (req_size (Z.max (slot_ser_defs.ser_cap op) 1)) with (Z.max (slot_ser_defs.ser_cap op) 1) in HbA
      by (unfold req_size; destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia).
    pose proof (Z.le_max_l (slot_ser_defs.ser_cap op) 1) as Hmx.
    assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
      by (unfold a3_r; rewrite length_app; cbn [length]; lia).
    assert (Hb0 : 0 <= buf /\ buf + Z.max (slot_ser_defs.ser_cap op) 1 <= 2 ^ 64) by zlia.
    apply (jk_garr8_kept WR W mem3 W (ms_mem ms) buf _ KD); [lia | rewrite Lb; lia | | exact HbG].
    intros x Hx. rewrite Lb in Hx. apply (NWB buf (Z.max (slot_ser_defs.ser_cap op) 1) x HbA). lia. }
  split; [exact Hjr|].
  split; [exact V360|].
  split; [exact Hvpad|].
  assert (LO : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad (acc ++ [cur]))))
    = 144 * (count + 1)).
  { rewrite length_map, (jdc_objs_len buf vpad (acc ++ [cur]) Hvpad M6), length_app, Hlen. cbn [length]. lia. }
  apply (jk_garr8_kept WR W mem3 W (ms_mem ms) (d_obj cx OO) _ KD);
    [unfold d_obj, dobj_off; lia | rewrite LO; unfold d_obj, dobj_off; lia | | exact MOO].
  intros x Hx. rewrite LO in Hx. apply NWF. unfold d_obj, dobj_off in Hx. lia. }
split; [destruct Hsp0 as (Q208 & Q320); split; apply KV; first [lia | assumption]|].
exact HBODY4.
Qed.

End h.
End f.
End d.

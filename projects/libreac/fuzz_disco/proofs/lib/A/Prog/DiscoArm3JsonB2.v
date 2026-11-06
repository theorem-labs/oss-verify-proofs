(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 568 of its 627 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntClsCuts.v, with its module paths and module names changed; 381 of its 433 lines of code are new or changed and 575 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonJs DiscoArm3JsonBDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition jb2_sx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 18%nat => SOff 32 0 | 27%nat => SLit 1
  | _ => SOff (AT_X + r) 0
  end.
Definition jb2_sr : list sv := map jb2_sx (seq 0 32).
Definition jb2_acs : list YP09.chunk :=
  [YP09.mkChunk 408 (CVal 8 (SOff 563 0)); YP09.mkChunk 344 (CVal 8 (SOff 565 0));
   YP09.mkChunk 368 (CVal 8 (SOff 566 0))].
Definition jb2_rs0 : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 280 400 (dslot_chunks ++ jb2_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 dfhdr_chunks;
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_scr);
   got_regionP; bcell_regionP 32].
Definition jb2_al : sv := SAlu ALU_ADD (SOff 516 240) (SMd M_MUL (SOff 563 0) (SLit 144)).
Definition jb2_vals (regs : bvmap 5 word) (ex : list word) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ ex.

Lemma jb2_rs0_sub : forall pc sr G, submem jb2_rs0 (ss_mem (ss_d pc sr dsh_scr jb2_acs [] [] G)).
Proof.
intros pc sr G. cbn [ss_d ss_mem d_kregions app].
apply submem_keep; [apply subregion_refl|].
apply submem_keep.
{ unfold subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|]. intros c Hc. exact Hc. }
apply submem_keep.
{ unfold subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
  intros c Hc. rewrite app_nil_r. exact Hc. }
apply submem_keep.
{ unfold subregion, fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
  intros c Hc. exact Hc. }
apply submem_keep; [apply subregion_refl|].
apply submem_keep; [apply subregion_refl|].
apply submem_nil.
Qed.

Lemma jb2_den : forall (E : env) (q : nat) v d, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff q d) = Z_to_bv 64 (v + d).
Proof. intros E q v d Hq Hv. cbn [sv_denot]. rewrite Hq, unsigned_lit_small by lia. reflexivity. Qed.

Lemma jb2_den0 : forall (E : env) (q : nat) v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff q 0) = Z_to_bv 64 v.
Proof. intros E q v Hq Hv. cbn [sv_denot]. rewrite Hq, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. Qed.

Lemma jb2_in : forall (c : YP09.chunk) l, existsb (chunk_eqb c) l = true -> In c l.
Proof.
intros c l H. apply existsb_exists in H as (x & Hx & He). apply chunk_eqb_eq in He. subst x. exact Hx.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition jb2_ex (cx : dcx) (count now buf : Z) : list word :=
  [Z_to_bv 64 count; Z_to_bv 64 (jcur cx count); Z_to_bv 64 now; Z_to_bv 64 (buf + 1)].

Lemma jb2_apres_grow : forall (Hh : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict Hh m) (mrestrict Hh m') -> apresent Hh m a -> apresent Hh m' a.
Proof.
intros Hh m m' a HG (Hh0 & b & Hb). split; [exact Hh0|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh0, Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.

Lemma jb2_x : forall cx E regs ex j, (j < 32)%nat ->
  ew (d_env cx E (jb2_vals regs ex)) (AT_X + j) = getr regs (Z_to_bv 5 (Z.of_nat j)).
Proof.
intros cx E regs ex j Hj.
rewrite d_env_x by (unfold jb2_vals; rewrite length_app, length_map, length_seq; lia).
unfold jb2_vals. rewrite app_nth1 by (rewrite length_map, length_seq; exact Hj).
set (f := fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))).
transitivity (nth j (map f (seq 0 32)) (f 0%nat)).
- apply nth_indep. rewrite length_map, length_seq. exact Hj.
- rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma jb2_xe : forall cx E regs ex j, (j < length ex)%nat ->
  ew (d_env cx E (jb2_vals regs ex)) (AT_X + (32 + j)) = nth j ex (Z_to_bv 64 0).
Proof.
intros cx E regs ex j Hj.
rewrite d_env_x by (unfold jb2_vals; rewrite length_app, length_map, length_seq; lia).
unfold jb2_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. f_equal. lia.
Qed.

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

Lemma jb2_regs_ok : forall cx E regs ex,
  d_E cx E -> d_rL B cx regs -> getr regs 27 = Z_to_bv 64 1 ->
  regs_ok (d_env cx E (jb2_vals regs ex)) jb2_sr regs.
Proof.
intros cx E regs ex HE HL H27.
destruct HE as (HER & H32 & _ & HA60 & _ & HSH).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
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
  | exact H27
  | rewrite Z.add_0_r; unfold d_env;
    first
    [ rewrite ew_havoc_old by (cbv; lia);
      first [ change AT_A with 60%nat in HA60; rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
            | change AT_STK with 2%nat; rewrite HS2, Z_to_bv_bv_unsigned; exact H8
            | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
    | unfold havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth jb2_vals map seq app Nat.add AT_X AT_FL];
      match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
        let y := eval vm_compute in x in change x with y end;
      rewrite Z_to_bv_bv_unsigned; reflexivity ] ].
Qed.

Theorem a3j_B2 : jseg_B2 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad j kk ks kl W c Hjs HM.
destruct HM as [HFROM HAT].
destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & accm & -> & HCSR & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & (R22 & R26 & R10 & R19 & R27 & R23) &
  (Hsp1 & Htab & Hbuf & HX & K448 & K456 & K464) & Hsp0 & Hbody).
destruct HX as (HFIN & Hii & Hc0 & Hal & HPF & HJM).
destruct HJM as (M408 & M368 & Hvpad & M444 & MOO & M6).
unfold JSC_KEY_OFF in K448, K456, K464.
replace (d_A cx + 448 + 8) with (d_A cx + 456) in K456 by lia.
replace (d_A cx + 448 + 16) with (d_A cx + 464) in K464 by lia.
pose proof HFIN as (Hjr & Hfin8 & Hnows & Hlen969 & _).
pose proof (jpairs_from_count _ _ _ _ _ _ HPF) as Hcnt.
destruct (jpairs_from_step _ _ _ _ _ _ HPF) as (j' & kk' & ks' & kl' & j2 & vk & vs & vl & c' & Hjs' & _ & H58 & _).
rewrite Hjs in Hjs'. injection Hjs' as <- <- <- <-.
pose proof (jscalar_lt (a3_text T1 now) (ii + 1) j kk ks kl ltac:(lia) Hjs) as Hjlt.
rewrite (json_ws_id _ j Hnows ltac:(lia)) in H58.
apply at_byte_true in H58 as (Hjlen & _).
assert (Hj969 : j < 969) by (unfold jlen in Hjlen; lia).
assert (H27 : getr regs 27 = Z_to_bv 64 1) by exact R27.
pose proof Hbody as (Tb & Gb & Lkb & Hb & Hframe & Hshadow & Hobjs & Hblocks & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF0 & GFc & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTKpres & GAR & GFin & GEFA & GEFL).
pose proof alloc_ceiling_lt as Hceil1.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA2).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof Hblocks as (HPm & _).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hinbuf) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _).
pose proof Hbuf as (Hbr & HbG).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = slot_ser_defs.ser_cap op).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hreq in Hbufceil, Hbufapp.
assert (Hjc : 0 <= jcur cx count /\ jcur cx count + 128 <= alloc_ceiling) by (unfold jcur, d_obj, dobj_off; lia).
pose proof Hsp0 as (Q232 & Q344).
assert (HAC : Forall (YP09.chunk_ok SEGS (d_env cx E (jb2_vals regs (jb2_ex cx count now buf))) (rd W mem3) (d_A cx))
  jb2_acs).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_ok_val _ _ _ _ _ 8 _ count).
    + apply jb2_den0; [exact (jb2_xe cx E regs (jb2_ex cx count now buf) 0 ltac:(cbn; lia)) | lia].
    + cbn. lia.
    + cbn. lia.
    + exact M408.
  - apply (chunk_ok_val _ _ _ _ _ 8 _ now).
    + apply jb2_den0; [exact (jb2_xe cx E regs (jb2_ex cx count now buf) 2 ltac:(cbn; lia)) | lia].
    + cbn. lia.
    + cbn. lia.
    + exact Q344.
  - apply (chunk_ok_val _ _ _ _ _ 8 _ (buf + 1)).
    + apply jb2_den0; [exact (jb2_xe cx E regs (jb2_ex cx count now buf) 3 ltac:(cbn; lia)) | lia].
    + cbn. lia.
    + cbn. lia.
    + exact M368. }
pose proof (DSEAT LAWS PAL fq cx dsh_scr ly3 S3 W regs mem3 md3 k E JSC_KEY_RA jb2_sr
  (jb2_vals regs (jb2_ex cx count now buf)) jb2_acs [] [] (d_facts [] []) HCTX HdE Hregs Hflag
  (jb2_regs_ok cx E regs _ HdE HrL H27)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E _ [] [] HCTX HdE I I)
  HAC (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ jb2_rs0 HS0 (jb2_rs0_sub _ _ _) ltac:(vm_compute; reflexivity)) as HS1.
clear HS0.
pose proof HdE as (HER & HE32 & HEIE & HE60 & HE516 & HE529).
remember (d_env cx E (jb2_vals regs (jb2_ex cx count now buf))) as E1 eqn:HE1 in HS1.
assert (E1a : ew E1 60 = Z_to_bv 64 (d_A cx)) by (rewrite HE1, d_env_old by (cbv; lia); exact HE60).
assert (E1F : ew E1 516 = Z_to_bv 64 (d_FB cx)) by (rewrite HE1, d_env_old by (cbv; lia); exact HE516).
assert (E1s : ew E1 2 = Z_to_bv 64 (d_S cx)).
{ rewrite HE1, d_env_old by (cbv; lia). rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (E132 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite HE1, d_env_old by (cbv; lia); exact HE32).
assert (X3 : ew E1 534 = getr regs 3) by (rewrite HE1; exact (jb2_x cx E regs _ 3 ltac:(lia))).
assert (X4 : ew E1 535 = getr regs 4) by (rewrite HE1; exact (jb2_x cx E regs _ 4 ltac:(lia))).
assert (X10 : ew E1 541 = getr regs 10) by (rewrite HE1; exact (jb2_x cx E regs _ 10 ltac:(lia))).
assert (X19 : ew E1 550 = getr regs 19) by (rewrite HE1; exact (jb2_x cx E regs _ 19 ltac:(lia))).
assert (X20 : ew E1 551 = getr regs 20) by (rewrite HE1; exact (jb2_x cx E regs _ 20 ltac:(lia))).
assert (X22 : ew E1 553 = getr regs 22) by (rewrite HE1; exact (jb2_x cx E regs _ 22 ltac:(lia))).
assert (X23 : ew E1 554 = getr regs 23) by (rewrite HE1; exact (jb2_x cx E regs _ 23 ltac:(lia))).
assert (X25 : ew E1 556 = getr regs 25) by (rewrite HE1; exact (jb2_x cx E regs _ 25 ltac:(lia))).
assert (X26 : ew E1 557 = getr regs 26) by (rewrite HE1; exact (jb2_x cx E regs _ 26 ltac:(lia))).
assert (X563 : ew E1 563 = Z_to_bv 64 count)
  by (rewrite HE1; exact (jb2_xe cx E regs (jb2_ex cx count now buf) 0 ltac:(cbn; lia))).
assert (X564 : ew E1 564 = Z_to_bv 64 (jcur cx count))
  by (rewrite HE1; exact (jb2_xe cx E regs (jb2_ex cx count now buf) 1 ltac:(cbn; lia))).
assert (X565 : ew E1 565 = Z_to_bv 64 now)
  by (rewrite HE1; exact (jb2_xe cx E regs (jb2_ex cx count now buf) 2 ltac:(cbn; lia))).
assert (X566 : ew E1 566 = Z_to_bv 64 (buf + 1))
  by (rewrite HE1; exact (jb2_xe cx E regs (jb2_ex cx count now buf) 3 ltac:(cbn; lia))).
assert (HEI : img_env VAL A_LIM E1).
{ rewrite HE1. unfold d_env. apply img_env_havoc_hi; [exact HEIE | cbv; lia]. }
assert (HdE1 : d_E cx E1) by (rewrite HE1; apply d_E_env; exact HdE).
assert (HFL1 : ew E1 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))) by (rewrite HE1; apply d_env_fl).
assert (HAL : sv_denot E1 jb2_al = sv_denot E1 (SOff 564 0)).
{ rewrite (denot_lit_U E1 jb2_al), (denot_lit_U E1 (SOff 564 0)). f_equal.
  unfold jb2_al. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
  rewrite (U_atom E1 563 count X563 ltac:(lia)), (U_atom E1 564 (jcur cx count) X564 ltac:(lia)).
  rewrite (U_lit E1 144 ltac:(lia)), U_SOff, E1F, unsigned_lit_small by lia.
  unfold jcur, d_obj, dobj_off.
  rewrite (zcanon_id (d_FB cx + 240)) by (unfold M64; lia).
  rewrite (zcanon_id (count * 144)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia. }
pose proof (st_ok_pi_add_alias _ _ _ jb2_al (SOff 564 0) HS1 HAL) as HS.
clear HS1.
norm_ss HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E1
  (mrestrict (w_H W) (ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + JSC_KEY_RA)) mem3 (YK11.seg_rom SEGS)))))
  by (unfold sh_ok; apply Forall_nil).
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + JSC_KEY_RA)) with (Z_to_bv 64 (BASE + JSC_KEY_RA)).
psrr_branch_tok RUN BR HS SHOK (0, 0).
2: { exfalso. rewrite branch_ne_U, U_lit in Hc by lia.
     rewrite (U_atom E1 541 j (eq_trans X10 R10) ltac:(lia)) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) PAIR_OFF.
{ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx)).
  - reflexivity.
  - rewrite E1a. rewrite unsigned_lit_small by lia. lia.
  - cbn [YP09.r_wlo YP09.r_whi]. unfold LLVMF_STK. lia.
  - cbn [YP09.r_wlo YP09.r_whi]. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (10%bv : bv 5) Ra0.
prreg HS (18%bv : bv 5) Rs2. prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4.
prreg HS (22%bv : bv 5) Rs6. prreg HS (23%bv : bv 5) Rs7. prreg HS (24%bv : bv 5) Rs8.
prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10. prreg HS (27%bv : bv 5) Rs11.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  assert (HWR : forall a, in_wrange E1 rs a -> d_A cx + 280 <= a < d_A cx + 400) end.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    try lia.
  rewrite E1a, unsigned_lit_small in Ha by lia. lia. }
assert (HK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 280 <= a < d_A cx + 400) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hn'. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros Hw. exact (Hn' (HWR a Hw)). }
assert (HKlow : forall a, 0 <= a < alloc_ceiling -> mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a).
{ intros a Ha. apply (mbyte_of_aview SEGS). apply HK1; lia. }
assert (HVM : forall off nb v, 0 <= off -> off + Z.of_nat nb <= 280 \/ 400 <= off -> off + Z.of_nat nb <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) nb v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) nb v).
{ intros off nb v Ho1 Ho2 Ho3 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms)); [|exact Hv].
  intros q Hq. apply HK1; lia. }
assert (HPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (jb2_apres_grow _ _ _ _ HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR60.
cbn [ms_mem restrict] in HR60.
assert (EA : bv_unsigned (ew E1 60) = d_A cx) by (rewrite E1a; apply unsigned_lit_small; lia).
assert (F392 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 392) 8 (jcur cx count + 72)).
{ apply (field_of_region _ _ _ _ _ _ _ _ _ 392 8 (SOff 564 72) _ HR60 EA).
  - apply jb2_in. vm_compute. reflexivity.
  - apply jb2_den; [exact X564 | lia].
  - cbn. lia.
  - cbn. lia. }
assert (F336 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 336) 8 (jcur cx count + 96)).
{ apply (field_of_region _ _ _ _ _ _ _ _ _ 336 8 (SOff 564 96) _ HR60 EA).
  - apply jb2_in. vm_compute. reflexivity.
  - apply jb2_den; [exact X564 | lia].
  - cbn. lia.
  - cbn. lia. }
assert (F280 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 280) 8 (jcur cx count + 120)).
{ apply (field_of_region _ _ _ _ _ _ _ _ _ 280 8 (SOff 564 120) _ HR60 EA).
  - apply jb2_in. vm_compute. reflexivity.
  - apply jb2_den; [exact X564 | lia].
  - cbn. lia.
  - cbn. lia. }
assert (F344 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 344) 8 now).
{ replace now with (now + 0) by lia.
  apply (field_of_region _ _ _ _ _ _ _ _ _ 344 8 (SOff 565 0) _ HR60 EA).
  - apply jb2_in. vm_compute. reflexivity.
  - apply jb2_den; [exact X565 | lia].
  - cbn. lia.
  - cbn. lia. }
assert (F368 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 (buf + 1)).
{ replace (buf + 1) with (buf + 1 + 0) by lia.
  apply (field_of_region _ _ _ _ _ _ _ _ _ 368 8 (SOff 566 0) _ HR60 EA).
  - apply jb2_in. vm_compute. reflexivity.
  - apply jb2_den; [exact X566 | lia].
  - cbn. lia.
  - cbn. lia. }
pose proof (DLAND LAWS FFL fq cx h dsh_scr ly3 S3 W _ k E1 _ _ (conj Hbase (conj HJ Hfrs)) HdE1 HFL1 HS
  ltac:(vm_compute; reflexivity)
  (HVM 216 8%nat h ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
     ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hh216)
  (HVM 152 8%nat (h + 440) ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)
     ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) Hh152))
  as (HFRM4 & HSHD4).
assert (HBODY4 : d_body B cx h n (a3_xb buf op) dsh_scr ly3 S3 W (ms_mem ms)).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_scr dsh_scr ly3 S3 W mem3 (ms_mem ms) (d_A cx + 280) (d_A cx + 400)
    (fun a => d_A cx + 280 <= a < d_A cx + 400) Hbody).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. left. exact Ha.
  - intros a Ha Hn'. exact (HK1 a Ha Hn').
  - intros a _ Ha. exact (HPR a Ha).
  - exact HFRM4.
  - exact HSHD4.
  - lia. }
pmkst HS.
apply SRr_ret. unfold jpair_in, jcut. split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms). eexists. exists k, accm.
split; [unfold cfg_at, w64, PAIR_OFF; reflexivity|].
split; [exact HCSR|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
pose proof HrL as (L2 & L3 & L4 & L8 & L9 & L18 & L20 & L25).
split.
{ split; [unfold spZ; rewrite Rsp, E1a; apply unsigned_lit_small; lia|].
  split; [rewrite Rgp, X3; exact L3|].
  split; [rewrite Rtp, X4; exact L4|].
  split; [rewrite Rs0, E1s; reflexivity|].
  split; [rewrite Rs1, E1a; reflexivity|].
  split; [rewrite Rs2, E132; reflexivity|].
  split; [rewrite Rs4, X20; exact L20|].
  rewrite Rs9, X25; exact L25. }
split.
{ split; [rewrite Rs6, X22; exact R22|].
  split; [rewrite Rs10, X26; exact R26|].
  split; [rewrite Ra0, X10; exact R10|].
  split; [rewrite Rs3, X19; exact R19|].
  split; [rewrite Rs7, X23; exact R23|].
  split; [rewrite Rs8, X564, unsigned_lit_small by lia; reflexivity|].
  rewrite Rs11, X564, unsigned_lit_small by lia; reflexivity. }
split.
{ split.
  { destruct Hsp1 as ((P232 & P344) & P224 & P248).
    split; [split|split].
    - apply HVM; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact P232].
    - exact F344.
    - apply HVM; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact P224].
    - apply HVM; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact P248]. }
  split.
  { destruct Htab as (Hage & HT1). split; [exact Hage|].
    destruct Hage as (removed & Hm & Hpost). pose proof (proj1 Hpost) as HL1.
    apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms)) (d_obj cx OT) _ HT1).
    intros a Ha. rewrite length_map, HL1 in Ha. apply HKlow. unfold d_obj, dobj_off in Ha. lia. }
  split.
  { split; [exact Hbr|].
    apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms)) buf _ HbG).
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply HKlow. unfold a3_r in Hbr. lia. }
  split; [exact HFIN|]. split; [lia|]. split; [exact Hc0|]. split; [exact Hal|].
  split; [exact Hjs|]. split; [exact HPF|]. split; [reflexivity|].
  split; [exact (jb_empty_in (a3_text T1 now))|].
  split.
  { split.
    { apply HVM; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact M408]. }
    split; [exact F368|]. split; [exact Hvpad|].
    split.
    { apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms)) (d_A cx + 444) _ M444).
      intros a Ha. rewrite length_map, Hvpad in Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
      apply (mbyte_of_aview SEGS). apply HK1; lia. }
    split; [|exact M6].
    apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms)) (d_obj cx OO) _ MOO).
    intros a Ha.
    rewrite length_map, (jb_objs_bytes_len buf vpad (acc ++ [jobj_empty]) Hvpad M6), length_app, Hal in Ha.
    cbn [length] in Ha. apply HKlow. unfold d_obj, dobj_off in Ha. lia. }
  split; [exact F392|]. split; [exact F336|]. split; [exact F280|].
  split; [apply HVM; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact K448]|].
  split; [apply HVM; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact K456]|].
  apply HVM; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact K464]. }
split.
{ split; [apply HVM; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Q232]|].
  exact F344. }
exact HBODY4.
Qed.

End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v; 300 of its 358 lines of code are new or changed and 438 lines of the source are left out. *)
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
DiscoArm3JsonDDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition jdc_sx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 12%nat => SLit 93 | 18%nat => SOff 32 0 | 22%nat => SOff (AT_X + 11) 1
  | _ => SOff (AT_X + r) 0
  end.
Definition jdc_sr : list sv := map jdc_sx (seq 0 32).
Definition jdc_acs : list YP09.chunk := [YP09.mkChunk 408 (CVal 8 (SOff (AT_X + 32) 0))].
Definition jdc_rs0 : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ jdc_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 dfhdr_chunks;
   fshadow_region AT_SH DFRAME_CLASS 4 22 (dsh_chunks dsh_scr);
   got_regionP; bcell_regionP 32].
Definition jdc_vals (regs : bvmap 5 word) (count : Z) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ [Z_to_bv 64 count].

Lemma jdc_rs0_sub : forall pc sr G, submem jdc_rs0 (ss_mem (ss_d pc sr dsh_scr jdc_acs [] [] G)).
Proof.
intros pc sr G. cbn [ss_d ss_mem d_kregions app].
apply submem_keep; [apply subregion_refl|].
apply submem_keep.
{ unfold subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc. exact Hc. }
apply submem_keep.
{ unfold subregion. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
  intros c Hc. rewrite app_nil_r. exact Hc. }
apply submem_keep.
{ unfold subregion, fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; unfold DFRAME_SH; lia|].
  intros c Hc. exact Hc. }
apply submem_keep; [apply subregion_refl|].
apply submem_keep; [apply subregion_refl|].
apply submem_nil.
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

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma jdc_apres_grow : forall (Hh : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict Hh m) (mrestrict Hh m') -> apresent Hh m a -> apresent Hh m' a.
Proof.
intros Hh m m' a HG (Hh0 & b & Hb). split; [exact Hh0|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh0, Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.

Lemma jdc_x : forall cx E regs count j, (j < 32)%nat ->
  ew (d_env cx E (jdc_vals regs count)) (AT_X + j) = getr regs (Z_to_bv 5 (Z.of_nat j)).
Proof.
intros cx E regs count j Hj.
rewrite d_env_x by (unfold jdc_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia).
unfold jdc_vals. rewrite app_nth1 by (rewrite length_map, length_seq; exact Hj).
set (f := fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))).
transitivity (nth j (map f (seq 0 32)) (f 0%nat)).
- apply nth_indep. rewrite length_map, length_seq. exact Hj.
- rewrite map_nth, seq_nth by exact Hj. reflexivity.
Qed.

Lemma jdc_cnt : forall cx E regs count,
  ew (d_env cx E (jdc_vals regs count)) (AT_X + 32) = Z_to_bv 64 count.
Proof.
intros cx E regs count.
rewrite d_env_x by (unfold jdc_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia).
unfold jdc_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. reflexivity.
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

Lemma jdc_regs_ok : forall cx E regs count p,
  d_E cx E -> d_rL B cx regs ->
  getr regs 12 = Z_to_bv 64 93 -> getr regs 11 = w64 (p + 1) -> getr regs 22 = w64 (p + 2) -> 0 <= p < 2 ^ 32 ->
  regs_ok (d_env cx E (jdc_vals regs count)) jdc_sr regs.
Proof.
intros cx E regs count p HE HL H12 H11 H22 Hp.
destruct HE as (HER & H32 & _ & HA60 & _ & HSH).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (X11 : ew (d_env cx E (jdc_vals regs count)) 542 = getr regs 11) by exact (jdc_x cx E regs count 11 ltac:(lia)).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
all: cbn [sv_denot].
all: first
  [ rewrite getr_zero; reflexivity
  | exact H12
  | rewrite X11, H11, H22; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
  | rewrite Z.add_0_r; unfold d_env;
    first
    [ rewrite ew_havoc_old by (cbv; lia);
      first [ change AT_A with 60%nat in HA60; rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
            | change AT_STK with 2%nat; rewrite HS2, Z_to_bv_bv_unsigned; exact H8
            | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
    | unfold havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth jdc_vals map seq app Nat.add AT_X AT_FL];
      match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
        let y := eval vm_compute in x in change x with y end;
      rewrite Z_to_bv_bv_unsigned; reflexivity ] ].
Qed.

Theorem a3j_D_C : jd_C_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c Hb93 Hr2 Hfin HM.
destruct HM as [HFROM HAT].
destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & accm & -> & HCSR & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & (R22 & R26 & R10 & R11 & R12 & R21 & R19) & (Hsp1 & Htab & Hbuf & HX) & Hsp0 & Hbody).
destruct HX as (HFIN & Hp0 & Hpr & Hcnt & Hlen & HAF & Hcur6 & Hcurin & HJM).
destruct HJM as (M408 & M368 & Hvpad & M444 & MOO & M6).
pose proof Hbody as (T & G & Lk & H & Hframe & Hshadow & Hobjs & Hblocks & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof HFIN as (Hjr & _ & _ & Hlen969 & _).
apply at_byte_true in Hb93 as (_ & Hj93).
assert (H12 : getr regs 12 = Z_to_bv 64 93) by (rewrite R12, Hj93; reflexivity).
assert (H22 : getr regs 22 = w64 (p + 2)) by (rewrite R22, Hr2; reflexivity).
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
assert (HAC : Forall (YP09.chunk_ok SEGS (d_env cx E (jdc_vals regs count)) (rd W mem3) (d_A cx)) jdc_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ 408 8 _ count).
  - cbn [sv_denot]. rewrite Z.add_0_r, jdc_cnt, Z_to_bv_bv_unsigned. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact M408. }
pose proof (DSEAT LAWS PAL fq cx dsh_scr ly3 S3 W regs mem3 md3 k E MID_OFF jdc_sr (jdc_vals regs count) jdc_acs [] []
  (d_facts [] []) HCTX HdE Hregs Hflag (jdc_regs_ok cx E regs count p HdE HrL H12 R11 H22 ltac:(lia))
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (jdc_vals regs count) [] [] HCTX HdE I I)
  HAC (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ jdc_rs0 HS0 (jdc_rs0_sub _ _ _) ltac:(vm_compute; reflexivity)) as HS.
clear HS0.
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
remember (d_env cx E (jdc_vals regs count)) as E1 eqn:HE1 in HS.
assert (E1sh : ew E1 529 = Z_to_bv 64 (shadow_addr (d_FB cx))).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE529. }
assert (E1a : ew E1 60 = Z_to_bv 64 (d_A cx)).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE60. }
assert (E1s : ew E1 2 = Z_to_bv 64 (d_S cx)).
{ rewrite HE1, d_env_old by (cbv; lia). rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (E132 : ew E1 32 = Z_to_bv 64 SHADOW_OFF).
{ rewrite HE1, d_env_old by (cbv; lia). exact HE32. }
assert (X3 : ew E1 534 = getr regs 3) by (rewrite HE1; exact (jdc_x cx E regs count 3 ltac:(lia))).
assert (X4 : ew E1 535 = getr regs 4) by (rewrite HE1; exact (jdc_x cx E regs count 4 ltac:(lia))).
assert (X20 : ew E1 551 = getr regs 20) by (rewrite HE1; exact (jdc_x cx E regs count 20 ltac:(lia))).
assert (X25 : ew E1 556 = getr regs 25) by (rewrite HE1; exact (jdc_x cx E regs count 25 ltac:(lia))).
assert (X26 : ew E1 557 = getr regs 26) by (rewrite HE1; exact (jdc_x cx E regs count 26 ltac:(lia))).
assert (X32 : ew E1 563 = Z_to_bv 64 count) by (rewrite HE1; exact (jdc_cnt cx E regs count)).
assert (HEI : img_env VAL A_LIM E1).
{ rewrite HE1. unfold d_env. apply img_env_havoc_hi; [exact HEIE | cbv; lia]. }
assert (HdE1 : d_E cx E1) by (rewrite HE1; apply d_E_env; exact HdE).
assert (HFL1 : ew E1 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))) by (rewrite HE1; apply d_env_fl).
norm_ss HS.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E1
  (mrestrict (w_H W) (ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + MID_OFF)) mem3 (YK11.seg_rom SEGS)))))
  by (unfold sh_ok; apply Forall_nil).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
unfold cfg_at. change (w64 (BASE + MID_OFF)) with (Z_to_bv 64 (BASE + MID_OFF)).
paj_run_to_tok RUNTO HS HJ SHOK (0, 0) R12_OFF.
{ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx))).
  - reflexivity.
  - rewrite E1sh. apply unsigned_lit_small. lia.
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite GEFA. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2. prreg HS (20%bv : bv 5) Rs4.
prreg HS (21%bv : bv 5) Rs5. prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10.
lazymatch type of HFr with frame_of _ ?rs _ _ =>
  assert (HWR : forall a, in_wrange E1 rs a -> shadow_addr (d_FB cx) + 4 <= a < shadow_addr (d_FB cx) + 22) end.
{ intros a (r & Hin & Ha).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    try lia.
  rewrite E1sh, unsigned_lit_small in Ha by lia. lia. }
assert (HK1 : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) + 4 <= a < shadow_addr (d_FB cx) + 22) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hn'. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros Hw. exact (Hn' (HWR a Hw)). }
assert (HKA : forall a, 0 <= a < 2 ^ 64 -> (a < kLowMemEnd \/ kHighShadowEnd <= a) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hz. apply HK1; [exact Ha | lia]. }
assert (HAPP : forall lo len a, in_app lo len -> lo <= a < lo + len ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros lo len a Hap Ha. apply HKA; zlia. }
assert (HVM : forall off v, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v).
{ intros off v Ho1 Ho2 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms)); [|exact Hv].
  intros kk Hkk. cbn in Hkk. apply HKA; zlia. }
assert (HPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (jdc_apres_grow _ _ _ _ HG Ha)).
pose proof (DLAND LAWS FFL fq cx h dsh_ser ly3 S3 W _ k E1 _ _ (conj Hbase (conj HJ Hfrs)) HdE1 HFL1 HS
  ltac:(vm_compute; reflexivity) (HVM 216 h ltac:(lia) ltac:(lia) Hh216) (HVM 152 (h + 440) ltac:(lia) ltac:(lia) Hh152))
  as (HFRM4 & HSHD4).
assert (HhA : in_app h (req_size HUNT_SIZE)).
{ destruct Hblocks as (HPm & _).
  assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. right. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hin))))). }
assert (HbA : in_app buf (req_size (Z.max (slot_ser_defs.ser_cap op) 1))).
{ destruct Hblocks as (HPm & _).
  assert (Hin : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ GAR Hin))))). }
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. destruct Hbase as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (HBODY4 : d_body B cx h n (a3_xb buf op) dsh_ser ly3 S3 W (ms_mem ms)).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_scr dsh_ser ly3 S3 W mem3 (ms_mem ms) (d_S cx) (d_S cx)
    (fun a => shadow_addr (d_FB cx) + 4 <= a < shadow_addr (d_FB cx) + 22) Hbody).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a Ha. right. intros Hr.
    unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hr.
    change (req_size HUNT_SIZE) with 480 in HhA. unfold HUNT_SIZE in Hr.
    destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | Hr]]]]]].
    + zlia.
    + zlia.
    + zlia.
    + zlia.
    + zlia.
    + specialize (HpA Hc). unfold req_size in HpA. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. zlia.
    + destruct Hr as [Hr | Hr]; [specialize (Hro a (proj1 Hr)); zlia | unfold AE2k.FF_canary in Hr; zlia].
  - intros a Ha Hn'. exact (HK1 a Ha Hn').
  - intros a _ Ha. exact (HPR a Ha).
  - exact HFRM4.
  - exact HSHD4.
  - lia. }
pmkst HS.
apply SRr_ret. unfold jr12. exists (count + 1), (acc ++ [cur]), vpad.
unfold r12_in. split; [exact HFROM|].
unfold d_arm_at_pf, d_at. cbv beta.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms). eexists. exists k, accm.
split; [unfold cfg_at, w64, R12_OFF; reflexivity|].
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
{ split.
  - rewrite Rs5, X32. rewrite (unsigned_lit_small count) by lia. rewrite unsigned_lit_small by lia.
    apply Z.mod_small. lia.
  - rewrite Rs10, X26. exact R26. }
split.
{ split.
  { destruct Hsp1 as ((Q232 & Q344) & Q224 & Q248).
    split; [split|split]; apply HVM; first [lia | assumption]. }
  split.
  { destruct Htab as (Hage & HT1). split; [exact Hage|].
    destruct Hage as (removed & Hm & Hpost). pose proof (proj1 Hpost) as HL1.
    apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms)) (d_obj cx OT) _ HT1).
    intros a Ha. rewrite length_map, HL1 in Ha.
    apply (mbyte_of_aview SEGS). apply (HAPP (d_FB cx) 4096). exact GFapp. unfold d_obj, dobj_off in Ha. lia. }
  split.
  { destruct Hbuf as (Hbr & HbG). split; [exact Hbr|].
    apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms)) buf _ HbG).
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite Nat2Z.inj_add in Ha.
    pose proof (YCbq.req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
    pose proof (Z.le_max_l (slot_ser_defs.ser_cap op) 1) as Hmx. unfold a3_r in Hbr.
    apply (mbyte_of_aview SEGS). apply (HAPP buf (req_size (Z.max (slot_ser_defs.ser_cap op) 1))). exact HbA.
    set (q := Z.max (slot_ser_defs.ser_cap op) 1) in *. clearbody q. change (Z.of_nat 1) with 1 in Ha. lia. }
  split; [rewrite Hjr, Hfin; reflexivity|].
  split; [exact Hvpad|].
  apply (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms)) (d_obj cx OO) _ MOO).
  intros a Ha. rewrite length_map, (jdc_objs_len buf vpad (acc ++ [cur]) Hvpad M6), length_app, Hlen in Ha.
  cbn [length] in Ha.
  apply (mbyte_of_aview SEGS). apply (HAPP (d_FB cx) 4096). exact GFapp. unfold d_obj, dobj_off in Ha. lia. }
split; [destruct Hsp0 as (Q232 & Q344); split; apply HVM; first [lia | assumption]|].
exact HBODY4.
Qed.

End h.
End f.
End d.

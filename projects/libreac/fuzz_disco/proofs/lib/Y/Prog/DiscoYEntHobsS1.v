(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v, with its module paths, module names and numbers changed; 339 of its 410 lines of code are new or changed and 1202 lines of the source are left out. *)
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

Definition hb_acs : list YP09.chunk := [YP09.mkChunk 184 (CVal 8 (SOff (AT_X + 32) 0))].
Lemma hb_stk : RoleOf.TROLE_OF_STK = 8304.
Proof. reflexivity. Qed.
Lemma hb_map_firstn : forall (f : byte -> Z) (n : nat) (L : list byte), map f (firstn n L) = firstn n (map f L).
Proof. induction n as [|n IH]; intros [|x L]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma hb_map_skipn : forall (f : byte -> Z) (q : nat) (L : list byte), map f (skipn q L) = skipn q (map f L).
Proof. induction q as [|q IH]; intros [|x L]; cbn; try reflexivity. apply IH. Qed.
Lemma hb_map_sub : forall (f : byte -> Z) (L : list byte) (q : Z) (n : nat),
  map f (sub L q n) = firstn n (skipn (Z.to_nat q) (map f L)).
Proof. intros f L q n. unfold sub. rewrite hb_map_firstn, hb_map_skipn. reflexivity. Qed.

Ltac hb_ro HS i :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

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

Lemma hb_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma hb_vals_len : forall (regs : bvmap 5 word) (xs : list word),
  length (cl_vals regs xs) = (32 + length xs)%nat.
Proof. intros regs xs. unfold cl_vals. rewrite length_app, length_map, length_seq. reflexivity. Qed.

Lemma hb_env_h : forall cx E (regs : bvmap 5 word) (h : Z),
  ew (d_env cx E (cl_vals regs [w64 h])) (AT_X + 32) = w64 h.
Proof.
intros cx E regs h.
rewrite (hb_env_x cx E (cl_vals regs [w64 h]) 32%nat ltac:(rewrite hb_vals_len; cbn [length]; lia)).
unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. replace (32 - 32)%nat with 0%nat by lia. reflexivity.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis TROLE : RoleOf.trole_of_spec B.


Theorem hb_L1 : hb_L1_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold hb_L1_stmt. intros cx h i n now op nb fr len W c Hin.
unfold hobs_in, d_arm_at_pf in Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
destruct HX as (Hop & Hop2 & Hfrm & Hclen & HspREC & HspOP & Hlen & Hnbn).
destruct HR as (R22 & R26 & R11).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & V184 & V120 & V136 & V376 & V280 & V232 & V264).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
destruct (hb_hblk_read B MT XM_LIB RLO RHI tfib_K LAWS cx h n (dxb fr len) dsh_rec ly3 S3 W mem3 md3 k
  RoleOf.TROLE_OF_STK HctxD Hbody ltac:(rewrite hb_stk; lia))
  as (Hhin & Hh0 & Hh8 & Hh63 & Hhmr & Hhra & Hhsh & Hhoi & Hhsp & Hhfb & Hhpres).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs [w64 h])) (rd W mem3) (d_A cx)) hb_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ _ 8 _ h);
  [ rewrite sv_denot_SOff0, hb_env_h; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold HUNT_SIZE in Hh63; lia
  | lia
  | exact V184 ]. }
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [w64 h]))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env.
  rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [w64 h])) (rd W mem3)) by constructor.
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E HOBS_OFF cl_sr
  (cl_vals regs [w64 h]) hb_acs [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (cl_regs_ok B cx E regs [w64 h] HdE HrL HAr2)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs [w64 h]) [] [] HctxD HdE I I)
  HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
hb_ro HS 1%nat. hb_ro HS 2%nat. hb_ro HS 3%nat.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + HOBS_OFF)) with (Z_to_bv 64 (BASE + HOBS_OFF)).
paj_run_tok RUN HS HJ SHOK cl_span.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := cl_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
assert (Hav : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
  by (intros a; apply aview_eq_of; apply Hptr).
assert (VM3 : forall a q v0, val_mem SEGS (rd W mem3) a q v0 -> val_mem SEGS (rd W (ms_mem ms)) a q v0).
{ intros a q v0 HV. eapply YC88.val_mem_aview_kept_x; [|exact HV]. intros x _. exact (Hav x). }
pose proof (cl_regs_ok B cx E regs [w64 h] HdE HrL HAr2) as HROK.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 11; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + HB_P1)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64, HB_P1. exact (codeptr_val _ 3580 HEI). }
assert (A10 : getr (ms_regs ms) 10 = w64 h).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  rewrite sv_denot_SOff0. change 563%nat with (AT_X + 32)%nat. apply hb_env_h. }
assert (A21 : getr (ms_regs ms) 21 = w64 h).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 21%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  rewrite sv_denot_SOff0. change 563%nat with (AT_X + 32)%nat. apply hb_env_h. }
assert (A11 : getr (ms_regs ms) 11 = w64 (if 11 <? len then fr + 6 else d_obj cx OOUR))
  by (rewrite (RG 11%bv ltac:(cbv; tauto)); exact R11).
assert (Hsp4 : spZ (ms_regs ms) = d_A cx) by (unfold spZ; rewrite (RG 2%bv ltac:(cbv; tauto)); exact Hsp).
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
assert (Hframe4 : d_frame cx h dsh_rec W (ms_mem ms))
  by (apply (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W mem3 ly3 S3 W (ms_mem ms) md4 k HC4 Hframe);
      intros a _; exact (Hav a)).
assert (Hshadow4 : d_shadow cx dsh_rec W (ms_mem ms))
  by (apply (cl_shadow_keep cx dsh_rec W W mem3 (ms_mem ms) Hshadow); intros a _; exact (Hav a)).
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (BRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx)
    (fun _ => False) Hbody).
  - unfold LLVMF_STK, MFRAME in *; lia.
  - unfold MFRAME in HA1; lia.
  - intros a [].
  - intros a _ _. exact (Hav a).
  - intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite Hpt. exact Hb.
  - exact Hframe4.
  - exact Hshadow4.
  - lia. }
pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4' & Hshadow4' & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoff4 &
  Hgeo4 & Hcan4 & Hstk4 & Hawr4).
pose proof Hobjs4 as (LT4 & GT4 & TOK4 & LG4 & GG4 & GOK4 & LLk4 & GLk4 & LkOK4 & GOUR4 & LH4 & GH4 & HOK4 & EOUR4).
assert (Hfrm4 : d_frm cx nb fr len W (ms_mem ms)).
{ pose proof Hfrm as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
  eapply YC88.garr8_aview_kept; [|exact F4]. intros a _. exact (Hav a). }
destruct (hb_hblk_read B MT XM_LIB RLO RHI tfib_K LAWS cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) md4 k
  RoleOf.TROLE_OF_STK HC4 Hbody4 ltac:(rewrite hb_stk; lia))
  as (Nhin & Nh0 & Nh8 & Nh63 & Nhmr & Nhra & Nhsh & Nhoi & Nhsp & Nhfb & Nhpres).
pose proof (proj1 HJ) as HAR4.
assert (HSZ : HUNT_SIZE = 480) by reflexivity.
pose proof (req_size_pos HUNT_SIZE ltac:(lia)) as (_ & Hrqh).
assert (HPb : 0 < (if 11 <? len then fr + 6 else d_obj cx OOUR) /\
  (if 11 <? len then fr + 6 else d_obj cx OOUR) + 6 <= 2 ^ 63 /\
  length (hb_mac cx nb fr len) = 6%nat /\
  garr8 SEGS (rd W (ms_mem ms)) (if 11 <? len then fr + 6 else d_obj cx OOUR)
    (map (fun b : byte => bv_unsigned b) (hb_mac cx nb fr len)) /\
  amem_range (if 11 <? len then fr + 6 else d_obj cx OOUR) 6 /\
  range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF
    (if 11 <? len then fr + 6 else d_obj cx OOUR) 6 /\
  shadow_hull_vis (aview SEGS (w_H W) (ms_mem ms)) (if 11 <? len then fr + 6 else d_obj cx OOUR) 6 /\
  (if 11 <? len then fr + 6 else d_obj cx OOUR) + 6 <= d_A cx - RoleOf.TROLE_OF_STK).
{ unfold hb_mac. destruct (Z.ltb_spec 11 len) as [Hl12 | Hl11].
  - destruct (hb_blk_read B MT XM_LIB RLO RHI tfib_K LAWS cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k
      RoleOf.TROLE_OF_STK HC4 Hbody4 Hfrm4 Hlen ltac:(lia) ltac:(rewrite hb_stk; lia))
      as (Nfin & Nfr0 & Nfr63 & Nfrmr & Nfrra & Nfrsh & Nfroi & Nfrsp & Nfrsep & Nfrpres).
    pose proof Hfrm4 as (F1 & F2 & F3 & F4).
    pose proof Hgeo4 as (_ & _ & _ & _ & _ & Epl & _).
    assert (LL : length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) = Z.to_nat len)
      by (apply cl_rest_len; lia).
    pose proof (req_size_pos len ltac:(lia)) as (_ & Hrq).
    split; [lia|]. split; [lia|].
    split; [unfold sub; rewrite length_firstn, length_skipn, LL; lia|].
    split.
    { rewrite hb_map_sub. change (Z.to_nat 6) with 6%nat.
      replace (fr + 6) with (fr + Z.of_nat 6) by (cbn [Z.of_nat]; lia).
      apply (garr8_sub_x SEGS (rd W (ms_mem ms)) fr
        (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) 6 6 F4).
      rewrite length_map, LL. lia. }
    split; [exact (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 fr len (fr + 6) 6 HAR4 Nfin
      ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 fr len (fr + 6) 6 HAR4 Nfin
      ltac:(lia) ltac:(lia))|].
    split; [exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 fr len (fr + 6) 6 HAR4 Nfin
      ltac:(lia) ltac:(lia) ltac:(lia))|].
    lia.
  - destruct (hb_obj_read B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k OOUR
      RoleOf.TROLE_OF_STK HC4 Hshadow4 ltac:(vm_compute; reflexivity) ltac:(rewrite hb_stk; lia))
      as (No0 & No63 & No8 & Nomr & Nora & Nosh & Nooi & Nosp & Nopres).
    cbn [dobj_size] in No63, Nomr, Nora, Nosh, Nooi, Nosp, Nopres.
    split; [exact No0|]. split; [exact No63|].
    split; [unfold our_of; rewrite length_map, length_seq; reflexivity|].
    split; [exact GOUR4|]. split; [exact Nomr|]. split; [exact Nora|]. split; [exact Nosh|]. exact Nosp. }
destruct HPb as (Hp0 & Hp63 & LP & GP & Pmr & Pra & Psh & Psp).
assert (HA16 : d_A cx mod 16 = 0)
  by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans 16 32);
      [exists 2; reflexivity | apply Z.mod_divide; [lia | exact HA2]]).
assert (Esp8 : spZ (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) = spZ (ms_regs ms))
  by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
pose proof (pa_base_lo (PI := PI)) as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k
  (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) RoleOf.TROLE_OF_STK (d_A cx - d_S cx) [] HJ) as HPRE1.
specialize (HPRE1 ltac:(rewrite Esp8, Hsp4; lia)).
specialize (HPRE1 ltac:(rewrite Zminus_mod, HA16, Hal16; reflexivity)).
specialize (HPRE1 ltac:(unfold MFRAME in HA1; lia)).
specialize (HPRE1 ltac:(rewrite hb_stk; lia)).
specialize (HPRE1 ltac:(rewrite hb_stk; unfold LLVMF_STK, MFRAME in *; lia)).
specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite R1;
  apply ret_ok_codeptr_v; [unfold HB_P1; lia | unfold HB_P1; reflexivity])).
specialize (HPRE1 ltac:(unfold raZ; rewrite getr_other by reg_neq_tac; rewrite R1; unfold w64;
  rewrite unsigned_lit_small by (unfold HB_P1; lia); unfold HB_P1; lia)).
specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite (RG 3%bv ltac:(cbv; tauto)); exact Hgp)).
specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite (RG 4%bv ltac:(cbv; tauto)); exact Htp)).
specialize (HPRE1 ltac:(apply achain_low; unfold s0Z; rewrite getr_same by reg_neq_tac;
  rewrite unsigned_lit_small by lia; lia)).
rewrite Hms. rewrite (pa_sigma_role_of (PI := PI)).
eapply SRr_bind.
{ apply (TROLE fq ly3 S3 W (ms_regs ms) (ms_mem ms) md4 [] h
    (if 11 <? len then fr + 6 else d_obj cx OOUR) (sub H4 0 400) (hb_mac cx nb fr len) HPRE1).
  - exact Himg4.
  - exact A10.
  - exact A11.
  - lia.
  - exact Nh8.
  - lia.
  - exact Hp0.
  - exact Hp63.
  - unfold sub. rewrite length_firstn, length_skipn, LH4. reflexivity.
  - exact (cl_garr8_firstn SEGS _ h H4 400 GH4).
  - exact LP.
  - exact GP.
  - exact (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 h HUNT_SIZE h 400 HAR4 Nhin
      ltac:(lia) ltac:(lia)).
  - exact Pmr.
  - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 h HUNT_SIZE h 400 HAR4 Nhin
      ltac:(lia) ltac:(lia)).
  - exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md4 h HUNT_SIZE h 400 HAR4 Nhin
      ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact Pra.
  - exact Psh.
  - left. rewrite Hsp4. lia.
  - left. rewrite Hsp4. lia.
  - unfold off_img in Nhoi |- *. lia.
  - exact (proj1 (proj1 (proj2 HOK4))).
  - exact (proj1 (proj2 (proj1 (proj2 HOK4)))). }
cbv beta. intros W2 c2 Hwle Hpost.
destruct Hpost as (fx2 & ly2 & S2 & regs2 & mem2 & md2 & Hc2 & _ & Hcsr2 & HJ2 & HPR & HPerm2 & r & v & Hfr & Ev & Hr10 & Hvr).
pose proof pa_segs_low as Hsegs.
assert (HJc : ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  ([] ++ [(DFRAME_CLASS, c_fpos cx)]) ly2 S2 W2 mem2 md2 (k + 0)).
{ eapply (ajournal_sub SEGS B LAWS Hsegs);
  [ exact HJ | exact HJ2
  | rewrite Hsp4, hb_stk; unfold LLVMF_STK, MFRAME in *; lia
  | rewrite Hsp4; unfold MFRAME in HA1; lia
  | intros a (rg & [] & _) ]. }
cbn [app] in HJc. rewrite Z.add_0_r in HJc.
pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs2 & Hnev2 & _).
cbn [app] in Hfrs2.
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
  by (split; [exact Hbase | split; [exact HJc | rewrite Hfrs2; exact Hfrs]]).
assert (HK0 : acall_kept SEGS B ly3 S3 W (ms_mem ms) W2 mem2
  (spZ (ms_regs ms) - RoleOf.TROLE_OF_STK) (spZ (ms_regs ms)) (fun _ => False)).
{ apply (acall_kept_of_journal SEGS B Hsegs RoleOf.TROLE_OF_STK (spZ (ms_regs ms)) [] [] ly3 S3 W (ms_mem ms) md4
    ly2 S2 W2 mem2 md2 0 (fun _ => False) HJ2 HAR4).
  - intros a (rg & [] & _).
  - intros b m j Hb Hj _. eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | exact Hb].
  - intros (rg & [] & _). }
assert (HK : cl_kept B ly3 S3 W (ms_mem ms) W2 mem2
  (spZ (ms_regs ms) - RoleOf.TROLE_OF_STK) (spZ (ms_regs ms)) (fun _ => False)).
{ pose proof HK0 as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [intros a Ha Hnn _; exact (K1 a Ha Hnn)|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|]. exact K6. }
rewrite Hsp4 in HK.
assert (VK : forall off v0, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v0 -> val_mem SEGS (rd W2 mem2) (d_A cx + off) 8 v0).
{ intros off v0 Q1 Q2 HV.
  exact (cl_slot_keep B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k W2 mem2
    (d_A cx - RoleOf.TROLE_OF_STK) (d_A cx) (fun _ => False) off v0 HC4 HK ltac:(lia) ltac:(intros a []) Q1 Q2 HV). }
assert (CS2 : getr regs2 2 = getr (ms_regs ms) 2)
  by exact (cl_cs (ms_regs ms) regs2 2 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS3 : getr regs2 3 = getr (ms_regs ms) 3)
  by exact (cl_cs (ms_regs ms) regs2 3 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS4 : getr regs2 4 = getr (ms_regs ms) 4)
  by exact (cl_cs (ms_regs ms) regs2 4 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS8 : getr regs2 8 = getr (ms_regs ms) 8)
  by exact (cl_cs (ms_regs ms) regs2 8 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS9 : getr regs2 9 = getr (ms_regs ms) 9)
  by exact (cl_cs (ms_regs ms) regs2 9 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS18 : getr regs2 18 = getr (ms_regs ms) 18)
  by exact (cl_cs (ms_regs ms) regs2 18 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS19 : getr regs2 19 = getr (ms_regs ms) 19)
  by exact (cl_cs (ms_regs ms) regs2 19 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS20 : getr regs2 20 = getr (ms_regs ms) 20)
  by exact (cl_cs (ms_regs ms) regs2 20 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS21 : getr regs2 21 = getr (ms_regs ms) 21)
  by exact (cl_cs (ms_regs ms) regs2 21 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS22 : getr regs2 22 = getr (ms_regs ms) 22)
  by exact (cl_cs (ms_regs ms) regs2 22 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS26 : getr regs2 26 = getr (ms_regs ms) 26)
  by exact (cl_cs (ms_regs ms) regs2 26 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (CS27 : getr regs2 27 = getr (ms_regs ms) 27)
  by exact (cl_cs (ms_regs ms) regs2 27 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
assert (GH2 : garr8 SEGS (rd W2 mem2) h (map (fun b : byte => bv_unsigned b) H4)).
{ eapply YC88.garr8_aview_kept; [|exact GH4]. intros a Ha. rewrite length_map, LH4 in Ha.
  replace a with (h + (a - h)) by lia.
  exact (proj1 (proj2 HK) h HUNT_SIZE (a - h) Nhin ltac:(lia) ltac:(intros [])). }
apply SRr_ret. exists v.
unfold hb_R1, d_arm_at_pf, d_at.
exists fx2, ly2, S2, regs2, mem2, md2, k, acc.
split; [rewrite Hc2, R1; reflexivity|].
split; [exact (hb_frm0_post fq fx2 Hfrm0 Hcsr2)|].
split; [exact Hbase|]. split; [exact HJc|]. split; [rewrite Hfrs2; exact Hfrs|]. split; [exact Hk|].
split; [lia|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rL. unfold spZ in *.
  split; [rewrite CS2; exact Hsp4|].
  split; [rewrite CS3, (RG 3%bv ltac:(cbv; tauto)); exact Hgp|].
  split; [rewrite CS4, (RG 4%bv ltac:(cbv; tauto)); exact Htp|].
  split; [rewrite CS8, (RG 8%bv ltac:(cbv; tauto)); exact H8|].
  split; [rewrite CS9, (RG 9%bv ltac:(cbv; tauto)); exact H9|].
  split; [rewrite CS19, (RG 19%bv ltac:(cbv; tauto)); exact H19|].
  split; [rewrite CS18, (RG 18%bv ltac:(cbv; tauto)); exact H18|].
  split; [rewrite CS20, (RG 20%bv ltac:(cbv; tauto)); exact H20|].
  rewrite CS27, (RG 27%bv ltac:(cbv; tauto)); exact H27. }
split.
{ split; [rewrite CS22, (RG 22%bv ltac:(cbv; tauto)); exact R22|].
  split; [rewrite CS26, (RG 26%bv ltac:(cbv; tauto)); exact R26|].
  split; [exact Hr10|].
  rewrite CS21; exact A21. }
split.
{ split.
  { split; [exact Hop|]. split; [exact Hop2|].
    split; [exact (cl_frm_keep B MT XM_LIB RLO RHI tfib_K LAWS cx nb fr len ly3 S3 W (ms_mem ms) md4 k W2 mem2
      (d_A cx - RoleOf.TROLE_OF_STK) (d_A cx) (fun _ => False) h n dsh_rec HC4 Hbody4 HK
      ltac:(intros a []) Hfrm4)|].
    split.
    { pose proof HspREC as (Q200 & Q328 & Q368 & Q408).
      split; [apply VK; [lia | lia | exact (VM3 _ _ _ Q200)]|].
      split; [apply VK; [lia | lia | exact (VM3 _ _ _ Q328)]|].
      split; [apply VK; [lia | lia | exact (VM3 _ _ _ Q368)]|].
      apply VK; [lia | lia | exact (VM3 _ _ _ Q408)]. }
    split.
    { pose proof HspOP as (Q360 & Q352).
      split; [apply VK; [lia | lia | exact (VM3 _ _ _ Q360)]|].
      apply VK; [lia | lia | exact (VM3 _ _ _ Q352)]. }
    split; [exact Hlen | exact Hnbn]. }
  split; [exact Hvr|].
  exists H4. split; [exact LH4|]. split; [exact GH2|].
  intros Ev1. subst v.
  destruct (Z.ltb_spec r 0) as [Hr0 | Hr0]; [exfalso; lia|].
  destruct Hfr as [(Erm & _) | (Hrn & Hmac & _)]; [exfalso; lia|].
  exists r. split; [exact Hrn|]. split; [exact Hmac | exact Ev1]. }
split.
{ pose proof Hsp0 as (Q208 & Q320).
  split; [apply VK; [lia | lia | exact (VM3 _ _ _ Q208)]|].
  apply VK; [lia | lia | exact (VM3 _ _ _ Q320)]. }
exact (cl_body_call B MT XM_LIB RLO RHI tfib_K LAWS AIL KCAN cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) md4 k
  ly2 S2 W2 mem2 md2 k (d_A cx - RoleOf.TROLE_OF_STK) (d_A cx) (fun _ => False) [] Hbody4 HC4 HC2 HK
  ltac:(rewrite hb_stk; unfold LLVMF_STK, MFRAME in *; lia) ltac:(lia)
  ltac:(intros a []) ltac:(intros a []) (Forall_nil _) HPerm2 BTOBS).
Qed.
End h.
End f.
End d.

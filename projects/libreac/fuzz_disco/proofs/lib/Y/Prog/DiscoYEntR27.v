(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition r27_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 27%nat => SOff AT_SH 0
  | _ => SOff (AT_X + r) 0
  end.
Definition r27_sr : list sv := map r27_x (seq 0 32).
Definition r27_acs : list YP09.chunk :=
  [YP09.mkChunk 184 (CVal 8 (SOff 563 0)); YP09.mkChunk 120 (CVal 8 (SOff 564 0));
   YP09.mkChunk 136 (CVal 8 (SOff 565 0)); YP09.mkChunk 376 (CVal 8 (SOff 566 0));
   YP09.mkChunk 280 (CVal 8 (SOff 567 0)); YP09.mkChunk 232 (CVal 8 (SOff 568 0));
   YP09.mkChunk 264 (CVal 8 (SOff 569 0)); YP09.mkChunk 200 (CVal 8 (SOff 570 0));
   YP09.mkChunk 208 (CVal 8 (SOff 571 0)); YP09.mkChunk 328 (CVal 8 (SOff 572 0));
   YP09.mkChunk 368 (CVal 8 (SOff 573 0)); YP09.mkChunk 320 (CVal 8 (SOff 574 0));
   YP09.mkChunk 408 (CVal 8 (SOff 575 0))].

Ltac r27_ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition r27_vals (cx : dcx) (regs : bvmap 5 word) (h i nb fr len now : Z) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++
  map (Z_to_bv 64)
    [h; h + 440; 0; dnot (d_obj cx OG); dnot (d_obj cx OT); dnot (d_obj cx OO); dnot (d_obj cx OUSED);
     d_cur cx nb; i; nb; fr; now; len].
Lemma r27_env_old : forall cx E vals q, (q < AT_FL)%nat -> ew (d_env cx E vals) q = ew E q.
Proof. intros cx E vals q Hq. unfold d_env. apply ew_havoc_old. exact Hq. Qed.
Lemma r27_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma r27_env_fl : forall cx E vals,
  ew (d_env cx E vals) AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof.
intros cx E vals. unfold d_env. change AT_FL with (AT_FL + 0)%nat at 2.
rewrite (ew_havoc_new _ AT_FL _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma r27_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
rewrite !r27_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
- intros nn r Hn. rewrite r27_env_old; [exact (EE nn r Hn)|].
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
- unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
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
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Hypothesis DUNIV : duniv_ok B.
Hypothesis DRO : d_ro_hyps B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis BFREE : d_body_free_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BSTEP : d_body_step_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DCAN : d_can_hyps B tfib_K.

Lemma r27_objr_frame : forall cx o a, d_objr cx o a -> d_FB cx <= a < d_FB cx + DFRAME_SIZE.
Proof. intros cx o a. unfold d_objr, d_obj, DFRAME_SIZE. destruct o; cbn [dobj_off dobj_size]; lia. Qed.
Lemma r27_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; assumption | exact (pa_relro_img a Hr)]. Qed.

Lemma r27_A_range : forall cx ly3 S3 W3 mem3 md3 k,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 mem3 md3 k ->
  alloc_ceiling + LLVMF_STK <= d_S cx <= 2 ^ 47 /\ d_S cx mod 16 = 0 /\
  d_S cx - 592 <= d_A cx <= d_S cx - 576 /\ d_A cx mod 32 = 0.
Proof.
intros cx ly3 S3 W3 mem3 md3 k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as M.
unfold MFRAME in *. split; [lia|]. split; [exact Hal|]. split; [|rewrite Z.mul_comm; apply Z_mod_mult].
assert ((d_S cx - 576) mod 32 = 0 \/ (d_S cx - 576) mod 32 = 16).
{ assert (E16 : (d_S cx - 576) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  pose proof (Z.div_mod (d_S cx - 576) 16 ltac:(lia)). lia. }
lia.
Qed.

Lemma r27_EFB : forall cx ly' S' W' m' md' k,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly' S' W' m' md' k ->
  frame_addr ly' DFRAME_CLASS (c_fpos cx) = d_FB cx.
Proof.
intros cx ly' S' W' m' md' k HJ.
pose proof HJ as (_ & Hly & _).
unfold frame_addr, d_FB, frame_addr.
destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

Lemma r27_dcur_bound : forall cx m,
  ((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) ->
  AR SEGS B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ->
  0 <= m <= c_n cx -> 0 <= d_cur cx m < 2 ^ 64.
Proof.
intros cx m HINdisj HAR Hm. pose proof asan_consts as (C1 & _). unfold d_cur.
destruct HINdisj as [(Hn0 & Hp0) | (Hnr & Hin)].
- rewrite Hp0, Hn0. rewrite Hn0 in Hm. unfold A_EMPTY. lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpce & Happ & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma r27_regs_ok : forall cx E regs h i nb fr len now, d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (r27_vals cx regs h i nb fr len now)) r27_sr regs.
Proof.
intros cx E regs h i nb fr len now HE HL HA.
destruct HE as (HER & H32 & _ & HA60 & HAF & HASH).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_SH with 529%nat in HASH.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite HASH; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth r27_vals map seq app Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Lemma r27_den0 : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> sv_denot E (SOff k 0) = Z_to_bv 64 v.
Proof. intros E k v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma r27_chunk : forall E m base off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (base + off) 8 v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 e)).
Proof. intros E m base off e v He Hv Hm. eapply chunk_ok_val; [exact He | cbn; lia | cbn; lia | exact Hm]. Qed.

Lemma r27_slot : forall E m (nn : nat) b lo hi wlo whi cs off e v,
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) -> bv_unsigned (ew E nn) = b ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem SEGS m (b + off) 8 v.
Proof.
intros E m nn b lo hi wlo whi cs off e v HR Hb Hin He Hv. change 8%nat with (N.to_nat 8).
exact (field_of_region E m nn b cs lo hi wlo whi off 8%N e v HR Hb Hin He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma r27_dE_havoc : forall cx E kk ws, d_E cx E -> (530 <= kk)%nat -> d_E cx (havoc E kk ws).
Proof.
intros cx E kk ws (EE & E32 & HEI & E60 & EF & ESH) Hk. unfold d_E.
rewrite !ew_havoc_old by (unfold AT_A, AT_F, AT_SH; lia).
split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
- intros nn r Hn. rewrite ew_havoc_old; [exact (EE nn r Hn)|]. pose proof (bv_unsigned_in_range _ r) as Hr.
  change (bv_modulus 5) with 32 in Hr. lia.
- apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia].
Qed.
Lemma r27_pres_grows : forall (H : word -> bool) m m' a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG (Hh & b & Hb). split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG.
rewrite Hh, Hb in HG. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.
Lemma r27_kept_conv : forall lyc Sc W memc W2 mem2 slo shi slo' shi' (E1 E2 : Z -> Prop),
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi E1 -> slo' = slo -> shi' = shi -> (forall a, E1 a -> E2 a) ->
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo' shi' E2.
Proof.
intros lyc Sc W memc W2 mem2 slo shi slo' shi' E1 E2 (K1 & K2 & K3 & K4 & K5 & K6) -> -> HE.
split; [exact K1|]. split; [intros b m i0 Hb Hi Hn; apply (K2 b m i0 Hb Hi); intros Hx; exact (Hn (HE _ Hx))|].
split; [exact K3|]. split; [intros cid pos a Hin Hr Hn; apply (K4 cid pos a Hin Hr); intros Hx; exact (Hn (HE _ Hx))|].
split; [exact K5 | exact K6].
Qed.
Lemma r27_pi_of : forall (fq : YK11.FPState) E ss ms, st_ok (fx := fq) SEGS E ss ms ->
  st_ok_pi (fx := fq) SEGS VAL E (setpc ss (ss_pc ss - BASE)) ms.
Proof.
intros fq E ss ms HS. unfold st_ok_pi, abs_ss. destruct ss as [p0 r0 f0 m0 v0 g0]. unfold setpc in *. cbn in *.
replace (BASE + (p0 - BASE)) with p0 by lia. exact HS.
Qed.
Lemma r27_add_w : forall E (a b : nat) x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = Z_to_bv 64 (x + y).
Proof.
intros E a b x y Ha Hb. rewrite denot_lit_U, U_SAlu, !U_SOff, Ha, Hb. cbn [zalu_raw].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.add_0_r. lia.
Qed.
Lemma r27_sub_w : forall E (a b : nat) x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff b 0) (SLit (-1)))) = Z_to_bv 64 (x - y).
Proof.
intros E a b x y Ha Hb. rewrite denot_lit_U, U_SAlu, U_SMd, !U_SOff, U_SLit, Ha, Hb. cbn [zalu_raw zmd_raw].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.add_0_r. lia.
Qed.
Lemma r27_blocks_perm : forall cx h xb ly S ly' S',
  d_blocks B cx h xb ly S -> Permutation (ablocks B ly' S') (ablocks B ly S) -> d_blocks B cx h xb ly' S'.
Proof.
intros cx h xb ly S ly' S' (P & F & Bb & O) HP. unfold d_blocks.
split; [exact (Permutation_trans HP P)|]. split; [exact F|]. split; [|exact O].
rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP), <- (blocks_bytes_bsum B ly S). exact Bb.
Qed.
Lemma r27_length_our : forall pl, length (our_of pl) = 6%nat.
Proof. intros pl. unfold our_of. rewrite length_map, length_seq. reflexivity. Qed.
Lemma r27_objs_kept : forall cx h T G Lk H W m W' m',
  d_objs cx h T G Lk H W m ->
  (forall a, (d_objr cx OT a \/ d_objr cx OG a \/ d_objr cx OLOCK a \/ d_objr cx OOUR a \/ (h <= a < h + HUNT_SIZE)) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_objs cx h T G Lk H W' m'.
Proof.
intros cx h T G Lk H W m W' m'
  (LT & GT & QT & LG & GG & QG & LL & GL & QL & GO & LH & GH & QH & EO) K.
unfold d_objs.
refine (conj LT (conj _ (conj QT (conj LG (conj _ (conj QG (conj LL (conj _ (conj QL (conj _ (conj LH (conj _ (conj QH EO))))))))))))).
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GT).
  intros a Ha. apply K. left. unfold d_objr. rewrite length_map, LT in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GG).
  intros a Ha. apply K. right; left. unfold d_objr. rewrite length_map, LG in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GL).
  intros a Ha. apply K. right; right; left. unfold d_objr. rewrite length_map, LL in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GO).
  intros a Ha. apply K. right; right; right; left. unfold d_objr. rewrite length_map, r27_length_our in Ha. cbn [dobj_size]. lia.
- refine (garr8_aview_kept SEGS (w_H W) (w_H W') m m' _ _ _ GH).
  intros a Ha. apply K. right; right; right; right. rewrite length_map, LH in Ha. unfold HUNT_SIZE. lia.
Qed.
Ltac r27_in := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma r27_chain_disj : forall cx ly3 S3 W3 m3 md3 k,
  d_base B MT XM_LIB RLO RHI tfib_K cx /\
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 m3 md3 k /\ frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  bad_next (d_S cx) (ly_top ly3) (s0Z (c_regs cx)) = true \/
  fpchain (rdword (aview SEGS (w_H W3) m3)) (s0Z (c_regs cx)) (ly_top ly3) [].
Proof.
intros cx ly3 S3 W3 m3 md3 k (HB & HJ & _).
destruct HB as ((HPRE & _) & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
rewrite Etop. change (spZ (c_regs cx)) with (d_S cx) in *.
destruct Hch as [(Hb & _) | (H1 & H2 & H3 & Hf & _)].
- left. unfold bad_next. destruct Hb as [Hb|[Hb|Hb]].
  + rewrite (proj2 (Z.leb_le (s0Z (c_regs cx)) (d_S cx)) ltac:(lia)). reflexivity.
  + rewrite (proj2 (Z.leb_le (ly_top (c_ly cx) - 16) (s0Z (c_regs cx))) Hb), Bool.orb_true_r. reflexivity.
  + rewrite (proj2 (Z.eqb_neq _ _) Hb), Bool.orb_true_r. reflexivity.
- right. cbn [fpchain] in Hf |- *. destruct Hf as (r & Hr & Hr2). exists r. split; [|exact Hr2].
  rewrite <- Hr. apply rdword_ext. intros k0 Hk0. apply F1; lia.
Qed.

Lemma r27_call_chain : forall (pc0 off : Z) (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k
  (regs : bvmap 5 word) (V0 : Z),
  d_base B MT XM_LIB RLO RHI tfib_K cx /\
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 mem3 md3 k /\ frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  pc0 < BASE -> 0 <= off -> 4096 <= BASE + off ->
  In [pc0; BASE + off] (as_universe B) -> In [pc0; BASE + off; RA_LLVMF] (as_universe B) ->
  spZ regs = d_A cx -> s0Z regs = d_S cx -> d_A cx + 16 <= d_S cx -> raZ regs = BASE + off ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 8) = Some RA_LLVMF ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 16) = Some V0 ->
  (bad_next (d_S cx) (ly_top ly3) V0 = true \/ fpchain (rdword (aview SEGS (w_H W3) mem3)) V0 (ly_top ly3) []) ->
  exists ch, chain_pre ly3 (aview SEGS (w_H W3) mem3) regs ch /\
    In (call_trace0 pc0 regs ch) (as_universe B).
Proof.
intros pc0 off cx ly3 S3 W3 mem3 md3 k regs V0 Hctx Hpc0 Hoff Hra4 HU2 HU3 Hsp Hs0 HAS Hra Hsave HV0 HCH.
assert (Hrane : (BASE + off =? pc0) = false) by (apply Z.eqb_neq; lia).
assert (Htr0 : forall l, (length l <= 1)%nat -> In (pc0 :: [BASE + off] ++ l) (as_universe B) ->
          In (firstn kUnwindMax (pc0 :: (if BASE + off =? pc0 then [] else [BASE + off]) ++ l)) (as_universe B)).
{ intros l Hlen Hl. rewrite Hrane. cbn [app] in *.
  destruct l as [|x [|y l']]; cbn [length] in Hlen; try lia;
  change kUnwindMax with 30%nat; cbn [firstn]; exact Hl. }
assert (Htr1 : In (firstn kUnwindMax (pc0 :: (if BASE + off =? pc0 then [] else [BASE + off]) ++
          (if RA_LLVMF =? pc0 then [] else [RA_LLVMF]) ++ [])) (as_universe B)).
{ destruct (Z.eqb_spec RA_LLVMF pc0) as [He|Hne].
  - apply Htr0; [cbn [length app]; lia|]. cbn [app]. exact HU2.
  - apply Htr0; [cbn [length app]; lia|]. cbn [app]. exact HU3. }
unfold chain_pre, frame0_ok, call_trace0, unwind_of_chain.
rewrite Hra.
destruct (spZ regs + 16 <? ly_top ly3) eqn:Hf0.
- destruct (bad_next (spZ regs) (ly_top ly3) (s0Z regs)) eqn:Hbn.
  + exists []. split; [split; [lia | reflexivity]|].
    cbn [flat_map app]. apply Htr0; [cbn [length]; lia|]. cbn [app]. exact HU2.
  + exists [(s0Z regs, RA_LLVMF, V0)]. split.
    { unfold bad_next in Hbn.
      apply Bool.orb_false_elim in Hbn as [Hbn1 Hbn3].
      apply Bool.orb_false_elim in Hbn1 as [Hbn1 Hbn2].
      apply Z.leb_gt in Hbn1. apply Z.leb_gt in Hbn2.
      apply Bool.negb_false_iff, Z.eqb_eq in Hbn3.
      split; [lia|]. split; [lia|].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hbn3|].
      rewrite <- Hs0 in Hsave, HV0. split; [exact Hsave|]. split; [exact HV0|].
      split; [unfold RA_LLVMF; lia|].
      rewrite Hs0. destruct HCH as [Hb|Hf].
      - rewrite Hb. reflexivity.
      - destruct (bad_next (d_S cx) (ly_top ly3) V0); [reflexivity | exact Hf]. }
    { cbn [flat_map app]. exact Htr1. }
- exists []. split; [split; [lia | reflexivity]|].
  cbn [flat_map app]. apply Htr0; [cbn [length]; lia|]. cbn [app]. exact HU2.
Qed.

Theorem pb_r27 : r27_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold r27_spec.
intros cx h i n now nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & _ & HX & Hsp0 & Hbody).
destruct HX as (Hfrm2 & HspREC & Hlennb & Hnnb).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & HRGf & Hfl & Hh184 & Hh120 & Hh136 & Hh376 & Hh280 & Hh232 & Hh264).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (proj1 HJ) as HAR3.
assert (Hin3 : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds _ _ LAWS ly3 S3 W mem3 md3 DFRAME_CLASS (c_fpos cx) HAR3 Hin3) as (HFB1x & HFB2x & HFBappx).
rewrite (r27_EFB cx ly3 S3 W mem3 md3 k HJ) in HFB1x, HFB2x, HFBappx.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HFB1x, HFB2x, HFBappx.
destruct (r27_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in *; lia).
pose proof Hbase as ((HPRE0 & _ & _ & _ & HINdisj & _) & _).
pose proof Hgeo as (Hg1 & Hg2 & Hg3 & Hg4 & Hgce & Hg6 & Hg7 & Hg8).
assert (HFB1 : 4096 <= d_FB cx) by exact HFB1x.
assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ destruct Hblocks as (HP & _). eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ h HUNT_SIZE HAR3 Hhin) as (_ & Hh4096 & Hhce & _).
destruct Hsp0 as (V208 & V320).
pose proof HspREC as (V200 & V328 & V368 & V408).
pose proof Hfrm2 as (Hlen0 & Hfr0imp & Hnbcn & Hgarr).
assert (Hnb0 : 0 <= nb) by lia.
assert (Rcn : c_n cx < 2 ^ 26) by (destruct HINdisj as [(-> & _) | (Hr & _)]; lia).
assert (Hdcurnb : 0 <= d_cur cx nb < 2 ^ 64) by (apply (r27_dcur_bound cx nb HINdisj (proj1 HPRE0)); lia).
assert (Hfrbound : 0 <= fr < 2 ^ 64).
{ destruct (Z.eq_dec fr 0) as [->|Nfr]; [lia|].
  assert (Hinfr : In (fr, len) (ablocks B ly3 S3)).
  { destruct Hblocks as (HP & _). eapply Permutation_in; [apply Permutation_sym; exact HP|].
    apply in_or_app. left. unfold dxb. rewrite (proj2 (Z.eqb_neq fr 0) Nfr). left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ fr len HAR3 Hinfr) as (_ & Hf4096 & Hfce & _).
  pose proof (req_size_pos len ltac:(lia)) as (Hrq1 & _). lia. }
set (vals := r27_vals cx regs h i nb fr len now).
assert (EX : forall j, (j < 45)%nat -> ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0)).
{ intros j Hj. apply r27_env_x. subst vals. unfold r27_vals. rewrite length_app, length_map, length_map, length_seq. cbn. lia. }
assert (E563 : ew (d_env cx E vals) 563 = Z_to_bv 64 h) by (exact (EX 32%nat ltac:(lia))).
assert (E564 : ew (d_env cx E vals) 564 = Z_to_bv 64 (h + 440)) by (exact (EX 33%nat ltac:(lia))).
assert (E565 : ew (d_env cx E vals) 565 = Z_to_bv 64 0) by (exact (EX 34%nat ltac:(lia))).
assert (E566 : ew (d_env cx E vals) 566 = Z_to_bv 64 (dnot (d_obj cx OG))) by (exact (EX 35%nat ltac:(lia))).
assert (E567 : ew (d_env cx E vals) 567 = Z_to_bv 64 (dnot (d_obj cx OT))) by (exact (EX 36%nat ltac:(lia))).
assert (E568 : ew (d_env cx E vals) 568 = Z_to_bv 64 (dnot (d_obj cx OO))) by (exact (EX 37%nat ltac:(lia))).
assert (E569 : ew (d_env cx E vals) 569 = Z_to_bv 64 (dnot (d_obj cx OUSED))) by (exact (EX 38%nat ltac:(lia))).
assert (E570 : ew (d_env cx E vals) 570 = Z_to_bv 64 (d_cur cx nb)) by (exact (EX 39%nat ltac:(lia))).
assert (E571 : ew (d_env cx E vals) 571 = Z_to_bv 64 i) by (exact (EX 40%nat ltac:(lia))).
assert (E572 : ew (d_env cx E vals) 572 = Z_to_bv 64 nb) by (exact (EX 41%nat ltac:(lia))).
assert (E573 : ew (d_env cx E vals) 573 = Z_to_bv 64 fr) by (exact (EX 42%nat ltac:(lia))).
assert (E574 : ew (d_env cx E vals) 574 = Z_to_bv 64 now) by (exact (EX 43%nat ltac:(lia))).
assert (E575 : ew (d_env cx E vals) 575 = Z_to_bv 64 len) by (exact (EX 44%nat ltac:(lia))).
assert (Hdnotb : forall o, 0 <= dnot (d_obj cx o) < 2 ^ 64).
{ intros o. unfold dnot, d_obj.
  assert (Hoff2 : 0 <= dobj_off o <= 2992) by (destruct o; cbn [dobj_off]; lia).
  lia. }
assert (Hhb : 0 <= h < 2 ^ 64) by (unfold HUNT_SIZE in *; lia).
assert (Hh440b : 0 <= h + 440 < 2 ^ 64) by (unfold HUNT_SIZE in *; lia).
assert (HAC : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) r27_acs).
{ unfold r27_acs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (r27_chunk _ _ _ _ _ h); [apply r27_den0; exact E563 | exact Hhb | exact Hh184].
  - apply (r27_chunk _ _ _ _ _ (h + 440)); [apply r27_den0; exact E564 | exact Hh440b | exact Hh120].
  - apply (r27_chunk _ _ _ _ _ 0); [apply r27_den0; exact E565 | lia | exact Hh136].
  - apply (r27_chunk _ _ _ _ _ (dnot (d_obj cx OG))); [apply r27_den0; exact E566 | apply Hdnotb | exact Hh376].
  - apply (r27_chunk _ _ _ _ _ (dnot (d_obj cx OT))); [apply r27_den0; exact E567 | apply Hdnotb | exact Hh280].
  - apply (r27_chunk _ _ _ _ _ (dnot (d_obj cx OO))); [apply r27_den0; exact E568 | apply Hdnotb | exact Hh232].
  - apply (r27_chunk _ _ _ _ _ (dnot (d_obj cx OUSED))); [apply r27_den0; exact E569 | apply Hdnotb | exact Hh264].
  - apply (r27_chunk _ _ _ _ _ (d_cur cx nb)); [apply r27_den0; exact E570 | exact Hdcurnb | exact V200].
  - apply (r27_chunk _ _ _ _ _ i); [apply r27_den0; exact E571 | unfold MAX_OPS in *; lia | exact V208].
  - apply (r27_chunk _ _ _ _ _ nb); [apply r27_den0; exact E572 | lia | exact V328].
  - apply (r27_chunk _ _ _ _ _ fr); [apply r27_den0; exact E573 | exact Hfrbound | exact V368].
  - apply (r27_chunk _ _ _ _ _ now); [apply r27_den0; exact E574 | lia | exact V320].
  - apply (r27_chunk _ _ _ _ _ len); [apply r27_den0; exact E575 | unfold REC_MAX in *; lia | exact V408]. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E R27_OFF r27_sr vals r27_acs [] []
  (d_facts [] []) HC HdE HRGf Hfl (r27_regs_ok cx E regs h i nb fr len now HdE HrL HAr2)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HC HdE I I)
  HAC (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
fs_roF HS. r27_ro_base HS 516%nat.
pose proof (r27_E_env cx E vals HdE) as HdEd.
pose proof HdEd as (_ & _ & HEI & _).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals) (rd W mem3)) by constructor.
pose proof (paj_run (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUN.
assert (E60 : bv_unsigned (ew (d_env cx E vals) 60%nat) = d_S cx + (d_A cx - d_S cx)).
{ rewrite r27_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & HA & _). unfold AT_A in HA. rewrite HA.
  unfold w64. rewrite unsigned_lit_small by exact HAr2. lia. }
unfold cfg_at. change (w64 (BASE + R27_OFF)) with (Z_to_bv 64 (BASE + R27_OFF)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
    [reflexivity | exact E60 | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (Hctx4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (proj1 HJ) as HAR4.
pose proof Hbase as ((HPRE & Hra0 & _ & _ & Hpn & Hnl & _ & Hfr0 & HNEV & _) & _).
pose proof HdE as (EE & E32 & _ & E60v & E516v & E529v).
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS).
  rewrite (r27_regs_ok cx E regs h i nb fr len now HdE HrL HAr2 r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr. }
assert (R10 : getr (ms_regs ms) 10 = w64 fr).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  lazymatch goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end.
  apply r27_den0. exact E573. }
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 7476)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS). exact (codeptr_val _ 7476 HEI). }
rewrite (pal_free B TL) in HS.
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
pose proof pa_B_ok as HBok.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = d_S cx + (d_A cx - d_S cx)).
{ unfold spZ. rewrite (RG 2%bv ltac:(cbv; tauto)). pose proof HrL as (Hsp & _). unfold spZ in Hsp. lia. }
assert (Hs0' : s0Z (ms_regs ms) = d_S cx).
{ unfold s0Z. rewrite (RG 8%bv ltac:(cbv; tauto)). pose proof HrL as (_ & _ & _ & H8 & _). rewrite H8. unfold w64.
  apply unsigned_lit_small. unfold LLVMF_STK in *; lia. }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (RG 3%bv ltac:(cbv; tauto)); exact (proj1 (proj2 HrL))).
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (RG 4%bv ltac:(cbv; tauto)); exact (proj1 (proj2 (proj2 HrL)))).
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 7476))) by (apply ret_ok_codeptr_v; lia).
assert (Hraz : raZ (ms_regs ms) = BASE + 7476) by (unfold raZ; rewrite R1; apply unsigned_lit_small; lia).
assert (Hev : st_nev S3 < EV_MAX) by (unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, MAX_OPS in *; lia).
assert (USP2 : bv_unsigned (ew (d_env cx E vals) 2) = d_S cx)
  by (rewrite r27_env_old by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
pose proof (st_ok_region_nth (d_env cx E vals) _ (restrict (w_H W) ms) 0 _ HS eq_refl) as HRS0.
cbn [ms_mem restrict] in HRS0.
assert (HRD8 : rdword (aview SEGS (w_H W) (ms_mem ms)) (d_S cx - 8) = Some RA_LLVMF).
{ apply rdword_of_val_mem; [|unfold RA_LLVMF; lia].
  replace (d_S cx - 8) with (d_S cx + (-8)) by lia.
  eapply (r27_slot _ _ 2%nat _ _ _ _ _ _ (-8) (SOff 1 0)); [exact HRS0 | exact USP2 | r27_in | | unfold RA_LLVMF; lia].
  apply r27_den0. rewrite r27_env_old by (unfold AT_FL; lia). rewrite (EE 1%nat 1%bv eq_refl). unfold raZ in Hra0.
  rewrite <- Hra0. symmetry. apply Z_to_bv_bv_unsigned. }
assert (HRD16 : rdword (aview SEGS (w_H W) (ms_mem ms)) (d_S cx - 16) = Some (s0Z (c_regs cx))).
{ pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr8. change (bv_modulus 64) with (2 ^ 64) in Hr8.
  apply rdword_of_val_mem; [|unfold s0Z; lia].
  replace (d_S cx - 16) with (d_S cx + (-16)) by lia.
  eapply (r27_slot _ _ 2%nat _ _ _ _ _ _ (-16) (SOff 8 0)); [exact HRS0 | exact USP2 | r27_in | | unfold s0Z; lia].
  apply r27_den0. rewrite r27_env_old by (unfold AT_FL; lia). rewrite (EE 8%nat 8%bv eq_refl). unfold s0Z.
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (HU2 : In [pc_free_ra0 (as_code B); BASE + 7476] (as_universe B)) by (apply DUNIV; unfold d_sites; r27_in).
assert (HU3 : In [pc_free_ra0 (as_code B); BASE + 7476; RA_LLVMF] (as_universe B)) by (apply DUNIV; unfold d_sites; r27_in).
destruct (r27_call_chain (pc_free_ra0 (as_code B)) 7476 cx ly3 S3 W (ms_mem ms) md4 k (ms_regs ms)
  (s0Z (c_regs cx)) Hctx4 (proj1 (pal_rt_below B TL)) ltac:(lia) ltac:(lia) HU2 HU3 ltac:(lia) Hs0' ltac:(lia) Hraz HRD8 HRD16
  (r27_chain_disj cx ly3 S3 W (ms_mem ms) md4 k Hctx4)) as (ch & Hch & Htr).
pose proof (r27_pi_of fq _ _ _ HS) as HSpi. cbn [ss_pc setpc] in HSpi.
pose proof (st_ok_region_nth (d_env cx E vals) _ (restrict (w_H W) ms) 1 _ HS eq_refl) as HR60c.
cbn [ms_mem restrict] in HR60c.
assert (E60A : bv_unsigned (ew (d_env cx E vals) 60%nat) = d_A cx) by lia.
assert (L184 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 184) 8 h)
  by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 184 (SOff 563 0)); [exact HR60c | exact E60A | r27_in | apply r27_den0; exact E563 | exact Hhb]).
assert (L120 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 120) 8 (h + 440))
  by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 120 (SOff 564 0)); [exact HR60c | exact E60A | r27_in | apply r27_den0; exact E564 | exact Hh440b]).
assert (L136 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 136) 8 0)
  by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 136 (SOff 565 0)); [exact HR60c | exact E60A | r27_in | apply r27_den0; exact E565 | lia]).
assert (L376 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 376) 8 (dnot (d_obj cx OG)))
  by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 376 (SOff 566 0)); [exact HR60c | exact E60A | r27_in | apply r27_den0; exact E566 | apply Hdnotb]).
assert (L280 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 280) 8 (dnot (d_obj cx OT)))
  by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 280 (SOff 567 0)); [exact HR60c | exact E60A | r27_in | apply r27_den0; exact E567 | apply Hdnotb]).
assert (L232 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 232) 8 (dnot (d_obj cx OO)))
  by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 232 (SOff 568 0)); [exact HR60c | exact E60A | r27_in | apply r27_den0; exact E568 | apply Hdnotb]).
assert (L264 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)))
  by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 264 (SOff 569 0)); [exact HR60c | exact E60A | r27_in | apply r27_den0; exact E569 | apply Hdnotb]).
destruct (LAND LAWS FFL fq cx h dsh_rec ly3 S3 W md4 k (d_env cx E vals) _ ms Hctx4 HdEd (r27_env_fl cx E vals)
  HSpi ltac:(vm_compute; reflexivity) L184 L120 L136 L376 L280 L232 L264) as [Hframe4 Hshadow4].
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (BRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx + 472)
    (fun a => d_A cx <= a < d_A cx + 472) Hbody).
  - unfold LLVMF_STK in *; lia.
  - lia.
  - intros a Ha. left. exact Ha.
  - intros a Ha HnR. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia.
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; first [lia | rewrite E60A in Hr; lia] |]).
    destruct Hin.
  - intros a _ Hp. exact (r27_pres_grows _ _ _ a HG Hp).
  - exact Hframe4.
  - exact Hshadow4.
  - lia. }
pose proof (r27_EFB cx ly3 S3 W (ms_mem ms) md4 k HJ) as EFB3.
assert (POST : forall W2 ly2 S2 regs2 mem2 md2, wle W W2 ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved (ms_regs ms) regs2 -> frames S2 = frames S3 ->
  acall_kept SEGS B ly3 S3 W (ms_mem ms) W2 mem2 (d_A cx - 16384) (d_A cx) (d_inxb (dxb fr len)) ->
  (d_frame cx h dsh_rec W2 mem2 -> d_shadow cx dsh_rec W2 mem2 -> d_body B cx h n [] dsh_rec ly2 S2 W2 mem2) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 7476)) mem2 (seg_rom SEGS)) md2)
    (l27_pre B MT XM_LIB RLO RHI tfib_K cx h i n now)).
{ intros W2 ly2 S2 regs2 mem2 md2 Hw2 HJ2 HP2 Hfr2 HK HBODY2.
  assert (Hfrs2 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfr2; exact Hfrs).
  assert (Hctx2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 (k + 1))
    by (split; [exact Hbase | split; [exact HJ2 | exact Hfrs2]]).
  pose proof (r27_EFB cx ly2 S2 W2 mem2 md2 (k + 1) HJ2) as EFB2.
  assert (HnE : forall a, d_inxb (dxb fr len) a -> exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + req_size m).
  { intros a (b & m & Hbm & Hr). exists b, m. split; [|exact Hr]. destruct Hblocks as (HP & _).
    eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. left. exact Hbm. }
  assert (HnEF : forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ d_inxb (dxb fr len) a).
  { intros a Ha Hx. destruct (HnE a Hx) as (b & m & Hbm & Hr).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W (ms_mem ms) md4 b m DFRAME_CLASS (c_fpos cx) HAR4 Hbm Hin3) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFB3 in Hd. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd. lia. }
  assert (HnES : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ d_inxb (dxb fr len) a).
  { intros a Ha Hx. destruct (HnE a Hx) as (b & m & Hbm & Hr).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR4 Hbm) as (_ & _ & _ & Happ & _).
    unfold shadow_addr, SHADOW_OFF in Ha.
    exact (fshadow_not_app (d_FB cx) 512 b (req_size m) a HFB1 ltac:(lia) Happ ltac:(lia) Hr). }
  assert (E516A : bv_unsigned (ew (d_env cx E vals) 516%nat) = d_FB cx).
  { rewrite r27_env_old by (unfold AT_FL; lia). unfold AT_F in E516v. rewrite E516v. unfold w64. apply unsigned_lit_small. lia. }
  assert (E529A : bv_unsigned (ew (d_env cx E vals) 529%nat) = shadow_addr (d_FB cx)).
  { rewrite r27_env_old by (unfold AT_FL; lia). unfold AT_SH in E529v. rewrite E529v. unfold w64. apply unsigned_lit_small.
    unfold shadow_addr, SHADOW_OFF. lia. }
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (firstn 4 (ss_mem ssx)) in
    pose proof (st_ok_pi_after_call_hi (fx := fq) 600 Ex ssx msx regs2 (mrestrict (w_H W2) mem2) rs 7476 HEI ltac:(lia) HS eq_refl
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(submem_tac) eq_refl HP2) as HS2
  end.
  lazymatch type of HS2 with Forall ?P ?rs -> _ => assert (HKEPT : Forall P rs) end.
  { apply Forall_cons.
    { eapply region_kept_stack_aj; [exact HK | exact HJ2 | exact USP2 | lia | unfold LLVMF_STK; lia | lia | lia | lia]. }
    apply Forall_cons.
    { eapply region_kept_stack_aj; [exact HK | exact HJ2 | exact E60A | lia | unfold LLVMF_STK; lia | lia | lia | lia]. }
    apply Forall_cons.
    { eapply region_kept_frame_aj; [exact HK | exact E516A | exact Hin3 | rewrite EFB3; lia
      | rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS) with 4096; lia | lia | intros a Ha; apply HnEF; lia]. }
    apply Forall_cons.
    { eapply region_kept_ownframe_aj; [exact HK | exact E529A | exact Hin3
      | right; rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia
      | intros a Ha; apply HnES; lia | intros a Ha; lia]. }
    apply Forall_nil. }
  specialize (HS2 HKEPT).
  change (mkst regs2 (Z_to_bv 64 (BASE + 7476)) (rd W2 mem2) (seg_rom SEGS))
    with (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 7476)) mem2 (seg_rom SEGS))) in HS2.
  norm_ss HS2.
  set (E2 := havoc (d_env cx E vals) 600 (map (getr regs2) CLOB)) in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
  assert (HdE2 : d_E cx E2) by (apply r27_dE_havoc; [exact HdEd | lia]).
  assert (EH : forall j : nat, (j < 600)%nat -> ew E2 j = ew (d_env cx E vals) j)
    by (intros j Hj; unfold E2; apply ew_havoc_old; exact Hj).
  assert (HFL2 : ew E2 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
    by (rewrite EH by (unfold AT_FL; lia); apply r27_env_fl).
  assert (E60B : bv_unsigned (ew E2 60%nat) = d_A cx) by (rewrite EH by lia; exact E60A).
  pose proof (st_ok_pi_region_nth E2 _ _ 1 _ HS2 eq_refl) as HR60b. cbn [ms_mem restrict mkst] in HR60b.
  assert (M184 : val_mem SEGS (rd W2 mem2) (d_A cx + 184) 8 h)
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 184 (SOff 563 0)); [exact HR60b | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E563 | exact Hhb]).
  assert (M120 : val_mem SEGS (rd W2 mem2) (d_A cx + 120) 8 (h + 440))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 120 (SOff 564 0)); [exact HR60b | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E564 | exact Hh440b]).
  assert (M136 : val_mem SEGS (rd W2 mem2) (d_A cx + 136) 8 0)
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 136 (SOff 565 0)); [exact HR60b | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E565 | lia]).
  assert (M376 : val_mem SEGS (rd W2 mem2) (d_A cx + 376) 8 (dnot (d_obj cx OG)))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 376 (SOff 566 0)); [exact HR60b | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E566 | apply Hdnotb]).
  assert (M280 : val_mem SEGS (rd W2 mem2) (d_A cx + 280) 8 (dnot (d_obj cx OT)))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 280 (SOff 567 0)); [exact HR60b | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E567 | apply Hdnotb]).
  assert (M232 : val_mem SEGS (rd W2 mem2) (d_A cx + 232) 8 (dnot (d_obj cx OO)))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 232 (SOff 568 0)); [exact HR60b | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E568 | apply Hdnotb]).
  assert (M264 : val_mem SEGS (rd W2 mem2) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 264 (SOff 569 0)); [exact HR60b | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E569 | apply Hdnotb]).
  destruct (LAND LAWS FFL fq cx h dsh_rec ly2 S2 W2 md2 (k + 1) E2 _
    (YK11.mkst (fx := fq) regs2 (Z_to_bv 64 (BASE + 7476)) mem2 (seg_rom SEGS)) Hctx2 HdE2 HFL2 HS2
    ltac:(vm_compute; reflexivity) M184 M120 M136 M376 M280 M232 M264) as [Hframe5 Hshadow5].
  pose proof (HBODY2 Hframe5 Hshadow5) as Hbody5.
  r27_ro_base HS2 60%nat.
  assert (HWR : forall o, 0 <= o < DFRAME_SH -> writable_at SEGS (rd W2 mem2) (shadow_addr (d_FB cx) + o)).
  { pose proof Hframe5 as (E5 & HE5 & HR5 & _).
    pose proof HE5 as (_ & _ & _ & _ & _ & E5SH).
    assert (Hb : bv_unsigned (ew E5 AT_SH) = shadow_addr (d_FB cx)).
    { rewrite E5SH. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
    apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail, Forall_inv in HR5.
    unfold region_ok in HR5. cbv zeta in HR5.
    destruct HR5 as (_ & _ & HW5 & _).
    intros o Ho. rewrite <- Hb. exact (HW5 o Ho). }
  assert (E529B : bv_unsigned (ew E2 529%nat) = shadow_addr (d_FB cx)) by (rewrite EH by lia; exact E529A).
  lazymatch type of HS2 with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
    pose proof (ast_ok_pi_set_region Ex ssx msx 3 r (set_window r 0 DFRAME_SH) HS2 ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity)
      (region_ok_rewindow _ Ex _ r 0 DFRAME_SH (st_ok_pi_region_nth Ex ssx msx 3 r HS2 ltac:(vm_compute; reflexivity))
        ltac:(intros o Ho; cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E529B; exact (HWR o Ho)))) as HS3
  end.
  clear HS2. norm_ss HS3.
  pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
  paj_run_to_sh RUNTO HS3 HJ2 L27_OFF.
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx))); [reflexivity | exact E529B | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFB2. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. unfold DFRAME_SH in Ha. lia. }
  set (md5 := with_vm_backing (m_vm_lazy md2) mat0 md2) in *.
  pose proof (st_ok_pi_restrict_mkst (w_H W2) _ _ ms0 HS3 eq_refl) as Hms5. cbn [ss_pc] in Hms5.
  assert (Hctx5 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 (ms_mem ms0) md5 (k + 1))
    by (split; [exact Hbase | split; [exact HJ2 | exact Hfrs2]]).
  pose proof (st_ok_pi_region_nth E2 _ _ 1 _ HS3 eq_refl) as HR60f. cbn [ms_mem restrict mkst] in HR60f.
  assert (F184 : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 184) 8 h)
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 184 (SOff 563 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E563 | exact Hhb]).
  assert (F120 : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 120) 8 (h + 440))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 120 (SOff 564 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E564 | exact Hh440b]).
  assert (F136 : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 136) 8 0)
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 136 (SOff 565 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E565 | lia]).
  assert (F376 : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 376) 8 (dnot (d_obj cx OG)))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 376 (SOff 566 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E566 | apply Hdnotb]).
  assert (F280 : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 280) 8 (dnot (d_obj cx OT)))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 280 (SOff 567 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E567 | apply Hdnotb]).
  assert (F232 : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 232) 8 (dnot (d_obj cx OO)))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 232 (SOff 568 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E568 | apply Hdnotb]).
  assert (F264 : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)))
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 264 (SOff 569 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E569 | apply Hdnotb]).
  assert (H208f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 208) 8 i)
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 208 (SOff 571 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E571 | unfold MAX_OPS in *; lia]).
  assert (H320f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 320) 8 now)
    by (eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 320 (SOff 574 0)); [exact HR60f | exact E60B | r27_in | apply r27_den0; rewrite EH by lia; exact E574 | lia]).
  assert (Hnmax : 0 <= n < 2 ^ 64) by lia.
  assert (H192f : val_mem SEGS (rd W2 (ms_mem ms0)) (d_A cx + 192) 8 n).
  { eapply (r27_slot _ _ 60%nat _ _ _ _ _ _ 192 (SAlu ALU_ADD (SOff 572 0) (SMd M_MUL (SOff 575 0) (SLit (-1)))));
      [exact HR60f | exact E60B | r27_in | | exact Hnmax].
    rewrite Hnnb. apply r27_sub_w; [rewrite EH by lia; exact E572 | rewrite EH by lia; exact E575]. }
  destruct (LAND LAWS FFL fq cx h dsh_loop ly2 S2 W2 md5 (k + 1) E2 _ ms0 Hctx5 HdE2 HFL2 HS3
    ltac:(vm_compute; reflexivity) F184 F120 F136 F376 F280 F232 F264) as [Hframe6 Hshadow6].
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ h HUNT_SIZE HAR4 Hhin) as (_ & _ & _ & Happh & _).
  assert (Hrq : 480 <= req_size HUNT_SIZE) by (vm_compute; intros Hq; discriminate Hq).
  assert (HnRD : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + DFRAME_SH -> ~ d_rdset B cx h a).
  { intros a Ha Hd. unfold shadow_addr, SHADOW_OFF, DFRAME_SH in Ha. unfold d_rdset in Hd.
    destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]]].
    - pose proof (r27_objr_frame cx OT a Hd) as Hf. unfold DFRAME_SIZE in Hf.
      exact (fshadow_not_app (d_FB cx) 384 (d_FB cx) 4096 a HFB1 ltac:(lia) HFBappx ltac:(lia) ltac:(lia)).
    - pose proof (r27_objr_frame cx OG a Hd) as Hf. unfold DFRAME_SIZE in Hf.
      exact (fshadow_not_app (d_FB cx) 384 (d_FB cx) 4096 a HFB1 ltac:(lia) HFBappx ltac:(lia) ltac:(lia)).
    - pose proof (r27_objr_frame cx OLOCK a Hd) as Hf. unfold DFRAME_SIZE in Hf.
      exact (fshadow_not_app (d_FB cx) 384 (d_FB cx) 4096 a HFB1 ltac:(lia) HFBappx ltac:(lia) ltac:(lia)).
    - pose proof (r27_objr_frame cx OOUR a Hd) as Hf. unfold DFRAME_SIZE in Hf.
      exact (fshadow_not_app (d_FB cx) 384 (d_FB cx) 4096 a HFB1 ltac:(lia) HFBappx ltac:(lia) ltac:(lia)).
    - unfold HUNT_SIZE in *.
      exact (fshadow_not_app (d_FB cx) 384 h (req_size 480) a HFB1 ltac:(lia) Happh ltac:(lia) ltac:(lia)).
    - destruct Hd as (HN0 & Hpa). destruct Hpn as [(HN1 & _) | (_ & Hpin)]; [lia|].
      destruct HPRE as (HAR0 & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hpin) as (_ & _ & _ & Happp & _).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq2).
      exact (fshadow_not_app (d_FB cx) 384 (c_p cx) (req_size (c_n cx)) a HFB1 ltac:(lia) Happp ltac:(lia) ltac:(lia)).
    - destruct Hd as (Hro & _). pose proof (pa_segs_low a (r27_roP_img a Hro)) as Hlow. unfold kLowMemEnd in Hlow.
      pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)). lia.
    - unfold FF_canary in Hd. lia. }
  assert (Hbody6 : d_body B cx h n [] dsh_loop ly2 S2 W2 (ms_mem ms0)).
  { apply (BRT cx h n n [] dsh_rec dsh_loop ly2 S2 W2 mem2 (ms_mem ms0) (d_A cx) (d_A cx)
      (fun a => shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + DFRAME_SH) Hbody5).
    - unfold LLVMF_STK in *; lia.
    - lia.
    - intros a Ha. right. exact (HnRD a Ha).
    - intros a Ha HnR. unfold DFRAME_SH in HnR. apply (aview_eq_of SEGS). apply HFr0. rewrite unsigned_lit_small by lia.
      intros (r & Hin & Hr).
      lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; first [lia | rewrite E529B in Hr; lia] |]).
      destruct Hin.
    - intros a _ Hp. exact (r27_pres_grows _ _ _ a HG0 Hp).
    - exact Hframe6.
    - exact Hshadow6.
    - lia. }
  assert (RF : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms0) r = getr regs r).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms0 r HS3), (r27_regs_ok cx E regs h i nb fr len now HdE HrL HAr2 r).
    cbv [In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [match goal with |- sv_denot _ ?a = sv_denot _ ?b =>
         let a' := eval vm_compute in a in let b' := eval vm_compute in b in change a with a'; change b with b' end;
       cbn [sv_denot]; rewrite EH by lia; reflexivity|]).
    destruct Hr. }
  assert (R21f : getr (ms_regs ms0) 21 = w64 i).
  { rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms0 21%bv HS3).
    match goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end.
    apply r27_den0. rewrite EH by lia. exact E571. }
  assert (R24f : getr (ms_regs ms0) 24 = w64 (d_cur cx n)).
  { rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms0 24%bv HS3).
    match goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end.
    replace (d_cur cx n) with (d_cur cx nb + len) by (unfold d_cur; lia).
    apply r27_add_w; [rewrite EH by lia; exact E570 | rewrite EH by lia; exact E575]. }
  assert (R22f : getr (ms_regs ms0) 22 = w64 1).
  { rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms0 22%bv HS3).
    match goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end.
    reflexivity. }
  apply SRr_ret.
  unfold l27_pre, d_at.
  exists fq, ly2, S2, (ms_regs ms0), (ms_mem ms0), md5, (k + 1), (acc + mo_free MT).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
  split; [unfold cfg_at, w64; rewrite Hms5 at 1; reflexivity|].
  split; [exact Hfrm0|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [exact Hfrs2|].
  split; [unfold EV_HEAD, EV_PRO, EV_ITER in *; lia|].
  split; [unfold EV_HEAD, EV_PRO, EV_ITER in *; lia|].
  split; [rewrite MT_TRIV; exact I|].
  split; [rewrite MT_TRIV in *; unfold ACC_HEAD, ACC_ITER, ACC_PRO in *; cbn [mo_malloc mo_free ameter_triv] in *; lia|].
  split; [lia|]. split; [lia|]. split; [exact Hnow|].
  split.
  { pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
    split; [|exact R22f].
    split; [unfold spZ in *; rewrite (RF 2%bv ltac:(cbv; tauto)); exact Hsp|].
    rewrite (RF 3%bv ltac:(cbv; tauto)), (RF 4%bv ltac:(cbv; tauto)), (RF 8%bv ltac:(cbv; tauto)), (RF 9%bv ltac:(cbv; tauto)),
      (RF 19%bv ltac:(cbv; tauto)), (RF 18%bv ltac:(cbv; tauto)), (RF 20%bv ltac:(cbv; tauto)), (RF 27%bv ltac:(cbv; tauto)).
    repeat split; assumption. }
  split; [exact R21f|]. split; [exact R24f|]. split; [exact (conj H208f H320f)|]. split; [exact H192f|]. exact Hbody6. }
rewrite Hms.
destruct (Z.eq_dec fr 0) as [Efr | Nfr].
- assert (Hdxb0 : dxb fr len = []) by (unfold dxb; rewrite Efr; reflexivity).
  assert (R10z : getr (ms_regs ms) 10 = w64 0) by (rewrite R10, Efr; reflexivity).
  eapply SRr_bind; [exact (aj_free_null_at (fx := fq) SEGS B LAWS pa_segs_low (pal_env B TL) ML (AFREE fq) W (ms_regs ms) (ms_mem ms)
    LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md4 k
    (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 7476)) ch HJ R10z Hsp' ltac:(lia) ltac:(lia) ltac:(unfold LLVMF_STK; lia) R3 R4 R1 Hraw Hev Hch Htr)|].
  intros W2 c2 Hw2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hperm & Hfr2 & HK).
  assert (HKc : acall_kept SEGS B ly3 S3 W (ms_mem ms) W2 mem2 (d_A cx - 16384) (d_A cx) (d_inxb (dxb fr len))).
  { eapply r27_kept_conv; [exact HK | lia | lia |]. intros a []. }
  apply (POST W2 ly2 S2 regs2 mem2 md2 Hw2 HJ2 HP2 Hfr2 HKc).
  intros Hframe5 Hshadow5.
  rewrite Hdxb0 in Hbody4, Hblocks.
  pose proof HK as (_ & K2 & K3 & K4 & _).
  pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & _ & _ & Hobj4 & _).
  assert (KB : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + req_size m ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros b m a Hbm Ha. replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hbm ltac:(lia)). intros []. }
  apply (BSTEP LAWS DRO DCAN cx h n [] [] dsh_rec dsh_rec ly3 S3 W (ms_mem ms) ly2 S2 W2 mem2 md2 (k + 1)
    T4 G4 Lk4 H4 Hbody4 (conj Hbase HJ2) (r27_blocks_perm cx h [] ly3 S3 ly2 S2 Hblocks Hperm)).
  + apply (r27_objs_kept cx h T4 G4 Lk4 H4 W (ms_mem ms) W2 mem2 Hobj4).
    intros a Ht.
    destruct Ht as [Ht|[Ht|[Ht|[Ht|Ht]]]];
      [ pose proof (r27_objr_frame cx OT a Ht) as Hf | pose proof (r27_objr_frame cx OG a Ht) as Hf
      | pose proof (r27_objr_frame cx OLOCK a Ht) as Hf | pose proof (r27_objr_frame cx OOUR a Ht) as Hf | ].
    1-4: apply (K4 DFRAME_CLASS (c_fpos cx) a Hin3); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFB3;
           change (fs_frame_bytes DFRAME_CLASS) with 4096; unfold DFRAME_SIZE in Hf; lia | intros []].
    apply (KB h HUNT_SIZE a Hhin). pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)) as (_ & Hrqh).
    unfold HUNT_SIZE in *. lia.
  + intros a HN0 Ha. destruct Hpn as [(HN1 & _) | (_ & Hpin)]; [lia|].
    assert (Hpin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { destruct Hblocks as (HP & _). eapply Permutation_in; [apply Permutation_sym; exact HP|]. right. exact Hpin. }
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq2).
    apply (KB _ _ a Hpin3). lia.
  + intros a Hro Ho He. apply (K3 a (r27_roP_img a Hro) Ho He).
  + exact Hframe5.
  + exact Hshadow5.
- assert (Hdxb : dxb fr len = [(fr, len)]) by (unfold dxb; rewrite (proj2 (Z.eqb_neq fr 0) Nfr); reflexivity).
  assert (Hin : In (fr, len) (ablocks B ly3 S3)).
  { destruct Hblocks as (HP & _). eapply Permutation_in; [apply Permutation_sym; exact HP|]. rewrite Hdxb. left. reflexivity. }
  assert (Hnent : ~ In (fr, len) (ablocks B (c_ly cx) (c_S cx))).
  { destruct Hblocks as (_ & HFb & _). rewrite Hdxb in HFb. inversion HFb as [|? ? _ HF2]. inversion HF2. assumption. }
  eapply SRr_bind; [exact (aj_free_at (fx := fq) SEGS B LAWS pa_segs_low (pal_env B TL) ML (AFREE fq) W (ms_regs ms) (ms_mem ms)
    LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md4 k fr len
    (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 7476)) ch HJ Hin R10 Hsp' ltac:(lia) ltac:(lia) ltac:(unfold LLVMF_STK; lia) R3 R4 R1 Hraw Hev Hch Htr
    (fun Hc => False_ind _ (Hnent Hc)))|].
  intros W2 c2 Hw2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Hs1 & Hs2) & Hfr2 & HK).
  assert (HKc : acall_kept SEGS B ly3 S3 W (ms_mem ms) W2 mem2 (d_A cx - 16384) (d_A cx) (d_inxb [(fr, len)])).
  { eapply r27_kept_conv; [exact HK | lia | lia |]. intros a Ha. exists fr, len. split; [left; reflexivity | exact Ha]. }
  apply (POST W2 ly2 S2 regs2 mem2 md2 Hw2 HJ2 HP2 Hfr2); [rewrite Hdxb; exact HKc|].
  intros Hframe5 Hshadow5. rewrite Hdxb in Hbody4.
  exact (BFREE LAWS DRO DCAN cx h n [] [] [(fr, len)] dsh_rec dsh_rec ly3 S3 W (ms_mem ms) md4 k ly2 S2 W2 mem2 md2 (k + 1)
    (d_A cx - 16384) (d_A cx) l1 l2 Hbody4 (conj Hbase HJ) (conj Hbase HJ2) ltac:(cbn; lia) ltac:(unfold LLVMF_STK; lia) ltac:(lia)
    Hs1 Hs2 HKc Hframe5 Hshadow5).
Qed.
End h.
End f.
End d.

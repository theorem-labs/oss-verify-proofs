(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v, with its numbers changed; 882 of its 1012 lines of code are new or changed and 662 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC81 YC85 YC88 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntRecCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition yc_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 27%nat => SOff AT_SH 0
  | _ => SOff (AT_X + r) 0
  end.
Definition yc_sr : list sv := map yc_x (seq 0 32).
Definition yc_acs : list YP09.chunk :=
  [YP09.mkChunk 184 (CVal 8 (SOff 563 0)); YP09.mkChunk 120 (CVal 8 (SOff 564 0));
   YP09.mkChunk 136 (CVal 8 (SOff 565 0)); YP09.mkChunk 376 (CVal 8 (SOff 566 0));
   YP09.mkChunk 280 (CVal 8 (SOff 567 0)); YP09.mkChunk 232 (CVal 8 (SOff 568 0));
   YP09.mkChunk 264 (CVal 8 (SOff 569 0)); YP09.mkChunk 208 (CVal 8 (SOff 570 0));
   YP09.mkChunk 320 (CVal 8 (SOff 571 0)); YP09.mkChunk 360 (CVal 8 (SOff 572 0));
   YP09.mkChunk 352 (CVal 8 (SOff 573 0)); YP09.mkChunk 408 (CVal 8 (SOff 574 0))].

Definition RA_CPY : Z := 3488.

Ltac yc_ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Ltac yc_in := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma yc_length_firstn : forall {X} (t : nat) (l : list X), length (firstn t l) = Nat.min t (length l).
Proof.
intros X t. induction t as [|t IH]; intros [|x l]; cbn [firstn length Nat.min]; try reflexivity.
rewrite IH. reflexivity.
Qed.
Lemma yc_length_skipn : forall {X} (s : nat) (l : list X), length (skipn s l) = (length l - s)%nat.
Proof.
intros X s. induction s as [|s IH]; intros [|x l]; cbn [skipn length Nat.sub]; try reflexivity.
apply IH.
Qed.
Lemma yc_nth_skipn : forall {X} (l : list X) (s k : nat) (d : X), nth k (skipn s l) d = nth (s + k) l d.
Proof.
intros X l. induction l as [|x l IH]; intros s k d.
- destruct s; destruct k; reflexivity.
- destruct s; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.
Lemma yc_nth_firstn : forall {X} (l : list X) (t k : nat) (d : X), (k < t)%nat -> nth k (firstn t l) d = nth k l d.
Proof.
intros X l. induction l as [|x l IH]; intros t k d Hk.
- destruct t; cbn [firstn]; reflexivity.
- destruct t; [lia|]. cbn [firstn]. destruct k; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition yc_ex (cx : dcx) (h i now op len : Z) : list word :=
  map (Z_to_bv 64)
    [h; h + 440; 0; dnot (d_obj cx OG); dnot (d_obj cx OT); dnot (d_obj cx OO); dnot (d_obj cx OUSED);
     i; now; op; (if op <? 128 then op else op - 256) mod 2 ^ 64; len].
Definition yc_vals (cx : dcx) (regs : bvmap 5 word) (h i now op len : Z) : list word :=
  map (fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ yc_ex cx h i now op len.

Lemma yc_env_fl : forall cx E vals,
  ew (d_env cx E vals) AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof.
intros cx E vals. unfold d_env. change AT_FL with (AT_FL + 0)%nat at 2.
rewrite (ew_havoc_new _ AT_FL _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma yc_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  ew (d_env cx E (map (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) ++ ex)) a = getr regs r.
Proof.
intros cx E regs ex r a ->.
pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite y_env_x by (rewrite length_app, length_map, length_seq; lia).
rewrite app_nth1 by (rewrite length_map, length_seq; lia).
rewrite (nth_indep _ _ ((fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) 0%nat))
  by (rewrite length_map, length_seq; lia).
pose proof (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat
  (Z.to_nat (bv_unsigned r))) as Hm.
cbv beta in Hm |- *. rewrite Hm, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia.
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma yc_env_ex : forall cx E regs ex j a, a = (AT_X + 32 + j)%nat -> (j < length ex)%nat ->
  ew (d_env cx E (map (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) ++ ex)) a =
  nth j ex (Z_to_bv 64 0).
Proof.
intros cx E regs ex j a -> Hj.
replace (AT_X + 32 + j)%nat with (AT_X + (32 + j))%nat by lia.
rewrite y_env_x by (rewrite length_app, length_map, length_seq; lia).
rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. replace (32 + j - 32)%nat with j by lia. reflexivity.
Qed.

Lemma yc_den0 : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> sv_denot E (SOff k 0) = Z_to_bv 64 v.
Proof. intros E k v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma yc_chunk : forall E m base off e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (base + off) 8 v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 e)).
Proof. intros E m base off e v He Hv Hm. eapply chunk_ok_val; [exact He | cbn; lia | cbn; lia | exact Hm]. Qed.

Lemma yc_slot : forall E m (nn : nat) b lo hi wlo whi cs off e v,
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) -> bv_unsigned (ew E nn) = b ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (b + off) 8 v.
Proof.
intros E m nn b lo hi wlo whi cs off e v HR Hb Hin He Hv. change 8%nat with (N.to_nat 8).
exact (field_of_region E m nn b cs lo hi wlo whi off 8%N e v HR Hb Hin He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Lemma yc_dE_havoc : forall cx E kk ws, d_E cx E -> (530 <= kk)%nat -> d_E cx (havoc E kk ws).
Proof.
intros cx E kk ws (EE & E32 & HEI & E60 & EF & ESH) Hk. unfold d_E.
rewrite !ew_havoc_old by (unfold AT_A, AT_F, AT_SH; lia).
split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
- intros nn r Hn. rewrite ew_havoc_old; [exact (EE nn r Hn)|]. pose proof (bv_unsigned_in_range _ r) as Hr.
  change (bv_modulus 5) with 32 in Hr. lia.
- apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia].
Qed.

Lemma yc_pres_grows : forall (H : word -> bool) m m' a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG (Hh & b & Hb). split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG.
rewrite Hh, Hb in HG. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.

Lemma yc_pi_of : forall (fq : YK11.FPState) E ss ms, st_ok (fx := fq) SEGS E ss ms ->
  st_ok_pi (fx := fq) SEGS VAL E (setpc ss (ss_pc ss - BASE)) ms.
Proof.
intros fq E ss ms HS. unfold st_ok_pi, abs_ss. destruct ss as [p0 r0 f0 m0 v0 g0]. unfold setpc in *. cbn in *.
replace (BASE + (p0 - BASE)) with p0 by lia. exact HS.
Qed.

Ltac yc_awr Ev cxv ly3v A60v A516v A529v EFBv :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end;
  eapply (y_awr Ev cxv ly3v);
  [ vm_compute; reflexivity | exact A60v | exact A516v | exact A529v
  | lia | unfold LLVMF_STK; lia | exact EFBv ].

Ltac yc_keep HFRx A60v A529v :=
  apply (aview_eq_of SEGS); apply HFRx; rewrite unsigned_lit_small by lia;
  intros (rz & Hinr & Hrr);
  lazymatch type of Hinr with
  | In _ ?rs => let rs' := eval vm_compute in rs in change (In rz rs') in Hinr end;
  cbn [In] in Hinr;
  repeat (destruct Hinr as [<- | Hinr];
    [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hrr;
      first [ lia | rewrite A60v in Hrr; lia | rewrite A529v in Hrr; lia ] |]);
  destruct Hinr.

Ltac yc_fld HRv A60v o a :=
  eapply (yc_slot _ _ 60%nat _ _ _ _ _ _ o (SOff a 0));
  [ exact HRv | exact A60v | yc_in | apply yc_den0; assumption | ].

Ltac yc_reg Wv HSv msv rr :=
  rewrite (st_ok_pi_restrict_reg (w_H Wv) _ _ msv rr HSv);
  match goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end;
  apply yc_den0; assumption.

Lemma yc_objr_frame : forall cx o a, d_objr cx o a -> d_FB cx <= a < d_FB cx + DFRAME_SIZE.
Proof. intros cx o a. unfold d_objr, d_obj, DFRAME_SIZE. destruct o; cbn [dobj_off dobj_size]; lia. Qed.
Lemma yc_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof. intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; assumption | exact (pa_relro_img a Hr)]. Qed.

Lemma yc_mbyte_move : forall (H : word -> bool) (m m' : word -> option byte) a a',
  aview SEGS H m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H m m' a a' E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb;
destruct (mbyte SEGS (mrestrict H m') a') as [b'|] eqn:Eb';
cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma yc_val1_move : forall (W : world SEGS) m m' a a' v,
  aview SEGS (w_H W) m' a' = aview SEGS (w_H W) m a ->
  val_mem SEGS (rd W m) a 1 v -> val_mem SEGS (rd W m') a' 1 v.
Proof.
intros W m m' a a' v HK HV k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
specialize (HV 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in HV. rewrite Z.add_0_r in HV.
rewrite (yc_mbyte_move (w_H W) m m' a a' HK). exact HV.
Qed.

Lemma yc_garr8_some : forall (W : world SEGS) m p (L : list Z) a,
  garr8 SEGS (rd W m) p L -> p <= a < p + Z.of_nat (length L) ->
  aview SEGS (w_H W) m a <> None.
Proof.
intros W m p L a HG Ha.
destruct (HG (Z.to_nat (a - p)) ltac:(lia)) as (HV & _).
specialize (HV 0%nat ltac:(lia)).
replace (p + Z.of_nat (Z.to_nat (a - p)) + Z.of_nat 0) with a in HV by lia.
unfold aview. rewrite HV. cbn [option_map]. discriminate.
Qed.

Lemma yc_frm_garr8 : forall (W : world SEGS) m m' (pl : list byte) p cn nb len fr,
  Z.of_nat (length pl) = cn -> 0 <= nb <= cn -> 0 <= len -> len <= nb ->
  garr8 SEGS (rd W m) p (map (fun b : byte => bv_unsigned b) pl) ->
  (forall j, 0 <= j < len -> aview SEGS (w_H W) m' (fr + j) = aview SEGS (w_H W) m (p + (cn - nb) + j)) ->
  garr8 SEGS (rd W m') fr
    (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (skipn (length pl - Z.to_nat nb) pl))).
Proof.
intros W m m' pl p cn nb len fr Hlen Hnb Hlen0 Hlennb HG HK.
set (s := (length pl - Z.to_nat nb)%nat) in *.
assert (Hs : Z.of_nat s = cn - nb) by (unfold s; lia).
intros j Hj.
rewrite length_map, yc_length_firstn, yc_length_skipn in Hj.
assert (Hjl : (j < Z.to_nat len)%nat) by lia.
assert (Hsj : (s + j < length pl)%nat) by lia.
assert (Hnthsrc : nth j (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (skipn s pl))) 0 =
                  nth (s + j)%nat (map (fun b : byte => bv_unsigned b) pl) 0).
{ rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map, yc_length_firstn, yc_length_skipn; lia).
  rewrite (nth_indep (map (fun b : byte => bv_unsigned b) pl) 0 (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map; lia).
  rewrite (map_nth (fun b : byte => bv_unsigned b)), (map_nth (fun b : byte => bv_unsigned b)).
  f_equal. rewrite yc_nth_firstn by lia. apply yc_nth_skipn. }
destruct (HG (s + j)%nat ltac:(rewrite length_map; lia)) as (HV & Hr).
rewrite Hnthsrc. split; [|exact Hr].
apply (yc_val1_move W m m' (p + Z.of_nat (s + j)) (fr + Z.of_nat j)); [|exact HV].
replace (p + Z.of_nat (s + j)%nat) with (p + (cn - nb) + Z.of_nat j) by (rewrite Nat2Z.inj_add, Hs; lia).
apply HK. lia.
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
Hypothesis AMEMCPY : forall fq : YK11.FPState,
  aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.

Lemma yc_EFB : forall cx ly' S' W' m' md' k,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly' S' W' m' md' k ->
  frame_addr ly' DFRAME_CLASS (c_fpos cx) = d_FB cx.
Proof.
intros cx ly' S' W' m' md' k HJ. pose proof HJ as (_ & Hly & _).
unfold frame_addr, d_FB, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

Lemma yc_A_range : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 mem3 md3 k ->
  alloc_ceiling + LLVMF_STK <= d_S cx <= 2 ^ 47 /\ d_S cx mod 16 = 0 /\
  d_S cx - 592 <= d_A cx <= d_S cx - 576 /\ d_A cx mod 32 = 0.
Proof.
intros cx ly3 S3 W3 mem3 md3 k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as M.
unfold MFRAME in *. split; [lia|]. split; [exact Hal|]. split; [|rewrite Z.mul_comm; apply Z_mod_mult].
assert ((d_S cx - 576) mod 32 = 0 \/ (d_S cx - 576) mod 32 = 16).
{ assert (E16 : (d_S cx - 576) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  pose proof (Z.div_mod (d_S cx - 576) 16 ltac:(lia)). lia. }
lia.
Qed.

Lemma yc_regs_ok : forall cx E regs h i now op len, d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (yc_vals cx regs h i now op len)) yc_sr regs.
Proof.
intros cx E regs h i now op len HE HL HA.
pose proof (y_E_env cx E (yc_vals cx regs h i now op len) HE) as HE'.
destruct HE' as (HER & H32 & _ & HA60 & HAF & HASH).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx))
  by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew (d_env cx E (yc_vals cx regs h i now op len)) 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_SH with 529%nat in HASH.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
unfold yc_vals in *.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?rr) =>
       let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
all: cbv [AT_STK AT_A AT_SH].
all: cbn [sv_denot].
all: first
  [ rewrite getr_zero; reflexivity
  | rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
  | rewrite HS2, Z.add_0_r, Z_to_bv_bv_unsigned; exact H8
  | rewrite HASH, Z.add_0_r, Z_to_bv_bv_unsigned; exact H27
  | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
      rewrite (yc_env_reg cx E regs (yc_ex cx h i now op len) x a eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Lemma yc_not_rdset : forall cx h,
  4096 <= d_FB cx -> d_FB cx + 4096 <= alloc_ceiling ->
  in_app (d_FB cx) 4096 -> in_app h (req_size HUNT_SIZE) ->
  (0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))) ->
  forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + DFRAME_SH -> ~ d_rdset B cx h a.
Proof.
intros cx h HFB1 HFBc HFBapp Happh Happp a Ha Hd.
pose proof alloc_ceiling_val as Hac.
unfold shadow_addr, SHADOW_OFF, DFRAME_SH in Ha. unfold d_rdset in Hd.
destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]]].
- pose proof (yc_objr_frame cx OT a Hd) as Hf. unfold DFRAME_SIZE in Hf.
  exact (fshadow_not_app (d_FB cx) 384 (d_FB cx) 4096 a HFB1 ltac:(lia) HFBapp ltac:(lia) ltac:(lia)).
- pose proof (yc_objr_frame cx OG a Hd) as Hf. unfold DFRAME_SIZE in Hf.
  exact (fshadow_not_app (d_FB cx) 384 (d_FB cx) 4096 a HFB1 ltac:(lia) HFBapp ltac:(lia) ltac:(lia)).
- pose proof (yc_objr_frame cx OLOCK a Hd) as Hf. unfold DFRAME_SIZE in Hf.
  exact (fshadow_not_app (d_FB cx) 384 (d_FB cx) 4096 a HFB1 ltac:(lia) HFBapp ltac:(lia) ltac:(lia)).
- pose proof (yc_objr_frame cx OOUR a Hd) as Hf. unfold DFRAME_SIZE in Hf.
  exact (fshadow_not_app (d_FB cx) 384 (d_FB cx) 4096 a HFB1 ltac:(lia) HFBapp ltac:(lia) ltac:(lia)).
- pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)) as (_ & Hrq). unfold HUNT_SIZE in *.
  exact (fshadow_not_app (d_FB cx) 384 h (req_size 480) a HFB1 ltac:(lia) Happh ltac:(lia) ltac:(lia)).
- destruct Hd as (HN0 & Hpa). pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq2).
  exact (fshadow_not_app (d_FB cx) 384 (c_p cx) (req_size (c_n cx)) a HFB1 ltac:(lia) (Happp HN0)
    ltac:(lia) ltac:(lia)).
- destruct Hd as (Hro & _). pose proof (pa_segs_low a (yc_roP_img a Hro)) as Hlow. unfold kLowMemEnd in Hlow.
  pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)). lia.
- unfold FF_canary in Hd. pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma yc_mid_of : forall (fq : YK11.FPState) cx h i n now op fr len nb ly3 S3 (W : world SEGS) md k acc
  (E' : env) ss ms,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 -> 0 <= op < 256 -> op mod 4 <> 3 ->
  4096 <= fr -> 0 <= len <= REC_MAX -> len <= nb -> nb <= c_n cx -> nb - len <= Z.max 0 (c_n cx - 7) ->
  st_ok_pi (fx := fq) SEGS VAL E' ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = MID_OFF ->
  d_rL B cx (ms_regs ms) ->
  getr (ms_regs ms) 22 = w64 1 -> getr (ms_regs ms) 21 = w64 i -> getr (ms_regs ms) 26 = w64 now ->
  getr (ms_regs ms) 23 = w64 (op mod 4) -> getr (ms_regs ms) 12 = w64 len ->
  getr (ms_regs ms) 24 = w64 nb -> getr (ms_regs ms) 25 = w64 (d_cur cx nb) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 208) 8 i ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 320) 8 now ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 360) 8 op ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 352) 8 (if op <? 128 then op else op - 256) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 200) 8 (d_cur cx nb) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 328) 8 nb ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 fr ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 408) 8 len ->
  garr8 SEGS (rd W (ms_mem ms)) fr
    (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) ->
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) ->
  yr_mid B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W (mkCfg ms md).
Proof.
intros fq cx h i n now op fr len nb ly3 S3 W md k acc E' ss ms
  HFQ Hbase HJ Hfrs Hk Hnev Hmo Hacc Ri Rn Rnow Rop Ropm Rfr Rlen Rlennb Rnbcn Rnbmax
  HS Hrv Hpc HrL H22 H21 H26 H23 H12 H24 H25 V208 V320 V360 V352 V200 V328 V368 V408 HGA Hbody.
pose proof (st_ok_pi_restrict_mkst (w_H W) E' ss ms HS Hrv) as Hms.
unfold yr_mid, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md, k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFQ|].
split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Ri|]. split; [exact Rn|]. split; [exact Rnow|].
split; [exact HrL|].
split; [repeat split; assumption|].
split.
- split; [exact Rop|]. split; [exact Ropm|]. split; [exact Rfr|].
  split; [split; [exact Rlen | split; [intros Hz; lia | split; [exact Rnbcn | exact HGA]]]|].
  split; [exact (conj V200 (conj V328 (conj V368 V408)))|].
  split; [exact (conj V360 V352)|].
  split; [exact Rlennb | exact Rnbmax].
- split; [exact (conj V208 V320) | exact Hbody].
Qed.

Theorem pb_rec_copy : yr_s2b_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold yr_s2b_stmt.
intros cx h i n now op fr len W c Hpre.
destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFQ & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Ri & Rn & Rnow & Rop & Ropm & Rfr & Rlen & Rlennb & Rnbcn & Rnbmax &
  HrL & H22 & H21 & H26 & H23 & H10 & H24 & H25 & V408 & Hsp0 & Hspop & Hbody).
set (nb := rec_rem n) in *.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (proj1 HJ) as HAR3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin3 : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof (yc_EFB cx ly3 S3 W mem3 md3 k HJ) as EFB3.
destruct (frames_bounds _ _ LAWS ly3 S3 W mem3 md3 DFRAME_CLASS (c_fpos cx) HAR3 Hin3) as (HFB1 & HFBc & HFBapp).
rewrite EFB3 in HFB1, HFBc, HFBapp.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HFB1, HFBc, HFBapp.
destruct (yc_A_range cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (RA : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in *; lia).
assert (RS : 0 <= d_S cx < 2 ^ 64) by (unfold LLVMF_STK in *; lia).
assert (RFB : 0 <= d_FB cx < 2 ^ 64) by lia.
assert (RSH : 0 <= shadow_addr (d_FB cx) < 2 ^ 64)
  by (unfold shadow_addr; apply y_shaddr_range; lia).
pose proof Hbase as ((HPRE & _ & _ & _ & HINdisj & _) & _).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo &
  Hcan & Hstk & Hawr).
pose proof Hframe as (E & HdE & HRGf & Hfl & Hh184 & Hh120 & Hh136 & Hh376 & Hh280 & Hh232 & Hh264).
pose proof HdE as (EE & E32 & HEI0 & E60v & E516v & E529v).
unfold AT_A, AT_F, AT_SH in E60v, E516v, E529v.
pose proof Hgeo as (Hg1 & Hg2 & Hg3 & Hg4 & Hgce & Hglen & Hg7 & Hg8).
pose proof Hinput as (Rnm & HINPg & HINPo).
assert (Rcn : 0 <= c_n cx < 2 ^ 26)
  by (destruct HINdisj as [(Hn0 & _) | (Hr & _)]; lia).
assert (Hnb0 : 0 <= nb) by (unfold nb, rec_rem, rec_take; lia).
assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ destruct Hblocks as (HP & _). eapply Permutation_in; [apply Permutation_sym; exact HP|].
  apply in_or_app. right. left. reflexivity. }
assert (Hfrin : In (fr, len) (ablocks B ly3 S3)).
{ destruct Hblocks as (HP & _). eapply Permutation_in; [apply Permutation_sym; exact HP|].
  apply in_or_app. left. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ h HUNT_SIZE HAR3 Hhin) as (_ & Hh4096 & Hhce & Happh & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fr len HAR3 Hfrin) as (_ & Hfr4096 & Hfrce & Happfr & _).
pose proof (req_size_pos len ltac:(lia)) as (Hrql1 & Hrql2).
assert (Happp : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. destruct HINdisj as [(Hn0 & _) | (Hr & Hpin)]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) (proj1 HPRE) Hpin) as (_ & _ & _ & Hap & _).
  exact Hap. }
pose proof (yc_not_rdset cx h HFB1 HFBc HFBapp Happh Happp) as HnRD.
assert (Hdcur : 0 <= d_cur cx nb < 2 ^ 64).
{ unfold d_cur. destruct HINdisj as [(Hn0 & Hp0) | (Hr & Hpin)].
  - rewrite Hn0, Hp0 in *. unfold A_EMPTY in *. unfold nb, rec_rem, rec_take in *. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_p cx) (c_n cx) (proj1 HPRE) Hpin) as (_ & Hp4 & Hpce & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq). lia. }
assert (Hdnotb : forall o, 0 <= dnot (d_obj cx o) < 2 ^ 64).
{ intros o. unfold dnot, d_obj.
  assert (Hoff2 : 0 <= dobj_off o <= 2992) by (destruct o; cbn [dobj_off]; lia). lia. }
assert (Hhb : 0 <= h < 2 ^ 64) by (unfold HUNT_SIZE in *; lia).
assert (Hh440b : 0 <= h + 440 < 2 ^ 64) by (unfold HUNT_SIZE in *; lia).
assert (Hsopb : 0 <= (if op <? 128 then op else op - 256) mod 2 ^ 64 < 2 ^ 64)
  by (apply Z.mod_pos_bound; lia).
set (vals := yc_vals cx regs h i now op len) in *.
pose proof (y_E_env cx E vals HdE) as HdEd.
pose proof HdEd as (_ & _ & HEI & _).
set (Ed := d_env cx E vals) in *.
assert (AO : forall q, (q < AT_FL)%nat -> ew Ed q = ew E q) by (intros q Hq; apply y_env_old; exact Hq).
assert (EXx : forall j q, q = (AT_X + 32 + j)%nat -> (j < 12)%nat ->
  ew Ed q = nth j (yc_ex cx h i now op len) (Z_to_bv 64 0)).
{ intros j q Hq Hj. unfold Ed, vals, yc_vals. apply (yc_env_ex cx E regs _ j q Hq).
  unfold yc_ex. cbn [length map]. lia. }
assert (E563 : ew Ed 563 = Z_to_bv 64 h)
  by (rewrite (EXx 0%nat 563%nat eq_refl ltac:(lia)); reflexivity).
assert (E564 : ew Ed 564 = Z_to_bv 64 (h + 440))
  by (rewrite (EXx 1%nat 564%nat eq_refl ltac:(lia)); reflexivity).
assert (E565 : ew Ed 565 = Z_to_bv 64 0)
  by (rewrite (EXx 2%nat 565%nat eq_refl ltac:(lia)); reflexivity).
assert (E566 : ew Ed 566 = Z_to_bv 64 (dnot (d_obj cx OG)))
  by (rewrite (EXx 3%nat 566%nat eq_refl ltac:(lia)); reflexivity).
assert (E567 : ew Ed 567 = Z_to_bv 64 (dnot (d_obj cx OT)))
  by (rewrite (EXx 4%nat 567%nat eq_refl ltac:(lia)); reflexivity).
assert (E568 : ew Ed 568 = Z_to_bv 64 (dnot (d_obj cx OO)))
  by (rewrite (EXx 5%nat 568%nat eq_refl ltac:(lia)); reflexivity).
assert (E569 : ew Ed 569 = Z_to_bv 64 (dnot (d_obj cx OUSED)))
  by (rewrite (EXx 6%nat 569%nat eq_refl ltac:(lia)); reflexivity).
assert (E570 : ew Ed 570 = Z_to_bv 64 i)
  by (rewrite (EXx 7%nat 570%nat eq_refl ltac:(lia)); reflexivity).
assert (E571 : ew Ed 571 = Z_to_bv 64 now)
  by (rewrite (EXx 8%nat 571%nat eq_refl ltac:(lia)); reflexivity).
assert (E572 : ew Ed 572 = Z_to_bv 64 op)
  by (rewrite (EXx 9%nat 572%nat eq_refl ltac:(lia)); reflexivity).
assert (E573 : ew Ed 573 = Z_to_bv 64 ((if op <? 128 then op else op - 256) mod 2 ^ 64))
  by (rewrite (EXx 10%nat 573%nat eq_refl ltac:(lia)); reflexivity).
assert (E574 : ew Ed 574 = Z_to_bv 64 len)
  by (rewrite (EXx 11%nat 574%nat eq_refl ltac:(lia)); reflexivity).
assert (ERg : forall (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat -> ew Ed a = getr regs r).
{ intros r a Ha. unfold Ed, vals, yc_vals. exact (yc_env_reg cx E regs _ r a Ha). }
assert (E541 : ew Ed 541 = Z_to_bv 64 fr)
  by (rewrite (ERg 10%bv 541%nat eq_refl), H10; reflexivity).
assert (E555 : ew Ed 555 = Z_to_bv 64 nb)
  by (rewrite (ERg 24%bv 555%nat eq_refl), H24; reflexivity).
assert (E556 : ew Ed 556 = Z_to_bv 64 (d_cur cx nb))
  by (rewrite (ERg 25%bv 556%nat eq_refl), H25; reflexivity).
assert (E552 : ew Ed 552 = Z_to_bv 64 i)
  by (rewrite (ERg 21%bv 552%nat eq_refl), H21; reflexivity).
assert (E553 : ew Ed 553 = Z_to_bv 64 1)
  by (rewrite (ERg 22%bv 553%nat eq_refl), H22; reflexivity).
assert (E554 : ew Ed 554 = Z_to_bv 64 (op mod 4))
  by (rewrite (ERg 23%bv 554%nat eq_refl), H23; reflexivity).
assert (E557 : ew Ed 557 = Z_to_bv 64 now)
  by (rewrite (ERg 26%bv 557%nat eq_refl), H26; reflexivity).
pose proof HrL as (Hsp & Hgp & Htp & Hr8 & Hr9 & Hr19 & Hr18 & Hr20 & Hr27).
pose proof Hsp0 as (V208 & V320). pose proof Hspop as (V360 & V352).
assert (HAC : Forall (YP09.chunk_ok SEGS Ed (rd W mem3) (d_A cx)) yc_acs).
{ unfold yc_acs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (yc_chunk _ _ _ _ _ h); [apply yc_den0; exact E563 | exact Hhb | exact Hh184].
  - apply (yc_chunk _ _ _ _ _ (h + 440)); [apply yc_den0; exact E564 | exact Hh440b | exact Hh120].
  - apply (yc_chunk _ _ _ _ _ 0); [apply yc_den0; exact E565 | lia | exact Hh136].
  - apply (yc_chunk _ _ _ _ _ (dnot (d_obj cx OG))); [apply yc_den0; exact E566 | apply Hdnotb | exact Hh376].
  - apply (yc_chunk _ _ _ _ _ (dnot (d_obj cx OT))); [apply yc_den0; exact E567 | apply Hdnotb | exact Hh280].
  - apply (yc_chunk _ _ _ _ _ (dnot (d_obj cx OO))); [apply yc_den0; exact E568 | apply Hdnotb | exact Hh232].
  - apply (yc_chunk _ _ _ _ _ (dnot (d_obj cx OUSED))); [apply yc_den0; exact E569 | apply Hdnotb | exact Hh264].
  - apply (yc_chunk _ _ _ _ _ i); [apply yc_den0; exact E570 | unfold MAX_OPS in *; lia | exact V208].
  - apply (yc_chunk _ _ _ _ _ now); [apply yc_den0; exact E571 | lia | exact V320].
  - apply (yc_chunk _ _ _ _ _ op); [apply yc_den0; exact E572 | lia | exact V360].
  - apply (yc_chunk _ _ _ _ _ ((if op <? 128 then op else op - 256) mod 2 ^ 64));
      [apply yc_den0; exact E573 | exact Hsopb | apply y_val_mem_mod64; exact V352].
  - apply (yc_chunk _ _ _ _ _ len); [apply yc_den0; exact E574 | unfold REC_MAX in *; lia | exact V408]. }
pose proof (SEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E C2_OFF yc_sr vals yc_acs [] []
  (d_facts [] []) HC HdE HRGf Hfl (yc_regs_ok cx E regs h i now op len HdE HrL RA)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HC HdE I I)
  HAC (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS. fold Ed in HS.
yc_ro_base HS 516%nat.
assert (A60 : bv_unsigned (ew Ed 60) = d_A cx)
  by (rewrite (AO 60%nat ltac:(unfold AT_FL; lia)), E60v; unfold w64; apply unsigned_lit_small; exact RA).
assert (A516 : bv_unsigned (ew Ed 516) = d_FB cx)
  by (rewrite (AO 516%nat ltac:(unfold AT_FL; lia)), E516v; unfold w64; apply unsigned_lit_small; exact RFB).
assert (A529 : bv_unsigned (ew Ed 529) = shadow_addr (d_FB cx))
  by (rewrite (AO 529%nat ltac:(unfold AT_FL; lia)), E529v; unfold w64; apply unsigned_lit_small; exact RSH).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNC.
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + C2_OFF)) with (Z_to_bv 64 (BASE + C2_OFF)).
assert (Hdxb : dxb fr len = [(fr, len)])
  by (unfold dxb; rewrite (proj2 (Z.eqb_neq fr 0) ltac:(lia)); reflexivity).
assert (Hoffr : off_img fr (req_size len)).
{ destruct Hblocks as (_ & _ & _ & HFo).
  pose proof (proj1 (Forall_forall _ _) HFo (fr, len) ltac:(right; left; reflexivity)) as Hx.
  cbn [fst snd] in Hx. exact Hx. }
assert (Hnotbase : ~ In (fr, len) (ablocks B (c_ly cx) (c_S cx))).
{ destruct Hblocks as (_ & HFb & _).
  exact (proj1 (Forall_forall _ _) HFb (fr, len) ltac:(right; left; reflexivity)). }
assert (Hpin3 : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ intros Hc. destruct HINdisj as [(Hn0 & _) | (Hr & Hpin)]; [lia|].
  destruct Hblocks as (HP & _). eapply Permutation_in; [apply Permutation_sym; exact HP|].
  cbn [app]. right. right. exact Hpin. }
assert (HnRDfr : forall a, fr <= a < fr + len -> ~ d_rdset B cx h a).
{ intros a Ha Hd.
  assert (Hsepf : fr + req_size len <= d_FB cx \/ d_FB cx + 4096 <= fr).
  { pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 fr len DFRAME_CLASS (c_fpos cx)
      HAR3 Hfrin Hin3) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite EFB3 in Hz.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hz. lia. }
  assert (Hseph : fr + req_size len <= h \/ h + req_size HUNT_SIZE <= fr).
  { pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W mem3 md3 (fr, len) (h, HUNT_SIZE)
      (ablocks B (c_ly cx) (c_S cx)) HAR3
      ltac:(destruct Hblocks as (HP & _); cbn [app] in HP; exact HP)) as Hz.
    unfold zdisjoint, block_rng in Hz. cbn [fst snd] in Hz. lia. }
  unfold d_rdset in Hd.
  destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]]].
  - pose proof (yc_objr_frame cx OT a Hd). unfold DFRAME_SIZE in *. lia.
  - pose proof (yc_objr_frame cx OG a Hd). unfold DFRAME_SIZE in *. lia.
  - pose proof (yc_objr_frame cx OLOCK a Hd). unfold DFRAME_SIZE in *. lia.
  - pose proof (yc_objr_frame cx OOUR a Hd). unfold DFRAME_SIZE in *. lia.
  - pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)) as (_ & Hq).
    unfold HUNT_SIZE in *. lia.
  - destruct Hd as (HN0 & Hpa).
    assert (Hne : (fr, len) <> (c_p cx, c_n cx)).
    { intros Heq. apply Hnotbase. rewrite Heq.
      destruct HINdisj as [(Hn0 & _) | (Hr & Hpin)]; [lia | exact Hpin]. }
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W mem3 md3 fr len (c_p cx) (c_n cx)
      HAR3 Hfrin (Hpin3 HN0) Hne) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz.
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq2). lia.
  - destruct Hd as (Hro & _). pose proof (pa_img_range a (yc_roP_img a Hro)) as Hri.
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoffr.
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hri. lia.
  - pose proof Hcan as (_ & _ & Hcimg). pose proof (pa_img_range a (Hcimg a Hd)) as Hri.
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoffr.
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hri. lia. }
assert (HnRDsh : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 ->
  ~ d_rdset B cx h a) by (intros a Ha; apply HnRD; unfold DFRAME_SH; lia).
assert (HnotA : forall a, fr <= a < fr + len -> ~ (d_A cx - 4096 <= a < d_A cx + 472)).
{ intros a Ha. unfold LLVMF_STK in Hgce. lia. }
assert (HnotAp : forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx ->
  ~ (d_A cx - 4096 <= a < d_A cx + 472)).
{ intros a Hc Ha. destruct (Hg8 Hc) as (Hp0 & Hpce & _). unfold LLVMF_STK in Hgce. lia. }
assert (HnotShp : forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384)).
{ intros a Hc Ha Hsh. unfold shadow_addr, SHADOW_OFF in Hsh.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq2).
  exact (fshadow_not_app (d_FB cx) 384 (c_p cx) (req_size (c_n cx)) a HFB1 ltac:(lia) (Happp Hc)
    ltac:(lia) ltac:(lia)). }
assert (HnotShfr : forall a, fr <= a < fr + len ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384)).
{ intros a Ha Hsh. unfold shadow_addr, SHADOW_OFF in Hsh.
  exact (fshadow_not_app (d_FB cx) 384 fr (req_size len) a HFB1 ltac:(lia) Happfr
    ltac:(lia) ltac:(lia)). }
paj_run_to_sh RUNTO HS HJ 3452.
{ yc_awr Ed cx ly3 A60 A516 A529 EFB3. }
psrr_branch_pi RUNP BR HS.
- rewrite branch_eq_U, (U_atom Ed 574%nat len E574 ltac:(unfold REC_MAX in *; lia)),
    (U_lit Ed 0 ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc.
  paj_run_to_sh RUNTO HS HJ MID_OFF.
  { yc_awr Ed cx ly3 A60 A516 A529 EFB3. }
  set (md5 := with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat md3)) mat0
    (with_vm_backing (m_vm_lazy md3) mat md3)) in *.
  assert (Hctx5 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms0) md5 k)
    by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
  pose proof (st_ok_pi_region_nth Ed _ _ 1 _ HS eq_refl) as HR60f.
  cbn [ms_mem restrict mkst] in HR60f.
  assert (F184 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 184) 8 h)
    by (yc_fld HR60f A60 184 563%nat; exact Hhb).
  assert (F120 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 120) 8 (h + 440))
    by (yc_fld HR60f A60 120 564%nat; exact Hh440b).
  assert (F136 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 136) 8 0)
    by (yc_fld HR60f A60 136 565%nat; lia).
  assert (F376 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 376) 8 (dnot (d_obj cx OG)))
    by (yc_fld HR60f A60 376 566%nat; apply Hdnotb).
  assert (F280 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 280) 8 (dnot (d_obj cx OT)))
    by (yc_fld HR60f A60 280 567%nat; apply Hdnotb).
  assert (F232 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 232) 8 (dnot (d_obj cx OO)))
    by (yc_fld HR60f A60 232 568%nat; apply Hdnotb).
  assert (F264 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)))
    by (yc_fld HR60f A60 264 569%nat; apply Hdnotb).
  assert (F208 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 208) 8 i)
    by (yc_fld HR60f A60 208 570%nat; unfold MAX_OPS in *; lia).
  assert (F320 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 320) 8 now)
    by (yc_fld HR60f A60 320 571%nat; lia).
  assert (F360 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 360) 8 op)
    by (yc_fld HR60f A60 360 572%nat; lia).
  assert (F352 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 352) 8
    ((if op <? 128 then op else op - 256) mod 2 ^ 64))
    by (yc_fld HR60f A60 352 573%nat; exact Hsopb).
  assert (F408 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 408) 8 len)
    by (yc_fld HR60f A60 408 574%nat; unfold REC_MAX in *; lia).
  assert (F200 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 200) 8 (d_cur cx nb))
    by (yc_fld HR60f A60 200 556%nat; exact Hdcur).
  assert (F328 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 328) 8 nb)
    by (yc_fld HR60f A60 328 555%nat; lia).
  assert (F368 : val_mem SEGS (rd W (ms_mem ms0)) (d_A cx + 368) 8 fr)
    by (yc_fld HR60f A60 368 541%nat; pose proof alloc_ceiling_val; lia).
  destruct (LAND LAWS FFL fq cx h dsh_rec ly3 S3 W md5 k Ed _ ms0 Hctx5 HdEd (yc_env_fl cx E vals) HS
    ltac:(vm_compute; reflexivity) F184 F120 F136 F376 F280 F232 F264) as [Hframe6 Hshadow6].
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((d_A cx - 4096 <= a < d_A cx + 472) \/ (fr <= a < fr + len) \/
       (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384)) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha HnR.
    assert (HA1 : ~ (d_A cx - 4096 <= a < d_A cx + 472)) by tauto.
    assert (HA3 : ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384)) by tauto.
    transitivity (aview SEGS (w_H W) (ms_mem ms) a);
      [yc_keep HFr0 A60 A529 | yc_keep HFr A60 A529]. }
  assert (PRES : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms0) a).
  { intros a Hp. exact (yc_pres_grows _ _ _ a HG0 (yc_pres_grows _ _ _ a HG Hp)). }
  assert (Hbodyf : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms0)).
  { rewrite Hdxb.
    apply (BRT cx h n n [(fr, len)] dsh_loop dsh_rec ly3 S3 W mem3 (ms_mem ms0)
      (d_A cx - 4096) (d_A cx + 472)
      (fun a => (d_A cx - 4096 <= a < d_A cx + 472) \/ (fr <= a < fr + len) \/
                (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384)) Hbody);
      [ unfold LLVMF_STK; lia | lia
      | intros a [Ha | [Ha | Ha]];
        [left; exact Ha | right; exact (HnRDfr a Ha) | right; exact (HnRDsh a Ha)]
      | exact KEEP | intros a _ Hp; exact (PRES a Hp) | exact Hframe6 | exact Hshadow6 | lia ]. }
  assert (HGA : garr8 SEGS (rd W (ms_mem ms0)) fr
    (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))).
  { replace (Z.to_nat len) with 0%nat by lia. cbn [firstn map]. apply garr8_nil. }
  assert (RF : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
    getr (ms_regs ms0) r = getr regs r).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms0 r HS),
      (yc_regs_ok cx E regs h i now op len HdE HrL RA r).
    cbv [In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [match goal with |- sv_denot _ ?a = sv_denot _ ?b =>
         let a' := eval vm_compute in a in let b' := eval vm_compute in b in
         change a with a'; change b with b' end; reflexivity|]).
    destruct Hr. }
  assert (HrLf : d_rL B cx (ms_regs ms0)).
  { unfold d_rL.
    split; [unfold spZ in *; rewrite (RF 2%bv ltac:(cbv; tauto)); exact Hsp|].
    rewrite (RF 3%bv ltac:(cbv; tauto)), (RF 4%bv ltac:(cbv; tauto)), (RF 8%bv ltac:(cbv; tauto)),
      (RF 9%bv ltac:(cbv; tauto)), (RF 19%bv ltac:(cbv; tauto)), (RF 18%bv ltac:(cbv; tauto)),
      (RF 20%bv ltac:(cbv; tauto)), (RF 27%bv ltac:(cbv; tauto)).
    repeat split; assumption. }
  assert (R22f : getr (ms_regs ms0) 22 = w64 1) by (yc_reg W HS ms0 (22%bv : bv 5)).
  assert (R21f : getr (ms_regs ms0) 21 = w64 i) by (yc_reg W HS ms0 (21%bv : bv 5)).
  assert (R26f : getr (ms_regs ms0) 26 = w64 now) by (yc_reg W HS ms0 (26%bv : bv 5)).
  assert (R23f : getr (ms_regs ms0) 23 = w64 (op mod 4)) by (yc_reg W HS ms0 (23%bv : bv 5)).
  assert (R12f : getr (ms_regs ms0) 12 = w64 len) by (yc_reg W HS ms0 (12%bv : bv 5)).
  assert (R24f : getr (ms_regs ms0) 24 = w64 nb) by (yc_reg W HS ms0 (24%bv : bv 5)).
  assert (R25f : getr (ms_regs ms0) 25 = w64 (d_cur cx nb)) by (yc_reg W HS ms0 (25%bv : bv 5)).
  apply SRr_ret.
  apply (yc_mid_of fq cx h i n now op fr len nb ly3 S3 W md5 k acc Ed _ ms0 HFQ Hbase HJ Hfrs
    Hk Hnev Hmo Hacc Ri Rn Rnow Rop Ropm Rfr Rlen Rlennb Rnbcn ltac:(lia) HS eq_refl eq_refl
    HrLf R22f R21f R26f R23f R12f R24f R25f F208 F320 F360
    (y_val_mem_unmod64 _ _ _ F352) F200 F328 F368 F408 HGA Hbodyf).
- rewrite branch_eq_U, (U_atom Ed 574%nat len E574 ltac:(unfold REC_MAX in *; lia)),
    (U_lit Ed 0 ltac:(lia)) in Hc.
  apply Z.eqb_neq in Hc.
  assert (Hlenpos : 0 < len) by lia.
  assert (Hcn0 : 0 < c_n cx) by lia.
  paj_run_to_sh RUNTO HS HJ 3460.
  { yc_awr Ed cx ly3 A60 A516 A529 EFB3. }
  psrr_branch_pi RUNP BR HS.
  2: { exfalso. rewrite branch_ne_U, (U_atom Ed 541%nat fr E541 ltac:(lia)),
         (U_lit Ed 0 ltac:(lia)) in Hc0.
       apply Bool.negb_false_iff, Z.eqb_eq in Hc0. lia. }
  paj_run_shc RUNP RUNC HS HJ.
  { yc_awr Ed cx ly3 A60 A516 A529 EFB3. }
  set (md6 := with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy
    (with_vm_backing (m_vm_lazy md3) mat md3)) mat0 (with_vm_backing (m_vm_lazy md3) mat md3))) mat1
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat md3)) mat0
      (with_vm_backing (m_vm_lazy md3) mat md3))) in *.
  assert (KEEPp : forall a, 0 <= a < 2 ^ 64 ->
    ~ (d_A cx - 4096 <= a < d_A cx + 472) ->
    ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) ->
    aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha HA1 HA3.
    transitivity (aview SEGS (w_H W) (ms_mem ms0) a); [yc_keep HFr1 A60 A529|].
    transitivity (aview SEGS (w_H W) (ms_mem ms) a); [yc_keep HFr0 A60 A529 | yc_keep HFr A60 A529]. }
  assert (PRESp : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms1) a).
  { intros a Hp.
    exact (yc_pres_grows _ _ _ a HG1 (yc_pres_grows _ _ _ a HG0 (yc_pres_grows _ _ _ a HG Hp))). }
  assert (HGp : garr8 SEGS (rd W (ms_mem ms1)) (c_p cx)
    (map (fun b : byte => bv_unsigned b) (c_pl cx))).
  { refine (garr8_aview_kept SEGS (w_H W) (w_H W) mem3 (ms_mem ms1) _ _ _ HINPg).
    intros a Ha. rewrite length_map in Ha.
    apply KEEPp; [ pose proof alloc_ceiling_val; destruct (Hg8 Hcn0) as (Hp0 & Hpce & _); lia
                 | apply (HnotAp a Hcn0); lia | apply (HnotShp a Hcn0); lia ]. }
  pose proof (proj1 HJ) as HARc.
  assert (RGc : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms1) r = getr regs r).
  { intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 r HS),
      (yc_regs_ok cx E regs h i now op len HdE HrL RA r).
    cbv [In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [match goal with |- sv_denot _ ?a = sv_denot _ ?b =>
         let a' := eval vm_compute in a in let b' := eval vm_compute in b in
         change a with a'; change b with b' end; reflexivity|]).
    destruct Hr. }
  assert (R10c : getr (ms_regs ms1) 10 = w64 fr).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 10%bv HS).
    match goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end.
    apply yc_den0. exact E541. }
  assert (R11c : getr (ms_regs ms1) 11 = w64 (d_cur cx nb)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 11%bv HS).
    match goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end.
    apply yc_den0. exact E556. }
  assert (R12c : getr (ms_regs ms1) 12 = w64 len).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 12%bv HS).
    match goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end.
    apply yc_den0. exact E574. }
  assert (R1c : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + RA_CPY)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 1%bv HS).
    match goal with |- sv_denot _ ?a = _ => let a' := eval vm_compute in a in change a with a' end.
    exact (codeptr_val _ RA_CPY HEI). }
  assert (Hspc : spZ (ms_regs ms1) = d_S cx + (d_A cx - d_S cx)).
  { unfold spZ. rewrite (RGc 2%bv ltac:(cbv; tauto)). unfold spZ in Hsp. lia. }
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY fq) W
      (ms_regs ms1) (ms_mem ms1) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k fr (d_cur cx nb) len (d_A cx - d_S cx) _ HJ).
    - exact R10c.
    - exact R11c.
    - exact R12c.
    - unfold REC_MAX in *; lia.
    - lia.
    - pose proof alloc_ceiling_val; lia.
    - exact Hspc.
    - lia.
    - lia.
    - unfold ESTACK, LLVMF_STK; lia.
    - rewrite (RGc 3%bv ltac:(cbv; tauto)); exact Hgp.
    - rewrite (RGc 4%bv ltac:(cbv; tauto)); exact Htp.
    - exact R1c.
    - apply ret_ok_codeptr_v; [unfold RA_CPY; lia | reflexivity].
    - intros a Ha. split.
      + right. right. left. exists fr, len. split; [exact Hfrin | split; [exact Hnotbase | lia]].
      + unfold ESTACK, LLVMF_STK in *. lia.
      - eapply (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms1) _ fr len);
        [exact HARc | exact Hfrin | lia | lia].
    - eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms1) _ fr len);
        [exact HARc | exact Hfrin | lia | lia].
    - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms1) _ fr len);
        [exact HARc | exact Hfrin | lia | lia | lia].
    - split; [unfold d_cur; destruct (Hg8 Hcn0) as (Hp0 & Hpce & _); lia|].
      split; [unfold d_cur; destruct (Hg8 Hcn0) as (Hp0 & Hpce & _);
              pose proof alloc_ceiling_val; lia|].
      split.
      { intros a Ha. unfold d_cur in Ha. split.
        - apply (yc_garr8_some W (ms_mem ms1) (c_p cx)
            (map (fun b : byte => bv_unsigned b) (c_pl cx)) a HGp).
          rewrite length_map. lia.
        - unfold ESTACK. rewrite Hspc.
          destruct (Hg8 Hcn0) as (Hp0 & Hpce & _). unfold LLVMF_STK in Hgce. lia. }
      split.
      { assert (Hne : (fr, len) <> (c_p cx, c_n cx)).
        { intros Heq. apply Hnotbase. rewrite Heq.
          destruct HINdisj as [(Hn0 & _) | (Hr & Hpin)]; [lia | exact Hpin]. }
        pose proof (sep_blocks SEGS B LAWS ly3 S3 W mem3 md3 fr len (c_p cx) (c_n cx)
          HAR3 Hfrin (Hpin3 Hcn0) Hne) as Hz.
        unfold zdisjoint in Hz. cbn [fst snd] in Hz.
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq2).
        unfold d_cur in *. lia. }
      split.
      { eapply (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms1) _ (c_p cx) (c_n cx));
          [exact HARc | exact (Hpin3 Hcn0) | unfold d_cur; lia
          | pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq2); unfold d_cur; lia]. }
      split.
      { eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms1) _ (c_p cx) (c_n cx));
          [exact HARc | exact (Hpin3 Hcn0) | unfold d_cur; lia
          | pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq2); unfold d_cur; lia]. }
      intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W (ms_mem ms1) _ (c_p cx) (c_n cx));
        [exact HARc | exact (Hpin3 Hcn0) | unfold d_cur; lia
        | pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq2); unfold d_cur; lia | lia]. }
  cbv beta. intros W5 c5 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha10 & Heff & Hfr5 & Hpres5 & Hsame5).
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (firstn 4 (ss_mem ssx)) in
    pose proof (st_ok_pi_after_call_hi (fx := fq) 600 Ex ssx msx regs2 (mrestrict (w_H W) mem2) rs
      RA_CPY HEI ltac:(unfold RA_CPY; lia) HS eq_refl
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(submem_tac) eq_refl HP2) as HS2
  end.
  lazymatch type of HS2 with Forall ?P ?rs -> _ => assert (HKEPT : Forall P rs) end.
  { assert (HnotSh512 : forall a, fr <= a < fr + len ->
      ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512)).
    { intros a Ha Hsh. unfold shadow_addr, SHADOW_OFF in Hsh.
      exact (fshadow_not_app (d_FB cx) 512 fr (req_size len) a HFB1 ltac:(lia) Happfr
        ltac:(lia) ltac:(lia)). }
    pose proof alloc_ceiling_val as Hacv.
    apply Forall_cons.
    { eapply (region_kept_aview Ed (w_H W) (ms_mem ms1) mem2 2%nat (d_S cx));
        [ rewrite (AO 2%nat ltac:(unfold AT_FL; lia)), (EE 2%nat 2%bv eq_refl); reflexivity
        | | exact Hpres5 ].
      intros a Ha. unfold LLVMF_STK in Hgce. apply Hfr5.
      - lia.
      - lia.
      - unfold ESTACK. lia. }
    apply Forall_cons.
    { eapply (region_kept_aview Ed (w_H W) (ms_mem ms1) mem2 60%nat (d_A cx));
        [ exact A60 | | exact Hpres5 ].
      intros a Ha. unfold LLVMF_STK in Hgce. apply Hfr5.
      - lia.
      - lia.
      - unfold ESTACK. lia. }
    apply Forall_cons.
    { eapply (region_kept_aview Ed (w_H W) (ms_mem ms1) mem2 516%nat (d_FB cx));
        [ exact A516 | | exact Hpres5 ].
      intros a Ha. unfold LLVMF_STK in Hgce.
      pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 fr len DFRAME_CLASS (c_fpos cx)
        HAR3 Hfrin Hin3) as Hz.
      unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite EFB3 in Hz.
      change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hz.
      apply Hfr5.
      - lia.
      - lia.
      - unfold ESTACK. lia. }
    apply Forall_cons; [|apply Forall_nil].
    eapply (region_kept_aview Ed (w_H W) (ms_mem ms1) mem2 529%nat (shadow_addr (d_FB cx)));
      [ exact A529 | | exact Hpres5 ].
    intros a Ha. unfold LLVMF_STK in Hgce.
    pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)) as Dfb.
    pose proof (Z.mod_pos_bound (d_FB cx) 8 ltac:(lia)) as Mfb.
    unfold shadow_addr, SHADOW_OFF in Ha.
    apply Hfr5.
    - lia.
    - intros Hfa. apply (HnotSh512 a Hfa). unfold shadow_addr, SHADOW_OFF. lia.
    - unfold ESTACK. lia. }
  specialize (HS2 HKEPT).
  change (mkst regs2 (Z_to_bv 64 (BASE + RA_CPY)) (rd W mem2) (seg_rom SEGS))
    with (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + RA_CPY)) mem2 (seg_rom SEGS))) in HS2.
  norm_ss HS2.
  set (E2 := havoc Ed 600 (map (getr regs2) CLOB)) in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
  assert (HdE2 : d_E cx E2) by (apply yc_dE_havoc; [exact HdEd | lia]).
  assert (EH : forall j : nat, (j < 600)%nat -> ew E2 j = ew Ed j)
    by (intros j Hj; unfold E2; apply ew_havoc_old; exact Hj).
  assert (A60b : bv_unsigned (ew E2 60%nat) = d_A cx) by (rewrite EH by lia; exact A60).
  assert (A516b : bv_unsigned (ew E2 516%nat) = d_FB cx) by (rewrite EH by lia; exact A516).
  assert (A529b : bv_unsigned (ew E2 529%nat) = shadow_addr (d_FB cx)) by (rewrite EH by lia; exact A529).
  assert (HFL2 : ew E2 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
    by (rewrite EH by (unfold AT_FL; lia); apply yc_env_fl).
  paj_run_to_sh RUNTO HS2 HJ2 MID_OFF.
  { yc_awr E2 cx ly3 A60b A516b A529b EFB3. }
  set (md7 := with_vm_backing (m_vm_lazy md2) mat2 md2) in *.
  assert (Hctx7 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms2) md7 k)
    by (split; [exact Hbase | split; [exact HJ2 | exact Hfrs]]).
  pose proof (st_ok_pi_region_nth E2 _ _ 1 _ HS2 eq_refl) as HR60f.
  cbn [ms_mem restrict mkst] in HR60f.
  assert (G563 : ew E2 563 = Z_to_bv 64 h) by (rewrite EH by lia; exact E563).
  assert (G564 : ew E2 564 = Z_to_bv 64 (h + 440)) by (rewrite EH by lia; exact E564).
  assert (G565 : ew E2 565 = Z_to_bv 64 0) by (rewrite EH by lia; exact E565).
  assert (G566 : ew E2 566 = Z_to_bv 64 (dnot (d_obj cx OG))) by (rewrite EH by lia; exact E566).
  assert (G567 : ew E2 567 = Z_to_bv 64 (dnot (d_obj cx OT))) by (rewrite EH by lia; exact E567).
  assert (G568 : ew E2 568 = Z_to_bv 64 (dnot (d_obj cx OO))) by (rewrite EH by lia; exact E568).
  assert (G569 : ew E2 569 = Z_to_bv 64 (dnot (d_obj cx OUSED))) by (rewrite EH by lia; exact E569).
  assert (G570 : ew E2 570 = Z_to_bv 64 i) by (rewrite EH by lia; exact E570).
  assert (G571 : ew E2 571 = Z_to_bv 64 now) by (rewrite EH by lia; exact E571).
  assert (G572 : ew E2 572 = Z_to_bv 64 op) by (rewrite EH by lia; exact E572).
  assert (G573 : ew E2 573 = Z_to_bv 64 ((if op <? 128 then op else op - 256) mod 2 ^ 64))
    by (rewrite EH by lia; exact E573).
  assert (G574 : ew E2 574 = Z_to_bv 64 len) by (rewrite EH by lia; exact E574).
  assert (G541 : ew E2 541 = Z_to_bv 64 fr) by (rewrite EH by lia; exact E541).
  assert (G555 : ew E2 555 = Z_to_bv 64 nb) by (rewrite EH by lia; exact E555).
  assert (G556 : ew E2 556 = Z_to_bv 64 (d_cur cx nb)) by (rewrite EH by lia; exact E556).
  assert (G552 : ew E2 552 = Z_to_bv 64 i) by (rewrite EH by lia; exact E552).
  assert (G553 : ew E2 553 = Z_to_bv 64 1) by (rewrite EH by lia; exact E553).
  assert (G554 : ew E2 554 = Z_to_bv 64 (op mod 4)) by (rewrite EH by lia; exact E554).
  assert (G557 : ew E2 557 = Z_to_bv 64 now) by (rewrite EH by lia; exact E557).
  clear E563 E564 E565 E566 E567 E568 E569 E570 E571 E572 E573 E574 E541 E555 E556
    E552 E553 E554 E557.
  assert (F184 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 184) 8 h)
    by (yc_fld HR60f A60b 184 563%nat; exact Hhb).
  assert (F120 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 120) 8 (h + 440))
    by (yc_fld HR60f A60b 120 564%nat; exact Hh440b).
  assert (F136 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 136) 8 0)
    by (yc_fld HR60f A60b 136 565%nat; lia).
  assert (F376 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 376) 8 (dnot (d_obj cx OG)))
    by (yc_fld HR60f A60b 376 566%nat; apply Hdnotb).
  assert (F280 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 280) 8 (dnot (d_obj cx OT)))
    by (yc_fld HR60f A60b 280 567%nat; apply Hdnotb).
  assert (F232 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 232) 8 (dnot (d_obj cx OO)))
    by (yc_fld HR60f A60b 232 568%nat; apply Hdnotb).
  assert (F264 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)))
    by (yc_fld HR60f A60b 264 569%nat; apply Hdnotb).
  assert (F208 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 208) 8 i)
    by (yc_fld HR60f A60b 208 570%nat; unfold MAX_OPS in *; lia).
  assert (F320 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 320) 8 now)
    by (yc_fld HR60f A60b 320 571%nat; lia).
  assert (F360 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 360) 8 op)
    by (yc_fld HR60f A60b 360 572%nat; lia).
  assert (F352 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 352) 8
    ((if op <? 128 then op else op - 256) mod 2 ^ 64))
    by (yc_fld HR60f A60b 352 573%nat; exact Hsopb).
  assert (F408 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 408) 8 len)
    by (yc_fld HR60f A60b 408 574%nat; unfold REC_MAX in *; lia).
  assert (F200 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 200) 8 (d_cur cx nb))
    by (yc_fld HR60f A60b 200 556%nat; exact Hdcur).
  assert (F328 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 328) 8 nb)
    by (yc_fld HR60f A60b 328 555%nat; lia).
  assert (F368 : val_mem SEGS (rd W (ms_mem ms2)) (d_A cx + 368) 8 fr)
    by (yc_fld HR60f A60b 368 541%nat; pose proof alloc_ceiling_val; lia).
  destruct (LAND LAWS FFL fq cx h dsh_rec ly3 S3 W md7 k E2 _ ms2 Hctx7 HdE2 HFL2 HS2
    ltac:(vm_compute; reflexivity) F184 F120 F136 F376 F280 F232 F264) as [Hframe6 Hshadow6].
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((d_A cx - 4096 <= a < d_A cx + 472) \/ (fr <= a < fr + len) \/
       (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384)) ->
    aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha HnR.
    assert (HA1 : ~ (d_A cx - 4096 <= a < d_A cx + 472)) by tauto.
    assert (HA2 : ~ (fr <= a < fr + len)) by tauto.
    assert (HA3 : ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384)) by tauto.
    transitivity (aview SEGS (w_H W) mem2 a); [yc_keep HFr2 A60b A529b|].
    transitivity (aview SEGS (w_H W) (ms_mem ms1) a);
      [apply Hfr5; [lia | lia | unfold ESTACK; lia] | apply KEEPp; assumption]. }
  assert (PRES : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms2) a).
  { intros a Hp. exact (yc_pres_grows _ _ _ a HG2 (Hpres5 a (PRESp a Hp))). }
  assert (Hbodyf : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms2)).
  { rewrite Hdxb.
    apply (BRT cx h n n [(fr, len)] dsh_loop dsh_rec ly3 S3 W mem3 (ms_mem ms2)
      (d_A cx - 4096) (d_A cx + 472)
      (fun a => (d_A cx - 4096 <= a < d_A cx + 472) \/ (fr <= a < fr + len) \/
                (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384)) Hbody);
      [ unfold LLVMF_STK; lia | lia
      | intros a [Ha | [Ha | Ha]];
        [left; exact Ha | right; exact (HnRDfr a Ha) | right; exact (HnRDsh a Ha)]
      | exact KEEP | intros a _ Hp; exact (PRES a Hp) | exact Hframe6 | exact Hshadow6 | lia ]. }
  assert (HGA : garr8 SEGS (rd W (ms_mem ms2)) fr
    (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))).
  { refine (garr8_aview_kept SEGS (w_H W) (w_H W) mem2 (ms_mem ms2) _ _ _ _).
    - intros a Ha. unfold rest_of in Ha.
      rewrite length_map, yc_length_firstn, yc_length_skipn in Ha.
      assert (HA1 : ~ (d_A cx - 4096 <= a < d_A cx + 472)) by (apply HnotA; lia).
      assert (HA3 : ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384))
        by (apply HnotShfr; lia).
      yc_keep HFr2 A60b A529b.
    - unfold rest_of.
      apply (yc_frm_garr8 W (ms_mem ms1) mem2 (c_pl cx) (c_p cx) (c_n cx) nb len fr
        Hglen ltac:(lia) ltac:(lia) Rlennb HGp).
      intros j Hj. rewrite (Heff j Hj). unfold d_cur. reflexivity. }
  assert (RF : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
    getr (ms_regs ms2) r = getr regs r).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms2 r HS2),
      (yc_regs_ok cx E regs h i now op len HdE HrL RA r).
    cbv [In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [match goal with |- sv_denot _ ?a = sv_denot _ ?b =>
         let a' := eval vm_compute in a in let b' := eval vm_compute in b in
         change a with a'; change b with b' end;
       cbn [sv_denot]; rewrite EH by lia; reflexivity|]).
    destruct Hr. }
  assert (HrLf : d_rL B cx (ms_regs ms2)).
  { unfold d_rL.
    split; [unfold spZ in *; rewrite (RF 2%bv ltac:(cbv; tauto)); exact Hsp|].
    rewrite (RF 3%bv ltac:(cbv; tauto)), (RF 4%bv ltac:(cbv; tauto)), (RF 8%bv ltac:(cbv; tauto)),
      (RF 9%bv ltac:(cbv; tauto)), (RF 19%bv ltac:(cbv; tauto)), (RF 18%bv ltac:(cbv; tauto)),
      (RF 20%bv ltac:(cbv; tauto)), (RF 27%bv ltac:(cbv; tauto)).
    repeat split; assumption. }
  assert (R22f : getr (ms_regs ms2) 22 = w64 1) by (yc_reg W HS2 ms2 (22%bv : bv 5)).
  assert (R21f : getr (ms_regs ms2) 21 = w64 i) by (yc_reg W HS2 ms2 (21%bv : bv 5)).
  assert (R26f : getr (ms_regs ms2) 26 = w64 now) by (yc_reg W HS2 ms2 (26%bv : bv 5)).
  assert (R23f : getr (ms_regs ms2) 23 = w64 (op mod 4)) by (yc_reg W HS2 ms2 (23%bv : bv 5)).
  assert (R12f : getr (ms_regs ms2) 12 = w64 len) by (yc_reg W HS2 ms2 (12%bv : bv 5)).
  assert (R24f : getr (ms_regs ms2) 24 = w64 nb) by (yc_reg W HS2 ms2 (24%bv : bv 5)).
  assert (R25f : getr (ms_regs ms2) 25 = w64 (d_cur cx nb)) by (yc_reg W HS2 ms2 (25%bv : bv 5)).
  apply SRr_ret.
  apply (yc_mid_of fq cx h i n now op fr len nb ly3 S3 W md7 k acc E2 _ ms2 HFQ Hbase HJ2 Hfrs
    Hk Hnev Hmo Hacc Ri Rn Rnow Rop Ropm Rfr Rlen Rlennb Rnbcn ltac:(lia) HS2 eq_refl eq_refl
    HrLf R22f R21f R26f R23f R12f R24f R25f F208 F320 F360
    (y_val_mem_unmod64 _ _ _ F352) F200 F328 F368 F408 HGA Hbodyf).
Qed.
End h.
End f.
End d.

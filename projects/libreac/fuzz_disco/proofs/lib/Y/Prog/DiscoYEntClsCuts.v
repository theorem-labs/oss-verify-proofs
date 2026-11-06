(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 568 of its 627 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntClsCuts.v, with its module paths, module names and addresses changed; 248 of its 701 lines of code are new or changed and 174 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel CtrlParsed slot_classify.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt ClassifyCore.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition cl_sr_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 19%nat => SOff 32 0 | 27%nat => SOff AT_SH 0
  | _ => SOff (AT_X + r) 0
  end.
Definition cl_sr : list sv := map cl_sr_x (seq 0 32).
Definition cl_vals (regs : bvmap 5 word) (xs : list word) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ xs.
Definition cl_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition cl_F (pl : list byte) (nb len : Z) : list byte := firstn 50 (firstn (Z.to_nat len) (rest_of pl nb)).
Definition saddr_okb (x s : Z) : bool := (s =? 0) || ((x mod 8 <? s) && (s <? 8)).
Definition cl_obj_shb (o : dobj) : bool :=
  forallb (fun j => let x := dobj_off o + Z.of_nat j in saddr_okb x (dsh_rec (x / 8))) (seq 0 (Z.to_nat (dobj_size o))).
Definition cl_rng_chk (lo hi : Z) (cs : list YP09.chunk) : bool :=
  forallb (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + c_len c <=? hi) && (0 <=? c_len c)) cs.

Lemma cl_saddr_okb : forall x s, saddr_okb x s = true -> saddr_ok x s.
Proof.
intros x s H. unfold saddr_okb in H. unfold saddr_ok.
apply orb_true_iff in H as [H | H]; [left; apply Z.eqb_eq; exact H|].
apply andb_true_iff in H as [H1 H2]. right. apply Z.ltb_lt in H1, H2. lia.
Qed.

Lemma cl_rng_chk_ok : forall lo hi cs c, cl_rng_chk lo hi cs = true -> In c cs ->
  lo <= YP09.c_off c /\ YP09.c_off c + c_len c <= hi /\ 0 <= c_len c.
Proof.
intros lo hi cs c H Hin. unfold cl_rng_chk in H. rewrite forallb_forall in H. specialize (H c Hin).
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.leb_le in H1, H2, H3. lia.
Qed.

Lemma cl_nn : forall x y : option Z, ~ (x <> y) -> x = y.
Proof.
intros [x|] [y|] H; try reflexivity; try (exfalso; apply H; discriminate).
destruct (Z.eq_dec x y) as [->|Hne]; [reflexivity | exfalso; apply H; congruence].
Qed.

Lemma cl_ro_pt : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Ha).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma cl_garr8_firstn : forall segs (m : word -> option byte) p (L : list byte) k,
  garr8 segs m p (map (fun b : byte => bv_unsigned b) L) ->
  garr8 segs m p (map (fun b : byte => bv_unsigned b) (firstn k L)).
Proof.
intros segs m p L k HG j Hj. rewrite length_map, length_firstn in Hj.
rewrite <- firstn_map, nth_firstn. replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
apply HG. rewrite length_map. lia.
Qed.

Lemma cl_rest_len : forall (pl : list byte) nb len, 0 <= len <= nb -> nb <= Z.of_nat (length pl) ->
  length (firstn (Z.to_nat len) (rest_of pl nb)) = Z.to_nat len.
Proof.
intros pl nb len H1 H2. unfold rest_of. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma cl_fb50 : forall L : list byte, (50 <= length L)%nat -> slot_classify.fb50 L = firstn 50 L.
Proof.
intros L HL. unfold slot_classify.fb50. rewrite firstn_app. replace (50 - length L)%nat with 0%nat by lia.
rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma cl_fs6 : fs_frame_bytes DFRAME_CLASS = 4096.
Proof. reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.

Lemma cl_objr_frame : forall cx o a, d_objr cx o a -> d_FB cx <= a < d_FB cx + DFRAME_SIZE.
Proof. intros cx o a H. unfold d_objr, d_obj, DFRAME_SIZE in *. destruct o; cbn [dobj_off dobj_size] in H; lia. Qed.

End f.
End d.

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

Lemma cl_rok_keep : forall E (H H2 : word -> bool) (m m2 : word -> option byte) r,
  region_ok SEGS E (mrestrict H m) r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < c_len c ->
     aview SEGS H2 m2 (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     aview SEGS H m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> apresent H2 m2 (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E (mrestrict H2 m2) r.
Proof.
intros E H H2 m m2 r HR Hc Hw. unfold region_ok in *. cbv zeta in *.
destruct HR as (H1 & H3 & _ & Hcs).
split; [exact H1|]. split; [exact H3|]. split.
- intros o Ho. apply (apresent_writable SEGS). apply Hw. exact Ho.
- rewrite Forall_forall in Hcs |- *. intros c Hin i Hi.
  destruct (Hcs c Hin i Hi) as (b & Hb & Hm). exists b. split; [exact Hb|].
  rewrite (mbyte_of_aview SEGS H H2 m m2); [exact Hm | apply Hc; assumption].
Qed.

Lemma cl_shadow_keep : forall cx shf (W W2 : world SEGS) m m2, d_shadow cx shf W m ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) ->
  d_shadow cx shf W2 m2.
Proof. intros cx shf W W2 m m2 H K k Hk. rewrite K by (unfold DFRAME_SH in Hk; lia). exact (H k Hk). Qed.

Lemma cl_A_range : forall cx, 0 <= d_S cx - MFRAME ->
  d_S cx - MFRAME - 31 <= d_A cx <= d_S cx - MFRAME /\ d_A cx mod 32 = 0.
Proof.
intros cx Hs. unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as Hmp.
split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma cl_garr8_ex : forall (H : word -> bool) m p n,
  (forall a, p <= a < p + Z.of_nat n -> apresent H m a) ->
  exists L : list byte, length L = n /\ garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L).
Proof.
intros H m p n Hp.
exists (map (fun j => match mbyte SEGS (mrestrict H m) (p + Z.of_nat j) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
split; [rewrite length_map, length_seq; reflexivity|].
intros j Hj. rewrite !length_map, length_seq in Hj.
pose proof (aview_some_of_apresent SEGS H m (p + Z.of_nat j) (Hp (p + Z.of_nat j) ltac:(lia))) as Hs.
unfold aview in Hs. destruct (mbyte SEGS (mrestrict H m) (p + Z.of_nat j)) as [b|] eqn:Eb; [|exfalso; apply Hs; reflexivity].
assert (Enth : nth j (map (fun b0 : byte => bv_unsigned b0)
  (map (fun j0 => match mbyte SEGS (mrestrict H m) (p + Z.of_nat j0) with Some b0 => b0 | None => Z_to_bv 8 0 end) (seq 0 n))) 0
  = bv_unsigned b).
{ rewrite map_map. rewrite (nth_indep _ 0 (bv_unsigned (match mbyte SEGS (mrestrict H m) (p + Z.of_nat 0) with Some b0 => b0 | None => Z_to_bv 8 0 end)))
    by (rewrite length_map, length_seq; exact Hj).
  rewrite (map_nth (fun j0 => bv_unsigned (match mbyte SEGS (mrestrict H m) (p + Z.of_nat j0) with Some b0 => b0 | None => Z_to_bv 8 0 end)) (seq 0 n) 0%nat j).
  rewrite seq_nth by exact Hj. cbn [Nat.add]. rewrite Eb. reflexivity. }
rewrite Enth.
pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
split; [|lia].
intros q Hq. assert (q = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. change (bv_modulus 8) with 256. repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
reflexivity.
Qed.

Lemma cl_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; assumption | exact (pa_relro_img a Hr)].
Qed.

Lemma cl_off_not_img : forall p n a, off_img p n -> p <= a < p + n -> ~ in_img SEGS a.
Proof.
intros p n a Ho Ha Hi. pose proof (pa_img_range a Hi) as Hr. unfold off_img in Ho.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation DCTX := (d_ctx B MT XM_LIB RLO RHI tfib_K).

Lemma cl_geom : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  DCTX cx ly3 S3 W3 mem3 md3 k ->
  d_S cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= d_S cx /\ d_S cx <= 2 ^ 47 /\
  4096 <= d_FB cx /\ d_FB cx + 4096 <= alloc_ceiling /\ in_app (d_FB cx) 4096 /\
  off_img (d_FB cx) 4096 /\ d_FB cx mod 32 = 0 /\
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> apresent (w_H W3) mem3 a) /\
  (forall i, 0 <= i < 512 -> apresent (w_H W3) mem3 (shadow_addr (d_FB cx) + i)) /\
  (forall a, d_S cx - LLVMF_STK <= a < d_S cx -> apresent (w_H W3) mem3 a) /\
  AR SEGS B ly3 S3 W3 mem3 md3 /\ In (DFRAME_CLASS, c_fpos cx) (frames S3) /\
  frame_addr ly3 DFRAME_CLASS (c_fpos cx) = d_FB cx /\
  flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx).
Proof.
intros cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
destruct HB as ((HPRE & _) & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
assert (Efl : flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
{ pose proof (Efa 0 0) as E00. unfold frame_addr in E00. unfold flag_addr. lia. }
destruct (frames_bounds _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (HF0 & HFc & HFia).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as HFo.
destruct (al_frames _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (Hal & _ & HFpres & HSpres).
rewrite Efa in HF0, HFc, HFia, HFo, Hal, HFpres, HSpres.
change (frame_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) with (d_FB cx) in *.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. change (4096 / 8) with 512 in HSpres.
change (spZ (c_regs cx)) with (d_S cx) in *.
split; [exact Hal16|]. split; [unfold LLVMF_STK in *; lia|]. split; [lia|].
split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|]. split; [exact Hal|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [intros i Hi; exact (proj1 (HSpres i Hi))|].
split; [intros a Ha; apply HJpres; exact Ha|].
split; [exact HAR3|]. split; [exact Hfin|]. split; [rewrite Efa; reflexivity|]. exact Efl.
Qed.

Definition cl_kmax (i : Z) : Z := EV_HEAD i + 1.
Definition cl_amax (i : Z) : Z := ACC_HEAD MT i + mo_malloc MT REC_MAX.
Definition cl_base (cx : dcx) (h i n now op nb fr len : Z) (regs : bvmap 5 word) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ (op mod 4 = 0 \/ op mod 4 = 1) /\ 0 <= op < 256 /\
  d_rL B cx regs /\ d_sp0 cx i now W3 mem3 /\ d_frm cx nb fr len W3 mem3 /\
  d_spREC cx nb fr len W3 mem3 /\ d_spOP cx op W3 mem3 /\
  len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7) /\ nb <= c_n cx /\
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W3 mem3.
Definition cl_sg (cx : dcx) (nb len : Z) (Sg : list byte) (W : world SEGS) (m : word -> option byte) : Prop :=
  length Sg = 24%nat /\ garr8 SEGS (rd W m) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) /\
  sighting_facts Sg (cl_F (c_pl cx) nb len) (our_of (c_pl cx)) len 0.
Definition cl_gate (cx : dcx) (G : list byte) (W : world SEGS) (m : word -> option byte) : Prop :=
  length G = 264%nat /\ garr8 SEGS (rd W m) (d_obj cx OG) (map (fun b : byte => bv_unsigned b) G) /\ gate_ok G.
Definition cl_spl (cx : dcx) (push : Z) (W : world SEGS) (m : word -> option byte) : Prop :=
  val_mem SEGS (rd W m) (d_A cx + 296) 8 push /\ 0 <= push <= 1.
Definition cl_R (cx : dcx) (h i n now op nb fr len pc : Z) : world SEGS -> config -> Prop :=
  DAT cx pc (cl_kmax i) (cl_amax i) (fun regs ly3 S3 W3 mem3 md3 => exists r,
    cl_base cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\
    getr regs 10 = w64 r /\ (r = -1 \/ (r = 0 /\ exists Sg, cl_sg cx nb len Sg W3 mem3))).
Definition cl_CSR (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx 0xf0c (cl_kmax i) (cl_amax i) (fun regs ly3 S3 W3 mem3 md3 => exists Sg,
    cl_base cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\
    getr regs 21 = w64 (d_obj cx OS) /\ getr regs 23 = w64 now /\ getr regs 22 = w64 1 /\
    cl_sg cx nb len Sg W3 mem3).
Definition cl_GR (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx 0xf1c (cl_kmax i) (cl_amax i) (fun regs ly3 S3 W3 mem3 md3 => exists Sg G push,
    cl_base cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\
    getr regs 22 = w64 1 /\ cl_sg cx nb len Sg W3 mem3 /\ cl_gate cx G W3 mem3 /\
    getr regs 10 = w64 push /\ 0 <= push <= 1).
Definition cl_lmem (cx : dcx) (h i n now op nb fr len nn : Z) (regs : bvmap 5 word) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  exists Sg G push, cl_base cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ cl_sg cx nb len Sg W3 mem3 /\
    cl_gate cx G W3 mem3 /\ gn G = nn /\ cl_spl cx push W3 mem3.
Definition cl_LI (cx : dcx) (h i n now op nb fr len nn k : Z) : world SEGS -> config -> Prop :=
  DAT cx 0xf4c (cl_kmax i) (cl_amax i) (fun regs ly3 S3 W3 mem3 md3 =>
    cl_lmem cx h i n now op nb fr len nn regs ly3 S3 W3 mem3 /\ 0 <= k < nn /\
    getr regs 21 = w64 k /\ getr regs 24 = w64 nn /\ getr regs 22 = w64 (32 * (k + 1)) /\
    getr regs 26 = w64 (32 * nn)).
Definition cl_jregs (cx : dcx) (nn k j : Z) (regs : bvmap 5 word) : Prop :=
  0 <= k < j /\ j < nn /\
  getr regs 21 = w64 (k + 1) /\ getr regs 24 = w64 nn /\ getr regs 22 = w64 (32 * (k + 1)) /\
  getr regs 26 = w64 (32 * nn) /\ getr regs 25 = w64 (d_obj cx OG + 32 * k) /\ getr regs 23 = w64 (32 * j).
Definition cl_LJ (cx : dcx) (h i n now op nb fr len nn k j : Z) : world SEGS -> config -> Prop :=
  DAT cx 0xf68 (cl_kmax i) (cl_amax i) (fun regs ly3 S3 W3 mem3 md3 =>
    cl_lmem cx h i n now op nb fr len nn regs ly3 S3 W3 mem3 /\ cl_jregs cx nn k j regs).
Definition cl_BR (cx : dcx) (h i n now op nb fr len nn k j : Z) : world SEGS -> config -> Prop :=
  DAT cx 0xf94 (cl_kmax i) (cl_amax i) (fun regs ly3 S3 W3 mem3 md3 =>
    cl_lmem cx h i n now op nb fr len nn regs ly3 S3 W3 mem3 /\ cl_jregs cx nn k j regs /\
    getr regs 10 <> w64 0).
Definition cl_X (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  DAT cx 0xfac (cl_kmax i) (cl_amax i) (fun regs ly3 S3 W3 mem3 md3 => exists Sg push,
    cl_base cx h i n now op nb fr len regs ly3 S3 W3 mem3 /\ cl_sg cx nb len Sg W3 mem3 /\
    cl_spl cx push W3 mem3).
Definition cl_post (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  fun W' c' => (exists Sg, obs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg W' c') \/
    r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len W' c'.

Lemma cl_regs_ok : forall cx E regs xs, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (cl_vals regs xs)) cl_sr regs.
Proof.
intros cx E regs xs HE HL HA.
destruct HE as (HER & H32 & _ & HA60 & _ & HSH).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_SH with 529%nat in HSH.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H19
          | rewrite HSH; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth cl_vals map seq app Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Lemma cl_frame_keep : forall cx h shf (W : world SEGS) m ly2 S2 (W2 : world SEGS) m2 md2 k2,
  DCTX cx ly2 S2 W2 m2 md2 k2 -> d_frame cx h shf W m ->
  (forall a, (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/ (d_FB cx <= a < d_FB cx + 24) \/
     (d_FB cx + 4088 <= a < d_FB cx + 4096) \/ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) ->
  d_frame cx h shf W2 m2.
Proof.
intros cx h shf W m ly2 S2 W2 m2 md2 k2 HC (E & HE & HR & Hfl & V184 & V120 & V136 & V376 & V280 & V232 & V264) K.
destruct (cl_geom cx ly2 S2 W2 m2 md2 k2 HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
unfold AT_A, AT_F, AT_SH in E60, EF, ESH.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U60 : bv_unsigned (ew E 60) = d_A cx)
  by (rewrite E60; unfold w64; apply unsigned_lit_small; unfold MFRAME, LLVMF_STK in *; lia).
assert (U516 : bv_unsigned (ew E 516) = d_FB cx) by (rewrite EF; unfold w64; apply unsigned_lit_small; lia).
assert (HSHb : 0 <= shadow_addr (d_FB cx) < 2 ^ 64).
{ pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSH.
  unfold kLowMemEnd, kHighShadowEnd in *. lia. }
assert (U529 : bv_unsigned (ew E 529) = shadow_addr (d_FB cx)) by (rewrite ESH; unfold w64; apply unsigned_lit_small; lia).
exists E. split; [exact HE|].
unfold d_regions in HR |- *.
apply Forall_cons_iff in HR as (R0 & HR). apply Forall_cons_iff in HR as (R1 & HR).
apply Forall_cons_iff in HR as (R2 & HR). apply Forall_cons_iff in HR as (R3 & _).
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- repeat apply Forall_cons; [ | | | | apply Forall_nil].
  + apply (cl_rok_keep E _ _ _ _ _ R0); cbn [YP09.r_chunks YP09.r_base YP09.r_wlo YP09.r_whi base_val]; unfold AT_STK.
    * intros c i Hc Hi. apply K. left.
      pose proof (cl_rng_chk_ok (-104) 0 dsave_chunks c ltac:(vm_compute; reflexivity) Hc). rewrite U2. lia.
    * intros o Ho. lia.
  + apply (cl_rok_keep E _ _ _ _ _ R1); cbn [YP09.r_chunks YP09.r_base YP09.r_wlo YP09.r_whi base_val]; unfold AT_A.
    * intros c i Hc Hi. apply K. right. left.
      pose proof (cl_rng_chk_ok 0 472 dslot_chunks c ltac:(vm_compute; reflexivity) Hc). rewrite U60. lia.
    * intros o Ho. rewrite U60. apply HWpres. unfold MFRAME, LLVMF_STK in *. lia.
  + apply (cl_rok_keep E _ _ _ _ _ R2); cbn [YP09.r_chunks YP09.r_base YP09.r_wlo YP09.r_whi base_val]; unfold AT_F.
    * intros c i Hc Hi. apply K. right. right. left.
      assert (Hb : cl_rng_chk 0 24 [YP09.mkChunk 0 (CVal 8 (SLit MAGIC_LIVE)); YP09.mkChunk 8 (CVal 8 (SOff (A_OBJ 2) 0));
        YP09.mkChunk 16 (CVal 8 (SOff (A_OBJ 3) 0))] = true) by (vm_compute; reflexivity).
      pose proof (cl_rng_chk_ok 0 24 _ c Hb Hc). rewrite U516. lia.
    * intros o Ho. rewrite U516. apply HFpres. unfold DFRAME_SIZE in Ho. lia.
  + apply (cl_rok_keep E _ _ _ _ _ R3); unfold fshadow_region;
      cbn [YP09.r_chunks YP09.r_base YP09.r_wlo YP09.r_whi base_val]; unfold AT_SH.
    * intros c i Hc Hi. apply K. right. right. right. right.
      assert (Hb : cl_rng_chk 0 384 (dsh_chunks shf) = true) by (vm_compute; reflexivity).
      pose proof (cl_rng_chk_ok 0 384 _ c Hb Hc). rewrite U529. lia.
    * intros o Ho. rewrite U529. apply HSpres. unfold DFRAME_SH in Ho. lia.
- rewrite <- Hfl. apply rdword_ext. intros k0 Hk0. apply K. right. right. right. left.
  rewrite cl_fs6. lia.
- eapply YC88.val_mem_aview_kept_x; [|exact V184]. intros x Hx. apply K. right. left.
  change (Z.of_nat 8) with 8 in Hx. lia.
- eapply YC88.val_mem_aview_kept_x; [|exact V120]. intros x Hx. apply K. right. left.
  change (Z.of_nat 8) with 8 in Hx. lia.
- eapply YC88.val_mem_aview_kept_x; [|exact V136]. intros x Hx. apply K. right. left.
  change (Z.of_nat 8) with 8 in Hx. lia.
- eapply YC88.val_mem_aview_kept_x; [|exact V376]. intros x Hx. apply K. right. left.
  change (Z.of_nat 8) with 8 in Hx. lia.
- eapply YC88.val_mem_aview_kept_x; [|exact V280]. intros x Hx. apply K. right. left.
  change (Z.of_nat 8) with 8 in Hx. lia.
- eapply YC88.val_mem_aview_kept_x; [|exact V232]. intros x Hx. apply K. right. left.
  change (Z.of_nat 8) with 8 in Hx. lia.
- eapply YC88.val_mem_aview_kept_x; [|exact V264]. intros x Hx. apply K. right. left.
  change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

Lemma cl_body_n : forall cx h n n' xb shf ly S W m, d_body B cx h n xb shf ly S W m ->
  0 <= n' <= Z.max 0 (c_n cx - 7) -> d_body B cx h n' xb shf ly S W m.
Proof.
intros cx h n n' xb shf ly S W m (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & (Hn & Hg & Ho) & Rest) Hn'.
exists T, G, Lk, H. split; [exact Hfr|]. split; [exact Hsh|]. split; [exact Hobj|]. split; [exact Hbl|].
split; [exact (conj Hn' (conj Hg Ho))|]. exact Rest.
Qed.

Lemma cl_achain : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k E sp,
  DCTX cx ly3 S3 W3 mem3 md3 k -> d_E cx E ->
  region_ok SEGS E (rd W3 mem3) (YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks) ->
  sp + 16 <= d_S cx ->
  exists ch, achain ly3 (aview SEGS (w_H W3) mem3) sp (d_S cx) ch.
Proof.
intros cx ly3 S3 W3 mem3 md3 k E sp (Hbase & HJ & Hfrs) HE HRS Hsp.
destruct Hbase as ((HPRE & Hra & _) & _).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & Hkeep & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
change (spZ (c_regs cx)) with (d_S cx) in *.
pose proof HE as (EE & _).
assert (U2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
destruct (Z_lt_ge_dec (d_S cx) (ly_top ly3 - 16)) as [Hlt | Hge].
- exists [(d_S cx, RA_LLVMF, s0Z (c_regs cx))].
  apply (achain_push ly3 (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) mem3) (d_S cx)
    (s0Z (c_regs cx)) RA_LLVMF [] sp).
  + exact (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop Hch).
  + rewrite Etop. lia.
  + intros a Ha. apply Hkeep; [unfold LLVMF_STK in *; lia | lia].
  + apply rdword_of_val_mem; [| unfold RA_LLVMF; lia].
    replace (d_S cx - 8) with (d_S cx + (-8)) by lia.
    apply (field_of_region E (rd W3 mem3) AT_STK (d_S cx) dsave_chunks (-104) 0 0 0 (-8) 8%N (SOff 1 0) RA_LLVMF HRS
      U2 ltac:(vm_compute; tauto)); [| cbn; unfold RA_LLVMF; lia | cbn; lia].
    cbn [sv_denot]. rewrite Z.add_0_r, (EE 1%nat 1%bv eq_refl). unfold raZ in Hra. rewrite <- Hra.
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  + apply rdword_of_val_mem; [| unfold s0Z; apply bv_unsigned_in_range].
    replace (d_S cx - 16) with (d_S cx + (-16)) by lia.
    apply (field_of_region E (rd W3 mem3) AT_STK (d_S cx) dsave_chunks (-104) 0 0 0 (-16) 8%N (SOff 8 0)
      (s0Z (c_regs cx)) HRS U2 ltac:(vm_compute; tauto));
      [| unfold s0Z; generalize (bv_unsigned_in_range 64 (getr (c_regs cx) 8)); unfold bv_modulus;
         change (8 * Z.of_N 8) with 64; change (Z.of_N 64) with 64; lia | cbn; lia].
    cbn [sv_denot]. rewrite Z.add_0_r, (EE 8%nat 8%bv eq_refl). unfold s0Z. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + unfold RA_LLVMF. lia.
  + unfold LLVMF_STK in *. lia.
  + lia.
  + exact Hlt.
  + exact Hsp.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.

Lemma cl_obj_ra : forall cx (W : world SEGS) m o, d_shadow cx dsh_rec W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx ->
  cl_obj_shb o = true -> range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_obj cx o) (dobj_size o).
Proof.
intros cx W m o Hsh Hal H0 Hb x Hx. unfold d_obj in Hx.
assert (Hob : dobj_off o + dobj_size o <= 3072 /\ 0 <= dobj_off o) by (destruct o; cbn; lia).
set (j := x - d_FB cx - dobj_off o).
assert (Hj : 0 <= j < dobj_size o) by (subst j; lia).
unfold cl_obj_shb in Hb. rewrite forallb_forall in Hb.
specialize (Hb (Z.to_nat j) ltac:(apply in_seq; lia)). cbv zeta in Hb. rewrite Z2Nat.id in Hb by lia.
assert (Ex : x = d_FB cx + (dobj_off o + j)) by (subst j; lia).
assert (HF8 : d_FB cx = d_FB cx / 8 * 8) by (pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)); lia).
assert (Hdiv : x / 8 = d_FB cx / 8 + (dobj_off o + j) / 8).
{ rewrite Ex. replace (d_FB cx + (dobj_off o + j)) with (d_FB cx / 8 * 8 + (dobj_off o + j)) by lia.
  apply Z.div_add_l. lia. }
assert (Hmod : x mod 8 = (dobj_off o + j) mod 8).
{ rewrite Ex. replace (d_FB cx + (dobj_off o + j)) with ((dobj_off o + j) + d_FB cx / 8 * 8) by lia.
  apply Z_mod_plus_full. }
exists (dsh_rec ((dobj_off o + j) / 8)). split.
- unfold shadow_of_addr. rewrite Hdiv.
  assert (Hk : 0 <= (dobj_off o + j) / 8 < DFRAME_SH).
  { unfold DFRAME_SH. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite <- (Hsh _ Hk). unfold shadow_addr. f_equal. lia.
- apply cl_saddr_okb. unfold saddr_okb in Hb |- *. rewrite Hmod. exact Hb.
Qed.

Lemma cl_cread_obj : forall cx ly3 S3 (W : world SEGS) m md k o sp,
  DCTX cx ly3 S3 W m md k -> d_shadow cx dsh_rec W m -> cl_obj_shb o = true ->
  d_S cx - LLVMF_STK <= sp - CLS_STK ->
  cls_read W m sp (d_obj cx o) (dobj_size o).
Proof.
intros cx ly3 S3 W m md k o sp HC Hsh Hb Hsp.
destruct (cl_geom cx ly3 S3 W m md k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
assert (Hob : dobj_off o + dobj_size o <= 3072 /\ 0 <= dobj_off o /\ 0 < dobj_size o) by (destruct o; cbn; lia).
assert (HF8 : d_FB cx mod 8 = 0) by (rewrite <- (Z.mod_mod (d_FB cx) 32) in HFal by lia; lia).
unfold cls_read, d_obj. split; [lia|]. split; [unfold LLVMF_STK in *; pose proof alloc_ceiling_lt; lia|].
split; [apply (amem_range_sub_app (d_FB cx) 4096); [exact HFia | lia | lia | lia | lia]|].
split; [right; unfold LLVMF_STK in *; lia|].
split; [intros a Ha; apply HFpres; lia|].
split; [exact (cl_obj_ra cx W m o Hsh HF8 ltac:(lia) Hb)|].
apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W m md DFRAME_CLASS (c_fpos cx));
  [exact HAR | exact Hfin | rewrite Efa; lia | rewrite Efa, cl_fs6; lia | lia].
Qed.

Definition cl_kept (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (m3 : word -> option byte)
  (W4 : world SEGS) (m4 : word -> option byte) (lo hi : Z) (wr : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ wr a ->
     aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall b m i, In (b, m) (ablocks B ly3 S3) -> 0 <= i < req_size m -> ~ wr (b + i) ->
     aview SEGS (w_H W4) m4 (b + i) = aview SEGS (w_H W3) m3 (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall cid pos a, In (cid, pos) (frames S3) ->
     (in_zr a (frame_rng ly3 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8)) ->
     ~ wr a -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> apresent (w_H W3) m3 a -> apresent (w_H W4) m4 a) /\
  (forall a, lo <= a < hi -> apresent (w_H W4) m4 a).

Lemma cl_objr_dec : forall cx o a, {d_objr cx o a} + {~ d_objr cx o a}.
Proof.
intros cx o a. unfold d_objr.
destruct (Z_le_gt_dec (d_obj cx o) a); destruct (Z_lt_ge_dec a (d_obj cx o + dobj_size o));
  [left; lia | right; lia | right; lia | right; lia].
Qed.

Lemma cl_sh_frame : forall cx a b, in_app (d_FB cx) 4096 -> 4096 <= d_FB cx ->
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> d_FB cx <= b < d_FB cx + 4096 -> a <> b.
Proof.
intros cx a b Hin H0 Ha Hb E. subst b. unfold shadow_addr, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (d_FB cx) 8 ltac:(lia)). lia.
Qed.

Lemma cl_canary_img : forall a, FF_canary <= a < FF_canary + 8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. apply (ail_env SEGS B tfib_K AIL). apply (aenv_of_core SEGS B tfib_K AIL).
left. unfold aenv_core. rewrite KCAN. do 3 right. exact Ha.
Qed.

Lemma cl_view_A : forall cx ly3 S3 (W3 : world SEGS) m3 md3 k3 W4 m4 lo hi (wr : Z -> Prop),
  DCTX cx ly3 S3 W3 m3 md3 k3 -> cl_kept ly3 S3 W3 m3 W4 m4 lo hi wr -> hi <= d_A cx ->
  (forall a, wr a -> a < alloc_ceiling) ->
  forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a.
Proof.
intros cx ly3 S3 W3 m3 md3 k3 W4 m4 lo hi wr HC (K1 & _) Hhi Hwr a Ha.
destruct (cl_geom cx ly3 S3 W3 m3 md3 k3 HC) as (Hal16 & Hlo & Hhi2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
apply K1; [unfold MFRAME, LLVMF_STK in *; lia | lia | intros Hw; apply Hwr in Hw; unfold MFRAME, LLVMF_STK in *; lia].
Qed.

Lemma cl_slot_keep : forall cx ly3 S3 (W3 : world SEGS) m3 md3 k3 W4 m4 lo hi (wr : Z -> Prop) off v,
  DCTX cx ly3 S3 W3 m3 md3 k3 -> cl_kept ly3 S3 W3 m3 W4 m4 lo hi wr -> hi <= d_A cx ->
  (forall a, wr a -> a < alloc_ceiling) -> 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W3 m3) (d_A cx + off) 8 v -> val_mem SEGS (rd W4 m4) (d_A cx + off) 8 v.
Proof.
intros cx ly3 S3 W3 m3 md3 k3 W4 m4 lo hi wr off v HC HK Hhi Hwr H0 H8 HV.
destruct (cl_geom cx ly3 S3 W3 m3 md3 k3 HC) as (Hal16 & Hlo & Hhi2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
eapply YC88.val_mem_aview_kept_x; [|exact HV]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
apply (cl_view_A cx ly3 S3 W3 m3 md3 k3 W4 m4 lo hi wr HC HK Hhi Hwr). unfold MFRAME in HA1. lia.
Qed.

Lemma cl_body_call : forall cx h n xb shf ly3 S3 (W3 : world SEGS) m3 md3 k3 ly4 S4 (W4 : world SEGS) m4 md4 k4 lo hi
  (wr : Z -> Prop) (os : list dobj),
  d_body B cx h n xb shf ly3 S3 W3 m3 -> DCTX cx ly3 S3 W3 m3 md3 k3 -> DCTX cx ly4 S4 W4 m4 md4 k4 ->
  cl_kept ly3 S3 W3 m3 W4 m4 lo hi wr ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_A cx ->
  (forall a, wr a -> d_FB cx + 24 <= a < d_FB cx + DFRAME_SIZE) ->
  (forall a, wr a -> d_rdset B cx h a -> Exists (fun o => d_objr cx o a) os) ->
  Forall (fun o => d_obj_new cx o W4 m4) os ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K ->
  d_body B cx h n xb shf ly4 S4 W4 m4.
Proof.
intros cx h n xb shf ly3 S3 W3 m3 md3 k3 ly4 S4 W4 m4 md4 k4 lo hi wr os HB HC3 HC4 HK Hlo Hhi Hwr Hwro Hnew Hperm BTOBS.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
destruct (cl_geom cx ly3 S3 W3 m3 md3 k3 HC3)
  as (Hal16 & Hlo2 & Hhi2 & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
rewrite cl_fs6 in G2, G7, G8.
assert (KR : forall a, d_rdset B cx h a -> ~ Exists (fun o => d_objr cx o a) os ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hrd Hno. assert (Hnw : ~ wr a) by (intros Hw; exact (Hno (Hwro a Hw Hrd))).
  unfold d_rdset in Hrd. destruct Hrd as [Ho | [Ho | [Ho | [Ho | [Hh | [Hp | [(Hro & Hos & Her) | Hcn]]]]]]].
  1-4: apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa, cl_fs6;
    pose proof (cl_objr_frame cx _ a Ho); unfold DFRAME_SIZE in *; lia | exact Hnw].
  - pose proof Hbl as (Hp & _).
    assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact Hp | apply in_or_app; right; left; reflexivity]).
    replace a with (h + (a - h)) by lia. apply (K2 h HUNT_SIZE (a - h) Hhin).
    + pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)). lia.
    + replace (h + (a - h)) with a by lia. exact Hnw.
  - destruct Hp as (Hn0 & Hpa).
    destruct HC3 as (((_ & _ & _ & _ & Hpn & _) & _) & _).
    destruct Hpn as [(Hz & _) | (_ & Hpin)]; [lia|].
    pose proof Hbl as (Hp & _).
    assert (Hpin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact Hp | apply in_or_app; right; right; exact Hpin]).
    replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hpin3).
    + pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
    + replace (c_p cx + (a - c_p cx)) with a by lia. exact Hnw.
  - apply K3; [exact (cl_roP_img a Hro) | exact Hos | exact Her].
  - destruct (cl_canary_img a Hcn) as (Hi & Hos & Her). apply K3; assumption. }
assert (Hshw : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ wr a).
{ intros a Ha Hw. pose proof (Hwr a Hw) as Hb. unfold DFRAME_SIZE in Hb.
  exact (cl_sh_frame cx a a HFia HF0 Ha ltac:(lia) eq_refl). }
assert (KSH : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [right; unfold in_zr; cbn [fst snd]; rewrite Efa, cl_fs6; lia |].
  apply Hshw. lia. }
apply (BTOBS LAWS cx h n xb shf shf ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 lo hi os
  (fun a => aview SEGS (w_H W4) m4 a <> aview SEGS (w_H W3) m3 a) HB).
- exact (conj (proj1 HC4) (proj1 (proj2 HC4))).
- exact Hlo.
- unfold MFRAME in HA1. lia.
- intros a HRa. destruct (Exists_dec (fun o => d_objr cx o a) os (fun o => cl_objr_dec cx o a)) as [He | Hne];
    [right; left; exact He|].
  right; right. intros Hrd. apply HRa. exact (KR a Hrd Hne).
- intros a _ HnR. apply cl_nn. exact HnR.
- exact Hnew.
- exact Hperm.
- apply (cl_frame_keep cx h shf W3 m3 ly4 S4 W4 m4 md4 k4 HC4 Hfr).
  intros a Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  + apply K1; [unfold MFRAME, LLVMF_STK in *; lia | unfold MFRAME in HA1; lia |
      intros Hw; pose proof (Hwr a Hw); unfold DFRAME_SIZE, MFRAME, LLVMF_STK in *; lia].
  + apply K1; [unfold MFRAME, LLVMF_STK in *; lia | lia |
      intros Hw; pose proof (Hwr a Hw); unfold DFRAME_SIZE, MFRAME, LLVMF_STK in *; lia].
  + apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa, cl_fs6; lia |].
    intros Hw. pose proof (Hwr a Hw). lia.
  + apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Efa, cl_fs6; lia |].
    intros Hw. pose proof (Hwr a Hw). unfold DFRAME_SIZE in *. lia.
  + exact (KSH a Ha).
- exact (cl_shadow_keep cx shf W3 W4 m3 m4 Hsh KSH).
Qed.

Lemma cl_frm_keep : forall cx nb fr len ly3 S3 (W3 : world SEGS) m3 md3 k3 W4 m4 lo hi (wr : Z -> Prop) h n shf,
  DCTX cx ly3 S3 W3 m3 md3 k3 -> d_body B cx h n (dxb fr len) shf ly3 S3 W3 m3 ->
  cl_kept ly3 S3 W3 m3 W4 m4 lo hi wr -> (forall a, wr a -> d_FB cx <= a < d_FB cx + DFRAME_SIZE) ->
  d_frm cx nb fr len W3 m3 -> d_frm cx nb fr len W4 m4.
Proof.
intros cx nb fr len ly3 S3 W3 m3 md3 k3 W4 m4 lo hi wr h n shf HC3 HB HK Hwr (F1 & F2 & F3 & F4).
split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
destruct (Z.eq_dec fr 0) as [E0 | Hne].
- subst fr. rewrite (F2 eq_refl). intros j Hj. rewrite length_map, length_firstn in Hj. lia.
- pose proof HK as (_ & K2 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hbl & _).
  destruct (cl_geom cx ly3 S3 W3 m3 md3 k3 HC3)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR & Hfin & Efa & _).
  assert (Hin : In (fr, len) (ablocks B ly3 S3)).
  { pose proof Hbl as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
    unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 m3 md3 fr len DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
  rewrite Efa, cl_fs6 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos len ltac:(lia)) as Hrq.
  eapply YC88.garr8_aview_kept; [|exact F4]. intros a Ha.
  rewrite length_map in Ha.
  assert (Hl : Z.of_nat (length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) <= len)
    by (rewrite length_firstn; lia).
  replace a with (fr + (a - fr)) by lia. apply (K2 fr len (a - fr) Hin); [lia|].
  replace (fr + (a - fr)) with a by lia. intros Hw. pose proof (Hwr a Hw). unfold DFRAME_SIZE in *. lia.
Qed.

Lemma cl_cs : forall (r3 r2 : bvmap 5 word) r v, aregs_preserved r3 r2 -> acallee_saved r ->
  getr r3 (Z_to_bv 5 r) = v -> getr r2 (Z_to_bv 5 r) = v.
Proof. intros r3 r2 r v HP Hr E. rewrite (HP r Hr). exact E. Qed.

Lemma cl_s_not_rdset : forall cx h a, d_geo cx h -> off_img (d_FB cx) (fs_frame_bytes DFRAME_CLASS) ->
  d_FB cx + 2960 <= a < d_FB cx + 3016 -> ~ d_objr cx OLOCK a -> ~ d_rdset B cx h a.
Proof.
intros cx h a G Ho Ha Hnl Hr. pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite cl_fs6 in *.
unfold d_rdset in Hr.
destruct Hr as [H|[H|[H|[H|[H|[(Hn & H)|[(H & _)|Hcn]]]]]]].
- unfold d_objr, d_obj in H. cbn [dobj_off dobj_size] in H. lia.
- unfold d_objr, d_obj in H. cbn [dobj_off dobj_size] in H. lia.
- exact (Hnl H).
- unfold d_objr, d_obj in H. cbn [dobj_off dobj_size] in H. lia.
- unfold HUNT_SIZE in *. lia.
- destruct (G8 Hn) as (_ & _ & G9 & _). lia.
- exact (cl_off_not_img (d_FB cx) 4096 a Ho ltac:(lia) (cl_roP_img a H)).
- exact (cl_off_not_img (d_FB cx) 4096 a Ho ltac:(lia) (proj1 (cl_canary_img a Hcn))).
Qed.

Definition cl_L1_stmt : Prop := forall cx h i n now op nb fr len W c,
  cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c -> op mod 4 = 0 -> nb <= c_n cx ->
  SRr SEGS W c (cl_R cx h i n now op nb fr len 0xec0).
Definition cl_L2_stmt : Prop := forall cx h i n now op nb fr len W c,
  cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c -> op mod 4 = 1 -> nb <= c_n cx ->
  SRr SEGS W c (cl_R cx h i n now op nb fr len 0xed8).
Definition cl_L3_stmt : Prop := forall cx h i n now op nb fr len W c,
  cl_R cx h i n now op nb fr len 0xec0 W c -> SRr SEGS W c (cl_R cx h i n now op nb fr len 0xed8).
Definition cl_L4_stmt : Prop := forall cx h i n now op nb fr len W c,
  cl_R cx h i n now op nb fr len 0xed8 W c ->
  SRr SEGS W c (fun W' c' => r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len W' c' \/
    cl_CSR cx h i n now op nb fr len W' c').
Definition cl_L5_stmt : Prop := forall cx h i n now op nb fr len W c,
  cl_CSR cx h i n now op nb fr len W c -> SRr SEGS W c (cl_GR cx h i n now op nb fr len).
Definition cl_L6_stmt : Prop := forall cx h i n now op nb fr len W c,
  cl_GR cx h i n now op nb fr len W c ->
  SRr SEGS W c (fun W' c' => cl_X cx h i n now op nb fr len W' c' \/ exists nn, cl_LI cx h i n now op nb fr len nn 0 W' c').
Definition cl_L7_stmt : Prop := forall cx h i n now op nb fr len nn k W c,
  cl_LI cx h i n now op nb fr len nn k W c ->
  SRr SEGS W c (fun W' c' => cl_X cx h i n now op nb fr len W' c' \/ cl_LJ cx h i n now op nb fr len nn k (k + 1) W' c').
Definition cl_L8_stmt : Prop := forall cx h i n now op nb fr len nn k j W c,
  cl_LJ cx h i n now op nb fr len nn k j W c -> SRr SEGS W c (cl_BR cx h i n now op nb fr len nn k j).
Definition cl_L9_stmt : Prop := forall cx h i n now op nb fr len nn k j W c,
  cl_BR cx h i n now op nb fr len nn k j W c ->
  SRr SEGS W c (fun W' c' => cl_LJ cx h i n now op nb fr len nn k (j + 1) W' c' \/
    cl_LI cx h i n now op nb fr len nn (k + 1) W' c' \/ cl_X cx h i n now op nb fr len W' c').
Definition cl_loop_stmt : Prop := forall cx h i n now op nb fr len nn k W c,
  cl_LI cx h i n now op nb fr len nn k W c -> SRr SEGS W c (cl_X cx h i n now op nb fr len).
Definition cl_L10_stmt : Prop := forall cx h i n now op nb fr len W c,
  cl_X cx h i n now op nb fr len W c -> SRr SEGS W c (cl_post cx h i n now op nb fr len).

Lemma cl_in_op : forall cx h i n now op nb fr len W c, cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c ->
  op mod 4 = 0 \/ op mod 4 = 1.
Proof.
intros cx h i n now op nb fr len W c H. unfold cls_in, d_arm_at_pf, d_at in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFRM0 & Hb & HJ & Hfr & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (_ & _ & _ & _ & _ & (Hop & _) & _). exact Hop.
Qed.

Lemma cl_in_nb : forall cx h i n now op nb fr len W c,
  cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c -> nb <= c_n cx.
Proof.
intros cx h i n now op nb fr len W c H. unfold cls_in, d_arm_at_pf, d_at in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFRM0 & Hb & HJ & Hfr & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (_ & _ & _ & _ & _ & (_ & _ & (_ & _ & Hnb & _) & _) & _). exact Hnb.
Qed.

Theorem cl_compose :
  cl_L1_stmt -> cl_L2_stmt -> cl_L3_stmt -> cl_L4_stmt -> cl_L5_stmt -> cl_L6_stmt -> cl_loop_stmt -> cl_L10_stmt ->
  cls_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros L1 L2 L3 L4 L5 L6 LL L10. unfold cls_spec.
intros cx h i n now op nb fr len W c Hin.
assert (TAIL : forall W1 c1, cl_R cx h i n now op nb fr len 0xed8 W1 c1 ->
  SRr SEGS W1 c1 (cl_post cx h i n now op nb fr len)).
{ intros W1 c1 HR. eapply SRr_bind; [exact (L4 _ _ _ _ _ _ _ _ _ _ _ HR)|].
  intros W2 c2 _ [H27 | HCS]; [apply SRr_ret; right; exact H27|].
  eapply SRr_bind; [exact (L5 _ _ _ _ _ _ _ _ _ _ _ HCS)|]. intros W3 c3 _ HGR.
  eapply SRr_bind; [exact (L6 _ _ _ _ _ _ _ _ _ _ _ HGR)|]. intros W4 c4 _ [HX | (nn & HLI)].
  - exact (L10 _ _ _ _ _ _ _ _ _ _ _ HX).
  - eapply SRr_bind; [exact (LL _ _ _ _ _ _ _ _ _ _ _ _ _ HLI)|]. intros W5 c5 _ HX.
    exact (L10 _ _ _ _ _ _ _ _ _ _ _ HX). }
pose proof (cl_in_nb _ _ _ _ _ _ _ _ _ _ _ Hin) as Hnb.
destruct (cl_in_op _ _ _ _ _ _ _ _ _ _ _ Hin) as [H0 | H1].
- eapply SRr_bind; [exact (L1 _ _ _ _ _ _ _ _ _ _ _ Hin H0 Hnb)|]. intros W1 c1 _ HR.
  eapply SRr_bind; [exact (L3 _ _ _ _ _ _ _ _ _ _ _ HR)|]. intros W2 c2 _ HR2. exact (TAIL W2 c2 HR2).
- eapply SRr_bind; [exact (L2 _ _ _ _ _ _ _ _ _ _ _ Hin H1 Hnb)|]. intros W1 c1 _ HR. exact (TAIL W1 c1 HR).
Qed.

End h.
End f.
End d.

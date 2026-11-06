(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 568 of its 627 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntClsCuts.v, with its module paths and module names changed; 517 of its 574 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3FieldPFB.v, with its module paths, module names and numbers changed; 99 of its 580 lines of code are new or changed and 93 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnShared SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3FieldPFKit DiscoArm3FieldCall.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfb_ps : list pf_piece :=
  [Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02].
Definition pfb_args (T : list byte) (j : Z) : list pf_arg :=
  [AInt (pf_mb T j 0); AInt (pf_mb T j 1); AInt (pf_mb T j 2); AInt (pf_mb T j 3); AInt (pf_mb T j 4);
   AInt (pf_mb T j 5)].
Definition pfb_rs : smem := [YP09.mkRegion (Some 9%nat) 408 416 0 0 [YP09.mkChunk 408 (CVal 8 (SOff 33 0))]].

Lemma pfb_parse : pf_parse a3f_fmt_mac = Some pfb_ps.
Proof. reflexivity. Qed.

Lemma pfb_hex2 : forall v, 0 <= v < 256 -> pf_hex2 v = disco_json_text.hex2 v.
Proof.
  intros v Hv.
  assert (A : forallb (fun k => if list_eq_dec Z.eq_dec (pf_hex2 (Z.of_nat k)) (disco_json_text.hex2 (Z.of_nat k))
                                then true else false) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A (Z.to_nat v) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in A by lia. destruct (list_eq_dec Z.eq_dec _ _); [assumption | discriminate].
Qed.

Lemma pfb_mb_range : forall T j k, 0 <= pf_mb T j k < 256.
Proof.
  intros T j k. unfold pf_mb.
  destruct (Nat.lt_ge_cases (Z.to_nat (48 * (j - 1) + k)) (length T)) as [Hl|Hl].
  - rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hl). rewrite map_nth.
    pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (48 * (j - 1) + k)) T (Z_to_bv 8 0))) as Hr.
    change (bv_modulus 8) with 256 in Hr. exact Hr.
  - rewrite nth_overflow by (rewrite length_map; exact Hl). lia.
Qed.

Lemma pfb_nth_firstn : forall (l : list Z) n k, (k < n)%nat -> nth k (firstn n l) 0 = nth k l 0.
Proof.
  induction l as [|x l IH]; intros n k Hk.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma pfb_nth_skipn : forall (l : list Z) a k, nth k (skipn a l) 0 = nth (a + k) l 0.
Proof.
  induction l as [|x l IH]; intros a k.
  - rewrite skipn_nil. rewrite !nth_overflow by (cbn; lia). reflexivity.
  - destruct a as [|a]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma pfb_nth_mac : forall (T : list byte) j (k : nat), (k < 6)%nat -> 1 <= j ->
  nth k (map bv_unsigned (disco_table_c.mac_of T (j - 1))) 0 = pf_mb T j (Z.of_nat k).
Proof.
  intros T j k Hk Hj. unfold disco_table_c.mac_of, disco_table_c.sub, pf_mb.
  rewrite <- firstn_map, <- skipn_map. rewrite pfb_nth_firstn by exact Hk. rewrite pfb_nth_skipn.
  f_equal. lia.
Qed.

Lemma pfb_text : forall T j, 1 <= j -> pf_text pfb_ps (pfb_args T j) = Some (pf_mtext T j).
Proof.
  intros T j Hj. unfold pfb_ps, pfb_args, pf_mtext, disco_json_text.mac_text.
  unfold reac_disco_table_json_c.tj_entry. cbn [disco_json_text.e_mac].
  rewrite !pfb_nth_mac by lia. cbn [pf_text option_map].
  rewrite !pfb_hex2 by apply pfb_mb_range. reflexivity.
Qed.

Lemma pfb_mtext_len : forall T j, length (pf_mtext T j) = 17%nat.
Proof. intros T j. reflexivity. Qed.

Lemma pfb_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.

Lemma pfb_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os -> length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, pfb_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Lemma pfb_rdword : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  assert (H0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma pfb_chunk_in : forall r c, In c (YP09.r_chunks r) -> region_wf r = true ->
  YP09.r_lo r <= YP09.c_off c /\ YP09.c_off c + c_len c <= YP09.r_hi r.
Proof.
  intros r c Hin Hwf. unfold region_wf in Hwf. apply andb_prop in Hwf as [_ Hcs].
  pose proof (proj1 (forallb_forall _ _) Hcs c Hin) as X. unfold chunk_inside in X.
  apply andb_prop in X as [X _]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}
  {POV : PAObjVal lib_both3_0_listing (PI := PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfb_aview_some : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

Lemma pfb_region_tr : forall (E : env) H (m m' : word -> option byte) (r : YP09.region),
  region_ok SEGS E (mrestrict H m) r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < c_len c ->
     aview SEGS H m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     aview SEGS H m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall a, apresent H m a -> apresent H m' a) ->
  region_ok SEGS E (mrestrict H m') r.
Proof.
  intros E H m m' r (B1 & B2 & Wr & C) Hc Hp. split; [exact B1|]. split; [exact B2|]. split.
  - intros o Ho. apply (writable_kept H m m'); [apply Hp | exact (Wr o Ho)].
  - apply Forall_forall. intros c Hin i Hi. destruct (proj1 (Forall_forall _ _) C c Hin i Hi) as (b & Hb1 & Hb2).
    exists b. split; [exact Hb1|]. rewrite (mbyte_of_aview SEGS H H m m' _ (Hc c i Hin Hi)). exact Hb2.
Qed.

Lemma pfb_frame_tr : forall (cx : dcx) h shf (W : world SEGS) (m m' : word -> option byte) (K : Z -> Prop),
  d_frame cx h shf W m ->
  (forall a, K a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  (forall a, d_S cx - 104 <= a < d_S cx -> K a) ->
  (forall a, d_A cx <= a < d_A cx + 472 -> K a) ->
  (forall a, d_FB cx <= a < d_FB cx + 24 -> K a) ->
  (forall a, d_FB cx + 4088 <= a < d_FB cx + 4096 -> K a) ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 -> K a) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 47 ->
  d_frame cx h shf W m'.
Proof.
  intros cx h shf W m m' K (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264)
    HK Hp K2 K60 K516 KFL KSH HA HF.
  exists E. split; [exact HE|].
  pose proof HE as (EE & _ & _ & E60 & EF & ESH).
  assert (B2 : base_val E (Some AT_STK) = d_S cx).
  { cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (B60 : base_val E (Some AT_A) = d_A cx).
  { cbn [base_val]. rewrite E60. unfold w64. apply unsigned_lit_small. lia. }
  assert (B516 : base_val E (Some AT_F) = d_FB cx).
  { cbn [base_val]. rewrite EF. unfold w64. apply unsigned_lit_small. lia. }
  assert (B529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  unfold d_regions in HREG |- *.
  apply Forall_cons_iff in HREG as [R2 HREG]. apply Forall_cons_iff in HREG as [R60 HREG].
  apply Forall_cons_iff in HREG as [R516 HREG]. apply Forall_cons_iff in HREG as [R529 _].
  split.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    - apply (pfb_region_tr E (w_H W) m m' _ R2); [|exact Hp]. intros c i Hin Hi. apply HK.
      pose proof (pfb_chunk_in _ c Hin ltac:(vm_compute; reflexivity)) as Hc.
      cbn [YP09.r_lo YP09.r_hi YP09.r_base] in Hc |- *. rewrite B2. apply K2. lia.
    - apply (pfb_region_tr E (w_H W) m m' _ R60); [|exact Hp]. intros c i Hin Hi. apply HK.
      pose proof (pfb_chunk_in _ c Hin ltac:(vm_compute; reflexivity)) as Hc.
      cbn [YP09.r_lo YP09.r_hi YP09.r_base] in Hc |- *. rewrite B60. apply K60. lia.
    - apply (pfb_region_tr E (w_H W) m m' _ R516); [|exact Hp]. intros c i Hin Hi. apply HK.
      cbn [YP09.r_chunks YP09.r_base In] in Hin |- *. rewrite B516.
      destruct Hin as [<-|[<-|[<-|[]]]]; cbn in Hi |- *; apply K516; lia.
    - apply (pfb_region_tr E (w_H W) m m' _ R529); [|exact Hp]. intros c i Hin Hi. apply HK.
      unfold fshadow_region in Hin |- *. cbn [YP09.r_chunks YP09.r_base] in Hin |- *. rewrite B529.
      unfold dsh_chunks in Hin. apply in_map_iff in Hin as (kk & <- & Hkk). apply in_seq in Hkk.
      change (Z.to_nat DFRAME_SH) with 384%nat in Hkk. cbn in Hi |- *. apply KSH. lia. }
  assert (KVM : forall off v, 0 <= off -> off + 8 <= 472 ->
    val_mem SEGS (rd W m) (d_A cx + off) 8 v -> val_mem SEGS (rd W m') (d_A cx + off) 8 v).
  { intros off v H0 H1 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact Hv].
    intros kk Hkk. apply HK. apply K60. change (Z.of_nat 8) with 8 in Hkk. lia. }
  split.
  { rewrite <- HFLAG. apply pfb_rdword. intros i Hi. apply HK. apply KFL.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  split; [apply KVM; [lia | lia | exact V184]|].
  split; [apply KVM; [lia | lia | exact V120]|].
  split; [apply KVM; [lia | lia | exact V136]|].
  split; [apply KVM; [lia | lia | exact V376]|].
  split; [apply KVM; [lia | lia | exact V280]|].
  split; [apply KVM; [lia | lia | exact V232]|].
  apply KVM; [lia | lia | exact V264].
Qed.

Lemma pfb_shadow_tr : forall (cx : dcx) shf (W : world SEGS) (m m' : word -> option byte) (K : Z -> Prop),
  d_shadow cx shf W m ->
  (forall a, K a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384 -> K a) ->
  d_shadow cx shf W m'.
Proof.
  intros cx shf W m m' K HS HK KSH kk Hkk. rewrite HK by (apply KSH; unfold DFRAME_SH in Hkk; lia).
  exact (HS kk Hkk).
Qed.

Lemma pfb_garr8_tr : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
  intros W m m' a l Hk Hg. apply (garr8_frame SEGS (rd W m)); [exact Hg|].
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hk. exact Hx.
Qed.

Lemma pfb_vm_tr : forall (W : world SEGS) (m m' : word -> option byte) a (nn : nat) v,
  (forall x, a <= x < a + Z.of_nat nn -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rd W m) a nn v -> val_mem SEGS (rd W m') a nn v.
Proof.
  intros W m m' a nn v Hk Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact Hv].
  intros kk Hkk. apply Hk. lia.
Qed.

Lemma pfb_garr8_out : forall (W : world SEGS) (m : word -> option byte) d (T : list Z),
  (forall i, 0 <= i < Z.of_nat (length T) -> aview SEGS (w_H W) m (d + i) = Some (nth (Z.to_nat i) T 0)) ->
  aview SEGS (w_H W) m (d + Z.of_nat (length T)) = Some 0 ->
  garr8 SEGS (rd W m) d (T ++ [0]).
Proof.
  intros W m d T Hb Hz jj Hjj. rewrite length_app in Hjj. cbn [length] in Hjj.
  destruct (Nat.lt_ge_cases jj (length T)) as [Hl|Hl].
  - rewrite app_nth1 by exact Hl.
    pose proof (Hb (Z.of_nat jj) ltac:(lia)) as Hv. rewrite Nat2Z.id in Hv.
    exact (YC88.val_mem1_of_aview SEGS (w_H W) m _ _ Hv).
  - assert (jj = length T) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    exact (YC88.val_mem1_of_aview SEGS (w_H W) m _ _ Hz).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASNPRINTF : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi FF_got_canary FF_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA AS___interceptor_trampoline_snprintf).
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis DBRT : d_body_rt_stmt B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis KGOT : ak_can_got tfib_K = FF_got_canary.
Hypothesis SNPRO : forall a, Exists (in_zr a) snp_cr -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis SNPUN : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Theorem a3f_pfb : pfB_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & R24 &
  (R1 & (R21 & R22 & R23 & R25 & R26) & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R27) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & ((HSL & Hj & H408 & HUSED) & H16)).
destruct HSL as (Hp & H368 & H360).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKS & HAWRF).
pose proof HCAN as (HCv & HCr & HCi).
pose proof DCAN as (AIL & KCAN).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as (Hceil0 & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HOFF.
pose proof HGEO as (_ & _ & Hh0 & Hhc & _ & _ & Hhf & Hinp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
assert (HFB8 : 0 <= d_FB cx / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (Esn : SNPRINTF_STK = 11776) by reflexivity.
assert (Eom : d_obj cx OMAC = d_FB cx + 1728) by reflexivity.
assert (Eoo : d_obj cx OO = d_FB cx + 240) by reflexivity.
assert (Eot : d_obj cx OT = d_FB cx + 2160) by reflexivity.
assert (Eou : d_obj cx OUSED = d_FB cx + 1664) by reflexivity.
assert (SpR : spZ regs = d_A cx - 16) by (rewrite Rsp; lia).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 _ _ _ _ HAR3 Hinb HFin3) as Hbf.
rewrite EFA3 in Hbf. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hbf. unfold zdisjoint in Hbf. cbn [fst snd] in Hbf.
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LO : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os))) <= 1296).
{ rewrite length_map, (pfb_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (LU : length (a3f_used p) = 32%nat) by (unfold a3f_used; reflexivity).
replace (BASE + (SIGMA AS___interceptor_trampoline_snprintf - BASE)) with (SIGMA AS___interceptor_trampoline_snprintf)
  by ring.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hhf, Hinp. unfold HUNT_SIZE in Hhf, Hhc.
assert (Hsh : shadow_addr (d_FB cx) = 2147450880 + d_FB cx / 8) by reflexivity.
assert (Hm5 : 0 <= pf_mb T1 j 5 < 2 ^ 64) by (pose proof (pfb_mb_range T1 j 5); lia).
assert (HDC : dimg_consts W mem3) by exact (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HIMG).
pose proof HDC as (_ & _ & _ & HSTR & _).
pose proof HSTR as (_ & _ & _ & _ & _ & _ & (TS10 & _) & _).
pose proof TS10 as (_ & GF10 & Hf0 & _ & _ & AM10 & RA10 & SH10 & _ & IMG10).
pose proof (pa_img_range _ (IMG10 (VAL (A_OBJ 10)) ltac:(cbn [length Z.of_nat]; lia))) as If0.
pose proof (pa_img_range _ (IMG10 (VAL (A_OBJ 10) + 29) ltac:(cbn [length Z.of_nat]; lia))) as If1.
pose proof (pa_img_range _ (HCi FF_canary ltac:(lia))) as Ifc.
assert (HFMT : SnShared.fmt_at (aview SEGS (w_H W) mem3) (SnShared.snp_out SNPRINTF_STK (spZ regs) (d_obj cx OMAC) 18)
  (VAL (A_OBJ 10)) a3f_fmt_mac).
{ assert (L30 : Z.of_nat (length a3f_fmt_mac) + 1 = 30) by reflexivity.
  unfold SnShared.fmt_at. split; [exact Hf0|]. split.
  - intros ii Hii. change (Z.of_nat (length a3f_fmt_mac)) with 29 in Hii.
    destruct (GF10 (Z.to_nat ii) ltac:(rewrite length_app; cbn [length]; lia)) as (Hv & Hr).
    rewrite Z2Nat.id in Hv by lia. exact (aview_of_val_mem1 SEGS (w_H W) mem3 _ _ Hv Hr).
  - split; [|split; [exact AM10 | split; [exact RA10 | exact SH10]]].
    unfold SnShared.snp_out. rewrite Esn, SpR, L30.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd].
    + unfold IMG_LO, IMG_TOP in *. lia.
    + unfold off_img in HOFF. rewrite Eom. unfold IMG_LO, IMG_TOP in *. lia. }
assert (HRA : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (d_obj cx OMAC) 18).
{ intros x Hx. rewrite Eom in Hx. unfold shadow_of_addr.
  assert (Hq : (x / 8 = d_FB cx / 8 + 216 \/ x / 8 = d_FB cx / 8 + 217) \/
               (x / 8 = d_FB cx / 8 + 218 /\ x mod 8 < 2)) by lia.
  destruct Hq as [[Hq|Hq] | (Hq & Hm)].
  - exists 0. split; [|left; reflexivity]. rewrite Hq.
    replace (SHADOW_OFF + (d_FB cx / 8 + 216)) with (shadow_addr (d_FB cx) + 216) by (rewrite Hsh; unfold SHADOW_OFF; lia).
    rewrite (HSHD 216 ltac:(unfold DFRAME_SH; lia)). reflexivity.
  - exists 0. split; [|left; reflexivity]. rewrite Hq.
    replace (SHADOW_OFF + (d_FB cx / 8 + 217)) with (shadow_addr (d_FB cx) + 217) by (rewrite Hsh; unfold SHADOW_OFF; lia).
    rewrite (HSHD 217 ltac:(unfold DFRAME_SH; lia)). reflexivity.
  - exists 2. split; [|right; lia]. rewrite Hq.
    replace (SHADOW_OFF + (d_FB cx / 8 + 218)) with (shadow_addr (d_FB cx) + 218) by (rewrite Hsh; unfold SHADOW_OFF; lia).
    rewrite (HSHD 218 ltac:(unfold DFRAME_SH; lia)). reflexivity. }
assert (HSV : shadow_hull_vis (aview SEGS (w_H W) mem3) (d_obj cx OMAC) 18).
{ intros s Hs. rewrite Eom in Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by (rewrite Hsh; lia).
  apply pfb_aview_some. apply GFsh. rewrite Hsh. lia. }
assert (HAMR : amem_range (d_obj cx OMAC) (18 + 8)).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. rewrite Eom. lia. }
assert (V10 : VAL (A_OBJ 10) = 0x20f80)
  by (rewrite (pa_obj_val (PI := PI) 10%nat) by (unfold tfib_nobj; lia); reflexivity).
eapply SRr_bind.
{ eapply (aj_snprintf_at B LAWS ASNPRINTF fq W regs mem3 _ _ _ _ _ _ _ _ _ ly3 S3 md3 k
    (d_obj cx OMAC) 18 (VAL (A_OBJ 10)) a3f_fmt_mac pfb_ps [pf_mb T1 j 5]
    (map (argZ regs) [3; 4; 5; 6; 7] ++ [pf_mb T1 j 5]) (pfb_args T1 j) (pf_mtext T1 j) (d_A cx - 16 - d_S cx)
    HJ HFRM0 R10 R11 R12).
  - rewrite SpR. lia.
  - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
    rewrite GA32 in DA. rewrite GS16 in DS.
    replace (d_A cx - 16 - d_S cx) with ((2 * (d_A cx / 32) - 1 - d_S cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - rewrite Esn. unfold LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold PFR1_OFF; lia | reflexivity].
  - apply (snp_ctx_ok B).
    + exact SNPRO.
    + exact SNPUN.
    + exact HIMG.
    + exact (snp_can_of B tfib_K AIL KGOT KCAN ly3 S3 W mem3 md3 (c_canary cx) HAR3 HCv HCr).
    + unfold off_img, IMG_LO, IMG_TOP. rewrite Esn, SpR. lia.
    + unfold off_img in HOFF |- *. rewrite Eom. lia.
  - exact HFMT.
  - exact pfb_parse.
  - unfold pfb_ps. repeat (apply Forall_cons; [exact I|]). apply Forall_nil.
  - rewrite V10. unfold disco_fmt_lo. lia.
  - rewrite V10. change (Z.of_nat (length a3f_fmt_mac)) with 29. unfold disco_fmt_hi. lia.
  - unfold a3f_fmt_mac. discriminate.
  - split; [reflexivity|]. intros ii Hii. cbn [length] in Hii. assert (ii = 0%nat) as -> by lia.
    cbn [nth Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r, SpR. exact (rdword_of_val_mem SEGS (w_H W) mem3 _ _ H16 Hm5).
  - cbn [length Z.of_nat]. rewrite SpR.
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HS1 & HS2 & _) & _).
    lia.
  - unfold SnShared.snp_out. rewrite Esn, SpR. cbn [length Z.of_nat].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd]; rewrite ?Eom; lia.
  - unfold pfb_args. cbn [SnShared.pf_args_asan map app SnShared.pf_arg_asan].
    assert (HAI : forall (r : bv 5) kk, getr regs r = w64 (pf_mb T1 j kk) ->
      -2 ^ 31 <= pf_mb T1 j kk < 2 ^ 31 /\ bv_unsigned (getr regs r) mod 2 ^ 32 = pf_mb T1 j kk mod 2 ^ 32).
    { intros r kk Hr. rewrite Hr. pose proof (pfb_mb_range T1 j kk). unfold w64.
      rewrite unsigned_lit_small by lia. lia. }
    unfold argZ. cbn [Z.add].
    split; [exact (HAI _ 0 R13)|]. split; [exact (HAI _ 1 R14)|]. split; [exact (HAI _ 2 R15)|].
    split; [exact (HAI _ 3 R16)|]. split; [exact (HAI _ 4 R17)|]. split; [|exact I].
    pose proof (pfb_mb_range T1 j 5). lia.
  - exact I.
  - exact (pfb_text T1 j ltac:(lia)).
  - lia.
  - rewrite pfb_mtext_len. lia.
  - rewrite Eom. lia.
  - lia.
  - unfold SnShared.snp_out. rewrite Esn, SpR. cbn [pairwise].
    split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rewrite Eom; lia | apply Forall_nil]|].
    split; [apply Forall_nil | exact I].
  - intros a Ha. rewrite Eom in Ha. split.
    + apply (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia))).
    + rewrite Esn, SpR. lia.
  - exact HAMR.
  - exact HRA.
  - exact HSV.
  - exact HIMG. }
intros W2 c2 _ (-> & fx2 & regs2 & mem2 & md2 & -> & HFRMc & _ & HJ2 & HPR & Hsame & Hres & Heff & Hz & Hfr & Hpres2).
clear dependent fq. rename fx2 into fq. rename HFRMc into HFRM0.
rewrite pfb_mtext_len in Heff, Hz, Hfr. change (Z.min (Z.of_nat 17) (18 - 1)) with 17 in Heff, Hz, Hfr.
rewrite SpR, Esn in Hfr.
pose (K := fun a : Z => 0 <= a < 2 ^ 64 /\ ~ (d_obj cx OMAC <= a <= d_obj cx OMAC + 17) /\
  ~ (d_A cx - 16 - 11776 <= a < d_A cx - 16)).
assert (HK : forall a, K a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a (Ha & Hb & Hc). exact (Hfr a Ha Hb Hc). }
assert (KR : forall lo hi, 0 <= lo -> hi <= 2 ^ 64 -> (hi <= d_obj cx OMAC \/ d_obj cx OMAC + 18 <= lo) ->
  (hi <= d_A cx - 16 - 11776 \/ d_A cx - 16 <= lo) -> forall a, lo <= a < hi -> K a).
{ intros lo hi H1 H2 H3 H4 a Ha. unfold K. clear - H1 H2 H3 H4 Ha. lia. }
assert (HFRM2 : d_frame cx h dsh_mac W mem2).
{ apply (pfb_frame_tr cx h dsh_mac W mem3 mem2 K HFRM HK Hpres2); try (apply KR; rewrite ?Eom, ?Hsh; lia); lia. }
assert (HSHD2 : d_shadow cx dsh_mac W mem2).
{ apply (pfb_shadow_tr cx dsh_mac W mem3 mem2 K HSHD HK). apply KR; rewrite ?Eom, ?Hsh; lia. }
assert (HBODY2 : d_body B cx h n (a3_xb buf op) dsh_mac ly3 S3 W mem2).
{ apply (DBRT cx h n n (a3_xb buf op) dsh_mac dsh_mac ly3 S3 W mem3 mem2 (d_A cx - 16 - 11776) (d_A cx - 16)
    (fun a => (d_A cx - 16 - 11776 <= a < d_A cx - 16) \/ d_objr cx OMAC a) HBODY).
  - unfold LLVMF_STK. lia.
  - lia.
  - intros a [Ha|Ha]; [left; exact Ha|right].
    unfold d_objr in Ha. rewrite Eom in Ha. cbn [dobj_size] in Ha.
    unfold d_rdset, d_objr. intros [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
    + unfold d_obj, dobj_off, dobj_size in Hr. lia.
    + unfold d_obj, dobj_off, dobj_size in Hr. lia.
    + unfold d_obj, dobj_off, dobj_size in Hr. lia.
    + unfold d_obj, dobj_off, dobj_size in Hr. lia.
    + unfold HUNT_SIZE in Hr. lia.
    + destruct Hr as (Hcn & Hr). destruct (Hinp Hcn) as (_ & _ & Hpf & _). lia.
    + assert (Hro : in_roP SEGS pa_relro_lo pa_relro_hi a) by (first [exact Hr | exact (proj1 Hr)]).
      destruct Hro as [(sg & Hsg & _ & Hsr) | Hrr].
      * pose proof (pa_img_range a (ex_intro _ sg (conj Hsg Hsr))) as Hi'. unfold off_img in HOFF. lia.
      * pose proof (pa_img_range a (pa_relro_img a Hrr)) as Hi'. unfold off_img in HOFF. lia.
    + pose proof (pa_img_range a (HCi a Hr)) as Hi'. unfold off_img in HOFF. lia.
  - intros a Ha HnR. apply Hfr; [exact Ha | |].
    + intros Hd. apply HnR. right. unfold d_objr. cbn [dobj_size]. lia.
    + intros Hw. apply HnR. left. exact Hw.
  - intros a _ Hpa. exact (Hpres2 a Hpa).
  - exact HFRM2.
  - exact HSHD2.
  - lia. }
assert (KV : forall a (nn : nat) v, (forall x, a <= x < a + Z.of_nat nn -> K x) ->
  val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W mem2) a nn v).
{ intros a nn v Hx Hv. apply (pfb_vm_tr W mem3 mem2 a nn v); [|exact Hv]. intros x Hx'. apply HK. apply Hx. exact Hx'. }
assert (KG : forall a l, (forall x, a <= x < a + Z.of_nat (length l) -> K x) ->
  garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W mem2) a l).
{ intros a l Hx Hg. apply (pfb_garr8_tr W mem3 mem2 a l); [|exact Hg]. intros x Hx'. apply HK. apply Hx. exact Hx'. }
pose proof HSP1 as ((H208 & H320) & H192 & H200).
assert (V408 : val_mem SEGS (rd W mem2) (d_A cx + 408) 8 (d_obj cx OO + 144 * p))
  by (apply KV; [apply KR; lia | exact H408]).
assert (HY2 : garr8 SEGS (rd W mem2) (d_obj cx OMAC) (pf_mtext T1 j ++ [0])).
{ apply pfb_garr8_out; rewrite pfb_mtext_len; [exact Heff | exact Hz]. }
assert (P2 : getr regs2 2 = getr regs 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr regs 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr regs 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr regs 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr regs 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr regs 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regs 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr regs 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr regs 22) by exact (HPR 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23 = getr regs 23) by exact (HPR 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr regs 24) by exact (HPR 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr regs 25) by exact (HPR 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr regs 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27 = getr regs 27) by exact (HPR 27 ltac:(unfold acallee_saved; lia)).
rewrite R1. unfold w64.
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
remember (Eimg (Ereg regs2 [Z_to_bv 64 SB; Z_to_bv 64 (d_obj cx OO + 144 * p)])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs2 r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (E33 : ew E0 33 = Z_to_bv 64 (d_obj cx OO + 144 * p)).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (U9 : bv_unsigned (ew E0 9) = d_A cx).
{ rewrite (EE0 9%nat 9%bv eq_refl), P9, Rs1. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 (mkSS PFR1_OFF sr_atoms pfb_rs None (mkFacts [] [] []))
  (restrict (w_H W) (YK11.mkst (fx := fq) regs2 (Z_to_bv 64 (BASE + PFR1_OFF)) mem2 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - unfold pfb_rs. apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E0 _ (d_A cx) 408 8%N (SOff 33 0) (d_obj cx OO + 144 * p)).
    + cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + exact V408.
  - unfold pfb_rs. split; exact I.
  - split; [exact I | split; exact I]. }
reshok_bx HS 32%nat.
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ lazymatch goal with |- awr_ok ?E ?rs ?a ?b ?c ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' a b c d e f g) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (Emem : ms_mem ms = mem2).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hr & Hw).
  cbn [ss_mem] in Hr. unfold pfb_rs in Hr. cbn [In] in Hr. destruct Hr as [<- | []]. cbn in Hw. lia. }
pmkst HS.
rewrite Emem. rewrite Emem in HJ2.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
rewrite pa_sigma_jtok_is.
assert (G1 : getr (ms_regs ms) 1 = w64 (BASE + PFR2_OFF)) by (rewrite Q1; reflexivity).
assert (G2 : getr (ms_regs ms) 2 = w64 (d_A cx)).
{ rewrite Q2, (EE0 2%nat 2%bv eq_refl), P2. unfold w64. f_equal.
  change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite SpR. lia. }
assert (G3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite Q3, (EE0 3%nat 3%bv eq_refl); exact P3).
assert (G4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite Q4, (EE0 4%nat 4%bv eq_refl); exact P4).
assert (G8 : getr (ms_regs ms) 8 = getr regs 8) by (rewrite Q8, (EE0 8%nat 8%bv eq_refl); exact P8).
assert (G9 : getr (ms_regs ms) 9 = getr regs 9) by (rewrite Q9, (EE0 9%nat 9%bv eq_refl); exact P9).
assert (G18 : getr (ms_regs ms) 18 = getr regs 18) by (rewrite Q18, (EE0 18%nat 18%bv eq_refl); exact P18).
assert (G19 : getr (ms_regs ms) 19 = getr regs 19) by (rewrite Q19, (EE0 19%nat 19%bv eq_refl); exact P19).
assert (G20 : getr (ms_regs ms) 20 = getr regs 20) by (rewrite Q20, (EE0 20%nat 20%bv eq_refl); exact P20).
assert (G21 : getr (ms_regs ms) 21 = getr regs 21) by (rewrite Q21, (EE0 21%nat 21%bv eq_refl); exact P21).
assert (G22 : getr (ms_regs ms) 22 = getr regs 22) by (rewrite Q22, (EE0 22%nat 22%bv eq_refl); exact P22).
assert (G23 : getr (ms_regs ms) 23 = getr regs 23) by (rewrite Q23, (EE0 23%nat 23%bv eq_refl); exact P23).
assert (G24 : getr (ms_regs ms) 24 = getr regs 24) by (rewrite Q24, (EE0 24%nat 24%bv eq_refl); exact P24).
assert (G25 : getr (ms_regs ms) 25 = getr regs 25) by (rewrite Q25, (EE0 25%nat 25%bv eq_refl); exact P25).
assert (G26 : getr (ms_regs ms) 26 = getr regs 26) by (rewrite Q26, (EE0 26%nat 26%bv eq_refl); exact P26).
assert (G10 : getr (ms_regs ms) 10 = w64 (d_obj cx OO + 144 * p)) by (rewrite Q10, E33; reflexivity).
assert (G11 : getr (ms_regs ms) 11 = w64 1) by (rewrite Q11; reflexivity).
assert (G12 : getr (ms_regs ms) 12 = w64 (d_obj cx OMAC)).
{ rewrite Q12, (EE0 27%nat 27%bv eq_refl), P27. exact R27. }
apply SRr_ret.
unfold pf_c2, a3f_stg. split; [exact Hfrom|].
unfold d_at.
exists fq, ly3, S3, (ms_regs ms), mem2, (with_vm_backing (m_vm_lazy md2) mat md2), k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact HFRM0|].
split; [exact HBASE|]. split; [exact HJ2|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rLs. split; [unfold spZ; rewrite G2; unfold w64; rewrite unsigned_lit_small by lia; lia|].
  split; [rewrite G3; exact Rgp|]. split; [rewrite G4; exact Rtp|]. split; [rewrite G8; exact Rs0|].
  split; [rewrite G9; exact Rs1|]. split; [rewrite G19; exact Rs19|]. split; [rewrite G18; exact Rs18|].
  rewrite G20; exact Rs20. }
split; [rewrite G24; exact R24|].
split.
{ cbv beta. split; [exact G1|].
  split; [unfold pf_Rj; rewrite G21, G22, G23, G25, G26; exact (conj R21 (conj R22 (conj R23 (conj R25 R26))))|].
  split; [exact G10|]. split; [exact G11 | exact G12]. }
split.
{ cbv beta. split; [split; [split | split] |].
  - apply KV; [apply KR; lia | exact H208].
  - apply KV; [apply KR; lia | exact H320].
  - apply KV; [apply KR; lia | exact H192].
  - apply KV; [apply KR; lia | exact H200].
  - split; [split; [exact (proj1 HTAB)|]|].
    + apply KG; [|exact HGT]. apply KR; rewrite ?length_map, ?HLT1, ?Eot, ?Eom; lia.
    + split; [split; [exact Hr2|]|].
      * apply KG; [|exact HGB]. apply KR; rewrite ?Lb, ?Eom; lia.
      * split; [exact HJR|]. split; [exact HVP|]. split.
        -- apply KG; [|exact HOO]. apply KR; rewrite ?Eoo, ?Eom; lia.
        -- split; [|exact HY2].
           split; [split; [exact Hp|]; split|].
           ++ apply KV; [apply KR; lia | exact H368].
           ++ apply KV; [apply KR; lia | exact H360].
           ++ split; [exact Hj|]. split; [exact V408|].
              apply KG; [|exact HUSED]. apply KR; rewrite ?LU, ?Eou, ?Eom; lia. }
split.
{ split.
  - apply KV; [apply KR; lia | exact H208].
  - apply KV; [apply KR; lia | exact H320]. }
exact HBODY2.
Qed.

End h.
End f.
End d.

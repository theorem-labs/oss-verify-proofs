(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 885 of its 952 lines of code are new or changed and 3943 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3AgeCall2.v; 462 of its 555 lines of code are new or changed and 859 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YC88 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require ConstsViewDef SetShadowDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldCall.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require SbCh SbDec SbDecWalk ReacBoxName ReacBoxNameTop DiscoArm3FieldRbnFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_table reac_disco_table_json_c disco_json_reader_model slot_ser_defs disco_box_name_model
reac_box_name_c slot_ser_P1 slot_ser_P3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pfc_u1 : forall (T : list byte) (k : Z), 0 <= disco_table_c.u_at T k 1 < 256.
Proof.
  intros T k. unfold disco_table_c.u_at.
  pose proof (disco_table.ble_range (disco_table_c.sub T k 1)) as H.
  assert (HL : (length (disco_table_c.sub T k 1) <= 1)%nat).
  { unfold disco_table_c.sub. rewrite length_firstn. lia. }
  assert (HP : 2 ^ (8 * Z.of_nat (length (disco_table_c.sub T k 1))) <= 2 ^ 8).
  { apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma pfc_nn : forall x y : option Z, ~ x <> y -> x = y.
Proof.
  intros [x|] [y|] H; try reflexivity; try (exfalso; apply H; discriminate).
  destruct (Z.eq_dec x y) as [->|Hn]; [reflexivity|].
  exfalso. apply H. intros E. injection E as E. exact (Hn E).
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi} {PX : PAXcalls lib_both3_0_listing}
  {PO : PAObjImg lib_both3_0_listing} {POV : PAObjVal lib_both3_0_listing (PI := PI)}
  {PR : PARoPresent lib_both3_0_listing}.

Lemma pfc_roimg : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hg)].
Qed.

Lemma pfc_rbnw : forall (cx : dcx) f i o a,
  ReacBoxName.rbn_wr f [] i o (d_obj cx ONM) 24 (d_obj cx OTOK) 24 (d_obj cx ODISP) 48 a ->
  d_FB cx + 1792 <= a < d_FB cx + 1968.
Proof.
  intros cx f i o a (Hacc & Hr). unfold reac_box_name_c.bn_accept in Hacc.
  apply andb_prop in Hacc as [Hacc H3]. apply andb_prop in Hacc as [Hacc H2]. apply andb_prop in Hacc as [_ H1].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  unfold d_obj in Hr. cbn [dobj_off] in Hr. lia.
Qed.

Lemma pfc_zero : forall (cx : dcx) (W : world SEGS) m c len,
  d_shadow cx dsh_md W m -> d_FB cx mod 8 = 0 -> c mod 8 = 0 -> len mod 8 = 0 -> 0 <= c ->
  c + len <= 8 * DFRAME_SH ->
  forallb (fun i => dsh_md (c / 8 + Z.of_nat i) =? 0) (seq 0 (Z.to_nat (len / 8))) = true ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + c) len.
Proof.
  intros cx W m c len HSH HF Hc Hl Hc0 Hcl Hz.
  apply zero_shadow_range; [lia | exact Hl |].
  intros i Hi.
  assert (E : shadow_of_addr SHADOW_OFF (d_FB cx + c) + i = shadow_addr (d_FB cx) + (c / 8 + i)).
  { unfold shadow_of_addr, shadow_addr. lia. }
  rewrite E. rewrite HSH by (unfold DFRAME_SH in *; lia).
  f_equal. apply Z.eqb_eq.
  rewrite forallb_forall in Hz. specialize (Hz (Z.to_nat i)). cbv beta in Hz.
  rewrite Z2Nat.id in Hz by lia. apply Hz. apply in_seq. lia.
Qed.

Lemma pfc_hull : forall (cx : dcx) (W : world SEGS) m shf c len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= d_FB cx -> 64 <= c -> 0 < len ->
  c + len + 64 <= 8 * DFRAME_SH ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_FB cx + c) len.
Proof.
  intros cx W m shf c len HSH HF HF0 Hc Hl Hcl s Hs.
  unfold shadow_addr in Hs.
  replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
  rewrite HSH; [discriminate|]. unfold shadow_addr, DFRAME_SH in *. lia.
Qed.

Lemma pfc_region_kept : forall E (m m' : word -> option byte) r (P : Z -> Prop),
  region_ok SEGS E m r ->
  (forall c, In c (YP09.r_chunks r) -> forall i, 0 <= i < YP09.c_len c -> P (YP09.c_off c + i)) ->
  (forall o, YP09.r_lo r <= o < YP09.r_hi r -> P o ->
     mbyte SEGS m' (base_val E (YP09.r_base r) + o) = mbyte SEGS m (base_val E (YP09.r_base r) + o)) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  forallb (YP09.chunk_inside r) (YP09.r_chunks r) = true ->
  region_ok SEGS E m' r.
Proof.
  intros E m m' r P HR HP Hk Hw Hin. unfold region_ok in HR |- *. cbv zeta in HR |- *.
  destruct HR as (H1 & H2 & _ & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact Hw|].
  apply Forall_forall. intros c Hc i Hi.
  pose proof (proj1 (forallb_forall _ _) Hin c Hc) as Hci. unfold YP09.chunk_inside in Hci.
  apply andb_prop in Hci as [Hci H03]. apply andb_prop in Hci as [H01 H02].
  apply Z.leb_le in H01. apply Z.leb_le in H02. apply Z.leb_le in H03.
  destruct (proj1 (Forall_forall _ _) H4 c Hc i Hi) as (b & Hb1 & Hb2).
  exists b. split; [exact Hb1|].
  replace (base_val E (YP09.r_base r) + YP09.c_off c + i)
    with (base_val E (YP09.r_base r) + (YP09.c_off c + i)) in Hb2 |- * by lia.
  rewrite Hk; [exact Hb2 | lia | exact (HP c Hc i Hi)].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  StrlenDef.astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis ASSF5 : forall fq : YK11.FPState,
  SetShadowDef.aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f5) 0xf5.
Hypothesis ASM3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASM0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DCRO : dimg_consts_of_ro_stmt B.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis DTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis MCRO : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_roP SEGS pa_relro_lo pa_relro_hi a.
Hypothesis MCUN : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

Lemma pfc_tbox : ReacBoxName.treac_box_name_spec B.
Proof.
  destruct DROH as (DRO & GM & HV).
  assert (MCIMG : forall a, ReacBoxName.MC_CONSTS_LO <= a < ReacBoxName.MC_CONSTS_HI -> in_img SEGS a)
    by (intros a Ha; exact (pfc_roimg a (MCRO a Ha))).
  assert (TSB : SbCh.tsb_ch_spec B) by (apply SbCh.pb_sb_ch; assumption).
  assert (HSBDEC : SbDec.tsb_dec_spec B) by (apply SbDecWalk.pb_sb_dec; assumption).
  apply ReacBoxNameTop.pb_reac_box_name; first [assumption | exact MCUN].
Qed.

Lemma pfc_input : forall cx, d_base B MT XM_LIB RLO RHI tfib_K cx -> 0 < c_n cx ->
  In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)).
Proof.
  intros cx ((_ & _ & _ & _ & Hin & _) & _) Hn. destruct Hin as [(E & _) | (_ & Hin)]; [lia | exact Hin].
Qed.

Lemma pfc_achain : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k E shf,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k -> d_E cx E ->
  Forall (region_ok SEGS E (rd W3 mem3)) (d_regions cx shf) ->
  exists ch, achain ly3 (aview SEGS (w_H W3) mem3) (d_A cx) (d_S cx) ch.
Proof.
  intros cx ly3 S3 W3 mem3 md3 k E shf HC HE HREG.
  pose proof HC as (HBASE & HJ & HFR).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k HC)
    as (GS16 & GSlo & GShi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof alloc_ceiling_value as Hceil0.
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
  unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
  pose proof HBASE as ((HPRE0 & _) & _).
  pose proof HPRE0 as (_ & _ & Hra40 & _ & _ & _ & _ & HCH0 & _).
  pose proof HPRE0 as (_ & _ & _ & _ & _ & HSTK0 & _).
  pose proof HSTK0 as (_ & _ & _ & _ & _ & HSHI0 & _ & _ & HTOP0).
  pose proof (proj1 (proj2 HJ)) as HLY.
  destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & LTOP & _).
  assert (GS8 : d_S cx mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16); [exists 2; reflexivity|].
    apply Z.mod_divide; [lia | exact GS16]. }
  assert (KTOP : forall a, d_S cx <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
  { intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). apply F1; [lia|]. unfold LLVMF_STK. lia. }
  assert (HCH3 : achain ly3 (aview SEGS (w_H W3) mem3) (d_S cx) (s0Z (c_regs cx)) []).
  { apply (achain_ly_top (c_ly cx) ly3); [exact LTOP|].
    apply (achain_kept (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) mem3)
      (d_S cx) (s0Z (c_regs cx)) [] (d_S cx) HCH0 ltac:(lia) ltac:(lia) KTOP). }
  pose proof HREG as HREGu. unfold d_regions in HREGu.
  pose proof (Forall_inv HREGu) as HRSTK.
  assert (ES2 : bv_unsigned (ew E 2) = d_S cx) by (rewrite (proj1 HE 2%nat 2%bv eq_refl); reflexivity).
  assert (Vra : val_mem SEGS (mrestrict (w_H W3) mem3) (d_S cx + -8) 8 (raZ (c_regs cx))).
  { apply (field_of_region E (mrestrict (w_H W3) mem3) AT_STK (d_S cx) dsave_chunks (-104) 0 0 0
      (-8) 8%N (SOff 1%nat 0) (raZ (c_regs cx)) HRSTK ES2).
    - vm_compute. tauto.
    - cbn [sv_denot]. rewrite (proj1 HE 1%nat 1%bv eq_refl), Z.add_0_r. reflexivity.
    - cbn. pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hq.
      change (bv_modulus 64) with (2 ^ 64) in Hq. unfold raZ. lia.
    - cbn. lia. }
  assert (Vs0 : val_mem SEGS (mrestrict (w_H W3) mem3) (d_S cx + -16) 8 (s0Z (c_regs cx))).
  { apply (field_of_region E (mrestrict (w_H W3) mem3) AT_STK (d_S cx) dsave_chunks (-104) 0 0 0
      (-16) 8%N (SOff 8%nat 0) (s0Z (c_regs cx)) HRSTK ES2).
    - vm_compute. tauto.
    - cbn [sv_denot]. rewrite (proj1 HE 8%nat 8%bv eq_refl), Z.add_0_r. reflexivity.
    - cbn. pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hq.
      change (bv_modulus 64) with (2 ^ 64) in Hq. unfold s0Z. lia.
    - cbn. lia. }
  destruct (Z_lt_ge_dec (d_S cx) (ly_top ly3 - 16)) as [Hlt | Hge].
  - exists [(d_S cx, raZ (c_regs cx), s0Z (c_regs cx))].
    apply (achain_push ly3 (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W3) mem3)
      (d_S cx) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] (d_A cx) HCH3 ltac:(lia) ltac:(reflexivity)).
    + replace (d_S cx - 8) with (d_S cx + -8) by lia.
      apply rdword_of_val_mem; [exact Vra|].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hq.
      change (bv_modulus 64) with (2 ^ 64) in Hq. unfold raZ. lia.
    + replace (d_S cx - 16) with (d_S cx + -16) by lia.
      apply rdword_of_val_mem; [exact Vs0|].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hq.
      change (bv_modulus 64) with (2 ^ 64) in Hq. unfold s0Z. lia.
    + exact Hra40.
    + lia.
    + exact GS8.
    + lia.
    + lia.
  - exists []. left. split; [right; left; lia | reflexivity].
Qed.

Lemma pfc_buf : forall cx ly3 S3 (W : world SEGS) mem3 md3 k sp c len,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_shadow cx dsh_md W mem3 ->
  (forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE ->
     awr_byte LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
       [(DFRAME_CLASS, c_fpos cx)] a /\ apresent (w_H W) mem3 a) ->
  d_S cx - LLVMF_STK + ReacBoxName.REAC_BOX_NAME_STK <= sp ->
  64 <= c -> c + len + 64 <= 3072 -> c mod 8 = 0 -> len mod 8 = 0 -> 0 < len ->
  forallb (fun i => dsh_md (c / 8 + Z.of_nat i) =? 0) (seq 0 (Z.to_nat (len / 8))) = true ->
  ReacBoxName.rbn_buf B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3
    sp (d_FB cx + c) len.
Proof.
  intros cx ly3 S3 W mem3 md3 k sp c len HC HSH HAW Hsp Hc Hcl Hc8 Hl8 Hl Hz.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
    as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & _).
  assert (RBNS : ReacBoxName.REAC_BOX_NAME_STK = 8816) by reflexivity.
  unfold LLVMF_STK in *. rewrite RBNS in Hsp.
  unfold ReacBoxName.rbn_buf.
  split; [lia|]. split; [lia|].
  split; [apply (amem_range_sub_app (d_FB cx) 4096); [exact GFapp | lia | lia | lia | lia]|].
  split; [right; rewrite RBNS; lia|].
  split; [apply pfc_zero; [exact HSH | lia | exact Hc8 | exact Hl8 | lia | unfold DFRAME_SH; lia | exact Hz]|].
  split; [apply (pfc_hull cx W mem3 dsh_md); [exact HSH | lia | lia | exact Hc | exact Hl | unfold DFRAME_SH; lia]|].
  intros a Ha. apply HAW. unfold DFRAME_SIZE. lia.
Qed.

Theorem a3f_pfc : forall p, 0 <= p < 8 -> seg_pfc_p_spec B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p _ cx h i n now op W0 c0 T0 T1 buf count os vpad W c (HFROM & HAT).
unfold d_at in HAT.
destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & R24 & (R1 & HBR & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & (HPYK & Hhd & HDISP & HDL & H352 & HWID)) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20).
pose proof HBR as (R21 & R22 & R23 & R25 & R26 & R27).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HBLK as (HPerm0 & _ & _ & _).
pose proof HTAB as ((removed & _ & Hpost) & _).
destruct Hpost as (LT1 & _ & _ & _ & _ & _ & TOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os LT1 TOK1 Hnow HJR) as (_ & Hc8 & Los & Hlen6 & _).
assert (HFB8 : d_FB cx mod 8 = 0) by lia.
assert (RBNS : ReacBoxName.REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (Hs0 : s0Z regs = d_S cx) by (unfold s0Z; rewrite Rs0; unfold w64; apply unsigned_lit_small; lia).
destruct (pfc_achain cx ly3 S3 W mem3 md3 k E dsh_md HCTX HE HREG) as (ch & HCH).
pose proof (DCRO LAWS DROH ly3 S3 W mem3 md3 HAR3 HIMG) as HDCN.
pose proof (DiscoArm3FieldRbnFacts.pfc_rbn_img_y2 B W mem3 DROH HDCN) as HRBN.
pose proof pa_B_ok as (PB0 & PB1 & _). pose proof (pa_base_lo (PI := PI)) as PBL. unfold IMG_LO in PBL.
eapply SRr_mono.
{ apply (pfc_tbox fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k regs ch (a3f_fam T1 p) 0
    (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p) (d_obj cx ONM) 24 (d_obj cx OTOK) 24
    (d_obj cx ODISP) 48 []).
  - exact HJ.
  - exact HIMG.
  - exact (mc_cv_ok B W mem3 MCRO MCUN HIMG).
  - rewrite R1. unfold w64. apply ret_ok_codeptr_v; unfold BNR_OFF; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold BNR_OFF; lia). unfold BNR_OFF. lia.
  - exact Rgp.
  - exact Rtp.
  - rewrite Rsp, Hs0. apply (achain_lower ly3 _ (d_A cx)); [exact HCH | lia].
  - rewrite Rsp. lia.
  - rewrite Rsp, RBNS. unfold LLVMF_STK. lia.
  - rewrite Rsp. lia.
  - rewrite HFR. cbn [length Z.of_nat]. lia.
  - exact R10.
  - pose proof (pfc_u1 T1 (48 * p + 15)). unfold a3f_fam. lia.
  - exact R11.
  - lia.
  - exact R12.
  - pose proof (pfc_u1 T1 (48 * p + 13)). unfold disco_table_c.din_of. lia.
  - exact R13.
  - pose proof (pfc_u1 T1 (48 * p + 14)). unfold disco_table_c.dout_of. lia.
  - exact R14.
  - unfold d_obj. cbn [dobj_off]. lia.
  - exact R15.
  - lia.
  - exact R16.
  - unfold d_obj. cbn [dobj_off]. lia.
  - exact R17.
  - lia.
  - rewrite Rsp. replace (d_A cx + -16) with (d_A cx - 16) by lia. exact HDISP.
  - unfold d_obj. cbn [dobj_off]. lia.
  - rewrite Rsp. replace (d_A cx + -16 + 8) with (d_A cx - 8) by lia. exact HDL.
  - lia.
  - exact HRBN.
  - intros _. split; [left; split; reflexivity|].
    unfold ReacBoxName.rbn_bufs. change (Z.min 24 24) with 24. change (Z.min 48 48) with 48.
    assert (HSP : d_S cx - LLVMF_STK + ReacBoxName.REAC_BOX_NAME_STK <= spZ regs)
      by (rewrite Rsp, RBNS; unfold LLVMF_STK; lia).
    split; [|split; [|split; [|split; [|split]]]].
    + change (d_obj cx ONM) with (d_FB cx + 1792).
      apply (pfc_buf cx ly3 S3 W mem3 md3 k); [exact HCTX | exact HSHD | exact HAWRF | exact HSP | lia | lia | lia | lia | lia |].
      vm_compute. reflexivity.
    + change (d_obj cx OTOK) with (d_FB cx + 1856).
      apply (pfc_buf cx ly3 S3 W mem3 md3 k); [exact HCTX | exact HSHD | exact HAWRF | exact HSP | lia | lia | lia | lia | lia |].
      vm_compute. reflexivity.
    + change (d_obj cx ODISP) with (d_FB cx + 1920).
      apply (pfc_buf cx ly3 S3 W mem3 md3 k); [exact HCTX | exact HSHD | exact HAWRF | exact HSP | lia | lia | lia | lia | lia |].
      vm_compute. reflexivity.
    + unfold d_obj. cbn [dobj_off]. lia.
    + unfold d_obj. cbn [dobj_off]. lia.
    + unfold d_obj. cbn [dobj_off]. lia. }
cbv beta. intros W2 c2 HW2 Hpost.
unfold ReacBoxName.treac_box_name_post in Hpost.
destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPR & HFR2 & HPERM & H10 & KS & KB & KI & KF & PA & PS & HACC).
assert (HFR4 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite HFR2; exact HFR).
assert (HCTX2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k) by exact (conj HBASE (conj HJ2 HFR4)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly2 S2 W2 mem2 md2 k HCTX2)
  as (_ & _ & _ & _ & _ & _ & _ & _ & GFpres2 & GFsh2 & GSTK2 & _).
assert (HN0 : d_obj cx ONM <> 0) by (unfold d_obj; cbn [dobj_off]; lia).
assert (HT0 : d_obj cx OTOK <> 0) by (unfold d_obj; cbn [dobj_off]; lia).
assert (HD0 : d_obj cx ODISP <> 0) by (unfold d_obj; cbn [dobj_off]; lia).
pose proof (slot_ser_P3.bn_accept_ret (a3f_fam T1 p) (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p)
  (d_obj cx ONM) (d_obj cx OTOK) (d_obj cx ODISP) HN0 HT0 HD0) as HAE.
assert (RBNW : forall a, ReacBoxName.rbn_wr (a3f_fam T1 p) [] (disco_table_c.din_of T1 p) (disco_table_c.dout_of T1 p)
  (d_obj cx ONM) 24 (d_obj cx OTOK) 24 (d_obj cx ODISP) 48 a -> d_FB cx + 1792 <= a < d_FB cx + 1968)
  by (intros a Ha; exact (pfc_rbnw cx _ _ _ a Ha)).
assert (KF2 : forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_FB cx + 1792 <= a < d_FB cx + 1968) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hno. apply (KF DFRAME_CLASS (c_fpos cx) a).
  - rewrite HFR. left. reflexivity.
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - intros Hw. exact (Hno (RBNW a Hw)). }
assert (KS2 : forall kk, 0 <= kk < 512 ->
  aview SEGS (w_H W2) mem2 (shadow_addr (d_FB cx) + kk) = aview SEGS (w_H W) mem3 (shadow_addr (d_FB cx) + kk)).
{ intros kk Hkk. apply (KF DFRAME_CLASS (c_fpos cx)).
  - rewrite HFR. left. reflexivity.
  - right. unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
  - intros Hw. apply RBNW in Hw.
    apply (fshadow_not_app (d_FB cx) 512 (d_FB cx) 4096 (shadow_addr (d_FB cx) + kk));
      [exact GF4096 | lia | exact GFapp | unfold shadow_addr, SHADOW_OFF; lia | lia]. }
assert (KST : forall a, d_A cx - 16 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply KS.
  - lia.
  - rewrite Rsp. lia.
  - intros Hw. apply RBNW in Hw. lia. }
assert (KBL : forall b m j, In (b, m) (ablocks B ly3 S3) -> 0 <= j < req_size m ->
  aview SEGS (w_H W2) mem2 (b + j) = aview SEGS (w_H W) mem3 (b + j)).
{ intros b m j Hb Hj. apply (KB b m j Hb Hj). intros Hw. apply RBNW in Hw.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 b m DFRAME_CLASS (c_fpos cx) HAR3 Hb HFin3) as Hz.
  rewrite EFA3 in Hz. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia. }
assert (RDK : forall a, d_rdset B cx h a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Hd. unfold d_rdset in Hd.
  destruct Hd as [Hd | [Hd | [Hd | [Hd | [Hd | [(Hc & Hd) | [(Hro & Ho & He) | Hd]]]]]]].
  1-4: apply KF2; unfold d_objr, d_obj in Hd; cbn [dobj_off dobj_size] in Hd; lia.
  - assert (Hh3 : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm0)). apply in_or_app. right. left. reflexivity. }
    pose proof (req_size_pos HUNT_SIZE ltac:(unfold HUNT_SIZE; lia)) as (_ & Hrs).
    replace a with (h + (a - h)) by lia. apply (KBL h HUNT_SIZE (a - h) Hh3). lia.
  - assert (Hp3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm0)). apply in_or_app. right. right.
      exact (pfc_input cx HBASE Hc). }
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrs).
    replace a with (c_p cx + (a - c_p cx)) by lia. apply (KBL _ _ _ Hp3). lia.
  - exact (KI a (pfc_roimg a Hro) Ho He).
  - destruct DCAN as (AIL & KCAN).
    assert (Hev : aenv_addr tfib_K a)
      by (left; apply (ail_owned_core _ _ _ AIL); unfold aenv_core; rewrite KCAN; repeat right; exact Hd).
    destruct (ail_env _ _ _ AIL a Hev) as (Hi1 & Ho1 & He1).
    exact (KI a Hi1 Ho1 He1). }
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
assert (US : base_val E (Some AT_STK) = d_S cx).
{ cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
assert (UA : base_val E (Some AT_A) = d_A cx).
{ cbn [base_val]. rewrite E60. unfold w64. apply unsigned_lit_small. lia. }
assert (UF : base_val E (Some AT_F) = d_FB cx).
{ cbn [base_val]. rewrite EF. unfold w64. apply unsigned_lit_small. lia. }
assert (USH : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
{ cbn [base_val]. rewrite ESH. unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (VA : forall off v, 0 <= off <= 464 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W2 mem2) (d_A cx + off) 8 v).
{ intros off v Ho Hv. apply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact Hv].
  intros kk Hkk. apply KST. lia. }
assert (HFRM2 : d_frame cx h dsh_md W2 mem2).
{ exists E. split; [exact HE|]. split.
  - unfold d_regions in HREG |- *.
    pose proof (Forall_inv HREG) as HR0.
    pose proof (Forall_inv (Forall_inv_tail HREG)) as HR1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HREG))) as HR2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HREG)))) as HR3.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (pfc_region_kept E _ _ _ (fun _ => True) HR0); [intros; exact I | | | vm_compute; reflexivity].
      * cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite US. intros o Ho _.
        apply (mbyte_of_aview SEGS). apply KST. lia.
      * cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
    + apply (pfc_region_kept E _ _ _ (fun _ => True) HR1); [intros; exact I | | | vm_compute; reflexivity].
      * cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite UA. intros o Ho _.
        apply (mbyte_of_aview SEGS). apply KST. lia.
      * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite UA. intros o Ho.
        apply (apresent_writable SEGS). apply GSTK2. unfold LLVMF_STK. lia.
    + apply (pfc_region_kept E _ _ _ (fun o => 0 <= o < 24) HR2); [| | | vm_compute; reflexivity].
      * intros cc Hcc ii Hii. cbn [YP09.r_chunks In] in Hcc.
        destruct Hcc as [<- | [<- | [<- | []]]]; cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in Hii |- *; lia.
      * cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite UF. intros o Ho Hp. cbv beta in Hp.
        apply (mbyte_of_aview SEGS). apply KF2; lia.
      * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite UF. intros o Ho.
        apply (apresent_writable SEGS). apply GFpres2. unfold DFRAME_SIZE in Ho. lia.
    + unfold fshadow_region in HR3 |- *.
      apply (pfc_region_kept E _ _ _ (fun _ => True) HR3); [intros; exact I | | | vm_compute; reflexivity].
      * cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite USH. change (fs_frame_bytes DFRAME_CLASS / 8) with 512.
        intros o Ho _. apply (mbyte_of_aview SEGS). apply KS2. lia.
      * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite USH. intros o Ho.
        apply (apresent_writable SEGS). apply GFsh2. unfold DFRAME_SH in Ho. lia.
  - split.
    { rewrite (rdword_ext (aview SEGS (w_H W) mem3) (aview SEGS (w_H W2) mem2)); [exact HFLAG|].
      intros kk Hkk. change (fs_frame_bytes DFRAME_CLASS) with 4096. apply KF2; lia. }
    split; [exact (VA 184 _ ltac:(lia) V184)|].
    split; [exact (VA 120 _ ltac:(lia) V120)|].
    split; [exact (VA 136 _ ltac:(lia) V136)|].
    split; [exact (VA 376 _ ltac:(lia) V376)|].
    split; [exact (VA 280 _ ltac:(lia) V280)|].
    split; [exact (VA 232 _ ltac:(lia) V232)|].
    exact (VA 264 _ ltac:(lia) V264). }
assert (HSHD2 : d_shadow cx dsh_md W2 mem2).
{ intros kk Hkk. rewrite (KS2 kk) by (unfold DFRAME_SH in Hkk; lia). exact (HSHD kk Hkk). }
assert (HBODY2 : d_body B cx h n (a3_xb buf op) dsh_md ly2 S2 W2 mem2).
{ apply (DTOBS LAWS cx h n (a3_xb buf op) dsh_md dsh_md ly3 S3 W mem3
    ly2 S2 W2 mem2 md2 k (d_A cx - 16 - ReacBoxName.REAC_BOX_NAME_STK) (d_A cx - 16) [ONM; OTOK; ODISP]
    (fun a => aview SEGS (w_H W2) mem2 a <> aview SEGS (w_H W) mem3 a) HBODY (conj HBASE HJ2)).
  - rewrite RBNS. unfold LLVMF_STK. lia.
  - lia.
  - intros a HRa. right. right. intros Hd. exact (HRa (RDK a Hd)).
  - intros a _ HRa. exact (pfc_nn _ _ HRa).
  - repeat constructor.
  - exact HPERM.
  - exact HFRM2.
  - exact HSHD2. }
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
unfold f_bnr, a3f_stg.
split.
{ destruct HFROM as (HA3 & HW0 & HR0). exact (conj HA3 (conj (wle_trans _ _ _ _ HW0 HW2) HR0)). }
unfold d_at.
exists fq, ly2, S2, regs2, mem2, md2, k, acc.
split; [unfold cfg_at; rewrite R1; reflexivity|].
split; [exact HFRM0|].
split; [exact HBASE|]. split; [exact HJ2|]. split; [exact HFR4|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ unfold d_rLs.
  split; [transitivity (spZ regs); [unfold spZ; f_equal; exact P2 | exact Rsp]|].
  split; [etransitivity; [exact P3 | exact Rgp]|].
  split; [etransitivity; [exact P4 | exact Rtp]|].
  split; [etransitivity; [exact P8 | exact Rs0]|].
  split; [etransitivity; [exact P9 | exact Rs1]|].
  split; [etransitivity; [exact P19 | exact Rs19]|].
  split; [etransitivity; [exact P18 | exact Rs18]|].
  etransitivity; [exact P20 | exact Rs20]. }
split; [etransitivity; [exact P24 | exact R24]|].
split.
{ split.
  { unfold a3f_bnregs.
    split; [etransitivity; [exact P21 | exact R21]|].
    split; [etransitivity; [exact P22 | exact R22]|].
    split; [etransitivity; [exact P23 | exact R23]|].
    split; [etransitivity; [exact P25 | exact R25]|].
    split; [etransitivity; [exact P26 | exact R26]|].
    etransitivity; [exact P27 | exact R27]. }
  etransitivity; [exact H10|]. rewrite HAE. reflexivity. }
split.
{ split.
  { destruct HSP1 as ((V208 & V320) & V192 & V200).
    exact (conj (conj (VA 208 _ ltac:(lia) V208) (VA 320 _ ltac:(lia) V320))
      (conj (VA 192 _ ltac:(lia) V192) (VA 200 _ ltac:(lia) V200))). }
  split.
  { destruct HTAB as (HTAB1 & HGT). split; [exact HTAB1|].
    apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact HGT].
    intros a Ha. rewrite length_map, LT1 in Ha. apply KF2; unfold d_obj in Ha; cbn [dobj_off] in Ha; lia. }
  split.
  { destruct HBUF as (HRB & HGB). split; [exact HRB|].
    apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact HGB].
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. unfold a3_r in HRB.
    assert (Hb3 : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm0)). apply in_or_app. left. left. reflexivity. }
    pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrs).
    replace a with (buf + (a - buf)) by lia. apply (KBL _ _ _ Hb3). lia. }
  split; [exact HJR|]. split; [exact HVP|].
  split.
  { pose proof (slot_ser_P1.objs_len_le buf vpad os count HVP Hlen6 Los Hc8) as LO.
    apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact HOO].
    intros a Ha. rewrite length_map in Ha. apply KF2; unfold d_obj in Ha; cbn [dobj_off] in Ha; lia. }
  destruct HPYK as ((Hp & V368 & V360) & V408 & HGU).
  split.
  { split; [split; [exact Hp | split; [exact (VA 368 _ ltac:(lia) V368) | exact (VA 360 _ ltac:(lia) V360)]]|].
    split; [exact (VA 408 _ ltac:(lia) V408)|].
    apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact HGU].
    intros a Ha. assert (LU : length (a3f_used (p + 1)) = 32%nat) by (unfold a3f_used; reflexivity).
    rewrite LU in Ha. apply KF2; unfold d_obj in Ha; cbn [dobj_off] in Ha; lia. }
  split; [exact Hhd|]. split; [exact (VA 352 _ ltac:(lia) H352)|]. split.
  { apply (garr8_aview_kept SEGS (w_H W) (w_H W2) mem3 mem2); [|exact HWID].
    intros a Ha. cbn [length a3f_wid0] in Ha. apply KF2; unfold d_obj in Ha; cbn [dobj_off] in Ha; lia. }
  intros H0. refine (proj1 (proj2 (HACC _))). rewrite HAE. unfold a3f_bnret in H0. rewrite H0. reflexivity. }
split.
{ destruct HSP0 as (V208 & V320). exact (conj (VA 208 _ ltac:(lia) V208) (VA 320 _ ltac:(lia) V320)). }
exact HBODY2.
Qed.

End h.
End f.
End d.

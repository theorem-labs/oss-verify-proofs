(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_list_push.v, with its module paths and module names changed; 616 of its 666 lines of code are new or changed and 1541 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA2.v, with its module paths, module names and numbers changed; 764 of its 828 lines of code are new or changed and 602 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel ReacDiscoTableAge DiscoArm3FieldPH.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_table reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs slot_ser_P3.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfb_fcs (b : bool) (p : Z) : list YP09.chunk :=
  [YP09.mkChunk (2172 + 48 * p) (CVal 1 (if b then SLit 0 else SOff 563 0));
   YP09.mkChunk (2173 + 48 * p) (CVal 1 (SOff 564 0));
   YP09.mkChunk (2174 + 48 * p) (CVal 1 (SOff 565 0));
   YP09.mkChunk (2175 + 48 * p) (CVal 1 (SOff 566 0))].
Definition pfb_G (b : bool) : facts :=
  d_facts [(563%nat, if b then mkAF 0 0 0 else mkAF 1 255 0); (564%nat, mkAF 0 255 0);
           (565%nat, mkAF 0 255 0); (566%nat, mkAF 0 255 0)] [].
Definition pfb_stk : YP09.region := YP09.mkRegion (Some AT_A) (-16) 0 (-16) 0 [].
Definition pfb_rs (b : bool) (p : Z) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 352 360 (dslot_chunks ++ []);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 2000 2004 (dfhdr_chunks ++ pfb_fcs b p);
   YP09.mkRegion (Some AT_SH) 0 (fs_frame_bytes DFRAME_CLASS / 8) 224 253 (dsh_chunks dsh_ser2);
   got_regionP; bcell_regionP 32; pfb_stk].
Definition pfb_sr (p : Z) : list sv :=
  sr_set (sr_set (a3f_sr 0) 22%bv (SOff AT_F (2160 + 48 * p))) 27%bv (SOff AT_SH 0).
Definition pfb_ex (T : list byte) (p : Z) : list word :=
  [w64 (disco_table_c.hd_of T p); w64 (disco_table_c.din_of T p);
   w64 (disco_table_c.dout_of T p); w64 (a3f_fam T p)].

Lemma pfb_u1_range : forall (T : list byte) (k : Z), 0 <= disco_table_c.u_at T k 1 < 256.
Proof.
  intros T k. unfold disco_table_c.u_at.
  pose proof (disco_table.ble_range (disco_table_c.sub T k 1)) as H.
  assert (HL : (length (disco_table_c.sub T k 1) <= 1)%nat).
  { unfold disco_table_c.sub. rewrite length_firstn. lia. }
  assert (HP : 2 ^ (8 * Z.of_nat (length (disco_table_c.sub T k 1))) <= 2 ^ 8).
  { apply Z.pow_le_mono_r; lia. }
  change (2 ^ 8) with 256 in HP. lia.
Qed.

Lemma pfb_subregion : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.
Lemma pfb_subrefl : forall r, subregion r r.
Proof. intros [b lo hi wlo whi cs]. apply pfb_subregion. lia. Qed.
Lemma pfb_submem : forall b p, submem (pfb_rs b p) (d_kregions dsh_ser2 [] (pfb_fcs b p) ++ [pfb_stk]).
Proof.
  intros b p. unfold pfb_rs, d_kregions, fshadow_region, DFRAME_SIZE, DFRAME_SH. cbn [app].
  apply submem_keep; [apply pfb_subrefl|].
  apply submem_keep; [apply pfb_subregion; lia|].
  apply submem_keep; [apply pfb_subregion; lia|].
  apply submem_keep; [apply pfb_subregion; lia|].
  apply submem_keep; [apply pfb_subrefl|].
  apply submem_keep; [apply pfb_subrefl|].
  apply submem_keep; [apply pfb_subrefl|].
  apply submem_nil.
Qed.
Lemma pfb_kwf : forall b p, 0 <= p < 8 ->
  regions_wf (d_kregions dsh_ser2 [] (pfb_fcs b p) ++ [pfb_stk]) = true.
Proof.
  intros b p Hp.
  assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct b; destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma pfb_wf : forall b p, 0 <= p < 8 -> regions_wf (pfb_rs b p) = true.
Proof.
  intros b p Hp.
  assert (E : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
  destruct b; destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma pfb_wid_bytes : forall segs (m : word -> option byte) a,
  val_mem segs m a 4 slot_inv.W0X0 -> garr8 segs m a a3f_wid0.
Proof.
  intros segs m a Hv j Hj. cbn [length a3f_wid0] in Hj.
  assert (Ej : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%nat) by lia.
  split; [|destruct Ej as [-> | [-> | [-> | ->]]]; cbn [nth a3f_wid0]; lia].
  intros kk Hkk. assert (Hk0 : kk = 0%nat) by lia. subst kk.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite (Hv j ltac:(lia)). f_equal. f_equal.
  destruct Ej as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
Qed.

Lemma pfb_inw : forall E b p a, in_wrange E (pfb_rs b p) a ->
  base_val E (Some AT_A) - 16 <= a < base_val E (Some AT_A) \/
  base_val E (Some AT_A) + 352 <= a < base_val E (Some AT_A) + 360 \/
  base_val E (Some AT_F) + 2000 <= a < base_val E (Some AT_F) + 2004 \/
  base_val E (Some AT_SH) + 224 <= a < base_val E (Some AT_SH) + 253.
Proof.
  intros E b p a (r & Hin & Hr). unfold pfb_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]];
    unfold got_regionP, bcell_regionP, pfb_stk in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr |- *; lia.
Qed.

Lemma pfb_slot24_len : forall buf vpad t, length vpad = 4%nat ->
  length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.
Lemma pfb_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|].
    cbn [map concat length]. rewrite length_app, IHl, pfb_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Lemma pfb_used_len : forall p, length (a3f_used p) = 32%nat.
Proof. intros p. unfold a3f_used. reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfb_pc_shift : forall (fq : YK11.FPState) E ss ms z,
  st_ok (fx := fq) SEGS E (setpc ss (BASE + z)) ms -> st_ok_pi (fx := fq) SEGS VAL E (setpc ss z) ms.
Proof. intros fq E ss ms z HS. unfold st_ok_pi, abs_ss. exact HS. Qed.

Lemma pfb_offimg : forall b n a, off_img b n -> in_img SEGS a -> b <= a < b + n -> False.
Proof.
  intros b n a Hoff Hi Ha. pose proof (pa_img_range a Hi) as Hr. unfold off_img in Hoff. lia.
Qed.

Lemma pfb_roimg : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hg)].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DBRT : d_body_rt_stmt B.

Theorem a3f_pfxb : forall p, 0 <= p < 8 -> seg_pfb_p_spec B MT XM_LIB RLO RHI tfib_K p.
Proof.
intros p Hp cx h i n now op W0 c0 T0 T1 buf count os vpad W c (Hfrom & Hd).
destruct Hd as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc & P).
destruct P as (Hi & Hn & Hnow & HRL & (R24 & R22) & HX & HSP0 & HBODY).
destruct HX as (HSP1 & HTAB & HBUF & HJR & HVP & HOO & HPYK).
destruct HPYK as (HSL & H408 & HUSED).
pose proof HSL as (Hpc & H368 & H360).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GSHpres & GWpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
assert (Hd1 : d_FB cx / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
assert (HFB8 : d_FB cx mod 8 = 0) by (pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)); lia).
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
assert (Hinh : In (h, slot_inv.HUNT_SIZE) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. right. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinh) as (Hh16 & Hh4096 & Hhceil & Hhapp & _).
change (req_size slot_inv.HUNT_SIZE) with 480 in Hhceil, Hhapp.
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LU : length (a3f_used (p + 1)) = 32%nat) by apply pfb_used_len.
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. destruct HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a Hr. apply pa_segs_low. exact (pfb_roimg a Hr). }
assert (HTB : forall kk (nn : nat), 0 <= kk -> (Z.to_nat kk + nn <= 400)%nat ->
  val_mem SEGS (rd W mem3) (d_obj cx OT + kk) nn (disco_table_c.u_at T1 kk nn)).
{ intros kk nn Hk0 Hkn. unfold disco_table_c.u_at.
  apply (ReacDiscoTableAge.ta_vm_of_ga (rd W mem3) (d_obj cx OT) T1 kk nn HGT Hk0). rewrite HLT1. lia. }
set (vals := a3f_vals regs ++ pfb_ex T1 p).
pose proof (d_E_env cx E vals HE) as HE'.
pose proof HE' as (EE' & E32' & HEI & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E vals) 60) = d_A cx).
{ change 60%nat with AT_A. rewrite E60'. unfold w64. apply unsigned_lit_small. lia. }
assert (U516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx).
{ change 516%nat with AT_F. rewrite EF'. unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : bv_unsigned (ew (d_env cx E vals) 529) = shadow_addr (d_FB cx)).
{ change 529%nat with AT_SH. rewrite ESH'. unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (BV60 : base_val (d_env cx E vals) (Some AT_A) = d_A cx) by exact U60.
assert (BV516 : base_val (d_env cx E vals) (Some AT_F) = d_FB cx) by exact U516.
assert (BV529 : base_val (d_env cx E vals) (Some AT_SH) = shadow_addr (d_FB cx)) by exact U529.
assert (QX : forall (r : bv 5) (a : nat), a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  ew (d_env cx E vals) a = getr regs r)
  by (intros r a Ha; exact (DiscoArm3FieldPH.ph_env_reg cx E regs (pfb_ex T1 p) r a Ha)).
assert (Lv : length vals = 36%nat)
  by (unfold vals, a3f_vals, pfb_ex; rewrite length_app, length_map, length_seq; reflexivity).
assert (EAX : forall j, (j < 4)%nat ->
  ew (d_env cx E vals) (563 + j) = nth j (pfb_ex T1 p) (Z_to_bv 64 0)).
{ intros j Hj. replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
  rewrite d_env_x by (rewrite Lv; lia).
  unfold vals. rewrite app_nth2 by (unfold a3f_vals; rewrite length_map, length_seq; lia).
  unfold a3f_vals. rewrite length_map, length_seq. f_equal. lia. }
assert (EA563 : ew (d_env cx E vals) 563 = w64 (disco_table_c.hd_of T1 p)) by exact (EAX 0%nat ltac:(lia)).
assert (EA564 : ew (d_env cx E vals) 564 = w64 (disco_table_c.din_of T1 p)) by exact (EAX 1%nat ltac:(lia)).
assert (EA565 : ew (d_env cx E vals) 565 = w64 (disco_table_c.dout_of T1 p)) by exact (EAX 2%nat ltac:(lia)).
assert (EA566 : ew (d_env cx E vals) 566 = w64 (a3f_fam T1 p)) by exact (EAX 3%nat ltac:(lia)).
pose proof HCAN as (_ & _ & HCIMG).
assert (HNOSH : forall a, shadow_addr (d_FB cx) + 224 <= a < shadow_addr (d_FB cx) + 253 ->
  ~ d_rdset B cx h a).
{ intros a Ha Hr. unfold shadow_addr, SHADOW_OFF in Ha.
  assert (HFA : forall q m, in_app q m -> q <= a < q + m -> False).
  { intros q m Hq Hqa. apply (fshadow_not_app (d_FB cx) 512 q m a ltac:(lia) ltac:(lia) Hq); lia. }
  unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size, slot_inv.HUNT_SIZE in Hr.
  destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hcn & Hr) | [(Hr & _) | Hr]]]]]]].
  - apply (HFA (d_FB cx) 4096 GFapp). lia.
  - apply (HFA (d_FB cx) 4096 GFapp). lia.
  - apply (HFA (d_FB cx) 4096 GFapp). lia.
  - apply (HFA (d_FB cx) 4096 GFapp). lia.
  - apply (HFA h 480 Hhapp). lia.
  - apply (HFA (c_p cx) (req_size (c_n cx)) (HpA Hcn)).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hq). lia.
  - specialize (Hro a Hr). unfold kLowMemEnd in Hro. lia.
  - unfold FF_canary in Hr. lia. }
assert (HNOWID : forall a, d_FB cx + 2000 <= a < d_FB cx + 2004 -> ~ d_rdset B cx h a).
{ intros a Ha Hr. pose proof HGEO as (_ & _ & _ & _ & _ & _ & Ghf & Gpf).
  unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size, slot_inv.HUNT_SIZE in Hr.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ghf, Gpf, HOFF.
  change slot_inv.HUNT_SIZE with 480 in Ghf.
  destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hcn & Hr) | [(Hr & _) | Hr]]]]]]];
    [lia | lia | lia | lia | lia | specialize (Gpf Hcn); lia | |].
  - exact (pfb_offimg (d_FB cx) 4096 a HOFF (pfb_roimg a Hr) ltac:(lia)).
  - exact (pfb_offimg (d_FB cx) 4096 a HOFF (HCIMG a Hr) ltac:(lia)). }
assert (LOO : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)))
  <= 1152).
{ rewrite length_map, (pfb_objs_len buf vpad os HVP Lo6), Los. lia. }
assert (POSTC : forall (ms : machine_state) (mat : list word) (ss' : sstate),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss' (restrict (w_H W) ms) ->
  d_land_chk dsh_md (ss_mem ss') = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 16 <= a < d_A cx) -> ~ (d_A cx + 352 <= a < d_A cx + 360) ->
     ~ (d_FB cx + 2000 <= a < d_FB cx + 2004) ->
     ~ (shadow_addr (d_FB cx) + 224 <= a < shadow_addr (d_FB cx) + 253) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  d_body B cx h n (a3_xb buf op) dsh_md ly3 S3 W (ms_mem ms) /\
  d_sp1 cx i n now W (ms_mem ms) /\ d_sp0 cx i now W (ms_mem ms) /\
  a3_tab cx now T0 T1 W (ms_mem ms) /\ a3_buf op T1 now buf W (ms_mem ms) /\
  garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OO)
    (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)) /\
  a3f_pyk cx p count W (ms_mem ms)).
{ intros ms mat ss' HS1 Hchk HJ1 HKEEP HPR.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 16 <= a < d_A cx) -> ~ (d_A cx + 352 <= a < d_A cx + 360) ->
    ~ (d_FB cx + 2000 <= a < d_FB cx + 2004) ->
    ~ (shadow_addr (d_FB cx) + 224 <= a < shadow_addr (d_FB cx) + 253) ->
    mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a).
  { intros a H1 H2 H3 H4 H5. apply (mbyte_of_aview SEGS). exact (HKEEP a H1 H2 H3 H4 H5). }
  assert (KFR : forall x, d_FB cx <= x < d_FB cx + 4096 -> ~ (d_FB cx + 2000 <= x < d_FB cx + 2004) ->
    mbyte SEGS (rd W (ms_mem ms)) x = mbyte SEGS (rd W mem3) x).
  { intros x Hx Hx2. apply KB; [lia | lia | lia | exact Hx2 |].
    intros Hsh. apply (fshadow_not_app (d_FB cx) 512 (d_FB cx) 4096 x ltac:(lia) ltac:(lia) GFapp);
      unfold shadow_addr, SHADOW_OFF in Hsh; lia. }
  assert (KBF : forall x, buf <= x < buf + req_size (Z.max (slot_ser_defs.ser_cap op) 1) ->
    mbyte SEGS (rd W (ms_mem ms)) x = mbyte SEGS (rd W mem3) x).
  { intros x Hx. apply KB; [lia | lia | lia | |].
    - pose proof (sep_block_frame _ _ LAWS ly3 S3 W mem3 md3 buf (Z.max (slot_ser_defs.ser_cap op) 1)
        DFRAME_CLASS (c_fpos cx) HAR3 Hinb HFin3) as Hsep.
      rewrite EFA3 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
      change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsep. lia.
    - intros Hsh. apply (fshadow_not_app (d_FB cx) 512 buf (req_size (Z.max (slot_ser_defs.ser_cap op) 1)) x
        ltac:(lia) ltac:(lia) Hbapp); unfold shadow_addr, SHADOW_OFF in Hsh; lia. }
  assert (KV : forall a (nn : nat) v,
    (forall x, a <= x < a + Z.of_nat nn -> mbyte SEGS (rd W (ms_mem ms)) x = mbyte SEGS (rd W mem3) x) ->
    val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v).
  { intros a nn v Hx Hv. exact (val_mem_frame SEGS (rd W mem3) (rd W (ms_mem ms)) a nn v Hx Hv). }
  assert (KG : forall a l,
    (forall x, a <= x < a + Z.of_nat (length l) -> mbyte SEGS (rd W (ms_mem ms)) x = mbyte SEGS (rd W mem3) x) ->
    garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l).
  { intros a l Hx Hg. exact (garr8_frame SEGS (rd W mem3) (rd W (ms_mem ms)) a l Hg Hx). }
  assert (KA : forall (off v : Z), 0 <= off -> off + 8 <= 352 \/ 360 <= off -> off + 8 <= 472 ->
    val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v).
  { intros off v H1 H2 H3 Hv. apply KV; [|exact Hv].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KB; unfold shadow_addr, SHADOW_OFF; lia. }
  pose proof HSP1 as ((H208 & H320) & H192 & H200).
  assert (HSP0' : d_sp0 cx i now W (ms_mem ms))
    by (split; [exact (KA 208 i ltac:(lia) ltac:(lia) ltac:(lia) H208) | exact (KA 320 now ltac:(lia) ltac:(lia) ltac:(lia) H320)]).
  assert (HHS1 : d_hslots cx h W (ms_mem ms)).
  { split; [exact (KA 184 _ ltac:(lia) ltac:(lia) ltac:(lia) V184)|].
    split; [exact (KA 120 _ ltac:(lia) ltac:(lia) ltac:(lia) V120)|].
    split; [exact (KA 136 _ ltac:(lia) ltac:(lia) ltac:(lia) V136)|].
    split; [exact (KA 376 _ ltac:(lia) ltac:(lia) ltac:(lia) V376)|].
    split; [exact (KA 280 _ ltac:(lia) ltac:(lia) ltac:(lia) V280)|].
    split; [exact (KA 232 _ ltac:(lia) ltac:(lia) ltac:(lia) V232)|].
    exact (KA 264 _ ltac:(lia) ltac:(lia) ltac:(lia) V264). }
  assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms)
    (with_vm_backing (m_vm_lazy md3) mat md3) k) by exact (conj HBASE (conj HJ1 HFR)).
  pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_md ly3 S3 W
    (with_vm_backing (m_vm_lazy md3) mat md3) k (d_env cx E vals) ss' ms HCTX1 HE' (d_env_fl cx E vals)
    HS1 Hchk HHS1) as (HFRM1 & HSHD1).
  split.
  { apply (DBRT cx h n n (a3_xb buf op) dsh_ser2 dsh_md ly3 S3 W mem3 (ms_mem ms) (d_A cx - 16) (d_A cx + 360)
      (fun a => (d_A cx - 16 <= a < d_A cx) \/ (d_A cx + 352 <= a < d_A cx + 360) \/
                (d_FB cx + 2000 <= a < d_FB cx + 2004) \/
                (shadow_addr (d_FB cx) + 224 <= a < shadow_addr (d_FB cx) + 253)) HBODY).
    - unfold LLVMF_STK. lia.
    - lia.
    - intros a [Ha | [Ha | [Ha | Ha]]]; [left; lia | left; lia | right; exact (HNOWID a Ha) | right; exact (HNOSH a Ha)].
    - intros a Ha Hna. apply HKEEP;
        [exact Ha | intros Hx; apply Hna; left; exact Hx
         | intros Hx; apply Hna; right; left; exact Hx
         | intros Hx; apply Hna; right; right; left; exact Hx
         | intros Hx; apply Hna; right; right; right; exact Hx].
    - exact HPR.
    - exact HFRM1.
    - exact HSHD1.
    - lia. }
  split; [split; [exact HSP0'|]; split;
          [exact (KA 192 n ltac:(lia) ltac:(lia) ltac:(lia) H192) | exact (KA 200 (d_cur cx n) ltac:(lia) ltac:(lia) ltac:(lia) H200)]|].
  split; [exact HSP0'|].
  split.
  { split; [exact (proj1 HTAB)|]. apply KG; [|exact HGT]. rewrite length_map, HLT1. change (Z.of_nat 400) with 400.
    intros x Hx. apply KFR; unfold d_obj, dobj_off in *; lia. }
  split.
  { split; [exact Hr2|]. apply KG; [|exact HGB]. rewrite Lb. intros x Hx. apply KBF. lia. }
  split.
  { apply KG; [|exact HOO]. intros x Hx. apply KFR; unfold d_obj, dobj_off in *; lia. }
  split; [split; [exact Hpc|]; split;
          [exact (KA 368 p ltac:(lia) ltac:(lia) ltac:(lia) H368) | exact (KA 360 count ltac:(lia) ltac:(lia) ltac:(lia) H360)]|].
  split; [exact (KA 408 _ ltac:(lia) ltac:(lia) ltac:(lia) H408)|].
  apply KG; [|exact HUSED]. rewrite LU. change (Z.of_nat 32) with 32.
  intros x Hx. apply KFR; unfold d_obj, dobj_off in *; lia. }
assert (POSTM : forall (ms : machine_state) (mat : list word) (ss' : sstate),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss' (restrict (w_H W) ms) ->
  ss_pc ss' = MD_OFF -> ss_resv ss' = None ->
  d_land_chk dsh_md (ss_mem ss') = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 16 <= a < d_A cx) -> ~ (d_A cx + 352 <= a < d_A cx + 360) ->
     ~ (d_FB cx + 2000 <= a < d_FB cx + 2004) ->
     ~ (shadow_addr (d_FB cx) + 224 <= a < shadow_addr (d_FB cx) + 253) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  spZ (ms_regs ms) = d_A cx ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 8 = w64 (d_S cx) -> getr (ms_regs ms) 9 = w64 (d_A cx) ->
  getr (ms_regs ms) 19 = w64 SHADOW_OFF -> getr (ms_regs ms) 18 = w64 WS_MASK ->
  getr (ms_regs ms) 20 = w64 32 -> getr (ms_regs ms) 27 = w64 (shadow_addr (d_FB cx)) ->
  getr (ms_regs ms) 24 = w64 buf ->
  getr (ms_regs ms) 23 = w64 (VAL (A_OBJ 11)) ->
  getr (ms_regs ms) 22 = w64 (d_obj cx OT + 48 * p) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_obj cx OWID) 4 slot_inv.W0X0 ->
  disco_table_c.hd_of T1 p = 0 ->
  SRr SEGS W (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3))
    (fun W' c' =>
       f_md B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p (VAL (A_OBJ 11)) W' c' \/
       f_bn B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p W' c')).
{ intros ms mat ss' HS1 Hpc' Hrv Hchk HJ1 HKEEP HPR Q2 Q3 Q4 Q8 Q9 Q19 Q18 Q20 Q27 Q24 Q23 Q22 HW0 Hhd0.
  destruct (POSTC ms mat ss' HS1 Hchk HJ1 HKEEP HPR) as (HBODY1 & HSP1' & HSP0' & HTAB' & HBUF' & HOO' & HPYK').
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS1 Hrv). rewrite Hpc'.
  apply SRr_ret. left.
  unfold f_md, a3f_st. split; [exact Hfrom|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md3) mat md3), k, acc.
  split; [reflexivity|].
  split; [exact HFRM0|].
  split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { unfold d_rL. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
    split; [exact Q8|]. split; [exact Q9|]. split; [exact Q19|].
    split; [exact Q18|]. split; [exact Q20|]. exact Q27. }
  split.
  { cbv beta. split; [exact Q24|]. split; [exact Q23|]. exact Q22. }
  split.
  { cbv beta.
    split; [exact HSP1'|]. split; [exact HTAB'|]. split; [exact HBUF'|].
    split; [exact HJR|]. split; [exact HVP|]. split; [exact HOO'|].
    destruct HPYK' as (HSL' & H408' & HUSED').
    split; [exact HSL'|]. split; [exact H408'|]. split; [exact HUSED'|].
    unfold a3f_model, a3f_ent. rewrite (slot_ser_P3.model_hd0 T1 p Hhd0). cbn [fst snd].
    split; [exact (pfb_wid_bytes SEGS (rd W (ms_mem ms)) (d_obj cx OWID) HW0)|].
    unfold a3f_mstr. left. split; reflexivity. }
  split; [exact HSP0'|]. exact HBODY1. }
assert (POSTB : forall (ms : machine_state) (mat : list word) (ss' : sstate),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss' (restrict (w_H W) ms) ->
  ss_pc ss' = AF_both3_reac_box_name -> ss_resv ss' = None ->
  d_land_chk dsh_md (ss_mem ss') = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 16 <= a < d_A cx) -> ~ (d_A cx + 352 <= a < d_A cx + 360) ->
     ~ (d_FB cx + 2000 <= a < d_FB cx + 2004) ->
     ~ (shadow_addr (d_FB cx) + 224 <= a < shadow_addr (d_FB cx) + 253) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  spZ (ms_regs ms) = d_A cx + -16 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 8 = w64 (d_S cx) -> getr (ms_regs ms) 9 = w64 (d_A cx) ->
  getr (ms_regs ms) 19 = w64 SHADOW_OFF -> getr (ms_regs ms) 18 = w64 WS_MASK ->
  getr (ms_regs ms) 20 = w64 32 -> getr (ms_regs ms) 24 = w64 buf ->
  getr (ms_regs ms) 1 = w64 (BASE + BNR_OFF) ->
  getr (ms_regs ms) 21 = w64 (shadow_addr (d_obj cx OT + 48 * p + 13)) ->
  getr (ms_regs ms) 22 = w64 (d_obj cx OT + 48 * p) ->
  getr (ms_regs ms) 23 = w64 (VAL (A_OBJ 11)) ->
  getr (ms_regs ms) 25 = w64 (d_obj cx OT + 48 * p + 14) ->
  getr (ms_regs ms) 26 = w64 (d_obj cx OT + 48 * p + 13) ->
  getr (ms_regs ms) 27 = w64 (shadow_addr (d_FB cx)) ->
  getr (ms_regs ms) 10 = w64 (a3f_fam T1 p) -> getr (ms_regs ms) 11 = w64 0 ->
  getr (ms_regs ms) 12 = w64 (disco_table_c.din_of T1 p) ->
  getr (ms_regs ms) 13 = w64 (disco_table_c.dout_of T1 p) ->
  getr (ms_regs ms) 14 = w64 (d_obj cx ONM) -> getr (ms_regs ms) 15 = w64 24 ->
  getr (ms_regs ms) 16 = w64 (d_obj cx OTOK) -> getr (ms_regs ms) 17 = w64 24 ->
  val_mem SEGS (rd W (ms_mem ms)) (d_obj cx OWID) 4 slot_inv.W0X0 ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx - 16) 8 (d_obj cx ODISP) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx - 8) 8 48 ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 352) 8 (shadow_addr (d_obj cx OT + 48 * p + 14)) ->
  disco_table_c.hd_of T1 p <> 0 ->
  SRr SEGS W (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3))
    (fun W' c' =>
       f_md B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p (VAL (A_OBJ 11)) W' c' \/
       f_bn B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad p W' c')).
{ intros ms mat ss' HS1 Hpc' Hrv Hchk HJ1 HKEEP HPR Q2 Q3 Q4 Q8 Q9 Q19 Q18 Q20 Q24
    Q1 Q21 Q22 Q23 Q25 Q26 Q27 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 HW0 HD16 HD8 H352 Hhdn.
  destruct (POSTC ms mat ss' HS1 Hchk HJ1 HKEEP HPR) as (HBODY1 & HSP1' & HSP0' & HTAB' & HBUF' & HOO' & HPYK').
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS1 Hrv). rewrite Hpc'.
  apply SRr_ret. right.
  unfold f_bn, a3f_stg. split; [exact Hfrom|].
  unfold d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md3) mat md3), k, acc.
  split; [reflexivity|].
  split; [exact HFRM0|].
  split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { unfold d_rLs. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
    split; [exact Q8|]. split; [exact Q9|]. split; [exact Q19|].
    split; [exact Q18|]. exact Q20. }
  split; [exact Q24|].
  split.
  { cbv beta. split; [exact Q1|].
    split; [unfold a3f_bnregs; split; [exact Q21|]; split; [exact Q22|]; split; [exact Q23|];
            split; [exact Q25|]; split; [exact Q26|]; exact Q27|].
    split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|].
    split; [exact Q14|]. split; [exact Q15|]. split; [exact Q16|]. exact Q17. }
  split.
  { cbv beta.
    split; [exact HSP1'|]. split; [exact HTAB'|]. split; [exact HBUF'|].
    split; [exact HJR|]. split; [exact HVP|]. split; [exact HOO'|].
    split; [exact HPYK'|]. split; [exact Hhdn|]. split; [exact HD16|]. split; [exact HD8|].
    split; [exact H352|].
    exact (pfb_wid_bytes SEGS (rd W (ms_mem ms)) (d_obj cx OWID) HW0). }
  split; [exact HSP0'|]. exact HBODY1. }
assert (U2 : base_val (d_env cx E vals) (Some AT_STK) = d_S cx).
{ cbn [base_val]. unfold AT_STK. rewrite (EE' 2%nat 2%bv eq_refl). reflexivity. }
assert (EA : forall nn, (A_TEXT <= nn < A_LIM)%nat ->
  base_val (d_env cx E vals) (Some nn) = VAL nn).
{ intros nn Hn'. cbn [base_val]. rewrite (img_env_atomP _ nn HEI Hn').
  apply unsigned_lit_small. apply pa_val_range. }
assert (UG0 : base_val (d_env cx E vals) (Some (A_OBJ 0)) = VAL (A_OBJ 0))
  by (apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (UG12 : base_val (d_env cx E vals) (Some (A_OBJ 12)) = VAL (A_OBJ 12))
  by (apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as HO0.
pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
unfold IMG_LO, IMG_TOP in HO0, HO12.
assert (HQ13 : (d_FB cx + 2160 + 48 * p + 13) / 8 = d_FB cx / 8 + (271 + 6 * p)).
{ pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)) as D. rewrite HFB8 in D.
  replace (d_FB cx + 2160 + 48 * p + 13) with ((d_FB cx / 8 + (271 + 6 * p)) * 8 + 5) by lia.
  rewrite Z.div_add_l by lia. change (5 / 8) with 0. lia. }
assert (HQ14 : (d_FB cx + 2160 + 48 * p + 14) / 8 = d_FB cx / 8 + (271 + 6 * p)).
{ pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)) as D. rewrite HFB8 in D.
  replace (d_FB cx + 2160 + 48 * p + 14) with ((d_FB cx / 8 + (271 + 6 * p)) * 8 + 6) by lia.
  rewrite Z.div_add_l by lia. change (6 / 8) with 0. lia. }
assert (AWR : forall (b : bool) (q : Z), awr_ok (d_env cx E vals) (pfb_rs b q) LLVMF_STK (d_S cx) []
  (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ intros b q. unfold pfb_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ AT_A (d_A cx - d_S cx));
    [reflexivity | unfold AT_A; rewrite U60; lia | unfold LLVMF_STK; cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ AT_F (d_FB cx)); [reflexivity | exact U516 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ AT_SH (shadow_addr (d_FB cx))); [reflexivity | exact U529 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ AT_A (d_A cx - d_S cx));
    [reflexivity | unfold AT_A; rewrite U60; lia | unfold pfb_stk, LLVMF_STK; cbn; lia
     | unfold pfb_stk; cbn; lia | apply awr_ok_nil]. }
assert (SHV : forall (ms0 : machine_state) (ss0 : sstate) (e : sv) (off : Z),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss0 (restrict (w_H W) ms0) ->
  shadow_norm (ss_facts ss0) e = Some (Some AT_SH, off) ->
  sv_denot (d_env cx E vals) e = Z_to_bv 64 (shadow_addr (d_FB cx) + off)).
{ intros ms0 ss0 e off HS0 Hsn.
  rewrite (shadow_norm_sound _ _ _ _ _ (st_ok_facts_ok SEGS _ (abs_ss VAL ss0) _ HS0) Hsn).
  rewrite BV529. reflexivity. }
assert (SHR : forall (ms0 : machine_state) (ss0 : sstate) (r : bv 5) (off : Z),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss0 (restrict (w_H W) ms0) ->
  shadow_norm (ss_facts ss0) (sr_get (ss_regs ss0) r) = Some (Some AT_SH, off) ->
  getr (ms_regs ms0) r = Z_to_bv 64 (shadow_addr (d_FB cx) + off)).
{ intros ms0 ss0 r off HS0 Hsn.
  rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS0). exact (SHV ms0 ss0 _ off HS0 Hsn). }
assert (HSEAT : forall b : bool,
  (b = true -> disco_table_c.hd_of T1 p = 0) -> (b = false -> disco_table_c.hd_of T1 p <> 0) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) (mkSS R1_OFF (pfb_sr p) (pfb_rs b p) None (pfb_G b))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + R1_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ intros b Hbt Hbf.
  assert (HB0 : 0 <= disco_table_c.hd_of T1 p < 256) by (unfold disco_table_c.hd_of; apply pfb_u1_range).
  assert (HREGS : regs_ok (d_env cx E vals) (a3f_sr 0) regs)
    by exact (DiscoArm3FieldPH.ph_regs_ok B cx E regs (pfb_ex T1 p) HE HRL).
  assert (HGF : facts_ok (d_env cx E vals) (pfb_G b)).
  { apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals _ [] HCTX HE); [|exact I].
    unfold pfb_G. cbn [atoms_ok]. unfold afact_ok.
    pose proof (pfb_u1_range T1 (48 * p + 13)) as Q13'.
    pose proof (pfb_u1_range T1 (48 * p + 14)) as Q14'.
    pose proof (pfb_u1_range T1 (48 * p + 15)) as Q15'.
    unfold disco_table_c.din_of, disco_table_c.dout_of, a3f_fam in *.
    rewrite EA563, EA564, EA565, EA566. unfold w64.
    rewrite !unsigned_lit_small by lia.
    destruct b; [pose proof (Hbt eq_refl) as Hz | pose proof (Hbf eq_refl) as Hz];
      cbn [af_lo af_hi af_al2]; rewrite !Z.pow_0_r, !Z.mod_1_r;
      repeat split; first [exact I | lia]. }
  assert (HFCS : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) (pfb_fcs b p)).
  { unfold pfb_fcs. repeat (apply Forall_cons); [| | | | apply Forall_nil].
    - apply (chunk_ok_val SEGS _ _ (d_FB cx) (2172 + 48 * p) 1%N _ (disco_table_c.hd_of T1 p)).
      + destruct b; [rewrite (Hbt eq_refl); reflexivity | cbn [sv_denot]; rewrite EA563, Z.add_0_r;
          unfold w64; apply Z_to_bv_bv_unsigned].
      + cbn [Z.of_N]. change (8 * 1) with 8. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat]. unfold disco_table_c.hd_of.
        replace (d_FB cx + (2172 + 48 * p)) with (d_obj cx OT + (48 * p + 12))
          by (unfold d_obj, dobj_off; lia).
        apply HTB; lia.
    - apply (chunk_ok_val SEGS _ _ (d_FB cx) (2173 + 48 * p) 1%N _ (disco_table_c.din_of T1 p)).
      + cbn [sv_denot]. rewrite EA564, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned.
      + cbn [Z.of_N]. change (8 * 1) with 8. pose proof (pfb_u1_range T1 (48 * p + 13)).
        unfold disco_table_c.din_of. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat]. unfold disco_table_c.din_of.
        replace (d_FB cx + (2173 + 48 * p)) with (d_obj cx OT + (48 * p + 13))
          by (unfold d_obj, dobj_off; lia).
        apply HTB; lia.
    - apply (chunk_ok_val SEGS _ _ (d_FB cx) (2174 + 48 * p) 1%N _ (disco_table_c.dout_of T1 p)).
      + cbn [sv_denot]. rewrite EA565, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned.
      + cbn [Z.of_N]. change (8 * 1) with 8. pose proof (pfb_u1_range T1 (48 * p + 14)).
        unfold disco_table_c.dout_of. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat]. unfold disco_table_c.dout_of.
        replace (d_FB cx + (2174 + 48 * p)) with (d_obj cx OT + (48 * p + 14))
          by (unfold d_obj, dobj_off; lia).
        apply HTB; lia.
    - apply (chunk_ok_val SEGS _ _ (d_FB cx) (2175 + 48 * p) 1%N _ (a3f_fam T1 p)).
      + cbn [sv_denot]. rewrite EA566, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned.
      + cbn [Z.of_N]. change (8 * 1) with 8. pose proof (pfb_u1_range T1 (48 * p + 15)).
        unfold a3f_fam. lia.
      + cbn [Z.of_N]. lia.
      + cbn [N.to_nat]. unfold a3f_fam.
        replace (d_FB cx + (2175 + 48 * p)) with (d_obj cx OT + (48 * p + 15))
          by (unfold d_obj, dobj_off; lia).
        apply HTB; lia. }
  assert (HEXT : Forall (region_ok SEGS (d_env cx E vals) (rd W mem3)) [pfb_stk]).
  { apply Forall_cons; [|apply Forall_nil]. unfold pfb_stk.
    apply (region_ok_stack SEGS _ _ AT_A (d_A cx) (-16) U60 ltac:(lia) ltac:(lia)).
    intros a Ha. apply (apresent_writable SEGS). apply GWpres. unfold LLVMF_STK. lia. }
  assert (HDX : Forall (fun r => all_disjoint (d_env cx E vals) r
      (d_kregions dsh_ser2 [] (pfb_fcs b p))) [pfb_stk]).
  { apply Forall_cons; [|apply Forall_nil]. apply all_disjoint_of_extents.
    unfold d_kregions, fshadow_region, got_regionP, bcell_regionP, pfb_stk, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U2, BV60, BV516, BV529, UG0, UG12.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_addr, SHADOW_OFF in *. repeat split; lia. }
  pose proof (DSEAT LAWS PAL fq cx dsh_ser2 ly3 S3 W regs mem3 md3 k E R1_OFF (a3f_sr 0)
    vals [] (pfb_fcs b p) [pfb_stk] (pfb_G b)
    HCTX HE HREG HFLAG HREGS HGF (Forall_nil _) HFCS HEXT ltac:(cbn; split; exact I) HDX
    (pfb_kwf b p Hp)) as HS0.
  unfold ss_d in HS0.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ 22%bv (SOff AT_F (2160 + 48 * p)) HS0 eq_refl
    ltac:(cbn [sv_denot ms_regs restrict YK11.mkst]; unfold AT_F; rewrite U516, R22;
          unfold d_obj, dobj_off, w64; f_equal; lia)) as HS1.
  pose proof (ast_ok_pi_set_reg_fp _ _ _ 27%bv (SOff AT_SH 0) HS1 eq_refl
    ltac:(cbn [sv_denot ms_regs restrict YK11.mkst]; unfold AT_SH; rewrite U529, Z.add_0_r, Rs27;
          reflexivity)) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  exact (st_ok_pi_submem _ _ _ (pfb_rs b p) HS2 (pfb_submem b p) (pfb_wf b p Hp)). }
assert (Hp8 : p = 0 \/ p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7) by lia.
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
unfold cfg_at, w64.
destruct (Z.eq_dec (disco_table_c.hd_of T1 p) 0) as [Hhd0 | Hhdn].
- pose proof (HSEAT true ltac:(intros _; exact Hhd0) ltac:(discriminate)) as HS.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals)
    (mrestrict (w_H W) (ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + R1_OFF)) mem3
      (YK11.seg_rom SEGS))))) by constructor.
  destruct Hp8 as [Ep | [Ep | [Ep | [Ep | [Ep | [Ep | [Ep | Ep]]]]]]]; rewrite Ep in HS;
    (paj_run_to_tok RUNTO HS HJ SHOK (0%Z, 0%Z) MD_OFF;
     [ cbn [ss_mem]; exact (AWR true _)
     | lazymatch type of HS with
       | st_ok_pi _ _ _ ?ssf _ =>
         pose proof (st_ok_pi_region_nth _ ssf _ 2%nat _ HS eq_refl) as RF;
         change (ms_mem (restrict (w_H W) ms)) with (rd W (ms_mem ms)) in RF
       end;
       prreg HS (2%bv : bv 5) Z2; prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4;
       prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9; prreg HS (18%bv : bv 5) Z18;
       prreg HS (19%bv : bv 5) Z19; prreg HS (20%bv : bv 5) Z20; prreg HS (22%bv : bv 5) Z22;
       prreg HS (23%bv : bv 5) Z23; prreg HS (24%bv : bv 5) Z24; prreg HS (27%bv : bv 5) Z27;
       refine (POSTM ms mat _ HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hhd0);
       [ intros a Ha H1 H2 H3 H4; apply (aview_eq_of SEGS); apply HFr;
         rewrite unsigned_lit_small by lia; intros Hw; apply pfb_inw in Hw;
         rewrite BV60, BV516, BV529 in Hw; destruct Hw as [Hw | [Hw | [Hw | Hw]]];
         [apply H1 | apply H2 | apply H3 | apply H4]; lia
       | intros a _ Hpa; exact (apresent_grows _ _ _ a HG Hpa)
       | unfold spZ; rewrite Z2; exact U60
       | rewrite Z3, (QX 3%bv 534%nat eq_refl); exact Rgp
       | rewrite Z4, (QX 4%bv 535%nat eq_refl); exact Rtp
       | rewrite Z8, (EE' 2%nat 2%bv eq_refl); unfold d_S, spZ, w64;
         rewrite Z_to_bv_bv_unsigned; reflexivity
       | rewrite Z9; exact E60'
       | rewrite Z19; exact E32'
       | rewrite Z18; unfold w64, WS_MASK; reflexivity
       | exact Z20
       | rewrite Z27; exact ESH'
       | rewrite Z24, (QX 24%bv 555%nat eq_refl); exact R24
       | rewrite Z23, (img_env_atomP _ 252%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)); reflexivity
       | rewrite Z22, U516; unfold d_obj, dobj_off, w64; f_equal; lia
       | replace (d_obj cx OWID) with (d_FB cx + 2000) by (unfold d_obj, dobj_off; lia);
         exact (field_of_region _ _ AT_F (d_FB cx) _ _ _ _ _ 2000 4%N (SLit slot_inv.W0X0) slot_inv.W0X0
                  RF U516 (in_eq _ _) eq_refl ltac:(cbn [Z.of_N]; unfold slot_inv.W0X0; lia)
                  ltac:(cbn [Z.of_N]; lia)) ] ]).
- pose proof (HSEAT false ltac:(discriminate) ltac:(intros _; exact Hhdn)) as HS.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals)
    (mrestrict (w_H W) (ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + R1_OFF)) mem3
      (YK11.seg_rom SEGS))))) by constructor.
  assert (Hp4 : (p = 0 \/ p = 1 \/ p = 2 \/ p = 3) \/ (p = 4 \/ p = 5 \/ p = 6 \/ p = 7)) by lia.
  clear Hp8. destruct Hp4 as [Hp4 | Hp4].
  + destruct Hp4 as [Ep | [Ep | [Ep | Ep]]]; rewrite Ep in HS;
      (paj_run_tok RUN HS HJ SHOK (0%Z, 0%Z);
       [ cbn [ss_mem]; exact (AWR false _)
       | rewrite pa_sigma_reac_box_name in HS;
         lazymatch type of HS with
         | st_ok _ _ (setpc ?ssf _) _ =>
           pose proof (pfb_pc_shift fq _ ssf _ AF_both3_reac_box_name HS) as HSP;
           pose proof (st_ok_pi_region_nth _ (setpc ssf AF_both3_reac_box_name) _ 1%nat _ HSP eq_refl) as RA;
           pose proof (st_ok_pi_region_nth _ (setpc ssf AF_both3_reac_box_name) _ 2%nat _ HSP eq_refl) as RF;
           pose proof (st_ok_pi_region_nth _ (setpc ssf AF_both3_reac_box_name) _ 6%nat _ HSP eq_refl) as RK
         end;
         change (ms_mem (restrict (w_H W) ms)) with (rd W (ms_mem ms)) in RA, RF, RK;
         pose proof (SHR ms _ 21%bv (271 + 6 * p) HSP ltac:(rewrite Ep; vm_compute; reflexivity)) as Z21;
         prreg HSP (2%bv : bv 5) Z2; prreg HSP (3%bv : bv 5) Z3; prreg HSP (4%bv : bv 5) Z4;
         prreg HSP (8%bv : bv 5) Z8; prreg HSP (9%bv : bv 5) Z9; prreg HSP (18%bv : bv 5) Z18;
         prreg HSP (19%bv : bv 5) Z19; prreg HSP (20%bv : bv 5) Z20; prreg HSP (24%bv : bv 5) Z24;
         prreg HSP (1%bv : bv 5) Z1; prreg HSP (22%bv : bv 5) Z22; prreg HSP (23%bv : bv 5) Z23;
         prreg HSP (25%bv : bv 5) Z25; prreg HSP (26%bv : bv 5) Z26; prreg HSP (27%bv : bv 5) Z27;
         prreg HSP (10%bv : bv 5) Z10; prreg HSP (11%bv : bv 5) Z11; prreg HSP (12%bv : bv 5) Z12;
         prreg HSP (13%bv : bv 5) Z13; prreg HSP (14%bv : bv 5) Z14; prreg HSP (15%bv : bv 5) Z15;
         prreg HSP (16%bv : bv 5) Z16; prreg HSP (17%bv : bv 5) Z17;
         refine (POSTB ms mat _ HSP eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hhdn);
         [ intros a Ha H1 H2 H3 H4; apply (aview_eq_of SEGS); apply HFr;
           rewrite unsigned_lit_small by lia; intros Hw; apply pfb_inw in Hw;
           rewrite BV60, BV516, BV529 in Hw; destruct Hw as [Hw | [Hw | [Hw | Hw]]];
           [apply H1 | apply H2 | apply H3 | apply H4]; lia
         | intros a _ Hpa; exact (apresent_grows _ _ _ a HG Hpa)
         | unfold spZ; rewrite Z2, U60; rewrite unsigned_lit_small by lia; lia
         | rewrite Z3, (QX 3%bv 534%nat eq_refl); exact Rgp
         | rewrite Z4, (QX 4%bv 535%nat eq_refl); exact Rtp
         | rewrite Z8, (EE' 2%nat 2%bv eq_refl); unfold d_S, spZ, w64;
           rewrite Z_to_bv_bv_unsigned; reflexivity
         | rewrite Z9; exact E60'
         | rewrite Z19; exact E32'
         | rewrite Z18; unfold w64, WS_MASK; reflexivity
         | exact Z20
         | rewrite Z24, (QX 24%bv 555%nat eq_refl); exact R24
         | rewrite Z1; unfold BNR_OFF, w64; f_equal; lia
         | rewrite Z21; unfold w64, d_obj, dobj_off, shadow_addr; rewrite HQ13; f_equal; lia
         | rewrite Z22, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | rewrite Z23, (img_env_atomP _ 252%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)); reflexivity
         | rewrite Z25, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | rewrite Z26, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | rewrite Z27; exact ESH'
         | rewrite Z10; exact EA566
         | exact Z11
         | rewrite Z12; exact EA564
         | rewrite Z13; exact EA565
         | rewrite Z14, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | exact Z15
         | rewrite Z16, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | exact Z17
         | replace (d_obj cx OWID) with (d_FB cx + 2000) by (unfold d_obj, dobj_off; lia);
           exact (field_of_region _ _ AT_F (d_FB cx) _ _ _ _ _ 2000 4%N (SLit slot_inv.W0X0) slot_inv.W0X0
                    RF U516 (in_eq _ _) eq_refl ltac:(cbn [Z.of_N]; unfold slot_inv.W0X0; lia)
                    ltac:(cbn [Z.of_N]; lia))
         | replace (d_A cx - 16) with (d_A cx + (-16)) by lia;
           exact (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ (-16) 8%N (SOff AT_F 1920) (d_obj cx ODISP)
                    RK U60 (in_cons _ _ _ (in_eq _ _))
                    ltac:(cbn [sv_denot]; unfold AT_F; rewrite U516; unfold d_obj, dobj_off; f_equal; lia)
                    ltac:(cbn [Z.of_N]; unfold d_obj, dobj_off; lia) ltac:(cbn [Z.of_N]; lia))
         | replace (d_A cx - 8) with (d_A cx + (-8)) by lia;
           exact (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ (-8) 8%N (SLit 48) 48
                    RK U60 (in_eq _ _) eq_refl ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia))
         | eapply (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 352 8%N _ (shadow_addr (d_obj cx OT + 48 * p + 14))
             RA U60);
           [ apply in_eq
           | lazymatch goal with |- sv_denot _ ?e = _ =>
               rewrite (SHV ms _ e (271 + 6 * p) HSP ltac:(rewrite Ep; vm_compute; reflexivity)) end;
             unfold d_obj, dobj_off, shadow_addr; rewrite HQ14; f_equal; lia
           | cbn [Z.of_N]; unfold d_obj, dobj_off, shadow_addr, SHADOW_OFF; lia
           | cbn [Z.of_N]; lia ] ] ]).
  + destruct Hp4 as [Ep | [Ep | [Ep | Ep]]]; rewrite Ep in HS;
      (paj_run_tok RUN HS HJ SHOK (0%Z, 0%Z);
       [ cbn [ss_mem]; exact (AWR false _)
       | rewrite pa_sigma_reac_box_name in HS;
         lazymatch type of HS with
         | st_ok _ _ (setpc ?ssf _) _ =>
           pose proof (pfb_pc_shift fq _ ssf _ AF_both3_reac_box_name HS) as HSP;
           pose proof (st_ok_pi_region_nth _ (setpc ssf AF_both3_reac_box_name) _ 1%nat _ HSP eq_refl) as RA;
           pose proof (st_ok_pi_region_nth _ (setpc ssf AF_both3_reac_box_name) _ 2%nat _ HSP eq_refl) as RF;
           pose proof (st_ok_pi_region_nth _ (setpc ssf AF_both3_reac_box_name) _ 6%nat _ HSP eq_refl) as RK
         end;
         change (ms_mem (restrict (w_H W) ms)) with (rd W (ms_mem ms)) in RA, RF, RK;
         pose proof (SHR ms _ 21%bv (271 + 6 * p) HSP ltac:(rewrite Ep; vm_compute; reflexivity)) as Z21;
         prreg HSP (2%bv : bv 5) Z2; prreg HSP (3%bv : bv 5) Z3; prreg HSP (4%bv : bv 5) Z4;
         prreg HSP (8%bv : bv 5) Z8; prreg HSP (9%bv : bv 5) Z9; prreg HSP (18%bv : bv 5) Z18;
         prreg HSP (19%bv : bv 5) Z19; prreg HSP (20%bv : bv 5) Z20; prreg HSP (24%bv : bv 5) Z24;
         prreg HSP (1%bv : bv 5) Z1; prreg HSP (22%bv : bv 5) Z22; prreg HSP (23%bv : bv 5) Z23;
         prreg HSP (25%bv : bv 5) Z25; prreg HSP (26%bv : bv 5) Z26; prreg HSP (27%bv : bv 5) Z27;
         prreg HSP (10%bv : bv 5) Z10; prreg HSP (11%bv : bv 5) Z11; prreg HSP (12%bv : bv 5) Z12;
         prreg HSP (13%bv : bv 5) Z13; prreg HSP (14%bv : bv 5) Z14; prreg HSP (15%bv : bv 5) Z15;
         prreg HSP (16%bv : bv 5) Z16; prreg HSP (17%bv : bv 5) Z17;
         refine (POSTB ms mat _ HSP eq_refl eq_refl ltac:(vm_compute; reflexivity) HJ
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hhdn);
         [ intros a Ha H1 H2 H3 H4; apply (aview_eq_of SEGS); apply HFr;
           rewrite unsigned_lit_small by lia; intros Hw; apply pfb_inw in Hw;
           rewrite BV60, BV516, BV529 in Hw; destruct Hw as [Hw | [Hw | [Hw | Hw]]];
           [apply H1 | apply H2 | apply H3 | apply H4]; lia
         | intros a _ Hpa; exact (apresent_grows _ _ _ a HG Hpa)
         | unfold spZ; rewrite Z2, U60; rewrite unsigned_lit_small by lia; lia
         | rewrite Z3, (QX 3%bv 534%nat eq_refl); exact Rgp
         | rewrite Z4, (QX 4%bv 535%nat eq_refl); exact Rtp
         | rewrite Z8, (EE' 2%nat 2%bv eq_refl); unfold d_S, spZ, w64;
           rewrite Z_to_bv_bv_unsigned; reflexivity
         | rewrite Z9; exact E60'
         | rewrite Z19; exact E32'
         | rewrite Z18; unfold w64, WS_MASK; reflexivity
         | exact Z20
         | rewrite Z24, (QX 24%bv 555%nat eq_refl); exact R24
         | rewrite Z1; unfold BNR_OFF, w64; f_equal; lia
         | rewrite Z21; unfold w64, d_obj, dobj_off, shadow_addr; rewrite HQ13; f_equal; lia
         | rewrite Z22, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | rewrite Z23, (img_env_atomP _ 252%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)); reflexivity
         | rewrite Z25, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | rewrite Z26, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | rewrite Z27; exact ESH'
         | rewrite Z10; exact EA566
         | exact Z11
         | rewrite Z12; exact EA564
         | rewrite Z13; exact EA565
         | rewrite Z14, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | exact Z15
         | rewrite Z16, U516; unfold d_obj, dobj_off, w64; f_equal; lia
         | exact Z17
         | replace (d_obj cx OWID) with (d_FB cx + 2000) by (unfold d_obj, dobj_off; lia);
           exact (field_of_region _ _ AT_F (d_FB cx) _ _ _ _ _ 2000 4%N (SLit slot_inv.W0X0) slot_inv.W0X0
                    RF U516 (in_eq _ _) eq_refl ltac:(cbn [Z.of_N]; unfold slot_inv.W0X0; lia)
                    ltac:(cbn [Z.of_N]; lia))
         | replace (d_A cx - 16) with (d_A cx + (-16)) by lia;
           exact (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ (-16) 8%N (SOff AT_F 1920) (d_obj cx ODISP)
                    RK U60 (in_cons _ _ _ (in_eq _ _))
                    ltac:(cbn [sv_denot]; unfold AT_F; rewrite U516; unfold d_obj, dobj_off; f_equal; lia)
                    ltac:(cbn [Z.of_N]; unfold d_obj, dobj_off; lia) ltac:(cbn [Z.of_N]; lia))
         | replace (d_A cx - 8) with (d_A cx + (-8)) by lia;
           exact (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ (-8) 8%N (SLit 48) 48
                    RK U60 (in_eq _ _) eq_refl ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia))
         | eapply (field_of_region _ _ AT_A (d_A cx) _ _ _ _ _ 352 8%N _ (shadow_addr (d_obj cx OT + 48 * p + 14))
             RA U60);
           [ apply in_eq
           | lazymatch goal with |- sv_denot _ ?e = _ =>
               rewrite (SHV ms _ e (271 + 6 * p) HSP ltac:(rewrite Ep; vm_compute; reflexivity)) end;
             unfold d_obj, dobj_off, shadow_addr; rewrite HQ14; f_equal; lia
           | cbn [Z.of_N]; unfold d_obj, dobj_off, shadow_addr, SHADOW_OFF; lia
           | cbn [Z.of_N]; lia ] ] ]).
Qed.

End h.
End f.
End d.

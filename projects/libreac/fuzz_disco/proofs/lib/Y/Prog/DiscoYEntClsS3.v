(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v; 360 of its 424 lines of code are new or changed and 728 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC88 YK0w.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel CtrlParsed slot_classify.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt ClassifyCore DiscoYEntClsCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition s3_fcs : list YP09.chunk := [YP09.mkChunk 2880 (CVal 4 (SOff 563 0))].
Definition s3_wchk (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    ((match YP09.r_base r with Some q => Nat.eqb q 60 | None => false end) &&
     (YP09.r_wlo r =? 296) && (YP09.r_whi r =? 304))) rs.

Lemma s3_frame_win : forall E rs (m m' : word -> option byte) b, frame_of E rs m m' ->
  bv_unsigned (ew E 60) = b -> s3_wchk rs = true ->
  forall x : word, ~ (b + 296 <= bv_unsigned x < b + 304) -> m' x = m x.
Proof.
intros E rs m m' b HF Hb Hc x Hx. apply HF. intros (r & Hr & Ha).
unfold s3_wchk in Hc. rewrite forallb_forall in Hc. specialize (Hc r Hr).
apply orb_true_iff in Hc as [Hc | Hc]; [apply Z.leb_le in Hc; lia|].
destruct (YP09.r_base r) as [q|] eqn:Eb; [|discriminate].
apply andb_true_iff in Hc as [Hc H3]. apply andb_true_iff in Hc as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2, H3. subst q.
try rewrite Eb in Ha. cbn [base_val] in Ha. rewrite Hb, H2, H3 in Ha. apply Hx. exact Ha.
Qed.

Lemma s3_keep_aview : forall segs H (m m' : word -> option byte) b,
  (forall x : word, ~ (b + 296 <= bv_unsigned x < b + 304) -> m' x = m x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (b + 296 <= a < b + 304) -> aview segs H m' a = aview segs H m a.
Proof.
intros segs H m m' b MK a Ha Hw. apply aview_eq_of. unfold mrestrict.
rewrite (MK (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hw.
Qed.

Lemma s3_le_byte : forall (bs : list byte) j, (j < length bs)%nat ->
  YO0f.le_byte (bytes_le_to_Z bs) (length bs) j = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
intros bs j Hj. unfold YO0f.le_byte.
pose proof (YK11.bytes_le_to_Z_bound bs) as Hb. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hn.
rewrite (Z.mod_small (bytes_le_to_Z bs) (2 ^ (8 * Z.of_nat (length bs)))) by (split; [exact Hn | exact Hb]).
rewrite Z.shiftr_div_pow2 by lia.
rewrite <- (YK0w.zb_of_bytes bs j Hj). reflexivity.
Qed.

Lemma s3_vm4 : forall segs (m : word -> option byte) b (L : list byte) k,
  garr8 segs m b (map bv_unsigned L) -> (k + 4 <= length L)%nat ->
  val_mem segs m (b + Z.of_nat k) 4 (bytes_le_to_Z (firstn 4 (skipn k L))).
Proof.
intros segs m b L k HG Hkl j Hj.
set (bs := firstn 4 (skipn k L)).
assert (Hlen : length bs = 4%nat) by (subst bs; rewrite length_firstn, length_skipn; lia).
replace (YO0f.le_byte (bytes_le_to_Z bs) 4 j) with (YO0f.le_byte (bytes_le_to_Z bs) (length bs) j)
  by (rewrite Hlen; reflexivity).
rewrite s3_le_byte by lia.
assert (Hn : nth j bs (Z_to_bv 8 0) = nth (k + j) L (Z_to_bv 8 0)).
{ subst bs. rewrite nth_firstn. replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. reflexivity. }
rewrite Hn.
assert (Hj2 : (k + j < length (map bv_unsigned L))%nat) by (rewrite length_map; lia).
destruct (HG _ Hj2) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
replace (b + Z.of_nat k + Z.of_nat j) with (b + Z.of_nat (k + j) + Z.of_nat 0) by lia.
rewrite Hv. do 2 f_equal.
rewrite (nth_indep (map bv_unsigned L) 0 (bv_unsigned (Z_to_bv 8 0)) Hj2). rewrite map_nth.
apply YC88.le_byte_1_0. pose proof (bv_unsigned_in_range _ (nth (k + j) L (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. lia.
Qed.

Lemma s3_u : forall G : list byte, length G = 264%nat -> 0 <= gn G <= 8 ->
  0 <= CtrlParsed.fu G 256 4 <= 8 /\ gn G = CtrlParsed.fu G 256 4.
Proof.
intros G LG Hg. unfold gn in *.
assert (Hr : 0 <= CtrlParsed.fu G 256 4 < 2 ^ 32).
{ unfold CtrlParsed.fu. pose proof (YK11.bytes_le_to_Z_nonneg (CtrlParsed.fld G 256 4)) as H0.
  pose proof (YK11.bytes_le_to_Z_bound (CtrlParsed.fld G 256 4)) as Hb.
  rewrite (GateModel.length_fld G 256 4) in Hb by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb. lia. }
unfold CtrlParsed.s32 in *. destruct (CtrlParsed.fu G 256 4 <? 2 ^ 31); [split; [lia | reflexivity] | lia].
Qed.

Lemma s3_den : forall E u, ew E 563 = Z_to_bv 64 u -> 0 <= u <= 8 ->
  branch_taken BC_GEU (sv_denot E (SLit 8)) (sv_denot E (SExt true 32 (SOff 563 0))) = true /\
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff 563 0))) (sv_denot E (SLit 0)) = (u =? 0) /\
  sv_denot E (SExt true 32 (SOff 563 0)) = Z_to_bv 64 u /\
  sv_denot E (SAlu ALU_SLL (SExt true 32 (SOff 563 0)) (SLit 5)) = Z_to_bv 64 (32 * u).
Proof.
intros E u H Hu. cbn [sv_denot]. rewrite H.
assert (Hc : u = 0 \/ u = 1 \/ u = 2 \/ u = 3 \/ u = 4 \/ u = 5 \/ u = 6 \/ u = 7 \/ u = 8) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
  (split; apply bv_eq; vm_compute; reflexivity).
Qed.

Lemma s3_geu1 : forall p, 0 <= p <= 1 -> branch_taken BC_GEU (w64 1) (w64 p) = true.
Proof. intros p Hp. assert (Hc : p = 0 \/ p = 1) by lia. destruct Hc as [-> | ->]; vm_compute; reflexivity. Qed.

Ltac s3_win HS n lo hi :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let RO := fresh "RO" in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as RO;
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r lo hi) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r lo hi RO ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho;
     apply (proj1 (proj2 (proj2 RO))); cbn [YP09.r_wlo YP09.r_whi]; clear - Ho; lia))) as HS3;
clear HS RO; rename HS3 into HS; norm_ss HS end.

Ltac s3_awr UA AW :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat _);
    [reflexivity | exact UA | cbn [YP09.r_wlo YP09.r_whi]; clear - AW; lia
    | cbn [YP09.r_wlo YP09.r_whi]; clear - AW; lia |] ].

Ltac s3_step UA60 MK :=
  lazymatch goal with HF : frame_of ?E ?rs (ms_mem ?m0) (ms_mem ?m1) |- _ =>
    let M := fresh "M" in
    pose proof (s3_frame_win E rs (ms_mem m0) (ms_mem m1) _ HF UA60 ltac:(vm_compute; reflexivity)) as M;
    let MK2 := fresh "MK" in
    pose proof (fun x Hx => eq_trans (M x Hx) (MK x Hx)) as MK2; clear M MK HF; rename MK2 into MK end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac s3_rg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

Ltac s3_srg := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbv [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]); destruct Hr.

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

Lemma s3_env_old : forall cx E vals q, (q < AT_FL)%nat -> ew (d_env cx E vals) q = ew E q.
Proof. intros cx E vals q Hq. unfold d_env. apply ew_havoc_old. exact Hq. Qed.

Lemma s3_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
rewrite !s3_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
- intros q r Hq. rewrite s3_env_old; [exact (EE q r Hq)|].
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
- unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.

Lemma s3_env_fl : forall cx E vals,
  ew (d_env cx E vals) AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof. intros cx E vals. reflexivity. Qed.

Lemma s3_ew563 : forall cx E (regs : bvmap 5 word) u, ew (d_env cx E (cl_vals regs [w64 u])) 563 = Z_to_bv 64 u.
Proof. intros cx E regs u. reflexivity. Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
#[local] Notation DCTX := (d_ctx B MT XM_LIB RLO RHI tfib_K).

Lemma s3_post : forall cx h i n now op nb fr len (regs regs' : bvmap 5 word) ly3 S3 (W : world SEGS) m m' md k md'
  Sg G push,
  DCTX cx ly3 S3 W m md k -> DCTX cx ly3 S3 W m' md' k ->
  cl_base B cx h i n now op nb fr len regs ly3 S3 W m ->
  cl_sg cx nb len Sg W m -> cl_gate cx G W m -> 0 <= push <= 1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 296 <= a < d_A cx + 304) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  d_frame cx h dsh_rec W m' -> d_shadow cx dsh_rec W m' ->
  val_mem SEGS (rd W m') (d_A cx + 296) 8 push ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr regs' r = getr regs r) ->
  cl_base B cx h i n now op nb fr len regs' ly3 S3 W m' /\ cl_sg cx nb len Sg W m' /\ cl_gate cx G W m' /\
  cl_spl cx push W m'.
Proof.
intros cx h i n now op nb fr len regs regs' ly3 S3 W m m' md k md' Sg G push HC HC' HB HSg HGt Hp K Hfr' Hsh' V296 RG.
pose proof HB as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HspR & HspO & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan &
  Hstk & Hawr).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAc : alloc_ceiling <= d_A cx /\ d_A cx + 472 <= d_S cx /\ d_S cx <= 2 ^ 47 /\ 0 <= d_FB cx /\
  d_FB cx + 4096 <= alloc_ceiling /\ d_S cx - 607 <= d_A cx /\ 0 <= alloc_ceiling)
  by (clear - Hlo Hhi HF0 HFc HA1 Hac; unfold MFRAME, LLVMF_STK in *; lia).
clear Hal16 Hlo Hhi HF0 HFc HFia HFo HFal HFpres HSpres HWpres Efa Efl HA1 HA2 C1 C2 C3 C4 C5 Hac.
assert (VM : forall o v, 0 <= o -> o + 8 <= 296 \/ 304 <= o -> o + 8 <= 472 ->
  val_mem SEGS (rd W m) (d_A cx + o) 8 v -> val_mem SEGS (rd W m') (d_A cx + o) 8 v).
{ intros o v H1 H2 H3 Hv. eapply YC88.val_mem_aview_kept_x; [|exact Hv]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  apply K; [clear - HAc H1 H3 Hx; lia | clear - H2 Hx; lia]. }
assert (GF : forall p (L : list Z), 0 <= p -> p + Z.of_nat (length L) <= alloc_ceiling ->
  garr8 SEGS (rd W m) p L -> garr8 SEGS (rd W m') p L).
{ intros p L H1 H2 HG. eapply YC88.garr8_aview_kept; [|exact HG]. intros a Ha.
  apply K; clear - HAc H1 H2 Ha; lia. }
split; [|split; [|split]].
- unfold cl_base.
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
  split.
  { destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL, spZ in *.
    rewrite !RG by (cbv; tauto). repeat split; assumption. }
  split; [destruct Hsp0 as (S1 & S2); split; (apply VM; [lia | lia | lia | assumption])|].
  split.
  { destruct Hfrm as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
    destruct (Z.eq_dec fr 0) as [E0 | Hne].
    - subst fr. rewrite (F2 eq_refl). intros j Hj. rewrite length_map, length_firstn in Hj. lia.
    - pose proof Hblocks as (Hp0 & _).
      assert (Hin : In (fr, len) (ablocks B ly3 S3)).
      { eapply Permutation_in; [apply Permutation_sym; exact Hp0|]. unfold dxb.
        replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
      destruct (al_blocks _ _ LAWS ly3 S3 W m md fr len HAR Hin) as (_ & Hfr0 & Hfrc & _).
      pose proof (req_size_pos len ltac:(lia)) as (_ & Hrq).
      apply GF; [lia | rewrite length_map, length_firstn; lia | exact F4]. }
  split; [destruct HspR as (P1 & P2 & P3 & P4); split; [|split; [|split]];
    (apply VM; [lia | lia | lia | assumption])|].
  split; [destruct HspO as (P1 & P2); split; (apply VM; [lia | lia | lia | assumption])|].
  split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
  apply (BTOBS LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W m ly3 S3 W m' md' k (d_A cx + 296) (d_A cx + 304) []
    (fun a => d_A cx + 296 <= a < d_A cx + 304) Hbody).
  + exact (conj (proj1 HC') (proj1 (proj2 HC'))).
  + clear - HAc. unfold LLVMF_STK. lia.
  + clear - HAc. lia.
  + intros a Ha. left. exact Ha.
  + intros a Ha Hn'. exact (K a Ha Hn').
  + apply Forall_nil.
  + apply Permutation_refl.
  + exact Hfr'.
  + exact Hsh'.
- destruct HSg as (LSg & GSg & HSf). split; [exact LSg|]. split; [|exact HSf].
  apply GF; [unfold d_obj; cbn [dobj_off]; clear - HAc; lia
    | rewrite length_map, LSg; unfold d_obj; cbn [dobj_off]; clear - HAc; lia | exact GSg].
- destruct HGt as (LG & GG & HGok). split; [exact LG|]. split; [|exact HGok].
  apply GF; [unfold d_obj; cbn [dobj_off]; clear - HAc; lia
    | rewrite length_map, LG; unfold d_obj; cbn [dobj_off]; clear - HAc; lia | exact GG].
- split; [exact V296 | exact Hp].
Qed.

Lemma s3_land : forall cx h i n now op nb fr len (regs : bvmap 5 word) ly3 S3 (W : world SEGS) mem3 md3 k Sg G push
  E0 u (fq : YK11.FPState) ss ms md4 cs,
  DCTX cx ly3 S3 W mem3 md3 k -> DCTX cx ly3 S3 W (ms_mem ms) md4 k ->
  cl_base B cx h i n now op nb fr len regs ly3 S3 W mem3 ->
  cl_sg cx nb len Sg W mem3 -> cl_gate cx G W mem3 -> 0 <= push <= 1 -> getr regs 10 = w64 push -> d_E cx E0 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (cl_vals regs [w64 u])) ss (restrict (w_H W) ms) ->
  d_land_chk dsh_rec (ss_mem ss) = true ->
  nth_error (ss_mem ss) 1 = Some (YP09.mkRegion (Some AT_A) 0 472 296 304 cs) ->
  In (YP09.mkChunk 296 (CVal 8 (SOff 541 0))) cs ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> sr_get (ss_regs ss) r = sr_get cl_sr r) ->
  (forall x : word, ~ (d_A cx + 296 <= bv_unsigned x < d_A cx + 304) -> ms_mem ms x = mem3 x) ->
  cl_base B cx h i n now op nb fr len (ms_regs ms) ly3 S3 W (ms_mem ms) /\ cl_sg cx nb len Sg W (ms_mem ms) /\
  cl_gate cx G W (ms_mem ms) /\ cl_spl cx push W (ms_mem ms).
Proof.
intros cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k Sg G push E0 u fq ss ms md4 cs
  HC HC4 HB3 HSg HGt Hpush R10 HdE HS Hchk Hnth Hin Hsr MK.
pose proof HB3 as (_ & _ & _ & _ & _ & HrL & _ & _ & _ & _ & _ & _ & _ & Hbody).
pose proof Hbody as (_ & _ & _ & _ & Hframe & _).
pose proof Hframe as (E1 & _ & _ & _ & V184 & V120 & V136 & V376 & V280 & V232 & V264).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC) as (Hal16 & Hlo & Hhi & HF0 & HFc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr : 0 <= d_A cx /\ d_A cx + 472 <= 2 ^ 64) by (clear - Hlo Hhi HA1 Hac; unfold MFRAME, LLVMF_STK in *; lia).
assert (UA60 : bv_unsigned (ew (d_env cx E0 (cl_vals regs [w64 u])) 60) = d_A cx).
{ rewrite s3_env_old by (unfold AT_FL; lia). pose proof HdE as (_ & _ & _ & E60 & _). unfold AT_A in E60.
  rewrite E60. unfold w64. apply unsigned_lit_small. lia. }
pose proof (cl_regs_ok B cx E0 regs [w64 u] HdE HrL ltac:(lia)) as HROK.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 296 <= a < d_A cx + 304) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
  by exact (s3_keep_aview SEGS (w_H W) mem3 (ms_mem ms) (d_A cx) MK).
assert (VK : forall o v, 0 <= o -> o + 8 <= 296 \/ 304 <= o -> o + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + o) 8 v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + o) 8 v).
{ intros o v H1 H2 H3 Hv. eapply YC88.val_mem_aview_kept_x; [|exact Hv]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  apply K4; [clear - HAr H1 H3 Hx; lia | clear - H2 Hx; lia]. }
destruct (LAND LAWS FFL fq cx h dsh_rec ly3 S3 W md4 k (d_env cx E0 (cl_vals regs [w64 u])) ss ms HC4
  (s3_E_env cx E0 (cl_vals regs [w64 u]) HdE) (s3_env_fl cx E0 (cl_vals regs [w64 u])) HS Hchk
  (VK 184 h ltac:(lia) ltac:(lia) ltac:(lia) V184) (VK 120 (h + 440) ltac:(lia) ltac:(lia) ltac:(lia) V120)
  (VK 136 0 ltac:(lia) ltac:(lia) ltac:(lia) V136)
  (VK 376 (dnot (d_obj cx OG)) ltac:(lia) ltac:(lia) ltac:(lia) V376)
  (VK 280 (dnot (d_obj cx OT)) ltac:(lia) ltac:(lia) ltac:(lia) V280)
  (VK 232 (dnot (d_obj cx OO)) ltac:(lia) ltac:(lia) ltac:(lia) V232)
  (VK 264 (dnot (d_obj cx OUSED)) ltac:(lia) ltac:(lia) ltac:(lia) V264)) as (Hfr4 & Hsh4).
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS Hnth) as RA4.
assert (D541 : sv_denot (d_env cx E0 (cl_vals regs [w64 u])) (SOff 541 0) = Z_to_bv 64 push).
{ transitivity (getr regs 10); [|exact R10]. rewrite (HROK 10%bv). f_equal; vm_compute; reflexivity. }
pose proof (field_of_region (d_env cx E0 (cl_vals regs [w64 u])) (ms_mem (restrict (w_H W) ms)) 60 (d_A cx) cs
  0 472 296 304 296 8 (SOff 541 0) push RA4 UA60 Hin D541 ltac:(clear - Hpush; cbn; lia) ltac:(lia)) as V296.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS), (HROK r), (Hsr r Hr). reflexivity. }
exact (s3_post cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md3 k md4 Sg G push
  HC HC4 HB3 HSg HGt Hpush K4 Hfr4 Hsh4 V296 RG).
Qed.

Theorem pb_cl_L6 : cl_L6_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len W c HGR.
destruct HGR as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hev & Hmo & Hacc &
  Sg & G & push & HB3 & R22 & HSg & HGt & R10 & Hpush).
pose proof HB3 as (_ & _ & _ & _ & _ & HrL & _ & _ & _ & _ & _ & _ & _ & Hbody).
pose proof Hbody as (_ & _ & _ & _ & Hframe & _).
pose proof Hframe as (E0 & HdE & Hregs & Hflag & _).
assert (HC : DCTX cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs)).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC) as (Hal16 & Hlo & Hhi & HF0 & HFc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (clear - Hlo Hhi HA1 Hac; unfold MFRAME, LLVMF_STK in *; lia).
assert (AW : - LLVMF_STK <= d_A cx - d_S cx + 296 /\ d_A cx - d_S cx + 304 <= 0)
  by (clear - HA1; unfold MFRAME, LLVMF_STK in *; lia).
clear Hal16 Hlo Hhi HF0 HFc C1 C2 C3 C4 C5 Hac HA2.
pose proof HGt as (LG & GG & GOK).
destruct (s3_u G LG (proj1 (proj2 GOK))) as (Hu & Egn).
set (u := CtrlParsed.fu G 256 4) in *.
assert (HROK : regs_ok (d_env cx E0 (cl_vals regs [w64 u])) cl_sr regs)
  by exact (cl_regs_ok B cx E0 regs [w64 u] HdE HrL HAr2).
assert (D553 : sv_denot (d_env cx E0 (cl_vals regs [w64 u])) (SOff 553 0) = w64 1).
{ transitivity (getr regs 22); [|exact R22]. rewrite (HROK 22%bv). f_equal; vm_compute; reflexivity. }
assert (D541 : sv_denot (d_env cx E0 (cl_vals regs [w64 u])) (SOff 541 0) = w64 push).
{ transitivity (getr regs 10); [|exact R10]. rewrite (HROK 10%bv). f_equal; vm_compute; reflexivity. }
assert (E563 : ew (d_env cx E0 (cl_vals regs [w64 u])) 563 = Z_to_bv 64 u) by exact (s3_ew563 cx E0 regs u).
assert (UA60 : bv_unsigned (ew (d_env cx E0 (cl_vals regs [w64 u])) 60) = d_A cx).
{ rewrite s3_env_old by (unfold AT_FL; lia). pose proof HdE as (_ & _ & _ & E60 & _). unfold AT_A in E60.
  rewrite E60. unfold w64. apply unsigned_lit_small. exact HAr2. }
assert (UA : bv_unsigned (ew (d_env cx E0 (cl_vals regs [w64 u])) 60) = d_S cx + (d_A cx - d_S cx))
  by (rewrite UA60; ring).
assert (HEd : d_E cx (d_env cx E0 (cl_vals regs [w64 u]))) by exact (s3_E_env cx E0 _ HdE).
assert (HEI : img_env VAL A_LIM (d_env cx E0 (cl_vals regs [w64 u]))) by exact (proj1 (proj2 (proj2 HEd))).
assert (HFCS : Forall (YP09.chunk_ok SEGS (d_env cx E0 (cl_vals regs [w64 u])) (rd W mem3) (d_FB cx)) s3_fcs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) 2880 4 (SOff 563 0) u).
  - rewrite sv_denot_SOff0. exact E563.
  - clear - Hu. cbn. lia.
  - clear. cbn. lia.
  - replace (d_FB cx + 2880) with (d_obj cx OG + Z.of_nat 256) by (unfold d_obj; cbn [dobj_off]; lia).
    unfold u, CtrlParsed.fu, CtrlParsed.fld. apply (s3_vm4 SEGS); [exact GG | rewrite LG; lia]. }
assert (HFACTS : facts_ok (d_env cx E0 (cl_vals regs [w64 u])) (d_facts [] []))
  by exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E0 (cl_vals regs [w64 u]) [] [] HC HdE I I).
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E0 0xf1c cl_sr (cl_vals regs [w64 u]) [] s3_fcs []
  (d_facts [] []) HC HdE Hregs Hflag HROK HFACTS (Forall_nil _) HFCS (Forall_nil _) I (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
s3_win HS 516%nat 0 0. s3_win HS 529%nat 0 0. s3_win HS 60%nat 296 304.
clear Hregs Hflag HFACTS HFCS.
assert (MK : forall x : word, ~ (d_A cx + 296 <= bv_unsigned x < d_A cx + 304) ->
  ms_mem (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + 0xf1c)) mem3 (YK11.seg_rom SEGS)) x = mem3 x)
  by (intros x _; reflexivity).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0xf1c)) with (Z_to_bv 64 (BASE + 0xf1c)).
paj_run_to_sh RUNTO HS HJ 0xfac; [s3_awr UA AW|].
s3_step UA60 MK.
apply (BR W _ _ _ _ _ BC_GEU (SOff 553 0) (SOff 541 0) HS); intros Hc HS2; clear HS.
2: { exfalso. rewrite D553, D541, (s3_geu1 push Hpush) in Hc. discriminate. }
paj_run_to_sh RUNTO HS2 HJ 0xfac; [s3_awr UA AW|].
s3_step UA60 MK.
apply (BR W _ _ _ _ _ BC_GEU (SLit 8) (SExt true 32 (SOff 563 0)) HS2); intros Hc2 HS3; clear HS2.
2: { exfalso. rewrite (proj1 (s3_den _ u E563 Hu)) in Hc2. discriminate. }
paj_run_to_sh RUNTO HS3 HJ 0xfac; [s3_awr UA AW|].
s3_step UA60 MK.
apply (BR W _ _ _ _ _ BC_EQ (SExt true 32 (SOff 563 0)) (SLit 0) HS3); intros Hc3 HS4; clear HS3.
- paj_run_to_sh RUNTO HS4 HJ 0xfac; [s3_awr UA AW|].
  s3_step UA60 MK.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => set (md4 := mdx) in *; rename msx into msF end.
  lazymatch type of HS4 with st_ok_pi _ _ _ ?ssx _ => set (ssF := ssx) in HS4 end.
  let r := eval vm_compute in (nth 1 (ss_mem ssF) got_regionP) in
  lazymatch r with YP09.mkRegion _ _ _ _ _ ?cs =>
    destruct (s3_land cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k Sg G push E0 u fq ssF msF md4 cs
      HC (conj Hbase (conj HJ Hfrs)) HB3 HSg HGt Hpush R10 HdE HS4 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(apply in_eq) ltac:(s3_srg) MK) as (HB4 & HSg4 & HGt4 & HSpl4) end.
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS4 eq_refl) as Hms.
  apply SRr_ret. left. unfold cl_X, d_at.
  exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), md4, k, acc.
  split; [unfold cfg_at; rewrite Hms at 1; reflexivity|].
  split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hev|].
  split; [exact Hmo|]. split; [exact Hacc|].
  exists Sg, push. exact (conj HB4 (conj HSg4 HSpl4)).
- paj_run_to_sh RUNTO HS4 HJ 0xf4c; [s3_awr UA AW|].
  s3_step UA60 MK.
  rewrite (proj1 (proj2 (s3_den _ u E563 Hu))) in Hc3. apply Z.eqb_neq in Hc3.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => set (md4 := mdx) in *; rename msx into msF end.
  lazymatch type of HS4 with st_ok_pi _ _ _ ?ssx _ => set (ssF := ssx) in HS4 end.
  let r := eval vm_compute in (nth 1 (ss_mem ssF) got_regionP) in
  lazymatch r with YP09.mkRegion _ _ _ _ _ ?cs =>
    destruct (s3_land cx h i n now op nb fr len regs ly3 S3 W mem3 md3 k Sg G push E0 u fq ssF msF md4 cs
      HC (conj Hbase (conj HJ Hfrs)) HB3 HSg HGt Hpush R10 HdE HS4 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(apply in_eq) ltac:(s3_srg) MK) as (HB4 & HSg4 & HGt4 & HSpl4) end.
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS4 eq_refl) as Hms.
  s3_rg HS4 (21%bv : bv 5) Q21. s3_rg HS4 (24%bv : bv 5) Q24. s3_rg HS4 (22%bv : bv 5) Q22.
  s3_rg HS4 (26%bv : bv 5) Q26.
  apply SRr_ret. right. exists (gn G). unfold cl_LI, d_at.
  exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), md4, k, acc.
  split; [unfold cfg_at; rewrite Hms at 1; reflexivity|].
  split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hev|].
  split; [exact Hmo|]. split; [exact Hacc|].
  split; [exists Sg, G, push; exact (conj HB4 (conj HSg4 (conj HGt4 (conj eq_refl HSpl4))))|].
  split; [rewrite Egn; clear - Hc3 Hu; lia|].
  split; [rewrite Q21; reflexivity|].
  split; [rewrite Q24, (proj1 (proj2 (proj2 (s3_den _ u E563 Hu)))), Egn; reflexivity|].
  split; [rewrite Q22; reflexivity|].
  rewrite Q26, (proj2 (proj2 (proj2 (s3_den _ u E563 Hu)))), Egn. reflexivity.
Qed.

End h.
End f.
End d.

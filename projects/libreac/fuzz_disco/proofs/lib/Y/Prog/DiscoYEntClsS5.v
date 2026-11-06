(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 390 of its 421 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntClsLoop10.v, with its module paths, module names, addresses and numbers changed; 515 of its 597 lines of code are new or changed and 339 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel CtrlParsed slot_classify slot_observe.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntClsCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition cl5_acs : list YP09.chunk :=
  [YP09.mkChunk 296 (CVal 8 (SOff 565 0)); YP09.mkChunk 352 (CVal 8 (SOff 564 0));
   YP09.mkChunk 360 (CVal 8 (SOff 563 0))].
Definition cl5_fcs : list YP09.chunk := [YP09.mkChunk 3007 (CVal 1 (SOff 566 0))].
Definition cl5_rs : smem :=
  [YP09.mkRegion (Some AT_A) 0 472 0 0 (YP09.mkChunk 176 (CVal 8 (SOff AT_F 2992)) :: cl5_acs);
   YP09.mkRegion (Some AT_F) 3007 3008 3007 3008 cl5_fcs].

Lemma cl5_vm_mod : forall segs (m : word -> option byte) a v, val_mem segs m a 8 v -> val_mem segs m a 8 (v mod 2 ^ 64).
Proof.
intros segs m a v H j Hj. rewrite (H j Hj). unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_mod by (cbv; discriminate). reflexivity.
Qed.

Lemma cl5_sh_ok : forall op, 0 <= op < 256 ->
  zalu64 ALU_SRL (zalu64 ALU_SLL ((if op <? 128 then op else op - 256) mod 2 ^ 64) 57) 62 = (op / 32) mod 4.
Proof.
intros op Hop.
assert (H : forallb (fun j => Z.eqb
  (zalu64 ALU_SRL (zalu64 ALU_SLL ((if Z.of_nat j <? 128 then Z.of_nat j else Z.of_nat j - 256) mod 2 ^ 64) 57) 62)
  ((Z.of_nat j / 32) mod 4)) (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat op) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Z.eqb_eq. exact H.
Qed.

Lemma cl5_bvu8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma cl5_map_nth : forall (l : list byte) j, (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j Hj. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
apply (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) j).
Qed.

Lemma cl5_len_upd : forall (bs : list byte) x, (16 <= length bs)%nat ->
  length (Mem.upd_bytes bs 15 [x]) = length bs.
Proof. intros bs x Hl. apply Mem.upd_bytes_length. cbn [length]. lia. Qed.

Lemma cl5_nth15 : forall (bs : list byte) x d, (15 < length bs)%nat -> nth 15 (Mem.upd_bytes bs 15 [x]) d = x.
Proof.
intros bs x d Hl. unfold Mem.upd_bytes.
rewrite app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn, Nat.min_l by lia. replace (15 - 15)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma cl5_upd_nth : forall (bs : list byte) x j d, (16 <= length bs)%nat -> (j < length bs)%nat -> j <> 15%nat ->
  nth j (Mem.upd_bytes bs 15 [x]) d = nth j bs d.
Proof.
intros bs x j d Hl Hj Hne. unfold Mem.upd_bytes.
destruct (Nat.lt_ge_cases j 15) as [Hlt | Hge].
- rewrite app_nth1 by (rewrite length_firstn; lia).
  rewrite <- (firstn_skipn 15 bs) at 2. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
- rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l by lia.
  replace (j - 15)%nat with (S (j - 16))%nat by lia. cbn [nth app].
  rewrite <- (firstn_skipn 16 bs) at 2. rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn, Nat.min_l by lia. reflexivity.
Qed.

Lemma cl5_fld_sub : forall (bs : list byte) k n, CtrlParsed.fld bs k n = disco_table_c.sub bs (Z.of_nat k) n.
Proof. intros bs k n. unfold CtrlParsed.fld, disco_table_c.sub. rewrite Nat2Z.id. reflexivity. Qed.

Lemma cl5_fld_upd : forall (bs : list byte) x k n, length bs = 24%nat ->
  (k + n <= 15)%nat \/ (16 <= k)%nat -> (k + n <= 24)%nat ->
  CtrlParsed.fld (Mem.upd_bytes bs 15 [x]) k n = CtrlParsed.fld bs k n.
Proof.
intros bs x k n L Hd Hk. rewrite !cl5_fld_sub.
change (Mem.upd_bytes bs 15 [x]) with (disco_table_c.upd bs 15 [x]).
apply slot_observe.sub_upd_out; cbn [length]; rewrite ?L; lia.
Qed.

Lemma cl5_sf_upd : forall (Sg : list byte) x F U len, length Sg = 24%nat ->
  sighting_facts Sg F U len 0 -> sighting_facts (Mem.upd_bytes Sg 15 [x]) F U len 0.
Proof.
intros Sg x F U len L (H50 & Hb1 & Hb2 & Hst0 & Hstn & Hok & HF).
assert (L' : length (Mem.upd_bytes Sg 15 [x]) = 24%nat) by (rewrite cl5_len_upd; lia).
assert (E0 : CtrlParsed.fld (Mem.upd_bytes Sg 15 [x]) 0 6 = CtrlParsed.fld Sg 0 6)
  by (apply cl5_fld_upd; [exact L | left; lia | lia]).
assert (E8 : CtrlParsed.fld (Mem.upd_bytes Sg 15 [x]) 8 4 = CtrlParsed.fld Sg 8 4)
  by (apply cl5_fld_upd; [exact L | left; lia | lia]).
assert (E20 : CtrlParsed.fld (Mem.upd_bytes Sg 15 [x]) 20 4 = CtrlParsed.fld Sg 20 4)
  by (apply cl5_fld_upd; [exact L | right; lia | lia]).
assert (EB : forall j, (j < 24)%nat -> j <> 15%nat ->
  CtrlParsed.fb (Mem.upd_bytes Sg 15 [x]) j = CtrlParsed.fb Sg j).
{ intros j Hj Hne. unfold CtrlParsed.fb. f_equal. apply cl5_upd_nth; lia. }
unfold sighting_facts in *. unfold CtrlParsed.fu in *. rewrite E0, E20.
split; [exact H50|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hst0|]. split; [exact Hstn|].
split; [|exact HF].
unfold disco_classify_c.sighting_ok in *. unfold CtrlParsed.fu in *.
destruct Hok as (HL & HR & HH). rewrite E8, !EB by lia.
split; [exact L' | split; [exact HR | exact HH]].
Qed.

Ltac cl5_awr U516 HAW :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end;
  apply awr_ok_cons_ro; [clear; cbn; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat);
  [reflexivity | exact U516 | cbn [YP09.r_wlo YP09.r_whi]; exact HAW | apply awr_ok_nil].

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma cl5_ew : forall cx E regs xs j, (j < length xs)%nat ->
  ew (d_env cx E (cl_vals regs xs)) (AT_X + 32 + j) = nth j xs (Z_to_bv 64 0).
Proof.
intros cx E regs xs j Hj. unfold d_env.
replace (AT_X + 32 + j)%nat with (AT_FL + S (32 + j))%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S (32 + j)) (Z_to_bv 64 0)).
- cbn [nth]. unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq. replace (32 + j - 32)%nat with j by lia. reflexivity.
- cbn [length]. unfold cl_vals. rewrite length_app, length_map, length_seq. lia.
Qed.

Lemma cl5_den : forall cx E regs xs j v, (j < length xs)%nat -> nth j xs (Z_to_bv 64 0) = Z_to_bv 64 v ->
  sv_denot (d_env cx E (cl_vals regs xs)) (SOff (AT_X + 32 + j) 0) = Z_to_bv 64 v.
Proof.
intros cx E regs xs j v Hj Hv. cbn [sv_denot]. rewrite (cl5_ew cx E regs xs j Hj), Hv, Z.add_0_r.
apply Z_to_bv_bv_unsigned.
Qed.

Lemma cl5_old : forall cx E vals q, (q < AT_FL)%nat -> ew (d_env cx E vals) q = ew E q.
Proof. intros cx E vals q Hq. unfold d_env. apply ew_havoc_old. exact Hq. Qed.

Lemma cl5_alu : forall E a b (x y : Z), sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  forall op, sv_denot E (SAlu op a b) = Z_to_bv 64 (zalu64 op x y).
Proof. intros E a b x y Ha Hb op. cbn [sv_denot]. rewrite Ha, Hb. apply zalu64_sound. Qed.

Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma cl5_keep_gen : forall (Ed : env) (rs : smem) (W : world SEGS) (m m' : word -> option byte) (x0 : Z),
  frame_of Ed rs (rd W m) (rd W m') ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> x0 -> ~ in_wrange Ed rs a) ->
  forall a, 0 <= a < 2 ^ 64 -> a <> x0 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros Ed rs W m m' x0 HF Hno a Ha Hne. apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by lia. exact (Hno a Ha Hne).
Qed.

Ltac cl5_keep nm x0 U516 :=
  match goal with
  | HFx : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?m) (mrestrict (w_H ?Wx) ?m') |- _ =>
      pose proof (cl5_keep_gen Ex rs Wx m m' x0 HFx
        ltac:(intros aa Haa Hnee Hw; destruct Hw as (rr & Hin & Hr);
              let l := eval vm_compute in rs in change (In rr l) in Hin;
              cbn [In] in Hin;
              repeat (destruct Hin as [<- | Hin];
                [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U516 in Hr; lia |]);
              destruct Hin)) as nm;
      clear HFx
  end.

Lemma cl5_trans : forall (W : world SEGS) (m1 m2 m3 : word -> option byte) (x0 : Z),
  (forall a, 0 <= a < 2 ^ 64 -> a <> x0 -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> x0 -> aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m2 a) ->
  forall a, 0 <= a < 2 ^ 64 -> a <> x0 -> aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m1 a.
Proof. intros W m1 m2 m3 x0 K1 K2 a Ha Hne. rewrite (K2 a Ha Hne). exact (K1 a Ha Hne). Qed.

Lemma cl5_byte15 : forall (fq : YK11.FPState) (Ed : env) (ss : sstate) (W : world SEGS) (ms : machine_state)
  (cs : list YP09.chunk) (e : sv) (v fb : Z),
  st_ok_pi (fx := fq) SEGS VAL Ed ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 1 =
    Some (YP09.mkRegion (Some 516%nat) 3007 3008 3007 3008 (YP09.mkChunk 3007 (CVal 1 e) :: cs)) ->
  bv_unsigned (ew Ed 516) = fb -> sv_denot Ed e = Z_to_bv 64 v -> 0 <= v < 256 ->
  val_mem SEGS (rd W (ms_mem ms)) (fb + 3007) 1 v.
Proof.
intros fq Ed ss W ms cs e v fb HS Hnth Hfb He Hv.
pose proof (st_ok_pi_region_nth Ed ss (restrict (w_H W) ms) 1%nat _ HS Hnth) as HR.
cbn [ms_mem restrict] in HR.
exact (field_of_region Ed _ 516%nat fb _ 3007 3008 3007 3008 3007 1%N e v HR Hfb
  (or_introl eq_refl) He ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; lia) ltac:(cbn; lia)).
Qed.

Lemma cl5_garr : forall cx (W : world SEGS) (m m' : word -> option byte) (Sg Sg' : list byte),
  length Sg = 24%nat -> length Sg' = 24%nat ->
  (forall j, (j < 24)%nat -> j <> 15%nat -> nth j Sg' (Z_to_bv 8 0) = nth j Sg (Z_to_bv 8 0)) ->
  garr8 SEGS (rd W m) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> d_FB cx + 3007 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  val_mem SEGS (rd W m') (d_FB cx + 3007) 1 (bv_unsigned (nth 15 Sg' (Z_to_bv 8 0))) ->
  0 <= d_FB cx -> d_FB cx + 3072 < 2 ^ 64 ->
  garr8 SEGS (rd W m') (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg').
Proof.
intros cx W m m' Sg Sg' LSg LSg' Hnth GSg Kall HB15 HF0 HF1 j Hj.
rewrite length_map, LSg' in Hj. rewrite (cl5_map_nth Sg' j ltac:(lia)).
pose proof (bv_unsigned_in_range 8 (nth j Sg' (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr.
destruct (Nat.eq_dec j 15) as [-> | Hne].
- split; [|lia].
  replace (d_obj cx OS + Z.of_nat 15) with (d_FB cx + 3007) by (unfold d_obj; cbn [dobj_off]; lia).
  exact HB15.
- rewrite (Hnth j ltac:(lia) Hne).
  destruct (GSg j ltac:(rewrite length_map, LSg; lia)) as (G1 & G2).
  rewrite (cl5_map_nth Sg j ltac:(lia)) in G1, G2.
  split; [|exact G2].
  eapply YC88.val_mem_aview_kept_x; [|exact G1]. intros x Hx. change (Z.of_nat 1) with 1 in Hx.
  apply Kall; unfold d_obj in *; cbn [dobj_off] in *; lia.
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
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.

Lemma cl5_keepall : forall cx h n nb fr len ly3 S3 (W : world SEGS) mem3 mem' md3 md' k k',
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem' md' k' ->
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W mem3 -> d_frm cx nb fr len W mem3 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> d_FB cx + 3007 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem3 a) ->
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W mem' /\ d_frm cx nb fr len W mem' /\
  (forall off v, 0 <= off -> off + 8 <= 472 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
     val_mem SEGS (rd W mem') (d_A cx + off) 8 v).
Proof.
intros cx h n nb fr len ly3 S3 W mem3 mem' md3 md' k k' HC HC' Hbody Hfrm Kall.
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan &
  Hstk & Hawr).
assert (HSHb : 0 <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 < 2 ^ 64).
{ pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSH.
  unfold kLowMemEnd, kHighShadowEnd in *. lia. }
assert (Kfr : forall a, (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/
   (d_FB cx <= a < d_FB cx + 24) \/ (d_FB cx + 4088 <= a < d_FB cx + 4096) \/
   (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) ->
   aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem3 a).
{ intros a [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply Kall; unfold MFRAME, LLVMF_STK in *; lia.
  - apply Kall; unfold MFRAME, LLVMF_STK in *; lia.
  - apply Kall; lia.
  - apply Kall; lia.
  - apply Kall; [lia|].
    exact (cl_sh_frame cx a (d_FB cx + 3007) HFia ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (Hframe' : d_frame cx h dsh_rec W mem')
  by exact (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W mem3 ly3 S3 W mem' md' k' HC' Hframe Kfr).
assert (Hshadow' : d_shadow cx dsh_rec W mem')
  by exact (cl_shadow_keep cx dsh_rec W W mem3 mem' Hshadow
       (fun a Ha => Kfr a (or_intror (or_intror (or_intror (or_intror Ha)))))).
assert (VA : forall off v, 0 <= off -> off + 8 <= 472 -> val_mem SEGS (rd W mem3) (d_A cx + off) 8 v ->
  val_mem SEGS (rd W mem') (d_A cx + off) 8 v).
{ intros off v H1 H2 HV. eapply YC88.val_mem_aview_kept_x; [|exact HV]. intros x Hx.
  change (Z.of_nat 8) with 8 in Hx. apply Kall; unfold MFRAME, LLVMF_STK in *; lia. }
split.
{ apply (BTOBS LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 ly3 S3 W mem' md' k'
    (d_S cx - LLVMF_STK) (d_S cx) [OS] (fun a => a = d_FB cx + 3007) Hbody
    (conj (proj1 HC') (proj1 (proj2 HC')))).
  - lia.
  - lia.
  - intros a ->. right. left. apply Exists_cons_hd. unfold d_objr, d_obj. cbn [dobj_off dobj_size]. lia.
  - intros a Ha Hne. apply Kall; [exact Ha | exact Hne].
  - apply Forall_cons; [exact I | apply Forall_nil].
  - apply Permutation_refl.
  - exact Hframe'.
  - exact Hshadow'. }
split; [|exact VA].
pose proof Hfrm as (F1 & F2 & F3 & F4).
split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
destruct (Z.eq_dec fr 0) as [E0 | Hne].
- subst fr. rewrite (F2 eq_refl). intros j Hj. rewrite length_map, length_firstn in Hj. lia.
- pose proof Hblocks as (Hp & _).
  assert (Hin : In (fr, len) (ablocks B ly3 S3)).
  { eapply Permutation_in; [apply Permutation_sym; exact Hp|]. unfold dxb.
    replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
  destruct (al_blocks SEGS B LAWS ly3 S3 W mem3 md3 fr len HAR Hin) as (Hfr16 & Hfr0 & Hfrc & _).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 fr len DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
  rewrite Efa, cl_fs6 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos len ltac:(lia)) as Hrq.
  eapply YC88.garr8_aview_kept; [|exact F4]. intros a Ha. rewrite length_map in Ha.
  assert (Hl : Z.of_nat (length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) <= len)
    by (rewrite length_firstn; lia).
  apply Kall; lia.
Qed.

Lemma cl5_post_obs : forall (fq : YK11.FPState) cx h i n now op nb fr len (Sg : list byte) ly3 S3
  (W : world SEGS) md' k acc (E : env) (ss : sstate) (ms : machine_state),
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= cl_kmax i -> st_nev S3 <= st_nev (c_S cx) + cl_kmax i ->
  mo_le MT (c_S cx) S3 acc -> acc <= cl_amax MT i ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = OBS_OFF ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  (op mod 4 = 0 \/ op mod 4 = 1) -> 0 <= op < 256 ->
  d_rL B cx (ms_regs ms) -> d_sp0 cx i now W (ms_mem ms) -> d_frm cx nb fr len W (ms_mem ms) ->
  length Sg = 24%nat ->
  garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) ->
  sighting_facts Sg (cl_F (c_pl cx) nb len) (our_of (c_pl cx)) len 0 ->
  d_spREC cx nb fr len W (ms_mem ms) -> d_spOP cx op W (ms_mem ms) ->
  len <= nb -> nb - len <= Z.max 0 (c_n cx - 7) ->
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) ->
  obs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg W (mkCfg ms md').
Proof.
intros fq cx h i n now op nb fr len Sg ly3 S3 W md' k acc E ss ms
  Hbase HFRM0 HJ Hfrs Hk Hnev Hmo Hacc HS Hrv Hpc Hi Hn Hnow Hop Hop2 HrL Hsp0 Hfrm LSg GSg HSf HspREC HspOP
  Hlen Hnbl Hbody.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact HrL|]. split; [exact I|].
split; [|split; [exact Hsp0 | exact Hbody]].
split; [exact Hop|]. split; [exact Hop2|]. split; [exact Hfrm|]. split; [exact LSg|]. split; [exact GSg|].
split; [exact HSf|]. split; [exact HspREC|]. split; [exact HspOP|]. split; [exact Hlen | exact Hnbl].
Qed.

Lemma cl5_post_r27 : forall (fq : YK11.FPState) cx h i now nb fr len ly3 S3
  (W : world SEGS) md' k acc (E : env) (ss : sstate) (ms : machine_state),
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= cl_kmax i -> st_nev S3 <= st_nev (c_S cx) + cl_kmax i ->
  mo_le MT (c_S cx) S3 acc -> acc <= cl_amax MT i ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = R27_OFF ->
  0 <= i < MAX_OPS -> 0 <= now < 2 ^ 64 ->
  d_rL B cx (ms_regs ms) -> d_sp0 cx i now W (ms_mem ms) -> d_frm cx nb fr len W (ms_mem ms) ->
  d_spREC cx nb fr len W (ms_mem ms) -> len <= nb -> 0 <= nb - len ->
  d_body B cx h (nb - len) (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms) ->
  r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len W (mkCfg ms md').
Proof.
intros fq cx h i now nb fr len ly3 S3 W md' k acc E ss ms
  Hbase HFRM0 HJ Hfrs Hk Hnev Hmo Hacc HS Hrv Hpc Hi Hnow HrL Hsp0 Hfrm HspREC Hlen Hn Hbody.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact HrL|]. split; [exact I|].
split; [|split; [exact Hsp0 | exact Hbody]].
split; [exact Hfrm|]. split; [exact HspREC|]. split; [exact Hlen | reflexivity].
Qed.

Theorem pb_cl_L10 : cl_L10_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len W c HX.
destruct HX as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Sg & push & HB3 & HSg & Hspl).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HspREC & HspOP & Hlen & Hnbl & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan &
  Hstk & Hawr).
pose proof Hframe as (E & HdE & HRG & HFL & _).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (cl_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (cl_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof HSg as (LSg & GSg & HSf). pose proof Hspl as (V296 & Hpush). pose proof HspOP as (V360 & V352).
pose proof (cl5_vm_mod _ _ _ _ V352) as V352m.
set (b15 := bv_unsigned (nth 15 Sg (Z_to_bv 8 0))) in *.
set (xs := [w64 op; w64 ((if op <? 128 then op else op - 256) mod 2 ^ 64); w64 push; Z_to_bv 64 b15]).
assert (Hb15r : 0 <= b15 < 256).
{ unfold b15. pose proof (bv_unsigned_in_range 8 (nth 15 Sg (Z_to_bv 8 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr. lia. }
assert (G15 : val_mem SEGS (rd W mem3) (d_FB cx + 3007) 1 b15).
{ destruct (GSg 15%nat ltac:(rewrite length_map, LSg; lia)) as (G1 & G2).
  rewrite (cl5_map_nth Sg 15%nat ltac:(lia)) in G1.
  replace (d_FB cx + 3007) with (d_obj cx OS + Z.of_nat 15) by (unfold d_obj; cbn [dobj_off]; lia).
  exact G1. }
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs xs)) (rd W mem3) (d_A cx)) cl5_acs).
{ unfold cl5_acs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS (d_env cx E (cl_vals regs xs)) (rd W mem3) (d_A cx) 296 8 (SOff 565 0) push);
      [exact (cl5_den cx E regs xs 2 push ltac:(cbn; lia) eq_refl)
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V296].
  - apply (chunk_ok_val SEGS (d_env cx E (cl_vals regs xs)) (rd W mem3) (d_A cx) 352 8 (SOff 564 0)
      ((if op <? 128 then op else op - 256) mod 2 ^ 64));
      [exact (cl5_den cx E regs xs 1 _ ltac:(cbn; lia) eq_refl)
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | lia | exact V352m].
  - apply (chunk_ok_val SEGS (d_env cx E (cl_vals regs xs)) (rd W mem3) (d_A cx) 360 8 (SOff 563 0) op);
      [exact (cl5_den cx E regs xs 0 op ltac:(cbn; lia) eq_refl)
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V360]. }
assert (HFCS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs xs)) (rd W mem3) (d_FB cx)) cl5_fcs).
{ unfold cl5_fcs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS (d_env cx E (cl_vals regs xs)) (rd W mem3) (d_FB cx) 3007 1 (SOff 566 0) b15);
    [exact (cl5_den cx E regs xs 3 b15 ltac:(cbn; lia) eq_refl)
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | exact G15]. }
pose proof (cl_regs_ok B cx E regs xs HdE HrL HAr2) as HROK.
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0xfac cl_sr (cl_vals regs xs) cl5_acs cl5_fcs []
  (d_facts [] []) HC HdE HRG HFL HROK
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs xs) [] [] HC HdE I I) HACS HFCS (Forall_nil _) I (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
unfold ss_d in HS0.
assert (HSUB : submem cl5_rs (d_kregions dsh_rec cl5_acs cl5_fcs ++ [])).
{ unfold cl5_rs, d_kregions. cbn [app]. apply submem_drop.
  apply submem_keep; [|apply submem_keep; [|apply submem_nil]].
  - unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|].
    intros c0 Hc0. apply in_or_app. destruct Hc0 as [<- | Hc0]; [left; clear; cbn; tauto | right; exact Hc0].
  - unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite cl_fs6. unfold DFRAME_SIZE.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|].
    intros c0 Hc0. apply in_or_app. right. exact Hc0. }
pose proof (st_ok_pi_submem _ _ _ cl5_rs HS0 HSUB ltac:(vm_compute; reflexivity)) as HS1.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS1. clear HS0.
set (Ed := d_env cx E (cl_vals regs xs)) in *.
assert (HEI : img_env VAL A_LIM Ed).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold Ed, d_env.
  rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
pose proof HdE as (EE & E32 & _ & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
assert (U516 : bv_unsigned (ew Ed 516) = d_FB cx).
{ unfold Ed. rewrite cl5_old by (unfold AT_FL; lia). rewrite E516. unfold w64. apply unsigned_lit_small. lia. }
assert (D564 : sv_denot Ed (SOff 564 0) = Z_to_bv 64 ((if op <? 128 then op else op - 256) mod 2 ^ 64))
  by exact (cl5_den cx E regs xs 1 _ ltac:(cbn; lia) eq_refl).
assert (D566 : sv_denot Ed (SOff 566 0) = Z_to_bv 64 b15)
  by exact (cl5_den cx E regs xs 3 b15 ltac:(cbn; lia) eq_refl).
assert (Dsh : sv_denot Ed (SAlu ALU_SRL (SAlu ALU_SLL (SOff 564 0) (SLit 57)) (SLit 62)) =
  Z_to_bv 64 ((op / 32) mod 4)).
{ rewrite (cl5_alu Ed (SAlu ALU_SLL (SOff 564 0) (SLit 57)) (SLit 62)
    (zalu64 ALU_SLL ((if op <? 128 then op else op - 256) mod 2 ^ 64) 57) 62
    (cl5_alu Ed (SOff 564 0) (SLit 57) ((if op <? 128 then op else op - 256) mod 2 ^ 64) 57 D564 eq_refl ALU_SLL)
    eq_refl ALU_SRL).
  rewrite (cl5_sh_ok op ltac:(lia)). reflexivity. }
assert (Hv4 : 0 <= (op / 32) mod 4 < 256)
  by (pose proof (Z.mod_pos_bound (op / 32) 4 ltac:(lia)); lia).
assert (HAW : forall a, d_FB cx + 3007 <= a < d_FB cx + 3008 ->
  awr_byte LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
    [(DFRAME_CLASS, c_fpos cx)] a).
{ intros a Ha. exact (proj1 (Hawr a ltac:(unfold DFRAME_SIZE; lia))). }
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0xfac)) with (Z_to_bv 64 (BASE + 0xfac)).
paj_run_to_sh RUNTO HS1 HJ 0xfe0; [cl5_awr U516 HAW|].
cl5_keep K1 (d_FB cx + 3007) U516.
psrr_branch_pi RUNP BR HS1.
- paj_run_to_sh RUNTO HS1 HJ 0xfe0; [cl5_awr U516 HAW|].
  cl5_keep K2 (d_FB cx + 3007) U516.
  psrr_branch_pi RUNP BR HS1.
  + paj_run_to_sh RUNTO HS1 HJ 0x1d14; [cl5_awr U516 HAW|].
    cl5_keep K3 (d_FB cx + 3007) U516.
    lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ =>
      pose proof (cl5_trans W mem3 _ _ (d_FB cx + 3007) (cl5_trans W mem3 _ _ (d_FB cx + 3007) K1 K2) K3) as Kall;
      assert (HCf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msf) mdf k)
        by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]);
      assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
          getr (ms_regs msf) r = getr regs r)
        by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) Ed _ _ r HS1), (HROK r);
            cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
      assert (HrL' : d_rL B cx (ms_regs msf))
        by (pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27);
            unfold d_rL; unfold spZ in Hsp |- *; rewrite !RG by (cbv; tauto); repeat split; assumption);
      destruct (cl5_keepall cx h n nb fr len ly3 S3 W mem3 (ms_mem msf) md3 mdf k k HC HCf Hbody Hfrm Kall)
        as (Hbody' & Hfrm' & VA);
      assert (Hsp0' : d_sp0 cx i now W (ms_mem msf))
        by (destruct Hsp0 as (A1 & A2); split; apply VA; first [lia | assumption]);
      assert (HspREC' : d_spREC cx nb fr len W (ms_mem msf))
        by (destruct HspREC as (A1 & A2 & A3 & A4); split; [|split; [|split]]; apply VA;
            first [lia | assumption]);
      pose proof (cl_body_n B cx h n (nb - len) (dxb fr len) dsh_rec ly3 S3 W (ms_mem msf) Hbody'
        ltac:(lia)) as Hbodyn;
      apply SRr_ret; unfold cl_post; right;
      eapply cl5_post_r27;
        [exact Hbase | exact HFRM0 | exact HJ | exact Hfrs | exact Hk | exact Hnev | exact Hmo | exact Hacc | exact HS1
        | reflexivity | reflexivity | exact Hi | exact Hnow | exact HrL' | exact Hsp0' | exact Hfrm'
        | exact HspREC' | exact Hlen | lia | exact Hbodyn] end.
  + paj_run_to_sh RUNTO HS1 HJ 0xfe0; [cl5_awr U516 HAW|].
    cl5_keep K3 (d_FB cx + 3007) U516.
    lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ =>
      pose proof (cl5_trans W mem3 _ _ (d_FB cx + 3007) (cl5_trans W mem3 _ _ (d_FB cx + 3007) K1 K2) K3) as Kall;
      assert (HCf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msf) mdf k)
        by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]);
      assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
          getr (ms_regs msf) r = getr regs r)
        by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) Ed _ _ r HS1), (HROK r);
            cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
      assert (HrL' : d_rL B cx (ms_regs msf))
        by (pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27);
            unfold d_rL; unfold spZ in Hsp |- *; rewrite !RG by (cbv; tauto); repeat split; assumption);
      destruct (cl5_keepall cx h n nb fr len ly3 S3 W mem3 (ms_mem msf) md3 mdf k k HC HCf Hbody Hfrm Kall)
        as (Hbody' & Hfrm' & VA);
      assert (Hsp0' : d_sp0 cx i now W (ms_mem msf))
        by (destruct Hsp0 as (A1 & A2); split; apply VA; first [lia | assumption]);
      assert (HspREC' : d_spREC cx nb fr len W (ms_mem msf))
        by (destruct HspREC as (A1 & A2 & A3 & A4); split; [|split; [|split]]; apply VA;
            first [lia | assumption]);
      assert (HspOP' : d_spOP cx op W (ms_mem msf))
        by (destruct HspOP as (A1 & A2); split; apply VA; first [lia | assumption]);
      assert (HB15 : val_mem SEGS (rd W (ms_mem msf)) (d_FB cx + 3007) 1 b15)
        by (eapply (cl5_byte15 fq Ed _ W msf [] (SOff 566 0) b15 (d_FB cx) HS1);
            [vm_compute; reflexivity | exact U516 | exact D566 | lia]);
      assert (GSg' : garr8 SEGS (rd W (ms_mem msf)) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg))
        by (apply (cl5_garr cx W mem3 (ms_mem msf) Sg Sg LSg LSg ltac:(intros jj Hjj Hne; reflexivity) GSg Kall
             HB15 ltac:(lia) ltac:(lia)));
      apply SRr_ret; unfold cl_post; left; exists Sg;
      eapply cl5_post_obs;
        [exact Hbase | exact HFRM0 | exact HJ | exact Hfrs | exact Hk | exact Hnev | exact Hmo | exact Hacc | exact HS1
        | reflexivity | reflexivity | exact Hi | exact Hn | exact Hnow | exact Hop | exact Hop2 | exact HrL'
        | exact Hsp0' | exact Hfrm' | exact LSg | exact GSg' | exact HSf | exact HspREC' | exact HspOP'
        | exact Hlen | exact Hnbl | exact Hbody'] end.
- paj_run_to_sh RUNTO HS1 HJ 0xfe0; [cl5_awr U516 HAW|].
  cl5_keep K2 (d_FB cx + 3007) U516.
  psrr_branch_pi RUNP BR HS1.
  + paj_run_to_sh RUNTO HS1 HJ 0x1d14; [cl5_awr U516 HAW|].
    cl5_keep K3 (d_FB cx + 3007) U516.
    lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ =>
      pose proof (cl5_trans W mem3 _ _ (d_FB cx + 3007) (cl5_trans W mem3 _ _ (d_FB cx + 3007) K1 K2) K3) as Kall;
      assert (HCf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msf) mdf k)
        by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]);
      assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
          getr (ms_regs msf) r = getr regs r)
        by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) Ed _ _ r HS1), (HROK r);
            cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
      assert (HrL' : d_rL B cx (ms_regs msf))
        by (pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27);
            unfold d_rL; unfold spZ in Hsp |- *; rewrite !RG by (cbv; tauto); repeat split; assumption);
      destruct (cl5_keepall cx h n nb fr len ly3 S3 W mem3 (ms_mem msf) md3 mdf k k HC HCf Hbody Hfrm Kall)
        as (Hbody' & Hfrm' & VA);
      assert (Hsp0' : d_sp0 cx i now W (ms_mem msf))
        by (destruct Hsp0 as (A1 & A2); split; apply VA; first [lia | assumption]);
      assert (HspREC' : d_spREC cx nb fr len W (ms_mem msf))
        by (destruct HspREC as (A1 & A2 & A3 & A4); split; [|split; [|split]]; apply VA;
            first [lia | assumption]);
      pose proof (cl_body_n B cx h n (nb - len) (dxb fr len) dsh_rec ly3 S3 W (ms_mem msf) Hbody'
        ltac:(lia)) as Hbodyn;
      apply SRr_ret; unfold cl_post; right;
      eapply cl5_post_r27;
        [exact Hbase | exact HFRM0 | exact HJ | exact Hfrs | exact Hk | exact Hnev | exact Hmo | exact Hacc | exact HS1
        | reflexivity | reflexivity | exact Hi | exact Hnow | exact HrL' | exact Hsp0' | exact Hfrm'
        | exact HspREC' | exact Hlen | lia | exact Hbodyn] end.
  + paj_run_to_sh RUNTO HS1 HJ 0xfe0; [cl5_awr U516 HAW|].
    cl5_keep K3 (d_FB cx + 3007) U516.
    lazymatch goal with |- SRr _ _ (mkCfg ?msf ?mdf) _ =>
      pose proof (cl5_trans W mem3 _ _ (d_FB cx + 3007) (cl5_trans W mem3 _ _ (d_FB cx + 3007) K1 K2) K3) as Kall;
      assert (HCf : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msf) mdf k)
        by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]);
      assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
          getr (ms_regs msf) r = getr regs r)
        by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) Ed _ _ r HS1), (HROK r);
            cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
      assert (HrL' : d_rL B cx (ms_regs msf))
        by (pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27);
            unfold d_rL; unfold spZ in Hsp |- *; rewrite !RG by (cbv; tauto); repeat split; assumption);
      destruct (cl5_keepall cx h n nb fr len ly3 S3 W mem3 (ms_mem msf) md3 mdf k k HC HCf Hbody Hfrm Kall)
        as (Hbody' & Hfrm' & VA);
      assert (Hsp0' : d_sp0 cx i now W (ms_mem msf))
        by (destruct Hsp0 as (A1 & A2); split; apply VA; first [lia | assumption]);
      assert (HspREC' : d_spREC cx nb fr len W (ms_mem msf))
        by (destruct HspREC as (A1 & A2 & A3 & A4); split; [|split; [|split]]; apply VA;
            first [lia | assumption]);
      assert (HspOP' : d_spOP cx op W (ms_mem msf))
        by (destruct HspOP as (A1 & A2); split; apply VA; first [lia | assumption]);
      assert (LSg' : length (Mem.upd_bytes Sg 15 [Z_to_bv 8 ((op / 32) mod 4)]) = 24%nat)
        by (rewrite cl5_len_upd; lia);
      assert (HB15 : val_mem SEGS (rd W (ms_mem msf)) (d_FB cx + 3007) 1 ((op / 32) mod 4))
        by (eapply (cl5_byte15 fq Ed _ W msf []
              (SAlu ALU_SRL (SAlu ALU_SLL (SOff 564 0) (SLit 57)) (SLit 62)) ((op / 32) mod 4) (d_FB cx) HS1);
            [vm_compute; reflexivity | exact U516 | exact Dsh | lia]);
      assert (HN15 : bv_unsigned (nth 15 (Mem.upd_bytes Sg 15 [Z_to_bv 8 ((op / 32) mod 4)]) (Z_to_bv 8 0)) =
          (op / 32) mod 4)
        by (rewrite cl5_nth15 by lia; apply cl5_bvu8; lia);
      assert (GSg' : garr8 SEGS (rd W (ms_mem msf)) (d_obj cx OS)
          (map (fun b : byte => bv_unsigned b) (Mem.upd_bytes Sg 15 [Z_to_bv 8 ((op / 32) mod 4)])))
        by (apply (cl5_garr cx W mem3 (ms_mem msf) Sg (Mem.upd_bytes Sg 15 [Z_to_bv 8 ((op / 32) mod 4)])
             LSg LSg' ltac:(intros jj Hjj Hne; apply cl5_upd_nth; lia) GSg Kall
             ltac:(rewrite HN15; exact HB15) ltac:(lia) ltac:(lia)));
      assert (HSf' : sighting_facts (Mem.upd_bytes Sg 15 [Z_to_bv 8 ((op / 32) mod 4)])
          (cl_F (c_pl cx) nb len) (our_of (c_pl cx)) len 0)
        by (apply cl5_sf_upd; [exact LSg | exact HSf]);
      apply SRr_ret; unfold cl_post; left; exists (Mem.upd_bytes Sg 15 [Z_to_bv 8 ((op / 32) mod 4)]);
      eapply cl5_post_obs;
        [exact Hbase | exact HFRM0 | exact HJ | exact Hfrs | exact Hk | exact Hnev | exact Hmo | exact Hacc | exact HS1
        | reflexivity | reflexivity | exact Hi | exact Hn | exact Hnow | exact Hop | exact Hop2 | exact HrL'
        | exact Hsp0' | exact Hfrm' | exact LSg' | exact GSg' | exact HSf' | exact HspREC' | exact HspOP'
        | exact Hlen | exact Hnbl | exact Hbody'] end.
Qed.

End h.
End f.
End d.

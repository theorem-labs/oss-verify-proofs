(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 551 of its 591 lines of code are new or changed and 505 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition y2_sr (ai : Z) : list sv :=
  map (fun r => match r with 10%nat => SLit ai | 23%nat => SOff AT_F 2992 | _ => sr_x r end) (seq 0 32).
Definition y2_acs : list YP09.chunk :=
  map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (SOff (snd kv) 0)))
  [(360, 563%nat); (320, 564%nat); (208, 565%nat); (184, 566%nat); (120, 567%nat); (136, 568%nat);
   (376, 569%nat); (280, 570%nat); (232, 571%nat); (264, 572%nat); (200, 573%nat); (328, 574%nat);
   (368, 575%nat); (408, 576%nat)].
Definition y2_tcs : list YP09.chunk :=
  [YP09.mkChunk 2544 (CVal 4 (SOff 577 0)); YP09.mkChunk 2548 (CVal 4 (SOff 578 0)); YP09.mkChunk 2552 (CVal 4 (SOff 579 0))].
Definition y2_ecs (ai : Z) : list YP09.chunk :=
  if ai <? 0 then [] else
  map (fun kv => YP09.mkChunk (2160 + 48 * ai + fst (fst kv)) (CVal (snd (fst kv)) (SOff (snd kv) 0)))
  [(8, 4%N, 580%nat); (12, 1%N, 581%nat); (13, 1%N, 582%nat); (14, 1%N, 583%nat); (15, 1%N, 584%nat);
   (16, 1%N, 585%nat); (20, 4%N, 586%nat); (24, 4%N, 587%nat); (32, 8%N, 588%nat)].
Definition y2_G : facts := d_facts [(570%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] [].

Lemma y2_u_rng : forall (T : list byte) p (n : nat), 0 <= u_at T p n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T p n. unfold u_at. pose proof (YK11.bytes_le_to_Z_nonneg (sub T p n)) as H0.
pose proof (YK11.bytes_le_to_Z_bound (sub T p n)) as H1.
assert (L : (length (sub T p n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma y2_w64_u64 : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v.
Proof. intros v. unfold u64. exact (Z_to_bv64_canon v). Qed.
Lemma y2_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma y2_nth_le_byte : forall bs k (b : byte),
  nth_error bs k = Some b -> bv_unsigned b = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
induction bs as [|b0 bs IHbs]; intros k b H; [destruct k; discriminate H|].
rewrite y2_ble_cons. pose proof (u8_range b0) as Hb0. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
destruct k as [|k].
- cbn in H. injection H as <-. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. lia.
- cbn [nth_error] in H. rewrite (IHbs k b H).
  replace (8 * Z.of_nat (Datatypes.S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite <- Z.div_div by lia. f_equal. f_equal. lia.
Qed.

Section u.
Variable E : env.
Lemma y2_dn_sx32 : forall a u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros a u H Hu. rewrite denot_lit_U, U_SExt, (U_atom E a u H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia. exact (Z_to_bv64_canon _).
Qed.
Lemma y2_dn_zx8 : forall a u, ew E a = Z_to_bv 64 u -> 0 <= u < 256 ->
  sv_denot E (SExt false 8 (SOff a 0)) = Z_to_bv 64 u.
Proof.
intros a u H Hu. rewrite denot_lit_U, U_SExt, (U_atom E a u H) by lia. cbv iota.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small u) by lia. exact (Z_to_bv64_canon _).
Qed.
Lemma y2_dn_own : forall a w, ew E a = Z_to_bv 64 (u64 w) ->
  sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff a 0) (SLit 60)) (SLit 63)) = Z_to_bv 64 ((u64 w / 8) mod 2).
Proof.
intros a w H. pose proof (oy_u64_rng w) as R.
rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, U_SLit, (U_atom E a (u64 w) H R).
change (Z.land (zcanon 60) 63) with 60. change (Z.land (zcanon 63) 63) with 63.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. f_equal. unfold zcanon, M64.
set (x := u64 w) in *. clearbody x.
change (2 ^ 60) with 1152921504606846976 in *. change (2 ^ 63) with 9223372036854775808 in *.
change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.
Lemma y2_dn_sx32u : forall a (T : list byte) p, ew E a = Z_to_bv 64 (u_at T p 4) ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 (u_at T p 4)).
Proof.
intros a T p H. apply (y2_dn_sx32 a _ H). pose proof (y2_u_rng T p 4) as R.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R.
Qed.
Lemma y2_dn_zx8u : forall a (T : list byte) p, ew E a = Z_to_bv 64 (u_at T p 1) ->
  sv_denot E (SExt false 8 (SOff a 0)) = Z_to_bv 64 (u_at T p 1).
Proof.
intros a T p H. apply (y2_dn_zx8 a _ H). pose proof (y2_u_rng T p 1) as R.
change (2 ^ (8 * Z.of_nat 1)) with 256 in R. exact R.
Qed.
End u.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Context {PX : PAXcalls lib_both3_0_listing}.

Lemma y2_vm_u64 : forall m a v, val_mem SEGS m a 8 v <-> val_mem SEGS m a 8 (u64 v).
Proof.
intros m a v. unfold val_mem, u64.
split; intros H k Hk; rewrite (H k Hk); first [unfold YO0f.le_byte | unfold YG0f.le_byte];
change (8 * Z.of_nat 8) with 64; rewrite ?Zmod_mod; reflexivity.
Qed.
Lemma y2_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) L) -> nth_error L j = Some b ->
  mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base _ j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth _ j 0 (map_nth_error (fun b : byte => bv_unsigned b) j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.
Lemma y2_u_val : forall (m : word -> option byte) t (T : list byte) p (n : nat),
  length T = 400%nat -> garr8 SEGS m t (map (fun b : byte => bv_unsigned b) T) ->
  0 <= p -> p + Z.of_nat n <= 400 ->
  val_mem SEGS m (t + p) n (u_at T p n).
Proof.
intros m t T p n LT GT Hp Hpn k Hk.
assert (Hlen : length (sub T p n) = n) by (unfold sub; rewrite length_firstn, length_skipn, LT; lia).
pose proof (y2_u_rng T p n) as Hb.
destruct (nth_error T (Z.to_nat p + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + p + Z.of_nat k) with (t + Z.of_nat (Z.to_nat p + k)) by lia.
rewrite (y2_garr8_nth m t T _ b GT Hb2). f_equal.
rewrite le_byte_small by first [exact Hk | exact Hb].
assert (Hs : nth_error (sub T p n) k = Some b).
{ unfold sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec k n); [|lia]. rewrite nth_error_skipn. exact Hb2. }
pose proof (y2_nth_le_byte _ _ _ Hs) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold u_at. rewrite <- Hv. first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.
Lemma y2_pres_grow : forall (H : word -> bool) (m1 m2 : word -> option byte),
  mem_grows (mrestrict H m1) (mrestrict H m2) -> forall a, apresent H m1 a -> apresent H m2 a.
Proof.
intros H m1 m2 HG a (Hh & b & Hb). split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|]. exfalso. apply HG; [discriminate | reflexivity].
Qed.
Lemma y2_atom : forall cx E (regs : bvmap 5 word) X j, (j < length X)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (563 + j) = nth j X (Z_to_bv 64 0).
Proof.
intros cx E regs X j Hj.
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite oy_d_env_x by (rewrite length_app; lia).
rewrite app_nth2 by lia. rewrite L. f_equal. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (oc B).
#[local] Notation ob_c2 := (ob_c2 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c3 := (ob_c3 B MT XM_LIB RLO RHI tfib_K).

Definition y2_x (cx : dcx) (h i now op nb fr len : Z) (T : list byte) (ai : Z) : list word :=
  [w64 (u64 op); w64 (u64 now); w64 (u64 i); w64 (u64 h); w64 (u64 (h + 440)); w64 (u64 0);
   w64 (u64 (dnot (d_obj cx OG))); w64 (u64 (dnot (d_obj cx OT))); w64 (u64 (dnot (d_obj cx OO)));
   w64 (u64 (dnot (d_obj cx OUSED))); w64 (u64 (d_cur cx nb)); w64 (u64 nb); w64 (u64 fr); w64 (u64 len);
   w64 (u_at T 384 4); w64 (u_at T 388 4); w64 (u_at T 392 4);
   w64 (u_at T (48 * ai + 8) 4); w64 (u_at T (48 * ai + 12) 1); w64 (u_at T (48 * ai + 13) 1);
   w64 (u_at T (48 * ai + 14) 1); w64 (u_at T (48 * ai + 15) 1); w64 (u_at T (48 * ai + 16) 1);
   w64 (u_at T (48 * ai + 20) 4); w64 (u_at T (48 * ai + 24) 4); w64 (u_at T (48 * ai + 32) 8)].

Lemma y2_regs_ok : forall cx E (regs : bvmap 5 word) ai X, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  getr regs 10 = w64 ai -> getr regs 23 = w64 (d_obj cx OS) ->
  regs_ok (d_env cx E (obs_vals regs ++ X)) (y2_sr ai) regs.
Proof.
intros cx E regs ai X HE HL HA R10 R23.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
pose proof HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
assert (LO : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
assert (D60 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D32 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact E32).
assert (D529 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact ESH).
assert (D516 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 516 2992) = w64 (d_obj cx OS)).
{ cbn [sv_denot]. rewrite oy_d_env_old by (unfold AT_FL; lia). change 516%nat with AT_F. rewrite EF.
  unfold w64. rewrite oy_w64_add_w. reflexivity. }
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 32)%nat ->
  sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff q 0) = nth j (obs_vals regs) (Z_to_bv 64 0)).
{ intros j q -> Hj. rewrite sv_denot_SOff0. rewrite oy_d_env_x by (rewrite length_app; lia).
  apply app_nth1. lia. }
apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
repeat (destruct Hz as [<-|Hz];
  [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
      let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
    lazymatch goal with
    | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
    | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 | exact R10 ]
    | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
        first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
    | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
    | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
    | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
    | |- _ = sv_denot _ (SOff 516 2992) => rewrite D516; exact R23
    | |- _ = sv_denot _ (SOff ?q 0) =>
        let j := eval vm_compute in (q - 531)%nat in
        rewrite (DX j q eq_refl ltac:(lia)); unfold obs_vals; cbn [nth map seq];
        f_equal; vm_compute; reflexivity
    end
  | ]).
destruct Hz.
Qed.

Lemma y2_seat : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T ai (regs : bvmap 5 word) ly3 S3 W mem3 md3 k E,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W mem3)) (d_regions cx dsh_rec) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  val_mem SEGS (rd W mem3) (d_A cx + 184) 8 h -> val_mem SEGS (rd W mem3) (d_A cx + 120) 8 (h + 440) ->
  val_mem SEGS (rd W mem3) (d_A cx + 136) 8 0 ->
  val_mem SEGS (rd W mem3) (d_A cx + 376) 8 (dnot (d_obj cx OG)) ->
  val_mem SEGS (rd W mem3) (d_A cx + 280) 8 (dnot (d_obj cx OT)) ->
  val_mem SEGS (rd W mem3) (d_A cx + 232) 8 (dnot (d_obj cx OO)) ->
  val_mem SEGS (rd W mem3) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)) ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W mem3 ->
  getr regs 10 = w64 ai -> getr regs 23 = w64 (d_obj cx OS) -> -1 <= ai < 8 ->
  val_mem SEGS (rd W mem3) (d_A cx + 360) 8 op ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai))
    (ss_d OB_FE_RET (y2_sr ai) dsh_rec y2_acs (y2_tcs ++ y2_ecs ai) [] y2_G)
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + OB_FE_RET)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now op nb fr len Sg T ai regs ly3 S3 W mem3 md3 k E HC HE HRG HFL
  V184 V120 V136 V376 V280 V232 V264 HOC R10 R23 Hai V360.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (V208 & V320) & Hfrm & HSgl & HSg & HSf &
  (V200 & V328 & V368 & V408) & Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof HC as (_ & HJ & _).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (_ & _ & _ & HF0 & HFc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (XA : forall j, (j < 26)%nat -> ew (d_env cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai)) (563 + j) =
  nth j (y2_x cx h i now op nb fr len T ai) (Z_to_bv 64 0)) by (intros j Hj; apply y2_atom; cbn; lia).
apply (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_FE_RET (y2_sr ai)
  (obs_vals regs ++ y2_x cx h i now op nb fr len T ai) y2_acs (y2_tcs ++ y2_ecs ai) [] y2_G HC HE HRG HFL).
- exact (y2_regs_ok cx E regs ai _ HE HrL HAr2 R10 R23).
- apply (FACTS LAWS cx ly3 S3 W mem3 md3 k E _ _ [] HC HE); [|exact I].
  cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (X7 : ew (d_env cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai)) 570 =
    w64 (u64 (dnot (d_obj cx OT)))) by exact (XA 7%nat ltac:(lia)).
  rewrite X7. unfold w64. rewrite unsigned_lit_small by (apply oy_u64_rng).
  rewrite Z.pow_0_r, Z.mod_1_r. rewrite oy_u64_small by (unfold dnot, d_obj, dobj_off; lia).
  unfold dnot, d_obj, dobj_off. lia.
- unfold y2_acs. cbn [map fst snd].
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?q 0))) =>
    let j := eval vm_compute in (q - 563)%nat in
    let v := eval cbn [nth y2_x] in (nth j (y2_x cx h i now op nb fr len T ai) (Z_to_bv 64 0)) in
    lazymatch v with w64 (u64 ?z) =>
      apply (chunk_ok_val SEGS _ _ _ o 8 _ (u64 z));
      [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | apply oy_u64_rng | cbn; lia
      | apply (proj1 (y2_vm_u64 _ _ z)); assumption ]
    end
  end.
- apply Forall_app. split.
  + unfold y2_tcs. repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 4 (SOff ?q 0))) =>
      let j := eval vm_compute in (q - 563)%nat in
      let v := eval cbn [nth y2_x] in (nth j (y2_x cx h i now op nb fr len T ai) (Z_to_bv 64 0)) in
      lazymatch v with w64 (u_at T ?p 4) =>
        apply (chunk_ok_val SEGS _ _ _ o 4 _ (u_at T p 4));
        [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | exact (y2_u_rng T p 4) | cbn; lia
        | replace (d_FB cx + o) with (d_obj cx OT + p) by (unfold d_obj, dobj_off; lia);
          exact (y2_u_val _ _ T p 4 HTl HT ltac:(lia) ltac:(lia)) ]
      end
    end.
  + unfold y2_ecs. destruct (Z.ltb_spec ai 0) as [Hneg|Hpos]; [apply Forall_nil|].
    cbn [map fst snd].
    repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?wd (SOff ?q 0))) =>
      let j := eval vm_compute in (q - 563)%nat in
      let v := eval cbn [nth y2_x] in (nth j (y2_x cx h i now op nb fr len T ai) (Z_to_bv 64 0)) in
      lazymatch v with w64 (u_at T ?p ?nn) =>
        apply (chunk_ok_val SEGS _ _ _ o wd _ (u_at T p nn));
        [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | exact (y2_u_rng T p nn) | cbn; lia
        | replace (d_FB cx + o) with (d_obj cx OT + p) by (unfold d_obj, dobj_off; lia);
          exact (y2_u_val _ _ T p nn HTl HT ltac:(lia) ltac:(lia)) ]
      end
    end.
- apply Forall_nil.
- exact I.
- apply Forall_nil.
- assert (Hc : ai = -1 \/ ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
  repeat (destruct Hc as [-> | Hc]; [vm_compute; reflexivity|]). subst ai. vm_compute; reflexivity.
Qed.

Lemma y2_oc_keep : forall cx h i n now op nb fr len Sg T (regs regs' : bvmap 5 word) ly3 S3 W mem3 mem' md k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem' md k ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W mem3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem3 a) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem' a) ->
  d_rL B cx regs' ->
  d_frame cx h dsh_rec W mem' -> d_shadow cx dsh_rec W mem' ->
  d_sp0 cx i now W mem' -> d_spREC cx nb fr len W mem' ->
  oc cx h i n now op nb fr len Sg T regs' ly3 S3 W mem'.
Proof.
intros cx h i n now op nb fr len Sg T regs regs' ly3 S3 W mem3 mem' md k HC HOC MEQ MPR HrL' HF' HSh' HSP' HREC'.
destruct HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC & Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & _ & _ & _ & HBL & _).
pose proof HC as (_ & HJ & _).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem' md k HC)
  as (_ & HSlo & _ & HF4 & HFc & _ & _ & _ & _ & _ & _ & HAR & _).
destruct (oy_A_range B cx ly3 S3 W mem' md k HJ) as (HSr & _ & HAr & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FAR : forall a, 0 <= a < d_S cx - LLVMF_STK -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply MEQ; unfold LLVMF_STK in *; lia. }
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj HrL' (conj HSP' (conj _ (conj HSgl (conj _ (conj HSf
  (conj HREC' (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok _))))))))))))))))).
- destruct Hfrm as (F1 & F2 & F0 & F3). split; [exact F1|]. split; [exact F2|]. split; [exact F0|].
  apply (oy_garr8_keep W W mem3 mem' fr); [|exact F3].
  intros j Hj. rewrite length_map, length_firstn in Hj.
  destruct (Z.eq_dec len 0) as [L0|L0]; [subst len; cbn in Hj; lia|].
  assert (Hfr0 : fr <> 0) by (intros E0; apply L0; exact (F2 E0)).
  assert (Hin : In (fr, len) (ablocks B ly3 S3)).
  { destruct HBL as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
    rewrite (proj2 (Z.eqb_neq fr 0) Hfr0). left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4k & Hpc & _).
  assert (Hrq : req_size len = len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
  rewrite Hrq in Hpc. apply FAR. unfold LLVMF_STK in *. lia.
- apply (oy_garr8_keep W W mem3 mem' _); [|exact HSg].
  intros j Hj. rewrite length_map, HSgl in Hj. apply FAR. unfold d_obj, dobj_off, LLVMF_STK in *. lia.
- apply (oy_garr8_keep W W mem3 mem' _); [|exact HT].
  intros j Hj. rewrite length_map, HTl in Hj. apply FAR. unfold d_obj, dobj_off, LLVMF_STK in *. lia.
- apply (BRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 mem' (d_A cx) (d_A cx + 472)
    (fun a => d_A cx <= a < d_A cx + 472) Hbody).
  + unfold LLVMF_STK in *. lia.
  + lia.
  + intros a Ha. left. exact Ha.
  + intros a Ha HnR. exact (MEQ a Ha HnR).
  + intros a _ Ha. exact (MPR a Ha).
  + exact HF'.
  + exact HSh'.
  + lia.
Qed.

Lemma y2_rL_keep : forall cx (regs regs' : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr regs' r = getr regs r) ->
  d_rL B cx regs -> d_rL B cx regs'.
Proof.
intros cx regs regs' RG (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL, spZ in *.
rewrite (RG 2%bv ltac:(cbv; tauto)), (RG 3%bv ltac:(cbv; tauto)), (RG 4%bv ltac:(cbv; tauto)),
  (RG 8%bv ltac:(cbv; tauto)), (RG 9%bv ltac:(cbv; tauto)), (RG 19%bv ltac:(cbv; tauto)),
  (RG 18%bv ltac:(cbv; tauto)), (RG 20%bv ltac:(cbv; tauto)), (RG 27%bv ltac:(cbv; tauto)).
repeat split; assumption.
Qed.

Lemma y2_land : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T kmax accmax ly3 S3 W mem3 md4 k acc E ss ms
   (regs : bvmap 5 word) pc (X : bvmap 5 word -> world SEGS -> (word -> option byte) -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax -> mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  0 <= flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx) < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_land_chk dsh_rec (ss_mem ss) = true ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W mem3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  d_rL B cx (ms_regs ms) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 184) 8 h ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 120) 8 (h + 440) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 136) 8 0 ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 376) 8 (dnot (d_obj cx OG)) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 280) 8 (dnot (d_obj cx OT)) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 232) 8 (dnot (d_obj cx OO)) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED)) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 208) 8 i -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 320) 8 now ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 200) 8 (d_cur cx nb) -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 328) 8 nb ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 fr -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 408) 8 len ->
  X (ms_regs ms) W (ms_mem ms) ->
  DAT cx pc kmax accmax (fun regs' ly' S' W' mem' md' => oc cx h i n now op nb fr len Sg T regs' ly' S' W' mem' /\ X regs' W' mem')
    W (mkCfg ms md4).
Proof.
intros fq cx h i n now op nb fr len Sg T kmax accmax ly3 S3 W mem3 md4 k acc E ss ms regs pc X
  HFRM0 HB HJ HFR Hk Hev Hmo Hacc HE HFL HFLr HS Hrv Hpc Hchk HOC MEQ MPR HrL'
  V184 V120 V136 V376 V280 V232 V264 V208 V320 V200 V328 V368 V408 HX.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (oy_land B MT XM_LIB RLO RHI tfib_K fq cx h dsh_rec ly3 S3 W md4 k E ss ms LAWS HC HE HFL HFLr HS Hchk
  V184 V120 V136 V376 V280 V232 V264) as [HF' HSh'].
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFRM0|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [|exact HX].
exact (y2_oc_keep cx h i n now op nb fr len Sg T regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md4 k HC HOC MEQ MPR HrL'
  HF' HSh' (conj V208 V320) (conj V200 (conj V328 (conj V368 V408)))).
Qed.

Definition y2_X3 (cx : dcx) (T : list byte) (ai ow now : Z) (regs : bvmap 5 word) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  ob_sp22 cx T ai W m /\ val_mem SEGS (rd W m) (d_A cx + 360) 8 ow /\
  getr regs 1 = w64 (BASE + OB_TO_RET) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 11 = w64 (d_obj cx OS) /\
  getr regs 12 = w64 ow /\ getr regs 13 = w64 now /\ getr regs 25 = w64 (n_of T) /\ getr regs 26 = w64 ai /\
  getr regs 22 = w64 (ov_of T) /\ getr regs 21 = w64 (s32_at T 392).
Lemma y2_c3_of : forall cx h i n now op nb fr len Sg kmax accmax T ai ow W c,
  find_res T (s_mac Sg) ai -> (ow = 0 \/ ow = 1) ->
  DAT cx AF_both3_reac_disco_table_observe kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T regs ly S W' m /\ y2_X3 cx T ai ow now regs W' m) W c ->
  ob_c3 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T ai ow W c HFR How
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFRM0 & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc.
refine (conj Hc (conj HFRM0 (conj HB (conj HJ (conj HF (conj Hk (conj Hev (conj Hmo (conj Hacc _))))))))).
destruct X as (XSP & X360 & X1 & X10 & X11 & X12 & X13 & X25 & X26 & X22 & X21).
exists T, ai, ow.
exact (conj HOC (conj HFR (conj How (conj XSP (conj X360 (conj X1 (conj X10 (conj X11 (conj X12 (conj X13
  (conj (conj X25 X26) (conj X22 X21)))))))))))).
Qed.

Ltac y2_dn0 :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity
  | |- sv_denot ?Ex (SOff 240 ?kk) = _ =>
      lazymatch goal with HE : img_env _ _ Ex |- _ => exact (codeptr_val Ex kk HE) end
  | |- sv_denot _ (SOff 516 _) = _ =>
      cbn [sv_denot]; lazymatch goal with H : ew _ 516 = _ |- _ => rewrite H end; unfold w64; rewrite oy_w64_add_w; reflexivity
  | |- sv_denot _ (SOff ?q 0) = _ =>
      rewrite sv_denot_SOff0; lazymatch goal with H : ew _ q = _ |- _ => rewrite H end; unfold w64; rewrite ?y2_w64_u64; reflexivity
  | |- sv_denot _ (SExt true 32 (SOff ?q 0)) = _ =>
      lazymatch goal with H : ew _ q = _ |- _ => rewrite (y2_dn_sx32u _ _ _ _ H) end; reflexivity
  | |- sv_denot _ (SExt false 8 (SOff ?q 0)) = _ =>
      lazymatch goal with H : ew _ q = _ |- _ => rewrite (y2_dn_zx8u _ _ _ _ H) end; reflexivity
  | |- sv_denot _ (SAlu ALU_SRL (SAlu ALU_SLL (SOff ?q 0) (SLit 60)) (SLit 63)) = _ =>
      lazymatch goal with H : ew _ q = _ |- _ => rewrite (y2_dn_own _ _ _ H) end; reflexivity
  end.
Ltac y2_fld RA UA :=
  eapply (YCjr.field_of_region _ _ 60 _ _ _ _ _ _ _ 8 _ _ RA);
  [ exact UA | cbn [In]; repeat (first [left; reflexivity | right]) | rewrite y2_w64_u64; y2_dn0 | apply oy_u64_rng | cbn; lia ].
Ltac y2_reg HSpi :=
  lazymatch goal with |- getr (ms_regs ?msx) ?r = _ =>
    rewrite (st_ok_pi_restrict_reg _ _ _ msx r HSpi);
    lazymatch type of HSpi with st_ok_pi _ _ _ ?ssx _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e end;
    unfold w64; y2_dn0 end.
Ltac y2_hwin UA :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | rewrite UA in Ha; lia ] | ]);
  destruct Hin.
Ltac y2_awr UA :=
  cbn [ss_mem];
  repeat (first [ apply awr_ok_cons_ro; [cbn; lia|]
                | eapply awr_ok_cons_gen; [reflexivity | exact UA | intros a Ha; left; cbn [YP09.r_wlo YP09.r_whi] in Ha;
                    unfold LLVMF_STK in *; lia | ] ]);
  apply awr_ok_nil.
Ltac y2_post HSpi :=
  lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
    rewrite (pa_sigma_reac_disco_table_observe (PI := PI)) in HS;
    lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
      assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_both3_reac_disco_table_observe) msx) by exact HS end;
    clear HS end.

Theorem ob_s23 : ob_seg23 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & T & ai &
  HOC & V360 & R23 & R10 & HFR).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (V208 & V320) & Hfrm & HSgl & HSg & HSf & (V200 & V328 & V368 & V408) &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & V184 & V120 & V136 & V376 & V280 & V232 & V264).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (HFLr : 0 <= flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx) < 2 ^ 64) by exact (oy_rdword_aview_range SEGS _ _ _ _ Hflag).
assert (Hai : -1 <= ai < 8) by (destruct HTok as (HT1 & _); unfold tbl_T1 in HT1; destruct HFR as [[-> _] | (Hr & _)]; lia).
pose proof (y2_seat fq cx h i n now op nb fr len Sg T ai regs ly3 S3 W mem3 md3 k E HC HdE Hregs Hflag
  V184 V120 V136 V376 V280 V232 V264 HOC R10 R23 Hai V360) as HS.
assert (XA : forall j, (j < 26)%nat -> ew (d_env cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai)) (563 + j) =
  nth j (y2_x cx h i now op nb fr len T ai) (Z_to_bv 64 0)) by (intros j Hj; apply y2_atom; cbn; lia).
pose proof (XA 0%nat ltac:(lia)) as AX563. pose proof (XA 1%nat ltac:(lia)) as AX564. pose proof (XA 2%nat ltac:(lia)) as AX565.
pose proof (XA 3%nat ltac:(lia)) as AX566. pose proof (XA 4%nat ltac:(lia)) as AX567. pose proof (XA 5%nat ltac:(lia)) as AX568.
pose proof (XA 6%nat ltac:(lia)) as AX569. pose proof (XA 7%nat ltac:(lia)) as AX570. pose proof (XA 8%nat ltac:(lia)) as AX571.
pose proof (XA 9%nat ltac:(lia)) as AX572. pose proof (XA 10%nat ltac:(lia)) as AX573. pose proof (XA 11%nat ltac:(lia)) as AX574.
pose proof (XA 12%nat ltac:(lia)) as AX575. pose proof (XA 13%nat ltac:(lia)) as AX576. pose proof (XA 14%nat ltac:(lia)) as AX577.
pose proof (XA 15%nat ltac:(lia)) as AX578. pose proof (XA 16%nat ltac:(lia)) as AX579. pose proof (XA 17%nat ltac:(lia)) as AX580.
pose proof (XA 18%nat ltac:(lia)) as AX581. pose proof (XA 19%nat ltac:(lia)) as AX582. pose proof (XA 20%nat ltac:(lia)) as AX583.
pose proof (XA 21%nat ltac:(lia)) as AX584. pose proof (XA 22%nat ltac:(lia)) as AX585. pose proof (XA 23%nat ltac:(lia)) as AX586.
pose proof (XA 24%nat ltac:(lia)) as AX587. pose proof (XA 25%nat ltac:(lia)) as AX588.
cbn [nth y2_x Nat.add] in AX563, AX564, AX565, AX566, AX567, AX568, AX569, AX570, AX571, AX572, AX573, AX574, AX575, AX576,
  AX577, AX578, AX579, AX580, AX581, AX582, AX583, AX584, AX585, AX586, AX587, AX588.
clear XA.
pose proof (y2_regs_ok cx E regs ai (y2_x cx h i now op nb fr len T ai) HdE HrL HAr2 R10 R23) as A1.
pose proof (oy_d_E_env cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai) HdE) as HdE'.
pose proof (oy_d_env_fl cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai)) as HFL'.
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai)))
  by exact (proj1 (proj2 (proj2 HdE'))).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai)) (rd W mem3))
  by constructor.
set (Ev := d_env cx E (obs_vals regs ++ y2_x cx h i now op nb fr len T ai)) in *. clearbody Ev.
pose proof HdE' as (_ & _ & _ & E60 & E516 & _). change AT_A with 60%nat in E60. change AT_F with 516%nat in E516.
assert (UA : bv_unsigned (ew Ev 60) = d_A cx) by (rewrite E60; apply unsigned_lit_small; lia).
pose (RUN := paj_run (fx := fq) (PL := PL_both3_0) B LAWS).
set (ow := (u64 op / 8) mod 2).
assert (How : ow = 0 \/ ow = 1) by (pose proof (Z.mod_pos_bound (u64 op / 8) 2 ltac:(lia)); unfold ow; lia).
unfold cfg_at. change (w64 (BASE + OB_FE_RET)) with (Z_to_bv 64 (BASE + OB_FE_RET)).
assert (Hc : ai = -1 \/ ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
clear Hai.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
all: (unfold ss_d in HS; ro_base HS 516%nat; ro_base HS 529%nat;
  paj_run_tok RUN HS HJ SHOK OBspan; [y2_awr UA|];
  y2_post HSpi;
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *;
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
    by (apply (kept_of_frame (segs := SEGS) _ _ (w_H W) mem3 (ms_mem ms) (fun a => d_A cx <= a < d_A cx + 472) HFr);
        y2_hwin UA);
  pose proof (y2_pres_grow (w_H W) mem3 (ms_mem ms) HG) as MPR;
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r)
    by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
        rewrite (st_ok_pi_restrict_reg _ _ _ ms r HSpi), (A1 r);
        cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
  pose proof (y2_rL_keep cx regs (ms_regs ms) RG HrL) as HrL';
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HSpi eq_refl) as RA; cbn [ms_mem restrict] in RA;
  assert (W184 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 184) 8 (u64 h)) by (y2_fld RA UA);
  assert (W120 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 120) 8 (u64 (h + 440))) by (y2_fld RA UA);
  assert (W136 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 136) 8 (u64 0)) by (y2_fld RA UA);
  assert (W376 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 376) 8 (u64 (dnot (d_obj cx OG)))) by (y2_fld RA UA);
  assert (W280 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 280) 8 (u64 (dnot (d_obj cx OT)))) by (y2_fld RA UA);
  assert (W232 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 232) 8 (u64 (dnot (d_obj cx OO)))) by (y2_fld RA UA);
  assert (W264 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 264) 8 (u64 (dnot (d_obj cx OUSED)))) by (y2_fld RA UA);
  assert (W208 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 208) 8 (u64 i)) by (y2_fld RA UA);
  assert (W320 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 320) 8 (u64 now)) by (y2_fld RA UA);
  assert (W200 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 200) 8 (u64 (d_cur cx nb))) by (y2_fld RA UA);
  assert (W328 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 328) 8 (u64 nb)) by (y2_fld RA UA);
  assert (W368 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 (u64 fr)) by (y2_fld RA UA);
  assert (W408 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 408) 8 (u64 len)) by (y2_fld RA UA);
  apply SRr_ret;
  apply (y2_c3_of cx h i n now op nb fr len Sg kmax accmax T _ ow W _ HFR How);
  apply (y2_land fq cx h i n now op nb fr len Sg T kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs _ _ HFRM0 Hbase HJ Hfrs Hk Hnev
    Hmo Hacc HdE' HFL' HFLr HSpi eq_refl eq_refl ltac:(vm_compute; reflexivity) HOC MEQ MPR HrL'
    (proj2 (y2_vm_u64 _ _ _) W184) (proj2 (y2_vm_u64 _ _ _) W120) (proj2 (y2_vm_u64 _ _ _) W136)
    (proj2 (y2_vm_u64 _ _ _) W376) (proj2 (y2_vm_u64 _ _ _) W280) (proj2 (y2_vm_u64 _ _ _) W232)
    (proj2 (y2_vm_u64 _ _ _) W264) (proj2 (y2_vm_u64 _ _ _) W208) (proj2 (y2_vm_u64 _ _ _) W320)
    (proj2 (y2_vm_u64 _ _ _) W200) (proj2 (y2_vm_u64 _ _ _) W328) (proj2 (y2_vm_u64 _ _ _) W368)
    (proj2 (y2_vm_u64 _ _ _) W408));
  unfold y2_X3, ob_sp22;
  repeat match goal with |- _ /\ _ => split end;
  first [ y2_reg HSpi | y2_fld RA UA | apply (proj2 (y2_vm_u64 _ _ _)); y2_fld RA UA ]).
Qed.
End h.
End f.
End d.

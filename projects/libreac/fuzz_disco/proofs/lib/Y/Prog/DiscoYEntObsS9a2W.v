(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 631 of its 671 lines of code are new or changed and 505 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe.
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

Definition w9_acs : list YP09.chunk :=
  map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (SOff (snd kv) 0)))
  [(184, 564%nat); (120, 565%nat); (136, 566%nat); (376, 567%nat); (280, 568%nat); (232, 569%nat);
   (264, 570%nat); (208, 571%nat); (320, 572%nat); (200, 573%nat); (328, 574%nat); (368, 575%nat);
   (408, 576%nat); (352, 577%nat); (192, 578%nat); (104, 579%nat); (96, 580%nat); (88, 581%nat);
   (80, 582%nat); (296, 583%nat); (72, 584%nat); (48, 585%nat); (8, 586%nat); (0, 587%nat)].
Definition w9_fcs : list YP09.chunk := [YP09.mkChunk 2544 (CVal 4 (SOff 563 0))].

Lemma w9_u_rng : forall (T : list byte) p (n : nat), 0 <= u_at T p n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T p n. unfold u_at. pose proof (YK11.bytes_le_to_Z_nonneg (sub T p n)) as H0.
pose proof (YK11.bytes_le_to_Z_bound (sub T p n)) as H1.
assert (L : (length (sub T p n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma w9_w64_u64 : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v.
Proof. intros v. unfold u64. exact (Z_to_bv64_canon v). Qed.
Lemma w9_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
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
Lemma w9_nth_le_byte : forall bs k (b : byte),
  nth_error bs k = Some b -> bv_unsigned b = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
induction bs as [|b0 bs IHbs]; intros k b H; [destruct k; discriminate H|].
rewrite w9_ble_cons. pose proof (u8_range b0) as Hb0. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
destruct k as [|k].
- cbn in H. injection H as <-. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. lia.
- cbn [nth_error] in H. rewrite (IHbs k b H).
  replace (8 * Z.of_nat (Datatypes.S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite <- Z.div_div by lia. f_equal. f_equal. lia.
Qed.
Lemma w9_nth_sub : forall (L : list byte) k n j d, 0 <= k -> (j < n)%nat -> nth j (sub L k n) d = nth (Z.to_nat k + j) L d.
Proof.
intros L k n j d Hk Hj. unfold sub. rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj).
rewrite nth_skipn. reflexivity.
Qed.
Lemma w9_mod32_8 : forall a, a mod 32 = 0 -> a mod 8 = 0.
Proof.
intros a H. pose proof (Z.div_mod a 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D. replace (32 * (a / 32)) with (4 * (a / 32) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma w9_pres : forall a b (r : bv 5), aregs_preserved a b -> acallee_saved (bv_unsigned r) -> getr b r = getr a r.
Proof. intros a b r H Hr. pose proof (H (bv_unsigned r) Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.

Lemma w9_keep : forall T Sg ow now T' ret ai,
  length T = 400%nat -> length Sg = 24%nat -> disco_table_c.table_ok T ->
  find_res T (s_mac Sg) ai -> 0 <= ai ->
  reac_disco_table_observe_c.observe_model T Sg ow now T' ret ->
  sub T' (48 * ai) 6 = sub Sg 0 6 /\ bv_swrap 32 (u_at T' 384 4) = n_of T.
Proof.
intros T Sg ow now T' ret ai LT LS (T1 & _) FR Hai OM.
pose proof T1 as T1'. unfold tbl_T1 in T1'.
assert (Hr8 : 0 <= ai < 8) by (destruct FR as [[? _]|[? _]]; lia).
pose proof (slot_observe.known_arm T Sg ow now T' ret ai FR Hai OM) as E.
destruct (slot_observe.ok_facts T Sg ow now ai T' ret LT LS Hr8 E) as (LT' & EM & E384 & _).
split; [|exact (slot_observe.n_of_sub T T' E384)].
change (mac_of T' ai = s_mac Sg). rewrite (EM ai Hr8).
destruct FR as [[? _] | (_ & M & _)]; [lia | exact M].
Qed.

Ltac w9_rr H := lazymatch type of H with _ = sv_denot _ (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v in H end.
Ltac w9_cs := unfold acallee_saved;
  repeat match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Section u.
Variable E : env.
Lemma w9_dn_sx32 : forall a u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros a u H Hu. rewrite denot_lit_U, U_SExt, (U_atom E a u H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia. exact (Z_to_bv64_canon _).
Qed.
Lemma w9_sv_atom : forall q v, ew E q = Z_to_bv 64 v -> sv_denot E (SOff q 0) = Z_to_bv 64 v.
Proof. intros q v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma w9_ew_of_sv : forall q w, sv_denot E (SOff q 0) = w -> ew E q = w.
Proof. intros q w H. cbn [sv_denot] in H. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma w9_br_ne_false : forall a b, sv_denot E a = sv_denot E b -> branch_taken BC_NE (sv_denot E a) (sv_denot E b) = false.
Proof. intros a b H. rewrite branch_ne_U. unfold U. rewrite H, Z.eqb_refl. reflexivity. Qed.
End u.

Ltac w9_dn0 :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity
  | |- sv_denot ?Ex (SOff 240 ?kk) = _ =>
      lazymatch goal with HE : img_env _ _ Ex |- _ => exact (codeptr_val Ex kk HE) end
  | |- sv_denot _ (SOff 516 _) = _ =>
      cbn [sv_denot]; lazymatch goal with H : ew _ 516 = _ |- _ => rewrite H end; unfold w64; rewrite oy_w64_add_w; reflexivity
  | |- sv_denot _ (SOff ?q 0) = _ =>
      rewrite sv_denot_SOff0; lazymatch goal with H : ew _ q = _ |- _ => rewrite H end; unfold w64; rewrite ?w9_w64_u64; reflexivity
  end.
Ltac w9_fld RA UA :=
  eapply (YCjr.field_of_region _ _ 60 _ _ _ _ _ _ _ 8 _ _ RA);
  [ exact UA | cbn [In]; repeat (first [left; reflexivity | right]) | rewrite w9_w64_u64; w9_dn0 | apply oy_u64_rng | cbn; lia ].
Ltac w9_hwin UA :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | rewrite UA in Ha; lia ] | ]);
  destruct Hin.
Ltac w9_awr UA :=
  cbn [ss_mem];
  repeat (first [ apply awr_ok_cons_ro; [cbn; lia|]
                | eapply awr_ok_cons_gen; [reflexivity | exact UA | intros a Ha; left; cbn [YP09.r_wlo YP09.r_whi] in Ha;
                    unfold LLVMF_STK in *; lia | ] ]);
  apply awr_ok_nil.

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

Lemma w9_vm_u64 : forall m a v, val_mem SEGS m a 8 v <-> val_mem SEGS m a 8 (u64 v).
Proof.
intros m a v. unfold val_mem, u64.
split; intros H k Hk; rewrite (H k Hk); first [unfold YO0f.le_byte | unfold YG0f.le_byte];
change (8 * Z.of_nat 8) with 64; rewrite ?Zmod_mod; reflexivity.
Qed.
Lemma w9_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) L) -> nth_error L j = Some b ->
  mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base _ j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth _ j 0 (map_nth_error (fun b : byte => bv_unsigned b) j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.
Lemma w9_u_val : forall (m : word -> option byte) t (T : list byte) p (n : nat),
  length T = 400%nat -> garr8 SEGS m t (map (fun b : byte => bv_unsigned b) T) ->
  0 <= p -> p + Z.of_nat n <= 400 ->
  val_mem SEGS m (t + p) n (u_at T p n).
Proof.
intros m t T p n LT GT Hp Hpn k Hk.
assert (Hlen : length (sub T p n) = n) by (unfold sub; rewrite length_firstn, length_skipn, LT; lia).
pose proof (w9_u_rng T p n) as Hb.
destruct (nth_error T (Z.to_nat p + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + p + Z.of_nat k) with (t + Z.of_nat (Z.to_nat p + k)) by lia.
rewrite (w9_garr8_nth m t T _ b GT Hb2). f_equal.
rewrite le_byte_small by first [exact Hk | exact Hb].
assert (Hs : nth_error (sub T p n) k = Some b).
{ unfold sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec k n); [|lia]. rewrite nth_error_skipn. exact Hb2. }
pose proof (w9_nth_le_byte _ _ _ Hs) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold u_at. rewrite <- Hv. first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.
Lemma w9_pres_grow : forall (H : word -> bool) (m1 m2 : word -> option byte),
  mem_grows (mrestrict H m1) (mrestrict H m2) -> forall a, apresent H m1 a -> apresent H m2 a.
Proof.
intros H m1 m2 HG a (Hh & b & Hb). split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|]. exfalso. apply HG; [discriminate | reflexivity].
Qed.
Lemma w9_aview_garr8 : forall H (m : word -> option byte) p (L : list byte) j,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L) -> (j < length L)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some (bv_unsigned (nth j L (Z_to_bv 8 0))).
Proof.
intros H m p L j HG Hj. unfold aview.
rewrite (YI00.garr8_mbyte SEGS (mrestrict H m) p _ j HG) by (rewrite length_map; exact Hj).
cbn [option_map]. f_equal. rewrite (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0)).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma w9_aview_nn : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a Hp. destruct (oy_aview_present H m a Hp) as [b Hb]. rewrite Hb. discriminate. Qed.
Lemma w9_obs_len : forall regs, length (obs_vals regs) = 32%nat.
Proof. intros regs. unfold obs_vals. rewrite length_map, length_seq. reflexivity. Qed.
Lemma w9_ew_app : forall cx E regs xs k, (k < 563)%nat ->
  ew (d_env cx E (obs_vals regs ++ xs)) k = ew (d_env cx E (obs_vals regs)) k.
Proof.
intros cx E regs xs k Hk. unfold d_env, havoc. cbn [ew].
destruct (k <? AT_FL)%nat eqn:Hl; [reflexivity|]. apply Nat.ltb_ge in Hl. unfold AT_FL in *.
rewrite app_comm_cons. rewrite app_nth1; [reflexivity|]. cbn [length]. rewrite w9_obs_len. lia.
Qed.
Lemma w9_atom : forall cx E (regs : bvmap 5 word) X j, (j < length X)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (563 + j) = nth j X (Z_to_bv 64 0).
Proof.
intros cx E regs X j Hj.
replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite oy_d_env_x by (rewrite length_app, w9_obs_len; lia).
rewrite app_nth2 by (rewrite w9_obs_len; lia). rewrite w9_obs_len. f_equal. lia.
Qed.
Lemma w9_sv_add2 : forall E f q c fb v, ew E f = Z_to_bv 64 fb -> ew E q = Z_to_bv 64 v ->
  sv_denot E (SAlu ALU_ADD (SOff f c) (SOff q 0)) = Z_to_bv 64 (fb + c + v).
Proof.
intros E f q c fb v Hf Hv. rewrite denot_lit_U. rewrite U_SAlu, !U_SOff, Hf, Hv.
cbn [zalu_raw]. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with 18446744073709551616. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis BCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (oc B).

Definition w9_x (cx : dcx) (h i now nb fr len : Z) (T T' Sg : list byte) (ai : Z) : list word :=
  [w64 (u_at T' 384 4);
   w64 (u64 h); w64 (u64 (h + 440)); w64 (u64 0); w64 (u64 (dnot (d_obj cx OG))); w64 (u64 (dnot (d_obj cx OT)));
   w64 (u64 (dnot (d_obj cx OO))); w64 (u64 (dnot (d_obj cx OUSED))); w64 (u64 i); w64 (u64 now);
   w64 (u64 (d_cur cx nb)); w64 (u64 nb); w64 (u64 fr); w64 (u64 len);
   w64 (u64 (u64 (oldv ai (role_of_e T ai)))); w64 (u64 (u64 (oldv ai (hd_of T ai))));
   w64 (u64 (u64 (oldv ai (din_of T ai)))); w64 (u64 (u64 (oldv ai (dout_of T ai))));
   w64 (u64 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai))));
   w64 (u64 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai))));
   w64 (u64 (u64 (oldv ai (s32_at T (48 * ai + 20))))); w64 (u64 (u64 (oldv ai (owned_of T ai))));
   w64 (u64 (u64 (oldv ai (u_at T (48 * ai + 32) 8))));
   w64 (u64 (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg
                          else reac_disco_table_observe_c.ch_of T ai)));
   w64 (u64 (bv_swrap 32 (s_ch Sg)))].

Lemma w9_regs_ok : forall cx E regs xs, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs ++ xs)) obs_sr regs.
Proof.
intros cx E regs xs HE HL HA.
pose proof (regs_ok_obs B cx E regs HE HL HA) as R.
apply regs_ok_by_cases. intros r Hr. rewrite (R r).
cbv [all_regs In] in Hr.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ];
  (match goal with |- sv_denot _ (sr_get ?sr ?r) = _ =>
     let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end);
  first [ reflexivity | cbn [sv_denot]; rewrite w9_ew_app by lia; reflexivity ].
Qed.

Lemma w9_seat : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T T' ai (regs : bvmap 5 word) ly3 S3 W mem3 md3 k E,
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
  oc cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 ->
  ob_sp22 cx T ai W mem3 ->
  val_mem SEGS (rd W mem3) (d_A cx + 8) 8
    (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg
                  else reac_disco_table_observe_c.ch_of T ai)) ->
  val_mem SEGS (rd W mem3) (d_A cx + 0) 8 (bv_swrap 32 (s_ch Sg)) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai))
    (ss_d OB_C9M obs_sr dsh_rec w9_acs w9_fcs [] (d_facts [] []))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + OB_C9M)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now op nb fr len Sg T T' ai regs ly3 S3 W mem3 md3 k E HC HE HRG HFL
  V184 V120 V136 V376 V280 V232 V264 HOC HSP V8 V0.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (V208 & V320) & Hfrm & HSgl & HSg & HSf &
  (V200 & V328 & V368 & V408) & Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof HSP as (S64 & S56 & S352 & S192 & S104 & S96 & S88 & S80 & S296 & S72 & S48).
pose proof HC as (_ & HJ & _).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (XA : forall j, (j < 25)%nat -> ew (d_env cx E (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai)) (563 + j) =
  nth j (w9_x cx h i now nb fr len T T' Sg ai) (Z_to_bv 64 0)) by (intros j Hj; apply w9_atom; cbn; lia).
apply (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_C9M obs_sr
  (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai) w9_acs w9_fcs [] (d_facts [] []) HC HE HRG HFL).
- exact (w9_regs_ok cx E regs _ HE HrL HAr2).
- exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E _ [] [] HC HE I I).
- unfold w9_acs. cbn [map fst snd].
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?q 0))) =>
    let j := eval vm_compute in (q - 563)%nat in
    let v := eval cbn [nth w9_x] in (nth j (w9_x cx h i now nb fr len T T' Sg ai) (Z_to_bv 64 0)) in
    lazymatch v with w64 (u64 ?z) =>
      apply (chunk_ok_val SEGS _ _ _ o 8 _ (u64 z));
      [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | apply oy_u64_rng | cbn; lia
      | apply (proj1 (w9_vm_u64 _ _ z)); assumption ]
    end
  end.
- unfold w9_fcs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ 2544 4 _ (u_at T' 384 4));
  [ rewrite sv_denot_SOff0; exact (XA 0%nat ltac:(lia)) | exact (w9_u_rng T' 384 4) | cbn; lia
  | replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj, dobj_off; lia);
    exact (w9_u_val _ _ T' 384 4 HTl HT ltac:(lia) ltac:(lia)) ].
- apply Forall_nil.
- exact I.
- apply Forall_nil.
- vm_compute; reflexivity.
Qed.

Lemma w9_oc_keep : forall cx h i n now op nb fr len Sg T (regs regs' : bvmap 5 word) ly3 S3 W mem3 mem' md k,
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

Theorem ob_s9a2 : ob_seg9a2 B MT XM_LIB RLO RHI tfib_K.
Proof.
clear XN_LIB.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HOT & Hai & V8 & V0 & HR9).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (V208 & V320) & Hfrm & HSgl & HSg & HSf &
  (V200 & V328 & V368 & V408) & Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HOT as (LT & TOK & HFR & HOW & HSP & H360 & HOM).
destruct HR9 as (R26 & R16 & R24 & R21 & R14 & R5 & R22 & R7 & R25 & R23).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as ACV.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (HFLr : 0 <= flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx) < 2 ^ 64) by exact (oy_rdword_aview_range SEGS _ _ _ _ Hflag).
pose proof TOK as (T1 & _). pose proof T1 as T1'. unfold tbl_T1 in T1'.
assert (Hai8 : ai < 8) by (destruct HFR as [[? _]|[? _]]; lia).
destruct (w9_keep T Sg ow now T' ret ai LT HSgl TOK HFR ltac:(lia) HOM) as (EMAC & Hn8).
pose proof (w9_seat fq cx h i n now op nb fr len Sg T T' ai regs ly3 S3 W mem3 md3 k E HC HdE Hregs Hflag
  V184 V120 V136 V376 V280 V232 V264 HOC HSP V8 V0) as HS.
assert (XA : forall j, (j < 25)%nat -> ew (d_env cx E (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai)) (563 + j) =
  nth j (w9_x cx h i now nb fr len T T' Sg ai) (Z_to_bv 64 0)) by (intros j Hj; apply w9_atom; cbn; lia).
pose proof (XA 0%nat ltac:(lia)) as AX563. pose proof (XA 1%nat ltac:(lia)) as AX564. pose proof (XA 2%nat ltac:(lia)) as AX565.
pose proof (XA 3%nat ltac:(lia)) as AX566. pose proof (XA 4%nat ltac:(lia)) as AX567. pose proof (XA 5%nat ltac:(lia)) as AX568.
pose proof (XA 6%nat ltac:(lia)) as AX569. pose proof (XA 7%nat ltac:(lia)) as AX570. pose proof (XA 8%nat ltac:(lia)) as AX571.
pose proof (XA 9%nat ltac:(lia)) as AX572. pose proof (XA 10%nat ltac:(lia)) as AX573. pose proof (XA 11%nat ltac:(lia)) as AX574.
pose proof (XA 12%nat ltac:(lia)) as AX575. pose proof (XA 13%nat ltac:(lia)) as AX576. pose proof (XA 14%nat ltac:(lia)) as AX577.
pose proof (XA 15%nat ltac:(lia)) as AX578. pose proof (XA 16%nat ltac:(lia)) as AX579. pose proof (XA 17%nat ltac:(lia)) as AX580.
pose proof (XA 18%nat ltac:(lia)) as AX581. pose proof (XA 19%nat ltac:(lia)) as AX582. pose proof (XA 20%nat ltac:(lia)) as AX583.
pose proof (XA 21%nat ltac:(lia)) as AX584. pose proof (XA 22%nat ltac:(lia)) as AX585. pose proof (XA 23%nat ltac:(lia)) as AX586.
pose proof (XA 24%nat ltac:(lia)) as AX587.
cbn [nth w9_x Nat.add] in AX563, AX564, AX565, AX566, AX567, AX568, AX569, AX570, AX571, AX572, AX573, AX574, AX575, AX576,
  AX577, AX578, AX579, AX580, AX581, AX582, AX583, AX584, AX585, AX586, AX587.
clear XA.
pose proof (w9_regs_ok cx E regs (w9_x cx h i now nb fr len T T' Sg ai) HdE HrL HAr2) as RO1.
pose proof (oy_d_E_env cx E (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai) HdE) as HdE'.
pose proof (oy_d_env_fl cx E (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai)) as HFL'.
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai)))
  by exact (proj1 (proj2 (proj2 HdE'))).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai)) (rd W mem3))
  by constructor.
set (Ev := d_env cx E (obs_vals regs ++ w9_x cx h i now nb fr len T T' Sg ai)) in *. clearbody Ev.
pose proof HdE' as (_ & _ & _ & E60 & E516 & _). change AT_A with 60%nat in E60. change AT_F with 516%nat in E516.
assert (UA : bv_unsigned (ew Ev 60) = d_A cx) by (rewrite E60; apply unsigned_lit_small; lia).
pose proof (RO1 16%bv) as AX547. w9_rr AX547. rewrite R16 in AX547. apply eq_sym, w9_ew_of_sv in AX547.
pose proof (RO1 23%bv) as AX554. w9_rr AX554. rewrite R23 in AX554. apply eq_sym, w9_ew_of_sv in AX554.
pose proof (RO1 7%bv) as AX538. w9_rr AX538. rewrite R7 in AX538. apply eq_sym, w9_ew_of_sv in AX538.
pose proof (RO1 25%bv) as AX556. w9_rr AX556. rewrite R25 in AX556. apply eq_sym, w9_ew_of_sv in AX556.
pose proof (RO1 14%bv) as AX545. w9_rr AX545. rewrite R14 in AX545. apply eq_sym, w9_ew_of_sv in AX545.
pose proof (RO1 5%bv) as AX536. w9_rr AX536. rewrite R5 in AX536. apply eq_sym, w9_ew_of_sv in AX536.
pose proof (RO1 26%bv) as AX557. w9_rr AX557. rewrite R26 in AX557. apply eq_sym, w9_ew_of_sv in AX557.
pose proof (RO1 24%bv) as AX555. w9_rr AX555. rewrite R24 in AX555. apply eq_sym, w9_ew_of_sv in AX555.
pose proof (RO1 21%bv) as AX552. w9_rr AX552. rewrite R21 in AX552. apply eq_sym, w9_ew_of_sv in AX552.
pose proof (RO1 22%bv) as AX553. w9_rr AX553. rewrite R22 in AX553. apply eq_sym, w9_ew_of_sv in AX553.
pose (RUN := paj_run (fx := fq) (PL := PL_both3_0) B LAWS).
pose proof (paj_run_to (fx := fq) (PL := PL_both3_0) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + OB_C9M)) with (Z_to_bv 64 (BASE + OB_C9M)).
unfold ss_d in HS. ro_base HS 516%nat. ro_base HS 529%nat.
paj_run_tok RUN HS HJ SHOK OBspan; [w9_awr UA|].
assert (MEQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
  by (apply (kept_of_frame (segs := SEGS) _ _ (w_H W) mem3 (ms_mem ms) (fun a => d_A cx <= a < d_A cx + 472) HFr);
      w9_hwin UA).
pose proof (w9_pres_grow (w_H W) mem3 (ms_mem ms) HG) as MPR1.
clear HF HFr HG.
rename ms into ms0.
psrr_branch_tok RUN BR HS SHOK OBspan.
{ exfalso. rewrite (w9_br_ne_false _ _ _) in Hc; [discriminate Hc|].
  rewrite (w9_dn_sx32 _ 563 _ AX563 ltac:(pose proof (w9_u_rng T' 384 4) as R; exact R)), Hn8.
  rewrite (w9_sv_atom _ 556 _ AX556). reflexivity. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK OBspan 0x1998; [w9_awr UA|].
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hna. rewrite <- (MEQ1 a Ha Hna).
  revert a Ha Hna.
  apply (kept_of_frame (segs := SEGS) _ _ (w_H W) (ms_mem ms0) (ms_mem ms) (fun a => d_A cx <= a < d_A cx + 472) HFr).
  w9_hwin UA. }
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (w9_pres_grow (w_H W) (ms_mem ms0) (ms_mem ms) HG a (MPR1 a Ha))).
clear HF HFr HG MEQ1 MPR1.
rename ms into ms1.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms1) r = getr regs r)
  by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
      rewrite (st_ok_pi_restrict_reg _ _ _ ms1 r HS), (RO1 r);
      cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr).
assert (HrL1 : d_rL B cx (ms_regs ms1)).
{ destruct HrL as (L2 & L3 & L4 & L8 & L9 & L19 & L18 & L20 & L27). unfold d_rL, spZ in *.
  rewrite !RG by (cbv; tauto). repeat split; assumption. }
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RA; cbn [ms_mem restrict] in RA.
assert (W184 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 184) 8 (u64 h)) by (w9_fld RA UA).
assert (W120 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 120) 8 (u64 (h + 440))) by (w9_fld RA UA).
assert (W136 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 136) 8 (u64 0)) by (w9_fld RA UA).
assert (W376 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 376) 8 (u64 (dnot (d_obj cx OG)))) by (w9_fld RA UA).
assert (W280 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 280) 8 (u64 (dnot (d_obj cx OT)))) by (w9_fld RA UA).
assert (W232 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 232) 8 (u64 (dnot (d_obj cx OO)))) by (w9_fld RA UA).
assert (W264 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 264) 8 (u64 (dnot (d_obj cx OUSED)))) by (w9_fld RA UA).
assert (W208 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 208) 8 (u64 i)) by (w9_fld RA UA).
assert (W320 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 320) 8 (u64 now)) by (w9_fld RA UA).
assert (W200 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 200) 8 (u64 (d_cur cx nb))) by (w9_fld RA UA).
assert (W328 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 328) 8 (u64 nb)) by (w9_fld RA UA).
assert (W368 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 368) 8 (u64 fr)) by (w9_fld RA UA).
assert (W408 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 408) 8 (u64 len)) by (w9_fld RA UA).
assert (W352 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 352) 8 (u64 (u64 (oldv ai (role_of_e T ai))))) by (w9_fld RA UA).
assert (W192 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 192) 8 (u64 (u64 (oldv ai (hd_of T ai))))) by (w9_fld RA UA).
assert (W104 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 104) 8 (u64 (u64 (oldv ai (din_of T ai))))) by (w9_fld RA UA).
assert (W96 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 96) 8 (u64 (u64 (oldv ai (dout_of T ai))))) by (w9_fld RA UA).
assert (W88 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 88) 8
  (u64 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai))))) by (w9_fld RA UA).
assert (W80 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 80) 8
  (u64 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai))))) by (w9_fld RA UA).
assert (W296 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 296) 8 (u64 (u64 (oldv ai (s32_at T (48 * ai + 20)))))) by (w9_fld RA UA).
assert (W72 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 72) 8 (u64 (u64 (oldv ai (owned_of T ai))))) by (w9_fld RA UA).
assert (W48 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 48) 8 (u64 (u64 (oldv ai (u_at T (48 * ai + 32) 8))))) by (w9_fld RA UA).
assert (W8 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 8) 8
  (u64 (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg
                     else reac_disco_table_observe_c.ch_of T ai)))) by (w9_fld RA UA).
assert (W0 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 0) 8 (u64 (bv_swrap 32 (s_ch Sg)))) by (w9_fld RA UA).
assert (W64 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 64) 8
  (u64 (if s_role Sg =? 0 then role_of_e T ai
        else if (role_of_e T ai =? 1) && (s_role Sg =? 2) then 1 else s_role Sg))) by (w9_fld RA UA).
assert (W56 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 56) 8 (u64 (if ow =? 0 then u64 (owned_of T ai) else 1)))
  by (w9_fld RA UA).
assert (W360 : val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + 360) 8 (u64 ret)) by (w9_fld RA UA).
clear RA.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => set (md4 := mdx) in * end.
assert (HC1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms1) md4 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_land B MT XM_LIB RLO RHI tfib_K fq cx h dsh_rec ly3 S3 W md4 k Ev _ ms1 LAWS HC1 HdE' HFL' HFLr HS
  ltac:(vm_compute; reflexivity)
  (proj2 (w9_vm_u64 _ _ _) W184) (proj2 (w9_vm_u64 _ _ _) W120) (proj2 (w9_vm_u64 _ _ _) W136)
  (proj2 (w9_vm_u64 _ _ _) W376) (proj2 (w9_vm_u64 _ _ _) W280) (proj2 (w9_vm_u64 _ _ _) W232)
  (proj2 (w9_vm_u64 _ _ _) W264)) as [HF1 HSh1].
pose proof (w9_oc_keep cx h i n now op nb fr len Sg T' regs (ms_regs ms1) ly3 S3 W mem3 (ms_mem ms1) md4 k HC1 HOC MEQ MPR
  HrL1 HF1 HSh1 (conj (proj2 (w9_vm_u64 _ _ _) W208) (proj2 (w9_vm_u64 _ _ _) W320))
  (conj (proj2 (w9_vm_u64 _ _ _) W200) (conj (proj2 (w9_vm_u64 _ _ _) W328)
    (conj (proj2 (w9_vm_u64 _ _ _) W368) (proj2 (w9_vm_u64 _ _ _) W408))))) as HOC1.
clear HC1 HF1 HSh1.
ro_base HS 60%nat.
paj_run_tok RUN HS HJ SHOK OBspan; [w9_awr UA|].
pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MP3.
clear HF HFr HG.
repeat rewrite wvb_collapse in HJ.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msc end.
lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ msc) |- _ =>
  pose proof (st_ok_restrict_mkst SEGS (w_H W) Ex ssx msc HS eq_refl) as Hms;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 10%bv HS) as Ra0;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 11%bv HS) as Ra1;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 12%bv HS) as Ra2;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 1%bv HS) as Rra;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 2%bv HS) as Rsp;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 23%bv HS) as Rc23;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 24%bv HS) as Rc24;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 21%bv HS) as Rc21;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 22%bv HS) as Rc22;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 25%bv HS) as Rc25;
  pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 26%bv HS) as Rc26;
  assert (RGc : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs msc) r = getr regs r)
    by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc r HS), (RO1 r); cbv [In] in Hr;
        repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr)
end.
cbn [ss_pc setpc] in Hms.
w9_rr Ra0. w9_rr Ra1. w9_rr Ra2. w9_rr Rra. w9_rr Rsp. w9_rr Rc23. w9_rr Rc24. w9_rr Rc21. w9_rr Rc22. w9_rr Rc25. w9_rr Rc26.
assert (EV10 : getr (ms_regs msc) 10 = w64 (d_obj cx OT + 48 * ai)).
{ rewrite Ra0, (w9_sv_add2 _ 516 557 2160 (d_FB cx) (48 * ai) E516 AX557). unfold w64, d_obj, dobj_off. f_equal; lia. }
assert (EV26 : getr (ms_regs msc) 26 = w64 (d_obj cx OT + 48 * ai)).
{ rewrite Rc26, (w9_sv_add2 _ 516 557 2160 (d_FB cx) (48 * ai) E516 AX557). unfold w64, d_obj, dobj_off. f_equal; lia. }
assert (EV11 : getr (ms_regs msc) 11 = w64 (d_obj cx OS)).
{ rewrite Ra1. cbn [sv_denot]. rewrite E516. unfold w64. rewrite oy_w64_add_w. unfold d_obj, dobj_off. reflexivity. }
assert (EV12 : getr (ms_regs msc) 12 = w64 6) by (rewrite Ra2; reflexivity).
change (SOff 240 6556) with (SOff A_TEXT 6556) in Rra. rewrite (codeptr_val _ 6556 HEI) in Rra.
rewrite (w9_sv_atom _ 60 (d_A cx) E60) in Rsp.
assert (SPZ : spZ (ms_regs msc) = d_A cx)
  by (unfold spZ; rewrite Rsp, Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
assert (HrLc : d_rL B cx (ms_regs msc)).
{ pose proof HrL as (Hspr & Hgpr & Htpr & R8r & R9r & R19r & R18r & R20r & R27r). unfold d_rL. split; [exact SPZ|].
  rewrite (RGc 3%bv), (RGc 4%bv), (RGc 8%bv), (RGc 9%bv), (RGc 18%bv), (RGc 19%bv), (RGc 20%bv), (RGc 27%bv)
    by (cbv; tauto).
  repeat split; assumption. }
pose proof (oy_oc_pt B cx h i n now op nb fr len Sg T' (ms_regs ms1) (ms_regs msc) ly3 S3 W (ms_mem ms1) (ms_mem msc)
  BRT MP3 HrLc HOC1) as HOC2.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => set (md5 := mdx) in * end.
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msc) md5 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem msc) md5 k HC2)
  as (_ & _ & _ & HF0 & HFc & HFia & HFo & HF32 & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
assert (HF8 : d_FB cx mod 8 = 0) by (apply w9_mod32_8; exact HF32).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
pose proof HOC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSg2 & _ & _ & _ & _ & _ & HT2 & _ & Hbody2).
pose proof Hbody2 as (_ & _ & _ & _ & _ & Hshadow2 & _).
rewrite Hms.
eapply SRr_bind.
{ eapply (aj_bcmp_at (fx := fq) SEGS B LAWS pa_segs_low (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W
    (ms_regs msc) (ms_mem msc) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k (d_obj cx OT + 48 * ai) (d_obj cx OS) 6 (d_A cx - d_S cx)
    (Z_to_bv 64 (BASE + 6556)) HJ).
  - exact EV10.
  - exact EV11.
  - exact EV12.
  - lia.
  - unfold d_obj, dobj_off; lia.
  - unfold d_obj, dobj_off; lia.
  - unfold d_obj, dobj_off; lia.
  - unfold d_obj, dobj_off; lia.
  - rewrite SPZ. lia.
  - lia.
  - lia.
  - unfold ESTACK, LLVMF_STK; lia.
  - destruct HrL as (_ & Hgp & _). rewrite (RGc 3%bv) by (cbv; tauto). exact Hgp.
  - destruct HrL as (_ & _ & Htp & _). rewrite (RGc 4%bv) by (cbv; tauto). exact Htp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. rewrite SPZ. unfold d_obj, dobj_off in Ha. split.
    + apply w9_aview_nn. apply HFpres. lia.
    + unfold ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. rewrite SPZ. unfold d_obj, dobj_off in Ha. split.
    + apply w9_aview_nn. apply HFpres. lia.
    + unfold ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. unfold ESTACK, LLVMF_STK, d_obj, dobj_off in *. lia.
  - intros a Ha. unfold ESTACK, LLVMF_STK, d_obj, dobj_off in *. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, d_obj, dobj_off. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, d_obj, dobj_off. lia.
  - replace (d_obj cx OT + 48 * ai) with (d_FB cx + (2160 + 48 * ai)) by (unfold d_obj, dobj_off; lia).
    apply (oy_ra_frame cx dsh_rec W (ms_mem msc) (2160 + 48 * ai) 6 Hshadow2 HF8 ltac:(lia) ltac:(lia) ltac:(lia)).
    intros kk Hkk. apply oy_dsh_rec_t. lia.
  - replace (d_obj cx OT + 48 * ai) with (d_FB cx + (2160 + 48 * ai)) by (unfold d_obj, dobj_off; lia).
    intros _. exact (oy_hull_frame cx dsh_rec W (ms_mem msc) (2160 + 48 * ai) 6 Hshadow2 HF8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - replace (d_obj cx OS) with (d_FB cx + 2992) by (unfold d_obj, dobj_off; lia).
    apply (oy_ra_frame cx dsh_rec W (ms_mem msc) 2992 6 Hshadow2 HF8 ltac:(lia) ltac:(lia) ltac:(lia)).
    intros kk Hkk. apply oy_dsh_rec_s. lia.
  - replace (d_obj cx OS) with (d_FB cx + 2992) by (unfold d_obj, dobj_off; lia).
    intros _. exact (oy_hull_frame cx dsh_rec W (ms_mem msc) 2992 6 Hshadow2 HF8 ltac:(lia) ltac:(lia) ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres).
assert (KPc : d_kept (fun a => d_A cx - 8192 <= a < d_A cx) W (ms_mem msc) W mem2).
{ intros a Ha Hna. apply (Hfr a Ha). unfold ESTACK; lia. }
assert (K8 : forall o v0, 0 <= o -> o + 8 <= 472 -> val_mem SEGS (rd W (ms_mem ms1)) (d_A cx + o) 8 v0 ->
  val_mem SEGS (rd W mem2) (d_A cx + o) 8 v0).
{ intros o v0 Ho Ho2 Hv0. apply (oy_val_mem_keep W W (ms_mem ms1) mem2 _ 8 v0); [|exact Hv0].
  intros j Hj. rewrite (KPc (d_A cx + o + Z.of_nat j) ltac:(lia) ltac:(cbv beta; lia)).
  unfold aview, mbyte, mrestrict. rewrite MP3. reflexivity. }
assert (HC3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem2 md2 k)
  by (split; [exact Hbase | split; [exact HJ2 | exact Hfrs]]).
pose proof (oy_oc_call_keep B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg T' (ms_regs msc)
  ly3 S3 W (ms_mem msc) md5 k regs2 ly3 S3 W mem2 md2 k 8192 LAWS BCK HC2 HC3 HOC2 ltac:(lia)
  ltac:(unfold LLVMF_STK; lia) KPc (Permutation_refl _) HP) as HOC3.
assert (Hv0 : v = w64 0).
{ apply (proj2 Hcmp). intros j Hj.
  replace (d_obj cx OT + 48 * ai + j) with (d_obj cx OT + Z.of_nat (Z.to_nat (48 * ai + j))) by lia.
  replace (d_obj cx OS + j) with (d_obj cx OS + Z.of_nat (Z.to_nat j)) by lia.
  rewrite (w9_aview_garr8 _ _ _ T' _ HT2) by (rewrite HTl; lia).
  rewrite (w9_aview_garr8 _ _ _ Sg _ HSg2) by (rewrite HSgl; lia).
  f_equal. f_equal.
  transitivity (nth (Z.to_nat j) (sub T' (48 * ai) 6) (Z_to_bv 8 0)).
  - rewrite w9_nth_sub by lia. f_equal. lia.
  - rewrite EMAC, w9_nth_sub by lia. reflexivity. }
apply SRr_ret. unfold ob_c11, d_at.
exists fq, ly3, S3, regs2, mem2, md2, k, acc.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
exists T, T', ai, ow, ret.
split; [exact HOC3|].
split; [exact LT|]. split; [exact TOK|]. split; [exact HFR|]. split; [lia|]. split; [exact HOW|]. split; [exact HOM|].
split.
- unfold ob_sp24.
  split; [exact (K8 352 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W352))|].
  split; [exact (K8 192 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W192))|].
  split; [exact (K8 104 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W104))|].
  split; [exact (K8 96 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W96))|].
  split; [exact (K8 88 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W88))|].
  split; [exact (K8 80 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W80))|].
  split; [exact (K8 296 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W296))|].
  split; [exact (K8 72 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W72))|].
  split; [exact (K8 48 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W48))|].
  split; [exact (K8 64 _ ltac:(lia) ltac:(lia) W64)|].
  split; [exact (K8 56 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W56))|].
  split; [exact (K8 360 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W360))|].
  split; [exact (K8 8 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W8))|].
  exact (K8 0 _ ltac:(lia) ltac:(lia) (proj2 (w9_vm_u64 _ _ _) W0)).
- unfold ob_r24.
  split; [rewrite Hv; exact Hv0|].
  split; [rewrite (w9_pres _ _ 24%bv HP) by w9_cs; rewrite Rc24, (w9_sv_atom _ 555 _ AX555); reflexivity|].
  split; [rewrite (w9_pres _ _ 21%bv HP) by w9_cs; rewrite Rc21, (w9_sv_atom _ 552 _ AX552); reflexivity|].
  split; [rewrite (w9_pres _ _ 25%bv HP) by w9_cs; rewrite Rc25, (w9_sv_atom _ 545 _ AX545); reflexivity|].
  split; [rewrite (w9_pres _ _ 23%bv HP) by w9_cs; rewrite Rc23, (w9_sv_atom _ 536 _ AX536); reflexivity|].
  split; [rewrite (w9_pres _ _ 22%bv HP) by w9_cs; rewrite Rc22, (w9_sv_atom _ 553 _ AX553); reflexivity|].
  rewrite (w9_pres _ _ 26%bv HP) by w9_cs. exact EV26.
Qed.
End h.
End f.
End d.

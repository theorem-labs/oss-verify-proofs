(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 1029 of its 1060 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs2.v, with its module paths and module names changed; 474 of its 562 lines of code are new or changed and 972 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_known slot_observe disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma o7_u_at_fb : forall (S : list byte) (k : nat), (k < length S)%nat ->
  u_at S (Z.of_nat k) 1 = CtrlParsed.fb S k.
Proof.
intros S k. unfold u_at, sub, CtrlParsed.fb. rewrite Nat2Z.id. revert S.
induction k as [|k IH]; intros [|b S] Hk; cbn [length] in Hk; try lia.
- cbn [skipn firstn nth bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
- cbn [skipn nth]. apply IH. lia.
Qed.
Lemma o7_sight_S12 : forall S : list byte, disco_classify_c.sighting_ok S ->
  disco_table_c.sighting_S1 S /\ disco_table_c.sighting_S2 S.
Proof.
intros S (HL & HR & HD).
assert (Hb : 0 <= CtrlParsed.fu S 8 4 < 2 ^ 32).
{ unfold CtrlParsed.fu, CtrlParsed.fld. pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn 8 S))).
  pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 8 S))) as Hu. rewrite length_firstn, length_skipn, HL in Hu. cbn in Hu. lia. }
assert (SW : bv_swrap 32 (CtrlParsed.fu S 8 4) = CtrlParsed.s32 (CtrlParsed.fu S 8 4)).
{ unfold CtrlParsed.s32. change (bv_swrap 32 (CtrlParsed.fu S 8 4)) with ((CtrlParsed.fu S 8 4 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
  destruct (Z.ltb_spec (CtrlParsed.fu S 8 4) (2 ^ 31)); lia. }
split.
- unfold disco_table_c.sighting_S1, disco_table_c.s_role, disco_table_c.s32_at.
  change (disco_table_c.u_at S 8 4) with (CtrlParsed.fu S 8 4). rewrite SW. lia.
- unfold disco_table_c.sighting_S2, disco_table_c.s_hd, disco_table_c.s_din, disco_table_c.s_dout.
  change 12 with (Z.of_nat 12). change 13 with (Z.of_nat 13). change 14 with (Z.of_nat 14).
  rewrite !o7_u_at_fb by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. lia.
Qed.
Lemma o7_w64u64 : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v.
Proof. intros v. unfold u64. exact (Z_to_bv64_canon v). Qed.

Lemma o7_fields : forall (T Sg T' : list byte) (ow now ret ai : Z),
  length T = 400%nat -> length Sg = 24%nat -> 0 <= ai < disco_table_c.n_of T -> 0 <= ai < 8 ->
  disco_table_c.tbl_T2 T -> disco_table_c.tbl_T4 T ->
  disco_table_c.sighting_S1 Sg -> disco_table_c.sighting_S2 Sg -> 0 <= ow <= 1 -> 0 <= now < 2 ^ 64 ->
  (T', ret) = reac_disco_table_observe_c.observe_known T Sg ow now ai ->
  disco_table_c.role_of_e T' ai = slot_known.want_role (disco_table_c.s_role Sg) (disco_table_c.role_of_e T ai) /\
  disco_table_c.hd_of T' ai = (if disco_table_c.s_hd Sg =? 0 then disco_table_c.hd_of T ai else 1) /\
  disco_table_c.din_of T' ai = (if disco_table_c.s_hd Sg =? 0 then disco_table_c.din_of T ai else disco_table_c.s_din Sg) /\
  disco_table_c.dout_of T' ai = (if disco_table_c.s_hd Sg =? 0 then disco_table_c.dout_of T ai else disco_table_c.s_dout Sg) /\
  reac_disco_table_observe_c.fam_of T' ai =
    (if disco_table_c.s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else disco_table_c.s_fam Sg) /\
  reac_disco_table_observe_c.slots_of T' ai =
    (if disco_table_c.s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else disco_table_c.s_slots Sg) /\
  disco_table_c.s32_at T' (48 * ai + 20) =
    bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? disco_table_c.s_ch Sg then disco_table_c.s_ch Sg
                 else reac_disco_table_observe_c.ch_of T ai) /\
  disco_table_c.owned_of T' ai = (if ow =? 0 then disco_table_c.owned_of T ai else 1) /\
  disco_table_c.u_at T' (48 * ai + 32) 8 = disco_table_c.u_at T (48 * ai + 32) 8 /\
  disco_table_c.u_at T' (48 * ai + 40) 8 = now /\
  ret = Z.b2z (slot_observe.c_any T Sg ow ai).
Proof.
intros T Sg T' ow now ret ai LT LS Hn Hr8 T2 T4 S1 S2 How Hnow E.
destruct (ok_facts T Sg ow now ai T' ret LT LS Hr8 E)
  as (_ & _ & _ & E8 & E12 & E13 & E14 & E15 & E16 & E20 & E24 & E32 & E40 & _ & Eret).
destruct (T4 ai Hn) as (HD & _ & OW).
split; [unfold disco_table_c.role_of_e, disco_table_c.s32_at, disco_table_c.u_at; rewrite E8; apply role_field; [exact S1 | exact (T2 ai Hn)]|].
split; [unfold disco_table_c.hd_of, disco_table_c.u_at; rewrite E12; apply hd_field; [exact S2 | exact HD]|].
split; [unfold disco_table_c.din_of, disco_table_c.u_at; rewrite E13; apply din_field; exact S2|].
split; [unfold disco_table_c.dout_of, disco_table_c.u_at; rewrite E14; apply dout_field; exact S2|].
split; [unfold reac_disco_table_observe_c.fam_of, disco_table_c.u_at; rewrite E15; apply fam_field|].
split; [unfold reac_disco_table_observe_c.slots_of, disco_table_c.u_at; rewrite E16; apply slots_field|].
split; [unfold disco_table_c.s32_at, disco_table_c.u_at; rewrite E20; apply ch_field|].
split; [unfold disco_table_c.owned_of, disco_table_c.s32_at, disco_table_c.u_at; rewrite E24; apply own_field; [exact How | exact OW]|].
split; [unfold disco_table_c.u_at; rewrite E32; reflexivity|].
split; [unfold disco_table_c.u_at; rewrite E40; rewrite OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.bytes_le_to_Z_to_le_bytes by lia;
  replace (8 * Z.of_nat 8) with 64 by reflexivity; apply Z.mod_small; exact Hnow|].
rewrite Eret. destruct (slot_observe.c_any T Sg ow ai); reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.

Lemma oy_sp24_pt : forall cx (T Sg : list byte) (ai ow ret : Z) (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> ob_sp24 cx T Sg ai ow ret W m -> ob_sp24 cx T Sg ai ow ret W m'.
Proof.
intros cx T Sg ai ow ret W m m' MEQ H.
assert (MR : forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) by (apply (oy_mrestrict_ext (w_H W) m m'); exact MEQ).
unfold ob_sp24 in H |- *.
destruct H as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14).
repeat split; (eapply oy_val_mem_pt; [exact MR | eassumption]).
Qed.

Lemma oy_c12 : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg (T T' : list byte)
    (ai ow ret kmax accmax : Z) ly3 S3 (W : world SEGS) md3 k acc (E : env) (ss : sstate) (ms : machine_state),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md3 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = OB_C12 ->
  oc B cx h i n now op nb fr len Sg T' (ms_regs ms) ly3 S3 W (ms_mem ms) ->
  length T = 400%nat -> disco_table_c.table_ok T -> find_res T (s_mac Sg) ai -> 0 <= ai < n_of T ->
  (ow = 0 \/ ow = 1) -> reac_disco_table_observe_c.observe_model T Sg ow now T' ret ->
  ob_sp24 cx T Sg ai ow ret W (ms_mem ms) ->
  ob_r12 cx T Sg ai ow ret (ms_regs ms) ->
  ob_c12 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg kmax accmax W (mkCfg ms md3).
Proof.
intros fq cx h i n now op nb fr len Sg T T' ai ow ret kmax accmax ly3 S3 W md3 k acc E ss ms
  HFRM0 HB HJ HFR Hk Hnev Hmo Hacc HS Hrv Hpc HOC HTl HTok HFR0 Hair How HOM Hsp24 Hr12.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms. rewrite Hpc in Hms.
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
unfold ob_c12. rewrite Hms at 1.
apply (oy_dat B MT XM_LIB RLO RHI tfib_K cx OB_C12 kmax accmax _ fq ly3 S3 (ms_regs ms) (ms_mem ms) md3 k acc W
  MT_TRIV HFRM0 Hctx Hk Hacc).
exists T, T', ai, ow, ret.
split; [exact HOC|]. split; [exact HTl|]. split; [exact HTok|]. split; [exact HFR0|]. split; [exact Hair|].
split; [exact How|]. split; [exact HOM|]. split; [exact Hsp24 | exact Hr12].
Qed.

Lemma o7_u8 : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.
Lemma o7_u_rng : forall (T : list byte) p (n : nat), 0 <= u_at T p n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T p n. unfold u_at. pose proof (YK11.bytes_le_to_Z_nonneg (sub T p n)) as H0.
pose proof (YK11.bytes_le_to_Z_bound (sub T p n)) as H1.
assert (L : (length (sub T p n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma o7_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (o7_u8 b) as Hb. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma o7_nth_le_byte : forall bs k (b : byte),
  nth_error bs k = Some b -> bv_unsigned b = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
induction bs as [|b0 bs IHbs]; intros k b H; [destruct k; discriminate H|].
rewrite o7_ble_cons. pose proof (o7_u8 b0) as Hb0. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
destruct k as [|k].
- cbn in H. injection H as <-. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. lia.
- cbn [nth_error] in H. rewrite (IHbs k b H).
  replace (8 * Z.of_nat (Datatypes.S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite <- Z.div_div by lia. f_equal. f_equal. lia.
Qed.
Lemma o7_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) L) -> nth_error L j = Some b ->
  mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base _ j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth _ j 0 (map_nth_error (fun b : byte => bv_unsigned b) j L Hj)).
apply Z_to_bv_bv_unsigned.
Qed.
Lemma o7_u_val : forall (m : word -> option byte) t (T : list byte) p (n : nat),
  garr8 SEGS m t (map (fun b : byte => bv_unsigned b) T) -> 0 <= p -> p + Z.of_nat n <= Z.of_nat (length T) ->
  val_mem SEGS m (t + p) n (u_at T p n).
Proof.
intros m t T p n GT Hp Hpn k Hk.
pose proof (o7_u_rng T p n) as Hb.
destruct (nth_error T (Z.to_nat p + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + p + Z.of_nat k) with (t + Z.of_nat (Z.to_nat p + k)) by lia.
rewrite (o7_garr8_nth m t T _ b GT Hb2). f_equal.
rewrite le_byte_small by first [exact Hk | exact Hb].
assert (Hs : nth_error (sub T p n) k = Some b).
{ unfold sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec k n); [|lia]. rewrite nth_error_skipn. exact Hb2. }
pose proof (o7_nth_le_byte _ _ _ Hs) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold u_at. rewrite <- Hv. first [reflexivity | symmetry; apply Z.mod_small; apply (o7_u8 b)].
Qed.
Lemma o7_obs_len : forall regs, length (obs_vals regs) = 32%nat.
Proof. intros regs. unfold obs_vals. rewrite length_map, length_seq. reflexivity. Qed.
Lemma o7_sv_atom : forall E a v, ew E a = Z_to_bv 64 v -> sv_denot E (SOff a 0) = Z_to_bv 64 v.
Proof. intros E a v H. rewrite sv_denot_SOff0. exact H. Qed.
Lemma o7_sv_sext32 : forall E a u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E a u H Hu. rewrite denot_lit_U, U_SExt, (U_atom E a u H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia. exact (Z_to_bv64_canon _).
Qed.
Lemma o7_sv_zext8 : forall E a u, ew E a = Z_to_bv 64 u -> 0 <= u < 256 ->
  sv_denot E (SExt false 8 (SOff a 0)) = Z_to_bv 64 u.
Proof.
intros E a u H Hu. rewrite denot_lit_U, U_SExt, (U_atom E a u H) by lia. cbv iota.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small u) by lia. exact (Z_to_bv64_canon _).
Qed.
Lemma o7_br_ne_false : forall E a b, sv_denot E a = sv_denot E b ->
  branch_taken BC_NE (sv_denot E a) (sv_denot E b) = false.
Proof. intros E a b H. rewrite branch_ne_U. unfold U. rewrite H, Z.eqb_refl. reflexivity. Qed.
Lemma o7_add0 : forall E x, sv_denot E (SAlu ALU_ADD x (SLit 0)) = sv_denot E x.
Proof.
intros E x. rewrite (denot_lit_U E (SAlu ALU_ADD x (SLit 0))), (denot_lit_U E x). f_equal.
rewrite U_SAlu, U_SLit. cbn [zalu_raw]. pose proof (U_range E x) as HR.
unfold zcanon, M64 in *. rewrite Z.mod_0_l by lia. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.
Lemma o7_ew_app : forall cx E regs xs k, (k < 563)%nat ->
  ew (d_env cx E (obs_vals regs ++ xs)) k = ew (d_env cx E (obs_vals regs)) k.
Proof.
intros cx E regs xs k Hk.
destruct (lt_dec k AT_FL) as [Hlt|Hge].
- rewrite !oy_d_env_old by exact Hlt. reflexivity.
- destruct (Nat.eq_dec k AT_FL) as [->|Hne].
  + rewrite !oy_d_env_fl. reflexivity.
  + assert (Hj : exists j, k = (AT_X + j)%nat /\ (j < 32)%nat)
      by (exists (k - AT_X)%nat; unfold AT_X, AT_FL in *; split; lia).
    destruct Hj as (j & -> & Hj).
    rewrite (oy_d_env_x cx E (obs_vals regs ++ xs) j) by (rewrite length_app, o7_obs_len; lia).
    rewrite (oy_d_env_x cx E (obs_vals regs) j) by (rewrite o7_obs_len; lia).
    rewrite app_nth1 by (rewrite o7_obs_len; lia). reflexivity.
Qed.
Lemma o7_ew_x : forall cx E regs xs k, (563 <= k)%nat -> (k - 563 < length xs)%nat ->
  ew (d_env cx E (obs_vals regs ++ xs)) k = nth (k - 563) xs (Z_to_bv 64 0).
Proof.
intros cx E regs xs k Hk Hj.
assert (Hk' : k = (AT_X + (32 + (k - 563)))%nat) by (unfold AT_X; lia).
rewrite Hk' at 1.
rewrite (oy_d_env_x cx E (obs_vals regs ++ xs) (32 + (k - 563))) by (rewrite length_app, o7_obs_len; lia).
rewrite app_nth2 by (rewrite o7_obs_len; lia). rewrite o7_obs_len.
replace (32 + (k - 563) - 32)%nat with (k - 563)%nat by lia. reflexivity.
Qed.
Lemma o7_regs_ok : forall cx E regs xs, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs ++ xs)) obs_sr regs.
Proof.
intros cx E regs xs HE HL HA.
pose proof (regs_ok_obs B cx E regs HE HL HA) as R.
apply regs_ok_by_cases. intros r Hr. rewrite (R r).
cbv [all_regs In] in Hr.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ];
  (match goal with |- sv_denot _ (sr_get ?sr ?r) = _ =>
     let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end);
  first [ reflexivity | cbn [sv_denot]; rewrite o7_ew_app by lia; reflexivity ].
Qed.

Definition o7_xs (T Sg T' : list byte) (ow ret ai : Z) : list word :=
  [w64 (u_at T' (48 * ai + 8) 4);
   w64 (u_at T' (48 * ai + 12) 1);
   w64 (u_at T' (48 * ai + 13) 1);
   w64 (u_at T' (48 * ai + 14) 1);
   w64 (u_at T' (48 * ai + 15) 1);
   w64 (u_at T' (48 * ai + 16) 1);
   w64 (if ow =? 0 then u64 (owned_of T ai) else 1);
   w64 ret].
Definition o7_fcs (e : Z) : list YP09.chunk :=
  [YP09.mkChunk (e + 8) (CVal 4 (SOff 563 0));
   YP09.mkChunk (e + 12) (CVal 1 (SOff 564 0));
   YP09.mkChunk (e + 13) (CVal 1 (SOff 565 0));
   YP09.mkChunk (e + 14) (CVal 1 (SOff 566 0));
   YP09.mkChunk (e + 15) (CVal 1 (SOff 567 0));
   YP09.mkChunk (e + 16) (CVal 1 (SOff 568 0))].
Definition o7_acs : list YP09.chunk :=
  [YP09.mkChunk 64 (CVal 8 (SExt true 32 (SOff 563 0)));
   YP09.mkChunk 56 (CVal 8 (SOff 569 0));
   YP09.mkChunk 360 (CVal 8 (SOff 570 0))].
Definition o7_rs (acs fcs : list YP09.chunk) : smem :=
  [YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ fcs);
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_rec)].

Lemma o7_fcs_ok : forall cx (E : env) (regs : bvmap 5 word) (W : world SEGS) m (T Sg T' : list byte) (ow ret ai : Z),
  length T' = 400%nat -> 0 <= ai < 8 ->
  garr8 SEGS (rd W m) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T') ->
  Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (rd W m) (d_FB cx))
    (o7_fcs (2160 + 48 * ai)).
Proof.
intros cx E regs W m T Sg T' ow ret ai LT' Hai GT.
assert (HL' : Z.of_nat (length T') = 400) by (rewrite LT'; reflexivity).
unfold o7_fcs. repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS _ (rd W m) (d_FB cx) (2160 + 48 * ai + 8) 4%N (SOff 563 0) (u_at T' (48 * ai + 8) 4)).
  + apply o7_sv_atom. rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 563) by (cbn [length o7_xs]; lia).
    unfold o7_xs; cbn [nth]; reflexivity.
  + exact (o7_u_rng T' (48 * ai + 8) 4).
  + cbn [Z.of_N]; lia.
  + match goal with |- val_mem _ _ ?a _ _ => replace a with (d_obj cx OT + (48 * ai + 8)) by (unfold d_obj, dobj_off; lia) end.
    change (N.to_nat 4) with 4%nat. apply o7_u_val; [exact GT | lia | rewrite HL'; cbn [Z.of_nat]; lia].
- apply (chunk_ok_val SEGS _ (rd W m) (d_FB cx) (2160 + 48 * ai + 12) 1%N (SOff 564 0) (u_at T' (48 * ai + 12) 1)).
  + apply o7_sv_atom. rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 564) by (cbn [length o7_xs]; lia).
    unfold o7_xs; cbn [nth]; reflexivity.
  + exact (o7_u_rng T' (48 * ai + 12) 1).
  + cbn [Z.of_N]; lia.
  + match goal with |- val_mem _ _ ?a _ _ => replace a with (d_obj cx OT + (48 * ai + 12)) by (unfold d_obj, dobj_off; lia) end.
    change (N.to_nat 1) with 1%nat. apply o7_u_val; [exact GT | lia | rewrite HL'; cbn [Z.of_nat]; lia].
- apply (chunk_ok_val SEGS _ (rd W m) (d_FB cx) (2160 + 48 * ai + 13) 1%N (SOff 565 0) (u_at T' (48 * ai + 13) 1)).
  + apply o7_sv_atom. rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 565) by (cbn [length o7_xs]; lia).
    unfold o7_xs; cbn [nth]; reflexivity.
  + exact (o7_u_rng T' (48 * ai + 13) 1).
  + cbn [Z.of_N]; lia.
  + match goal with |- val_mem _ _ ?a _ _ => replace a with (d_obj cx OT + (48 * ai + 13)) by (unfold d_obj, dobj_off; lia) end.
    change (N.to_nat 1) with 1%nat. apply o7_u_val; [exact GT | lia | rewrite HL'; cbn [Z.of_nat]; lia].
- apply (chunk_ok_val SEGS _ (rd W m) (d_FB cx) (2160 + 48 * ai + 14) 1%N (SOff 566 0) (u_at T' (48 * ai + 14) 1)).
  + apply o7_sv_atom. rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 566) by (cbn [length o7_xs]; lia).
    unfold o7_xs; cbn [nth]; reflexivity.
  + exact (o7_u_rng T' (48 * ai + 14) 1).
  + cbn [Z.of_N]; lia.
  + match goal with |- val_mem _ _ ?a _ _ => replace a with (d_obj cx OT + (48 * ai + 14)) by (unfold d_obj, dobj_off; lia) end.
    change (N.to_nat 1) with 1%nat. apply o7_u_val; [exact GT | lia | rewrite HL'; cbn [Z.of_nat]; lia].
- apply (chunk_ok_val SEGS _ (rd W m) (d_FB cx) (2160 + 48 * ai + 15) 1%N (SOff 567 0) (u_at T' (48 * ai + 15) 1)).
  + apply o7_sv_atom. rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 567) by (cbn [length o7_xs]; lia).
    unfold o7_xs; cbn [nth]; reflexivity.
  + exact (o7_u_rng T' (48 * ai + 15) 1).
  + cbn [Z.of_N]; lia.
  + match goal with |- val_mem _ _ ?a _ _ => replace a with (d_obj cx OT + (48 * ai + 15)) by (unfold d_obj, dobj_off; lia) end.
    change (N.to_nat 1) with 1%nat. apply o7_u_val; [exact GT | lia | rewrite HL'; cbn [Z.of_nat]; lia].
- apply (chunk_ok_val SEGS _ (rd W m) (d_FB cx) (2160 + 48 * ai + 16) 1%N (SOff 568 0) (u_at T' (48 * ai + 16) 1)).
  + apply o7_sv_atom. rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 568) by (cbn [length o7_xs]; lia).
    unfold o7_xs; cbn [nth]; reflexivity.
  + exact (o7_u_rng T' (48 * ai + 16) 1).
  + cbn [Z.of_N]; lia.
  + match goal with |- val_mem _ _ ?a _ _ => replace a with (d_obj cx OT + (48 * ai + 16)) by (unfold d_obj, dobj_off; lia) end.
    change (N.to_nat 1) with 1%nat. apply o7_u_val; [exact GT | lia | rewrite HL'; cbn [Z.of_nat]; lia].
Qed.

Lemma o7_acs_ok : forall cx (E : env) (regs : bvmap 5 word) (W : world SEGS) m (T Sg T' : list byte) (ow ret ai : Z),
  0 <= ai < 8 -> 0 <= ret < 2 ^ 64 ->
  role_of_e T' ai = slot_known.want_role (s_role Sg) (role_of_e T ai) ->
  val_mem SEGS (rd W m) (d_A cx + 64) 8 (u64 (slot_known.want_role (s_role Sg) (role_of_e T ai))) ->
  val_mem SEGS (rd W m) (d_A cx + 56) 8 (if ow =? 0 then u64 (owned_of T ai) else 1) ->
  val_mem SEGS (rd W m) (d_A cx + 360) 8 ret ->
  Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (rd W m) (d_A cx)) o7_acs.
Proof.
intros cx E regs W m T Sg T' ow ret ai Hai Hret Erole V64 V56 V360.
assert (Hrng32 : 0 <= u_at T' (48 * ai + 8) 4 < 2 ^ 32)
  by (pose proof (o7_u_rng T' (48 * ai + 8) 4) as HH; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HH; lia).
assert (EW563 : ew (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) 563 = Z_to_bv 64 (u_at T' (48 * ai + 8) 4))
  by (rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 563) by (cbn [length o7_xs]; lia); unfold o7_xs; cbn [nth]; reflexivity).
unfold o7_acs. repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS _ (rd W m) (d_A cx) 64 8%N (SExt true 32 (SOff 563 0))
          (u64 (slot_known.want_role (s_role Sg) (role_of_e T ai)))).
  + rewrite (o7_sv_sext32 _ 563 (u_at T' (48 * ai + 8) 4) EW563 Hrng32).
    change (bv_swrap 32 (u_at T' (48 * ai + 8) 4)) with (role_of_e T' ai). rewrite Erole, o7_w64u64. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply oy_u64_rng.
  + cbn [Z.of_N]; lia.
  + change (N.to_nat 8) with 8%nat. exact V64.
- apply (chunk_ok_val SEGS _ (rd W m) (d_A cx) 56 8%N (SOff 569 0) (if ow =? 0 then u64 (owned_of T ai) else 1)).
  + apply o7_sv_atom. rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 569) by (cbn [length o7_xs]; lia).
    unfold o7_xs; cbn [nth]; reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). destruct (ow =? 0); [apply oy_u64_rng | lia].
  + cbn [Z.of_N]; lia.
  + change (N.to_nat 8) with 8%nat. exact V56.
- apply (chunk_ok_val SEGS _ (rd W m) (d_A cx) 360 8%N (SOff 570 0) ret).
  + apply o7_sv_atom. rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) 570) by (cbn [length o7_xs]; lia).
    unfold o7_xs; cbn [nth]; reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hret.
  + cbn [Z.of_N]; lia.
  + change (N.to_nat 8) with 8%nat. exact V360.
Qed.

Lemma o7_sub : forall acs fcs, submem (o7_rs acs fcs) (d_kregions dsh_rec acs fcs ++ []).
Proof.
intros acs fcs. unfold o7_rs, d_kregions. cbn [app].
apply submem_drop.
apply submem_keep;
  [ unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [left; lia|]; intros c Hc; exact Hc |].
apply submem_keep;
  [ unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [left; lia|]; intros c Hc; exact Hc |].
apply submem_keep;
  [ unfold fshadow_region, subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [left; lia|]; intros c Hc; exact Hc |].
apply submem_drop. apply submem_drop. apply submem_nil.
Qed.

Theorem ob_s9b1 : ob_seg9b1 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HB & HJ & HFR & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HTl0 & HTok0 & HFR0 & Hair & How & HOM & Hsp24 & Hr24).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
pose proof Hframe as (E & HdE & Hregions & Hrdword & _).
pose proof HTok0 as (T1 & T2 & T3 & T4). unfold tbl_T1 in T1.
pose proof HSf as (_ & _ & _ & _ & _ & HSok & _).
destruct (o7_sight_S12 Sg HSok) as (S1 & S2).
assert (Hai8 : 0 <= ai < 8) by lia.
pose proof (known_arm T Sg ow now T' ret ai HFR0 ltac:(lia) HOM) as EK.
destruct (o7_fields T Sg T' ow now ret ai HTl0 HSgl Hair Hai8 T2 T4 S1 S2 ltac:(lia) Hnow EK)
  as (Erole & Ehd & Edin & Edout & Efam & Eslots & _ & _ & _ & _ & Eret).
assert (Hret : 0 <= ret < 2 ^ 64) by (rewrite Eret; destruct (slot_observe.c_any T Sg ow ai); cbn; lia).
pose proof Hsp24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & V64 & V56 & V360 & _ & _).
pose proof Hr24 as (R10 & R24 & R21 & R25 & R23 & R22 & R26).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof alloc_ceiling_val as ACV.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof HdE as (EE & E32 & HEI0 & E60 & EF & ESH).
assert (EW : forall q v, (563 <= q)%nat -> (q - 563 < 8)%nat ->
  nth (q - 563) (o7_xs T Sg T' ow ret ai) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  ew (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) q = Z_to_bv 64 v)
  by (intros q v Hq1 Hq2 Hnq; rewrite (o7_ew_x cx E regs (o7_xs T Sg T' ow ret ai) q) by (cbn [length o7_xs]; lia); exact Hnq).
assert (R256 : forall p, 0 <= u_at T' p 1 < 256)
  by (intros p; pose proof (o7_u_rng T' p 1) as HH; change (2 ^ (8 * Z.of_nat 1)) with 256 in HH; exact HH).
assert (D26 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SOff AT_F (2160 + 48 * ai))
  = w64 (d_obj cx OT + 48 * ai)).
{ cbn [sv_denot]. rewrite oy_d_env_old by (unfold AT_F, AT_FL; lia). rewrite EF, oy_w64_add_w.
  unfold w64, d_obj, dobj_off. f_equal. lia. }
assert (D24 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SExt false 8 (SOff 564 0))
  = w64 (if s_hd Sg =? 0 then hd_of T ai else 1)).
{ rewrite (o7_sv_zext8 _ 564 (u_at T' (48 * ai + 12) 1)); [|apply EW; [lia | lia | reflexivity] | apply R256].
  change (u_at T' (48 * ai + 12) 1) with (hd_of T' ai). rewrite Ehd. reflexivity. }
assert (D21 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SExt false 8 (SOff 565 0))
  = w64 (if s_hd Sg =? 0 then din_of T ai else s_din Sg)).
{ rewrite (o7_sv_zext8 _ 565 (u_at T' (48 * ai + 13) 1)); [|apply EW; [lia | lia | reflexivity] | apply R256].
  change (u_at T' (48 * ai + 13) 1) with (din_of T' ai). rewrite Edin. reflexivity. }
assert (D25 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SExt false 8 (SOff 566 0))
  = w64 (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg)).
{ rewrite (o7_sv_zext8 _ 566 (u_at T' (48 * ai + 14) 1)); [|apply EW; [lia | lia | reflexivity] | apply R256].
  change (u_at T' (48 * ai + 14) 1) with (dout_of T' ai). rewrite Edout. reflexivity. }
assert (D22 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SExt false 8 (SOff 567 0))
  = w64 (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg)).
{ rewrite (o7_sv_zext8 _ 567 (u_at T' (48 * ai + 15) 1)); [|apply EW; [lia | lia | reflexivity] | apply R256].
  change (u_at T' (48 * ai + 15) 1) with (reac_disco_table_observe_c.fam_of T' ai). rewrite Efam. reflexivity. }
assert (D23 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SExt false 8 (SOff 568 0))
  = w64 (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg)).
{ rewrite (o7_sv_zext8 _ 568 (u_at T' (48 * ai + 16) 1)); [|apply EW; [lia | lia | reflexivity] | apply R256].
  change (u_at T' (48 * ai + 16) 1) with (reac_disco_table_observe_c.slots_of T' ai). rewrite Eslots. reflexivity. }
assert (D15 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SExt true 32 (SOff 563 0))
  = w64 (u64 (slot_known.want_role (s_role Sg) (role_of_e T ai)))).
{ assert (Hr32 : 0 <= u_at T' (48 * ai + 8) 4 < 2 ^ 32)
    by (pose proof (o7_u_rng T' (48 * ai + 8) 4) as HH; change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in HH; exact HH).
  rewrite (o7_sv_sext32 _ 563 (u_at T' (48 * ai + 8) 4)); [|apply EW; [lia | lia | reflexivity] | exact Hr32].
  change (bv_swrap 32 (u_at T' (48 * ai + 8) 4)) with (role_of_e T' ai). rewrite Erole.
  unfold w64. rewrite o7_w64u64. reflexivity. }
assert (D7 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SOff 569 0)
  = w64 (if ow =? 0 then u64 (owned_of T ai) else 1))
  by (apply o7_sv_atom; apply EW; [lia | lia | reflexivity]).
assert (D5 : sv_denot (d_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai)) (SOff 570 0) = w64 ret)
  by (apply o7_sv_atom; apply EW; [lia | lia | reflexivity]).
pose proof (o7_regs_ok cx E regs (o7_xs T Sg T' ow ret ai) HdE HrL HAr2) as HROK.
pose proof (FACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs ++ o7_xs T Sg T' ow ret ai) [] [] Hctx HdE I I) as HFACTS.
pose proof (o7_fcs_ok cx E regs W mem3 T Sg T' ow ret ai HTl Hai8 HT) as HFCS.
pose proof (o7_acs_ok cx E regs W mem3 T Sg T' ow ret ai Hai8 Hret Erole V64 V56 V360) as HACS.
pose proof (oy_d_E_env cx E (obs_vals regs ++ o7_xs T Sg T' ow ret ai) HdE) as HdE2.
pose proof HdE2 as (_ & _ & HEI & _).
unfold cfg_at. change (w64 (BASE + OB_BC_RET)) with (Z_to_bv 64 (BASE + OB_BC_RET)).
assert (Hm : ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
destruct Hm as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
all: pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_BC_RET obs_sr _ o7_acs _ []
       (d_facts [] []) Hctx HdE Hregions Hrdword HROK HFACTS HACS HFCS (Forall_nil _) I (Forall_nil _)
       ltac:(vm_compute; reflexivity)) as HS0;
     unfold ss_d in HS0;
     lazymatch type of HS0 with st_ok_pi _ _ _ (mkSS ?pc0 ?sr0 (d_kregions _ ?acs0 ?fcs0 ++ _) ?rv0 ?G0) ?ms0 =>
       pose proof (st_ok_pi_submem _ (mkSS pc0 sr0 (d_kregions dsh_rec acs0 fcs0 ++ []) rv0 G0) ms0 (o7_rs acs0 fcs0) HS0
         (o7_sub acs0 fcs0) ltac:(vm_compute; reflexivity)) as HS1
     end;
     clear HS0; norm_ss HS1.
all: lazymatch goal with HS1 : st_ok_pi _ _ ?Ex ?ss ?ms |- _ =>
       pose proof (st_ok_pi_set_reg Ex ss ms 10%bv (SLit 0) HS1 ltac:(discriminate)
         ltac:(cbn [ms_regs restrict mkst sv_denot]; exact R10)) as HS2 end;
     clear HS1; norm_ss HS2.
all: lazymatch goal with HS2 : st_ok_pi _ _ ?Ex ?ss ?ms, D : sv_denot _ (SOff AT_F ?o26) = _ |- _ =>
       pose proof (st_ok_pi_set_reg Ex ss ms 26%bv (SOff AT_F o26) HS2 ltac:(discriminate)
         ltac:(cbn [ms_regs restrict mkst]; rewrite D; exact R26)) as HS3 end;
     clear HS2; norm_ss HS3.
all: lazymatch goal with HS3 : st_ok_pi _ _ ?Ex ?ss ?ms |- _ =>
       pose proof (st_ok_pi_set_reg Ex ss ms 24%bv (SExt false 8 (SOff 564 0)) HS3 ltac:(discriminate)
         ltac:(cbn [ms_regs restrict mkst]; rewrite D24; exact R24)) as HS4 end;
     clear HS3; norm_ss HS4.
all: lazymatch goal with HS4 : st_ok_pi _ _ ?Ex ?ss ?ms |- _ =>
       pose proof (st_ok_pi_set_reg Ex ss ms 21%bv (SExt false 8 (SOff 565 0)) HS4 ltac:(discriminate)
         ltac:(cbn [ms_regs restrict mkst]; rewrite D21; exact R21)) as HS5 end;
     clear HS4; norm_ss HS5.
all: lazymatch goal with HS5 : st_ok_pi _ _ ?Ex ?ss ?ms |- _ =>
       pose proof (st_ok_pi_set_reg Ex ss ms 25%bv (SExt false 8 (SOff 566 0)) HS5 ltac:(discriminate)
         ltac:(cbn [ms_regs restrict mkst]; rewrite D25; exact R25)) as HS6 end;
     clear HS5; norm_ss HS6.
all: lazymatch goal with HS6 : st_ok_pi _ _ ?Ex ?ss ?ms |- _ =>
       pose proof (st_ok_pi_set_reg Ex ss ms 23%bv (SExt false 8 (SOff 568 0)) HS6 ltac:(discriminate)
         ltac:(cbn [ms_regs restrict mkst]; rewrite D23; exact R23)) as HS7 end;
     clear HS6; norm_ss HS7.
all: lazymatch goal with HS7 : st_ok_pi _ _ ?Ex ?ss ?ms |- _ =>
       pose proof (st_ok_pi_set_reg Ex ss ms 22%bv (SExt false 8 (SOff 567 0)) HS7 ltac:(discriminate)
         ltac:(cbn [ms_regs restrict mkst]; rewrite D22; exact R22)) as HS end;
     clear HS7; norm_ss HS.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
       assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ex (rd W mem3)) by constructor end.
all: pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
all: paj_run_to_tok RUNTO HS HJ SHOK OBspan OB_C12;
     [ cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil | ].
all: pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MA; clear HF HFr HG.
all: pose (RUN := paj_run (fx := fq) B LAWS); pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
all: psrr_branch_tok RUN BR HS SHOK OBspan.
all: lazymatch goal with
     | Hc : branch_taken BC_NE (sv_denot ?Ex ?a) (sv_denot _ ?b) = true |- _ =>
         exfalso; rewrite (o7_br_ne_false Ex a b (eq_sym (o7_add0 Ex a))) in Hc; discriminate Hc
     | Hc : branch_taken BC_NE _ _ = false |- _ => clear Hc
     end.
all: paj_run_to_tok RUNTO HS HJ SHOK OBspan OB_C12;
     [ cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil | ].
all: pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MB; clear HF HFr HG.
all: lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?mF) |- _ =>
  assert (MEQ : forall x, ms_mem mF x = mem3 x) by (intros x; rewrite MB; apply MA);
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs mF) r = getr regs r)
    by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ mF r HS), (HROK r); cbv [In] in Hr;
        repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
  assert (HrL' : d_rL B cx (ms_regs mF))
    by (pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27); unfold d_rL, spZ in *;
        rewrite (RG 2%bv), (RG 3%bv), (RG 4%bv), (RG 8%bv), (RG 9%bv), (RG 19%bv), (RG 18%bv), (RG 20%bv), (RG 27%bv)
          by (cbv; tauto);
        repeat split; assumption);
  apply SRr_ret;
  eapply (oy_c12 fq cx h i n now op nb fr len Sg T T' _ ow ret kmax accmax ly3 S3 W _ k acc _ _ mF
    HFRM0 HB HJ HFR Hk Hnev Hmo Hacc HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    (oy_oc_pt B cx h i n now op nb fr len Sg T' regs (ms_regs mF) ly3 S3 W mem3 (ms_mem mF) BRT MEQ HrL' HOC)
    HTl0 HTok0 HFR0 Hair How HOM (oy_sp24_pt cx T Sg _ ow ret W mem3 (ms_mem mF) MEQ Hsp24));
  unfold ob_r12;
  repeat split;
  match goal with |- getr _ ?r = _ =>
    rewrite (st_ok_pi_restrict_reg (w_H W) _ _ mF r HS);
    match goal with |- sv_denot _ (sr_get ?sr ?rr) = _ =>
      let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end
  end;
  first [ exact D26 | exact D24 | exact D21 | exact D23 | exact D22 | exact D15 | exact D7 | exact D5
        | rewrite o7_add0; exact D25 ]
end.
Qed.

End h.
End f.
End d.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 511 of its 551 lines of code are new or changed and 505 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_observe_c slot_observe slot_known.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts
FindEntry CheckTable RoleOf ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition o5_sr : list sv :=
  map (fun r => match r with 24%nat => SOff AT_F 2160 | _ => sr_x r end) (seq 0 32).
Definition o5_acs : list YP09.chunk := [YP09.mkChunk 352 (CVal 8 (SOff 564 0))].
Definition o5_fcs : list YP09.chunk := [YP09.mkChunk 2552 (CVal 4 (SOff 563 0))].
Definition o5_x (T T' : list byte) (ai : Z) : list word := [w64 (u_at T' 392 4); w64 (u64 (oldv ai (role_of_e T ai)))].

Lemma o5_u_rng : forall (T : list byte) p (n : nat), 0 <= u_at T p n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T p n. unfold u_at. pose proof (YK11.bytes_le_to_Z_nonneg (sub T p n)) as H0.
pose proof (YK11.bytes_le_to_Z_bound (sub T p n)) as H1.
assert (L : (length (sub T p n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma o5_sw : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_swrap 64 (zcanon (zcanon x)) = x.
Proof.
intros x Hx. rewrite (zcanon_wrap (zcanon x)), swrap_wrap', zcanon_wrap, swrap_wrap'. apply swrap64_id. unfold half64. lia.
Qed.
Lemma o5_z0 : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> (zcanon (zcanon x) <? zcanon 1) = (x =? 0).
Proof.
intros x Hx. unfold zcanon, M64. rewrite Zmod_mod. change (1 mod 2 ^ 64) with 1.
destruct (Z.eqb_spec x 0) as [->|Hn]; [reflexivity|]. apply Z.ltb_ge.
destruct (Z.ltb_spec x 0) as [Hl|Hl].
- replace (x mod 2 ^ 64) with (x + 2 ^ 64).
  + lia.
  + apply (Z.mod_unique x (2 ^ 64) (-1)); lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma o5_m64 : forall x, zcanon x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
intros x. unfold zcanon, M64. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
rewrite (Z.div_mod x (2 ^ 32 * 2 ^ 32)) at 2 by lia.
replace (2 ^ 32 * 2 ^ 32 * (x / (2 ^ 32 * 2 ^ 32)) + x mod (2 ^ 32 * 2 ^ 32))
  with (x mod (2 ^ 32 * 2 ^ 32) + (2 ^ 32 * (x / (2 ^ 32 * 2 ^ 32))) * 2 ^ 32) by ring.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma o5_arith : forall s ret f, 0 <= s < 2 ^ 32 ->
  ((s + ret + f) mod 2 ^ 32 - ((ret + bv_swrap 32 s) mod 2 ^ 32 + f mod 2 ^ 32)) mod 2 ^ 32 = 0.
Proof.
intros s ret f Hs.
assert (Hw : exists b, bv_swrap 32 s = s - 2 ^ 32 * b).
{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  change (2 ^ 32 / 2) with (2 ^ 31).
  destruct (Z.ltb_spec s (2 ^ 31)).
  - exists 0. rewrite Z.mod_small by lia. lia.
  - exists 1. replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
destruct Hw as [b ->].
replace (ret + (s - 2 ^ 32 * b)) with (ret + s + (- b) * 2 ^ 32) by ring.
rewrite Z_mod_plus_full.
rewrite Zminus_mod, Zmod_mod, <- Zplus_mod.
replace (ret + s + f) with (s + ret + f) by ring.
rewrite Z.sub_diag. reflexivity.
Qed.
Lemma o5_blt : forall E a v, ew E a = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff a 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E a v H Hv. change (branch_taken BC_LT (sv_denot E (SOff a 0)) (sv_denot E (SLit 0))) with (Sg E (SOff a 0) <? Sg E (SLit 0)).
rewrite S_SOff, S_SLit, H, unsigned_lit, Z.add_0_r, zcanon_wrap, swrap_wrap', swrap64_id by (unfold half64; lia). reflexivity.
Qed.

Definition o5_seqc : acond :=
  mkAC BC_EQ (SExt true 32 (SOff 563 0))
    (SAluw ALU_ADD (SAlu ALU_ADD (SOff 552 0) (SOff 554 0))
       (SAlu ALU_AND (SAlu ALU_AND (SAlu ALU_SLT (SOff 557 0) (SLit 0)) (SAlu ALU_SLTU (SOff 553 0) (SLit 1)))
          (SAlu ALU_XOR (SAlu ALU_SLT (SOff 556 0) (SLit 8)) (SLit (-1))))).
Lemma o5_flag : forall E (ai ov nn : Z),
  ew E 557 = Z_to_bv 64 ai -> - 2 ^ 63 <= ai < 2 ^ 63 ->
  ew E 553 = Z_to_bv 64 ov -> - 2 ^ 63 <= ov < 2 ^ 63 ->
  ew E 556 = Z_to_bv 64 nn -> - 2 ^ 63 <= nn < 2 ^ 63 ->
  U E (SAlu ALU_AND (SAlu ALU_AND (SAlu ALU_SLT (SOff 557 0) (SLit 0)) (SAlu ALU_SLTU (SOff 553 0) (SLit 1)))
        (SAlu ALU_XOR (SAlu ALU_SLT (SOff 556 0) (SLit 8)) (SLit (-1)))) =
  Z.b2z ((ai <? 0) && (ov =? 0) && negb (nn <? 8)).
Proof.
intros E ai ov nn Ha Ra Ho Ro Hn Rn.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, !U_SOff, Ha, Ho, Hn, !unsigned_lit, !Z.add_0_r.
rewrite (o5_sw ai Ra), (o5_sw nn Rn), (o5_z0 ov Ro).
change (bv_swrap 64 (zcanon 0)) with 0. change (bv_swrap 64 (zcanon 8)) with 8.
destruct (ai <? 0), (ov =? 0), (nn <? 8); vm_compute; reflexivity.
Qed.
Lemma o5_seq : forall E (u ret s ai ov nn : Z),
  ew E 563 = Z_to_bv 64 u -> 0 <= u < 2 ^ (8 * Z.of_nat 4) ->
  ew E 554 = Z_to_bv 64 ret -> 0 <= ret <= 1 ->
  ew E 552 = Z_to_bv 64 (bv_swrap 32 s) -> 0 <= s < 2 ^ (8 * Z.of_nat 4) ->
  ew E 557 = Z_to_bv 64 ai -> - 2 ^ 63 <= ai < 2 ^ 63 ->
  ew E 553 = Z_to_bv 64 ov -> - 2 ^ 63 <= ov < 2 ^ 63 ->
  ew E 556 = Z_to_bv 64 nn -> - 2 ^ 63 <= nn < 2 ^ 63 ->
  u = (s + ret + Z.b2z ((ai <? 0) && (ov =? 0) && negb (nn <? 8))) mod 2 ^ 32 ->
  acond_ok E o5_seqc.
Proof.
intros E u ret s ai ov nn Hu Ru Hr Rr Hs Rs Ha Ra Ho Ro Hn Rn Heq.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Ru, Rs.
unfold acond_ok, o5_seqc. cbn [ac_c ac_a ac_b].
rewrite branch_eq_U. apply Z.eqb_eq.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
rewrite (o5_flag E ai ov nn Ha Ra Ho Ro Hn Rn).
rewrite U_SExt, (U_atom E 563 u Hu) by lia. cbv iota.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hr, Hs, !unsigned_lit, !Z.add_0_r.
rewrite (Z.add_comm (zcanon (zcanon (bv_swrap 32 s))) (zcanon (zcanon ret))).
set (f := Z.b2z ((ai <? 0) && (ov =? 0) && negb (nn <? 8))) in *.
clearbody f. subst u.
change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (o5_m64 (zcanon (zcanon ret) + zcanon (zcanon (bv_swrap 32 s)))).
rewrite (Zplus_mod (zcanon (zcanon ret)) (zcanon (zcanon (bv_swrap 32 s))) (2 ^ 32)).
rewrite (o5_m64 (zcanon ret)), (o5_m64 ret), (o5_m64 (zcanon (bv_swrap 32 s))), (o5_m64 (bv_swrap 32 s)).
rewrite <- (Zplus_mod ret (bv_swrap 32 s) (2 ^ 32)).
rewrite (Zmod_mod (s + ret + f) (2 ^ 32)).
rewrite zcanon_wrap. f_equal.
apply (swrapN_congr 32). change (2 ^ Z.of_N 32) with (2 ^ 32).
apply o5_arith. exact Rs.
Qed.

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
Context {PX : YXcalls.PAXcalls lib_both3_0_listing}.

Lemma o5_atom : forall cx E regs X j, (j < length X)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (563 + j) = nth j X (Z_to_bv 64 0).
Proof.
intros cx E regs X j Hj.
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite oy_d_env_x by (rewrite length_app; lia).
rewrite app_nth2 by lia. rewrite L. f_equal. lia.
Qed.
Lemma o5_regatom : forall cx E regs X (j : nat), (j < 32)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (531 + j) = getr regs (Z_to_bv 5 (Z.of_nat j)).
Proof.
intros cx E regs X j Hj.
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
replace (531 + j)%nat with (AT_X + j)%nat by (unfold AT_X; lia).
rewrite oy_d_env_x by (rewrite length_app; lia).
rewrite app_nth1 by lia. unfold obs_vals.
rewrite (nth_indep _ _ ((fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))) 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite (map_nth (fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) 0%nat j).
rewrite seq_nth by lia. reflexivity.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (oc B).
#[local] Notation ob_c6 := (ob_c6 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c7 := (ob_c7 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c9 := (ob_c9 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c10 := (ob_c10 B MT XM_LIB RLO RHI tfib_K).

Lemma o5_regs_ok : forall cx E regs X, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  getr regs 24 = w64 (d_obj cx OT) ->
  regs_ok (d_env cx E (obs_vals regs ++ X)) o5_sr regs.
Proof.
intros cx E regs X HE HL HA R24.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
pose proof HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27).
assert (D60 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D32 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact E32).
assert (D516 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 516 2160) = w64 (d_obj cx OT)).
{ cbn [sv_denot]. rewrite oy_d_env_old by (unfold AT_FL; lia).
  change 516%nat with AT_F. rewrite EF. unfold w64. rewrite oy_w64_add_w. unfold d_obj, dobj_off. reflexivity. }
assert (D529 : sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, oy_d_env_old by (unfold AT_FL; lia); exact ESH).
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 32)%nat ->
  sv_denot (d_env cx E (obs_vals regs ++ X)) (SOff q 0) = nth j (obs_vals regs) (Z_to_bv 64 0)).
{ intros j q -> Hj. rewrite sv_denot_SOff0. rewrite oy_d_env_x by (rewrite length_app; unfold obs_vals; rewrite length_map, length_seq; lia).
  rewrite app_nth1 by (unfold obs_vals; rewrite length_map, length_seq; lia). reflexivity. }
apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
repeat (destruct Hz as [<-|Hz];
  [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
      let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
    lazymatch goal with
    | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
    | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 ]
    | |- _ = sv_denot _ (SOff 516 2160) => rewrite D516; exact R24
    | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
        first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
    | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
    | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
    | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
    | |- _ = sv_denot _ (SOff ?q 0) =>
        let j := eval vm_compute in (q - 531)%nat in
        rewrite (DX j q eq_refl ltac:(lia)); unfold obs_vals; cbn [nth map seq]; f_equal; vm_compute; reflexivity
    end
  | ]).
destruct Hz.
Qed.

Lemma o5_obT_pt : forall cx now Sg T T' ai ow ret (W : world SEGS) (m m' : word -> option byte),
  (forall x, rd W m' x = rd W m x) -> obT cx now Sg T T' ai ow ret W m -> obT cx now Sg T T' ai ow ret W m'.
Proof.
intros cx now Sg T T' ai ow ret W m m' Hpt (LT & TO & FR & HOW & SP & V360 & OM).
destruct SP as (S64 & S56 & S352 & S192 & S104 & S96 & S88 & S80 & S296 & S72 & S48).
unfold obT, ob_sp22.
split; [exact LT|]. split; [exact TO|]. split; [exact FR|]. split; [exact HOW|].
split.
- split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S64)|]. split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S56)|].
  split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S352)|]. split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S192)|].
  split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S104)|]. split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S96)|].
  split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S88)|]. split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S80)|].
  split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S296)|].
  split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt S72) | exact (oy_val_mem_pt _ _ _ _ _ Hpt S48)].
- split; [exact (oy_val_mem_pt _ _ _ _ _ Hpt V360) | exact OM].
Qed.

Definition o5_rs : smem :=
  [YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ o5_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ o5_fcs)].
Lemma o5_sub : submem o5_rs (d_kregions dsh_rec o5_acs o5_fcs ++ []).
Proof.
unfold o5_rs, d_kregions. cbn [app].
apply submem_drop. apply submem_keep;
  [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
   split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [left; lia|]; intros c Hc; exact Hc|].
apply submem_keep;
  [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
   split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [left; lia|]; intros c Hc; exact Hc|].
apply submem_drop. apply submem_drop. apply submem_drop. apply submem_nil.
Qed.

Lemma o5_seat : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg (T T' : list byte) (ai ow ret : Z) (regs : bvmap 5 word)
    ly3 S3 W mem3 md3 k E cs,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W mem3)) (d_regions cx dsh_rec) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) = Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  oc cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 ->
  obT cx now Sg T T' ai ow ret W mem3 ->
  getr regs 24 = w64 (d_obj cx OT) -> 0 <= d_A cx < 2 ^ 64 ->
  conds_ok (d_env cx E (obs_vals regs ++ o5_x T T' ai)) cs ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (obs_vals regs ++ o5_x T T' ai))
    (ss_d OB_CT_RET o5_sr dsh_rec o5_acs o5_fcs [] (d_facts [] cs))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + OB_CT_RET)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E cs
  HC HE HRG HFL HOC HoT R24 HA HCS.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof HoT as (LT & TOK & HFR & HOW & HSP22 & V360 & HOM).
set (X := o5_x T T' ai).
assert (XA : forall j, (j < 2)%nat -> ew (d_env cx E (obs_vals regs ++ X)) (563 + j) = nth j X (Z_to_bv 64 0))
  by (intros j Hj; apply o5_atom; cbn; lia).
apply (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_CT_RET o5_sr
  (obs_vals regs ++ X) o5_acs o5_fcs [] (d_facts [] cs) HC HE HRG HFL).
- exact (o5_regs_ok cx E regs X HE HrL HA R24).
- exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E _ [] cs HC HE I HCS).
- unfold o5_acs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ 352 8 (SOff 564 0) (u64 (oldv ai (role_of_e T ai)))).
  + rewrite sv_denot_SOff0. exact (XA 1%nat ltac:(lia)).
  + apply oy_u64_rng.
  + cbn; lia.
  + change (N.to_nat 8) with 8%nat. exact (proj1 (proj2 (proj2 HSP22))).
- unfold o5_fcs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ 2552 4 (SOff 563 0) (u_at T' 392 4)).
  + rewrite sv_denot_SOff0. exact (XA 0%nat ltac:(lia)).
  + pose proof (ro_u_at_range T' 392) as R. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  + cbn; lia.
  + change (N.to_nat 4) with 4%nat. replace (d_FB cx + 2552) with (d_obj cx OT + 392) by (unfold d_obj, dobj_off; lia).
    exact (ro_val_mem4_garr8 (mrestrict (w_H W) mem3) (d_obj cx OT) T' 392 HT ltac:(lia) ltac:(rewrite HTl; lia)).
- apply Forall_nil.
- exact I.
- apply Forall_nil.
- vm_compute; reflexivity.
Qed.

Lemma o5_land : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg (T' : list byte) kmax accmax ly3 S3 W mem3 md4 k acc E ss ms
    (regs : bvmap 5 word) pc (X : bvmap 5 word -> world SEGS -> (word -> option byte) -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax -> mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  oc cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv -> getr (ms_regs ms) r = getr regs r) ->
  X (ms_regs ms) W (ms_mem ms) ->
  DAT cx pc kmax accmax (fun regs' ly S W' m md => oc cx h i n now op nb fr len Sg T' regs' ly S W' m /\ X regs' W' m)
    W (mkCfg ms md4).
Proof.
intros fq cx h i n now op nb fr len Sg T' kmax accmax ly3 S3 W mem3 md4 k acc E ss ms regs pc X
  HFRM0 HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc HOC MEQ RG HX.
pose proof HOC as (_ & _ & _ & _ & _ & HrL & _).
assert (HrL' : d_rL B cx (ms_regs ms)).
{ pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27). unfold d_rL.
  split; [unfold spZ in *; rewrite (RG 2%bv ltac:(cbv; tauto)); exact Hsp|].
  split; [rewrite (RG 3%bv ltac:(cbv; tauto)); exact Hgp|].
  split; [rewrite (RG 4%bv ltac:(cbv; tauto)); exact Htp|].
  split; [rewrite (RG 8%bv ltac:(cbv; tauto)); exact H8|].
  split; [rewrite (RG 9%bv ltac:(cbv; tauto)); exact H9|].
  split; [rewrite (RG 19%bv ltac:(cbv; tauto)); exact H19|].
  split; [rewrite (RG 18%bv ltac:(cbv; tauto)); exact H18|].
  split; [rewrite (RG 20%bv ltac:(cbv; tauto)); exact H20|].
  rewrite (RG 27%bv ltac:(cbv; tauto)); exact H27. }
pose proof (oy_oc_pt B cx h i n now op nb fr len Sg T' regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) BRT MEQ HrL' HOC) as HOC'.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFRM0|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|]. exact (conj HOC' HX).
Qed.

Definition o5_X7 (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret : Z) (regs : bvmap 5 word) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  obT cx now Sg T T' ai ow ret W m /\ ob_rT T ai regs /\ getr regs 23 = w64 ret /\ 0 <= ai /\ role_of_e T ai = 1 /\
  getr regs 1 = w64 (BASE + OB_RO_RET) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 11 = w64 (d_obj cx OS).
Definition o5_X9 (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret : Z) (regs : bvmap 5 word) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  obT cx now Sg T T' ai ow ret W m /\ getr regs 25 = w64 (n_of T) /\ getr regs 23 = w64 ret /\ 0 <= ai.
Definition o5_X10 (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret : Z) (regs : bvmap 5 word) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  obT cx now Sg T T' ai ow ret W m /\ getr regs 25 = w64 (n_of T) /\ getr regs 23 = w64 ret /\ ai < 0.
Lemma o5_c7_of : forall cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c,
  DAT cx AF_both3_role_of kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T' regs ly S W' m /\ o5_X7 cx now Sg T T' ai ow ret regs W' m)
    W c ->
  ob_c7 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFRM0 & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]).
destruct X as (XT & XR & X23 & X0 & XR1 & X1 & X10 & X11).
exists T, T', ai, ow, ret. repeat (split; [assumption|]). assumption.
Qed.
Lemma o5_c9_of : forall cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c,
  DAT cx OB_C9 kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T' regs ly S W' m /\ o5_X9 cx now Sg T T' ai ow ret regs W' m)
    W c ->
  ob_c9 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFRM0 & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]).
destruct X as (XT & X25 & X23 & X0).
exists T, T', ai, ow, ret. repeat (split; [assumption|]). assumption.
Qed.
Lemma o5_c10_of : forall cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c,
  DAT cx OB_C10 kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T' regs ly S W' m /\ o5_X10 cx now Sg T T' ai ow ret regs W' m)
    W c ->
  ob_c10 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFRM0 & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]).
destruct X as (XT & X25 & X23 & X0).
exists T, T', ai, ow, ret. repeat (split; [assumption|]). assumption.
Qed.

Theorem ob_s67 : ob_seg67 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HOT & HRT & R23 & R24 & R22 & R21).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof alloc_ceiling_val as Hac.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof HOT as (LT & TOK & HFR & HOW & HSP & V360 & HOM).
pose proof TOK as (HT1 & HT2 & _).
destruct HRT as (R25 & R26).
destruct (slot_observe.seq_target T Sg ow now T' ret ai LT HSgl HT1 HFR HOM) as (Hr0 & Hrf & EST).
assert (Hai : -1 <= ai < 8) by (unfold tbl_T1 in HT1; destruct HFR as [[-> _] | (Hr & _)]; lia).
assert (Hn8 : 0 <= n_of T <= 8) by exact HT1.
assert (Hov : - 2 ^ 31 <= ov_of T < 2 ^ 31) by (unfold ov_of, s32_at; apply swrap32_range).
assert (Hret : 0 <= ret <= 1) by (destruct (_ && _); cbn in Hrf; lia).
set (X := o5_x T T' ai).
set (Ev := d_env cx E (obs_vals regs ++ X)).
assert (E552 : ew Ev 552 = w64 (s32_at T 392))
  by (unfold Ev; change 552%nat with (531 + 21)%nat; rewrite (o5_regatom cx E regs X 21 ltac:(lia)), <- R21; f_equal; apply bv_eq; reflexivity).
assert (E553 : ew Ev 553 = w64 (ov_of T))
  by (unfold Ev; change 553%nat with (531 + 22)%nat; rewrite (o5_regatom cx E regs X 22 ltac:(lia)), <- R22; f_equal; apply bv_eq; reflexivity).
assert (E554 : ew Ev 554 = w64 ret)
  by (unfold Ev; change 554%nat with (531 + 23)%nat; rewrite (o5_regatom cx E regs X 23 ltac:(lia)), <- R23; f_equal; apply bv_eq; reflexivity).
assert (E556 : ew Ev 556 = w64 (n_of T))
  by (unfold Ev; change 556%nat with (531 + 25)%nat; rewrite (o5_regatom cx E regs X 25 ltac:(lia)), <- R25; f_equal; apply bv_eq; reflexivity).
assert (E557 : ew Ev 557 = w64 ai)
  by (unfold Ev; change 557%nat with (531 + 26)%nat; rewrite (o5_regatom cx E regs X 26 ltac:(lia)), <- R26; f_equal; apply bv_eq; reflexivity).
assert (XA : forall j, (j < 2)%nat -> ew Ev (563 + j) = nth j X (Z_to_bv 64 0)) by (intros j Hj; apply o5_atom; cbn; lia).
pose proof (XA 0%nat ltac:(lia)) as AX563. pose proof (XA 1%nat ltac:(lia)) as AX564.
unfold X in AX563, AX564. cbn [nth o5_x Nat.add] in AX563, AX564.
clear XA.
assert (CSEQ : acond_ok Ev o5_seqc).
{ apply (o5_seq Ev (u_at T' 392 4) ret (u_at T 392 4) ai (ov_of T) (n_of T) AX563 (o5_u_rng T' 392 4) E554 Hret E552
    (o5_u_rng T 392 4) E557 ltac:(lia) E553 ltac:(lia) E556 ltac:(lia)).
  exact EST. }
pose proof (o5_regs_ok cx E regs X HdE HrL HAr2 R24) as A1.
fold Ev in A1.
assert (HEI : img_env VAL A_LIM Ev).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold Ev, d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (E516 : ew Ev 516 = w64 (d_FB cx)).
{ unfold Ev, d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & EF & _). exact EF. }
assert (DF : forall off, sv_denot Ev (SOff 516 off) = w64 (d_FB cx + off)).
{ intros off. cbn [sv_denot]. rewrite E516. unfold w64. apply oy_w64_add_w. }
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNC.
unfold cfg_at. change (w64 (BASE + OB_CT_RET)) with (Z_to_bv 64 (BASE + OB_CT_RET)).
destruct (Z.ltb_spec ai 0) as [Hneg|Hpos].
- assert (CA : acond_ok Ev (mkAC BC_LT (SOff 557 0) (SLit 0))).
  { unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite (o5_blt Ev 557 ai E557 ltac:(lia)). apply Z.ltb_lt. exact Hneg. }
  pose proof (o5_seat fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E
    [o5_seqc; mkAC BC_LT (SOff 557 0) (SLit 0)] HC HdE Hregs Hflag HOC HOT R24 HAr2 (conj CSEQ (conj CA I))) as HS0.
  fold X Ev in HS0.
  pose proof (st_ok_pi_submem _ _ _ o5_rs HS0 o5_sub ltac:(vm_compute; reflexivity)) as HS1. clear HS0.
  paj_run_to_sh RUNTO HS1 HJ OB_C10.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  cbn [ms_mem mkst] in HF.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MEQ0.
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r HS1), (A1 r).
    cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
  apply SRr_ret. right. right.
  apply (o5_c10_of cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W _).
  apply (o5_land fq cx h i n now op nb fr len Sg T' kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs OB_C10 _
    HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HS1 eq_refl eq_refl HOC MEQ0
    ltac:(intros r Hr; apply RG; cbv [In] in Hr |- *; tauto)).
  unfold o5_X10. split; [|split; [|split]].
  + exact (o5_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) (oy_mrestrict_ext (w_H W) mem3 (ms_mem ms) MEQ0) HOT).
  + rewrite (RG 25%bv ltac:(cbv; tauto)). exact R25.
  + rewrite (RG 23%bv ltac:(cbv; tauto)). exact R23.
  + exact Hneg.
- assert (CA : acond_ok Ev (mkAC BC_GE (SOff 557 0) (SLit 0))).
  { unfold acond_ok. cbn [ac_c ac_a ac_b].
    change (branch_taken BC_GE (sv_denot Ev (SOff 557 0)) (sv_denot Ev (SLit 0)))
      with (negb (branch_taken BC_LT (sv_denot Ev (SOff 557 0)) (sv_denot Ev (SLit 0)))).
    rewrite (o5_blt Ev 557 ai E557 ltac:(lia)). apply negb_true_iff, Z.ltb_ge. exact Hpos. }
  assert (Hrr : - 2 ^ 31 <= role_of_e T ai < 2 ^ 31) by (unfold role_of_e, s32_at; apply swrap32_range).
  assert (U564 : U Ev (SOff 564 0) = u64 (role_of_e T ai)).
  { rewrite (U_atom Ev 564 _ AX564 (oy_u64_rng _)). unfold oldv. rewrite (proj2 (Z.ltb_ge ai 0) Hpos). reflexivity. }
  destruct (Z.eq_dec (role_of_e T ai) 1) as [Hr1|Hr1].
  + assert (HCR : acond_ok Ev (mkAC BC_EQ (SOff 564 0) (SLit 1))).
    { unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U564, U_lit by lia. rewrite Hr1. reflexivity. }
    pose proof (o5_seat fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E
      [o5_seqc; mkAC BC_GE (SOff 557 0) (SLit 0); mkAC BC_EQ (SOff 564 0) (SLit 1)] HC HdE Hregs Hflag HOC HOT R24 HAr2
      (conj CSEQ (conj CA (conj HCR I)))) as HS0.
    fold X Ev in HS0.
    pose proof (st_ok_pi_submem _ _ _ o5_rs HS0 o5_sub ltac:(vm_compute; reflexivity)) as HS1. clear HS0.
    paj_run_shc RUNP RUNC HS1 HJ.
    { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
    rewrite (pa_sigma_role_of (PI := PI)) in HS1.
    lazymatch type of HS1 with
    | st_ok _ ?Ex (setpc ?ssx _) ?msx => assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_both3_role_of) msx) by exact HS1
    | st_ok _ ?Ex (mkSS _ ?r ?m ?rv ?f) ?msx => assert (HSpi : st_ok_pi SEGS VAL Ex (mkSS AF_both3_role_of r m rv f) msx) by exact HS1
    end.
    clear HS1.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
    pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MEQ0.
    assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
    { intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r HSpi), (A1 r).
      cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
    assert (R1x : getr (ms_regs ms) 1 = w64 (BASE + OB_RO_RET)).
    { rewrite (st_ok_pi_restrict_reg _ _ _ ms 1%bv HSpi).
      lazymatch goal with |- sv_denot _ (sr_get ?sr ?r) = _ =>
        let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
      exact (codeptr_val Ev OB_RO_RET HEI). }
    assert (R10x : getr (ms_regs ms) 10 = w64 (d_obj cx OT)).
    { rewrite (st_ok_pi_restrict_reg _ _ _ ms 10%bv HSpi).
      lazymatch goal with |- sv_denot _ (sr_get ?sr ?r) = _ =>
        let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
      rewrite DF. unfold d_obj, dobj_off. reflexivity. }
    assert (R11x : getr (ms_regs ms) 11 = w64 (d_obj cx OS)).
    { rewrite (st_ok_pi_restrict_reg _ _ _ ms 11%bv HSpi).
      lazymatch goal with |- sv_denot _ (sr_get ?sr ?r) = _ =>
        let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
      rewrite DF. unfold d_obj, dobj_off. reflexivity. }
    apply SRr_ret. left.
    apply (o5_c7_of cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W _).
    apply (o5_land fq cx h i n now op nb fr len Sg T' kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs AF_both3_role_of _
      HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HSpi eq_refl eq_refl HOC MEQ0
      ltac:(intros r Hr; apply RG; cbv [In] in Hr |- *; tauto)).
    unfold o5_X7, ob_rT.
    split; [exact (o5_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) (oy_mrestrict_ext (w_H W) mem3 (ms_mem ms) MEQ0) HOT)|].
    split; [split; [rewrite (RG 25%bv ltac:(cbv; tauto)); exact R25 | rewrite (RG 26%bv ltac:(cbv; tauto)); exact R26]|].
    split; [rewrite (RG 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [exact Hpos|]. split; [exact Hr1|].
    split; [exact R1x|]. split; [exact R10x | exact R11x].
  + assert (HCR : acond_ok Ev (mkAC BC_NE (SOff 564 0) (SLit 1))).
    { unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, U564, U_lit by lia.
      apply negb_true_iff, Z.eqb_neq. unfold u64. intros Hm. apply Hr1.
      destruct (Z.ltb_spec (role_of_e T ai) 0) as [Hl|Hl].
      - exfalso. rewrite <- (Z.mod_unique (role_of_e T ai) (2 ^ 64) (-1) (role_of_e T ai + 2 ^ 64)) in Hm by lia. lia.
      - rewrite Z.mod_small in Hm by lia. exact Hm. }
    pose proof (o5_seat fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E
      [o5_seqc; mkAC BC_GE (SOff 557 0) (SLit 0); mkAC BC_NE (SOff 564 0) (SLit 1)] HC HdE Hregs Hflag HOC HOT R24 HAr2
      (conj CSEQ (conj CA (conj HCR I)))) as HS0.
    fold X Ev in HS0.
    pose proof (st_ok_pi_submem _ _ _ o5_rs HS0 o5_sub ltac:(vm_compute; reflexivity)) as HS1. clear HS0.
    paj_run_to_sh RUNTO HS1 HJ OB_C9.
    { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
    cbn [ms_mem mkst] in HF.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
    pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MEQ0.
    assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
    { intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r HS1), (A1 r).
      cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
    apply SRr_ret. right. left.
    apply (o5_c9_of cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W _).
    apply (o5_land fq cx h i n now op nb fr len Sg T' kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs OB_C9 _
      HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HS1 eq_refl eq_refl HOC MEQ0
      ltac:(intros r Hr; apply RG; cbv [In] in Hr |- *; tauto)).
    unfold o5_X9. split; [|split; [|split]].
    * exact (o5_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) (oy_mrestrict_ext (w_H W) mem3 (ms_mem ms) MEQ0) HOT).
    * rewrite (RG 25%bv ltac:(cbv; tauto)). exact R25.
    * rewrite (RG 23%bv ltac:(cbv; tauto)). exact R23.
    * exact Hpos.
Qed.

End h.
End f.
End d.

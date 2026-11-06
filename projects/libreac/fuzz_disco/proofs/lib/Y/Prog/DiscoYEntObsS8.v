(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 721 of its 760 lines of code are new or changed and 506 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Bytes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition OB_BCR : Z := 0x1b94.

Lemma o5_ble_byte : forall (bs : list byte) n k, length bs = n -> (k < n)%nat ->
  Z.shiftr (bytes_le_to_Z bs mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof.
intros bs n k <-. revert k. induction bs as [|b bs IH]; intros k Hk; [cbn in Hk; lia|].
rewrite (Z.mod_small (bytes_le_to_Z (b :: bs))) by exact (disco_table.ble_range (b :: bs)).
pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (disco_table.ble_range bs) as Hr.
assert (Ec : bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256)
  by (rewrite !Bytes.bytes_le_to_Z_le_val; cbn [map Bytes.le_val]; lia).
rewrite Ec. destruct k as [|k].
- cbn [nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth length] in Hk |- *. rewrite Z.shiftr_div_pow2 by lia.
  replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia.
  rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
  change (2 ^ 8) with 256. rewrite Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b) 256) by lia. rewrite Z.add_0_l.
  specialize (IH k ltac:(lia)). rewrite (Z.mod_small (bytes_le_to_Z bs)) in IH by exact Hr.
  rewrite Z.shiftr_div_pow2 in IH by lia. exact IH.
Qed.
Lemma o5_obs_len : forall regs, length (obs_vals regs) = 32%nat.
Proof. intros regs. unfold obs_vals. rewrite length_map, length_seq. reflexivity. Qed.
Lemma o5_sub_len : forall (L : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) -> length (sub L k n) = n.
Proof. intros L k n Hk Hn. unfold sub. rewrite length_firstn, length_skipn. lia. Qed.
Lemma o5_u_range : forall (L : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  0 <= u_at L k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros L k n Hk Hn. unfold u_at. pose proof (disco_table.ble_range (sub L k n)) as H.
rewrite (o5_sub_len L k n Hk Hn) in H. exact H.
Qed.
Lemma o5_nth_sub : forall (L : list byte) k n j d, 0 <= k -> (j < n)%nat -> nth j (sub L k n) d = nth (Z.to_nat k + j) L d.
Proof.
intros L k n j d Hk Hj. unfold sub. rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj).
rewrite nth_skipn. reflexivity.
Qed.
Lemma o5_u_le : forall z (n : nat), 0 <= z < 2 ^ (8 * Z.of_nat n) -> bytes_le_to_Z (Z_to_le_bytes n z) = z.
Proof. intros z n Hz. rewrite bytes_le_to_Z_of_le_bytes by lia. apply Z.mod_small. exact Hz. Qed.
Lemma o5_mod_nz : forall x, x <> 0 -> - 2 ^ 31 <= x < 2 ^ 31 -> x mod 2 ^ 64 <> 0 mod 2 ^ 64.
Proof. intros x Hx Hr. rewrite Z.mod_0_l by lia. destruct (Z_lt_le_dec x 0); [rewrite Z.mod_eq by lia | rewrite Z.mod_small by lia]; lia. Qed.
Lemma o5_pres : forall a b (r : bv 5), aregs_preserved a b -> acallee_saved (bv_unsigned r) -> getr b r = getr a r.
Proof. intros a b r H Hr. pose proof (H (bv_unsigned r) Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Lemma o5_mod32_8 : forall a, a mod 32 = 0 -> a mod 8 = 0.
Proof.
intros a H. pose proof (Z.div_mod a 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D. replace (32 * (a / 32)) with (4 * (a / 32) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma o5_w64_mod : forall x, Z_to_bv 64 x = Z_to_bv 64 (x mod 2 ^ 64).
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. Qed.

Ltac o5_rr H := lazymatch type of H with _ = sv_denot _ (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v in H end.
Ltac o5_upd :=
  lazymatch goal with HF : frame_of _ _ ?m1 ?m2, MP : forall x, ?m1 x = ?m0 x |- _ =>
    let MP2 := fresh "MP" in
    assert (MP2 : forall x, m2 x = m0 x)
      by (intros x; rewrite (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity) x); apply MP);
    clear MP; rename MP2 into MP end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac o5_cs := unfold acallee_saved;
  repeat match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
Ltac o5_nt := repeat match goal with |- context [N.to_nat ?x] =>
  let y := eval vm_compute in (N.to_nat x) in change (N.to_nat x) with y end.
Ltac o5_awr := cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac o5_run RUN :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_tok RUN HS HJ SHOK OBspan; [o5_awr | o5_upd] end.
Ltac o5_runto RUNTO stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK OBspan stop; [o5_awr | o5_upd] end.

Section u.
Variable E : env.
Lemma o5_sv_atom : forall q v, ew E q = Z_to_bv 64 v -> sv_denot E (SOff q 0) = Z_to_bv 64 v.
Proof. intros q v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma o5_ew_of_sv : forall q w, sv_denot E (SOff q 0) = w -> ew E q = w.
Proof. intros q w H. cbn [sv_denot] in H. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma o5_sv_sext32 : forall q u, ew E q = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff q 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros q u H Hu. rewrite denot_lit_U, U_SExt, U_SOff, H. rewrite (Z_to_bv_unsigned 64 u).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small u) by lia. rewrite Z.add_0_r.
rewrite (zcanon_id u) by (unfold M64; lia). change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia.
rewrite zcanon_wrap. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. lia.
Qed.
Lemma o5_br_ne_false : forall a b, sv_denot E a = sv_denot E b -> branch_taken BC_NE (sv_denot E a) (sv_denot E b) = false.
Proof. intros a b H. rewrite branch_ne_U. unfold U. rewrite H, Z.eqb_refl. reflexivity. Qed.
Lemma o5_br_eq_false : forall a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  x mod 2 ^ 64 <> y mod 2 ^ 64 -> branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = false.
Proof.
intros a b x y Ha Hb Hxy. rewrite branch_eq_U. unfold U. rewrite Ha, Hb, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.eqb_neq. exact Hxy.
Qed.
Lemma o5_br_ltu_false : forall a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= y <= x -> x < 2 ^ 64 -> branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = false.
Proof.
intros a b x y Ha Hb H1 H2. rewrite branch_ltu_U. unfold U. rewrite Ha, Hb, !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite !Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma o5_br_lt7 : forall q v, ew E q = Z_to_bv 64 v -> 0 <= v <= 8 ->
  branch_taken BC_LT (sv_denot E (SLit 7)) (sv_denot E (SOff q 0)) = (7 <? v).
Proof.
intros q v H Hv. rewrite (o5_sv_atom q v H).
assert (v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7 \/ v = 8) as Hc by lia.
repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]). subst v. vm_compute. reflexivity.
Qed.
Lemma o5_sv_aluw1 : forall q v, ew E q = Z_to_bv 64 v -> 0 <= v < 8 ->
  sv_denot E (SAluw ALU_ADD (SOff q 0) (SLit 1)) = Z_to_bv 64 (v + 1).
Proof.
intros q v H Hv. cbn [sv_denot]. rewrite H.
assert (v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) as Hc by lia.
repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]). subst v. vm_compute. reflexivity.
Qed.
Lemma o5_sv_mul48 : forall q v, ew E q = Z_to_bv 64 v -> 0 <= v < 8 ->
  sv_denot E (SMd M_MUL (SOff q 0) (SLit 48)) = Z_to_bv 64 (48 * v).
Proof.
intros q v H Hv. cbn [sv_denot]. rewrite H.
assert (v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) as Hc by lia.
repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]). subst v. vm_compute. reflexivity.
Qed.
Lemma o5_sv_addr : forall f q c v fb, ew E f = Z_to_bv 64 fb -> ew E q = Z_to_bv 64 v ->
  sv_denot E (SAlu ALU_ADD (SOff f c) (SMd M_MUL (SOff q 0) (SLit 48))) = Z_to_bv 64 (fb + c + 48 * v).
Proof.
intros f q c v fb Hf Hv. rewrite denot_lit_U. rewrite U_SAlu, U_SMd, !U_SOff, U_SLit, Hf, Hv.
cbn [zalu_raw zmd_raw]. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold zcanon, bv_wrap. change (bv_modulus 64) with 18446744073709551616. rewrite Z.add_0_r.
change (48 mod 18446744073709551616) with 48.
rewrite (Zmod_mod v), Z.mul_mod_idemp_l, Z.add_mod_idemp_r, Z.add_mod_idemp_l, Zmod_mod by discriminate.
change (48 mod M64) with 48. rewrite <- Z.add_assoc, Z.add_mod_idemp_l by discriminate. f_equal. lia.
Qed.
End u.

Definition o5_fcs (e : Z) : list YP09.chunk :=
  [YP09.mkChunk (e + 8) (CVal 4 (SOff 563 0)); YP09.mkChunk (e + 12) (CVal 1 (SOff 564 0));
   YP09.mkChunk (e + 13) (CVal 1 (SOff 565 0)); YP09.mkChunk (e + 14) (CVal 1 (SOff 566 0));
   YP09.mkChunk (e + 15) (CVal 1 (SOff 567 0)); YP09.mkChunk (e + 16) (CVal 1 (SOff 568 0));
   YP09.mkChunk (e + 20) (CVal 4 (SOff 569 0)); YP09.mkChunk (e + 24) (CVal 4 (SOff 570 0));
   YP09.mkChunk (e + 32) (CVal 8 (SOff 571 0)); YP09.mkChunk (e + 40) (CVal 8 (SOff 571 0));
   YP09.mkChunk 3000 (CVal 4 (SOff 563 0)); YP09.mkChunk 3004 (CVal 1 (SOff 564 0));
   YP09.mkChunk 3005 (CVal 1 (SOff 565 0)); YP09.mkChunk 3006 (CVal 1 (SOff 566 0));
   YP09.mkChunk 3007 (CVal 1 (SOff 567 0)); YP09.mkChunk 3008 (CVal 1 (SOff 568 0));
   YP09.mkChunk 3012 (CVal 4 (SOff 569 0))].
Definition o5_acs : list YP09.chunk :=
  [YP09.mkChunk 320 (CVal 8 (SOff 571 0)); YP09.mkChunk 360 (CVal 8 (SOff 570 0))].
Definition o5_acs1 : list YP09.chunk := [YP09.mkChunk 280 (CVal 8 (SOff 565 0))].
Definition o5_fcs1 : list YP09.chunk :=
  [YP09.mkChunk 2544 (CVal 4 (SOff 563 0)); YP09.mkChunk 2548 (CVal 4 (SOff 564 0))].
Definition o5_SH : list shent := [mkSHE AT_F 2160 2560].

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

Lemma o5_val_mem_sub : forall (m : word -> option byte) p (L : list byte) k (n : nat),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  val_mem SEGS m (p + k) n (u_at L k n).
Proof.
intros m p L k n HG Hk Hn j Hj.
unfold u_at, YO0f.le_byte. rewrite (o5_ble_byte (sub L k n) n j (o5_sub_len L k n Hk Hn) Hj).
rewrite (o5_nth_sub L k n j _ Hk Hj).
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (YI00.garr8_mbyte SEGS m p _ (Z.to_nat k + j) HG) by (rewrite length_map; lia).
f_equal. rewrite (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0)). rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma o5_aview_garr8 : forall H (m : word -> option byte) p (L : list byte) j,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L) -> (j < length L)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some (bv_unsigned (nth j L (Z_to_bv 8 0))).
Proof.
intros H m p L j HG Hj. unfold aview.
rewrite (YI00.garr8_mbyte SEGS (mrestrict H m) p _ j HG) by (rewrite length_map; exact Hj).
cbn [option_map]. f_equal. rewrite (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0)).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma o5_aview_nn : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a Hp. destruct (oy_aview_present H m a Hp) as [b Hb]. rewrite Hb. discriminate. Qed.
Lemma o5_ew_app : forall cx E regs xs k, (k < 563)%nat ->
  ew (d_env cx E (obs_vals regs ++ xs)) k = ew (d_env cx E (obs_vals regs)) k.
Proof.
intros cx E regs xs k Hk. unfold d_env, havoc. cbn [ew].
destruct (k <? AT_FL)%nat eqn:Hl; [reflexivity|]. apply Nat.ltb_ge in Hl. unfold AT_FL in *.
rewrite app_comm_cons. rewrite app_nth1; [reflexivity|]. cbn [length]. rewrite o5_obs_len. lia.
Qed.
Lemma o5_ew_x : forall cx E regs xs k d, (563 <= k)%nat -> (k - 563 < length xs)%nat ->
  ew (d_env cx E (obs_vals regs ++ xs)) k = nth (k - 563) xs d.
Proof.
intros cx E regs xs k d Hk Hj. unfold d_env. replace k with (530 + (33 + (k - 563)))%nat at 1 by lia.
rewrite (ew_havoc_new E 530 _ (33 + (k - 563)) d) by (cbn [length]; rewrite length_app, o5_obs_len; lia).
replace (33 + (k - 563))%nat with (S (32 + (k - 563))) by lia. cbn [nth].
rewrite app_nth2 by (rewrite o5_obs_len; lia). rewrite o5_obs_len. f_equal. lia.
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
Hypothesis BCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (DiscoYEntObsCuts.oc B).
#[local] Notation ob_c10 := (DiscoYEntObsCuts.ob_c10 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation r27 := (r27_in B MT XM_LIB RLO RHI tfib_K).

Lemma o5_regs_ok : forall cx E regs xs, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs ++ xs)) obs_sr regs.
Proof.
intros cx E regs xs HE HL HA.
pose proof (regs_ok_obs B cx E regs HE HL HA) as R.
apply regs_ok_by_cases. intros r Hr. rewrite (R r).
cbv [all_regs In] in Hr.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ];
  (match goal with |- sv_denot _ (sr_get ?sr ?r) = _ =>
     let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end);
  first [ reflexivity | cbn [sv_denot]; rewrite o5_ew_app by lia; reflexivity ].
Qed.

Lemma o5_body_n : forall cx h n n' xb shf ly S W m, d_body B cx h n xb shf ly S W m ->
  0 <= n' <= Z.max 0 (c_n cx - 7) -> d_body B cx h n' xb shf ly S W m.
Proof.
intros cx h n n' xb shf ly S W m (T & G & Lk & H & Hf & Hs & Ho & Hb & (_ & Hg & Hoi) & Hrest) Hn.
exists T, G, Lk, H. exact (conj Hf (conj Hs (conj Ho (conj Hb (conj (conj Hn (conj Hg Hoi)) Hrest))))).
Qed.

Lemma o5_land : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T ly3 S3 (W : world SEGS) mem0 regs md k acc
    E vals ss ms,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss (restrict (w_H W) ms) ->
  ss_pc ss = R27_OFF -> ss_resv ss = None ->
  (forall x, ms_mem ms x = mem0 x) ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W mem0 ->
  d_rL B cx (ms_regs ms) ->
  r27 cx h i (nb - len) now nb fr len W (mkCfg ms md).
Proof.
intros fq cx h i n now op nb fr len Sg T ly3 S3 W mem0 regs md k acc E vals ss ms
  HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HS Hpc Hrv MP HOC HrL'.
pose proof (st_ok_pi_restrict_mkst (w_H W) _ ss ms HS Hrv) as Hms. rewrite Hpc in Hms.
pose proof (oy_oc_pt B cx h i n now op nb fr len Sg T regs (ms_regs ms) ly3 S3 W mem0 (ms_mem ms) BRT MP HrL' HOC)
  as HOC2.
pose proof HOC2 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
unfold r27_in, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md, k, acc.
split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [lia|]. split; [exact Hnow|]. split; [exact HrL|]. split; [exact I|].
split; [exact (conj Hfrm (conj HREC (conj Hlen eq_refl)))|].
split; [exact Hsp0|].
exact (o5_body_n cx h n (nb - len) _ _ _ _ _ _ Hbody ltac:(lia)).
Qed.

Definition o5_ret (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z)
  : world SEGS -> config -> Prop :=
  DAT cx OB_BCR kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ow,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\
    length T = 400%nat /\ 0 <= n_of T < 8 /\ (T', 1) = reac_disco_table_observe_c.observe_new T Sg ow now /\
    (ow = 0 \/ ow = 1) /\ val_mem SEGS (rd W3 mem3) (d_A cx + 360) 8 ow /\
    getr regs 23 = w64 (d_obj cx OT + 48 * n_of T) /\ getr regs 10 = w64 0).

Lemma o5_h1 : forall cx h i n now op nb fr len Sg W c,
  ob_c10 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (fun W' c' => r27 cx h i (nb - len) now nb fr len W' c' \/
    o5_ret cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W' c').
Proof.
intros cx h i n now op nb fr len Sg W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HobT & H25 & H23 & Hai).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan).
pose proof Hframe as (E & HdE & Hregs & Hflag & V184 & V120 & V136 & V376 & V280 & V232 & V264).
destruct HobT as (HTl0 & HTok0 & HFR & How & Hsp22 & H360 & HOM).
pose proof HTok0 as (HT1 & _). unfold tbl_T1 in HT1.
pose proof (slot_observe.unknown_arm T Sg ow now T' ret ai HFR Hai HOM) as ARM.
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (_ & _ & _ & HF0 & HFc & HFia & HFo & HF32 & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as ACV.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (HF8 : d_FB cx mod 8 = 0) by (apply o5_mod32_8; exact HF32).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
pose proof (o5_u_range T' 384 4 ltac:(lia) ltac:(rewrite HTl; cbn; lia)) as Hu1.
pose proof (o5_u_range T' 388 4 ltac:(lia) ltac:(rewrite HTl; cbn; lia)) as Hu2.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hu1, Hu2.
set (xs1 := [w64 (u_at T' 384 4); w64 (u_at T' 388 4); w64 (dnot (d_obj cx OT))]).
assert (FC : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ xs1)) (rd W mem3) (d_FB cx)) o5_fcs1).
{ unfold o5_fcs1. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ (u_at T' 384 4)); [ | exact Hu1 | lia | ].
    + apply o5_sv_atom. rewrite (o5_ew_x cx E regs xs1 563 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia). reflexivity.
    + replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj, dobj_off; lia).
      exact (o5_val_mem_sub _ _ T' 384 4 HT ltac:(lia) ltac:(rewrite HTl; cbn; lia)).
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ (u_at T' 388 4)); [ | exact Hu2 | lia | ].
    + apply o5_sv_atom. rewrite (o5_ew_x cx E regs xs1 564 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia). reflexivity.
    + replace (d_FB cx + 2548) with (d_obj cx OT + 388) by (unfold d_obj, dobj_off; lia).
      exact (o5_val_mem_sub _ _ T' 388 4 HT ltac:(lia) ltac:(rewrite HTl; cbn; lia)). }
assert (AC : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ xs1)) (rd W mem3) (d_A cx)) o5_acs1).
{ unfold o5_acs1. apply Forall_cons; [|apply Forall_nil].
  apply (YI04.chunk_ok_val SEGS _ _ _ _ 8 _ (dnot (d_obj cx OT)));
    [ | unfold dnot, d_obj, dobj_off; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact V280].
  apply o5_sv_atom. rewrite (o5_ew_x cx E regs xs1 565 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia). reflexivity. }
pose proof (o5_regs_ok cx E regs xs1 HdE HrL HAr2) as RO1.
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_C10 obs_sr (obs_vals regs ++ xs1)
  o5_acs1 o5_fcs1 [] (d_facts [] []) HctxD HdE Hregs Hflag RO1
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs ++ xs1) [] [] HctxD HdE I I)
  AC FC (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
assert (EW516 : ew (d_env cx E (obs_vals regs ++ xs1)) 516 = Z_to_bv 64 (d_FB cx)).
{ rewrite oy_d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & _ & EF & _). exact EF. }
assert (EW60 : ew (d_env cx E (obs_vals regs ++ xs1)) 60 = Z_to_bv 64 (d_A cx)).
{ rewrite oy_d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & EA & _). exact EA. }
assert (SV556 : sv_denot (d_env cx E (obs_vals regs ++ xs1)) (SOff 556 0) = Z_to_bv 64 (n_of T)).
{ pose proof (RO1 25%bv) as R. o5_rr R. rewrite H25 in R. symmetry. exact R. }
pose proof (o5_ew_of_sv _ _ _ SV556) as EW556.
assert (SV554 : sv_denot (d_env cx E (obs_vals regs ++ xs1)) (SOff 554 0) = Z_to_bv 64 ret).
{ pose proof (RO1 23%bv) as R. o5_rr R. rewrite H23 in R. symmetry. exact R. }
assert (EW563 : ew (d_env cx E (obs_vals regs ++ xs1)) 563 = Z_to_bv 64 (u_at T' 384 4))
  by (rewrite (o5_ew_x cx E regs xs1 563 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia); reflexivity).
assert (EW564 : ew (d_env cx E (obs_vals regs ++ xs1)) 564 = Z_to_bv 64 (u_at T' 388 4))
  by (rewrite (o5_ew_x cx E regs xs1 564 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia); reflexivity).
assert (EW565 : ew (d_env cx E (obs_vals regs ++ xs1)) 565 = Z_to_bv 64 (dnot (d_obj cx OT)))
  by (rewrite (o5_ew_x cx E regs xs1 565 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia); reflexivity).
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ xs1))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia).
  exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs ++ xs1)) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) (PI := PI) B LAWS).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (MP : forall x, mem3 x = mem3 x) by reflexivity.
unfold cfg_at. change (w64 (BASE + OB_C10)) with (Z_to_bv 64 (BASE + OB_C10)).
o5_run RUN.
psrr_branch_tok RUN BR HS SHOK OBspan.
- rewrite (o5_br_lt7 _ 556%nat (n_of T) EW556 ltac:(lia)) in Hc. apply Z.ltb_lt in Hc. rename Hc into HN7.
  destruct ARM as [(HN8 & EF) | (HN8 & _)]; [|lia].
  destruct (slot_observe.full_facts T T' ret HTl0 EF) as (_ & Hret0 & E384 & E388 & _ & _).
  assert (Hn8 : bv_swrap 32 (u_at T' 384 4) = n_of T) by exact (slot_observe.n_of_sub T T' E384).
  assert (Hov : bv_swrap 32 (u_at T' 388 4) <> 0).
  { change (bv_swrap 32 (u_at T' 388 4)) with (ov_of T'). unfold ov_of, s32_at, u_at. rewrite E388.
    destruct (Z.eqb_spec (ov_of T) 0) as [_|Hz]; [intros Hx; vm_compute in Hx; discriminate Hx | exact Hz]. }
  o5_run RUN.
  psrr_branch_tok RUN BR HS SHOK OBspan.
  + exfalso. rewrite (o5_br_ne_false _ (SOff 554 0) (SLit 0)) in Hc; [discriminate Hc|]. rewrite SV554, Hret0. reflexivity.
  + clear Hc. o5_run RUN.
    psrr_branch_tok RUN BR HS SHOK OBspan.
    * exfalso. rewrite (o5_br_ne_false _ (SExt true 32 (SOff 563 0)) (SOff 556 0)) in Hc; [discriminate Hc|].
      rewrite (o5_sv_sext32 _ 563 _ EW563 Hu1), SV556, Hn8. reflexivity.
    * clear Hc. o5_run RUN.
      psrr_branch_tok RUN BR HS SHOK OBspan.
      -- exfalso. rewrite (o5_br_eq_false _ (SExt true 32 (SOff 564 0)) (SLit 0) (bv_swrap 32 (u_at T' 388 4)) 0) in Hc;
           [discriminate Hc | exact (o5_sv_sext32 _ 564 _ EW564 Hu2) | reflexivity |
            apply o5_mod_nz; [exact Hov | apply swrap32_range]].
      -- clear Hc. o5_runto RUNTO R27_OFF.
         repeat rewrite wvb_collapse in HJ.
         apply SRr_ret. left.
         lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?ms) |- _ =>
           assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
             getr (ms_regs ms) r = getr regs r)
             by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), (RO1 r); cbv [In] in Hr;
                 repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
           apply (o5_land fq cx h i n now op nb fr len Sg T' ly3 S3 W mem3 regs _ k acc E _ ss ms
             HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) MP HOC)
         end.
         destruct HrL as (Hsp & Hgp & Htp & R8 & R9 & R19 & R18 & R20 & R27). unfold d_rL, spZ in *.
         rewrite (RG 2%bv), (RG 3%bv), (RG 4%bv), (RG 8%bv), (RG 9%bv), (RG 18%bv), (RG 19%bv), (RG 20%bv), (RG 27%bv)
           by (cbv; tauto).
         repeat split; assumption.
- rewrite (o5_br_lt7 _ 556%nat (n_of T) EW556 ltac:(lia)) in Hc. apply Z.ltb_ge in Hc. rename Hc into HN7.
  destruct ARM as [(HN8 & _) | (HN8 & EN)]; [lia|].
  destruct (slot_observe.new_facts T Sg ow now T' ret HTl0 HSgl ltac:(lia) EN) as (_ & Hret1 & E384 & _ & NF).
  subst ret.
  assert (Hu1v : u_at T' 384 4 = n_of T + 1).
  { unfold u_at. rewrite E384. apply o5_u_le. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). lia. }
  o5_run RUN.
  psrr_branch_tok RUN BR HS SHOK OBspan.
  + exfalso. rewrite (o5_br_ltu_false _ (SLit 8) (SOff 556 0) 8 (n_of T)) in Hc;
      [discriminate Hc | reflexivity | exact SV556 | lia | lia].
  + clear Hc. o5_run RUN.
    psrr_branch_tok RUN BR HS SHOK OBspan.
    * exfalso.
      rewrite (o5_br_ltu_false _ (SOff 565 0) (SMd M_MUL (SOff 556 0) (SLit 48)) (dnot (d_obj cx OT)) (48 * n_of T)) in Hc;
        [discriminate Hc | exact (o5_sv_atom _ 565 _ EW565) | exact (o5_sv_mul48 _ 556 _ EW556 ltac:(lia)) |
         unfold dnot, d_obj, dobj_off; lia | unfold dnot, d_obj, dobj_off; lia].
    * clear Hc. o5_run RUN.
      psrr_branch_tok RUN BR HS SHOK OBspan.
      -- exfalso. rewrite (o5_br_ne_false _ (SOff 554 0) (SLit 1)) in Hc; [discriminate Hc|]. rewrite SV554. reflexivity.
      -- clear Hc. o5_run RUN.
         psrr_branch_tok RUN BR HS SHOK OBspan.
         ++ exfalso. rewrite (o5_br_ne_false _ (SExt true 32 (SOff 563 0)) (SAluw ALU_ADD (SOff 556 0) (SLit 1))) in Hc;
              [discriminate Hc|].
            rewrite (o5_sv_sext32 _ 563 _ EW563 Hu1), (o5_sv_aluw1 _ 556 (n_of T) EW556 ltac:(lia)), Hu1v.
            rewrite swrap32_id by lia. reflexivity.
         ++ clear Hc. o5_run RUN.
            repeat rewrite wvb_collapse in HJ.
            lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msc end.
            lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ msc) |- _ =>
              pose proof (st_ok_restrict_mkst SEGS (w_H W) Ex ssx msc HS eq_refl) as Hms;
              pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 10%bv HS) as Ra0;
              pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 11%bv HS) as Ra1;
              pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 12%bv HS) as Ra2;
              pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 1%bv HS) as Rra;
              pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 2%bv HS) as Rsp;
              pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 23%bv HS) as R23c;
              assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
                getr (ms_regs msc) r = getr regs r)
                by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc r HS), (RO1 r); cbv [In] in Hr;
                    repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr)
            end.
            assert (MPv : forall a, aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) mem3 a)
              by (intros a; unfold aview, mbyte, mrestrict; rewrite MP; reflexivity).
            cbn [ss_pc setpc] in Hms.
            o5_rr Ra0. o5_rr Ra1. o5_rr Ra2. o5_rr Rra. o5_rr Rsp. o5_rr R23c.
            rewrite (o5_sv_addr _ 516 556 2160 (n_of T) (d_FB cx) EW516 EW556) in Ra0, R23c.
            cbn [sv_denot] in Ra1. rewrite EW516, oy_w64_add_w in Ra1.
            change (SOff 240 7060) with (SOff A_TEXT 7060) in Rra. rewrite (codeptr_val _ 7060 HEI) in Rra.
            rewrite (o5_sv_atom _ 60 (d_A cx) EW60) in Rsp.
            assert (SPZ : spZ (ms_regs msc) = d_A cx)
              by (unfold spZ; rewrite Rsp, Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
            pose proof HrL as (Hspr & Hgpr & Htpr & R8r & R9r & R19r & R18r & R20r & R27r).
            assert (HrLc : d_rL B cx (ms_regs msc)).
            { unfold d_rL. split; [exact SPZ|].
              rewrite (RG 3%bv), (RG 4%bv), (RG 8%bv), (RG 9%bv), (RG 18%bv), (RG 19%bv), (RG 20%bv), (RG 27%bv)
                by (cbv; tauto).
              repeat split; assumption. }
            pose proof (conj Hbase (conj HJ Hfrs)) as HctxDc.
            pose proof (oy_oc_pt B cx h i n now op nb fr len Sg T' regs (ms_regs msc) ly3 S3 W mem3 (ms_mem msc)
              BRT MP HrLc HOC) as HOCc.
            rewrite Hms.
            eapply SRr_bind.
            { eapply (aj_bcmp_at (fx := fq) SEGS B LAWS pa_segs_low (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W
                (ms_regs msc) (ms_mem msc) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
                [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k (d_obj cx OT + 48 * n_of T) (d_obj cx OS) 6 (d_A cx - d_S cx)
                (Z_to_bv 64 (BASE + 7060)) HJ).
              - rewrite Ra0. unfold w64, d_obj, dobj_off. f_equal; lia.
              - rewrite Ra1. unfold w64, d_obj, dobj_off. reflexivity.
              - rewrite Ra2. reflexivity.
              - lia.
              - unfold d_obj, dobj_off; lia.
              - unfold d_obj, dobj_off; lia.
              - unfold d_obj, dobj_off; lia.
              - unfold d_obj, dobj_off; lia.
              - rewrite SPZ. lia.
              - lia.
              - lia.
              - unfold ESTACK, LLVMF_STK; lia.
              - destruct HrL as (_ & Hgp & _). rewrite (RG 3%bv) by (cbv; tauto). exact Hgp.
              - destruct HrL as (_ & _ & Htp & _). rewrite (RG 4%bv) by (cbv; tauto). exact Htp.
              - exact Rra.
              - apply ret_ok_codeptr_v; [lia | reflexivity].
              - intros a Ha. rewrite MPv, SPZ. unfold d_obj, dobj_off in Ha. split.
                + apply o5_aview_nn. apply HFpres. lia.
                + unfold ESTACK, LLVMF_STK in *. lia.
              - intros a Ha. rewrite MPv, SPZ. unfold d_obj, dobj_off in Ha. split.
                + apply o5_aview_nn. apply HFpres. lia.
                + unfold ESTACK, LLVMF_STK in *. lia.
              - intros a Ha. unfold ESTACK, LLVMF_STK, d_obj, dobj_off in *. lia.
              - intros a Ha. unfold ESTACK, LLVMF_STK, d_obj, dobj_off in *. lia.
              - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, d_obj, dobj_off.
                lia.
              - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, d_obj, dobj_off.
                lia.
              - assert (RA1 : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (d_obj cx OT + 48 * n_of T) 6).
                { replace (d_obj cx OT + 48 * n_of T) with (d_FB cx + (2160 + 48 * n_of T))
                    by (unfold d_obj, dobj_off; lia).
                  apply (oy_ra_frame cx dsh_rec W mem3 (2160 + 48 * n_of T) 6 Hshadow HF8 ltac:(lia) ltac:(lia)
                    ltac:(lia)). intros kk Hkk. apply oy_dsh_rec_t. lia. }
                intros x Hx. rewrite MPv. exact (RA1 x Hx).
              - assert (HV1 : shadow_hull_vis (aview SEGS (w_H W) mem3) (d_obj cx OT + 48 * n_of T) 6).
                { replace (d_obj cx OT + 48 * n_of T) with (d_FB cx + (2160 + 48 * n_of T))
                    by (unfold d_obj, dobj_off; lia).
                  apply (oy_hull_frame cx dsh_rec W mem3 (2160 + 48 * n_of T) 6 Hshadow HF8 ltac:(lia) ltac:(lia)
                    ltac:(lia)). }
                intros _ s Hs. rewrite MPv. exact (HV1 s Hs).
              - assert (RA2 : range_addressable (aview SEGS (w_H W) mem3) SHADOW_OFF (d_obj cx OS) 6).
                { replace (d_obj cx OS) with (d_FB cx + 2992) by (unfold d_obj, dobj_off; lia).
                  apply (oy_ra_frame cx dsh_rec W mem3 2992 6 Hshadow HF8 ltac:(lia) ltac:(lia) ltac:(lia)).
                  intros kk Hkk. apply oy_dsh_rec_s. lia. }
                intros x Hx. rewrite MPv. exact (RA2 x Hx).
              - assert (HV2 : shadow_hull_vis (aview SEGS (w_H W) mem3) (d_obj cx OS) 6).
                { replace (d_obj cx OS) with (d_FB cx + 2992) by (unfold d_obj, dobj_off; lia).
                  apply (oy_hull_frame cx dsh_rec W mem3 2992 6 Hshadow HF8 ltac:(lia) ltac:(lia) ltac:(lia)). }
                intros _ s Hs. rewrite MPv. exact (HV2 s Hs). }
            cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres).
            assert (KPc : d_kept (fun a => d_A cx - 8192 <= a < d_A cx) W (ms_mem msc) W mem2).
            { intros a Ha Hna. apply (Hfr a Ha). unfold ESTACK; lia. }
            assert (KP : d_kept (fun a => d_A cx - 8192 <= a < d_A cx) W mem3 W mem2).
            { intros a Ha Hna. rewrite (Hfr a Ha) by (unfold ESTACK; lia). apply MPv. }
            assert (HctxD2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem2 md2 k)
              by (split; [exact Hbase | split; [exact HJ2 | exact Hfrs]]).
            assert (EM : sub T' (48 * n_of T) 6 = sub Sg 0 6).
            { replace (48 * n_of T) with (48 * n_of T + 0) by lia. rewrite (NF 0 6%nat) by (cbn; lia).
              destruct (slot_observe.new_fields Sg ow now HSgl) as (F0 & _). exact F0. }
            assert (Hv0 : v = w64 0).
            { apply (proj2 Hcmp). intros j Hj. rewrite !MPv.
              replace (d_obj cx OT + 48 * n_of T + j) with (d_obj cx OT + Z.of_nat (Z.to_nat (48 * n_of T + j))) by lia.
              replace (d_obj cx OS + j) with (d_obj cx OS + Z.of_nat (Z.to_nat j)) by lia.
              rewrite (o5_aview_garr8 _ _ _ T' _ HT) by (rewrite HTl; lia).
              rewrite (o5_aview_garr8 _ _ _ Sg _ HSg) by (rewrite HSgl; lia).
              f_equal. f_equal.
              transitivity (nth (Z.to_nat j) (sub T' (48 * n_of T) 6) (Z_to_bv 8 0)).
              - rewrite o5_nth_sub by lia. f_equal. lia.
              - rewrite EM, o5_nth_sub by lia. reflexivity. }
            apply SRr_ret. right. unfold o5_ret, d_at.
            exists fq, ly3, S3, regs2, mem2, md2, k, acc.
            split; [unfold cfg_at, w64; reflexivity|].
            split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
            split; [exact Hmo|]. split; [exact Hacc|].
            exists T, T', ow.
            split.
            { exact (oy_oc_call_keep B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg T' (ms_regs msc)
                ly3 S3 W (ms_mem msc) _ k regs2 ly3 S3 W mem2 md2 k 8192 LAWS BCK HctxDc HctxD2 HOCc ltac:(lia)
                ltac:(unfold LLVMF_STK; lia) KPc (Permutation_refl _) HP). }
            split; [exact HTl0|]. split; [lia|]. split; [exact EN|]. split; [exact How|].
            split.
            { apply (oy_val_mem_keep W W mem3 mem2 (d_A cx + 360) 8 ow); [|exact H360].
              intros j Hj. apply KP; lia. }
            split.
            { rewrite (o5_pres _ _ 23%bv HP) by o5_cs. rewrite R23c. unfold w64, d_obj, dobj_off. f_equal; lia. }
            rewrite Hv. exact Hv0.
Qed.

Lemma o5_h2 : forall cx h i n now op nb fr len Sg W c,
  o5_ret cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (r27 cx h i (nb - len) now nb fr len).
Proof.
intros cx h i n now op nb fr len Sg W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ow & HOC & HTl0 & HN8 & HON & How & H360 & H23 & H10).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan).
pose proof Hframe as (E & HdE & Hregs & Hflag & V184 & V120 & V136 & V376 & V280 & V232 & V264).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (_ & _ & _ & HF0 & HFc & HFia & HFo & HF32 & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as ACV.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (HF8 : d_FB cx mod 8 = 0) by (apply o5_mod32_8; exact HF32).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFia.
destruct (slot_observe.new_facts T Sg ow now T' 1 HTl0 HSgl HN8 HON) as (_ & _ & _ & _ & NF).
destruct (slot_observe.new_fields Sg ow now HSgl) as (F0 & F8 & F12 & F13 & F14 & F15 & F16 & F20 & F24 & F32 & F40).
assert (UT : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= 48 ->
  u_at T' (48 * n_of T + d) w = bytes_le_to_Z (sub (reac_disco_table_observe_c.new_entry Sg ow now) d w))
  by (intros d w Hd Hw; unfold u_at; rewrite NF by lia; reflexivity).
assert (VT : forall d (w : nat) v, 0 <= d -> d + Z.of_nat w <= 48 -> u_at T' (48 * n_of T + d) w = v ->
  val_mem SEGS (rd W mem3) (d_FB cx + (2160 + 48 * n_of T + d)) w v).
{ intros d w v Hd Hw <-. replace (d_FB cx + (2160 + 48 * n_of T + d)) with (d_obj cx OT + (48 * n_of T + d))
    by (unfold d_obj, dobj_off; lia).
  apply o5_val_mem_sub; [exact HT | lia | rewrite HTl; lia]. }
assert (VS : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= 24 ->
  val_mem SEGS (rd W mem3) (d_FB cx + (2992 + d)) w (u_at Sg d w)).
{ intros d w Hd Hw. replace (d_FB cx + (2992 + d)) with (d_obj cx OS + d) by (unfold d_obj, dobj_off; lia).
  apply o5_val_mem_sub; [exact HSg | lia | rewrite HSgl; lia]. }
assert (RS : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= 24 -> 0 <= u_at Sg d w < 2 ^ (8 * Z.of_nat w))
  by (intros d w Hd Hw; apply o5_u_range; [lia | rewrite HSgl; lia]).
set (xs2 := [w64 (u_at Sg 8 4); w64 (u_at Sg 12 1); w64 (u_at Sg 13 1); w64 (u_at Sg 14 1); w64 (u_at Sg 15 1);
             w64 (u_at Sg 16 1); w64 (u_at Sg 20 4); w64 ow; w64 now]).
assert (EWX : forall j q d, q = (563 + j)%nat -> (j < 9)%nat ->
  ew (d_env cx E (obs_vals regs ++ xs2)) q = nth j xs2 d).
{ intros j q d -> Hj. rewrite (o5_ew_x cx E regs xs2 (563 + j) d) by (unfold xs2; cbn [length]; lia).
  f_equal. lia. }
assert (FC2 : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ xs2)) (rd W mem3) (d_FB cx))
  (o5_fcs (2160 + 48 * n_of T))).
{ unfold o5_fcs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ (u_at Sg 8 4));
      [apply o5_sv_atom; rewrite (EWX 0%nat 563%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 8 4%nat ltac:(lia) ltac:(lia)) | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F8 by lia; reflexivity]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 12 1));
      [apply o5_sv_atom; rewrite (EWX 1%nat 564%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 12 1%nat ltac:(lia) ltac:(lia)) | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F12 by lia; reflexivity]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 13 1));
      [apply o5_sv_atom; rewrite (EWX 2%nat 565%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 13 1%nat ltac:(lia) ltac:(lia)) | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F13 by lia; reflexivity]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 14 1));
      [apply o5_sv_atom; rewrite (EWX 3%nat 566%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 14 1%nat ltac:(lia) ltac:(lia)) | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F14 by lia; reflexivity]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 15 1));
      [apply o5_sv_atom; rewrite (EWX 4%nat 567%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 15 1%nat ltac:(lia) ltac:(lia)) | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F15 by lia; reflexivity]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 16 1));
      [apply o5_sv_atom; rewrite (EWX 5%nat 568%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 16 1%nat ltac:(lia) ltac:(lia)) | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F16 by lia; reflexivity]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ (u_at Sg 20 4));
      [apply o5_sv_atom; rewrite (EWX 6%nat 569%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 20 4%nat ltac:(lia) ltac:(lia)) | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F20 by lia; reflexivity]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ ow);
      [apply o5_sv_atom; rewrite (EWX 7%nat 570%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F24 by lia; destruct How as [Hw|Hw]; rewrite Hw; reflexivity]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 8 _ now);
      [apply o5_sv_atom; rewrite (EWX 8%nat 571%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F32 by lia; apply o5_u_le; exact Hnow]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 8 _ now);
      [apply o5_sv_atom; rewrite (EWX 8%nat 571%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia
      | o5_nt; apply VT; [lia | lia | rewrite UT, F40 by lia; apply o5_u_le; exact Hnow]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ (u_at Sg 8 4));
      [apply o5_sv_atom; rewrite (EWX 0%nat 563%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 8 4%nat ltac:(lia) ltac:(lia)) | lia | o5_nt; exact (VS 8 4%nat ltac:(lia) ltac:(lia))].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 12 1));
      [apply o5_sv_atom; rewrite (EWX 1%nat 564%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 12 1%nat ltac:(lia) ltac:(lia)) | lia | o5_nt; exact (VS 12 1%nat ltac:(lia) ltac:(lia))].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 13 1));
      [apply o5_sv_atom; rewrite (EWX 2%nat 565%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 13 1%nat ltac:(lia) ltac:(lia)) | lia | o5_nt; exact (VS 13 1%nat ltac:(lia) ltac:(lia))].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 14 1));
      [apply o5_sv_atom; rewrite (EWX 3%nat 566%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 14 1%nat ltac:(lia) ltac:(lia)) | lia | o5_nt; exact (VS 14 1%nat ltac:(lia) ltac:(lia))].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 15 1));
      [apply o5_sv_atom; rewrite (EWX 4%nat 567%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 15 1%nat ltac:(lia) ltac:(lia)) | lia | o5_nt; exact (VS 15 1%nat ltac:(lia) ltac:(lia))].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 1 _ (u_at Sg 16 1));
      [apply o5_sv_atom; rewrite (EWX 5%nat 568%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 16 1%nat ltac:(lia) ltac:(lia)) | lia | o5_nt; exact (VS 16 1%nat ltac:(lia) ltac:(lia))].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ (u_at Sg 20 4));
      [apply o5_sv_atom; rewrite (EWX 6%nat 569%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | exact (RS 20 4%nat ltac:(lia) ltac:(lia)) | lia | o5_nt; exact (VS 20 4%nat ltac:(lia) ltac:(lia))]. }
assert (AC2 : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ xs2)) (rd W mem3) (d_A cx)) o5_acs).
{ unfold o5_acs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 8 _ now);
      [apply o5_sv_atom; rewrite (EWX 8%nat 571%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact (proj2 Hsp0)].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 8 _ ow);
      [apply o5_sv_atom; rewrite (EWX 7%nat 570%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact H360]. }
pose proof (o5_regs_ok cx E regs xs2 HdE HrL HAr2) as RO2.
assert (EW516 : ew (d_env cx E (obs_vals regs ++ xs2)) 516 = Z_to_bv 64 (d_FB cx)).
{ rewrite oy_d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & _ & EF & _). exact EF. }
assert (EW570 : ew (d_env cx E (obs_vals regs ++ xs2)) 570 = Z_to_bv 64 ow)
  by (rewrite (EWX 7%nat 570%nat (Z_to_bv 64 0) eq_refl ltac:(lia)); reflexivity).
assert (SV541 : sv_denot (d_env cx E (obs_vals regs ++ xs2)) (SOff 541 0) =
  sv_denot (d_env cx E (obs_vals regs ++ xs2)) (SLit 0)).
{ pose proof (RO2 10%bv) as R. o5_rr R. rewrite H10 in R. rewrite <- R. reflexivity. }
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ xs2))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia).
  exact (HI a Ha). }
assert (EW32 : ew (d_env cx E (obs_vals regs ++ xs2)) 32 = Z_to_bv 64 SHADOW_OFF).
{ rewrite oy_d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & E32 & _). exact E32. }
assert (SHOK : sh_ok SEGS (SOff 32 0) o5_SH (d_env cx E (obs_vals regs ++ xs2)) (rd W mem3)).
{ unfold o5_SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. unfold AT_F, U.
    rewrite (o5_sv_atom _ 516 _ EW516), (o5_sv_atom _ 32 _ EW32), !Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 (d_FB cx)) by (unfold bv_modulus; lia).
    rewrite (bv_wrap_small 64 SHADOW_OFF) by (unfold bv_modulus, SHADOW_OFF; lia).
    replace (2560 - 2160) with 400 by lia.
    refine (oy_ra_frame cx dsh_rec W mem3 2160 400 Hshadow HF8 ltac:(lia) ltac:(lia) ltac:(lia) _).
    intros kk Hkk. apply oy_dsh_rec_t. lia.
  - intros a Ha. cbn [she_m she_lo she_hi] in Ha. unfold AT_F, U in Ha |- *.
    rewrite (o5_sv_atom _ 516 _ EW516), Z_to_bv_unsigned in Ha.
    rewrite (bv_wrap_small 64 (d_FB cx)) in Ha by (unfold bv_modulus; lia).
    rewrite (o5_sv_atom _ 32 _ EW32), Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 SHADOW_OFF) by (unfold bv_modulus, SHADOW_OFF; lia).
    unfold SHADOW_OFF. lia. }
pose (RUN := paj_run (fx := fq) (PI := PI) B LAWS).
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (MP : forall x, mem3 x = mem3 x) by reflexivity.
unfold cfg_at. change (w64 (BASE + OB_BCR)) with (Z_to_bv 64 (BASE + OB_BCR)).
assert (R23s : getr regs 23%bv = sv_denot (d_env cx E (obs_vals regs ++ xs2)) (SOff 516 (2160 + 48 * n_of T))).
{ cbn [sv_denot]. rewrite EW516, oy_w64_add_w, H23. unfold w64, d_obj, dobj_off. f_equal; lia. }
assert (Hm : n_of T = 0 \/ n_of T = 1 \/ n_of T = 2 \/ n_of T = 3 \/ n_of T = 4 \/ n_of T = 5 \/ n_of T = 6 \/
  n_of T = 7) by lia.
destruct Hm as [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]]; rewrite Hm in FC2, R23s.
all: lazymatch goal with
  | FC2 : Forall _ (o5_fcs ?e) |- _ =>
    let HS := fresh "HS" in
    pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_BCR obs_sr (obs_vals regs ++ xs2)
      o5_acs (o5_fcs e) [] (d_facts [] []) HctxD HdE Hregs Hflag RO2
      (FACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs ++ xs2) [] [] HctxD HdE I I)
      AC2 FC2 (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS;
    unfold ss_d in HS;
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let HS2 := fresh "HS" in
      pose proof (st_ok_pi_set_reg Ex ssx msx 23%bv (SOff 516 e) HS ltac:(discriminate) R23s) as HS2;
      clear HS; rename HS2 into HS; norm_ss HS
    end;
    ro_base HS 516%nat; ro_base HS 529%nat; ro_base HS 60%nat
  end;
  o5_run RUN;
  psrr_branch_tok RUN BR HS SHOK OBspan;
  [ exfalso; rewrite (o5_br_ne_false _ (SOff 541 0) (SLit 0)) in Hc; [discriminate Hc | exact SV541]
  | clear Hc; o5_run RUN;
    psrr_branch_tok RUN BR HS SHOK OBspan;
    [ exfalso; rewrite (o5_br_ne_false _ (SExt true 32 (SOff 570 0)) (SOff 570 0)) in Hc; [discriminate Hc|];
      rewrite (o5_sv_sext32 _ 570 _ EW570 ltac:(lia)), (o5_sv_atom _ 570 _ EW570);
      destruct How as [Hw|Hw]; rewrite Hw; reflexivity
    | clear Hc; o5_runto RUNTO R27_OFF;
      repeat rewrite wvb_collapse in HJ;
      apply SRr_ret;
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?ms) |- _ =>
        assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 27]%bv ->
          getr (ms_regs ms) r = getr regs r)
          by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), (RO2 r); cbv [In] in Hr;
              repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
        apply (o5_land fq cx h i n now op nb fr len Sg T' ly3 S3 W mem3 regs _ k acc E _ ss ms
          HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) MP HOC);
        destruct HrL as (Hsp & Hgp & Htp & R8 & R9 & R19 & R18 & R20 & R27); unfold d_rL, spZ in *;
        rewrite (RG 2%bv), (RG 3%bv), (RG 4%bv), (RG 8%bv), (RG 9%bv), (RG 18%bv), (RG 19%bv), (RG 20%bv), (RG 27%bv)
          by (cbv; tauto);
        repeat split; assumption
      end ] ].
Qed.

Theorem ob_s10r : ob_seg10r B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg W c H.
eapply SRr_bind; [exact (o5_h1 cx h i n now op nb fr len Sg W c H)|].
intros W' c' _ [HR|HR]; [apply SRr_ret; exact HR | exact (o5_h2 cx h i n now op nb fr len Sg W' c' HR)].
Qed.
End h.
End f.
End d.

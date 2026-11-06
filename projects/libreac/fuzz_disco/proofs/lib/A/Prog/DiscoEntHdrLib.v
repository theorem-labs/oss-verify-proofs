(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition hdr_sr (x7 : sv) : list sv :=
  [SLit 0; SOff 536 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 537 0; SOff 534 0; x7;
   SOff 2 0; SOff 60 0; SOff 538 0; SOff 533 0; SOff 539 0; SOff 540 0; SOff 516 2160; SOff 541 0;
   SOff 542 0; SOff 543 0; SOff 32 0; SOff 535 0; SLit WS_MASK; SOff 531 0; SOff 516 2992; SOff 544 0;
   SOff 545 0; SLit 32; SOff 516 2128; SOff 546 0; SOff 547 0; SOff 548 0; SOff 549 0; SOff 550 0].
Definition hdr_inchunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 551 0)); YP09.mkChunk 1 (CVal 1 (SOff 552 0)); YP09.mkChunk 2 (CVal 1 (SOff 553 0))].
Definition hdr_in (m : nat) : YP09.region := YP09.mkRegion (Some 531%nat) 0 (Z.of_nat m) 0 0 (firstn m hdr_inchunks).
Definition hdr_rs (m : nat) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 232 352 (dslot_chunks ++ []);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ []);
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_loop);
   got_regionP; bcell_regionP 32; hdr_in m].
Definition hdr_fa (n3 : bool) : list (nat * afact) :=
  (if n3 then [(532%nat, mkAF 3 (2 ^ 26) 0)] else []) ++
  [(551%nat, mkAF 0 255 0); (552%nat, mkAF 0 255 0); (553%nat, mkAF 0 255 0)].
Definition hdr_ss (x7 : sv) (m : nat) (n3 : bool) : sstate := mkSS HDR_OFF (hdr_sr x7) (hdr_rs m) None (d_facts (hdr_fa n3) []).
Definition hdr_now (op dt now : Z) : Z :=
  if op <? 128 then (dt * 1000000 + now) mod 2 ^ 64 else if now <? dt * 1000000 then 0 else now - dt * 1000000.

Lemma hd_swrap8 : forall b, 0 <= b < 256 -> bv_swrap 8 b = if b <? 128 then b else b - 256.
Proof.
intros b Hb. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
destruct (Z.ltb_spec b 128).
- rewrite Z.mod_small by lia. lia.
- replace (b + 128) with ((b - 128) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma hd_land_ones : forall x k, 0 <= k -> Z.land x (Z.ones k) = x mod 2 ^ k.
Proof. intros x k Hk. apply Z.land_ones. exact Hk. Qed.
Lemma hd_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma hd_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma hd_land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma hd_land_m1 : forall x, 0 <= x < 2 ^ 64 -> Z.land (2 ^ 64 - 1) x = x.
Proof.
intros x Hx. rewrite Z.land_comm. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
rewrite Z.land_ones by lia. apply Z.mod_small. exact Hx.
Qed.
Lemma hd_lor_add : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
intros a b Ha Hb.
assert (H0 : Z.land (a * 256) b = 0).
{ apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.bits_0.
  change 256 with (2 ^ 8). rewrite <- Z.shiftl_mul_pow2 by lia.
  destruct (Z.lt_ge_cases m 8) as [Hl|Hg].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 b m); [apply andb_false_r | lia |].
    apply Z.log2_lt_pow2; [lia|]. change (2 ^ 8) with 256 in *. assert (2 ^ 8 <= 2 ^ m) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 8) with 256 in *. lia. }
rewrite <- Z.lxor_lor by exact H0. rewrite <- Z.add_nocarry_lxor by exact H0. reflexivity.
Qed.

Section u.
Variable E : env.
Lemma hd_U_sext8 : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SExt true 8 (SOff k 0)) = if b <? 128 then b else b + (2 ^ 64 - 256).
Proof.
intros k b Hk Hb. rewrite U_SExt, (U_atom E k b Hk) by lia. change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small b 256) by lia. rewrite hd_swrap8 by lia. unfold zcanon, M64.
destruct (Z.ltb_spec b 128).
- apply Z.mod_small. lia.
- replace (b - 256) with ((b + (2 ^ 64 - 256)) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma hd_S_sext8 : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  Sg E (SExt true 8 (SOff k 0)) = if b <? 128 then b else b - 256.
Proof.
intros k b Hk Hb. rewrite S_of_U, (hd_U_sext8 k b Hk Hb).
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
destruct (Z.ltb_spec b 128).
- rewrite Z.mod_small by lia. lia.
- replace (b + (2 ^ 64 - 256) + 2 ^ 63) with ((b - 256 + 2 ^ 63) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma hd_U_op3 : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_AND (SExt true 8 (SOff k 0)) (SLit 3)) = b mod 4.
Proof.
intros k b Hk Hb. rewrite U_and_lit by lia. rewrite (hd_U_sext8 k b Hk Hb), hd_land3.
destruct (b <? 128); [reflexivity|].
replace (b + (2 ^ 64 - 256)) with (b + (2 ^ 62 - 64) * 4) by lia. apply Z.mod_add. lia.
Qed.
Lemma hd_U_op255 : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_AND (SExt true 8 (SOff k 0)) (SLit 255)) = b.
Proof.
intros k b Hk Hb. rewrite U_and_lit by lia. rewrite (hd_U_sext8 k b Hk Hb), hd_land255.
destruct (b <? 128).
- apply Z.mod_small. lia.
- replace (b + (2 ^ 64 - 256)) with (b + (2 ^ 56 - 1) * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma hd_U_dt1 : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 -> U E (SAlu ALU_OR (SLit 0) (SOff k 0)) = b.
Proof.
intros k b Hk Hb. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E k b Hk) by lia.
change (zcanon 0) with 0. rewrite Z.lor_0_l. apply zcanon_id. unfold M64. lia.
Qed.
Lemma hd_U_dt2 : forall k2 k1 b2 b1, ew E k2 = Z_to_bv 64 b2 -> 0 <= b2 < 256 -> ew E k1 = Z_to_bv 64 b1 -> 0 <= b1 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff k2 0) (SLit 8)) (SOff k1 0)) = b2 * 256 + b1.
Proof.
intros k2 k1 b2 b1 H2 R2 H1 R1. rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E k2 b2 H2), (U_atom E k1 b1 H1) by lia.
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (b2 * 256)) by (unfold M64; lia). rewrite hd_lor_add by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma hd_U_nowadd : forall X dt k now, U E X = dt -> 0 <= dt < 65536 -> ew E k = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL X (SLit 1000000)) (SOff k 0)) = (dt * 1000000 + now) mod 2 ^ 64.
Proof.
intros X dt k now HX Rdt Hk Rn. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite HX, U_SLit, (U_atom E k now Hk) by lia.
change (zcanon 1000000) with 1000000. rewrite (zcanon_id (dt * 1000000)) by (unfold M64; lia). reflexivity.
Qed.
Lemma hd_U_nowsub : forall X dt k now, U E X = dt -> 0 <= dt < 65536 -> ew E k = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff k 0) (SAlu ALU_SUB (SOff k 0) (SMd M_MUL X (SLit 1000000))))
                     (SLit (-1))) (SAlu ALU_SUB (SOff k 0) (SMd M_MUL X (SLit 1000000))))
  = if now <? dt * 1000000 then 0 else now - dt * 1000000.
Proof.
intros X dt k now HX Rdt Hk Rn.
assert (UM : U E (SMd M_MUL X (SLit 1000000)) = dt * 1000000).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite HX, U_SLit. change (zcanon 1000000) with 1000000. apply zcanon_id. unfold M64. lia. }
assert (US : U E (SAlu ALU_SUB (SOff k 0) (SMd M_MUL X (SLit 1000000))) =
  if now <? dt * 1000000 then now - dt * 1000000 + 2 ^ 64 else now - dt * 1000000).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite UM, (U_atom E k now Hk) by lia. unfold zcanon, M64.
  destruct (Z.ltb_spec now (dt * 1000000)).
  - rewrite <- (Z.mod_add (now - dt * 1000000) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - apply Z.mod_small. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite US. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite US, (U_atom E k now Hk), U_SLit by lia. change (zcanon (-1)) with (2 ^ 64 - 1).
destruct (Z.ltb_spec now (dt * 1000000)).
- rewrite (proj2 (Z.ltb_lt now (now - dt * 1000000 + 2 ^ 64))) by lia.
  replace (zcanon (zcanon 1 + (2 ^ 64 - 1))) with 0 by reflexivity. rewrite Z.land_0_l. reflexivity.
- rewrite (proj2 (Z.ltb_ge now (now - dt * 1000000))) by lia.
  replace (zcanon (zcanon 0 + (2 ^ 64 - 1))) with (2 ^ 64 - 1) by reflexivity. rewrite (hd_land_m1 (now - dt * 1000000)) by lia.
  apply zcanon_id. unfold M64. lia.
Qed.
Lemma hd_U_nowand : forall k now, ew E k = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
  U E (SAlu ALU_AND (SOff k 0) (SLit 18446744073709551615)) = now.
Proof.
intros k now Hk Rn. rewrite U_and_lit by lia. rewrite (U_atom E k now Hk Rn).
change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma hd_shaddr : forall k c v, ew E k = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> 0 <= v -> 0 <= c -> v + c < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff k c) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (shadow_addr (v + c)).
Proof.
intros k c v Hk H32 Hv Hc Hvc. rewrite denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E k v c Hk), U_SLit, (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; lia).
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 <= v + c) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). unfold shadow_addr, SHADOW_OFF.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma hd_br_lt : forall a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros a b. reflexivity. Qed.
Lemma hd_br_ge : forall a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros a b. reflexivity. Qed.
Lemma hd_S_and7 : forall k c v, ew E k = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 ->
  Sg E (SAlu ALU_AND (SOff k c) (SLit 7)) = (v + c) mod 8.
Proof.
intros k c v Hk Hv Hc Hvc. rewrite S_of_U. rewrite U_and_lit by lia. rewrite (U_atom_off E k v c Hk) by lia. rewrite hd_land7.
pose proof (Z.mod_pos_bound (v + c) 8 ltac:(lia)). apply swrap64_id. unfold half64. lia.
Qed.
Lemma hd_S_lit0 : Sg E (SLit 0) = 0.
Proof. rewrite S_SLit. reflexivity. Qed.
End u.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition hb (cx : dcx) (n j : Z) : Z := nth (Z.to_nat (c_n cx - n + j)) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0.
Definition hsh (cx : dcx) (n j : Z) : Z := if (c_n cx - n + j) / 8 <? c_n cx / 8 then 0 else c_n cx mod 8.
Definition hdt (cx : dcx) (n : Z) : Z := if n =? 1 then 0 else if n =? 2 then hb cx n 1 else hb cx n 2 * 256 + hb cx n 1.
Definition hn' (n : Z) : Z := if n <=? 2 then 0 else n - 3.
Definition hdr_vals (cx : dcx) (h i n now : Z) (regs : bvmap 5 word) : list word :=
  [w64 (d_cur cx n); w64 n; w64 now; w64 i; w64 h; getr regs 1; getr regs 5; getr regs 10; getr regs 12; getr regs 13;
   getr regs 15; getr regs 16; getr regs 17; getr regs 23; getr regs 24; getr regs 27; getr regs 28; getr regs 29;
   getr regs 30; getr regs 31; w64 (hb cx n 0); w64 (hb cx n 1); w64 (hb cx n 2)].

Lemma hb_range : forall cx n j, 0 <= hb cx n j < 256.
Proof.
intros cx n j. unfold hb. set (l := map (fun b : byte => bv_unsigned b) (c_pl cx)). set (k := Z.to_nat (c_n cx - n + j)).
destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
- assert (In (nth k l 0) l) by (apply nth_In; exact Hk). subst l. apply in_map_iff in H as (b & <- & _). apply u8_range.
- rewrite nth_overflow by exact Hk. lia.
Qed.
Lemma hd_val_mem1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte SEGS H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
first [unfold YO0f.le_byte | unfold YG0f.le_byte]. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma hd_val_mem_keep : forall (H : word -> bool) (m m' : word -> option byte) a (w : nat) v,
  val_mem SEGS (mrestrict H m) a w v -> (forall j, 0 <= j < Z.of_nat w -> aview SEGS H m' (a + j) = aview SEGS H m (a + j)) ->
  val_mem SEGS (mrestrict H m') a w v.
Proof.
intros H m m' a w v Hv Hk k Hkk. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat k)); [apply Hv; exact Hkk|]. apply Hk. lia.
Qed.
Lemma hd_meq_frame : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> lo <= a < hi) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 lo hi HF Hw HM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs H m1 m2 (fun a => lo <= a < hi) HF Hw a Ha Hn). exact (HM a Ha Hn).
Qed.
Lemma hd_pres_grow : forall (H : word -> bool) (m0 m1 m2 : word -> option byte),
  mem_grows (mrestrict H m1) (mrestrict H m2) ->
  (forall a, apresent H m0 a -> apresent H m1 a) -> forall a, apresent H m0 a -> apresent H m2 a.
Proof.
intros H m0 m1 m2 HG HP a Ha. destruct (HP a Ha) as (Hh & b & Hb). split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|]. exfalso. apply HG; [discriminate | reflexivity].
Qed.
Lemma hd_cell : forall (H : word -> bool) (m : word -> option byte) p N n j,
  block_shadow (aview SEGS H m) SHADOW_OFF p N -> 0 <= N - n + j < N ->
  aview SEGS H m (shadow_addr (p + (N - n) + j)) = Some (if (N - n + j) / 8 <? N / 8 then 0 else N mod 8).
Proof.
intros H m p N n j (Hp8 & HN0 & HB) Hr.
assert (Hi : 0 <= (N - n + j) / 8 < (N + 7) / 8).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  pose proof (Z.mul_div_le (N - n + j) 8 ltac:(lia)). pose proof (Z.div_mod (N + 7) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (N + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (N - n + j) 8 ltac:(lia)).
  pose proof (Z.div_mod (N - n + j) 8 ltac:(lia)). lia. }
specialize (HB _ Hi). unfold shadow_of_addr in HB. rewrite <- HB. f_equal. unfold shadow_addr.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. rewrite Hp8 in Dp.
replace (p + (N - n) + j) with ((N - n + j) + (p / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.

Lemma hd_d_E_agree : forall cx E E', d_E cx E -> (forall k, (k < 530)%nat -> ew E' k = ew E k) -> d_E cx E'.
Proof.
intros cx E E' (EE & E32 & HEI & E60 & E516 & E529) AG.
split; [intros n r Hn; rewrite AG; [apply EE; exact Hn | pose proof (u5_range r); lia]|].
split; [rewrite AG by lia; exact E32|].
split; [intros a Ha; rewrite AG by (unfold A_LIM in Ha; lia); apply HEI; exact Ha|].
split; [rewrite AG by (unfold AT_A; lia); exact E60|].
split; [rewrite AG by (unfold AT_F; lia); exact E516|].
rewrite AG by (unfold AT_SH; lia); exact E529.
Qed.

Lemma hd_d_at_mono : forall cx pc kmax accmax (P P' : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop) W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P W c ->
  (forall regs ly S W' mem md, P regs ly S W' mem md -> P' regs ly S W' mem md) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P' W c.
Proof.
intros cx pc kmax accmax P P' W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hq & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HP) HPP.
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]). apply HPP. exact HP.
Qed.

Lemma hd_A_range : forall cx, 608 <= d_S cx -> d_S cx - 608 < d_A cx <= d_S cx - 576 /\ d_A cx mod 32 = 0.
Proof.
intros cx HS. unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as M. unfold MFRAME in *.
split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Lemma hdr_land : forall (fq : YK11.FPState) (cx : dcx) (h i n now : Z) ly3 S3 (W3 : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state) (n' now' pc : Z)
  (P : bvmap 5 word -> Prop) (Q : Prop),
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_land_chk dsh_loop (ss_mem ss) = true ->
  d_body B cx h n [] dsh_loop ly3 S3 W3 mem3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 232 <= a < d_A cx + 352) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms) a) ->
  0 <= n' <= n ->
  val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 232) 8 i -> val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 344) 8 now' ->
  P (ms_regs ms) -> Q ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc (EV_HEAD i) (ACC_HEAD MT i)
    (fun regs ly3' S3' W3' mem3' md3' =>
       Q /\ P regs /\ d_sp0 cx i now' W3' mem3' /\ d_body B cx h n' [] dsh_loop ly3' S3' W3' mem3')
    W3 (mkCfg ms md').
Proof.
intros fq cx h i n now ly3 S3 W3 mem3 md' k acc E ss ms n' now' pc P Q
  HB HFQ HJ HFR Hk Hev Hmo Hacc HE HFL HS Hrv Hpc Hchk HBD MEQ MPR Hn' V232 V344 HP HQ.
pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
destruct (hd_A_range cx HS608) as [HAr _].
pose proof HBD as (T & G & Lk & H & HFRM & _).
pose proof HFRM as (E0 & _ & _ & _ & V216 & V152).
assert (V216' : val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 216) 8 h).
{ apply (hd_val_mem_keep (w_H W3) mem3 (ms_mem ms) (d_A cx + 216) 8 h V216). intros j Hj. apply MEQ; [|lia].
  unfold d_S, LLVMF_STK in *. lia. }
assert (V152' : val_mem SEGS (rd W3 (ms_mem ms)) (d_A cx + 152) 8 (h + 440)).
{ apply (hd_val_mem_keep (w_H W3) mem3 (ms_mem ms) (d_A cx + 152) 8 (h + 440) V152). intros j Hj. apply MEQ; [|lia].
  unfold d_S, LLVMF_STK in *. lia. }
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_loop ly3 S3 W3 md' k E ss ms (conj HB (conj HJ HFR)) HE HFL HS Hchk V216' V152')
  as [HFRM' HSHD'].
assert (HBD' : d_body B cx h n' [] dsh_loop ly3 S3 W3 (ms_mem ms)).
{ apply (d_body_keep B cx h n n' dsh_loop ly3 S3 W3 mem3 (ms_mem ms) (d_A cx + 232) (d_A cx + 352) HBD).
  - unfold d_S, LLVMF_STK in *. lia.
  - lia.
  - exact MEQ.
  - intros a _ Ha. exact (MPR a Ha).
  - exact HFRM'.
  - exact HSHD'.
  - exact Hn'. }
pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFQ|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact HQ|]. split; [exact HP|]. split; [exact (conj V232 V344)|]. exact HBD'.
Qed.

Lemma hdr_seat : forall (fq : YK11.FPState) (cx : dcx) (h i n now : Z) ly3 S3 (W3 : world SEGS) (regs : bvmap 5 word) mem3 md3 k
  (E : env) (x7 : sv) (m : nat) (n3 : bool),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W3 mem3)) (d_regions cx dsh_loop) ->
  rdword (aview SEGS (w_H W3) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) = Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  d_rH B cx h i n now regs ->
  getr regs 7 = sv_denot (d_env cx E (hdr_vals cx h i n now regs)) x7 ->
  (m <= 3)%nat -> Z.of_nat m <= n -> (n3 = true -> 3 <= n <= 2 ^ 26) ->
  0 <= i < 2 ^ 64 -> 0 <= now < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  In (c_p cx, c_n cx) (ablocks B ly3 S3) -> 1 <= n <= c_n cx - 7 -> c_n cx < 2 ^ 26 ->
  garr8 SEGS (rd W3 mem3) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  off_img (c_p cx) (c_n cx) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (hdr_vals cx h i n now regs)) (hdr_ss x7 m n3)
    (restrict (w_H W3) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + HDR_OFF)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now ly3 S3 W3 regs mem3 md3 k E x7 m n3 HC HE HRG HFL HR H7 Hm Hmn Hn3 Ri Rnow Rh Hin Hn HN HG HOI.
set (vals := hdr_vals cx h i n now regs).
pose proof HC as (HB & HJ & HFR).
pose proof HB as ((HPRE & _) & _). pose proof HPRE as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & HLY & _).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529). unfold AT_A, AT_F, AT_SH in E60, E516, E529.
pose proof HR as ((Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25) & H19 & H6 & H7' & H11 & H14 & H21 & H22 & H26).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY) as (_ & EFA3 & _).
assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF0 & HFc & HFapp).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin Hfin) as HBF.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hp16 & Hp4k & Hpc & Hpapp & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF32 & _).
rewrite EFA3 in HF0, HFc, HFapp, HBF, HF32. fold (d_FB cx) in HF0, HFc, HFapp, HBF, HF32.
assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
rewrite Hrq in Hpc, Hpapp, HBF.
assert (Hfb : fs_frame_bytes DFRAME_CLASS = 4096) by reflexivity. rewrite Hfb in *.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
destruct (hd_A_range cx HS608) as [HAr HA32].
assert (HSr : 0 <= d_S cx <= 2 ^ 47) by (unfold d_S, LLVMF_STK in *; lia).
assert (HSlo : alloc_ceiling + 32768 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Ho1. pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Ho66.
assert (EL : forall q, (q < 530)%nat -> ew (d_env cx E vals) q = ew E q) by (intros q Hq; unfold d_env; apply ew_havoc_old; exact Hq).
assert (EV : forall q j, q = (531 + j)%nat -> (j < 23)%nat -> ew (d_env cx E vals) q = nth j vals (Z_to_bv 64 0)).
{ intros q j -> Hj. unfold d_env. replace (531 + j)%nat with (AT_FL + S j)%nat by (unfold AT_FL; lia).
  rewrite (ew_havoc_new E AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; unfold vals, hdr_vals; cbn [length]; lia). reflexivity. }
assert (Ecur : ew (d_env cx E vals) 531 = Z_to_bv 64 (d_cur cx n)) by exact (EV 531%nat 0%nat eq_refl ltac:(lia)).
assert (Ecur0 : 0 <= d_cur cx n) by (unfold d_cur; lia).
assert (Uf : forall q v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E q) = v)
  by (intros q v Hq Hv; rewrite Hq; apply unsigned_lit_small; exact Hv).
assert (UFB : bv_unsigned (ew E 516) = d_FB cx) by (apply Uf; [exact E516 | lia]).
pose proof (pa_val_range (A_OBJ 1)) as RV1. pose proof (pa_val_range (A_OBJ 66)) as RV66.
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply img_env_atomP; [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (EO66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (apply img_env_atomP; [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (E2 : ew E 2 = Z_to_bv 64 (d_S cx)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ly3 S3 W3 regs mem3 md3 k E HDR_OFF (hdr_sr x7) vals [] [] [hdr_in m]
  (d_facts (hdr_fa n3) []) HC HE HRG HFL) as HSEAT.
assert (Hm4 : m = 0%nat \/ m = 1%nat \/ m = 2%nat \/ m = 3%nat) by lia.
assert (HREGS : regs_ok (d_env cx E vals) (hdr_sr x7) regs).
{ apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [ <- | Hr ];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
      lazymatch goal with
      | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
      | |- _ = sv_denot _ x7 => exact H7
      | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H20 | exact H25 ]
      | |- _ = sv_denot _ (SOff 516 _) => cbn [sv_denot]; rewrite EL by lia; rewrite UFB;
          first [ rewrite H14 | rewrite H22 | rewrite H26 ]; unfold w64, d_obj, dobj_off; reflexivity
      | |- _ = sv_denot _ (SOff ?q 0) => rewrite sv_denot_SOff0;
          lazymatch eval vm_compute in (Nat.ltb q 530) with
          | true => rewrite EL by lia;
              first [ rewrite E60; first [ exact H9 | unfold w64; rewrite <- Hsp; unfold YG0d.spZ; symmetry; apply Z_to_bv_bv_unsigned ]
                    | rewrite E32; exact H18
                    | rewrite E2; exact H8
                    | rewrite (EE 3%nat 3%bv eq_refl), Hgp0; exact Hgp
                    | rewrite (EE 4%nat 4%bv eq_refl), Htp0; exact Htp ]
          | false => let j := eval vm_compute in (q - 531)%nat in
              rewrite (EV q j eq_refl ltac:(lia)); unfold vals, hdr_vals; cbn [nth];
              first [ reflexivity | assumption ]
          end
      end
    | ]).
  destruct Hr. }
assert (HFACTS : facts_ok (d_env cx E vals) (d_facts (hdr_fa n3) [])).
{ apply (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k E vals (hdr_fa n3) [] HC HE); [|exact I].
  assert (AB : forall j q, (j < 3)%nat -> q = (551 + j)%nat -> afact_ok (d_env cx E vals) q (mkAF 0 255 0)).
  { intros j q Hj ->. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (EV (551 + j)%nat (20 + j)%nat ltac:(lia) ltac:(lia)).
    pose proof (hb_range cx n 0). pose proof (hb_range cx n 1). pose proof (hb_range cx n 2).
    assert (Hj3 : j = 0%nat \/ j = 1%nat \/ j = 2%nat) by lia.
    destruct Hj3 as [ -> | [ -> | -> ] ]; unfold vals, hdr_vals; cbn [nth Nat.add]; unfold w64;
    rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia. }
  assert (ABS : atoms_ok (d_env cx E vals) [(551%nat, mkAF 0 255 0); (552%nat, mkAF 0 255 0); (553%nat, mkAF 0 255 0)]).
  { cbn [atoms_ok]. split; [exact (AB 0%nat _ ltac:(lia) eq_refl)|]. split; [exact (AB 1%nat _ ltac:(lia) eq_refl)|].
    split; [exact (AB 2%nat _ ltac:(lia) eq_refl) | exact I]. }
  destruct n3; cbn [hdr_fa app]; [|exact ABS].
  cbn [atoms_ok]. split; [|exact ABS].
  unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (EV 532%nat 1%nat eq_refl ltac:(lia)); unfold vals, hdr_vals; cbn [nth]; unfold w64.
  specialize (Hn3 eq_refl). rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (HSUB : forall rs, rs = hdr_rs m -> submem rs (d_kregions dsh_loop [] [] ++ [hdr_in m])).
{ intros rs ->. unfold hdr_rs, d_kregions. cbn [app].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|].
  apply submem_keep; [apply subregion_refl|]. apply submem_nil. }
assert (HEXT : Forall (region_ok SEGS (d_env cx E vals) (rd W3 mem3)) [hdr_in m]).
{ apply Forall_cons; [|apply Forall_nil]. unfold region_ok, hdr_in.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Ecur.
  rewrite unsigned_lit_small by (unfold d_cur in *; lia).
  split; [lia|]. split; [unfold d_cur in *; lia|]. split; [intros o Ho; lia|].
  assert (CK : forall j, (j < 3)%nat -> Z.of_nat j < Z.of_nat m ->
    YP09.chunk_ok SEGS (d_env cx E vals) (rd W3 mem3) (d_cur cx n) (YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (551 + j) 0)))).
  { intros j Hj Hjm. apply (chunk_ok_val SEGS _ _ _ _ 1 _ (hb cx n (Z.of_nat j))).
    - rewrite sv_denot_SOff0, (EV (551 + j)%nat (20 + j)%nat ltac:(lia) ltac:(lia)).
      assert (Hj3 : j = 0%nat \/ j = 1%nat \/ j = 2%nat) by lia. destruct Hj3 as [ -> | [ -> | -> ] ]; reflexivity.
    - pose proof (hb_range cx n (Z.of_nat j)). change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    - cbn. lia.
    - change (N.to_nat 1) with 1%nat. unfold hb.
      assert (Hidx : (Z.to_nat (c_n cx - n + Z.of_nat j) < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat).
      { rewrite length_map. pose proof HB as ((_ & _ & _ & _ & _ & Hlen & _) & _). lia. }
      destruct (HG _ Hidx) as [Hv _]. unfold d_cur. rewrite Z2Nat.id in Hv by lia.
      replace (c_p cx + (c_n cx - n) + Z.of_nat j) with (c_p cx + (c_n cx - n + Z.of_nat j)) by lia. exact Hv. }
  destruct Hm4 as [ -> | [ -> | [ -> | -> ] ] ]; cbn [firstn hdr_inchunks]; repeat apply Forall_cons; try apply Forall_nil;
  first [ exact (CK 0%nat ltac:(lia) ltac:(lia)) | exact (CK 1%nat ltac:(lia) ltac:(lia)) | exact (CK 2%nat ltac:(lia) ltac:(lia)) ]. }
assert (HPD : pairwise_disjoint (d_env cx E vals) [hdr_in m]) by (cbn; tauto).
assert (HAD : Forall (fun r => all_disjoint (d_env cx E vals) r (d_kregions dsh_loop [] [])) [hdr_in m]).
{ apply Forall_cons; [|apply Forall_nil]. apply all_disjoint_of_extents. unfold extent_of_region, hdr_in, d_kregions, fshadow_region,
    got_regionP, bcell_regionP. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold AT_STK, AT_A, AT_F, AT_SH.
  rewrite Ecur, !EL by (unfold A_OBJ; lia). rewrite E2, E60, E516, E529, EO1, EO66. unfold w64.
  rewrite !unsigned_lit_small by (unfold d_cur, shadow_addr, SHADOW_OFF in *; unfold IMG_LO, IMG_TOP in *;
    pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia)); pose proof (Z.div_le_upper_bound (d_FB cx) 8 (d_FB cx) ltac:(lia) ltac:(lia)); lia).
  change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, d_cur, shadow_addr, SHADOW_OFF, off_img, zdisjoint in *.
  unfold IMG_LO, IMG_TOP in *. cbn [fst snd] in HBF.
  pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (d_FB cx) 8 ltac:(lia)).
  destruct Hm4 as [ -> | [ -> | [ -> | -> ] ] ]; cbn [Z.of_nat]; repeat split; lia. }
assert (HWF : regions_wf (d_kregions dsh_loop [] [] ++ [hdr_in m]) = true)
  by (destruct Hm4 as [ -> | [ -> | [ -> | -> ] ] ]; vm_compute; reflexivity).
specialize (HSEAT HREGS HFACTS (Forall_nil _) (Forall_nil _) HEXT HPD HAD HWF).
pose proof (st_ok_pi_submem _ _ _ (hdr_rs m) HSEAT (HSUB _ eq_refl)
  ltac:(destruct Hm4 as [ -> | [ -> | [ -> | -> ] ] ]; vm_compute; reflexivity)) as HS1.
exact HS1.
Qed.
End h.
End f.
End d.

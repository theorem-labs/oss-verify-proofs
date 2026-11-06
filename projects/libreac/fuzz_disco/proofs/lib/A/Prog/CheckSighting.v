(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue_defect.v, with its module paths, module names and numbers changed; 985 of its 1061 lines of code are new or changed and 583 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import SightModel.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel CtrlParsed disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC4b YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j YK00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Section h.
Variable B : asyms.
Definition TCHECK_SIGHTING_STK : Z := 64 + 2 * ESTACK.
Definition tcheck_sighting_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TCHECK_SIGHTING_STK [] regs ly S W mem md 0 (fun ly' S' W' _ mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_SIGHTING_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).
Definition tcheck_sighting_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (s f len u st : Z) (G FB U : list byte),
  afn_pre SEGS B TCHECK_SIGHTING_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 f -> getr regs 12 = w64 len -> getr regs 13 = w64 u ->
  getr regs 14 = w64 st ->
  0 < s -> s mod 4 = 0 -> s + 24 <= 2 ^ 63 -> 0 < f -> f + 50 <= 2 ^ 63 -> 0 < u -> u + 6 <= 2 ^ 63 ->
  0 <= len < 2 ^ 64 -> 0 <= st < 2 ^ 64 -> len <= 65535 ->
  length G = 24%nat -> garr8 SEGS (mrestrict (w_H W) mem) s (map bv_unsigned G) ->
  length FB = 50%nat -> garr8 SEGS (mrestrict (w_H W) mem) f (map bv_unsigned FB) ->
  length U = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem) u (map bv_unsigned U) ->
  amem_range s 24 -> amem_range f 50 -> amem_range u 6 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s 24 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) s 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF f 50 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) f 50 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF u 6 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) u 6 ->
  (s + 24 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= s) ->
  (f + 50 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= f) ->
  off_img s 24 -> off_img f 50 -> (s + 24 <= f \/ f + 50 <= s) ->
  (u + 6 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= u) ->
  sighting_facts G FB U len st ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_check_sighting) regs mem md) (tcheck_sighting_post fq regs ly S W mem md).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Definition cs_q : sv := SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 48)) (SLit (-14636698788954112))) (SLit 3817799680)) (SLit 21).
Definition cs_r : sv := SAlu ALU_SUB (SOff 12 (-52)) (SMd M_MUL cs_q (SLit 36)).
Definition cs_mq : sv := SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_AND cs_r (SLit 65535))) (SLit (-1))) cs_q.
Definition cs_rem : sv := SAlu ALU_SLL (SAluw ALU_SUB (SOff 12 (-52)) (SMd M_MUL cs_q (SLit 36))) (SLit 48).
Definition cs_sx : sv := SExt true 32 (SOff 37 0).
Fixpoint cs_sum (n : nat) : sv := match n with O => SOff 40 0 | S k => SAlu ALU_ADD (cs_sum k) (SOff (40 + S k) 0) end.
Definition cs_fl : sv := SAlu ALU_SLTU (SOff 39 0) (SLit 1).
Definition cs_sb (fl : sv) : sv := SAlu ALU_OR fl (SAlu ALU_SLTU (SAlu ALU_AND (cs_sum 31) (SLit 255)) (SLit 1)).
Definition zsx (c : Z) : Z := if c <? 2 ^ 31 then c else c + (2 ^ 64 - 2 ^ 32).
Definition zmq (len : Z) : Z := if (len - 52) mod 36 =? 0 then (len - 52) / 36 else 0.
Lemma cs_U_sx : forall E ch, ew E 37 = Z_to_bv 64 ch -> 0 <= ch < 2 ^ 32 -> U E cs_sx = zsx ch.
Proof.
intros E ch H R. unfold cs_sx. rewrite U_SExt, (U_atom E 37 ch H) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small ch (2 ^ 32)) by lia. unfold zsx. destruct (Z.ltb_spec ch (2 ^ 31)) as [L|L].
- rewrite (swrap32_id ch) by lia. apply zcanon_small. lia.
- replace ch with (ch - 2 ^ 32 + 1 * bv_modulus 32) at 1 by (change (bv_modulus 32) with (2 ^ 32); lia).
rewrite swrap_add_mod, (swrap32_id (ch - 2 ^ 32)) by lia. unfold zcanon, M64. symmetry. apply Z.mod_unique with (-1); lia.
Qed.
Lemma cs_U_q : forall E len, ew E 12 = Z_to_bv 64 len -> 52 <= len <= 65535 -> U E cs_q = (len - 52) / 36.
Proof.
intros E len H R. unfold cs_q. rewrite !U_SAlu, U_SMd, !U_SAlu, !U_SLit, (U_atom E 12 len H) by lia. cbn [zalu_raw zmd_raw].
change (zcanon 48) with 48. change (Z.land 48 63) with 48. change (zcanon (-14636698788954112)) with 18432107374920597504.
change (zcanon 3817799680) with 3817799680. change (Z.of_N 64) with 64. change (zcanon 21) with 21. change (Z.land 21 63) with 21.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_small (len * 2 ^ 48)) by lia.
replace (zcanon (len * 2 ^ 48 + 18432107374920597504)) with ((len - 52) * 2 ^ 48) by (unfold zcanon, M64; apply Z.mod_unique with 1; lia).
replace ((len - 52) * 2 ^ 48 * 3817799680) with ((len - 52) * 58255 * 2 ^ 64) by lia.
rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. rewrite (zcanon_small ((len - 52) * 58255)) by lia.
change (2 ^ 21) with 2097152.
pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as M.
assert (Q : (len - 52) * 58255 / 2097152 = (len - 52) / 36).
{ symmetry. apply Z.div_unique_pos with (r := 28 * ((len - 52) / 36) + (len - 52) mod 36 * 58255); lia. }
rewrite Q. apply zcanon_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma cs_U_r : forall E len, ew E 12 = Z_to_bv 64 len -> 52 <= len <= 65535 -> U E cs_r = (len - 52) mod 36.
Proof.
intros E len H R. unfold cs_r. rewrite U_SAlu, U_SMd, (cs_U_q E len H R), U_SOff, U_SLit, H. cbn [zalu_raw zmd_raw].
rewrite unsigned_lit_small by lia. change (zcanon 36) with 36.
pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as M.
set (q := (len - 52) / 36) in *. set (m := (len - 52) mod 36) in *.
rewrite (zcanon_small (len + -52)) by lia. rewrite (zcanon_small (q * 36)) by lia. rewrite zcanon_small by lia. lia.
Qed.
Lemma cs_U_mq : forall E len, ew E 12 = Z_to_bv 64 len -> 52 <= len <= 65535 -> U E cs_mq = zmq len.
Proof.
intros E len H R. unfold cs_mq.
rewrite (U_SAlu E ALU_AND (SAlu ALU_ADD _ _) cs_q), (U_SAlu E ALU_ADD), (U_SAlu E ALU_SLTU), (U_SAlu E ALU_AND cs_r (SLit 65535)).
rewrite (cs_U_r E len H R), (cs_U_q E len H R), !U_SLit. cbn [zalu_raw].
pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as M.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones, (Z.mod_small ((len - 52) mod 36)) by lia.
change (zcanon 0) with 0. change (zcanon (-1)) with (Z.ones 64).
unfold zmq. destruct (Z.eqb_spec ((len - 52) mod 36) 0) as [E0|E0].
- rewrite E0. change (zcanon (if 0 <? zcanon 0 then 1 else 0)) with 0. change (zcanon (0 + Z.ones 64)) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones by lia. rewrite (Z.mod_small ((len - 52) / 36)) by lia. apply zcanon_small. lia.
- rewrite (zcanon_small ((len - 52) mod 36)) by lia. replace (0 <? (len - 52) mod 36) with true by (symmetry; apply Z.ltb_lt; lia).
change (zcanon (zcanon 1 + Z.ones 64)) with 0. rewrite Z.land_0_l. reflexivity.
Qed.
Lemma cs_U_rem : forall E len, ew E 12 = Z_to_bv 64 len -> 52 <= len <= 65535 -> U E cs_rem = (len - 52) mod 36 * 2 ^ 48.
Proof.
intros E len H R. unfold cs_rem. rewrite U_SAlu, U_SLit. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw.
rewrite U_SMd, (cs_U_q E len H R), U_SOff, U_SLit, H. cbn [zalu_raw zmd_raw].
rewrite unsigned_lit_small by lia. change (zcanon 36) with 36. change (zcanon 48) with 48. change (Z.land 48 63) with 48.
pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as M.
set (q := (len - 52) / 36) in *. set (m := (len - 52) mod 36) in *.
rewrite (zcanon_small (len + -52)) by lia. rewrite (zcanon_small (q * 36)) by lia.
rewrite (Z.mod_small (len + -52) (2 ^ 32)) by lia. rewrite (Z.mod_small (q * 36) (2 ^ 32)) by lia.
replace (len + -52 - q * 36) with m by lia.
assert (SW : bv_swrap 32 m = m) by (apply swrap32_id; lia).
rewrite SW. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small m) by lia.
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_small. lia.
Qed.
Lemma cs_psum_rng : forall (bs : list byte) k, 0 <= psum bs k <= 255 * Z.of_nat k.
Proof.
intros bs k. induction k as [|k IH]; cbn [psum]; [lia|].
pose proof (bv_unsigned_in_range 8 (nth k bs (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256 in Hb. lia.
Qed.
Lemma cs_nth_fld : forall (FB : list byte) j d, (j < 32)%nat -> nth j (fld FB 18 32) d = nth (18 + j) FB d.
Proof. intros FB j d Hj. unfold fld. rewrite nth_firstn. destruct (Nat.ltb_spec j 32); [|lia]. apply nth_skipn. Qed.
Lemma cs_U_sum : forall E (FB : list byte), (forall n, (38 <= n < 72)%nat -> ew E n = Z_to_bv 64 (fb FB (n - 22))) ->
  forall k, (k < 32)%nat -> U E (cs_sum k) = psum (fld FB 18 32) (S k).
Proof.
intros E FB HF k. induction k as [|k IH]; intros Hk.
- cbn [cs_sum psum]. pose proof (bv_unsigned_in_range 8 (nth 18 FB (zb 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
rewrite (U_atom E 40 (fb FB 18)) by (try apply (HF 40%nat); unfold fb; lia). rewrite cs_nth_fld by lia. cbn [Nat.add]. unfold fb, zb. lia.
- cbn [cs_sum]. rewrite U_SAlu, (IH ltac:(lia)). cbn [zalu_raw].
pose proof (bv_unsigned_in_range 8 (nth (18 + S k) FB (zb 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
rewrite (U_atom E (40 + S k) (fb FB (18 + S k))) by (try (rewrite (HF (40 + S k)%nat) by lia; f_equal; f_equal; lia); unfold fb; lia).
change (psum (fld FB 18 32) (S (S k))) with (psum (fld FB 18 32) (S k) + bv_unsigned (nth (S k) (fld FB 18 32) (Z_to_bv 8 0))).
rewrite cs_nth_fld by lia. pose proof (cs_psum_rng (fld FB 18 32) (S k)) as P. unfold fb, zb in *. apply zcanon_small. lia.
Qed.
Lemma cs_c_eq0 : forall E k v bb, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = bb -> (v =? 0) = bb.
Proof. intros E k v bb H R Hb. rewrite branch_eq_U, (U_atom E k v H R), U_lit in Hb by lia. exact Hb. Qed.
Lemma cs_c_ne0 : forall E k v bb, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = bb -> negb (v =? 0) = bb.
Proof. intros E k v bb H R Hb. rewrite branch_ne_U, (U_atom E k v H R), U_lit in Hb by lia. exact Hb. Qed.
Lemma cs_c_geu : forall E k v c bb, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SOff k 0)) (sv_denot E (SLit c)) = bb -> negb (v <? c) = bb.
Proof. intros E k v c bb H R Rc Hb. rewrite branch_geu_U, (U_atom E k v H R), U_lit in Hb by lia. exact Hb. Qed.
Lemma cs_c_ltu : forall E k v c bb, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff k 0)) (sv_denot E (SLit c)) = bb -> (v <? c) = bb.
Proof. intros E k v c bb H R Rc Hb. rewrite branch_ltu_U, (U_atom E k v H R), U_lit in Hb by lia. exact Hb. Qed.
Lemma cs_c_ltul : forall E k v c bb, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SLit c)) (sv_denot E (SOff k 0)) = bb -> (c <? v) = bb.
Proof. intros E k v c bb H R Rc Hb. rewrite branch_ltu_U, (U_atom E k v H R), U_lit in Hb by lia. exact Hb. Qed.
Lemma cs_c_geul : forall E k v c bb, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SLit c)) (sv_denot E (SOff k 0)) = bb -> negb (c <? v) = bb.
Proof. intros E k v c bb H R Rc Hb. rewrite branch_geu_U, (U_atom E k v H R), U_lit in Hb by lia. exact Hb. Qed.
Lemma cs_c_sx0 : forall E ch bb, ew E 37 = Z_to_bv 64 ch -> 0 <= ch < 2 ^ 32 ->
  branch_taken BC_NE (sv_denot E cs_sx) (sv_denot E (SLit 0)) = bb -> negb (zsx ch =? 0) = bb.
Proof. intros E ch bb H R Hb. rewrite branch_ne_U, (cs_U_sx E ch H R), U_lit in Hb by lia. exact Hb. Qed.
Lemma cs_c_sxmq : forall E ch len bb, ew E 37 = Z_to_bv 64 ch -> 0 <= ch < 2 ^ 32 -> ew E 12 = Z_to_bv 64 len -> 52 <= len <= 65535 ->
  branch_taken BC_NE (sv_denot E cs_sx) (sv_denot E cs_mq) = bb -> negb (zsx ch =? zmq len) = bb.
Proof. intros E ch len bb H R H12 R12 Hb. rewrite branch_ne_U, (cs_U_sx E ch H R), (cs_U_mq E len H12 R12) in Hb. exact Hb. Qed.
Lemma cs_c_rem : forall E len bb, ew E 12 = Z_to_bv 64 len -> 52 <= len <= 65535 ->
  branch_taken BC_NE (sv_denot E cs_rem) (sv_denot E (SLit 0)) = bb -> negb ((len - 52) mod 36 =? 0) = bb.
Proof.
intros E len bb H R Hb. rewrite branch_ne_U, (cs_U_rem E len H R), U_lit in Hb by lia. rewrite <- Hb. f_equal.
pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as M.
destruct (Z.eqb_spec ((len - 52) mod 36) 0) as [E0|E0]; symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; lia.
Qed.
Lemma cs_c_sxq : forall E ch len bb, ew E 37 = Z_to_bv 64 ch -> 0 <= ch < 2 ^ 32 -> ew E 12 = Z_to_bv 64 len -> 52 <= len <= 65535 ->
  branch_taken BC_GEU (sv_denot E cs_sx) (sv_denot E cs_q) = bb -> negb (zsx ch <? (len - 52) / 36) = bb.
Proof. intros E ch len bb H R H12 R12 Hb. rewrite branch_geu_U, (cs_U_sx E ch H R), (cs_U_q E len H12 R12) in Hb. exact Hb. Qed.
Lemma cs_U_sbit : forall E (FB : list byte), (forall n, (38 <= n < 72)%nat -> ew E n = Z_to_bv 64 (fb FB (n - 22))) ->
  U E (SAlu ALU_SLTU (SAlu ALU_AND (cs_sum 31) (SLit 255)) (SLit 1)) = if psum (fld FB 18 32) 32 mod 256 =? 0 then 1 else 0.
Proof.
intros E FB HF. rewrite U_SAlu, U_SAlu, (cs_U_sum E FB HF 31 ltac:(lia)), !U_SLit. cbn [zalu_raw].
change (zcanon 255) with (Z.ones 8). change (zcanon 1) with 1. rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
pose proof (Z.mod_pos_bound (psum (fld FB 18 32) 32) 256 ltac:(lia)) as M.
rewrite (zcanon_small (psum (fld FB 18 32) 32 mod 256)) by lia.
destruct (Z.eqb_spec (psum (fld FB 18 32) 32 mod 256) 0) as [E0|E0].
- rewrite E0. reflexivity.
- replace (psum (fld FB 18 32) 32 mod 256 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma cs_c_sum0 : forall E (FB : list byte) bb, (forall n, (38 <= n < 72)%nat -> ew E n = Z_to_bv 64 (fb FB (n - 22))) ->
  branch_taken BC_EQ (sv_denot E (cs_sb (SLit 0))) (sv_denot E (SLit 0)) = bb -> negb (psum (fld FB 18 32) 32 mod 256 =? 0) = bb.
Proof.
intros E FB bb HF Hb. rewrite <- Hb. rewrite branch_eq_U. unfold cs_sb. rewrite (U_SAlu E ALU_OR), (cs_U_sbit E FB HF), (U_SLit E 0). cbn [zalu_raw].
destruct (psum (fld FB 18 32) 32 mod 256 =? 0); vm_compute; reflexivity.
Qed.
Lemma cs_c_sum1 : forall E (FB : list byte) bb, (forall n, (38 <= n < 72)%nat -> ew E n = Z_to_bv 64 (fb FB (n - 22))) ->
  branch_taken BC_EQ (sv_denot E (cs_sb cs_fl)) (sv_denot E (SLit 0)) = bb ->
  (negb (fb FB 17 =? 0) && negb (psum (fld FB 18 32) 32 mod 256 =? 0)) = bb.
Proof.
intros E FB bb HF Hb. rewrite <- Hb. rewrite branch_eq_U. unfold cs_sb, cs_fl. rewrite (U_SAlu E ALU_OR), (cs_U_sbit E FB HF), (U_SAlu E ALU_SLTU (SOff 39 0)), (U_SLit E 0), (U_SLit E 1).
pose proof (bv_unsigned_in_range 8 (nth 17 FB (zb 0))) as Hb17. change (bv_modulus 8) with 256 in Hb17.
rewrite (U_atom E 39 (fb FB 17)) by (try (rewrite (HF 39%nat) by lia; reflexivity); unfold fb; lia). cbn [zalu_raw].
destruct (Z.eqb_spec (fb FB 17) 0) as [E0|E0].
- rewrite E0. destruct (psum (fld FB 18 32) 32 mod 256 =? 0); vm_compute; reflexivity.
- replace (fb FB 17 <? zcanon 1) with false by (symmetry; apply Z.ltb_ge; change (zcanon 1) with 1; unfold fb in *; lia).
destruct (psum (fld FB 18 32) 32 mod 256 =? 0); vm_compute; reflexivity.
Qed.
Definition cs_hide (P : Prop) : Prop := P.
Lemma cs_r_sx0 : forall st len ch, 0 <= ch < 2 ^ 32 -> cs_hide (st = 0 -> ch = geo len) -> st = 0 -> len < 52 -> zsx ch <> 0 -> False.
Proof.
unfold cs_hide. intros st len ch R H0 Hst Hl Hz. specialize (H0 Hst). unfold geo in H0.
replace (52 <=? len) with false in H0 by (symmetry; apply Z.leb_gt; lia). cbn [andb] in H0. subst ch. apply Hz. reflexivity.
Qed.
Lemma cs_r_sxmq : forall st len ch, 0 <= ch < 2 ^ 32 -> cs_hide (st = 0 -> ch = geo len) -> st = 0 -> 52 <= len <= 65535 ->
  zsx ch <> zmq len -> False.
Proof.
unfold cs_hide. intros st len ch R H0 Hst Hl Hz. specialize (H0 Hst). apply Hz. unfold zsx, zmq, geo in *.
replace (52 <=? len) with true in H0 by (symmetry; apply Z.leb_le; lia). cbn [andb] in H0.
pose proof (Z.div_mod (len - 52) 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (len - 52) 36 ltac:(lia)) as M.
destruct ((len - 52) mod 36 =? 0) eqn:Q.
- rewrite Z.mod_small in H0 by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). subst ch.
  replace ((len - 52) / 36 <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; apply Z.div_lt_upper_bound; lia). reflexivity.
- subst ch. reflexivity.
Qed.
Lemma cs_r_sxq : forall st len ch, 0 <= ch < 2 ^ 32 -> cs_hide (st <> 0 -> geo len <= ch) -> st <> 0 -> 52 <= len <= 65535 ->
  (len - 52) mod 36 = 0 -> zsx ch < (len - 52) / 36 -> False.
Proof.
unfold cs_hide. intros st len ch R H1 Hst Hl Hm Hz. specialize (H1 Hst). unfold geo in H1.
replace (52 <=? len) with true in H1 by (symmetry; apply Z.leb_le; lia). rewrite Hm in H1. cbn [andb Z.eqb] in H1.
rewrite Z.mod_small in H1 by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
unfold zsx in Hz. destruct (ch <? 2 ^ 31) eqn:Q; cbv beta iota in Hz; [apply Z.ltb_lt in Q | apply Z.ltb_ge in Q]; lia.
Qed.
Lemma cs_r_sum0 : forall (FB : list byte), cs_hide ((fb FB 16 = 0 /\ fb FB 17 = 0) \/ psum (fld FB 18 32) 32 mod 256 = 0) ->
  fb FB 16 <> 0 -> psum (fld FB 18 32) 32 mod 256 <> 0 -> False.
Proof. unfold cs_hide. tauto. Qed.
Lemma cs_r_sum1 : forall (FB : list byte), cs_hide ((fb FB 16 = 0 /\ fb FB 17 = 0) \/ psum (fld FB 18 32) 32 mod 256 = 0) ->
  fb FB 17 <> 0 -> psum (fld FB 18 32) 32 mod 256 <> 0 -> False.
Proof. unfold cs_hide. tauto. Qed.
Lemma cs_r_din : forall (G : list byte), cs_hide (fb G 12 = 0 \/ (fb G 12 = 1 /\ fb G 13 <= 40 /\ fb G 14 <= 40)) ->
  fb G 12 <> 0 -> 40 < fb G 13 -> False.
Proof. unfold cs_hide. lia. Qed.
Lemma cs_r_dout : forall (G : list byte), cs_hide (fb G 12 = 0 \/ (fb G 12 = 1 /\ fb G 13 <= 40 /\ fb G 14 <= 40)) ->
  fb G 12 <> 0 -> 41 <= fb G 14 -> False.
Proof. unfold cs_hide. lia. Qed.
Lemma cs_fsum_eq : forall FB, fsum FB = psum (fld FB 18 32) 32 mod 256.
Proof. intros FB. unfold fsum, blocksum. reflexivity. Qed.
Definition CBx : sv := SOff 32 0.
Definition CBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition cs_fchunks : list YP09.chunk := map (fun j => YP09.mkChunk (16 + Z.of_nat j) (CVal 1 (SOff (38 + j) 0))) (seq 0 34).
Definition cs_sregion : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 0
  [YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 12 (CVal 1 (SOff 34 0)); YP09.mkChunk 13 (CVal 1 (SOff 35 0));
   YP09.mkChunk 14 (CVal 1 (SOff 36 0)); YP09.mkChunk 20 (CVal 4 (SOff 37 0))].
Definition cs_fregion : YP09.region := YP09.mkRegion (Some 11%nat) 0 50 0 0 cs_fchunks.
Definition cs_regions : smem := [ stack_region 64; got_regionP; bcell_regionP 32; cs_sregion; cs_fregion ].
Definition cs_facts : facts := mkFacts ([ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 25) 2); (11%nat, mkAF 1 (2 ^ 47 - 51) 0);
  (12%nat, mkAF 50 65535 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 2 0); (34%nat, mkAF 0 1 0); (35%nat, mkAF 0 255 0);
  (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 4294967295 0) ] ++ map (fun j => ((38 + j)%nat, mkAF 0 255 0)) (seq 0 34)) [] [].
Definition ss_cs : sstate := mkSS AF_check_sighting sr_atoms cs_regions None cs_facts.
Definition cs_SH : list shent := [ mkSHE 10 0 24; mkSHE 11 0 50 ].
Definition cs_extra (G FB : list byte) : list word :=
  map (Z_to_bv 64) ([SHADOW_OFF; fu G 8 4; fb G 12; fb G 13; fb G 14; fu G 20 4] ++ map (fun j => fb FB (16 + j)) (seq 0 34)).
Definition ECS (regs : bvmap 5 word) (G FB : list byte) : env := Eimg (Ereg regs (cs_extra G FB)).
Lemma cs_getr8 : forall (regs : bvmap 5 word) v (r : bv 5), r <> 8%bv -> getr (regupd regs 8 v) r = getr regs r.
Proof. intros regs v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. exact (regupd_other regs 8 v r Hr). Qed.
Lemma cs_spZ8 : forall (regs : bvmap 5 word) v, spZ (regupd regs 8 v) = spZ regs.
Proof. intros regs v. unfold spZ. rewrite cs_getr8; [reflexivity|]. intros X. apply (f_equal bv_unsigned) in X. discriminate X. Qed.
Lemma cs_fb_rng : forall (L : list byte) k, 0 <= fb L k < 256.
Proof. intros L k. unfold fb. pose proof (bv_unsigned_in_range 8 (nth k L (zb 0))) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.
Lemma cs_fld_len : forall (L : list byte) k n, (k + n <= length L)%nat -> length (fld L k n) = n.
Proof. intros L k n H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.
Lemma cs_fld_all : forall (L : list byte), length L = 6%nat -> fld L 0 6 = L.
Proof. intros L H. unfold fld. cbn [skipn]. apply firstn_all2. lia. Qed.
Lemma cs_fu_rng : forall (L : list byte) k, (k + 4 <= length L)%nat -> 0 <= fu L k 4 < 2 ^ 32.
Proof.
intros L k H. unfold fu. pose proof (bytes_le_to_Z_bound (fld L k 4)) as H1. pose proof (bytes_le_to_Z_nonneg (fld L k 4)) as H0.
rewrite (cs_fld_len L k 4 H) in H1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in H1. lia.
Qed.
Lemma cs_nth_map : forall (L : list byte) j, (j < length L)%nat -> nth j (map bv_unsigned L) 0 = fb L j.
Proof.
intros L j Hj. unfold fb. rewrite (nth_indep (map bv_unsigned L) 0 (bv_unsigned (zb 0))) by (rewrite length_map; exact Hj). apply map_nth.
Qed.
Lemma cs_fb_val : forall H (m : word -> option byte) base (L : list byte) j, (j < length L)%nat ->
  garr8 SEGS (mrestrict H m) base (map bv_unsigned L) -> val_mem SEGS (mrestrict H m) (base + Z.of_nat j) 1 (fb L j).
Proof. intros H m base L j Hj G. rewrite <- (cs_nth_map L j Hj). exact (proj1 (G j ltac:(rewrite length_map; exact Hj))). Qed.
Lemma cs_fu_val : forall H (m : word -> option byte) base (L : list byte) k, (k + 4 <= length L)%nat ->
  garr8 SEGS (mrestrict H m) base (map bv_unsigned L) -> val_mem SEGS (mrestrict H m) (base + Z.of_nat k) 4 (fu L k 4).
Proof.
intros H m base L k Hk G kk Hkk.
assert (Hb : 0 <= fu L k 4 < 2 ^ (8 * Z.of_nat 4)) by (pose proof (cs_fu_rng L k Hk); change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
destruct (nth_error L (k + kk)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (base + Z.of_nat k + Z.of_nat kk) with (base + Z.of_nat (k + kk)) by lia.
rewrite (garr8_mbyte SEGS _ base _ (k + kk) G) by (rewrite length_map; lia). f_equal.
rewrite le_byte_small by first [lia | exact Hb].
assert (Hf : nth_error (fld L k 4) kk = Some b).
{ unfold fld. rewrite nth_error_firstn. destruct (Nat.ltb_spec kk 4); [|lia]. rewrite nth_error_skipn. exact Hb2. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hf) as Hv. change (bytes_le_to_Z (fld L k 4)) with (fu L k 4) in Hv.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. rewrite <- Hv.
rewrite (nth_indep _ 0 (bv_unsigned (zb 0))) by (rewrite length_map; lia). rewrite map_nth.
rewrite (nth_error_nth L (k + kk) (zb 0) Hb2). pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma cs_aview_g : forall H (m : word -> option byte) base (L : list byte) j, (j < length L)%nat ->
  garr8 SEGS (mrestrict H m) base (map bv_unsigned L) -> aview SEGS H m (base + Z.of_nat j) = Some (fb L j).
Proof.
intros H m base L j Hj G. unfold aview. rewrite (garr8_mbyte SEGS _ base _ j G) by (rewrite length_map; exact Hj).
rewrite (cs_nth_map L j Hj). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. apply cs_fb_rng.
Qed.
Lemma cs_cmp6 : forall H (m : word -> option byte) a b (A Bl : list byte) kb,
  (6 <= length A)%nat -> (kb + 6 <= length Bl)%nat ->
  garr8 SEGS (mrestrict H m) a (map bv_unsigned A) -> garr8 SEGS (mrestrict H m) b (map bv_unsigned Bl) ->
  ((forall i, 0 <= i < 6 -> aview SEGS H m (a + i) = aview SEGS H m (b + Z.of_nat kb + i)) <->
   bytes_eqb (fld A 0 6) (fld Bl kb 6) = true).
Proof.
intros H m a b A Bl kb LA LB GA GB.
assert (NA : forall i, (i < 6)%nat -> nth i (map bv_unsigned (fld A 0 6)) 0 = fb A i).
{ intros i Hi. rewrite (cs_nth_map (fld A 0 6) i) by (rewrite cs_fld_len; lia). unfold fb, fld. rewrite nth_firstn.
  destruct (Nat.ltb_spec i 6); [|lia]. rewrite nth_skipn. reflexivity. }
assert (NB : forall i, (i < 6)%nat -> nth i (map bv_unsigned (fld Bl kb 6)) 0 = fb Bl (kb + i)).
{ intros i Hi. rewrite (cs_nth_map (fld Bl kb 6) i) by (rewrite cs_fld_len; lia). unfold fb, fld. rewrite nth_firstn.
  destruct (Nat.ltb_spec i 6); [|lia]. rewrite nth_skipn. reflexivity. }
assert (VA : forall i, 0 <= i < 6 -> aview SEGS H m (a + i) = Some (fb A (Z.to_nat i))).
{ intros i Hi. replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. apply cs_aview_g; [lia | exact GA]. }
assert (VB : forall i, 0 <= i < 6 -> aview SEGS H m (b + Z.of_nat kb + i) = Some (fb Bl (kb + Z.to_nat i))).
{ intros i Hi. replace (b + Z.of_nat kb + i) with (b + Z.of_nat (kb + Z.to_nat i)) by lia. apply cs_aview_g; [lia | exact GB]. }
unfold bytes_eqb. destruct (list_eq_dec Z.eq_dec (map bv_unsigned (fld A 0 6)) (map bv_unsigned (fld Bl kb 6))) as [EQ|NE].
- split; [reflexivity|]. intros _ i Hi. rewrite (VA i Hi), (VB i Hi). f_equal.
  rewrite <- (NA (Z.to_nat i)), <- (NB (Z.to_nat i)) by lia. rewrite EQ. reflexivity.
- split; [|discriminate]. intros HE. exfalso. apply NE. apply (nth_ext _ _ 0 0).
  + rewrite !length_map, !cs_fld_len by lia. reflexivity.
  + intros n Hn. rewrite length_map, cs_fld_len in Hn by lia. rewrite (NA n Hn), (NB n Hn).
    pose proof (HE (Z.of_nat n) ltac:(lia)) as X. rewrite (VA (Z.of_nat n) ltac:(lia)), (VB (Z.of_nat n) ltac:(lia)) in X. rewrite !Nat2Z.id in X.
    injection X as X. exact X.
Qed.
Lemma cs_hull_sub : forall rd a n a' n', shadow_hull_vis rd a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> 0 < n' ->
  shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' HV Ha H1 H2 Hn s Hs. apply HV. unfold shadow_addr in *.
pose proof (Z.div_le_mono a a' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + a' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (a' + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.
Lemma cs_meq_frame : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> lo <= a < hi) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 lo hi HF Hw HM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs H m1 m2 (fun a => lo <= a < hi) HF Hw a Ha Hn). exact (HM a Ha Hn).
Qed.
Lemma cs_EF : forall regs G FB n, (38 <= n < 72)%nat -> ew (ECS regs G FB) n = Z_to_bv 64 (fb FB (n - 22)).
Proof.
intros regs G FB n Hn. unfold ECS. rewrite Eimg_low by (unfold A_TEXT; lia).
replace n with (32 + (6 + (n - 38)))%nat by lia. rewrite ew_Ereg_extra. unfold cs_extra.
rewrite map_app. rewrite app_nth2 by (cbn; lia). cbn [length map].
replace (6 + (n - 38) - 6)%nat with (n - 38)%nat by lia.
rewrite map_map.
transitivity (nth (n - 38) (map (fun j => Z_to_bv 64 (fb FB (16 + j))) (seq 0 34)) ((fun j => Z_to_bv 64 (fb FB (16 + j))) 0%nat)).
- apply nth_indep. rewrite length_map, length_seq. lia.
- rewrite (map_nth (fun j => Z_to_bv 64 (fb FB (16 + j))) (seq 0 34) 0%nat (n - 38)), seq_nth by lia. cbv beta; f_equal; f_equal; lia.
Qed.
Lemma cs_shok : forall (Ex : env) H (m : word -> option byte) s f,
  ew Ex 32 = Z_to_bv 64 SHADOW_OFF -> ew Ex 10 = Z_to_bv 64 s -> ew Ex 11 = Z_to_bv 64 f -> 0 <= s -> 0 <= f ->
  amem_range s 24 -> amem_range f 50 ->
  range_addressable (aview SEGS H m) SHADOW_OFF s 24 -> range_addressable (aview SEGS H m) SHADOW_OFF f 50 ->
  sh_ok SEGS CBx cs_SH Ex (mrestrict H m).
Proof.
intros Ex H m s f E32 E10 E11 Hs Hf AMs AMf RAs RAf. unfold sh_ok, cs_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS H m Ex CBx 10 s 24 s 0 24 RAs).
  + unfold U, CBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold amem_range, kLowMemEnd, kHighMemEnd in AMs; lia.
  + lia. + lia.
  + intros x Hx. revert AMs Hx. clear. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF. intros. lia.
- apply (shent_ok_of_range SEGS H m Ex CBx 11 f 50 f 0 50 RAf).
  + unfold U, CBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
  + unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold amem_range, kLowMemEnd, kHighMemEnd in AMf; lia.
  + lia. + lia.
  + intros x Hx. revert AMf Hx. clear. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF. intros. lia.
Qed.
Lemma cs_region_kept_refl : forall (Ex : env) (H : word -> bool) (m : word -> option byte) r, region_kept SEGS Ex (mrestrict H m) (mrestrict H m) r.
Proof. intros Ex H m r. split; [intros a Ha; reflexivity | intros a Ha Hw; exact Hw]. Qed.
Lemma cs_drop_conds : forall (fq : YK11.FPState) (Ex : env) ss ms,
  st_ok_pi (fx := fq) SEGS VAL Ex ss ms ->
  st_ok_pi (fx := fq) SEGS VAL Ex (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (mkFacts (f_atoms (ss_facts ss)) [] [])) ms.
Proof.
intros fq Ex ss ms HS. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & Ha & Hc & Hl).
unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts
  ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj Ha (conj I I)))))))))).
Qed.
Definition cs_tail_ss : sstate := mkSS 11360 [SLit 0; SOff 528 0; SOff 2 (-64); SOff 3 0; SOff 4 0; SOff 529 0; SOff 530 0; SOff 531 0; SOff 10 0; SOff 11 0; SExt true 32 (SOff 37 0); SOff 1024 0; SOff 1025 0; SOff 1026 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 539 0; SOff 12 0; SOff 14 0; SOff 13 0; SOff 32 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 540 0; SOff 541 0; SOff 542 0; SOff 543 0] [{| r_base := Some 2%nat; r_lo := -64; r_hi := 0; r_wlo := -64; r_whi := 0; r_chunks := [{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |}; {| r_base := Some 10%nat; r_lo := 0; r_hi := 24; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 8; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 12; YP09.c_val := CVal 1 (SOff 34 0) |}; {| c_off := 13; YP09.c_val := CVal 1 (SOff 35 0) |}; {| c_off := 14; YP09.c_val := CVal 1 (SOff 36 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 37 0) |}] |}; {| r_base := Some 11%nat; r_lo := 0; r_hi := 50; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 16; YP09.c_val := CVal 1 (SOff 38 0) |}; {| c_off := 17; YP09.c_val := CVal 1 (SOff 39 0) |}; {| c_off := 18; YP09.c_val := CVal 1 (SOff 40 0) |}; {| c_off := 19; YP09.c_val := CVal 1 (SOff 41 0) |}; {| c_off := 20; YP09.c_val := CVal 1 (SOff 42 0) |}; {| c_off := 21; YP09.c_val := CVal 1 (SOff 43 0) |}; {| c_off := 22; YP09.c_val := CVal 1 (SOff 44 0) |}; {| c_off := 23; YP09.c_val := CVal 1 (SOff 45 0) |}; {| c_off := 24; YP09.c_val := CVal 1 (SOff 46 0) |}; {| c_off := 25; YP09.c_val := CVal 1 (SOff 47 0) |}; {| c_off := 26; YP09.c_val := CVal 1 (SOff 48 0) |}; {| c_off := 27; YP09.c_val := CVal 1 (SOff 49 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 50 0) |}; {| c_off := 29; YP09.c_val := CVal 1 (SOff 51 0) |}; {| c_off := 30; YP09.c_val := CVal 1 (SOff 52 0) |}; {| c_off := 31; YP09.c_val := CVal 1 (SOff 53 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 54 0) |}; {| c_off := 33; YP09.c_val := CVal 1 (SOff 55 0) |}; {| c_off := 34; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 35; YP09.c_val := CVal 1 (SOff 57 0) |}; {| c_off := 36; YP09.c_val := CVal 1 (SOff 58 0) |}; {| c_off := 37; YP09.c_val := CVal 1 (SOff 59 0) |}; {| c_off := 38; YP09.c_val := CVal 1 (SOff 60 0) |}; {| c_off := 39; YP09.c_val := CVal 1 (SOff 61 0) |}; {| c_off := 40; YP09.c_val := CVal 1 (SOff 62 0) |}; {| c_off := 41; YP09.c_val := CVal 1 (SOff 63 0) |}; {| c_off := 42; YP09.c_val := CVal 1 (SOff 64 0) |}; {| c_off := 43; YP09.c_val := CVal 1 (SOff 65 0) |}; {| c_off := 44; YP09.c_val := CVal 1 (SOff 66 0) |}; {| c_off := 45; YP09.c_val := CVal 1 (SOff 67 0) |}; {| c_off := 46; YP09.c_val := CVal 1 (SOff 68 0) |}; {| c_off := 47; YP09.c_val := CVal 1 (SOff 69 0) |}; {| c_off := 48; YP09.c_val := CVal 1 (SOff 70 0) |}; {| c_off := 49; YP09.c_val := CVal 1 (SOff 71 0) |}] |}] None {| f_atoms := [(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 1; af_hi := 140737488355303; af_al2 := 2 |}); (11%nat, {| af_lo := 1; af_hi := 140737488355277; af_al2 := 0 |}); (12%nat, {| af_lo := 50; af_hi := 65535; af_al2 := 0 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (33%nat, {| af_lo := 0; af_hi := 2; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 1; af_al2 := 0 |}); (35%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (41%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (42%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (44%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (45%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (46%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (47%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (48%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (52%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (54%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (59%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (60%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (61%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (62%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (63%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (64%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (65%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (66%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (67%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (68%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (69%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (70%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (71%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |})]; f_conds := []; f_alias := [] |}.
Lemma cs_tail : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md
  (s f len u st : Z) (G FB : list byte) (Et : env) (ms2 : machine_state) (md2 : Model),
  getr regs 10 = w64 s -> getr regs 11 = w64 f -> getr regs 12 = w64 len ->
  getr regs 13 = w64 u -> getr regs 14 = w64 st ->
  0 < s -> 0 < f -> 50 <= len <= 65535 -> amem_range s 24 -> amem_range f 50 ->
  0 <= fu G 20 4 < 2 ^ 32 ->
  YK0s.ret_ok (getr regs 1) ->
  cs_hide (fb G 12 = 0 \/ (fb G 12 = 1 /\ fb G 13 <= 40 /\ fb G 14 <= 40)) ->
  cs_hide ((fb FB 16 = 0 /\ fb FB 17 = 0) \/ psum (fld FB 18 32) 32 mod 256 = 0) ->
  env_agree 512 (Eimg (Ereg regs (cs_extra G FB))) Et ->
  st_ok_pi (fx := fq) SEGS VAL Et cs_tail_ss (restrict (w_H W) ms2) ->
  sh_ok SEGS CBx cs_SH Et (mrestrict (w_H W) (ms_mem ms2)) ->
  ajournal SEGS B TCHECK_SIGHTING_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms2) md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_SIGHTING_STK <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) mem a) ->
  SRr SEGS W (mkCfg ms2 md2) (tcheck_sighting_post fq regs ly S W mem md).
Proof.
intros fq ly S W regs mem md s f len u st G FB Et ms2 md2 H10 H11 H12 H13 H14 Hs0 Hf0 Rlen16 AMs AMf Rf20 Hra HDC HE6 HAEt HS0 SHOK HJ MEQc.
pose proof (pa_segs_low) as Hsegs.
pose proof (cs_fb_rng G 12) as Rg12. pose proof (cs_fb_rng G 13) as Rg13. pose proof (cs_fb_rng G 14) as Rg14.
pose proof (cs_fb_rng FB 16) as Rb16. pose proof (cs_fb_rng FB 17) as Rb17.
remember Et as E eqn:HEeq.
pose proof (proj1 HAEt) as AGw. pose proof (proj2 HAEt) as AGd.
assert (HEI : img_env VAL A_LIM E) by (intros a Ha; rewrite (AGw a ltac:(clear -Ha; unfold A_TEXT, A_LIM in *; lia)); exact (Eimg_env (Ereg regs (cs_extra G FB)) a Ha)).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AGw 1%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AGw 2%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AGw 3%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AGw 4%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (rewrite (AGw 10%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 f) by (rewrite (AGw 11%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 len) by (rewrite (AGw 12%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 u) by (rewrite (AGw 13%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 st) by (rewrite (AGw 14%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (AGw 32%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (fb G 12)) by (rewrite (AGw 34%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (fb G 13)) by (rewrite (AGw 35%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (fb G 14)) by (rewrite (AGw 36%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (fu G 20 4)) by (rewrite (AGw 37%nat ltac:(lia)); rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (EF : forall n, (38 <= n < 72)%nat -> ew E n = Z_to_bv 64 (fb FB (n - 22))) by (intros n Hn; rewrite (AGw n ltac:(lia)); apply cs_EF; exact Hn).
assert (E38 : ew E 38 = Z_to_bv 64 (fb FB 16)) by exact (EF 38%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cs_extra G FB)) E) by (split; [intros k Hk; rewrite (AGw k ltac:(lia)); apply Eimg_low; unfold A_TEXT; lia | rewrite AGd; reflexivity]).
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)) as RET.
rename HS0 into HS.
assert (AG0 : forall k, (k < 512)%nat -> ew E k = ew E k) by (intros; reflexivity).
clear HEeq HAEt AGw AGd.
let cs_win AG := (idtac;
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros b wlo whi a Hin Ha; vm_compute in Hin;
repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; cbn [base_val] in Ha; repeat (progress (rewrite AG in Ha by lia)); rewrite ?Usp in Ha; unfold TCHECK_SIGHTING_STK, ESTACK; lia|]);
destruct Hin) in
let upd_meq := idtac;
lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : forall a, _ -> _ -> aview _ _ ?m1 a = aview _ _ mem a |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Eh k = ew E k |- _ => H end in
let MEQ2 := fresh "MEQ" in
pose proof (cs_meq_frame Eh rs (w_H W) mem m1 m2 (spZ regs - TCHECK_SIGHTING_STK) (spZ regs) HFr ltac:(cs_win AG) MEQ) as MEQ2;
clear MEQ
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end in
let rebase_env En :=
tryif is_var En then idtac else
lazymatch goal with AG : forall k, (k < 512)%nat -> ew ?Eo k = ew E k, HAE : env_agree 32 (Ereg regs (cs_extra G FB)) ?Eo |- _ =>
let E2 := fresh "Ec" in
set (E2 := En) in *;
let AG2 := fresh "AG" in let HAE2 := fresh "HAE" in
assert (AG2 : forall k, (k < 512)%nat -> ew E2 k = ew E k) by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
assert (HAE2 : env_agree 32 (Ereg regs (cs_extra G FB)) E2) by (split; [intros kk Hkk; rewrite AG2 by lia; try (rewrite <- (AG kk) by lia); exact (proj1 HAE kk Hkk) | subst E2; cbn [ed ewset havoc]; exact (proj2 HAE)]);
lazymatch Eo with
| E => idtac
| _ => repeat match goal with H : ew Eo ?kk = ?vv |- _ => let H2 := fresh "EV" in assert (H2 : ew E2 kk = vv) by (subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact H); clear H end
end;
clearbody E2; clear AG HAE;
repeat match goal with H : img_env _ _ ?Ex |- _ => lazymatch Ex with E2 => fail | _ => clear H end end
end in
let rebase := idtac;
lazymatch goal with
| HS : st_ok_pi _ _ ?En _ _ |- _ => rebase_env En
| HS : st_ok _ ?En _ _ |- _ => rebase_env En
end in
let awr := idtac; awr_ok_tac; first [exact Usp | lazymatch goal with AG : forall k, (k < 512)%nat -> ew ?Eo k = ew E k |- _ => repeat (progress (rewrite AG by lia)); exact Usp end] in
let norm := idtac; repeat match goal with
| H : negb _ = true |- _ => apply negb_true_iff in H
| H : negb _ = false |- _ => apply negb_false_iff in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
end in
let refute := idtac; norm; first
[ contradiction
| exact (cs_r_sum0 FB HE6 ltac:(assumption) ltac:(assumption))
| exact (cs_r_sum1 FB HE6 ltac:(assumption) ltac:(assumption))
| exact (cs_r_din G HDC ltac:(assumption) ltac:(assumption))
| exact (cs_r_dout G HDC ltac:(assumption) ltac:(assumption))
| match goal with |- ?g => idtac "TAILREFUTEFAIL" g end; fail ] in
let eqk AG k := lazymatch k with
| 12%nat => constr:(eq_trans (AG 12%nat ltac:(lia)) E12)
| 14%nat => constr:(eq_trans (AG 14%nat ltac:(lia)) E14)
| 34%nat => constr:(eq_trans (AG 34%nat ltac:(lia)) E34)
| 35%nat => constr:(eq_trans (AG 35%nat ltac:(lia)) E35)
| 36%nat => constr:(eq_trans (AG 36%nat ltac:(lia)) E36)
| 38%nat => constr:(eq_trans (AG 38%nat ltac:(lia)) E38)
end in
let conv := idtac;
lazymatch goal with
| Hc : branch_taken ?c (sv_denot ?Ex ?a) (sv_denot ?Ex ?b) = ?bb |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ex k = ew E k |- _ => H end in
lazymatch a with
| SAlu ALU_OR (SLit 0) _ => apply (cs_c_sum0 Ex FB bb (fun n Hn => eq_trans (AG n ltac:(lia)) (EF n Hn))) in Hc
| SAlu ALU_OR _ _ => apply (cs_c_sum1 Ex FB bb (fun n Hn => eq_trans (AG n ltac:(lia)) (EF n Hn))) in Hc
| SAlu ALU_SLL _ _ => apply (cs_c_rem Ex len bb (eq_trans (AG 12%nat ltac:(lia)) E12) ltac:(lia)) in Hc
| SExt _ _ _ =>
  lazymatch c with
  | BC_GEU => apply (cs_c_sxq Ex (fu G 20 4) len bb (eq_trans (AG 37%nat ltac:(lia)) E37) Rf20 (eq_trans (AG 12%nat ltac:(lia)) E12) ltac:(lia)) in Hc
  | BC_NE =>
    lazymatch b with
    | SLit _ => apply (cs_c_sx0 Ex (fu G 20 4) bb (eq_trans (AG 37%nat ltac:(lia)) E37) Rf20) in Hc
    | _ => apply (cs_c_sxmq Ex (fu G 20 4) len bb (eq_trans (AG 37%nat ltac:(lia)) E37) Rf20 (eq_trans (AG 12%nat ltac:(lia)) E12) ltac:(lia)) in Hc
    end
  end
| SOff ?k 0 =>
  let EQ := lazymatch goal with EVx : ew Ex k = Z_to_bv 64 _ |- _ => constr:(EVx) | _ => eqk AG k end in
  lazymatch b with SLit ?cv =>
  lazymatch c with
  | BC_EQ => apply (cs_c_eq0 Ex k _ bb EQ ltac:(lia)) in Hc
  | BC_NE => apply (cs_c_ne0 Ex k _ bb EQ ltac:(lia)) in Hc
  | BC_GEU => apply (cs_c_geu Ex k _ cv bb EQ ltac:(lia) ltac:(lia)) in Hc
  | BC_LTU => apply (cs_c_ltu Ex k _ cv bb EQ ltac:(lia) ltac:(lia)) in Hc
  end end
| SLit ?cv =>
  lazymatch b with SOff ?k 0 =>
  let EQ := eqk AG k in
  lazymatch c with
  | BC_LTU => apply (cs_c_ltul Ex k _ cv bb EQ ltac:(lia) ltac:(lia)) in Hc
  | BC_GEU => apply (cs_c_geul Ex k _ cv bb EQ ltac:(lia) ltac:(lia)) in Hc
  end end
end
end in
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ssx (restrict _ ?msc) |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ec k = ew E k |- _ => H end in
let HAEc := lazymatch goal with H : env_agree 32 (Ereg regs (cs_extra G FB)) Ec |- _ => H end in
let MEQ := lazymatch goal with H : forall a, _ -> _ -> aview _ _ (ms_mem msc) a = aview _ _ mem a |- _ => H | H : forall a, _ -> _ -> aview _ _ _ a = aview _ _ mem a |- _ => H end in
let R1 := fresh "R1" in
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold tcheck_sighting_post; apply apost_base_same_fx;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1; repeat (progress (rewrite AG by lia)); rewrite E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (cs_extra G FB) HS); [exact HAEc | vm_compute; reflexivity]|];
split; [apply Permutation_refl | exact MEQ]
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK CBspan; [awr |];
upd_meq; rebase;
lazymatch goal with
| HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => exfalso; refute
| HS' : st_ok_pi _ _ ?Ec ?ss _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx CBspan SH (start K Bx CBspan SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' CBspan; [conv; norm; go | conv; norm; go]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "TAILSTUCK" pc why; fail
end
end end in
go.
Qed.
Lemma cs_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch s f len (G FB : list byte),
  afn_pre SEGS B TCHECK_SIGHTING_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  getr regs 10 = w64 s -> getr regs 11 = w64 f -> getr regs 12 = w64 len ->
  0 < s -> s mod 4 = 0 -> 0 < f -> 50 <= len <= 65535 ->
  length G = 24%nat -> garr8 SEGS (mrestrict (w_H W) mem) s (map bv_unsigned G) ->
  length FB = 50%nat -> garr8 SEGS (mrestrict (w_H W) mem) f (map bv_unsigned FB) ->
  amem_range s 24 -> amem_range f 50 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s 24 -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF f 50 ->
  (s + 24 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= s) -> (f + 50 <= spZ regs - TCHECK_SIGHTING_STK \/ spZ regs <= f) ->
  off_img s 24 -> off_img f 50 -> (s + 24 <= f \/ f + 50 <= s) ->
  0 <= fu G 8 4 <= 2 -> 0 <= fb G 12 <= 1 ->
  st_ok_pi (fx := fq) SEGS VAL (ECS regs G FB) ss_cs
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_check_sighting)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CBx cs_SH (ECS regs G FB) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch s f len G FB HPRE H10 H11 H12 Hs0 Hs4 Hf0 Rlen LG GG LF GF AMs AMf RAs RAf DSs DSf OIs OIf Dsf Rrole Rhd.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite cs_spZ8 in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_SIGHTING_STK = 8256) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
unfold IMG_LO, IMG_TOP in HcellR, HgotR.
pose proof (cs_fu_rng G 8 ltac:(lia)) as Rf8. pose proof (cs_fu_rng G 20 ltac:(lia)) as Rf20.
pose proof (cs_fb_rng G 13) as Rg13. pose proof (cs_fb_rng G 14) as Rg14.
assert (Bs : 1 <= s <= 2 ^ 47 - 25) by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in AMs; lia).
assert (Bf : 1 <= f <= 2 ^ 47 - 51) by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in AMf; lia).
rewrite restrict_mkst_fx.
set (E := ECS regs G FB).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (cs_extra G FB)) k) by (intros k Hk; subst E; unfold ECS; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (fu G 8 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (fb G 12)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (fb G 13)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (fb G 14)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (fu G 20 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (EF : forall n, (38 <= n < 72)%nat -> ew E n = Z_to_bv 64 (fb FB (n - 22))) by (intros n Hn; subst E; apply cs_EF; exact Hn).
assert (E66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold ECS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold ECS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_cs. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cs_regions, stack_region, got_regionP, bcell_regionP, cs_sregion, cs_fregion.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1o) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
[cbn [sv_denot]; rewrite E66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E66) by (pose proof (pa_val_range (A_OBJ 66)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat s E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
-- apply (chunk_ok_val SEGS E _ s 8 4 (SOff 33 0) (fu G 8 4));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (cs_fu_val _ _ s G 8 ltac:(lia) GG)].
-- apply (chunk_ok_val SEGS E _ s 12 1 (SOff 34 0) (fb G 12));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (cs_fb_val _ _ s G 12 ltac:(lia) GG)].
-- apply (chunk_ok_val SEGS E _ s 13 1 (SOff 35 0) (fb G 13));
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (cs_fb_val _ _ s G 13 ltac:(lia) GG)].
-- apply (chunk_ok_val SEGS E _ s 14 1 (SOff 36 0) (fb G 14));
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (cs_fb_val _ _ s G 14 ltac:(lia) GG)].
-- apply (chunk_ok_val SEGS E _ s 20 4 (SOff 37 0) (fu G 20 4));
[cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (cs_fu_val _ _ s G 20 ltac:(lia) GG)].
* rewrite (VB 11%nat f E11) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold cs_fchunks. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
pose proof (cs_fb_rng FB (16 + j)) as Rj.
apply (chunk_ok_val SEGS E _ f (16 + Z.of_nat j) 1 (SOff (38 + j) 0) (fb FB (16 + j)));
[ cbn [sv_denot]; rewrite (EF (38 + j)%nat) by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; replace (38 + j - 22)%nat with (16 + j)%nat by lia; reflexivity
| change (2 ^ (8 * Z.of_N 1)) with 256; lia | zside |].
replace (f + (16 + Z.of_nat j)) with (f + Z.of_nat (16 + j)) by lia. exact (cs_fb_val _ _ f FB (16 + j) ltac:(lia) GF).
+ apply pairwise_disjoint_of_extents.
unfold cs_regions, stack_region, got_regionP, bcell_regionP, cs_sregion, cs_fregion, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat s E10) by lia. rewrite (VB 11%nat f E11) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1o) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR OIs OIf DSs DSf Dsf Bs Bf. clear. unfold off_img, IMG_LO, IMG_TOP in *. intros.
repeat split; lia.
+ unfold cs_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok app map seq Nat.add]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E12, E32, E33, E34, E35, E36, E37.
repeat (match goal with |- context [ew E ?n] => rewrite (EF n) by lia end).
cbn [Nat.sub].
repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 ?v)] => rewrite (unsigned_lit_small v) by (first [lia | unfold SHADOW_OFF; lia | match goal with |- context [fb ?L ?k] => pose proof (cs_fb_rng L k); lia end]) end).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end;
first [ assumption | lia | unfold SHADOW_OFF; lia | match goal with |- context [fb ?L ?k] => pose proof (cs_fb_rng L k); lia end
      | match goal with |- ?g => idtac "FACTFAIL" g; fail end ].
- exact (cs_shok E (w_H W) mem s f E32 E10 E11 ltac:(lia) ltac:(lia) AMs AMf RAs RAf).
Qed.
Theorem pb_check_sighting : tcheck_sighting_spec.
Proof.
unfold tcheck_sighting_spec.
intros fq ly S W regs mem md ch s f len u st G FB Ub HPRE HRO H10 H11 H12 H13 H14 Hs0 Hs4 Hs63 Hf0 Hf63 Hu0 Hu63 Rlen Rst Rlen16
  LG GG LF GF LU GU AMs AMf AMu RAs SHs RAf SHf RAu SHu DSs DSf OIs OIf Dsf DSu SF.
pose proof (pa_segs_low) as Hsegs.
destruct SF as (L50 & EQ1 & EQ2 & E4a & E4b & (_ & Hrole & Hdecl) & E6).
pose proof (cs_fu_rng G 8 ltac:(lia)) as Rf8. pose proof (cs_fu_rng G 20 ltac:(lia)) as Rf20.
pose proof (cs_fb_rng G 12) as Rg12. pose proof (cs_fb_rng G 13) as Rg13. pose proof (cs_fb_rng G 14) as Rg14.
pose proof (cs_fb_rng FB 16) as Rb16. pose proof (cs_fb_rng FB 17) as Rb17.
assert (Rrole : 0 <= fu G 8 4 <= 2) by (unfold s32 in Hrole; destruct (Z.ltb_spec (fu G 8 4) (2 ^ 31)); lia).
assert (Rhd : 0 <= fb G 12 <= 1) by lia.
destruct (cs_entry fq ly S W regs mem md ch s f len G FB HPRE H10 H11 H12 Hs0 Hs4 Hf0 ltac:(lia) LG GG LF GF AMs AMf RAs RAf DSs DSf OIs OIf Dsf Rrole Rhd)
  as [HS SHOK].
pose proof (ajournal_init SEGS B TCHECK_SIGHTING_STK [] ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch HPRE) as HJ.
rewrite cs_spZ8 in HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite cs_spZ8 in Hstk, Hpres.
assert (N1 : (1%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
assert (N3 : (3%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
assert (N4 : (4%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
unfold raZ in Hra4. rewrite (cs_getr8 regs _ 1 N1) in Hra, Hra4. rewrite (cs_getr8 regs _ 3 N3) in Hgp. rewrite (cs_getr8 regs _ 4 N4) in Htp.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_SIGHTING_STK = 8256) by reflexivity.
assert (HE4a : cs_hide (st = 0 -> fu G 20 4 = geo len)) by exact E4a.
assert (HE4b : cs_hide (st <> 0 -> geo len <= fu G 20 4)) by exact E4b.
assert (HDC : cs_hide (fb G 12 = 0 \/ (fb G 12 = 1 /\ fb G 13 <= 40 /\ fb G 14 <= 40))) by exact Hdecl.
assert (HE6 : cs_hide ((fb FB 16 = 0 /\ fb FB 17 = 0) \/ psum (fld FB 18 32) 32 mod 256 = 0)) by (unfold cs_hide; rewrite <- cs_fsum_eq; exact E6).
clear E4a E4b Hdecl E6 Dsf OIs OIf Hrole.
remember (ECS regs G FB) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ECS; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (cs_extra G FB)) k) by (intros k Hk; subst E; unfold ECS; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 f) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 u) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 st) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (fb G 12)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (fb G 13)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (fb G 14)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (fu G 20 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (EF : forall n, (38 <= n < 72)%nat -> ew E n = Z_to_bv 64 (fb FB (n - 22))) by (intros n Hn; subst E; apply cs_EF; exact Hn).
assert (E38 : ew E 38 = Z_to_bv 64 (fb FB 16)) by exact (EF 38%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cs_extra G FB)) E) by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear EL.
unfold cfg_at. change (w64 (BASE + AF_check_sighting)) with (Z_to_bv 64 (BASE + AF_check_sighting)).
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)) as RET.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
assert (AG0 : forall k, (k < 512)%nat -> ew E k = ew E k) by (intros; reflexivity).
assert (MEQ0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_SIGHTING_STK <= a < spZ regs) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
  by (intros; reflexivity).
let cs_win AG := (idtac;
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros b wlo whi a Hin Ha; vm_compute in Hin;
repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; cbn [base_val] in Ha; repeat (progress (rewrite AG in Ha by lia)); rewrite ?Usp in Ha; unfold TCHECK_SIGHTING_STK, ESTACK; lia|]);
destruct Hin) in
let upd_meq := idtac;
lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : forall a, _ -> _ -> aview _ _ ?m1 a = aview _ _ mem a |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Eh k = ew E k |- _ => H end in
let MEQ2 := fresh "MEQ" in
pose proof (cs_meq_frame Eh rs (w_H W) mem m1 m2 (spZ regs - TCHECK_SIGHTING_STK) (spZ regs) HFr ltac:(cs_win AG) MEQ) as MEQ2;
clear MEQ
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end in
let rebase_env En :=
tryif is_var En then idtac else
lazymatch goal with AG : forall k, (k < 512)%nat -> ew ?Eo k = ew E k, HAE : env_agree 32 (Ereg regs (cs_extra G FB)) ?Eo |- _ =>
let E2 := fresh "Ec" in
set (E2 := En) in *;
let AG2 := fresh "AG" in let HAE2 := fresh "HAE" in
assert (AG2 : forall k, (k < 512)%nat -> ew E2 k = ew E k) by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
assert (HAE2 : env_agree 32 (Ereg regs (cs_extra G FB)) E2) by (split; [intros kk Hkk; rewrite AG2 by lia; try (rewrite <- (AG kk) by lia); exact (proj1 HAE kk Hkk) | subst E2; cbn [ed ewset havoc]; exact (proj2 HAE)]);
lazymatch Eo with
| E => idtac
| _ => repeat match goal with H : ew Eo ?kk = ?vv |- _ => let H2 := fresh "EV" in assert (H2 : ew E2 kk = vv) by (subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact H); clear H end
end;
clearbody E2; clear AG HAE;
repeat match goal with H : img_env _ _ ?Ex |- _ => lazymatch Ex with E2 => fail | _ => clear H end end
end in
let rebase := idtac;
lazymatch goal with
| HS : st_ok_pi _ _ ?En _ _ |- _ => rebase_env En
| HS : st_ok _ ?En _ _ |- _ => rebase_env En
end in
let awr := idtac; awr_ok_tac; first [exact Usp | lazymatch goal with AG : forall k, (k < 512)%nat -> ew ?Eo k = ew E k |- _ => repeat (progress (rewrite AG by lia)); exact Usp end] in
let norm := idtac; repeat match goal with
| H : negb _ = true |- _ => apply negb_true_iff in H
| H : negb _ = false |- _ => apply negb_false_iff in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
end in
let refute := idtac; norm; first
[ contradiction
| exact (cs_r_sx0 st len (fu G 20 4) Rf20 HE4a ltac:(assumption) ltac:(assumption) ltac:(assumption))
| exact (cs_r_sxmq st len (fu G 20 4) Rf20 HE4a ltac:(assumption) ltac:(lia) ltac:(assumption))
| exact (cs_r_sxq st len (fu G 20 4) Rf20 HE4b ltac:(assumption) ltac:(lia) ltac:(assumption) ltac:(assumption))
| exact (cs_r_sum0 FB HE6 ltac:(assumption) ltac:(assumption))
| exact (cs_r_sum1 FB HE6 ltac:(assumption) ltac:(assumption))
| exact (cs_r_din G HDC ltac:(assumption) ltac:(assumption))
| exact (cs_r_dout G HDC ltac:(assumption) ltac:(assumption))
| match goal with |- ?g => idtac "REFUTEFAIL" g end; fail ] in
let eqk AG k := lazymatch k with
| 12%nat => constr:(eq_trans (AG 12%nat ltac:(lia)) E12)
| 14%nat => constr:(eq_trans (AG 14%nat ltac:(lia)) E14)
| 34%nat => constr:(eq_trans (AG 34%nat ltac:(lia)) E34)
| 35%nat => constr:(eq_trans (AG 35%nat ltac:(lia)) E35)
| 36%nat => constr:(eq_trans (AG 36%nat ltac:(lia)) E36)
| 38%nat => constr:(eq_trans (AG 38%nat ltac:(lia)) E38)
end in
let conv := idtac;
lazymatch goal with
| Hc : branch_taken ?c (sv_denot ?Ex ?a) (sv_denot ?Ex ?b) = ?bb |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ex k = ew E k |- _ => H end in
lazymatch a with
| SAlu ALU_OR (SLit 0) _ => apply (cs_c_sum0 Ex FB bb (fun n Hn => eq_trans (AG n ltac:(lia)) (EF n Hn))) in Hc
| SAlu ALU_OR _ _ => apply (cs_c_sum1 Ex FB bb (fun n Hn => eq_trans (AG n ltac:(lia)) (EF n Hn))) in Hc
| SAlu ALU_SLL _ _ => apply (cs_c_rem Ex len bb (eq_trans (AG 12%nat ltac:(lia)) E12) ltac:(lia)) in Hc
| SExt _ _ _ =>
  lazymatch c with
  | BC_GEU => apply (cs_c_sxq Ex (fu G 20 4) len bb (eq_trans (AG 37%nat ltac:(lia)) E37) Rf20 (eq_trans (AG 12%nat ltac:(lia)) E12) ltac:(lia)) in Hc
  | BC_NE =>
    lazymatch b with
    | SLit _ => apply (cs_c_sx0 Ex (fu G 20 4) bb (eq_trans (AG 37%nat ltac:(lia)) E37) Rf20) in Hc
    | _ => apply (cs_c_sxmq Ex (fu G 20 4) len bb (eq_trans (AG 37%nat ltac:(lia)) E37) Rf20 (eq_trans (AG 12%nat ltac:(lia)) E12) ltac:(lia)) in Hc
    end
  end
| SOff ?k 0 =>
  let EQ := lazymatch goal with EVx : ew Ex k = Z_to_bv 64 _ |- _ => constr:(EVx) | _ => eqk AG k end in
  lazymatch b with SLit ?cv =>
  lazymatch c with
  | BC_EQ => apply (cs_c_eq0 Ex k _ bb EQ ltac:(lia)) in Hc
  | BC_NE => apply (cs_c_ne0 Ex k _ bb EQ ltac:(lia)) in Hc
  | BC_GEU => apply (cs_c_geu Ex k _ cv bb EQ ltac:(lia) ltac:(lia)) in Hc
  | BC_LTU => apply (cs_c_ltu Ex k _ cv bb EQ ltac:(lia) ltac:(lia)) in Hc
  end end
| SLit ?cv =>
  lazymatch b with SOff ?k 0 =>
  let EQ := eqk AG k in
  lazymatch c with
  | BC_LTU => apply (cs_c_ltul Ex k _ cv bb EQ ltac:(lia) ltac:(lia)) in Hc
  | BC_GEU => apply (cs_c_geul Ex k _ cv bb EQ ltac:(lia) ltac:(lia)) in Hc
  end end
end
end in
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ssx (restrict _ ?msc) |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ec k = ew E k |- _ => H end in
let HAEc := lazymatch goal with H : env_agree 32 (Ereg regs (cs_extra G FB)) Ec |- _ => H end in
let MEQ := lazymatch goal with H : forall a, _ -> _ -> aview _ _ (ms_mem msc) a = aview _ _ mem a |- _ => H | H : forall a, _ -> _ -> aview _ _ _ a = aview _ _ mem a |- _ => H end in
let R1 := fresh "R1" in
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold tcheck_sighting_post; apply apost_base_same_fx;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1; repeat (progress (rewrite AG by lia)); rewrite E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (cs_extra G FB) HS); [exact HAEc | vm_compute; reflexivity]|];
split; [apply Permutation_refl | exact MEQ]
end in
let bcall Yb Yl ky GY kind := idtac;
lazymatch goal with HS : st_ok _ ?Ec ?ssc (restrict (w_H W) ?msX) |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ec k = ew E k |- _ => H end in
let HAEc := lazymatch goal with H : env_agree 32 (Ereg regs (cs_extra G FB)) Ec |- _ => H end in
let HEIc := lazymatch goal with H : img_env _ _ Ec |- _ => H end in
let MEQ := lazymatch goal with H : forall a, _ -> _ -> aview _ _ _ a = aview _ _ mem a |- _ => H end in
let rk := eval vm_compute in (match sr_get (ss_regs ssc) 1%bv with SOff _ z => z | _ => 0 end) in
let K := run_K_hi HS in
let K4 := eval vm_compute in (K + 4)%nat in
let idxs := lazymatch kind with 1%nat => constr:([0; 3; 4]%nat) | _ => constr:([0; 1; 2]%nat) end in
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
repeat (progress (rewrite AG in Ra0 by lia)); repeat (progress (rewrite AG in Ra1 by lia)); repeat (progress (rewrite AG in Qsp by lia));
repeat (progress (rewrite AG in Qgp by lia)); repeat (progress (rewrite AG in Qtp by lia));
rewrite ?E10 in Ra0; rewrite ?E11, ?E13 in Ra1; rewrite ?Usp in Qsp; rewrite ?E3 in Qgp; rewrite ?E4 in Qtp;
let HspU := fresh "HspU" in
assert (HspU : spZ (ms_regs msX) = spZ regs + -64) by (unfold spZ at 1; rewrite Qsp; apply unsigned_lit_small; lia);
pmkst HS;
eapply SRr_bind;
[ eapply (aj_bcmp_at (fx := fq) SEGS B LAWS Hsegs (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W (ms_regs msX) (ms_mem msX)
    TCHECK_SIGHTING_STK (spZ regs) [] ly S W mem md [] ly S _ 0 s (Yb + Z.of_nat ky) 6 (-64) (Z_to_bv 64 (BASE + rk)) HJ);
  [ rewrite Ra0; unfold w64; f_equal; rewrite ?unsigned_lit_small by lia; lia
  | rewrite Ra1; unfold w64; f_equal; rewrite ?unsigned_lit_small by lia; lia
  | exact Ra2
  | lia | lia | lia | lia | lia
  | exact HspU
  | reflexivity | lia | unfold TCHECK_SIGHTING_STK, ESTACK; lia
  | rewrite Qgp; exact Hgp
  | rewrite Qtp; exact Htp
  | exact Rra
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | let a := fresh in let Ha := fresh in intros a Ha; split;
    [ rewrite MEQ by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia);
      replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia; rewrite (cs_aview_g (w_H W) mem s G (Z.to_nat (a - s)) ltac:(lia) GG); discriminate
    | rewrite HspU; unfold ESTACK; lia ]
  | let a := fresh in let Ha := fresh in intros a Ha; split;
    [ rewrite MEQ by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia);
      replace a with (Yb + Z.of_nat (Z.to_nat (a - Yb))) by lia; rewrite (cs_aview_g (w_H W) mem Yb Yl (Z.to_nat (a - Yb)) ltac:(lia) GY); discriminate
    | rewrite HspU; unfold ESTACK; lia ]
  | let a := fresh in let Ha := fresh in intros a Ha; unfold ESTACK; lia
  | let a := fresh in let Ha := fresh in intros a Ha; unfold ESTACK; lia
  | unfold amem_range in *; lia
  | unfold amem_range in *; lia
  | apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TCHECK_SIGHTING_STK) (spZ regs));
    [ let x := fresh in let Hx := fresh in let Hn := fresh in intros x Hx Hn; apply MEQ; [exact Hx | exact Hn]
    | rewrite C2; unfold TCHECK_SIGHTING_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia
    | apply (range_addressable_sub _ _ s 24); [exact RAs | lia | lia] ]
  | intros _; apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TCHECK_SIGHTING_STK) (spZ regs));
    [ let x := fresh in let Hx := fresh in let Hn := fresh in intros x Hx Hn; apply MEQ; [exact Hx | exact Hn]
    | rewrite C2; unfold TCHECK_SIGHTING_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia | lia
    | apply (cs_hull_sub _ s 24); [exact SHs | lia | lia | lia | lia] ]
  | apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TCHECK_SIGHTING_STK) (spZ regs));
    [ let x := fresh in let Hx := fresh in let Hn := fresh in intros x Hx Hn; apply MEQ; [exact Hx | exact Hn]
    | rewrite C2; unfold TCHECK_SIGHTING_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia
    | first [ apply (range_addressable_sub _ _ f 50); [exact RAf | lia | lia] | apply (range_addressable_sub _ _ u 6); [exact RAu | lia | lia] ] ]
  | intros _; apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TCHECK_SIGHTING_STK) (spZ regs));
    [ let x := fresh in let Hx := fresh in let Hn := fresh in intros x Hx Hn; apply MEQ; [exact Hx | exact Hn]
    | rewrite C2; unfold TCHECK_SIGHTING_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia | lia
    | first [ apply (cs_hull_sub _ f 50); [exact SHf | lia | lia | lia | lia] | apply (cs_hull_sub _ u 6); [exact SHu | lia | lia | lia | lia] ] ] ]
| cbv beta;
  let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
  let v := fresh "v" in let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let Hv := fresh "Hv" in let Hcmp := fresh "Hcmp" in
  let Hfr2 := fresh "Hfr2" in let Hpres2 := fresh "Hpres2" in let HPP := fresh "HPP" in
  intros W2 c2 _ HPP; destruct HPP as (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2);
  let RV := fresh "RV" in let VZ := fresh "VZ" in
  assert (RV : 0 <= bv_unsigned v < 2 ^ 64) by (let X := fresh in pose proof (bv_unsigned_in_range 64 v) as X; change (bv_modulus 64) with (2 ^ 64) in X; exact X);
  lazymatch kind with
  | 1%nat =>
    assert (VZ : bv_unsigned v = 0);
    [ let Hz := fresh in
      assert (Hz : v = w64 0);
      [ apply (proj2 Hcmp); let i := fresh in let Hi := fresh in intros i Hi;
        rewrite !MEQ by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia);
        exact (proj2 (cs_cmp6 (w_H W) mem s f G FB 6 ltac:(lia) ltac:(lia) GG GF) EQ1 i Hi)
      | rewrite Hz; unfold w64; apply unsigned_lit_small; lia ]
    | ]
  | _ =>
    assert (VZ : bv_unsigned v <> 0);
    [ let Hz := fresh in let Hv0 := fresh in let X := fresh in intros Hz;
      assert (Hv0 : v = w64 0) by (apply bv_eq; rewrite Hz; unfold w64; rewrite unsigned_lit_small by lia; reflexivity);
      let Hv1 := fresh in pose proof (proj1 Hcmp Hv0) as Hv1;
      assert (X : bytes_eqb (fld G 0 6) (fld Ub 0 6) = true);
      [ apply (proj1 (cs_cmp6 (w_H W) mem s u G Ub 0 ltac:(lia) ltac:(lia) GG GU)); let i := fresh in let Hi := fresh in intros i Hi;
        rewrite <- !MEQ by (unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia); exact (Hv1 i Hi)
      | rewrite (cs_fld_all Ub LU) in X; rewrite X in EQ2; discriminate EQ2 ]
    | ]
  end;
  let MEQ2 := fresh "MEQ" in
  assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_SIGHTING_STK <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
  by (let a := fresh in let Ha := fresh in let Hn := fresh in intros a Ha Hn; rewrite Hfr2 by (unfold TCHECK_SIGHTING_STK, ESTACK in *; lia); apply MEQ; assumption);
  let RAs2 := fresh "RAs2" in let RAf2 := fresh "RAf2" in
  assert (RAs2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF s 24)
  by (apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2) (spZ regs - TCHECK_SIGHTING_STK) (spZ regs));
      [ let x := fresh in let Hx := fresh in let Hn := fresh in intros x Hx Hn; apply MEQ2; [exact Hx | exact Hn]
      | rewrite C2; unfold TCHECK_SIGHTING_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia | exact RAs ]);
  assert (RAf2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF f 50)
  by (apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2) (spZ regs - TCHECK_SIGHTING_STK) (spZ regs));
      [ let x := fresh in let Hx := fresh in let Hn := fresh in intros x Hx Hn; apply MEQ2; [exact Hx | exact Hn]
      | rewrite C2; unfold TCHECK_SIGHTING_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia | exact RAf ]);
  let HS2 := fresh "HS" in
  jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 idxs HS2;
  match type of HS2 with ?tt -> _ => let HRK := fresh in assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end;
  [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
    (eapply region_kept_aview;
    [ repeat (progress (rewrite AG by lia));
      first [ exact Usp | rewrite E10; apply unsigned_lit_small; lia | rewrite E11; apply unsigned_lit_small; lia ]
    | let a := fresh in let Ha := fresh in intros a Ha; apply Hfr2; unfold ESTACK; unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia
    | exact Hpres2 ])
  | clear HS; rewrite <- restrict_mkst_fx in HS2;
    lazymatch type of HS2 with st_ok_pi _ _ ?En _ _ =>
    let E2 := fresh "Ec" in
    set (E2 := En) in HS2;
    let HEI2 := fresh "HEI" in let AG2 := fresh "AG" in let HAE2 := fresh "HAE" in let EV := fresh "EV" in let SHOK2 := fresh "SHOK" in
    assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply img_env_havoc_hi; [exact HEIc | cbv; lia]);
    assert (AG2 : forall k, (k < 512)%nat -> ew E2 k = ew E k) by (intros kk Hkk; subst E2; rewrite ew_havoc_old by lia; apply AG; exact Hkk);
    assert (HAE2 : env_agree 32 (Ereg regs (cs_extra G FB)) E2) by (subst E2; apply env_agree_havoc_ge; [cbv; lia | exact HAEc]);
    assert (EV : ew E2 K4 = Z_to_bv 64 (bv_unsigned v))
      by (subst E2; change K4 with (K + 4)%nat; rewrite (ew_havoc_new Ec K _ 4 (Z_to_bv 64 0)) by (cbn; lia); rewrite Z_to_bv_bv_unsigned; exact Hv);
    clearbody E2;
    pose proof (cs_shok E2 (w_H W) mem2 s f (eq_trans (AG2 32%nat ltac:(lia)) E32) (eq_trans (AG2 10%nat ltac:(lia)) E10)
      (eq_trans (AG2 11%nat ltac:(lia)) E11) ltac:(lia) ltac:(lia) AMs AMf RAs2 RAf2) as SHOK2;
    clear AG HAEc HEIc MEQ Hcmp Hfr2 Hpres2 HP2 Hv Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp HspU RAs2 RAf2;
    repeat match goal with H : sh_ok _ _ _ ?Ex _ |- _ => lazymatch Ex with E2 => fail | _ => clear H end end;
    clear HJ; rename HJ2 into HJ
    end ] ]
end in
let call := idtac;
lazymatch goal with HS : st_ok _ ?Ec ?ssc (restrict (w_H W) ?msX) |- _ =>
lazymatch type of HS with
| context [DS___asan_handle_no_return] => exfalso; refute
| _ =>
  let a1sv := eval vm_compute in (sr_get (ss_regs ssc) 11%bv) in
  lazymatch a1sv with
  | SOff 11%nat 6 => bcall f FB 6%nat GF 1%nat
  | SOff 13%nat 0 => bcall u Ub 0%nat GU 2%nat
  end
end end in
let join := idtac;
lazymatch goal with HS' : st_ok_pi _ _ ?Ec ?ss (restrict (w_H W) ?msX), SHOK' : sh_ok _ _ _ _ _ |- _ =>
let AG := lazymatch goal with H : forall k, (k < 512)%nat -> ew Ec k = ew E k |- _ => H end in
let HAEc := lazymatch goal with H : env_agree 32 (Ereg regs (cs_extra G FB)) Ec |- _ => H end in
let MEQ := lazymatch goal with H : forall a, _ -> _ -> aview _ _ (ms_mem msX) a = aview _ _ mem a |- _ => H | H : forall a, _ -> _ -> aview _ _ _ a = aview _ _ mem a |- _ => H end in
let HSd := fresh "HSd" in
pose proof (cs_drop_conds fq Ec ss (restrict (w_H W) msX) HS') as HSd;
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in HSd;
pmkst HSd;
let HS2 := fresh "HS2" in
jafter_stretch_keep_hi HSd 1024%nat (ms_regs msX) (mrestrict (w_H W) (ms_mem msX)) [(11%bv : bv 5); (12%bv : bv 5); (13%bv : bv 5)] 11360 [0; 1; 2]%nat HS2;
specialize (HS2 ltac:(intros rr Hrr; reflexivity) ltac:(repeat apply Forall_cons; try apply Forall_nil; apply cs_region_kept_refl));
rewrite <- restrict_mkst_fx in HS2;
lazymatch type of HS2 with st_ok_pi _ _ ?EC2 _ _ =>
let RAsj := fresh "RAsj" in let RAfj := fresh "RAfj" in let SHOK2 := fresh "SHOK2" in
assert (RAsj : range_addressable (aview SEGS (w_H W) (ms_mem msX)) SHADOW_OFF s 24)
  by (apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TCHECK_SIGHTING_STK) (spZ regs));
      [ let x := fresh in let Hx := fresh in let Hn := fresh in intros x Hx Hn; apply MEQ; [exact Hx | exact Hn]
      | rewrite C2; unfold TCHECK_SIGHTING_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia | exact RAs ]);
assert (RAfj : range_addressable (aview SEGS (w_H W) (ms_mem msX)) SHADOW_OFF f 50)
  by (apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - TCHECK_SIGHTING_STK) (spZ regs));
      [ let x := fresh in let Hx := fresh in let Hn := fresh in intros x Hx Hn; apply MEQ; [exact Hx | exact Hn]
      | rewrite C2; unfold TCHECK_SIGHTING_STK, ESTACK; lia | lia | unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia | exact RAf ]);
pose proof (cs_shok EC2 (w_H W) (ms_mem msX) s f
  ltac:(rewrite ew_havoc_old by lia; rewrite (AG 32%nat ltac:(lia)); exact E32)
  ltac:(rewrite ew_havoc_old by lia; rewrite (AG 10%nat ltac:(lia)); exact E10)
  ltac:(rewrite ew_havoc_old by lia; rewrite (AG 11%nat ltac:(lia)); exact E11)
  ltac:(lia) ltac:(lia) AMs AMf RAsj RAfj) as SHOK2;
eapply (cs_tail fq ly S W regs mem md s f len u st G FB EC2 _ _
  H10 H11 H12 H13 H14 Hs0 Hf0 ltac:(lia) AMs AMf Rf20 Hra HDC HE6
  ltac:(split; [intros nn Hnn; rewrite ew_havoc_old by lia; rewrite (AG nn ltac:(lia)); rewrite HE; reflexivity | cbn [ed havoc]; rewrite (proj2 HAEc); reflexivity])
  HS2 SHOK2 HJ
  ltac:(let a := fresh in let Ha := fresh in let Hn := fresh in intros a Ha Hn; apply MEQ; [exact Ha | exact Hn]))
end
end in
let rec go := idtac;
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_to_tok RUNTO HS HJ SHOK CBspan 11360; [awr |];
upd_meq; rebase;
lazymatch goal with
| HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => call; go
| HS' : st_ok_pi _ _ ?Ec ?ss _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
let pc := eval vm_compute in (ss_pc ss) in
lazymatch pc with
| 11360 => join
| _ =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bx CBspan SH (start K Bx CBspan SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' CBspan; [conv; norm; go | conv; norm; go]
| _ => let p := eval vm_compute in (ss_pc ss) in idtac "MAINSTUCK" p why; fail
end
end
end end in
go.
Qed.

End h.
End f.
End d.

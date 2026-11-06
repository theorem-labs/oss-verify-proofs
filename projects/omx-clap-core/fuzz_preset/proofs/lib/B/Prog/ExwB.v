(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: ex_word (fuzz_preset.c :295-305) of fuzz_preset's asan-ubsan image B' (the #102 pin d663f82d,
   unstripped twin c90d4fa5), B_prog_sigma AS_ex_word = 0x848d4, 96 slots of B_prog_listing (neutral listing
   the internal file ex_word.fuzz_preset.asan-ubsan.s, read for the instruction stream
   only). RELOCATED from the old-pin walk origin/cold/h-pre-b3-exword-b 7974f60dc186 (image B f8f98a95 / 3b5e1a09):
   ex_word's 380 bytes are equal up to pc-relative fields on B and B', every pc-relative target naming the
   same symbol + offset, the address numerals moved by alreloc.py (sha256 c4338d099cfb8025, commit d99acc3edd97; audited against
   the internal file b-to-bprime.tsv 5a684bb2), and
   the ledger's two #102 cells (most own) added where the kit text has them.
   TWO THEOREMS, ONE WALK (ex_word_walk, over a memory invariant P):
   - ex_word_holds_B: this tree's tex_word_specX (cstr_ok's bound p + len + 1, PRH_Base.v:1872; the + 8 bound is the kit decff67d721f's, lib/A/PRH_FnEx.v blob
     45ddb7a7d5ae, PRH_Base.v blob 3004a98fe2d9), verbatim, no extra premise. Its post is the m-form fpostWm (the
     memnorm keep) with S' = S; P := (memnorm mem -> memnorm _)
     (YSRrMemnorm.v srr_inv_laws_imp of srr_inv_laws_memnorm_k), the calls through YGcallMxmn.v's aj_strlen_at_xrom
     and aj_bcmp_at_xm (the keep as their last conjunct).
   - ex_word_holds_B_bounded: the pre-04388d628fb text with the range premise of v (ExwB_Stmt.v tex_word_specX_vr; why:
     the internal file specX-obstacle.md), kept while ex_value's EHW cites it; P := True, the calls through YGcallMxmn.v's
     aj_strlen_at_xro and YGcallMx.v's aj_bcmp_at_x.
   RUNNER: YC1fPx's paj_run_x_inv / paj_run_tok_x_inv over YCbqG's ajournal_x (journal from
   YCbqGcallW.ajournal_x_init_W, the caller window d), the listing form (PI := PI_prog_B); the two runtime calls at
   B 0x84920 (`__wrap_strlen (word)`, the strlen text with the read-only premise arodata_okP: rom_view cannot be met
   at image B) and B 0x84974 (`__wrap_bcmp (in->p, word, len)`), each through the rule shape ew_strlen_rule /
   ew_bcmp_rule (the engine rule with the keep read through P). Journal-free helpers: ex_ws_x.v's exw_* lemmas (the
   B' ex_ws walk int102 carries, h-rw-pre-7 bp-ex_ws, blob 1da1e4be3773).
   THE SIX REPORT SITES (B' pcs from the neutral listing above; prh_img_B's pi_err_sites F_ex_word lists the five calls,
   the sixth is the UBSan `unimp`) are refuted, each by a named lemma:
   - B 0x84a18 `unimp` (UBSan): entry 0x84928 `bnez (q & 7)` and entry 0x84984 `bnez (v & 7)` are decided not taken
     by the run from the alignment facts of atoms 10 (q) and 13 (v) that ew_entry proves; entry 0x849c0
     `bltu p + len < p` is refuted by ew_site_unimp_ovf; entry 0x849d0 `beqz ((p != 0) ^ (p + len == 0))` is decided
     not taken by the run from atom 33's fact p >= 4096 (ew_entry).
   - B 0x84a28 errpath_load4 (FORM B): the entry edge 0x84994 `bnez` (v's shadow byte s) is followed when s <> 0;
     the in-block branch 0x84a20 `blt 3, s` is then taken by range_addressable v 4 at v + 3 (s = 0 \/ 3 < s < 8):
     ew_site_load4.
   - B 0x84a38 errpath_store4, 0x84a3c / 0x84a44 errpath_load8, 0x84a4c errpath_store8 (FORM A): q + 32's, q + 8's
     and q's shadow is 0 (the real stack, AR_laws_x alx_zshadow_byte): ew_site_q_shadow gives the covered shadow entry
     [q, q + 40) of every run, so the entry edges 0x849b0 / 0x84940 / 0x84950 / 0x849d8 are not taken.
   v's shadow byte is read through a one-byte region at an atom equal to (v >> 3) + 0x7fff8000 (an alias fact of the
   symbolic state), not through the token rule: the slow block at 0x84a1c has no `andi` (the alignment check's a0 is
   reused), so YCbn.v's slow_block does not match it.
   Numerals: 80 (LENGTH: frame, `addi sp,sp,-80`); 8272 (DERIVED: STK_ex_word at prh_img_B, checked by vm_compute);
   12808 (DERIVED: B_prog_sigma AS_ex_word - B_prog_base, slot 3202 of PAImg_prog's B_entry_ex_word); 0x7fff8000
   (DERIVED: SHADOW_OFF); 0x7fff7f800000 (DERIVED: CEIL_MIN, YM05.v:11, the lower bound of the RunCeil field
   YM05.alloc_ceiling by alloc_ceiling_value; not YK06's constant); 3, 7, 8, 32, 36, 40 (LENGTH / WORD: shift, mask,
   struct ex offsets); 2 ^ 32, 2 ^ 44, 2 ^ 46, 2 ^ 47, 2 ^ 63, 2 ^ 64 (LENGTH: widths and address-space bounds); atom
   numbers 32-41, 42, 46, 58, 62 (DERIVED: the engine's numbering; a0 is CLOB's 5th entry). Two ADDRESS literals, each
   checked by vm_compute against the listing: 0xa2850 = VAL (A_OBJ 0) (the GOT word) and 0xab6f8 = VAL (A_OBJ 12) (the
   shadow-offset cell); the pcs in comments are B' pcs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ex_ws_x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExwB_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).

(* ---- the symbolic states (listing form: pcs are offsets from the listing base) ---- *)
Definition EW_PC : Z := B_prog_sigma AS_ex_word - B_prog_base.
Definition EW_BX : sv := SOff 32 0.
Definition EW_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* in->p and in->end, read-only until the stores: the 16 bytes at q *)
Definition EW_QR : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
(* the cells the two stores write, swapped in for EW_QR (and v's regions) before the stores: in->p (8 bytes at q) and
   in->differs (4 bytes at q + 32, with its entry bytes) *)
Definition EW_QW : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 8 [].
Definition EW_DW : YP09.region :=
  YP09.mkRegion (Some 10%nat) 32 36 32 36
    [YP09.mkChunk 32 (CVal 1 (SOff 38 0)); YP09.mkChunk 33 (CVal 1 (SOff 39 0));
     YP09.mkChunk 34 (CVal 1 (SOff 40 0)); YP09.mkChunk 35 (CVal 1 (SOff 41 0))].
Definition ew_regions : smem := [stack_region 80; got_regionP; bcell_regionP 32; EW_QR].
Definition EW_CEIL : Z := 0x7fffff800000.  (* CEIL_MAX (YM05.v:12): alloc_ceiling's upper bound *)
Definition ew_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3);
           (11%nat, mkAF 4096 EW_CEIL 0); (12%nat, mkAF 0 2 0); (13%nat, mkAF 0 (2 ^ 47 - 8) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 EW_CEIL 0); (34%nat, mkAF 4096 EW_CEIL 0)] [] [].
Definition ss_ew : sstate := mkSS EW_PC sr_atoms ew_regions None ew_facts.
Definition ew_SH : list shent := [mkSHE 10 0 40].
(* v's shadow byte and v->type (added in the v <> 0 arm), and the alias that names the shadow address *)
Definition EW_SHR : YP09.region := YP09.mkRegion (Some 37%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition EW_VR : YP09.region := YP09.mkRegion (Some 13%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))].
Definition EW_ALIAS : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 13 0) (SLit 3)) (SOff 32 0), SOff 37 0).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ew_pc_val : BASE + EW_PC = B_prog_sigma AS_ex_word.
Proof. vm_compute. reflexivity. Qed.
Lemma ew_stk_val : @STK_ex_word prh_img_B = 8272.
Proof. vm_compute. reflexivity. Qed.
Lemma ew_ceil : 0x7fff7f800000 <= alloc_ceiling <= EW_CEIL.
Proof. pose proof alloc_ceiling_value as [H _]. unfold EW_CEIL. lia. Qed.

(* ---- journal-free helpers ---- *)
Lemma ew_w64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Lemma ew_aview_garr8 : forall (W : world SEGS) m p l j, garr8 SEGS (mrestrict (w_H W) m) p l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.

Lemma ew_byte_present : forall H (m : word -> option byte) a,
  apresent H m a -> exists v, 0 <= v < 256 /\ val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a [Hh [c Hc]]. exists (bv_unsigned c).
pose proof (bv_unsigned_in_range 8 c) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [exact Hr|]. intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
unfold mbyte, mrestrict. rewrite Hh, Hc. f_equal.
rewrite (le_byte_small (bv_unsigned c) 1 0) by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma ew_val1_of_aview : forall H (m : word -> option byte) a z,
  aview SEGS H m a = Some z -> val_mem SEGS (mrestrict H m) a 1 z /\ 0 <= z < 256.
Proof.
intros H m a z Ha. unfold aview in Ha.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; cbn [option_map] in Ha; [|discriminate].
injection Ha as <-. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr]. intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r. rewrite Hb. f_equal.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* two memories that hold the same value at [a, a + n) agree there *)
Lemma ew_vm_same : forall H (m m' : word -> option byte) a n v,
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v ->
  forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x.
Proof.
intros H m m' a n v V V' x Hx. unfold aview. f_equal.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (V (Z.to_nat (x - a)) ltac:(lia)), (V' (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.

Lemma ew_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
  by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* the byte lists the bcmp text compares: equal views on [0, n) are equal lists *)
Lemma ew_lists_eq : forall (a b : list Z) n,
  length a = n -> length b = n ->
  (forall i, (i < n)%nat -> nth i a 0 = nth i b 0) -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] n Ha Hb H; cbn in Ha, Hb; subst n; try discriminate; [reflexivity|].
injection Hb as Hb. f_equal; [exact (H 0%nat ltac:(lia))|].
apply (IH b (length a) eq_refl ltac:(lia)). intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma ew_U_sub : forall E n m p e, ew E n = Z_to_bv 64 p -> ew E m = Z_to_bv 64 e -> 0 <= p <= e -> e < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit (-1))) (SOff m 0)) = e - p.
Proof.
intros E n m p e Hn Hm Hp He. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n p Hn), (U_atom E m e Hm), U_SLit by lia. unfold zcanon, M64.
rewrite Z.add_mod_idemp_l by lia. change (-1 mod 2 ^ 64) with (2 ^ 64 - 1).
replace (p * (2 ^ 64 - 1) + e) with ((e - p) + p * 2 ^ 64) by ring. rewrite Z.mod_add by lia.
apply Z.mod_small. lia.
Qed.
Lemma ew_U_add : forall E n m p l, ew E n = Z_to_bv 64 p -> ew E m = Z_to_bv 64 l -> 0 <= p -> 0 <= l -> p + l < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = p + l.
Proof.
intros E n m p l Hn Hm Hp Hl Hs. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n p Hn), (U_atom E m l Hm) by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma ew_hull_low : forall x n s0, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s0 < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s0 < 2 ^ 46.
Proof.
intros x n s0 H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
lia.
Qed.
Lemma ew_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* the C string's terminator through the strlen text (first_byte), from cstr *)
Lemma ew_fb_entry : forall (W : world SEGS) m p cs, garr8 SEGS (mrestrict (w_H W) m) p (cs ++ [0]) ->
  Forall (fun c => c <> 0) cs ->
  first_byte SEGS W m p (Z.of_nat (length cs) + 1) 0 (Z.of_nat (length cs)).
Proof.
intros W m p cs Hg Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) cs 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (ew_aview_garr8 W m p (cs ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _.
  rewrite (ew_aview_garr8 W m p (cs ++ [0]) (length cs) Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma ew_fb_kept : forall (W : world SEGS) m m' p n c k,
  (forall a, p <= a < p + n -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  first_byte SEGS W m p n c k -> first_byte SEGS W m' p n c k.
Proof.
intros W m m' p n c k HK (Hk & H1 & H2). split; [exact Hk|]. split.
- intros i Hi. rewrite HK by lia. exact (H1 i Hi).
- intros Hkn. rewrite HK by lia. exact (H2 Hkn).
Qed.

Lemma ew_nth_firstn : forall (l : list Z) n i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
induction l as [|a l IH]; intros [|n] [|i] H; cbn; try lia; try reflexivity. apply IH. lia.
Qed.
Lemma ew_nth_skipn : forall (l : list Z) k i, nth i (skipn k l) 0 = nth (k + i) l 0.
Proof. induction l as [|a l IH]; intros [|k] i; cbn; try reflexivity; [destruct i; reflexivity | apply IH]. Qed.
(* bcmp's answer as the hit of the text: the compared views are the text's and the word's bytes *)
Lemma ew_hit_iff : forall (A : Z -> option Z) x0 i0 (x : list Z) w (wl : list Z),
  (forall j, (j < length x)%nat -> A (x0 + Z.of_nat j) = Some (nth j x 0)) ->
  (forall j, (j < length wl)%nat -> A (w + Z.of_nat j) = Some (nth j wl 0)) ->
  0 <= i0 -> Z.of_nat (length wl) <= Z.of_nat (length x) - i0 ->
  ((forall i, 0 <= i < Z.of_nat (length wl) -> A (x0 + i0 + i) = A (w + i)) <->
   firstn (length wl) (skipn (Z.to_nat i0) x) = wl).
Proof.
intros A x0 i0 x w wl HX HW Hi0 Hl. split.
- intros H. apply (ew_lists_eq _ _ (length wl)); [rewrite length_firstn, length_skipn; lia | reflexivity |].
  intros i Hi. rewrite ew_nth_firstn by exact Hi. rewrite ew_nth_skipn.
  specialize (H (Z.of_nat i) ltac:(lia)).
  replace (x0 + i0 + Z.of_nat i) with (x0 + Z.of_nat (Z.to_nat i0 + i)) in H by lia.
  rewrite (HW i Hi) in H. rewrite (HX (Z.to_nat i0 + i)%nat) in H by lia. injection H as H. exact H.
- intros Heq i Hi.
  replace (x0 + i0 + i) with (x0 + Z.of_nat (Z.to_nat i0 + Z.to_nat i)) by lia.
  replace (w + i) with (w + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (HX (Z.to_nat i0 + Z.to_nat i)%nat) by lia. rewrite (HW (Z.to_nat i)) by lia. f_equal.
  rewrite <- Heq. rewrite ew_nth_firstn by lia. rewrite ew_nth_skipn. reflexivity.
Qed.

Lemma ew_denot_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* in->differs's four bytes read back as at entry *)
Lemma ew_d_same : forall H (m m' : word -> option byte) q d0 d1 d2 d3,
  val_mem SEGS (mrestrict H m) (q + 32) 1 d0 -> val_mem SEGS (mrestrict H m) (q + 33) 1 d1 ->
  val_mem SEGS (mrestrict H m) (q + 34) 1 d2 -> val_mem SEGS (mrestrict H m) (q + 35) 1 d3 ->
  val_mem SEGS (mrestrict H m') (q + 32) 1 d0 -> val_mem SEGS (mrestrict H m') (q + 33) 1 d1 ->
  val_mem SEGS (mrestrict H m') (q + 34) 1 d2 -> val_mem SEGS (mrestrict H m') (q + 35) 1 d3 ->
  forall z, q + 32 <= z < q + 32 + 4 -> aview SEGS H m' z = aview SEGS H m z.
Proof.
intros H m m' q d0 d1 d2 d3 V0 V1 V2 V3 V0' V1' V2' V3' z Hz.
assert (Hc : z = q + 32 \/ z = q + 33 \/ z = q + 34 \/ z = q + 35) by lia.
destruct Hc as [-> | [-> | [-> | ->]]];
  [exact (ew_vm_same H m m' _ 1 _ V0 V0' (q + 32) ltac:(cbn; lia)) | exact (ew_vm_same H m m' _ 1 _ V1 V1' (q + 33) ltac:(cbn; lia))
  | exact (ew_vm_same H m m' _ 1 _ V2 V2' (q + 34) ltac:(cbn; lia)) | exact (ew_vm_same H m m' _ 1 _ V3 V3' (q + 35) ltac:(cbn; lia))].
Qed.

Lemma ew_swrap_small : forall (w : N) z, 0 <= z < 2 ^ (Z.of_N w - 1) -> 0 < Z.of_N w -> bv_swrap w z = z.
Proof.
intros w z Hz Hw. unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
assert (E : 2 ^ Z.of_N w = 2 * 2 ^ (Z.of_N w - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
rewrite E. rewrite Z.mod_small; [lia|]. split; [|]; nia.
Qed.
(* `lb` of a byte below 128: its value *)
Lemma ew_U_sext8 : forall E n z, ew E n = Z_to_bv 64 z -> 0 <= z < 128 -> U E (SExt true 8 (SOff n 0)) = z.
Proof.
intros E n z H Hz. rewrite U_SExt, (U_atom E n z H) by lia. change (Z.of_N 8) with 8.
rewrite Z.mod_small by lia. rewrite ew_swrap_small by (cbn; lia). apply zcanon_id. unfold M64. lia.
Qed.
(* `lw` of v->type compared with ty (0..2): equal exactly when the 32-bit value is ty *)
Lemma ew_type_eqb : forall E n z ty, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 32 -> 0 <= ty <= 2 ->
  (U E (SExt true 32 (SOff n 0)) =? ty) = (z =? ty).
Proof.
intros E n z ty H Hz Hty. rewrite U_SExt, (U_atom E n z H) by lia. change (Z.of_N 32) with 32.
rewrite (Z.mod_small z) by lia.
destruct (Z_lt_le_dec z (2 ^ 31)) as [Hs|Hs].
- rewrite ew_swrap_small by (cbn; lia). rewrite zcanon_id by (unfold M64; lia). reflexivity.
- assert (Hw : bv_swrap 32 z = z - 2 ^ 32).
  { unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus.
    assert (Hm : forall h m, h = 2 ^ 31 -> m = 2 ^ 32 -> (z + h) mod m - h = z - 2 ^ 32)
      by (intros h m -> ->; rewrite <- (Z.mod_unique (z + 2 ^ 31) (2 ^ 32) 1 (z + 2 ^ 31 - 2 ^ 32)) by lia; lia).
    apply Hm; reflexivity. }
  rewrite Hw. unfold zcanon, M64.
  assert (Hm : (z - 2 ^ 32) mod 2 ^ 64 = z - 2 ^ 32 + 2 ^ 64) by (rewrite <- (Z.mod_unique (z - 2 ^ 32) (2 ^ 64) (-1) (z - 2 ^ 32 + 2 ^ 64)) by lia; reflexivity).
  rewrite Hm. destruct (Z.eqb_spec (z - 2 ^ 32 + 2 ^ 64) ty), (Z.eqb_spec z ty); lia.
Qed.
(* SITE B 0x84a28 (errpath_load4, FORM B): with v's shadow byte s <> 0 the entry edge 0x84994 is followed, and the
   in-block branch 0x84a20 `blt 3, s` is TAKEN: range_addressable v 4 at v + 3 gives s = 0 \/ 3 < s < 8 (the run
   reads `lb` of s as s itself: the atom's fact is 0 <= s <= 7) *)
Lemma ew_site_load4 : forall E n sb, ew E n = Z_to_bv 64 sb -> (sb = 0 \/ 3 < sb < 8) -> sb <> 0 ->
  branch_taken BC_LT (sv_denot E (SLit 3)) (sv_denot E (SOff n 0)) = true.
Proof.
intros E n sb H Hr Hn. change (branch_taken BC_LT (sv_denot E (SLit 3)) (sv_denot E (SOff n 0)))
  with (Sg E (SLit 3) <? Sg E (SOff n 0)).
rewrite !S_of_U, U_lit, (U_atom E n sb H) by lia. rewrite !ew_swrap_small by (cbn; lia). apply Z.ltb_lt. lia.
Qed.
(* SITE B 0x84a18 via entry B 0x849c0 (UBSan pointer overflow `bltu p + len < p`): not taken, no wrap *)
Lemma ew_site_unimp_ovf : forall E np nl p l, ew E np = Z_to_bv 64 p -> ew E nl = Z_to_bv 64 l -> 0 <= p -> 0 <= l ->
  p + l < 2 ^ 64 -> branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff np 0) (SOff nl 0))) (sv_denot E (SOff np 0)) = false.
Proof.
intros E np nl p l Hp Hl Hp0 Hl0 Hs. rewrite branch_ltu_U, (ew_U_add E np nl p l Hp Hl Hp0 Hl0 Hs), (U_atom E np p Hp) by lia.
apply Z.ltb_ge. lia.
Qed.

(* reshaping a listing-form state: drop regions, add an alias fact *)
Lemma ew_pi_sub : forall E ss ms rs, st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms rs HS Hs Hw. unfold st_ok_pi, abs_ss in *.
pose proof (st_ok_submem SEGS E _ ms rs HS Hs Hw) as H. destruct ss. exact H.
Qed.
Lemma ew_pi_alias : forall E ss ms a b, st_ok_pi SEGS VAL E ss ms -> sv_denot E a = sv_denot E b ->
  st_ok_pi SEGS VAL E (YP03.set_facts ss (mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((a, b) :: f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms a b HS Hab. unfold st_ok_pi, abs_ss in *.
pose proof (st_ok_facts_ok SEGS E _ ms HS) as (FA & FC & FL).
pose proof (st_ok_set_facts SEGS E _ ms (mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((a, b) :: f_alias (ss_facts ss))) HS
  (conj FA (conj FC (conj Hab FL)))) as H.
destruct ss. exact H.
Qed.
Ltac ew_drop HS idxs :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?E ?ss ?ms =>
    let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
    let HSd := fresh "HSd" in
    pose proof (ew_pi_sub E ss ms rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HSd;
    let ss' := eval vm_compute in (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) in
    change (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) with ss' in HSd;
    clear HS; rename HSd into HS
  end.
Ltac ew_norm HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?E ?ss ?ms =>
    let ss' := eval vm_compute in ss in change ss with ss' in HS end.

(* swap in the two written cells (EW_QW, EW_DW) over a state whose regions are exactly its stack frame:
   U10b / Uspb the bases, HPJ the journal's presence of the caller window, KQ the cells' entry view,
   Eds the d-byte atoms, V0-V3 the d bytes at entry *)
Ltac ew_addq HS U10b Uspb HPJ KQ Ed0 Ed1 Ed2 Ed3 V0 V1 V2 V3 :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?ms =>
    let H1 := fresh "HSq" in
    pose proof (st_ok_pi_add_region (PI := PI_prog_B) Ex ss ms EW_QW HS eq_refl) as H1;
    lazymatch type of H1 with ?A -> ?Bd -> _ =>
      assert (Ha_ : A);
      [ unfold region_ok, EW_QW; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
        rewrite U10b; split; [lia|]; split; [lia|]; split; [|constructor];
        intros o Ho; cbn [ms_mem restrict]; apply (apresent_writable SEGS); apply HPJ; lia
      | assert (Hb_ : Bd);
        [ apply all_disjoint_of_extents; cbn [ss_mem map]; unfold extent_of_region;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val EW_QW]; rewrite U10b, Uspb;
          cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia
        | specialize (H1 Ha_ Hb_); clear Ha_ Hb_ ] ] end;
    clear HS; rename H1 into HS; ew_norm HS
  end;
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?ms =>
    let H1 := fresh "HSq" in
    pose proof (st_ok_pi_add_region (PI := PI_prog_B) Ex ss ms EW_DW HS eq_refl) as H1;
    lazymatch type of H1 with ?A -> ?Bd -> _ =>
      assert (Ha_ : A);
      [ unfold region_ok, EW_DW; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
        rewrite U10b; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; cbn [ms_mem restrict]; apply (apresent_writable SEGS); apply HPJ; lia |];
        cbn [ms_mem restrict];
        repeat apply Forall_cons; try apply Forall_nil;
        [ eapply (chunk_ok_val SEGS Ex _ _ 32 1 (SOff 38 0) _); [cbn [sv_denot]; rewrite Ed0, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |]
        | eapply (chunk_ok_val SEGS Ex _ _ 33 1 (SOff 39 0) _); [cbn [sv_denot]; rewrite Ed1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |]
        | eapply (chunk_ok_val SEGS Ex _ _ 34 1 (SOff 40 0) _); [cbn [sv_denot]; rewrite Ed2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |]
        | eapply (chunk_ok_val SEGS Ex _ _ 35 1 (SOff 41 0) _); [cbn [sv_denot]; rewrite Ed3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |] ];
        (eapply (ex_ws_x.exw_val_kept rsegs (w_H _)); [intros z Hz; apply KQ; cbn in Hz; lia | first [exact V0 | exact V1 | exact V2 | exact V3]])
      | assert (Hb_ : Bd);
        [ apply all_disjoint_of_extents; cbn [ss_mem map]; unfold extent_of_region;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val EW_DW EW_QW]; rewrite ?U10b, ?Uspb;
          cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia
        | specialize (H1 Ha_ Hb_); clear Ha_ Hb_ ] ] end;
    clear HS; rename H1 into HS; ew_norm HS
  end.

(* at a return after the stores: the cells' values from the two written regions (EW_DW index 0, EW_QW index 1) *)
Ltac ew_cells HS U10b Eb33 Eb46 Eb38 Eb39 Eb40 Eb41 VQ VD0 VD1 VD2 VD3 :=
  let RD := fresh "RD" in let RQ := fresh "RQ" in
  pose proof (ex_ws_x.exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RD; cbn [ms_mem restrict] in RD;
  pose proof (ex_ws_x.exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ; cbn [ms_mem restrict] in RQ;
  first
  [ pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 0 8 (SAlu ALU_ADD (SOff 33 0) (SOff 46 0)) _ RQ U10b
      ltac:(left; reflexivity) (ew_denot_of_U _ _ _ (ew_U_add _ 33 46 _ _ Eb33 Eb46 ltac:(lia) ltac:(lia) ltac:(lia)))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VQ; rewrite Z.add_0_r in VQ
  | idtac ];
  pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 32 1 (SOff 38 0) _ RD U10b ltac:(left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite Eb38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VD0;
  pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 33 1 (SOff 39 0) _ RD U10b ltac:(right; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite Eb39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VD1;
  pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 34 1 (SOff 40 0) _ RD U10b ltac:(right; right; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite Eb40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VD2;
  pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 35 1 (SOff 41 0) _ RD U10b ltac:(right; right; right; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite Eb41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VD3;
  clear RD RQ.

(* ---- tactics: the write premise of a run, and the bytes a run keeps ---- *)
Ltac ew_awr RW :=
  lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply ex_ws_x.exw_awr_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth] in Ha; RW Ha;
      first [lia | left; lia | left; split; lia] | ]);
  apply awr_ok_nil.
Ltac ew_kept_of HFr Zs ev KP :=
  lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview rsegs H m' a = aview rsegs H m a);
  [ apply (ex_ws_x.exw_kept rsegs E rs H m m' Zs HFr); intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
    repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; cbv beta; lia|]);
    destruct Hin_
  | cbv beta in KP ]
  end.

(* ---- the walk ---- *)
Section w. Context {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the entry environment: registers, then SHADOW_OFF, in->p, in->end, v->type, v's shadow byte, v's shadow address,
   the four entry bytes of in->differs *)
Definition EW_E (regs : bvmap 5 word) (p e t s v d0 d1 d2 d3 : Z) : env :=
  @Eimg _ B_prog_listing PI_prog_B (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; p; e; t; s; SHADOW_OFF + v / 8; d0; d1; d2; d3])).
(* the inputs: three fields of ExvB_Stmt.v's EXV_HYP (the allocator laws eh_laws, the image binding eh_palib, the
   bcmp text eh_bcmp) and the strlen text, which EXV_HYP does not carry, in its read-only form (YGcallMxmn.v
   astrlen_realizes_xro, MARKED TEXT, owner c-libc-stdio; its strcmp twin is EXV_HYP's eh_strcmp) *)
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis PAL : PALib (PI := PI_prog_B) B.
Hypothesis STRLEN :
  YGcallMxmn.astrlen_realizes_xro rsegs B ARx B_prog_relro_lo B_prog_relro_hi (B_prog_sigma AS___wrap_strlen).
Hypothesis BCMP : abcmp_realizes_x rsegs B ARx (B_prog_sigma AS___wrap_bcmp).
(* ex_word_holds_B (kit 04388d628fb's m-form post) takes the same two texts WITH the memnorm keep as the last post
   conjunct: YGcallMxmn.v's astrlen_realizes_xrom (the strlen text above plus the keep; MARKED TEXT, owner
   c-libc-stdio) and abcmp_realizes_xm (YGcallMx.v's abcmp_realizes_x plus the keep) *)
Hypothesis STRLENm :
  YGcallMxmn.astrlen_realizes_xrom rsegs B ARx B_prog_relro_lo B_prog_relro_hi (B_prog_sigma AS___wrap_strlen).
Hypothesis BCMPm : YGcallMxmn.abcmp_realizes_xm rsegs B ARx (B_prog_sigma AS___wrap_bcmp).

(* the read-only view of a state whose image bytes are the entry's *)
Lemma ew_rod_kept : forall (W : world SEGS) m m',
  arodata_okP rsegs B_prog_relro_lo B_prog_relro_hi B (aview SEGS (w_H W) m) ->
  (forall a, 0 <= a < kLowMemEnd -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  arodata_okP rsegs B_prog_relro_lo B_prog_relro_hi B (aview SEGS (w_H W) m').
Proof.
intros W m m' H HK a Hro Hno Her.
assert (Hi : in_img rsegs a).
{ destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (B_prog_relro a Hr)]. }
pose proof (B_prog_segs_low a Hi). rewrite HK by lia. exact (H a Hro Hno Her).
Qed.

(* SITES B 0x84a38 (errpath_store4), 0x84a3c / 0x84a44 (errpath_load8), 0x84a4c (errpath_store8), FORM A: in->differs
   (q + 32), in->end (q + 8) and in->p (q) sit on the real stack above the entry sp, whose shadow bytes are 0 at every
   ARx state (AR_laws_x alx_zshadow_byte); [q, q + 40) is addressable, so the token run's shadow entry covers each
   check's granule, the load reads 0 and the entry edges 0x849b0 / 0x84940 / 0x84950 / 0x849d8 are not taken *)
Lemma ew_site_q_shadow : forall ly S Hp (W : world rsegs) mem md q, ARx ly S Hp W mem md -> q mod 8 = 0 ->
  ly_stk_lo ly <= q -> q + 36 <= ly_stk_hi ly -> range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF q 40.
Proof.
intros ly S Hp W mem md q HAR Hq8 Hlo Hhi z Hz. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
destruct (Z_lt_le_dec z (q + 32)) as [Hz1|Hz1].
- apply (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md z HAR). lia.
- replace (z / 8) with ((q + 32) / 8) by lia.
  apply (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md (q + 32) HAR). lia.
Qed.

Let HBgot := pal_got_shadow (PI := PI_prog_B) B PAL.
Let HBcell := pal_cell (PI := PI_prog_B) B PAL.

Lemma ew_entry : forall ly S Hp W regs mem md ch STK q w ty v t x0 i0 len s d0 d1 d2 d3,
  afn_pre_x rsegs B ARx STK ly S Hp W regs mem md ch -> 80 <= STK ->
  getr regs 10 = w64 q -> getr regs 11 = w64 w -> getr regs 12 = w64 ty -> getr regs 13 = w64 v ->
  4096 <= w <= EW_CEIL -> 0 <= ty <= 2 -> 0 <= v <= 2 ^ 47 - 8 -> v mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 (x0 + i0) -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 (x0 + len) ->
  4096 <= x0 + i0 <= EW_CEIL -> 4096 <= x0 + len <= EW_CEIL ->
  q mod 8 = 0 -> spZ regs <= q -> q + 40 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 40 ->
  st_ok_pi SEGS VAL (EW_E regs (x0 + i0) (x0 + len) t s v d0 d1 d2 d3) ss_ew
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + EW_PC)) mem (seg_rom SEGS))) /\
  sh_ok SEGS EW_BX ew_SH (EW_E regs (x0 + i0) (x0 + len) t s v d0 d1 d2 d3) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch STK q w ty v t x0 i0 len s d0 d1 d2 d3 HPRE HSTK H10 H11 H12 H13 Hw Hty Hv Hv8
  Vp Ve Hpi Hel Hq8 Hspq Hq47 HRAq.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
assert (Eo0v : VAL (A_OBJ 0) = 0xa2850) by (vm_compute; reflexivity).
assert (Eo12v : VAL (A_OBJ 12) = 0xab6f8) by (vm_compute; reflexivity).
unfold EW_CEIL in *.
set (E := EW_E regs (x0 + i0) (x0 + len) t s v d0 d1 d2 d3) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n =
  ew (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; x0 + i0; x0 + len; t; s; SHADOW_OFF + v / 8; d0; d1; d2; d3])) n)
  by (intros n Hn; subst E; unfold EW_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 w) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 ty) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (x0 + i0)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EW_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EW_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
clear EL.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some n) = z).
{ intros n z Hn Hz. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hz. }
assert (UA : forall n z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ew E n) = z).
{ intros n z Hn Hz. rewrite Hn. apply unsigned_lit_small. exact Hz. }
split.
- rewrite restrict_mkst_fx. unfold ss_ew. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ew_regions, stack_region, got_regionP, bcell_regionP, EW_QR.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat q E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ q 0 8 (SOff 33 0) (x0 + i0));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
         rewrite Z.add_0_r. exact Vp.
      -- apply (chunk_ok_val SEGS E _ q 8 8 (SOff 34 0) (x0 + len));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Ve].
  + apply pairwise_disjoint_of_extents. unfold ew_regions, stack_region, got_regionP, bcell_regionP, EW_QR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat q E10) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia.
    cbn [base_val]. rewrite Usp, Eo0v, Eo12v.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ew_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, (UA 10%nat q E10), (UA 11%nat w E11), (UA 12%nat ty E12), (UA 13%nat v E13), (UA 32%nat SHADOW_OFF E32),
      (UA 33%nat (x0 + i0) E33), (UA 34%nat (x0 + len) E34) by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, EW_CEIL. repeat split; lia.
- unfold sh_ok, ew_SH. constructor; [|constructor].
  assert (HBx : U E EW_BX = SHADOW_OFF) by (unfold EW_BX; rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia); reflexivity).
  apply (shent_ok_of_range SEGS (w_H W) mem E EW_BX 10 q 40 q 0 40 HRAq HBx); [rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* the return: from the walk's memory invariant P at the end memory, the journal at the end, the kept bytes and the
   result R, the caller-window post (S' = S: the run ends in the entry state) *)
Lemma ew_finish : forall (P : (word -> option byte) -> Prop) ly S Hp (W : world rsegs) regs mem md q d Lam peak cnt fail
  ran most own (regs' : bvmap 5 word) pc' mem' md' k (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
  P mem' ->
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ajournal_x (SK := SK) rsegs B (@prh_pst prh_img_B) ARx (8272 + d) (spZ regs + d) [(q, q + 8); (q + 32, q + 36)]
    ly S Hp W mem md [] ly S Hp W mem' md' k ->
  aregs_preserved regs regs' -> pc' = getr regs 1 ->
  alloc_ceiling + 8272 <= spZ regs -> spZ regs <= q -> spZ regs + d <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) -> ~ (q <= a < q + 8) -> ~ (q + 32 <= a < q + 36) ->
     aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
  R W regs' mem' ->
  fpostW (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK 8272 d [(q, q + 8); (q + 32, q + 36)]
    regs ly S Hp W mem md
    (fun ly' S' Hp' W' regs'' mem'' _ => ((room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\
       ablocks B ly' S' = ablocks B ly S /\
       prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly' S' Hp' W' mem'' Lam peak cnt fail ran
         most own /\
       R W' regs'' mem'') /\ P mem'')
    W (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md').
Proof.
intros P ly S Hp W regs mem md q d Lam peak cnt fail ran most own regs' pc' mem' md' k R HPm HAR HLED HJ HP Hpc Hsp Hq Hsd
  HK HR.
pose proof alloc_ceiling_value as [[CA CB] _].
subst pc'. unfold fpostW. exists ly, S, Hp, regs', mem', md', k.
split; [reflexivity|]. split; [exact HJ|].
split.
{ intros a Ha Hna. apply HK; [lia | lia | |]; intros Hin; apply Hna; [exists (q, q + 8) | exists (q + 32, q + 36)];
  (split; [cbn; tauto | cbn [fst snd]; lia]). }
split; [exact HP|]. split; [|exact HPm]. split; [exact (fun H => H)|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [|exact HR].
apply (ex_ws_x.exw_ledger_kept B ARx LAWS ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR); [|exact HLED].
intros a Ha. apply HK; lia.
Qed.

(* ---- the walk, ONCE, over a memory invariant P (YC80x.v srr_inv_laws) carried from the entry memory to every
   return: the runner segments by YC1fPx.v's paj_run_x_inv / paj_run_tok_x_inv, the two calls by the rule shapes below
   (P across the call), the branches and the return keep the state. ex_word_holds_B takes P := (memnorm mem ->
   memnorm _) (YSRrMemnorm.v srr_inv_laws_imp), the bounded theorem P := True. ---- *)
#[local] Abbreviation AJw := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx).
(* the strlen call rule with P across the call: YGcallMxmn.v aj_strlen_at_xro / aj_strlen_at_xrom (:1209 / :1329)
   at segs := SEGS, rlo / rhi := B's relro bounds, pc := __wrap_strlen, the keep conjunct read through P *)
Definition ew_strlen_rule (P : (word -> option byte) -> Prop) : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
AJw STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte SEGS W memT x (len + 1) 0 len ->
src_ok SEGS W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview SEGS (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
PresetRodata.arodata_okP SEGS B_prog_relro_lo B_prog_relro_hi B (aview SEGS (w_H W) memT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA AS___wrap_strlen)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
AJw STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(P memT -> P mem2)).
(* the bcmp call rule with P across the call: YGcallMx.v aj_bcmp_at_x / YGcallMxmn.v aj_bcmp_at_xm (:550) at
   pc := __wrap_bcmp, the keep conjunct read through P *)
Definition ew_bcmp_rule (P : (word -> option byte) -> Prop) : Prop :=
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
AJw STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok SEGS W regsT memT x n -> src_ok SEGS W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) y n) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA AS___wrap_bcmp)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
AJw STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) = aview SEGS (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(P memT -> P mem2)).
(* the walk's statement: kit 04388d628fb's tex_word_specX (PRH_FnEx.v blob d32e3229d5dc) premise for premise, plus
   P at the entry memory, and its post at fpostW with Q /\ P mem' (fpostWm is fpostW at fQmn mem Q = Q /\ the keep) *)
Definition ew_core (P : (word -> option byte) -> Prop) : Prop :=
  forall ly S Hp (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) md ch (q w ty v t x0 i0 d : Z)
    (wl x : list Z) Lam peak cnt fail ran most own,
  let len := Z.of_nat (length x) in
  let hit := Z.of_nat (length wl) <= len - i0 /\ firstn (length wl) (skipn (Z.to_nat i0) x) = wl in
  fpre (L := B_prog_listing) (PA := PI_prog_B) B ARx (@STK_ex_word prh_img_B) ly S Hp W regs mem md ch ->
  getr regs 10 = w64 q -> getr regs 11 = w64 w -> getr regs 12 = w64 ty -> getr regs 13 = w64 v ->
  cstr_ok (L := B_prog_listing) (PA := PI_prog_B) W mem w wl -> 0 <= ty <= 2 ->
  0 <= v /\ v + 4 <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 (x0 + i0) -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 (x0 + len) ->
  q mod 8 = 0 -> spZ regs <= q -> q + 36 <= spZ regs + d -> fwin (L := B_prog_listing) (PA := PI_prog_B) ly W regs mem d ->
  src_rd (L := B_prog_listing) (PA := PI_prog_B) W mem x0 x ->
  prhex_inblk B ly S Hp x0 len -> len <= 3 * 2 ^ 20 ->
  0 <= i0 <= len ->
  (v <> 0 -> val_mem SEGS (mrestrict (w_H W) mem) v 4 t /\ 0 <= t < 2 ^ 32 /\ v mod 8 = 0 /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 4 /\
     (v + 4 <= spZ regs - (@STK_ex_word prh_img_B) \/ spZ regs <= v)) ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  P mem ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_ex_word) regs mem md)
    (fpostW (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK (@STK_ex_word prh_img_B) d
       [(q, q + 8); (q + 32, q + 36)] regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' =>
       ((room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly' S' Hp' W' mem' Lam peak cnt fail ran
         most own /\
       ((hit /\ getr regs' 10 = w64 0 /\
         val_mem SEGS (mrestrict (w_H W') mem') q 8 (x0 + i0 + Z.of_nat (length wl)) /\
         ((v <> 0 /\ t <> ty /\ val_mem SEGS (mrestrict (w_H W') mem') (q + 32) 4 1) \/
          ((v = 0 \/ t = ty) /\ prhex_same (L := B_prog_listing) (PA := PI_prog_B) W mem W' mem' (q + 32) 4)))
        \/
        (~ hit /\ getr regs' 10 = w64 (-1) /\ prhex_same (L := B_prog_listing) (PA := PI_prog_B) W mem W' mem' q 8 /\
         prhex_same (L := B_prog_listing) (PA := PI_prog_B) W mem W' mem' (q + 32) 4))) /\ P mem')).

Section g.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Hypothesis STRLEN_G : ew_strlen_rule P.
Hypothesis BCMP_G : ew_bcmp_rule P.

(* the walk: entry to every return *)
Lemma ex_word_walk : ew_core P.
Proof.
unfold ew_core. intros ly S Hp W regs mem md ch q w ty v t x0 i0 d wl x Lam peak cnt fail ran most own. cbv zeta.
intros [HFN [HROD HTOP]] H10 H11 H12 H13 HCS Hty HVR0 Vp Ve Hq8 Hspq Hqd HWIN HSRC HINB Hlen3 Hi0 HV HLED HPM.
change (@STK_ex_word prh_img_B) with 8272 in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ew_ceil as (CL1 & CL2).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HSRC as (GT & Hx4 & Hxceil & Hxam & Hxra & Hxhull).
(* The batch kit (the internal file MIGRATION.md section 1: cstr_ok's + 8 RELAXED to w + wlen + 1 <= alloc_ceiling): the NUL's aligned word tail
   lies below the ceiling by the kit's PRH_Base.cstr_ok_tail_lt, not by lia from the ceiling conjunct *)
pose proof (fun a => cstr_ok_tail_lt W mem w wl a HCS) as Hwtl.
set (len := Z.of_nat (length x)) in *.
set (wlen := Z.of_nat (length wl)) in *.
destruct HCS as ((GW & Hnz) & Hw4 & Hwceil & Hw32 & Hwam8 & Hwra & Hwhull & Hwtail).
assert (Hsp46 : 2 ^ 46 <= spZ regs) by lia.
assert (Hq40 : q + 40 <= 2 ^ 47) by lia.
(* v: NULL, or a node in range (the added premise) *)
assert (Hvb : 0 <= v <= 2 ^ 47 - 8 /\ v mod 8 = 0).
{ destruct (Z.eq_dec v 0) as [->|Hv0]; [lia|]. destruct (HV Hv0) as (_ & _ & Hv8 & _). destruct HVR0. lia. }
(* v's shadow byte (the one byte of the granule [v, v + 8)), and what range_addressable v 4 says of it at v + 3 *)
assert (HS0 : exists sb, v <> 0 -> aview SEGS (w_H W) mem (SHADOW_OFF + v / 8) = Some sb /\ (sb = 0 \/ 3 < sb < 8)).
{ destruct (Z.eq_dec v 0) as [->|Hv0]; [exists 0; intros []; reflexivity|].
  destruct (HV Hv0) as (_ & _ & Hv8 & HRAv & _).
  destruct (HRAv (v + 3) ltac:(lia)) as (sb & Hs & Hok). exists sb. intros _.
  unfold shadow_of_addr in Hs. replace ((v + 3) / 8) with (v / 8) in Hs by lia. split; [exact Hs|].
  unfold saddr_ok in Hok. replace ((v + 3) mod 8) with 3 in Hok by lia. lia. }
destruct HS0 as (sb & HS0).
(* the four entry bytes of in->differs *)
assert (HQP : forall a, q <= a < q + 36 -> apresent (w_H W) mem a) by (intros a Ha; apply Hdpres; lia).
destruct (ew_byte_present _ _ (q + 32) (HQP (q + 32) ltac:(lia))) as (d0 & D0 & V0).
destruct (ew_byte_present _ _ (q + 33) (HQP (q + 33) ltac:(lia))) as (d1 & D1 & V1).
destruct (ew_byte_present _ _ (q + 34) (HQP (q + 34) ltac:(lia))) as (d2 & D2 & V2).
destruct (ew_byte_present _ _ (q + 35) (HQP (q + 35) ltac:(lia))) as (d3 & D3 & V3).
(* q's shadow: the real stack's per-byte zero shadow (sites 0x84a38 / 0x84a3c / 0x84a44 / 0x84a4c, FORM A) *)
pose proof (ew_site_q_shadow ly S Hp W mem md q HAR Hq8 ltac:(lia) ltac:(lia)) as HRAq.
(* the caller-window journal at entry *)
pose proof (YCbqGcallW.ajournal_x_init_W (SK := SK) rsegs B (@prh_pst prh_img_B) ARx 8272 d
  [(q, q + 8); (q + 32, q + 36)] ly S Hp W regs mem md ch HFN HWIN) as HJ.
destruct (ew_entry ly S Hp W regs mem md ch 8272 q w ty v t x0 i0 len sb d0 d1 d2 d3 HFN ltac:(lia) H10 H11 H12 H13
  ltac:(unfold EW_CEIL in *; lia) Hty ltac:(lia) ltac:(lia) Vp Ve ltac:(unfold EW_CEIL in *; lia)
  ltac:(unfold EW_CEIL in *; lia) Hq8 Hspq Hq40 HRAq) as [HS SHOK].
remember (EW_E regs (x0 + i0) (x0 + len) t sb v d0 d1 d2 d3) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EW_E; apply Eimg_env).
set (XT := map (Z_to_bv 64) [SHADOW_OFF; x0 + i0; x0 + len; t; sb; SHADOW_OFF + v / 8; d0; d1; d2; d3]) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs XT) n)
  by (intros n Hn; subst E; unfold EW_E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 w) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 ty) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (x0 + i0)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (x0 + len)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 sb) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (SHADOW_OFF + v / 8)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 d0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 d1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 d2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 d3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (HAE : env_agree 32 (Ereg regs XT) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B (@prh_pst prh_img_B) ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_B)).
pose (RET := paj_ret_at (PL := PL_prog_B) (PI := PI_prog_B)).
unfold cfg_at. change (w64 (SIGMA AS_ex_word)) with (Z_to_bv 64 (BASE + EW_PC)).
(* ---- run 1: the prologue, s8 = the shadow base, the strlen call (B 0x848d4 - 0x84920) ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
{ ew_awr ltac:(fun h => rewrite ?Usp, ?U10 in h). }
ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp in h) K1.
clear HF HG HFr.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (2%bv : bv 5) Rsp1. prreg HS (1%bv : bv 5) Rra1.
prreg HS (3%bv : bv 5) Rgp1. prreg HS (4%bv : bv 5) Rtp1.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (KT1 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply K1; lia).
(* ---- the strlen call (B 0x84920): a0 = word, NUL-terminated at word + wlen ---- *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (STRLEN_G W rT mT (8272 + d) (spZ regs + d) [(q, q + 8); (q + 32, q + 36)]
    ly S Hp W mem md [] ly S Hp dT 0 w wlen (-80 - d) _ HJ) end.
  - rewrite Ra0, E11. reflexivity.
  - lia.
  - lia.
  - exact Hw32.
  - lia.
  - unfold spZ at 1. rewrite Rsp1, Usp, unsigned_lit_small by lia. lia.
  - lia.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rgp1, E3. exact Hgp.
  - rewrite Rtp1, E4. exact Htp.
  - exact Rra1.
  - apply (ret_ok_codeptr_v (PI := PI_prog_B)); [lia | reflexivity].
  - apply (ew_fb_kept W mem); [intros a Ha; apply KT1; lia | exact (ew_fb_entry W mem w wl GW Hnz)].
  - intros a Ha. split; [|unfold spZ; rewrite Rsp1, Usp, unsigned_lit_small by lia; lia].
    rewrite KT1 by lia. replace a with (w + Z.of_nat (Z.to_nat (a - w))) by lia.
    rewrite (ew_aview_garr8 W mem w (wl ++ [0]) (Z.to_nat (a - w)) GW) by (rewrite length_app; cbn; lia). discriminate.
  - intros a Ha. lia.
  - exact Hwam8.
  - eapply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hwra].
    intros z Hz. pose proof (ew_shadow_low z ltac:(lia)). apply KT1. lia.
  - intros s0 Hs0. pose proof (ew_hull_low w (wlen + 1) s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs0).
    rewrite KT1 by lia. exact (Hwhull s0 Hs0).
  - intros a Ha. pose proof (Hwtl a Ha) as Hta. rewrite KT1 by lia. exact (Hwtail a Ha).
  - apply (ew_rod_kept W mem); [exact HROD | intros a Ha; apply KT1; lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hlen2 & Hfr2 & Hpres2 & HPM2).
specialize (HPM2 HPM). clear HPM. rename HPM2 into HPM.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2J & _).
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; rewrite Hes in Hfr2; rewrite Hfr2 by lia; apply K1; lia).
jafter_call_keep_pi HS 42%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 3]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|constructor; [|apply Forall_nil]].
  - split.
    + intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
      apply (mbyte_of_aview SEGS). rewrite Hes in Hfr2. apply Hfr2; lia.
    + intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
      apply (apresent_writable SEGS). apply Hpres2J. lia.
  - split.
    + intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite U10 in Ha.
      apply (mbyte_of_aview SEGS). rewrite Hes in Hfr2. apply Hfr2; lia.
    + intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 42 (map (getr regs2) CLOB)) as Es eqn:HEs in HSX.
assert (HEIs : img_env VAL A_LIM Es) by (rewrite HEs; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDs : forall n, (n < 42)%nat -> ew Es n = ew E n) by (intros n Hn; rewrite HEs; apply ew_havoc_old; exact Hn).
assert (Esa0 : ew Es 46 = w64 wlen) by (rewrite HEs, <- Hlen2; reflexivity).
assert (HAEs : env_agree 32 (Ereg regs XT) Es) by (rewrite HEs; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEs.
pose proof (st_ok_pi_add_fact (PI := PI_prog_B) Es _ _ 46%nat (mkAF 0 (2 ^ 32 - 2) 0) HSX) as HS2.
lazymatch type of HS2 with ?T -> st_ok_pi _ _ _ ?ssx _ =>
  assert (HF46 : T) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Esa0, ew_w64 by lia;
    change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia);
  specialize (HS2 HF46); clear HF46;
  let ss2 := eval vm_compute in ssx in change ssx with ss2 in HS2 end.
clear HSX HS HJ SHOK Ra0 Rsp1 Rra1 Rgp1 Rtp1 KT1 K1.
assert (SHOK2 : sh_ok SEGS EW_BX ew_SH Es (mrestrict (w_H W) mem2)).
{ unfold sh_ok, ew_SH. constructor; [|constructor].
  assert (Es32 : ew Es 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDs by lia; exact E32).
  assert (Es10 : ew Es 10 = Z_to_bv 64 q) by (rewrite OLDs by lia; exact E10).
  assert (HBx : U Es EW_BX = SHADOW_OFF) by (unfold EW_BX; rewrite (U_atom Es 32 SHADOW_OFF Es32) by (unfold SHADOW_OFF; lia); reflexivity).
  apply (shent_ok_of_range SEGS (w_H W) mem2 Es EW_BX 10 q 40 q 0 40); [| exact HBx | rewrite (U_atom Es 10 q Es10) by lia; reflexivity | lia | lia |].
  - apply (ex_ws_x.exw_ra_kept rsegs (w_H W) mem); [|exact HRAq]. intros z Hz. apply KA2; unfold shadow_of_addr, SHADOW_OFF; lia.
  - intros z Hz. unfold SHADOW_OFF. lia. }
rename HJ2 into HJ. rename HS2 into HS. rename SHOK2 into SHOK.
(* ---- run 2: the q alignment check (decided), q + 8's and q's shadow (covered), in->p, in->end, the room test ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
{ ew_awr ltac:(fun h => rewrite ?OLDs in h by lia; rewrite ?Usp, ?U10 in h). }
ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDs in h by lia; rewrite ?Usp in h) K2.
clear HF HG HFr.
assert (Es33 : ew Es 33 = Z_to_bv 64 (x0 + i0)) by (rewrite OLDs by lia; exact E33).
assert (Es34 : ew Es 34 = Z_to_bv 64 (x0 + len)) by (rewrite OLDs by lia; exact E34).
psrr_branch_tok RUN BR HS SHOK EW_SPAN.
- (* in->end - in->p < wlen: no room, return -1 *)
  rewrite branch_ltu_U, (ew_U_sub Es 33 34 (x0 + i0) (x0 + len) Es33 Es34), (U_atom Es 46 wlen Esa0) in Hc by lia.
  apply Z.ltb_lt in Hc.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
  { ew_awr ltac:(fun h => rewrite ?OLDs in h by lia; rewrite ?Usp, ?U10 in h). }
  ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDs in h by lia; rewrite ?Usp in h) K3.
  clear HF HG HFr.
  prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) Rra.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold YK0s.ret_ok in Hra.
  eapply (ew_finish P); [exact HPM|..].
  + exact HAR.
  + exact HLED.
  + apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
  + eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs XT HS); [exact HAEs | vm_compute; reflexivity].
  + rewrite Rra, OLDs, E1 by lia. exact Hra.
  + lia.
  + exact Hspq.
  + lia.
  + intros a Ha Hn _ _. rewrite K3, K2 by lia. exact (KA2 a Ha Hn).
  + right. split; [intros (Hh & _); lia|].
    split; [rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
    split; intros z Hz; (rewrite K3, K2, KA2 by lia; reflexivity).
- (* room: the bcmp call (B 0x84974), a0 = in->p, a1 = word, a2 = wlen *)
  rewrite branch_ltu_U, (ew_U_sub Es 33 34 (x0 + i0) (x0 + len) Es33 Es34), (U_atom Es 46 wlen Esa0) in Hc by lia.
  apply Z.ltb_ge in Hc. rename Hc into Hroom.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
  { ew_awr ltac:(fun h => rewrite ?OLDs in h by lia; rewrite ?Usp, ?U10 in h). }
  ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDs in h by lia; rewrite ?Usp in h) K3.
  clear HF HG HFr.
  pmkst HS.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (2%bv : bv 5) Rsp1.
  prreg HS (1%bv : bv 5) Rra1. prreg HS (3%bv : bv 5) Rgp1. prreg HS (4%bv : bv 5) Rtp1.
  assert (KT3 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a)
    by (intros a Ha; rewrite K3, K2, KA2 by lia; reflexivity).
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
    eapply (BCMP_G W rT mT (8272 + d) (spZ regs + d) [(q, q + 8); (q + 32, q + 36)] ly S Hp W mem md [] ly S Hp dT 0
      (x0 + i0) w wlen (-80 - d) _ HJ) end.
    - rewrite Ra0, Es33. reflexivity.
    - rewrite Ra1, OLDs, E11 by lia. reflexivity.
    - rewrite Ra2, Esa0. reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Rsp1, OLDs, Usp, unsigned_lit_small by lia. lia.
    - lia.
    - lia.
    - rewrite Hes. lia.
    - rewrite Rgp1, OLDs, E3 by lia. exact Hgp.
    - rewrite Rtp1, OLDs, E4 by lia. exact Htp.
    - exact Rra1.
    - apply (ret_ok_codeptr_v (PI := PI_prog_B)); [lia | reflexivity].
    - intros a Ha. split; [|unfold spZ; rewrite Rsp1, OLDs, Usp, unsigned_lit_small by lia; lia].
      rewrite KT3 by lia. replace a with (x0 + Z.of_nat (Z.to_nat (a - x0))) by lia.
      rewrite (ew_aview_garr8 W mem x0 x (Z.to_nat (a - x0)) GT) by lia. discriminate.
    - intros a Ha. split; [|unfold spZ; rewrite Rsp1, OLDs, Usp, unsigned_lit_small by lia; lia].
      rewrite KT3 by lia. replace a with (w + Z.of_nat (Z.to_nat (a - w))) by lia.
      rewrite (ew_aview_garr8 W mem w (wl ++ [0]) (Z.to_nat (a - w)) GW) by (rewrite length_app; cbn; lia). discriminate.
    - intros a Ha. lia.
    - intros a Ha. lia.
    - unfold amem_range in *. lia.
    - unfold YGcfStr.amem_range8, amem_range in *. lia.
    - eapply (range_addressable_agree (aview SEGS (w_H W) mem)); [|apply (range_addressable_sub _ _ x0 len); [exact Hxra | lia | lia]].
      intros z Hz. pose proof (ew_shadow_low z ltac:(lia)). apply KT3. lia.
    - intros Hn s0 Hs0. pose proof (ew_hull_low (x0 + i0) wlen s0 ltac:(lia) Hn ltac:(lia) Hs0).
      rewrite KT3 by lia. exact (ew_hull_sub _ x0 len (x0 + i0) wlen (Hxhull ltac:(lia)) ltac:(lia) ltac:(lia) Hn s0 Hs0).
    - eapply (range_addressable_agree (aview SEGS (w_H W) mem)); [|apply (range_addressable_sub _ _ w (wlen + 1)); [exact Hwra | lia | lia]].
      intros z Hz. pose proof (ew_shadow_low z ltac:(lia)). apply KT3. lia.
    - intros Hn s0 Hs0. pose proof (ew_hull_low w wlen s0 ltac:(lia) Hn ltac:(lia) Hs0).
      rewrite KT3 by lia. exact (ew_hull_sub _ w (wlen + 1) w wlen Hwhull ltac:(lia) ltac:(lia) Hn s0 Hs0). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & vres & -> & HJ3 & HP3 & Hv3 & Hcmp & Hfr3 & Hpres3 & HPM3).
  specialize (HPM3 HPM). clear HPM. rename HPM3 into HPM.
  (* bcmp's answer is the hit test *)
  assert (HIT : vres = w64 0 <-> firstn (length wl) (skipn (Z.to_nat i0) x) = wl).
  { rewrite Hcmp. apply (ew_hit_iff (aview SEGS (w_H W) (ms_mem ms1)) x0 i0 x w wl); [| | lia | lia].
    - intros j Hj. rewrite KT3 by lia. exact (ew_aview_garr8 W mem x0 x j GT Hj).
    - intros j Hj. rewrite KT3 by lia. rewrite (ew_aview_garr8 W mem w (wl ++ [0]) j GW) by (rewrite length_app; cbn; lia).
      rewrite app_nth1 by lia. reflexivity. }
  clear Hcmp.
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3J & _).
  assert (KA4 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
    aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hn; rewrite Hes in Hfr3; rewrite Hfr3, K3, K2, KA2 by lia; reflexivity).
  jafter_call_keep_pi HS 58%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1]%nat HSX.
  lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
  { constructor; [|constructor; [|apply Forall_nil]].
    - split.
      + intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite OLDs, Usp in Ha by lia.
        apply (mbyte_of_aview SEGS). rewrite Hes in Hfr3. apply Hfr3; lia.
      + intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite OLDs, Usp in Ha by lia.
        apply (apresent_writable SEGS). apply Hpres3J. lia.
    - split.
      + intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite OLDs, U10 in Ha by lia.
        apply (mbyte_of_aview SEGS). rewrite Hes in Hfr3. apply Hfr3; lia.
      + intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
  specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
  remember (havoc Es 58 (map (getr regs3) CLOB)) as Eb eqn:HEb in HSX.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIs | cbv; lia]).
  assert (OLDb : forall n, (n < 42)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; apply OLDs; exact Hn).
  assert (Eb46 : ew Eb 46 = w64 wlen) by (rewrite HEb, ew_havoc_old by lia; exact Esa0).
  assert (Eba0 : ew Eb 62 = vres) by (rewrite HEb, <- Hv3; reflexivity).
  assert (HAEb : env_agree 32 (Ereg regs XT) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEs]).
  clear HEb.
  assert (SHOK3 : sh_ok SEGS EW_BX ew_SH Eb (mrestrict (w_H W) mem3)).
  { unfold sh_ok, ew_SH. constructor; [|constructor].
    assert (Eb32 : ew Eb 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDb by lia; exact E32).
    assert (Eb10 : ew Eb 10 = Z_to_bv 64 q) by (rewrite OLDb by lia; exact E10).
    assert (HBx : U Eb EW_BX = SHADOW_OFF) by (unfold EW_BX; rewrite (U_atom Eb 32 SHADOW_OFF Eb32) by (unfold SHADOW_OFF; lia); reflexivity).
    apply (shent_ok_of_range SEGS (w_H W) mem3 Eb EW_BX 10 q 40 q 0 40); [| exact HBx | rewrite (U_atom Eb 10 q Eb10) by lia; reflexivity | lia | lia |].
    - apply (ex_ws_x.exw_ra_kept rsegs (w_H W) mem); [|exact HRAq]. intros z Hz. apply KA4; unfold shadow_of_addr, SHADOW_OFF; lia.
    - intros z Hz. unfold SHADOW_OFF. lia. }
  clear HS HJ SHOK Ra0 Ra1 Ra2 Rsp1 Rra1 Rgp1 Rtp1 KT3 K3 K2.
  rename HJ3 into HJ. rename HSX into HS. rename SHOK3 into SHOK.
  (* ---- run 3: bcmp's answer ---- *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
  { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
  ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp in h) K5.
  clear HF HG HFr.
  psrr_branch_tok RUN BR HS SHOK EW_SPAN.
  + (* the bytes differ: return -1 *)
    rewrite branch_ne_U, U_SOff, U_SLit, Eba0, Z.add_0_r in Hc. rewrite !zcanon_id in Hc by (unfold M64; first [lia | pose proof (bv_unsigned_in_range 64 vres) as R; unfold bv_modulus in R; cbn in R; lia]).
    assert (Hnh : firstn (length wl) (skipn (Z.to_nat i0) x) <> wl).
    { intros Heq. apply HIT in Heq. rewrite Heq in Hc. vm_compute in Hc. discriminate. }
    paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
    { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
    ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp in h) K6.
    clear HF HG HFr.
    prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) Rra.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold YK0s.ret_ok in Hra.
    eapply (ew_finish P); [exact HPM|..].
    * exact HAR.
    * exact HLED.
    * apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
    * eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs XT HS); [exact HAEb | vm_compute; reflexivity].
    * rewrite Rra, OLDb, E1 by lia. exact Hra.
    * lia.
    * exact Hspq.
    * lia.
    * intros a Ha Hn _ _. rewrite K6, K5 by lia. exact (KA4 a Ha Hn).
    * right. split; [intros (_ & Hh); exact (Hnh Hh)|].
      split; [rewrite R10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
      split; intros z Hz; (rewrite K6, K5, KA4 by lia; reflexivity).
  + (* the bytes are the word: hit *)
    rewrite branch_ne_U, U_SOff, U_SLit, Eba0, Z.add_0_r in Hc. rewrite !zcanon_id in Hc by (unfold M64; first [lia | pose proof (bv_unsigned_in_range 64 vres) as R; unfold bv_modulus in R; cbn in R; lia]).
    assert (Hhit : firstn (length wl) (skipn (Z.to_nat i0) x) = wl).
    { apply HIT. apply negb_false_iff, Z.eqb_eq in Hc. apply bv_eq. unfold w64. rewrite unsigned_lit_small by lia. exact Hc. }
    clear Hc HIT.
    assert (Eb13 : ew Eb 13 = Z_to_bv 64 v) by (rewrite OLDb by lia; exact E13).
    paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
    { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
    ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp in h) K6.
    clear HF HG HFr.
    psrr_branch_tok RUN BR HS SHOK EW_SPAN.
    * (* v = NULL *)
      rewrite branch_eq_U, (U_atom Eb 13 v Eb13), U_lit in Hc by lia. apply Z.eqb_eq in Hc. rename Hc into Hv0.
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
      assert (U10b : bv_unsigned (ew Eb 10) = q) by (rewrite OLDb by lia; exact U10).
      assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact Usp).
      assert (Eb38 : ew Eb 38 = Z_to_bv 64 d0) by (rewrite OLDb by lia; exact E38).
      assert (Eb39 : ew Eb 39 = Z_to_bv 64 d1) by (rewrite OLDb by lia; exact E39).
      assert (Eb40 : ew Eb 40 = Z_to_bv 64 d2) by (rewrite OLDb by lia; exact E40).
      assert (Eb41 : ew Eb 41 = Z_to_bv 64 d3) by (rewrite OLDb by lia; exact E41).
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
        assert (KQ : forall z, q <= z < q + 36 -> aview SEGS (w_H W) (ms_mem mx) z = aview SEGS (w_H W) mem z)
          by (intros z Hz; rewrite K6, K5, KA4 by lia; reflexivity) end.
      ew_drop HS [0]%nat.
      ew_addq HS U10b Uspb HPJ KQ Eb38 Eb39 Eb40 Eb41 V0 V1 V2 V3.
      assert (Eb33 : ew Eb 33 = Z_to_bv 64 (x0 + i0)) by (rewrite OLDb by lia; exact E33).
      (* ---- the tail (B 0x849bc): in->p + wlen, the two pointer checks, q's shadow, the store, return 0 ---- *)
      paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
      { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
      ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
        ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K7.
      clear HF HG HFr.
      psrr_branch_tok RUN BR HS SHOK EW_SPAN.
      { (* B 0x849c0 bltu in->p + wlen < in->p (to the trap 0x84a18): not taken, no wrap *)
        exfalso. rewrite branch_ltu_U, (ew_U_add Eb 33 46 (x0 + i0) wlen Eb33 Eb46), (U_atom Eb 33 (x0 + i0) Eb33) in Hc by lia.
        apply Z.ltb_lt in Hc. lia. }
      rewrite branch_ltu_U, (ew_U_add Eb 33 46 (x0 + i0) wlen Eb33 Eb46), (U_atom Eb 33 (x0 + i0) Eb33) in Hc by lia.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
      { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
      ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
        ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K8.
      clear HF HG HFr.
      prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) Rra.
      ew_cells HS U10b Eb33 Eb46 Eb38 Eb39 Eb40 Eb41 VQ VD0 VD1 VD2 VD3.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold YK0s.ret_ok in Hra.
      eapply (ew_finish P); [exact HPM|..].
      -- exact HAR.
      -- exact HLED.
      -- apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
      -- eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs XT HS); [exact HAEb | vm_compute; reflexivity].
      -- rewrite Rra, OLDb, E1 by lia. exact Hra.
      -- lia.
      -- exact Hspq.
      -- lia.
      -- intros a Ha Hn Hq1 Hq2. rewrite K8, K7, K6, K5 by lia. exact (KA4 a Ha Hn).
      -- left. split; [split; [lia | exact Hhit]|]. split; [rewrite R10; reflexivity|]. split; [exact VQ|].
         right. split; [left; exact Hv0|]. exact (ew_d_same _ mem _ q d0 d1 d2 d3 V0 V1 V2 V3 VD0 VD1 VD2 VD3).
    * (* v is a node *)
      rewrite branch_eq_U, (U_atom Eb 13 v Eb13), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into Hv0.
      destruct (HV Hv0) as (Vt & Ht & Hv8 & HRAv & Hvfr). destruct HVR0 as (Hvlo & Hv47).
      destruct (HS0 Hv0) as (Hsb & Hsbr). clear HS0 HV.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
        assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) mem a)
          by (intros a Ha Hn; rewrite K6, K5 by lia; exact (KA4 a Ha Hn)) end.
      clear K6 K5 KA4.
      assert (U10b : bv_unsigned (ew Eb 10) = q) by (rewrite OLDb by lia; exact U10).
      assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact Usp).
      assert (Eb12 : ew Eb 12 = Z_to_bv 64 ty) by (rewrite OLDb by lia; exact E12).
      assert (Eb32 : ew Eb 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDb by lia; exact E32).
      assert (Eb33 : ew Eb 33 = Z_to_bv 64 (x0 + i0)) by (rewrite OLDb by lia; exact E33).
      assert (Eb35 : ew Eb 35 = Z_to_bv 64 t) by (rewrite OLDb by lia; exact E35).
      assert (Eb36 : ew Eb 36 = Z_to_bv 64 sb) by (rewrite OLDb by lia; exact E36).
      assert (Eb37 : ew Eb 37 = Z_to_bv 64 (SHADOW_OFF + v / 8)) by (rewrite OLDb by lia; exact E37).
      assert (Eb38 : ew Eb 38 = Z_to_bv 64 d0) by (rewrite OLDb by lia; exact E38).
      assert (Eb39 : ew Eb 39 = Z_to_bv 64 d1) by (rewrite OLDb by lia; exact E39).
      assert (Eb40 : ew Eb 40 = Z_to_bv 64 d2) by (rewrite OLDb by lia; exact E40).
      assert (Eb41 : ew Eb 41 = Z_to_bv 64 d3) by (rewrite OLDb by lia; exact E41).
      assert (Hvd8 : 0 <= v / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      (* ---- v's shadow byte (B 0x84990): a one-byte region at atom 37 = (v >> 3) + 0x7fff8000, by the alias ---- *)
      pose proof (st_ok_pi_add_fact (PI := PI_prog_B) Eb _ _ 35%nat (mkAF 0 (2 ^ 32 - 1) 0) HS) as HSa.
      lazymatch type of HSa with ?T -> _ => assert (HF_ : T) by (unfold afact_ok; cbn [af_lo af_hi af_al2];
        rewrite Eb35, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia) end.
      specialize (HSa HF_); clear HF_ HS; rename HSa into HS.
      pose proof (st_ok_pi_add_fact (PI := PI_prog_B) Eb _ _ 36%nat (mkAF 0 7 0) HS) as HSa.
      lazymatch type of HSa with ?T -> _ => assert (HF_ : T) by (unfold afact_ok; cbn [af_lo af_hi af_al2];
        rewrite Eb36, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia) end.
      specialize (HSa HF_); clear HF_ HS; rename HSa into HS.
      pose proof (st_ok_pi_add_fact (PI := PI_prog_B) Eb _ _ 37%nat (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0) HS) as HSa.
      lazymatch type of HSa with ?T -> _ => assert (HF_ : T) by (unfold afact_ok; cbn [af_lo af_hi af_al2];
        rewrite Eb37, unsigned_lit_small by (unfold SHADOW_OFF; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; unfold SHADOW_OFF; lia) end.
      specialize (HSa HF_); clear HF_ HS; rename HSa into HS. ew_norm HS.
      lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?ms =>
        pose proof (st_ok_pi_add_region (PI := PI_prog_B) Ex ss ms EW_SHR HS eq_refl) as HSa end.
      lazymatch type of HSa with ?A -> ?Bd -> _ => assert (Ha_ : A); [|assert (Hb_ : Bd)] end.
      { unfold region_ok, EW_SHR; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Eb37, unsigned_lit_small by (unfold SHADOW_OFF; lia).
        split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor]. cbn [ms_mem restrict].
        apply (chunk_ok_val SEGS Eb _ (SHADOW_OFF + v / 8) 0 1 (SOff 36 0) sb);
          [cbn [sv_denot]; rewrite Eb36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. apply (ew_val1_of_aview (w_H W)). rewrite KB by (unfold SHADOW_OFF; lia). exact Hsb. }
      { apply all_disjoint_of_extents. cbn [ss_mem map]. unfold extent_of_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val EW_SHR]. rewrite Eb37, unsigned_lit_small by (unfold SHADOW_OFF; lia).
        rewrite Uspb, U10b. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF. repeat split; lia. }
      specialize (HSa Ha_ Hb_); clear Ha_ Hb_ HS; rename HSa into HS.
      pose proof (ew_pi_alias Eb _ _ (fst EW_ALIAS) (snd EW_ALIAS) HS) as HSa.
      lazymatch type of HSa with ?T -> _ => assert (HF_ : T) end.
      { cbn [fst snd EW_ALIAS]. rewrite (ex_ws_x.exw_denot_shx Eb 13 32 v SHADOW_OFF Eb13 Eb32) by (unfold SHADOW_OFF; lia).
        cbn [sv_denot]. rewrite Eb37, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity. }
      specialize (HSa HF_); clear HF_ HS; rename HSa into HS. ew_norm HS.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
      { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
      ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp in h) K9.
      clear HF HG HFr.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
        assert (KB' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) mem a)
          by (intros a Ha Hn; rewrite K9 by lia; exact (KB a Ha Hn)) end.
      clear KB K9. rename KB' into KB.
      (* ---- v->type (B 0x84998): swap the shadow byte's region (and in->p's) for v's 4 bytes ---- *)
      ew_drop HS [1]%nat.
      lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?ms =>
        pose proof (st_ok_pi_add_region (PI := PI_prog_B) Ex ss ms EW_VR HS eq_refl) as HSa end.
      lazymatch type of HSa with ?A -> ?Bd -> _ => assert (Ha_ : A); [|assert (Hb_ : Bd)] end.
      { unfold region_ok, EW_VR; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Eb13, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor]. cbn [ms_mem restrict].
        apply (chunk_ok_val SEGS Eb _ v 0 4 (SOff 35 0) t);
          [cbn [sv_denot]; rewrite Eb35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. apply (ex_ws_x.exw_val_kept rsegs (w_H W) mem); [|exact Vt].
        intros z Hz. cbn in Hz. apply KB; lia. }
      { apply all_disjoint_of_extents. cbn [ss_mem map]. unfold extent_of_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val EW_VR]. rewrite Eb13, unsigned_lit_small by lia.
        rewrite Uspb. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
      specialize (HSa Ha_ Hb_); clear Ha_ Hb_ HS; rename HSa into HS. ew_norm HS.
      psrr_branch_tok RUN BR HS SHOK EW_SPAN.
      -- (* s <> 0: the slow block B 0x84a1c *)
         rewrite branch_ne_U, (U_atom Eb 36 sb Eb36), U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
         rename Hc into Hsb0.
         paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
         { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
         ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp in h) K9.
         clear HF HG HFr.
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
           assert (KB' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
             aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) mem a)
             by (intros a Ha Hn; rewrite K9 by lia; exact (KB a Ha Hn)) end.
         clear KB K9. rename KB' into KB.
         psrr_branch_tok RUN BR HS SHOK EW_SPAN.
         ++ (* 3 < s: back to B 0x84998 *)
            clear Hc.
            paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
            { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
            ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp in h) K9.
            clear HF HG HFr.
            lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
              assert (KB' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
                aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) mem a)
                by (intros a Ha Hn; rewrite K9 by lia; exact (KB a Ha Hn)) end.
            clear KB K9. rename KB' into KB.
            (* ---- the type compare (B 0x8499c), in->p's and in->differs's cells swapped back in for the stores ---- *)
            pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
            lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
              assert (KQ : forall z, q <= z < q + 36 -> aview SEGS (w_H W) (ms_mem mx) z = aview SEGS (w_H W) mem z)
                by (intros z Hz; apply KB; lia) end.
            ew_drop HS [1]%nat.
            ew_addq HS U10b Uspb HPJ KQ Eb38 Eb39 Eb40 Eb41 V0 V1 V2 V3.
            clear HPJ KQ.
            psrr_branch_tok RUN BR HS SHOK EW_SPAN.
            { (* t = ty: in->differs stays *)
              rewrite branch_eq_U, (U_atom Eb 12 ty Eb12), (ew_type_eqb Eb 35 t ty Eb35 Ht Hty) in Hc by lia.
              apply Z.eqb_eq in Hc. rename Hc into Htt.
              paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
            { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
            ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
              ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K10.
            clear HF HG HFr.
              psrr_branch_tok RUN BR HS SHOK EW_SPAN.
              { exfalso. rewrite (ew_site_unimp_ovf Eb 33 46 (x0 + i0) wlen Eb33 Eb46) in Hc by lia. discriminate. }
              clear Hc.
              paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
            { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
            ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
              ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K11.
            clear HF HG HFr.
              prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) Rra.
            ew_cells HS U10b Eb33 Eb46 Eb38 Eb39 Eb40 Eb41 VQ VD0 VD1 VD2 VD3.
            eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
            intros mat'. unfold YK0s.ret_ok in Hra.
            eapply (ew_finish P); [exact HPM|..].
            - exact HAR.
            - exact HLED.
            - apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
            - eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs XT HS); [exact HAEb | vm_compute; reflexivity].
            - rewrite Rra, OLDb, E1 by lia. exact Hra.
            - lia.
            - exact Hspq.
            - lia.
            - intros a Ha Hn Hq1 Hq2. rewrite K11, K10 by lia. exact (KB a Ha Hn).
            - left. split; [split; [lia | exact Hhit]|]. split; [rewrite R10; reflexivity|]. split; [exact VQ|].
              right. split; [right; exact Htt|]. exact (ew_d_same _ mem _ q d0 d1 d2 d3 V0 V1 V2 V3 VD0 VD1 VD2 VD3). }
            { (* t <> ty: in->differs = 1 *)
              rewrite branch_eq_U, (U_atom Eb 12 ty Eb12), (ew_type_eqb Eb 35 t ty Eb35 Ht Hty) in Hc by lia.
              apply Z.eqb_neq in Hc. rename Hc into Htt.
              paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
            { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
            ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
              ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K10.
            clear HF HG HFr.
              psrr_branch_tok RUN BR HS SHOK EW_SPAN.
              { exfalso. rewrite (ew_site_unimp_ovf Eb 33 46 (x0 + i0) wlen Eb33 Eb46) in Hc by lia. discriminate. }
              clear Hc.
              paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
            { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
            ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
              ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K11.
            clear HF HG HFr.
              prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) Rra.
              pose proof (ex_ws_x.exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RD. cbn [ms_mem restrict] in RD.
              pose proof (ex_ws_x.exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
              pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 0 8 (SAlu ALU_ADD (SOff 33 0) (SOff 46 0)) _ RQ U10b
                ltac:(left; reflexivity) (ew_denot_of_U _ _ _ (ew_U_add _ 33 46 _ _ Eb33 Eb46 ltac:(lia) ltac:(lia) ltac:(lia)))
                ltac:(cbn; lia) ltac:(cbn; lia)) as VQ. rewrite Z.add_0_r in VQ.
              pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 32 4 (SLit 1) 1 RD U10b ltac:(left; reflexivity)
                ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VD.
              clear RD RQ.
              eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
              intros mat'. unfold YK0s.ret_ok in Hra.
              eapply (ew_finish P); [exact HPM|..].
              - exact HAR.
              - exact HLED.
              - apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
              - eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs XT HS); [exact HAEb | vm_compute; reflexivity].
              - rewrite Rra, OLDb, E1 by lia. exact Hra.
              - lia.
              - exact Hspq.
              - lia.
              - intros a Ha Hn Hq1 Hq2. rewrite K11, K10 by lia. exact (KB a Ha Hn).
              - left. split; [split; [lia | exact Hhit]|]. split; [rewrite R10; reflexivity|]. split; [exact VQ|].
                left. split; [exact Hv0|]. split; [exact Htt | exact VD]. }
         ++ (* the fall-through to errpath_load4 (B 0x84a24 / 0x84a28): refuted *)
            exfalso. rewrite (ew_site_load4 Eb 36 sb Eb36 Hsbr Hsb0) in Hc. discriminate.
      -- (* s = 0 *)
         clear Hc.
         paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
         { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
         ew_kept_of HFr (fun a => spZ regs - 80 <= a < spZ regs) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp in h) K9.
         clear HF HG HFr.
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
           assert (KB' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 8272 <= a < spZ regs) ->
             aview SEGS (w_H W) (ms_mem mx) a = aview SEGS (w_H W) mem a)
             by (intros a Ha Hn; rewrite K9 by lia; exact (KB a Ha Hn)) end.
         clear KB K9. rename KB' into KB.
         (* ---- the type compare (B 0x8499c), in->p's and in->differs's cells swapped back in for the stores ---- *)
         pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mx) =>
           assert (KQ : forall z, q <= z < q + 36 -> aview SEGS (w_H W) (ms_mem mx) z = aview SEGS (w_H W) mem z)
             by (intros z Hz; apply KB; lia) end.
         ew_drop HS [1]%nat.
         ew_addq HS U10b Uspb HPJ KQ Eb38 Eb39 Eb40 Eb41 V0 V1 V2 V3.
         clear HPJ KQ.
         psrr_branch_tok RUN BR HS SHOK EW_SPAN.
         { (* t = ty: in->differs stays *)
           rewrite branch_eq_U, (U_atom Eb 12 ty Eb12), (ew_type_eqb Eb 35 t ty Eb35 Ht Hty) in Hc by lia.
           apply Z.eqb_eq in Hc. rename Hc into Htt.
           paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
         { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
         ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
           ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K10.
         clear HF HG HFr.
           psrr_branch_tok RUN BR HS SHOK EW_SPAN.
           { exfalso. rewrite (ew_site_unimp_ovf Eb 33 46 (x0 + i0) wlen Eb33 Eb46) in Hc by lia. discriminate. }
           clear Hc.
           paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
         { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
         ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
           ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K11.
         clear HF HG HFr.
           prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) Rra.
         ew_cells HS U10b Eb33 Eb46 Eb38 Eb39 Eb40 Eb41 VQ VD0 VD1 VD2 VD3.
         eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
         intros mat'. unfold YK0s.ret_ok in Hra.
         eapply (ew_finish P); [exact HPM|..].
         - exact HAR.
         - exact HLED.
         - apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
         - eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs XT HS); [exact HAEb | vm_compute; reflexivity].
         - rewrite Rra, OLDb, E1 by lia. exact Hra.
         - lia.
         - exact Hspq.
         - lia.
         - intros a Ha Hn Hq1 Hq2. rewrite K11, K10 by lia. exact (KB a Ha Hn).
         - left. split; [split; [lia | exact Hhit]|]. split; [rewrite R10; reflexivity|]. split; [exact VQ|].
           right. split; [right; exact Htt|]. exact (ew_d_same _ mem _ q d0 d1 d2 d3 V0 V1 V2 V3 VD0 VD1 VD2 VD3). }
         { (* t <> ty: in->differs = 1 *)
           rewrite branch_eq_U, (U_atom Eb 12 ty Eb12), (ew_type_eqb Eb 35 t ty Eb35 Ht Hty) in Hc by lia.
           apply Z.eqb_neq in Hc. rename Hc into Htt.
           paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
         { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
         ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
           ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K10.
         clear HF HG HFr.
           psrr_branch_tok RUN BR HS SHOK EW_SPAN.
           { exfalso. rewrite (ew_site_unimp_ovf Eb 33 46 (x0 + i0) wlen Eb33 Eb46) in Hc by lia. discriminate. }
           clear Hc.
           paj_run_tok_x_inv RUN HS HJ SHOK HPM EW_SPAN.
         { ew_awr ltac:(fun h => rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h). }
         ew_kept_of HFr (fun a => (spZ regs - 80 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 32 <= a < q + 36))
           ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?OLDb in h by lia; rewrite ?Usp, ?U10 in h) K11.
         clear HF HG HFr.
           prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) Rra.
           pose proof (ex_ws_x.exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RD. cbn [ms_mem restrict] in RD.
           pose proof (ex_ws_x.exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
           pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 0 8 (SAlu ALU_ADD (SOff 33 0) (SOff 46 0)) _ RQ U10b
             ltac:(left; reflexivity) (ew_denot_of_U _ _ _ (ew_U_add _ 33 46 _ _ Eb33 Eb46 ltac:(lia) ltac:(lia) ltac:(lia)))
             ltac:(cbn; lia) ltac:(cbn; lia)) as VQ. rewrite Z.add_0_r in VQ.
           pose proof (ex_ws_x.exw_field rsegs _ _ 10%nat _ _ _ _ _ _ 32 4 (SLit 1) 1 RD U10b ltac:(left; reflexivity)
             ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VD.
           clear RD RQ.
           eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
           intros mat'. unfold YK0s.ret_ok in Hra.
           eapply (ew_finish P); [exact HPM|..].
           - exact HAR.
           - exact HLED.
           - apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
           - eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs XT HS); [exact HAEb | vm_compute; reflexivity].
           - rewrite Rra, OLDb, E1 by lia. exact Hra.
           - lia.
           - exact Hspq.
           - lia.
           - intros a Ha Hn Hq1 Hq2. rewrite K11, K10 by lia. exact (KB a Ha Hn).
           - left. split; [split; [lia | exact Hhit]|]. split; [rewrite R10; reflexivity|]. split; [exact VQ|].
             left. split; [exact Hv0|]. split; [exact Htt | exact VD]. }
Qed.
End g.

(* the two rule shapes from the engine's rules: at P := True from the texts without the keep (aj_strlen_at_xro,
   aj_bcmp_at_x), at P := (memnorm mem0 -> memnorm _) from the texts with the keep (aj_strlen_at_xrom, aj_bcmp_at_xm) *)
Lemma ew_strlen_rule_xro : ew_strlen_rule (fun _ => True).
Proof.
intros W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len o raw HJ
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21.
eapply SRr_mono; [exact (YGcallMxmn.aj_strlen_at_xro (SK := SK) rsegs B (@prh_pst prh_img_B) ARx B_prog_relro_lo
  B_prog_relro_hi LAWS B_prog_segs_low _ STRLEN W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len o raw
  HJ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21) |].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc & K1 & K2 & K3 & K4 & K5).
split; [reflexivity|]. exists regs2, mem2, md2.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (fun _ => I))))))).
Qed.
Lemma ew_strlen_rule_xrom : forall mem0,
  ew_strlen_rule (fun m => YAkMemnorm.memnorm SEGS mem0 -> YAkMemnorm.memnorm SEGS m).
Proof.
intros mem0 W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len o raw HJ
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21.
eapply SRr_mono; [exact (YGcallMxmn.aj_strlen_at_xrom (SK := SK) rsegs B (@prh_pst prh_img_B) ARx B_prog_relro_lo
  B_prog_relro_hi LAWS B_prog_segs_low _ STRLENm W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len o raw
  HJ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21) |].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc & K1 & K2 & K3 & K4 & K5 & Kmn).
split; [reflexivity|]. exists regs2, mem2, md2.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (YSRrMemnorm.srr_inv_call_imp SEGS mem0 memT mem2 Kmn))))))).
Qed.
Lemma ew_bcmp_rule_x : ew_bcmp_rule (fun _ => True).
Proof.
intros W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw HJ
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26.
eapply SRr_mono; [exact (aj_bcmp_at_x (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low _ BCMP
  W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw
  HJ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26) |].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & vr & Hc & K1 & K2 & K3 & K4 & K5 & K6).
split; [reflexivity|]. exists regs2, mem2, md2, vr.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (fun _ => I)))))))).
Qed.
Lemma ew_bcmp_rule_xm : forall mem0,
  ew_bcmp_rule (fun m => YAkMemnorm.memnorm SEGS mem0 -> YAkMemnorm.memnorm SEGS m).
Proof.
intros mem0 W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw HJ
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26.
eapply SRr_mono; [exact (YGcallMxmn.aj_bcmp_at_xm (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low _
  BCMPm W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw
  HJ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26) |].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & vr & Hc & K1 & K2 & K3 & K4 & K5 & K6 & Kmn).
split; [reflexivity|]. exists regs2, mem2, md2, vr.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6
  (YSRrMemnorm.srr_inv_call_imp SEGS mem0 memT mem2 Kmn)))))))).
Qed.

(* ex_word_holds_B: kit 04388d628fb's tex_word_specX (lib/A/PRH_FnEx.v blob d32e3229d5dcf3d74f35fb6471aecd7e033047f8),
   VERBATIM, no extra premise: the walk at P := (memnorm mem -> memnorm _), whose post is fpostWm's by unfolding *)
Theorem ex_word_holds_B :
  tex_word_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
intros ly S Hp W regs mem md ch q w ty v t x0 i0 d wl x Lam peak cnt fail ran most own len hit
  H1 H2 H3 H4 H5 H6 H7 Hv H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
exact (ex_word_walk (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS _ mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS))
  (ew_strlen_rule_xrom mem) (ew_bcmp_rule_xm mem)
  ly S Hp W regs mem md ch q w ty v t x0 i0 d wl x Lam peak cnt fail ran most own
  H1 H2 H3 H4 H5 H6 H7 Hv H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 (fun h => h)).
Qed.

(* ex_word_holds_B_bounded: the bounded text (ExwB_Stmt.v tex_word_specX_vr), kept while ex_value's EHW cites it
   (origin/cold/h-rw-pre-7-b-ex_value 30962b8840a, ExvB_Disp.v:39-40, with the texts without the keep): the walk at
   P := True, the range premise from ex_word_vrange, S' = S and P dropped from the post *)
Theorem ex_word_holds_B_bounded :
  tex_word_specX_vr (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
unfold tex_word_specX_vr. intros ly S Hp W regs mem md ch q w ty v t x0 i0 d wl x Lam peak cnt fail ran most own.
cbv zeta.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 HVR H19.
assert (Hv : 0 <= v /\ v + 4 <= 2 ^ 47) by (destruct (Z.eq_dec v 0) as [->|Hv0]; [lia | exact (HVR Hv0)]).
eapply SRr_mono; [exact (ex_word_walk (fun _ => True) (srr_inv_laws_true _) ew_strlen_rule_xro ew_bcmp_rule_x
  ly S Hp W regs mem md ch q w ty v t x0 i0 d wl x Lam peak cnt fail ran most own
  H1 H2 H3 H4 H5 H6 H7 Hv H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 I) |].
unfold fpostW. cbv beta.
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HK & HP & (Hr & Hhp & _ & Hab & Hled & Hres) & _).
exists ly', S', Hp', regs', mem', md', k.
exact (conj Hc (conj HJ (conj HK (conj HP (conj Hr (conj Hhp (conj Hab (conj Hled Hres)))))))).
Qed.
End w.
End e.

Print Assumptions ex_word_holds_B.

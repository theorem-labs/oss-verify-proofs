(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths changed; 844 of its 881 lines of code are new or changed and 508 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacPortsParse ClassifyCore ClassifyCoreSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed RcParse disco_classify_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition PC_M2C : Z := AF_both3_classify_core + 0x210.

Lemma m2_model_bad : forall FB len U L,
  disco_classify_c.dkind FB len <> 0 -> CtrlParsed.bytes_eqb (disco_classify_c.src FB) U = false ->
  disco_classify_c.dkind FB len <> 1 -> disco_classify_c.fsum FB <> 0 ->
  disco_classify_c.classify_model FB len U L = (-1, None, L).
Proof.
intros FB len U L H0 Hs H1 Hf. unfold disco_classify_c.classify_model. cbv zeta.
rewrite (proj2 (Z.eqb_neq _ _) H0), Hs, (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) Hf). reflexivity.
Qed.

Lemma m2_model_ok : forall FB len U L,
  disco_classify_c.dkind FB len <> 0 -> CtrlParsed.bytes_eqb (disco_classify_c.src FB) U = false ->
  disco_classify_c.dkind FB len <> 1 -> disco_classify_c.fsum FB = 0 ->
  disco_classify_c.classify_model FB len U L =
  (0, Some (disco_classify_c.sight FB len),
   match L with
   | None => None
   | Some Lb => Some (if disco_classify_c.lv Lb =? 0 then disco_classify_c.latch FB Lb else Lb)
   end).
Proof.
intros FB len U L H0 Hs H1 Hf. unfold disco_classify_c.classify_model. cbv zeta.
rewrite (proj2 (Z.eqb_neq _ _) H0), Hs, (proj2 (Z.eqb_neq _ _) H1), Hf. cbn [Z.eqb negb andb].
destruct L as [Lb|]; reflexivity.
Qed.

Lemma m2_ps_src : forall len FB j, fst (RcParse.ctrlparse len FB) <> 0 -> (j < 6)%nat ->
  nth (4 + j) (snd (RcParse.ctrlparse len FB)) (Z_to_bv 8 0) = nth (6 + j) FB (Z_to_bv 8 0).
Proof.
intros len FB j Hk Hj. pose proof (RcParse.ctrlparse_fields len FB Hk) as HF. cbv zeta in HF.
destruct HF as (H1 & _). exact (H1 j Hj).
Qed.

Lemma m2_latch_nth : forall FB Lb j, length FB = 50%nat -> length Lb = 12%nat -> (j < 12)%nat ->
  nth j (disco_classify_c.latch FB Lb) (Z_to_bv 8 0) =
  if (j <? 6)%nat then nth (6 + j) FB (Z_to_bv 8 0)
  else if (j <? 8)%nat then nth j Lb (Z_to_bv 8 0)
  else nth (j - 8) (Mem.le4 (Z_to_bv 64 1)) (Z_to_bv 8 0).
Proof.
intros FB Lb j HF HL Hj. unfold disco_classify_c.latch, disco_classify_c.src, CtrlParsed.fld.
assert (L1 : length (firstn 6 (skipn 6 FB)) = 6%nat) by (rewrite length_firstn, length_skipn; lia).
assert (L2 : length (firstn 2 (skipn 6 Lb)) = 2%nat) by (rewrite length_firstn, length_skipn; lia).
destruct (Nat.ltb_spec j 6) as [H6|H6].
- rewrite app_nth1 by lia. rewrite nth_firstn, nth_skipn. replace (j <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  reflexivity.
- rewrite app_nth2 by lia. rewrite L1. destruct (Nat.ltb_spec j 8) as [H8|H8].
  + rewrite app_nth1 by lia. rewrite nth_firstn, nth_skipn.
    replace (j - 6 <? 2)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    f_equal. lia.
  + rewrite app_nth2 by lia. rewrite L2. f_equal. lia.
Qed.

Lemma m2_lor8 : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor x (Z.shiftl y 8) = x + 256 * y.
Proof.
intros x y Hx Hy. rewrite Z.shiftl_mul_pow2 by lia.
assert (HL : Z.land x (y * 2 ^ 8) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small x (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
    rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite <- (Z.lxor_lor _ _ HL). rewrite <- (Z.add_nocarry_lxor _ _ HL). change (2 ^ 8) with 256. lia.
Qed.

Lemma m2_bytes4 : forall b0 b1 b2 b3 : byte,
  bytes_le_to_Z [b0; b1; b2; b3] =
  bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)).
Proof.
intros b0 b1 b2 b3.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
cbn [bytes_le_to_Z].
rewrite (m2_lor8 (bv_unsigned b3) 0) by lia.
rewrite (m2_lor8 (bv_unsigned b2)) by lia.
rewrite (m2_lor8 (bv_unsigned b1)) by lia.
rewrite (m2_lor8 (bv_unsigned b0)) by lia.
lia.
Qed.

Lemma m2_hull_sub : forall rd x n m, shadow_hull_vis rd x n -> 0 < m <= n -> 0 <= x -> shadow_hull_vis rd x m.
Proof.
intros rd x n m H Hm Hx s Hs. apply H. split; [lia|].
assert (shadow_addr (x + m - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (shadow_addr (x + m - 1) / 8 * 8 <= shadow_addr (x + n - 1) / 8 * 8) by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
lia.
Qed.

Lemma m2_rv : forall regs RV r v, Forall (fun rv => getr regs (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV ->
  In (r, v) RV -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs RV r v H Hin. rewrite Forall_forall in H. exact (H _ Hin). Qed.

Lemma m2_rv_sub : forall (l : list Z) regs3 regs4 RV RV',
  Forall (fun rv => getr regs3 (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV ->
  (forall r, In r l -> getr regs4 (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) ->
  Forall (fun rv => In rv RV /\ In (fst rv) l) RV' ->
  Forall (fun rv => getr regs4 (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV'.
Proof.
intros l regs3 regs4 RV RV' H HK H'. rewrite Forall_forall in H, H' |- *. intros [r v] Hin.
destruct (H' _ Hin) as [Hin1 Hin2]. cbn [fst snd] in *. rewrite (HK r Hin2). exact (H _ Hin1).
Qed.

Lemma m2_agree_ewset : forall E0 E n v, (32 <= n)%nat -> env_agree 32 E0 E -> env_agree 32 E0 (ewset E n v).
Proof.
intros E0 E n v Hn [HA HD]. split; [intros i Hi; rewrite ew_ewset_other by lia; apply HA; exact Hi | exact HD].
Qed.

Lemma m2_latch_len : forall FB Lb, length FB = 50%nat -> length Lb = 12%nat -> length (disco_classify_c.latch FB Lb) = 12%nat.
Proof.
intros FB Lb HF HL. unfold disco_classify_c.latch, disco_classify_c.src, CtrlParsed.fld.
rewrite !length_app, !length_firstn, !length_skipn, HF, HL. reflexivity.
Qed.

Lemma m2_chain : forall (A Bm C : bvmap 5 word) r v, aregs_preserved Bm A -> acallee_saved r ->
  getr Bm (Z_to_bv 5 r) = getr C (Z_to_bv 5 r) -> getr C (Z_to_bv 5 r) = v -> getr A (Z_to_bv 5 r) = v.
Proof. intros A Bm C r v HP Hr H1 H2. rewrite (HP r Hr), H1. exact H2. Qed.

Lemma m2_soff_agree : forall E E' n c, ew E n = ew E' n -> sv_denot E (SOff n c) = sv_denot E' (SOff n c).
Proof. intros E E' n c H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

Lemma m2_br_eq0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof. intros E n v H Hv. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit by lia. reflexivity. Qed.

Lemma m2_br_ne0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (v =? 0).
Proof. intros E n v H Hv. rewrite branch_ne_U, (U_atom E n v H Hv), U_lit by lia. reflexivity. Qed.

Ltac m2_in := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; vm_compute; reflexivity | right]).
Ltac m2_agree HAG := repeat (apply m2_agree_ewset; [lia|]); exact HAG.
Ltac m2_ew H := cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact H.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma m2_cfg : forall (fq : YK11.FPState) pc pc' regs mem md, pc = pc' ->
  mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)) md =
  cfg_at (fx := fq) SEGS (BASE + pc') regs mem md.
Proof. intros fq pc pc' regs mem md ->. reflexivity. Qed.

Lemma m2_val_mem_frame : forall m m' a n v, val_mem SEGS m a n v ->
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) -> val_mem SEGS m' a n v.
Proof. intros m m' a n v H Hk k Hkn. rewrite Hk by lia. exact (H k Hkn). Qed.

Lemma m2_aview_of_garr8 : forall H m base (l : list byte) j, garr8 SEGS (mrestrict H m) base (cls_bytes l) ->
  (j < length l)%nat -> aview SEGS H m (base + Z.of_nat j) = Some (bv_unsigned (nth j l (Z_to_bv 8 0))).
Proof.
intros H m base l j Hg Hj. unfold aview. unfold cls_bytes in Hg.
rewrite (garr8_mbyte SEGS _ base _ j Hg) by (rewrite length_map; exact Hj). cbn [option_map]. f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). rewrite map_nth.
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma m2_garr8_of_aview : forall H m base (l : list byte),
  (forall j, (j < length l)%nat -> aview SEGS H m (base + Z.of_nat j) = Some (bv_unsigned (nth j l (Z_to_bv 8 0)))) ->
  garr8 SEGS (mrestrict H m) base (cls_bytes l).
Proof.
intros H m base l Hv j Hj. unfold cls_bytes in *. rewrite length_map in Hj.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). rewrite map_nth.
pose proof (bv_unsigned_in_range 8 (nth j l (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|lia].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte SEGS _ _ _ _ (Hv j Hj)) as (b & Hb & Hbv & _). rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (bv_modulus 8) with 256. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned (nth j l (Z_to_bv 8 0))) 256) by lia. lia.
Qed.

Lemma m2_val_mem4 : forall m a (l : list byte), length l = 4%nat ->
  (forall j, (j < 4)%nat -> mbyte SEGS m (a + Z.of_nat j) = Some (nth j l (Z_to_bv 8 0))) ->
  val_mem SEGS m a 4 (bytes_le_to_Z l).
Proof.
intros m a l Hl Hb k Hk. rewrite (Hb k Hk). f_equal.
destruct l as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; try discriminate Hl.
rewrite m2_bytes4.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [nth];
[change (8 * Z.of_nat 0) with 0 | change (8 * Z.of_nat 1) with 8 | change (8 * Z.of_nat 2) with 16 | change (8 * Z.of_nat 3) with 24];
rewrite Z.shiftr_div_pow2 by lia;
[change (2 ^ 0) with 1 | change (2 ^ 8) with 256 | change (2 ^ 16) with 65536 | change (2 ^ 24) with 16777216];
Z.div_mod_to_equations; lia.
Qed.

Lemma m2_val_lv : forall m lk (Lb : list byte), length Lb = 12%nat -> garr8 SEGS m lk (cls_bytes Lb) ->
  val_mem SEGS m (lk + 8) 4 (disco_classify_c.lv Lb) /\ 0 <= disco_classify_c.lv Lb < 2 ^ 32.
Proof.
intros m lk Lb HL Hg. unfold disco_classify_c.lv, CtrlParsed.fu.
assert (L4 : length (CtrlParsed.fld Lb 8 4) = 4%nat) by (unfold CtrlParsed.fld; rewrite length_firstn, length_skipn; lia).
split.
- apply m2_val_mem4; [exact L4|]. intros j Hj. unfold CtrlParsed.fld. rewrite nth_firstn, nth_skipn.
  replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  unfold cls_bytes in Hg. rewrite <- Z.add_assoc. replace (8 + Z.of_nat j) with (Z.of_nat (8 + j)) by lia.
  rewrite (garr8_mbyte SEGS m lk _ (8 + j) Hg) by (rewrite length_map; lia). f_equal.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia). rewrite map_nth.
  apply Z_to_bv_bv_unsigned.
- destruct (CtrlParsed.fld Lb 8 4) as [|b0 [|b1 [|b2 [|b3 [|? ?]]]]]; try discriminate L4.
  rewrite m2_bytes4.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  change (bv_modulus 8) with 256 in R0, R1, R2, R3. lia.
Qed.

Lemma m2_br_lv : forall E v, ew E 32 = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 32 0))) (sv_denot E (SLit 0)) = negb (v =? 0).
Proof.
intros E v H Hv. rewrite branch_ne_U, U_SExt, (U_atom E 32 v H), U_lit by lia. cbv iota.
unfold bv_swrap, bv_wrap, zcanon, M64.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
change (2 ^ Z.of_N 32) with (2 ^ 32).
destruct (Z.eqb_spec v 0) as [->|Nv]; [vm_compute; reflexivity|].
cbn [negb]. apply negb_true_iff. apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Definition m2_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition m2_Bx0 : sv := SLit SB.
Definition m2_ss0 : sstate := mkSS PC_R2 sr_atoms [] None (mkFacts [] [] []).

Lemma m2_entry0 : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) m2_ss0
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + PC_R2)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS m2_Bx0 [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros fq W regs mem. rewrite restrict_mkst_fx. split.
- unfold m2_ss0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + reflexivity.
  + constructor.
  + exact I.
  + split; [exact I | split; exact I].
- constructor.
Qed.

Definition m2_lkr (wl wh : Z) (v : sv) : YP09.region :=
  YP09.mkRegion (Some 23%nat) 0 12 wl wh [YP09.mkChunk 8 (CVal 4 v)].
Definition m2_Bx : sv := SOff 21 0.
Definition m2_SH : list shent := [mkSHE 23 0 12].
Definition m2_facts1 : facts := mkFacts [(21%nat, mkAF SB SB 0); (23%nat, HPTR 2); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition m2_ss1 : sstate := mkSS PC_R2 sr_atoms [m2_lkr 0 0 (SOff 32 0)] None m2_facts1.
Definition m2_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 8) (SLit 3)) (SOff 21 0).
Definition m2_sr2 : list sv := sr_set (sr_set sr_atoms 24%bv (SOff 23 8)) 26%bv m2_shx.
Definition m2_facts2 : facts := mkFacts [(21%nat, mkAF SB SB 0); (23%nat, HPTR 2)] [] [].
Definition m2_ss2 : sstate := mkSS PC_M2C m2_sr2 [m2_lkr 8 12 (SLit 0)] None m2_facts2.

Lemma m2_lk_facts : forall E lk, ew E 21 = Z_to_bv 64 SB -> ew E 23 = Z_to_bv 64 lk ->
  4096 <= lk -> lk + 12 <= alloc_ceiling -> lk mod 4 = 0 ->
  afact_ok E 21 (mkAF SB SB 0) /\ afact_ok E 23 (HPTR 2).
Proof.
intros E lk H21 H23 Hlo Hhi Hal. pose proof (proj1 (@ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite H21, H23, !unsigned_lit_small by (unfold SB; lia). change (2 ^ 2) with 4. rewrite Z.pow_0_r, Z.mod_1_r.
unfold SB. repeat split; lia.
Qed.

Lemma m2_shok : forall H mem E lk, ew E 21 = Z_to_bv 64 SB -> ew E 23 = Z_to_bv 64 lk ->
  0 <= lk -> lk + 12 <= alloc_ceiling ->
  range_addressable (aview SEGS H mem) SHADOW_OFF lk 12 ->
  (lk + 12 <= kLowShadowBeg \/ kHighMemBeg <= lk) ->
  sh_ok SEGS m2_Bx m2_SH E (mrestrict H mem).
Proof.
intros H mem E lk H21 H23 Hlo Hhi HRA Happ. pose proof (proj1 (@ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
unfold sh_ok, m2_SH. apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range SEGS H mem E m2_Bx 23 lk 12 lk 0 12 HRA).
- unfold m2_Bx. rewrite (U_atom E 21 SB H21) by (unfold SB; lia). reflexivity.
- apply U_atom; [exact H23 | lia].
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Lemma m2_entry1 : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem lk v,
  getr regs 21 = w64 SB -> getr regs 23 = w64 lk ->
  4096 <= lk -> lk + 12 <= alloc_ceiling -> lk mod 4 = 0 -> 0 <= v < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) mem) (lk + 8) 4 v ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF lk 12 ->
  (lk + 12 <= kLowShadowBeg \/ kHighMemBeg <= lk) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 v])) m2_ss1
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + PC_R2)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS m2_Bx m2_SH (Eimg (Ereg regs [Z_to_bv 64 v])) (mrestrict (w_H W) mem).
Proof.
intros fq W regs mem lk v H21 H23 Hlo Hhi Hal Hv Hmem HRA Happ.
pose proof (proj1 (@ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [Z_to_bv 64 v])).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E23 : ew E 23 = Z_to_bv 64 lk) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
split.
- unfold m2_ss1. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, m2_lkr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ lk 8 4 _ v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Hmem].
  + cbn [pairwise_disjoint all_disjoint]. split; exact I.
  + destruct (m2_lk_facts E lk E21 E23 Hlo Hhi Hal) as [F21 F23].
    split; [|split; exact I]. cbn [m2_facts1 f_atoms atoms_ok]. split; [exact F21|]. split; [exact F23|].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia.
- apply (m2_shok _ mem E lk E21 E23); [lia | exact Hhi | exact HRA | exact Happ].
Qed.

Lemma m2_entry2 : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) mem lk,
  getr regs 21 = w64 SB -> getr regs 23 = w64 lk ->
  getr regs 24 = sv_denot (Eimg (Ereg regs [])) (SOff 23 8) ->
  getr regs 26 = sv_denot (Eimg (Ereg regs [])) m2_shx ->
  4096 <= lk -> lk + 12 <= alloc_ceiling -> lk mod 4 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) (lk + 8) 4 0 ->
  (forall a, lk + 8 <= a < lk + 12 -> apresent (w_H W) mem a) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF lk 12 ->
  (lk + 12 <= kLowShadowBeg \/ kHighMemBeg <= lk) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) m2_ss2
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + PC_M2C)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS m2_Bx m2_SH (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros fq W regs mem lk H21 H23 H24 H26 Hlo Hhi Hal Hmem Hpres HRA Happ.
pose proof (proj1 (@ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])) in *.
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 21 21%bv eq_refl); exact H21).
assert (E23 : ew E 23 = Z_to_bv 64 lk) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
split.
- unfold m2_ss2. apply pa_entry_st_ok_full.
  + unfold m2_sr2. apply YI04.regs_ok_pin; [apply YI04.regs_ok_pin; [apply regs_ok_Eimg_Ereg | | exact H24] | | exact H26];
    intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, m2_lkr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ lk 8 4 _ 0); [reflexivity | zside | zside | exact Hmem].
  + cbn [pairwise_disjoint all_disjoint]. split; exact I.
  + destruct (m2_lk_facts E lk E21 E23 Hlo Hhi Hal) as [F21 F23].
    split; [|split; exact I]. cbn [m2_facts2 f_atoms atoms_ok]. split; [exact F21|]. split; [exact F23 | exact I].
- apply (m2_shok _ mem E lk E21 E23); [lia | exact Hhi | exact HRA | exact Happ].
Qed.

Lemma m2_shx_agree : forall E E', ew E 23 = ew E' 23 -> ew E 21 = ew E' 21 -> sv_denot E m2_shx = sv_denot E' m2_shx.
Proof. intros E E' H23 H21. unfold m2_shx. cbn [sv_denot]. rewrite H23, H21. reflexivity. Qed.

Lemma m2_not_wr : forall E a lk, bv_unsigned (ew E 23) = lk -> ~ (lk + 8 <= a < lk + 12) ->
  ~ in_wrange E (ss_mem m2_ss2) a.
Proof.
intros E a lk H Ha (r & Hin & Hr). cbn [ss_mem m2_ss2 In] in Hin. destruct Hin as [<-|[]].
cbn [m2_lkr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite H in Hr. lia.
Qed.

Lemma m2_pres_grows : forall (m m' : word -> option byte) (H : word -> bool) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros m m' H a HG (Hh & b & Hb). split; [exact Hh|].
assert (Hne : mrestrict H m' (Z_to_bv 64 a) <> None).
{ apply HG. unfold mrestrict. rewrite Hh, Hb. discriminate. }
unfold mrestrict in Hne. rewrite Hh in Hne. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. apply Hne. reflexivity.
Qed.

Lemma m2_ra_keep : forall H (m m' : word -> option byte) B0 a len,
  range_addressable (aview SEGS H m) B0 a len ->
  (forall x, a <= x < a + len -> aview SEGS H m' (shadow_of_addr B0 x) = aview SEGS H m (shadow_of_addr B0 x)) ->
  range_addressable (aview SEGS H m') B0 a len.
Proof. intros H m m' B0 a len Hra Hk x Hx. rewrite (Hk x Hx). exact (Hra x Hx). Qed.

Lemma m2_aview_garr8Z : forall H m base l j, garr8 SEGS (mrestrict H m) base l -> (j < length l)%nat ->
  aview SEGS H m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m base l j Hg Hj. destruct (Hg j Hj) as [_ Hr]. unfold aview.
rewrite (garr8_mbyte SEGS _ base l j Hg Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma m2_src_shadow : forall H m F, F mod 32 = 0 -> 0 <= F ->
  garr8 SEGS (mrestrict H m) (SHADOW_OFF + F / 8) PAT_A ->
  range_addressable (aview SEGS H m) SHADOW_OFF (F + 36) 6 /\ shadow_hull_vis (aview SEGS H m) (F + 36) 6.
Proof.
intros H m F HF HF0 Hg.
assert (HV : forall j, 0 <= j < 32 -> aview SEGS H m (SHADOW_OFF + F / 8 + j) = Some (nth (Z.to_nat j) PAT_A 0)).
{ intros j Hj. rewrite <- (Z2Nat.id j) at 1 by lia. apply m2_aview_garr8Z; [exact Hg | cbn; lia]. }
assert (Hq : exists q, F = 32 * q) by (exists (F / 32); Z.div_mod_to_equations; lia).
destruct Hq as [q Hq].
split.
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  assert (Hx8 : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5) by (rewrite Hq in Hx |- *; Z.div_mod_to_equations; lia).
  destruct Hx8 as [E8|E8]; rewrite E8, Z.add_assoc, HV by lia; reflexivity.
- intros s Hs. unfold shadow_addr in Hs.
  assert (Hr : SHADOW_OFF + F / 8 <= s < SHADOW_OFF + F / 8 + 32)
    by (unfold SHADOW_OFF in *; rewrite Hq in Hs |- *; Z.div_mod_to_equations; lia).
  replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia. rewrite HV by lia. discriminate.
Qed.

Ltac m2_awr_ro := lazymatch goal with |- awr_ok ?E ?rs ?a ?b ?c ?d ?e ?f ?g =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' a b c d e f g) end;
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].

Ltac m2_ro HM :=
  lazymatch goal with HF : frame_of _ ?rs _ (ms_mem ?m1) |- _ =>
    let H := fresh "HMx" in pose proof (frame_of_read_only _ rs _ _ eq_refl HF) as H; clear HF;
    try (rewrite HM in H; clear HM); rename H into HM end;
  repeat match goal with
  | H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : forall fq, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis NOW : cls_now_ok B.
Hypothesis KS : cls_kept_step_ok B.

Lemma m2_cut_same : forall cx fpos pc pc' RV RV' O3 L3 SHP PS PS' LS LS' W3 ly3 S3 regs3 mem3 md3 regs4 md4,
  cls_cut B cx fpos pc RV O3 L3 SHP PS LS W3 ly3 S3 regs3 mem3 md3 ->
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem3 md4 (x_k cx) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 27] -> getr regs4 (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) ->
  Forall (fun rv => getr regs4 (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV' ->
  (PS' = None \/ PS' = PS) -> (LS' = true -> LS = true) ->
  cls_cut B cx fpos pc' RV' O3 L3 SHP PS' LS' W3 ly3 S3 regs4 mem3 md4.
Proof.
intros cx fpos pc pc' RV RV' O3 L3 SHP PS PS' LS LS' W3 ly3 S3 regs3 mem3 md3 regs4 md4 HC HJ HR HRV HPS HLS.
unfold cls_cut in *. cbv zeta in *.
destruct HC as (_ & Hfrs & Hnin & Hperm & Hfa & Hfl & Hkept & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G27 &
  _ & Gsp & Go & Gf & GF & GLS & Hshl & Hsh & HFLv & HPSf & HO3l & HO3 & HL3).
split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hnin|]. split; [exact Hperm|].
split; [exact Hfa|]. split; [exact Hfl|]. split; [exact Hkept|].
split; [exact (eq_trans (HR 2 ltac:(m2_in)) G2)|].
split; [exact (eq_trans (HR 3 ltac:(m2_in)) G3)|].
split; [exact (eq_trans (HR 4 ltac:(m2_in)) G4)|].
split; [exact (eq_trans (HR 8 ltac:(m2_in)) G8)|].
split; [exact (eq_trans (HR 9 ltac:(m2_in)) G9)|].
split; [exact (eq_trans (HR 18 ltac:(m2_in)) G18)|].
split; [exact (eq_trans (HR 19 ltac:(m2_in)) G19)|].
split; [exact (eq_trans (HR 20 ltac:(m2_in)) G20)|].
split; [exact (eq_trans (HR 27 ltac:(m2_in)) G27)|].
split; [exact HRV|]. split; [exact Gsp|]. split; [exact Go|]. split; [exact Gf|]. split; [exact GF|].
split; [intros HT; exact (GLS (HLS HT))|].
split; [exact Hshl|]. split; [exact Hsh|]. split; [exact HFLv|].
split; [destruct HPS as [-> | ->]; [exact I | exact HPSf]|].
split; [exact HO3l|]. split; [exact HO3 | exact HL3].
Qed.

Lemma m2_consts : CLS_STK = 8512 /\ ESTACK = 4096. Proof. split; reflexivity. Qed.

Lemma m2_pre_misc : forall cx, cls_pre B cx ->
  getr (x_regs cx) 3 = w64 (as_gp B) /\ getr (x_regs cx) 4 = w64 (as_tp B) /\ length (x_FB cx) = 50%nat /\
  x_sp0 cx - x_STK cx <= cSP cx - CLS_STK /\ cSP cx <= x_sp0 cx /\
  match x_L cx with None => x_lk cx = 0 | Some Lb => 0 < x_lk cx /\ x_lk cx mod 4 = 0 /\ length Lb = 12%nat end.
Proof.
intros cx HP. unfold cls_pre in HP. cbv zeta in HP.
destruct HP as (_ & _ & _ & _ & H3 & H4 & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _ & _ & _ & HFB &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _).
split; [exact H3|]. split; [exact H4|]. split; [exact HFB|]. split; [exact Hstk|]. split; [exact Hsp0|].
destruct (x_L cx) as [Lb|]; [destruct HM as (H1 & H2 & H5 & _); exact (conj H1 (conj H2 H5)) | exact HM].
Qed.

Lemma m2_cut_lk : forall cx fpos pc pc' RV RV' Lb L3' W3 ly3 S3 regs3 mem3 md3 regs4 mem4 md4,
  cls_pre B cx -> x_L cx = Some Lb ->
  cls_cut B cx fpos pc RV (x_OB cx) (x_L cx) PAT_A (Some (cPS cx)) true W3 ly3 S3 regs3 mem3 md3 ->
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem4 md4 (x_k cx) ->
  tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 mem4 (cSP cx) (x_lk cx) (x_o cx) (x_L cx) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 27] -> getr regs4 (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) ->
  Forall (fun rv => getr regs4 (Z_to_bv 5 (fst rv)) = w64 (snd rv)) RV' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_lk cx <= a < x_lk cx + 12) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
     mbyte SEGS (mrestrict (w_H W3) mem4) a = mbyte SEGS (mrestrict (w_H W3) mem3) a) ->
  length L3' = 12%nat -> garr8 SEGS (mrestrict (w_H W3) mem4) (x_lk cx) (cls_bytes L3') ->
  cls_cut B cx fpos pc' RV' (x_OB cx) (Some L3') PAT_A (Some (cPS cx)) true W3 ly3 S3 regs4 mem4 md4.
Proof.
intros cx fpos pc pc' RV RV' Lb L3' W3 ly3 S3 regs3 mem3 md3 regs4 mem4 md4 HPRE HL HC HJ HK HR HRV HKP HLl HLg.
pose proof (NOW cx fpos pc RV (x_OB cx) (x_L cx) PAT_A (Some (cPS cx)) true W3 ly3 S3 regs3 mem3 md3 HPRE HC) as HN.
cbv zeta in HN.
destruct HN as ((HF4096 & HFceil & HF32 & HFz & HFapp & _) & _ & _ & _ & HOok & _ & _ & _ & HLk).
rewrite HL in HLk. destruct HLk as (HLok & HL4096 & HLceil & _).
destruct HLok as ((HLa0 & HLa47 & HLam & HLimg & HLapp) & _ & HLF & HLsp).
destruct HOok as ((HOa0 & HOa47 & _) & _ & _ & HOsp).
pose proof HPRE as HP. unfold cls_pre in HP. cbv zeta in HP. rewrite HL in HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & HLdisj).
destruct HLdisj as (HLO & _ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (proj1 (@ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
destruct m2_consts as [CS ES].
assert (HS1 : cSP cx - 192 < cS1 cx <= cSP cx - 160) by (unfold cS1, cls_S1; Z.div_mod_to_equations; lia).
assert (HF8 : cF cx fpos / 8 + 32 <= 2 ^ 44) by (apply Z.le_add_le_sub_r; apply Z.div_le_upper_bound; lia).
assert (HF8b : 0 <= cF cx fpos / 8) by (apply Z.div_pos; lia).
unfold cls_cut in *. cbv zeta in *.
destruct HC as (_ & Hfrs & Hnin & Hperm & Hfa & Hfl & _ & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G27 &
  _ & Gsp & Go & Gf & GF & GLS & Hshl & Hsh & HFLv & HPSf & HO3l & HO3 & _).
unfold cSP in *.
unfold zone2, off_img, in_app, cls_addr, amem_range, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL, SHADOW_OFF in *.
split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hnin|]. split; [exact Hperm|].
split; [exact Hfa|]. split; [exact Hfl|]. split; [exact HK|].
split; [exact (eq_trans (HR 2 ltac:(m2_in)) G2)|].
split; [exact (eq_trans (HR 3 ltac:(m2_in)) G3)|].
split; [exact (eq_trans (HR 4 ltac:(m2_in)) G4)|].
split; [exact (eq_trans (HR 8 ltac:(m2_in)) G8)|].
split; [exact (eq_trans (HR 9 ltac:(m2_in)) G9)|].
split; [exact (eq_trans (HR 18 ltac:(m2_in)) G18)|].
split; [exact (eq_trans (HR 19 ltac:(m2_in)) G19)|].
split; [exact (eq_trans (HR 20 ltac:(m2_in)) G20)|].
split; [exact (eq_trans (HR 27 ltac:(m2_in)) G27)|].
split; [exact HRV|].
split.
{ rewrite Forall_forall in Gsp |- *. intros p Hp. specialize (Gsp p Hp).
  assert (Hb : -104 <= snd p <= -8).
  { unfold cls_spills in Hp. cbn [In] in Hp. repeat (destruct Hp as [<-|Hp]; [cbn [snd]; lia|]). destruct Hp. }
  apply (m2_val_mem_frame _ _ _ _ _ Gsp). intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply HKP; lia. }
split; [apply (m2_val_mem_frame _ _ _ _ _ Go); intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply HKP; lia|].
split; [apply (m2_val_mem_frame _ _ _ _ _ Gf); intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply HKP; lia|].
split; [apply (m2_val_mem_frame _ _ _ _ _ GF); intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply HKP; lia|].
split; [intros _; apply (m2_val_mem_frame _ _ _ _ _ (GLS eq_refl)); intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply HKP; lia|].
split; [exact Hshl|].
split; [apply (garr8_frame SEGS _ _ _ _ Hsh); intros x Hx; rewrite Hshl in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply HKP; lia|].
split; [apply (m2_val_mem_frame _ _ _ _ _ HFLv); intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply HKP; lia|].
split.
{ destruct HPSf as [HPSl HPSg]. split; [exact HPSl|].
  apply (garr8_frame SEGS _ _ _ _ HPSg). intros x Hx. unfold cls_bytes in Hx. rewrite length_map, HPSl in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  apply HKP; lia. }
split; [exact HO3l|].
split; [apply (garr8_frame SEGS _ _ _ _ HO3); intros x Hx; unfold cls_bytes in Hx; rewrite length_map, HO3l in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; apply HKP; lia|].
rewrite HL. split; [exact HLl | exact HLg].
Qed.

Section m.
Hypothesis HSW : cls_from_SW B.
Hypothesis HX : cls_from_X B.

Lemma m2_path_bad : forall cx fpos W3 ly3 S3 regs3 mem3 md3,
  cls_pre B cx -> cls_at_R2 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
  disco_classify_c.fsum (x_FB cx) <> 0 ->
  SRr SEGS W3 (cfg_at (fx := x_fq cx) SEGS (BASE + PC_R2) regs3 mem3 md3) (cls_Q B cx).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 HPRE HAT Hf.
pose proof HAT as (Hk0 & Hk1 & Hsrc & HC).
pose proof HC as HC'. unfold cls_cut in HC'. cbv zeta in HC'.
destruct HC' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GRV & _).
pose proof (m2_rv _ _ 10 _ GRV ltac:(m2_in)) as V10. rewrite (proj2 (Z.eqb_neq _ _) Hf) in V10.
destruct (m2_entry0 (x_fq cx) W3 regs3 mem3) as [HS SHOK].
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs3 []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 (-1)) by (subst E; rewrite (ew_Eimg_Ereg_nat regs3 [] 10 (Z_to_bv 5 10) eq_refl); exact V10).
clear HE.
unfold cfg_at. change (w64 (BASE + PC_R2)) with (Z_to_bv 64 (BASE + PC_R2)).
pose proof (paj_run (fx := x_fq cx) B LAWS) as RUN.
pose proof (paj_run_to (fx := x_fq cx) B LAWS) as RUNTO.
pose proof (paj_branch (fx := x_fq cx) (PI := PI)) as BR.
psrr_branch_tok RUN BR HS SHOK m2_Bspan.
2:{ exfalso. rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc. rewrite E10 in Hc. vm_compute in Hc. discriminate Hc. }
paj_run_to_tok RUNTO HS HJ SHOK m2_Bspan PC_X; [apply awr_ok_nil|].
pmkst HS.
lazymatch goal with HF : frame_of _ ?rs mem3 (ms_mem ?m1) |- _ => pose proof (frame_of_read_only _ rs _ _ eq_refl HF) as HM end.
rewrite HM in HJ |- *.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 [] [2; 3; 4; 8; 9; 18; 19; 20; 24; 27]%bv HS
  ltac:(cbn [extK]; m2_agree HAG) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
rewrite (m2_cfg _ _ PC_X) by reflexivity.
apply (HX cx fpos W3 ly3 S3 _ _ _ HPRE).
pose proof (m2_model_bad (x_FB cx) (x_len cx) (x_U cx) (x_L cx) Hk0 Hsrc Hk1 Hf) as HMb.
assert (ERet : cRet cx = -1) by (unfold cRet, disco_classify_c.cm_ret; rewrite HMb; reflexivity).
assert (EOut : cOut cx = x_OB cx) by (unfold cOut, disco_classify_c.cm_out; rewrite HMb; reflexivity).
assert (ELock : cLock cx = x_L cx) by (unfold cLock, disco_classify_c.cm_lock; rewrite HMb; reflexivity).
unfold cls_at_X. rewrite EOut, ELock, ERet.
apply (m2_cut_same cx fpos _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 mem3 md3 _ _ HC HJ).
- intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; apply HKr; m2_in.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. rewrite (HKr (Z_to_bv 5 24)) by m2_in.
  exact (m2_rv _ _ 24 _ GRV ltac:(m2_in)).
- left. reflexivity.
- intros Hq. discriminate Hq.
Qed.

Lemma m2_path_none : forall cx fpos W3 ly3 S3 regs3 mem3 md3,
  cls_pre B cx -> cls_at_R2 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
  disco_classify_c.fsum (x_FB cx) = 0 -> x_L cx = None ->
  SRr SEGS W3 (cfg_at (fx := x_fq cx) SEGS (BASE + PC_R2) regs3 mem3 md3) (cls_Q B cx).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 HPRE HAT Hf HL.
pose proof HAT as (Hk0 & Hk1 & Hsrc & HC).
pose proof (m2_model_ok (x_FB cx) (x_len cx) (x_U cx) (x_L cx) Hk0 Hsrc Hk1 Hf) as HMo.
pose proof (m2_pre_misc cx HPRE) as (_ & _ & _ & _ & _ & HPL). rewrite HL in HPL.
pose proof HC as HC'. unfold cls_cut in HC'. cbv zeta in HC'.
destruct HC' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GRV & _).
pose proof (m2_rv _ _ 10 _ GRV ltac:(m2_in)) as V10. rewrite Hf in V10.
pose proof (m2_rv _ _ 23 _ GRV ltac:(m2_in)) as V23. rewrite HPL in V23.
destruct (m2_entry0 (x_fq cx) W3 regs3 mem3) as [HS SHOK].
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs3 []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Eimg_Ereg_nat regs3 [] 10 (Z_to_bv 5 10) eq_refl); exact V10).
assert (E23 : ew E 23 = Z_to_bv 64 0) by (subst E; rewrite (ew_Eimg_Ereg_nat regs3 [] 23 (Z_to_bv 5 23) eq_refl); exact V23).
clear HE.
unfold cfg_at. change (w64 (BASE + PC_R2)) with (Z_to_bv 64 (BASE + PC_R2)).
pose proof (paj_run (fx := x_fq cx) B LAWS) as RUN.
pose proof (paj_run_to (fx := x_fq cx) B LAWS) as RUNTO.
pose proof (paj_branch (fx := x_fq cx) (PI := PI)) as BR.
psrr_branch_tok RUN BR HS SHOK m2_Bspan.
{ exfalso. rewrite (m2_br_ne0 _ 10 0) in Hc by first [m2_ew E10 | lia]. discriminate Hc. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK m2_Bspan PC_SW; [apply awr_ok_nil|].
m2_ro HM.
psrr_branch_tok RUN BR HS SHOK m2_Bspan.
2:{ exfalso. rewrite (m2_br_eq0 _ 23 0) in Hc by first [m2_ew E23 | lia]. discriminate Hc. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK m2_Bspan PC_SW; [apply awr_ok_nil|].
m2_ro HM.
pmkst HS. rewrite HM in HJ |- *.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 27]%bv HS
  ltac:(m2_agree HAG) ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
rewrite (m2_cfg _ _ PC_SW) by reflexivity.
apply (HSW cx fpos W3 ly3 S3 _ _ _ HPRE).
assert (ERet : cRet cx = 0) by (unfold cRet, disco_classify_c.cm_ret; rewrite HMo; reflexivity).
assert (ELock : cLock cx = x_L cx) by (unfold cLock, disco_classify_c.cm_lock; rewrite HMo, HL; reflexivity).
unfold cls_at_SW. split; [exact ERet|]. rewrite ELock.
apply (m2_cut_same cx fpos _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 mem3 md3 _ _ HC HJ).
- intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; apply HKr; m2_in.
- apply (m2_rv_sub [21; 22; 25] regs3 _ _ _ GRV).
  + intros r Hr. destruct Hr as [<-|[<-|[<-|[]]]]; apply HKr; m2_in.
  + repeat apply Forall_cons; try apply Forall_nil; split; m2_in.
- right. reflexivity.
- intros _. reflexivity.
Qed.

Lemma m2_after_cpy : forall cx fpos W3 ly3 S3 regs3 mem3 md3 Lb regs2 mem2 md2,
  cls_pre B cx -> cls_at_R2 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
  disco_classify_c.fsum (x_FB cx) = 0 -> x_L cx = Some Lb -> disco_classify_c.lv Lb = 0 ->
  ajournal SEGS B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
    ((2, fpos) :: x_own cx) ly3 S3 W3 mem2 md2 (x_k cx) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27] -> getr regs2 (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) ->
  getr regs2 24 = sv_denot (Eimg (Ereg regs2 [])) (SOff 23 8) ->
  getr regs2 26 = sv_denot (Eimg (Ereg regs2 [])) m2_shx ->
  (forall i, 0 <= i < 6 -> aview SEGS (w_H W3) mem2 (x_lk cx + i) = aview SEGS (w_H W3) mem3 (cF cx fpos + 36 + i)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_lk cx <= a < x_lk cx + 6) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
     aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem2 a) ->
  SRr SEGS W3 (mkCfg (mkst (fx := x_fq cx) regs2 (Z_to_bv 64 (BASE + PC_M2C)) mem2 (seg_rom SEGS)) md2) (cls_Q B cx).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Lb regs2 mem2 md2 HPRE HAT Hf HL Hlv HJ2 HK2 H24 H26 Heff Hfr Hpres2.
pose proof HAT as (Hk0 & Hk1 & Hsrc & HC).
pose proof (m2_model_ok (x_FB cx) (x_len cx) (x_U cx) (x_L cx) Hk0 Hsrc Hk1 Hf) as HMo.
assert (ERet : cRet cx = 0) by (unfold cRet, disco_classify_c.cm_ret; rewrite HMo; reflexivity).
assert (ELock : cLock cx = Some (disco_classify_c.latch (x_FB cx) Lb))
  by (unfold cLock, disco_classify_c.cm_lock; rewrite HMo, HL, Hlv; reflexivity).
pose proof (m2_pre_misc cx HPRE) as (_ & _ & PFBl & Pstk & Psp0 & HPL). rewrite HL in HPL. destruct HPL as (Hlk0 & Hlk4 & HLbl).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 HPRE HC) as HN. cbv zeta in HN.
destruct HN as ((HF4096 & HFceil & HF32 & HFz & HFapp & _) & _ & _ & _ & _ & _ & _ & _ & HLk).
rewrite HL in HLk. destruct HLk as (HLok & HL4096 & HLceil & HLwr).
destruct HLok as ((HLa0 & HLa47 & HLam & HLimg & HLapp) & (HLpr & HLra & HLhv) & HLF & HLsp).
pose proof HC as HC'. unfold cls_cut in HC'. cbv zeta in HC'.
destruct HC' as (HJ3 & Hfrs & Hnin & Hperm & Hfa & Hfl & Hkept & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  GRV & _ & _ & _ & _ & _ & _ & _ & _ & HPSf & _ & _ & HL3).
rewrite HL in HL3. destruct HL3 as (_ & HLbg). destruct HPSf as (HPSl & HPSg).
pose proof (proj1 HJ3) as HAR3.
pose proof (m2_val_lv _ _ _ HLbl HLbg) as (Mlv & _). rewrite Hlv in Mlv.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (proj1 (@ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
destruct m2_consts as [CS ES].
assert (HS1 : cSP cx - 192 < cS1 cx <= cSP cx - 160) by (unfold cS1, cls_S1; Z.div_mod_to_equations; lia).
unfold cSP in *.
pose proof (m2_rv _ _ 21 _ GRV ltac:(m2_in)) as V21.
pose proof (m2_rv _ _ 23 _ GRV ltac:(m2_in)) as V23.
assert (R21 : getr regs2 21 = w64 SB) by exact (eq_trans (HK2 21 ltac:(m2_in)) V21).
assert (R23 : getr regs2 23 = w64 (x_lk cx)) by exact (eq_trans (HK2 23 ltac:(m2_in)) V23).
assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (x_lk cx <= a < x_lk cx + 6) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
  mbyte SEGS (mrestrict (w_H W3) mem2) a = mbyte SEGS (mrestrict (w_H W3) mem3) a)
  by (intros a Ha H1 H2; apply (mbyte_of_aview SEGS); apply Hfr; assumption).
assert (Hmem2 : val_mem SEGS (mrestrict (w_H W3) mem2) (x_lk cx + 8) 4 0).
{ apply (m2_val_mem_frame _ _ _ _ _ Mlv). intros x Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. apply KL; lia. }
assert (Hpr2 : forall a, x_lk cx + 8 <= a < x_lk cx + 12 -> apresent (w_H W3) mem2 a)
  by (intros a Ha; apply Hpres2; apply HLpr; lia).
assert (Hra2 : range_addressable (aview SEGS (w_H W3) mem2) SHADOW_OFF (x_lk cx) 12).
{ apply (m2_ra_keep _ mem3 mem2 _ _ _ HLra). intros x Hx. unfold shadow_of_addr.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply Hfr; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia. }
destruct (m2_entry2 (x_fq cx) W3 regs2 mem2 (x_lk cx) R21 R23 H24 H26 HL4096 HLceil Hlk4 Hmem2 Hpr2 Hra2 HLapp) as [HS SHOK].
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs2 []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E23 : ew E 23 = Z_to_bv 64 (x_lk cx)) by (subst E; rewrite (ew_Eimg_Ereg_nat regs2 [] 23 23%bv eq_refl); exact R23).
clear HE.
pose proof (paj_run_to (fx := x_fq cx) B LAWS) as RUNTO.
paj_run_to_tok RUNTO HS HJ2 SHOK m2_Bspan PC_SW.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?a ?b ?c ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' a b c d e f g) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (x_lk cx)); [reflexivity | rewrite E23; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply HLwr. lia. }
pmkst HS.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 27]%bv HS
  ltac:(m2_agree HAG) ltac:(vm_compute; reflexivity)) as HKf.
cbn [ms_regs restrict] in HKf.
pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
pose proof (field_of_region _ _ 23%nat (x_lk cx) _ 0 12 8 12 8 4%N (SLit 1) 1 HRf
  ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E23; apply unsigned_lit_small; lia)
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vf.
change (N.to_nat 4) with 4%nat in Vf.
rewrite (m2_cfg _ _ PC_SW) by reflexivity.
apply (HSW cx fpos W3 ly3 S3 _ _ _ HPRE).
unfold cls_at_SW. split; [exact ERet|]. rewrite ELock.
set (memf := ms_mem ms) in *.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (x_lk cx + 8 <= a < x_lk cx + 12) ->
  aview SEGS (w_H W3) memf a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  apply (m2_not_wr E a (x_lk cx)); [rewrite E23; apply unsigned_lit_small; lia | exact Hn]. }
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (x_lk cx <= a < x_lk cx + 12) -> ~ (cS1 cx - ESTACK <= a < cS1 cx) ->
  aview SEGS (w_H W3) memf a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H1 H2. rewrite (KF a Ha) by lia. apply Hfr; [exact Ha | lia | exact H2]. }
assert (HKS : tcls_kept B (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) W3 memf (cSP cx) (x_lk cx) (x_o cx) (x_L cx)).
{ apply (KS cx fpos W3 ly3 S3 mem3 md3 memf (fun a => (x_lk cx <= a < x_lk cx + 12) \/ (cS1 cx - ESTACK <= a < cS1 cx))
    HPRE HAR3 Hfrs Hnin Hperm Hfa Hfl Hkept).
  - intros a Ha Hn. apply KV; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; exact H].
  - intros a Hp. apply (m2_pres_grows mem2 memf); [exact HG | apply Hpres2; exact Hp].
  - intros a [Ha|Ha]; [right; left; unfold cls_wr; right; rewrite HL; exact Ha | left; unfold cSP; lia]. }
apply (m2_cut_lk cx fpos _ _ _ _ Lb _ W3 ly3 S3 regs3 mem3 md3 _ memf _ HPRE HL HC HJ2 HKS).
- intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]];
  (etransitivity; [apply HKf; m2_in|]); apply HK2; m2_in.
- apply (m2_rv_sub [21; 22; 25] regs3 _ _ _ GRV).
  + intros r Hr. destruct Hr as [<-|[<-|[<-|[]]]]; (etransitivity; [apply HKf; m2_in|]); apply HK2; m2_in.
  + repeat apply Forall_cons; try apply Forall_nil; split; m2_in.
- intros a Ha H1 H2. apply (mbyte_of_aview SEGS). apply KV; assumption.
- apply m2_latch_len; assumption.
- apply m2_garr8_of_aview. intros j Hj. rewrite (m2_latch_len _ _ PFBl HLbl) in Hj.
  rewrite (m2_latch_nth _ _ j PFBl HLbl Hj).
  destruct (Nat.ltb_spec j 6) as [H6|H6].
  + rewrite KF, Heff by lia.
    replace (cF cx fpos + 36 + Z.of_nat j) with (cF cx fpos + 32 + Z.of_nat (4 + j)) by lia.
    rewrite (m2_aview_of_garr8 _ _ _ _ _ HPSg) by (rewrite HPSl; lia).
    unfold cPS. rewrite (m2_ps_src (x_len cx) (x_FB cx) j Hk0 H6). reflexivity.
  + destruct (Nat.ltb_spec j 8) as [H8|H8].
    * rewrite KF, Hfr by lia. rewrite (m2_aview_of_garr8 _ _ _ _ _ HLbg) by (rewrite HLbl; lia). reflexivity.
    * assert (Hj4 : (j = 8 \/ j = 9 \/ j = 10 \/ j = 11)%nat) by lia.
      destruct Hj4 as [ -> | [ -> | [ -> | -> ] ] ]; unfold aview;
      [ replace (x_lk cx + Z.of_nat 8) with (x_lk cx + 8 + Z.of_nat 0) by lia; rewrite (Vf 0%nat) by lia
      | replace (x_lk cx + Z.of_nat 9) with (x_lk cx + 8 + Z.of_nat 1) by lia; rewrite (Vf 1%nat) by lia
      | replace (x_lk cx + Z.of_nat 10) with (x_lk cx + 8 + Z.of_nat 2) by lia; rewrite (Vf 2%nat) by lia
      | replace (x_lk cx + Z.of_nat 11) with (x_lk cx + 8 + Z.of_nat 3) by lia; rewrite (Vf 3%nat) by lia ];
      vm_compute; reflexivity.
Qed.

Lemma m2_path_some : forall cx fpos W3 ly3 S3 regs3 mem3 md3 Lb,
  cls_pre B cx -> cls_at_R2 B cx fpos W3 ly3 S3 regs3 mem3 md3 ->
  disco_classify_c.fsum (x_FB cx) = 0 -> x_L cx = Some Lb ->
  SRr SEGS W3 (cfg_at (fx := x_fq cx) SEGS (BASE + PC_R2) regs3 mem3 md3) (cls_Q B cx).
Proof.
intros cx fpos W3 ly3 S3 regs3 mem3 md3 Lb HPRE HAT Hf HL.
pose proof HAT as (Hk0 & Hk1 & Hsrc & HC).
pose proof (m2_model_ok (x_FB cx) (x_len cx) (x_U cx) (x_L cx) Hk0 Hsrc Hk1 Hf) as HMo.
assert (ERet : cRet cx = 0) by (unfold cRet, disco_classify_c.cm_ret; rewrite HMo; reflexivity).
pose proof (m2_pre_misc cx HPRE) as (Pgp & Ptp & PFBl & Pstk & Psp0 & HPL). rewrite HL in HPL. destruct HPL as (Hlk0 & Hlk4 & HLbl).
pose proof (NOW cx fpos _ _ _ _ _ _ _ W3 ly3 S3 regs3 mem3 md3 HPRE HC) as HN. cbv zeta in HN.
destruct HN as ((HF4096 & HFceil & HF32 & HFz & HFapp & _) & _ & _ & _ & _ & _ & _ & _ & HLk).
rewrite HL in HLk. destruct HLk as (HLok & HL4096 & HLceil & HLwr).
destruct HLok as ((HLa0 & HLa47 & HLam & HLimg & HLapp) & (HLpr & HLra & HLhv) & HLF & HLsp).
pose proof HC as HC'. unfold cls_cut in HC'. cbv zeta in HC'.
destruct HC' as (HJ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _ & _ & _ & _ & _ & _ &
  GRV & _ & _ & _ & _ & _ & _ & Hsh & _ & HPSf & _ & _ & HL3).
rewrite HL in HL3. destruct HL3 as (_ & HLbg). destruct HPSf as (HPSl & HPSg).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (proj1 (@ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
destruct m2_consts as [CS ES].
assert (HS1 : cSP cx - 192 < cS1 cx <= cSP cx - 160) by (unfold cS1, cls_S1; Z.div_mod_to_equations; lia).
assert (HS1m : cS1 cx mod 32 = 0) by (unfold cS1, cls_S1; rewrite Z.mul_comm; apply Z_mod_mult).
unfold cSP in *.
pose proof (m2_rv _ _ 10 _ GRV ltac:(m2_in)) as V10. rewrite Hf in V10.
pose proof (m2_rv _ _ 21 _ GRV ltac:(m2_in)) as V21.
pose proof (m2_rv _ _ 23 _ GRV ltac:(m2_in)) as V23.
pose proof (m2_rv _ _ 25 _ GRV ltac:(m2_in)) as V25.
destruct (m2_val_lv _ _ _ HLbl HLbg) as (Mlv & Rlv).
destruct (m2_entry1 (x_fq cx) W3 regs3 mem3 (x_lk cx) (disco_classify_c.lv Lb) V21 V23 HL4096 HLceil Hlk4 Rlv Mlv HLra HLapp)
  as [HS SHOK].
remember (Eimg (Ereg regs3 [Z_to_bv 64 (disco_classify_c.lv Lb)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs3 [Z_to_bv 64 (disco_classify_c.lv Lb)]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Eimg_Ereg_nat regs3 _ 10 (Z_to_bv 5 10) eq_refl); exact V10).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (subst E; rewrite (ew_Eimg_Ereg_nat regs3 _ 21 (Z_to_bv 5 21) eq_refl); exact V21).
assert (E23 : ew E 23 = Z_to_bv 64 (x_lk cx)) by (subst E; rewrite (ew_Eimg_Ereg_nat regs3 _ 23 (Z_to_bv 5 23) eq_refl); exact V23).
assert (E25 : ew E 25 = Z_to_bv 64 (cF cx fpos + 36)) by (subst E; rewrite (ew_Eimg_Ereg_nat regs3 _ 25 (Z_to_bv 5 25) eq_refl); exact V25).
assert (E32 : ew E 32 = Z_to_bv 64 (disco_classify_c.lv Lb))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
clear HE.
unfold cfg_at. change (w64 (BASE + PC_R2)) with (Z_to_bv 64 (BASE + PC_R2)).
pose proof (paj_run (fx := x_fq cx) B LAWS) as RUN.
pose proof (paj_run_to (fx := x_fq cx) B LAWS) as RUNTO.
pose proof (paj_branch (fx := x_fq cx) (PI := PI)) as BR.
psrr_branch_tok RUN BR HS SHOK m2_Bspan.
{ exfalso. rewrite (m2_br_ne0 _ 10 0) in Hc by first [m2_ew E10 | lia]. discriminate Hc. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK m2_Bspan PC_SW; [m2_awr_ro|].
m2_ro HM.
psrr_branch_tok RUN BR HS SHOK m2_Bspan.
- rewrite (m2_br_lv _ (disco_classify_c.lv Lb)) in Hc by first [m2_ew E32 | lia].
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK m2_Bspan PC_SW; [m2_awr_ro|].
  m2_ro HM.
  pmkst HS. rewrite HM in HJ |- *.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 27]%bv HS
    ltac:(m2_agree HAG) ltac:(vm_compute; reflexivity)) as HKr.
  cbn [ms_regs restrict] in HKr.
  rewrite (m2_cfg _ _ PC_SW) by reflexivity.
  apply (HSW cx fpos W3 ly3 S3 _ _ _ HPRE).
  assert (ELock : cLock cx = x_L cx)
    by (unfold cLock, disco_classify_c.cm_lock; rewrite HMo, HL, (proj2 (Z.eqb_neq _ _) Hc); reflexivity).
  unfold cls_at_SW. split; [exact ERet|]. rewrite ELock.
  apply (m2_cut_same cx fpos _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 mem3 md3 _ _ HC HJ).
  + intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; apply HKr; m2_in.
  + apply (m2_rv_sub [21; 22; 25] regs3 _ _ _ GRV).
    * intros r Hr. destruct Hr as [<-|[<-|[<-|[]]]]; apply HKr; m2_in.
    * repeat apply Forall_cons; try apply Forall_nil; split; m2_in.
  + right. reflexivity.
  + intros _. reflexivity.
- rewrite (m2_br_lv _ (disco_classify_c.lv Lb)) in Hc by first [m2_ew E32 | lia].
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hlv.
  paj_run_to_tok RUNTO HS HJ SHOK m2_Bspan PC_SW; [m2_awr_ro|].
  m2_ro HM.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into mc end.
  pmkst HS. rewrite HM in HJ |- *.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs3 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 27]%bv HS
    ltac:(m2_agree HAG) ltac:(vm_compute; reflexivity)) as HKc.
  cbn [ms_regs restrict] in HKc.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ 24%bv HS) as Q24.
  pose proof (st_ok_restrict_reg SEGS _ _ _ _ 26%bv HS) as Q26.
  lazymatch type of Q24 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in Q24 end.
  lazymatch type of Q26 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in Q26 end.
  rewrite E23 in Q10. rewrite E25 in Q11.
  assert (HspT : spZ (ms_regs mc) = cS1 cx).
  { unfold spZ. rewrite (HKc 2%bv) by m2_in. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  destruct (m2_src_shadow (w_H W3) mem3 (cF cx fpos) HF32 ltac:(lia) Hsh) as [HRS HHS].
  eapply SRr_bind.
  { refine (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY (x_fq cx)) W3 (ms_regs mc) mem3
      (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) ((2, fpos) :: x_own cx) ly3 S3 _
      (x_k cx) (x_lk cx) (cF cx fpos + 36) 6 (cS1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + PC_M2C)) HJ Q10 Q11 Q12
      _ _ _ _ _ _ _ _ _ Q1 _ _ _ _ _ _).
    - lia.
    - lia.
    - lia.
    - rewrite HspT. lia.
    - pose proof (Z.div_mod (cS1 cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D2.
      rewrite HS1m in D1. rewrite Hsp16 in D2.
      replace (cS1 cx - x_sp0 cx) with ((2 * (cS1 cx / 32) - x_sp0 cx / 16) * 16) by lia. apply Z_mod_mult.
    - lia.
    - lia.
    - rewrite (HKc 3%bv) by m2_in. rewrite G3. exact Pgp.
    - rewrite (HKc 4%bv) by m2_in. rewrite G4. exact Ptp.
    - apply ret_ok_codeptr_v; unfold PC_M2C, AF_both3_classify_core; [lia | reflexivity].
    - intros a Ha. split; [apply HLwr; lia | lia].
    - unfold amem_range in *. lia.
    - apply (range_addressable_sub _ _ _ _ _ _ HLra); lia.
    - intros _. apply (m2_hull_sub _ _ 12); [exact HLhv | lia | lia].
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - replace a with (cF cx fpos + 32 + Z.of_nat (Z.to_nat (a - (cF cx fpos + 32)))) by lia.
          rewrite (m2_aview_of_garr8 _ _ _ _ _ HPSg) by (rewrite HPSl; lia). discriminate.
        - rewrite HspT. lia. }
      split; [lia|]. split.
      { unfold amem_range, zone2, off_img, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
      split; [exact HRS | intros _; exact HHS]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Heff & Hfr & Hpres2).
  assert (W23 : ew (Eimg (Ereg regs2 [])) 23 = Z_to_bv 64 (x_lk cx)).
  { rewrite (ew_Eimg_Ereg_nat regs2 [] 23 (Z_to_bv 5 23) eq_refl).
    exact (eq_trans (HP2 23 ltac:(unfold acallee_saved; lia)) (eq_trans (HKc (Z_to_bv 5 23) ltac:(m2_in)) V23)). }
  assert (W21 : ew (Eimg (Ereg regs2 [])) 21 = Z_to_bv 64 SB).
  { rewrite (ew_Eimg_Ereg_nat regs2 [] 21 (Z_to_bv 5 21) eq_refl).
    exact (eq_trans (HP2 21 ltac:(unfold acallee_saved; lia)) (eq_trans (HKc (Z_to_bv 5 21) ltac:(m2_in)) V21)). }
  apply (m2_after_cpy cx fpos W3 ly3 S3 regs3 mem3 md3 Lb regs2 mem2 md2 HPRE HAT Hf HL Hlv HJ2).
  + intros r Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
    (etransitivity; [apply HP2; unfold acallee_saved; lia|]); apply HKc; m2_in.
  + refine (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) (eq_trans Q24 _)).
    apply m2_soff_agree. rewrite W23. m2_ew E23.
  + refine (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) (eq_trans Q26 _)).
    apply m2_shx_agree; [rewrite W23; m2_ew E23 | rewrite W21; m2_ew E21].
  + exact Heff.
  + intros a Ha H1 H2. apply Hfr; [exact Ha | exact H1 | lia].
  + exact Hpres2.
Qed.

Lemma cls_m2_gen : cls_from_R2 B.
Proof.
unfold cls_from_R2, cls_from. intros cx fpos W3 ly3 S3 regs3 mem3 md3 HPRE HAT.
destruct (Z.eq_dec (disco_classify_c.fsum (x_FB cx)) 0) as [Hf|Hf].
- destruct (x_L cx) as [Lb|] eqn:HL.
  + exact (m2_path_some cx fpos W3 ly3 S3 regs3 mem3 md3 Lb HPRE HAT Hf HL).
  + exact (m2_path_none cx fpos W3 ly3 S3 regs3 mem3 md3 HPRE HAT Hf HL).
- exact (m2_path_bad cx fpos W3 ly3 S3 regs3 mem3 md3 HPRE HAT Hf).
Qed.

End m.

Lemma cls_m2 : cls_from_SW B -> cls_from_X B -> cls_from_R2 B.
Proof. exact cls_m2_gen. Qed.

End h.
End f.
End d.

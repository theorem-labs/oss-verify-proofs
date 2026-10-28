(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNAEK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition argp (top : Z) (FF : list fframe) (sp v p n : Z) : Prop :=   (* [comment removed for export] *)
  (PMSPA.aobjA FF p n \/ (sp <= p /\ p + n <= top)) /\ (p + n <= v \/ v + 24 <= p).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma stack_zeros12 M sp : shadow_zero M (sp - 12288) 1536 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
  intros SZ S16 i Hi. pose proof (SZ (1024 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
  replace (sp / 8 + 2147450368 + i) with ((sp - 12288) / 8 + 2147450880 + (1024 + i)) by Lia.lia. exact X.
Qed.
Lemma zsh1 M p : byte_at M (S p) 0 -> L5KA.zeros_at M (p / 8 + 2147450880) 1.
Proof. intros X i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r. unfold byte_at, S, SB in X. exact X. Qed.
Lemma shadow_low b c j : 0 <= b -> b + c <= 2 ^ 47 -> 0 <= j < c / 8 -> 2147450880 <= S b + j < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma shadow_lowU b c j : 0 <= b -> b + c <= 2 ^ 47 -> 0 <= j < (c + 7) / 8 -> 2147450880 <= S b + j < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
(* [comment removed for export] *)
Lemma sh_apartU b c x o : b mod 8 = 0 -> o mod 8 = 0 -> 0 < c -> 0 <= b -> 0 <= o <= x -> (x < b \/ b + c <= o) -> ~ in_shadow_of b c (S x).
Proof. unfold in_shadow_of, S, SB. intros. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma vis_u8 H M1 M1v a v : mrestrict H M1 = M1v -> L5A.avis H a 1 -> 0 <= a -> a < 2 ^ 63 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v.
Proof. intros E AV H0 H1 X. rewrite <- E in X. exact (proj1 (L5A.u8_at_vis H M1 a v AV ltac:(Lia.lia) ltac:(Lia.lia)) X). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma S_range x : 0 <= x < 2 ^ 47 -> 2147450880 <= S x < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma S_add8 a j : S a + j = S (a + 8 * j).
Proof. unfold S. Lia.lia. Qed.
Lemma stk_sh_idx sp i : sp mod 16 = 0 -> 0 <= i < 512 -> sp / 8 + 2147450368 + i = S (sp - 4096 + 8 * i).
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma d40 x : (40 * x) / 8 = 5 * x.
Proof. Lia.lia. Qed.
Lemma d40b x : (40 * x + 40) / 8 = 5 * x + 5.
Proof. Lia.lia. Qed.
Lemma pow2k k : 0 <= k <= 11 -> 1 <= 2 ^ k <= 2048.
Proof. intros Hk. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(Lia.lia) ltac:(Lia.lia)); Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Lemma mul_to fx R M (pc : Z) (W : bv 32) (rd rs1 rs2 : bv 5) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  msteps RSEGS (st fx R pc M) (st fx (regupd R rd (v_mul (getr R rs1) (getr R rs2))) (pc + 4) M).
Proof.
  intros HF HE HD HZ H0 H1. eapply mst_step; [reflexivity| | apply mst_refl].
  rewrite (step_mul RSEGS R (Z_to_bv 64 pc) M (seg_rom RSEGS) W rd rs1 rs2 HF HE HD). rewrite HZ.
  f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma v_srai3_small d : 0 <= d < 2 ^ 63 -> v_srai (Z_to_bv 64 d) 3 = Z_to_bv 64 (d / 8).
Proof.
  intros Hd. unfold v_srai. f_equal.
  assert (S1 : bv_signed (Z_to_bv 64 d) = d).
  { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (bv_half_modulus 64) with (2 ^ 63). rewrite (Z.mod_small d) by lia. rewrite (Z.mod_small (d + 2 ^ 63)) by lia. lia. }
  rewrite S1. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma v_mul_magic40 n : 0 <= n <= 2 ^ 60 -> v_mul (Z_to_bv 64 (40 * n / 8)) (Z_to_bv 64 14757395258967641293) = Z_to_bv 64 n.
Proof.
  intros Hn. unfold v_mul. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (40 * n / 8) with (5 * n) by lia. rewrite (Z.mod_small (5 * n)) by lia. rewrite (Z.mod_small 14757395258967641293) by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (5 * n * 14757395258967641293) with (n + (4 * n) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma blk_facts LB FF LK cr Aw M V q m : ri_inv HI LB FF LK cr Aw M V -> In (q, m) LB ->
  4096 <= q /\ 0 < m /\ q + m <= ahl_ceil ar /\ q + m <= 2 ^ 47 /\ q mod 16 = 0 /\ (q + m <= 65536 \/ 0x696000 <= q)
  /\ (2147446784 + 17592186048512 <= q \/ q + m <= 2147446784) /\ L5.defined M q m
  /\ (forall f, In f FF -> q + m <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= q).
Proof.
  intros HH Hin. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB (q, m) Hin) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & QD & _ & _ & _ & QF & _). cbn [fst snd] in *.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Q2|]. split; [lia|]. split; [lia|]. split; [exact QD|].
  intros f Hf. apply QF. apply in_or_app. left. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma arg_facts LB FF LK cr Aw M V sp scr v p n : ri_inv HI LB FF LK cr Aw M V -> L5CA.astk ar M sp scr -> 0 <= scr -> argp (ar_sptop ar) FF sp v p n -> 0 < n <= 8 ->
  6905856 <= p /\ p + n <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= p \/ p + n <= 2147446784) /\ (p + n <= v \/ v + 24 <= p)
  /\ (sp <= p \/ p + n <= ahl_ceil ar)
  /\ (forall q m, In (q, m) LB -> p + n <= q \/ q + m <= p)
  /\ (forall i sp' scr', 0 <= i < n -> sp' <= sp -> aclient L ar LB FF sp' scr' (p + i)).
Proof.
  intros HH ASTK SC0 (PL & PV) Hn. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL, FSIMG.
  assert (FS0 : 0x696000 <= ar_fs ar) by (destruct FSAPP as (FA0 & _ & _); destruct FSIMG as [FI|FI]; lia).
  destruct PL as [(f & Hf & X1 & X2)|(X1 & X2)].
  - pose proof (WF f Hf) as (F1 & F2 & _ & F4 & _). unfold FS_BYTES in F1, F2.
    assert (HB : 0 < ff_bytes (ff_class f) <= 2048).
    { destruct F4 as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E;
        [change (ff_bytes 0) with 64 | change (ff_bytes 1) with 128 | change (ff_bytes 2) with 256 | change (ff_bytes 3) with 512 | change (ff_bytes 4) with 1024 | change (ff_bytes 5) with 2048]; lia. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact PV|]. split; [right; lia|].
    split. { intros q m Hin. destruct (WB (q, m) Hin) as (_ & _ & _ & _ & _ & QF & _). cbn [fst snd] in QF.
             destruct (QF f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y]; lia. }
    intros i sp' scr' Hi Hs. unfold aclient, aclient_g. right; right; right; left. exists f. split; [exact Hf| lia].
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [exact PV|]. split; [left; lia|].
    split. { intros q m Hin. destruct (WB (q, m) Hin) as ((_ & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q4. lia. }
    intros i sp' scr' Hi Hs. apply L5SAR.stack_client; lia.
Qed.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ann_agree (M M' : word -> option byte) b u c : (forall j, 0 <= j < (c + 7) / 8 -> M' (Z_to_bv 64 (S b + j)) = M (Z_to_bv 64 (S b + j))) ->
  0 <= u -> u <= c -> HAJ.ann_shadow M b u c -> HAJ.ann_shadow M' b u c.
Proof.
  intros AG U0 U1 (Z0 & P1 & P). split; [|split].
  - intros j Hj. unfold byte_at. rewrite AG; [apply Z0; exact Hj|]. Lia.lia.
  - intros Hu. unfold byte_at. rewrite AG; [apply P1; exact Hu|]. Lia.lia.
  - intros j Hj. unfold byte_at. rewrite AG; [apply P; exact Hj| Lia.lia].
Qed.
(* [comment removed for export] *)
Lemma sh_apart b c x : b mod 8 = 0 -> c mod 8 = 0 -> 0 < c -> 0 <= b -> 0 <= x -> (x < b \/ b + c <= x) -> ~ in_shadow_of b c (S x).
Proof. unfold in_shadow_of, S, SB. intros. Lia.lia. Qed.
(* [comment removed for export] *)
Lemma sh_in b c j : b mod 8 = 0 -> c mod 8 = 0 -> 0 <= b -> 0 <= j < c / 8 -> in_shadow_of b c (S b + j).
Proof. unfold in_shadow_of, S, SB. intros. Lia.lia. Qed.
Lemma sh_idx b d : b mod 8 = 0 -> d mod 8 = 0 -> (b + d) / 8 + 2147450880 = S b + d / 8.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma in_shadow_range b c a : 0 <= b -> b + c <= 2 ^ 47 -> in_shadow_of b c a -> 2147450880 <= a < 2147450880 + 2 ^ 44.
Proof. unfold in_shadow_of, S, SB. intros. Lia.lia. Qed.
(* [comment removed for export] *)
Lemma frame_sh_client FF o n x LBz spz scz : PMSPA.aobjA FF o n -> o <= x < o + n -> aclient L ar LBz FF spz scz (S x).
Proof.
  intros (f & Hf & X1 & X2) Hx. unfold aclient, aclient_g. right; right; right; right; right; left. exists f. split; [exact Hf|].
  unfold in_shadow_of, S, SB. Lia.lia.
Qed.
Lemma stack_sh_client FF x LBz spz scz : ahl_ceil ar <= x < 2 ^ 47 -> aclient L ar LBz FF spz scz (S x).
Proof. intros Hx. unfold aclient, aclient_g. right; right; right; right; left. unfold in_shadow_of, S, SB. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma arg_client LB FF LK cr Aw M V sp scr v p n : ri_inv HI LB FF LK cr Aw M V -> L5CA.astk ar M sp scr -> 0 <= scr -> argp (ar_sptop ar) FF sp v p n -> 0 < n ->
  forall LBz spz scz, aclient L ar LBz FF spz scz (S p).
Proof.
  intros HH ASTK SC0 [[AO|[X1 X2]] _] Hn LBz spz scz.
  - apply (frame_sh_client FF p n p); [exact AO|]. destruct AO as (f & _ & Y1 & Y2). pose proof (proj1 ASTK) as _. Lia.lia.
  - pose proof ASTK as (A16 & SLO & SHI & SPT & _). apply stack_sh_client. Lia.lia.
Qed.
Lemma arg_vis LB FF LK cr Aw M model sp scr v p n : ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.astk ar M sp scr -> 0 <= scr -> argp (ar_sptop ar) FF sp v p n -> 0 < n ->
  L5A.avis (ahid Aw model) p n /\ L5A.avis (ahid Aw model) (S p) 1.
Proof.
  intros HH ASTK SC0 [PL _] Hn. pose proof ASTK as (A16 & SLO & SHI & SPT & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct PL as [AO|[X1 X2]].
  - destruct AO as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (F1 & F2 & _).
    split; [apply VFS; Lia.lia|]. apply VFSSH. intros i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r.
    unfold in_shadow_of, S, SB. unfold FS_BYTES in *. clear - F1 F2 Y1 Y2 Hn.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
  - split; [apply VIS; Lia.lia|]. apply VSTSH. intros i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r.
    unfold in_shadow_of, S, SB. clear - X1 X2 SLO SHI SPT Hn SC0. Lia.lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma own_facts b c LBX FF LK cr Aw M V : ri_inv HI ((b, c) :: LBX) FF LK cr Aw M V ->
  (forall q m, In (q, m) LBX -> b + c <= q \/ q + m <= b) /\ (forall f, In f (FF ++ LK) -> b + c <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= b).
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB (b, c) ltac:(left; reflexivity)) as (_ & _ & _ & _ & BA & FA & _). cbn [fst snd lb_remove] in BA, FA. rewrite Z.eqb_refl in BA.
  split; [intros q m Hin; destruct (BA (q, m) Hin) as [X|X]; cbn [fst snd] in X; lia| exact FA].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma own_notclient b c LBX FF LK cr Aw M V : ri_inv HI ((b, c) :: LBX) FF LK cr Aw M V ->
  forall a spz scz, aclient L ar LBX FF spz scz a -> ~ (b <= a < b + c).
Proof.
  intros HH a spz scz Hc Ha. pose proof (own_facts b c LBX FF LK cr Aw M V HH) as (BA & FA).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  destruct (WB (b, c) ltac:(left; reflexivity)) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in *.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X. destruct (BA q m Hin); lia.
  - lia.
  - rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Hc. lia.
  - destruct Hc as (f & Hf & X & _). destruct (FA f ltac:(apply in_or_app; left; exact Hf)); lia.
  - unfold in_shadow_of, S, SB in Hc. lia.
  - destruct Hc as (f & Hf & X). unfold in_shadow_of, S, SB in X. destruct (WF f Hf) as (F1 & F2 & _).
    unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, F1, F2. lia.
  - destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X. unfold in_shadow_of, S, SB in X.
    destruct (proj1 (WB (q, m) ltac:(right; exact Hin))) as (Y0 & _ & _ & _ & _ & Y5). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5. lia.
Qed.
Lemma own_sh_notclient b c LBX FF LK cr Aw M V : ri_inv HI ((b, c) :: LBX) FF LK cr Aw M V -> c mod 8 = 0 ->
  forall a spz scz, aclient L ar LBX FF spz scz a -> ~ in_shadow_of b c a.
Proof.
  intros HH C8 a spz scz Hc Ha. pose proof (own_facts b c LBX FF LK cr Aw M V HH) as (BA & FA).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  destruct (WB (b, c) ltac:(left; reflexivity)) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in *.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  assert (SR : 2147450880 <= a < 2147450880 + 2 ^ 44) by (apply (in_shadow_range b c a); [lia| lia| exact Ha]).
  unfold in_shadow_of, S, SB in Ha.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X.
    destruct (proj1 (WB (q, m) ltac:(right; exact Hin))) as (Y0 & _ & _ & _ & _ & Y5). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5. clear - X Y5 SR. lia.
  - clear - Hc SR CB2. lia.
  - rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Hc. clear - Hc SR. lia.
  - destruct Hc as (f & Hf & X & _). destruct (WF f Hf) as (F1 & F2 & _). unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, F1, F2. clear - X F1 F2 FSAPP SR. lia.
  - unfold in_shadow_of, S, SB in Hc. clear - Hc Ha Q3 Q4 Q0 CB2. lia.
  - destruct Hc as (f & Hf & X). unfold in_shadow_of, S, SB in X. destruct (WF f Hf) as (F1 & F2 & F3 & F4 & _).
    destruct (FA f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y].
    + assert (E8 : ff_addr f mod 8 = 0).
      { destruct F4 as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E in F3;
          [change (ff_bytes 0) with 64 in F3 | change (ff_bytes 1) with 128 in F3 | change (ff_bytes 2) with 256 in F3 | change (ff_bytes 3) with 512 in F3 | change (ff_bytes 4) with 1024 in F3 | change (ff_bytes 5) with 2048 in F3];
          clear - F3; lia. }
      clear - X Ha Y E8 C8 Q2 Q0. lia.
    + assert (E8 : ff_bytes (ff_class f) mod 8 = 0 /\ ff_addr f mod 8 = 0).
      { destruct F4 as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E in *;
          [change (ff_bytes 0) with 64 in * | change (ff_bytes 1) with 128 in * | change (ff_bytes 2) with 256 in * | change (ff_bytes 3) with 512 in * | change (ff_bytes 4) with 1024 in * | change (ff_bytes 5) with 2048 in *];
          clear - F3; lia. }
      clear - X Ha Y E8 C8 Q2 Q0. lia.
  - destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X. unfold in_shadow_of, S, SB in X.
    destruct (proj1 (WB (q, m) ltac:(right; exact Hin))) as (Y0 & _ & Y2 & _). cbn [fst snd] in *.
    destruct (BA q m Hin) as [Z1|Z1]; clear - X Ha Z1 Y2 Q2 C8 Y0 Q0; lia.
Qed.
(* [comment removed for export] *)
Lemma own_sh_notclientU b c LBX FF LK cr Aw M V : ri_inv HI ((b, c) :: LBX) FF LK cr Aw M V ->
  forall a spz scz, aclient L ar LBX FF spz scz a -> ~ in_shadow_of b c a.
Proof.
  intros HH a spz scz Hc Ha. pose proof (own_facts b c LBX FF LK cr Aw M V HH) as (BA & FA).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  destruct (WB (b, c) ltac:(left; reflexivity)) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in *.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  assert (SR : 2147450880 <= a < 2147450880 + 2 ^ 44) by (apply (in_shadow_range b c a); [lia| lia| exact Ha]).
  unfold in_shadow_of, S, SB in Ha.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X.
    destruct (proj1 (WB (q, m) ltac:(right; exact Hin))) as (Y0 & _ & _ & _ & _ & Y5). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5. clear - X Y5 SR. lia.
  - clear - Hc SR CB2. lia.
  - rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Hc. clear - Hc SR. lia.
  - destruct Hc as (f & Hf & X & _). destruct (WF f Hf) as (F1 & F2 & _). unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, F1, F2. clear - X F1 F2 FSAPP SR. lia.
  - unfold in_shadow_of, S, SB in Hc. clear - Hc Ha Q3 Q4 Q0 CB2. lia.
  - destruct Hc as (f & Hf & X). unfold in_shadow_of, S, SB in X. destruct (WF f Hf) as (F1 & F2 & F3 & F4 & _).
    destruct (FA f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y].
    + assert (E8 : ff_addr f mod 8 = 0).
      { destruct F4 as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E in F3;
          [change (ff_bytes 0) with 64 in F3 | change (ff_bytes 1) with 128 in F3 | change (ff_bytes 2) with 256 in F3 | change (ff_bytes 3) with 512 in F3 | change (ff_bytes 4) with 1024 in F3 | change (ff_bytes 5) with 2048 in F3];
          clear - F3; lia. }
      clear - X Ha Y E8 Q2 Q0. lia.
    + assert (E8 : ff_bytes (ff_class f) mod 8 = 0 /\ ff_addr f mod 8 = 0).
      { destruct F4 as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E in *;
          [change (ff_bytes 0) with 64 in * | change (ff_bytes 1) with 128 in * | change (ff_bytes 2) with 256 in * | change (ff_bytes 3) with 512 in * | change (ff_bytes 4) with 1024 in * | change (ff_bytes 5) with 2048 in *];
          clear - F3; lia. }
      clear - X Ha Y E8 Q2 Q0. lia.
  - destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X. unfold in_shadow_of, S, SB in X.
    destruct (proj1 (WB (q, m) ltac:(right; exact Hin))) as (Y0 & _ & Y2 & _). cbn [fst snd] in *.
    destruct (BA q m Hin) as [Z1|Z1]; clear - X Ha Z1 Y2 Q2 Y0 Q0; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma arg_fresh_apart (M : word -> option byte) FF LK sp scr v p n B m : L5CA.astk ar M sp scr -> 0 <= scr -> argp (ar_sptop ar) FF sp v p n ->
  (forall f, In f (FF ++ LK) -> B + m <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= B) -> B + m <= ahl_ceil ar -> 0 < n -> p + n <= B \/ B + m <= p.
Proof.
  intros ASTK SC0 [[(f & Hf & X1 & X2)|(X1 & X2)] _] FA BC Hn.
  - destruct (FA f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y]; [right; lia| left; lia].
  - pose proof ASTK as (A16 & SLO & _). right. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_shift (segs : list Segment) (M M' : word -> option byte) : forall (n : nat) a b,
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None /\ M' (Z_to_bv 64 (b + i)) = M (Z_to_bv 64 (a + i))) ->
  rdn segs M' (Z_to_bv 64 b) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  induction n as [|n IH]; intros a b HH; [reflexivity|].
  cbn [rdn]. destruct (HH 0 ltac:(lia)) as (D0 & E0). replace (a + 0) with a in D0, E0 by lia. replace (b + 0) with b in E0 by lia. rewrite E0.
  destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea; [|exfalso; apply D0; reflexivity].
  rewrite !L5C.add1_lit. rewrite (IH (a + 1) (b + 1)); [reflexivity|].
  intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. replace (b + 1 + i) with (b + (i + 1)) by lia. apply HH. lia.
Qed.
Lemma rdn_nth (segs : list Segment) (M : word -> option byte) : forall (n : nat) a bs, rdn segs M (Z_to_bv 64 a) n = Some bs ->
  forall i, (i < n)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) <> None -> M (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros a bs E i Hi D; [lia|].
  cbn [rdn] in E. destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea.
  - rewrite L5C.add1_lit in E. destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. destruct i as [|i].
    + cbn. rewrite Z.add_0_r. exact Ea.
    + cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
  - destruct i as [|i]; [rewrite Z.add_0_r in D; exfalso; apply D; exact Ea|].
    destruct (seg_rom segs (Z_to_bv 64 a)) as [y|]; [|discriminate E]. rewrite L5C.add1_lit in E.
    destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
    injection E as <-. cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
    replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
Qed.
Lemma bstate_copy (segs : list Segment) (M M' : word -> option byte) a b s :
  (forall i, 0 <= i < 40 -> M (Z_to_bv 64 (a + i)) <> None /\ M' (Z_to_bv 64 (b + i)) = M (Z_to_bv 64 (a + i))) ->
  PNM.bstate_at segs M a s -> PNM.bstate_at segs M' b s.
Proof.
  intros HH (P0 & P8 & P16 & P24 & P32). unfold PNM.bstate_at, L5.u32_at, L5.u64_at, L5.u8_at in *.
  assert (SH : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= 40 -> rdn segs M' (Z_to_bv 64 (b + d)) w = rdn segs M (Z_to_bv 64 (a + d)) w).
  { intros d w H1 H2. apply rdn_shift. intros i Hi. replace (a + d + i) with (a + (d + i)) by lia. replace (b + d + i) with (b + (d + i)) by lia. apply HH. lia. }
  split; [rewrite <- (Z.add_0_r b), SH, Z.add_0_r by (cbn; lia); exact P0|].
  split; [rewrite SH by (cbn; lia); exact P8|]. split; [rewrite SH by (cbn; lia); exact P16|]. split; [rewrite SH by (cbn; lia); exact P24|].
  rewrite SH by (cbn; lia); exact P32.
Qed.

End Kit.
End PNAEK.

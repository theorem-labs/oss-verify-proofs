(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare LibIface LibEff SymDriveX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep StrLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record tabl_img : Type := TABL_IMG {
  ti_spans   : Z;
  ti_strings : Z;
  ti_insn    : Z;
  ti_opnd    : Z;
  ti_ext     : Z;
  ti_spec    : Z;
  ti_tstr    : list (Z * Z);
  ti_tstr_dflt : Z * Z;
  ti_ro_lo   : Z;
  ti_ro_hi   : Z
}.

Definition INSN_STRIDE : Z := 60.
Definition OPND_STRIDE : Z := 52.
Definition EXT_STRIDE  : Z := 28.
Definition SPEC_STRIDE : Z := 16.

Section Checker.
Variable SEGS : list Segment.
Variable ti : tabl_img.

Definition rom_rd (a : Z) (n : nat) : option (list Z) :=
  match rdn SEGS (fun _ => None) (Z_to_bv 64 a) n with
  | Some bs => Some (map bv_unsigned bs)
  | None => None
  end.

Definition le4 (v : Z) : list Z := [v mod 256; (v / 256) mod 256; (v / 65536) mod 256; (v / 16777216) mod 256].

Definition chk_u32 (a v : Z) : bool :=
  (0 <=? v) && (v <? 2 ^ 32) &&
  match rom_rd a 4 with Some bs => TablGrammar.list_eqb bs (le4 v) | None => false end.

Definition in_win (a : Z) (n : Z) : bool := (ti_ro_lo ti <=? a) && (a + n <=? ti_ro_hi ti).

Definition align_dn8 (a : Z) : Z := a - a mod 8.
Definition align_up8 (a : Z) : Z := a + (8 - a mod 8) mod 8.
Definition chk_cstr (p n : Z) : bool :=
  (0 <=? n) && (n <=? 256) && in_win (align_dn8 p) (align_up8 (p + n + 1) - align_dn8 p) &&
  match rom_rd p (Z.to_nat (n + 1)) with
  | Some bs => forallb (fun c => negb (c =? 0)) (firstn (Z.to_nat n) bs) && (nth (Z.to_nat n) bs 1 =? 0)
  | None => false
  end &&
  match rom_rd (align_dn8 p) (Z.to_nat (align_up8 (p + n + 1) - align_dn8 p)) with Some _ => true | None => false end.

Fixpoint chk_insn (i : Z) (rows : list (Z * Z * Z * Z * Z)) : bool :=
  match rows with
  | [] => true
  | r :: rows' =>
      let a := ti_insn ti + INSN_STRIDE * i in
      in_win a INSN_STRIDE &&
      chk_u32 a (i_opcode r) && chk_u32 (a + 8) (i_first r) && chk_u32 (a + 12) (i_count r) &&
      chk_u32 (a + 16) (i_nfirst r) && chk_u32 (a + 20) (i_ncount r) &&
      (i_first r + i_count r <=? Zlen SPANS) && (0 <=? i_first r) &&
      (1 <=? i_ncount r) && chk_cstr (ti_strings ti + i_nfirst r) (i_ncount r - 1) &&
      chk_insn (i + 1) rows'
  end.

Fixpoint chk_rows3 (base stride : Z) (i : Z) (rows : list (Z * Z * Z)) : bool :=
  match rows with
  | [] => true
  | r :: rows' =>
      let a := base + stride * i in
      in_win a stride &&
      chk_u32 a (v_value r) && chk_u32 (a + 4) (v_first r) && chk_u32 (a + 8) (v_count r) &&
      (v_first r + v_count r <=? Zlen SPANS) && (0 <=? v_first r) &&
      chk_rows3 base stride (i + 1) rows'
  end.

Fixpoint chk_words (base stride : Z) (i : Z) (vs : list Z) : bool :=
  match vs with
  | [] => true
  | v :: vs' => chk_u32 (base + stride * i) v && chk_words base stride (i + 1) vs'
  end.

Definition chk_tstr : bool :=
  (Zlen (ti_tstr ti) =? 108) &&
  forallb (fun pn => chk_cstr (fst pn) (snd pn)) (ti_tstr_dflt ti :: ti_tstr ti).

Definition img_okb : bool :=
  (0x10000 <=? ti_ro_lo ti) && (ti_ro_hi ti <=? 2 ^ 40) &&
  in_win (ti_spans ti) (4 * Zlen SPANS) && (ti_spans ti mod 4 =? 0) &&
  chk_words (ti_spans ti) 4 0 SPANS &&
  chk_insn 0 INSN &&
  chk_rows3 (ti_opnd ti) OPND_STRIDE 0 OPND &&
  chk_rows3 (ti_ext ti) EXT_STRIDE 0 EXT &&
  chk_words (ti_spec ti) SPEC_STRIDE 0 SPECOPS && (0x10000 <=? ti_spec ti) && (ti_spec ti + 16 * 65 <=? 2 ^ 40) &&
  chk_tstr.
End Checker.

Lemma map_unsigned_inj : forall (a b : list byte), map bv_unsigned a = map bv_unsigned b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hx Hr. f_equal; [apply bv_eq; exact Hx | apply IH, Hr].
Qed.

Lemma le4_bytes : forall v, 0 <= v < 2 ^ 32 -> map bv_unsigned (word_to_le_bytes 4 (Z_to_bv 64 v)) = le4 v.
Proof.
  intros v Hv. unfold word_to_le_bytes, le4. rewrite Z_to_bv_unsigned, bv_wrap64_mod, (Z.mod_small v) by lia.
  cbn [Z_to_le_bytes map]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  rewrite !Z.div_div by lia. reflexivity.
Qed.

Section Sound.
Variable SEGS : list Segment.
Variable L : Layout.
Variable ti : tabl_img.
Hypothesis IMGOK : img_okb SEGS ti = true.
Hypothesis RODATA : forall a, ti_ro_lo ti <= a < ti_ro_hi ti -> ro_addr L a.

#[local] Abbreviation fld := (CRep.fld SEGS).

Lemma chk_u32_rom : forall a v, chk_u32 SEGS a v = true ->
  0 <= v < 2 ^ 32 /\ rdn SEGS (fun _ => None) (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 v)).
Proof using SEGS.
  intros a v H. unfold chk_u32 in H.
  apply andb_prop in H as [H Hr]. apply andb_prop in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. split; [lia|].
  unfold rom_rd in Hr. destruct (rdn SEGS (fun _ => None) (Z_to_bv 64 a) 4) as [bs|] eqn:E; [|discriminate].
  apply list_eqb_eq in Hr. f_equal. apply map_unsigned_inj. rewrite Hr. symmetry. apply le4_bytes. lia.
Qed.

Lemma rdn_clear : forall M a n,
  (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn SEGS M (Z_to_bv 64 a) n = rdn SEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof using SEGS. intros M a n Hn H0 H1. apply rdn_untouched; [lia|lia|exact Hn]. Qed.

Lemma ro_clear_win : forall M a n, ro_clear L M -> ti_ro_lo ti <= a -> a + n <= ti_ro_hi ti ->
  0x10000 <= ti_ro_lo ti -> ti_ro_hi ti <= 2 ^ 40 ->
  forall i, a <= i < a + n -> M (Z_to_bv 64 i) = None.
Proof using L ti RODATA.
  intros M a n HR Hlo Hhi W0 W1 i Hi. apply (ro_clear_at L M i HR); [lia|]. apply RODATA. lia.
Qed.

Local Ltac win_tac :=
  match goal with |- _ => idtac end.

Lemma fld_of_chk : forall M a v, ro_clear L M ->
  0x10000 <= ti_ro_lo ti -> ti_ro_hi ti <= 2 ^ 40 ->
  ti_ro_lo ti <= a -> a + 4 <= ti_ro_hi ti ->
  chk_u32 SEGS a v = true -> fld M a 4 v /\ 0 <= v < 2 ^ 32.
Proof using SEGS L ti RODATA.
  intros M a v HR W0 W1 Hlo Hhi Hc. destruct (chk_u32_rom _ _ Hc) as [Hv Hrd].
  split; [|exact Hv]. unfold CRep.fld. rewrite rdn_clear; [exact Hrd| |lia|cbn; lia].
  intros i Hi. eapply ro_clear_win; eauto; cbn in Hi; lia.
Qed.

Record img_facts : Prop := IMG_FACTS {
  if_w0 : 0x10000 <= ti_ro_lo ti;
  if_w1 : ti_ro_hi ti <= 2 ^ 40;
  if_spans_win : ti_ro_lo ti <= ti_spans ti /\ ti_spans ti + 4 * Zlen SPANS <= ti_ro_hi ti;
  if_spans_al : ti_spans ti mod 4 = 0;
  if_spans : chk_words SEGS (ti_spans ti) 4 0 SPANS = true;
  if_insn : chk_insn SEGS ti 0 INSN = true;
  if_opnd : chk_rows3 SEGS ti (ti_opnd ti) OPND_STRIDE 0 OPND = true;
  if_ext : chk_rows3 SEGS ti (ti_ext ti) EXT_STRIDE 0 EXT = true;
  if_spec : chk_words SEGS (ti_spec ti) SPEC_STRIDE 0 SPECOPS = true;
  if_spec_lo : 0x10000 <= ti_spec ti;
  if_spec_hi : ti_spec ti + 16 * 65 <= 2 ^ 40;
  if_tstr : chk_tstr SEGS ti = true
}.

Lemma img_facts_of : img_facts.
Proof using SEGS ti IMGOK.
  pose proof IMGOK as H. unfold img_okb in H.
  apply andb_prop in H as [H C11]. apply andb_prop in H as [H C10]. apply andb_prop in H as [H C9].
  apply andb_prop in H as [H C8]. apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6].
  apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3].
  apply andb_prop in H as [H C2]. apply andb_prop in H as [C0 C1].
  unfold in_win in C2. apply andb_prop in C2 as [C2a C2b].
  apply Z.leb_le in C0. apply Z.leb_le in C1. apply Z.leb_le in C2a. apply Z.leb_le in C2b.
  apply Z.eqb_eq in C3. apply Z.leb_le in C9. apply Z.leb_le in C10.
  constructor; try assumption. lia.
Qed.

Lemma chk_words_nth : forall base stride i vs, chk_words SEGS base stride i vs = true ->
  forall j v, nth_error vs j = Some v -> chk_u32 SEGS (base + stride * (i + Z.of_nat j)) v = true.
Proof using SEGS.
  intros base stride i vs. revert i. induction vs as [|x vs IH]; intros i H j v Hj.
  - destruct j; discriminate.
  - cbn [chk_words] in H. apply andb_prop in H as [H1 H2]. destruct j as [|j].
    + cbn in Hj. injection Hj as <-. rewrite Nat2Z.inj_0, Z.add_0_r. exact H1.
    + cbn in Hj. specialize (IH (i + 1) H2 j v Hj). rewrite Nat2Z.inj_succ.
      replace (i + Z.succ (Z.of_nat j)) with (i + 1 + Z.of_nat j) by lia. exact IH.
Qed.

Lemma Znth_nth_error : forall (l : list Z) i, 0 <= i < Zlen l -> nth_error l (Z.to_nat i) = Some (Znth i l).
Proof using.
  intros l i Hi. unfold Znth, Zlen in *. apply nth_error_nth'. lia.
Qed.

Lemma spans_fld : img_facts -> forall M i, ro_clear L M -> 0 <= i < Zlen SPANS ->
  fld M (ti_spans ti + 4 * i) 4 (Znth i SPANS) /\ 0 <= Znth i SPANS < 2 ^ 32.
Proof using SEGS L ti RODATA.
  intros F M i HR Hi.
  pose proof (chk_words_nth _ _ _ _ (if_spans F) (Z.to_nat i) (Znth i SPANS) (Znth_nth_error _ _ Hi)) as C.
  rewrite Z2Nat.id in C by lia. rewrite Z.add_0_l in C.
  pose proof (if_spans_win F) as W. unfold Zlen in W, Hi.
  apply fld_of_chk; [exact HR | apply (if_w0 F) | apply (if_w1 F) | lia | lia | exact C].
Qed.

Lemma ro_span_of : img_facts -> forall f c, 0 <= f -> 0 <= c -> f + c <= Zlen SPANS ->
  ro_span SEGS L (ti_spans ti + 4 * f) (span f c) /\ (ti_spans ti + 4 * f) mod 4 = 0 /\ Zlen (span f c) = c.
Proof using SEGS L ti RODATA.
  intros F f c Hf Hc Hfc.
  assert (HL : Zlen (span f c) = c).
  { unfold Zlen, span, zsub in *. rewrite length_firstn, length_skipn. lia. }
  pose proof (if_spans_win F) as W. pose proof (if_w0 F) as W0. pose proof (if_w1 F) as W1.
  split; [|split; [|exact HL]].
  2:{ pose proof (if_spans_al F) as AL. apply Z.mod_divide in AL; [|lia]. apply Z.mod_divide; [lia|].
      destruct AL as [q Hq]. exists (q + f). lia. }
  unfold ro_span. rewrite HL. split; [lia|]. split; [lia|].
  intros M HR i Hi.
  assert (Hnth : Znth i (span f c) = Znth (f + i) SPANS).
  { unfold span, zsub, Znth. rewrite nth_firstn.
    destruct (Z.to_nat i <? Z.to_nat c)%nat eqn:En; [|apply Nat.ltb_ge in En; lia].
    rewrite nth_skipn. f_equal. lia. }
  rewrite Hnth. replace (ti_spans ti + 4 * f + 4 * i) with (ti_spans ti + 4 * (f + i)) by lia.
  destruct (spans_fld F M (f + i) HR ltac:(unfold Zlen in *; lia)) as [A B]. split; [exact B | exact A].
Qed.

Lemma rom_rd_bytes : forall M a n zs, ro_clear L M -> 0x10000 <= ti_ro_lo ti -> ti_ro_hi ti <= 2 ^ 40 ->
  ti_ro_lo ti <= a -> a + Z.of_nat n <= ti_ro_hi ti ->
  rom_rd SEGS a n = Some zs ->
  exists bs, rdn SEGS M (Z_to_bv 64 a) n = Some bs /\ map bv_unsigned bs = zs.
Proof using SEGS L ti RODATA.
  intros M a n zs HR W0 W1 Hlo Hhi H. unfold rom_rd in H.
  destruct (rdn SEGS (fun _ => None) (Z_to_bv 64 a) n) as [bs|] eqn:E; [|discriminate]. injection H as <-.
  exists bs. split; [|reflexivity]. rewrite rdn_clear; [exact E| |lia|lia].
  intros i Hi. eapply ro_clear_win; eauto; lia.
Qed.

Lemma byte_w1 : forall b : byte, word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b] /\ 0 <= bv_unsigned b < 256.
Proof using.
  intros b. pose proof (bv_unsigned_in_range _ b) as X. unfold bv_modulus in X. cbn in X.
  split; [|lia]. rewrite w1_bytes_small by lia. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.pow Z.of_N Pos.pow]. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma rdn_byte_fld : forall M a n bs j, rdn SEGS M (Z_to_bv 64 a) n = Some bs -> (j < n)%nat -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  fld M (a + Z.of_nat j) 1 (bv_unsigned (nth j bs (Z_to_bv 8 0))) /\ 0 <= bv_unsigned (nth j bs (Z_to_bv 8 0)) < 256.
Proof using SEGS.
  intros M a n bs j H Hj H0 H1. unfold CRep.fld.
  pose proof (rdn_nth SEGS M n (Z_to_bv 64 a) bs j H Hj) as R.
  replace (Z_to_bv 64 a + nat_to_word j)%bv with (Z_to_bv 64 (a + Z.of_nat j)) in R.
  2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
      rewrite <- Zplus_mod. reflexivity. }
  destruct (byte_w1 (nth j bs (Z_to_bv 8 0))) as [E B]. rewrite R, E. split; [reflexivity | exact B].
Qed.

Lemma rdn_length : forall M (a : word) n bs, rdn SEGS M a n = Some bs -> length bs = n.
Proof using SEGS.
  intros M a n. revert a. induction n as [|n IH]; intros a bs H; cbn [rdn] in H.
  - injection H as <-. reflexivity.
  - destruct (match M a with Some b => Some b | None => seg_rom SEGS a end); [|discriminate].
    destruct (rdn SEGS M (a + 1)%bv n) eqn:E; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH, E.
Qed.

Lemma ro_cstr_of_chk : forall p n, 0x10000 <= ti_ro_lo ti -> ti_ro_hi ti <= 2 ^ 40 ->
  chk_cstr SEGS ti p n = true -> ro_cstr SEGS L p n /\ n <= 256.
Proof using SEGS L ti RODATA.
  intros p n W0 W1 H. unfold chk_cstr in H.
  apply andb_prop in H as [H Hslack]. apply andb_prop in H as [H Hstr]. apply andb_prop in H as [H Hwin].
  apply andb_prop in H as [Hn0 Hn1]. apply Z.leb_le in Hn0. apply Z.leb_le in Hn1.
  unfold in_win in Hwin. apply andb_prop in Hwin as [Hw0 Hw1]. apply Z.leb_le in Hw0. apply Z.leb_le in Hw1.
  assert (Hdn : align_dn8 p <= p /\ p - 8 < align_dn8 p) by (unfold align_dn8; pose proof (Z.mod_pos_bound p 8); lia).
  assert (Hup : p + n + 1 <= align_up8 (p + n + 1) /\ align_up8 (p + n + 1) < p + n + 1 + 8).
  { unfold align_up8. pose proof (Z.mod_pos_bound (p + n + 1) 8). pose proof (Z.mod_pos_bound (8 - (p + n + 1) mod 8) 8). lia. }
  split; [|exact Hn1].
  unfold ro_cstr. split; [lia|]. split; [lia|]. split; [lia|].
  intros M HR.
  destruct (rom_rd SEGS p (Z.to_nat (n + 1))) as [zs|] eqn:E; [|discriminate].
  apply andb_prop in Hstr as [Hnz Hz]. rewrite forallb_forall in Hnz. apply Z.eqb_eq in Hz.
  destruct (rom_rd_bytes M p (Z.to_nat (n + 1)) zs HR W0 W1 ltac:(lia) ltac:(lia) E) as (bs & Hbs & Hmap).
  pose proof (rdn_length _ _ _ _ Hbs) as Hlen.
  assert (Hlenz : length zs = Z.to_nat (n + 1)) by (rewrite <- Hmap, length_map; exact Hlen).
  assert (BY : forall j, (j < Z.to_nat (n + 1))%nat -> fld M (p + Z.of_nat j) 1 (nth j zs 1) /\ 0 <= nth j zs 1 < 256).
  { intros j Hj. destruct (rdn_byte_fld M p _ bs j Hbs Hj ltac:(lia) ltac:(lia)) as [Fj Rj].
    assert (Hnth : nth j zs 1 = bv_unsigned (nth j bs (Z_to_bv 8 0))).
    { rewrite <- Hmap. erewrite nth_indep by (rewrite length_map; lia). apply map_nth. }
    rewrite Hnth. split; [exact Fj| exact Rj]. }
  split; [|split].
  - intros i Hi. destruct (BY (Z.to_nat i) ltac:(lia)) as [Fi Ri]. rewrite Z2Nat.id in Fi by lia.
    exists (nth (Z.to_nat i) zs 1). split; [|exact Fi].
    enough (nth (Z.to_nat i) zs 1 <> 0) by lia.
    specialize (Hnz (nth (Z.to_nat i) zs 1)).
    assert (HIn : In (nth (Z.to_nat i) zs 1) (firstn (Z.to_nat n) zs)).
    { replace (nth (Z.to_nat i) zs 1) with (nth (Z.to_nat i) (firstn (Z.to_nat n) zs) 1).
      - apply nth_In. rewrite length_firstn. lia.
      - rewrite nth_firstn. destruct (Z.to_nat i <? Z.to_nat n)%nat eqn:En; [reflexivity|apply Nat.ltb_ge in En; lia]. }
    specialize (Hnz HIn). intros C. rewrite C in Hnz. discriminate.
  - destruct (BY (Z.to_nat n) ltac:(lia)) as [Fn _]. rewrite Z2Nat.id in Fn by lia. rewrite Hz in Fn. exact Fn.
  - intros a Ha. change (p - p mod 8) with (align_dn8 p) in Ha.
    change (p + n + 1 + (8 - (p + n + 1) mod 8) mod 8) with (align_up8 (p + n + 1)) in Ha.
    destruct (rom_rd SEGS (align_dn8 p) (Z.to_nat (align_up8 (p + n + 1) - align_dn8 p))) as [zs2|] eqn:E2; [|discriminate].
    destruct (rom_rd_bytes M (align_dn8 p) (Z.to_nat (align_up8 (p + n + 1) - align_dn8 p)) zs2 HR W0 W1 ltac:(lia) ltac:(lia) E2) as (bs2 & Hbs2 & Hmap2).
    assert (Q1 : (Z.to_nat (a - align_dn8 p) < Z.to_nat (align_up8 (p + n + 1) - align_dn8 p))%nat). { lia. }
    destruct (rdn_byte_fld M (align_dn8 p) (Z.to_nat (align_up8 (p + n + 1) - align_dn8 p)) bs2 (Z.to_nat (a - align_dn8 p)) Hbs2 Q1 ltac:(lia) ltac:(lia)) as [Fa Ra].
    rewrite Z2Nat.id in Fa by lia. replace (align_dn8 p + (a - align_dn8 p)) with a in Fa by lia.
    eexists. split; [exact Ra | exact Fa].
Qed.

Lemma chk_insn_nth : forall i0 rows, chk_insn SEGS ti i0 rows = true ->
  forall j r, nth_error rows j = Some r ->
  let a := ti_insn ti + INSN_STRIDE * (i0 + Z.of_nat j) in
  in_win ti a INSN_STRIDE = true /\
  chk_u32 SEGS a (i_opcode r) = true /\ chk_u32 SEGS (a + 8) (i_first r) = true /\ chk_u32 SEGS (a + 12) (i_count r) = true /\
  chk_u32 SEGS (a + 16) (i_nfirst r) = true /\ chk_u32 SEGS (a + 20) (i_ncount r) = true /\
  0 <= i_first r /\ i_first r + i_count r <= Zlen SPANS /\ 1 <= i_ncount r /\
  chk_cstr SEGS ti (ti_strings ti + i_nfirst r) (i_ncount r - 1) = true.
Proof using SEGS ti.
  intros i0 rows. revert i0. induction rows as [|x rows IH]; intros i0 H j r Hj.
  - destruct j; discriminate.
  - cbn [chk_insn] in H.
    apply andb_prop in H as [H Hrest]. apply andb_prop in H as [H C9]. apply andb_prop in H as [H C8].
    apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5].
    apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [H C2].
    apply andb_prop in H as [C0 C1].
    destruct j as [|j].
    + cbn in Hj. injection Hj as <-. cbn [Z.of_nat]. rewrite Z.add_0_r.
      apply Z.leb_le in C6. apply Z.leb_le in C7. apply Z.leb_le in C8.
      repeat split; try assumption.
    + cbn in Hj. specialize (IH (i0 + 1) Hrest j r Hj). rewrite Nat2Z.inj_succ.
      replace (i0 + Z.succ (Z.of_nat j)) with (i0 + 1 + Z.of_nat j) by lia. exact IH.
Qed.

Lemma chk_rows3_nth : forall base stride i0 rows, chk_rows3 SEGS ti base stride i0 rows = true ->
  forall j r, nth_error rows j = Some r ->
  let a := base + stride * (i0 + Z.of_nat j) in
  in_win ti a stride = true /\
  chk_u32 SEGS a (v_value r) = true /\ chk_u32 SEGS (a + 4) (v_first r) = true /\ chk_u32 SEGS (a + 8) (v_count r) = true /\
  0 <= v_first r /\ v_first r + v_count r <= Zlen SPANS.
Proof using SEGS ti.
  intros base stride i0 rows. revert i0. induction rows as [|x rows IH]; intros i0 H j r Hj.
  - destruct j; discriminate.
  - cbn [chk_rows3] in H.
    apply andb_prop in H as [H Hrest]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4].
    apply andb_prop in H as [H C3]. apply andb_prop in H as [H C2]. apply andb_prop in H as [C0 C1].
    destruct j as [|j].
    + cbn in Hj. injection Hj as <-. cbn [Z.of_nat]. rewrite Z.add_0_r.
      apply Z.leb_le in C4. apply Z.leb_le in C5. repeat split; try assumption.
    + cbn in Hj. specialize (IH (i0 + 1) Hrest j r Hj). rewrite Nat2Z.inj_succ.
      replace (i0 + Z.succ (Z.of_nat j)) with (i0 + 1 + Z.of_nat j) by lia. exact IH.
Qed.

Definition idesc (d op : Z) : Prop := exists i r, find_insn op = Some (i, r) /\ d = ti_insn ti + INSN_STRIDE * i.
Definition odesc (d t v : Z) : Prop := exists i r, find_opnd t v = Some (i, r) /\ d = ti_opnd ti + OPND_STRIDE * i.
Definition edesc (d e v : Z) : Prop := exists i r, find_ext e v = Some (i, r) /\ d = ti_ext ti + EXT_STRIDE * i.

Lemma in_win_bounds : forall a n, in_win ti a n = true -> ti_ro_lo ti <= a /\ a + n <= ti_ro_hi ti.
Proof using ti. intros a n H. unfold in_win in H. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia. Qed.

Lemma idesc_facts : img_facts -> forall d op, idesc d op ->
  exists r, find_insn op = Some ((d - ti_insn ti) / INSN_STRIDE, r) /\ i_opcode r = op /\ tg_op op = Some (i_span r) /\
  0x10000 <= d /\ d + INSN_STRIDE <= 2 ^ 40 /\
  (forall M, ro_clear L M ->
     fld M d 4 op /\ fld M (d + 8) 4 (i_first r) /\ fld M (d + 12) 4 (i_count r) /\
     fld M (d + 16) 4 (i_nfirst r) /\ fld M (d + 20) 4 (i_ncount r)) /\
  0 <= i_first r /\ 0 <= i_count r /\ i_first r + i_count r <= Zlen SPANS /\ 1 <= i_ncount r /\
  0 <= i_nfirst r < 2 ^ 32 /\ i_ncount r < 2 ^ 32 /\
  ro_span SEGS L (ti_spans ti + 4 * i_first r) (i_span r) /\ (ti_spans ti + 4 * i_first r) mod 4 = 0 /\ Zlen (i_span r) = i_count r /\
  ro_cstr SEGS L (ti_strings ti + i_nfirst r) (i_ncount r - 1) /\ i_ncount r - 1 <= 256.
Proof using SEGS L ti RODATA.
  intros F d op (i & r & Hf & Hd).
  pose proof Hf as Hf0. unfold find_insn in Hf. destruct (find_ix_some _ _ _ _ _ Hf) as (Hin & Hp & Hi0 & Hnth).
  apply Z.eqb_eq in Hp. rewrite Z.sub_0_r in Hnth.
  pose proof (chk_insn_nth 0 INSN (if_insn F) (Z.to_nat i) r Hnth) as C. cbn beta iota zeta in C.
  rewrite Z2Nat.id in C by lia. rewrite Z.add_0_l in C. rewrite <- Hd in C.
  destruct C as (Cw & C0 & C8 & C12 & C16 & C20 & Cf & Cfc & Cnc & Cstr).
  destruct (in_win_bounds _ _ Cw) as [Wlo Whi]. pose proof (if_w0 F) as W0. pose proof (if_w1 F) as W1.
  destruct (chk_u32_rom _ _ C12) as [Rc _]. destruct (chk_u32_rom _ _ C16) as [Rnf _]. destruct (chk_u32_rom _ _ C20) as [Rnc _].
  exists r. split.
  { rewrite Hd. replace (ti_insn ti + INSN_STRIDE * i - ti_insn ti) with (i * INSN_STRIDE) by lia.
    unfold INSN_STRIDE. rewrite Z.div_mul by lia. exact Hf0. }
  split; [exact Hp|]. split; [unfold tg_op; rewrite Hf0; reflexivity|].
  split; [lia|]. split; [unfold INSN_STRIDE in *; lia|].
  split.
  { intros M HR. unfold INSN_STRIDE in *.
    assert (Wd: d + 4 <= ti_ro_hi ti) by lia.
    destruct (fld_of_chk M d (i_opcode r) HR W0 W1 Wlo Wd C0) as [F0 _].
    assert (W8: ti_ro_lo ti <= d + 8) by lia. assert (W8': d + 8 + 4 <= ti_ro_hi ti) by lia.
    destruct (fld_of_chk M _ _ HR W0 W1 W8 W8' C8) as [F8 _].
    assert (W12: ti_ro_lo ti <= d + 12) by lia. assert (W12': d + 12 + 4 <= ti_ro_hi ti) by lia.
    destruct (fld_of_chk M _ _ HR W0 W1 W12 W12' C12) as [F12 _].
    assert (W16: ti_ro_lo ti <= d + 16) by lia. assert (W16': d + 16 + 4 <= ti_ro_hi ti) by lia.
    destruct (fld_of_chk M _ _ HR W0 W1 W16 W16' C16) as [F16 _].
    assert (W20: ti_ro_lo ti <= d + 20) by lia. assert (W20': d + 20 + 4 <= ti_ro_hi ti) by lia.
    destruct (fld_of_chk M _ _ HR W0 W1 W20 W20' C20) as [F20 _].
    rewrite Hp in F0. repeat split; assumption. }
  destruct (ro_span_of F (i_first r) (i_count r) Cf ltac:(lia) Cfc) as (SP & AL & LEN).
  destruct (ro_cstr_of_chk _ _ W0 W1 Cstr) as [CS CN].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact SP|]. split; [exact AL|]. split; [exact LEN|]. split; [exact CS| exact CN].
Qed.

Lemma byvalue_facts : forall K T base stride t v i r d (CHK : chk_rows3 SEGS ti base stride 0 T = true),
  img_facts -> 12 <= stride ->
  find_byvalue K T t v = Some (i, r) -> d = base + stride * i ->
  v_value r = v /\ 0x10000 <= d /\ d + stride <= 2 ^ 40 /\ 0 <= i /\
  (forall M, ro_clear L M -> fld M d 4 v /\ fld M (d + 4) 4 (v_first r) /\ fld M (d + 8) 4 (v_count r)) /\
  0 <= v < 2 ^ 32 /\ 0 <= v_first r /\ 0 <= v_count r /\ v_first r + v_count r <= Zlen SPANS /\
  ro_span SEGS L (ti_spans ti + 4 * v_first r) (v_span r) /\ (ti_spans ti + 4 * v_first r) mod 4 = 0 /\ Zlen (v_span r) = v_count r.
Proof using SEGS L ti RODATA.
  intros K T base stride t v i r d CHK F Hs Hf Hd.
  destruct (find_byvalue_row _ _ _ _ _ _ Hf) as (Hin & Hv & Hrng & Hnth).
  pose proof (chk_rows3_nth base stride 0 T CHK (Z.to_nat i) r Hnth) as C. cbn beta iota zeta in C.
  rewrite Z2Nat.id in C by lia. rewrite Z.add_0_l in C. rewrite <- Hd in C.
  destruct C as (Cw & C0 & C4 & C8 & Cf & Cfc).
  destruct (in_win_bounds _ _ Cw) as [Wlo Whi]. pose proof (if_w0 F) as W0. pose proof (if_w1 F) as W1.
  destruct (chk_u32_rom _ _ C0) as [Rv _]. destruct (chk_u32_rom _ _ C8) as [Rc _].
  split; [exact Hv|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros M HR.
    assert (Wd: d + 4 <= ti_ro_hi ti) by lia.
    destruct (fld_of_chk M d (v_value r) HR W0 W1 Wlo Wd C0) as [F0 _].
    assert (W4: ti_ro_lo ti <= d + 4) by lia. assert (W4': d + 4 + 4 <= ti_ro_hi ti) by lia.
    destruct (fld_of_chk M _ _ HR W0 W1 W4 W4' C4) as [F4 _].
    assert (W8: ti_ro_lo ti <= d + 8) by lia. assert (W8': d + 8 + 4 <= ti_ro_hi ti) by lia.
    destruct (fld_of_chk M _ _ HR W0 W1 W8 W8' C8) as [F8 _].
    rewrite Hv in F0. repeat split; assumption. }
  destruct (ro_span_of F (v_first r) (v_count r) Cf ltac:(lia) Cfc) as (SP & AL & LEN).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact SP|]. split; [exact AL| exact LEN].
Qed.

Lemma odesc_facts : img_facts -> forall d t v, odesc d t v ->
  exists r, find_opnd t v = Some ((d - ti_opnd ti) / OPND_STRIDE, r) /\ tg_operand t v = Some (v_span r) /\
  v_value r = v /\ 0x10000 <= d /\ d + OPND_STRIDE <= 2 ^ 40 /\
  (forall M, ro_clear L M -> fld M d 4 v /\ fld M (d + 4) 4 (v_first r) /\ fld M (d + 8) 4 (v_count r)) /\
  0 <= v < 2 ^ 32 /\ 0 <= v_first r /\ 0 <= v_count r /\ v_first r + v_count r <= Zlen SPANS /\
  ro_span SEGS L (ti_spans ti + 4 * v_first r) (v_span r) /\ (ti_spans ti + 4 * v_first r) mod 4 = 0 /\ Zlen (v_span r) = v_count r.
Proof using SEGS L ti RODATA.
  intros F d t v (i & r & Hf & Hd). exists r.
  destruct (byvalue_facts OPND_KIND OPND (ti_opnd ti) OPND_STRIDE t v i r d (if_opnd F) F ltac:(unfold OPND_STRIDE; lia) Hf Hd)
    as (A1 & A2 & A3 & A4 & A5).
  split.
  { rewrite Hd. replace (ti_opnd ti + OPND_STRIDE * i - ti_opnd ti) with (i * OPND_STRIDE) by lia.
    unfold OPND_STRIDE. rewrite Z.div_mul by lia. exact Hf. }
  split; [unfold tg_operand, find_opnd in *; rewrite Hf; reflexivity|].
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. exact A5.
Qed.

Lemma edesc_facts : img_facts -> forall d e v, edesc d e v ->
  exists r, find_ext e v = Some ((d - ti_ext ti) / EXT_STRIDE, r) /\ tg_ext e v = Some (v_span r) /\
  v_value r = v /\ 0x10000 <= d /\ d + EXT_STRIDE <= 2 ^ 40 /\
  (forall M, ro_clear L M -> fld M d 4 v /\ fld M (d + 4) 4 (v_first r) /\ fld M (d + 8) 4 (v_count r)) /\
  0 <= v < 2 ^ 32 /\ 0 <= v_first r /\ 0 <= v_count r /\ v_first r + v_count r <= Zlen SPANS /\
  ro_span SEGS L (ti_spans ti + 4 * v_first r) (v_span r) /\ (ti_spans ti + 4 * v_first r) mod 4 = 0 /\ Zlen (v_span r) = v_count r.
Proof using SEGS L ti RODATA.
  intros F d e v (i & r & Hf & Hd). exists r.
  destruct (byvalue_facts EXT_KIND EXT (ti_ext ti) EXT_STRIDE e v i r d (if_ext F) F ltac:(unfold EXT_STRIDE; lia) Hf Hd)
    as (A1 & A2 & A3 & A4 & A5).
  split.
  { rewrite Hd. replace (ti_ext ti + EXT_STRIDE * i - ti_ext ti) with (i * EXT_STRIDE) by lia.
    unfold EXT_STRIDE. rewrite Z.div_mul by lia. exact Hf. }
  split; [unfold tg_ext, find_ext in *; rewrite Hf; reflexivity|].
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. exact A5.
Qed.

Lemma tstr_facts : img_facts ->
  Zlen (ti_tstr ti) = 108 /\
  (forall pn, In pn (ti_tstr_dflt ti :: ti_tstr ti) -> ro_cstr SEGS L (fst pn) (snd pn) /\ snd pn <= 256).
Proof using SEGS L ti RODATA.
  intros F. pose proof (if_tstr F) as H. unfold chk_tstr in H. apply andb_prop in H as [HL HA].
  apply Z.eqb_eq in HL. split; [exact HL|]. rewrite forallb_forall in HA.
  intros pn Hin. apply (ro_cstr_of_chk (fst pn) (snd pn) (if_w0 F) (if_w1 F)). apply HA, Hin.
Qed.
End Sound.

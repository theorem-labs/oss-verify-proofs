(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of check_refusal (plugin-hostd/fuzz_command, 0x87f08, 52 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (pb_wcb: entry, branch, return) and A/ACh2.v:122-290 (a program call through cl_callS and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_refusal.v, with its module paths and module names changed; 429 of its 474 lines of code are new or changed and 271 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...; unstripped twin
   80e82127e8ca...): the walk of reac_box_catalogue_by_token (catalogue.c:47-50; entry 0x8a8f4 = BASE +
   AF_reac_box_catalogue_by_token = 0x84dc0 + 0x5b34, 64 bytes, 16 instructions, a 16-byte real-stack frame, no
   side-stack frame) against reac_box_catalogue_by_token_contract (lib/B/Prog/reac_box_catalogue_by_token_c.v, the
   image-B copy of the image-A owner's FINAL 6f783602b5e3) at image B's numbers (lib/B/Prog/SegInstB.v), in
   plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of apost_base at the return, over
   `Context {PI : PAImg seg_listing}` of image B's listing).
   RELOCATION of image A's reac_box_catalogue_by_token (0x8a148): of image B's 16 words 14 are image A's, the other
   two (`jal` 0x8a908 to the strlen trampoline 0x43a98 and `j` 0x8a920 to fuzz_catalogue_row 0x8a7d8) reach the same
   symbols at image B's addresses; the walk reaches them through the B listing's PCall / PTail slots (SegList.v
   :5893, :5899), SIGMA and seg_sig_prog. the image-A m_file-family lane's image-A walk lib/A/Prog/reac_box_catalogue_by_tokenA.v was
   not on origin when this file was written, so the text is new: the form of the guide
   the walk-form survey (2.4 the strlen call, 2.5 / 2.7 the tail call as in
   fuzz_command's hand_back.v:888-907), the logic of the segconf porter's UBSan walk lib/U/Prog/reac_box_catalogue_by_token.v,
   and the image-B shape of the image-B listing lane's check_absent walk (a working branch: the entry seed, cl_callS
   at a program callee, and its check_absent_lem.v reader lemmas, restated below with the prefix tk_).
   Code (the neutral listing of reac_box_catalogue_by_token in image B):
     0x8a8f4 .. 0x8a8fc  addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp)
     0x8a900             beqz a0, 0x8a924: not taken, by_token_pre gives tok <> 0; the NULL arm 0x8a924 .. 0x8a930
                         (which returns 0) is not reached under the contract
     0x8a904 .. 0x8a908  s0 := a0; jal strlen (trampoline 0x43a98; the image-A wrapper lane's row 16, RtString.astrlen_realizes)
     0x8a90c .. 0x8a91c  a1 := strlen's answer; a0 := s0; ra and s0 back from the frame; sp := sp0
     0x8a920             j fuzz_catalogue_row: the tail call at the entry sp with the entry ra (cl_callS with o = 0,
                         raw = getr regs 1 and the entry's chain), so fuzz_catalogue_row_contract's post, at the
                         call's state, is this function's.
   No instrumented check (the executor's shadow table is empty) and no UBSan trap: none of the 16 words is
   `unimp` and no branch targets one.
   Image B's numbers (SegInstB.v): STK_reac_box_catalogue_by_token = STK_fuzz_catalogue_row = 64 + 2 * ESTACK =
   8256 (the tail-called callee runs at this function's entry sp, deeper than its own 16-byte frame plus strlen's
   ESTACK; guide pitfall 11), RLO_A / RHI_A = SegGlob's 0xa1c60 / 0xa3f08, catA = 0xa20a0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YK06 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
fuzz_catalogue_row_c reac_box_catalogue_by_token_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------
   Readers that agree below alloc_ceiling: the token, its shadow and the catalogue lie there (a heap block, a
   side-stack frame or the image), the real stack above it. the image-B listing lane's check_absent_lem.v (ca_shadow_low,
   ca_hull_low, ca_tail_low, ca_addr_low, ca_loc_low, ca_rodata_kept), restated. *)
Section cc. Context {rc : YM05.RunCeil}.
Definition tk_low (rd rd' : reader) : Prop := forall a, 0 <= a < alloc_ceiling -> rd' a = rd a.
Lemma tk_low_of_kept : forall rd rd' lo hi, kept_out rd rd' lo hi -> alloc_ceiling <= lo -> tk_low rd rd'.
Proof using.
  unfold kept_out, tk_low. intros rd rd' lo hi H Hlo a Ha. pose proof asan_consts as ([Hmin Hmax] & _).
  apply H; lia.
Qed.
Lemma tk_shadow_low : forall x, 0 <= x -> x < alloc_ceiling -> 4096 <= SHADOW_OFF + x / 8 < alloc_ceiling.
Proof using.
  intros x H0 H. pose proof asan_consts as ([Hmin Hmax] & _).
  assert (Hd : x / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
  assert (HC : 140737479966720 / 8 = 17592184995840) by reflexivity.
  assert (H0d : 0 <= x / 8) by (apply Z.div_pos; lia).
  unfold SHADOW_OFF. lia.
Qed.
Lemma tk_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= alloc_ceiling ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 4096 <= s < alloc_ceiling.
Proof using.
  intros x n s H0 Hn Hxn Hs. pose proof asan_consts as ([Hmin Hmax] & _).
  unfold shadow_addr in Hs.
  assert (L1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (L2 : 268431360 <= (SHADOW_OFF + x / 8) / 8).
  { apply Z.div_le_lower_bound; [lia|]. unfold SHADOW_OFF. lia. }
  assert (U1 : (x + n - 1) / 8 <= 140737479966720 / 8) by (apply Z.div_le_mono; lia).
  assert (UC : 140737479966720 / 8 = 17592184995840) by reflexivity.
  assert (U2 : (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (x + n - 1) / 8).
  { rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
  unfold SHADOW_OFF in *. lia.
Qed.
(* the word-at-a-time slack after a terminator below alloc_ceiling stays below it (alloc_ceiling is a multiple of
   4096, so of 8) *)
Lemma tk_tail_low : forall e, 0 <= e -> e < alloc_ceiling -> e - e mod 8 + 8 <= alloc_ceiling.
Proof using.
  intros e H0 He. pose proof alloc_ceiling_value as [_ CMOD].
  assert (H8 : alloc_ceiling mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact CMOD]]. }
  apply Z.mod_divide in H8 as [q Hq]; [|lia].
  pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hb.
  pose proof (Z.div_mod e 8 ltac:(lia)) as Hdm.
  assert (Hlt : e / 8 < q) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.
(* the shadow fact of a range below alloc_ceiling survives such an agreement *)
Lemma tk_addr_low : forall (rd rd' : reader) q n, tk_low rd rd' ->
  0 <= q -> q + n <= alloc_ceiling -> sa_addr rd q n -> sa_addr rd' q n.
Proof using.
  intros rd rd' q n L Hq Hqn (A1 & A2 & A3 & A4 & A5). unfold tk_low in L.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
  - intros x Hx. destruct (A4 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite L; [exact Hs|]. unfold shadow_of_addr. pose proof (tk_shadow_low x ltac:(lia) ltac:(lia)). lia.
  - intros Hn s Hs. rewrite L; [exact (A5 Hn s Hs)|].
    pose proof (tk_hull_low q n s Hq Hn Hqn Hs). lia.
Qed.
(* a shorter range at the same start *)
Lemma tk_addr_sub : forall (rd : reader) q n m, sa_addr rd q n -> 0 <= m <= n -> sa_addr rd q m.
Proof using.
  intros rd q n m (A1 & A2 & A3 & A4 & A5) Hm.
  split; [exact A1|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  - eapply range_addressable_sub; [exact A4 | lia | lia].
  - intros Hm0 s Hs. apply (A5 ltac:(lia)). unfold shadow_addr in *.
    assert (D1 : (q + m - 1) / 8 <= (q + n - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (SHADOW_OFF + (q + m - 1) / 8) / 8 <= (SHADOW_OFF + (q + n - 1) / 8) / 8)
      by (apply Z.div_le_mono; lia).
    lia.
Qed.
Lemma tk_loc_sub : forall segs B ly S q n m, sa_loc segs B ly S q n -> 0 <= m <= n -> sa_loc segs B ly S q m.
Proof using.
  intros segs B ly S q n m [(b & k & Hb & H1 & H2) | [(cid & pos & Hf & H0 & H1 & H2) | HI]] Hm.
  - left. exists b, k. split; [exact Hb | lia].
  - right; left. exists cid, pos. split; [exact Hf|]. split; [exact H0 | lia].
  - right; right. intros x Hx. apply HI. lia.
Qed.
Lemma tk_bytes_app : forall (rd : reader) a l1 l2, sa_bytes rd a (l1 ++ l2) -> sa_bytes rd a l1.
Proof using.
  intros rd a l1 l2 H i Hi. rewrite <- (app_nth1 l1 l2 ZB0 Hi). apply H. rewrite length_app. lia.
Qed.
(* the catalogue premise at a reader that agrees below alloc_ceiling: the table and the tokens are image bytes *)
Lemma tk_cat_low : forall segs B H mem H' mem' cat,
  (forall a, in_img segs a -> 0 <= a < alloc_ceiling) ->
  tk_low (aview segs H mem) (aview segs H' mem') ->
  sa_cat segs B (aview segs H mem) cat -> sa_cat segs B (aview segs H' mem') cat.
Proof using.
  intros segs B H mem H' mem' cat HI L (Hpin & Himg & Hrows). unfold tk_low in L.
  split; [exact Hpin|]. split; [exact Himg|].
  intros i Hi. destruct (Hrows i Hi) as (tp & Hw & Hlit).
  destruct Hlit as (Htp & ((Hzs & Hn0) & _) & Hp & Hr & Hm).
  exists tp. split.
  - rewrite (rdword_ext (aview segs H mem) (aview segs H' mem')); [exact Hw|].
    intros k Hk. apply L.
    assert (Hrow : cat <= pin_spec.row_addr cat i + k < cat + pin_spec.CAT_BYTES).
    { unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
    destruct (Himg (pin_spec.row_addr cat i + k) Hrow) as (Hii & _ & _).
    exact (HI _ Hii).
  - unfold sa_lit, sa_str, sa_strz. split; [exact Htp|]. split; [split; [split; [|exact Hn0]|]|].
    + intros j Hj. rewrite L; [exact (Hzs j Hj)|].
      rewrite length_app in Hj. cbn [length] in Hj.
      destruct (Hm (tp + Z.of_nat j) ltac:(lia)) as (Hii & _ & _).
      exact (HI _ Hii).
    + exact (sa_tail_of_romtail segs H' mem' _ Hr).
    + split; [exact Hp|]. split; [exact Hr | exact Hm].
Qed.
(* by_token_pre at a reader that agrees below alloc_ceiling, for a token that lies below it *)
Lemma tk_btp_low : forall segs B ly S H mem H' mem' cat tok s,
  (forall a, in_img segs a -> 0 <= a < alloc_ceiling) ->
  tk_low (aview segs H mem) (aview segs H' mem') ->
  0 <= tok -> tok + Z.of_nat (length s) + 1 <= alloc_ceiling ->
  by_token_pre segs B ly S (aview segs H mem) cat tok s -> by_token_pre segs B ly S (aview segs H' mem') cat tok s.
Proof using.
  intros segs B ly S H mem H' mem' cat tok s HI L H0 Hc (Hne & ((Hzs & Hn0) & Ht) & Ha & Hl & Hlen & Hcat).
  pose proof L as L'. unfold tk_low in L'.
  unfold by_token_pre. split; [exact Hne|]. split.
  { unfold sa_str, sa_strz. split; [split; [|exact Hn0]|].
    - intros j Hj. rewrite L'; [exact (Hzs j Hj)|]. rewrite length_app in Hj. cbn [length] in Hj. lia.
    - intros x Hx. rewrite L'; [exact (Ht x Hx)|].
      pose proof (tk_tail_low (tok + Z.of_nat (length s)) ltac:(lia) ltac:(lia)). lia. }
  split; [exact (tk_addr_low _ _ tok (Z.of_nat (length s) + 1) L H0 ltac:(lia) Ha)|].
  split; [exact Hl|]. split; [exact Hlen|].
  exact (tk_cat_low segs B H mem H' mem' cat HI L Hcat).
Qed.
(* arodata_okP at a later state: every read-only byte lies below the window *)
Lemma tk_rodata_kept : forall segs B RLO RHI (rd rd' : reader) lo hi,
  kept_out rd rd' lo hi ->
  (forall a, in_roP segs RLO RHI a -> 0 <= a < 2 ^ 64 /\ a < lo) ->
  arodata_okP segs RLO RHI B rd -> arodata_okP segs RLO RHI B rd'.
Proof using.
  intros segs B RLO RHI rd rd' lo hi HK HB0 HR a Hro Ho He.
  destruct (HB0 a Hro) as [Hb Hlt]. rewrite (HK a Hb ltac:(lia)). exact (HR a Hro Ho He).
Qed.
End cc.

(* where the token lies: in [4096, alloc_ceiling) (blocks and frames by AR's laws, image bytes by the image's
   bound) *)
Section ll. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tk_loc_low : forall segs B (LAWS : AR_laws segs B) ly S W mem md q n,
  AR segs B ly S W mem md -> (forall a, in_img segs a -> 4096 <= a < alloc_ceiling) ->
  sa_loc segs B ly S q n -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling.
Proof using.
  intros segs B LAWS ly S W mem md q n HAR HI HL Hn.
  destruct HL as [(b & m & Hb & H1 & H2) | [(cid & pos & Hf & _ & H1 & H2) | HM]].
  - destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & H4 & Hc & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
  - destruct (al_sep _ _ LAWS ly S W mem md HAR) as [_ HF].
    pose proof (proj1 (Forall_forall _ _) HF (cid, pos) Hf) as Hfb. cbn [fst snd] in Hfb. lia.
  - destruct (HM q ltac:(lia)) as (Hq & _ & _). destruct (HM (q + n - 1) ltac:(lia)) as (Hq' & _ & _).
    pose proof (HI _ Hq). pose proof (HI _ Hq'). lia.
Qed.
End ll.

(* ------------------------------------------------------------------------------------------------
   The symbolic entry state: the stack pointer (atom 2) and the 16-byte frame below it. Atom 32 is the shadow
   base the executor's shadow table is indexed by; this function has no instrumented check, so the table is
   empty. *)
Definition TK_SB : Z := 0x7fff8000.
Definition TKx : sv := SOff 32 0.
Definition TKspan : Z * Z := (TK_SB, TK_SB + 2 ^ 44 - 1).
Definition tk_regions : smem := [stack_region 16].
Definition tk_facts : facts := mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF TK_SB TK_SB 0)] [] [].
Definition ss_tk : sstate := mkSS AF_reac_box_catalogue_by_token sr_atoms tk_regions None tk_facts.
Definition tk_SH : list shent := [].
Definition tk_extra : list word := [Z_to_bv 64 TK_SB].
(* the strlen call's return point 0x8a90c, as a listing offset *)
Definition TK_RET : Z := 0x5b4c.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition tk_E (regs : bvmap 5 word) : env := Eimg (Ereg regs tk_extra).

Lemma tk_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly STK,
  astk_ok STK ly (spZ regs) -> 16 <= STK ->
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (tk_E regs) ss_tk
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_catalogue_by_token)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS TKx tk_SH (tk_E regs) (mrestrict (w_H W) mem).
Proof using.
  intros W regs mem ly STK Hstk H16 Hpres.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as [[CMIN CMAX] CMOD].
  set (E := tk_E regs).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs tk_extra) n)
    by (intros n Hn; subst E; unfold tk_E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 TK_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  split.
  - unfold ss_tk. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    + subst E. unfold tk_E. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold tk_regions, stack_region.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + apply pairwise_disjoint_of_extents. unfold tk_regions, stack_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [tk_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32, !unsigned_lit_small by (unfold TK_SB; lia).
      unfold TK_SB. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil Hal16 Hstk0 C1 CMIN CMAX. clear. intros.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
  - unfold sh_ok, tk_SH. constructor.
Qed.

Section e.
Variable B : asyms.
(* the listing facts every walk of this tree takes: PALib (the errno cell the strlen step needs; SegPaLib.v) and
   the call targets of the program functions (SegObj.v seg_sig_prog) *)
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog.
(* the two callees: the image-A wrapper lane's row 16, the strlen wrapper at its trampoline (0x43a98), at every FP state; and
   fuzz_catalogue_row's contract at its entry, its window and the same read-only window and table *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis FCR : fuzz_catalogue_row_contract SEGS B (BASE + AF_fuzz_catalogue_row) SegInstB.STK_fuzz_catalogue_row
  SegInstB.RLO_A SegInstB.RHI_A SegInstB.catA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let errno_low := pal_env B TL.

Theorem reac_box_catalogue_by_token_walkB :
  reac_box_catalogue_by_token_contract SEGS B (BASE + AF_reac_box_catalogue_by_token)
    SegInstB.STK_reac_box_catalogue_by_token SegInstB.RLO_A SegInstB.RHI_A SegInstB.catA.
Proof.
unfold reac_box_catalogue_by_token_contract.
intros ly S W regs mem md ch tok s HPRE HROD H10 Htok64 HBT HEV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof (pa_img_range (L := seg_listing)) as HIMG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as [[CMIN CMAX] CMOD].
assert (Hes : ESTACK = 4096) by reflexivity.
(* image B's windows (SegInstB.v) *)
assert (WS : SegInstB.STK_reac_box_catalogue_by_token = 8256) by reflexivity.
assert (WF : SegInstB.STK_fuzz_catalogue_row = 8256) by reflexivity.
rewrite WS in HPRE |- *.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (LOWSP : alloc_ceiling <= spZ regs - 8256) by lia.
assert (IMGLOW : forall a, in_img SEGS a -> 4096 <= a < alloc_ceiling)
  by (intros a Ha; pose proof (HIMG a Ha) as [L1 L2]; unfold kImgEnd in L2; lia).
assert (IMGLOW0 : forall a, in_img SEGS a -> 0 <= a < alloc_ceiling)
  by (intros a Ha; pose proof (IMGLOW a Ha); lia).
(* every read-only byte of the image lies below the window *)
assert (ROLOW : forall a, in_roP SEGS SegInstB.RLO_A SegInstB.RHI_A a -> 0 <= a < 2 ^ 64 /\ a < spZ regs - 8256).
{ intros a [(sg & Hin & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hin | exact Hr]).
    pose proof (IMGLOW a Hi). lia.
  - unfold SegInstB.RLO_A, SegInstB.RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
(* the token: below alloc_ceiling, a C string with no NUL among its bytes *)
pose proof HBT as (Hne & HSTR & HADDR & HLOC & HLEN & HCAT).
destruct (tk_loc_low SEGS B LAWS ly S W mem md tok (Z.of_nat (length s) + 1) HAR IMGLOW HLOC ltac:(lia))
  as [TLO THI].
destruct (sa_strz_bytes SEGS (w_H W) mem tok s (proj1 HSTR)) as (_ & _ & HZS).
assert (HNUL : SegModel.nulfree s) by exact (proj2 (proj1 HSTR)).
assert (HLzb : Z.of_nat (length (seg_spec.zb s)) = Z.of_nat (length s))
  by (unfold seg_spec.zb; rewrite length_map; reflexivity).
destruct (tk_entry W regs mem ly 8256 Hstk ltac:(lia) Hpres) as [HS SHOK].
assert (HJ : ajournal SEGS B 8256 (spZ regs) [] ly S W mem md [] ly S W mem md 0) by (eapply ajournal_init; exact HPRE).
unfold cfg_at, w64.
set (E := tk_E regs) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, tk_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs tk_extra) n)
  by (intros n Hn; unfold E, tk_E; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E8 : ew E 8 = getr regs 8) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 tok) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs tk_extra) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
clearbody E. clear EL EEo.
(* ---- 0x8a8f4 .. 0x8a8fc: the frame, ra and s0 stored; the run stops at the beqz 0x8a900 ---- *)
paj_run_tok RUN HS HJ SHOK TKspan.
{ awr_ok_tac; exact Usp. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
assert (K1 : kept_out (rdW W m1) (rdW W m2) (spZ regs - 8256) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 8256 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    destruct Hin
  | lia | exact Hn ]) end.
clear HF HFr HG.
(* 0x8a900 beqz a0: a0 is the token, and tok <> 0, so the NULL arm 0x8a924 is not taken *)
psrr_branch_tok RUN BR HS SHOK TKspan.
{ exfalso. apply Hne. rewrite branch_eq_U, U_SLit in Hc. apply Z.eqb_eq in Hc.
  rewrite (U_atom E 10 tok E10 ltac:(lia)) in Hc. change (zcanon 0) with 0 in Hc. exact Hc. }
clear Hc.
(* ---- 0x8a904 .. 0x8a908: s0 := a0, jal strlen ---- *)
paj_run_tok RUN HS HJ SHOK TKspan.
{ awr_ok_tac; exact Usp. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
assert (K2 : kept_out (rdW W m1) (rdW W m2) (spZ regs - 8256) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 8256 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    destruct Hin
  | lia | exact Hn ]) end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?mdT) _ =>
  set (rT0 := rT) in *; set (mT0 := mT) in *; set (mdT0 := mdT) in * end.
assert (K01 : kept_out (rdW W mem) (rdW W mT0) (spZ regs - 8256) (spZ regs))
  by (apply (kept_out_trans _ _ _ _ _ _ _ K1 K2); lia).
clear K1 K2.
assert (HspT : spZ rT0 = spZ regs + -16)
  by (unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; reflexivity).
assert (P3' : getr rT0 3 = Z_to_bv 64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
assert (P4' : getr rT0 4 = Z_to_bv 64 (as_tp B)) by (rewrite P4, E4; exact Htp).
assert (P10' : getr rT0 10 = Z_to_bv 64 tok) by (rewrite P10; exact E10).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* strlen's premises at the call: the token's text, its range and tail, the read-only words *)
pose proof (tk_btp_low SEGS B ly S (w_H W) mem (w_H W) mT0 SegInstB.catA tok s IMGLOW0
  (tk_low_of_kept _ _ _ _ K01 LOWSP) ltac:(lia) ltac:(lia) HBT) as BT0.
destruct BT0 as (_ & ((Z0 & N0) & T0) & A0 & _ & _ & _).
destruct (sa_strz_bytes SEGS (w_H W) mT0 tok s (conj Z0 N0)) as (BY0 & NZ0 & _).
assert (STR0 : astr_at SEGS W mT0 tok (seg_spec.zb s)) by (split; [exact BY0 | exact NZ0]).
assert (RD0 : aread_ok SEGS ESTACK W rT0 mT0 tok (astr_len (seg_spec.zb s) + 1)).
{ unfold astr_len. rewrite HLzb. destruct A0 as (Q0 & Q1 & Q2 & Q3 & Q4). unfold aread_ok.
  split; [lia|]. split; [lia|]. split; [lia|]. split.
  - intros a Ha. split.
    + replace a with (tok + Z.of_nat (Z.to_nat (a - tok))) by lia.
      rewrite (Z0 (Z.to_nat (a - tok))); [discriminate|]. rewrite length_app. cbn [length]. lia.
    + unfold ascratch_stk. rewrite HspT. lia.
  - split; [exact Q2|]. split; [exact Q3 | exact Q4]. }
assert (TL0 : atail_vis SEGS W mT0 (tok + astr_len (seg_spec.zb s))) by (unfold astr_len; rewrite HLzb; exact T0).
assert (ROD0 : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W mT0))
  by (eapply tk_rodata_kept; [exact K01 | exact ROLOW | exact HROD]).
assert (ROM0 : rt_rom_view SEGS B W mT0) by (intros a Hr Ho He; exact (ROD0 a (or_introl Hr) Ho He)).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False) (SIGMA SS___interceptor_trampoline_strlen)
    W rT0 mT0 8256 (spZ regs) [] ly S W mem md [] ly S mdT0 0 (-16) (Z_to_bv 64 (BASE + TK_RET)) _ HJ HspT eq_refl
    ltac:(lia) ltac:(lia) ltac:(lia) P1 (fun a0 (H : False) => False_ind _ H)).
  apply (ASTRLEN fx ly S W rT0 mT0 mdT0 tok (seg_spec.zb s)).
  - exact (ecall_pre_stk_at SEGS B ESTACK 8256 (spZ regs) [] ly S W mem md [] ly S W mT0 mdT0 0 rT0 (-16)
      HJ HspT eq_refl ltac:(lia) ltac:(lia) ltac:(lia) HraT P3' P4').
  - exact P10'.
  - lia.
  - exact STR0.
  - exact RD0.
  - exact TL0.
  - exact ROM0. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* ---- back at 0x8a90c: the frame region is kept, the caller-saved registers are fresh atoms from 40 ---- *)
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply HK2; [lia | rewrite Hes; lia | intros []].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A44 : ew (havoc E 40 (map (getr regs2) CLOB)) 44 = getr regs2 10) by reflexivity.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 40)%nat -> ew Ea n = ew E n)
  by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : env_agree 32 (Ereg regs tk_extra) Ea).
{ destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite OLDa by lia; exact (HA1 n Hn) | rewrite HEa; exact HA2]. }
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
assert (SHOKa : sh_ok SEGS TKx tk_SH Ea (mrestrict (w_H W) mem2)) by (unfold sh_ok, tk_SH; constructor).
assert (K3 : kept_out (rdW W mT0) (rdW W mem2) (spZ regs - 8256) (spZ regs))
  by (intros a Ha Hn; apply HK2; [exact Ha | rewrite Hes; lia | intros []]).
clear HK2.
(* ---- 0x8a90c .. 0x8a920: a1 := n, a0 := s0, ra and s0 back from the frame, sp := sp0, j fuzz_catalogue_row ---- *)
paj_run_tok RUN HS HJ2 SHOKa TKspan.
{ awr_ok_tac; exact Uspa. }
lazymatch goal with Hfr : frame_of Ea _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
assert (K4 : kept_out (rdW W m1) (rdW W m2) (spZ regs - 8256) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 8256 <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uspa in Hrr; lia|]);
    destruct Hin
  | lia | exact Hn ]) end.
clear HF HFr HG.
(* the callee-saved registers at the tail call are the entry's *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HPc : aregs_preserved regs (ms_regs msx))
    by exact (aregs_preserved_of_st_ok SEGS _ Ea _ _ regs tk_extra HS HAEa ltac:(vm_compute; reflexivity)) end.
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?mdT) _ =>
  set (rT3 := rT) in *; set (mT3 := mT) in *; set (mdT3 := mdT) in * end.
assert (Kc : kept_out (rdW W mem) (rdW W mT3) (spZ regs - 8256) (spZ regs))
  by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ K01 K3 ltac:(lia) ltac:(lia)) K4); lia).
clear K3 K4.
assert (HspC : spZ rT3 = spZ regs + 0)
  by (unfold spZ at 1; rewrite T2, Uspa; lia).
assert (T1' : getr rT3 1 = getr regs 1) by (rewrite T1, OLDa by lia; exact E1).
assert (T3' : getr rT3 3 = Z_to_bv 64 (as_gp B)) by (rewrite T3, OLDa, E3 by lia; exact Hgp).
assert (T4' : getr rT3 4 = Z_to_bv 64 (as_tp B)) by (rewrite T4, OLDa, E4 by lia; exact Htp).
assert (T10' : getr rT3 10 = Z_to_bv 64 tok) by (rewrite T10, OLDa by lia; exact E10).
assert (T11' : getr rT3 11 = w64 (Z.of_nat (length (seg_spec.zb s)))) by (rewrite T11, A44; exact HQ2).
assert (Hs0T : s0Z rT3 = s0Z regs) by (unfold s0Z; rewrite T8, OLDa, E8 by lia; reflexivity).
assert (HchT : achain ly (rdW W mT3) (spZ regs + 0) (s0Z rT3) ch).
{ rewrite Hs0T, Z.add_0_r.
  apply (achain_kept ly (rdW W mem) (rdW W mT3) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. apply (Kc a); lia. }
(* fuzz_catalogue_row's premises at the tail call: the token's n = length s bytes, their range and place, the table *)
pose proof (tk_btp_low SEGS B ly S (w_H W) mem (w_H W) mT3 SegInstB.catA tok s IMGLOW0
  (tk_low_of_kept _ _ _ _ Kc LOWSP) ltac:(lia) ltac:(lia) HBT) as BTc.
destruct BTc as (_ & ((Zc & Nc) & _) & Ac & _ & _ & CATc).
destruct (sa_strz_bytes SEGS (w_H W) mT3 tok s (conj Zc Nc)) as (BYc & _ & _).
assert (SBc : sa_bytes (rdW W mT3) tok (seg_spec.zb s)) by exact (tk_bytes_app _ _ _ _ BYc).
assert (SAc : sa_addr (rdW W mT3) tok (Z.of_nat (length (seg_spec.zb s))))
  by (apply (tk_addr_sub _ tok (Z.of_nat (length s) + 1)); [exact Ac | lia]).
assert (SLc : sa_loc SEGS B ly S tok (Z.of_nat (length (seg_spec.zb s))))
  by (apply (tk_loc_sub SEGS B ly S tok (Z.of_nat (length s) + 1)); [exact HLOC | lia]).
assert (RODc : arodata_okP SEGS SegInstB.RLO_A SegInstB.RHI_A B (rdW W mT3))
  by (eapply tk_rodata_kept; [exact Kc | exact ROLOW | exact HROD]).
(* the tail call's target is fuzz_catalogue_row's entry *)
rewrite (SIGP SS_fuzz_catalogue_row ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_fuzz_catalogue_row) with AF_fuzz_catalogue_row by (vm_compute; reflexivity).
eapply SRr_mono.
{ eapply (cl_callS B LAWS W rT3 mT3 _ 8256 (spZ regs) [] ly S W mem md [] ly S mdT3 0
    SegInstB.STK_fuzz_catalogue_row [] 0 0 (getr regs 1) ch
    (fun ly3 S3 W3 regs3 mem3 md3 =>
      getr regs3 10 = w64 (seg_spec.cat_ptr SegInstB.catA (SegModel.cat_row (seg_spec.zs (seg_spec.zb s)))) /\
      sa_kept SEGS W mT3 W3 mem3 rT3 SegInstB.STK_fuzz_catalogue_row (fun _ => False) /\
      sa_noalloc B ly S ly3 S3)
    HJ2 HspC).
  - reflexivity.
  - lia.
  - rewrite WF; lia.
  - rewrite WF; lia.
  - exact T3'.
  - exact T4'.
  - exact T1'.
  - exact Hra.
  - exact Hra4.
  - exact HchT.
  - intros HPRE1. eapply SRr_mono.
    + apply (FCR ly S W rT3 mT3 mdT3 ch tok (Z.of_nat (length (seg_spec.zb s))) (seg_spec.zb s) HPRE1 RODc T10'
        Htok64 T11' ltac:(lia) SBc eq_refl SAc SLc CATc).
      unfold EV_fuzz_catalogue_row. unfold EV_reac_box_catalogue_by_token in HEV. lia.
    + cbv beta. unfold apost_base.
      intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite T1'; reflexivity|].
      split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & _ & HP3 & (A0r & KP & NA)).
unfold apost_base. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|].
split; [exact HJ3|].
split; [exact (aregs_preserved_trans _ _ _ HPc HP3)|].
split.
{ rewrite A0r, HZS. unfold SegModel.by_token. rewrite (SegModel.cut_nul_id s HNUL). reflexivity. }
split; [|exact NA].
intros a Ha Hn _.
rewrite (KP a Ha ltac:(rewrite HspC, WF, Z.add_0_r; exact Hn) (fun x => x)).
exact (Kc a Ha Hn).
Qed.
(* inside the Sections: the walk's hypotheses as its assumptions *)
About reac_box_catalogue_by_token_walkB.
Print Assumptions reac_box_catalogue_by_token_walkB.
End e.
End f.
End d.
About reac_box_catalogue_by_token_walkB.
Print Assumptions reac_box_catalogue_by_token_walkB.

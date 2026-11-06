(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v, with its numbers changed; 410 of its 529 lines of code are new or changed and 673 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC81 YC85 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition y_dsh_cell (p n x : Z) : Z := if (x - p) / 8 <? n / 8 then 0 else n mod 8.
Definition y_dsh_cell_addr (x : Z) : Z := SHADOW_OFF + x / 8.

Lemma y_div8_shift : forall p d, p mod 8 = 0 -> (p + d) / 8 = p / 8 + d / 8.
Proof.
intros p d Hp. pose proof (Z.div_mod p 8 ltac:(lia)) as D.
replace (p + d) with (8 * (p / 8) + d) by lia. rewrite Z.mul_comm, Z.div_add_l by lia. lia.
Qed.

Lemma y_shaddr_range : forall y, 0 <= y < 2 ^ 64 -> 0 <= SHADOW_OFF + y / 8 < 2 ^ 64.
Proof.
intros y Hy.
assert (Hlt : y / 8 < 2305843009213693952)
  by (apply Z.div_lt_upper_bound; [lia | change (8 * 2305843009213693952) with (2 ^ 64); lia]).
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia.
Qed.

Lemma y_dsh_cell_range : forall p n x, 0 <= y_dsh_cell p n x < 8.
Proof.
intros p n x. unfold y_dsh_cell. destruct ((x - p) / 8 <? n / 8); [lia|].
pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
Qed.

Lemma y_dsh_cell_lt : forall p n x,
  p mod 8 = 0 -> 0 <= n -> p <= x < p + n -> y_dsh_cell p n x <> 0 -> x mod 8 < y_dsh_cell p n x.
Proof.
intros p n x Hp Hn Hx Hne. unfold y_dsh_cell in *.
destruct ((x - p) / 8 <? n / 8) eqn:Hlt; [lia|]. apply Z.ltb_ge in Hlt.
assert (Hdiv : (x - p) / 8 = n / 8).
{ pose proof (Z.div_le_mono (x - p) n 8 ltac:(lia) ltac:(lia)). lia. }
pose proof (Z.div_mod (x - p) 8 ltac:(lia)) as D1.
pose proof (Z.div_mod n 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (x - p) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
assert (Hm : (x - p) mod 8 < n mod 8) by lia.
replace (x mod 8) with ((x - p) mod 8); [exact Hm|].
rewrite <- (Z.add_0_r (x - p)) at 1. rewrite <- Hp.
rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Lemma y_lor_lxor : forall x y, Z.land x y = 0 -> Z.lor x y = Z.lxor x y.
Proof.
intros x y H. apply Z.bits_inj'. intros n Hn.
rewrite Z.lor_spec, Z.lxor_spec.
assert (Hb : Z.testbit (Z.land x y) n = false) by (rewrite H; apply Z.testbit_0_l).
rewrite Z.land_spec in Hb.
destruct (Z.testbit x n), (Z.testbit y n); cbn in *; congruence.
Qed.

Lemma y_lor_byte : forall a b, 0 <= a < 256 -> 0 <= b -> Z.lor (256 * b) a = a + 256 * b.
Proof.
intros a b Ha Hb.
assert (Hsh : Z.shiftl b 8 = 256 * b) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
assert (Hlog : Z.log2 a < 8).
{ destruct (Z.eq_dec a 0) as [->|Hne]; [rewrite Z.log2_nonpos by lia; lia|].
  apply Z.log2_lt_pow2; [lia | change (2 ^ 8) with 256; lia]. }
assert (HL : Z.land (256 * b) a = 0).
{ apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
  destruct (Z_lt_le_dec n 0) as [Hn|Hn].
  - rewrite (Z.testbit_neg_r a n Hn). apply andb_false_r.
  - destruct (Z_lt_le_dec n 8) as [H8|H8].
    + rewrite <- Hsh, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r b (n - 8)) by lia. reflexivity.
    + rewrite (Z.bits_above_log2 a n ltac:(lia) ltac:(lia)). apply andb_false_r. }
rewrite (y_lor_lxor _ _ HL).
rewrite <- Z.add_nocarry_lxor by exact HL. lia.
Qed.

Definition yr_sr : list sv :=
  [SLit 0; SOff 544 0; SOff AT_A 0; SOff 3 0; SOff 4 0; SOff 545 0; SOff 546 0; SOff 547 0;
   SOff AT_STK 0; SOff AT_A 0; SOff 548 0; SOff 549 0; SOff 550 0; SOff 551 0; SOff 531 0; SOff 552 0;
   SOff 536 0; SOff 553 0; SLit WS_MASK; SOff 32 0; SLit 32; SOff 532 0; SLit 1; SOff 537 0;
   SOff 554 0; SOff 534 0; SOff 533 0; SOff AT_SH 0; SOff 555 0; SOff 556 0; SOff 557 0; SOff 558 0].

Definition yr_acs : list YP09.chunk :=
  [YP09.mkChunk 208 (CVal 8 (SOff 532 0)); YP09.mkChunk 320 (CVal 8 (SOff 533 0));
   YP09.mkChunk 360 (CVal 8 (SOff 535 0)); YP09.mkChunk 352 (CVal 8 (SOff 536 0));
   YP09.mkChunk 184 (CVal 8 (SOff 538 0)); YP09.mkChunk 120 (CVal 8 (SOff 539 0));
   YP09.mkChunk 136 (CVal 8 (SLit 0));
   YP09.mkChunk 376 (CVal 8 (SOff 540 0)); YP09.mkChunk 280 (CVal 8 (SOff 541 0));
   YP09.mkChunk 232 (CVal 8 (SOff 542 0)); YP09.mkChunk 264 (CVal 8 (SOff 543 0))].

Lemma y_Z_to_bv_mod64 : forall v, Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v.
Proof.
intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Ltac yr_rg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

Definition yr_win_ok (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  match YP09.r_base r with
  | Some 60%nat => (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 472)
  | Some 516%nat => (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 4096)
  | Some 529%nat => (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 512)
  | _ => false
  end.
Definition yr_wins_ok (rs : smem) : bool := forallb yr_win_ok rs.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Definition yr_vals (cx : dcx) (h i n now op : Z) (regs : bvmap 5 word) : list word :=
  [w64 n; w64 i; w64 now; w64 (d_cur cx n); w64 op; w64 (if op <? 128 then op else op - 256); w64 (op mod 4);
   w64 h; w64 (h + 440); w64 (dnot (d_obj cx OG)); w64 (dnot (d_obj cx OT)); w64 (dnot (d_obj cx OO));
   w64 (dnot (d_obj cx OUSED));
   getr regs 1; getr regs 5; getr regs 6; getr regs 7; getr regs 10; getr regs 11; getr regs 12; getr regs 13;
   getr regs 15; getr regs 17; getr regs 24; getr regs 28; getr regs 29; getr regs 30; getr regs 31;
   w64 (y_dsh_cell_addr (d_cur cx n)); w64 (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n));
   w64 (rdb (rest_of (c_pl cx) n) 0);
   w64 (y_dsh_cell_addr (d_cur cx n + 1)); w64 (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n + 1));
   w64 (rdb (rest_of (c_pl cx) n) 1)].

Lemma y_val_mem_mod64 : forall m a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. specialize (H k Hk).
replace (YO0f.le_byte (v mod 2 ^ 64) 8 k) with (YO0f.le_byte v 8 k); [exact H|].
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma y_val_mem_unmod64 : forall m a v, val_mem SEGS m a 8 (v mod 2 ^ 64) -> val_mem SEGS m a 8 v.
Proof.
intros m a v H k Hk. specialize (H k Hk).
replace (YO0f.le_byte v 8 k) with (YO0f.le_byte (v mod 2 ^ 64) 8 k); [exact H|].
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma y_env_old : forall cx E vals q, (q < AT_FL)%nat -> ew (d_env cx E vals) q = ew E q.
Proof. intros cx E vals q Hq. unfold d_env. apply ew_havoc_old. exact Hq. Qed.

Lemma y_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma y_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
rewrite !y_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
- intros q r Hq. rewrite y_env_old; [exact (EE q r Hq)|].
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
- unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.

Lemma y_bvr : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as Hr. unfold bv_modulus in Hr. exact Hr. Qed.

Lemma y_A_range : forall S, 0 <= S - MFRAME ->
  S - MFRAME - 31 <= 32 * ((S - MFRAME) / 32) <= S - MFRAME.
Proof.
intros S Hs. pose proof (Z.div_mod (S - MFRAME) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (S - MFRAME) 32 ltac:(lia)) as Hmp. lia.
Qed.

Lemma y_frame_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hw x. apply HF. intros (r & Hr & Ha).
rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.

Lemma y_mrestrict_ext : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall x, mrestrict H m' x = mrestrict H m x.
Proof. intros H m m' HM x. unfold mrestrict. rewrite HM. reflexivity. Qed.

Lemma y_mbyte_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof. intros segs H m m' HM a. unfold mbyte, mrestrict. rewrite HM. reflexivity. Qed.

Lemma y_aview_ext : forall segs (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' HM a. unfold aview. rewrite (y_mbyte_ext segs H m m' HM). reflexivity. Qed.

Lemma y_rok_ext : forall segs E (m m' : word -> option byte) r,
  (forall x, m' x = m x) -> region_ok segs E m r -> region_ok segs E m' r.
Proof.
intros segs E m m' r HM HR. unfold region_ok in *. cbv zeta in *.
destruct HR as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (writable_at_grows segs m m'); [intros x Hx; rewrite HM; exact Hx | exact (H3 o Ho)].
- refine (Forall_impl _ _ H4). intros c Hc j Hj. destruct (Hc j Hj) as (b & Hb & Hm).
  exists b. split; [exact Hb|]. unfold mbyte in *. rewrite HM. exact Hm.
Qed.

Lemma y_frame_ext : forall cx h shf (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_frame cx h shf W m -> d_frame cx h shf W m'.
Proof.
intros cx h shf W m m' HM (E & HE & HR & HFL & V1 & V2 & V3 & V4 & V5 & V6 & V7).
pose proof (y_mbyte_ext SEGS (w_H W) m m' HM) as MB.
assert (VM : forall a q v, val_mem SEGS (rd W m) a q v -> val_mem SEGS (rd W m') a q v)
  by (intros a q v Hv j Hj; rewrite MB; exact (Hv j Hj)).
exists E. split; [exact HE|]. split.
- refine (Forall_impl _ _ HR). intros r Hr. exact (y_rok_ext SEGS E _ _ r (y_mrestrict_ext (w_H W) m m' HM) Hr).
- split.
  + rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m')); [exact HFL|].
    intros j _. apply y_aview_ext. exact HM.
  + exact (conj (VM _ _ _ V1) (conj (VM _ _ _ V2) (conj (VM _ _ _ V3) (conj (VM _ _ _ V4)
      (conj (VM _ _ _ V5) (conj (VM _ _ _ V6) (VM _ _ _ V7))))))).
Qed.

Lemma y_shadow_ext : forall cx shf (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> d_shadow cx shf W m -> d_shadow cx shf W m'.
Proof. intros cx shf W m m' HM Hs j Hj. rewrite (y_aview_ext SEGS (w_H W) m m' HM). exact (Hs j Hj). Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma y_dsh_cell_val : forall ly S (W : world SEGS) mem md p n x,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= x < p + n ->
  aview SEGS (w_H W) mem (y_dsh_cell_addr x) = Some (y_dsh_cell p n x).
Proof.
intros ly S W mem md p n x HAR Hin Hx.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & Hia & Hpres & Hn).
destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (Hbs & _).
unfold block_shadow in Hbs. destruct Hbs as (Hp8 & Hn0 & Hbytes).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [lia | reflexivity]).
rewrite Hrq in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp.
assert (Hsplit : x / 8 = p / 8 + (x - p) / 8)
  by (rewrite <- (y_div8_shift p (x - p) Hp8); f_equal; lia).
assert (Hidx : 0 <= (x - p) / 8 < (n + 7) / 8).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as Dn.
  pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
pose proof (Hbytes ((x - p) / 8) Hidx) as Hb.
unfold shadow_of_addr in Hb. unfold y_dsh_cell_addr, y_dsh_cell.
replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + p / 8 + (x - p) / 8) by lia.
exact Hb.
Qed.

Lemma y_dsh_cell_denot : forall E (a q : nat) (c x : Z),
  ew E a = w64 x -> 0 <= x -> 0 <= c -> 0 <= x + c < 2 ^ 64 -> ew E 32%nat = w64 SHADOW_OFF ->
  ew E q = w64 (y_dsh_cell_addr (x + c)) ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a c) (SLit 3)) (SOff 32 0)) = sv_denot E (SOff q 0).
Proof.
intros E a q c x Ha Hq Hc Hxc H32 Hqv. unfold w64 in Ha, H32, Hqv. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Ha, H32, Hqv, !Z.add_0_r.
rewrite (unsigned_lit_small x) by lia.
rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
assert (Hsr : 0 <= y_dsh_cell_addr (x + c) < 2 ^ 64) by (unfold y_dsh_cell_addr; apply y_shaddr_range; lia).
rewrite (unsigned_lit_small (y_dsh_cell_addr (x + c))) by lia.
unfold y_dsh_cell_addr in *.
rewrite (zcanon_id (x + c)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
f_equal. lia.
Qed.

Definition y_byte_region (q v : nat) (o : Z) : YP09.region :=
  YP09.mkRegion (Some q) o (o + 1) 0 0 [YP09.mkChunk o (CVal 1 (SOff v 0))].

Lemma y_byte_region_wf : forall q v o, region_wf (y_byte_region q v o) = true.
Proof.
intros q v o. unfold region_wf, y_byte_region, chunk_inside.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off YP09.c_val YP09.c_len cv_len
     Z.of_N forallb].
replace (o <=? o + 1) with true by (symmetry; apply Z.leb_le; lia).
replace (o + 1 <=? o + 1) with true by (symmetry; apply Z.leb_le; lia).
repeat (first [ apply Bool.andb_true_iff; split
              | apply Bool.orb_true_iff; left
              | apply Z.leb_le; lia
              | reflexivity ]).
Qed.

Lemma y_byte_region_ok : forall E (W : world SEGS) mem (q v : nat) (y s o : Z),
  ew E q = w64 y -> 0 <= y -> 0 <= o -> y + o + 1 <= 2 ^ 64 -> ew E v = w64 s -> 0 <= s < 256 ->
  aview SEGS (w_H W) mem (y + o) = Some s ->
  region_ok SEGS E (mrestrict (w_H W) mem) (y_byte_region q v o).
Proof.
intros E W mem q v y s o Hq Hy Ho Hy1 Hv Hs Hav. unfold w64 in Hq, Hv.
unfold region_ok, y_byte_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hq, (unsigned_lit_small y) by lia.
split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len Z.of_N] in *.
assert (Hi0 : i = 0) by lia. subst i.
assert (Hdv : sv_denot E (SOff v 0) = Z_to_bv 64 s).
{ rewrite denot_lit_U, U_SOff, Hv, Z.add_0_r, (unsigned_lit_small s) by lia.
  f_equal. apply zcanon_id. unfold M64. lia. }
unfold cbyte. cbn [YP09.c_val]. rewrite Hdv.
unfold byte_of_word. rewrite (unsigned_lit_small s) by lia. cbn [Z.mul]. rewrite Z.shiftr_0_r.
unfold aview in Hav. destruct (mbyte SEGS (mrestrict (w_H W) mem) (y + o)) as [b|] eqn:Hb; [|discriminate].
cbn [option_map] in Hav. injection Hav as Hav.
exists (Z_to_bv 8 s). split; [reflexivity|].
rewrite !Z.add_0_r, Hb. f_equal. rewrite <- Hav. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma y_byte_seat : forall (fq : YK11.FPState) (E : env) (ss : sstate) (ms : machine_state) (W : world SEGS)
  (rdst : bv 5) (q v : nat) (y s o : Z),
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) ->
  bv_eqb rdst 0 = false ->
  sv_denot E (SOff q o) = getr (ms_regs ms) rdst ->
  ew E q = w64 y -> 0 <= y -> 0 <= o -> y + o + 1 <= 2 ^ 64 -> ew E v = w64 s -> 0 <= s < 256 ->
  aview SEGS (w_H W) (ms_mem ms) (y + o) = Some s ->
  all_disjoint E (y_byte_region q v o) (ss_mem ss) ->
  st_ok_pi (fx := fq) SEGS VAL E
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) rdst (SOff q o)) (y_byte_region q v o :: ss_mem ss)
          (ss_resv ss) (ss_facts ss))
    (restrict (w_H W) ms).
Proof.
intros fq E ss ms W rdst q v y s o HS Hrd Hden Hq Hy Ho Hy1 Hv Hs Hav Hdis.
pose proof (ast_ok_pi_set_reg_fp (PI := PI) E ss (restrict (w_H W) ms) rdst (SOff q o) HS Hrd Hden) as HS1.
pose proof (st_ok_pi_add_region (L := lib_both3_0_listing) (PI := PI) E
  (mkSS (ss_pc ss) (sr_set (ss_regs ss) rdst (SOff q o)) (ss_mem ss) (ss_resv ss) (ss_facts ss))
  (restrict (w_H W) ms) (y_byte_region q v o) HS1 (y_byte_region_wf q v o)) as HS2.
cbn [ms_mem restrict] in HS2.
apply HS2; [exact (y_byte_region_ok E W (ms_mem ms) q v y s o Hq Hy Ho Hy1 Hv Hs Hav) | exact Hdis].
Qed.

Section g.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.


Lemma y_awr : forall (E : env) (cx : dcx) (ly3 : alayout) (rs : smem) (FP bl0 blc : list (Z * Z)),
  yr_wins_ok rs = true ->
  bv_unsigned (ew E 60) = d_A cx -> bv_unsigned (ew E 516) = d_FB cx ->
  bv_unsigned (ew E 529) = shadow_addr (d_FB cx) ->
  d_A cx + 472 <= d_S cx -> d_S cx - LLVMF_STK <= d_A cx ->
  frame_addr ly3 DFRAME_CLASS (c_fpos cx) = d_FB cx ->
  awr_ok E rs LLVMF_STK (d_S cx) FP bl0 blc ly3 [(DFRAME_CLASS, c_fpos cx)].
Proof.
intros E cx ly3 rs FP bl0 blc Hw E60 E516 E529 HA1 HA2 EFB.
induction rs as [|r rs IH]; [apply awr_ok_nil|].
cbn [forallb] in Hw. apply andb_prop in Hw as [Hr Hrs].
specialize (IH Hrs).
unfold yr_win_ok in Hr. apply Bool.orb_true_elim in Hr as [Hro | Hb].
- apply awr_ok_cons_ro; [apply Z.leb_le; exact Hro | exact IH].
- destruct (YP09.r_base r) as [bn|] eqn:Eb; [|discriminate Hb].
  destruct bn as [|b1]; [discriminate Hb|].
  do 59 (destruct b1 as [|b1]; [discriminate Hb|]).
  destruct b1 as [|b1].
  { apply andb_prop in Hb as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    apply (awr_ok_cons_stack_off E r rs LLVMF_STK (d_S cx) FP bl0 blc ly3 _ 60%nat (d_A cx - d_S cx));
    [exact Eb | rewrite E60; lia | lia | lia | exact IH]. }
  do 455 (destruct b1 as [|b1]; [discriminate Hb|]).
  destruct b1 as [|b1].
  { apply andb_prop in Hb as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    apply (awr_ok_cons_gen E r rs LLVMF_STK (d_S cx) FP bl0 blc ly3 _ 516%nat (d_FB cx));
    [exact Eb | exact E516 | | exact IH].
    intros a Ha. right. right. right. exists DFRAME_CLASS, (c_fpos cx).
    split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  do 12 (destruct b1 as [|b1]; [discriminate Hb|]).
  destruct b1 as [|b1]; [|discriminate Hb].
  apply andb_prop in Hb as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  apply (awr_ok_cons_gen E r rs LLVMF_STK (d_S cx) FP bl0 blc ly3 _ 529%nat (shadow_addr (d_FB cx)));
  [exact Eb | exact E529 | | exact IH].
  intros a Ha. right. right. right. exists DFRAME_CLASS, (c_fpos cx).
  split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EFB.
  change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
Qed.

Lemma y_geom : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_S cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= d_S cx /\ d_S cx <= 2 ^ 47 /\
  4096 <= d_FB cx /\ d_FB cx + 4096 <= alloc_ceiling /\ in_app (d_FB cx) 4096 /\
  off_img (d_FB cx) 4096 /\ d_FB cx mod 32 = 0 /\
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> apresent (w_H W3) mem3 a) /\
  (forall j, 0 <= j < 512 -> apresent (w_H W3) mem3 (shadow_addr (d_FB cx) + j)) /\
  (forall a, d_S cx - LLVMF_STK <= a < d_S cx -> apresent (w_H W3) mem3 a) /\
  AR SEGS B ly3 S3 W3 mem3 md3 /\ In (DFRAME_CLASS, c_fpos cx) (frames S3) /\
  frame_addr ly3 DFRAME_CLASS (c_fpos cx) = d_FB cx /\
  flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx).
Proof.
intros cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
destruct HB as ((HPRE & _) & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
assert (Efl : flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
{ pose proof (Efa 0 0) as E00. unfold frame_addr in E00. unfold flag_addr. lia. }
destruct (frames_bounds _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (HF0 & HFc & HFia).
pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as HFo.
destruct (al_frames _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (Hal & _ & HFpres & HSpres).
rewrite Efa in HF0, HFc, HFia, HFo, Hal, HFpres, HSpres.
change (frame_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) with (d_FB cx) in *.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. change (4096 / 8) with 512 in HSpres.
change (spZ (c_regs cx)) with (d_S cx) in *.
split; [exact Hal16|]. split; [unfold LLVMF_STK in *; lia|]. split; [lia|].
split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|]. split; [exact Hal|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
split; [intros j Hj; exact (proj1 (HSpres j Hj))|].
split; [intros a Ha; apply HJpres; exact Ha|].
split; [exact HAR3|]. split; [exact Hfin|]. split; [rewrite Efa; reflexivity|]. exact Efl.
Qed.
Lemma d_call_chain : forall (pc0 off : Z) (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k
  (regs : bvmap 5 word) (V0 : Z),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  pc0 < BASE -> 0 <= off -> 4096 <= BASE + off ->
  In [pc0; BASE + off] (as_universe B) -> In [pc0; BASE + off; RA_LLVMF] (as_universe B) ->
  spZ regs = d_A cx -> s0Z regs = d_S cx -> d_A cx + 16 <= d_S cx -> raZ regs = BASE + off ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 8) = Some RA_LLVMF ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 16) = Some V0 ->
  (bad_next (d_S cx) (ly_top ly3) V0 = true \/ fpchain (rdword (aview SEGS (w_H W3) mem3)) V0 (ly_top ly3) []) ->
  exists ch, chain_pre ly3 (aview SEGS (w_H W3) mem3) regs ch /\
    In (call_trace0 pc0 regs ch) (as_universe B).
Proof.
intros pc0 off cx ly3 S3 W3 mem3 md3 k regs V0 Hctx Hpc0 Hoff Hra4 HU2 HU3 Hsp Hs0 HAS Hra Hsave HV0 HCH.
assert (Hrane : (BASE + off =? pc0) = false) by (apply Z.eqb_neq; lia).
assert (Htr0 : forall l, (length l <= 1)%nat -> In (pc0 :: [BASE + off] ++ l) (as_universe B) ->
          In (firstn kUnwindMax (pc0 :: (if BASE + off =? pc0 then [] else [BASE + off]) ++ l)) (as_universe B)).
{ intros l Hlen Hl. rewrite Hrane. cbn [app] in *.
  destruct l as [|x [|y l']]; cbn [length] in Hlen; try lia;
  change kUnwindMax with 30%nat; cbn [firstn]; exact Hl. }
assert (Htr1 : In (firstn kUnwindMax (pc0 :: (if BASE + off =? pc0 then [] else [BASE + off]) ++
          (if RA_LLVMF =? pc0 then [] else [RA_LLVMF]) ++ [])) (as_universe B)).
{ destruct (Z.eqb_spec RA_LLVMF pc0) as [He|Hne].
  - apply Htr0; [cbn [length app]; lia|]. cbn [app]. exact HU2.
  - apply Htr0; [cbn [length app]; lia|]. cbn [app]. exact HU3. }
unfold chain_pre, frame0_ok, call_trace0, unwind_of_chain.
rewrite Hra.
destruct (spZ regs + 16 <? ly_top ly3) eqn:Hf0.
- destruct (bad_next (spZ regs) (ly_top ly3) (s0Z regs)) eqn:Hbn.
  + exists []. split; [split; [lia | reflexivity]|].
    cbn [flat_map app]. apply Htr0; [cbn [length]; lia|]. cbn [app]. exact HU2.
  + exists [(s0Z regs, RA_LLVMF, V0)]. split.
    { unfold bad_next in Hbn.
      apply Bool.orb_false_elim in Hbn as [Hbn1 Hbn3].
      apply Bool.orb_false_elim in Hbn1 as [Hbn1 Hbn2].
      apply Z.leb_gt in Hbn1. apply Z.leb_gt in Hbn2.
      apply Bool.negb_false_iff, Z.eqb_eq in Hbn3.
      split; [lia|]. split; [lia|].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hbn3|].
      rewrite <- Hs0 in Hsave, HV0. split; [exact Hsave|]. split; [exact HV0|].
      split; [unfold RA_LLVMF; lia|].
      rewrite Hs0. destruct HCH as [Hb|Hf].
      - rewrite Hb. reflexivity.
      - destruct (bad_next (d_S cx) (ly_top ly3) V0); [reflexivity | exact Hf]. }
    { cbn [flat_map app]. exact Htr1. }
- exists []. split; [split; [lia | reflexivity]|].
  cbn [flat_map app]. apply Htr0; [cbn [length]; lia|]. cbn [app]. exact HU2.
Qed.

Definition JOIN_OFF : Z := 0xd50.
Definition MID_OFF : Z := 0xdb8.

Definition yr_join (cx : dcx) (h i n now op : Z) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx JOIN_OFF (EV_HEAD i) (ACC_HEAD MT i)
    (fun regs ly3 S3 W3 mem3 md3 =>
       0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 <> 3 /\
       d_rL B cx regs /\ getr regs 22 = w64 1 /\ getr regs 21 = w64 i /\ getr regs 26 = w64 now /\
       getr regs 23 = w64 (op mod 4) /\
       getr regs 11 = w64 (rdb (rest_of (c_pl cx) n) 0) /\
       getr regs 12 = w64 (256 * rdb (rest_of (c_pl cx) n) 1) /\
       getr regs 24 = w64 (rec_rem n) /\ getr regs 25 = w64 (d_cur cx (rec_rem n)) /\
       d_sp0 cx i now W3 mem3 /\ d_spOP cx op W3 mem3 /\
       d_body B cx h n [] dsh_loop ly3 S3 W3 mem3).

Definition yr_mid (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx MID_OFF h i n now (dxb fr len) dsh_rec
    (fun regs => getr regs 22 = w64 1 /\ getr regs 21 = w64 i /\ getr regs 26 = w64 now /\
                 getr regs 23 = w64 (op mod 4) /\ getr regs 12 = w64 len /\
                 getr regs 24 = w64 nb /\ getr regs 25 = w64 (d_cur cx nb))
    (fun W m => 0 <= op < 256 /\ op mod 4 <> 3 /\ 4096 <= fr /\ d_frm cx nb fr len W m /\
                d_spREC cx nb fr len W m /\ d_spOP cx op W m /\
                len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7)).

Definition C2_OFF : Z := 0xd74.

Definition yr_c2 (cx : dcx) (h i n now op fr len : Z) : world SEGS -> config -> Prop :=
  d_at B MT XM_LIB RLO RHI tfib_K cx C2_OFF (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX)
    (fun regs ly3 S3 W3 mem3 md3 =>
       0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 <> 3 /\
       4096 <= fr /\ 0 <= len <= REC_MAX /\ len <= rec_rem n /\
       rec_rem n <= c_n cx /\ rec_rem n <= Z.max 0 (c_n cx - 7) /\
       d_rL B cx regs /\ getr regs 22 = w64 1 /\ getr regs 21 = w64 i /\ getr regs 26 = w64 now /\
       getr regs 23 = w64 (op mod 4) /\ getr regs 10 = w64 fr /\
       getr regs 24 = w64 (rec_rem n) /\ getr regs 25 = w64 (d_cur cx (rec_rem n)) /\
       val_mem SEGS (rd W3 mem3) (d_A cx + 408) 8 len /\
       d_sp0 cx i now W3 mem3 /\ d_spOP cx op W3 mem3 /\
       d_body B cx h n [(fr, len)] dsh_loop ly3 S3 W3 mem3).

Definition yr_s2a_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  yr_join cx h i n now op W c ->
  SRr SEGS W c (fun W' c' => exists fr,
    yr_c2 cx h i n now op fr (rec_len (rest_of (c_pl cx) n) n) W' c').

Definition yr_s2b_stmt : Prop :=
  forall (cx : dcx) (h i n now op fr len : Z) (W : world SEGS) (c : config),
  yr_c2 cx h i n now op fr len W c ->
  SRr SEGS W c (yr_mid cx h i n now op (rec_rem n) fr len).

Definition yr_head_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  rec_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W c ->
  SRr SEGS W c (yr_join cx h i n now op).

Definition yr_arm_stmt : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (W : world SEGS) (c : config),
  yr_mid cx h i n now op nb fr len W c ->
  SRr SEGS W c (fun W' c' =>
    (op mod 4 <> 2 /\ cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W' c') \/
    (op mod 4 = 2 /\ hobs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W' c')).

Definition yr_body_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config),
  yr_join cx h i n now op W c ->
  SRr SEGS W c (fun W' c' => exists fr,
    yr_mid cx h i n now op (rec_rem n) fr (rec_len (rest_of (c_pl cx) n) n) W' c').

Lemma y_mono : forall cx pc kmax accmax
  (P P' : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop) W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P W c ->
  (forall regs ly S W' mem md, P regs ly S W' mem md -> P' regs ly S W' mem md) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P' W c.
Proof.
intros cx pc kmax accmax P P' W c
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFQ & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HP) HPP.
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]). apply HPP. exact HP.
Qed.

Lemma y_body_ext : d_body_rt_stmt B -> forall cx h n xb shf ly3 S3 (W3 : world SEGS) m m',
  (forall x, m' x = m x) -> d_body B cx h n xb shf ly3 S3 W3 m -> d_body B cx h n xb shf ly3 S3 W3 m'.
Proof.
intros BRT cx h n xb shf ly3 S3 W3 m m' HM HBD.
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & _ & _ & _ & _).
apply (BRT cx h n n xb shf shf ly3 S3 W3 m m' (d_S cx) (d_S cx) (fun _ => False) HBD).
- unfold LLVMF_STK. lia.
- lia.
- intros a Ha. destruct Ha.
- intros a _ _. apply y_aview_ext. exact HM.
- intros a _ (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite HM. exact Hb.
- exact (y_frame_ext cx h shf W3 m m' HM HFRM).
- exact (y_shadow_ext cx shf W3 m m' HM HSHD).
- pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & _ & (Hn & _) & _). lia.
Qed.

End g.
End h.
End f.
End d.

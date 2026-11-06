(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1285 of its 1379 lines of code are new or changed and 684 lines of the source are left out. *)
(* fuzz_preset, the #102 IMAGE-GENERIC GLUE of the tx_string walk (fuzz_preset.c merged :408-430, body instruction-equal
   to the base's :374-396), shared by image A' and image B'.
   OWNER: h-rw-pre-5 (lane TxStrBp), branch cold/h-rw-pre-5-r102-txstrB; announced blob: to be named when it lands
   (pins102). THE SHARED HOME (K0 / S10's owner h-hpreset-7, 2026-10-29 19:36Z): S10's own #102 move cites this file and
   BTxValueB's lib/A/Prog/Tx102Glue.v (the text state), not the reverse. It is the #102 form of S10's old-pin
   lib/A/Prog/S10TxStrGlue.v (blob 472f01fdb977, cold/h-hpreset-7-walk-S10 b2764049d6cd), with S10's lemma names (the
   ts_ family) wherever a statement keeps its shape; it Requires NO S10 file: the text state is Tx102Glue's tx_state /
   tx_pos, and S10's image- and text-agnostic segment environment (S10Env.v d8ca1dd59ead) is inlined below.
   WHY A RE-WALK, NOT A RE-FIT: the #102 tx texts change the state the walk carries, not only its spelling: prhtx_rec
   takes f (the record's `int failed` at t + 24), prh_ledger takes most / own, prhtx_fp is 28 bytes, and prhtx_out has
   THREE outcomes (a refused put RETURNS with failed = 1, and every later put takes the FAILED arm), where the old text
   had the fabortW abort arm that ended the walk. So every call site continues on every outcome, and the live state
   carries the buffer, failed, own and the appended prefix.
   THE BATCH KIT, NOW THE RE-HIDE MOVE'S TEXTS (PRH_FnTx.v 7cf918708def; history: first fitted as a prep over the
   batch kit's cdde0ed15730, then on the kit's cut 7cdbb61b5fa0 at PRH_FnTx.v 88468bf162d8, superseding bff94397b16a;
   every lemma name kept, the lead's approval 2026-10-30). Against the texts now: (1) DW gone: Context TXPUT is
   ttx_put_specX .. CTX0 (:414); (2) ts_pre: prh_univ_closure B CTX0 (:671) and the guarded room `f0 = 0 -> wild_room
   (as_universe B) [] k (st_depot S)` and consumer window `f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i k`, k the
   events of TS_ks (:677 / :682); (3) QT: DEAD-TXSTRING `f0 = 0 -> f1 = 0` (:706); (4) QF: fpostWbm budgeted at
   wbudget_if f0 [] k, the text's fpostWbmR at RCF (:696; PRH_Base.v:1647-1650), under SRRCF (:695); (5) ts_side
   carries DEAD so far and the depot's wild growth within the budget; ts_liveR's journal starts at the REBASED entry
   set_depot (st_depot Sc) S; (6) ts_put_call takes `(length rp_os <= 4)%nat` (:422), concludes SRRCF, and unbases
   by ajournal_xw_unbase0R, calls s10_call_WbmR with the callee's room and window (Tx102Glue.v tx_room_window /
   tx_cons_window), folds by tx_state_fold_wR / tx_budget_fold; R twins ts_liveR, ts_live_runR/_sameR, ts_str_keep_wR.
   prhtx_trace is STATE-FREE in the batch (inU, no S): unchanged here (tx_state's trace is memory-only).
   SRC-CEIL RETIRED (on the cut 7cdbb61b5fa0, the internal file MIGRATION.md, section 4): the Context {K0_SRC_CEIL} is DELETED. The cut's
   src_rd states `p + len <= alloc_ceiling` (no `+ 8`), and ts_src_byte takes that bound from the string's own
   prhtx_bvis granule bound (PRH_FnTx.v :271), as BTxValue did; ts_src_byte loses that one implicit argument.
   THE PRE-CUT TEXTS: lib/A/PRH_FnTx.v a52a78336898 and lib/A/PRH_Base.v fdb45545469b of walkkit-next f97c8b2f046b
   (ttx_string_specX / ttx_put_specX: decff67d721f's word for word). What #102 changed, and what this file does:
   - the record has `int failed` at t + 24 (prhtx_rec's f; 28 bytes): the source of every put is disjoint from
     [t, t + 28);
   - NO ABORT ARM: tx_put's post is ONE fpostWm naming its outcome (DONE / FAILED AT ENTRY / REFUSED), and every arm
     RETURNS; tx_string's code does not test `failed`, so the walk continues after every call whatever the outcome.
     The live state therefore carries the buffer (b, cap), failed f, own and what was ACTUALLY appended (pre) next to
     the calls made so far (ks) and the text they would append (add): Tx102Glue's tx_state, and the position tx_pos.
     QF is ONE fpostWm at the record texts, ONE fpostWbm at the batch (above) (no fabortW disjunct);
   - the ledger carries most and own (prh_ledger's `most own`); the text's binders gain f0 / own / most;
   - the run premise is guarded by f0 = 0, and the post's position is the exact-or-frozen `exists j hist', ..`
     (tx_pos_post);
   - fpre ends in `frm_zero (fp_csr fx)` (FRM0-ENTRY): tx_string runs no float instruction, so tx_put's is the
     entry's (ts_pre carries it);
   - kept_img is PER-INSTANCE (pa_lo / pa_hi): the literals' route is Tx102Glue's s10_src_img, under its img_box /
     img_cf_box;
   - image bounds are PER-INSTANCE: img_shadow_vis_x over `@cf_img_lo ci` / `@cf_img_top ci` (h-mani-a8's rule
     18:56Z), pal_uar_img over the same bounds (never YImgTop's IMG_LO / IMG_TOP, never pa_box).
   Generic over `{L : ptable asym} {PA : PAImg L}`, the PrhImg `{PI}`, the CfImg `{ci}` and the sink head `{SK}`;
   CfParams is CfParams_preset (cf_head = 16). Every image-dependent number is a NAMED Context parameter: the seam
   offsets from the listing base (TS_PC, TS_A2_OFF, TS_A3_OFF, TS_LH_OFF, TS_G_OFF) and the three read-only literals
   (TS_STR25 = the quote, TS_STR26 = the backslash, TS_HEX = tx_string.hex; each image names its own .str.N). Every
   conclusion is `srealizes` through SRr' at RZ_cf (SRRCF, :518).
   PALib ONLY AT THE WHOLE-PROGRAM INSTANCES (owner ruling 2026-10-29 06:05Z): the glue takes `PALib (PI := PA) B`, whose
   pal_got_uar / pal_got_uar_disj say A_OBJ 1 is the GOT word of __asan_option_detect_stack_use_after_return; tx_string
   reads that word, so PALib stays; instantiate this file at PI_prog_A / PI_prog_B only.
   FAKE FRAME (frame_alloc_0, class 0, 64 bytes): F + 0 the magic, F + 8 the frame description (a pointer the listing
   computes; its bytes are never read here: the #102 DATA TRAP changed them, esc:382 -> esc:416), F + 16 the pc, esc[]
   at F + 32 (6 bytes), the flag pointer at F + 56; F's shadow bytes 0-3 = f1, 4 = f8, 5-7 = f3; byte 4 = 06 around
   each byte's pieces; all f5 at the release. The real frame: 160 bytes, s0 = the entry sp, saves at entry sp - 8 ..
   - 104, sp1 = (entry sp - 160) rounded down to 32, F stored at sp1 + 16, sp1 + 24 and sp1 + 48.
   Rule 24: proves no function (kind: glue).
   Numerals: 8 / 16 / 24 / 28 / 32 / 48 / 56 / 64 / 160 / 176 (LENGTH: frame and record layout), 2 ^ 31 / 2 ^ 44 /
   2 ^ 46 / 2 ^ 47 / 2 ^ 64 (DERIVED: image, shadow, stack and word bounds), 9 / 10 / 13 / 32 / 34 / 48 / 92 / 116 /
   117 (WORD: the bytes the body compares or stores), atom indices (DERIVED: the engine's numbering). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Tx102Glue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- THE SEGMENT ENVIRONMENT, inlined from S10's lib/A/Prog/S10Env.v (blob d8ca1dd59ead, identical in every S10
   copy; owner h-hpreset-7) so that this file depends on no S10 file (the lead's condition (1), 2026-10-29): image- and
   text-agnostic, no PRH_* text; S10's names kept (TE, te_*, ts_st_ok, ts_rok, ts_chunk, ts_keep, ts_vm_av, ...) ---- *)
(* ======================================================================================================== *)
(* ---- registers and the segment environment ---- *)
Lemma s10s_nth_all_regs : forall k, (k < 32)%nat -> nth k all_regs 0%bv = Z_to_bv 5 (Z.of_nat k).
Proof. intros k Hk. do 32 (destruct k as [|k]; [apply bv_eq; reflexivity|]). lia. Qed.
(* the atoms 32-63 hold the current registers *)
Definition cur_atoms : list sv := SLit 0 :: map (fun i => SOff (32 + i) 0) (seq 1 31).
Definition xr (r : nat) : nat := (32 + r)%nat.

(* `andi sp, sp, -32` on a 64-bit value *)
Lemma ts_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x / 32 * 32.
Proof.
intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
replace (2 ^ 64 - 32) with (Z.shiftl (Z.ones 59) 5) by reflexivity.
replace (x / 32 * 32) with (Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
rewrite !Z.shiftl_spec by lia.
destruct (Z_lt_le_dec i 5) as [Hl|Hl].
- rewrite (Z.testbit_neg_r (Z.ones 59) (i - 5)), (Z.testbit_neg_r (Z.shiftr x 5) (i - 5)) by lia. apply andb_false_r.
- rewrite Z.shiftr_spec by lia. replace (i - 5 + 5) with i by lia.
  destruct (Z_lt_le_dec i 64) as [H64|H64].
  + rewrite Z.ones_spec_low by lia. apply andb_true_r.
  + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
    symmetry. apply (Z.bits_above_log2 x i); [lia|]. destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
    apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.
Lemma ts_low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
  Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hl|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma ts_add0_word : forall w : word, alu64 ALU_ADD w (Z_to_bv 64 0) = w.
Proof. intros w. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
rewrite Z.add_0_r. unfold bv_wrap. apply Z.mod_small. exact (bv_unsigned_in_range 64 w). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PA).
#[local] Notation VAL := (@pa_val _ L PA).
#[local] Notation BASE := (@pa_val _ L PA A_TEXT).

(* the segment environment: entry registers, current registers, extras *)
Definition TE (regs0 regsc : bvmap 5 word) (more : list word) : env :=
  @Eimg _ L PA (Ereg regs0 (map (getr regsc) all_regs ++ more)).

Lemma te_env : forall regs0 regsc more, img_env VAL A_LIM (TE regs0 regsc more).
Proof. intros. unfold TE. apply Eimg_env. Qed.
Lemma te_entry : forall regs0 regsc more (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew (TE regs0 regsc more) n = getr regs0 r.
Proof.
intros regs0 regsc more r n Hn. pose proof (u5_range r). unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hn.
Qed.
Lemma te_cur : forall regs0 regsc more (r : bv 5) k, Z.of_nat k = bv_unsigned r -> ew (TE regs0 regsc more) (32 + k) = getr regsc r.
Proof.
intros regs0 regsc more r k Hk. pose proof (u5_range r). unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsc 0%bv)) by (rewrite length_map; cbn; lia).
rewrite map_nth. rewrite s10s_nth_all_regs by lia. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. rewrite Hk. apply Z.mod_small. lia.
Qed.
Lemma te_more : forall regs0 regsc more j, ew (TE regs0 regsc more) (64 + j) = nth j more (Z_to_bv 64 0) \/ (240 <= 64 + j)%nat.
Proof.
intros regs0 regsc more j. destruct (Nat.lt_ge_cases (64 + j) 240) as [H|H]; [left|right; exact H].
unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia). replace (64 + j)%nat with (32 + (32 + j))%nat by lia.
rewrite ew_Ereg_extra. rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map. cbn [length all_regs].
f_equal. lia.
Qed.
Lemma te_more_lt : forall regs0 regsc more j, (64 + j < 240)%nat -> ew (TE regs0 regsc more) (64 + j) = nth j more (Z_to_bv 64 0).
Proof. intros regs0 regsc more j Hj. destruct (te_more regs0 regsc more j) as [H|H]; [exact H | lia]. Qed.
Lemma te_img : forall regs0 regsc more n, (A_TEXT <= n < A_LIM)%nat -> ew (TE regs0 regsc more) n = Z_to_bv 64 (VAL n).
Proof. intros regs0 regsc more n Hn. unfold TE. apply Eimg_img. exact Hn. Qed.
Lemma te_obj : forall regs0 regsc more n kk, (A_TEXT <= n < A_LIM)%nat ->
  sv_denot (TE regs0 regsc more) (SOff n kk) = Z_to_bv 64 (VAL n + kk).
Proof.
intros regs0 regsc more n kk Hn. cbn [sv_denot]. rewrite te_img by exact Hn.
pose proof (@pa_val_range _ _ PA n) as R. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma cur_atoms_nth : forall k, (1 <= k < 32)%nat -> nth k cur_atoms (SLit 0) = SOff (32 + k) 0.
Proof.
intros k Hk. destruct k as [|k']; [lia|]. unfold cur_atoms. cbn [nth].
pose proof (map_nth (fun i : nat => SOff (32 + i) 0) (seq 1 31) 0%nat k') as M. cbv beta in M.
rewrite (nth_indep _ (SLit 0) (SOff (32 + 0) 0)) by (rewrite length_map, length_seq; lia).
rewrite M, seq_nth by lia. first [reflexivity | f_equal; lia].
Qed.
Lemma te_regs_ok : forall regs0 regsc more, regs_ok (TE regs0 regsc more) cur_atoms regsc.
Proof.
intros regs0 regsc more r. unfold sr_get. pose proof (u5_range r) as Hr.
destruct (bv_eqb r 0) eqn:Hz.
- apply bv_eqb_eq in Hz. subst r. rewrite getr_zero. reflexivity.
- assert (Hne : bv_unsigned r <> 0).
  { intros H0. assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in Hz. discriminate. }
  unfold ridx. rewrite cur_atoms_nth by lia. cbn [sv_denot]. rewrite Z.add_0_r.
  rewrite (te_cur regs0 regsc more r (Z.to_nat (bv_unsigned r))) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- building a segment's symbolic state from concrete facts ---- *)
Lemma ts_st_ok : forall regs0 regsc more pc sr rs G (Wc : world SEGS) memc,
  regs_ok (TE regs0 regsc more) sr regsc -> regions_wf rs = true ->
  Forall (YP09.region_ok SEGS (TE regs0 regsc more) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (TE regs0 regsc more) rs -> facts_ok (TE regs0 regsc more) G ->
  st_ok_pi SEGS VAL (TE regs0 regsc more) (mkSS pc sr rs None G)
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof. intros. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; assumption. Qed.

Lemma ts_bv_some : forall E n, base_val E (Some n) = bv_unsigned (ew E n).
Proof. reflexivity. Qed.

Lemma ts_rok : forall E m n base lo hi wlo whi cs, bv_unsigned (ew E n) = base -> 0 <= base + lo -> base + hi <= 2 ^ 64 ->
  (forall o, wlo <= o < whi -> YP09.writable_at SEGS m (base + o)) -> Forall (YP09.chunk_ok SEGS E m base) cs ->
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E m n base lo hi wlo whi cs Hb H1 H2 H3 H4. unfold YP09.region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb. auto.
Qed.

Lemma ts_chunk : forall E m base off (n : N) e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) ->
  (Z.of_N n <= 8) -> val_mem SEGS m (base + off) (N.to_nat n) v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n e)).
Proof. intros. eapply chunk_ok_val; eassumption. Qed.

Lemma ts_aview_range : forall H mem a v, aview SEGS H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.
Lemma ts_rdword_range : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply ts_aview_range in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.

(* reading a region of a run's final state back as concrete bytes *)
Lemma ts_region_nth : forall E ss ms i r, st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  YP09.region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma ts_region_nth_c : forall E ss ms i r, st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r ->
  YP09.region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma ts_field : forall E m n b cs lo hi wlo whi od (w : N) e,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) (U E e mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as H. cbn [YP09.r_base base_val] in H. rewrite Hn in H.
intros k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val c_len cv_len] in H.
pose proof (N_nat_Z w) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (bb & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold YP09.byte_of_word in Hb1.
injection Hb1 as <-. rewrite Hb2. f_equal. unfold U.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
set (u := bv_unsigned (sv_denot E e)) in *.
assert (Hm : 0 <= u mod 2 ^ (8 * Z.of_N w) < 2 ^ (8 * Z.of_nat (N.to_nat w))).
{ rewrite Hnn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply ts_low_byte_mod; [lia | exact Hk].
Qed.
Lemma ts_U0 : forall E n, U E (SOff n 0) = bv_unsigned (ew E n).
Proof.
intros E n. rewrite U_SOff, Z.add_0_r. apply YP0m.zcanon_small.
pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Lemma ts_U_atom_mod : forall E n, U E (SOff n 0) mod 2 ^ 64 = bv_unsigned (ew E n).
Proof.
intros E n. rewrite U_SOff, Z.add_0_r. pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H.
rewrite zcanon_id by (unfold M64; lia). apply Z.mod_small. lia.
Qed.

(* a byte a value is read from is present *)
Lemma ts_vm_present : forall (H : word -> bool) m a n v, val_mem SEGS (mrestrict H m) a n v ->
  forall j, (j < n)%nat -> aview SEGS H m (a + Z.of_nat j) <> None.
Proof. intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). discriminate. Qed.
(* a word read through readers that agree on its 8 bytes *)
Lemma ts_rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* bytes a run did not write *)
Lemma ts_keep : forall (Wx : world SEGS) E rs mA mB (P : Z -> Prop),
  frame_of E rs (mrestrict (w_H Wx) mA) (mrestrict (w_H Wx) mB) ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a.
Proof.
intros Wx E rs mA mB P HF HP a Ha Hn. unfold aview. f_equal. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros H. exact (Hn (HP a H)).
Qed.
Lemma ts_val_mem_rd32 : forall (H : word -> bool) m a v, rd32 (aview SEGS H m) a v -> val_mem SEGS (mrestrict H m) a 4 v.
Proof.
intros H m a v Hr kk Hk. pose proof (Hr kk Hk) as Hb. unfold aview in Hb.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat kk)) as [b|] eqn:Em; [|discriminate].
cbn [option_map] in Hb. injection Hb as Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. transitivity (bv_wrap 8 (bv_unsigned b)).
- unfold bv_wrap. rewrite Z.mod_small; [reflexivity | exact (bv_unsigned_in_range 8 b)].
- f_equal. exact Hb.
Qed.
(* bytes kept in the reader's view are kept in the value view *)
Lemma ts_vm_av : forall (H H' : word -> bool) m m' a n v,
  (forall j, (j < n)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hag HV j Hj. rewrite (mbyte_of_aview SEGS H H' m m' _ (Hag j Hj)). exact (HV j Hj).
Qed.
Lemma ts_garr_av : forall (H H' : word -> bool) m m' a l,
  (forall j, (j < length l)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hag HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
apply (ts_vm_av H H' m m' _ 1 _); [|exact V].
intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (Hag j Hj).
Qed.
(* a register the segment did not write: its final value is the segment's start value *)
Lemma ts_reg_kept : forall regs0 regsc more ss (H : word -> bool) ms (r r' : bv 5),
  st_ok_pi SEGS VAL (TE regs0 regsc more) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (32 + Z.to_nat (bv_unsigned r')) 0 -> getr (ms_regs ms) r = getr regsc r'.
Proof.
intros regs0 regsc more ss H ms r r' HS Hr. rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, (te_cur regs0 regsc more r' (Z.to_nat (bv_unsigned r'))) by (pose proof (u5_range r'); lia).
apply Z_to_bv_bv_unsigned.
Qed.
Lemma ts_reg_kept_c : forall regs0 regsc more ss (H : word -> bool) ms (r r' : bv 5),
  st_ok SEGS (TE regs0 regsc more) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (32 + Z.to_nat (bv_unsigned r')) 0 -> getr (ms_regs ms) r = getr regsc r'.
Proof.
intros regs0 regsc more ss H ms r r' HS Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, (te_cur regs0 regsc more r' (Z.to_nat (bv_unsigned r'))) by (pose proof (u5_range r'); lia).
apply Z_to_bv_bv_unsigned.
Qed.
(* the frame's shadow pointer `(F >> 3) + shadow base` (A 0x84f24 / 0x84f4c) as one atom *)
Lemma ts_alias_shadow : forall E nF nB nS F, bv_unsigned (ew E nF) = F -> bv_unsigned (ew E nB) = SHADOW_OFF ->
  bv_unsigned (ew E nS) = shadow_addr F -> 0 <= F < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nF 0) (SLit 3)) (SOff nB 0)) = sv_denot E (SOff nS 0).
Proof.
intros E nF nB nS F HF HB HS HFr. apply U_inj. rewrite !U_SAlu, !U_SOff, U_SLit, HF, HB, HS.
unfold zcanon, M64, zalu_raw, shadow_addr, SHADOW_OFF.
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= F / 8 < 2 ^ 44) by lia. rewrite !Z.add_0_r. rewrite !Z.mod_small; lia.
Qed.
(* one byte: its value in the view and in val_mem *)
Lemma ts_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_small; lia.
Qed.
Lemma ts_aview_of_vm1 : forall (H : word -> bool) m a v, val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 ->
  aview SEGS H m a = Some v.
Proof.
intros H m a v HV Hv. pose proof (HV 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal. rewrite ts_le_byte1 by exact Hv.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma ts_vm1_of_aview : forall (H : word -> bool) m a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Ha k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Ha. destruct (mbyte SEGS (mrestrict H m) a) as [bb|] eqn:Em; [|discriminate].
cbn [option_map] in Ha. injection Ha as <-.
pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite ts_le_byte1 by exact Hr. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* a byte register differs from each listed value: the conditions a segment starts with *)
Lemma ts_conds_ne : forall E n cb nes, bv_unsigned (ew E n) = cb ->
  Forall (fun v => cb <> v /\ 0 <= v < 2 ^ 64) nes ->
  conds_ok E (map (fun v => mkAC BC_NE (SOff n 0) (SLit v)) nes).
Proof.
intros E n cb nes Hn H. induction H as [|v nes [Hv Hr] _ IH]; [exact I|].
cbn [map conds_ok]. split; [|exact IH].
unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, ts_U0, U_SLit, Hn.
rewrite YP0m.zcanon_small by lia. apply negb_true_iff, Z.eqb_neq. exact Hv.
Qed.
Lemma ts_conds_eq : forall E n cb eqs, bv_unsigned (ew E n) = cb ->
  Forall (fun v => cb = v /\ 0 <= v < 2 ^ 64) eqs ->
  conds_ok E (map (fun v => mkAC BC_EQ (SOff n 0) (SLit v)) eqs).
Proof.
intros E n cb eqs Hn H. induction H as [|v eqs [Hv Hr] _ IH]; [exact I|].
cbn [map conds_ok]. split; [|exact IH].
unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, ts_U0, U_SLit, Hn.
rewrite YP0m.zcanon_small by lia. apply Z.eqb_eq. exact Hv.
Qed.
Lemma ts_conds_app : forall E l1 l2, conds_ok E l1 -> conds_ok E l2 -> conds_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|c l1 IH]; [exact H2|]. destruct H1 as [Hc H1]. split; [exact Hc | exact (IH H1)]. Qed.
(* the value of an ALU result over known operands, as a word (the forms prreg leaves after a run) *)
Lemma ts_alu_w64 : forall op (w1 w2 : word) a b, bv_unsigned w1 = a -> bv_unsigned w2 = b ->
  alu64 op w1 w2 = w64 (zalu64 op a b).
Proof.
intros op w1 w2 a b H1 H2. rewrite <- (Z_to_bv_bv_unsigned _ w1), <- (Z_to_bv_bv_unsigned _ w2), H1, H2.
apply zalu64_sound.
Qed.
Lemma ts_zalu_and255 : forall c, 0 <= c < 256 -> zalu64 ALU_AND c 255 = c.
Proof.
intros c Hc. unfold zalu64. rewrite (YP0m.zcanon_small c), (YP0m.zcanon_small 255) by lia. unfold zalu_raw.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small by (change (2 ^ 8) with 256; lia).
apply YP0m.zcanon_small. lia.
Qed.
Lemma ts_zalu_and15 : forall c, 0 <= c < 256 -> zalu64 ALU_AND c 15 = c mod 16.
Proof.
intros c Hc. unfold zalu64. rewrite (YP0m.zcanon_small c), (YP0m.zcanon_small 15) by lia. unfold zalu_raw.
change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. apply YP0m.zcanon_small. lia.
Qed.
Lemma ts_zalu_srl4 : forall c, 0 <= c < 256 -> zalu64 ALU_SRL c 4 = c / 16.
Proof.
intros c Hc. unfold zalu64. rewrite (YP0m.zcanon_small c), (YP0m.zcanon_small 4) by lia. unfold zalu_raw.
change (Z.land 4 63) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply YP0m.zcanon_small. lia.
Qed.
Lemma ts_zalu_add : forall a d, 0 <= a -> 0 <= d -> a + d < 2 ^ 64 -> zalu64 ALU_ADD a d = a + d.
Proof.
intros a d Ha Hd Hs. unfold zalu64. rewrite (YP0m.zcanon_small a), (YP0m.zcanon_small d) by lia. unfold zalu_raw.
apply YP0m.zcanon_small. lia.
Qed.
(* bytes a run did not write, at the mbyte level (for garr8's frame lemmas) *)
Lemma ts_keep_mb : forall (H : word -> bool) E rs mA mB (P : Z -> Prop),
  frame_of E rs (mrestrict H mA) (mrestrict H mB) ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> mbyte SEGS (mrestrict H mB) a = mbyte SEGS (mrestrict H mA) a.
Proof.
intros H E rs mA mB P HF HP a Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros HW. exact (Hn (HP a HW)).
Qed.
End d.

(* closes `ew (TE r0 rc mo) n = X` for an entry register (n < 32), a current register (32 <= n < 64) or an extra *)
Ltac te_close :=
  lazymatch goal with |- ew (TE ?r0 ?rc ?mo) ?n = _ =>
    let nn := eval vm_compute in n in
    lazymatch eval vm_compute in (Nat.ltb nn 32) with
    | true => apply (te_entry r0 rc mo _ nn); reflexivity
    | false => lazymatch eval vm_compute in (Nat.ltb nn 64) with
      | true => let kk := eval vm_compute in (Nat.sub nn 32) in apply (te_cur r0 rc mo _ kk); reflexivity
      | false => let j := eval vm_compute in (Nat.sub nn 64) in rewrite (te_more_lt r0 rc mo j) by lia; reflexivity
      end
    end
  end.

(* a callee-saved register index, by computation *)
Ltac ts_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.
Lemma ts_ap : forall rg rg' (r : bv 5), aregs_preserved rg rg' -> acallee_saved (bv_unsigned r) -> getr rg' r = getr rg r.
Proof. intros rg rg' r HP Hr. pose proof (HP _ Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. Qed.

(* ======================================================================================================== *)
(* ---- the functional model, per byte class (S10TxState.v has the whole-string fact s10_strp_wstr) ---- *)
Lemma s10s_spcs_q : forall c, c = 34 \/ c = 92 -> TxModel.spcs c = [[92]; [c]].
Proof. intros c [-> | ->]; reflexivity. Qed.
Lemma s10s_spcs_p : forall c, 32 <= c -> c <> 34 -> c <> 92 -> TxModel.spcs c = [[c]].
Proof.
intros c H32 H34 H92. unfold TxModel.spcs, WriterSpec.special.
rewrite (proj2 (Z.eqb_neq c 34) H34), (proj2 (Z.eqb_neq c 92) H92), (proj2 (Z.ltb_ge c 32) H32). reflexivity.
Qed.
Lemma s10s_spcs_e : forall c, c < 32 -> TxModel.spcs c = [WriterSpec.esc c].
Proof.
intros c H. unfold TxModel.spcs, WriterSpec.special.
rewrite (proj2 (Z.eqb_neq c 34) ltac:(lia)), (proj2 (Z.eqb_neq c 92) ltac:(lia)), (proj2 (Z.ltb_lt c 32) H). reflexivity.
Qed.
Lemma s10s_esc_tnr : forall c, c = 9 \/ c = 10 \/ c = 13 ->
  WriterSpec.esc c = [92; if c =? 9 then 116 else if c =? 10 then 110 else 114].
Proof. intros c [-> | [-> | ->]]; reflexivity. Qed.
Lemma s10s_esc_u : forall c, 0 <= c < 32 -> c <> 9 -> c <> 10 -> c <> 13 ->
  WriterSpec.esc c = [92; 117; 48; 48; WriterSpec.hexd (c / 16); WriterSpec.hexd (c mod 16)].
Proof.
intros c Hc H9 H10 H13. unfold WriterSpec.esc.
rewrite (proj2 (Z.eqb_neq c 34) ltac:(lia)), (proj2 (Z.eqb_neq c 92) ltac:(lia)), (proj2 (Z.eqb_neq c 10) H10),
  (proj2 (Z.eqb_neq c 9) H9), (proj2 (Z.eqb_neq c 13) H13). reflexivity.
Qed.
(* the call sizes of tx_string: the opening quote, the byte pieces, the closing quote *)
Lemma s10s_ks : forall bs, TxModel.plen (TxModel.strp bs) = 1 :: TxModel.plen (concat (map TxModel.spcs bs)) ++ [1].
Proof. intros bs. unfold TxModel.strp, TxModel.plen. cbn [map]. rewrite map_app. reflexivity. Qed.

(* ======================================================================================================== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {PI : PrhImg} {RL : PrhRoomLive} {SK : YI16.sink_head} {L : ptable asym} {PA : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PA).
#[local] Notation VAL := (@pa_val _ L PA).
#[local] Notation SIGMA := (@pa_sigma _ L PA).
#[local] Notation BASE := (@pa_val _ L PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ L PA).
#[local] Notation RHI := (@pa_relro_hi _ L PA).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation STKS := (@STK_tx_string PI).
(* ---- the image's seams (offsets from the listing base, read from its neutral listing) and literals: NAMED ---- *)
Context {TS_PC TS_A2_OFF TS_A3_OFF TS_LH_OFF TS_G_OFF : Z}.
Context {TS_STR25 TS_STR26 TS_HEX : Z}.
(* the image's object atoms lie below 2 ^ 31, far below the stack (image fact: pa_hi is the instance's image top, by
   vm_compute; B' 0x601000) *)
Context {pa_hi_ok : @pa_hi _ L PA <= 2 ^ 31}.
(* the instance's CfImg bounds are a low range (image fact: B' CfImg_B 0x10000 / 0x601000, by vm_compute) *)
Context {cf_img_ok : 0 <= @cf_img_lo ci /\ @cf_img_top ci <= 2 ^ 31}.
(* tx_string's stack allowance covers its own 176 bytes and frame_alloc_0's 4096 (PrhImg fact: A 16640, by vm_compute) *)
Context {HSTK : 4096 + 176 <= STKS}.
(* tx_put's allowance plus tx_string's 176 bytes fit in tx_string's (PrhImg fact: A, by vm_compute) *)
Context {HSTKP : 0 <= @STK_tx_put PI /\ @STK_tx_put PI + 176 <= STKS}.

Section f.
Context {B : asyms}.
Context {ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop}.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
(* the same journal over a world relation R, and this unit's crossing relation with its step relation: a run that
   may re-hide a cf cell. AJ is AJR at wle. *)
#[local] Notation AJR R := (ajournal_xR (SK := SK) SEGS B PST ARx R).
#[local] Notation RCF := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation SRRCF := (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf).
(* ---- the allocator laws at the cf instance's head (25 fields, YCbqG.v:330-356; 16 at YCbqG 83da015952be) ---- *)
Context {LAWS : AR_laws_x SEGS B ARx cf_head}.
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B: PALib's fields, pal_got_uar and its disjointness included) *)
Context {PAL : PALib (L := L) (PI := PA) B}.
(* MARKED STAND-IN (owner a Theorem Labs lane / the core's PALib): the flag cell lies in the image, PER-INSTANCE over the CfImg bounds
   (B': 0xab700, 4 bytes of .bss, inside CfImg_B's [0x10000, 0x601000)) *)
Context {pal_uar_img : @cf_img_lo ci <= as_uar_cell B /\ as_uar_cell B + 4 <= @cf_img_top ci}.
(* image fact: alloc.c's statics lie in the image (A: S1ImgA.v pst_in_img_A) *)
Context {pst_img : forall a, Exists (in_zr a) PST -> in_img SEGS a}.
(* MARKED STAND-IN (owner a Theorem Labs lane, the image binding of B; another Theorem Labs lane's ruling 2026-10-29 ~05:45Z): alloc.c's statics are not
   the runtime's own statics and not errno, so a runtime call's image clause (acall_kept) keeps them *)
Context {pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)}.
(* image fact: alloc.c's statics are not read-only (A: S1ImgA.v pst_not_ro_A) *)
Context {pst_ro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a}.
(* the callee's text (K0Tx, PRH_FnTx.v 7cf918708def ttx_put_specX :414-474: SRr' RZ_cf over ONE fpostWbmR at RCF
   budgeted at wbudget_if f0 [] (its own events) (:454-455), naming the outcome, DEAD-TXPUT, the iface_room_pos
   position at entry, `(length rp_os <= 4)%nat` UNGUARDED (:422), the guarded room, consumer window and GROW event
   (entry premises guarded by f0 = 0)) at the caller's universe closure CTX0 (no DW: prh_univ_closure B CTX0, :418) *)
Context {CTX0 : list (list Z)}.
Context {TXPUT : ttx_put_specX (PI := PI) (PA := PA) B ARx SK CTX0}.
(* Tx102Glue's Section hypotheses (a Theorem Labs lane's, MARKED there): MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B);
   MARKED STAND-IN (owner a Theorem Labs lane, rule 18:56Z: img_shadow_vis_cf over the PER-INSTANCE CfImg bounds, restated over
   ARx; B' instance lib/AU/AImgShadowVisCfB.v tfib_img_shadow_vis_cf_B); the instance's kept_img bounds (closed facts
   of the instance, by vm_compute) *)
Context {zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B)}.
Context {img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> @cf_img_lo ci <= a < @cf_img_top ci ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None}.
Context {img_box : 4096 <= @pa_lo _ L PA /\ @pa_hi _ L PA <= kLowMemEnd}.
Context {img_cf_box : @cf_img_lo ci <= @pa_lo _ L PA /\ @pa_hi _ L PA <= @cf_img_top ci}.

Lemma ts_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

Section g.
(* ---- the entry: ttx_string_specX's binders ---- *)
Context {ly : alayout} {S : astate} {Hp : list Z} {W : world SEGS} {regs : bvmap 5 word} {mem : word -> option byte}
  {md : Model} {dw t s k b0 len0 cap0 f0 own0 : Z} {bs txt : list Z} {Lam : list (Z * Z)}
  {peak cnt fail ran most : Z}.
(* the model-run position the text takes at the entry (PRH_FnTx.v's rp_* binders; rp_hist is the entry lemma's) *)
Context {rp_sm : list Z -> Z * Z} {rp_x : list Z} {rp_os : list (option nat * option nat * option nat)} {rp_i : nat}
  {rp_H0 : list Z}.
(* the entry texts' premise `length rp_os <= 4` (the run has at most 4 calls: A17's prefix bound for the grow's hull at
   the position) is NOT a Section hypothesis here: as one, the section discharge captured it in 17 lemmas of this file
   and changed their arity. It is an explicit premise of ts_put_call, the only lemma that applies ttx_put. *)
#[local] Notation sp0 := (spZ regs).
Definition TS_add : list Z := WriterSpec.wstr bs.
Definition TS_ks : list Z := TxModel.plen (TxModel.strp bs).
Definition FP0 : list (Z * Z) := prhtx_fp t b0 cap0.

(* ---- segment A1: the prologue, the GOT words, to the flag's load (A and B byte-identical, h-rw-pre-5) ---- *)
Definition A1_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) (-160) 0 (-160) 0 [];
    got_regionP;
    YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 64 0))] ].
Definition A1_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_A1 : sstate := mkSS TS_PC sr_atoms A1_regions None A1_facts.

Lemma ts_A1_entry : forall ch,
  afn_pre_x SEGS B ARx STKS ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (TE regs regs [w64 (as_uar_cell B)]) ss_A1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TS_PC)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regs [w64 (as_uar_cell B)]) (mrestrict (w_H W) mem).
Proof.
intros ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite (pal_got_shadow (PI := PA) B PAL), (pal_cell (PI := PA) B PAL) in Kgot.
rewrite (pal_got_uar (PI := PA) B PAL) in Kgotu.
pose proof (pal_got_uar_disj (PI := PA) B PAL) as (D01 & _).
set (E := TE regs regs [w64 (as_uar_cell B)]).
assert (E2 : ew E 2 = getr regs 2) by (apply te_entry; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (E64 : ew E 64 = w64 (as_uar_cell B)) by exact (te_more_lt regs regs [w64 (as_uar_cell B)] 0 ltac:(lia)).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply te_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (@pa_val_range _ _ PA (A_OBJ 0)) as R0. pose proof (@pa_val_range _ _ PA (A_OBJ 1)) as R1.
pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12.
pose proof (ts_rdword_range _ _ _ _ Kgotu) as Ruar.
pose proof (@pa_obj_img _ _ PA 0 ltac:(lia)) as I0. pose proof (@pa_obj_img _ _ PA 1 ltac:(lia)) as I1.
pose proof pa_hi_ok as Hhi.
split.
- apply ts_st_ok.
  all: try change (TE regs regs [w64 (as_uar_cell B)]) with E.
  + unfold E, TE. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold A1_regions, got_regionP. repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ 2 sp0); [exact Usp | lia | lia | | constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * apply (ts_rok E _ (A_OBJ 0) (VAL (A_OBJ 0))); [rewrite Eo0; apply unsigned_lit_small; lia | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * apply (ts_rok E _ (A_OBJ 1) (VAL (A_OBJ 1))); [rewrite Eo1; apply unsigned_lit_small; lia | lia | lia | intros o Ho; lia |].
      constructor; [|constructor].
      apply (ts_chunk E _ _ 0 8 (SOff 64 0) (as_uar_cell B));
        [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgotu).
  + apply pairwise_disjoint_of_extents. unfold A1_regions, got_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite Usp, Eo0, Eo1, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [A1_facts f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- segment A2: the flag's load (one instruction; the flag cell is the only region) ---- *)
Definition ss_A2 : sstate :=
  mkSS (TS_PC + TS_A2_OFF) cur_atoms [YP09.mkRegion (Some (xr 12)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]] None
    (mkFacts [] [] []).
Lemma ts_A2_entry : forall regsc memc (Wc : world SEGS),
  getr regsc 12 = w64 (as_uar_cell B) -> rd32 (aview SEGS (w_H Wc) memc) (as_uar_cell B) 1 ->
  st_ok_pi SEGS VAL (TE regs regsc []) ss_A2
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (TS_PC + TS_A2_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regsc []) (mrestrict (w_H Wc) memc).
Proof.
intros regsc memc Wc R12 Hu. pose proof pal_uar_img as Huar. pose proof cf_img_ok as Hcf.
set (E := TE regs regsc []).
assert (X12 : bv_unsigned (ew E (xr 12)) = as_uar_cell B).
{ unfold E, xr. rewrite (te_cur regs regsc [] 12%bv 12) by reflexivity. rewrite R12. apply unsigned_lit_small. lia. }
split.
- apply ts_st_ok.
  all: try change (TE regs regsc []) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + constructor; [|constructor].
    apply (ts_rok E _ (xr 12) (as_uar_cell B)); [exact X12 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (ts_val_mem_rd32 _ _ _ _ Hu).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- segment A3: the shadow base's load, `mv s4, a0`, the flag test, to the frame call ---- *)
Definition ss_A3 : sstate :=
  mkSS (TS_PC + TS_A3_OFF) cur_atoms [YP09.mkRegion (Some (xr 11)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 64 0))]] None
    (mkFacts [(xr 12, mkAF 1 1 0)] [] []).
Lemma ts_A3_entry : forall regsc memc (Wc : world SEGS),
  getr regsc 11 = w64 (VAL (A_OBJ 12)) -> getr regsc 12 = w64 1 ->
  rdword (aview SEGS (w_H Wc) memc) (VAL (A_OBJ 12)) = Some SHADOW_OFF ->
  st_ok_pi SEGS VAL (TE regs regsc [w64 SHADOW_OFF]) ss_A3
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (TS_PC + TS_A3_OFF))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SLit 0) [] (TE regs regsc [w64 SHADOW_OFF]) (mrestrict (w_H Wc) memc).
Proof.
intros regsc memc Wc R11 R12 Hc.
pose proof (@pa_obj_img _ _ PA 12 ltac:(lia)) as I12.
pose proof pa_hi_ok as Hhi. pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12v.
set (E := TE regs regsc [w64 SHADOW_OFF]).
assert (X11 : bv_unsigned (ew E (xr 11)) = VAL (A_OBJ 12)).
{ unfold E, xr. rewrite (te_cur regs regsc _ 11%bv 11) by reflexivity. rewrite R11. apply unsigned_lit_small. lia. }
assert (X12 : bv_unsigned (ew E (xr 12)) = 1).
{ unfold E, xr. rewrite (te_cur regs regsc _ 12%bv 12) by reflexivity. rewrite R12. reflexivity. }
assert (E64 : ew E 64 = w64 SHADOW_OFF) by exact (te_more_lt regs regsc [w64 SHADOW_OFF] 0 ltac:(lia)).
split.
- apply ts_st_ok.
  all: try change (TE regs regsc [w64 SHADOW_OFF]) with E.
  + apply te_regs_ok.
  + vm_compute. reflexivity.
  + constructor; [|constructor].
    apply (ts_rok E _ (xr 11) (VAL (A_OBJ 12))); [exact X11 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 0 8 (SOff 64 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Hc).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X12. cbn. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- the text's conclusion (ttx_string_specX's post, PRH_FnTx.v 7cf918708def :698-720, word for word: the outcome
   prhtx_out over what was ACTUALLY appended, DEAD-TXSTRING `f0 = 0 -> f1 = 0` (:706), the exact-or-frozen
   position, the ledger at own'; ONE fpostWbmR at RCF (:696; QF's fpostWbm is that term, PRH_Base.v:1647-1650)
   budgeted at wbudget_if f0 [] (the events of the text's own puts), under SRRCF (:695), no abort arm) ---- *)
Definition QT : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    exists b1 cap1 f1 own' (pre : list Z),
    prhtx_post (PA := PA) B Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
      (txt ++ pre) /\
    prhtx_out f0 f1 own0 own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 TS_ks) TS_add pre /\
    (f0 = 0 -> f1 = 0) /\
    PRH_Reader.pj_cstrR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) s k bs /\ prhtx_bvis (PA := PA) W' mem' s k /\
    room_live_cf S' /\
    exists j hist', (j <= length (prhtx_evs len0 cap0 TS_ks))%nat /\
       PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S' /\
       (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 TS_ks)) /\ (f0 <> 0 -> j = 0%nat) /\
    prh_ledger (PI := PI) (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own'.
Definition QF : world SEGS -> config -> Prop := fun W' c' =>
  fpostWbm (PI := PI) (PA := PA) B ARx SK (wbudget_if f0 [] (length (prhtx_evs len0 cap0 TS_ks)))
    STKS dw FP0 regs ly S Hp W mem md QT W' c'.

(* ---- the machine facts the walk carries between segments ---- *)
(* the frame base after `andi sp, sp, -32` (DERIVED: sp0 - 160 rounded down to 32) *)
Definition TS_sp1 : Z := (sp0 - 160) / 32 * 32.
(* the prologue's saves: ra, s0, s1, s2-s11 at sp0 - 8 .. sp0 - 104 *)
Definition TS_SAVED : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ts_saved (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  forall j, (j < 13)%nat ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp0 - 8 * (Z.of_nat j + 1)) 8 (bv_unsigned (getr regs (nth j TS_SAVED 0%bv))).
(* the words tx_string reads back after a call: its saves and the flag pointer frame_alloc_0 leaves in the last word
   of the fake frame *)
Definition ts_mem (Wc : world SEGS) (memc : word -> option byte) (F fl : Z) : Prop :=
  ts_saved Wc memc /\
  rdword (aview SEGS (w_H Wc) memc) (F + 56) = Some fl.
(* the two spill words of the fake frame F at sp1 + 16 and sp1 + 24. SEPARATE from ts_mem (h-hpreset-7's ruling,
   2026-10-29 07:2xZ): image A spills them BEFORE the opening quote's tx_put (A 0x84f10 / 0x84f40, call 0x84f84),
   image B AFTER it (B call 0x855a4, spills 0x855ac / 0x855b0); ts_put_call carries them across a call when they hold *)
Definition ts_spill (Wc : world SEGS) (memc : word -> option byte) (F : Z) : Prop :=
  val_mem SEGS (mrestrict (w_H Wc) memc) (TS_sp1 + 16) 8 F /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (TS_sp1 + 24) 8 F.
Lemma ts_spill_keep : forall Wc memc Wc' memc' F,
  (forall a, TS_sp1 + 16 <= a < TS_sp1 + 32 -> aview SEGS (w_H Wc') memc' a = aview SEGS (w_H Wc) memc a) ->
  ts_spill Wc memc F -> ts_spill Wc' memc' F.
Proof.
intros Wc memc Wc' memc' F K [V16 V24].
split; (eapply ts_vm_av; [|eassumption]); intros i Hi; apply K; lia.
Qed.
(* the string, as the text states it *)
Definition ts_str (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  PRH_Reader.pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lam) s k bs /\ prhtx_bvis (PA := PA) Wc memc s k.
(* the facts a state carries besides its journal: the caller window kept outside FP0, Tx102Glue's text state (the
   calls so far, sizes ks, the text they would append add; the buffer (b, cap), failed f, own, and pre ACTUALLY
   appended; the outcome so far; the room invariant; the ledger) and position tx_pos (exact while failed = 0, frozen
   otherwise), the memnorm keep from the entry memory, the read-only view, the string; and (the batch kit) DEAD so far
   and the depot's wild growth since the entry within a budget of at most the events of ks (tx_line's tl_tx form) *)
Definition ts_side (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS) (memc : word -> option byte)
  (b cap f own : Z) (ks add pre : list Z) : Prop :=
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP0 a -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H W) mem a) /\
  tx_state (PI := PI) (PA := PA) B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own0
    b cap f own ks add pre lyc Sc Hpc Wc memc /\
  tx_pos rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 f ks Sc /\
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) /\
  ts_str Wc memc /\
  (f0 = 0 -> f = 0) /\
  exists WS, incl (wild_part (as_universe B) (st_depot Sc)) (wild_part (as_universe B) (st_depot S) ++ WS) /\
    wbudget_if f0 [] (length (prhtx_evs len0 cap0 ks)) WS.
(* THE LIVE STATE after frame_alloc_0: the journal from the entry REBASED to the current depot (the batch kit:
   YCbqGwild.ajournal_xw_rebaseR, as tx_line's tl_live; the depot's growth is ts_side's budget) with the fake frame
   (0, pos) at F still owned, the side facts, the words above *)
Definition ts_liveR (R : world SEGS -> world SEGS -> Prop)
  (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (kj pos F b cap f own : Z) (ks add pre : list Z) : Prop :=
  AJR R (STKS + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [(0, pos)] lyc Sc Hpc Wc memc mdc kj /\
  ts_side lyc Sc Hpc Wc memc b cap f own ks add pre /\
  F = frame_addr lyc 0 pos /\
  ts_mem Wc memc F (flag_addr lyc 0 pos).
(* ts_live keeps its OWN body, with ts_liveR beside it as the copy over R. It was kept for walks that took a ts_live
   hypothesis apart; no file does now (BTxStep.v:289 / BTxString.v:287 liveb and ATxStep.v:298 livea are @ts_liveR
   at WR). ts_live_R_wle below is the guard that the two bodies cannot drift. *)
Definition ts_live (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS) (memc : word -> option byte)
  (mdc : Model) (kj pos F b cap f own : Z) (ks add pre : list Z) : Prop :=
  AJ (STKS + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [(0, pos)] lyc Sc Hpc Wc memc mdc kj /\
  ts_side lyc Sc Hpc Wc memc b cap f own ks add pre /\
  F = frame_addr lyc 0 pos /\
  ts_mem Wc memc F (flag_addr lyc 0 pos).
Lemma ts_live_R_wle : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre,
  ts_live lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre =
  ts_liveR (@wle SEGS) lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre.
Proof. reflexivity. Qed.
(* the registers tx_string keeps from its prologue on (sp, gp, tp, s0 = the entry sp, s1, s4 = t, s8 = the shadow
   base), and in the loop also s2 = '\\', s3 = s + i, s5 = s + i + 1, s6 = esc, s7 = .str.26, s9 = hex, s10 = the
   frame's shadow, s11 = '0' *)
Definition ts_bregs (rg : bvmap 5 word) : Prop :=
  getr rg 2 = w64 TS_sp1 /\ getr rg 3 = getr regs 3 /\ getr rg 4 = getr regs 4 /\ getr rg 8 = getr regs 2 /\
  getr rg 9 = w64 TS_sp1 /\ getr rg 20 = w64 t /\ getr rg 24 = w64 SHADOW_OFF.
Definition ts_lregs (rg : bvmap 5 word) (F i : Z) : Prop :=
  ts_bregs rg /\ getr rg 18 = w64 92 /\ getr rg 19 = w64 (s + i) /\ getr rg 21 = w64 (s + i + 1) /\
  getr rg 22 = w64 (F + 32) /\ getr rg 23 = w64 TS_STR26 /\ getr rg 25 = w64 TS_HEX /\
  getr rg 26 = w64 (shadow_addr F) /\ getr rg 27 = w64 48.
(* the call sizes and text of the first i bytes, after the opening quote *)
Definition ts_pieces (pre : list Z) : list (list Z) := [34] :: concat (map TxModel.spcs pre).
Definition ts_rest (post : list Z) : list Z := TxModel.plen (concat (map TxModel.spcs post)) ++ [1].
(* the kept registers across a call (all callee-saved) *)
Lemma ts_bregs_pres : forall rg rg', ts_bregs rg -> aregs_preserved rg rg' -> ts_bregs rg'.
Proof.
intros rg rg' (R2 & R3 & R4 & R8 & R9 & R20 & R24) HP. unfold ts_bregs.
rewrite (ts_ap rg rg' 2%bv HP) by ts_cs. rewrite (ts_ap rg rg' 3%bv HP) by ts_cs. rewrite (ts_ap rg rg' 4%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 8%bv HP) by ts_cs. rewrite (ts_ap rg rg' 9%bv HP) by ts_cs. rewrite (ts_ap rg rg' 20%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 24%bv HP) by ts_cs. repeat split; assumption.
Qed.
Lemma ts_lregs_pres : forall rg rg' F i, ts_lregs rg F i -> aregs_preserved rg rg' -> ts_lregs rg' F i.
Proof.
intros rg rg' F i (HB & R18 & R19 & R21 & R22 & R23 & R25 & R26 & R27) HP. unfold ts_lregs.
split; [exact (ts_bregs_pres rg rg' HB HP)|].
rewrite (ts_ap rg rg' 18%bv HP) by ts_cs. rewrite (ts_ap rg rg' 19%bv HP) by ts_cs. rewrite (ts_ap rg rg' 21%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 22%bv HP) by ts_cs. rewrite (ts_ap rg rg' 23%bv HP) by ts_cs. rewrite (ts_ap rg rg' 25%bv HP) by ts_cs.
rewrite (ts_ap rg rg' 26%bv HP) by ts_cs. rewrite (ts_ap rg rg' 27%bv HP) by ts_cs. repeat split; assumption.
Qed.
(* the calls so far plus the next one fit in the text tx_string appends *)
Lemma ts_zsum_nonneg : forall l, Forall (fun x => 0 <= x) l -> 0 <= TxModel.zsum l.
Proof.
induction l as [|x l IH]; intros H; cbn [TxModel.zsum]; [lia|].
inversion H as [|? ? Hx Hl]; subst. specialize (IH Hl). lia.
Qed.
Lemma ts_cnt : forall ks n rest (add : list Z), ks ++ n :: rest = TS_ks -> TxModel.zsum ks = Z.of_nat (length add) ->
  Z.of_nat (length add) + n <= Z.of_nat (length TS_add).
Proof.
intros ks n rest add H Hz.
assert (Hnn : Forall (fun x => 0 <= x) TS_ks).
{ apply Forall_forall. intros x Hx. unfold TS_ks, TxModel.plen in Hx. apply in_map_iff in Hx as (y & <- & _). lia. }
unfold TS_add. rewrite <- s10_strp_wstr, <- TxModel.zsum_plen.
change (TxModel.plen (TxModel.strp bs)) with TS_ks. rewrite <- H in Hnn |- *.
rewrite TxModel.zsum_app. cbn [TxModel.zsum].
apply Forall_app in Hnn as [_ Hr]. inversion Hr as [|? ? Hn0 Hrest]; subst.
pose proof (ts_zsum_nonneg rest Hrest). lia.
Qed.

(* ---- the side facts at the entry (the text's premises, the position at rp_i among them) ---- *)
Lemma ts_side_init : forall rp_hist ch,
  afn_pre_x SEGS B ARx STKS ly S Hp W regs mem md ch -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  fwin (PA := PA) ly W regs mem dw ->
  prhtx_place (PA := PA) ly S W regs mem dw t -> prhtx_trace (PI := PI) (PA := PA) B ly W mem t ->
  prhtx_rec (PA := PA) W mem t b0 len0 cap0 f0 -> prhtx_inv (PA := PA) B Lam ly S W mem b0 len0 cap0 txt ->
  PRH_Reader.pj_cstrR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) s k bs -> prhtx_bvis (PA := PA) W mem s k ->
  prh_ledger (PI := PI) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own0 ->
  ts_side ly S Hp W mem b0 cap0 f0 own0 [] [] [].
Proof.
intros rp_hist ch HPRE HROD HROOM HPOS HFWIN HPLACE HTRACE HREC HINV HSTR HBVIS HLED.
split; [intros; reflexivity|].
split; [eapply tx_state_init; eassumption|].
split; [eapply tx_pos_init; exact HPOS|].
split; [exact (fun H => H)|].
split; [exact HROD | split; [split; [exact HSTR | exact HBVIS]|]].
split; [exact (fun H => H)|].
exists []. split; [rewrite app_nil_r; apply incl_refl | intros _; unfold YCbqGwild.wbudget; cbn; lia].
Qed.

(* ---- the side facts across a step that keeps the allocator's blocks and layout, changes the allocator state at most
   by fake-frame bookkeeping (set_fs: frame_alloc_0, the release's stack_free_state), and changes memory only off the
   stack above the entry sp, off the blocks and off the image's non-runtime bytes (the caller's own runs; the
   frame-area call); the memnorm keep across the step is the caller's (the engine's, at the image) ---- *)
Lemma ts_side_move : forall lyc Sc Hpc Wc memc lyc' Sc' memc' mdc' b cap f own ks add pre,
  ts_side lyc Sc Hpc Wc memc b cap f own ks add pre ->
  ARx lyc' Sc' Hpc Wc memc' mdc' ->
  ly_top lyc' = ly_top lyc -> ablocks B lyc' Sc' = ablocks B lyc Sc -> blocks_bytes Sc' = blocks_bytes Sc ->
  (Sc' = Sc \/ exists fs, Sc' = set_fs fs Sc) ->
  sp0 + dw <= ly_top lyc ->
  (forall a, sp0 <= a < sp0 + dw -> apresent (w_H Wc) memc' a /\ ly_stk_lo lyc' <= a < ly_stk_hi lyc') ->
  (forall a, sp0 <= a < ly_top lyc -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
     aview SEGS (w_H Wc) memc' (p + i) = aview SEGS (w_H Wc) memc (p + i)) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS memc') ->
  ts_side lyc' Sc' Hpc Wc memc' b cap f own ks add pre.
Proof.
intros lyc Sc Hpc Wc memc lyc' Sc' memc' mdc' b cap f own ks add pre
  (HWIN & HTX & HPOS & HMN & HRO & (HCS & HBV) & HDEADs & (WSs & HWIs & HWBs))
  HAR' Etop Eab Ebb HSc Hdw Hpst Kst Kbl Kimg HMNk.
(* the depot is untouched by fake-frame bookkeeping (YG00.v set_fs) *)
assert (Edep : st_depot Sc' = st_depot Sc) by (destruct HSc as [-> | (fs & ->)]; reflexivity).
assert (Hroom : room_live_cf Sc -> room_live_cf Sc')
  by (destruct HSc as [-> | (fs & ->)]; [exact (fun H => H) | apply RL_set_fs]).
assert (HPOS' : tx_pos rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 f ks Sc').
{ destruct HPOS as (j & hist & Hj & HpP). destruct HSc as [-> | (fs & ->)].
  - exists j, hist. split; [exact Hj | exact HpP].
  - destruct (s10_pos_set_fs _ _ _ _ _ _ fs (ex_intro _ hist HpP)) as (hist' & HpP').
    exists j, hist'. split; [exact Hj | exact HpP']. }
destruct HTX as (Ht0 & Ht47 & Hks & (Hrec & Hinv & Hpl & HHp & Hgr & Hbb) & HO & Htr & Hrm & Hled).
pose proof Hpl as (Ht8 & Htlo & Hthi & _ & _).
assert (Kpst : forall a, Exists (in_zr a) PST -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. destruct (pal_pst_static a Ha) as [H1 H2]. exact (Kimg a (pst_img a Ha) H1 H2). }
(* the ledger: the seven statics are image bytes no runtime owns; the harness blocks' heads are block bytes *)
assert (Hled' : prh_ledger (PI := PI) (PA := PA) B lyc' Sc' Hpc Wc memc' Lam peak cnt fail ran most own).
{ destruct Hled as (HG & Hnd & HF & Hperm).
  split; [|split; [exact Hnd | split; [|exact Hperm]]].
  - unfold prh_glob, prh_most, prh_own in *. destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & GR).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj (conj _ G6r) (conj (conj _ G7r) GR)))))));
    (eapply ts_vm_av; [|eassumption]); intros j Hj; apply Kpst; unfold prh_pst;
    repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
  - rewrite Forall_forall in HF |- *. intros [a kk] Hin. specialize (HF _ Hin). cbn [fst snd] in *.
    unfold prh_hblock in *. change (@cf_head CfParams_preset) with 16 in *.
    destruct HF as (Hk & Hab & Hhp & Ha16 & Hv).
    split; [exact Hk|]. split; [rewrite Eab; exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
    eapply ts_vm_av; [|exact Hv]. intros j Hj.
    apply (Kbl (a - 16) (kk + 16) (Z.of_nat j) Hab). unfold req_size. destruct (Z.eqb_spec (kk + 16) 0); lia. }
(* the buffer *)
assert (Hinv' : prhtx_inv (PA := PA) B Lam lyc' Sc' Wc memc' b (len0 + Z.of_nat (length pre)) cap (txt ++ pre)).
{ destruct Hinv as (Hl & [Hz | (Hc & Hlc & Hin & Hby & H4096 & Hceil & Hamr & Hw & Hra & Hhull & Hlam)]).
  - split; [exact Hl | left; exact Hz].
  - assert (Hrq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
    assert (Hin' : In (b, cap) (ablocks B lyc' Sc')) by (rewrite Eab; exact Hin).
    destruct (alx_blocks _ _ _ LAWS lyc' Sc' Hpc Wc memc' mdc' _ _ HAR' Hin') as (_ & _ & _ & _ & Hpres' & _).
    assert (Hnohd : forall h, In h Hpc -> ~ (b <= h < b + req_size cap)).
    { intros h Hh Hhr. destruct Hled as (_ & _ & HF & Hperm).
      apply (Permutation_in _ Hperm) in Hh. apply in_map_iff in Hh as ([a kk] & Eh & Hak). cbn [fst] in Eh.
      rewrite Forall_forall in HF. destruct (HF _ Hak) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
      pose proof (Hlam a kk Hak) as Hne0. change (@cf_head CfParams_preset) with 16 in *.
      assert (Hab' : In (a - 16, kk + 16) (ablocks B lyc' Sc')) by (rewrite Eab; exact Hab).
      assert (Hne : (b, cap) <> (a - 16, kk + 16)) by (intros E; injection E as E1 _; lia).
      pose proof (sep_blocks_x _ _ _ LAWS lyc' Sc' Hpc Wc memc' mdc' _ _ _ _ HAR' Hin' Hab' Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      assert (1 <= req_size (kk + 16)) by (unfold req_size; destruct (Z.eqb_spec (kk + 16) 0); lia). lia. }
    destruct (alx_shadow _ _ _ LAWS lyc' Sc' Hpc Wc memc' mdc' b cap HAR' Hin' Hnohd) as [Hbs Hhv].
    rewrite Hrq in Hbs, Hhv.
    split; [exact Hl|]. right. split; [exact Hc|]. split; [exact Hlc|]. split; [exact Hin'|]. split.
    + unfold bytes_at in *. eapply ts_garr_av; [|exact Hby]. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
      apply (Kbl b cap (Z.of_nat j) Hin). rewrite Hrq. lia.
    + split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hamr|]. split; [|split; [|split; [|exact Hlam]]].
      * intros a Ha. apply (apresent_writable SEGS). apply (proj1 (Hpres' a ltac:(rewrite Hrq; lia))).
      * exact (block_shadow_range _ _ b cap b cap Hbs ltac:(lia) ltac:(lia)).
      * exact Hhv. }
(* the record (its four fields, 28 bytes) and its place *)
assert (Hrec' : prhtx_rec (PA := PA) Wc memc' t b (len0 + Z.of_nat (length pre)) cap f).
{ destruct Hrec as (R1 & R2 & R3 & Rf & V1 & V2 & V3 & V4).
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact Rf|].
  split; [|split; [|split]]; (eapply ts_vm_av; [|eassumption]); intros j Hj; apply Kst; lia. }
assert (Hpl' : prhtx_place (PA := PA) lyc' Sc' Wc regs memc' dw t).
{ split; [exact Ht8|]. split; [exact Htlo|]. split; [exact Hthi|]. split.
  - intros a Ha. apply (apresent_writable SEGS). exact (proj1 (Hpst a ltac:(lia))).
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    exact (alx_zshadow_byte _ _ _ LAWS lyc' Sc' Hpc Wc memc' mdc' x HAR' (proj2 (Hpst x ltac:(lia)))). }
assert (Htr' : prhtx_trace (PI := PI) (PA := PA) B lyc' Wc memc' t).
{ eapply s10_trace_keep; [exact Htr | exact Etop | |].
  - intros Hc a Ha Hn. apply Kst. lia.
  - intros Hc a Ha. apply s10_aview_present. exact (proj1 (Hpst a ltac:(lia))). }
split; [intros a Ha Hn; rewrite (Kst a ltac:(lia)); exact (HWIN a Ha Hn)|].
split.
{ split; [exact Ht0|]. split; [exact Ht47|]. split; [exact Hks|].
  split; [|split; [exact HO | split; [exact Htr' | split; [exact (Hroom Hrm) | exact Hled']]]].
  split; [exact Hrec'|]. split; [exact Hinv'|]. split; [exact Hpl'|]. split; [exact HHp|].
  split; [unfold prhtx_grow in *; rewrite Eab; exact Hgr | rewrite Ebb; exact Hbb]. }
split; [exact HPOS'|]. split; [exact (fun H => HMNk (HMN H))|].
split.
- intros a Hro Hno Her. rewrite (Kimg a (ts_ro_img a Hro) Hno Her). exact (HRO a Hro Hno Her).
- split; [|split; [exact HDEADs | exists WSs; split; [rewrite Edep; exact HWIs | exact HWBs]]].
  destruct HCS as (Hl & Hlen & H32 & Hfa & Hga).
  destruct Hled as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (s, k) Hl) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab. change (@cf_head CfParams_preset) with 16 in Hab.
  split; [split; [exact Hl | split; [exact Hlen | split; [exact H32 | split; [exact Hfa|]]]]|].
  + eapply ts_garr_av; [|exact Hga]. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    replace (s + Z.of_nat j) with ((s - 16) + (16 + Z.of_nat j)) by lia.
    apply (Kbl _ _ _ Hab). unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia.
  + eapply s10_bvis_lam with (W0 := Wc) (mem0 := memc); eassumption.
Qed.

(* ---- the caller's own writes: its stack frame below the entry sp, its fake frame (0, pos) and that frame's shadow *)
Definition ts_own (lyc : alayout) (Sc : astate) (a : Z) : Prop :=
  (sp0 - STKS <= a < sp0) \/
  (exists pos, In (0, pos) (frames Sc) /\
     (in_zr a (frame_rng lyc (0, pos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8))).

(* ---- the side facts across one of the caller's own runs ---- *)
Lemma ts_side_run : forall lyc Sc Hpc Wc memc memc' mdc' b cap f own ks add pre (Wr : Z -> Prop),
  ts_side lyc Sc Hpc Wc memc b cap f own ks add pre ->
  ARx lyc Sc Hpc Wc memc' mdc' ->
  YM05.alloc_ceiling <= sp0 - STKS -> sp0 + dw <= ly_top lyc -> ly_top lyc <= 2 ^ 47 ->
  (forall a, sp0 <= a < sp0 + dw -> apresent (w_H Wc) memc' a /\ ly_stk_lo lyc <= a < ly_stk_hi lyc) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  (forall a, Wr a -> ts_own lyc Sc a) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS memc') ->
  ts_side lyc Sc Hpc Wc memc' b cap f own ks add pre.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc' b cap f own ks add pre Wr HS HAR' Hc0 Hdw Htop47 Hpst Hag HWr HMNk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply aview_eq_of. apply Hag. rewrite unsigned_lit_small by lia. exact Hn. }
assert (Hfr : forall pos, In (0, pos) (frames Sc) ->
  4096 <= frame_addr lyc 0 pos /\ frame_addr lyc 0 pos + 64 <= YM05.alloc_ceiling /\ in_app (frame_addr lyc 0 pos) 64).
{ intros pos Hin. exact (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc' mdc' 0 pos HAR' Hin). }
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hsp. change (bv_modulus 64) with (2 ^ 64) in Hsp.
change (bv_unsigned (getr regs 2)) with sp0 in Hsp.
apply (ts_side_move lyc Sc Hpc Wc memc lyc Sc memc' mdc' b cap f own ks add pre HS HAR' eq_refl eq_refl eq_refl
  (or_introl eq_refl) Hdw Hpst); [| | |exact HMNk].
- intros a Ha. apply K; [lia|]. intros HW. destruct (HWr a HW) as [Hs | (pos & Hin & [Hf | Hf])]; [lia | |];
  destruct (Hfr pos Hin) as (H1 & H2 & H3); unfold in_zr, frame_rng, shadow_addr, fs_frame_bytes in Hf; cbn [fst snd] in Hf;
  change (Z.shiftl 64 0) with 64 in Hf; unfold SHADOW_OFF in Hf; lia.
- intros p n i Hin Hi. destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc' mdc' _ _ HAR' Hin) as (_ & H4096 & Hpce & Happ & _).
  apply K; [lia|]. intros HW. destruct (HWr (p + i) HW) as [Hs | (pos & Hin' & [Hf | Hf])]; [lia | |].
  + pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc' mdc' _ _ 0 pos HAR' Hin Hin') as Hd.
    unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in *. lia.
  + destruct (Hfr pos Hin') as (H1 & H2 & H3). unfold in_zr, shadow_addr, fs_frame_bytes in Hf. cbn [fst snd] in Hf.
    change (Z.shiftl 64 0 / 8) with 8 in Hf. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- intros a Ha _ _. pose proof (pa_segs_low a Ha) as Hlow. apply K; [lia|]. intros HW.
  destruct (HWr a HW) as [Hs | (pos & Hin & [Hf | Hf])]; [lia | |].
  + exact (frm_img_x _ _ _ LAWS lyc Sc Hpc Wc memc' mdc' 0 pos a HAR' Hin Hf Ha).
  + destruct (Hfr pos Hin) as (H1 & H2 & H3). unfold in_zr, shadow_addr, fs_frame_bytes in Hf. cbn [fst snd] in Hf.
    unfold SHADOW_OFF in *. lia.
Qed.

Lemma ts_sp1_bounds : 160 <= sp0 -> 0 <= TS_sp1 /\ sp0 - 191 <= TS_sp1 <= sp0 - 160.
Proof.
intros H. unfold TS_sp1. pose proof (Z.mul_div_le (sp0 - 160) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)).
pose proof (Z.div_pos (sp0 - 160) 32 ltac:(lia) ltac:(lia)). lia.
Qed.

(* ---- the live state across one of the caller's own runs that leaves the read-back words alone ---- *)
Lemma ts_live_runR : forall (R : world SEGS -> world SEGS -> Prop)
  lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos F b cap f own ks add pre (Wr : Z -> Prop),
  ts_liveR R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  AJR R (STKS + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [(0, pos)] lyc Sc Hpc Wc memc' mdc' kj' ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  (forall a, Wr a -> ts_own lyc Sc a) ->
  (forall a, Wr a -> ~ (sp0 - 104 <= a < sp0) /\ ~ (F + 56 <= a < F + 64)) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS memc') ->
  ts_liveR R lyc Sc Hpc Wc memc' mdc' kj' pos F b cap f own ks add pre.
Proof.
intros R lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos F b cap f own ks add pre Wr (HJ & HSD & EF & (HSV & HFL))
  HJ' Hag Hown Hav HMNk.
pose proof HJ' as (HAR' & HLY' & _ & _ & _ & HFR' & _ & _ & _ & _ & _ & _ & _ & HPR' & Hstk' & _).
pose proof HLY' as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk' as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HSTK as HSTK'.
pose proof HSD as (_ & (_ & _ & _ & (_ & _ & Hpl & _) & _) & _).
pose proof Hpl as (_ & Htlo & Hthi & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFR'; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc' mdc' 0 pos HAR' Hin) as (Fb1 & Fb2 & _).
change (fs_frame_bytes 0) with 64 in Fb2.
destruct (ts_sp1_bounds ltac:(lia)) as (Hs1 & Hs2).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. unfold aview. f_equal. unfold mbyte. rewrite (Hag (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn. }
split; [exact HJ'|]. split.
{ refine (ts_side_run lyc Sc Hpc Wc memc memc' mdc' b cap f own ks add pre Wr HSD HAR' _ _ _ _ Hag Hown HMNk).
  - lia.
  - rewrite Etop. lia.
  - rewrite Etop. lia.
  - intros a Ha. rewrite Eslo, Eshi. split; [apply HPR'; lia | lia]. }
split; [exact EF|]. rewrite <- EF in Fb1, Fb2. split.
- intros j Hj. eapply ts_vm_av; [|exact (HSV j Hj)]. intros i Hi. apply K; [lia|].
  intros HW. destruct (Hav _ HW) as (H1 & _). lia.
- rewrite <- HFL. apply ts_rdword_keep. intros j Hj. apply K; [lia|].
  intros HW. destruct (Hav _ HW) as (_ & H1). lia.
Qed.
Lemma ts_live_run : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos F b cap f own ks add pre (Wr : Z -> Prop),
  ts_live lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  AJ (STKS + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [(0, pos)] lyc Sc Hpc Wc memc' mdc' kj' ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  (forall a, Wr a -> ts_own lyc Sc a) ->
  (forall a, Wr a -> ~ (sp0 - 104 <= a < sp0) /\ ~ (F + 56 <= a < F + 64)) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS memc') ->
  ts_live lyc Sc Hpc Wc memc' mdc' kj' pos F b cap f own ks add pre.
Proof. exact (ts_live_runR (@wle SEGS)). Qed.

Lemma ts_live_sameR : forall (R : world SEGS -> world SEGS -> Prop)
  lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos F b cap f own ks add pre,
  ts_liveR R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  AJR R (STKS + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [(0, pos)] lyc Sc Hpc Wc memc' mdc' kj' ->
  (forall x : word, mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS memc') ->
  ts_liveR R lyc Sc Hpc Wc memc' mdc' kj' pos F b cap f own ks add pre.
Proof.
intros R lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos F b cap f own ks add pre HL HJ' Hm HMNk.
apply (ts_live_runR R lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos F b cap f own ks add pre (fun _ => False) HL HJ').
- intros x _. exact (Hm x).
- intros a [].
- intros a [].
- exact HMNk.
Qed.
Lemma ts_live_same : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' pos F b cap f own ks add pre,
  ts_live lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  AJ (STKS + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [(0, pos)] lyc Sc Hpc Wc memc' mdc' kj' ->
  (forall x : word, mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS memc') ->
  ts_live lyc Sc Hpc Wc memc' mdc' kj' pos F b cap f own ks add pre.
Proof. exact (ts_live_sameR (@wle SEGS)). Qed.

(* the realigned frame base *)
Lemma ts_sp1_word : 160 <= sp0 ->
  alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (getr regs 2) + -160)) (Z_to_bv 64 (-32)) = w64 TS_sp1.
Proof.
intros H160. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned. unfold w64, TS_sp1, spZ in *.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small (bv_unsigned (getr regs 2) + -160)) by lia.
change ((-32) mod 2 ^ 64) with (2 ^ 64 - 32). rewrite ts_land_m32 by lia.
rewrite Z.mod_small; [lia|]. split; [apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia|].
pose proof (Z.mul_div_le (bv_unsigned (getr regs 2) - 160) 32 ltac:(lia)). lia.
Qed.

(* ---- the entry facts every call site carries (the text's premises at the entry): the run premise guarded by f0 = 0
   (the run's events from rp_i are those of all of tx_string's puts when it is entered at failed = 0), the batch's
   guarded room and guarded consumer window over the same events (PRH_FnTx.v 7cf918708def :677 / :682), and fpre's
   FRM0-ENTRY conjunct (the rounding mode is 0 at the entry; tx_string runs no float instruction, so every
   tx_put call is entered with it); the universe closure without DW (:671) ---- *)
Definition ts_pre (ch : list (Z * Z * Z)) : Prop :=
  afn_pre_x SEGS B ARx STKS ly S Hp W regs mem md ch /\ prh_univ_closure (PI := PI) B CTX0 /\
  fwin (PA := PA) ly W regs mem dw /\ prhtx_place (PA := PA) ly S W regs mem dw t /\
  len0 + Z.of_nat (length TS_add) + 1 <= 2 ^ 28 /\ blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX /\
  2 * (len0 + Z.of_nat (length TS_add) + 1) < cf_malloc_max /\
  (f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 TS_ks)) /\
  (f0 = 0 -> YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 TS_ks)) (st_depot S)) /\
  (f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 TS_ks))) /\
  frm_zero (@YK11.fp_csr fx).

(* the realigned frame base, as a range *)
Lemma ts_sp1_range : sp0 mod 16 = 0 -> 176 <= sp0 -> sp0 - 176 <= TS_sp1 <= sp0 - 160 /\ TS_sp1 mod 32 = 0.
Proof.
intros Hal16 H. unfold TS_sp1. pose proof (Z.mul_div_le (sp0 - 160) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)).
split; [|apply Z.mod_mul; lia]. split; [|lia]. lia.
Qed.

(* the string across a journal whose footprint misses it, with the ledger at both ends *)
Lemma ts_str_keep : forall STK1 spx FP own lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 own1 own2,
  AJ STK1 spx FP lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PI := PI) (PA := PA) B lyc Sc Hpc Wc memc Lam peak cnt fail ran most own1 ->
  prh_ledger (PI := PI) (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam peak cnt fail ran most own2 ->
  (forall a, s <= a < s + k -> ~ inFP FP a) ->
  ts_str Wc memc -> ts_str W2 mem2.
Proof.
intros STK1 spx FP own lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 own1 own2 HJ HL1 HL2 HnFP
  ((Hl & Hlen & H32 & Hfa & Hga) & HBV).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & KB & _).
pose proof HL1 as (_ & _ & HF1 & _). pose proof HL2 as (_ & _ & HF2 & _).
rewrite Forall_forall in HF1, HF2.
destruct (HF1 (s, k) Hl) as (Hk & Hab1 & _). destruct (HF2 (s, k) Hl) as (_ & Hab2 & _).
cbn [fst snd] in Hk, Hab1, Hab2. change (@cf_head CfParams_preset) with 16 in Hab1, Hab2.
split; [split; [exact Hl | split; [exact Hlen | split; [exact H32 | split; [exact Hfa|]]]]|].
- eapply ts_garr_av; [|exact Hga]. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  replace (s + Z.of_nat j) with ((s - 16) + (16 + Z.of_nat j)) by lia.
  apply (KB _ _ _ Hab1 Hab2).
  + unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia.
  + replace (s - 16 + (16 + Z.of_nat j)) with (s + Z.of_nat j) by lia. apply HnFP. lia.
- eapply s10_bvis_lam with (W0 := Wc) (mem0 := memc); eassumption.
Qed.
(* ADDITION (the batch kit): the same keep across a BUDGETED journal (YCbqG.ajournal_xwR at any R and WS; the callee's
   journal from s10_call_WbmR, :1304); the proof reads only its allocator relation and block keep (ajxR_ar, ajxR_blk) *)
Lemma ts_str_keep_wR : forall (R : world SEGS -> world SEGS -> Prop)
  STK1 spx FP own lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1 own1 own2,
  YCbqG.ajournal_xwR (SK := SK) SEGS B PST ARx R STK1 spx FP lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  prh_ledger (PI := PI) (PA := PA) B lyc Sc Hpc Wc memc Lam peak cnt fail ran most own1 ->
  prh_ledger (PI := PI) (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam peak cnt fail ran most own2 ->
  (forall a, s <= a < s + k -> ~ inFP FP a) ->
  ts_str Wc memc -> ts_str W2 mem2.
Proof.
intros R STK1 spx FP own lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1 own1 own2 HJ HL1 HL2 HnFP
  ((Hl & Hlen & H32 & Hfa & Hga) & HBV).
pose proof (ajxR_blk HJ) as KB.
pose proof HL1 as (_ & _ & HF1 & _). pose proof HL2 as (_ & _ & HF2 & _).
rewrite Forall_forall in HF1, HF2.
destruct (HF1 (s, k) Hl) as (Hk & Hab1 & _). destruct (HF2 (s, k) Hl) as (_ & Hab2 & _).
cbn [fst snd] in Hk, Hab1, Hab2. change (@cf_head CfParams_preset) with 16 in Hab1, Hab2.
split; [split; [exact Hl | split; [exact Hlen | split; [exact H32 | split; [exact Hfa|]]]]|].
- eapply ts_garr_av; [|exact Hga]. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  replace (s + Z.of_nat j) with ((s - 16) + (16 + Z.of_nat j)) by lia.
  apply (KB _ _ _ Hab1 Hab2).
  + unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia.
  + replace (s - 16 + (16 + Z.of_nat j)) with (s + Z.of_nat j) by lia. apply HnFP. lia.
- pose proof (ajxR_ar HJ) as HAR2.
  eapply s10_bvis_lam with (W0 := Wc) (mem0 := memc); eassumption.
Qed.
Lemma ts_str_keep_w : forall STK1 spx FP own lyc Sc Hpc Wc memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1 own1 own2,
  YCbqG.ajournal_xw (SK := SK) SEGS B PST ARx STK1 spx FP lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  prh_ledger (PI := PI) (PA := PA) B lyc Sc Hpc Wc memc Lam peak cnt fail ran most own1 ->
  prh_ledger (PI := PI) (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam peak cnt fail ran most own2 ->
  (forall a, s <= a < s + k -> ~ inFP FP a) ->
  ts_str Wc memc -> ts_str W2 mem2.
Proof. exact (ts_str_keep_wR (@wle SEGS)). Qed.


(* ---- THE tx_put CALL, from the state a run leaves at a `jal tx_put` (Tx102Glue.v s10_call_WbmR, :1400, with tx_put's
   text: SRr' RZ_cf over ONE fpostWbmR at RCF budgeted at its own events, PRH_FnTx.v:454-455: every outcome RETURNS):
   the calls so far ks, this call n, the calls to come rest, ks ++ n :: rest = TS_ks; the texts' premise
   `(length rp_os <= 4)%nat` is passed on. The callee starts at the caller's buffer (b, cap), failed f, own and length
   len0 + |pre| (tx_state_pre), at the caller's current position rp_i + j (tx_pos); its GROW premise is the caller's run
   window over this call (tx_window, tx_put_ev), its guarded room and consumer window the caller's over this call
   (tx_room_window, tx_cons_window; only at f = 0). Its post (three arms, DEAD-TXPUT, two position conjuncts) becomes an
   outcome over [n] and a position step (tx_put_res), folded into the caller's state and position (tx_state_fold_wR,
   :1356; tx_pos_fold), its budget into the caller's (tx_budget_fold). The journal enters REBASED (ts_liveR RCF, :1202),
   is unbased for the call (YCbqGwild.ajournal_xw_unbase0R, :1277) and leaves rebased at the callee's end depot
   (ajournal_xw_rebaseR, :1338). Its fQmn keep extends the caller's memnorm keep; the return address below the ceiling
   is the jal's own return pc, which the image discharges. The continuation receives the live state with the call done,
   WHATEVER the outcome (the code does not test failed), the appended prec ([] unless DONE), and the spill words kept.
   One lemma at all five call sites (opening quote, backslash, byte, esc[], closing quote) of both images ---- *)
Lemma ts_put_call : forall ch Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ks add pre n srcp srcl rest,
  ts_pre ch ->
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
  bv_unsigned (ew E 2) = sp0 ->
  ts_liveR RCF lyc Sc Hpc Wc (ms_mem ms) mdc kj pos F b cap f own ks add pre ->
  ts_bregs (ms_regs ms) ->
  getr (ms_regs ms) 10 = w64 t -> getr (ms_regs ms) 11 = w64 srcp -> getr (ms_regs ms) 12 = w64 n ->
  YK0s.ret_ok (getr (ms_regs ms) 1) -> 4096 <= raZ (ms_regs ms) -> raZ (ms_regs ms) < YM05.alloc_ceiling ->
  src_rd (PA := PA) Wc (ms_mem ms) srcp srcl -> Z.of_nat (length srcl) = n ->
  prhtx_kept (PA := PA) B Lam lyc Sc srcp n ->
  (forall a, srcp <= a < srcp + n -> ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)) ->
  ks ++ n :: rest = TS_ks ->
  (* the entry texts' own premise, passed to ttx_put below. It is a PREMISE, not a Section hypothesis: as a
     hypothesis the section discharge captured it in 17 lemmas of this file and changed their arity. *)
  (length rp_os <= 4)%nat ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 cap2 f2 own2 prec,
     ts_liveR RCF ly2 S2 Hp2 W2 mem2 md2 kj2 pos F b2 cap2 f2 own2 (ks ++ [n]) (add ++ srcl) (pre ++ prec) ->
     (ts_spill Wc (ms_mem ms) F -> ts_spill W2 mem2 F) ->
     aregs_preserved (ms_regs ms) regs2 ->
     SRRCF W2 (mkCfg (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2) QF) ->
  SRRCF Wc (mkCfg ms mdc) QF.
Proof.
intros ch Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ks add pre n srcp srcl rest
  (HPRE & HCL & HFWIN & HPLACE & HLEN & HLIVE & HMAX & HEVS & HROOMW & HCONS & HFRM) HS Hrv Hpcs HE2
  (HJ & (HWIN & HTX & HPOSs & HMN & HRO & HSTR & HDEAD & (WS0 & HWI & HWB)) & EF & HM)
  HBR Ha0 Ha1 Ha2 Hra Hra4 Hrac HSRC Hn HKEPT Hdisj Hsplit HOS HK.
subst n.
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & Hdpres).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
pose proof HSTKP as (HSTKP0 & HSTKP1).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc. pose proof (ajxR_frs HJ) as HFRc.
pose proof (ajxR_pres HJ) as HPRc.
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Eshi & _).
pose proof HBR as (R2 & R3 & R4 & R8 & R9 & R20 & R24).
pose proof HM as (HSV & HFL).
pose proof HTX as (Ht0 & Ht47 & Hks & (Hrec & Hinv & Hpl & HHp & Hgr & Hbb) & HO & Htr & Hroom & Hled).
pose proof (ts_cnt ks (Z.of_nat (length srcl)) rest add Hsplit Hks) as Hcnt.
destruct HPOSs as (j & rp_histc & Hjok & HPOSc).
assert (H176 : 176 <= sp0) by lia.
destruct (ts_sp1_range Hal16 H176) as (Hsp1a & Hsp1b).
set (o := TS_sp1 - sp0).
set (lenc := len0 + Z.of_nat (length pre)) in *.
assert (Ho16 : o mod 16 = 0) by (unfold o; lia).
assert (Hdo16 : (dw - o) mod 16 = 0) by (unfold o; lia).
assert (Hspc : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ at 1. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. unfold o. lia. }
assert (Hsp : getr (ms_regs ms) 2 = sv_denot E (SOff 2 o)).
{ apply bv_eq. rewrite denot_SOff, HE2, R2. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite YP0m.zcanon_small by (unfold o; lia). unfold o. lia. }
destruct (tx_state_pre B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own0
  b cap f own ks add pre lyc Sc Hpc Wc (ms_mem ms) (ms_regs ms) (dw - o) HTX
  ltac:(rewrite Hspc; unfold o; lia) ltac:(rewrite Hspc; lia))
  as (HRM & HPL & HTR & HREC1 & HINV1 & HLED1 & HBB & EHp & Hplen).
(* the text's run premise, room and consumer window split as ks (done) ++ [n] (this call) ++ rest (to come) *)
assert (HEV : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 (ks ++ [Z.of_nat (length srcl)] ++ rest)))
  by (intros Hf0; specialize (HEVS Hf0); rewrite <- Hsplit in HEVS; exact HEVS).
assert (HRW : f0 = 0 -> YCbqGwild.wild_room (as_universe B) []
  (length (prhtx_evs len0 cap0 (ks ++ [Z.of_nat (length srcl)] ++ rest))) (st_depot S))
  by (intros Hf0; specialize (HROOMW Hf0); rewrite <- Hsplit in HROOMW; exact HROOMW).
assert (HCF : f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i
  (length (prhtx_evs len0 cap0 (ks ++ [Z.of_nat (length srcl)] ++ rest))))
  by (intros Hf0; specialize (HCONS Hf0); rewrite <- Hsplit in HCONS; exact HCONS).
(* the callee's run window and GROW premise, its guarded room and consumer window: from the text's, only while the
   caller is at failed = 0 *)
assert (HWc : f = 0 -> prh_run_at rp_sm rp_x rp_os (rp_i + j) (prhtx_evs lenc cap [Z.of_nat (length srcl)]))
  by exact (tx_window rp_sm rp_x rp_os rp_i j len0 cap0 f0 f own0 own b0 b cap ks add pre
    [Z.of_nat (length srcl)] rest HO Hjok Hks HEV).
pose proof (tx_room_window (as_universe B) (st_depot S) (st_depot Sc) WS0 len0 cap0 f0 f own0 own b0 b cap ks add pre
  [Z.of_nat (length srcl)] rest HO Hks HRW HWI HWB) as HROOMc.
pose proof (tx_cons_window rp_sm rp_x rp_os rp_i j len0 cap0 f0 f own0 own b0 b cap ks add pre
  [Z.of_nat (length srcl)] rest HO Hjok Hks HCF) as HCONSc.
pose proof (s10_fwin_callR B ARx SK RCF STKS dw sp0 FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [(0, pos)] lyc Sc Hpc Wc
  (ms_mem ms) mdc kj (ms_regs ms) o HJ Hspc ltac:(unfold o; lia) ltac:(unfold o; lia) ltac:(unfold o; lia) Hdo16)
  as HFW.
(* the journal unbased for the call: from the entry S, at the budget WS0 the side facts carry *)
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx RCF _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWI)
  as HJW.
(* the bytes the callee may write: the record (28 bytes) and the buffer; neither is a byte of the string, the window
   below sp0, or the fake frame *)
assert (HnotFP : forall a, ~ (t <= a < t + 28) -> (cap <> 0 -> ~ (b <= a < b + req_size cap)) ->
  ~ inFP (prhtx_fp t b cap) a).
{ intros a H1 H2 Hf. destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)]; [exact (H1 Hr) | exact (H2 Hc0 Hb)]. }
assert (Hbuf : cap <> 0 -> In (b, cap) (ablocks B lyc Sc) /\ b + req_size cap <= YM05.alloc_ceiling /\
  forall a kk, In (a, kk) Lam -> a - 16 <> b).
{ intros Hc0. destruct HINV1 as (_ & [(Hz & _) | (_ & _ & Hin & _ & _ & Hceil' & _ & _ & _ & _ & Hlam)]); [lia|].
  split; [exact Hin|]. split; [unfold req_size; destruct (Z.eqb_spec cap 0); lia | exact Hlam]. }
(* the achain at the call: s0 = sp0, the saves below it, the window and the record's trace region above it *)
assert (Hpres : forall a, sp0 - 16 <= a < ly_top lyc -> aview SEGS (w_H Wc) (ms_mem ms) a <> None).
{ intros a Ha. destruct (Z_lt_le_dec a sp0) as [Hlo|Hhi].
  - destruct (Z_lt_le_dec a (sp0 - 8)) as [H1|H1].
    + pose proof (ts_vm_present _ _ _ _ _ (HSV 1%nat ltac:(lia)) (Z.to_nat (a - (sp0 - 16))) ltac:(lia)) as V.
      replace (sp0 - 8 * (Z.of_nat 1 + 1) + Z.of_nat (Z.to_nat (a - (sp0 - 16)))) with a in V by lia. exact V.
    + pose proof (ts_vm_present _ _ _ _ _ (HSV 0%nat ltac:(lia)) (Z.to_nat (a - (sp0 - 8))) ltac:(lia)) as V.
      replace (sp0 - 8 * (Z.of_nat 0 + 1) + Z.of_nat (Z.to_nat (a - (sp0 - 8)))) with a in V by lia. exact V.
  - destruct (Z_lt_le_dec a (t - 16)) as [H1|H1].
    + apply s10_aview_present. apply HPRc. lia.
    + destruct (Htr ltac:(lia)) as (Hp3 & _). apply Hp3. lia. }
destruct (s10_achain_at lyc Wc (ms_mem ms) TS_sp1 sp0 Hpres ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  as (ch1 & Hch1).
assert (Hs0 : s0Z (ms_regs ms) = sp0) by (unfold s0Z, spZ; rewrite R8; reflexivity).
assert (HSHI1 : spZ (ms_regs ms) + 64 <= ly_stk_hi lyc) by (rewrite Hspc, Eshi; unfold o; lia).
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (s10_call_WbmR B ARx SK LAWS RCF (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms STKS dw sp0 FP0 ly S Hp W mem md [(0, pos)] lyc Sc Hpc mdc kj WS0
    (@STK_tx_put PI) (prhtx_fp t b cap) o (ew E 2) (getr (ms_regs ms) 1) ch1
    _ _ HS Hrv HJW Hsp eq_refl HE2 Ho16 ltac:(unfold o; lia) HSTKP0 ltac:(unfold o; lia)
    Hdw0 Hdw16 ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp) eq_refl Hra Hra4
    ltac:(rewrite Hs0; replace (sp0 + o) with TS_sp1 by (unfold o; lia); exact Hch1)).
  - intros HPRE1. rewrite Hpcs.
    exact (TXPUT rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 rp_histc lyc Sc Hpc Wc (ms_regs ms)
      (ms_mem ms) mdc ch1 (dw - o) t srcp
      (Z.of_nat (length srcl)) b lenc cap f own (txt ++ pre) srcl Lam peak cnt fail ran most
      (conj HPRE1 (conj HRO (conj HSHI1 (conj Hrac HFRM)))) HCL HRM HPOSc HOS HROOMc HCONSc Ha0 Ha1 Ha2 HFW HPL HTR
      HREC1 HINV1 HSRC eq_refl HKEPT Hdisj ltac:(unfold lenc; pose proof HO as HOl; apply tx_out_len in HOl; lia) HLED1
      (fun Hf Hlt => tx_put_ev rp_sm rp_x rp_os (rp_i + j)%nat lenc cap (Z.of_nat (length srcl)) f HWc Hf Hlt)
      ltac:(lia) ltac:(unfold lenc; pose proof HO as HOl; apply tx_out_len in HOl; lia)).
  - unfold fp_sub_x. intros a Ha.
    destruct (tx_state_fp B ARx LAWS Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own0
      b cap f own ks add pre lyc Sc Hpc Wc (ms_mem ms) mdc HTX HARc a Ha) as [H1|H1]; [left | right; left]; exact H1. }
cbv beta. intros W2 c2 _ HN.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HWB1 & HJW2 & HJ1 & HW1 & HP & HQ).
destruct HQ as ((b2 & cap2 & f2 & own2 & prec & HPOST & HARMS & HDEAD2 & _ & HRM2 & HG2 & HN2 & HLED2) & HMN2).
(* the callee's outcome and position step over [n], folded into the caller's *)
destruct (tx_put_res rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 rp_histc S2 lenc cap f f2 own own2 b b2 cap2
  (Z.of_nat (length srcl)) srcl prec _ HARMS HG2 HN2) as (HOc & jq & hist2 & Hjq & HPOS2).
pose proof (ajxR_ly HJ1) as HLY1. pose proof (ajxR_frm HJ1) as KF1.
pose proof HLY1 as (_ & _ & _ & _ & _ & EFF & _).
assert (HinF : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc (ms_mem ms) mdc 0 pos HARc HinF) as (Fb1 & Fb2 & Fb3).
change (fs_frame_bytes 0) with 64 in Fb2, Fb3.
(* the caller's frame below sp0 is outside the callee's footprint, and so kept *)
assert (Kst : forall a, TS_sp1 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha. apply HW1; [unfold o; lia|]. apply HnotFP; [lia|]. intros Hc0 Hb.
  destruct (Hbuf Hc0) as (_ & Hb2 & _). lia. }
apply (HK ly2 S2 Hp2 W2 regs2 mem2 md2 (kj + k1) b2 cap2 f2 own2 prec); [| |exact HP].
2: { apply ts_spill_keep. intros a Ha. apply Kst. lia. }
split.
{ exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx RCF _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJW2). }
split.
2: { split.
  - rewrite EF. unfold frame_addr. rewrite EFF. reflexivity.
  - assert (EFL : flag_addr ly2 0 pos = flag_addr lyc 0 pos) by (unfold flag_addr; rewrite EFF; reflexivity).
    rewrite EFL. split.
    + intros j0 Hj0. eapply ts_vm_av; [|exact (HSV j0 Hj0)]. intros i Hi. apply Kst. lia.
    + rewrite <- HFL. apply ts_rdword_keep. intros j0 Hj0. rewrite EF in *.
      apply (KF1 0 pos _ HinF); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia|].
      apply HnotFP; [lia|]. intros Hc0 Hb. destruct (Hbuf Hc0) as (Hin & _ & _).
      pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc (ms_mem ms) mdc _ _ 0 pos HARc Hin HinF) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. lia. }
(* the side facts after the call *)
split.
{ intros a Ha Hn0. rewrite (HW1 a ltac:(unfold o; lia)); [exact (HWIN a Ha Hn0)|].
  intros Hf. apply Hn0. exact (tx_state_fp_win B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own0
    b cap f own ks add pre lyc Sc Hpc Wc (ms_mem ms) HTX a ltac:(lia) Hf). }
split.
{ eapply (tx_state_fold_wR B ARx SK RCF Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own0
    b cap f own ks add pre [Z.of_nat (length srcl)] srcl b2 cap2 f2 own2 prec lyc Sc Hpc Wc (ms_mem ms) mdc
    ly2 S2 Hp2 W2 mem2 md2 (ms_regs ms) (dw - o) (@STK_tx_put PI) k1 WS1 HTX HARc).
  - cbn [TxModel.zsum]. lia.
  - rewrite Hspc. unfold o. lia.
  - exact HSTKP0.
  - rewrite Hspc. replace (sp0 + o + (dw - o)) with (sp0 + dw) by lia. exact HJ1.
  - intros a Ha Hn0. apply HW1; [rewrite Hspc in Ha; lia | exact Hn0].
  - exact HPOST.
  - exact HOc.
  - exact HRM2.
  - exact HLED2. }
split.
{ exact (tx_pos_fold rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 f f2 own0 own own2 b0 b b2 cap cap2 j jq hist2 S2
    ks [Z.of_nat (length srcl)] add srcl pre prec Hks HO Hjok HOc Hjq HPOS2). }
split; [exact (fun H => HMN2 (HMN H))|].
split.
{ exact (s10_rod_keptR B ARx SK pst_ro RCF (@STK_tx_put PI + (dw - o)) (sp0 + dw) (prhtx_fp t b cap)
    lyc (set_depot (st_depot S2) Sc) Hpc Wc (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1
    (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx RCF _ _ _ _ _ Hpc _ _ _ _ _ _ _ _ _ _ _ _ HJ1)
    (s10_fp_closed B Lam lyc Sc Wc (ms_mem ms) t b lenc cap (txt ++ pre) ltac:(lia) HINV1) HRO). }
split.
{ apply (ts_str_keep_wR RCF _ _ _ _ lyc Sc Hpc Wc (ms_mem ms) mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS1 own own2 HJ1 HLED1 HLED2);
    [|exact HSTR].
  pose proof HSTR as ((Hl & _) & (_ & _ & _ & Hsk & _)).
  intros a Ha. apply HnotFP; [lia|]. intros Hc0 Hb.
  destruct (Hbuf Hc0) as (Hin & _ & Hlam).
  pose proof HLED1 as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (s, k) Hl) as (_ & Hab & _). cbn [fst snd] in Hab. change (@cf_head CfParams_preset) with 16 in Hab.
  assert (Hne : (b, cap) <> (s - 16, k + 16)) by (intros E0; injection E0 as E1 _; exact (Hlam s k Hl ltac:(lia))).
  pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc (ms_mem ms) mdc _ _ _ _ HARc Hin Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof HSTR as ((_ & Hlen & _) & _).
  assert (req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
  assert (req_size cap = cap \/ cap = 0) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia). lia. }
(* DEAD so far, and the budget: WS0 ++ WS1 (the callee's budget folded, Tx102Glue.v tx_budget_fold) *)
split; [intros Hf0; exact (HDEAD2 (HDEAD Hf0))|].
exists (WS0 ++ WS1). split; [exact (ajxR_wild HJW2)|].
exact (tx_budget_fold len0 cap0 f0 f own0 own b0 b cap ks add pre [Z.of_nat (length srcl)] WS0 WS1 HO Hks HDEAD HWB
  HWB1).
Qed.

(* ---- a read-only literal handed to tx_put (the quote, the backslash): the state-free, PER-INSTANCE kept_img, at any
   live state (Tx102Glue.v s10_src_img) ---- *)
Lemma ts_src_litR : forall (R : world SEGS -> world SEGS -> Prop)
  lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre srcp srcl,
  ts_liveR R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  kept_img (PA := PA) B srcp (Z.of_nat (length srcl)) -> (0 < length srcl)%nat ->
  (forall j, (j < length srcl)%nat ->
     option_map (fun bb : byte => bv_unsigned bb) (seg_rom SEGS (Z_to_bv 64 (srcp + Z.of_nat j))) = Some (nth j srcl 0)) ->
  src_rd (PA := PA) Wc memc srcp srcl /\ prhtx_kept (PA := PA) B Lam lyc Sc srcp (Z.of_nat (length srcl)) /\
  (forall a, srcp <= a < srcp + Z.of_nat (length srcl) -> ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)).
Proof.
intros R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre srcp srcl
  (HJ & (HWIN & HTX & HPOS & HMN & HRO & HSTR & _) & EF & HM) HKI Hn0 Hrom.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof HTX as (_ & _ & _ & (_ & Hinv & Hpl & _) & _).
pose proof Hpl as (_ & Htlo & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof pa_hi_ok as Hph. pose proof img_box as Hbox.
destruct (s10_src_img B ARx LAWS zs_aligned img_shadow_vis_x img_box img_cf_box lyc Sc Hpc Wc memc mdc Lam srcp srcl
  HARc HRO HKI Hn0 Hrom) as [HSRC HKEPT].
split; [exact HSRC|]. split; [exact HKEPT|].
intros a Ha. pose proof HKI as (Hlo & Hhi & Hro).
split; [lia|]. intros Hb.
destruct Hinv as (_ & [(Hz & _) | (Hc & _ & Hin & _)]); [lia|].
destruct (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc a HARc) as [_ Hni].
{ left. exists b, cap. split; [exact Hin|]. unfold req_size. destruct (Z.eqb_spec cap 0); lia. }
apply Hni. apply ts_ro_img. exact (proj1 (Hro a Ha)).
Qed.
Lemma ts_src_lit : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre srcp srcl,
  ts_live lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  kept_img (PA := PA) B srcp (Z.of_nat (length srcl)) -> (0 < length srcl)%nat ->
  (forall j, (j < length srcl)%nat ->
     option_map (fun bb : byte => bv_unsigned bb) (seg_rom SEGS (Z_to_bv 64 (srcp + Z.of_nat j))) = Some (nth j srcl 0)) ->
  src_rd (PA := PA) Wc memc srcp srcl /\ prhtx_kept (PA := PA) B Lam lyc Sc srcp (Z.of_nat (length srcl)) /\
  (forall a, srcp <= a < srcp + Z.of_nat (length srcl) -> ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)).
Proof. exact (ts_src_litR (@wle SEGS)). Qed.

(* ---- the call sizes and text around one byte ---- *)
Lemma ts_pieces_snoc : forall pre cb, ts_pieces (pre ++ [cb]) = ts_pieces pre ++ TxModel.spcs cb.
Proof.
intros pre cb. unfold ts_pieces. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.
Lemma ts_rest_cons : forall cb post, ts_rest (cb :: post) = TxModel.plen (TxModel.spcs cb) ++ ts_rest post.
Proof.
intros cb post. unfold ts_rest, TxModel.plen. cbn [map concat]. rewrite map_app, app_assoc. reflexivity.
Qed.
Lemma ts_ks_split : forall pre post, bs = pre ++ post -> TxModel.plen (ts_pieces pre) ++ ts_rest post = TS_ks.
Proof.
intros pre post Ebs. unfold TS_ks. rewrite s10s_ks, Ebs. unfold ts_pieces, ts_rest, TxModel.plen.
rewrite map_app, concat_app, map_app. cbn [map app]. rewrite app_assoc. reflexivity.
Qed.

(* a covering hull covers a sub-range (S10TxPut.v tp_hull_sub, S1Strdup's sd_hull_sub) *)
Lemma ts_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s0 Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* the buffer, when there is one, is a block of its own: no harness string and no fake frame meets it *)
Lemma ts_buf_apartR : forall (R : world SEGS -> world SEGS -> Prop)
  lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre,
  ts_liveR R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  cap <> 0 ->
  (forall x kx, In (x, kx) Lam -> forall a, x <= a < x + kx -> ~ (b <= a < b + cap)) /\
  (forall a, F <= a < F + 64 -> ~ (b <= a < b + cap)).
Proof.
intros R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre (HJ & (_ & HTX & _) & EF & _) Hc0.
pose proof HJ as (HARc & _ & _ & _ & _ & HFRc & _).
pose proof HTX as (_ & _ & _ & (_ & Hinv & _) & _ & _ & _ & HLED).
destruct Hinv as (_ & [(Hz & _) | (Hc & _ & Hin & _ & _ & _ & _ & _ & _ & _ & Hlam)]); [lia|].
assert (Hrq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
split.
- intros x kx Hx a Ha Hb.
  pose proof HLED as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (x, kx) Hx) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
  change (@cf_head CfParams_preset) with 16 in Hab.
  assert (Hne : (b, cap) <> (x - 16, kx + 16)).
  { intros E0; injection E0 as E1 _. apply (Hlam x kx Hx). unfold cf_head, CfParams_preset in *. cbn in *. lia. }
  pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hin Hab Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (req_size (kx + 16) = kx + 16) by (unfold req_size; destruct (Z.eqb_spec (kx + 16) 0); lia). lia.
- intros a Ha Hb.
  assert (HinF : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
  pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ 0 pos HARc Hin HinF) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. rewrite <- EF in Hd. lia.
Qed.
Lemma ts_buf_apart : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre,
  ts_live lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  cap <> 0 ->
  (forall x kx, In (x, kx) Lam -> forall a, x <= a < x + kx -> ~ (b <= a < b + cap)) /\
  (forall a, F <= a < F + 64 -> ~ (b <= a < b + cap)).
Proof. exact (ts_buf_apartR (@wle SEGS)). Qed.

(* ---- byte i of the string handed to tx_put (`tx_put(t, s, 1)`): the string is a Lam block ---- *)
Lemma ts_src_byteR : forall (Rw : world SEGS -> world SEGS -> Prop)
  lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap pre cb post,
  ts_liveR Rw lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap -> bs = pre ++ cb :: post ->
  YM05.alloc_ceiling <= sp0 ->
  src_rd (PA := PA) Wc memc (s + Z.of_nat (length pre)) [cb] /\
  prhtx_kept (PA := PA) B Lam lyc Sc (s + Z.of_nat (length pre)) 1 /\
  (forall a, s + Z.of_nat (length pre) <= a < s + Z.of_nat (length pre) + 1 ->
     ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)) /\
  0 < cb < 256.
Proof.
intros Rw lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap pre cb post HL Ebs Hc0.
pose proof HL as (HJ & (HWIN & HTX & HPOS & HMN & HRO & ((Hl & Hlen & H32 & Hfa & Hga) & HBV) & _) & EF & HM).
pose proof HBV as (Hs4096 & Hs8 & Hk0 & Hsk & Hamr & Hras & Hhull & Hpres).
pose proof HTX as (_ & _ & _ & (_ & _ & Hpl & _) & _).
pose proof Hpl as (_ & Htlo & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
set (i := length pre) in *.
assert (Hi : (i < length bs)%nat) by (rewrite Ebs, length_app; cbn; lia).
assert (Hnth : nth i (bs ++ [0]) 0 = cb).
{ rewrite Ebs, <- app_assoc, <- app_comm_cons. unfold i. apply nth_middle. }
assert (Hcb : 0 < cb < 256).
{ rewrite Forall_forall in Hfa. apply Hfa. rewrite Ebs. apply in_or_app. right. left. reflexivity. }
assert (Hik : Z.of_nat i + 1 <= k) by lia.
(* src_rd's ceiling clause `p + len <= alloc_ceiling` (PRH_Base.v :1929; SRC-CEIL retired: no `+ 8`) from the
   string's prhtx_bvis granule bound `(s + k + 7) / 8 * 8 <= alloc_ceiling` (PRH_FnTx.v :271) *)
assert (Hck : s + k <= YM05.alloc_ceiling).
{ pose proof (Z.div_mod (s + k + 7) 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (s + k + 7) 8 ltac:(lia)).
  lia. }
split; [|split; [|split; [|exact Hcb]]].
- split; [|split; [lia|split; [cbn [length]; lia|split; [|split]]]].
  + unfold bytes_at. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j.
    destruct (Hga i ltac:(rewrite length_app; cbn; lia)) as [V R]. rewrite Hnth in V, R.
    cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact V | exact R].
  + cbn [length]. unfold amem_range in *. lia.
  + cbn [length]. apply (range_addressable_sub _ SHADOW_OFF s k); [exact Hras | lia | lia].
  + cbn [length]. intros _. apply (ts_hull_sub _ s k); [apply Hhull; lia | lia | lia | lia].
- left. left. exists s, k. split; [exact Hl | lia].
- intros a Ha. split; [lia|].
  destruct (Z.eq_dec cap 0) as [Hz|Hnz]; [lia|].
  exact (proj1 (ts_buf_apartR Rw lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap HL Hnz) s k Hl a ltac:(lia)).
Qed.
Lemma ts_src_byte : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap pre cb post,
  ts_live lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap -> bs = pre ++ cb :: post ->
  YM05.alloc_ceiling <= sp0 ->
  src_rd (PA := PA) Wc memc (s + Z.of_nat (length pre)) [cb] /\
  prhtx_kept (PA := PA) B Lam lyc Sc (s + Z.of_nat (length pre)) 1 /\
  (forall a, s + Z.of_nat (length pre) <= a < s + Z.of_nat (length pre) + 1 ->
     ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)) /\
  0 < cb < 256.
Proof. exact (ts_src_byteR (@wle SEGS)). Qed.

(* ---- esc[] (F + 32, l its first bytes) handed to tx_put (a1 = s6): a fake frame of S, its bytes usable by the
   unpoison store (the frame's shadow byte 4 is 06), its hull the frame's 8 shadow bytes ---- *)
Lemma ts_src_escR : forall (R : world SEGS -> world SEGS -> Prop)
  lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre l,
  ts_liveR R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  YM05.alloc_ceiling <= sp0 -> F mod 64 = 0 ->
  aview SEGS (w_H Wc) memc (shadow_addr F + 4) = Some 6 ->
  garr8 SEGS (mrestrict (w_H Wc) memc) (F + 32) l -> (0 < length l <= 6)%nat ->
  src_rd (PA := PA) Wc memc (F + 32) l /\ prhtx_kept (PA := PA) B Lam lyc Sc (F + 32) (Z.of_nat (length l)) /\
  (forall a, F + 32 <= a < F + 32 + Z.of_nat (length l) -> ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)).
Proof.
intros R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre l HL Hc0 HF64 Hsh6 Hga Hn.
pose proof HL as (HJ & (HWIN & HTX & _) & EF & HM).
pose proof HTX as (_ & _ & _ & (_ & _ & Hpl & _) & _).
pose proof Hpl as (_ & Htlo & _).
pose proof HJ as (HARc & _ & _ & _ & _ & HFRc & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (_ & _ & _ & Fsh).
change (fs_frame_bytes 0) with 64 in Fb2, Fb3, Fsh. rewrite <- EF in Fb1, Fb2, Fb3, Fsh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
set (n := Z.of_nat (length l)) in *.
assert (Hn' : 0 < n <= 6) by (unfold n; lia).
assert (HSA : forall x, F + 32 <= x < F + 38 -> shadow_addr x = shadow_addr F + 4).
{ intros x Hx. unfold shadow_addr. pose proof (Z.div_mod F 64 ltac:(lia)).
  assert (x / 8 = F / 8 + 4) by (rewrite Z.div_mod with (a := F) (b := 64) in Hx |- * by lia; lia). lia. }
split; [|split].
- split; [exact Hga|]. split; [lia|]. split; [lia|]. split; [|split].
  + unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg in *. lia.
  + intros x Hx. exists 6. split.
    * unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). rewrite HSA by lia. exact Hsh6.
    * unfold saddr_ok. right. pose proof (Z.div_mod F 64 ltac:(lia)). split; [|lia].
      rewrite Z.mod_eq by lia. assert (x / 8 = F / 8 + 4).
      { pose proof (HSA x ltac:(lia)) as Hs. unfold shadow_addr in Hs. lia. }
      lia.
  + intros _ s0 Hs. change (Z.of_nat (length l)) with n in Hs.
    rewrite (HSA (F + 32)) in Hs by lia. rewrite (HSA (F + 32 + n - 1)) in Hs by lia.
    assert (Hal : (shadow_addr F + 4) / 8 * 8 = shadow_addr F).
    { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod F 64 ltac:(lia)). lia. }
    rewrite Hal in Hs.
    apply s10_aview_present. replace s0 with (shadow_addr F + (s0 - shadow_addr F)) by lia.
    exact (proj1 (Fsh (s0 - shadow_addr F) ltac:(change (64 / 8) with 8; lia))).
- right. exists 0, pos. split; [exact Hin|]. intros a Ha. unfold in_zr, frame_rng. cbn [fst snd].
  change (fs_frame_bytes 0) with 64. rewrite <- EF. lia.
- intros a Ha. split; [lia|].
  destruct (Z.eq_dec cap 0) as [Hz|Hnz]; [lia|].
  exact (proj2 (ts_buf_apartR R lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre HL Hnz) a ltac:(lia)).
Qed.
Lemma ts_src_esc : forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre l,
  ts_live lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add pre ->
  YM05.alloc_ceiling <= sp0 -> F mod 64 = 0 ->
  aview SEGS (w_H Wc) memc (shadow_addr F + 4) = Some 6 ->
  garr8 SEGS (mrestrict (w_H Wc) memc) (F + 32) l -> (0 < length l <= 6)%nat ->
  src_rd (PA := PA) Wc memc (F + 32) l /\ prhtx_kept (PA := PA) B Lam lyc Sc (F + 32) (Z.of_nat (length l)) /\
  (forall a, F + 32 <= a < F + 32 + Z.of_nat (length l) -> ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)).
Proof. exact (ts_src_escR (@wle SEGS)). Qed.

(* ---- THE LOOP, at its head (TS_LH_OFF) before byte i: the bytes before it are pre, the byte is cb; both images have
   spilled F by the loop head. The text state at the head: the calls of the pieces of pre made, whatever their
   outcomes (buffer (b, cap), failed f, own and the appended ap existential) ---- *)
Definition ts_LH (i : nat) (Wc : world SEGS) (cf : config) : Prop :=
  exists lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post,
    cf = mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC + TS_LH_OFF))) memc (seg_rom SEGS)) mdc /\
    bs = pre ++ cb :: post /\ length pre = i /\
    ts_liveR RCF lyc Sc Hpc Wc memc mdc kj pos F b cap f own (TxModel.plen (ts_pieces pre)) (concat (ts_pieces pre)) ap /\
    ts_spill Wc memc F /\
    ts_lregs rg F (Z.of_nat i) /\ getr rg 11 = w64 cb.
(* the loop closes from one iteration (the image's run of the body) by the measure |bs| - i *)
Lemma ts_loop :
  (forall i Wc cf, ts_LH i Wc cf ->
     SRRCF Wc cf (fun W' c' => QF W' c' \/ exists i', (length bs - i' < length bs - i)%nat /\ ts_LH i' W' c')) ->
  forall i Wc cf, ts_LH i Wc cf -> SRRCF Wc cf QF.
Proof.
intros STEP.
exact (YSRrG.SRr'_loop SEGS YGcfRehidePost.RZ_cf nat (fun i => (length bs - i)%nat) ts_LH QF STEP).
Qed.

(* ---- THE RETURN: the side facts after every call (ks = TS_ks, add = TS_add) at the released state are the text's
   post body QT (tx_pos_post: the exact-or-frozen position; the outcome is the state's own) ---- *)
Lemma ts_post : forall lyc Sc Hpc Wc memc ly' S' regs' md' b cap f own ap,
  ts_side lyc Sc Hpc Wc memc b cap f own TS_ks TS_add ap ->
  ly' = lyc -> S' = Sc ->
  QT ly' S' Hpc Wc regs' memc md'.
Proof.
intros lyc Sc Hpc Wc memc ly' S' regs' md' b cap f own ap (HWIN & HTX & HPOS & HMN & HRO & HSTR & HDEAD & _) -> ->.
pose proof HTX as (_ & _ & _ & HPOST & HO & _ & HRM & HLED).
destruct (tx_pos_post rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 f TS_ks Sc HPOS) as (j & hist' & Hj & HpP & HjE & Hj0).
exists b, cap, f, own, ap.
split; [exact HPOST|]. split; [exact HO|]. split; [exact HDEAD|].
split; [exact (proj1 HSTR)|]. split; [exact (proj2 HSTR)|].
split; [exact HRM|].
exists j, hist'. split; [exact Hj|]. split; [exact HpP|]. split; [exact HjE|]. split; [exact Hj0 | exact HLED].
Qed.

End g.
End f.
End w.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths, module names and numbers changed; 918 of its 1024 lines of code are new or changed and 408 lines of the source are left out. *)
(* THE FREE / REALLOC MOVE (S3 phase B, a Theorem Labs lane; plan rows B-2 .. B-14, rule F12): tx_put's grow frees the old
   buffer, so the kit's ttx_put_specX / ttx_line_specX conclude SRr' segs RZ_cf with the post's journal at
   WR := wle' SEGS RZ_cf (PRH_Base fpostWb is fpostW_xbR at WR, so QF below is already the primed post). The walk
   lifts the entry journal ONCE, at the top of tl_main (ajournal_x_init_WR, at WR from the start); from there every
   journal is AJR (ajournal_xR at WR), every segment is SRW (SRr' at RZ_cf), the runners are the R forms at WR, and
   each tx_put call is Tx102Glue's s10_call_WbmR at WR. The return step (paj_ret_at, a plain SRr step that frees
   nothing) is lifted by YA0nH.SRr_SRr'. HULL (R2320): the text's `(length rp_os <= 4)%nat` is the Section-g
   hypothesis HOS, passed to each tx_put text. *)
(* INT102-READY on the kit's cut 7cdbb61b5fa0 (it replaces the signed record walk ce6b0b3e4a7c
   of a working branch 02fc33de3e82, which the cut carries as int102's copy): the same walk re-fitted to the batch kit's
   texts, a working branch 4dcec0343c87 (lib/A/PRH_FnTx.v 88468bf162d8, lib/A/PRH_Base.v
   fbe6513ce9cd; at the cut PRH_FnTx.v 88468bf162d8 and PRH_Base.v ef7c8ca98529). What the batch changed, and
   what this file does about it (each change forced by the batch text; every lemma name kept):
   - DW is gone (prh_univ_closure B CTX0; ttx_*_specX B ARx SK CTX0);
   - prhtx_trace is STATE-FREE (inU, no S) - unchanged here: tx_state's TRACE is memory-only;
   - each tx text takes a GUARDED ROOM premise `f0 = 0 -> wild_room (as_universe B) [] k (st_depot S)` and a GUARDED
     CONSUMER WINDOW `f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i k`, k = length (prhtx_evs len0 cap0 ks): Section-g
     hypotheses HROOMW / HCONS; each tx_put call gets its own from them on the DONE path (Tx102Glue.v tx_room_window,
     tx_cons_window; a call entered failed needs neither);
   - each post states DEAD `f0 = 0 -> f1 = 0` (QT's new conjunct; carried in tl_tx, folded from tx_put's own);
   - the posts are BUDGETED (fpostWbm (wbudget_if f0 [] k)): tx_put's journal is at a budget WS1 of at most its k
     fresh traces, the caller's at WS0 ++ WS1 (Tx102Glue.v s10_call_Wbm, tx_budget_fold). The cut invariant carries
     no depot conjunct in its journal: tl_live's journal starts at the REBASED entry `set_depot (st_depot Sc) S`
     (YCbqGwild.ajournal_xw_rebase), so every runner segment is unchanged; the depot's wild growth since the entry is
     tl_tx's `incl (wild_part (st_depot Sc)) (wild_part (st_depot S) ++ WS)` with `wbudget_if f0 [] (events of ks) WS`,
     which unbases at each call (ajournal_xw_unbase0) and at the return (tl_fin).
   ALSO DONE HERE: a Theorem Labs lane's S1ImgCheck cut (this file Requires S1ImgCheck for in_ro_b, not S1ImgA). *)

(* fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d, unstripped twin c90d4fa54d43): the walk of tx_line (merged
   fuzz_preset.c :432-439, body instruction-equal to the base's :398-405; entry B' 0x85c34, slot 4442 of
   lib/B/Listing_prog.v, B_entry_tx_line of lib/B/PAImg_prog.v; 27 instructions to the `ret` at 0x85c9c) against K0's
   #102 text ttx_line_specX (lib/A/PRH_FnTx.v 88468bf162d8 at the kit's cut 7cdbb61b5fa0, with the batch changes above;
   first walked against PRH_FnTx.v blob a52a78336898: the
   record's `int failed`, the run premise `f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 ks)`, ONE
   fpostWm post naming the outcome prhtx_out (DONE / FAILED AT ENTRY / REFUSED, no abort arm) and the position
   `exists j hist', ..`), at PI := prh_img_B. RELOCATED from the old-pin walk cold/h-rw-pre-5-b-txl 79ea3b230f09 (blob
   a082c52b0694, Qed at image B f8f98a95) by alreloc frozen-c4338d099cfb8025, then RE-FITTED to the #102 texts.
   MODEL: image A's walk lib/A/Prog/S10TxLine.v (cold/h-hpreset-7-walk-S10-fold, WalkS10) - its cut structure (the
   prologue to the first call, the `blez`, the loop head, the loop call, `addiw` / `bnez`, the tail). tx_line's B' body
   is the old B body word for word up to addresses (alreloc: every tx_line offset is same-code), so the cuts are at
   the same offsets 48 / 60 / 76 / 84. Every image number here is B''s, from B''s listing.
   GLUE (no local copy): lib/A/Prog/Tx102Glue.v, the image-generic #102 tx glue: tx_state / tx_pos and their _init /
   _keep / _pre / _fp / _fp_win / _fold, tx_window, tx_put_ev, tx_put_res, the no-abort call rule s10_call_Wm,
   s10_src_img, s10_rod_kept, s10_fwin_call, s10_fp_closed, s10_fp_cases.
   FORM (generic P): the walk is over an abstract memory invariant P with srr_inv_laws (every runner segment) and
   srr_inv_call (every tx_put call: a text with an m-form post); P is instantiated ONCE, in tx_line_B_holds, at
   P := fun m => memnorm SEGS mem -> memnorm SEGS m (YSRrMemnorm.v srr_inv_laws_imp / srr_inv_call_imp), where QF is the
   text's post. tx_put's text takes no memnorm at entry, so srr_inv_mn is not used.
   REPORT SITES AND OUTCOMES: tx_line has no `jal __asan_report_*` and no UBSan `unimp` on B' (and no pi_err_sites
   entry: PRH_ImgB F_tx_line). A tx_put call's refused realloc RETURNS with failed = 1 (#102): tx_put's REFUSED arm,
   after which every later put takes its FAILED arm; the outcome of each call folds into the text's prhtx_out by
   tx_state_fold (tx_out_fold's cases). The run events: the text's own guarded entry premise; each call's window is
   derived from it when the caller is still at failed = 0 (tx_window), each call's position folded by tx_put_res /
   tx_pos_fold; no extra premise.
   SEGMENTS. The engine runs the entry to the first call from tx_line's entry state; every other segment starts from a
   FRESH symbolic state built by tl_mk: atoms 0-31 the ENTRY registers, 32-63 the current ones, sp pinned to entry sp -
   32, the eleven kept callee-saved registers pinned to their entry atoms, the frame one read-only region holding the
   entry ra, s0, s1, s2.
   Numerals: 32 (LENGTH: the frame, B''s `addi sp, sp, -32` at 0x85c34; PRH_ImgB F_tx_line = 32); -8 / -16 / -24 / -32
   (LENGTH: the saved ra, s0, s1, s2, B''s `sd` offsets 24 / 16 / 8 / 0 at 0x85c38-0x85c44); 48 / 60 / 76 / 84 (DERIVED:
   B' 0x85c64 / 0x85c70 / 0x85c80 / 0x85c88 minus the entry 0x85c34); 17816 / 17828 / 17844 / 17852 (DERIVED: TL_PC =
   4 * B_prog_slot AS_tx_line = 17768 plus those offsets, each checked by vm_compute in TL_*_val); 70112 / 70496
   (DERIVED: B''s auipc / addi of .str.19 = 0x211e0 and .str.29 = 0x21360 against the listing's object 2, pa_val
   (A_OBJ 2) = 0x10000, the read-only band); 1 / 2 (LENGTH: tx_put sizes, B''s `li a2`); 10 / 32 (WORD: the bytes "\n"
   and " " read from B''s ROM by vm_compute); 28 (LENGTH: the record extent, #102); 8 / 16 (LENGTH: word, stack
   alignment); 64 (LENGTH: fpre's margin below ly_stk_hi); 4096 (LENGTH: the call rule's floor on a return address);
   2 ^ 31, 2 ^ 32, 2 ^ 40 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (DERIVED: int range, the 32-bit `addiw`,
   pa_slot_lt_ceil_b's and ret_ok_codeptr_v's offset bound, shadow, stack and sign bounds); register numbers 1-27,
   widths 5 / 64 (DERIVED: RISC-V); atom indices 2 / 8-18 / 32-63 / 243 (DERIVED: the engine's numbering, A_OBJ 2).
   No ADDRESS literal in a statement: addresses are pa_sigma / pa_val of PAImg_prog.v; the image bounds are the
   instance's pa_lo / pa_hi and the CfImg's cf_img_lo / cf_img_top (never image A's YImgTop bounds).
   RULE 24 (tx_line, image B' d663f82d, ttx_line_specX of f97c8b2f046b): proof-index tx_line 19:15:34Z (rc=0, index
   v5 built 19:12:20Z, lemma index 18:36:17Z): `6 named, 10 by address, 0 related, 3 released lemma(s), an earlier delivery 0 named,
   6 UNRELEASED cold/* file(s), 0 UNRELEASED hit(s) on live working heads`; the released hits are the plain / UBSan
   contract texts (plain 0x14f7c, ubsan 0x155d4: other images), the unreleased ones contract programs TX_LINE (lib/A,
   lib/B, lib/AZ, lib/Prog/CF), BRttStgNlF.v's Module tx_line and PresetReqAt.v's model tx_line - none a walk at B'.
   The census-1 cold/* + release/* sweep 19:16Z (15709 refs, 15268 with fuzz_preset, 2149 unique trees, 26260 blobs;
   patterns tx_line / ttx_line_specX / TxLine / 85c34 / 17768 ..) found the positive control (tx_line_B_holds with
   0x85c34) only at cold/h-rw-pre-5-r102-txB 123fe3cd3ec4, this lane's relocation; 85c34 occurs elsewhere only in B''s
   listing and image tables (PAImg_prog, PAImg_leaves, PRH_ImgB, YB1w). No released or unreleased proof of tx_line at
   B' exists; the old-pin walk 79ea3b230f09 (image B f8f98a95) is this file's donor. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Tx102Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
(* the re-hiding relation WR and its step relation (the free / realloc move) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l.
(* PRW_StepKit loads YF0v.v (new to this file's closure through it), which sets Zify's euclidean-division flag off
   GLOBALLY; the walk's lia goals (S10TxLine.v's, whose closure has no YF0v) need it on *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- the functional model: tx_line's call sizes and text (WriterValue.wind, TxModel.plen; tx_line_c.v's model,
   restated, the plain file not cited) after i of its d indent calls ---- *)
Definition tl_ks (i : nat) : list Z := [1] ++ repeat 2 i.
Definition tl_add (i : nat) : list Z := [10] ++ concat (repeat [32; 32] i).

Lemma tl_rep_snoc : forall (A : Type) (x : A) i, repeat x i ++ [x] = repeat x (S i).
Proof. intros A x i. induction i as [|i IH]; [reflexivity|]. cbn [repeat app]. rewrite IH. reflexivity. Qed.
Lemma tl_ks_S : forall i, tl_ks i ++ [2] = tl_ks (S i).
Proof. intros i. unfold tl_ks. rewrite <- app_assoc, tl_rep_snoc. reflexivity. Qed.
Lemma tl_rep_mid : forall (A : Type) (x : A) i j, repeat x i ++ x :: repeat x j = repeat x (i + S j)%nat.
Proof. intros A x i j. induction i as [|i IH]; [reflexivity|]. cbn [repeat app Nat.add]. rewrite IH. reflexivity. Qed.
(* the call sizes at a loop call: the calls done, this call, the calls to come *)
Lemma tl_ks_split : forall i j, tl_ks i ++ [2] ++ repeat 2 j = tl_ks (i + S j)%nat.
Proof. intros i j. unfold tl_ks. rewrite <- app_assoc, <- tl_rep_mid. reflexivity. Qed.
Lemma tl_concat_rep : forall (x : list Z) i, concat (repeat x i) ++ x = x ++ concat (repeat x i).
Proof.
intros x i. induction i as [|i IH]; cbn [repeat concat]; [rewrite app_nil_r; reflexivity|].
rewrite <- app_assoc, IH. reflexivity.
Qed.
Lemma tl_add_S : forall i, tl_add i ++ [32; 32] = tl_add (S i).
Proof. intros i. unfold tl_add. rewrite <- app_assoc, tl_concat_rep. reflexivity. Qed.
Lemma tl_rep_len : forall i, length (concat (repeat [32; 32] i)) = (2 * i)%nat.
Proof. induction i as [|i IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, IH. cbn [length]. lia. Qed.
Lemma tl_add_len : forall i, Z.of_nat (length (tl_add i)) = 1 + 2 * Z.of_nat i.
Proof. intros i. unfold tl_add. rewrite length_app, tl_rep_len. cbn [length]. lia. Qed.
Lemma tl_model_ks : forall d, TxModel.plen (WriterValue.wind true d) = tl_ks (Z.to_nat d).
Proof. intros d. unfold TxModel.plen, WriterValue.wind, tl_ks. cbn [map app]. rewrite map_repeat. reflexivity. Qed.
Lemma tl_model_add : forall d, concat (WriterValue.wind true d) = tl_add (Z.to_nat d).
Proof. intros d. unfold WriterValue.wind, tl_add. reflexivity. Qed.

(* ---- registers ---- *)
Lemma tl_nth_all_regs : forall k, (k < 32)%nat -> nth k all_regs 0%bv = Z_to_bv 5 (Z.of_nat k).
Proof. intros k Hk. do 32 (destruct k as [|k]; [apply bv_eq; reflexivity|]). lia. Qed.
(* the atoms 32-63 hold the current registers *)
Definition cur_atoms : list sv := SLit 0 :: map (fun i => SOff (32 + i) 0) (seq 1 31).
Lemma cur_atoms_nth : forall k, (1 <= k < 32)%nat -> nth k cur_atoms (SLit 0) = SOff (32 + k) 0.
Proof.
intros k Hk. destruct k as [|k']; [lia|]. unfold cur_atoms. cbn [nth].
pose proof (map_nth (fun i : nat => SOff (32 + i) 0) (seq 1 31) 0%nat k') as M. cbv beta in M.
rewrite (nth_indep _ (SLit 0) (SOff (32 + 0) 0)) by (rewrite length_map, length_seq; lia).
rewrite M, seq_nth by lia. first [reflexivity | f_equal; lia].
Qed.
(* the callee-saved registers tx_line never writes (gp, tp, s3-s11): pinned to their entry atoms *)
Definition TL_KEPT : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition tl_pin (sr : list sv) (r : bv 5) : list sv := sr_set sr r (SOff (Z.to_nat (bv_unsigned r)) 0).
Definition sr_L : list sv := fold_left tl_pin TL_KEPT (sr_set cur_atoms 2%bv (SOff 2 (-32))).
Lemma tl_pins : forall E rg (l : list (bv 5)) sr, regs_ok E sr rg ->
  (forall r, In r l -> r <> 0%bv /\ getr rg r = sv_denot E (SOff (Z.to_nat (bv_unsigned r)) 0)) ->
  regs_ok E (fold_left tl_pin l sr) rg.
Proof.
intros E rg l. induction l as [|r l IH]; intros sr H Hl; cbn [fold_left]; [exact H|].
apply IH; [|intros r' Hr'; apply Hl; right; exact Hr'].
destruct (Hl r (or_introl eq_refl)) as [Hr0 Hv]. unfold tl_pin. apply YI04.regs_ok_pin; assumption.
Qed.

(* the frame, as one READ-ONLY region at the entry sp (atom 2): ra, s0, s1, s2 of the entry at -8 .. -32 *)
Definition tl_chunks : list YP09.chunk :=
  [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition tl_frame_region : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 0 0 tl_chunks.

(* ---- bytes ---- *)
Lemma tl_low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
  Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hl|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma tl_U_atom_mod : forall E n, U E (SOff n 0) mod 2 ^ 64 = bv_unsigned (ew E n).
Proof.
intros E n. rewrite U_SOff, Z.add_0_r. pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H.
rewrite zcanon_id by (unfold M64; lia). apply Z.mod_small. lia.
Qed.

(* ---- the loop counter's `addiw s0, s0, -1` and the `blez` test, as numbers ---- *)
Lemma tl_swrap32_m1 : forall v, 1 <= v < 2 ^ 31 -> bv_swrap 32 (v + (2 ^ 32 - 1)) = v - 1.
Proof.
intros v Hv. unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
replace (v + (2 ^ 32 - 1) + 2 ^ 31) with ((v + 2 ^ 31 - 1) + 1 * 2 ^ 32) by ring.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma tl_addw_m1 : forall E n v, ew E n = Z_to_bv 64 v -> 1 <= v < 2 ^ 31 ->
  U E (SAluw ALU_ADD (SOff n 0) (SLit (-1))) = v - 1.
Proof.
intros E n v Hn Hv. rewrite U_of_S, S_SAluw, (U_atom E n v Hn ltac:(lia)), U_SLit.
replace (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1) by (vm_compute; reflexivity).
rewrite (Z.mod_small v (2 ^ 32)) by lia. cbn [zalu_raw]. rewrite tl_swrap32_m1 by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
Lemma tl_denot_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma tl_ge0 : forall x, 0 <= x < 2 ^ 63 -> branch_taken BC_GE (Z_to_bv 64 0) (Z_to_bv 64 x) = (x <=? 0).
Proof.
intros x Hx. cbn [branch_taken]. unfold bv_lts.
rewrite !YK11.bv_signed_small by (rewrite unsigned_lit_small by lia; lia).
rewrite !unsigned_lit_small by lia. destruct (Z.ltb_spec 0 x); destruct (Z.leb_spec x 0); cbn [negb]; first [reflexivity | lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

(* tx_line's entry and resume points, as byte offsets from the listing's base (DERIVED: B_prog_slot) *)
Definition TL_PC : Z := 4 * Z.of_nat (B_prog_slot AS_tx_line).
Lemma TL_PC_val : BASE + TL_PC = SIGMA AS_tx_line.
Proof. vm_compute. reflexivity. Qed.
Definition TL_R1 : Z := TL_PC + 48.     (* B 0x85c64: the first call's return, `blez s0` *)
Definition TL_LH : Z := TL_PC + 60.     (* B 0x85c70: the loop head, `li a2, 2` *)
Definition TL_R2 : Z := TL_PC + 76.     (* B 0x85c80: the loop call's return, `addiw s0, s0, -1` *)
Definition TL_TAIL : Z := TL_PC + 84.   (* B 0x85c88: the epilogue *)
Lemma TL_R1_val : TL_R1 = 17816. Proof. vm_compute. reflexivity. Qed.
Lemma TL_LH_val : TL_LH = 17828. Proof. vm_compute. reflexivity. Qed.
Lemma TL_R2_val : TL_R2 = 17844. Proof. vm_compute. reflexivity. Qed.
Lemma TL_TAIL_val : TL_TAIL = 17852. Proof. vm_compute. reflexivity. Qed.
(* the two jal return pcs lie below the ceiling, as the callee text's fpre asks (raZ < YM05.alloc_ceiling):
   PRW_StepKit.pa_slot_lt_ceil_b on each CLOSED slot, here and not inside a walk proof *)
Lemma tl_ceil_R1 : BASE + TL_R1 < YM05.alloc_ceiling.
Proof. rewrite TL_R1_val. apply (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA)); [lia | vm_compute; reflexivity]. Qed.
Lemma tl_ceil_R2 : BASE + TL_R2 < YM05.alloc_ceiling.
Proof. rewrite TL_R2_val. apply (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA)); [lia | vm_compute; reflexivity]. Qed.
(* the read-only literals passed to tx_put (DERIVED: image B's `auipc a0, 0xfff9b` / `addi` at 0x85c50 / 0x85c54 and
   0x85c68 / 0x85c6c, resolved by the listing against its object 2, the read-only band) *)
Definition STR19 : Z := VAL (A_OBJ 2) + 70112.   (* B .str.19 (0x211e0), "\n" *)
Definition STR29 : Z := VAL (A_OBJ 2) + 70496.   (* B .str.29 (0x21360), "  " *)

Definition TL_Bx : sv := SOff 32 0.
Definition TL_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition tl_regions : smem := [ stack_region 32 ].
Definition tl_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_tl : sstate := mkSS TL_PC sr_atoms tl_regions None tl_facts.
Definition tl_SH : list shent := [].
Definition TL_EI (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs []).
(* the fresh-segment environment: atoms 0-31 the entry registers regs0, 32-63 the current registers rg *)
Definition TE (regs0 rg : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs0 (map (getr rg) all_regs)).
Definition ss_L (pc : Z) : sstate := mkSS pc sr_L [tl_frame_region] None tl_facts.

Lemma te_env : forall regs0 rg, img_env VAL A_LIM (TE regs0 rg).
Proof. intros. unfold TE. apply Eimg_env. Qed.
Lemma te_agree : forall regs0 rg, env_agree 32 (Ereg regs0 (map (getr rg) all_regs)) (TE regs0 rg).
Proof. intros regs0 rg. split; [intros n Hn; unfold TE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma te_entry : forall regs0 rg (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew (TE regs0 rg) n = getr regs0 r.
Proof.
intros regs0 rg r n Hn. pose proof (u5_range r). unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hn.
Qed.
Lemma te_cur : forall regs0 rg (r : bv 5) k, Z.of_nat k = bv_unsigned r -> ew (TE regs0 rg) (32 + k) = getr rg r.
Proof.
intros regs0 rg r k Hk. pose proof (u5_range r). unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. rewrite (nth_indep _ _ (getr rg 0%bv)) by (rewrite length_map; cbn; lia).
rewrite map_nth. rewrite tl_nth_all_regs by lia. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. rewrite Hk. apply Z.mod_small. lia.
Qed.
Lemma te_den_entry : forall regs0 rg n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (TE regs0 rg) (SOff n 0) = getr regs0 r.
Proof. intros regs0 rg n r Hn. cbn [sv_denot]. rewrite (te_entry regs0 rg r n Hn), Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma te_den_cur : forall regs0 rg n k (r : bv 5), n = (32 + k)%nat -> Z.of_nat k = bv_unsigned r ->
  sv_denot (TE regs0 rg) (SOff n 0) = getr rg r.
Proof. intros regs0 rg n k r -> Hk. cbn [sv_denot]. rewrite (te_cur regs0 rg r k Hk), Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma tl_obj2 : forall E k, img_env VAL A_LIM E -> sv_denot E (SOff 243 k) = Z_to_bv 64 (VAL (A_OBJ 2) + k).
Proof.
intros E k HE. cbn [sv_denot]. rewrite (HE 243%nat ltac:(unfold A_TEXT, A_LIM; lia)).
reflexivity.
Qed.
Lemma te_regs_ok : forall regs0 rg, regs_ok (TE regs0 rg) cur_atoms rg.
Proof.
intros regs0 rg r. unfold sr_get. pose proof (u5_range r) as Hr.
destruct (bv_eqb r 0) eqn:Hz.
- apply bv_eqb_eq in Hz. subst r. rewrite getr_zero. reflexivity.
- assert (Hne : bv_unsigned r <> 0).
  { intros H0. assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in Hz. discriminate. }
  unfold ridx. rewrite cur_atoms_nth by lia. cbn [sv_denot]. rewrite Z.add_0_r.
  rewrite (te_cur regs0 rg r (Z.to_nat (bv_unsigned r))) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* a region's chunk read back as concrete bytes (as S10TxLine.v's tl_field, image A) *)
Lemma tl_field : forall E m n b cs lo hi wlo whi od (w : N) e,
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
rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply tl_low_byte_mod; [lia | exact Hk].
Qed.
Lemma tl_chunk : forall E m base off (n : N) e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) ->
  (Z.of_N n <= 8) -> val_mem SEGS m (base + off) (N.to_nat n) v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n e)).
Proof. intros. eapply chunk_ok_val; eassumption. Qed.
Lemma tl_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* a register the run did not write keeps its value; aregs_preserved by register *)
Lemma tl_ap : forall rA rB, aregs_preserved rA rB -> forall r : bv 5, acallee_saved (bv_unsigned r) -> getr rB r = getr rA r.
Proof. intros rA rB H r Hr. pose proof (H _ Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. Qed.

(* the register of a symbolic state, as the denotation of its (computed) entry *)
Ltac tlreg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.
(* memory a run did not write: nothing, for a run from a fresh state (its only region is read-only) *)
Ltac tl_same HFr H :=
  lazymatch type of HFr with frame_of ?Ex ?rs ?mA ?mB =>
  assert (H : forall x, mB x = mA x) by (intros x; apply HFr; intros (r & Hin & Hr); vm_compute in Hin;
     repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi tl_frame_region] in Hr; lia |]); destruct Hin) end.
Ltac tl_awr_ro :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* FuzzStrdup.v's sd_awr (c-omx-alloc), at the window journal: the stack writes of tx_line's frame lie in
   [sp - 32, sp), sp = sp0' - dw *)
Ltac tl_awr rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
| cbn [YP09.r_wlo stack_region]; lia
| cbn [YP09.r_whi stack_region]; lia
| apply awr_ok_nil ].

(* ---- image facts of B' (S1ImgB.v, computed on B''s segments; the names of Tx102Glue.v's Section hypotheses) ---- *)
(* alloc.c's statics lie in the image *)
Lemma HPST : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. exact S1ImgB.pst_in_img_B. Qed.
(* alloc.c's statics are not read-only *)
Lemma HPSTro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. exact S1ImgB.pst_not_ro_B. Qed.

(* ---- INSTANCE WITNESSES (unit ruling 16:45Z) of the image premises this file takes as Section hypotheses over an
   abstract B (zs_aligned and tl_lit_img) or an abstract CfImg (tl_img_cf_box), closed by computation at image B''s
   asyms YD2l.TfibB (generated from fuzz_preset.asan-ubsan, the unstripped twin c90d4fa54d43 of d663f82d) and B''s
   CfImg CfImgB.CfImg_B; and the instance's own bound fact tl_img_box (Tx102Glue.v's img_box at PI_prog_B) ---- *)
(* the boolean read-only checker's soundness (S1ImgCheck.v in_ro_b, image-free; as BTxValue.v's s10v_in_ro_b_sound) *)
Lemma tl_in_ro_b_sound : forall segs rlo rhi a, S1ImgCheck.in_ro_b segs rlo rhi a = true -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold S1ImgCheck.in_ro_b in H. apply orb_prop in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs|]. split; [exact H0 | lia].
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
(* a byte in no range of a list, by a boolean search *)
Lemma tl_not_in_zr_b : forall a (l : list (Z * Z)),
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = false -> ~ Exists (in_zr a) l.
Proof.
intros a l H HE. apply Exists_exists in HE as (r & Hin & Hr). unfold in_zr in Hr.
assert (Ht : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
{ apply existsb_exists. exists r. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
congruence.
Qed.
Lemma tl_STR19_val : STR19 = 0x211e0. Proof. vm_compute. reflexivity. Qed.
Lemma tl_STR29_val : STR29 = 0x21360. Proof. vm_compute. reflexivity. Qed.
(* one byte of a literal: read-only, not owned, not errno, its granule's const-shadow cell v (the cell searched in
   YF0m.Tfib_const_shadow, the layout-free tail of TfibB's as_const) *)
Lemma tl_lit_byte_TfibB : forall a v, 0 <= a < 2 ^ 47 ->
  S1ImgCheck.in_ro_b SEGS RLO RHI a = true ->
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) YF0m.Tfib_owned_static = false ->
  ~ (YF0m.TFIB_ERRNO <= a < YF0m.TFIB_ERRNO + 4) ->
  In (z1 (ANum (shadow_addr a)) v) YF0m.Tfib_const_shadow -> (v = 0 \/ a mod 8 < v < 8) ->
  in_roP SEGS RLO RHI a /\ ~ Exists (in_zr a) (as_owned_static YD2l.TfibB) /\
  ~ (as_errno YD2l.TfibB <= a < as_errno YD2l.TfibB + 4) /\ ro_shadow_ok YD2l.TfibB a.
Proof.
intros a v _ Hro Hown Herr Hc Hv.
split; [exact (tl_in_ro_b_sound _ _ _ a Hro)|].
split; [cbn [as_owned_static YD2l.TfibB]; exact (tl_not_in_zr_b a _ Hown)|].
split; [cbn [as_errno YD2l.TfibB]; exact Herr|].
right. exists v. split; [|exact Hv].
intros ly. cbn [as_const YD2l.TfibB]. unfold YF0m.Tfib_const.
apply in_or_app. right. apply in_or_app. right. exact Hc.
Qed.
(* WITNESS of tl_lit_img: .str.19 ("\n", 0x211e0, cell shadow 2) and .str.29 ("  ", 0x21360, cell shadow 3); the
   kept_img bounds are the instance's pa_lo / pa_hi, the shadow cells computed (vm_compute), not written *)
Lemma tl_lit_img_TfibB : kept_img (PA := PA) YD2l.TfibB STR19 1 /\ kept_img (PA := PA) YD2l.TfibB STR29 2.
Proof.
rewrite tl_STR19_val, tl_STR29_val. unfold kept_img.
assert (HB : @pa_lo _ _ PA + 64 <= 0x211e0 /\ 0x21360 + 2 + 64 <= @pa_hi _ _ PA)
  by (vm_compute; split; intro H; discriminate H).
destruct HB as [HB1 HB2].
split; (split; [lia|]); (split; [lia|]); intros a Ha.
- assert (Ea : a = 0x211e0) by lia. subst a.
  apply (tl_lit_byte_TfibB _ 2); [lia | vm_compute; reflexivity | vm_compute; reflexivity | unfold YF0m.TFIB_ERRNO; lia | |
    right; split; reflexivity].
  vm_compute. repeat (first [left; reflexivity | right]).
- assert (Ea : a = 0x21360 \/ a = 0x21361) by lia. destruct Ea as [-> | ->];
    (apply (tl_lit_byte_TfibB _ 3); [lia | vm_compute; reflexivity | vm_compute; reflexivity | unfold YF0m.TFIB_ERRNO; lia | |
      right; split; reflexivity]);
    vm_compute; repeat (first [left; reflexivity | right]).
Qed.
(* WITNESS of zs_aligned: TfibB's zero-shadow ranges are granule-aligned *)
Lemma tl_zs_aligned_TfibB : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow YD2l.TfibB).
Proof.
cbn [as_zero_shadow YD2l.TfibB].
assert (H : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) YF0m.Tfib_zero_shadow = true)
  by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1, H2. split; assumption.
Qed.
(* the instance's kept_img bounds lie in the low half (Tx102Glue.v's img_box at PI_prog_B: closed) *)
Lemma tl_img_box : 4096 <= @pa_lo _ _ PA /\ @pa_hi _ _ PA <= kLowMemEnd.
Proof. vm_compute. split; intro H; discriminate H. Qed.
(* WITNESS of tl_img_cf_box at B''s CfImg: its bounds hold the instance's kept_img bounds *)
Lemma tl_img_cf_box_B : @cf_img_lo CfImgB.CfImg_B <= @pa_lo _ _ PA /\ @pa_hi _ _ PA <= @cf_img_top CfImgB.CfImg_B.
Proof. vm_compute. split; intro H; discriminate H. Qed.
(* GUARDS (the wrong-image trap, 19:3xZ): every witness above is stated over SEGS / RLO / RHI of PI_prog_B and over
   YD2l.TfibB / CfImgB.CfImg_B; these are image B''s, named fully qualified *)
Lemma tl_segs_B : SEGS = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
Proof. reflexivity. Qed.
Lemma tl_segs_B_img : SEGS = OSSVerify.omx_clap_core.fuzz_preset.images.AsanUbsan.M.loaded_segments.
Proof. reflexivity. Qed.
Locate Img0.rsegs.
Locate TfibB.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* THE ONE RELATION of this walk (F12): the journal from the entry at WR, every segment at SRW *)
#[local] Notation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation SRW := (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx WR).
#[local] Notation WRrefl := (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRtrans := (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf).
(* ---- the Section hypotheses Tx102Glue.v's lemmas carry (same names, same statements; owners there) ---- *)
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B; ARcf gives it by amc_syms / aso_zshadow, YG0f.v:191) *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN (owner h-mani-a8, rule 18:56Z: img_shadow_vis_cf over the PER-INSTANCE CfImg bounds, restated over
   ARx; B' instance lib/AU/AImgShadowVisCfB.v tfib_img_shadow_vis_cf_B, cold/h-mani-a8-alloc102) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> cf_img_lo <= a < cf_img_top ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the CfImg bounds hold the instance's kept_img bounds (witness tl_img_cf_box_B at CfImgB.CfImg_B) *)
Hypothesis tl_img_cf_box : cf_img_lo <= @pa_lo _ _ PA /\ @pa_hi _ _ PA <= cf_img_top.
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B, route (a) of PRH_Base.v, as BTxValue.v's tv_lit_img):
   the two literals tx_line passes to tx_put on image B' (.str.19 "\n" at length 1, .str.29 "  " at length 2) are
   image strings, kept_img, at the length passed (witness tl_lit_img_TfibB) *)
Hypothesis tl_lit_img : kept_img (PA := PA) B STR19 1 /\ kept_img (PA := PA) B STR29 2.
(* the callee's text (the Tx part, PRH_FnTx.v), at the caller's own allocator-trace closure parameter CTX0 (the batch: the
   cursor run word DW is gone) *)
Variables (CTX0 : list (list Z)).
Hypothesis TXPUT : ttx_put_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.

Lemma tl_entry : forall STK ly S Hp W regs mem md ch,
afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 32 <= STK ->
st_ok_pi SEGS VAL (TL_EI regs) ss_tl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TL_PC)) mem (seg_rom SEGS)))
/\ sh_ok SEGS TL_Bx tl_SH (TL_EI regs) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch HPRE H32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := TL_EI regs) in *.
assert (E2 : ew E 2 = getr regs 2)
by (subst E; unfold TL_EI; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_tl. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold tl_regions, stack_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [tl_regions pairwise_disjoint all_disjoint]. exact (conj I I).
+ split; [|split; [exact I | exact I]].
cbn [tl_facts f_atoms atoms_ok].
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
- unfold sh_ok, tl_SH. apply Forall_nil.
Qed.

(* ==== THE WALK OVER A GENERIC MEMORY INVARIANT P (YSRrMemnorm.v's form): P crosses every runner segment by its laws
   (srr_inv_laws) and every tx_put call (a text with an m-form post) by srr_inv_call; it is instantiated ONCE, in
   tx_line_B_holds, at P := fun m => memnorm SEGS mem -> memnorm SEGS m. tx_put's text takes no memnorm at entry, so
   srr_inv_mn is not needed. ==== *)
Section p.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Hypothesis PCALL : YSRrMemnorm.srr_inv_call SEGS P.

Section g.
(* ---- the entry: the text's binders and premises (ttx_line_specX), and P at the entry memory ---- *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (dw t d b0 len0 cap0 f0 own : Z) (txt : list Z) (Lam : list (Z * Z))
  (peak cnt fail ran most : Z).
Hypothesis HPRE : afn_pre_x SEGS B ARx (@STK_tx_line prh_img_B) ly S Hp W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem).
Hypothesis HHI : spZ regs + 64 <= ly_stk_hi ly.
Hypothesis HFRM : frm_zero (@YK11.fp_csr fx).
Hypothesis HCL : prh_univ_closure (PI := prh_img_B) B CTX0.
Hypothesis HROOM : room_live_cf S.
Hypothesis HPOS : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S.
(* HULL (R2320, plan row B-14): the run has at most 4 calls, the text's premise, passed to each tx_put text *)
Hypothesis HOS : (length rp_os <= 4)%nat.
(* the batch's guarded room (the wild budget's entry room) and guarded consumer window *)
Hypothesis HROOMW : f0 = 0 ->
  YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 (TxModel.plen (WriterValue.wind true d))))
    (st_depot S).
Hypothesis HCONS : f0 = 0 ->
  prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 (TxModel.plen (WriterValue.wind true d)))).
Hypothesis HEVS : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 (TxModel.plen (WriterValue.wind true d))).
Hypothesis H10 : getr regs 10 = w64 t.
Hypothesis H11 : getr regs 11 = w64 d.
Hypothesis Hd : 0 <= d <= 2 ^ 31 - 1.
Hypothesis HFWIN : fwin (PA := PA) ly W regs mem dw.
Hypothesis HPLACE : prhtx_place (PA := PA) ly S W regs mem dw t.
Hypothesis HTRACE : prhtx_trace (PI := prh_img_B) (PA := PA) B ly W mem t.
Hypothesis HREC : prhtx_rec (PA := PA) W mem t b0 len0 cap0 f0.
Hypothesis HINV : prhtx_inv (PA := PA) B Lam ly S W mem b0 len0 cap0 txt.
Hypothesis HLEN : len0 + 1 + 2 * d + 1 <= 2 ^ 28.
Hypothesis HLED : prh_ledger (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own.
Hypothesis HLIVE : blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX.
Hypothesis HMAX : 2 * (len0 + 1 + 2 * d + 1) < cf_malloc_max.
Hypothesis HP0 : P mem.

#[local] Notation sp0 := (spZ regs).
#[local] Notation STKL := (@STK_tx_line prh_img_B).
#[local] Notation FP0 := (prhtx_fp t b0 cap0).
#[local] Notation TL_N := (Z.to_nat d).
(* the run premise at the model's call sizes *)
Lemma tl_evs : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 (tl_ks TL_N)).
Proof. rewrite <- tl_model_ks. exact HEVS. Qed.
(* the room and the window at the model's call sizes *)
Lemma tl_roomw : f0 = 0 ->
  YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 (tl_ks TL_N))) (st_depot S).
Proof. rewrite <- tl_model_ks. exact HROOMW. Qed.
Lemma tl_consw : f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 (tl_ks TL_N))).
Proof. rewrite <- tl_model_ks. exact HCONS. Qed.

(* ---- the text's conclusion (its post body: the outcome prhtx_out, DEAD and the position; the batch) ---- *)
Definition QT : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    exists b1 cap1 f1 own' (pre : list Z),
    prhtx_post (PA := PA) B Lam regs dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
      (txt ++ pre) /\
    prhtx_out f0 f1 own own' b0 cap0 b1 cap1
      (TxModel.tx_capf len0 cap0 (TxModel.plen (WriterValue.wind true d))) (concat (WriterValue.wind true d)) pre /\
    (f0 = 0 -> f1 = 0) /\
    room_live_cf S' /\
    exists j hist', (j <= length (prhtx_evs len0 cap0 (TxModel.plen (WriterValue.wind true d))))%nat /\
       PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 hist' S' /\
       (f0 = 0 -> f1 = 0 -> j = length (prhtx_evs len0 cap0 (TxModel.plen (WriterValue.wind true d)))) /\
       (f0 <> 0 -> j = 0%nat) /\
    prh_ledger (PI := prh_img_B) (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own'.
(* the text's post with P for fQmn's memnorm keep (at the top's P it IS fpostWbm .. QT: fQmn mem QT unfolds to it);
   the batch: BUDGETED at wbudget_if f0 [] (the events of the text's own puts); no abort arm *)
Definition QF : world SEGS -> config -> Prop := fun W' c' =>
  fpostWb (PI := prh_img_B) (PA := PA) B ARx SK
    (wbudget_if f0 [] (length (prhtx_evs len0 cap0 (TxModel.plen (WriterValue.wind true d)))))
    STKL dw FP0 regs ly S Hp W mem md
    (fun ly' S' Hp' W' regs' mem' md' => QT ly' S' Hp' W' regs' mem' md' /\ P mem') W' c'.

(* ---- the facts every segment carries ---- *)
(* the caller window outside FP is the entry's (fpostW's clause) *)
Definition tl_win (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  forall a, sp0 <= a < sp0 + dw -> ~ inFP FP0 a -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H W) mem a.
(* the frame holds the entry ra, s0, s1, s2 *)
Definition tl_frame (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp0 + -32) 8%nat (bv_unsigned (getr regs 18)) /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp0 + -24) 8%nat (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp0 + -16) 8%nat (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp0 + -8) 8%nat (bv_unsigned (getr regs 1)).
(* the text state after puts of sizes ks that would append add: Tx102Glue.v's tx_state at the buffer (b, cap), failed
   fc, own ow, pre appended; its position tx_pos; P of the current memory (in place of a memnorm keep); DEAD so
   far; and the depot's wild growth since the entry, within a budget of at most the events of ks (the batch) *)
Definition tl_tx (b cap fc ow : Z) (ks add pre : list Z) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) : Prop :=
  tx_state (PI := prh_img_B) (PA := PA) B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own
    b cap fc ow ks add pre lyc Sc Hpc Wc memc /\
  tx_pos rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 fc ks Sc /\
  P memc /\
  (f0 = 0 -> fc = 0) /\
  exists WS, incl (wild_part (as_universe B) (st_depot Sc)) (wild_part (as_universe B) (st_depot S) ++ WS) /\
    wbudget_if f0 [] (length (prhtx_evs len0 cap0 ks)) WS.
(* the live state after i indent calls with j to come: the journal from the entry at WR, REBASED to the current depot
   (YCbqGwild.ajournal_xw_rebaseR: no depot conjunct in the cut journal), the window, the frame, the text state *)
Definition tl_live (i j : nat) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kc b : Z) : Prop :=
  AJR (STKL + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [] lyc Sc Hpc Wc memc mdc kc /\
  tl_win Wc memc /\ tl_frame Wc memc /\ (i + j = TL_N)%nat /\
  exists cap fc ow pre, tl_tx b cap fc ow (tl_ks i) (tl_add i) pre lyc Sc Hpc Wc memc.
(* the registers a fresh segment needs: sp = entry sp - 32, gp, tp, s3-s11 the entry's *)
Definition tl_regs (rg : bvmap 5 word) : Prop :=
  getr rg 2 = w64 (sp0 - 32) /\ forall r, In r TL_KEPT -> getr rg r = getr regs r.

Ltac tl_csv := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.
Lemma tl_regs_pres : forall rA rB, tl_regs rA -> aregs_preserved rA rB -> tl_regs rB.
Proof.
intros rA rB (R2 & RK) HP. split.
- rewrite (tl_ap rA rB HP 2%bv) by tl_csv. exact R2.
- intros r Hr. rewrite (tl_ap rA rB HP r); [exact (RK r Hr)|].
  cbv [TL_KEPT In] in Hr. repeat (destruct Hr as [<- | Hr]; [tl_csv|]). destruct Hr.
Qed.
Lemma tl_regs_post : forall E extra ss (Hh : word -> bool) ms,
  st_ok SEGS E ss (restrict Hh ms) -> env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) TL_KEPT = true ->
  sr_get (ss_regs ss) 2%bv = SOff 2 (-32) ->
  tl_regs (ms_regs ms).
Proof.
intros E extra ss Hh ms HS HA Hk H2. split.
- rewrite (st_ok_restrict_reg SEGS Hh E ss ms 2%bv HS), H2. cbn [sv_denot].
  rewrite (proj1 HA 2%nat ltac:(lia)), (ew_Ereg_nat regs extra 2 2%bv eq_refl). unfold w64, spZ. f_equal; lia.
- intros r Hr. exact (regs_kept_of_st_ok SEGS E ss (restrict Hh ms) regs extra TL_KEPT HS HA Hk r Hr).
Qed.

Lemma tl_top : forall lyc Sc Hpc Wc memc mdc kc,
  AJR (STKL + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  ly_top lyc <= 2 ^ 47.
Proof.
intros lyc Sc Hpc Wc memc mdc kc HJ.
pose proof (ajxR_ly HJ) as Hly. pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
lia.
Qed.
Lemma tl_hi : forall lyc Sc Hpc Wc memc mdc kc,
  AJR (STKL + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [] lyc Sc Hpc Wc memc mdc kc ->
  ly_stk_hi lyc = ly_stk_hi ly.
Proof.
intros lyc Sc Hpc Wc memc mdc kc HJ.
pose proof (ajxR_ly HJ) as Hly. pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _). exact Ehi.
Qed.

Lemma tl_frame_move : forall (W1 W2 : world SEGS) m1 m2,
  (forall a, sp0 - 32 <= a < sp0 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  tl_frame W1 m1 -> tl_frame W2 m2.
Proof.
intros W1 W2 m1 m2 HA (F1 & F2 & F3 & F4).
assert (M : forall a (n : nat) v, sp0 - 32 <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (mrestrict (w_H W1) m1) a n v -> val_mem SEGS (mrestrict (w_H W2) m2) a n v).
{ intros a n v H1 H2 HV k Hk. rewrite (mbyte_of_aview SEGS (w_H W1) (w_H W2) m1 m2 (a + Z.of_nat k)) by (apply HA; lia).
  exact (HV k Hk). }
split; [|split; [|split]]; (apply M; [lia | cbn; lia |]); assumption.
Qed.

(* across a run from a fresh state, which writes nothing, with P of the run's end memory *)
Lemma tl_live_same : forall i j lyc Sc Hpc Wc memc memc' mdc mdc' kc kc' b,
  tl_live i j lyc Sc Hpc Wc memc mdc kc b ->
  AJR (STKL + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [] lyc Sc Hpc Wc memc' mdc' kc' ->
  (forall x, mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  P memc' ->
  tl_live i j lyc Sc Hpc Wc memc' mdc' kc' b.
Proof.
intros i j lyc Sc Hpc Wc memc memc' mdc mdc' kc kc' b
  (HJ & HW & HFR & Hij & (cap & fc & ow & pre & (HTX & HPS & _ & HDEAD & HWS)))
  HJ' Hm HK.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
assert (HA : forall a, aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a)
  by (intros a; unfold aview, mbyte; rewrite Hm; reflexivity).
split; [exact HJ'|]. split; [intros a Ha Hn; rewrite HA; exact (HW a Ha Hn)|].
split; [apply (tl_frame_move Wc Wc memc memc'); [intros a _; exact (HA a) | exact HFR]|].
split; [exact Hij|].
exists cap, fc, ow, pre.
split; [|split; [exact HPS | split; [exact HK | split; [exact HDEAD | exact HWS]]]].
apply (tx_state_keep B ARx LAWS HPST Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own
  b cap fc ow _ _ pre lyc Sc Hpc Wc memc memc' mdc sp0 sp0 HTX (ajxR_ar HJ) (tl_top _ _ _ _ _ _ _ HJ) ltac:(lia) ltac:(lia)).
intros x _. exact (Hm x).
Qed.

(* ---- a FRESH segment state at pc from concrete facts ---- *)
Lemma tl_mk : forall pc rg (Wc : world SEGS) memc, tl_regs rg -> tl_frame Wc memc ->
  st_ok_pi SEGS VAL (TE regs rg) (ss_L pc) (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS TL_Bx [] (TE regs rg) (mrestrict (w_H Wc) memc).
Proof.
intros pc rg Wc memc (R2 & RK) (F1 & F2 & F3 & F4).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (Usp : bv_unsigned (ew (TE regs rg) 2) = sp0) by (rewrite (te_entry regs rg 2%bv 2) by reflexivity; reflexivity).
assert (VR : forall r : bv 5, 0 <= bv_unsigned (getr regs r) < 2 ^ (8 * Z.of_N 8)).
{ intros r. pose proof (bv_unsigned_in_range 64 (getr regs r)) as X. change (bv_modulus 64) with (2 ^ 64) in X.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact X. }
rewrite restrict_mkst_fx. split; [|unfold sh_ok; apply Forall_nil].
unfold ss_L. apply pa_entry_st_ok_full.
- unfold sr_L. apply tl_pins.
  + apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |].
    rewrite R2. cbn [sv_denot]. rewrite Usp. unfold w64. f_equal; lia.
  + intros r Hr. split.
    * cbv [TL_KEPT In] in Hr. repeat (destruct Hr as [<- | Hr]; [intros X; discriminate X|]). destruct Hr.
    * rewrite (RK r Hr). symmetry. apply te_den_entry. pose proof (u5_range r). lia.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold tl_frame_region, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
  unfold tl_chunks. repeat apply Forall_cons; try apply Forall_nil.
  + apply (tl_chunk _ _ _ (-32) 8 (SOff 18 0) (bv_unsigned (getr regs 18)));
      [rewrite (te_den_entry regs rg 18 18%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned | apply VR | cbn; lia | exact F1].
  + apply (tl_chunk _ _ _ (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)));
      [rewrite (te_den_entry regs rg 9 9%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned | apply VR | cbn; lia | exact F2].
  + apply (tl_chunk _ _ _ (-16) 8 (SOff 8 0) (bv_unsigned (getr regs 8)));
      [rewrite (te_den_entry regs rg 8 8%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned | apply VR | cbn; lia | exact F3].
  + apply (tl_chunk _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)));
      [rewrite (te_den_entry regs rg 1 1%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned | apply VR | cbn; lia | exact F4].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [tl_facts f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
Qed.

(* the frame read back from the prologue's symbolic state *)
Lemma tl_frame_of_st : forall E ss (Wc : world SEGS) ms wlo whi,
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> env_agree 32 (Ereg regs []) E ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) (-32) 0 wlo whi tl_chunks) ->
  tl_frame Wc (ms_mem ms).
Proof.
intros E ss Wc ms wlo whi HS HA Hn0.
assert (EE : forall (r : bv 5) n, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros r n Hn Hr. rewrite (proj1 HA n Hn). exact (ew_Ereg_nat regs [] n r Hr). }
destruct (st_ok_mem_ok SEGS E ss _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hn0)) as HR. cbn [ms_mem restrict] in HR.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%bv 2%nat) by (lia || reflexivity); reflexivity).
assert (F : forall od n (r : bv 5), In (YP09.mkChunk od (CVal 8 (SOff n 0))) tl_chunks -> (n < 32)%nat ->
  Z.of_nat n = bv_unsigned r ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (sp0 + od) 8%nat (bv_unsigned (getr regs r))).
{ intros od n r Hin Hn Hr. pose proof (tl_field E _ 2 sp0 _ _ _ _ _ od 8 (SOff n 0) HR Usp Hin ltac:(cbn; lia)) as V.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V. rewrite tl_U_atom_mod, (EE r n Hn Hr) in V. exact V. }
split; [|split; [|split]];
  [apply (F (-32) 18%nat 18%bv) | apply (F (-24) 9%nat 9%bv) | apply (F (-16) 8%nat 8%bv) | apply (F (-8) 1%nat 1%bv)];
  first [unfold tl_chunks; cbn [In]; tauto | lia | reflexivity].
Qed.

(* ---- THE tx_put CALL (Tx102Glue.v s10_call_Wbm with TXPUT, the batch's budgeted text; tx_state_pre / tx_window at the
   call memory; the callee's guarded room and consumer window from the text's own on the DONE path (tx_room_window,
   tx_cons_window); tx_put's post (its three arms, DEAD and two position conjuncts) through tx_put_res, folded by
   tx_state_fold_w / tx_pos_fold, its budget by tx_budget_fold; P across the call by srr_inv_call), from the state a
   run leaves at a `jal tx_put` with sp = entry sp - 32: a literal source of n bytes, the return pc below the ceiling,
   the guarded run premise, room and window split as ks (done) ++ [n] (this call) ++ rest (to come), the text state
   with the call of n bytes next; the live state with the call done (no abort arm; a refused grow is its REFUSED arm,
   a call entered failed its FAILED arm). The journal enters REBASED (tl_live's form, at WR), is unbased for the call
   (ajournal_xw_unbase0R) and leaves rebased at the callee's end depot (ajournal_xw_rebaseR); the call is
   s10_call_WbmR at WR, so the segment is SRW ---- *)
Lemma tl_call : forall (Wc : world SEGS) E ss ms mdc lyc Sc Hpc kc b cap fc ow ks add pre n rest s src raw,
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
  AJR (STKL + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [] lyc Sc Hpc Wc (ms_mem ms) mdc kc ->
  getr (ms_regs ms) 2 = sv_denot E (SOff 2 (-32)) -> ew E 2 = getr regs 2 ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  s0Z (ms_regs ms) < YM05.alloc_ceiling ->
  getr (ms_regs ms) 10 = w64 t -> getr (ms_regs ms) 11 = w64 s -> getr (ms_regs ms) 12 = w64 n ->
  kept_img (PA := PA) B s (Z.of_nat (length src)) -> (0 < length src)%nat ->
  (forall j, (j < length src)%nat ->
     option_map (fun bb : byte => bv_unsigned bb) (seg_rom SEGS (Z_to_bv 64 (s + Z.of_nat j))) = Some (nth j src 0)) ->
  Z.of_nat (length src) = n -> Z.of_nat (length add) + n <= 1 + 2 * d ->
  tl_win Wc (ms_mem ms) ->
  (f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 (ks ++ [n] ++ rest))) ->
  (f0 = 0 -> YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 (ks ++ [n] ++ rest))) (st_depot S)) ->
  (f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 (ks ++ [n] ++ rest)))) ->
  tl_tx b cap fc ow ks add pre lyc Sc Hpc Wc (ms_mem ms) ->
  SRW Wc (mkCfg ms mdc) (fun W2 c2 =>
    exists ly2 S2 Hp2 regs2 mem2 md2 k2 b2 cap2 fc2 ow2 pre2,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
      AJR (STKL + dw) (sp0 + dw) FP0 ly (set_depot (st_depot S2) S) Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k2 /\
      tl_win W2 mem2 /\
      (forall a, sp0 - 32 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) /\
      aregs_preserved (ms_regs ms) regs2 /\
      tl_tx b2 cap2 fc2 ow2 (ks ++ [n]) (add ++ src) pre2 ly2 S2 Hp2 W2 mem2).
Proof.
intros Wc E ss ms mdc lyc Sc Hpc kc b cap fc ow ks add pre n rest s src raw HS Hrv Hpcs HJ Hsp HE2 Hgp Htp Hra Hraw
  Hra4 Hrac Hs0 Ha0 Ha1 Ha2 Hki Hsrc0 Hrom Hn Hcnt HWIN HEV HRW HCF HTX.
subst n.
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & Hdpres).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof tl_img_box as (Hib1 & Hib2).
pose proof (ajxR_ar HJ) as HARc.
pose proof HTX as (HTX0 & (j & histc & Hj & HPOSc) & HPc & HDEAD & (WS0 & HWI & HWB)).
pose proof HTX0 as (_ & _ & Hks & _ & HO & _).
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx WR _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWI)
  as HJW.
assert (FTL : STKL = 32 + @STK_tx_put prh_img_B) by reflexivity.
assert (FTP : 32 <= @STK_tx_put prh_img_B) by (vm_compute; discriminate).
assert (Hspc : spZ (ms_regs ms) = sp0 + -32).
{ unfold spZ at 1. rewrite Hsp, denot_SOff, HE2. apply YP0m.zcanon_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)). unfold spZ in *. lia. }
pose proof (s10_rod_keptR B ARx SK HPSTro WR (STKL + dw) (sp0 + dw) FP0 ly _ Hp W mem md [] lyc Sc Hpc Wc (ms_mem ms)
  mdc kc
  HJ (s10_fp_closed B Lam ly S W mem t b0 len0 cap0 txt ltac:(lia) HINV) HROD) as HRODc.
destruct (tx_state_pre B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b cap fc ow ks add pre
  lyc Sc Hpc Wc (ms_mem ms) (ms_regs ms) (dw - -32) HTX0 ltac:(lia) ltac:(lia))
  as (HRM & HPL & HTR & HREC1 & HINV1 & HLED1 & HBB & EHp & Hplen).
pose proof (tx_window rp_sm rp_x rp_os rp_i j len0 cap0 f0 fc own ow b0 b cap ks add pre [Z.of_nat (length src)] rest
  HO Hj Hks HEV) as HWINc.
pose proof (tx_room_window (as_universe B) (st_depot S) (st_depot Sc) WS0 len0 cap0 f0 fc own ow b0 b cap ks add pre
  [Z.of_nat (length src)] rest HO Hks HRW HWI HWB) as HROOMc.
pose proof (tx_cons_window rp_sm rp_x rp_os rp_i j len0 cap0 f0 fc own ow b0 b cap ks add pre [Z.of_nat (length src)]
  rest HO Hj Hks HCF) as HCONSc.
destruct (s10_src_img B ARx LAWS zs_aligned img_shadow_vis_x tl_img_box tl_img_cf_box lyc Sc Hpc Wc (ms_mem ms) mdc Lam
  s src HARc HRODc Hki Hsrc0 Hrom) as [HSRC HKEPT].
pose proof (s10_fwin_callR B ARx SK WR STKL dw sp0 FP0 ly _ Hp W mem md [] lyc Sc Hpc Wc (ms_mem ms) mdc kc (ms_regs ms)
  (-32) HJ Hspc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hdw16; reflexivity)) as HFW.
assert (HHIc : spZ (ms_regs ms) + 64 <= ly_stk_hi lyc) by (rewrite Hspc, (tl_hi _ _ _ _ _ _ _ HJ); lia).
assert (HRAc : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite Hra; exact Hrac).
assert (Hdisj : forall a, s <= a < s + Z.of_nat (length src) -> ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)).
{ intros a Ha. destruct Hki as (Hlo & Hhi & Hro).
  split; [lia|]. intros Hb.
  destruct HINV1 as (_ & [(Hz & _) | (Hc & _ & Hin & _)]); [lia|].
  destruct (alx_client_img SEGS B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) mdc a HARc) as [_ Hni].
  { left. exists b, cap. split; [exact Hin|].
    unfold req_size. destruct (Z.eqb_spec cap 0); lia. }
  apply Hni. apply tl_ro_img. exact (proj1 (Hro a Ha)). }
eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
{ eapply (s10_call_WbmR B ARx SK LAWS WR WRtrans Wc E ss ms STKL dw sp0 FP0 ly S Hp W mem md [] lyc Sc Hpc mdc kc WS0
    (@STK_tx_put prh_img_B) (prhtx_fp t b cap) (-32) (getr regs 2) raw []
    _ _ HS Hrv HJW Hsp HE2 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Hdw0 Hdw16 Hgp Htp Hra Hraw Hra4
    (achain_low _ _ _ _ Hs0)).
  - intros HPRE1. rewrite Hpcs.
    exact (TXPUT rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc
      lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc [] (dw - -32) t s (Z.of_nat (length src)) b
      (len0 + Z.of_nat (length pre)) cap fc ow (txt ++ pre) src Lam peak cnt fail ran most
      (conj HPRE1 (conj HRODc (conj HHIc (conj HRAc HFRM)))) HCL HRM HPOSc HOS HROOMc HCONSc Ha0 Ha1 Ha2 HFW HPL HTR
      HREC1 HINV1 HSRC eq_refl HKEPT Hdisj ltac:(lia) HLED1
      (fun Hf Hlt => tx_put_ev rp_sm rp_x rp_os (rp_i + j) (len0 + Z.of_nat (length pre)) cap (Z.of_nat (length src)) fc
         HWINc Hf Hlt)
      ltac:(lia) ltac:(lia)).
  - unfold fp_sub_x. intros a Ha.
    destruct (tx_state_fp B ARx LAWS Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b cap fc ow
      ks add pre lyc Sc Hpc Wc (ms_mem ms) mdc HTX0 HARc a Ha) as [H1|H1]; [left | right; left]; exact H1. }
cbv beta. intros W2 c2 _ HN.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HWB1 & HJW2 & HJ1 & HW1 & HP & HQ).
destruct HQ as ((b2 & cap2 & f2 & ow2 & pre2 & HPOST & HARMS & HDEAD2 & _ & HRM2 & HGRW & HNGR & HLED2) & HMN2).
destruct (tx_put_res rp_sm rp_x rp_os (rp_i + j) rp_H0 histc S2 (len0 + Z.of_nat (length pre)) cap fc f2 ow ow2 b b2
  cap2 (Z.of_nat (length src)) src pre2 _ HARMS HGRW HNGR) as (HOUT & jq & h2 & Hjq & HPOS2).
exists ly2, S2, Hp2, regs2, mem2, md2, (kc + k1), b2, cap2, f2, ow2, (pre ++ pre2).
split; [reflexivity|].
split; [exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx WR _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJW2)|].
split.
{ intros a Ha Hn0. rewrite (HW1 a ltac:(lia)); [exact (HWIN a Ha Hn0)|].
  intros Hf. apply Hn0. exact (tx_state_fp_win B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own
    b cap fc ow ks add pre lyc Sc Hpc Wc (ms_mem ms) HTX0 a ltac:(lia) Hf). }
split.
{ intros a Ha. apply HW1; [lia|]. intros Hf. destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)]; [lia|].
  destruct HINV1 as (_ & [(Hz & _) | (_ & _ & _ & _ & _ & Hceil' & _)]); [lia|].
  unfold req_size in Hb. destruct (Z.eqb_spec cap 0); lia. }
split; [exact HP|].
split; [|split; [|split; [|split]]].
- eapply (tx_state_fold_wR B ARx SK WR Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b cap fc ow ks
    add pre [Z.of_nat (length src)] src b2 cap2 f2 ow2 pre2 lyc Sc Hpc Wc (ms_mem ms) mdc ly2 S2 Hp2 W2 mem2 md2
    (ms_regs ms) (dw - -32) (@STK_tx_put prh_img_B) k1 WS1 HTX0 HARc).
  + cbn [TxModel.zsum]. lia.
  + rewrite Hspc. lia.
  + lia.
  + rewrite Hspc. replace (sp0 + -32 + (dw - -32)) with (sp0 + dw) by lia. exact HJ1.
  + intros a Ha Hn0. apply HW1; [rewrite Hspc in Ha; lia | exact Hn0].
  + exact HPOST.
  + exact HOUT.
  + exact HRM2.
  + exact HLED2.
- exact (tx_pos_fold rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 fc f2 own ow ow2 b0 b b2 cap cap2 j jq h2 S2
    ks [Z.of_nat (length src)] add src pre pre2 Hks HO Hj HOUT Hjq HPOS2).
- exact (PCALL _ _ HMN2 HPc).
- intros Hf0. exact (HDEAD2 (HDEAD Hf0)).
- exists (WS0 ++ WS1). split; [exact (ajxR_wild HJW2)|].
  exact (tx_budget_fold len0 cap0 f0 fc own ow b0 b cap ks add pre [Z.of_nat (length src)] WS0 WS1 HO Hks HDEAD HWB
    HWB1).
Qed.

(* ---- at `ret`: the text's conclusion from the final state (the journal, the window, the registers, the text state:
   the outcome, DEAD and the position, P of the final memory, and the budget: the rebased journal at WR unbased at
   the budget tl_tx carries, YCbqGwild.ajournal_xw_unbase0R; QF's journal is at WR, fpostWb = fpostW_xbR at WR) ---- *)
Lemma tl_fin : forall lyF SF HpF WF regsF memF mdF kF bF capF fF owF preF X,
  AJR (STKL + dw) (sp0 + dw) FP0 ly (set_depot (st_depot SF) S) Hp W mem md [] lyF SF HpF WF memF mdF kF ->
  tl_win WF memF -> aregs_preserved regs regsF -> getr regsF 1 = getr regs 1 ->
  tl_tx bF capF fF owF (tl_ks TL_N) (tl_add TL_N) preF lyF SF HpF WF memF ->
  QF WF (mkCfg (mkst regsF (v_jalr (getr regsF 1) 0) memF (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdF) X mdF)).
Proof.
intros lyF SF HpF WF regsF memF mdF kF bF capF fF owF preF X HJ HW HP R1 HTX.
destruct HTX as ((_ & _ & _ & HPOST & HO & _ & HRM & HLEDF) & HPOSF & HMN & HDEADF & (WSF & HWIF & HWBF)).
pose proof HPRE as (_ & Hra & _).
unfold QF, fpostWb, YCbqGwild.fpostW_xbR.
exists lyF, SF, HpF, regsF, memF, (with_vm_backing (m_vm_lazy mdF) X mdF), kF, WSF.
split; [rewrite R1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [rewrite tl_model_ks; exact HWBF|].
split.
{ eapply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx WR _ _ _ _ _ Hp); [|exact HWIF].
  apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) WR). exact HJ. }
split; [exact HW|]. split; [exact HP|].
split; [|exact HMN].
unfold QT. rewrite tl_model_ks, tl_model_add. exists bF, capF, fF, owF, preF.
split; [exact HPOST|]. split; [exact HO|]. split; [exact HDEADF|]. split; [exact HRM|].
destruct (tx_pos_post _ _ _ _ _ _ _ _ _ _ _ HPOSF) as (jF & hF & Hj1 & Hj2 & Hj3 & Hj4).
exists jF, hF. split; [exact Hj1|]. split; [exact Hj2|]. split; [exact Hj3|]. split; [exact Hj4 | exact HLEDF].
Qed.

(* ---- the TAIL (B' 0x85c88): reload ra, s0, s1, s2, pop the frame, `ret` (the runner at WR; the `ret` step is a
   plain SRr step, lifted by YA0nH.SRr_SRr') ---- *)
Lemma tl_tail : forall i lyc Sc Hpc Wc memc mdc kc b rg, i = TL_N ->
  tl_live i 0 lyc Sc Hpc Wc memc mdc kc b -> tl_regs rg ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + TL_TAIL)) memc (seg_rom SEGS)) mdc) QF.
Proof.
intros i lyc Sc Hpc Wc memc mdc kc b rg -> HL HR.
pose proof HL as (HJ & _ & HFR & _ & (_ & _ & _ & _ & (_ & _ & HPM & _))).
destruct (tl_mk TL_TAIL rg Wc memc HR HFR) as [HS SHOK].
pose proof (te_env regs rg) as HEI.
pose (RUN := paj_run_x_invR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS P PLAW WR WRrefl WRtrans).
pose (RET := paj_ret_at (PL := PL) (PI := PA)).
paj_run_tok_x_invR RUN HS HJ SHOK HPM TL_Bspan; [tl_awr_ro|].
tl_same HFr Hm.
pose proof (tl_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm HPM) as (HJ' & HW' & _ & _ & (capF & fF & owF & preF & HTX')).
tlreg HS (1%bv : bv 5) Q1.
apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
apply (tl_fin lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ kc b capF fF owF preF mat' HJ' HW').
- eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (map (getr rg) all_regs) HS);
    [apply te_agree | vm_compute; reflexivity].
- rewrite Q1. apply te_den_entry. reflexivity.
- exact HTX'.
Qed.

(* ---- the LOOP: at its head (B' 0x85c70) with S j indent calls to come ---- *)
Definition tl_LH_ok (j : nat) : Prop :=
  forall i lyc Sc Hpc Wc memc mdc kc b rg,
  tl_live i (Datatypes.S j) lyc Sc Hpc Wc memc mdc kc b -> tl_regs rg ->
  getr rg 8 = w64 (Z.of_nat (Datatypes.S j)) -> getr rg 9 = w64 t -> getr rg 18 = w64 STR29 ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + TL_LH)) memc (seg_rom SEGS)) mdc) QF.

(* after the loop's call (B' 0x85c80): `addiw s0, s0, -1`, `bnez s0`: back to the head, or the tail *)
Lemma tl_back : forall j, (forall j', j = Datatypes.S j' -> tl_LH_ok j') ->
  forall i lyc Sc Hpc Wc memc mdc kc b rg,
  tl_live (Datatypes.S i) j lyc Sc Hpc Wc memc mdc kc b -> tl_regs rg ->
  getr rg 8 = w64 (Z.of_nat (Datatypes.S j)) -> getr rg 9 = w64 t -> getr rg 18 = w64 STR29 ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + TL_R2)) memc (seg_rom SEGS)) mdc) QF.
Proof.
intros j Hrec i lyc Sc Hpc Wc memc mdc kc b rg HL HR R8 R9 R18.
pose proof HL as (HJ & _ & HFR & Hij & (_ & _ & _ & _ & (_ & _ & HPM & _))).
destruct (tl_mk TL_R2 rg Wc memc HR HFR) as [HS SHOK].
pose proof (te_env regs rg) as HEI.
pose (RUN := paj_run_x_invR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS P PLAW WR WRrefl WRtrans).
pose (RUNTO := paj_run_to_x_invR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS P PLAW WR WRrefl WRtrans).
pose (BR := YSRrG.paj_branchR (PI := PA) WR).
paj_run_tok_x_invR RUN HS HJ SHOK HPM TL_Bspan; [tl_awr_ro|].
tl_same HFr Hm.
pose proof (tl_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm HPM) as HL1.
clear HF HFr HG Hm.
YSRrG.psrr_branch_tokR RUN BR HS SHOK TL_Bspan.
- (* s0 - 1 <> 0: back to the loop head with j = S j' *)
  rewrite branch_ne_U, (tl_addw_m1 _ 40 (Z.of_nat (Datatypes.S j)) ltac:(exact (eq_trans (te_cur regs rg 8%bv 8 eq_refl) R8))
    ltac:(lia)), U_SLit in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc. change (zcanon 0) with 0 in Hc.
  destruct j as [|j']; [lia|].
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM TL_Bspan TL_LH; [tl_awr_ro|].
  tl_same HFr Hm. pose proof (tl_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ HL1 HJ Hm HPM) as HL2. clear HF HFr HG Hm.
  pose proof (tl_regs_post _ _ _ _ _ HS (te_agree regs rg) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
    as HRL.
  tlreg HS (8%bv : bv 5) Q8. tlreg HS (9%bv : bv 5) Q9. tlreg HS (18%bv : bv 5) Q18.
  pmkst HS. rewrite <- TL_LH_val.
  apply (Hrec j' eq_refl (Datatypes.S i) lyc Sc Hpc Wc _ _ _ b _ HL2 HRL).
  + rewrite Q8, tl_denot_U, (tl_addw_m1 _ 40 (Z.of_nat (Datatypes.S (Datatypes.S j')))
      ltac:(exact (eq_trans (te_cur regs rg 8%bv 8 eq_refl) R8)) ltac:(lia)).
    unfold w64. f_equal; lia.
  + rewrite Q9, (te_den_cur regs rg 41 9 9%bv eq_refl eq_refl). exact R9.
  + rewrite Q18, (te_den_cur regs rg 50 18 18%bv eq_refl eq_refl). exact R18.
- (* s0 - 1 = 0: the tail *)
  rewrite branch_ne_U, (tl_addw_m1 _ 40 (Z.of_nat (Datatypes.S j)) ltac:(exact (eq_trans (te_cur regs rg 8%bv 8 eq_refl) R8))
    ltac:(lia)), U_SLit in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc.
  assert (Hj0 : j = 0%nat) by lia. subst j.
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM TL_Bspan TL_TAIL; [tl_awr_ro|].
  tl_same HFr Hm. pose proof (tl_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ HL1 HJ Hm HPM) as HL2. clear HF HFr HG Hm.
  pose proof (tl_regs_post _ _ _ _ _ HS (te_agree regs rg) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
    as HRL.
  pmkst HS. rewrite <- TL_TAIL_val.
  exact (tl_tail (Datatypes.S i) lyc Sc Hpc Wc _ _ _ b _ ltac:(lia) HL2 HRL).
Qed.

(* the loop head to its call, the call, then tl_back *)
Lemma tl_step : forall j, (forall j', j = Datatypes.S j' -> tl_LH_ok j') -> tl_LH_ok j.
Proof.
intros j Hrec i lyc Sc Hpc Wc memc mdc kc b rg HL HR R8 R9 R18.
pose proof HL as (HJ & _ & HFR & Hij & (_ & _ & _ & _ & (_ & _ & HPM & _))).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
pose proof (@pa_B_ok _ _ PA) as HBASE.
destruct (tl_mk TL_LH rg Wc memc HR HFR) as [HS SHOK].
pose proof (te_env regs rg) as HEI.
pose (RUN := paj_run_x_invR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS P PLAW WR WRrefl WRtrans).
paj_run_tok_x_invR RUN HS HJ SHOK HPM TL_Bspan; [tl_awr_ro|].
tl_same HFr Hm.
pose proof (tl_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm HPM) as HL1.
pose proof HL1 as (_ & HW1 & HFR1 & _ & (cap1 & fc1 & ow1 & pre1 & HTX1)).
clear HF HFr HG.
pose proof (tl_regs_post _ _ _ _ _ HS (te_agree regs rg) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  as HRc.
tlreg HS (2%bv : bv 5) Q2. tlreg HS (3%bv : bv 5) Q3. tlreg HS (4%bv : bv 5) Q4. tlreg HS (1%bv : bv 5) Q1.
tlreg HS (8%bv : bv 5) Q8. tlreg HS (9%bv : bv 5) Q9. tlreg HS (18%bv : bv 5) Q18. tlreg HS (10%bv : bv 5) Q10.
tlreg HS (11%bv : bv 5) Q11. tlreg HS (12%bv : bv 5) Q12.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (tl_call Wc (TE regs rg) _ ms _ lyc Sc Hpc kc b cap1 fc1 ow1 (tl_ks i) (tl_add i) pre1 2 (repeat 2 j) STR29 [32; 32]
    (Z_to_bv 64 (BASE + TL_R2)) HS).
  - reflexivity.
  - reflexivity.
  - exact HJ.
  - exact Q2.
  - exact (te_entry regs rg 2%bv 2 eq_refl).
  - rewrite Q3, (te_den_entry regs rg 3 3%bv eq_refl). exact Hgp.
  - rewrite Q4, (te_den_entry regs rg 4 4%bv eq_refl). exact Htp.
  - rewrite Q1, TL_R2_val. exact (codeptr_val (TE regs rg) 17844 HEI).
  - rewrite TL_R2_val. apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite TL_R2_val, unsigned_lit_small by lia. lia.
  - pose proof tl_ceil_R2 as HC. rewrite TL_R2_val in HC. rewrite TL_R2_val, unsigned_lit_small by lia. exact HC.
  - unfold s0Z. rewrite Q8, (te_den_cur regs rg 40 8 8%bv eq_refl eq_refl), R8. unfold w64.
    rewrite unsigned_lit_small by lia. lia.
  - rewrite Q10, (te_den_cur regs rg 41 9 9%bv eq_refl eq_refl). exact R9.
  - rewrite Q11, (te_den_cur regs rg 50 18 18%bv eq_refl eq_refl). exact R18.
  - rewrite Q12. reflexivity.
  - exact (proj2 tl_lit_img).
  - cbn [length]. lia.
  - intros jj Hjj. destruct jj as [|[|jj]]; [vm_compute; reflexivity | vm_compute; reflexivity | cbn [length] in Hjj; lia].
  - reflexivity.
  - rewrite tl_add_len. lia.
  - exact HW1.
  - rewrite tl_ks_split, Hij. exact tl_evs.
  - rewrite tl_ks_split, Hij. exact tl_roomw.
  - rewrite tl_ks_split, Hij. exact tl_consw.
  - exact HTX1. }
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & b2 & cap2 & fc2 & ow2 & pre2 & -> & HJ2 & HW2 & HFK & HP2 & HTX2).
apply (tl_back j Hrec i ly2 S2 Hp2 W2 mem2 md2 k2 b2 regs2).
- split; [exact HJ2|]. split; [exact HW2|]. split; [exact (tl_frame_move Wc W2 (ms_mem ms) mem2 HFK HFR1)|].
  split; [lia|]. exists cap2, fc2, ow2, pre2. rewrite <- tl_ks_S, <- tl_add_S. exact HTX2.
- exact (tl_regs_pres _ _ HRc HP2).
- rewrite (tl_ap _ _ HP2 8%bv) by tl_csv. rewrite Q8, (te_den_cur regs rg 40 8 8%bv eq_refl eq_refl). exact R8.
- rewrite (tl_ap _ _ HP2 9%bv) by tl_csv. rewrite Q9, (te_den_cur regs rg 41 9 9%bv eq_refl eq_refl). exact R9.
- rewrite (tl_ap _ _ HP2 18%bv) by tl_csv. rewrite Q18, (te_den_cur regs rg 50 18 18%bv eq_refl eq_refl). exact R18.
Qed.

Lemma tl_loop : forall j, tl_LH_ok j.
Proof.
intros j. induction j as [|j IH]; apply tl_step; intros j' Hj'; [discriminate Hj' | injection Hj' as <-; exact IH].
Qed.

(* ---- after the first call (B' 0x85c64): `blez s0` to the tail (d = 0), else s2 = "  " and the loop ---- *)
Lemma tl_seg1 : forall lyc Sc Hpc Wc memc mdc kc b rg,
  tl_live 0 TL_N lyc Sc Hpc Wc memc mdc kc b -> tl_regs rg -> getr rg 8 = w64 d -> getr rg 9 = w64 t ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + TL_R1)) memc (seg_rom SEGS)) mdc) QF.
Proof.
intros lyc Sc Hpc Wc memc mdc kc b rg HL HR R8 R9.
pose proof HL as (HJ & _ & HFR & Hij & (_ & _ & _ & _ & (_ & _ & HPM & _))).
destruct (tl_mk TL_R1 rg Wc memc HR HFR) as [HS SHOK].
pose proof (te_env regs rg) as HEI.
pose (RUN := paj_run_xR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS WR WRrefl WRtrans).
pose (RUNTO := paj_run_to_x_invR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS P PLAW WR WRrefl WRtrans).
pose (BR := YSRrG.paj_branchR (PI := PA) WR).
YSRrG.psrr_branch_tokR RUN BR HS SHOK TL_Bspan.
- (* d <= 0, so d = 0: the tail *)
  rewrite (te_den_cur regs rg 40 8 8%bv eq_refl eq_refl), R8 in Hc. cbn [sv_denot] in Hc. unfold w64 in Hc.
  rewrite (tl_ge0 d) in Hc by lia. apply Z.leb_le in Hc.
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM TL_Bspan TL_TAIL; [tl_awr_ro|].
  tl_same HFr Hm. pose proof (tl_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm HPM) as HL2. clear HF HFr HG Hm.
  pose proof (tl_regs_post _ _ _ _ _ HS (te_agree regs rg) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
    as HRL.
  replace (Z.to_nat d) with 0%nat in HL2 by lia.
  pmkst HS. rewrite <- TL_TAIL_val.
  exact (tl_tail 0 lyc Sc Hpc Wc _ _ _ b _ ltac:(lia) HL2 HRL).
- (* d >= 1: s2 = "  ", the loop *)
  rewrite (te_den_cur regs rg 40 8 8%bv eq_refl eq_refl), R8 in Hc. cbn [sv_denot] in Hc. unfold w64 in Hc.
  rewrite (tl_ge0 d) in Hc by lia. apply Z.leb_gt in Hc.
  paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM TL_Bspan TL_LH; [tl_awr_ro|].
  tl_same HFr Hm. pose proof (tl_live_same _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm HPM) as HL2. clear HF HFr HG Hm.
  pose proof (tl_regs_post _ _ _ _ _ HS (te_agree regs rg) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
    as HRL.
  tlreg HS (8%bv : bv 5) Q8. tlreg HS (9%bv : bv 5) Q9. tlreg HS (18%bv : bv 5) Q18.
  replace (Z.to_nat d) with (Datatypes.S (Z.to_nat d - 1)) in HL2 by lia.
  pmkst HS. rewrite <- TL_LH_val.
  apply (tl_loop (Z.to_nat d - 1) 0%nat lyc Sc Hpc Wc _ _ _ b _ HL2 HRL).
  + rewrite Q8, (te_den_cur regs rg 40 8 8%bv eq_refl eq_refl), R8. unfold w64. f_equal; lia.
  + rewrite Q9, (te_den_cur regs rg 41 9 9%bv eq_refl eq_refl). exact R9.
  + rewrite Q18, (tl_obj2 _ 70496 HEI). reflexivity.
Qed.

(* ---- the entry: the prologue to the first call, the call, then tl_seg1. THE ONE LIFT (F12, plan row B-12): the
   entry journal is made at WR (ajournal_x_init_WR), so the prologue, the first tx_put call and every later
   segment run at WR; no lift at a call ---- *)
Lemma tl_main : SRW W (cfg_at SEGS (SIGMA AS_tx_line) regs mem md) QF.
Proof.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (@pa_B_ok _ _ PA) as HBASE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & Hdpres).
assert (FTL : STKL = 32 + @STK_tx_put prh_img_B) by reflexivity.
assert (FTP : 32 <= @STK_tx_put prh_img_B) by (vm_compute; discriminate).
destruct (tl_entry STKL ly S Hp W regs mem md ch HPRE ltac:(lia)) as [HS SHOK].
(* the entry's journal (S to S) at WR, REBASED to the entry depot: tl_live's form (YCbqGwild.ajournal_xw_rebaseR at
   WS = []) *)
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx WR _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ []
  (ajournal_x_init_WR (SK := SK) SEGS B PST ARx WR WRrefl STKL dw FP0 ly S Hp W regs mem md ch HPRE
    ltac:(unfold fwin in HFWIN; unfold fwin_x; exact HFWIN))) as HJ.
assert (HTX0 : tl_tx b0 cap0 f0 own [] [] [] ly S Hp W mem).
{ split; [exact (tx_state_init B ARx Lam regs dw ly S Hp W mem md ch STKL t b0 len0 cap0 f0 txt peak cnt fail ran most own
    HPRE HFWIN HPLACE HTRACE HREC HINV HROOM HLED)|].
  split; [exact (tx_pos_init rp_sm rp_x rp_os rp_i rp_H0 rp_hist len0 cap0 f0 S HPOS)|].
  split; [exact HP0|]. split; [exact (fun E => E)|].
  exists []. split; [rewrite app_nil_r; apply incl_refl | intros _; unfold YCbqGwild.wbudget; cbn; lia]. }
remember (TL_EI regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold TL_EI; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n) by (intros n Hn; subst E; unfold TL_EI; apply Eimg_low; exact Hn).
assert (EE : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros r n Hn. pose proof (u5_range r). rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn). }
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%bv 2%nat eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE EL.
pose (RUN := paj_run_x_invR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS P PLAW WR WRrefl WRtrans).
assert (HPM : P mem) by exact HP0.
unfold cfg_at. rewrite <- TL_PC_val.
(* ---- slots 0-11: the frame, s0 = d, s1 = t, a1 = "\n", a2 = 1, the first tx_put call ---- *)
paj_run_tok_x_invR RUN HS HJ SHOK HPM TL_Bspan; [tl_awr regs Usp|].
assert (KA : forall x : word, bv_unsigned x < sp0 - 32 \/ sp0 <= bv_unsigned x ->
   mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x Hx. apply HFr. intros (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Usp in Hr. lia. }
assert (HW1 : tl_win W (ms_mem ms)).
{ intros a Ha _. unfold aview, mbyte. rewrite KA; [reflexivity|]. rewrite unsigned_lit_small by lia. lia. }
assert (HTX1 : tl_tx b0 cap0 f0 own [] [] [] ly S Hp W (ms_mem ms)).
{ destruct HTX0 as (HT0 & HPS0 & _ & HD0 & HW0).
  split; [|split; [exact HPS0 | split; [exact HPM | split; [exact HD0 | exact HW0]]]].
  exact (tx_state_keep B ARx LAWS HPST Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b0 cap0 f0 own
    [] [] [] ly S Hp W mem (ms_mem ms) md (sp0 - 32) sp0 HT0 HAR ltac:(lia) ltac:(lia) ltac:(lia) KA). }
pose proof (tl_frame_of_st E _ W ms (-32) 0 HS HAE ltac:(vm_compute; reflexivity)) as HFR1.
pose proof (tl_regs_post E [] _ _ _ HS HAE ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HRc.
clear HF HFr HG.
tlreg HS (2%bv : bv 5) Q2. tlreg HS (3%bv : bv 5) Q3. tlreg HS (4%bv : bv 5) Q4. tlreg HS (1%bv : bv 5) Q1.
tlreg HS (8%bv : bv 5) Q8. tlreg HS (9%bv : bv 5) Q9. tlreg HS (10%bv : bv 5) Q10. tlreg HS (11%bv : bv 5) Q11.
tlreg HS (12%bv : bv 5) Q12.
assert (DE : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> sv_denot E (SOff n 0) = getr regs r).
{ intros r n Hn. cbn [sv_denot]. rewrite (EE r n Hn), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (tl_call W E _ ms _ ly S Hp 0 b0 cap0 f0 own [] [] [] 1 (repeat 2 TL_N) STR19 [10] (Z_to_bv 64 (BASE + TL_R1)) HS).
  - reflexivity.
  - reflexivity.
  - exact HJ.
  - exact Q2.
  - exact (EE 2%bv 2%nat eq_refl).
  - rewrite Q3, (DE 3%bv 3%nat eq_refl). exact Hgp.
  - rewrite Q4, (DE 4%bv 4%nat eq_refl). exact Htp.
  - rewrite Q1, TL_R1_val. exact (codeptr_val E 17816 HEI).
  - rewrite TL_R1_val. apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite TL_R1_val, unsigned_lit_small by lia. lia.
  - pose proof tl_ceil_R1 as HC. rewrite TL_R1_val in HC. rewrite TL_R1_val, unsigned_lit_small by lia. exact HC.
  - unfold s0Z. rewrite Q8, (DE 11%bv 11%nat eq_refl), H11. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q10, (DE 10%bv 10%nat eq_refl). exact H10.
  - rewrite Q11, (tl_obj2 _ 70112 HEI). reflexivity.
  - rewrite Q12. reflexivity.
  - exact (proj1 tl_lit_img).
  - cbn [length]. lia.
  - intros jj Hjj. destruct jj as [|jj]; [vm_compute; reflexivity | cbn [length] in Hjj; lia].
  - reflexivity.
  - cbn [length Z.of_nat]. lia.
  - exact HW1.
  - exact tl_evs.
  - exact tl_roomw.
  - exact tl_consw.
  - exact HTX1. }
intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & b2 & cap2 & fc2 & ow2 & pre2 & -> & HJ2 & HW2 & HFK & HP2 & HTX2).
apply (tl_seg1 ly2 S2 Hp2 W2 mem2 md2 k2 b2 regs2).
- split; [exact HJ2|]. split; [exact HW2|]. split; [exact (tl_frame_move W W2 (ms_mem ms) mem2 HFK HFR1)|].
  split; [lia|]. exists cap2, fc2, ow2, pre2. exact HTX2.
- exact (tl_regs_pres _ _ HRc HP2).
- rewrite (tl_ap _ _ HP2 8%bv) by tl_csv. rewrite Q8, (DE 11%bv 11%nat eq_refl). exact H11.
- rewrite (tl_ap _ _ HP2 9%bv) by tl_csv. rewrite Q9, (DE 10%bv 10%nat eq_refl). exact H10.
Qed.

End g.
End p.

(* ==== The batch kit's text ttx_line_specX (lib/A/PRH_FnTx.v at a working branch 4dcec0343c87, blob
   88468bf162d8) at image B': the walk at P := fun m => memnorm SEGS mem -> memnorm SEGS m (YSRrMemnorm.v
   srr_inv_laws_imp / srr_inv_call_imp); at that P, QF IS the text's post (fpostWbmR .. WR .. QT = fpostWb ..
   (fQmn mem QT), both fpostW_xbR at WR) and P mem is the identity; the walk's SRW is the text's SRr' segs RZ_cf ==== *)
Theorem tx_line_B_holds : ttx_line_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Proof.
unfold ttx_line_specX. cbv zeta.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t d b0 len0 cap0 f0 own txt Lam peak cnt fail ran
  most HPRE0 HCL HROOM HPOS HOS HROOMW HCONS H10 H11 Hd HFWIN HPLACE HTRACE HREC HINV HLEN HLED HEVS HLIVE HMAX.
destruct HPRE0 as (HPRE & HROD & HHI & _ & HFRM).
eapply (tl_main (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS _ mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS))
  (YSRrMemnorm.srr_inv_call_imp SEGS mem)); first [eassumption | exact (fun H => H)].
Qed.

End f.
End d.

(* ---- the audit read-outs (the reporting rule): the top lemma's assumptions and statement, and the elaborated bodies
   of every definition this re-fit changed, with every implicit argument shown (the Print implicit check) ---- *)
Print Assumptions tx_line_B_holds.
Set Printing Implicit.
Check tx_line_B_holds.
Print tl_tx.
Print tl_live.
Print QT.
Print QF.
Print tl_img_box.
Print tl_img_cf_box_B.
Unset Printing Implicit.

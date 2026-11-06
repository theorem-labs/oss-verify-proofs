(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths, module names and numbers changed; 5113 of its 5220 lines of code are new or changed and 407 lines of the source are left out. *)
(* INT102-READY on the kit's cut 7cdbb61b5fa0 (it replaces the record walk ef6206ba4c8a of
   a working branch f854a0d93453; the cut carries int102's copy 391e9ae7b481): the same walk re-fitted to the batch kit's
   texts, a working branch cdde0ed15730 (lib/A/PRH_FnTx.v 88468bf162d8, lib/A/PRH_Base.v
   966b522cc722, lib/Reusable/YCbqGwild.v aa0b10a819fa; at the cut PRH_FnTx.v 88468bf162d8, PRH_Base.v ef7c8ca98529,
   YCbqGwild.v 0c63874858e4), as the tx_line PREP (BTxLine.v 60600612cede) did. What the batch changed, and what this
   file does about it (each change forced by the batch text; every lemma name kept):
   - DW is gone (prh_univ_closure B CTX0; ttx_*_specX B ARx SK CTX0, tx_value's at CTX0 n);
   - prhtx_trace is STATE-FREE (inU, no S) - unchanged here: tx_state's TRACE is memory-only;
   - each tx text takes a GUARDED ROOM premise `f0 = 0 -> wild_room (as_universe B) [] k (st_depot S)` and a GUARDED
     CONSUMER WINDOW `f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i k`, k = length (prhtx_evs len0 cap0 ks): Section-g
     hypotheses HROOMW / HCONS (split over a prefix by tv_roomw_split / tv_cons_split); each call from the open arm
     gets its callee's from them on the DONE path (Tx102Glue.v tx_room_window, tx_cons_window); the two ENTRY tails
     (tx_put, tx_string) pass them on at the same events (PRH_FnTx.v 7cf918708def :987-990);
   - each post states DEAD `f0 = 0 -> f1 = 0` (QT's new conjunct; carried in tv_tx, folded from each callee's own);
   - the posts are BUDGETED (fpostWbm (wbudget_if f0 [] k)): a callee's journal is at a budget WS1, the caller's at
     WS0 ++ WS1 (Tx102Glue.v s10_call_WbmR / s10_tail_WbmR, tx_budget_fold). The cut invariant carries no depot conjunct
     in its journal: tv_live's journal starts at the REBASED entry `set_depot (st_depot Sc) S`
     (YCbqGwild.ajournal_xw_rebase), so every runner segment is unchanged; the depot's wild growth since the entry is
     tv_tx's `incl (wild_part (st_depot Sc)) (wild_part (st_depot S) ++ WS)` with `wbudget_if f0 [] (events of P) WS`,
     which unbases at each call and at the closing tail (ajournal_xw_unbase0R). The lemmas that read a callee's journal
     (tv_foot_journal, tv_node_ra_end, tv_qt) take it at any budget WS. *)
(* THE RE-HIDE MOVE (the free / realloc contracts re-hide shadow, so a run that crosses one ends at the world relation
   wle' SEGS RZ_cf, written WR here, and concludes SRr', written SRW): ttx_value_specX and the texts it calls conclude
   SRr' with their posts at WR (fpostWbmR), and take the threaded allocator hull premise (length rp_os <= 4)%nat
   (Section hypothesis HRP4, handed to every callee text). Every call tx_value makes reaches tx_put's realloc, so:
   - the leaf runs (tv_run_lit_B, tv_run_str_B, tv_run_num_B, tv_run_open_B) call no free and keep their SRr
     statements; their callers use them through tv_srr_then / tv_srr_now (SRr_SRr', SRr'_bind);
   - the tail calls (tv_tail_put, tv_tail_string) lift the entry journal (at wle) to WR and use Tx102Glue.v's
     s10_tail_WbmR; the calls from the open arm use s10_call_WbmR;
   - the live state tv_live is ONE definition over the journal's relation R (tv_liveR R; tv_live its instance at
     wle, used at the opening call and lifted by tv_liveR_mono); every cut after the opening call is at WR, its runs
     use the R runners (RUNIR, RUNTOIR, paj_branchR) and its journal lemmas the R forms (ajxR_* projections,
     ajournal_xw_rebaseR / ajournal_xw_unbase0R);
   - QT is the text's named post body txvP_Q (PRH_FnTx.v) at this text's binders. *)

(* fuzz_preset IMAGE B' (asan-ubsan, #102 pin d663f82d; unstripped twin c90d4fa54d43): tx_value (B' 0x85440,
   slot 3933 of the whole-range listing lib/B/Listing_prog.v c97cc46b3e13, instance PI_prog_B) against K0's #102
   text ttx_value_specX (lib/A/PRH_FnTx.v 7cf918708def :975-1043, with the batch and re-hide changes above; first
   walked against an earlier version of that text, lib/A/PRH_FnTx.v blob a52a78336898: the record's `int failed` f0,
   the ledger's own, the run premise GUARDED by f0 = 0, ONE fpostWm post naming the outcome prhtx_out (DONE / FAILED AT
   ENTRY / REFUSED, no abort arm) and the position `exists j hist', ..`), at PI := prh_img_B: tx_value_B_holds (every
   depth bound, by induction on the bound; the recursion through the text one level down). RELOCATED from the old-pin
   walk by alreloc (d1f716c44f9d, relocation only), then RE-FITTED to the #102 texts after lib/B/Prog/BTxLine.v's
   re-fit. The B twin of S10's lib/A/Prog/S10TxValue.v
   (origin/cold/h-hpreset-7-walk-S10: d356ed78f634 the entry and leaf arms, 37251f6b9a5 the loop segments), over the
   same engine: YC1fPx's memory-invariant runner paj_run_x_inv over YCbqG's ajournal_x (caller-window form,
   YCbqGcallW.v ajournal_x_init_W) at the memnorm keep (YSRrMemnorm), the strlen wrapper through YGcallMxmn.v
   aj_strlen_at_xrom. GLUE (no local copy): lib/A/Prog/Tx102Glue.v - the no-abort call / tail-call rules s10_call_WbmR /
   s10_tail_WbmR, the text state tx_state / tx_pos (folded at each call by tx_state_fold_wR / tx_pos_fold), tx_window (a
   call's run window from the guarded premise), tx_put_ev / tx_put_res (tx_put's GROW premise and post). tx_line is
   DISCHARGED by BTxLine.tx_line_B_holds. Every arm and the text conclude SRW (SRr' at RZ_cf); the leaf runs keep SRr.
   Decomposition template only (not a donor, old pin 921b68a8): origin/cold/c-omx-hpreset-cls6 lib/B/Prog/tx_value.v
   :48-86 (btv_all -> tx_value_holds, the depth induction).
   RULE 24 (tx_value, image B' d663f82d, ttx_value_specX at PRH_FnTx.v blob a52a78336898): proof index tx_value 20:28:19Z (rc=0,
   index v5 built 19:12:20Z, lemma index 19:39:33Z): `6 named, 12 by address, 0 related, 3 released lemma(s), an earlier delivery 0
   named, 4 UNRELEASED cold/* file(s), 0 UNRELEASED hit(s) on live working heads`; the released hits are the plain /
   UBSan contract texts and models (other images), the unreleased ones TX_VALUE contract programs (lib/A, lib/AZ, lib/B
   old binary, lib/Prog/CF) - none a walk at B'. Rule-24 check CONFIRM (checker BTxValueB.TxvR24B102, 20:40Z): no Qed
   proof of tx_value at image B' exists other than this lane's relocated walk d1f716c44f9d, which this file re-fits.
   The census-1 cold/* + release/* sweep 20:28Z (15893 refs, 26854 blobs) found the positive control (tx_value_B_holds
   with 0x85440) only on this lane's branches.
   IMAGE B', measured with elfdis on the unstripped twin c90d4fa54d43 of d663f82d (tx_value at 0x85440, 1152 bytes)
   and checked here against PI_prog_B by computation:
   - frame 192 (`addi sp,sp,-192`, ra .. s11 at sp+184 .. sp+88) and B's dispatch, which differs from A's: `sd
     a3,24(sp)`; UBSan's `beqz a1,0x85868` and `andi a0,a1,7; sd a0,16(sp); bnez a0,0x85868` (0x85868 `unimp`; the
     engine decides both from the node atom's fact: 4096 <= v, v mod 8 = 0); the shadow base through the GOT word
     A_OBJ 0 kept at 72(sp); `lb a0,0(s2); bnez a0,0x8586c` (the node's shadow entry: 0); `lw a0,0(s1)`; `li a1,6;
     bltu a1,a0,0x85780` (excluded: tag <= 6); the table at 0x20f34 = pa_val (A_OBJ 2) + TV_JT_OFF_B; `jr a1`.
   - arms (ao = arm - BASE; ent = TV_JT_OFF_B + table entry; both DERIVED): tag 0 JNull 0x857fc (.str.3 0x20fa0, 4),
     tag 1 JFalse 0x8580c (.str.2 0x20f80, 5), tag 2 JTrue 0x857bc (.str 0x20f60; `j 0x85804` `li a2,4`), joined at
     0x85828 `mv a0,s0`, the epilogue, `j tx_put` 0x85864; tag 3 JNum 0x857c8 (shadow check of v->str, `ld s1`, `jal
     wrapper_strlen` = SIGMA AS___wrap_strlen, a2 := len, a0 := s0, a1 := s1, `j 0x8582c`, epilogue, `j tx_put`);
     tag 4 JStr 0x85724 (shadow check, a1 := v->str, a0 := s0, epilogue, `j tx_string` 0x8577c).
   - tags 5 / 6 (JArr / JObj, 0x854e0): the opening bracket's `jal tx_put` (return 0x8550c); n = 0 to the close seam
     0x856f0 (s5 = 1); else the set-up and the loop: L 0x8559c (`beqz s10`, the comma), C1 0x855b0 (`beqz s3`, the
     depth flag s9 = 0, tx_line(t, d + 1)), T 0x855c4 (the tag; an object's key slot and `jal tx_string`), K 0x85638
     (':'), Co 0x85648 (`beqz s3`, ' '), Sp 0x8565c (kids + 56 i, `jal tx_value`), I 0x856b8 (i := i + 1, `bltu
     s10,a0`), the closing tx_line(t, d) when pretty, X 0x85704 (the closing bracket, `j tx_put`). UBSan's loop
     checks are decided by the engine from the state's facts or from the seated conditions T: i >> 60 = 0,
     keys + 8 i >= keys; Sp: kids + 56 i >= kids, the `mulh` overflow test 0 (each proved by tvo_condU).
   NUMERALS. DERIVED: TV_PC_B (4 * the listing slot), TV_JT_OFF_B = 0x10f34 (0x20f34 - pa_val (A_OBJ 2)), the arm
   offsets and table entries above, the literal offsets 69536 / 69504 / 69472 / 70144 .. 70336 from pa_val (A_OBJ 2),
   the segment offsets 15936 .. 16440 (address - BASE), atom indices.
   WORDs of the image (PT_LOAD flags 4, file offset 0x10f34): the seven table entries, checked against seg_rom by
   vm_compute (tv_jt_rom_B). LENGTH: 192, 56, the node's field offsets 0 / 16 / 24 / 32 / 40, the frame offsets
   8 .. 184, the literal lengths 4 / 5 / 4 / 1, 28, 4096, 2 ^ 31 / 2 ^ 42 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47, the shift 60.
   No other ADDRESS literal: every address is pa_sigma / pa_val of lib/B/PAImg_prog.v.
   IMAGE CLOSURE: nothing of image A is used. The read-only / in-image byte checkers in_ro_b / in_img_b are
   lib/A/Prog/S1ImgA.v's image-free ones (lib/B/Prog/S1ImgB.v has no checker of its own and uses the same). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Tx102Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require BTxLine.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require TxModel WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
Import ListNotations.
(* PRW_StepKit loads YF0v.v, which sets Zify's euclidean-division flag off GLOBALLY; the #102 bvis clause
   ((x + k + 7) / 8 * 8 <= alloc_ceiling) needs lia over `/ 8` (as BTxLine.v) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* ---- image B: tx_value's entry, as a byte offset from the listing's base (DERIVED: 4 * the listing slot) ---- *)
Definition TV_PC_B : Z := 4 * Z.of_nat (B_prog_slot AS_tx_value).
(* tx_value's own frame at B: 192 bytes below the entry sp (LENGTH, the listing's `addi sp,sp,-192`) *)
Definition TV_FRAME_B : Z := 192.
(* the jump table at B 0x20f34, as an offset in the read-only band A_OBJ 2 (DERIVED: addr - pa_val (A_OBJ 2)); its
   seven entries are WORDs read from the pinned image d663f82d (PT_LOAD flags 4, file offset 0x10f34): tag i
   jumps to 0x20f34 + entry i, the seven targets PjTree.tag's arms: 0 JNull 0x857fc, 1 JFalse 0x8580c, 2 JTrue
   0x857bc, 3 JNum 0x857c8, 4 JStr 0x85724, 5 JArr and 6 JObj 0x854e0 *)
Definition TV_JT_OFF_B : Z := 0x10f34.
Definition tv_jt_words_B : list Z := [0x648c8; 0x648d8; 0x64888; 0x64894; 0x647f0; 0x645ac; 0x645ac].
Definition tv_jt_chunks_B : list YP09.chunk :=
  [YP09.mkChunk TV_JT_OFF_B (CVal 4 (SLit 0x648c8));
   YP09.mkChunk (TV_JT_OFF_B + 4) (CVal 4 (SLit 0x648d8));
   YP09.mkChunk (TV_JT_OFF_B + 8) (CVal 4 (SLit 0x64888));
   YP09.mkChunk (TV_JT_OFF_B + 12) (CVal 4 (SLit 0x64894));
   YP09.mkChunk (TV_JT_OFF_B + 16) (CVal 4 (SLit 0x647f0));
   YP09.mkChunk (TV_JT_OFF_B + 20) (CVal 4 (SLit 0x645ac));
   YP09.mkChunk (TV_JT_OFF_B + 24) (CVal 4 (SLit 0x645ac))].

Lemma TV_PC_val_B : B_prog_base + TV_PC_B = B_prog_sigma AS_tx_value.
Proof. vm_compute. reflexivity. Qed.

(* ---- DELETE when S10TxValGlue lands: B-local copy of S10TxValue.v (walk-S10 d356ed78f634) generic helpers
   (the pure model s10v_wsep / s10v_tvp_wv / s10v_zsum; the node's fields and facts; the checker soundness; the frame
   and view lemmas; the number arm's string facts). tv_keep takes the frame size as an argument (A's fixes 176). ---- *)
Lemma s10v_wsep : forall (p : bool), concat ([[58]] ++ (if p then [[32]] else [])) = concat [WriterValue.wsep p].
Proof. intros [|]; reflexivity. Qed.

Lemma s10v_tvp_wv : forall tv p d, concat (TxModel.tvp tv p d) = concat (WriterValue.wvpieces tv p d).
Proof.
intros tv. induction tv as [| | |txt bits|s|items IHitems|members IHmembers] using PjTree.jv_ind'; intros p d;
  try reflexivity.
- (* JStr *) cbn [TxModel.tvp WriterValue.wvpieces]. rewrite s10_strp_wstr. reflexivity.
- (* JArr *) cbn [TxModel.tvp WriterValue.wvpieces]. cbn [concat]. rewrite !concat_app. f_equal.
  assert (G : forall i, concat
    ((fix go (i : nat) (l : list PjTree.jv) {struct l} : list (list Z) :=
        match l with
        | [] => []
        | x :: r => WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ TxModel.tvp x p (d + 1) ++ go (S i) r
        end) i items) = concat
    ((fix go (i : nat) (l : list PjTree.jv) {struct l} : list (list Z) :=
        match l with
        | [] => []
        | x :: r => WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ WriterValue.wvpieces x p (d + 1) ++ go (S i) r
        end) i items)).
  { induction items as [|x r IH]; intros i; [reflexivity|].
    inversion IHitems as [|? ? Hx Hr]; subst.
    cbn [concat]. rewrite !concat_app. rewrite Hx, (IH Hr (S i)). reflexivity. }
  rewrite (G 0%nat). reflexivity.
- (* JObj *) cbn [TxModel.tvp WriterValue.wvpieces]. cbn [concat]. rewrite !concat_app. f_equal.
  assert (G : forall i, concat
    ((fix go (i : nat) (l : list (list Z * PjTree.jv)) {struct l} : list (list Z) :=
        match l with
        | [] => []
        | (k, x) :: r => WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ TxModel.strp k ++ [[58]] ++
                         (if p then [[32]] else []) ++ TxModel.tvp x p (d + 1) ++ go (S i) r
        end) i members) = concat
    ((fix go (i : nat) (l : list (list Z * PjTree.jv)) {struct l} : list (list Z) :=
        match l with
        | [] => []
        | (k, x) :: r => WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ WriterSpec.spieces k ++
                         [WriterValue.wsep p] ++ WriterValue.wvpieces x p (d + 1) ++ go (S i) r
        end) i members)).
  { induction members as [|[k x] r IH]; intros i; [reflexivity|].
    inversion IHmembers as [|? ? Hx Hr]; subst. cbn [snd] in Hx.
    cbn [concat]. rewrite !concat_app. rewrite Hx, (IH Hr (S i)).
    rewrite s10_strp_wstr. unfold WriterSpec.wstr.
    destruct p; reflexivity. }
  rewrite (G 0%nat). reflexivity.
Qed.

Lemma s10v_zsum : forall tv p d,
  TxModel.zsum (TxModel.tv_calls tv p d) = Z.of_nat (length (concat (WriterValue.wvpieces tv p d))).
Proof. intros tv p d. unfold TxModel.tv_calls. rewrite TxModel.zsum_plen, s10v_tvp_wv. reflexivity. Qed.

(* the extra env words' layout (ExUtf8.v's EU): 32 the shadow base, and the node's four pointer / count fields as
   ATOMS 33 str, 34 kids, 35 keys, 36 n; the register atoms are 2 sp, 10 t, 11 v, 12 pretty, 13 depth *)
Definition TV_BX : sv := SOff 32 0.
Definition TV_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the node's five read fields (type, str, kids, keys, n), as the C layout places them *)
Definition tv_node_chunks (ty : Z) : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
   YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0))].
Definition tv_SH : list shent := [mkSHE 11 0 56].
Definition tv_facts (cs : list acond) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 (2 ^ 47 - 56) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] cs [].

(* the boolean read-only checker's soundness (S1ImgA.v in_ro_b, image-free) *)
Lemma s10v_in_ro_b_sound : forall segs rlo rhi a, S1ImgCheck.in_ro_b segs rlo rhi a = true -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold S1ImgCheck.in_ro_b in H. apply orb_prop in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs|]. split; [exact H0 | lia].
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* one read-only image byte read back through the view: the client map holds the image's byte or none *)
Lemma s10v_mbyte_of_aview : forall (sg : list Segment) (H : word -> bool) mem a (bb : byte),
  aview sg H mem a = Some (bv_unsigned bb) -> mbyte sg (mrestrict H mem) a = Some bb.
Proof.
intros sg H mem a bb E. unfold aview in E.
destruct (mbyte sg (mrestrict H mem) a) as [b'|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* two byte ranges, one off the image and one inside it, are apart *)
Lemma tv_apart_img : forall (sg : list Segment) p n q m, (forall a, p <= a < p + n -> ~ in_img sg a) ->
  (forall a, q <= a < q + m -> in_img sg a) -> 0 < n -> 0 < m -> p + n <= q \/ q + m <= p.
Proof.
intros sg p n q m Hp Hq Hn Hm. destruct (Z_le_gt_dec (p + n) q) as [h|h]; [left; exact h|].
destruct (Z_le_gt_dec (q + m) p) as [h'|h']; [right; exact h'|]. exfalso.
apply (Hp (Z.max p q)); [lia|]. apply Hq. lia.
Qed.

(* the string's shadow facts, from its block's prhtx_bvis, at the strlen length n <= k *)
Lemma tv_hull_sub : forall (v : Z -> option Z) x n k, 0 <= x -> 0 < n <= k ->
  shadow_hull_vis v x k -> shadow_hull_vis v x n.
Proof.
intros v x n k H0 Hn H s Hs. apply H. unfold shadow_addr in *.
assert ((SHADOW_OFF + (x + n - 1) / 8) / 8 <= (SHADOW_OFF + (x + k - 1) / 8) / 8).
{ apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

(* the node's shadow pointer `(v >> 3) + shadow base` (B 0x854a4 / 0x854ac), as the run leaves it in s2
   (S10TxStrGlue.v ts_alias_shadow's arithmetic, here at the word level) *)
Lemma tv_shadow_word : forall (x b : word) F, bv_unsigned x = F -> bv_unsigned b = SHADOW_OFF -> 0 <= F < 2 ^ 47 ->
  alu64 ALU_ADD (alu64 ALU_SRL x (Z_to_bv 64 3)) b = Z_to_bv 64 (shadow_addr F).
Proof.
intros x b F HF HB HFr.
rewrite <- (Z_to_bv_bv_unsigned 64 x), <- (Z_to_bv_bv_unsigned 64 b), HF, HB.
rewrite !zalu64_sound. f_equal.
unfold zalu64, zcanon, M64, zalu_raw, shadow_addr, SHADOW_OFF.
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (HF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small F (2 ^ 64)) by lia.
rewrite !(Z.mod_small (F / 8) (2 ^ 64)) by lia.
rewrite (Z.mod_small 2147450880 (2 ^ 64)) by lia.
rewrite (Z.mod_small (F / 8 + 2147450880) (2 ^ 64)) by lia.
lia.
Qed.

(* a region of a run's final state, read back from st_ok (S10TxStrGlue.v ts_region_nth, at st_ok rather than
   st_ok_pi: a run that stops at a call hands over st_ok of the state at the callee's entry) *)
Section r. Context {fx : YK11.FPState}.
Lemma tv_region_nth : forall (sg : list Segment) E ss ms i r, st_ok sg E ss ms -> nth_error (ss_mem ss) i = Some r ->
  YP09.region_ok sg E (ms_mem ms) r.
Proof.
intros sg E ss ms i r HS Hi. destruct (st_ok_mem_ok sg E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
End r.
Lemma tv_U_lit0 : forall E, U E (SLit 0) mod 2 ^ (8 * Z.of_N 8) = 0.
Proof. intros E. vm_compute. reflexivity. Qed.

(* one 8-byte frame slot of a run's final state, read back as a concrete value: the chunk at offset od of the
   stack region (base atom 2, the entry sp), holding the entry register r (atom k) or the literal 0 *)
Ltac tv_savef HR0 Usp EG sp0 od k r :=
  let V := fresh "V" in
  pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ od 8%N (SOff k 0) HR0 Usp
    ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
  cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V;
  rewrite ts_U_atom_mod in V; rewrite (EG k r eq_refl ltac:(lia)) in V;
  lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 + od) by (unfold TV_FRAME_B; lia) end;
  exact V.

(* DELETE when S10TxValGlue lands: B-local copy of S10TxValue.v (walk-S10 7623a0781f8) image-free open-arm pieces
   (tvA_go / tvO_go / tv_close, tvp_arr / tvp_obj, the item extraction tv_items_nth / tv_mems_nth) *)
(* ---- the open arm's pieces (TxModel.tvp of an array / object), named ---- *)
Fixpoint tvA_go (p : bool) (d : Z) (i : nat) (l : list PjTree.jv) : list (list Z) :=
  match l with
  | [] => []
  | x :: r => WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ TxModel.tvp x p (d + 1) ++ tvA_go p d (S i) r
  end.
Fixpoint tvO_go (p : bool) (d : Z) (i : nat) (l : list (list Z * PjTree.jv)) : list (list Z) :=
  match l with
  | [] => []
  | (k, x) :: r => WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ TxModel.strp k ++ [[58]] ++
                   (if p then [[32]] else []) ++ TxModel.tvp x p (d + 1) ++ tvO_go p d (S i) r
  end.
Definition tv_close {A : Type} (l : list A) (p : bool) (d : Z) : list (list Z) :=
  match l with [] => [] | _ :: _ => WriterValue.wind p d end.

Lemma tvp_arr : forall items p d,
  TxModel.tvp (PjTree.JArr items) p d = [91] :: tvA_go p d 0 items ++ tv_close items p d ++ [[93]].
Proof.
intros items p d. cbn [TxModel.tvp]. f_equal. f_equal.
generalize 0%nat as i. induction items as [|x r IH]; intros i; [reflexivity|].
cbn [tvA_go]. rewrite <- IH. reflexivity.
Qed.
Lemma tvp_obj : forall members p d,
  TxModel.tvp (PjTree.JObj members) p d = [123] :: tvO_go p d 0 members ++ tv_close members p d ++ [[125]].
Proof.
intros members p d. cbn [TxModel.tvp]. f_equal. f_equal.
generalize 0%nat as i. induction members as [|[k x] r IH]; intros i; [reflexivity|].
cbn [tvO_go]. rewrite <- IH. reflexivity.
Qed.
Lemma tvA_go_app : forall p d l1 l2 i, tvA_go p d i (l1 ++ l2) = tvA_go p d i l1 ++ tvA_go p d (i + length l1) l2.
Proof.
intros p d l1. induction l1 as [|x r IH]; intros l2 i; cbn [app tvA_go length].
- rewrite Nat.add_0_r. reflexivity.
- rewrite IH, Nat.add_succ_r, <- !app_assoc. reflexivity.
Qed.
Lemma tvO_go_app : forall p d l1 l2 i, tvO_go p d i (l1 ++ l2) = tvO_go p d i l1 ++ tvO_go p d (i + length l1) l2.
Proof.
intros p d l1. induction l1 as [|[k x] r IH]; intros l2 i; cbn [app tvO_go length].
- rewrite Nat.add_0_r. reflexivity.
- rewrite IH, Nat.add_succ_r. cbn [Nat.add]. rewrite <- !app_assoc. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma tvA_go_one : forall p d i x, tvA_go p d i [x] =
  WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ TxModel.tvp x p (d + 1).
Proof. intros. cbn [tvA_go]. rewrite !app_nil_r. reflexivity. Qed.
Lemma tvO_go_one : forall p d i k x, tvO_go p d i [(k, x)] =
  WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ TxModel.strp k ++ [[58]] ++ (if p then [[32]] else []) ++
  TxModel.tvp x p (d + 1).
Proof. intros. cbn [tvO_go]. rewrite !app_nil_r. reflexivity. Qed.
(* the plen / concat of a pieces list *)
Lemma tv_plen_app : forall P Q, TxModel.plen (P ++ Q) = TxModel.plen P ++ TxModel.plen Q.
Proof. intros. apply TxModel.plen_app. Qed.
Lemma tv_len_concat_app : forall P Q : list (list Z),
  length (concat (P ++ Q)) = (length (concat P) + length (concat Q))%nat.
Proof. intros. rewrite concat_app, length_app. reflexivity. Qed.

(* ---- the i-th item of an array / member of an object (the reader's pj_itemsR / pj_memsR) ---- *)
Lemma tv_items_nth : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D i, PRH_Reader.pj_itemsR P a l D ->
  (i < length l)%nat -> exists D1, P (a + 56 * Z.of_nat i) (nth i l PjTree.JNull) D1 /\ incl D1 D.
Proof.
intros P l. induction l as [|u r IH]; intros a D i H Hi; cbn [length] in Hi; [lia|].
destruct H as (D1 & D2 & E & HP & HR). destruct i as [|i].
- exists D1. split; [replace (a + 56 * Z.of_nat 0) with a by lia; exact HP|].
  subst D. intros x Hx. apply in_or_app. left. exact Hx.
- destruct (IH (a + 56) D2 i HR ltac:(lia)) as (D3 & H3 & Hinc). exists D3. split.
  + replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact H3.
  + subst D. intros x Hx. apply in_or_app. right. exact (Hinc x Hx).
Qed.
Lemma tv_mems_nth : forall segs m lb (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i,
  PRH_Reader.pj_memsR segs m lb P a ka l D -> (i < length l)%nat ->
  exists x k D1, PRH_Reader.rd_u64 segs m (ka + 8 * Z.of_nat i) x /\
    PRH_Reader.pj_cstrR segs m lb x k (fst (nth i l ([], PjTree.JNull))) /\ In (x, k) D /\
    P (a + 56 * Z.of_nat i) (snd (nth i l ([], PjTree.JNull))) D1 /\ incl D1 D.
Proof.
intros segs m lb P l. induction l as [|[nm u] r IH]; intros a ka D i H Hi; cbn [length] in Hi; [lia|].
destruct H as (x & k & D1 & D2 & E & Hx & Hc & HP & HR). destruct i as [|i].
- exists x, k, D1. cbn [nth fst snd].
  replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia.
  split; [exact Hx|]. split; [exact Hc|]. split; [subst D; left; reflexivity|]. split; [exact HP|].
  subst D. intros y Hy. right. apply in_or_app. left. exact Hy.
- destruct (IH (a + 56) (ka + 8) D2 i HR ltac:(lia)) as (x' & k' & D3 & H1 & H2 & H3 & H4 & H5).
  exists x', k', D3. cbn [nth].
  replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
  split; [exact H1|]. split; [exact H2|]. split; [subst D; right; apply in_or_app; right; exact H3|].
  split; [exact H4|]. subst D. intros y Hy. right. apply in_or_app. right. exact (H5 y Hy).
Qed.
(* DELETE when S10TxValGlue lands: B-local copy of S10TxValue.v (walk-S10 339382e2cb0) image-free item model
   (tvI_key / tvI_go and their lemmas, tv_firstn_S, tv_aregs13) *)
(* ---- one item model for both brackets: an array item has no key, an object member its key ---- *)
Definition tvI_key (p : bool) (ko : option (list Z)) : list (list Z) :=
  match ko with None => [] | Some k => TxModel.strp k ++ [[58]] ++ (if p then [[32]] else []) end.
Fixpoint tvI_go (p : bool) (d : Z) (i : nat) (l : list (option (list Z) * PjTree.jv)) : list (list Z) :=
  match l with
  | [] => []
  | (ko, x) :: r => WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ tvI_key p ko ++ TxModel.tvp x p (d + 1) ++
                    tvI_go p d (S i) r
  end.
Lemma tvA_go_I : forall p d items i, tvA_go p d i items = tvI_go p d i (map (fun x => (None, x)) items).
Proof. intros p d items. induction items as [|x r IH]; intros i; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma tvO_go_I : forall p d members i,
  tvO_go p d i members = tvI_go p d i (map (fun kx => (Some (fst kx), snd kx)) members).
Proof.
intros p d members. induction members as [|[k x] r IH]; intros i; [reflexivity|]. cbn [tvO_go tvI_go map fst snd].
rewrite IH. unfold tvI_key. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma tvI_go_app : forall p d l1 l2 i, tvI_go p d i (l1 ++ l2) = tvI_go p d i l1 ++ tvI_go p d (i + length l1) l2.
Proof.
intros p d l1. induction l1 as [|[ko x] r IH]; intros l2 i; cbn [app tvI_go length].
- rewrite Nat.add_0_r. reflexivity.
- rewrite IH, Nat.add_succ_r. cbn [Nat.add]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma tvI_go_one : forall p d i ko x, tvI_go p d i [(ko, x)] =
  WriterValue.wcomma i ++ WriterValue.wind p (d + 1) ++ tvI_key p ko ++ TxModel.tvp x p (d + 1).
Proof. intros. cbn [tvI_go]. rewrite !app_nil_r. reflexivity. Qed.
(* the pieces after i items *)
Lemma tv_firstn_S : forall {A : Type} (l : list A) i dflt, (i < length l)%nat ->
  firstn (S i) l = firstn i l ++ [nth i l dflt].
Proof.
intros A l. induction l as [|x r IH]; intros i dflt Hi; cbn [length] in Hi; [lia|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. rewrite (IH i dflt ltac:(lia)). reflexivity.
Qed.
Lemma tvI_go_firstn_S : forall p d l i, (i < length l)%nat ->
  tvI_go p d 0 (firstn (S i) l) = tvI_go p d 0 (firstn i l) ++ tvI_go p d i [nth i l (None, PjTree.JNull)].
Proof.
intros p d l i Hi. rewrite (tv_firstn_S l i (None, PjTree.JNull) Hi), tvI_go_app.
rewrite firstn_length_le by lia. reflexivity.
Qed.

(* the callee-saved registers one by one *)
Lemma tv_aregs13 : forall regs rgs : bvmap 5 word,
  getr rgs 2 = getr regs 2 -> getr rgs 3 = getr regs 3 -> getr rgs 4 = getr regs 4 -> getr rgs 8 = getr regs 8 ->
  getr rgs 9 = getr regs 9 -> getr rgs 18 = getr regs 18 -> getr rgs 19 = getr regs 19 ->
  getr rgs 20 = getr regs 20 -> getr rgs 21 = getr regs 21 -> getr rgs 22 = getr regs 22 ->
  getr rgs 23 = getr regs 23 -> getr rgs 24 = getr regs 24 -> getr rgs 25 = getr regs 25 ->
  getr rgs 26 = getr regs 26 -> getr rgs 27 = getr regs 27 -> aregs_preserved regs rgs.
Proof.
intros regs rgs E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 r Hr. unfold acallee_saved in Hr.
assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hr' as [-> | Hr']; [assumption|]). subst r. assumption.
Qed.
(* ---- end of the B-local copy's image-free part (the rest of the copy needs the Section's hypotheses: below) ---- *)

(* ---- the symbolic entry state of tx_value, at the whole-range listing of image B ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
(* preset's allocator parameters (CfParamsPreset.v): cf_head = 16 places every harness string at least a head past
   kHighMemBeg, which the strlen rule's amem_range8 asks of the number arm's text *)
#[local] Existing Instance CfParams_preset.
Context {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* THE RE-HIDE (the free / realloc move): after a call that can free or realloc a live block, the world step is wle'
   at the fixed zone RZ_cf (YA0nH.v wle', YGcfRehidePost.v RZ_cf), and a segment that crosses such a call concludes
   SRr' there. Every call tx_value makes reaches tx_put's realloc, so every cut after the opening call is at WR *)
#[local] Notation WR := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation SRW := (SRr' SEGS YGcfRehidePost.RZ_cf).
(* the image numbers the class carries, generated for image B (PRH_ImgB.v) *)
#[local] Existing Instance prh_img_B.
(* image A's listing instances are loaded through the image-generic A files this one requires; B's come first, so
   an implicit listing argument that no type pins resolves to image B *)
#[local] Existing Instance PI_prog_B | 0.
#[local] Existing Instance PL_prog_B | 0.

(* the frame tx_value fills in its prologue and dispatch (sp1 = the frame's own sp = the entry sp - 192):
   16(sp) the UBSan `andi a0,a1,7` result 0, 24(sp) the depth argument a3, 72(sp) the shadow base; and the
   thirteen saves ra, s0 .. s11 at 184(sp) .. 88(sp), which the epilogue reloads *)
Definition tv_slots_B (W : world SEGS) (m : word -> option byte) (sp1 d : Z) : Prop :=
  val_mem SEGS (rdW W m) (sp1 + 16) 8 0 /\
  val_mem SEGS (rdW W m) (sp1 + 24) 8 d /\
  val_mem SEGS (rdW W m) (sp1 + 72) 8 SHADOW_OFF.
Definition tv_saves_B (W : world SEGS) (m : word -> option byte) (sp1 : Z) (regs : bvmap 5 word) : Prop :=
  val_mem SEGS (rdW W m) (sp1 + 184) 8 (bv_unsigned (getr regs 1)) /\
  val_mem SEGS (rdW W m) (sp1 + 176) 8 (bv_unsigned (getr regs 8)) /\
  val_mem SEGS (rdW W m) (sp1 + 168) 8 (bv_unsigned (getr regs 9)) /\
  val_mem SEGS (rdW W m) (sp1 + 160) 8 (bv_unsigned (getr regs 18)) /\
  val_mem SEGS (rdW W m) (sp1 + 152) 8 (bv_unsigned (getr regs 19)) /\
  val_mem SEGS (rdW W m) (sp1 + 144) 8 (bv_unsigned (getr regs 20)) /\
  val_mem SEGS (rdW W m) (sp1 + 136) 8 (bv_unsigned (getr regs 21)) /\
  val_mem SEGS (rdW W m) (sp1 + 128) 8 (bv_unsigned (getr regs 22)) /\
  val_mem SEGS (rdW W m) (sp1 + 120) 8 (bv_unsigned (getr regs 23)) /\
  val_mem SEGS (rdW W m) (sp1 + 112) 8 (bv_unsigned (getr regs 24)) /\
  val_mem SEGS (rdW W m) (sp1 + 104) 8 (bv_unsigned (getr regs 25)) /\
  val_mem SEGS (rdW W m) (sp1 + 96) 8 (bv_unsigned (getr regs 26)) /\
  val_mem SEGS (rdW W m) (sp1 + 88) 8 (bv_unsigned (getr regs 27)).

(* the env of the entry: the image's atoms (Eimg at PI_prog_B) over the registers and the five extra words *)
Definition EV_B (regs : bvmap 5 word) (str kids keys n : Z) : env :=
  Eimg (L := B_prog_listing) (PI := PA)
    (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n]).
Definition tv_regions_B (ty : Z) : smem :=
  [ stack_region TV_FRAME_B; got_regionP; bcell_regionP 32;
    YP09.mkRegion (Some 11%nat) 0 56 0 0 (tv_node_chunks ty);
    YP09.mkRegion (Some (A_OBJ 2)) TV_JT_OFF_B (TV_JT_OFF_B + 28) 0 0 tv_jt_chunks_B ].
Definition ss_tv_B (eo ty : Z) (cs : list acond) : sstate :=
  mkSS eo sr_atoms (tv_regions_B ty) None (tv_facts cs).

Lemma TV_PC_sigma_B : BASE + TV_PC_B = SIGMA AS_tx_value.
Proof. exact TV_PC_val_B. Qed.

(* image fact (A's HOBJ, here proved): the shadow-base GOT word A_OBJ 0 and the shadow cell A_OBJ 12 lie in the
   image, by S1ImgA.v's image-free checker in_img_b run on B's segments *)
Lemma tv_obj_img_b_B : YP08.zallb (S1ImgCheck.in_img_b SEGS) (VAL (A_OBJ 0)) 8 = true /\
  YP08.zallb (S1ImgCheck.in_img_b SEGS) (VAL (A_OBJ 12)) 8 = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma HOBJ : forall i a, (i = 0 \/ i = 12)%nat -> VAL (A_OBJ i) <= a < VAL (A_OBJ i) + 8 -> in_img SEGS a.
Proof.
intros i a Hi Ha. apply S1ImgCheck.in_img_b_sound. destruct tv_obj_img_b_B as [H0 H12].
destruct Hi as [-> | ->]; [exact (YP08.zallb_sound _ _ _ a H0 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
  | exact (YP08.zallb_sound _ _ _ a H12 ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))].
Qed.

(* the 28 bytes of the jump table are read-only image bytes of the pinned image: the checker in_ro_b on B's segments *)
Lemma tv_jt_ro_b_B : YP08.zallb (S1ImgCheck.in_ro_b SEGS RLO RHI) (VAL (A_OBJ 2) + TV_JT_OFF_B) 28%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tv_jt_ro_B : forall i, 0 <= i < 28 -> in_roP SEGS RLO RHI (VAL (A_OBJ 2) + TV_JT_OFF_B + i).
Proof.
intros i Hi. apply s10v_in_ro_b_sound.
exact (YP08.zallb_sound _ _ _ (VAL (A_OBJ 2) + TV_JT_OFF_B + i) tv_jt_ro_b_B ltac:(lia)).
Qed.

(* the jump table's bytes in the image are the table words *)
Lemma tv_jt_rom_B : forall i k, (i < 7)%nat -> (k < 4)%nat ->
  seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + (TV_JT_OFF_B + 4 * Z.of_nat i) + Z.of_nat k)) =
  Some (Z_to_bv 8 (le_byte (nth i tv_jt_words_B 0) 4 k)).
Proof.
intros i k Hi Hk.
do 7 (destruct i as [|i]; [do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

(* the table's bytes are image bytes *)
Lemma tv_jt_img_B : forall a, VAL (A_OBJ 2) + TV_JT_OFF_B <= a < VAL (A_OBJ 2) + TV_JT_OFF_B + 28 -> in_img SEGS a.
Proof.
intros a Ha.
assert (Hi : 0 <= a - (VAL (A_OBJ 2) + TV_JT_OFF_B) < 28) by (clear - Ha; lia).
pose proof (tv_jt_ro_B (a - (VAL (A_OBJ 2) + TV_JT_OFF_B)) Hi) as Hro.
replace (VAL (A_OBJ 2) + TV_JT_OFF_B + (a - (VAL (A_OBJ 2) + TV_JT_OFF_B))) with a in Hro by (clear; lia).
destruct Hro as [(sg & Hin & _ & Hr) | Hr].
- exists sg. split; [exact Hin | exact Hr].
- exact (@pa_relro_img _ _ PA _ Hr).
Qed.

(* ---- INSTANCE WITNESSES (unit ruling 16:45Z) of the image premises Section f takes over an abstract B, closed by
   computation at image B''s asyms YD2l.TfibB (generated from fuzz_preset.asan-ubsan, unstripped twin c90d4fa54d43 of
   d663f82d), in BTxLine.v's style (its tl_lit_byte_TfibB / tl_not_in_zr_b); the shadow cells' values are COMPUTED
   by vm_compute, never written as addresses ---- *)
(* WITNESS of tv_jt_own: the 28 bytes of the jump table (the only read-only bytes the dispatch reads) are not runtime
   owned and not errno at TfibB (replaces the old pal_ro_ok, FALSE at B': Tfib_owned_static has read-only ranges) *)
Lemma tv_jt_own_TfibB : forall a, VAL (A_OBJ 2) + TV_JT_OFF_B <= a < VAL (A_OBJ 2) + TV_JT_OFF_B + 28 ->
  ~ Exists (in_zr a) (as_owned_static YD2l.TfibB) /\ ~ (as_errno YD2l.TfibB <= a < as_errno YD2l.TfibB + 4).
Proof.
intros a Ha.
assert (Eo2v : VAL (A_OBJ 2) = 0x10000) by (vm_compute; reflexivity).
rewrite Eo2v in Ha. unfold TV_JT_OFF_B in Ha.
cbn [as_owned_static as_errno YD2l.TfibB]. split; [|unfold YF0m.TFIB_ERRNO; lia].
apply BTxLine.tl_not_in_zr_b.
assert (E : exists i, (i < 28)%nat /\ a = 0x10000 + 0x10f34 + Z.of_nat i)
  by (exists (Z.to_nat (a - (0x10000 + 0x10f34))); split; lia).
destruct E as (i & Hi & ->).
do 28 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.
(* one literal byte at TfibB with its granule's const-shadow cell v (BTxLine.v tl_lit_byte_TfibB) *)
Local Ltac tv_lit_one v :=
  apply (BTxLine.tl_lit_byte_TfibB _ v); [lia | vm_compute; reflexivity | vm_compute; reflexivity |
    unfold YF0m.TFIB_ERRNO; lia | vm_compute; repeat (first [left; reflexivity | right]) | right; split; vm_compute; reflexivity].
(* WITNESS of tv_lit_img: the ten literals tx_value hands tx_put, each byte read-only, not owned, not errno, its
   granule's const-shadow cell (5 for "true" / "null", 6 for "false", 2 for each one-byte literal: the number of
   addressable bytes of the granule, string + NUL) in YF0m.Tfib_const_shadow; the bounds are the instance's pa_lo /
   pa_hi, read by vm_compute *)
Lemma tv_lit_img_TfibB : Forall (fun sl => kept_img (PA := PA) YD2l.TfibB (VAL (A_OBJ 2) + fst sl) (snd sl))
  [(69472, 4); (69504, 5); (69536, 4); (70144, 1); (70176, 1); (70208, 1); (70240, 1); (70272, 1); (70304, 1);
   (70336, 1)].
Proof.
assert (Eo2v : VAL (A_OBJ 2) = 0x10000) by (vm_compute; reflexivity).
assert (HB : @pa_lo _ _ PA + 64 <= VAL (A_OBJ 2) + 69472 /\ VAL (A_OBJ 2) + 70336 + 1 + 64 <= @pa_hi _ _ PA)
  by (vm_compute; split; intro H; discriminate H).
destruct HB as [HB1 HB2]. rewrite Eo2v in HB1, HB2 |- *.
repeat apply Forall_cons. all: try apply Forall_nil.
all: cbn [fst snd]; unfold kept_img; (split; [lia|]); (split; [lia|]); intros a Ha.
- assert (Ea : a = 0x10000 + 69472 \/ a = 0x10000 + 69472 + 1 \/ a = 0x10000 + 69472 + 2 \/ a = 0x10000 + 69472 + 3) by lia.
  destruct Ea as [-> | [-> | [-> | ->]]]; tv_lit_one 5.
- assert (Ea : a = 0x10000 + 69504 \/ a = 0x10000 + 69504 + 1 \/ a = 0x10000 + 69504 + 2 \/ a = 0x10000 + 69504 + 3 \/
    a = 0x10000 + 69504 + 4) by lia.
  destruct Ea as [-> | [-> | [-> | [-> | ->]]]]; tv_lit_one 6.
- assert (Ea : a = 0x10000 + 69536 \/ a = 0x10000 + 69536 + 1 \/ a = 0x10000 + 69536 + 2 \/ a = 0x10000 + 69536 + 3) by lia.
  destruct Ea as [-> | [-> | [-> | ->]]]; tv_lit_one 5.
- assert (Ea : a = 0x10000 + 70144) by lia. subst a. tv_lit_one 2.
- assert (Ea : a = 0x10000 + 70176) by lia. subst a. tv_lit_one 2.
- assert (Ea : a = 0x10000 + 70208) by lia. subst a. tv_lit_one 2.
- assert (Ea : a = 0x10000 + 70240) by lia. subst a. tv_lit_one 2.
- assert (Ea : a = 0x10000 + 70272) by lia. subst a. tv_lit_one 2.
- assert (Ea : a = 0x10000 + 70304) by lia. subst a. tv_lit_one 2.
- assert (Ea : a = 0x10000 + 70336) by lia. subst a. tv_lit_one 2.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the allocator laws at hl = cf_head (AR_laws_x of the P'' engine set as the kit's cut 7cdbb61b5fa0 carries it: 25 fields,
   YCbqG.v 219748197d6b) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B: PALib's fields). Taken at PI_prog_B, the whole-program
   instance (as BTxString.v's PAL); the shadow-base GOT word and cell are the listing's object atoms 0 and 12.
   Witness: lib/B/PALibB.v exvi_eh_palib : PALib (PI := PI_prog_B) YD2l.TfibB *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B; repair of the old pal_ro_ok, which is FALSE at B'): the
   28 bytes of the jump table the dispatch reads are not runtime-owned and not errno. Witness tv_jt_own_TfibB *)
Hypothesis tv_jt_own : forall a, VAL (A_OBJ 2) + TV_JT_OFF_B <= a < VAL (A_OBJ 2) + TV_JT_OFF_B + 28 ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* MARKED STAND-IN (owner c-libc-stdio's strlen row): the strlen wrapper __wrap_strlen (the number arm's `jal
   wrapper_strlen`) realizes the READ-ONLY strlen text with the memnorm keep (YGcallMxmn.v astrlen_realizes_xrom: its
   premise is fpre's arodata_okP). Witness lib/AU/PSstrRo.v ps_strlen_xrom_B 45e63604063e. The number arm's string is
   in a live harness block (blk_img_x), and all 90 Tfib_owned_static ranges lie in the image [0x10000, 0x601000), so
   the read-only row gives every byte strlen reads (measured 20:2xZ) *)
Hypothesis ASx : YGcallMxmn.astrlen_realizes_xrom SEGS B ARx RLO RHI (SIGMA AS___wrap_strlen).
Let HBgot := pal_got_shadow (PI := PA) B PAL.
Let HBcell := pal_cell (PI := PA) B PAL.

(* ---- DELETE when S10TxValGlue lands: B-local copy of S10TxValue.v (walk-S10 d356ed78f634) generic helpers (the part
   over the Section's hypotheses) ---- *)
(* the node's home (the Tx part's prhtx_home: a harness block of Lam, or one fake frame of S) is client memory, away from the
   image and the shadow band *)
Lemma tv_node_home : forall ly S Hp W mem md Lam peak cnt fail ran most own v,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhtx_home Lam ly S v 56 ->
  4096 <= v /\ v + 56 <= YM05.alloc_ceiling /\ in_app v 56 /\ (forall a, v <= a < v + 56 -> ~ in_img SEGS a).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own v HAR HL [(b & m & Hin & Hb & Hm) | (cid & pos & Hin & Hfr)].
- pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
  pose proof (@cf_head_nonneg CfParams_preset) as Hh0.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & Happ & _).
  assert (Hrq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
  rewrite Hrq in Hc, Happ.
  split; [lia|]. split; [lia|]. split.
  + unfold in_app in *. lia.
  + intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HAR Hab). rewrite Hrq. lia.
- destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (H4096 & Hfc & Happ).
  pose proof (Hfr v ltac:(lia)) as Hlo. pose proof (Hfr (v + 55) ltac:(lia)) as Hhi.
  unfold frame_rng, in_zr in Hlo, Hhi. cbn [fst snd] in Hlo, Hhi.
  split; [lia|]. split; [lia|]. split.
  + unfold in_app in *. lia.
  + intros a Ha. apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos a HAR Hin). lia.
Qed.

(* ---- THE MEMNORM KEEP (the kit's m-form posts, PRH_Base.v fQmn: memnorm mem -> memnorm mem'): every run
   goes through YC1fPx's memory-invariant runner at P := TVMN m0, "memnorm at the anchor m0 gives memnorm here", whose
   laws are YSRrMemnorm's (srr_inv_laws_imp over srr_inv_laws_memnorm_k); a branch (paj_branch) and a `jr` (SRr_jr_pi)
   keep the memory ---- *)
Definition TVMN (m0 m : word -> option byte) : Prop := YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m.
Lemma TVMN_laws : forall m0, srr_inv_laws SEGS (TVMN m0).
Proof. intros m0. exact (YSRrMemnorm.srr_inv_laws_imp SEGS _ m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)). Qed.
Lemma TVMN_refl : forall m, TVMN m m.
Proof. intros m H. exact H. Qed.
Lemma TVMN_trans : forall m0 m1 m2, TVMN m0 m1 -> TVMN m1 m2 -> TVMN m0 m2.
Proof. intros m0 m1 m2 H1 H2 H. exact (H2 (H1 H)). Qed.
(* the runner over the S10 journal (prh_pst the statics), keeping TVMN m0 *)
Let RUNI (m0 : word -> option byte) :=
  paj_run_x_inv (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (TVMN m0) (TVMN_laws m0).
(* the same runner over the journal at WR (YC1fPx.v paj_run_x_invR: R and its two laws after P's), for the cuts after
   the opening call *)
Let RUNIR (m0 : word -> option byte) :=
  paj_run_x_invR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (TVMN m0) (TVMN_laws m0) WR
    (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
(* a segment at SRr whose post is generic serves a caller at SRr': run it to the post "the world is still Wc and SRr'
   holds from here" (SRr_SRr' lifts the run, SRr'_bind continues at Wc). The four leaf runs (tv_run_lit_B,
   tv_run_str_B, tv_run_num_B, tv_run_open_B) call no free, so they keep their SRr statements and their callers
   use them through this lemma *)
Lemma tv_srr_then : forall (Wc : world SEGS) c (Q : world SEGS -> config -> Prop),
  SRr SEGS Wc c (fun W' c' => W' = Wc /\ SRW Wc c' Q) -> SRW Wc c Q.
Proof.
intros Wc c Q H. apply (SRr'_bind SEGS YGcfRehidePost.RZ_cf Wc c _ Q (SRr_SRr' SEGS YGcfRehidePost.RZ_cf Wc c _ H)).
intros W' c' _ (-> & H'). exact H'.
Qed.
(* its continuation: a state that already has SRr' at Wc is the post of the empty run *)
Lemma tv_srr_now : forall (Wc : world SEGS) c (Q : world SEGS -> config -> Prop),
  SRW Wc c Q -> SRr SEGS Wc c (fun W' c' => W' = Wc /\ SRW Wc c' Q).
Proof. intros Wc c Q H. apply SRr_ret. split; [reflexivity | exact H]. Qed.

(* the return pcs of the tx_* calls tx_value makes (offsets from BASE: the open bracket's 0x8550c and the loop's L / C1
   / T / K / Co / Sp / I segments) lie below the ceiling, as the callee texts' fpre asks (raZ < YM05.alloc_ceiling):
   PRW_StepKit.pa_slot_lt_ceil_b on each CLOSED slot, here and not inside a walk proof (vm_compute in a large goal runs
   away) *)
Definition TV_RETS_B : list Z := [15936; 16100; 16120; 16236; 16252; 16272; 16364; 16440].
Lemma tv_ret_ceil : forall off, In off TV_RETS_B -> BASE + off < YM05.alloc_ceiling.
Proof.
intros off Hin. unfold TV_RETS_B in Hin.
repeat (destruct Hin as [<- | Hin];
  [apply (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA)); [lia | vm_compute; reflexivity] |]).
destruct Hin.
Qed.

(* the frame write permission of every run: tx_value's own frame below the entry sp, inside the widened journal's
   window (STK + dw) (sp + dw); every other region is read-only *)
Ltac tv_awr rg dw Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
  [ reflexivity
  | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
    rewrite ?ew_havoc_old by (cbv; lia); rewrite Usp; lia
  | cbn [YP09.r_wlo stack_region]; lia
  | cbn [YP09.r_whi stack_region]; lia
  | repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil ].

(* a run's memory change lies in its writable regions: here only tx_value's own frame (FuzzStrdup.v's
   sd_aview_of_frame, c-omx-alloc) *)
Lemma tv_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* the view outside the frame [sp - fr, sp) is kept by the run whose frame_of is K *)
Ltac tv_keep K H rg Wx HU fr :=
  lazymatch type of K with
  | frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
    assert (H : forall tka, 0 <= tka < 2 ^ 64 -> ~ (spZ rg - fr <= tka < spZ rg) ->
      aview SEGS (w_H Wx) mB tka = aview SEGS (w_H Wx) mA tka)
    by (intros tka tkHa tkHn; apply (tv_aview_of_frame Wx Ex rsx mA mB tka K); [|exact tkHa];
        intros (tkr & tkHin & tkHr); vm_compute in tkHin;
        repeat (destruct tkHin as [tkHin | tkHin]; [subst tkr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in tkHr;
          rewrite ?ew_ewset_other in tkHr by lia; rewrite ?ew_havoc_old in tkHr by (cbv; lia);
          rewrite ?HU in tkHr; lia|]); destruct tkHin)
  end.

(* the number arm's string facts (FuzzStrdup.v's sd_garr8_aview / sd_garr8_move / sd_first_byte / sd_src_ok /
   sd_amr8 / sd_rom_view, restated for the node's text) *)
Lemma tv_garr8_aview : forall (W : world SEGS) m p l j, garr8 SEGS (rdW W m) p l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.
Lemma tv_garr8_move : forall (W : world SEGS) m m' x l, garr8 SEGS (rdW W m) x l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H W) m' (x + Z.of_nat j) = aview SEGS (w_H W) m (x + Z.of_nat j)) ->
  garr8 SEGS (rdW W m') x l.
Proof.
intros W m m' x l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte SEGS (rdW W m') (x + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma tv_first_byte : forall (W : world SEGS) m p cs, Forall (fun c => 0 < c < 256) cs ->
  garr8 SEGS (rdW W m) p (cs ++ [0]) ->
  first_byte SEGS W m p (Z.of_nat (length cs) + 1) 0 (Z.of_nat (length cs)).
Proof.
intros W m p cs Hnz Hg. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) cs 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (tv_garr8_aview W m p (cs ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + assert (Hlt : (Z.to_nat i < length cs)%nat) by lia.
    pose proof (proj1 (Forall_forall _ _) Hnz (nth (Z.to_nat i) cs 0) (nth_In cs 0 Hlt)) as Hc.
    cbv beta in Hc. lia.
- intros _.
  rewrite (tv_garr8_aview W m p (cs ++ [0]) (length cs) Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma tv_src_ok : forall (W : world SEGS) regs m p l, garr8 SEGS (rdW W m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok SEGS W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (tv_garr8_aview W m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.
(* a harness string (a Lam block, its head of cf_head = 16 bytes below it) leaves the strlen rule's 8-byte slack *)
Lemma tv_amr8 : forall ly S Hp W mem md Lam peak cnt fail ran most own s k n,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (s, k) Lam -> 0 <= n <= k ->
  amem_range8 s n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own s k n HAR HL Hin Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran s k _ _ HL Hin) as (Hk0 & Hab & _).
change (@cf_head CfParams_preset) with 16 in Hab.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & Happ & _).
assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hrq in Happ.
unfold amem_range8, in_app, kLowShadowBeg, ASAN_CEIL in *. rewrite C3, C4, C5. lia.
Qed.
Lemma tv_rod_kept : forall (W : world SEGS) m m', arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) m) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) m').
Proof.
intros W m m' H HA a Hro Hn He.
assert (Hi : in_img SEGS a)
  by (destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]).
pose proof (@pa_segs_low _ _ PA a Hi) as Hl. pose proof asan_consts as (C1 & _ & _ & _ & C5).
rewrite HA by lia. exact (H a Hro Hn He).
Qed.
(* ---- end of the B-local copy ---- *)

(* the seven table words as region chunks: each chunk's bytes are the image's (the read-only view) *)
Lemma tv_jt_chunk_ok_B : forall (W : world SEGS) mem E i,
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> bv_unsigned (ew E (A_OBJ 2)) = VAL (A_OBJ 2) ->
  (i < 7)%nat ->
  YP09.chunk_ok SEGS E (rdW W mem) (VAL (A_OBJ 2))
    (YP09.mkChunk (TV_JT_OFF_B + 4 * Z.of_nat i) (CVal 4 (SLit (nth i tv_jt_words_B 0)))).
Proof.
intros W mem E i HRO HE Hi.
set (w := nth i tv_jt_words_B 0).
assert (Hw : 0 <= w < 2 ^ 32) by (subst w; unfold tv_jt_words_B; do 7 (destruct i as [|i]; [cbn; lia|]); lia).
apply (chunk_ok_val SEGS E _ _ _ 4 (SLit w) w);
  [reflexivity | change (8 * Z.of_N 4) with 32; exact Hw | cbn; lia |].
intros k Hk. cbn [N.to_nat] in Hk.
assert (Hro : in_roP SEGS RLO RHI (VAL (A_OBJ 2) + (TV_JT_OFF_B + 4 * Z.of_nat i) + Z.of_nat k)).
{ replace (VAL (A_OBJ 2) + (TV_JT_OFF_B + 4 * Z.of_nat i) + Z.of_nat k)
    with (VAL (A_OBJ 2) + TV_JT_OFF_B + (4 * Z.of_nat i + Z.of_nat k)) by lia.
  apply tv_jt_ro_B. lia. }
assert (Hab : VAL (A_OBJ 2) + TV_JT_OFF_B <= VAL (A_OBJ 2) + (TV_JT_OFF_B + 4 * Z.of_nat i) + Z.of_nat k <
  VAL (A_OBJ 2) + TV_JT_OFF_B + 28) by lia.
destruct (tv_jt_own _ Hab) as [Hno Her].
pose proof (HRO _ Hro Hno Her) as E1. rewrite (tv_jt_rom_B i k Hi Hk) in E1. cbn [option_map] in E1.
exact (s10v_mbyte_of_aview SEGS (w_H W) mem _ _ E1).
Qed.

(* ---- THE ENTRY: the symbolic state ss_tv_B at an entry pc eo, its regions read off the caller's facts ---- *)
Lemma tv_entry_B : forall STK ly S Hp W regs mem md ch eo v ty str kids keys n cs,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> TV_FRAME_B <= STK ->
  getr regs 11 = w64 v ->
  4096 <= v -> v mod 8 = 0 -> v + 56 <= YM05.alloc_ceiling -> in_app v 56 ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS (rdW W mem) v 4 ty ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 40) 8 n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  conds_ok (EV_B regs str kids keys n) cs ->
  st_ok_pi SEGS VAL (EV_B regs str kids keys n) (ss_tv_B eo ty cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + eo)) mem (seg_rom SEGS))) /\
  sh_ok SEGS TV_BX tv_SH (EV_B regs str kids keys n) (rdW W mem).
Proof.
intros STK ly S Hp W regs mem md ch eo v ty str kids keys n cs HPRE HSTK H11 Hv0 Hv8 Hvc Hvapp Hvimg
  Hty Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO Hcs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pal_got_cell (PI := PA) B PAL) as HgcD.
pose proof (@pa_val_range _ _ PA (A_OBJ 0)) as R0. pose proof (@pa_val_range _ _ PA (A_OBJ 12)) as R12.
assert (Eo2v : VAL (A_OBJ 2) = 0x10000) by (vm_compute; reflexivity).
assert (I0 : forall a, VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8 -> in_img SEGS a)
  by (intros a Ha; apply (HOBJ 0); [left; reflexivity | exact Ha]).
assert (I12 : forall a, VAL (A_OBJ 12) <= a < VAL (A_OBJ 12) + 8 -> in_img SEGS a)
  by (intros a Ha; apply (HOBJ 12); [right; reflexivity | exact Ha]).
assert (Hb0 : VAL (A_OBJ 0) <= VAL (A_OBJ 0) < VAL (A_OBJ 0) + 8) by (clear; lia).
assert (Hb0' : VAL (A_OBJ 0) <= VAL (A_OBJ 0) + 7 < VAL (A_OBJ 0) + 8) by (clear; lia).
assert (Hb12 : VAL (A_OBJ 12) <= VAL (A_OBJ 12) < VAL (A_OBJ 12) + 8) by (clear; lia).
assert (Hb12' : VAL (A_OBJ 12) <= VAL (A_OBJ 12) + 7 < VAL (A_OBJ 12) + 8) by (clear; lia).
pose proof (@pa_segs_low _ _ PA _ (I0 _ Hb0)) as L0. pose proof (@pa_segs_low _ _ PA _ (I0 _ Hb0')) as L0'.
pose proof (@pa_segs_low _ _ PA _ (I12 _ Hb12)) as L12. pose proof (@pa_segs_low _ _ PA _ (I12 _ Hb12')) as L12'.
assert (P56 : 0 < 56) by (clear; lia). assert (P8 : 0 < 8) by (clear; lia). assert (P28 : 0 < 28) by (clear; lia).
pose proof (tv_apart_img SEGS v 56 (VAL (A_OBJ 0)) 8 Hvimg I0 P56 P8) as D0.
pose proof (tv_apart_img SEGS v 56 (VAL (A_OBJ 12)) 8 Hvimg I12 P56 P8) as D12.
pose proof (tv_apart_img SEGS v 56 (VAL (A_OBJ 2) + TV_JT_OFF_B) 28 Hvimg tv_jt_img_B P56 P28) as DJ.
assert (DJ0 : VAL (A_OBJ 2) + TV_JT_OFF_B + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 2) + TV_JT_OFF_B).
{ assert (Hb : ((VAL (A_OBJ 2) + TV_JT_OFF_B + 28 <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? VAL (A_OBJ 2) + TV_JT_OFF_B))%bool
    = true) by (vm_compute; reflexivity).
  apply orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; [left|right]; exact Hb. }
assert (DJ12 : VAL (A_OBJ 2) + TV_JT_OFF_B + 28 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 2) + TV_JT_OFF_B).
{ assert (Hb : ((VAL (A_OBJ 2) + TV_JT_OFF_B + 28 <=? VAL (A_OBJ 12)) || (VAL (A_OBJ 12) + 8 <=? VAL (A_OBJ 2) + TV_JT_OFF_B))%bool
    = true) by (vm_compute; reflexivity).
  apply orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; [left|right]; exact Hb. }
unfold kLowMemEnd in *.
set (E := EV_B regs str kids keys n) in *.
set (XL := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n]) in *.
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs XL) k)
  by (intros k Hk; subst E XL; unfold EV_B; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 str) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 kids) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 keys) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold EV_B; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EV_B; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo2 : ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2))) by (subst E; unfold EV_B; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
assert (Hu2 : bv_unsigned (ew E (A_OBJ 2)) = VAL (A_OBJ 2)) by (rewrite Eo2; apply unsigned_lit_small; rewrite Eo2v; lia).
unfold TV_FRAME_B in HSTK.
split.
- rewrite restrict_mkst_fx. unfold ss_tv_B. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold tv_regions_B, stack_region, got_regionP, bcell_regionP, TV_FRAME_B.
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
    * rewrite (VB 11%nat v E11) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      unfold tv_node_chunks.
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      -- apply (chunk_ok_val SEGS E _ v 0 4 (SLit ty) ty); [reflexivity | change (8 * Z.of_N 4) with 32; lia | cbn; lia |].
         rewrite Z.add_0_r. exact Vty.
      -- apply (chunk_ok_val SEGS E _ v 16 8 (SOff 33 0) str);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vstr].
      -- apply (chunk_ok_val SEGS E _ v 24 8 (SOff 34 0) kids);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vkids].
      -- apply (chunk_ok_val SEGS E _ v 32 8 (SOff 35 0) keys);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vkeys].
      -- apply (chunk_ok_val SEGS E _ v 40 8 (SOff 36 0) n);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vn].
    * cbn [base_val]. rewrite Hu2. unfold TV_JT_OFF_B. rewrite Eo2v. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      rewrite <- Eo2v. fold TV_JT_OFF_B. unfold tv_jt_chunks_B.
      constructor; [exact (tv_jt_chunk_ok_B W mem E 0 HRO Hu2 ltac:(lia))|].
      constructor; [exact (tv_jt_chunk_ok_B W mem E 1 HRO Hu2 ltac:(lia))|].
      constructor; [exact (tv_jt_chunk_ok_B W mem E 2 HRO Hu2 ltac:(lia))|].
      constructor; [exact (tv_jt_chunk_ok_B W mem E 3 HRO Hu2 ltac:(lia))|].
      constructor; [exact (tv_jt_chunk_ok_B W mem E 4 HRO Hu2 ltac:(lia))|].
      constructor; [exact (tv_jt_chunk_ok_B W mem E 5 HRO Hu2 ltac:(lia))|].
      constructor; [exact (tv_jt_chunk_ok_B W mem E 6 HRO Hu2 ltac:(lia))|].
      constructor.
  + apply pairwise_disjoint_of_extents. unfold tv_regions_B, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 11%nat v E11) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia.
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia.
    cbn [base_val]. rewrite Usp, Hu2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, TV_FRAME_B. cbn [fst snd].
    unfold TV_JT_OFF_B in *. repeat split; lia.
  + split; [|split; [exact Hcs | exact I]].
    cbn [tv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E11, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold spZ in *.
    repeat match goal with |- _ /\ _ => split end; try lia.
- unfold sh_ok, tv_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E TV_BX 11 v 56 v 0 56).
  + exact HRA.
  + unfold TV_BX. rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia). reflexivity.
  + rewrite (U_atom E 11 v E11) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ---- the three LITERAL arms, measured from the jump table (entries 0, 1, 2 -> 0x857fc / 0x8580c / 0x857bc):
   tag 0 JNull: arm 16688, a1 = .str.3 (band 0x10fa0), a2 = 4; tag 1 JFalse: arm 16704, a1 = .str.2 (0x10f80),
   a2 = 5; tag 2 JTrue: arm 16624, a1 = .str (0x10f60), a2 = 4 (arm = addr - BASE, DERIVED; ent = TV_JT_OFF_B + table
   entry, DERIVED; the lengths are the listing's `li a2,N`, LENGTH) ---- *)
Definition tv_lit_case_B (ty ao ent lo ln : Z) : Prop :=
  (ty, ao, ent, lo, ln) = (0, 16688, 481276, 69536, 4) \/
  (ty, ao, ent, lo, ln) = (1, 16704, 481292, 69504, 5) \/
  (ty, ao, ent, lo, ln) = (2, 16624, 481212, 69472, 4).
Lemma tv_run_lit_B : forall ty ao ent lo ln STK dw ly S Hp W regs mem md ch v str kids keys n (FP : list (Z * Z)) Q,
  tv_lit_case_B ty ao ent lo ln ->
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> TV_FRAME_B <= STK -> fwin (PA := PA) ly W regs mem dw ->
  getr regs 11 = w64 v ->
  4096 <= v -> v mod 8 = 0 -> v + 56 <= YM05.alloc_ceiling -> in_app v 56 ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  val_mem SEGS (rdW W mem) v 4 ty ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 40) 8 n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  (forall E' ss' ms' mdc k,
     st_ok SEGS E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
     ajournal_x (SK := SK) SEGS B PST ARx (STK + dw) (spZ regs + dw) FP ly S Hp W mem md []
       ly S Hp W (ms_mem ms') mdc k ->
     ms' = mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_put)) (ms_mem ms') (seg_rom SEGS) ->
     spZ (ms_regs ms') = spZ regs -> aregs_preserved regs (ms_regs ms') ->
     getr (ms_regs ms') 1 = getr regs 1 -> getr (ms_regs ms') 3 = getr regs 3 -> getr (ms_regs ms') 4 = getr regs 4 ->
     getr (ms_regs ms') 10 = getr regs 10 ->
     getr (ms_regs ms') 11 = Z_to_bv 64 (VAL (A_OBJ 2) + lo) -> getr (ms_regs ms') 12 = Z_to_bv 64 ln ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
     TVMN mem (ms_mem ms') ->
     SRr SEGS W (mkCfg ms' mdc) Q) ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) Q.
Proof.
intros ty ao ent lo ln STK dw ly S Hp W regs mem md ch v str kids keys n FP Q Hcase HPRE HSTK HWIN H11 Hv0 Hv8 Hvc
  Hvapp Hvimg Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO HK.
pose proof HWIN as (Hdw0 & Hdw16 & Hdwtop & _).
remember (EV_B regs str kids keys n) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EV_B; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys;
  Z_to_bv 64 n]) E)
  by (split; [intros k Hk; subst E; unfold EV_B; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (proj1 HAE 3%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (proj1 HAE 4%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite (proj1 HAE 10%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
subst E.
assert (Hty : 0 <= ty < 2 ^ 32)
  by (destruct Hcase as [Hc|[Hc|Hc]]; injection Hc; intros; subst; clear; lia).
destruct (tv_entry_B STK ly S Hp W regs mem md ch TV_PC_B v ty str kids keys n [] HPRE HSTK H11 Hv0 Hv8 Hvc Hvapp Hvimg
  Hty Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO I) as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx
  STK dw FP ly S Hp W regs mem md ch HPRE HWIN) as HJ.
destruct Hcase as [Hc|[Hc|Hc]]; injection Hc as Hty0 Hao Hent Hlo Hln; subst ty ao ent lo ln.
all: remember (EV_B regs str kids keys n) as E eqn:HE; clear HE; unfold TV_FRAME_B in HSTK.
all: unfold cfg_at; rewrite <- TV_PC_sigma_B; change (w64 (BASE + TV_PC_B)) with (Z_to_bv 64 (BASE + TV_PC_B)).
all: pose proof (TVMN_refl mem) as HMN.
all: paj_run_tok_x_inv (RUNI mem) HS HJ SHOK HMN TV_SPAN; [tv_awr regs dw Usp|].
all: clear HF HG; tv_keep HFr K1 regs W Usp 192; clear HFr.
all: prreg HS (11%bv : bv 5) R11.
all: lazymatch goal with
  HS0 : st_ok_pi _ _ ?Ej ?ssj (restrict _ ?msj), R : getr _ 11 = Z_to_bv 64 (bv_unsigned (ew _ 243) + ?ent)
  |- SRr _ _ (mkCfg ?msj ?mdj) _ =>
  let pcj := eval vm_compute in (ss_pc ssj) in
  let wj := eval vm_compute in (match plookup (@pl_tpi _ PL) pcj with Some (PW x) => x | _ => 0 end) in
  let ao := eval vm_compute in (VAL (A_OBJ 2) + ent - BASE) in
  eapply (SRr_jr_pi (PL := PL) (PI := PA) W Ej ssj msj mdj _ wj (11%bv : bv 5) (BASE + ao) HS0 eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv
  | rewrite R, (HEI 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); change 243%nat with (A_OBJ 2);
    f_equal; vm_compute; reflexivity
  | split; [vm_compute; discriminate | vm_compute; reflexivity]
  | vm_compute; reflexivity | ];
  let mat1 := fresh "mat1" in let ms1 := fresh "ms1" in let Hms1 := fresh "Hms1" in let HS1 := fresh "HS1" in
  intros mat1 ms1 Hms1 HS1; subst ms1;
  lazymatch type of HS1 with st_ok _ _ (mkSST _ ?r ?f ?m ?rv ?g) _ =>
    assert (HS2 : st_ok_pi SEGS VAL Ej (mkSST ao r f m rv g)
      (restrict (w_H W) (mkst (ms_regs msj) (Z_to_bv 64 (BASE + ao)) (ms_mem msj) (seg_rom SEGS))))
    by (unfold st_ok_pi, abs_ss, setpc; cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts]; exact HS1) end;
  clear HS1 R HS0;
  lazymatch goal with HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ0) as HJm;
    clear HJ0 end
end.
all: paj_run_tok_x_inv (RUNI mem) HS2 HJm SHOK HMN TV_SPAN; [tv_awr regs dw Usp|].
all: clear HF HG; tv_keep HFr K2 regs W Usp 192; clear HFr.
all: prreg HS2 (1%bv : bv 5) Q1; prreg HS2 (2%bv : bv 5) Q2; prreg HS2 (3%bv : bv 5) Q3; prreg HS2 (4%bv : bv 5) Q4.
all: prreg HS2 (10%bv : bv 5) Q10; prreg HS2 (11%bv : bv 5) Q11; prreg HS2 (12%bv : bv 5) Q12.
all: lazymatch goal with HS0 : st_ok _ ?Ex ?ssx (restrict _ ?msx), HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  apply (HK Ex ssx msx mdx _ HS0 ltac:(vm_compute; reflexivity) HJ0);
  [ rewrite (st_ok_restrict_mkst SEGS (w_H W) _ _ _ HS2 eq_refl) at 1; reflexivity
  | unfold spZ; rewrite Q2, E2; reflexivity
  | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids;
      Z_to_bv 64 keys; Z_to_bv 64 n] HS2);
      [env_agree_chain HAE | vm_compute; reflexivity]
  | rewrite Q1, E1; reflexivity
  | rewrite Q3, E3; reflexivity
  | rewrite Q4, E4; reflexivity
  | rewrite Q10, E10; reflexivity
  | rewrite Q11, (HEI 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); reflexivity
  | rewrite Q12; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hfr := fresh "Hfr" in
    intros a Ha Hfr; rewrite (K2 a Ha Hfr); exact (K1 a Ha Hfr)
  | exact HMN ]
end.
Qed.

(* ---- ARM tag 4 (JStr): table entry 4 -> 0x85724 (arm 16472, ent 481060, DERIVED): the inline shadow check of
   v->str (covered by the node's shadow entry), a1 := v->str, a0 := s0, the epilogue, `j tx_string` (0x8577c), with
   the s10_tail_orW-shaped continuation ---- *)
Lemma tv_run_str_B : forall STK dw ly S Hp W regs mem md ch v str kids keys n (FP : list (Z * Z)) Q,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> TV_FRAME_B <= STK -> fwin (PA := PA) ly W regs mem dw ->
  getr regs 11 = w64 v ->
  4096 <= v -> v mod 8 = 0 -> v + 56 <= YM05.alloc_ceiling -> in_app v 56 ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  val_mem SEGS (rdW W mem) v 4 4 ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 40) 8 n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  (forall E' ss' ms' mdc k,
     st_ok SEGS E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
     ajournal_x (SK := SK) SEGS B PST ARx (STK + dw) (spZ regs + dw) FP ly S Hp W mem md []
       ly S Hp W (ms_mem ms') mdc k ->
     ms' = mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_string)) (ms_mem ms') (seg_rom SEGS) ->
     spZ (ms_regs ms') = spZ regs -> aregs_preserved regs (ms_regs ms') ->
     getr (ms_regs ms') 1 = getr regs 1 -> getr (ms_regs ms') 3 = getr regs 3 -> getr (ms_regs ms') 4 = getr regs 4 ->
     getr (ms_regs ms') 10 = getr regs 10 -> getr (ms_regs ms') 11 = Z_to_bv 64 str ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
     TVMN mem (ms_mem ms') ->
     SRr SEGS W (mkCfg ms' mdc) Q) ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) Q.
Proof.
intros STK dw ly S Hp W regs mem md ch v str kids keys n FP Q HPRE HSTK HWIN H11 Hv0 Hv8 Hvc
  Hvapp Hvimg Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO HK.
pose proof HWIN as (Hdw0 & Hdw16 & Hdwtop & _).
remember (EV_B regs str kids keys n) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EV_B; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys;
  Z_to_bv 64 n]) E)
  by (split; [intros k Hk; subst E; unfold EV_B; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E33 : ew E 33 = Z_to_bv 64 str)
  by (subst E; unfold EV_B; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (proj1 HAE 3%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (proj1 HAE 4%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite (proj1 HAE 10%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
subst E.
destruct (tv_entry_B STK ly S Hp W regs mem md ch TV_PC_B v 4 str kids keys n [] HPRE HSTK H11 Hv0 Hv8 Hvc Hvapp Hvimg
  ltac:(clear; lia) Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO I) as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx
  STK dw FP ly S Hp W regs mem md ch HPRE HWIN) as HJ.
remember (EV_B regs str kids keys n) as E eqn:HE; clear HE; unfold TV_FRAME_B in HSTK.
unfold cfg_at; rewrite <- TV_PC_sigma_B; change (w64 (BASE + TV_PC_B)) with (Z_to_bv 64 (BASE + TV_PC_B)).
pose proof (TVMN_refl mem) as HMN.
paj_run_tok_x_inv (RUNI mem) HS HJ SHOK HMN TV_SPAN; [tv_awr regs dw Usp|].
clear HF HG; tv_keep HFr K1 regs W Usp 192; clear HFr.
prreg HS (11%bv : bv 5) R11.
lazymatch goal with
  HS0 : st_ok_pi _ _ ?Ej ?ssj (restrict _ ?msj), R : getr _ 11 = Z_to_bv 64 (bv_unsigned (ew _ 243) + ?ent)
  |- SRr _ _ (mkCfg ?msj ?mdj) _ =>
  let pcj := eval vm_compute in (ss_pc ssj) in
  let wj := eval vm_compute in (match plookup (@pl_tpi _ PL) pcj with Some (PW x) => x | _ => 0 end) in
  let ao := eval vm_compute in (VAL (A_OBJ 2) + ent - BASE) in
  eapply (SRr_jr_pi (PL := PL) (PI := PA) W Ej ssj msj mdj _ wj (11%bv : bv 5) (BASE + ao) HS0 eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv
  | rewrite R, (HEI 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); change 243%nat with (A_OBJ 2);
    f_equal; vm_compute; reflexivity
  | split; [vm_compute; discriminate | vm_compute; reflexivity]
  | vm_compute; reflexivity | ];
  let mat1 := fresh "mat1" in let ms1 := fresh "ms1" in let Hms1 := fresh "Hms1" in let HS1 := fresh "HS1" in
  intros mat1 ms1 Hms1 HS1; subst ms1;
  lazymatch type of HS1 with st_ok _ _ (mkSST _ ?r ?f ?m ?rv ?g) _ =>
    assert (HS2 : st_ok_pi SEGS VAL Ej (mkSST ao r f m rv g)
      (restrict (w_H W) (mkst (ms_regs msj) (Z_to_bv 64 (BASE + ao)) (ms_mem msj) (seg_rom SEGS))))
    by (unfold st_ok_pi, abs_ss, setpc; cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts]; exact HS1) end;
  clear HS1 R HS0;
  lazymatch goal with HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ0) as HJm;
    clear HJ0 end
end.
paj_run_tok_x_inv (RUNI mem) HS2 HJm SHOK HMN TV_SPAN; [tv_awr regs dw Usp|].
clear HF HG; tv_keep HFr K2 regs W Usp 192; clear HFr.
prreg HS2 (1%bv : bv 5) Q1; prreg HS2 (2%bv : bv 5) Q2; prreg HS2 (3%bv : bv 5) Q3; prreg HS2 (4%bv : bv 5) Q4.
prreg HS2 (10%bv : bv 5) Q10; prreg HS2 (11%bv : bv 5) Q11.
lazymatch goal with HS0 : st_ok _ ?Ex ?ssx (restrict _ ?msx), HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  apply (HK Ex ssx msx mdx _ HS0 ltac:(vm_compute; reflexivity) HJ0);
  [ rewrite (st_ok_restrict_mkst SEGS (w_H W) _ _ _ HS2 eq_refl) at 1; reflexivity
  | unfold spZ; rewrite Q2, E2; reflexivity
  | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids;
      Z_to_bv 64 keys; Z_to_bv 64 n] HS2);
      [env_agree_chain HAE | vm_compute; reflexivity]
  | rewrite Q1, E1; reflexivity
  | rewrite Q3, E3; reflexivity
  | rewrite Q4, E4; reflexivity
  | rewrite Q10, E10; reflexivity
  | rewrite Q11, ?E33; rewrite ?Z.add_0_r; rewrite ?unsigned_lit_small by lia; rewrite ?Z_to_bv_bv_unsigned;
    reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hfr := fresh "Hfr" in
    intros a Ha Hfr; rewrite (K2 a Ha Hfr); exact (K1 a Ha Hfr)
  | exact HMN ]
end.
Qed.

(* ---- ARM tag 3 (JNum): table entry 3 -> 0x857c8 (arm 16636, ent 481224, DERIVED): the inline shadow check of
   v->str, s1 := v->str, the strlen wrapper on it (`jal wrapper_strlen` 0x857e8, YGcallMx.aj_strlen_at_x), a2 := its
   length, a0 := s0, a1 := s1, `j 0x8582c`, the epilogue, `j tx_put` (s10_tail_orW's shape). The strlen call writes
   its 2 * ESTACK window below tx_value's frame, so the continuation keeps every byte outside
   [sp - 192 - 2 * ESTACK, sp) ---- *)
Lemma tv_run_num_B : forall STK dw ly S Hp W regs mem md ch v str kids keys n (FP : list (Z * Z))
  (txt : list Z) k Lam peak cnt fail ran most own Q,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> TV_FRAME_B + 2 * ESTACK <= STK ->
  fwin (PA := PA) ly W regs mem dw ->
  getr regs 11 = w64 v ->
  4096 <= v -> v mod 8 = 0 -> v + 56 <= YM05.alloc_ceiling -> in_app v 56 ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  val_mem SEGS (rdW W mem) v 4 3 ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 40) 8 n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  Forall (fun c => 0 < c < 256) txt -> garr8 SEGS (rdW W mem) str (txt ++ [0]) ->
  In (str, k) Lam -> Z.of_nat (length txt) + 1 <= k -> prhtx_bvis (PA := PA) W mem str k ->
  prh_ledger (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> Z.of_nat (length txt) + 1 < 2 ^ 32 ->
  (forall E' ss' ms' mdc kj,
     st_ok SEGS E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
     ajournal_x (SK := SK) SEGS B PST ARx (STK + dw) (spZ regs + dw) FP ly S Hp W mem md []
       ly S Hp W (ms_mem ms') mdc kj ->
     ms' = mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_put)) (ms_mem ms') (seg_rom SEGS) ->
     spZ (ms_regs ms') = spZ regs -> aregs_preserved regs (ms_regs ms') ->
     getr (ms_regs ms') 1 = getr regs 1 -> getr (ms_regs ms') 3 = getr regs 3 -> getr (ms_regs ms') 4 = getr regs 4 ->
     getr (ms_regs ms') 10 = getr regs 10 -> getr (ms_regs ms') 11 = Z_to_bv 64 str ->
     getr (ms_regs ms') 12 = Z_to_bv 64 (Z.of_nat (length txt)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 - 2 * ESTACK <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
     TVMN mem (ms_mem ms') ->
     SRr SEGS W (mkCfg ms' mdc) Q) ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) Q.
Proof.
intros STK dw ly S Hp W regs mem md ch v str kids keys n FP txt k Lam peak cnt fail ran most own Q HPRE HSTK HWIN H11 Hv0 Hv8
  Hvc Hvapp Hvimg Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO Hnz Hg Hin Hk Hbv HL Hl32 HK.
pose proof HWIN as (Hdw0 & Hdw16 & Hdwtop & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSTK1 : TV_FRAME_B <= STK) by (clear - HSTK Hes; unfold TV_FRAME_B in *; lia).
remember (EV_B regs str kids keys n) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EV_B; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys;
  Z_to_bv 64 n]) E)
  by (split; [intros kk Hkk; subst E; unfold EV_B; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E33 : ew E 33 = Z_to_bv 64 str)
  by (subst E; unfold EV_B; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (proj1 HAE 3%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (proj1 HAE 4%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite (proj1 HAE 10%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
subst E.
destruct (tv_entry_B STK ly S Hp W regs mem md ch TV_PC_B v 3 str kids keys n [] HPRE HSTK1
  H11 Hv0 Hv8 Hvc Hvapp Hvimg ltac:(clear; lia) Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO I) as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx
  STK dw FP ly S Hp W regs mem md ch HPRE HWIN) as HJ.
remember (EV_B regs str kids keys n) as E eqn:HE; clear HE; unfold TV_FRAME_B in HSTK.
unfold cfg_at; rewrite <- TV_PC_sigma_B; change (w64 (BASE + TV_PC_B)) with (Z_to_bv 64 (BASE + TV_PC_B)).
(* run 1: to `jr a1` *)
pose proof (TVMN_refl mem) as HMN.
paj_run_tok_x_inv (RUNI mem) HS HJ SHOK HMN TV_SPAN; [tv_awr regs dw Usp|].
clear HF HG; tv_keep HFr K1 regs W Usp 192; clear HFr.
prreg HS (11%bv : bv 5) R11.
lazymatch goal with
  HS0 : st_ok_pi _ _ ?Ej ?ssj (restrict _ ?msj), R : getr _ 11 = Z_to_bv 64 (bv_unsigned (ew _ 243) + ?ent)
  |- SRr _ _ (mkCfg ?msj ?mdj) _ =>
  let pcj := eval vm_compute in (ss_pc ssj) in
  let wj := eval vm_compute in (match plookup (@pl_tpi _ PL) pcj with Some (PW x) => x | _ => 0 end) in
  let ao := eval vm_compute in (VAL (A_OBJ 2) + ent - BASE) in
  eapply (SRr_jr_pi (PL := PL) (PI := PA) W Ej ssj msj mdj _ wj (11%bv : bv 5) (BASE + ao) HS0 eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv
  | rewrite R, (HEI 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); change 243%nat with (A_OBJ 2);
    f_equal; vm_compute; reflexivity
  | split; [vm_compute; discriminate | vm_compute; reflexivity]
  | vm_compute; reflexivity | ];
  let mat1 := fresh "mat1" in let ms1 := fresh "ms1" in let Hms1 := fresh "Hms1" in let HS1 := fresh "HS1" in
  intros mat1 ms1 Hms1 HS1; subst ms1;
  lazymatch type of HS1 with st_ok _ _ (mkSST _ ?r ?f ?m ?rv ?g) _ =>
    assert (HS2 : st_ok_pi SEGS VAL Ej (mkSST ao r f m rv g)
      (restrict (w_H W) (mkst (ms_regs msj) (Z_to_bv 64 (BASE + ao)) (ms_mem msj) (seg_rom SEGS))))
    by (unfold st_ok_pi, abs_ss, setpc; cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts]; exact HS1) end;
  clear HS1 R HS0;
  lazymatch goal with HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ0) as HJm;
    clear HJ0 end
end.
(* run 2: the arm to the strlen call *)
paj_run_tok_x_inv (RUNI mem) HS2 HJm SHOK HMN TV_SPAN; [tv_awr regs dw Usp|].
clear HF HG; tv_keep HFr K2 regs W Usp 192; clear HFr.
(* the strlen call (YGcallMxmn.aj_strlen_at_xrom, the read-only strlen row with the memnorm keep; its last premise is
   the read-only view arodata_okP) at sp - 192, its window 2 * ESTACK below *)
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hbv as (Hs4096 & Hs8 & Hk0 & Hsceil & Hsamr & HsRA & HsHULL & HsVIS).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
pmkst HS2.
prreg HS2 (10%bv : bv 5) Ra0. prreg HS2 (2%bv : bv 5) Rsp1. prreg HS2 (1%bv : bv 5) Rra1.
prreg HS2 (3%bv : bv 5) Rgp1. prreg HS2 (4%bv : bv 5) Rtp1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HspT : spZ rT = spZ regs - 192)
    by (unfold spZ at 1; rewrite Rsp1, Usp; rewrite unsigned_lit_small by lia; lia);
  assert (KA : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mT a = aview SEGS (w_H W) mem a)
    by (intros a Ha; rewrite (K2 a ltac:(lia) ltac:(lia)); exact (K1 a ltac:(lia) ltac:(lia)))
end.
set (len := Z.of_nat (length txt)) in *.
eapply SRr_bind.
{ lazymatch goal with
  | HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
    eapply (YGcallMxmn.aj_strlen_at_xrom (SK := SK) SEGS B PST ARx RLO RHI LAWS (@pa_segs_low _ _ PA)
      (SIGMA AS___wrap_strlen) ASx W rT mT (STK + dw) (spZ regs + dw) FP ly S Hp W mem md [] ly S Hp dT _ str len
      (-192 - dw) _ HJ0)
  end.
  - rewrite Ra0, ?E33; rewrite ?Z.add_0_r; rewrite ?unsigned_lit_small by lia; rewrite ?Z_to_bv_bv_unsigned;
    reflexivity.
  - lia.
  - lia.
  - exact Hl32.
  - lia.
  - rewrite HspT. lia.
  - rewrite Zminus_mod, Hdw16. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite Rgp1, E3. exact Hgp.
  - rewrite Rtp1, E4. exact Htp.
  - exact Rra1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - apply (tv_first_byte W _ str txt Hnz).
    apply (tv_garr8_move W mem _ str (txt ++ [0]) Hg). intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    apply KA. lia.
  - replace (len + 1) with (Z.of_nat (length (txt ++ [0]))) by (rewrite length_app; cbn [length]; subst len; lia).
    apply tv_src_ok.
    + apply (tv_garr8_move W mem _ str (txt ++ [0]) Hg). intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
      apply KA. lia.
    + intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite HspT, Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - exact (tv_amr8 ly S Hp W mem md Lam peak cnt fail ran most own str k (len + 1) HAR HL Hin ltac:(lia)).
  - apply (range_addressable_sub (aview SEGS (w_H W) _) SHADOW_OFF str k); [|lia|lia].
    eapply range_addressable_agree; [|exact HsRA]. intros x Hx.
    pose proof (s10_shadow_low x ltac:(lia)). apply KA. lia.
  - apply (tv_hull_sub _ str (len + 1) k); [lia | lia |].
    intros s0 Hs0. pose proof (s10_hull_low str k s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs0).
    rewrite KA by lia. exact (HsHULL ltac:(lia) s0 Hs0).
  - intros a Ha. rewrite KA by lia. apply HsVIS.
    pose proof (Z.div_mod (str + len) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (str + len) 8 ltac:(lia)).
    pose proof (Z.div_mod (k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (k + 7) 8 ltac:(lia)).
    apply Z.mod_divide in Hs8 as [q Hq]; [|lia]. lia.
  - exact (tv_rod_kept W mem _ HRO KA). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hlen2 & Hfr2 & Hpres2 & Hmn2).
pose proof (TVMN_trans _ _ _ HMN Hmn2) as HMN2. clear HMN Hmn2. rename HMN2 into HMN.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2J & _).
jafter_call_keep_pi HS2 37%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|apply Forall_nil]. split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; [lia|]. rewrite Hes. lia.
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    apply (apresent_writable SEGS). apply Hpres2J. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 37 (map (getr regs2) CLOB)) as E1' eqn:HE1 in HSX.
assert (HIM1 : img_env VAL A_LIM E1') by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall j, (j < 37)%nat -> ew E1' j = ew E j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (E1a0 : ew E1' 41 = w64 len) by (rewrite HE1, <- Hlen2; reflexivity).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys;
  Z_to_bv 64 n]) E1') by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE1.
assert (Usp1 : bv_unsigned (ew E1' 2) = spZ regs) by (rewrite OLD1 by (cbv; lia); exact Usp).
assert (SHOK1 : sh_ok SEGS TV_BX [] E1' (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil).
clear HS2 SHOK.
(* run 3: a2 := len, a0 := s0, a1 := s1, the epilogue, `j tx_put` *)
paj_run_tok_x_inv (RUNI mem) HSX HJ2 SHOK1 HMN TV_SPAN; [tv_awr regs dw Usp1|].
clear HF HG; tv_keep HFr K3 regs W Usp1 192; clear HFr.
prreg HSX (1%bv : bv 5) Q1; prreg HSX (2%bv : bv 5) Q2; prreg HSX (3%bv : bv 5) Q3; prreg HSX (4%bv : bv 5) Q4.
prreg HSX (10%bv : bv 5) Q10; prreg HSX (11%bv : bv 5) Q11; prreg HSX (12%bv : bv 5) Q12.
lazymatch goal with HS0 : st_ok _ ?Ex ?ssx (restrict _ ?msx), HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  apply (HK Ex ssx msx mdx _ HS0 ltac:(vm_compute; reflexivity) HJ0)
end.
- rewrite (st_ok_restrict_mkst SEGS (w_H W) _ _ _ HSX eq_refl) at 1. reflexivity.
- unfold spZ. rewrite Q2, OLD1 by (cbv; lia). rewrite E2. reflexivity.
- eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids;
    Z_to_bv 64 keys; Z_to_bv 64 n] HSX); [env_agree_chain HAE1 | vm_compute; reflexivity].
- rewrite Q1, OLD1 by (cbv; lia). rewrite E1. reflexivity.
- rewrite Q3, OLD1 by (cbv; lia). rewrite E3. reflexivity.
- rewrite Q4, OLD1 by (cbv; lia). rewrite E4. reflexivity.
- rewrite Q10, OLD1 by (cbv; lia). rewrite E10. reflexivity.
- rewrite Q11, ?OLD1 by (cbv; lia). rewrite ?E33. rewrite ?Z.add_0_r. rewrite ?unsigned_lit_small by lia.
  rewrite ?Z_to_bv_bv_unsigned. reflexivity.
- rewrite Q12, ?E1a0. rewrite ?Z.add_0_r. unfold w64. rewrite ?unsigned_lit_small by lia.
  rewrite ?Z_to_bv_bv_unsigned. reflexivity.
- intros a Ha Hfr. rewrite (K3 a Ha ltac:(lia)).
  rewrite (Hfr2 a Ha ltac:(rewrite Hes; lia)). rewrite (K2 a Ha ltac:(rewrite Hes in Hfr; lia)).
  exact (K1 a Ha ltac:(rewrite Hes in Hfr; lia)).
- exact HMN.
Qed.

(* ---- ARMS tag 5 (JArr) and tag 6 (JObj), THE OPEN BRACKET: table entries 5 and 6 both jump to 0x854e0 (arm 15892,
   ent 480480, DERIVED): `li a1,6; beq a0,a1,0x854f4` picks .str.20 '{' (tag 6, band offset 70144) or .str.21 '['
   (tag 5, 70176), then `li a2,1; li s5,1; mv a0,s0; jal tx_put` (0x85508, return 0x8550c = offset 15936). The
   continuation receives the CALL STATE at tx_put's entry: the symbolic state and the journal, the frame's sp, the
   return address, the argument registers a0 / a1 / a2 and the live callee-saved registers s0 = t, s1 = v,
   s3 = pretty, s5 = 1, so that one tx_put call lemma can plug in ---- *)
Definition tv_open_case_B (ty lo : Z) : Prop := (ty, lo) = (5, 70176) \/ (ty, lo) = (6, 70144).
Definition TV_RET_OPEN_B : Z := 15936.   (* 0x8550c, the open bracket's return *)

Lemma tv_run_open_B : forall ty lo STK dw ly S Hp W regs mem md ch v str kids keys n (FP : list (Z * Z)) Q,
  tv_open_case_B ty lo ->
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> TV_FRAME_B <= STK -> fwin (PA := PA) ly W regs mem dw ->
  getr regs 11 = w64 v ->
  4096 <= v -> v mod 8 = 0 -> v + 56 <= YM05.alloc_ceiling -> in_app v 56 ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  val_mem SEGS (rdW W mem) v 4 ty ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 40) 8 n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  (forall E' ss' ms' mdc k,
     st_ok SEGS E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None -> ss_pc ss' = SIGMA AS_tx_put ->
     bv_unsigned (ew E' 2) = spZ regs ->
     ajournal_x (SK := SK) SEGS B PST ARx (STK + dw) (spZ regs + dw) FP ly S Hp W mem md []
       ly S Hp W (ms_mem ms') mdc k ->
     ms' = mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_put)) (ms_mem ms') (seg_rom SEGS) ->
     spZ (ms_regs ms') = spZ regs - TV_FRAME_B ->
     getr (ms_regs ms') 1 = Z_to_bv 64 (BASE + TV_RET_OPEN_B) ->
     getr (ms_regs ms') 3 = getr regs 3 -> getr (ms_regs ms') 4 = getr regs 4 ->
     getr (ms_regs ms') 8 = getr regs 10 -> getr (ms_regs ms') 9 = Z_to_bv 64 v ->
     getr (ms_regs ms') 10 = getr regs 10 ->
     getr (ms_regs ms') 11 = Z_to_bv 64 (VAL (A_OBJ 2) + lo) -> getr (ms_regs ms') 12 = Z_to_bv 64 1 ->
     getr (ms_regs ms') 18 = Z_to_bv 64 (shadow_addr v) ->
     getr (ms_regs ms') 19 = getr regs 12 -> getr (ms_regs ms') 21 = Z_to_bv 64 1 ->
     tv_slots_B W (ms_mem ms') (spZ regs - TV_FRAME_B) (bv_unsigned (getr regs 13)) ->
     tv_saves_B W (ms_mem ms') (spZ regs - TV_FRAME_B) regs ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TV_FRAME_B <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
     TVMN mem (ms_mem ms') ->
     SRr SEGS W (mkCfg ms' mdc) Q) ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) Q.
Proof.
intros ty lo STK dw ly S Hp W regs mem md ch v str kids keys n FP Q Hcase HPRE HSTK HWIN H11 Hv0 Hv8 Hvc
  Hvapp Hvimg Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO HK.
pose proof HWIN as (Hdw0 & Hdw16 & Hdwtop & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
unfold TV_FRAME_B in HSTK.
assert (Hsp192 : 192 <= spZ regs <= 2 ^ 47) by lia.
remember (EV_B regs str kids keys n) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EV_B; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys;
  Z_to_bv 64 n]) E)
  by (split; [intros k Hk; subst E; unfold EV_B; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (proj1 HAE 3%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (proj1 HAE 4%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite (proj1 HAE 10%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (rewrite (proj1 HAE 11%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = getr regs 12) by (rewrite (proj1 HAE 12%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; unfold EV_B; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EG : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> (k < 32)%nat -> ew E k = getr regs r)
  by (intros k r Hk Hlt; rewrite (proj1 HAE k ltac:(lia)); exact (ew_Ereg_nat regs _ k r Hk)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
subst E.
assert (Hty : 0 <= ty < 2 ^ 32) by (destruct Hcase as [Hc|Hc]; injection Hc; intros; subst; clear; lia).
destruct (tv_entry_B STK ly S Hp W regs mem md ch TV_PC_B v ty str kids keys n [] HPRE HSTK H11 Hv0 Hv8 Hvc Hvapp Hvimg
  Hty Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn HRA HRO I) as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx
  STK dw FP ly S Hp W regs mem md ch HPRE HWIN) as HJ.
destruct Hcase as [Hc|Hc]; injection Hc as Hty0 Hlo; subst ty lo.
all: remember (EV_B regs str kids keys n) as E eqn:HE; clear HE.
all: unfold cfg_at; rewrite <- TV_PC_sigma_B; change (w64 (BASE + TV_PC_B)) with (Z_to_bv 64 (BASE + TV_PC_B)).
all: pose proof (TVMN_refl mem) as HMN.
all: paj_run_tok_x_inv (RUNI mem) HS HJ SHOK HMN TV_SPAN; [tv_awr regs dw Usp|].
all: clear HF HG; tv_keep HFr K1 regs W Usp 192; clear HFr.
all: prreg HS (11%bv : bv 5) R11.
all: lazymatch goal with
  HS0 : st_ok_pi _ _ ?Ej ?ssj (restrict _ ?msj), R : getr _ 11 = Z_to_bv 64 (bv_unsigned (ew _ 243) + ?ent)
  |- SRr _ _ (mkCfg ?msj ?mdj) _ =>
  let pcj := eval vm_compute in (ss_pc ssj) in
  let wj := eval vm_compute in (match plookup (@pl_tpi _ PL) pcj with Some (PW x) => x | _ => 0 end) in
  let ao := eval vm_compute in (VAL (A_OBJ 2) + ent - BASE) in
  eapply (SRr_jr_pi (PL := PL) (PI := PA) W Ej ssj msj mdj _ wj (11%bv : bv 5) (BASE + ao) HS0 eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv
  | rewrite R, (HEI 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); change 243%nat with (A_OBJ 2);
    f_equal; vm_compute; reflexivity
  | split; [vm_compute; discriminate | vm_compute; reflexivity]
  | vm_compute; reflexivity | ];
  let mat1 := fresh "mat1" in let ms1 := fresh "ms1" in let Hms1 := fresh "Hms1" in let HS1 := fresh "HS1" in
  intros mat1 ms1 Hms1 HS1; subst ms1;
  lazymatch type of HS1 with st_ok _ _ (mkSST _ ?r ?f ?m ?rv ?g) _ =>
    assert (HS2 : st_ok_pi SEGS VAL Ej (mkSST ao r f m rv g)
      (restrict (w_H W) (mkst (ms_regs msj) (Z_to_bv 64 (BASE + ao)) (ms_mem msj) (seg_rom SEGS))))
    by (unfold st_ok_pi, abs_ss, setpc; cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts]; exact HS1) end;
  clear HS1 R HS0;
  lazymatch goal with HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ0) as HJm;
    clear HJ0 end
end.
all: paj_run_tok_x_inv (RUNI mem) HS2 HJm SHOK HMN TV_SPAN; [tv_awr regs dw Usp|].
all: clear HF HG; tv_keep HFr K2 regs W Usp 192; clear HFr.
all: prreg HS2 (1%bv : bv 5) Q1; prreg HS2 (2%bv : bv 5) Q2; prreg HS2 (3%bv : bv 5) Q3; prreg HS2 (4%bv : bv 5) Q4.
all: prreg HS2 (8%bv : bv 5) Q8; prreg HS2 (9%bv : bv 5) Q9; prreg HS2 (10%bv : bv 5) Q10.
all: prreg HS2 (11%bv : bv 5) Q11; prreg HS2 (12%bv : bv 5) Q12.
all: prreg HS2 (18%bv : bv 5) Q18; prreg HS2 (19%bv : bv 5) Q19; prreg HS2 (21%bv : bv 5) Q21.
all: pose proof (tv_region_nth SEGS _ _ _ 0%nat _ HS2 eq_refl) as HR0; cbn [ms_mem restrict] in HR0.
all: lazymatch goal with HS0 : st_ok _ ?Ex ?ssx (restrict _ ?msx), HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  apply (HK Ex ssx msx mdx _ HS0 ltac:(vm_compute; reflexivity) ltac:(reflexivity) Usp HJ0);
  [ rewrite (st_ok_restrict_mkst SEGS (w_H W) _ _ _ HS2 eq_refl) at 1; reflexivity
  | unfold spZ at 1; rewrite Q2, Usp; rewrite unsigned_lit_small by lia; unfold TV_FRAME_B; lia
  | rewrite Q1; unfold TV_RET_OPEN_B; first [reflexivity | f_equal; vm_compute; reflexivity]
  | rewrite Q3, E3; reflexivity
  | rewrite Q4, E4; reflexivity
  | rewrite Q8, E10; reflexivity
  | rewrite Q9, E11; reflexivity
  | rewrite Q10, E10; reflexivity
  | rewrite Q11, (HEI 243%nat ltac:(unfold A_TEXT, A_LIM; lia)); reflexivity
  | rewrite Q12; reflexivity
  | rewrite Q18; apply (tv_shadow_word _ _ v);
    [ rewrite E11; apply unsigned_lit_small; lia
    | rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia | lia ]
  | rewrite Q19, E12; reflexivity
  | rewrite Q21; reflexivity
  | unfold tv_slots_B; split; [| split];
    [ let V := fresh "V" in
      pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ (-176) 8%N (SLit 0) HR0 Usp
        ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
      cbn [N.to_nat] in V; rewrite tv_U_lit0 in V;
      lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (spZ regs + -176) by (unfold TV_FRAME_B; lia) end;
      exact V
    | tv_savef HR0 Usp EG (spZ regs) (-168) 13%nat (13%bv : bv 5)
    | let V := fresh "V" in
      pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ (-120) 8%N (SOff 32 0) HR0 Usp
        ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
      cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite ts_U_atom_mod, E32 in V;
      rewrite unsigned_lit_small in V by (unfold SHADOW_OFF; lia);
      lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (spZ regs + -120) by (unfold TV_FRAME_B; lia) end;
      exact V ]
  | unfold tv_saves_B; repeat split;
    [ tv_savef HR0 Usp EG (spZ regs) (-8) 1%nat (1%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-16) 8%nat (8%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-24) 9%nat (9%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-32) 18%nat (18%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-40) 19%nat (19%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-48) 20%nat (20%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-56) 21%nat (21%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-64) 22%nat (22%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-72) 23%nat (23%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-80) 24%nat (24%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-88) 25%nat (25%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-96) 26%nat (26%bv : bv 5)
    | tv_savef HR0 Usp EG (spZ regs) (-104) 27%nat (27%bv : bv 5) ]
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hfr := fresh "Hfr" in
    intros a Ha Hfr; rewrite (K2 a Ha Hfr); exact (K1 a Ha Hfr)
  | exact HMN ]
end.
Qed.


(* ---- THE MID STATE: the symbolic state of a segment that starts after a call of the open arm has returned. Its
   atoms are the CURRENT registers (atom i = register i, sr_atoms), its extras 32 the shadow base, 33 str, 34 kids,
   35 keys, 36 n, 37 the depth; the node's base is s1 (atom 9) and the frame's is sp (atom 2). The frame's write
   window is [sp + 8, sp + 88): after its prologue tx_value writes only 8(sp) .. 80(sp), so the thirteen saves at
   88(sp) .. 184(sp) are read-only in every segment and survive it ---- *)
Definition EM_B (regs : bvmap 5 word) (str kids keys nn d : Z) : env :=
  Eimg (L := B_prog_listing) (PI := PA)
    (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 nn;
                Z_to_bv 64 d]).
Definition tv_frame_chunks : list YP09.chunk :=
  [YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SOff 37 0)); YP09.mkChunk 72 (CVal 8 (SOff 32 0))].
Definition tv_mid_regions_B (ty : Z) : smem :=
  [ YP09.mkRegion (Some 2%nat) 0 192 8 88 tv_frame_chunks;
    YP09.mkRegion (Some 9%nat) 0 56 0 0 (tv_node_chunks ty) ].
Definition tv_SHm : list shent := [mkSHE 9 0 56].
Definition tv_facts_m (nlo nhi : Z) (cs : list acond) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 4096 (2 ^ 47 - 56) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (36%nat, mkAF nlo nhi 0)] cs [].
Definition ss_tvm_B (eo ty nlo nhi : Z) (cs : list acond) : sstate :=
  mkSS eo sr_atoms (tv_mid_regions_B ty) None (tv_facts_m nlo nhi cs).

(* ---- THE OPEN ARM's segment states at image B (tags 5 / 6), over S10Env.v's TE env, as S10TxValue.v's ss_P / ss_M:
   atoms 0-31 the entry registers, 32-63 the current ones (xr r), 64 the shadow base, 65 kids, 66 keys, 67 n,
   68 keys + 8 i (the i-th key slot), 69 the i-th key pointer. B's frame is 192 and its live registers are
   s0 = t, s1 = v, s2 = shadow v, s3 = pretty, s4 = v + 40, s5 = 56 i, s6 = d + 1, s7 = v + 24, s8 = 8 i,
   s9 = 0 (the depth-overflow flag `slt s9,s6,a3`), s10 = i, s11 = shadow (v + 24). The listing offsets (DERIVED:
   address - B_prog_base): 0x8550c 15936 (after the opening bracket), 0x8559c 16080 (the loop head), 0x855b0 16100
   (after the comma), 0x855c4 16120 (after the item's tx_line), 0x85638 16236 (after the key), 0x85648 16252 (after
   the colon), 0x8565c 16272 (after the space), 0x856b8 16364 (after the item), 0x856f0 16420 (the close),
   0x85704 16440 (after the closing tx_line) ---- *)
Definition TVO_BX_B : sv := SOff 64 0.
Definition tvo_sh_B (e : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL e (SLit 3)) TVO_BX_B.
(* the prologue's saves at 88 .. 184 above the frame base sp0 - 192: s11 .. s2, s1, s0, ra (the entry atoms) *)
Definition tvo_saves_B : list YP09.chunk :=
  [YP09.mkChunk 88 (CVal 8 (SOff 27 0)); YP09.mkChunk 96 (CVal 8 (SOff 26 0)); YP09.mkChunk 104 (CVal 8 (SOff 25 0));
   YP09.mkChunk 112 (CVal 8 (SOff 24 0)); YP09.mkChunk 120 (CVal 8 (SOff 23 0)); YP09.mkChunk 128 (CVal 8 (SOff 22 0));
   YP09.mkChunk 136 (CVal 8 (SOff 21 0)); YP09.mkChunk 144 (CVal 8 (SOff 20 0)); YP09.mkChunk 152 (CVal 8 (SOff 19 0));
   YP09.mkChunk 160 (CVal 8 (SOff 18 0)); YP09.mkChunk 168 (CVal 8 (SOff 9 0)); YP09.mkChunk 176 (CVal 8 (SOff 8 0));
   YP09.mkChunk 184 (CVal 8 (SOff 1 0))].
(* what the dispatch wrote before the opening call: 16(sp) the UBSan `andi` result 0, 24(sp) the depth (entry a3),
   72(sp) the shadow base *)
Definition tvo_head_B : list YP09.chunk :=
  [YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SOff 13 0)); YP09.mkChunk 72 (CVal 8 TVO_BX_B)].
(* the loop's spills (0x8551c, 0x8554c .. 0x85598): 8(sp) (v & 7) + 3 = 3, 32(sp) .str.24 ' ', 40(sp) .str.23 ':',
   48(sp) the shadow of v + 32, 56(sp) v + 32, 64(sp) .str.22 ',', 80(sp) the shadow of v + 40 *)
Definition tvo_spills_B : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 32 (CVal 8 (SOff (A_OBJ 2) 70272));
   YP09.mkChunk 40 (CVal 8 (SOff (A_OBJ 2) 70240)); YP09.mkChunk 48 (CVal 8 (tvo_sh_B (SOff (xr 9) 32)));
   YP09.mkChunk 56 (CVal 8 (SOff (xr 9) 32)); YP09.mkChunk 64 (CVal 8 (SOff (A_OBJ 2) 70208));
   YP09.mkChunk 80 (CVal 8 (tvo_sh_B (SOff (xr 9) 40)))].
Definition tvo_node_B (ty : Z) : YP09.region :=
  YP09.mkRegion (Some (xr 9)) 0 56 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 24 (CVal 8 (SOff 65 0)); YP09.mkChunk 32 (CVal 8 (SOff 66 0));
     YP09.mkChunk 40 (CVal 8 (SOff 67 0))].
Definition tvo_atoms_B : list (nat * afact) :=
  [(xr 2, mkAF (2 ^ 46) (2 ^ 47) 4); (xr 9, mkAF 4096 (2 ^ 47 - 56) 3); (64%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
(* P: after the opening bracket; the frame's spill words still to be written *)
(* the thirteen saves are NOT chunks of P or M: the write window [8, 88) leaves them alone, and tv_saved carries
   them as a fact until the close's epilogue reloads them *)
Definition ss_P_B (ty : Z) (cs : list acond) : sstate :=
  mkSS TV_RET_OPEN_B (sr_set cur_atoms 18%bv (tvo_sh_B (SOff (xr 9) 0)))
    [YP09.mkRegion (Some (xr 2)) 0 192 8 88 tvo_head_B; tvo_node_B ty] None
    (mkFacts tvo_atoms_B cs []).
Definition tvo_SH_B (obj : bool) : list shent := mkSHE (xr 9) 0 56 :: (if obj then [mkSHE 68 0 8] else []).

(* M: a loop state (B 0x8559c .. 0x856f0). Registers: the current atoms, with s2 = shadow v, s4 = v + 40, s7 = v + 24,
   s11 = shadow (v + 24) and s9 = 0 (the depth-overflow flag, 0 while d + 1 fits). The frame is read-only: the
   spills and the dispatch's words (the saves are not chunks: no loop load reads them). The node; for an object the
   i-th key slot (atom 68, holding the key pointer, atom 69). Facts: the frame and node atoms, the shadow base, kids,
   n, i (s10) and for an object keys and the key slot; the closed bounds 2 ^ 42 / 2 ^ 47 (no Section term). The
   segment's branch conditions cs (UBSan's pointer checks, pretty, i = 0, the loop test) are seated by the caller *)
Definition tvo_mregs_B : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set cur_atoms 18%bv (tvo_sh_B (SOff (xr 9) 0))) 20%bv (SOff (xr 9) 40))
    23%bv (SOff (xr 9) 24)) 27%bv (tvo_sh_B (SOff (xr 9) 24))) 25%bv (SLit 0).
Definition tvo_keyslot_B : YP09.region := YP09.mkRegion (Some 68%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 69 0))].
Definition tvo_matoms_B (obj : bool) : list (nat * afact) :=
  tvo_atoms_B ++ [(65%nat, mkAF 4096 (2 ^ 47) 0); (67%nat, mkAF 1 (2 ^ 42) 0); (xr 26, mkAF 0 (2 ^ 42) 0)] ++
  (if obj then [(66%nat, mkAF 4096 (2 ^ 47) 0); (68%nat, mkAF 4096 (2 ^ 47 - 8) 3)] else []).
Definition tvo_alias_B (obj : bool) : list (sv * sv) :=
  if obj then [(SAlu ALU_ADD (SOff 66 0) (SOff (xr 24) 0), SOff 68 0)] else [].
Definition ss_M_B (pc ty : Z) (obj : bool) (cs : list acond) : sstate :=
  mkSS pc tvo_mregs_B
    ([YP09.mkRegion (Some (xr 2)) 0 192 0 0 (tvo_spills_B ++ tvo_head_B); tvo_node_B ty] ++
     (if obj then [tvo_keyslot_B] else []))
    None (mkFacts (tvo_matoms_B obj) cs (tvo_alias_B obj)).
(* X: after the closing tx_line (B 0x85704): s2 = shadow v, the dispatch's words and the saves (the epilogue reloads
   them), the node *)
Definition ss_X_B (pc ty : Z) : sstate :=
  mkSS pc (sr_set cur_atoms 18%bv (tvo_sh_B (SOff (xr 9) 0)))
    [YP09.mkRegion (Some (xr 2)) 0 192 0 0 (tvo_head_B ++ tvo_saves_B); tvo_node_B ty] None
    (mkFacts tvo_atoms_B [] []).


(* the shadow pointer `(x + k >> 3) + shadow base`, as the arm computes it (S10Env.v ts_alias_shadow's arithmetic,
   here against the literal value) *)
Lemma tvo_sh_val : forall E nF F k, bv_unsigned (ew E nF) = F -> bv_unsigned (ew E 64) = SHADOW_OFF ->
  0 <= F -> 0 <= k -> F + k < 2 ^ 47 ->
  sv_denot E (tvo_sh_B (SOff nF k)) = Z_to_bv 64 (shadow_addr (F + k)).
Proof.
intros E nF F k HF HB HF0 Hk0 Hk.
assert (H8 : 0 <= (F + k) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply bv_eq. rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
change (bv_unsigned (sv_denot E (tvo_sh_B (SOff nF k)))) with (U E (tvo_sh_B (SOff nF k))).
unfold tvo_sh_B, TVO_BX_B. rewrite !U_SAlu, !U_SOff, U_SLit, HF, HB.
unfold zcanon, M64, zalu_raw, shadow_addr, SHADOW_OFF.
change (Z.land (3 mod 2 ^ 64) 63) with 3.
rewrite (Z.mod_small (F + k) (2 ^ 64)) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite !(Z.mod_small ((F + k) / 8) (2 ^ 64)) by lia.
rewrite Z.add_0_r.
rewrite (Z.mod_small 2147450880 (2 ^ 64)) by lia.
rewrite (Z.mod_small ((F + k) / 8 + 2147450880) (2 ^ 64)) by lia.
lia.
Qed.

Lemma tv_mid_entry_B : forall (W2 : world SEGS) regs2 mem2 eo ty nlo nhi v str kids keys nn d cs,
  getr regs2 9 = w64 v ->
  4096 <= v -> v mod 8 = 0 -> v + 56 <= YM05.alloc_ceiling -> in_app v 56 -> v + 56 <= spZ regs2 ->
  spZ regs2 mod 16 = 0 -> 2 ^ 46 <= spZ regs2 -> spZ regs2 + 192 <= 2 ^ 47 ->
  (forall a, spZ regs2 <= a < spZ regs2 + 192 -> apresent (w_H W2) mem2 a) ->
  tv_slots_B W2 mem2 (spZ regs2) d -> 0 <= d < 2 ^ 64 ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS (rdW W2 mem2) v 4 ty ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W2 mem2) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W2 mem2) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W2 mem2) (v + 32) 8 keys ->
  0 <= nn < 2 ^ 64 -> val_mem SEGS (rdW W2 mem2) (v + 40) 8 nn ->
  0 <= nlo -> nlo <= nn <= nhi -> nhi < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56 ->
  conds_ok (EM_B regs2 str kids keys nn d) cs ->
  st_ok_pi SEGS VAL (EM_B regs2 str kids keys nn d) (ss_tvm_B eo ty nlo nhi cs)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + eo)) mem2 (seg_rom SEGS))) /\
  sh_ok SEGS TV_BX tv_SHm (EM_B regs2 str kids keys nn d) (rdW W2 mem2).
Proof.
intros W2 regs2 mem2 eo ty nlo nhi v str kids keys nn d cs
  H9 Hv0 Hv8 Hvc Hvapp Hvsp Hal16 Hsplo Hsphi Hpres
  (Vs16 & Vs24 & Vs72) Hd Hty Vty Hstr Vstr Hkids Vkids Hkeys Vkeys Hn Vn Hnlo Hnn Hnhi HRA Hcs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := EM_B regs2 str kids keys nn d) in *.
set (XL := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 nn;
            Z_to_bv 64 d]) in *.
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs2 XL) k)
  by (intros k Hk; subst E XL; unfold EM_B; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs2 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 str) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 kids) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 keys) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 nn) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 d) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs2) by (rewrite E2; reflexivity).
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
split.
- rewrite restrict_mkst_fx. unfold ss_tvm_B. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold tv_mid_regions_B.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split.
      -- intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
      -- unfold tv_frame_chunks.
         constructor; [|constructor; [|constructor; [|constructor]]].
         ++ apply (chunk_ok_val SEGS E _ (spZ regs2) 16 8 (SLit 0) 0);
            [reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vs16].
         ++ apply (chunk_ok_val SEGS E _ (spZ regs2) 24 8 (SOff 37 0) d);
            [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vs24].
         ++ apply (chunk_ok_val SEGS E _ (spZ regs2) 72 8 (SOff 32 0) SHADOW_OFF);
            [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | unfold SHADOW_OFF; cbn; lia | cbn; lia | exact Vs72].
    * rewrite (VB 9%nat v E9) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      unfold tv_node_chunks.
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      -- apply (chunk_ok_val SEGS E _ v 0 4 (SLit ty) ty); [reflexivity | change (8 * Z.of_N 4) with 32; lia | cbn; lia |].
         rewrite Z.add_0_r. exact Vty.
      -- apply (chunk_ok_val SEGS E _ v 16 8 (SOff 33 0) str);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vstr].
      -- apply (chunk_ok_val SEGS E _ v 24 8 (SOff 34 0) kids);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vkids].
      -- apply (chunk_ok_val SEGS E _ v 32 8 (SOff 35 0) keys);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vkeys].
      -- apply (chunk_ok_val SEGS E _ v 40 8 (SOff 36 0) nn);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vn].
  + apply pairwise_disjoint_of_extents. unfold tv_mid_regions_B, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat v E9) by lia. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact Hcs | exact I]].
    cbn [tv_facts_m f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E9, E32, E36, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try lia.
- unfold sh_ok, tv_SHm. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E TV_BX 9 v 56 v 0 56).
  + exact HRA.
  + unfold TV_BX. rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia). reflexivity.
  + rewrite (U_atom E 9 v E9) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ---- THE EMPTY ARRAY / OBJECT, from the open bracket's return to the CLOSE seam: 0x8550c computes s4 = v + 40,
   checks the shadow of the count field (covered by the node's entry), loads n, and `beqz a0,0x856f0` takes the
   empty exit with s5 = 1 (0x85500). The run stops at the close seam 0x856f0 (offset 16420, DERIVED) ---- *)
Definition TV_CLOSE_OFF_B : Z := 16420.   (* 0x856f0: beqz s3 (pretty), bnez s5, then the closing bracket *)
(* the runner to a stop pc over the journal at WR (YC1fPx.v paj_run_to_x_invR): every run that stops at a seam is
   after the opening call *)
Let RUNTOIR (m0 : word -> option byte) :=
  paj_run_to_x_invR (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (TVMN m0) (TVMN_laws m0) WR
    (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

Lemma tv_run_n0_B : forall STK dw sp0 ly S Hp W mem md ly2 S2 Hp2 (W2 : world SEGS) regs2 mem2 md2 k
    (FP : list (Z * Z)) ty v str kids keys d Q,
  ajournal_xR (SK := SK) SEGS B PST ARx WR (STK + dw) (sp0 + dw) FP ly S Hp W mem md []
    ly2 S2 Hp2 W2 mem2 md2 k ->
  192 <= STK -> 0 <= dw ->
  spZ regs2 = sp0 - 192 -> sp0 mod 16 = 0 -> 2 ^ 46 + 192 <= sp0 -> sp0 <= 2 ^ 47 ->
  getr regs2 9 = w64 v ->
  4096 <= v -> v mod 8 = 0 -> v + 56 <= YM05.alloc_ceiling -> in_app v 56 -> v + 56 <= sp0 - 192 ->
  (forall a, sp0 - 192 <= a < sp0 -> apresent (w_H W2) mem2 a) ->
  tv_slots_B W2 mem2 (sp0 - 192) d -> 0 <= d < 2 ^ 64 ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS (rdW W2 mem2) v 4 ty ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W2 mem2) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W2 mem2) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W2 mem2) (v + 32) 8 keys ->
  val_mem SEGS (rdW W2 mem2) (v + 40) 8 0 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56 ->
  (forall E' ss' ms' mdc' k',
     st_ok_pi SEGS VAL E' ss' (restrict (w_H W2) ms') -> ss_resv ss' = None ->
     ajournal_xR (SK := SK) SEGS B PST ARx WR (STK + dw) (sp0 + dw) FP ly S Hp W mem md []
       ly2 S2 Hp2 W2 (ms_mem ms') mdc' k' ->
     spZ (ms_regs ms') = sp0 - 192 ->
     getr (ms_regs ms') 1 = getr regs2 1 -> getr (ms_regs ms') 3 = getr regs2 3 ->
     getr (ms_regs ms') 4 = getr regs2 4 -> getr (ms_regs ms') 8 = getr regs2 8 ->
     getr (ms_regs ms') 9 = w64 v -> getr (ms_regs ms') 18 = getr regs2 18 ->
     getr (ms_regs ms') 19 = getr regs2 19 -> getr (ms_regs ms') 21 = getr regs2 21 ->
     tv_slots_B W2 (ms_mem ms') (sp0 - 192) d ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 184 <= a < sp0 - 104) ->
        aview SEGS (w_H W2) (ms_mem ms') a = aview SEGS (w_H W2) mem2 a) ->
     (forall x : word, (bv_unsigned x < sp0 - 184 \/ sp0 - 104 <= bv_unsigned x) ->
        rdW W2 (ms_mem ms') x = rdW W2 mem2 x) ->
     TVMN mem2 (ms_mem ms') ->
     SRW W2 (mkCfg (mkst (ms_regs ms') (Z_to_bv 64 (BASE + TV_CLOSE_OFF_B)) (ms_mem ms') (seg_rom SEGS)) mdc')
       Q) ->
  SRW W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + TV_RET_OPEN_B)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros STK dw sp0 ly S Hp W mem md ly2 S2 Hp2 W2 regs2 mem2 md2 k FP ty v str kids keys d Q
  HJ HSTK Hdw0 Hsp2 Hal16 Hsplo Hsphi H9 Hv0 Hv8 Hvc Hvapp Hvsp Hpres HSL Hd Hty Vty Hstr Vstr Hkids Vkids
  Hkeys Vkeys Vn HRA HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
set (cs := [mkAC BC_EQ (SOff 36 0) (SLit 0)]).
remember (EM_B regs2 str kids keys 0 d) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EM_B; apply Eimg_env).
assert (Hcs : conds_ok E cs)
  by (subst E cs; split; [|exact I]; unfold acond_ok; cbn [ac_c ac_a ac_b sv_denot];
      unfold EM_B; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs2 _ 4);
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; vm_compute; reflexivity).
assert (E2 : ew E 2 = getr regs2 2)
  by (subst E; unfold EM_B; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 192) by (rewrite E2; exact Hsp2).
assert (E32m : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; unfold EM_B; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E37m : ew E 37 = Z_to_bv 64 d)
  by (subst E; unfold EM_B; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (EGm : forall (j : nat) (r : bv 5), Z.of_nat j = bv_unsigned r -> (j < 32)%nat -> ew E j = getr regs2 r)
  by (intros j r Hj Hlt; subst E; unfold EM_B; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat regs2 _ j r Hj)).
destruct (tv_mid_entry_B W2 regs2 mem2 TV_RET_OPEN_B ty 0 0 v str kids keys 0 d cs
  H9 Hv0 Hv8 Hvc Hvapp
  ltac:(rewrite Hsp2; lia) ltac:(rewrite Hsp2, Zminus_mod, Hal16; reflexivity) ltac:(rewrite Hsp2; lia)
  ltac:(rewrite Hsp2; lia) ltac:(rewrite Hsp2; intros a Ha; apply Hpres; lia)
  ltac:(rewrite Hsp2; exact HSL) Hd Hty Vty
  Hstr Vstr Hkids Vkids Hkeys Vkeys ltac:(lia) Vn ltac:(lia) ltac:(lia) ltac:(lia) HRA
  ltac:(rewrite <- HE; exact Hcs)) as [HS SHOK].
rewrite <- HE in HS, SHOK.
pose proof (TVMN_refl mem2) as HMN.
paj_run_to_tok_x_inv (RUNTOIR mem2) HS HJ SHOK HMN TV_SPAN TV_CLOSE_OFF_B.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp0 - 192 - sp0')) end;
  [ reflexivity | cbn [ew]; rewrite ?Usp, ?Usp34; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]. apply awr_ok_nil. }
clear HF HG.
lazymatch type of HFr with
| frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 184 <= a < sp0 - 104) ->
    aview SEGS (w_H W2) mB a = aview SEGS (w_H W2) mA a)
  by (intros a Ha Hn; apply (tv_aview_of_frame W2 Ex rsx mA mB a HFr); [|exact Ha];
      intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Usp, ?Usp34, ?Uv, ?Uv41 in Hr; lia|]); destruct Hin);
  assert (KR : forall x : word, (bv_unsigned x < sp0 - 184 \/ sp0 - 104 <= bv_unsigned x) ->
    mrestrict (w_H W2) mB x = mrestrict (w_H W2) mA x)
  by (intros x Hx; apply HFr; intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Usp, ?Usp34, ?Uv, ?Uv41 in Hr; lia|]); destruct Hin)
end.
clear HFr.
prreg HS (1%bv : bv 5) P1; prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (18%bv : bv 5) P18.
prreg HS (19%bv : bv 5) P19; prreg HS (21%bv : bv 5) P21.
pmkst HS.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  lazymatch goal with HJ0 : ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (HK Ex ssx msx _ _ HS ltac:(vm_compute; reflexivity) HJ0) end
end.
- unfold spZ at 1. rewrite P2, E2. exact Hsp2.
- rewrite P1. exact (EGm 1%nat (1%bv : bv 5) eq_refl ltac:(lia)).
- rewrite P3. exact (EGm 3%nat (3%bv : bv 5) eq_refl ltac:(lia)).
- rewrite P4. exact (EGm 4%nat (4%bv : bv 5) eq_refl ltac:(lia)).
- rewrite P8. exact (EGm 8%nat (8%bv : bv 5) eq_refl ltac:(lia)).
- rewrite P9. rewrite (EGm 9%nat (9%bv : bv 5) eq_refl ltac:(lia)). exact H9.
- rewrite P18. exact (EGm 18%nat (18%bv : bv 5) eq_refl ltac:(lia)).
- rewrite P19. exact (EGm 19%nat (19%bv : bv 5) eq_refl ltac:(lia)).
- rewrite P21. exact (EGm 21%nat (21%bv : bv 5) eq_refl ltac:(lia)).
- pose proof (ts_region_nth (L := B_prog_listing) (PA := PI_prog_B) _ _ _ 0%nat _ HS eq_refl) as HR0;
  cbn [ms_mem restrict] in HR0.
  unfold tv_slots_B. split; [|split].
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 16 8%N (SLit 0) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; rewrite tv_U_lit0 in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 16) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 24 8%N (SOff 37 0) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite ts_U_atom_mod in V;
    rewrite E37m in V;
    rewrite unsigned_lit_small in V by lia;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 24) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 72 8%N (SOff 32 0) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite ts_U_atom_mod in V;
    rewrite E32m in V;
    rewrite unsigned_lit_small in V by (unfold SHADOW_OFF; lia);
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 72) by lia end; exact V.
- exact KP.
- exact KR.
- exact HMN.
Qed.


(* ==== THE LEAF ARMS END TO END (B twin of S10TxValue.v at walk-S10 7623a0781f8 / f1eb5e26dfc: the transfers, the tree
   lemmas, the text's binders and premises, tv_qt, tv_facts_at, tv_tail_put / tv_tail_string, tv_node_facts, tv_lit_src,
   tv_main_lit / tv_main_num / tv_main_str), at image B: frame 192, prh_img_B, the B run lemmas. The image-generic part
   (the transfers and the tree lemmas, tv_not_fp .. tv_foot_low, tv_buf_inFP, tv_garr8_prefix) is a B-local copy:
   DELETE when S10TxValGlue lands ==== *)
(* ==== TRANSFERS of the text's facts across a change that keeps the reader view off a window ==== *)
(* a byte off the image: equal views give equal client bytes, so writability moves *)
Lemma tv_client_av2 : forall (H H' : word -> bool) (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS H' m' a = aview SEGS H m a -> mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. pose proof (mbyte_of_aview SEGS H H' m m' a E) as M. unfold mbyte in M.
rewrite (seg_rom_none SEGS a Ha Hn) in M.
destruct (mrestrict H' m' (Z_to_bv 64 a)), (mrestrict H m (Z_to_bv 64 a)); congruence.
Qed.
Lemma tv_wr_av2 : forall (W W' : world SEGS) mem mem' a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a ->
  writable_at SEGS (rdW W mem) a -> writable_at SEGS (rdW W' mem') a.
Proof.
intros W W' mem mem' a Ha Hn E Hw. unfold writable_at, wview in *.
rewrite unsigned_lit_small in * by lia.
rewrite (tv_client_av2 (w_H W) (w_H W') mem mem' a Ha Hn E). exact Hw.
Qed.
Lemma tv_wr_av : forall (W : world SEGS) mem mem' a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a ->
  writable_at SEGS (rdW W mem) a -> writable_at SEGS (rdW W mem') a.
Proof. intros W mem mem' a Ha Hn E Hw. exact (tv_wr_av2 W W mem mem' a Ha Hn E Hw). Qed.
Lemma tv_val_av : forall (W : world SEGS) mem mem' a k v,
  (forall i, (i < k)%nat -> aview SEGS (w_H W) mem' (a + Z.of_nat i) = aview SEGS (w_H W) mem (a + Z.of_nat i)) ->
  val_mem SEGS (rdW W mem) a k v -> val_mem SEGS (rdW W mem') a k v.
Proof.
intros W mem mem' a k v HA HV i Hi.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem' (a + Z.of_nat i) (HA i Hi)). exact (HV i Hi).
Qed.

(* the record, the buffer, the place, a source window and the ledger move with the view (the record and the place
   are stack bytes, the buffer a heap block: neither is an image byte, so their writability moves too) *)
Lemma tv_rec_av : forall (W : world SEGS) mem mem' t b len cap f,
  (forall a, t <= a < t + 28 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prhtx_rec W mem t b len cap f -> prhtx_rec W mem' t b len cap f.
Proof.
intros W mem mem' t b len cap f HA (R1 & R2 & R3 & Rf & V1 & V2 & V3 & V4).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact Rf|].
split; [|split; [|split]]; (eapply tv_val_av; [|eassumption]); intros i Hi; apply HA; lia.
Qed.

Lemma tv_inv_av : forall ly S Hp (W : world SEGS) mem mem' md Lam b len cap txt,
  ARx ly S Hp W mem md ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prhtx_inv B Lam ly S W mem b len cap txt -> prhtx_inv B Lam ly S W mem' b len cap txt.
Proof.
intros ly S Hp W mem mem' md Lam b len cap txt HAR HA
  (Hl & [Hz | (Hc & Hlc & Hin & Hby & H4096 & Hceil & Hamr & Hw & Hra & Hhull & Hlam)]).
- split; [exact Hl | left; exact Hz].
- pose proof asan_consts as (C1 & _).
  assert (Hrq : req_size cap = cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
  split; [exact Hl|]. right. split; [exact Hc|]. split; [exact Hlc|]. split; [exact Hin|]. split.
  + unfold bytes_at in *. apply (tv_garr8_move W mem mem' b _ Hby). intros j Hj.
    rewrite length_app in Hj. cbn [length] in Hj. apply HA. lia.
  + split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hamr|]. split; [|split; [|split; [|exact Hlam]]].
    * intros a Ha. apply (tv_wr_av W mem mem' a ltac:(lia)); [| apply HA; lia | exact (Hw a Ha)].
      apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b cap a HAR Hin). rewrite Hrq. lia.
    * eapply range_addressable_agree; [|exact Hra]. intros x Hx. pose proof (s10_shadow_low x ltac:(lia)).
      apply HA. lia.
    * intros s Hs. pose proof (s10_hull_low b cap s ltac:(lia) ltac:(lia) ltac:(lia) Hs).
      rewrite HA by lia. exact (Hhull s Hs).
Qed.

Lemma tv_place_av : forall ly S (W : world SEGS) regs regs' mem mem' dw t,
  spZ regs' = spZ regs -> YM05.alloc_ceiling <= spZ regs -> spZ regs + dw <= 2 ^ 47 ->
  (forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, 0 <= a < 2 ^ 46 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prhtx_place ly S W regs mem dw t -> prhtx_place ly S W regs' mem' dw t.
Proof.
intros ly S W regs regs' mem mem' dw t Hsp Hc H47 HA HS (H8 & Hlo & Hhi & Hw & Hra).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
split; [exact H8|]. split; [lia|]. split; [lia|]. split.
- intros a Ha. apply (tv_wr_av W mem mem' a ltac:(lia)); [|apply HA; lia | exact (Hw a Ha)].
  intros Hi. pose proof (@pa_segs_low _ _ PA a Hi). lia.
- eapply range_addressable_agree; [|exact Hra]. intros x Hx. pose proof (s10_shadow_low x ltac:(lia)).
  apply HS. lia.
Qed.

Lemma tv_srcrd_av : forall (W : world SEGS) mem mem' s l,
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  src_rd W mem s l -> src_rd W mem' s l.
Proof.
intros W mem mem' s l HA (Hb & H4096 & Hc & Hamr & Hra & Hhull).
pose proof asan_consts as (C1 & _).
split; [|split; [exact H4096|split; [exact Hc|split; [exact Hamr|split]]]].
- unfold bytes_at in *. apply (tv_garr8_move W mem mem' s l Hb). intros j Hj. apply HA. lia.
- eapply range_addressable_agree; [|exact Hra]. intros x Hx. pose proof (s10_shadow_low x ltac:(lia)).
  apply HA. lia.
- intros Hn s0 Hs0. pose proof (s10_hull_low s _ s0 ltac:(lia) Hn ltac:(lia) Hs0).
  rewrite HA by lia. exact (Hhull Hn s0 Hs0).
Qed.

(* ==== THE TREE: pj_nodeR moves with its footprint's bytes (PjStruct.v's pj_node_frame, restated over the
   readers; the plain file read as a reference, not cited) ==== *)
Lemma tv_u64_eq : forall (m m' : word -> option byte) a v, PRH_Reader.rd_u64 SEGS m a v ->
  (forall x, a <= x < a + 8 -> mbyte SEGS m' x = mbyte SEGS m x) -> PRH_Reader.rd_u64 SEGS m' a v.
Proof.
intros m m' a v (Hv & V) HM. split; [exact Hv|]. intros i Hi. rewrite HM by lia. exact (V i Hi).
Qed.
Lemma tv_u32_eq : forall (m m' : word -> option byte) a v, PRH_Reader.rd_u32 SEGS m a v ->
  (forall x, a <= x < a + 4 -> mbyte SEGS m' x = mbyte SEGS m x) -> PRH_Reader.rd_u32 SEGS m' a v.
Proof.
intros m m' a v (Hv & V) HM. split; [exact Hv|]. intros i Hi. rewrite HM by lia. exact (V i Hi).
Qed.
Lemma tv_hdrR_eq : forall (m m' : word -> option byte) p ty num str kids keys n cap,
  PRH_Reader.pj_hdrR SEGS m p ty num str kids keys n cap ->
  (forall x, p <= x < p + 56 -> mbyte SEGS m' x = mbyte SEGS m x /\ (writable_at SEGS m x -> writable_at SEGS m' x)) ->
  PRH_Reader.pj_hdrR SEGS m' p ty num str kids keys n cap.
Proof.
intros m m' p ty num str kids keys n cap ((H8 & Hrw) & T & N & Sx & K & Y & Nn & C) HM.
split; [split; [exact H8 | intros x Hx; apply (proj2 (HM x Hx)); exact (Hrw x Hx)]|].
split; [apply (tv_u32_eq m m' p ty T); intros x Hx; apply (proj1 (HM x ltac:(lia)))|].
split; [apply (tv_u64_eq m m' _ num N); intros x Hx; apply (proj1 (HM x ltac:(lia)))|].
split; [apply (tv_u64_eq m m' _ str Sx); intros x Hx; apply (proj1 (HM x ltac:(lia)))|].
split; [apply (tv_u64_eq m m' _ kids K); intros x Hx; apply (proj1 (HM x ltac:(lia)))|].
split; [apply (tv_u64_eq m m' _ keys Y); intros x Hx; apply (proj1 (HM x ltac:(lia)))|].
split; [apply (tv_u64_eq m m' _ n Nn); intros x Hx; apply (proj1 (HM x ltac:(lia)))|].
apply (tv_u64_eq m m' _ cap C); intros x Hx; apply (proj1 (HM x ltac:(lia))).
Qed.
Lemma tv_itemsR_mono : forall (P Q : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  (forall i u D1, (i < length l)%nat -> In u l -> incl D1 D ->
     P (a + 56 * Z.of_nat i) u D1 -> Q (a + 56 * Z.of_nat i) u D1) ->
  PRH_Reader.pj_itemsR P a l D -> PRH_Reader.pj_itemsR Q a l D.
Proof.
intros P Q l. induction l as [|u r IH]; intros a D H Hl; cbn [PRH_Reader.pj_itemsR] in *.
- exact Hl.
- destruct Hl as (D1 & D2 & E & HP & HR). exists D1, D2. split; [exact E|]. split.
  + specialize (H 0%nat u D1). replace (a + 56 * Z.of_nat 0) with a in H by lia.
    apply H; [cbn; lia | left; reflexivity | subst D; intros b Hb; apply in_or_app; left; exact Hb | exact HP].
  + apply (IH (a + 56) D2); [|exact HR].
    intros i v D3 Hi Hv Hinc HP3.
    replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
    apply H; [cbn; lia | right; exact Hv | subst D; intros b Hb; apply in_or_app; right; apply Hinc; exact Hb | exact HP3].
Qed.
Lemma tv_memsR_mono : forall (m m' : word -> option byte) lb (P Q : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  (forall i nm u x k D1, (i < length l)%nat -> In (nm, u) l -> In (x, k) D -> incl D1 D ->
     PRH_Reader.rd_u64 SEGS m (ka + 8 * Z.of_nat i) x -> PRH_Reader.pj_cstrR SEGS m lb x k nm ->
     P (a + 56 * Z.of_nat i) u D1 ->
     PRH_Reader.rd_u64 SEGS m' (ka + 8 * Z.of_nat i) x /\ PRH_Reader.pj_cstrR SEGS m' lb x k nm /\
     Q (a + 56 * Z.of_nat i) u D1) ->
  PRH_Reader.pj_memsR SEGS m lb P a ka l D -> PRH_Reader.pj_memsR SEGS m' lb Q a ka l D.
Proof.
intros m m' lb P Q l. induction l as [|[nm u] r IH]; intros a ka D H Hl; cbn [PRH_Reader.pj_memsR] in *.
- exact Hl.
- destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & HP & HR).
  assert (G : PRH_Reader.rd_u64 SEGS m' ka x /\ PRH_Reader.pj_cstrR SEGS m' lb x k nm /\ Q a u D1).
  { specialize (H 0%nat nm u x k D1).
    replace (ka + 8 * Z.of_nat 0) with ka in H by lia. replace (a + 56 * Z.of_nat 0) with a in H by lia.
    apply H; [cbn; lia | left; reflexivity | subst D; left; reflexivity
             | subst D; intros b Hb; right; apply in_or_app; left; exact Hb | exact Hx | exact Hc | exact HP]. }
  destruct G as (Hx' & Hc' & HQ).
  exists x, k, D1, D2. split; [exact E|]. split; [exact Hx'|]. split; [exact Hc'|]. split; [exact HQ|].
  apply (IH (a + 56) (ka + 8) D2); [|exact HR].
  intros i nm' v x' k' D3 Hi Hv Hxk Hinc Hx3 Hc3 HP3.
  replace (ka + 8 + 8 * Z.of_nat i) with (ka + 8 * Z.of_nat (S i)) in Hx3 |- * by lia.
  replace (a + 56 + 56 * Z.of_nat i) with (a + 56 * Z.of_nat (S i)) in HP3 |- * by lia.
  apply H; [cbn; lia | right; exact Hv | subst D; right; apply in_or_app; right; exact Hxk
           | subst D; intros b Hb; right; apply in_or_app; right; apply Hinc; exact Hb
           | exact Hx3 | exact Hc3 | exact HP3].
Qed.

Lemma tv_nodeR_frame : forall tv (m m' : word -> option byte) lb p D,
  PRH_Reader.pj_nodeR SEGS m lb p tv D ->
  (forall x, PRH_Reader.pj_footR p D x ->
     mbyte SEGS m' x = mbyte SEGS m x /\ (writable_at SEGS m x -> writable_at SEGS m' x)) ->
  PRH_Reader.pj_nodeR SEGS m' lb p tv D.
Proof.
intros tv. induction tv as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m m' lb p D H HM; cbn [PRH_Reader.pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
  (split; [apply (tv_hdrR_eq m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (PRH_Reader.pj_cstrR_frame SEGS m m' lb str k txt Hc). intros x Hx. refine (proj1 (HM x _)).
  right. exists (str, k). split; [subst D; left; reflexivity | unfold PRH_Reader.pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED].
  apply (PRH_Reader.pj_cstrR_frame SEGS m m' lb str k s Hc). intros x Hx. refine (proj1 (HM x _)).
  right. exists (str, k). split; [subst D; left; reflexivity | unfold PRH_Reader.pj_holdsR; cbn [fst snd]; exact Hx].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split; [exact Hcap|].
  assert (Hin : 0 < cap -> In (kids, 56 * cap) D).
  { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (tv_itemsR_mono (PRH_Reader.pj_nodeR SEGS m lb) (PRH_Reader.pj_nodeR SEGS m' lb)); [|exact Hi].
  intros i u D1 Hil Hu Hinc HP.
  assert (Hp : 0 < cap) by lia.
  rewrite Forall_forall in IH.
  apply (IH u Hu m m' lb _ D1 HP).
  intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
  + right. exists (kids, 56 * cap). split; [apply (Hin Hp) | unfold PRH_Reader.pj_holdsR; cbn [fst snd]; lia].
  + right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|]. split; [exact Hcap|].
  assert (Hin : 0 < cap -> In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
  { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. split; [left; reflexivity | right; left; reflexivity]. }
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  exists Di. split; [exact ED|].
  apply (tv_memsR_mono m m' lb (PRH_Reader.pj_nodeR SEGS m lb) (PRH_Reader.pj_nodeR SEGS m' lb)); [|exact Hi].
  intros i nm u x k D1 Hil Hu Hxk Hinc Hx Hcs HP.
  assert (Hp : 0 < cap) by lia.
  split; [|split].
  + apply (tv_u64_eq m m' _ x Hx). intros y Hy. refine (proj1 (HM y _)). right. exists (keys, 8 * cap).
    split; [apply (proj2 (Hin Hp)) | unfold PRH_Reader.pj_holdsR; cbn [fst snd]; lia].
  + apply (PRH_Reader.pj_cstrR_frame SEGS m m' lb x k nm Hcs). intros y Hy. refine (proj1 (HM y _)).
    right. exists (x, k). split; [apply HDi; exact Hxk | unfold PRH_Reader.pj_holdsR; cbn [fst snd]; exact Hy].
  + rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (IH m m' lb _ D1 HP).
    intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
    * right. exists (kids, 56 * cap). split; [apply (proj1 (Hin Hp)) | unfold PRH_Reader.pj_holdsR; cbn [fst snd]; lia].
    * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

(* ==== THE TREE ACROSS A JOURNAL whose footprint is a text's (the record and the buffer): the tree's bytes lie in
   harness blocks of Lam or in one fake frame, which the buffer (no harness block's base, prhtx_inv) and the record
   (apart, by premise) never meet; a journal keeps such bytes ==== *)
Lemma tv_not_fp : forall ly S Hp W mem md Lam peak cnt fail ran most own t b cap len txt x,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhtx_inv B Lam ly S W mem b len cap txt ->
  ((exists bb m, In (bb, m) Lam /\ bb <= x < bb + m) \/
   (exists cid pos, In (cid, pos) (frames S) /\ in_zr x (frame_rng ly (cid, pos)))) ->
  ~ (t <= x < t + 28) -> ~ inFP (prhtx_fp t b cap) x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own t b cap len txt x HAR HL Hinv Hx Ht Hf.
destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc & Hb)]; [exact (Ht Hr)|].
destruct Hinv as (_ & [(Hz & _) | (Hc0 & _ & Hin & _ & _ & _ & _ & _ & _ & _ & Hlam)]); [lia|].
destruct Hx as [(bb & m & Hbm & Hx) | (cid & pos & Hfr & Hx)].
- destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran bb m _ _ HL Hbm) as (Hm0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab. pose proof (Hlam bb m Hbm) as Hne.
  change (@cf_head CfParams_preset) with 16 in Hne.
  assert (Hd : (b, cap) <> (bb - 16, m + 16)) by (intros E; injection E as E1 _; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin Hab Hd) as D.
  unfold zdisjoint in D. cbn [fst snd] in D.
  assert (Hrq : req_size (m + 16) = m + 16) by (unfold req_size; destruct (Z.eqb_spec (m + 16) 0); lia).
  rewrite Hrq in D. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin Hfr) as D.
  unfold zdisjoint, frame_rng, in_zr in *. cbn [fst snd] in *. lia.
Qed.

Definition tv_zz_eq_dec : forall p q : Z * Z, {p = q} + {p <> q}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* where a footprint byte lies *)
Lemma tv_foot_home : forall ly S Lam v D x,
  prhtx_home Lam ly S v 56 -> (forall bk, In bk D -> In bk Lam) -> PRH_Reader.pj_footR v D x ->
  (exists bb m, In (bb, m) Lam /\ bb <= x < bb + m) \/
  (exists cid pos, In (cid, pos) (frames S) /\ in_zr x (frame_rng ly (cid, pos))).
Proof.
intros ly S Lam v D x [(bb & m & Hin & Hb & Hm) | (cid & pos & Hin & Hfr)] HD [Hx | ((a, k) & Hak & Hx)].
- left. exists bb, m. split; [exact Hin | lia].
- left. exists a, k. split; [exact (HD _ Hak) | unfold PRH_Reader.pj_holdsR in Hx; cbn [fst snd] in Hx; lia].
- right. exists cid, pos. split; [exact Hin | exact (Hfr x Hx)].
- left. exists a, k. split; [exact (HD _ Hak) | unfold PRH_Reader.pj_holdsR in Hx; cbn [fst snd] in Hx; lia].
Qed.

(* the tree's footprint at a journal's end (any world relation R: it reads only the keep clauses) *)
Lemma tv_foot_journal : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem'
  md' k WS Lam peak cnt fail ran most ow t b cap len txt v D,
  ajournal_xwR (SK := SK) SEGS B (prh_pst (PI := prh_img_B)) ARx R STK sp0 (prhtx_fp t b cap)
    ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most ow ->
  prhtx_inv B Lam ly S W mem b len cap txt ->
  prhtx_home Lam ly S v 56 -> (forall bk, In bk D -> In bk Lam) ->
  (forall x, PRH_Reader.pj_footR v D x -> ~ (t <= x < t + 28)) ->
  forall x, PRH_Reader.pj_footR v D x -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x.
Proof.
intros R STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS Lam peak cnt fail ran most ow t b cap len txt v D
  HJ HAR HL Hinv Hhome HD Hap x Hx.
pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone.
pose proof (tv_foot_home ly S Lam v D x Hhome HD Hx) as Hw.
pose proof (tv_not_fp ly S Hp W mem md Lam peak cnt fail ran most ow t b cap len txt x HAR HL Hinv Hw (Hap x Hx)) as Hnf.
destruct Hw as [(bb & m & Hbm & Hxb) | (cid & pos & Hfr & Hxf)].
- destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran bb m _ _ HL Hbm) as (Hm0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab.
  assert (Hrq : req_size (m + 16) = m + 16) by (unfold req_size; destruct (Z.eqb_spec (m + 16) 0); lia).
  replace x with (bb - 16 + (x - (bb - 16))) in Hnf |- * by lia.
  destruct (in_dec tv_zz_eq_dec (bb - 16, m + 16) (ablocks B ly' S'))
    as [Hin' | Hout].
  + apply (F2 (bb - 16) (m + 16) (x - (bb - 16)) Hab Hin'); [rewrite Hrq; lia | exact Hnf].
  + exfalso. apply Hnf. apply (Hgone (bb - 16) (m + 16) (x - (bb - 16)) Hab Hout). rewrite Hrq. lia.
- apply (F4 cid pos x Hfr); [left; exact Hxf | exact Hnf].
Qed.

(* the node's shadow at a journal's end: a harness block's by ARx's field 14 there (its base still in Hp, by the
   ledger), a fake frame's by the journal's frame clause. #102: the ledger's own field (g_own_ran_out) may differ at the
   two ends (a refused grow sets it), so the two ledgers are taken at ow and ow'. Any world relation R: it reads only the
   journal's allocator invariant and frame clause *)
Lemma tv_node_ra_end : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem'
  md' k WS Lam peak cnt fail ran most ow ow' t b cap len txt v,
  ajournal_xwR (SK := SK) SEGS B (prh_pst (PI := prh_img_B)) ARx R STK sp0 (prhtx_fp t b cap)
    ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most ow ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most ow' ->
  prhtx_inv B Lam ly S W mem b len cap txt -> YM05.alloc_ceiling <= t ->
  prhtx_home Lam ly S v 56 -> v mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  range_addressable (aview SEGS (w_H W') mem') SHADOW_OFF v 56.
Proof.
intros R STK sp0 ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS Lam peak cnt fail ran most ow ow' t b cap len txt v
  HJ HAR HL HL' Hinv Ht Hhome Hv8 HRA.
pose proof (ajxR_ar HJ) as HAR'. pose proof (ajxR_frm HJ) as F4.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hhome as [(bb & m & Hbm & Hb & Hm) | (cid & pos & Hfr & Hxf)].
- destruct (prh_ledger_hblock B ly' S' Hp' W' mem' Lam peak cnt fail ran bb m _ _ HL' Hbm) as (Hm0 & Hab & Hhp & _).
  change (@cf_head CfParams_preset) with 16 in Hab, Hhp.
  destruct (alx_hshadow SEGS B ARx LAWS ly' S' Hp' W' mem' md' _ _ HAR' Hab Hhp) as [Hbs _].
  change (@cf_head CfParams_preset) with 16 in Hbs.
  assert (Hrq : req_size (m + 16) = m + 16) by (unfold req_size; destruct (Z.eqb_spec (m + 16) 0); lia).
  rewrite Hrq in Hbs. replace (bb - 16 + 16) with bb in Hbs by lia. replace (m + 16 - 16) with m in Hbs by lia.
  exact (block_shadow_range (aview SEGS (w_H W') mem') SHADOW_OFF bb m v 56 Hbs ltac:(lia) ltac:(lia)).
- destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfr) as (H4096 & Hfc & Happ).
  destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfr) as (Hfa32 & _).
  pose proof (Hxf v ltac:(lia)) as Hlo. pose proof (Hxf (v + 55) ltac:(lia)) as Hhi.
  unfold frame_rng, in_zr in Hlo, Hhi. cbn [fst snd] in Hlo, Hhi.
  eapply range_addressable_agree; [|exact HRA]. intros x Hx.
  set (fa := frame_addr ly cid pos) in *. set (fs := fs_frame_bytes cid) in *.
  assert (Hfs0 : 0 <= fs) by (subst fs; unfold fs_frame_bytes; apply (proj2 (Z.shiftl_nonneg 64 cid)); lia).
  assert (Hfa8 : fa mod 8 = 0).
  { apply Z.mod_divide in Hfa32 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 4) * 8) by lia.
    apply Z.mod_mul. lia. }
  pose proof (Z.div_mod fa 8 ltac:(lia)). pose proof (Z.div_mod v 8 ltac:(lia)).
  pose proof (Z.div_mod fs 8 ltac:(lia)). pose proof (Z.mod_pos_bound fs 8 ltac:(lia)).
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  apply (F4 cid pos _ Hfr).
  + right. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
    change (fs_frame_bytes cid) with fs. change (frame_addr ly cid pos) with fa. split; lia.
  + intros Hf. destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc & Hbx)].
    * unfold shadow_of_addr, SHADOW_OFF in Hr. lia.
    * destruct Hinv as (_ & [(Hz & _) | (_ & _ & Hin & _)]); [lia|].
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b cap HAR Hin) as (_ & Hb4 & Hbc & Hbapp & _).
      unfold in_app, kLowShadowBeg, ASAN_CEIL, shadow_of_addr, SHADOW_OFF in *. lia.
Qed.

(* a footprint byte is client memory below alloc_ceiling, off the image *)
Lemma tv_foot_low : forall ly S Hp W mem md Lam peak cnt fail ran most own v D x,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhtx_home Lam ly S v 56 -> (forall bk, In bk D -> In bk Lam) -> PRH_Reader.pj_footR v D x ->
  4096 <= x < YM05.alloc_ceiling /\ ~ in_img SEGS x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own v D x HAR HL Hh HD Hx.
destruct (tv_foot_home ly S Lam v D x Hh HD Hx) as [(bb & m & Hbm & Hxb) | (cid & pos & Hfr & Hxf)].
- destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran bb m _ _ HL Hbm) as (Hm0 & Hab & _).
  change (@cf_head CfParams_preset) with 16 in Hab.
  assert (Hrq : req_size (m + 16) = m + 16) by (unfold req_size; destruct (Z.eqb_spec (m + 16) 0); lia).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
  rewrite Hrq in Hc. split; [lia|].
  apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hab). rewrite Hrq. lia.
- destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfr) as (H4096 & Hfc & _).
  unfold frame_rng, in_zr in Hxf. cbn [fst snd] in Hxf. split; [lia|].
  exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HAR Hfr Hxf).
Qed.

#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B (prh_pst (PI := prh_img_B)) ARx).
#[local] Notation AJW := (ajournal_xw (SK := SK) SEGS B (prh_pst (PI := prh_img_B)) ARx).
(* the journal at WR, for every cut after the opening call (YCbqG.v ajournal_xR / ajournal_xwR) *)
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B (prh_pst (PI := prh_img_B)) ARx WR).
#[local] Notation AJWR := (ajournal_xwR (SK := SK) SEGS B (prh_pst (PI := prh_img_B)) ARx WR).
(* ---- the callees' texts (the Tx part, PRH_FnTx.v), at the allocator trace closure's parameter CTX0 (the batch: the cursor
   run word DW is gone) ---- *)
Variables (CTX0 : list (list Z)).
(* the callee texts tx_value calls (the kit's texts, PRH_FnTx.v 7cf918708def): tx_put (owner a Theorem Labs lane, tx_put B')
   and tx_string (owner of tx_string B'), texts :414 / :665; tx_line is DISCHARGED below by BTxLine.tx_line_B_holds *)
Hypothesis TXPUT : ttx_put_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
Hypothesis TXSTR : ttx_string_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0.
(* ---- Tx102Glue.v's Section hypotheses (same names, same statements; owners there) ---- *)
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B). Witness BTxLine.tl_zs_aligned_TfibB *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN (owner h-mani-a8, rule 18:56Z: img_shadow_vis_cf over the PER-INSTANCE CfImg bounds, restated over
   ARx; B' instance lib/AU/AImgShadowVisCfB.v tfib_img_shadow_vis_cf_B, cold/h-mani-a8-alloc102) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> cf_img_lo <= a < cf_img_top ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the CfImg bounds hold the instance's kept_img bounds (witness BTxLine.tl_img_cf_box_B at CfImgB.CfImg_B) *)
Hypothesis tv_img_cf_box : cf_img_lo <= @pa_lo _ _ PA /\ @pa_hi _ _ PA <= cf_img_top.
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B; BTxLine.v's tl_lit_img, needed only to discharge tx_line
   by tx_line_B_holds): tx_line's two literals are image strings. Witness BTxLine.tl_lit_img_TfibB *)
Hypothesis tl_lit_img : kept_img (PA := PA) B BTxLine.STR19 1 /\ kept_img (PA := PA) B BTxLine.STR29 2.
(* tx_line at image B', DISCHARGED (was the Section hypothesis TXLINE): BTxLine.tx_line_B_holds, this row's tx_line
   walk (BTxLine.v 5b34c2e84656 :1229-1238, Qed on PRH_FnTx.v 7cf918708def ttx_line_specX :821, SRr' at :850) *)
Let TXLINE : ttx_line_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0 :=
  BTxLine.tx_line_B_holds B ARx LAWS zs_aligned img_shadow_vis_x tv_img_cf_box tl_lit_img CTX0 TXPUT.
(* MARKED STAND-IN (owner a Theorem Labs lane, the unit's image binding of B, route (a) of PRH_Base.v, as S10TxLine.v's tl_lit_img and
   S10TxString.v's ts_lit_img; S10TxValue.v's tv_lit_img at image B): the ten literals tx_value hands tx_put at B
   (.str "true" 0x20f60, .str.2 "false" 0x20f80, .str.3 "null" 0x20fa0, .str.20 "{" 0x21200, .str.21 "[" 0x21220,
   .str.22 "," 0x21240, .str.23 ":" 0x21260, .str.24 " " 0x21280, .str.25 "}" 0x212a0, .str.26 "]" 0x212c0; offsets in
   the read-only band A_OBJ 2, DERIVED from B's listing's auipc / addi) are image
   strings at the length passed *)
Hypothesis tv_lit_img : Forall (fun sl => kept_img (PA := PA) B (VAL (A_OBJ 2) + fst sl) (snd sl))
  [(69472, 4); (69504, 5); (69536, 4); (70144, 1); (70176, 1); (70208, 1); (70240, 1); (70272, 1); (70304, 1);
   (70336, 1)].
(* SRC-CEIL (the record's stand-in) is NOT a hypothesis here: since the batch, PRH_Base.v src_rd
   (:1921-1932) bounds the window by p + len <= alloc_ceiling (:1929), without the old `+ 8`, which the number arm's
   prhtx_bvis gives. *)

(* ---- the stack budgets at image B (DERIVED: PRH_Base.v's STK_* at prh_img_B, by computation) ---- *)
Lemma tv_stkv : forall k, @STK_tx_value prh_img_B k = Z.of_nat k * 192 + @STK_tx_value prh_img_B 0.
Proof.
intros k. unfold STK_tx_value. change (@pi_frame prh_img_B F_tx_value) with 192. rewrite Nat2Z.inj_succ. cbn [Z.of_nat]. lia.
Qed.
Lemma tv_stk_facts : 0 <= @STK_tx_put prh_img_B /\ 192 + @STK_tx_put prh_img_B <= @STK_tx_value prh_img_B 0 /\
  0 <= @STK_tx_line prh_img_B /\ 192 + @STK_tx_line prh_img_B <= @STK_tx_value prh_img_B 0 /\
  0 <= @STK_tx_string prh_img_B /\ 192 + @STK_tx_string prh_img_B <= @STK_tx_value prh_img_B 0 /\
  192 + 2 * ESTACK <= @STK_tx_value prh_img_B 0.
Proof. repeat split; vm_compute; discriminate. Qed.
(* a callee-saved register is kept *)
Lemma tv_ap : forall rA rB, aregs_preserved rA rB -> forall r : bv 5, acallee_saved (bv_unsigned r) -> getr rB r = getr rA r.
Proof. intros rA rB H r Hr. pose proof (H _ Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. Qed.
(* a text's budgeted m-form post is monotone in its budget claim and its body (fpostWbmR R = fpostWbR R P .. (fQmn mem
   Q)): a callee's post is read back in the shape the caller folds (the batch: the posts are budgeted). Over any world
   relation R: the callees' texts post at WR after the move *)
Lemma tv_fpostWm_mono : forall (R : world SEGS -> world SEGS -> Prop) (P1 P2 : list (list Z) -> Prop) STK1 dwc FP regsc
  lyc Sc Hpc Wc memc mdc
  (Q1 Q2 : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  (forall WS, P1 WS -> P2 WS) ->
  (forall ly' S' Hp' W' regs' mem' md', Q1 ly' S' Hp' W' regs' mem' md' -> Q2 ly' S' Hp' W' regs' mem' md') ->
  forall W' c', fpostWbmR (PI := prh_img_B) (PA := PA) B ARx SK R P1 STK1 dwc FP regsc lyc Sc Hpc Wc memc mdc Q1 W' c' ->
  fpostWbmR (PI := prh_img_B) (PA := PA) B ARx SK R P2 STK1 dwc FP regsc lyc Sc Hpc Wc memc mdc Q2 W' c'.
Proof.
intros R P1 P2 STK1 dwc FP regsc lyc Sc Hpc Wc memc mdc Q1 Q2 HPP HQ W' c' HN.
unfold fpostWbmR, fpostWbR, YCbqGwild.fpostW_xbR, fQmn in HN |- *.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k & WS & Hc & HPW & HJ & HW & HP & H1 & HM).
exists ly2, S2, Hp2, regs2, mem2, md2, k, WS. split; [exact Hc|]. split; [exact (HPP WS HPW)|].
split; [exact HJ|]. split; [exact HW|].
split; [exact HP|]. split; [exact (HQ _ _ _ _ _ _ _ H1) | exact HM].
Qed.

(* ==== THE TEXT'S BINDERS AND PREMISES (ttx_value_specX nn) ==== *)
Section g.
Variable nn : nat.
(* the model-run position (PresetRoomPos.iface_room_pos, the text's rp_* binders) *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
  (rp_H0 : list Z) (rp_hist : list YG00.chunk).
(* #102: the text's binders f0 (the record's `int failed` on entry) and own (the ledger's g_own_ran_out on entry) *)
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (dw t v pretty d b0 len0 cap0 f0 own : Z) (tv : PjTree.jv) (D : list (Z * Z))
  (txt : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most : Z).
#[local] Notation PP := (negb (pretty =? 0)).
#[local] Notation ADD := (concat (WriterValue.wvpieces tv PP d)).
#[local] Notation KS := (TxModel.tv_calls tv PP d).
#[local] Notation STKV := (@STK_tx_value prh_img_B nn).
#[local] Notation FP0 := (prhtx_fp t b0 cap0).
#[local] Notation sp0 := (spZ regs).
Hypothesis HPRE : afn_pre_x SEGS B ARx STKV ly S Hp W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem).
Hypothesis HHI : sp0 + 64 <= ly_stk_hi ly.
Hypothesis HRAC : raZ regs < YM05.alloc_ceiling.
(* fpre's fifth conjunct (#102, FRM0-ENTRY): the rounding mode is 0 at entry; every callee's fpre asks it again *)
Hypothesis HFRM : YK0o.frm_zero (@YK11.fp_csr fx).
Hypothesis HCLO : prh_univ_closure B CTX0.
Hypothesis HROOM : room_live_cf S.
Hypothesis HPOS : PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S.
(* the threaded allocator hull premise (PRH_FnTx.v ttx_value_specX, after the run position): the run has at most
   4 calls; every callee text (tx_put, tx_string, tx_line, tx_value one level down) takes it at the same rp_os *)
Hypothesis HRP4 : (length rp_os <= 4)%nat.
(* the batch's guarded room (the wild budget's entry room, PRH_FnTx.v :991) and guarded consumer window (:996), over
   the events of all the text's puts *)
Hypothesis HROOMW : f0 = 0 ->
  YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 KS)) (st_depot S).
Hypothesis HCONS : f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 KS)).
(* the text's run premise (#102, PRH_FnTx.v :1010), GUARDED: the run's events of all the text's puts from rp_i,
   when the text is entered with failed = 0 (entered failed it makes no event) *)
Hypothesis HEVS : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 KS).
Hypothesis HDEP : (PjTree.depth tv <= nn)%nat.
Hypothesis H10 : getr regs 10 = w64 t.
Hypothesis H11 : getr regs 11 = w64 v.
Hypothesis H12 : getr regs 12 = w64 pretty.
Hypothesis H13 : getr regs 13 = w64 d.
Hypothesis HPR : - 2 ^ 31 <= pretty < 2 ^ 31.
Hypothesis Hd0 : 0 <= d.
Hypothesis HdD : d + Z.of_nat (PjTree.depth tv) <= 2 ^ 31 - 1.
Hypothesis HFWIN : fwin ly W regs mem dw.
Hypothesis HPLACE : prhtx_place ly S W regs mem dw t.
Hypothesis HTRACE : prhtx_trace (PI := prh_img_B) (PA := PA) B ly W mem t.
Hypothesis HREC : prhtx_rec W mem t b0 len0 cap0 f0.
Hypothesis HINV : prhtx_inv B Lam ly S W mem b0 len0 cap0 txt.
Hypothesis HNODE : PRH_Reader.pj_nodeR SEGS (rdW W mem) (prh_lin Lam) v tv D.
Hypothesis HDLAM : forall bk, In bk D -> In bk Lam.
Hypothesis HHOME : prhtx_home Lam ly S v 56.
Hypothesis HRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56.
Hypothesis HBV : Forall (fun bk => prhtx_bvis W mem (fst bk) (snd bk)) D.
Hypothesis HAPT : v + 56 <= t \/ t + 28 <= v.
Hypothesis HLEN : len0 + Z.of_nat (length ADD) + 1 <= 2 ^ 28.
Hypothesis HLED : prh_ledger (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own.
Hypothesis HLIVE : blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX.
Hypothesis HMAX : 2 * (len0 + Z.of_nat (length ADD) + 1) < cf_malloc_max.
Hypothesis HFR0 : count_cid 0 (frames S) < fs_frames 0.

(* ---- the text's conclusion: the named post body of ttx_value_specX, txvP_Q (PRH_FnTx.v; txvP_Q_check there fails to
   build if it ever differs from the text's post), at this text's binders: the record's post with the text pre ACTUALLY
   appended, the outcome prhtx_out (DONE / FAILED AT ENTRY / REFUSED), DEAD, the tree's keeps, the room, and the
   position, the ledger inside its existential ---- *)
Definition QT : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  txvP_Q (PI := prh_img_B) (PA := PA) B rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem dw t v b0 len0 cap0 f0 own tv D
    txt Lam peak cnt fail ran most ADD KS.
(* the text's post: ONE fpostWbmR at WR (the move: every run of the text reaches tx_put's realloc), BUDGETED at
   wbudget_if f0 [] (the events of the text's own puts) (PRH_FnTx.v ttx_value_specX; no abort arm; a refused grow is
   the REFUSED outcome of QT) *)
Definition QF : world SEGS -> config -> Prop := fun W' c' =>
  fpostWbmR (PI := prh_img_B) (PA := PA) B ARx SK WR (wbudget_if f0 [] (length (prhtx_evs len0 cap0 KS)))
    STKV dw FP0 regs ly S Hp W mem md QT W' c'.

(* the node is 8-aligned (the reader's pj_rwR) *)
Lemma tv_v8 : v mod 8 = 0.
Proof.
destruct tv; cbn [PRH_Reader.pj_nodeR] in HNODE; destruct HNODE as (_ & _ & _ & _ & _ & _ & _ & _ & ((H8 & _) & _) & _);
  exact H8.
Qed.

(* ---- THE POST: the text's conclusion at a final state whose journal starts at the entry (at any budget WS: the
   batch's budgeted posts), from the record's post (prhtx_post at the callee's entry regs regsX, sp = the entry's), the
   outcome of the whole text, DEAD and its position (Tx102Glue.v tx_pos over KS) ---- *)
Lemma tv_qt : forall ly' S' Hp' W' regs' mem' md' k WS regsX b1 cap1 f1 own' pre,
  AJWR (STKV + dw) (sp0 + dw) FP0 ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS ->
  spZ regsX = sp0 ->
  prhtx_post (PA := PA) B Lam regsX dw ly S Hp ly' S' Hp' W' mem' t b0 cap0 b1 (len0 + Z.of_nat (length pre)) cap1 f1
    (txt ++ pre) ->
  prhtx_out f0 f1 own own' b0 cap0 b1 cap1 (TxModel.tx_capf len0 cap0 KS) ADD pre ->
  (f0 = 0 -> f1 = 0) ->
  room_live_cf S' ->
  tx_pos rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 f1 KS S' ->
  prh_ledger (PI := prh_img_B) (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own' ->
  QT ly' S' Hp' W' regs' mem' md'.
Proof.
intros ly' S' Hp' W' regs' mem' md' k WS regsX b1 cap1 f1 own' pre HJ HspX
  (Hrec & Hinv & (H8 & Hlo & Hhi & Hw & Hra) & HHp & Hgr & Hbb) HO HDEAD HRM HPOS' HLED'.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & HSTKV & Hceil & Hslo & _).
pose proof HPLACE as (_ & Htlo & _).
pose proof (ajxR_ar HJ) as HAR'.
assert (HFK : forall x, PRH_Reader.pj_footR v D x -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x).
{ apply (tv_foot_journal _ _ _ ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS Lam peak cnt fail ran most own t b0 cap0
    len0 txt v D HJ HAR HLED HINV HHOME HDLAM).
  intros x Hx. destruct (tv_foot_low ly S Hp W mem md Lam peak cnt fail ran most own v D x HAR HLED HHOME HDLAM Hx). lia. }
destruct (tx_pos_post _ _ _ _ _ _ _ _ _ _ _ HPOS') as (jF & hF & Hj1 & Hj2 & Hj3 & Hj4).
exists b1, cap1, f1, own', pre.
split; [|split; [exact HO|split; [exact HDEAD|split; [|split; [exact HFK|split; [|split; [|split; [exact HRM|]]]]]]]].
- split; [exact Hrec|]. split; [exact Hinv|]. split; [|split; [exact HHp | split; [exact Hgr | exact Hbb]]].
  split; [exact H8|]. split; [rewrite HspX in Hlo; exact Hlo|]. split; [rewrite HspX in Hhi; exact Hhi|].
  split; [exact Hw | exact Hra].
- apply (tv_nodeR_frame tv (rdW W mem) (rdW W' mem') (prh_lin Lam) v D HNODE).
  intros x Hx. destruct (tv_foot_low ly S Hp W mem md Lam peak cnt fail ran most own v D x HAR HLED HHOME HDLAM Hx) as [Hb Hn].
  pose proof (HFK x Hx) as E. split.
  + exact (mbyte_of_aview SEGS (w_H W) (w_H W') mem mem' x E).
  + intros Hwr. pose proof asan_consts as (C1 & _). exact (tv_wr_av2 W W' mem mem' x ltac:(lia) Hn E Hwr).
- exact (tv_node_ra_end _ _ _ ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS Lam peak cnt fail ran most own own' t b0
    cap0 len0 txt v HJ HAR HLED HLED' HINV ltac:(lia) HHOME tv_v8 HRA).
- rewrite Forall_forall. intros [x kx] Hin. cbn [fst snd].
  apply (s10_bvis_lam B ARx LAWS ly' S' Hp' W' mem' md' Lam peak cnt fail ran most own' W mem x kx HAR' HLED' (HDLAM _ Hin)).
  exact (proj1 (Forall_forall _ _) HBV _ Hin).
- exists jF, hF. split; [exact Hj1|]. split; [exact Hj2|]. split; [exact Hj3|]. split; [exact Hj4 | exact HLED'].
Qed.

(* ---- the entry facts at a later state whose view off [sp0 - X, sp0) is the entry's ---- *)
Lemma tv_facts_at : forall memc mdc X,
  ARx ly S Hp W memc mdc -> 0 <= X -> YM05.alloc_ceiling <= sp0 - X ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - X <= a < sp0) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) memc) /\
  prhtx_rec W memc t b0 len0 cap0 f0 /\ prhtx_inv B Lam ly S W memc b0 len0 cap0 txt /\
  prhtx_trace B ly W memc t /\ prh_ledger B ly S Hp W memc Lam peak cnt fail ran most own.
Proof.
intros memc mdc X HARc HX0 HXc KA.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KAlow : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KA; lia).
assert (HRECc : prhtx_rec W memc t b0 len0 cap0 f0)
  by (apply (tv_rec_av W mem memc t b0 len0 cap0 f0); [intros a Ha; apply KA; lia | exact HREC]).
split; [exact (tv_rod_kept W mem memc HROD KAlow)|].
split; [exact HRECc|].
split; [exact (tv_inv_av ly S Hp W mem memc md Lam b0 len0 cap0 txt HAR KAlow HINV)|].
split.
- apply (s10_trace_keep B ly W mem ly W memc t HTRACE eq_refl).
  + intros Hc a Ha Hn. apply KA; lia.
  + intros Hc a Ha. exact (s10_rec_present W memc t b0 len0 cap0 f0 HRECc a Ha).
- apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W memc Lam peak cnt fail ran most own HLED).
  + intros a Ha. pose proof (@pa_segs_low _ _ PA a (S1ImgB.pst_in_img_B a Ha)). apply KAlow. lia.
  + intros a k i Hin Hi. destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k _ _ HLED Hin) as (Hk0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
    change (@cf_head CfParams_preset) with 16 in *.
    assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
    rewrite Hrq in Hc. apply KAlow. lia.
  + intros a k _ H. exact H.
  + apply Permutation_refl.
Qed.

(* ---- the TAIL CALL of tx_put (`j tx_put` with the frame popped: sp, ra and every callee-saved register the entry's)
   through Tx102Glue.v's s10_tail_WbmR at WR (the batch's budgeted tail rule over a world relation; no abort arm), from
   the continuation the run lemmas end in (with the runs' memnorm keep): the text's conclusion when the one call puts
   src at s, which is then the whole of KS / ADD. The entry journal IS a budgeted one at [] (AJ = AJW .. []) at wle,
   which no free has crossed; it is lifted to WR for the rule (ajournal_xwR_mono, wle_wle'), since tx_put's post is at
   WR. tx_put's guarded room, consumer window and budget are the text's own at KS = [n] (the same term); its GROW
   premise comes from the text's guarded run premise (tx_put_ev); its three arms and two position conjuncts are read
   back by tx_put_res, its DEAD is the text's ---- *)
Lemma tv_tail_put : forall E' ss' ms' mdc kj X s src,
  st_ok SEGS E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
  AJ (STKV + dw) (sp0 + dw) FP0 ly S Hp W mem md [] ly S Hp W (ms_mem ms') mdc kj ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_put)) (ms_mem ms') (seg_rom SEGS) ->
  spZ (ms_regs ms') = sp0 -> aregs_preserved regs (ms_regs ms') ->
  getr (ms_regs ms') 1 = getr regs 1 -> getr (ms_regs ms') 3 = getr regs 3 -> getr (ms_regs ms') 4 = getr regs 4 ->
  getr (ms_regs ms') 10 = getr regs 10 -> getr (ms_regs ms') 11 = Z_to_bv 64 s ->
  getr (ms_regs ms') 12 = Z_to_bv 64 (Z.of_nat (length src)) ->
  0 <= X -> YM05.alloc_ceiling <= sp0 - X ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - X <= a < sp0) ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
  src_rd W (ms_mem ms') s src -> prhtx_kept B Lam ly S s (Z.of_nat (length src)) ->
  (forall a, s <= a < s + Z.of_nat (length src) -> ~ (t <= a < t + 28) /\ ~ (b0 <= a < b0 + cap0)) ->
  KS = [Z.of_nat (length src)] -> ADD = src -> TVMN mem (ms_mem ms') ->
  SRW W (mkCfg ms' mdc) QF.
Proof.
intros E' ss' ms' mdc kj X s src HS Hrv HJ Hms Hsp HP R1 R3 R4 R10 R11 R12 HX0 HXc KA HSRC HKEPT HDISJ EKS EADD HMN.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARc.
pose proof tv_stk_facts as (SK0 & SK1 & _).
pose proof (tv_stkv nn) as ESK.
destruct (tv_facts_at (ms_mem ms') mdc X HARc HX0 HXc KA) as (HRODc & HRECc & HINVc & HTRc & HLEDc).
assert (HPLc : prhtx_place ly S W (ms_regs ms') (ms_mem ms') dw t).
{ apply (tv_place_av ly S W regs (ms_regs ms') mem (ms_mem ms') dw t Hsp ltac:(lia) ltac:(lia)).
  - intros a Ha. apply KA; lia.
  - intros a Ha. apply KA; lia.
  - exact HPLACE. }
assert (HFW : fwin ly W (ms_regs ms') (ms_mem ms') dw).
{ pose proof (s10_fwin_call B ARx SK STKV dw sp0 FP0 ly S Hp W mem md [] ly S Hp W (ms_mem ms') mdc kj (ms_regs ms') 0
    HJ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_0_r; exact Hdw16)) as H.
  rewrite Z.sub_0_r in H. exact H. }
assert (Hch' : achain ly (aview SEGS (w_H W) (ms_mem ms')) sp0 (s0Z (ms_regs ms')) ch).
{ unfold s0Z. rewrite (tv_ap regs (ms_regs ms') HP 8%bv); [|unfold acallee_saved;
    match goal with |- context [bv_unsigned ?x] => let w := eval vm_compute in (bv_unsigned x) in
      change (bv_unsigned x) with w end; lia].
  apply (achain_kept ly (aview SEGS (w_H W) mem) _ sp0 (s0Z regs) ch sp0 Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply KA; lia. }
set (n := Z.of_nat (length src)) in *.
assert (HLENc : len0 + n + 1 <= 2 ^ 28) by (rewrite EADD in HLEN; subst n; lia).
assert (HMAXc : 2 * (len0 + n + 1) < cf_malloc_max) by (rewrite EADD in HMAX; subst n; lia).
assert (HEV1 : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 [n])) by (rewrite <- EKS; exact HEVS).
assert (HRW1 : f0 = 0 -> YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 [n])) (st_depot S))
  by (rewrite <- EKS; exact HROOMW).
assert (HCF1 : f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 [n])))
  by (rewrite <- EKS; exact HCONS).
assert (HHIc : spZ (ms_regs ms') + 64 <= ly_stk_hi ly) by (rewrite Hsp; exact HHI).
assert (HRAc : raZ (ms_regs ms') < YM05.alloc_ceiling) by (unfold raZ; rewrite R1; exact HRAC).
assert (HJR : AJWR (STKV + dw) (sp0 + dw) FP0 ly S Hp W mem md [] ly S Hp W (ms_mem ms') mdc kj [])
  by exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx _ _ (wle_wle' SEGS YGcfRehidePost.RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
eapply SRr'_mono.
{ eapply (s10_tail_WbmR B ARx SK LAWS WR (wle'_trans SEGS YGcfRehidePost.RZ_cf) W E' ss' ms' STKV dw sp0 FP0 ly S Hp W
    mem md ly S Hp mdc kj [] (@STK_tx_put prh_img_B) FP0 ch regs (wbudget_if f0 [] (length (prhtx_evs len0 cap0 KS)))
    _ _ _ HS Hrv HJR eq_refl Hsp SK0 ltac:(lia) Hdw0 Hdw16 HP R1 Hra Hra4 ltac:(rewrite R3; exact Hgp)
    ltac:(rewrite R4; exact Htp) Hch').
  - intros HPRE1.
    replace (mkst (ms_regs ms') (Z_to_bv 64 (ss_pc ss')) (ms_mem ms') (seg_rom SEGS))
      with (mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_put)) (ms_mem ms') (seg_rom SEGS))
      by (rewrite <- (st_ok_restrict_mkst SEGS (w_H W) E' ss' ms' HS Hrv); first [exact Hms | symmetry; exact Hms]).
    exact (TXPUT rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W (ms_regs ms') (ms_mem ms') mdc ch dw t s n b0 len0 cap0 f0
      own txt src Lam peak cnt fail ran most
      (conj HPRE1 (conj HRODc (conj HHIc (conj HRAc HFRM)))) HCLO HROOM HPOS HRP4 HRW1 HCF1 ltac:(rewrite R10; exact H10)
      ltac:(rewrite R11; reflexivity) ltac:(rewrite R12; reflexivity) HFW HPLc HTRc HRECc HINVc HSRC eq_refl HKEPT HDISJ
      HLENc HLEDc (fun Hf Hlt => tx_put_ev rp_sm rp_x rp_os rp_i len0 cap0 n f0 HEV1 Hf Hlt) HLIVE HMAXc).
  - intros a Ha. left. exact Ha.
  - intros a Ha Hf. exact Hf.
  - intros a Ha Hn. apply KA; lia.
  - intros WS1 HW1. rewrite EKS. exact HW1.
  - intros ly' S' Hp' W' regs' mem' md' H. exact H.
  - exact HMN. }
cbv beta. intros W2 c2 _ HN. unfold QF.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & WS2 & Hc2 & HPW & HJ2 & HW2 & HP2 &
  ((b1 & cap1 & f1 & ow1 & pre & HPOST & HARMS & HDEAD1 & _ & HRM & HG & HNG & HLED2) & HMN2)).
destruct (tx_put_res rp_sm rp_x rp_os rp_i rp_H0 rp_hist S2 len0 cap0 f0 f1 own ow1 b0 b1 cap1 n src pre _ HARMS HG HNG)
  as (HOUT & jq & h2 & Hjq & HPOS2).
exists ly2, S2, Hp2, regs2, mem2, md2, k2, WS2. split; [exact Hc2|]. split; [exact HPW|]. split; [exact HJ2|].
split; [exact HW2|]. split; [exact HP2|]. split; [|exact HMN2].
apply (tv_qt ly2 S2 Hp2 W2 regs2 mem2 md2 k2 WS2 (ms_regs ms') b1 cap1 f1 ow1 pre HJ2 Hsp HPOST);
  [| exact HDEAD1 | exact HRM | | exact HLED2].
- rewrite EKS, EADD. exact HOUT.
- rewrite EKS. exists jq, h2. split; [exact Hjq | exact HPOS2].
Qed.

(* ---- the TAIL CALL of tx_string (`j tx_string`, the string arm), as tv_tail_put with TXSTR (the entry journal lifted
   to WR; its guarded run premise, room, consumer window and budget are the text's own at KS = the string's pieces;
   its post's outcome, DEAD and position are the text's) ---- *)
Lemma tv_tail_string : forall E' ss' ms' mdc kj X str k bs,
  st_ok SEGS E' ss' (restrict (w_H W) ms') -> ss_resv ss' = None ->
  AJ (STKV + dw) (sp0 + dw) FP0 ly S Hp W mem md [] ly S Hp W (ms_mem ms') mdc kj ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_string)) (ms_mem ms') (seg_rom SEGS) ->
  spZ (ms_regs ms') = sp0 -> aregs_preserved regs (ms_regs ms') ->
  getr (ms_regs ms') 1 = getr regs 1 -> getr (ms_regs ms') 3 = getr regs 3 -> getr (ms_regs ms') 4 = getr regs 4 ->
  getr (ms_regs ms') 10 = getr regs 10 -> getr (ms_regs ms') 11 = Z_to_bv 64 str ->
  0 <= X -> YM05.alloc_ceiling <= sp0 - X ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - X <= a < sp0) ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
  PRH_Reader.pj_cstrR SEGS (rdW W (ms_mem ms')) (prh_lin Lam) str k bs -> prhtx_bvis W (ms_mem ms') str k ->
  KS = TxModel.plen (TxModel.strp bs) -> ADD = WriterSpec.wstr bs -> TVMN mem (ms_mem ms') ->
  SRW W (mkCfg ms' mdc) QF.
Proof.
intros E' ss' ms' mdc kj X str k bs HS Hrv HJ Hms Hsp HP R1 R3 R4 R10 R11 HX0 HXc KA HSTR HBVS EKS EADD HMN.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARc.
pose proof tv_stk_facts as (_ & _ & _ & _ & SK4 & SK5 & _).
pose proof (tv_stkv nn) as ESK.
destruct (tv_facts_at (ms_mem ms') mdc X HARc HX0 HXc KA) as (HRODc & HRECc & HINVc & HTRc & HLEDc).
assert (HPLc : prhtx_place ly S W (ms_regs ms') (ms_mem ms') dw t).
{ apply (tv_place_av ly S W regs (ms_regs ms') mem (ms_mem ms') dw t Hsp ltac:(lia) ltac:(lia)).
  - intros a Ha. apply KA; lia.
  - intros a Ha. apply KA; lia.
  - exact HPLACE. }
assert (HFW : fwin ly W (ms_regs ms') (ms_mem ms') dw).
{ pose proof (s10_fwin_call B ARx SK STKV dw sp0 FP0 ly S Hp W mem md [] ly S Hp W (ms_mem ms') mdc kj (ms_regs ms') 0
    HJ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_0_r; exact Hdw16)) as H.
  rewrite Z.sub_0_r in H. exact H. }
assert (Hch' : achain ly (aview SEGS (w_H W) (ms_mem ms')) sp0 (s0Z (ms_regs ms')) ch).
{ unfold s0Z. rewrite (tv_ap regs (ms_regs ms') HP 8%bv); [|unfold acallee_saved;
    match goal with |- context [bv_unsigned ?x] => let w := eval vm_compute in (bv_unsigned x) in
      change (bv_unsigned x) with w end; lia].
  apply (achain_kept ly (aview SEGS (w_H W) mem) _ sp0 (s0Z regs) ch sp0 Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply KA; lia. }
assert (HLENc : len0 + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= 2 ^ 28) by (rewrite <- EADD; exact HLEN).
assert (HMAXc : 2 * (len0 + Z.of_nat (length (WriterSpec.wstr bs)) + 1) < cf_malloc_max) by (rewrite <- EADD; exact HMAX).
assert (HHIc : spZ (ms_regs ms') + 64 <= ly_stk_hi ly) by (rewrite Hsp; exact HHI).
assert (HRAc : raZ (ms_regs ms') < YM05.alloc_ceiling) by (unfold raZ; rewrite R1; exact HRAC).
assert (HEVS' : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 (TxModel.plen (TxModel.strp bs))))
  by (rewrite <- EKS; exact HEVS).
assert (HRW1 : f0 = 0 -> YCbqGwild.wild_room (as_universe B) []
  (length (prhtx_evs len0 cap0 (TxModel.plen (TxModel.strp bs)))) (st_depot S)) by (rewrite <- EKS; exact HROOMW).
assert (HCF1 : f0 = 0 ->
  prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 (TxModel.plen (TxModel.strp bs)))))
  by (rewrite <- EKS; exact HCONS).
assert (HJR : AJWR (STKV + dw) (sp0 + dw) FP0 ly S Hp W mem md [] ly S Hp W (ms_mem ms') mdc kj [])
  by exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx _ _ (wle_wle' SEGS YGcfRehidePost.RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
eapply SRr'_mono.
{ eapply (s10_tail_WbmR B ARx SK LAWS WR (wle'_trans SEGS YGcfRehidePost.RZ_cf) W E' ss' ms' STKV dw sp0 FP0 ly S Hp W
    mem md ly S Hp mdc kj [] (@STK_tx_string prh_img_B) FP0 ch regs
    (wbudget_if f0 [] (length (prhtx_evs len0 cap0 KS))) _ _ _
    HS Hrv HJR eq_refl Hsp SK4 ltac:(lia) Hdw0 Hdw16 HP R1 Hra Hra4 ltac:(rewrite R3; exact Hgp)
    ltac:(rewrite R4; exact Htp) Hch').
  - intros HPRE1.
    replace (mkst (ms_regs ms') (Z_to_bv 64 (ss_pc ss')) (ms_mem ms') (seg_rom SEGS))
      with (mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_string)) (ms_mem ms') (seg_rom SEGS))
      by (rewrite <- (st_ok_restrict_mkst SEGS (w_H W) E' ss' ms' HS Hrv); first [exact Hms | symmetry; exact Hms]).
    exact (TXSTR rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W (ms_regs ms') (ms_mem ms') mdc ch dw t str k b0 len0
      cap0 f0 own bs txt Lam peak cnt fail ran most
      (conj HPRE1 (conj HRODc (conj HHIc (conj HRAc HFRM)))) HCLO HROOM HPOS HRP4 HRW1 HCF1 ltac:(rewrite R10; exact H10)
      ltac:(rewrite R11; reflexivity)
      HFW HPLc HTRc HRECc HINVc HSTR HBVS HLENc HLEDc HEVS' HLIVE HMAXc HFR0).
  - intros a Ha. left. exact Ha.
  - intros a Ha Hf. exact Hf.
  - intros a Ha Hn. apply KA; lia.
  - intros WS1 HW1. rewrite EKS. exact HW1.
  - intros ly' S' Hp' W' regs' mem' md' H. exact H.
  - exact HMN. }
cbv beta. intros W2 c2 _ HN. unfold QF.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & WS2 & Hc2 & HPW & HJ2 & HW2 & HP2
  & ((b1 & cap1 & f1 & ow1 & pre & HPOST & HOUT & HDEAD1 & _ & _ & HRM & jF & hF & Hj1 & Hj2 & Hj3 & Hj4 & HLED2)
  & HMN2)).
exists ly2, S2, Hp2, regs2, mem2, md2, k2, WS2. split; [exact Hc2|]. split; [exact HPW|]. split; [exact HJ2|].
split; [exact HW2|]. split; [exact HP2|]. split; [|exact HMN2].
apply (tv_qt ly2 S2 Hp2 W2 regs2 mem2 md2 k2 WS2 (ms_regs ms') b1 cap1 f1 ow1 pre HJ2 Hsp HPOST);
  [| exact HDEAD1 | exact HRM | | exact HLED2].
- rewrite EKS, EADD. exact HOUT.
- rewrite EKS. exists jF, hF. split; [exact (conj Hj1 (conj Hj3 Hj4)) | exact Hj2].
Qed.

(* ---- the node's fields and placement from the text's premises ---- *)
Lemma tv_node_facts :
  4096 <= v /\ v mod 8 = 0 /\ v + 56 <= YM05.alloc_ceiling /\ in_app v 56 /\
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a).
Proof.
pose proof HPRE as (HAR & _).
destruct (tv_node_home ly S Hp W mem md Lam peak cnt fail ran most own v HAR HLED HHOME) as (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [exact tv_v8|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.
(* the literal sources: kept_img and the ROM bytes give src_rd and prhtx_kept at any state of the run *)
Lemma tv_lit_src : forall memc mdc lo src,
  ARx ly S Hp W memc mdc -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) memc) ->
  In (lo, Z.of_nat (length src)) [(69472, 4); (69504, 5); (69536, 4); (70144, 1); (70176, 1); (70208, 1); (70240, 1);
    (70272, 1); (70304, 1); (70336, 1)] -> (0 < length src)%nat ->
  (forall j, (j < length src)%nat -> option_map (fun bb : byte => bv_unsigned bb)
     (seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + lo + Z.of_nat j))) = Some (nth j src 0)) ->
  src_rd W memc (VAL (A_OBJ 2) + lo) src /\ prhtx_kept B Lam ly S (VAL (A_OBJ 2) + lo) (Z.of_nat (length src)) /\
  (forall a, VAL (A_OBJ 2) + lo <= a < VAL (A_OBJ 2) + lo + Z.of_nat (length src) ->
     ~ (t <= a < t + 28) /\ ~ (b0 <= a < b0 + cap0)).
Proof.
intros memc mdc lo src HARc HRODc Hin Hn Hrom.
pose proof (proj1 (Forall_forall _ _) tv_lit_img _ Hin) as Hki. cbn [fst snd] in Hki.
destruct (s10_src_img B ARx LAWS zs_aligned img_shadow_vis_x BTxLine.tl_img_box tv_img_cf_box ly S Hp W memc mdc Lam _
  src HARc HRODc Hki Hn Hrom)
  as [HSRC HKEPT].
split; [exact HSRC|]. split; [exact HKEPT|].
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof HPLACE as (_ & Htlo & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof BTxLine.tl_img_box as (Hib1 & Hib2).
intros a Ha. destruct Hki as (Hlo & Hhi & Hro).
split; [lia|]. intros Hb.
destruct HINV as (_ & [(Hz & _) | (Hc & _ & Hinb & _)]); [lia|].
apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b0 cap0 a HAR Hinb).
- unfold req_size. destruct (Z.eqb_spec cap0 0); lia.
- destruct (Hro a Ha) as (Hr & _).
  destruct Hr as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* ---- ARMS tag 0 / 1 / 2: the literal, tail-called into tx_put (the leaf run at SRr through tv_srr_then) ---- *)
Lemma tv_main_lit : forall ty ao ent lo ln src str kids keys n, tv_lit_case_B ty ao ent lo ln ->
  val_mem SEGS (rdW W mem) v 4 ty ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 40) 8 n ->
  Z.of_nat (length src) = ln -> KS = [ln] -> ADD = src ->
  (forall j, (j < length src)%nat -> option_map (fun bb : byte => bv_unsigned bb)
     (seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + lo + Z.of_nat j))) = Some (nth j src 0)) ->
  SRW W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) QF.
Proof.
intros ty ao ent lo ln src str kids keys n Hcase Vty Hs0 Vs Hk0 Vk Hy0 Vy Hn0 Vn Hln EKS EADD Hrom.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
assert (Hin : In (lo, Z.of_nat (length src)) [(69472, 4); (69504, 5); (69536, 4); (70144, 1); (70176, 1); (70208, 1);
    (70240, 1); (70272, 1); (70304, 1); (70336, 1)]).
{ rewrite Hln. destruct Hcase as [Hc|[Hc|Hc]]; injection Hc as _ _ _ <- <-; cbn; tauto. }
apply tv_srr_then.
apply (tv_run_lit_B ty ao ent lo ln STKV dw ly S Hp W regs mem md ch v str kids keys n FP0 _ Hcase HPRE
  ltac:(unfold TV_FRAME_B; lia) HFWIN H11 Hv0 Hv8 Hvc Hvapp Hvimg Vty Hs0 Vs Hk0 Vk Hy0 Vy Hn0 Vn HRA HROD).
intros E' ss' ms' mdc kj HS' Hrv HJ' Hms Hsp HP R1 R3 R4 R10 R11 R12 KA HMN.
apply tv_srr_now.
destruct (tv_facts_at (ms_mem ms') mdc 192 (proj1 HJ') ltac:(lia) ltac:(lia) KA) as (HRODc & _).
assert (Hlen0 : (0 < length src)%nat) by (destruct Hcase as [Hc|[Hc|Hc]]; injection Hc as _ _ _ _ E; lia).
destruct (tv_lit_src (ms_mem ms') mdc lo src (proj1 HJ') HRODc Hin Hlen0 Hrom) as (HSRC & HKEPT & HDISJ).
apply (tv_tail_put E' ss' ms' mdc kj 192 _ src HS' Hrv HJ' Hms Hsp HP R1 R3 R4 R10 R11
  ltac:(rewrite R12, Hln; reflexivity) ltac:(lia) ltac:(lia) KA HSRC HKEPT HDISJ ltac:(rewrite EKS, Hln; reflexivity) EADD
  HMN).
Qed.

(* a byte of the buffer block is in the text's footprint *)
Lemma tv_buf_inFP : forall t0 b cap a, cap <> 0 -> b <= a < b + cap -> inFP (prhtx_fp t0 b cap) a.
Proof.
intros t0 b cap a Hc Ha. exists (b, b + req_size cap). split.
- unfold prhtx_fp. right. destruct (Z.eqb_spec cap 0) as [E|E]; [lia|]. cbn [ablocks_fp map]. left. reflexivity.
- unfold in_zr. cbn [fst snd]. unfold req_size. destruct (Z.eqb_spec cap 0); lia.
Qed.
Lemma tv_garr8_prefix : forall (m : word -> option byte) a l1 l2, garr8 SEGS m a (l1 ++ l2) -> garr8 SEGS m a l1.
Proof.
intros m a l1 l2 H j Hj. specialize (H j ltac:(rewrite length_app; lia)). rewrite app_nth1 in H by exact Hj. exact H.
Qed.
(* a harness string of a Lam block apart from the record and the buffer (the record is on the stack, the buffer's base
   is no harness block's) *)
Lemma tv_lam_apart : forall x k a, In (x, k) Lam -> x <= a < x + k ->
  ~ (t <= a < t + 28) /\ ~ (b0 <= a < b0 + cap0).
Proof.
intros x k a Hin Ha.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof HPLACE as (_ & Htlo & _).
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran x k _ _ HLED Hin) as (Hk0 & Hab & _).
change (@cf_head CfParams_preset) with 16 in Hab.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hrq in Hc.
assert (Hnf : ~ inFP (prhtx_fp t b0 cap0) a).
{ apply (tv_not_fp ly S Hp W mem md Lam peak cnt fail ran most own t b0 cap0 len0 txt a HAR HLED HINV); [|lia].
  left. exists x, k. split; [exact Hin | lia]. }
split; [lia|]. intros Hb. destruct (Z.eq_dec cap0 0) as [E|E]; [lia|].
exact (Hnf (tv_buf_inFP t b0 cap0 a E Hb)).
Qed.

(* ---- ARM tag 3 (JNum): strlen, then tail-called into tx_put with the number's text ---- *)
Lemma tv_main_num : forall str kids keys n txt' k,
  val_mem SEGS (rdW W mem) v 4 3 ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 40) 8 n ->
  Forall (fun c => 0 < c < 256) txt' -> garr8 SEGS (rdW W mem) str (txt' ++ [0]) ->
  In (str, k) Lam -> Z.of_nat (length txt') + 1 <= k -> prhtx_bvis W mem str k ->
  KS = [Z.of_nat (length txt')] -> ADD = txt' ->
  SRW W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) QF.
Proof.
intros str kids keys n txt' k Vty Hs0 Vs Hk0 Vk Hy0 Vy Hn0 Vn Hnz Hg Hin Hk Hbv EKS EADD.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof tv_stk_facts as (SK0 & SK1 & _ & _ & _ & _ & SK6). pose proof (tv_stkv nn) as ESK.
pose proof asan_consts as (C1 & _).
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
assert (Hlen0 : 0 <= len0) by (destruct HINV as (Hl & _); lia).
assert (Hl32 : Z.of_nat (length txt') + 1 < 2 ^ 32) by (rewrite EADD in HLEN; lia).
assert (HSRC0 : src_rd W mem str txt').
{ pose proof Hbv as (H4096 & H8 & Hk0' & Hc & Hamr & HRAs & Hhull & _).
  split; [unfold bytes_at; exact (tv_garr8_prefix _ _ _ _ Hg)|]. split; [lia|]. split; [lia|].
  split; [unfold amem_range in *; lia|]. split.
  - apply (range_addressable_sub _ SHADOW_OFF str k); [exact HRAs | lia | lia].
  - intros Hn. apply (tv_hull_sub _ str _ k); [lia | lia | apply Hhull; lia]. }
apply tv_srr_then.
apply (tv_run_num_B STKV dw ly S Hp W regs mem md ch v str kids keys n FP0 txt' k Lam peak cnt fail ran most own _ HPRE
  ltac:(unfold TV_FRAME_B; lia) HFWIN H11 Hv0 Hv8 Hvc Hvapp Hvimg Vty Hs0 Vs Hk0 Vk Hy0 Vy Hn0 Vn HRA HROD
  Hnz Hg Hin Hk Hbv HLED Hl32).
intros E' ss' ms' mdc kj HS' Hrv HJ' Hms Hsp HP R1 R3 R4 R10 R11 R12 KA HMN.
apply tv_srr_now.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (KA' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - (192 + 2 * ESTACK) <= a < sp0) ->
  aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) by (intros a Ha Hn; apply KA; lia).
apply (tv_tail_put E' ss' ms' mdc kj (192 + 2 * ESTACK) str txt' HS' Hrv HJ' Hms Hsp HP R1 R3 R4 R10 R11 R12
  ltac:(lia) ltac:(lia) KA').
- apply (tv_srcrd_av W mem (ms_mem ms') str txt'); [|exact HSRC0]. intros a Ha. apply KA'; lia.
- left. left. exists str, k. split; [exact Hin | lia].
- intros a Ha. apply (tv_lam_apart str k a Hin). lia.
- exact EKS.
- exact EADD.
- exact HMN.
Qed.

(* ---- ARM tag 4 (JStr): tail-called into tx_string with the string ---- *)
Lemma tv_main_str : forall str kids keys n s k,
  val_mem SEGS (rdW W mem) v 4 4 ->
  0 <= str < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW W mem) (v + 40) 8 n ->
  PRH_Reader.pj_cstrR SEGS (rdW W mem) (prh_lin Lam) str k s -> prhtx_bvis W mem str k ->
  KS = TxModel.plen (TxModel.strp s) -> ADD = WriterSpec.wstr s ->
  SRW W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) QF.
Proof.
intros str kids keys n s k Vty Hs0 Vs Hk0 Vk Hy0 Vy Hn0 Vn HSTR Hbv EKS EADD.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof asan_consts as (C1 & _).
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
apply tv_srr_then.
apply (tv_run_str_B STKV dw ly S Hp W regs mem md ch v str kids keys n FP0 _ HPRE
  ltac:(unfold TV_FRAME_B; lia) HFWIN H11 Hv0 Hv8 Hvc Hvapp Hvimg Vty Hs0 Vs Hk0 Vk Hy0 Vy Hn0 Vn HRA HROD).
intros E' ss' ms' mdc kj HS' Hrv HJ' Hms Hsp HP R1 R3 R4 R10 R11 KA HMN.
apply tv_srr_now.
destruct (tv_facts_at (ms_mem ms') mdc 192 (proj1 HJ') ltac:(lia) ltac:(lia) KA) as (_ & _ & _ & _ & HLEDc).
pose proof Hbv as (H4096 & _ & _ & Hc & _).
apply (tv_tail_string E' ss' ms' mdc kj 192 str k s HS' Hrv HJ' Hms Hsp HP R1 R3 R4 R10 R11 ltac:(lia) ltac:(lia) KA).
- apply (PRH_Reader.pj_cstrR_frame SEGS (rdW W mem) (rdW W (ms_mem ms')) (prh_lin Lam) str k s HSTR).
  intros x Hx. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem (ms_mem ms') x). apply KA; lia.
- destruct HSTR as (Hin & _).
  exact (s10_bvis_lam B ARx LAWS ly S Hp W (ms_mem ms') mdc Lam peak cnt fail ran most own W mem str k (proj1 HJ') HLEDc Hin Hbv).
- exact EKS.
- exact EADD.
- exact HMN.
Qed.

(* ==== THE OPEN ARM'S MACHINERY at image B (B twin of S10TxValue.v 7623a0781f8: tv_saved / tv_spill at B's frame
   layout, tv_frame_keep, tv_live, tv_home_keep, tv_live_after, tv_cf, tv_call_core at o = -192, tv_kont, tv_callregs,
   tv_put_call / tv_line_call / tv_str_call / tv_val_call). B's frame is 192 bytes and its loop spills sit at other
   offsets than A's (tv_spill); everything else is A's text with B's constants ==== *)
(* ==== THE OPEN ARM: the facts a state carries between its segments ==== *)
(* the prologue's saves (ra, s0, s1, s2-s11 at sp0 - 8 .. sp0 - 104) and the three words tx_value stores before its
   first call at B: 72(sp) the shadow base (sp0 - 120), 16(sp) the UBSan `andi a0,a1,7` result 0 (sp0 - 176), 24(sp)
   the depth (sp0 - 168) *)
Definition TV_SAVED : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition tv_saved (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  (forall j, (j < 13)%nat -> val_mem SEGS (rdW Wc memc) (sp0 - 8 * (Z.of_nat j + 1)) 8
     (bv_unsigned (getr regs (nth j TV_SAVED 0%bv)))) /\
  val_mem SEGS (rdW Wc memc) (sp0 - 120) 8 SHADOW_OFF /\
  val_mem SEGS (rdW Wc memc) (sp0 - 176) 8 0 /\ val_mem SEGS (rdW Wc memc) (sp0 - 168) 8 d.
(* the loop's spills at B (0x8551c, 0x85554 .. 0x85598): 8(sp) 3 (sp0 - 184), 32(sp) .str.24 ' ' (sp0 - 160), 40(sp)
   .str.23 ':' (sp0 - 152), 48(sp) the shadow of &keys (sp0 - 144), 56(sp) &keys = v + 32 (sp0 - 136), 64(sp) .str.22 ','
   (sp0 - 128), 80(sp) the shadow of &n (sp0 - 112) *)
Definition tv_spill (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  val_mem SEGS (rdW Wc memc) (sp0 - 184) 8 3 /\
  val_mem SEGS (rdW Wc memc) (sp0 - 160) 8 (VAL (A_OBJ 2) + 70272) /\
  val_mem SEGS (rdW Wc memc) (sp0 - 152) 8 (VAL (A_OBJ 2) + 70240) /\
  val_mem SEGS (rdW Wc memc) (sp0 - 144) 8 (shadow_addr (v + 32)) /\
  val_mem SEGS (rdW Wc memc) (sp0 - 136) 8 (v + 32) /\
  val_mem SEGS (rdW Wc memc) (sp0 - 128) 8 (VAL (A_OBJ 2) + 70208) /\
  val_mem SEGS (rdW Wc memc) (sp0 - 112) 8 (shadow_addr (v + 40)).
Lemma tv_frame_keep : forall (Wc Wc' : world SEGS) memc memc',
  (forall a, sp0 - 192 <= a < sp0 -> aview SEGS (w_H Wc') memc' a = aview SEGS (w_H Wc) memc a) ->
  (tv_saved Wc memc -> tv_saved Wc' memc') /\ (tv_spill Wc memc -> tv_spill Wc' memc').
Proof.
intros Wc Wc' memc memc' K. split.
- intros (HS & H72 & H16 & H24). split; [|split; [|split]].
  + intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc') memc memc' _ 8 _); [|exact (HS j Hj)].
    intros i Hi. apply K. lia.
  + apply (ts_vm_av (w_H Wc) (w_H Wc') memc memc' _ 8 _); [|exact H72]. intros i Hi. apply K. lia.
  + apply (ts_vm_av (w_H Wc) (w_H Wc') memc memc' _ 8 _); [|exact H16]. intros i Hi. apply K. lia.
  + apply (ts_vm_av (w_H Wc) (w_H Wc') memc memc' _ 8 _); [|exact H24]. intros i Hi. apply K. lia.
- intros (V1 & V2 & V3 & V4 & V5 & V6 & V7).
  repeat split; (apply (ts_vm_av (w_H Wc) (w_H Wc') memc memc' _ 8 _); [|eassumption]); intros i Hi; apply K; lia.
Qed.

(* THE TEXT STATE of the open arm after the pieces P (#102): Tx102Glue.v's tx_state at the buffer b of capacity cap,
   failed fc, own ow, with pre ACTUALLY appended (a refused put stops the appending; the outcome is tx_state's
   prhtx_out); its position tx_pos (the text's own position clause over the calls so far); the memnorm keep from the
   entry memory; DEAD so far; and the depot's wild growth since the entry, within a budget of at most the events of
   P (the batch). The old pin's s10_txstate_e had the first three parts in the event form *)
Definition tv_tx (b cap fc ow : Z) (P : list (list Z)) (pre : list Z) (lyc : alayout) (Sc : astate) (Hpc : list Z)
  (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  tx_state (PI := prh_img_B) (PA := PA) B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own
    b cap fc ow (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc memc /\
  tx_pos rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 fc (TxModel.plen P) Sc /\
  TVMN mem memc /\
  (f0 = 0 -> fc = 0) /\
  exists WS, incl (wild_part (as_universe B) (st_depot Sc)) (wild_part (as_universe B) (st_depot S) ++ WS) /\
    wbudget_if f0 [] (length (prhtx_evs len0 cap0 (TxModel.plen P))) WS.
(* THE LIVE STATE of the open arm: the journal from the entry REBASED to the current depot (YCbqGwild.ajournal_xw_rebase:
   no depot conjunct in the cut journal; the batch), the caller window kept outside FP0, the text state after the pieces
   P (tv_tx, at some capacity, failed, own and appended text), the read-only view, the tree's footprint as at the entry,
   the node's shadow, the blocks' shadow facts, the saves. It is used at cuts on BOTH sides of a free (the opening
   call's state, at wle; every later cut, at WR), so it is ONE definition over the journal's world relation R
   (YCbqG.v ajournal_xR); tv_live is its instance at wle *)
Definition tv_liveR (R : world SEGS -> world SEGS -> Prop) (lyc : alayout) (Sc : astate) (Hpc : list Z)
  (Wc : world SEGS) (memc : word -> option byte) (mdc : Model) (kj b : Z) (P : list (list Z)) : Prop :=
  ajournal_xR (SK := SK) SEGS B (prh_pst (PI := prh_img_B)) ARx R (STKV + dw) (sp0 + dw) FP0 ly
    (set_depot (st_depot Sc) S) Hp W mem md [] lyc Sc Hpc Wc memc mdc kj /\
  (forall a, sp0 <= a < sp0 + dw -> ~ inFP FP0 a -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H W) mem a) /\
  (exists cap fc ow pre, tv_tx b cap fc ow P pre lyc Sc Hpc Wc memc) /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) /\
  (forall x, PRH_Reader.pj_footR v D x -> aview SEGS (w_H Wc) memc x = aview SEGS (w_H W) mem x) /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56 /\
  Forall (fun bk => prhtx_bvis Wc memc (fst bk) (snd bk)) D /\
  tv_saved Wc memc.
Definition tv_live : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Z -> Z ->
  list (list Z) -> Prop := tv_liveR (@wle SEGS).
Lemma tv_live_R_wle : forall lyc Sc Hpc Wc memc mdc kj b P,
  tv_live lyc Sc Hpc Wc memc mdc kj b P = tv_liveR (@wle SEGS) lyc Sc Hpc Wc memc mdc kj b P.
Proof. reflexivity. Qed.
(* a live state at wle is one at WR (only the journal's world conjunct reads R) *)
Lemma tv_liveR_mono : forall lyc Sc Hpc Wc memc mdc kj b P,
  tv_live lyc Sc Hpc Wc memc mdc kj b P -> tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P.
Proof.
intros lyc Sc Hpc Wc memc mdc kj b P (HJ & HL).
split; [|exact HL].
exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx _ _ (wle_wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* the node's home across a journal that owns no frame (any world relation R) *)
Lemma tv_home_keep : forall (R : world SEGS -> world SEGS -> Prop) STK spx FP ly1 S1 Hp1 (W1 : world SEGS) mem1 md1 ly2
  S2 Hp2 W2 mem2 md2 k Lam' x,
  ajournal_xR (SK := SK) SEGS B (prh_pst (PI := prh_img_B)) ARx R STK spx FP ly1 S1 Hp1 W1 mem1 md1 []
    ly2 S2 Hp2 W2 mem2 md2 k ->
  prhtx_home Lam' ly1 S1 x 56 -> prhtx_home Lam' ly2 S2 x 56.
Proof.
intros R STK spx FP ly1 S1 Hp1 W1 mem1 md1 ly2 S2 Hp2 W2 mem2 md2 k Lam' x HJ [Hb | (cid & pos & Hin & Hfr)];
  [left; exact Hb|].
pose proof (ajxR_ly HJ) as HLY. pose proof (ajxR_frs HJ) as HFR. pose proof HLY as (_ & _ & _ & _ & _ & EFF & _).
right. exists cid, pos. split; [rewrite HFR; exact Hin|].
intros a Ha. specialize (Hfr a Ha). unfold frame_rng, frame_addr in *. cbn [fst snd] in *. rewrite EFF. exact Hfr.
Qed.

(* ---- a callee's post folded into the live state (the rule's journal at the caller budget WS0 ++ WS1, the callee's
   journal at its budget WS1 and window clause, the record's prhtx_post at the call's registers and window dw + 192, the
   callee's outcome, DEAD, budget and position, its memnorm keep; Tx102Glue.v tx_state_fold_wR / tx_pos_fold /
   tx_budget_fold at the text state the call was made from, whose DEAD and budget WS0 are given): the next pieces Q;
   the live journal leaves REBASED at the callee's end depot (YCbqGwild.ajournal_xw_rebaseR). Both journals and both
   live states are at WR: the callee's run reaches tx_put's realloc ---- *)
Lemma tv_live_after : forall lyc Sc Hpc Wc memc mdc kj b cap fc ow P pre j Q ly2 S2 Hp2 W2 mem2 md2 k1
    b2 cap2 f2 ow2 pre2 jq h2 regsc STK1 WS0 WS1,
  tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P ->
  tx_state (PI := prh_img_B) (PA := PA) B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own
    b cap fc ow (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc memc ->
  tx_jok len0 cap0 f0 fc (TxModel.plen P) j ->
  (f0 = 0 -> fc = 0) -> wbudget_if f0 [] (length (prhtx_evs len0 cap0 (TxModel.plen P))) WS0 ->
  spZ regsc = sp0 - 192 -> 0 <= STK1 ->
  AJWR (STKV + dw) (sp0 + dw) FP0 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) (WS0 ++ WS1) ->
  AJWR (STK1 + (dw + 192)) (sp0 + dw) (prhtx_fp t b cap) lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, sp0 - 192 <= a < sp0 + dw -> ~ inFP (prhtx_fp t b cap) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
  prhtx_post (PA := PA) B Lam regsc (dw + 192) lyc Sc Hpc ly2 S2 Hp2 W2 mem2 t b cap b2
    (len0 + Z.of_nat (length pre) + Z.of_nat (length pre2)) cap2 f2 ((txt ++ pre) ++ pre2) ->
  prhtx_out fc f2 ow ow2 b cap b2 cap2
    (TxModel.tx_capf (len0 + Z.of_nat (length pre)) cap (TxModel.plen Q)) (concat Q) pre2 ->
  (fc = 0 -> f2 = 0) ->
  wbudget_if fc [] (length (prhtx_evs (len0 + Z.of_nat (length pre)) cap (TxModel.plen Q))) WS1 ->
  room_live_cf S2 -> prh_ledger (PI := prh_img_B) (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam peak cnt fail ran most ow2 ->
  tx_jok (len0 + Z.of_nat (length pre)) cap fc f2 (TxModel.plen Q) jq ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j + jq)%nat rp_H0 h2 S2 ->
  TVMN memc mem2 ->
  tv_liveR WR ly2 S2 Hp2 W2 mem2 md2 (kj + k1) b2 (P ++ Q) /\
  (forall a, sp0 - 192 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
Proof.
intros lyc Sc Hpc Wc memc mdc kj b cap fc ow P pre j Q ly2 S2 Hp2 W2 mem2 md2 k1 b2 cap2 f2 ow2 pre2 jq h2 regsc STK1
  WS0 WS1 (HJ & HWIN & (cx & fcx & owx & prx & (_ & _ & HMN & _)) & HRO & HFK & HRAc & HBVc & HSV) HTX0 Hj HDEAD HWB
  Hspc HSTK1 HJ2 HJ1 HW1 HPOST HOUT HDEAD2 HWB1 HRM2 HLED2 Hjq HPOS2 HMN2.
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & Hdpres).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
pose proof (ajxR_ar HJ) as HARc.
pose proof (ajxR_ar HJ1) as HAR2.
pose proof HTX0 as (Ht0 & Ht47 & Hks & (Hrec & Hinv & Hpl & HHp & Hgr & Hbb) & HO & Htr & Hroom & Hled).
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
(* the frame below sp0 is not the callee's footprint: the record is above sp0, the buffer below alloc_ceiling *)
assert (Kst : forall a, sp0 - 192 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply HW1; [lia|]. intros Hf. destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)]; [lia|].
  destruct Hinv as (_ & [(Hz & _) | (_ & _ & _ & _ & _ & Hceil' & _)]); [lia|].
  unfold req_size in Hb. destruct (Z.eqb_spec cap 0); lia. }
assert (HHc : prhtx_home Lam lyc Sc v 56)
  by exact (tv_home_keep _ _ _ _ ly _ Hp W mem md lyc Sc Hpc Wc memc mdc kj Lam v HJ HHOME).
assert (HFKc : forall x, PRH_Reader.pj_footR v D x -> aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x).
{ apply (tv_foot_journal _ _ _ lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 Lam peak cnt fail ran most ow t b
    cap (len0 + Z.of_nat (length pre)) (txt ++ pre) v D HJ1 HARc Hled Hinv HHc HDLAM).
  intros x Hx. destruct (tv_foot_low lyc Sc Hpc Wc memc mdc Lam peak cnt fail ran most ow v D x HARc Hled HHc HDLAM Hx). lia. }
split; [|exact Kst].
split; [exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx _ _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJ2)|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
- intros a Ha Hn0. rewrite (HW1 a ltac:(lia)); [exact (HWIN a Ha Hn0)|].
  intros Hf. apply Hn0. exact (tx_state_fp_win B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own
    b cap fc ow (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc memc HTX0 a ltac:(lia) Hf).
- exists cap2, f2, ow2, (pre ++ pre2). unfold tv_tx. rewrite tv_plen_app, concat_app.
  split; [|split; [|split; [|split]]].
  + apply (tx_state_fold_wR B ARx SK WR Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b cap fc ow
      (TxModel.plen P) (concat P) pre (TxModel.plen Q) (concat Q) b2 cap2 f2 ow2 pre2 lyc Sc Hpc Wc memc mdc
      ly2 S2 Hp2 W2 mem2 md2 regsc (dw + 192) STK1 k1 WS1 HTX0 HARc).
    * apply TxModel.zsum_plen.
    * lia.
    * exact HSTK1.
    * rewrite Hspc. replace (sp0 - 192 + (dw + 192)) with (sp0 + dw) by lia. exact HJ1.
    * intros a Ha Hn0. apply HW1; [rewrite Hspc in Ha; lia | exact Hn0].
    * exact HPOST.
    * exact HOUT.
    * exact HRM2.
    * exact HLED2.
  + exact (tx_pos_fold rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 fc f2 own ow ow2 b0 b b2 cap cap2 j jq h2 S2
      (TxModel.plen P) (TxModel.plen Q) (concat P) (concat Q) pre pre2 Hks HO Hj HOUT Hjq HPOS2).
  + exact (TVMN_trans mem memc mem2 HMN HMN2).
  + intros Hf0. exact (HDEAD2 (HDEAD Hf0)).
  + exists (WS0 ++ WS1). split; [exact (ajxR_wild HJ2)|].
    exact (tx_budget_fold len0 cap0 f0 fc own ow b0 b cap (TxModel.plen P) (concat P) pre (TxModel.plen Q) WS0 WS1
      HO Hks HDEAD HWB HWB1).
- exact (s10_rod_keptR B ARx SK S1ImgB.pst_not_ro_B WR (STK1 + (dw + 192)) (sp0 + dw) (prhtx_fp t b cap)
    lyc _ Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1
    (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B PST ARx _ _ _ _ _ _ Hpc _ _ _ _ _ _ _ _ _ _ _ _ HJ1)
    (s10_fp_closed B Lam lyc Sc Wc memc t b (len0 + Z.of_nat (length pre)) cap (txt ++ pre) ltac:(lia) Hinv) HRO).
- intros x Hx. rewrite (HFKc x Hx). exact (HFK x Hx).
- exact (tv_node_ra_end _ _ _ lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 Lam peak cnt fail ran most ow ow2 t
    b cap (len0 + Z.of_nat (length pre)) (txt ++ pre) v HJ1 HARc Hled HLED2 Hinv ltac:(lia) HHc tv_v8 HRAc).
- rewrite Forall_forall. intros [x kx] Hin. cbn [fst snd].
  apply (s10_bvis_lam B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 Lam peak cnt fail ran most ow2 Wc memc x kx HAR2 HLED2 (HDLAM _ Hin)).
  exact (proj1 (Forall_forall _ _) HBVc _ Hin).
- exact (proj1 (tv_frame_keep Wc W2 memc mem2 Kst) HSV).
Qed.

(* ---- the facts every callee text asks at a call made from the open arm (sp = sp0 - 192, window dw + 192), at the live
   state's buffer b of capacity cap, failed fc, own ow and appended text pre (no longer than concat P) ---- *)
Definition tv_cf (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS) (memc : word -> option byte)
  (regsc : bvmap 5 word) (b cap fc ow : Z) (P : list (list Z)) (pre : list Z) : Prop :=
  fwin lyc Wc regsc memc (dw + 192) /\ prhtx_place lyc Sc Wc regsc memc (dw + 192) t /\
  prhtx_trace (PI := prh_img_B) (PA := PA) B lyc Wc memc t /\
  prhtx_rec Wc memc t b (len0 + Z.of_nat (length pre)) cap fc /\
  prhtx_inv B Lam lyc Sc Wc memc b (len0 + Z.of_nat (length pre)) cap (txt ++ pre) /\
  prh_ledger (PI := prh_img_B) (PA := PA) B lyc Sc Hpc Wc memc Lam peak cnt fail ran most ow /\ room_live_cf Sc /\
  blocks_bytes Sc - cap + LIVE_tx <= LIVE_MAX /\
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) /\ spZ regsc + 64 <= ly_stk_hi lyc /\
  raZ regsc < YM05.alloc_ceiling /\
  count_cid 0 (frames Sc) < fs_frames 0 /\ Hpc = Hp /\ (length pre <= length (concat P))%nat /\
  (forall x, PRH_Reader.pj_footR v D x -> aview SEGS (w_H Wc) memc x = aview SEGS (w_H W) mem x) /\
  Forall (fun bk => prhtx_bvis Wc memc (fst bk) (snd bk)) D /\ prhtx_home Lam lyc Sc v 56.

(* the text's guarded run premise (HEVS) split at a call: the events of the pieces before, of the call's, and of the
   rest, when the text was entered with failed = 0 *)
Lemma tv_evs_split : forall P Q R, P ++ Q ++ R = TxModel.tvp tv PP d ->
  f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 (TxModel.plen P ++ TxModel.plen Q ++ TxModel.plen R)).
Proof. intros P Q R E Hf. rewrite <- (tv_plen_app Q R), <- (tv_plen_app P (Q ++ R)), E. exact (HEVS Hf). Qed.
(* the batch's guarded room (HROOMW) and guarded consumer window (HCONS) split at a call the same way *)
Lemma tv_roomw_split : forall P Q R, P ++ Q ++ R = TxModel.tvp tv PP d ->
  f0 = 0 -> YCbqGwild.wild_room (as_universe B) []
    (length (prhtx_evs len0 cap0 (TxModel.plen P ++ TxModel.plen Q ++ TxModel.plen R))) (st_depot S).
Proof. intros P Q R E Hf. rewrite <- (tv_plen_app Q R), <- (tv_plen_app P (Q ++ R)), E. exact (HROOMW Hf). Qed.
Lemma tv_cons_split : forall P Q R, P ++ Q ++ R = TxModel.tvp tv PP d ->
  f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhtx_evs len0 cap0 (TxModel.plen P ++ TxModel.plen Q ++ TxModel.plen R))).
Proof. intros P Q R E Hf. rewrite <- (tv_plen_app Q R), <- (tv_plen_app P (Q ++ R)), E. exact (HCONS Hf). Qed.
(* a prefix of the text's pieces appends at most ADD *)
Lemma tv_pfx_len : forall P Q, (exists R, P ++ Q ++ R = TxModel.tvp tv PP d) ->
  Z.of_nat (length (concat P)) + Z.of_nat (length (concat Q)) <= Z.of_nat (length ADD).
Proof. intros P Q (R & E). rewrite <- s10v_tvp_wv, <- E, !concat_app, !length_app. lia. Qed.

(* ---- THE CALL of a tx_* text from the open arm (Tx102Glue.v s10_call_WbmR at WR and o = -192, the batch's budgeted
   call rule over a world relation; no abort arm): the callee's premises tv_cf at the live state's text state, its
   entry position rp_i + j (the live state's tx_pos), its guarded run window (tx_window), guarded room
   (tx_room_window) and guarded consumer window (tx_cons_window), each cut out of the text's own by the prefix
   P ++ Q ++ R on the DONE path; the live journal is unbased at tv_tx's budget WS0 for the call
   (YCbqGwild.ajournal_xw_unbase0R); the callee's post (at WR: every callee reaches tx_put's realloc), read back by the
   call lemma as the record's prhtx_post after the pieces Q, the callee's outcome prhtx_out, DEAD and its position,
   at its budget claim, folded into the live state after P ++ Q by tv_live_after. The live state is at WR; the opening
   call's (at wle) is lifted by tv_liveR_mono ---- *)
Lemma tv_call_core : forall Wc E ss ms mdc lyc Sc Hpc kj b P Q STK1,
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> bv_unsigned (ew E 2) = sp0 ->
  tv_liveR WR lyc Sc Hpc Wc (ms_mem ms) mdc kj b P ->
  getr (ms_regs ms) 2 = w64 (sp0 - 192) -> getr (ms_regs ms) 3 = getr regs 3 -> getr (ms_regs ms) 4 = getr regs 4 ->
  getr (ms_regs ms) 8 = w64 t -> YK0s.ret_ok (getr (ms_regs ms) 1) -> 4096 <= raZ (ms_regs ms) ->
  raZ (ms_regs ms) < YM05.alloc_ceiling ->
  0 <= STK1 -> STK1 + 192 <= STKV ->
  (exists R, P ++ Q ++ R = TxModel.tvp tv PP d) ->
  (forall cap fc ow pre j histc ch1, tv_cf lyc Sc Hpc Wc (ms_mem ms) (ms_regs ms) b cap fc ow P pre ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc Sc ->
     (fc = 0 -> YCbqGwild.wild_room (as_universe B) []
        (length (prhtx_evs (len0 + Z.of_nat (length pre)) cap (TxModel.plen Q))) (st_depot Sc)) ->
     (fc = 0 -> prh_cons_from rp_sm rp_x rp_os (rp_i + j)%nat
        (length (prhtx_evs (len0 + Z.of_nat (length pre)) cap (TxModel.plen Q)))) ->
     (fc = 0 -> prh_run_at rp_sm rp_x rp_os (rp_i + j)%nat
        (prhtx_evs (len0 + Z.of_nat (length pre)) cap (TxModel.plen Q))) ->
     afn_pre_x SEGS B ARx STK1 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 ->
     SRW Wc (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom SEGS)) mdc)
       (fpostWbmR (PI := prh_img_B) (PA := PA) B ARx SK WR
          (wbudget_if fc [] (length (prhtx_evs (len0 + Z.of_nat (length pre)) cap (TxModel.plen Q))))
          STK1 (dw + 192) (prhtx_fp t b cap) (ms_regs ms) lyc Sc Hpc Wc (ms_mem ms) mdc
          (fun ly2 S2 Hp2 W2 regs2 mem2 md2 => exists b2 cap2 f2 ow2 pre2,
             prhtx_post (PA := PA) B Lam (ms_regs ms) (dw + 192) lyc Sc Hpc ly2 S2 Hp2 W2 mem2 t b cap b2
               (len0 + Z.of_nat (length pre) + Z.of_nat (length pre2)) cap2 f2 ((txt ++ pre) ++ pre2) /\
             prhtx_out fc f2 ow ow2 b cap b2 cap2
               (TxModel.tx_capf (len0 + Z.of_nat (length pre)) cap (TxModel.plen Q)) (concat Q) pre2 /\
             (fc = 0 -> f2 = 0) /\
             room_live_cf S2 /\
             (exists jq h2, tx_jok (len0 + Z.of_nat (length pre)) cap fc f2 (TxModel.plen Q) jq /\
                PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + j + jq)%nat rp_H0 h2 S2) /\
             prh_ledger (PI := prh_img_B) (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam peak cnt fail ran most ow2))) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2,
     tv_liveR WR ly2 S2 Hp2 W2 mem2 md2 kj2 b2 (P ++ Q) ->
     (forall a, sp0 - 192 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) ->
     aregs_preserved (ms_regs ms) regs2 ->
     SRW W2 (mkCfg (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2) QF) ->
  SRW Wc (mkCfg ms mdc) QF.
Proof.
intros Wc E ss ms mdc lyc Sc Hpc kj b P Q STK1 HS Hrv HE2 HL R2 R3 R4 R8 Hra Hra4 Hrac HSTK10 HSTK1 HPFX Hcallee HK.
pose proof HL as (HJ & HWIN & (cap & fc & ow & pre & (HTX0 & (j & histc & Hj & HPOSc) & HMN & HDEAD & (WS0 & HWI & HWB)))
  & HRO & HFK & HRAc & HBVc & HSV).
pose proof HPRE as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & Hdpres).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc. pose proof (ajxR_frs HJ) as HFRc.
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Eshi & _).
pose proof HTX0 as (_ & _ & Hks & _ & HO & _).
assert (Hspc : spZ (ms_regs ms) = sp0 - 192) by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hsp : getr (ms_regs ms) 2 = sv_denot E (SOff 2 (-192))).
{ apply bv_eq. rewrite denot_SOff, HE2, R2. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite YP0m.zcanon_small by lia. lia. }
destruct HPFX as (R & ER).
destruct (tx_state_pre B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b cap fc ow
  (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc (ms_mem ms) (ms_regs ms) (dw + 192) HTX0
  ltac:(rewrite Hspc; lia) ltac:(rewrite Hspc; lia))
  as (HRM & HPL & HTR & HREC1 & HINV1 & HLED1 & HBB & EHp & Hplen).
pose proof (tx_window rp_sm rp_x rp_os rp_i j len0 cap0 f0 fc own ow b0 b cap (TxModel.plen P) (concat P) pre
  (TxModel.plen Q) (TxModel.plen R) HO Hj Hks (tv_evs_split P Q R ER)) as HWQ.
pose proof (tx_room_window (as_universe B) (st_depot S) (st_depot Sc) WS0 len0 cap0 f0 fc own ow b0 b cap
  (TxModel.plen P) (concat P) pre (TxModel.plen Q) (TxModel.plen R) HO Hks (tv_roomw_split P Q R ER) HWI HWB)
  as HROOMc.
pose proof (tx_cons_window rp_sm rp_x rp_os rp_i j len0 cap0 f0 fc own ow b0 b cap (TxModel.plen P) (concat P) pre
  (TxModel.plen Q) (TxModel.plen R) HO Hj Hks (tv_cons_split P Q R ER)) as HCONSc.
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx _ _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWI)
  as HJW.
pose proof (s10_fwin_callR B ARx SK WR STKV dw sp0 FP0 ly _ Hp W mem md [] lyc Sc Hpc Wc (ms_mem ms) mdc kj
  (ms_regs ms) (-192) HJ ltac:(rewrite Hspc; lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(rewrite Zminus_mod, Hdw16; reflexivity)) as HFW.
replace (dw - -192) with (dw + 192) in HFW by lia.
assert (Hpres : forall a, t - 16 <= a < ly_top lyc -> aview SEGS (w_H Wc) (ms_mem ms) a <> None).
{ intros a Ha. destruct HTR as [HTR _]; [lia|]. exact (HTR a Ha). }
destruct (s10_achain_at lyc Wc (ms_mem ms) (sp0 - 192) t Hpres Ht8 ltac:(lia) ltac:(rewrite Etop; lia) ltac:(lia))
  as (ch1 & Hch1).
assert (Hs0 : s0Z (ms_regs ms) = t) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
assert (HSHI1 : spZ (ms_regs ms) + 64 <= ly_stk_hi lyc) by (rewrite Hspc, Eshi; lia).
assert (HCNT : count_cid 0 (frames Sc) < fs_frames 0) by (rewrite HFRc; exact HFR0).
assert (HHc : prhtx_home Lam lyc Sc v 56)
  by exact (tv_home_keep _ _ _ _ ly _ Hp W mem md lyc Sc Hpc Wc (ms_mem ms) mdc kj Lam v HJ HHOME).
assert (HCF : tv_cf lyc Sc Hpc Wc (ms_mem ms) (ms_regs ms) b cap fc ow P pre).
{ split; [exact HFW|]. split; [exact HPL|]. split; [exact HTR|]. split; [exact HREC1|]. split; [exact HINV1|].
  split; [exact HLED1|]. split; [exact HRM|]. split; [lia|]. split; [exact HRO|]. split; [exact HSHI1|].
  split; [exact Hrac|].
  split; [exact HCNT|]. split; [exact EHp|]. split; [exact Hplen|]. split; [exact HFK|]. split; [exact HBVc | exact HHc]. }
eapply SRr'_bind.
{ eapply (s10_call_WbmR B ARx SK LAWS WR (wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms STKV dw sp0 FP0 ly S Hp W
    mem md [] lyc Sc Hpc mdc kj WS0
    STK1 (prhtx_fp t b cap) (-192) (ew E 2) (getr (ms_regs ms) 1) ch1 _ _
    HS Hrv HJW Hsp eq_refl HE2 ltac:(reflexivity) ltac:(lia) HSTK10 ltac:(lia)
    Hdw0 Hdw16 ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp) eq_refl Hra Hra4
    ltac:(rewrite Hs0; replace (sp0 + -192) with (sp0 - 192) by lia; exact Hch1)).
  - intros HPRE1. replace (dw - -192) with (dw + 192) by lia.
    exact (Hcallee cap fc ow pre j histc ch1 HCF HPOSc HROOMc HCONSc HWQ HPRE1).
  - unfold fp_sub_x. intros a Ha.
    destruct (tx_state_fp B ARx LAWS Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b cap fc ow
      (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc (ms_mem ms) mdc HTX0 HARc a Ha) as [H1|H1]; [left | right; left]; exact H1. }
cbv beta. intros W2 c2 _ HN.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HWB1 & HJ2 & HJ1 & HW1 & HP &
  ((b2 & cap2 & f2 & ow2 & pre2 & HPOST & HOUT & HDEAD2 & HRM2 & (jq & h2 & Hjq & HPOS2) & HLED2) & HMN2)).
replace (dw - -192) with (dw + 192) in HJ1 by lia.
destruct (tv_live_after lyc Sc Hpc Wc (ms_mem ms) mdc kj b cap fc ow P pre j Q ly2 S2 Hp2 W2 mem2 md2 k1 b2 cap2 f2 ow2
  pre2 jq h2 (ms_regs ms) STK1 WS0 WS1 HL HTX0 Hj HDEAD HWB Hspc HSTK10 HJ2 HJ1
  ltac:(intros a Ha Hn; apply HW1; [lia | exact Hn])
  HPOST HOUT HDEAD2 HWB1 HRM2 HLED2 Hjq HPOS2 HMN2) as (HL2 & Kst).
exact (HK ly2 S2 Hp2 W2 regs2 mem2 md2 (kj + k1) b2 HL2 Kst HP).
Qed.

(* the shape of a call's continuation (after the call: the live state at WR) *)
Definition tv_kont (Wc : world SEGS) (ms : machine_state) (Q : list (list Z)) (P : list (list Z)) : Prop :=
  forall ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2,
    tv_liveR WR ly2 S2 Hp2 W2 mem2 md2 kj2 b2 (P ++ Q) ->
    (forall a, sp0 - 192 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a) ->
    aregs_preserved (ms_regs ms) regs2 ->
    SRW W2 (mkCfg (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2) QF.
(* the call registers every site sets up (the return address below the ceiling: the callee texts' fpre, discharged at
   each `jal` from its return pc by PRW_StepKit.pa_slot_lt_ceil_b) *)
Definition tv_callregs (ms : machine_state) : Prop :=
  getr (ms_regs ms) 2 = w64 (sp0 - 192) /\ getr (ms_regs ms) 3 = getr regs 3 /\ getr (ms_regs ms) 4 = getr regs 4 /\
  getr (ms_regs ms) 8 = w64 t /\ getr (ms_regs ms) 10 = w64 t /\
  YK0s.ret_ok (getr (ms_regs ms) 1) /\ 4096 <= raZ (ms_regs ms) /\ raZ (ms_regs ms) < YM05.alloc_ceiling.

(* ---- tx_put(t, srcp, |srcl|): its GROW premise from the call's guarded window (tx_put_ev), its three arms and two
   position conjuncts read back by tx_put_res; the source apart from the record and from every live block (so from the
   live buffer, whatever its capacity: the literal sources are image bytes) ---- *)
Lemma tv_put_call : forall Wc E ss ms mdc lyc Sc Hpc kj b P srcp srcl,
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
  bv_unsigned (ew E 2) = sp0 -> tv_liveR WR lyc Sc Hpc Wc (ms_mem ms) mdc kj b P -> tv_callregs ms ->
  getr (ms_regs ms) 11 = w64 srcp -> getr (ms_regs ms) 12 = w64 (Z.of_nat (length srcl)) ->
  src_rd Wc (ms_mem ms) srcp srcl -> prhtx_kept B Lam lyc Sc srcp (Z.of_nat (length srcl)) ->
  (forall a, srcp <= a < srcp + Z.of_nat (length srcl) -> ~ (t <= a < t + 28) /\
     forall bb cb, In (bb, cb) (ablocks B lyc Sc) -> ~ (bb <= a < bb + cb)) ->
  (exists R, P ++ [srcl] ++ R = TxModel.tvp tv PP d) ->
  tv_kont Wc ms [srcl] P ->
  SRW Wc (mkCfg ms mdc) QF.
Proof.
intros Wc E ss ms mdc lyc Sc Hpc kj b P srcp srcl HS Hrv Hpcs HE2 HL (R2 & R3 & R4 & R8 & Ha0 & Hra & Hra4 & Hrac)
  Ha1 Ha2 HSRC HKEPT Hdisj HPFX HK.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
assert (Hcnt : Z.of_nat (length (concat P)) + Z.of_nat (length srcl) <= Z.of_nat (length ADD))
  by (pose proof (tv_pfx_len P [srcl] HPFX) as H; cbn [concat] in H; rewrite app_nil_r in H; exact H).
eapply (tv_call_core Wc E ss ms mdc lyc Sc Hpc kj b P [srcl] (@STK_tx_put prh_img_B) HS Hrv HE2 HL R2 R3 R4
  R8 Hra Hra4 Hrac SK0 ltac:(lia) HPFX).
- intros cap fc ow pre j histc ch1
    (HFW & HPL & HTR & HREC1 & HINV1 & HLED1 & HRM & HBB & HRO & HSHI & HRAc & HCNT & EHp & Hplen & _) HPOSc HRW HCF HWQ
    HPRE1.
  rewrite Hpcs.
  assert (Hdisj' : forall a, srcp <= a < srcp + Z.of_nat (length srcl) -> ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)).
  { intros a Ha. destruct (Hdisj a Ha) as [H1 H2]. split; [exact H1|]. intros Hb.
    destruct HINV1 as (_ & [(Hz & _) | (_ & _ & Hin & _)]); [lia | exact (H2 b cap Hin Hb)]. }
  eapply SRr'_mono.
  { exact (TXPUT rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 (dw + 192) t srcp
      (Z.of_nat (length srcl)) b (len0 + Z.of_nat (length pre)) cap fc ow (txt ++ pre) srcl
      Lam peak cnt fail ran most (conj HPRE1 (conj HRO (conj HSHI (conj HRAc HFRM)))) HCLO HRM HPOSc HRP4 HRW HCF
      Ha0 Ha1 Ha2 HFW HPL HTR HREC1 HINV1 HSRC eq_refl HKEPT Hdisj' ltac:(lia) HLED1
      (fun Hf Hlt => tx_put_ev rp_sm rp_x rp_os (rp_i + j)%nat (len0 + Z.of_nat (length pre)) cap (Z.of_nat (length srcl))
         fc HWQ Hf Hlt)
      HBB ltac:(lia)). }
  intros W' c' _. apply tv_fpostWm_mono; [intros WS HW; exact HW|].
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 (b2 & cap2 & f2 & ow2 & pre2 & HPOST & HARMS & HDEAD2 & _ & HRM2 & HG & HNG & HLED2).
  destruct (tx_put_res rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc S2 (len0 + Z.of_nat (length pre)) cap fc f2 ow ow2 b b2
    cap2 (Z.of_nat (length srcl)) srcl pre2 _ HARMS HG HNG) as (HOUT & jq & h2 & Hjq & HPOS2).
  cbv beta. exists b2, cap2, f2, ow2, pre2.
  split; [exact HPOST|]. split; [cbn [concat]; rewrite app_nil_r; exact HOUT|].
  split; [exact HDEAD2|]. split; [exact HRM2|]. split; [exists jq, h2; split; [exact Hjq | exact HPOS2] | exact HLED2].
- exact HK.
Qed.

(* ---- tx_line(t, dl) ---- *)
Lemma tv_wind_len : forall dl, 0 <= dl -> Z.of_nat (length (concat (WriterValue.wind true dl))) = 1 + 2 * dl.
Proof.
intros dl H. unfold WriterValue.wind. cbn [concat length app].
assert (G : forall n, length (concat (repeat [32; 32] n)) = (2 * n)%nat).
{ induction n as [|n IH]; [reflexivity|]. cbn [repeat concat]. rewrite length_app, IH. cbn. lia. }
rewrite G. lia.
Qed.
Lemma tv_line_call : forall Wc E ss ms mdc lyc Sc Hpc kj b P dl,
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_line ->
  bv_unsigned (ew E 2) = sp0 -> tv_liveR WR lyc Sc Hpc Wc (ms_mem ms) mdc kj b P -> tv_callregs ms ->
  getr (ms_regs ms) 11 = w64 dl -> 0 <= dl <= 2 ^ 31 - 1 ->
  (exists R, P ++ WriterValue.wind true dl ++ R = TxModel.tvp tv PP d) ->
  tv_kont Wc ms (WriterValue.wind true dl) P ->
  SRW Wc (mkCfg ms mdc) QF.
Proof.
intros Wc E ss ms mdc lyc Sc Hpc kj b P dl HS Hrv Hpcs HE2 HL (R2 & R3 & R4 & R8 & Ha0 & Hra & Hra4 & Hrac)
  Ha1 Hdl HPFX HK.
pose proof tv_stk_facts as (_ & _ & SK2 & SK3 & _). pose proof (tv_stkv nn) as ESK.
pose proof (tv_wind_len dl ltac:(lia)) as WL.
pose proof (tv_pfx_len _ _ HPFX) as Hcnt. rewrite WL in Hcnt.
eapply (tv_call_core Wc E ss ms mdc lyc Sc Hpc kj b P (WriterValue.wind true dl) (@STK_tx_line prh_img_B)
  HS Hrv HE2 HL R2 R3 R4 R8 Hra Hra4 Hrac SK2 ltac:(lia) HPFX).
- intros cap fc ow pre j histc ch1
    (HFW & HPL & HTR & HREC1 & HINV1 & HLED1 & HRM & HBB & HRO & HSHI & HRAc & HCNT & EHp & Hplen & _) HPOSc HRW HCF HWQ
    HPRE1.
  rewrite Hpcs. eapply SRr'_mono.
  { exact (TXLINE rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 (dw + 192) t dl b
      (len0 + Z.of_nat (length pre)) cap fc ow (txt ++ pre)
      Lam peak cnt fail ran most (conj HPRE1 (conj HRO (conj HSHI (conj HRAc HFRM)))) HCLO HRM HPOSc HRP4 HRW HCF
      Ha0 Ha1 Hdl HFW HPL HTR HREC1 HINV1 ltac:(lia) HLED1 HWQ HBB ltac:(lia)). }
  intros W' c' _. apply tv_fpostWm_mono; [intros WS HW; exact HW|].
  intros ly2 S2 Hp2 W2 regs2 mem2 md2
    (b2 & cap2 & f2 & ow2 & pre2 & HPOST & HOUT & HDEAD2 & HRM2 & jq & h2 & Hj1 & Hj2 & Hj3 & Hj4 & HLED2).
  cbv beta. exists b2, cap2, f2, ow2, pre2.
  split; [exact HPOST|]. split; [exact HOUT|]. split; [exact HDEAD2|]. split; [exact HRM2|].
  split; [exists jq, h2; split; [exact (conj Hj1 (conj Hj3 Hj4)) | exact Hj2] | exact HLED2].
- exact HK.
Qed.

(* ---- tx_string(t, x): the i-th key ---- *)
Lemma tv_str_call : forall Wc E ss ms mdc lyc Sc Hpc kj b P x k nm,
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_string ->
  bv_unsigned (ew E 2) = sp0 -> tv_liveR WR lyc Sc Hpc Wc (ms_mem ms) mdc kj b P -> tv_callregs ms ->
  getr (ms_regs ms) 11 = w64 x ->
  PRH_Reader.pj_cstrR SEGS (rdW Wc (ms_mem ms)) (prh_lin Lam) x k nm -> prhtx_bvis Wc (ms_mem ms) x k ->
  (exists R, P ++ TxModel.strp nm ++ R = TxModel.tvp tv PP d) ->
  tv_kont Wc ms (TxModel.strp nm) P ->
  SRW Wc (mkCfg ms mdc) QF.
Proof.
intros Wc E ss ms mdc lyc Sc Hpc kj b P x k nm HS Hrv Hpcs HE2 HL (R2 & R3 & R4 & R8 & Ha0 & Hra & Hra4 & Hrac)
  Ha1 HSTR HBVS HPFX HK.
pose proof tv_stk_facts as (_ & _ & _ & _ & SK4 & SK5 & _). pose proof (tv_stkv nn) as ESK.
pose proof (tv_pfx_len _ _ HPFX) as Hcnt. rewrite s10_strp_wstr in Hcnt.
eapply (tv_call_core Wc E ss ms mdc lyc Sc Hpc kj b P (TxModel.strp nm) (@STK_tx_string prh_img_B)
  HS Hrv HE2 HL R2 R3 R4 R8 Hra Hra4 Hrac SK4 ltac:(lia) HPFX).
- intros cap fc ow pre j histc ch1
    (HFW & HPL & HTR & HREC1 & HINV1 & HLED1 & HRM & HBB & HRO & HSHI & HRAc & HCNT & EHp & Hplen & _) HPOSc HRW HCF HWQ
    HPRE1.
  rewrite Hpcs. eapply SRr'_mono.
  { exact (TXSTR rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 (dw + 192) t x k b
      (len0 + Z.of_nat (length pre)) cap fc ow nm (txt ++ pre)
      Lam peak cnt fail ran most (conj HPRE1 (conj HRO (conj HSHI (conj HRAc HFRM)))) HCLO HRM HPOSc HRP4 HRW HCF
      Ha0 Ha1 HFW HPL HTR HREC1 HINV1 HSTR HBVS ltac:(lia) HLED1 HWQ HBB ltac:(lia) HCNT). }
  intros W' c' _. apply tv_fpostWm_mono; [intros WS HW; exact HW|].
  intros ly2 S2 Hp2 W2 regs2 mem2 md2
    (b2 & cap2 & f2 & ow2 & pre2 & HPOST & HOUT & HDEAD2 & _ & _ & HRM2 & jq & h2 & Hj1 & Hj2 & Hj3 & Hj4 & HLED2).
  cbv beta. exists b2, cap2, f2, ow2, pre2.
  split; [exact HPOST|]. split; [rewrite s10_strp_wstr; exact HOUT|]. split; [exact HDEAD2|]. split; [exact HRM2|].
  split; [exists jq, h2; split; [exact (conj Hj1 (conj Hj3 Hj4)) | exact Hj2] | exact HLED2].
- exact HK.
Qed.

(* ---- tx_value(t, kid, pretty, d + 1): the recursion, at the text one level down ---- *)
Hypothesis IHV : forall n', nn = Nat.succ n' -> ttx_value_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n'.
Lemma tv_val_call : forall Wc E ss ms mdc lyc Sc Hpc kj b P n' kid tvk Dk,
  nn = Nat.succ n' ->
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_value ->
  bv_unsigned (ew E 2) = sp0 -> tv_liveR WR lyc Sc Hpc Wc (ms_mem ms) mdc kj b P -> tv_callregs ms ->
  getr (ms_regs ms) 11 = w64 kid -> getr (ms_regs ms) 12 = w64 pretty -> getr (ms_regs ms) 13 = w64 (d + 1) ->
  (PjTree.depth tvk <= n')%nat -> d + 1 + Z.of_nat (PjTree.depth tvk) <= 2 ^ 31 - 1 ->
  PRH_Reader.pj_nodeR SEGS (rdW Wc (ms_mem ms)) (prh_lin Lam) kid tvk Dk -> (forall bk, In bk Dk -> In bk Lam) ->
  prhtx_home Lam lyc Sc kid 56 -> range_addressable (aview SEGS (w_H Wc) (ms_mem ms)) SHADOW_OFF kid 56 ->
  Forall (fun bk => prhtx_bvis Wc (ms_mem ms) (fst bk) (snd bk)) Dk -> (kid + 56 <= t \/ t + 28 <= kid) ->
  (exists R, P ++ TxModel.tvp tvk PP (d + 1) ++ R = TxModel.tvp tv PP d) ->
  tv_kont Wc ms (TxModel.tvp tvk PP (d + 1)) P ->
  SRW Wc (mkCfg ms mdc) QF.
Proof.
intros Wc E ss ms mdc lyc Sc Hpc kj b P n' kid tvk Dk Enn HS Hrv Hpcs HE2 HL
  (R2 & R3 & R4 & R8 & Ha0 & Hra & Hra4 & Hrac) Ha1 Ha2 Ha3 Hdk HdkD HNk HDk HHk HRAk HBVk HAPk HPFX HK.
pose proof (tv_stkv nn) as ESK. pose proof (tv_stkv n') as ESK'. pose proof tv_stk_facts as (SK0 & SK1 & _).
assert (HSK' : 0 <= @STK_tx_value prh_img_B n') by lia.
assert (Ezn : Z.of_nat nn = Z.of_nat n' + 1) by (rewrite Enn, Nat2Z.inj_succ; lia).
pose proof (tv_pfx_len _ _ HPFX) as Hcnt. rewrite s10v_tvp_wv in Hcnt.
eapply (tv_call_core Wc E ss ms mdc lyc Sc Hpc kj b P (TxModel.tvp tvk PP (d + 1)) (@STK_tx_value prh_img_B n')
  HS Hrv HE2 HL R2 R3 R4 R8 Hra Hra4 Hrac HSK' ltac:(lia) HPFX).
- intros cap fc ow pre j histc ch1
    (HFW & HPL & HTR & HREC1 & HINV1 & HLED1 & HRM & HBB & HRO & HSHI & HRAc & HCNT & EHp & Hplen & _) HPOSc HRW HCF HWQ
    HPRE1.
  rewrite Hpcs. eapply SRr'_mono.
  { exact (IHV n' Enn rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 (dw + 192) t
      kid pretty (d + 1) b (len0 + Z.of_nat (length pre)) cap fc ow tvk Dk (txt ++ pre)
      Lam peak cnt fail ran most (conj HPRE1 (conj HRO (conj HSHI (conj HRAc HFRM)))) HCLO HRM HPOSc HRP4 HRW HCF
      Hdk Ha0 Ha1 Ha2 Ha3 HPR ltac:(lia) HdkD HFW HPL HTR HREC1 HINV1 HNk HDk HHk HRAk HBVk HAPk ltac:(lia) HLED1 HWQ
      HBB ltac:(lia)
      HCNT). }
  intros W' c' _. apply tv_fpostWm_mono; [intros WS HW; exact HW|].
  intros ly2 S2 Hp2 W2 regs2 mem2 md2
    (b2 & cap2 & f2 & ow2 & pre2 & HPOST & HOUT & HDEAD2 & _ & _ & _ & _ & HRM2 & jq & h2 & Hj1 & Hj2 & Hj3 & Hj4 & HLED2).
  cbv beta. exists b2, cap2, f2, ow2, pre2.
  split; [exact HPOST|]. split; [rewrite s10v_tvp_wv; exact HOUT|]. split; [exact HDEAD2|]. split; [exact HRM2|].
  split; [exists jq, h2; split; [exact (conj Hj1 (conj Hj3 Hj4)) | exact Hj2] | exact HLED2].
- exact HK.
Qed.


(* ---- the symbolic state P (0x8550c, after the opening bracket's call) from the concrete facts a call's
   continuation hands over ---- *)
(* ---- the depth-overflow flag `addiw s6,a3,1; slt s9,s6,a3` (B 0x85540 / 0x85564) is 0 when d + 1 fits
   (proved by BTx, lane b-tx; image-free) ---- *)
Lemma tvo_slt_zero : forall (x : word) dd, bv_unsigned x = dd -> 0 <= dd <= 2 ^ 31 - 2 ->
  alu64 ALU_SLT (sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 1)))) x = Z_to_bv 64 0.
Proof.
intros x dd Hx Hd.
assert (Ex : x = Z_to_bv 64 dd) by (rewrite <- Hx; symmetry; apply Z_to_bv_bv_unsigned).
subst x. rewrite zalu32_sound.
assert (Ez : zalu32 ALU_ADD dd 1 = dd + 1).
{ unfold zalu32, zalu_raw, zu32, M32, zcanon, M64.
  rewrite (Z.mod_small dd) by lia. rewrite (Z.mod_small 1) by lia.
  unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
  unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  rewrite (Z.mod_small (dd + 1 + 2147483648)) by lia.
  replace (dd + 1 + 2147483648 - 2147483648) with (dd + 1) by lia. apply Z.mod_small. lia. }
rewrite Ez.
apply bv_eq. rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw].
unfold bv_swrap. change (bv_half_modulus 64) with 9223372036854775808.
unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite (Z.mod_small (dd + 1)) by lia. rewrite (Z.mod_small dd) by lia.
rewrite (Z.mod_small (dd + 1 + 9223372036854775808)) by lia.
rewrite (Z.mod_small (dd + 9223372036854775808)) by lia.
rewrite (proj2 (Z.ltb_ge _ _)) by lia.
reflexivity.
Qed.

(* the 32-bit `addiw s6,a3,1` (B 0x85540) as a value *)
Lemma tvo_addw1 : forall (x : word) dd, bv_unsigned x = dd -> 0 <= dd <= 2 ^ 31 - 2 ->
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (dd + 1).
Proof.
intros x dd Hx Hd.
assert (Ex : x = Z_to_bv 64 dd) by (rewrite <- Hx; symmetry; apply Z_to_bv_bv_unsigned).
subst x. rewrite zalu32_sound. f_equal.
unfold zalu32, zalu_raw, zu32, M32, zcanon, M64.
rewrite (Z.mod_small dd) by lia. rewrite (Z.mod_small 1) by lia.
unfold bv_swrap. change (bv_half_modulus 32) with 2147483648.
unfold bv_wrap. change (bv_modulus 32) with 4294967296.
rewrite (Z.mod_small (dd + 1 + 2147483648)) by lia.
replace (dd + 1 + 2147483648 - 2147483648) with (dd + 1) by lia. apply Z.mod_small. lia.
Qed.

(* the values the segment states' chunks carry, at the sv level *)
Lemma tvo_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) mod 2 ^ 64 = z.
Proof. intros E z Hz. rewrite U_SLit. unfold zcanon, M64. rewrite (Z.mod_small z) by lia. apply Z.mod_small. lia. Qed.
Lemma tvo_U_off : forall E n F k, bv_unsigned (ew E n) = F -> 0 <= F + k < 2 ^ 64 ->
  U E (SOff n k) mod 2 ^ 64 = F + k.
Proof.
intros E n F k HF Hk. rewrite U_SOff, HF. unfold zcanon, M64. rewrite (Z.mod_small (F + k)) by lia. apply Z.mod_small. lia.
Qed.
Lemma tvo_U_sh : forall E n F k, bv_unsigned (ew E n) = F -> bv_unsigned (ew E 64) = SHADOW_OFF ->
  0 <= F -> 0 <= k -> F + k < 2 ^ 47 -> U E (tvo_sh_B (SOff n k)) mod 2 ^ 64 = shadow_addr (F + k).
Proof.
intros E n F k HF HB HF0 Hk0 Hk.
assert (H8 : 0 <= (F + k) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold U. rewrite (tvo_sh_val E n F k HF HB HF0 Hk0 Hk).
rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
apply Z.mod_small. unfold shadow_addr, SHADOW_OFF. lia.
Qed.
Lemma tvo_off_word : forall E n F k, bv_unsigned (ew E n) = F -> 0 <= F + k < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (F + k).
Proof.
intros E n F k HF Hk. apply bv_eq. rewrite unsigned_lit_small by lia.
change (bv_unsigned (sv_denot E (SOff n k))) with (U E (SOff n k)).
rewrite U_SOff, HF. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

Lemma tvo_P_state : forall (Wc : world SEGS) regsc memc ty kids keys nv cs,
  spZ regsc = sp0 - 192 ->
  getr regsc 9 = w64 v -> getr regsc 18 = w64 (shadow_addr v) ->
  (forall a, sp0 - 192 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  tv_saved Wc memc ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS (rdW Wc memc) v 4 ty ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 32) 8 keys ->
  0 <= nv < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 40) 8 nv ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56 ->
  conds_ok (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) cs ->
  st_ok_pi SEGS VAL (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (ss_P_B ty cs)
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + TV_RET_OPEN_B)) memc (seg_rom SEGS))) /\
  sh_ok SEGS TVO_BX_B (tvo_SH_B false) (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (rdW Wc memc).
Proof.
intros Wc regsc memc ty kids keys nv cs Hsp H9 H18 Hpres (HSV & H72 & H16 & H24) Hty Vty
  Hkids Vkids Hkeys Vkeys Hnv Vnv HRAc Hcs.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof (Nat2Z.is_nonneg nn) as Hnn0.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
assert (Hvsp : v + 56 <= sp0 - 192) by lia.
set (more := [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) in *.
assert (Ex2 : ew (TE regs regsc more) (xr 2) = getr regsc 2) by (apply (te_cur regs regsc more 2%bv 2); reflexivity).
assert (Ex9 : ew (TE regs regsc more) (xr 9) = w64 v) by (rewrite (te_cur regs regsc more 9%bv 9) by reflexivity; exact H9).
assert (E64 : ew (TE regs regsc more) 64 = w64 SHADOW_OFF) by (rewrite (te_more_lt regs regsc more 0) by lia; reflexivity).
assert (E65 : ew (TE regs regsc more) 65 = w64 kids) by (rewrite (te_more_lt regs regsc more 1) by lia; reflexivity).
assert (E66 : ew (TE regs regsc more) 66 = w64 keys) by (rewrite (te_more_lt regs regsc more 2) by lia; reflexivity).
assert (E67 : ew (TE regs regsc more) 67 = w64 nv) by (rewrite (te_more_lt regs regsc more 3) by lia; reflexivity).
assert (E13 : ew (TE regs regsc more) 13 = w64 d) by (rewrite (te_entry regs regsc more 13%bv 13) by reflexivity; exact H13).
assert (Usp : bv_unsigned (ew (TE regs regsc more) (xr 2)) = sp0 - 192) by (rewrite Ex2; unfold spZ in Hsp; exact Hsp).
assert (Uv : bv_unsigned (ew (TE regs regsc more) (xr 9)) = v) by (rewrite Ex9; apply unsigned_lit_small; lia).
assert (Ub : bv_unsigned (ew (TE regs regsc more) 64) = SHADOW_OFF) by (rewrite E64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Hd64 : 0 <= d < 2 ^ 64) by lia.
split.
- apply ts_st_ok.
  + intros r. destruct (bv_eqb r 18%bv) eqn:Hr18.
    * apply bv_eqb_eq in Hr18. subst r. rewrite sr_get_set_same by reflexivity.
      rewrite (tvo_sh_val (TE regs regsc more) (xr 9) v 0 Uv Ub ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite Z.add_0_r. exact H18.
    * rewrite sr_get_set_other by (intros HH; subst r; rewrite bv_eqb_refl in Hr18; discriminate).
      exact (te_regs_ok regs regsc more r).
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * apply (ts_rok (TE regs regsc more) _ (xr 2) (sp0 - 192)); [exact Usp | lia | lia | |].
      -- intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      -- unfold tvo_head_B. constructor; [|constructor; [|constructor; [|constructor]]].
         ++ apply (ts_chunk (TE regs regsc more) _ (sp0 - 192) 16 8 (SLit 0) 0);
            [reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
            replace (sp0 - 192 + 16) with (sp0 - 176) by lia. exact H16.
         ++ apply (ts_chunk (TE regs regsc more) _ (sp0 - 192) 24 8 (SOff 13 0) d);
            [cbn [sv_denot]; rewrite E13; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
            | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
            replace (sp0 - 192 + 24) with (sp0 - 168) by lia. exact H24.
         ++ apply (ts_chunk (TE regs regsc more) _ (sp0 - 192) 72 8 TVO_BX_B SHADOW_OFF);
            [unfold TVO_BX_B; cbn [sv_denot]; rewrite E64; unfold w64;
             rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite Z.add_0_r; reflexivity
            | change (8 * Z.of_N 8) with 64; unfold SHADOW_OFF; lia | cbn; lia |].
            replace (sp0 - 192 + 72) with (sp0 - 120) by lia. exact H72.
    * unfold tvo_node_B. apply (ts_rok (TE regs regsc more) _ (xr 9) v); [exact Uv | lia | lia | intros o Ho; lia |].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      -- apply (ts_chunk (TE regs regsc more) _ v 0 4 (SLit ty) ty);
         [reflexivity | change (8 * Z.of_N 4) with 32; lia | cbn; lia |].
         rewrite Z.add_0_r. exact Vty.
      -- apply (ts_chunk (TE regs regsc more) _ v 24 8 (SOff 65 0) kids);
         [cbn [sv_denot]; rewrite E65; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vkids].
      -- apply (ts_chunk (TE regs regsc more) _ v 32 8 (SOff 66 0) keys);
         [cbn [sv_denot]; rewrite E66; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vkeys].
      -- apply (ts_chunk (TE regs regsc more) _ v 40 8 (SOff 67 0) nv);
         [cbn [sv_denot]; rewrite E67; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
         | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact Vnv].
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, tvo_node_B.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite !(ts_bv_some (TE regs regsc more)), ?Usp, ?Uv.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact Hcs | exact I]].
    cbn [f_atoms]. unfold tvo_atoms_B. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    assert (Usp' : bv_unsigned (ew (TE regs regsc more) 34) = sp0 - 192) by exact Usp.
    assert (Uv' : bv_unsigned (ew (TE regs regsc more) 41) = v) by exact Uv.
    rewrite ?Usp, ?Uv, ?Usp', ?Uv', ?Ub.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    assert (Hspm : (sp0 - 192) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
    repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
- unfold sh_ok, tvo_SH_B. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H Wc) memc (TE regs regsc more) TVO_BX_B (xr 9) v 56 v 0 56).
  + exact HRAc.
  + unfold TVO_BX_B. rewrite (U_atom (TE regs regsc more) 64 SHADOW_OFF E64) by (unfold SHADOW_OFF; lia). reflexivity.
  + rewrite (U_atom (TE regs regsc more) (xr 9) v Ex9) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ==== THE OPEN ARM's LOOP STATES at image B, from concrete facts (B twin of S10TxValue.v 339382e2cb0's ss_M / ss_B
   entries; B's frame layout, B's registers, and the facts UBSan's pointer checks need) ==== *)
Lemma tv_regs_ok_set : forall E sr rg (r : bv 5) e, regs_ok E sr rg -> bv_eqb r 0 = false ->
  getr rg r = sv_denot E e -> regs_ok E (sr_set sr r e) rg.
Proof.
intros E sr rg r e H Hr He r'. destruct (decide (r' = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr. exact He.
- rewrite sr_get_set_other by exact Hne. exact (H r').
Qed.
Lemma tv_den_atom : forall E n x, bv_unsigned (ew E n) = x -> 0 <= x < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 x.
Proof.
intros E n x Hx Hr. apply bv_eq. rewrite denot_SOff, Hx, Z.add_0_r, unsigned_lit_small by exact Hr.
apply YP0m.zcanon_small. exact Hr.
Qed.
Lemma tv_den_off : forall E n k x, bv_unsigned (ew E n) = x -> 0 <= x + k < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof.
intros E n k x Hx Hr. apply bv_eq. rewrite denot_SOff, Hx, unsigned_lit_small by exact Hr.
apply YP0m.zcanon_small. exact Hr.
Qed.

(* the extras of the loop's states: the shadow base, kids, keys, n, and for an object the i-th key slot and pointer *)
Definition tvo_more (obj : bool) (kids keys n i kp : Z) : list word :=
  [w64 SHADOW_OFF; w64 kids; w64 keys; w64 n] ++ (if obj then [w64 (keys + 8 * i); w64 kp] else []).
(* the registers every loop state pins at B (callee-saved, so kept across the calls) *)
Definition tv_mregs_B (rg : bvmap 5 word) : Prop :=
  getr rg 2 = w64 (sp0 - 192) /\ getr rg 9 = w64 v /\ getr rg 18 = w64 (shadow_addr v) /\
  getr rg 20 = w64 (v + 40) /\ getr rg 23 = w64 (v + 24) /\ getr rg 27 = w64 (shadow_addr (v + 24)) /\
  getr rg 25 = w64 0.
(* the i-th key slot's facts (an object; s8 = 8 i) *)
Definition tv_keyf_B (rg : bvmap 5 word) (Wc : world SEGS) (memc : word -> option byte) (keys i kp : Z) : Prop :=
  getr rg 24 = w64 (8 * i) /\ 0 <= i /\ 4096 <= keys /\ keys + 8 * i + 8 <= YM05.alloc_ceiling /\
  (keys + 8 * i) mod 8 = 0 /\ in_app (keys + 8 * i) 8 /\
  (keys + 8 * i + 8 <= v \/ v + 56 <= keys + 8 * i) /\
  0 <= kp < 2 ^ 64 /\ val_mem SEGS (rdW Wc memc) (keys + 8 * i) 8 kp /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (keys + 8 * i) 8.

Lemma tv_M_entry_B : forall pc ty (obj : bool) rg (Wc : world SEGS) memc kids keys n i kp cs,
  tv_mregs_B rg -> tv_saved Wc memc -> tv_spill Wc memc ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS (rdW Wc memc) v 4 ty ->
  4096 <= kids <= 2 ^ 47 -> val_mem SEGS (rdW Wc memc) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 32) 8 keys ->
  1 <= n <= 2 ^ 42 -> val_mem SEGS (rdW Wc memc) (v + 40) 8 n ->
  0 <= i <= 2 ^ 42 -> getr rg 26 = w64 i ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56 ->
  (obj = true -> tv_keyf_B rg Wc memc keys i kp) ->
  conds_ok (TE regs rg (tvo_more obj kids keys n i kp)) cs ->
  st_ok_pi SEGS VAL (TE regs rg (tvo_more obj kids keys n i kp)) (ss_M_B pc ty obj cs)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS TVO_BX_B (tvo_SH_B obj) (TE regs rg (tvo_more obj kids keys n i kp)) (rdW Wc memc).
Proof.
intros pc ty obj rg Wc memc kids keys n i kp cs (R2 & R9 & R18 & R20 & R23 & R27 & R25) (HSV & H72 & H16 & H24)
  (S1 & S2 & S3 & S4 & S5 & S6 & S7) Hty Vty Hkd Vkd Hky Vky Hn Vn Hi R26 HRAv HKF Hcs.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof (Nat2Z.is_nonneg nn) as Hnn0.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
assert (HO2v : VAL (A_OBJ 2) = 65536) by (vm_compute; reflexivity).
set (E := TE regs rg (tvo_more obj kids keys n i kp)).
assert (X2 : bv_unsigned (ew E (xr 2)) = sp0 - 192).
{ unfold E, xr. rewrite (te_cur regs rg _ 2%bv 2) by reflexivity. rewrite R2. apply unsigned_lit_small. lia. }
assert (X9 : bv_unsigned (ew E (xr 9)) = v).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = i).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small. lia. }
assert (X64 : bv_unsigned (ew E 64) = SHADOW_OFF).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth app]. apply unsigned_lit_small.
  unfold SHADOW_OFF; lia. }
assert (X65 : bv_unsigned (ew E 65) = kids).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 1) by lia. cbn [nth app]. apply unsigned_lit_small. lia. }
assert (X66 : bv_unsigned (ew E 66) = keys).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 2) by lia. cbn [nth app]. apply unsigned_lit_small. lia. }
assert (X67 : bv_unsigned (ew E 67) = n).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 3) by lia. cbn [nth app]. apply unsigned_lit_small. lia. }
assert (X13 : sv_denot E (SOff 13 0) = Z_to_bv 64 d).
{ apply bv_eq. rewrite denot_SOff. unfold E. rewrite (te_entry regs rg _ 13%bv 13) by reflexivity. rewrite H13, Z.add_0_r.
  unfold w64. rewrite !unsigned_lit_small by lia. apply YP0m.zcanon_small. lia. }
(* the frame's chunks *)
assert (HFR : Forall (YP09.chunk_ok SEGS E (rdW Wc memc) (sp0 - 192)) (tvo_spills_B ++ tvo_head_B)).
{ unfold tvo_spills_B, tvo_head_B. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (ts_chunk E _ _ 8 8 (SLit 3) 3); [reflexivity | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 8) with (sp0 - 184) by lia. exact S1.
  - apply (ts_chunk E _ _ 32 8 (SOff (A_OBJ 2) 70272) (VAL (A_OBJ 2) + 70272));
      [unfold E; apply te_obj; unfold A_OBJ, A_TEXT, A_LIM; lia | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 32) with (sp0 - 160) by lia. exact S2.
  - apply (ts_chunk E _ _ 40 8 (SOff (A_OBJ 2) 70240) (VAL (A_OBJ 2) + 70240));
      [unfold E; apply te_obj; unfold A_OBJ, A_TEXT, A_LIM; lia | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 40) with (sp0 - 152) by lia. exact S3.
  - assert (Hsh32 : 0 <= shadow_addr (v + 32) < 2 ^ 64).
    { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (v + 32) 8 ltac:(lia) ltac:(lia)).
      assert ((v + 32) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
    apply (ts_chunk E _ _ 48 8 (tvo_sh_B (SOff (xr 9) 32)) (shadow_addr (v + 32)));
      [apply (tvo_sh_val E (xr 9) v 32 X9 X64); lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hsh32
      | cbn; lia |].
    replace (sp0 - 192 + 48) with (sp0 - 144) by lia. exact S4.
  - apply (ts_chunk E _ _ 56 8 (SOff (xr 9) 32) (v + 32)); [apply (tv_den_off E (xr 9) 32 v X9); lia | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 56) with (sp0 - 136) by lia. exact S5.
  - apply (ts_chunk E _ _ 64 8 (SOff (A_OBJ 2) 70208) (VAL (A_OBJ 2) + 70208));
      [unfold E; apply te_obj; unfold A_OBJ, A_TEXT, A_LIM; lia | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 64) with (sp0 - 128) by lia. exact S6.
  - assert (Hsh40 : 0 <= shadow_addr (v + 40) < 2 ^ 64).
    { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (v + 40) 8 ltac:(lia) ltac:(lia)).
      assert ((v + 40) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
    apply (ts_chunk E _ _ 80 8 (tvo_sh_B (SOff (xr 9) 40)) (shadow_addr (v + 40)));
      [apply (tvo_sh_val E (xr 9) v 40 X9 X64); lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hsh40
      | cbn; lia |].
    replace (sp0 - 192 + 80) with (sp0 - 112) by lia. exact S7.
  - apply (ts_chunk E _ _ 16 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 16) with (sp0 - 176) by lia. exact H16.
  - apply (ts_chunk E _ _ 24 8 (SOff 13 0) d); [exact X13 | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 24) with (sp0 - 168) by lia. exact H24.
  - apply (ts_chunk E _ _ 72 8 TVO_BX_B SHADOW_OFF); [apply (tv_den_atom E 64 SHADOW_OFF X64); unfold SHADOW_OFF; lia
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 72) with (sp0 - 120) by lia. exact H72. }
(* the node's chunks *)
assert (HND : Forall (YP09.chunk_ok SEGS E (rdW Wc memc) v)
  [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 24 (CVal 8 (SOff 65 0)); YP09.mkChunk 32 (CVal 8 (SOff 66 0));
   YP09.mkChunk 40 (CVal 8 (SOff 67 0))]).
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (ts_chunk E _ _ 0 4 (SLit ty) ty); [reflexivity | cbn; lia | cbn; lia |]. rewrite Z.add_0_r. exact Vty.
  - apply (ts_chunk E _ _ 24 8 (SOff 65 0) kids); [apply (tv_den_atom E 65 kids X65); lia | cbn; lia | cbn; lia | exact Vkd].
  - apply (ts_chunk E _ _ 32 8 (SOff 66 0) keys); [apply (tv_den_atom E 66 keys X66); lia | cbn; lia | cbn; lia | exact Vky].
  - apply (ts_chunk E _ _ 40 8 (SOff 67 0) n); [apply (tv_den_atom E 67 n X67); lia | cbn; lia | cbn; lia | exact Vn]. }
assert (HRG : regs_ok E tvo_mregs_B rg).
{ unfold tvo_mregs_B.
  apply tv_regs_ok_set; [|reflexivity|rewrite R25; reflexivity].
  apply tv_regs_ok_set; [|reflexivity|rewrite R27; symmetry; apply (tvo_sh_val E (xr 9) v 24 X9 X64); lia].
  apply tv_regs_ok_set; [|reflexivity|rewrite R23; symmetry; apply (tv_den_off E (xr 9) 24 v X9); lia].
  apply tv_regs_ok_set; [|reflexivity|rewrite R20; symmetry; apply (tv_den_off E (xr 9) 40 v X9); lia].
  apply tv_regs_ok_set; [|reflexivity|rewrite R18; symmetry; replace (shadow_addr v) with (shadow_addr (v + 0))
    by (rewrite Z.add_0_r; reflexivity); apply (tvo_sh_val E (xr 9) v 0 X9 X64); lia].
  apply te_regs_ok. }
assert (SHV : shent_ok SEGS TVO_BX_B E (rdW Wc memc) (mkSHE (xr 9) 0 56)).
{ apply (shent_ok_of_range SEGS (w_H Wc) memc E TVO_BX_B (xr 9) v 56 v 0 56); [exact HRAv | | | lia | lia |].
  - unfold TVO_BX_B, U. rewrite (tv_den_atom E 64 SHADOW_OFF X64) by (unfold SHADOW_OFF; lia).
    apply unsigned_lit_small. unfold SHADOW_OFF; lia.
  - unfold U. rewrite (tv_den_atom E (xr 9) v X9) by lia. apply unsigned_lit_small. lia.
  - intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
destruct obj.
- destruct (HKF eq_refl) as (R24 & Hi0 & Hk0 & Hk2 & Hk8 & Hkapp & Hkap & Hkp & Vkp & HRAk).
  assert (X68 : bv_unsigned (ew E 68) = keys + 8 * i).
  { unfold E, tvo_more. rewrite (te_more_lt regs rg _ 4) by lia. cbn [nth app]. apply unsigned_lit_small. lia. }
  assert (X69 : bv_unsigned (ew E 69) = kp).
  { unfold E, tvo_more. rewrite (te_more_lt regs rg _ 5) by lia. cbn [nth app]. apply unsigned_lit_small. lia. }
  assert (X24 : bv_unsigned (ew E (xr 24)) = 8 * i).
  { unfold E, xr. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. rewrite R24. apply unsigned_lit_small. lia. }
  split.
  + apply ts_st_ok.
    all: try change (TE regs rg (tvo_more true kids keys n i kp)) with E.
    * exact HRG.
    * vm_compute. reflexivity.
    * cbn [app]. repeat apply Forall_cons; try apply Forall_nil.
      -- apply (ts_rok E _ (xr 2) (sp0 - 192)); [exact X2 | lia | lia | intros o Ho; lia | exact HFR].
      -- apply (ts_rok E _ (xr 9) v); [exact X9 | lia | lia | intros o Ho; lia | exact HND].
      -- apply (ts_rok E _ 68 (keys + 8 * i)); [exact X68 | lia | lia | intros o Ho; lia |].
         constructor; [|constructor].
         apply (ts_chunk E _ _ 0 8 (SOff 69 0) kp); [apply (tv_den_atom E 69 kp X69); lia | cbn; lia | cbn; lia |].
         rewrite Z.add_0_r. exact Vkp.
    * apply pairwise_disjoint_of_extents. unfold extent_of_region, tvo_node_B, tvo_keyslot_B.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite !ts_bv_some. rewrite X2, X9, X68.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    * split; [|split; [exact Hcs|]].
      -- unfold tvo_matoms_B, tvo_atoms_B. cbn [app f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
         rewrite X2, X9, X64, X65, X67, X26, X66, X68.
         change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
         unfold SHADOW_OFF. repeat split; try lia. all: rewrite Zminus_mod, Hal16; reflexivity.
      -- cbn [f_alias alias_ok tvo_alias_B]. split; [|exact I]. apply U_inj.
         rewrite U_SAlu, !U_SOff, X66, X24, X68. rewrite !Z.add_0_r.
         rewrite (YP0m.zcanon_small keys) by (unfold M64; lia).
         rewrite (YP0m.zcanon_small (8 * i)) by (unfold M64; lia).
         rewrite (YP0m.zcanon_small (keys + 8 * i)) by (unfold M64; lia).
         unfold zcanon, M64, zalu_raw. apply Z.mod_small. lia.
  + unfold sh_ok, tvo_SH_B. constructor; [exact SHV|constructor; [|constructor]].
    apply (shent_ok_of_range SEGS (w_H Wc) memc E TVO_BX_B 68 (keys + 8 * i) 8 (keys + 8 * i) 0 8); [exact HRAk | | | lia | lia |].
    * unfold TVO_BX_B, U. rewrite (tv_den_atom E 64 SHADOW_OFF X64) by (unfold SHADOW_OFF; lia).
      apply unsigned_lit_small. unfold SHADOW_OFF; lia.
    * unfold U. rewrite (tv_den_atom E 68 (keys + 8 * i) X68) by lia. apply unsigned_lit_small. lia.
    * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- split.
  + apply ts_st_ok.
    all: try change (TE regs rg (tvo_more false kids keys n i kp)) with E.
    * exact HRG.
    * vm_compute. reflexivity.
    * cbn [app]. repeat apply Forall_cons; try apply Forall_nil.
      -- apply (ts_rok E _ (xr 2) (sp0 - 192)); [exact X2 | lia | lia | intros o Ho; lia | exact HFR].
      -- apply (ts_rok E _ (xr 9) v); [exact X9 | lia | lia | intros o Ho; lia | exact HND].
    * apply pairwise_disjoint_of_extents. unfold extent_of_region, tvo_node_B. cbn [app map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite !ts_bv_some. rewrite X2, X9.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    * split; [|split; [exact Hcs | exact I]].
      unfold tvo_matoms_B, tvo_atoms_B. cbn [app f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite X2, X9, X64, X65, X67, X26.
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold SHADOW_OFF. repeat split; try lia. all: rewrite Zminus_mod, Hal16; reflexivity.
  + unfold sh_ok, tvo_SH_B. constructor; [exact SHV | constructor].
Qed.

(* ---- the loop head (B 0x8559c, offset 16080, DERIVED) and the registers the loop carries: s0 = t, s1 = v,
   s2 = shadow v, s3 = pretty, s4 = v + 40, s5 = 56 i, s6 = d + 1, s7 = v + 24, s8 = 8 i, s9 = 0, s10 = i,
   s11 = shadow (v + 24) ---- *)
Definition TVO_LH_B : Z := 16080.
Definition tvo_lregs (rg : bvmap 5 word) (i : Z) : Prop :=
  tv_mregs_B rg /\ getr rg 3 = getr regs 3 /\ getr rg 4 = getr regs 4 /\ getr rg 8 = w64 t /\
  getr rg 19 = getr regs 12 /\ getr rg 21 = w64 (56 * i) /\ getr rg 22 = w64 (d + 1) /\
  getr rg 24 = w64 (8 * i) /\ getr rg 26 = w64 i.
Lemma tvo_lregs_pres : forall rg rg' i, tvo_lregs rg i -> aregs_preserved rg rg' -> tvo_lregs rg' i.
Proof.
intros rg rg' i ((R2 & R9 & R18 & R20 & R23 & R27 & R25) & R3 & R4 & R8 & R19 & R21 & R22 & R24 & R26) HP.
unfold tvo_lregs, tv_mregs_B.
rewrite (tv_ap rg rg' HP 2%bv) by ts_cs. rewrite (tv_ap rg rg' HP 9%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 18%bv) by ts_cs. rewrite (tv_ap rg rg' HP 20%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 23%bv) by ts_cs. rewrite (tv_ap rg rg' HP 27%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 25%bv) by ts_cs. rewrite (tv_ap rg rg' HP 3%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 4%bv) by ts_cs. rewrite (tv_ap rg rg' HP 8%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 19%bv) by ts_cs. rewrite (tv_ap rg rg' HP 21%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 22%bv) by ts_cs. rewrite (tv_ap rg rg' HP 24%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 26%bv) by ts_cs.
repeat split; assumption.
Qed.

(* ---- THE LOOP SET-UP, from the opening bracket's return to the loop head: 0x8550c .. 0x8559c computes s4 = v + 40,
   checks the count's shadow (covered by the node's entry), loads n, takes `beqz a0` NOT taken (n <> 0), sets the
   loop registers and writes the seven spills, and stops at the loop head with i = 0. The journal is tv_liveR's at WR,
   from the entry REBASED to the current depot (the batch) ---- *)
Lemma tvo_run_P_nz : forall lyc Sc Hpc (Wc : world SEGS) regsc memc mdc kj ty kids keys nv Q,
  AJR (STKV + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md []
    lyc Sc Hpc Wc memc mdc kj ->
  spZ regsc = sp0 - 192 ->
  getr regsc 9 = w64 v -> getr regsc 18 = w64 (shadow_addr v) -> getr regsc 8 = w64 t ->
  getr regsc 19 = w64 pretty -> getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
  (forall a, sp0 - 192 <= a < sp0 -> apresent (w_H Wc) memc a) ->
  tv_saved Wc memc ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS (rdW Wc memc) v 4 ty ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 32) 8 keys ->
  0 < nv < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 40) 8 nv ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56 ->
  d + 1 <= 2 ^ 31 - 1 ->
  (forall E' ss' ms' mdc' kj',
     st_ok_pi SEGS VAL E' ss' (restrict (w_H Wc) ms') -> ss_resv ss' = None ->
     AJR (STKV + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md []
       lyc Sc Hpc Wc (ms_mem ms') mdc' kj' ->
     tvo_lregs (ms_regs ms') 0 ->
     tv_saved Wc (ms_mem ms') -> tv_spill Wc (ms_mem ms') ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 184 <= a < sp0 - 104) ->
        aview SEGS (w_H Wc) (ms_mem ms') a = aview SEGS (w_H Wc) memc a) ->
     (forall x : word, (bv_unsigned x < sp0 - 184 \/ sp0 - 104 <= bv_unsigned x) ->
        rdW Wc (ms_mem ms') x = rdW Wc memc x) ->
     TVMN memc (ms_mem ms') ->
     SRW Wc (mkCfg (mkst (ms_regs ms') (Z_to_bv 64 (BASE + TVO_LH_B)) (ms_mem ms') (seg_rom SEGS)) mdc') Q) ->
  SRW Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + TV_RET_OPEN_B)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros lyc Sc Hpc Wc regsc memc mdc kj ty kids keys nv Q HJ Hsp H9 H18 H8 H19 H3 H4 Hpres HSV
  Hty Vty Hkids Vkids Hkeys Vkeys Hnv Vnv HRAc Hd1 HK.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof (Nat2Z.is_nonneg nn) as Hnn0.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
assert (Hvsp : v + 56 <= sp0 - 192) by lia.
set (cs := [mkAC BC_NE (SOff 67 0) (SLit 0)]).
assert (E13 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) 13 = w64 d)
  by (rewrite (te_entry regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 13%bv 13) by reflexivity; exact H13).
assert (E67 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) 67 = w64 nv)
  by (rewrite (te_more_lt regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 3) by lia; reflexivity).
assert (E64 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) 64 = w64 SHADOW_OFF)
  by (rewrite (te_more_lt regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 0) by lia; reflexivity).
assert (Ex9 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 9) = w64 v)
  by (rewrite (te_cur regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 9%bv 9) by reflexivity; exact H9).
assert (Ex2 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 2) = getr regsc 2)
  by (apply (te_cur regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 2%bv 2); reflexivity).
assert (Usp : bv_unsigned (ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 2)) = sp0 - 192) by (rewrite Ex2; exact Hsp).
assert (Uv : bv_unsigned (ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 9)) = v) by (rewrite Ex9; apply unsigned_lit_small; lia).
assert (Ub : bv_unsigned (ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) 64) = SHADOW_OFF)
  by (rewrite E64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Ud : bv_unsigned (ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) 13) = d) by (rewrite E13; apply unsigned_lit_small; lia).
assert (Uo2 : bv_unsigned (ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (A_OBJ 2)) = VAL (A_OBJ 2))
  by (rewrite (te_img regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] (A_OBJ 2)) by (unfold A_OBJ, A_TEXT, A_LIM; lia);
      apply unsigned_lit_small; apply pa_val_range).
assert (HO2v : VAL (A_OBJ 2) = 65536) by (vm_compute; reflexivity).
assert (Hcs : conds_ok (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) cs).
{ split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  unfold branch_taken. apply negb_true_iff. apply bv_eqb_false_iff. intros HH.
  assert (HU : U (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (SOff 67 0) = U (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (SLit 0))
    by (unfold U; rewrite HH; reflexivity).
  rewrite U_SOff, U_SLit, E67 in HU. unfold w64 in HU.
  rewrite unsigned_lit_small in HU by lia. unfold zcanon, M64 in HU.
  rewrite (Z.mod_small (nv + 0)) in HU by lia. rewrite (Z.mod_small 0) in HU by lia. lia. }
destruct (tvo_P_state Wc regsc memc ty kids keys nv cs Hsp H9 H18 Hpres HSV Hty Vty Hkids Vkids Hkeys Vkeys
  ltac:(lia) Vnv HRAc Hcs) as [HS SHOK].
assert (Ex1 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 1) = getr regsc 1) by (apply (te_cur regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 1%bv 1); reflexivity).
assert (Ex3 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 3) = getr regsc 3) by (apply (te_cur regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 3%bv 3); reflexivity).
assert (Ex4 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 4) = getr regsc 4) by (apply (te_cur regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 4%bv 4); reflexivity).
assert (Ex8 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 8) = getr regsc 8) by (apply (te_cur regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 8%bv 8); reflexivity).
assert (Ex19 : ew (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) (xr 19) = getr regsc 19) by (apply (te_cur regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv] 19%bv 19); reflexivity).
remember (TE regs regsc [w64 SHADOW_OFF; w64 kids; w64 keys; w64 nv]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply te_env).
assert (Usp34 : bv_unsigned (ew E 34) = sp0 - 192) by exact Usp.
assert (Uv41 : bv_unsigned (ew E 41) = v) by exact Uv.
assert (F33 : ew E 33 = getr regsc 1) by exact Ex1.
assert (F34 : ew E 34 = getr regsc 2) by exact Ex2.
assert (F35 : ew E 35 = getr regsc 3) by exact Ex3.
assert (F36 : ew E 36 = getr regsc 4) by exact Ex4.
assert (F40 : ew E 40 = getr regsc 8) by exact Ex8.
assert (F41 : ew E 41 = w64 v) by exact Ex9.
assert (F51 : ew E 51 = getr regsc 19) by exact Ex19.
pose proof (TVMN_refl memc) as HMN.
paj_run_to_tok_x_inv (RUNTOIR memc) HS HJ SHOK HMN TV_SPAN TVO_LH_B.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
  lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ (xr 2) (sp0 - 192 - sp0')) end;
  [ reflexivity | cbn [ew]; rewrite ?Usp, ?Usp34; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]. apply awr_ok_nil. }
clear HF HG.
lazymatch type of HFr with
| frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 184 <= a < sp0 - 104) ->
    aview SEGS (w_H Wc) mB a = aview SEGS (w_H Wc) mA a)
  by (intros a Ha Hn; apply (tv_aview_of_frame Wc Ex rsx mA mB a HFr); [|exact Ha];
      intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Usp, ?Usp34, ?Uv, ?Uv41 in Hr; lia|]); destruct Hin);
  assert (KR : forall x : word, (bv_unsigned x < sp0 - 184 \/ sp0 - 104 <= bv_unsigned x) ->
    mrestrict (w_H Wc) mB x = mrestrict (w_H Wc) mA x)
  by (intros x Hx; apply HFr; intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Usp, ?Usp34, ?Uv, ?Uv41 in Hr; lia|]); destruct Hin)
end.
clear HFr.
prreg HS (1%bv : bv 5) P1; prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (18%bv : bv 5) P18; prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22; prreg HS (23%bv : bv 5) P23.
prreg HS (24%bv : bv 5) P24; prreg HS (25%bv : bv 5) P25; prreg HS (26%bv : bv 5) P26; prreg HS (27%bv : bv 5) P27.
pose proof (ts_region_nth (L := B_prog_listing) (PA := PI_prog_B) _ _ _ 0%nat _ HS eq_refl) as HR0;
  cbn [ms_mem restrict] in HR0.
pmkst HS.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  lazymatch goal with HJ0 : ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (HK Ex ssx msx _ _ HS ltac:(vm_compute; reflexivity) HJ0) end
end.
- unfold tvo_lregs, tv_mregs_B. repeat split.
  + rewrite P2. rewrite ?Ex2, ?F34. unfold w64. rewrite <- Hsp. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + rewrite P9. first [exact Ex9 | exact F41].
  + rewrite P18. apply (tv_shadow_word _ _ v); [exact Uv41 | exact Ub | lia].
  + rewrite P20, Uv41. reflexivity.
  + rewrite P23, Uv41. reflexivity.
  + rewrite P27, Uv41. apply (tv_shadow_word _ _ (v + 24)); [apply unsigned_lit_small; lia | exact Ub | lia].
  + rewrite P25. apply (tvo_slt_zero _ d Ud ltac:(lia)).
  + rewrite P3. rewrite ?Ex3, ?F35. exact H3.
  + rewrite P4. rewrite ?Ex4, ?F36. exact H4.
  + rewrite P8. rewrite ?Ex8, ?F40. exact H8.
  + rewrite P19. rewrite ?Ex19, ?F51. rewrite H12. exact H19.
  + rewrite P21. unfold w64. f_equal; try lia.
  + rewrite P22. apply (tvo_addw1 _ d Ud ltac:(lia)).
  + rewrite P24. unfold w64. f_equal; try lia.
  + rewrite P26. reflexivity.
- unfold tv_saved. split; [|split; [|split]].
  + intros j Hj. assert (Hj12 : Z.of_nat j <= 12) by lia.
    apply (ts_vm_av (w_H Wc) (w_H Wc) memc _ _ 8 _); [|exact (proj1 HSV j Hj)].
    intros i Hi. apply KP; lia.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 72 8%N TVO_BX_B HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; unfold TVO_BX_B in V;
    rewrite (tvo_U_off E 64 SHADOW_OFF 0 Ub ltac:(unfold SHADOW_OFF; lia)) in V;
    rewrite Z.add_0_r in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 72) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 16 8%N (SLit 0) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V;
    rewrite (tvo_U_lit E 0 ltac:(lia)) in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 16) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 24 8%N (SOff 13 0) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V;
    rewrite (tvo_U_off E 13 d 0 Ud ltac:(lia)) in V; rewrite Z.add_0_r in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 24) by lia end; exact V.
- unfold tv_spill. repeat split.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 8 8%N (SLit 3) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite (tvo_U_lit E 3 ltac:(lia)) in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 8) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 32 8%N (SOff (A_OBJ 2) 70272) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite (tvo_U_off E (A_OBJ 2) (VAL (A_OBJ 2)) 70272 Uo2 ltac:(lia)) in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 32) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 40 8%N (SOff (A_OBJ 2) 70240) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite (tvo_U_off E (A_OBJ 2) (VAL (A_OBJ 2)) 70240 Uo2 ltac:(lia)) in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 40) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 48 8%N (tvo_sh_B (SOff (xr 9) 32)) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite (tvo_U_sh E (xr 9) v 32 Uv Ub ltac:(lia) ltac:(lia) ltac:(lia)) in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 48) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 56 8%N (SOff (xr 9) 32) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite (tvo_U_off E (xr 9) v 32 Uv ltac:(lia)) in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 56) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 64 8%N (SOff (A_OBJ 2) 70208) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite (tvo_U_off E (A_OBJ 2) (VAL (A_OBJ 2)) 70208 Uo2 ltac:(lia)) in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 64) by lia end; exact V.
  + let V := fresh "V" in
    pose proof (ts_field (L := B_prog_listing) (PA := PI_prog_B) _ _ _ _ _ _ _ _ _ 80 8%N (tvo_sh_B (SOff (xr 9) 40)) HR0 Usp
      ltac:(cbn [In]; repeat first [left; reflexivity | right]) ltac:(cbn; lia)) as V;
    cbn [N.to_nat] in V; change (8 * Z.of_N 8) with 64 in V; rewrite (tvo_U_sh E (xr 9) v 40 Uv Ub ltac:(lia) ltac:(lia) ltac:(lia)) in V;
    lazymatch goal with |- val_mem _ _ ?a _ _ => replace a with (sp0 - 192 + 80) by lia end; exact V.
- exact KP.
- exact KR.
- exact HMN.
Qed.



(* ==== THE CLOSING TAIL CALL and the live-state helpers (B twin of S10TxValue.v 339382e2cb0: tv_post_trans,
   tv_apresent_av, tv_apresent_of_aview, tv_live_present, tv_achain_re, tv_tail_close, tv_live_same, tv_lit_src_at,
   tv_fields_now) at frame 192 ==== *)
(* ==== THE CLOSING TAIL CALL from a live state ==== *)
(* the record's post from the entry composed with a callee's post from a later state at the same sp *)
Lemma tv_post_trans : forall lyc Sc Hpc (Wc : world SEGS) memc ly2 S2 Hp2 (W2 : world SEGS) mem2 regsc b capc fc b2 len2
  cap2 f2 txt2 lenc txtc,
  prhtx_post (PA := PA) B Lam regs dw ly S Hp lyc Sc Hpc Wc memc t b0 cap0 b lenc capc fc txtc ->
  prhtx_post (PA := PA) B Lam regsc dw lyc Sc Hpc ly2 S2 Hp2 W2 mem2 t b capc b2 len2 cap2 f2 txt2 ->
  spZ regsc = sp0 ->
  prhtx_post (PA := PA) B Lam regs dw ly S Hp ly2 S2 Hp2 W2 mem2 t b0 cap0 b2 len2 cap2 f2 txt2.
Proof.
intros lyc Sc Hpc Wc memc ly2 S2 Hp2 W2 mem2 regsc b capc fc b2 len2 cap2 f2 txt2 lenc txtc
  (_ & _ & _ & HHp1 & Hgr1 & Hbb1) (Hrec2 & Hinv2 & (H8 & Hlo & Hhi & Hw & Hra) & HHp2 & Hgr2 & Hbb2) Hsp.
split; [exact Hrec2|]. split; [exact Hinv2|].
split; [split; [exact H8|]; split; [rewrite <- Hsp; exact Hlo|]; split; [rewrite <- Hsp; exact Hhi|];
  split; [exact Hw | exact Hra]|].
split; [rewrite HHp2; exact HHp1|].
split; [exact (prhtx_grow_trans B ly S lyc Sc ly2 S2 b0 cap0 b capc b2 cap2 Hgr1 Hgr2) | lia].
Qed.

(* a present stack byte stays present when its view is kept *)
Lemma tv_apresent_av : forall (W1 W2 : world SEGS) m1 m2 a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a -> apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a.
Proof.
intros W1 W2 m1 m2 a Ha Hn E (Hh & bb & Hb).
pose proof (tv_client_av2 (w_H W1) (w_H W2) m1 m2 a Ha Hn E) as M. unfold mrestrict in M. rewrite Hh, Hb in M.
destruct (w_H W2 (Z_to_bv 64 a)) eqn:Eh; [discriminate M|]. split; [exact Eh | exists bb; exact M].
Qed.
(* a present byte of the view is present *)
Lemma tv_apresent_of_aview : forall (Wc : world SEGS) memc a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS (w_H Wc) memc a <> None -> apresent (w_H Wc) memc a.
Proof.
intros Wc memc a Ha Hn E. unfold aview, mbyte in E. rewrite (seg_rom_none SEGS a Ha Hn) in E.
unfold mrestrict in E. destruct (w_H Wc (Z_to_bv 64 a)) eqn:Eh; [cbn in E; congruence|].
destruct (memc (Z_to_bv 64 a)) as [bb|] eqn:Em; [|cbn in E; congruence]. split; [exact Eh | exists bb; exact Em].
Qed.

(* the stack above sp0 is present at every live state after the opening call: the window (kept outside FP0, the record
   present) and the trace region above t - 16 *)
Lemma tv_live_present : forall lyc Sc Hpc Wc memc mdc kj b P, tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P ->
  forall a, sp0 <= a < ly_top lyc -> aview SEGS (w_H Wc) memc a <> None.
Proof.
intros lyc Sc Hpc Wc memc mdc kj b P (HJ & HWIN & HTX & _) a Ha.
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & Hdpres).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
pose proof (ajxR_ly HJ) as HLYc.
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HTX as (cx & fcx & owx & prx & ((_ & _ & _ & _ & _ & Htr & _) & _)).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
destruct (Z_le_gt_dec (t - 16) a) as [H1|H1].
- destruct Htr as [HPr _]; [lia|]. exact (HPr a ltac:(rewrite Etop; lia)).
- rewrite (HWIN a ltac:(lia)).
  + apply s10_aview_present. apply Hdpres. lia.
  + intros Hf. destruct (s10_fp_cases _ _ _ _ Hf) as [Hr | (Hc0 & Hb)]; [lia|].
    destruct HINV as (_ & [(Hz & _) | (_ & _ & _ & _ & _ & Hceil' & _)]); [lia|].
    unfold req_size in Hb. destruct (Z.eqb_spec cap0 0); lia.
Qed.

(* a fresh frame chain from the entry's s0 at a live state *)
Lemma tv_achain_re : forall lyc (Wc : world SEGS) memc vv chx,
  achain ly (aview SEGS (w_H W) mem) sp0 vv chx -> ly_top lyc = ly_top ly ->
  (forall a, sp0 <= a < ly_top lyc -> aview SEGS (w_H Wc) memc a <> None) ->
  exists ch1, achain lyc (aview SEGS (w_H Wc) memc) sp0 vv ch1.
Proof.
intros lyc Wc memc vv chx [(Hbad & ->) | (H1 & H2 & H3 & _ & _)] Etop HP.
- exists []. left. rewrite Etop. split; [exact Hbad | reflexivity].
- pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & _) & _).
  pose proof asan_consts as (C1 & _).
  destruct (s10_achain_at lyc Wc memc sp0 vv ltac:(intros a Ha; apply HP; lia) H3 H1 ltac:(rewrite Etop; exact H2)
    ltac:(lia)) as (ch1 & Hc). exists ch1. exact Hc.
Qed.

(* ---- `j tx_put` closing the bracket, from the live state after the pieces P; P ++ [srcl] is the whole text. The tail
   callee's entry position is the live state's (rp_i + j, its tx_pos); its GROW premise comes from the text's guarded run
   premise cut at P (tx_window, tx_put_ev), its guarded room and consumer window from the text's own the same way
   (tx_room_window, tx_cons_window, rest = []); its post (three arms, DEAD, two position conjuncts) is read back by
   tx_put_res and folded with the live state's outcome, DEAD and position (tx_out_fold, tx_pos_fold) and record post
   (tv_post_trans). The live journal (at WR) is unbased at tv_tx's budget WS0 (YCbqGwild.ajournal_xw_unbase0R) for
   s10_tail_WbmR at WR, whose claim at WS0 ++ WS1 is tx_budget_fold of tv_tx's budget and the callee's (no abort
   arm) ---- *)
Lemma tv_tail_close : forall (Wc : world SEGS) E' ss' ms' mdc lyc Sc Hpc kj b P srcp srcl,
  st_ok SEGS E' ss' (restrict (w_H Wc) ms') -> ss_resv ss' = None ->
  ms' = mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_put)) (ms_mem ms') (seg_rom SEGS) ->
  tv_liveR WR lyc Sc Hpc Wc (ms_mem ms') mdc kj b P ->
  spZ (ms_regs ms') = sp0 -> aregs_preserved regs (ms_regs ms') ->
  getr (ms_regs ms') 1 = getr regs 1 -> getr (ms_regs ms') 3 = getr regs 3 -> getr (ms_regs ms') 4 = getr regs 4 ->
  getr (ms_regs ms') 10 = w64 t -> getr (ms_regs ms') 11 = w64 srcp ->
  getr (ms_regs ms') 12 = w64 (Z.of_nat (length srcl)) ->
  src_rd Wc (ms_mem ms') srcp srcl -> prhtx_kept B Lam lyc Sc srcp (Z.of_nat (length srcl)) ->
  (forall a, srcp <= a < srcp + Z.of_nat (length srcl) -> ~ (t <= a < t + 28) /\
     forall bb cb, In (bb, cb) (ablocks B lyc Sc) -> ~ (bb <= a < bb + cb)) ->
  P ++ [srcl] = TxModel.tvp tv PP d ->
  SRW Wc (mkCfg ms' mdc) QF.
Proof.
intros Wc E' ss' ms' mdc lyc Sc Hpc kj b P srcp srcl HS Hrv Hms HL Hsp HP R1 R3 R4 R10 R11 R12 HSRC HKEPT Hdisj EP.
pose proof HL as (HJ & HWIN & (cap & fc & ow & pre & (HTX0 & (j & histc & Hj & HPOSc) & HMNc & HDEAD & (WS0 & HWI & HWB)))
  & HRO & HFK & HRAc & HBVc & HSV).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & Hdpres).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc.
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Eshi & _).
pose proof HTX0 as (Ht0 & Ht47 & Hks & HPOST0 & HO & Htr & Hroom & Hled).
pose proof HPOST0 as (Hrec & Hinv & Hpl & HHp & Hgr & Hbb).
pose proof (tx_out_len _ _ _ _ _ _ _ _ _ _ _ HO) as Hplen.
set (lenc := len0 + Z.of_nat (length pre)) in *.
set (n := Z.of_nat (length srcl)) in *.
assert (EADD : concat P ++ srcl = ADD).
{ rewrite <- s10v_tvp_wv, <- EP, concat_app. cbn [concat]. rewrite app_nil_r. reflexivity. }
assert (ELEN : lenc + n <= len0 + Z.of_nat (length ADD)) by (rewrite <- EADD, length_app; unfold lenc, n; lia).
assert (EKS : KS = TxModel.plen P ++ [n]) by (unfold TxModel.tv_calls; rewrite <- EP, tv_plen_app; reflexivity).
assert (HPRES : forall a, sp0 <= a < ly_top lyc -> aview SEGS (w_H Wc) (ms_mem ms') a <> None)
  by exact (tv_live_present lyc Sc Hpc Wc (ms_mem ms') mdc kj b P HL).
destruct (tv_achain_re lyc Wc (ms_mem ms') (s0Z regs) ch Hch Etop HPRES) as (ch1 & Hch1).
assert (Hs0 : s0Z (ms_regs ms') = s0Z regs) by (unfold s0Z; rewrite (tv_ap regs (ms_regs ms') HP 8%bv); [reflexivity|ts_cs]).
(* the callee's premises at the tail *)
assert (HFW : fwin lyc Wc (ms_regs ms') (ms_mem ms') dw).
{ split; [exact Hdw0|]. split; [exact Hdw16|]. split; [rewrite Hsp, Etop; exact Hdtop|].
  intros a Ha. rewrite Hsp in Ha. apply tv_apresent_of_aview; [lia| |apply HPRES; rewrite Etop; lia].
  intros Hi. pose proof (@pa_segs_low _ _ PA a Hi). lia. }
assert (HPL : prhtx_place lyc Sc Wc (ms_regs ms') (ms_mem ms') dw t).
{ destruct Hpl as (P8 & Plo & Phi & Pw & Pra). split; [exact P8|]. split; [rewrite Hsp; exact Plo|].
  split; [rewrite Hsp; exact Phi|]. split; [exact Pw | exact Pra]. }
assert (HSHI : spZ (ms_regs ms') + 64 <= ly_stk_hi lyc) by (rewrite Hsp, Eshi; exact HHI).
assert (HRAc' : raZ (ms_regs ms') < YM05.alloc_ceiling) by (unfold raZ; rewrite R1; exact HRAC).
assert (Hdisj' : forall a, srcp <= a < srcp + n -> ~ (t <= a < t + 28) /\ ~ (b <= a < b + cap)).
{ intros a Ha. destruct (Hdisj a Ha) as [H1 H2]. split; [exact H1|]. intros Hb.
  destruct Hinv as (_ & [(Hz & _) | (_ & _ & Hin & _)]); [lia | exact (H2 b cap Hin Hb)]. }
assert (HEV : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 (TxModel.plen P ++ [n] ++ []))).
{ intros Hf. rewrite app_nil_r, <- EKS. exact (HEVS Hf). }
pose proof (tx_window rp_sm rp_x rp_os rp_i j len0 cap0 f0 fc own ow b0 b cap (TxModel.plen P) (concat P) pre [n] []
  HO Hj Hks HEV) as HWQ.
assert (HRW0 : f0 = 0 ->
  YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 (TxModel.plen P ++ [n] ++ []))) (st_depot S)).
{ intros Hf. rewrite app_nil_r, <- EKS. exact (HROOMW Hf). }
assert (HCF0 : f0 = 0 ->
  prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 (TxModel.plen P ++ [n] ++ [])))).
{ intros Hf. rewrite app_nil_r, <- EKS. exact (HCONS Hf). }
pose proof (tx_room_window (as_universe B) (st_depot S) (st_depot Sc) WS0 len0 cap0 f0 fc own ow b0 b cap
  (TxModel.plen P) (concat P) pre [n] [] HO Hks HRW0 HWI HWB) as HROOMc.
pose proof (tx_cons_window rp_sm rp_x rp_os rp_i j len0 cap0 f0 fc own ow b0 b cap (TxModel.plen P) (concat P) pre
  [n] [] HO Hj Hks HCF0) as HCONSc.
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B PST ARx _ _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWI)
  as HJW.
eapply SRr'_mono.
{ eapply (s10_tail_WbmR B ARx SK LAWS WR (wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E' ss' ms' STKV dw sp0 FP0 ly S Hp W
    mem md lyc Sc Hpc mdc kj WS0 (@STK_tx_put prh_img_B) (prhtx_fp t b cap) ch1 regs
    (wbudget_if f0 [] (length (prhtx_evs len0 cap0 KS))) _ _ _
    HS Hrv HJW eq_refl Hsp SK0 ltac:(lia) Hdw0 Hdw16 HP R1 Hra Hra4 ltac:(rewrite R3; exact Hgp)
    ltac:(rewrite R4; exact Htp) ltac:(rewrite Hs0; exact Hch1)).
  - intros HPRE1.
    replace (mkst (ms_regs ms') (Z_to_bv 64 (ss_pc ss')) (ms_mem ms') (seg_rom SEGS))
      with (mkst (ms_regs ms') (Z_to_bv 64 (SIGMA AS_tx_put)) (ms_mem ms') (seg_rom SEGS))
      by (rewrite <- (st_ok_restrict_mkst SEGS (w_H Wc) E' ss' ms' HS Hrv); first [exact Hms | symmetry; exact Hms]).
    exact (TXPUT rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc lyc Sc Hpc Wc (ms_regs ms') (ms_mem ms') mdc ch1 dw t srcp n b
      lenc cap fc ow (txt ++ pre) srcl Lam peak cnt fail ran most
      (conj HPRE1 (conj HRO (conj HSHI (conj HRAc' HFRM)))) HCLO Hroom HPOSc HRP4 HROOMc HCONSc R10 R11 R12 HFW HPL
      Htr Hrec Hinv HSRC eq_refl HKEPT Hdisj' ltac:(lia) Hled
      (fun Hf Hlt => tx_put_ev rp_sm rp_x rp_os (rp_i + j)%nat lenc cap n fc HWQ Hf Hlt) ltac:(lia) ltac:(lia)).
  - unfold fp_sub_x. intros a Ha.
    destruct (tx_state_fp B ARx LAWS Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b cap fc ow
      (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc (ms_mem ms') mdc HTX0 HARc a Ha) as [H1|H1]; [left | right; left]; exact H1.
  - intros a Ha Hf. exact (tx_state_fp_win B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own b cap fc
      ow (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc (ms_mem ms') HTX0 a ltac:(lia) Hf).
  - exact HWIN.
  - intros WS1 HWB1. rewrite EKS.
    exact (tx_budget_fold len0 cap0 f0 fc own ow b0 b cap (TxModel.plen P) (concat P) pre [n] WS0 WS1 HO Hks HDEAD
      HWB HWB1).
  - intros ly' S' Hp' W' regs' mem' md' H. exact H.
  - exact HMNc. }
cbv beta. intros W2 c2 _ HN. unfold QF.
destruct HN as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & WS2 & Hc2 & HPW & HJ2 & HW2 & HP2
  & ((b1 & cap1 & f1 & ow1 & pre1 & HPOST & HARMS & HDEAD1 & _ & HRM & HG & HNG & HLED2) & HMN2)).
destruct (tx_put_res rp_sm rp_x rp_os (rp_i + j)%nat rp_H0 histc S2 lenc cap fc f1 ow ow1 b b1 cap1 n srcl pre1 _
  HARMS HG HNG) as (HOUTq & jq & h2 & Hjq & HPOS2).
exists ly2, S2, Hp2, regs2, mem2, md2, k2, WS2. split; [exact Hc2|]. split; [exact HPW|]. split; [exact HJ2|].
split; [exact HW2|]. split; [exact HP2|]. split; [|exact HMN2].
apply (tv_qt ly2 S2 Hp2 W2 regs2 mem2 md2 k2 WS2 regs b1 cap1 f1 ow1 (pre ++ pre1) HJ2 eq_refl).
- rewrite length_app, app_assoc.
  replace (len0 + Z.of_nat (length pre + length pre1)) with (lenc + Z.of_nat (length pre1)) by (unfold lenc; lia).
  exact (tv_post_trans lyc Sc Hpc Wc (ms_mem ms') ly2 S2 Hp2 W2 mem2 (ms_regs ms') b cap fc b1 _ cap1 f1 _ lenc
    (txt ++ pre) HPOST0 HPOST Hsp).
- rewrite EKS, <- EADD.
  exact (tx_out_fold len0 cap0 f0 fc f1 own ow ow1 b0 b b1 cap cap1 (TxModel.plen P) [n] (concat P) srcl pre pre1
    Hks HO HOUTq).
- intros Hf0. exact (HDEAD1 (HDEAD Hf0)).
- exact HRM.
- rewrite EKS.
  exact (tx_pos_fold rp_sm rp_x rp_os rp_i rp_H0 len0 cap0 f0 fc f1 own ow ow1 b0 b b1 cap cap1 j jq h2 S2
    (TxModel.plen P) [n] (concat P) srcl pre pre1 Hks HO Hj HOUTq Hjq HPOS2).
- exact HLED2.
Qed.

(* the live state across one of the caller's own runs that wrote nothing (the memnorm keep from the entry memory to the
   run's end: the runs of a segment are anchored at mem, RUNIR mem); the run's journal is tv_liveR's at WR, REBASED (the
   batch) *)
Lemma tv_live_same : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' b P,
  tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P ->
  AJR (STKV + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [] lyc Sc Hpc Wc memc' mdc' kj' ->
  (forall x : word, rdW Wc memc' x = rdW Wc memc x) -> TVMN mem memc' ->
  tv_liveR WR lyc Sc Hpc Wc memc' mdc' kj' b P.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' b P
  (HJ & HWIN & (cap & fc & ow & pre & (HTX0 & HPS & _ & HDEAD & HWS)) & HRO & HFK & HRAc & HBVc & HSV) HJ' Hm HMNk.
assert (AV : forall a, aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a)
  by (intros a; unfold aview, mbyte; rewrite Hm; reflexivity).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & _) & _).
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc.
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Eshi & H47' & _).
split; [exact HJ'|]. split; [intros a Ha Hn; rewrite AV; exact (HWIN a Ha Hn)|].
split; [exists cap, fc, ow, pre; split; [|split; [exact HPS | split; [exact HMNk | split; [exact HDEAD | exact HWS]]]];
  apply (tx_state_keep B ARx LAWS S1ImgB.pst_in_img_B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own
  b cap fc ow (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc memc memc' mdc (sp0 - 192) (sp0 - 192) HTX0 HARc); [|lia|lia|];
  [rewrite Etop; pose proof HPRE as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2) & _); lia
  | intros x _; exact (Hm x)]|].
split; [intros a Hro Hno Her; rewrite AV; exact (HRO a Hro Hno Her)|].
split; [intros x Hx; rewrite AV; exact (HFK x Hx)|].
split; [eapply range_addressable_agree; [|exact HRAc]; intros x _; apply AV|].
split.
- rewrite Forall_forall in HBVc |- *. intros bk Hbk.
  destruct (HBVc bk Hbk) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
  split; [eapply range_addressable_agree; [|exact B6]; intros x _; apply AV|].
  split; [intros Hk s0 Hs0; rewrite AV; exact (B7 Hk s0 Hs0)|].
  intros a Ha. rewrite AV. exact (B8 a Ha).
- destruct HSV as (HS1 & HS2 & HS3 & HS4). split; [|split; [|split]].
  + intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc' _ 8 _); [|exact (HS1 j Hj)]. intros k Hk. apply AV.
  + apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc' _ 8 _); [|exact HS2]. intros k Hk. apply AV.
  + apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc' _ 8 _); [|exact HS3]. intros k Hk. apply AV.
  + apply (ts_vm_av (w_H Wc) (w_H Wc) memc memc' _ 8 _); [|exact HS4]. intros k Hk. apply AV.
Qed.

(* a read-only literal handed to tx_put at a later state: kept, and apart from the record and from every live block *)
Lemma tv_lit_src_at : forall lyc Sc Hpc (Wc : world SEGS) memc mdc lo src,
  ARx lyc Sc Hpc Wc memc mdc -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) ->
  In (lo, Z.of_nat (length src)) [(69472, 4); (69504, 5); (69536, 4); (70144, 1); (70176, 1); (70208, 1); (70240, 1);
    (70272, 1); (70304, 1); (70336, 1)] -> (0 < length src)%nat ->
  (forall j, (j < length src)%nat -> option_map (fun bb : byte => bv_unsigned bb)
     (seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + lo + Z.of_nat j))) = Some (nth j src 0)) ->
  src_rd Wc memc (VAL (A_OBJ 2) + lo) src /\ prhtx_kept B Lam lyc Sc (VAL (A_OBJ 2) + lo) (Z.of_nat (length src)) /\
  (forall a, VAL (A_OBJ 2) + lo <= a < VAL (A_OBJ 2) + lo + Z.of_nat (length src) ->
     ~ (t <= a < t + 28) /\ forall bb cb, In (bb, cb) (ablocks B lyc Sc) -> ~ (bb <= a < bb + cb)).
Proof.
intros lyc Sc Hpc Wc memc mdc lo src HARc HRODc Hin Hn Hrom.
pose proof (proj1 (Forall_forall _ _) tv_lit_img _ Hin) as Hki. cbn [fst snd] in Hki.
destruct (s10_src_img B ARx LAWS zs_aligned img_shadow_vis_x BTxLine.tl_img_box tv_img_cf_box lyc Sc Hpc Wc memc mdc
  Lam _ src HARc HRODc Hki Hn Hrom)
  as [HSRC HKEPT].
split; [exact HSRC|]. split; [exact HKEPT|].
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof HPLACE as (_ & Htlo & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof BTxLine.tl_img_box as (Hib1 & Hib2).
intros a Ha. destruct Hki as (Hlo & Hhi & Hro).
split; [lia|]. intros bb cb Hinb Hb.
apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc bb cb a HARc Hinb).
- unfold req_size. destruct (Z.eqb_spec cb 0); lia.
- destruct (Hro a Ha) as (Hr & _).
  destruct Hr as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* the node's fields at a live state after the opening call (its bytes are the entry's) *)
Lemma tv_fields_now : forall lyc Sc Hpc Wc memc mdc kj b P ty0 num0 str0 kids0 keys0 n0 cap1,
  tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P ->
  PRH_Reader.pj_hdrR SEGS (rdW W mem) v ty0 num0 str0 kids0 keys0 n0 cap1 ->
  (0 <= ty0 < 2 ^ 32 /\ val_mem SEGS (rdW Wc memc) v 4 ty0) /\
  (0 <= kids0 < 2 ^ 64 /\ val_mem SEGS (rdW Wc memc) (v + 24) 8 kids0) /\
  (0 <= keys0 < 2 ^ 64 /\ val_mem SEGS (rdW Wc memc) (v + 32) 8 keys0) /\
  (0 <= n0 < 2 ^ 64 /\ val_mem SEGS (rdW Wc memc) (v + 40) 8 n0).
Proof.
intros lyc Sc Hpc Wc memc mdc kj b P ty0 num0 str0 kids0 keys0 n0 cap1 (_ & _ & _ & _ & HFK & _)
  (_ & (Rt & Vt) & _ & _ & (Rk & Vk) & (Ry & Vy) & (Rn & Vn) & _).
assert (KV : forall o k, 0 <= o -> o + Z.of_nat k <= 56 -> forall val, val_mem SEGS (rdW W mem) (v + o) k val ->
  val_mem SEGS (rdW Wc memc) (v + o) k val).
{ intros o k Ho Hk val V. apply (ts_vm_av (w_H W) (w_H Wc) mem memc _ k _); [|exact V].
  intros j Hj. apply HFK. left. lia. }
split; [split; [exact Rt | apply (ts_vm_av (w_H W) (w_H Wc) mem memc v 4 ty0); [|exact Vt];
  intros j Hj; apply HFK; left; lia]|].
split; [split; [exact Rk | apply KV; [lia|cbn;lia|exact Vk]]|].
split; [split; [exact Ry | apply KV; [lia|cbn;lia|exact Vy]]|].
split; [exact Rn | apply KV; [lia|cbn;lia|exact Vn]].
Qed.


(* ==== THE BASE STATE X (after the closing tx_line, B 0x85704) from concrete facts (B twin of S10's tv_B_entry, w =
   false: the dispatch's words and the saves, all read-only) ==== *)
(* the base registers: sp, s1 = v, s2 = the shadow of v, gp, tp, s0 = t *)
Definition tv_bregs_B (rg : bvmap 5 word) : Prop :=
  getr rg 2 = w64 (sp0 - 192) /\ getr rg 9 = w64 v /\ getr rg 18 = w64 (shadow_addr v) /\
  getr rg 3 = getr regs 3 /\ getr rg 4 = getr regs 4 /\ getr rg 8 = w64 t.
Lemma tv_X_entry_B : forall pc ty rg (Wc : world SEGS) memc kids keys n,
  tv_bregs_B rg -> tv_saved Wc memc ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS (rdW Wc memc) v 4 ty ->
  0 <= kids < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 24) 8 kids ->
  0 <= keys < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 32) 8 keys ->
  0 <= n < 2 ^ 64 -> val_mem SEGS (rdW Wc memc) (v + 40) 8 n ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF v 56 ->
  st_ok_pi SEGS VAL (TE regs rg (tvo_more false kids keys n 0 0)) (ss_X_B pc ty)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS TVO_BX_B (tvo_SH_B false) (TE regs rg (tvo_more false kids keys n 0 0)) (rdW Wc memc).
Proof.
intros pc ty rg Wc memc kids keys n (R2 & R9 & R18 & _) (HSV & H72 & H16 & H24)
  Hty Vty Hkd Vkd Hky Vky Hn Vn HRAv.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof (Nat2Z.is_nonneg nn) as Hnn0.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
set (E := TE regs rg (tvo_more false kids keys n 0 0)).
assert (X2 : bv_unsigned (ew E (xr 2)) = sp0 - 192).
{ unfold E, xr. rewrite (te_cur regs rg _ 2%bv 2) by reflexivity. rewrite R2. apply unsigned_lit_small. lia. }
assert (X9 : bv_unsigned (ew E (xr 9)) = v).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X64 : bv_unsigned (ew E 64) = SHADOW_OFF).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth app]. apply unsigned_lit_small.
  unfold SHADOW_OFF; lia. }
assert (X65 : bv_unsigned (ew E 65) = kids).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 1) by lia. cbn [nth app]. apply unsigned_lit_small. lia. }
assert (X66 : bv_unsigned (ew E 66) = keys).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 2) by lia. cbn [nth app]. apply unsigned_lit_small. lia. }
assert (X67 : bv_unsigned (ew E 67) = n).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 3) by lia. cbn [nth app]. apply unsigned_lit_small. lia. }
assert (XE : forall (r : bv 5) k, Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros r k Hk; unfold E; exact (te_entry regs rg _ r k Hk)).
assert (X13 : sv_denot E (SOff 13 0) = Z_to_bv 64 d).
{ apply bv_eq. rewrite denot_SOff, (XE 13%bv 13%nat) by reflexivity. rewrite H13, Z.add_0_r.
  unfold w64. rewrite !unsigned_lit_small by lia. apply YP0m.zcanon_small. lia. }
assert (HFR : Forall (YP09.chunk_ok SEGS E (rdW Wc memc) (sp0 - 192)) (tvo_head_B ++ tvo_saves_B)).
{ unfold tvo_head_B, tvo_saves_B. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil.
  4-16: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?k 0))) =>
      let j := eval vm_compute in (Z.to_nat ((192 - off) / 8 - 1)) in
      let r := eval vm_compute in (nth j TV_SAVED 0%bv) in
      apply (ts_chunk E _ _ off 8 (SOff k 0) (bv_unsigned (getr regs r)));
      [ apply bv_eq; rewrite denot_SOff, (XE r k) by reflexivity; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
        apply YP0m.zcanon_small; exact (bv_unsigned_in_range 64 (getr regs r))
      | pose proof (bv_unsigned_in_range 64 (getr regs r)) as BR; change (bv_modulus 64) with (2 ^ 64) in BR; cbn; lia
      | cbn; lia
      | pose proof (HSV j ltac:(vm_compute; lia)) as V;
        replace (sp0 - 8 * (Z.of_nat j + 1)) with (sp0 - 192 + off) in V by (cbn; lia); exact V ]
    end.
  - apply (ts_chunk E _ _ 16 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 16) with (sp0 - 176) by lia. exact H16.
  - apply (ts_chunk E _ _ 24 8 (SOff 13 0) d); [exact X13 | cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 24) with (sp0 - 168) by lia. exact H24.
  - apply (ts_chunk E _ _ 72 8 TVO_BX_B SHADOW_OFF); [apply (tv_den_atom E 64 SHADOW_OFF X64); unfold SHADOW_OFF; lia
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    replace (sp0 - 192 + 72) with (sp0 - 120) by lia. exact H72. }
assert (HND : Forall (YP09.chunk_ok SEGS E (rdW Wc memc) v)
  [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 24 (CVal 8 (SOff 65 0)); YP09.mkChunk 32 (CVal 8 (SOff 66 0));
   YP09.mkChunk 40 (CVal 8 (SOff 67 0))]).
{ repeat apply Forall_cons; try apply Forall_nil.
  - apply (ts_chunk E _ _ 0 4 (SLit ty) ty); [reflexivity | cbn; lia | cbn; lia |]. rewrite Z.add_0_r. exact Vty.
  - apply (ts_chunk E _ _ 24 8 (SOff 65 0) kids); [apply (tv_den_atom E 65 kids X65); lia | cbn; lia | cbn; lia | exact Vkd].
  - apply (ts_chunk E _ _ 32 8 (SOff 66 0) keys); [apply (tv_den_atom E 66 keys X66); lia | cbn; lia | cbn; lia | exact Vky].
  - apply (ts_chunk E _ _ 40 8 (SOff 67 0) n); [apply (tv_den_atom E 67 n X67); lia | cbn; lia | cbn; lia | exact Vn]. }
split.
- apply ts_st_ok.
  all: try change (TE regs rg (tvo_more false kids keys n 0 0)) with E.
  + apply tv_regs_ok_set; [|reflexivity|rewrite R18; symmetry; replace (shadow_addr v) with (shadow_addr (v + 0))
      by (rewrite Z.add_0_r; reflexivity); apply (tvo_sh_val E (xr 9) v 0 X9 X64); lia].
    apply te_regs_ok.
  + vm_compute. reflexivity.
  + cbn [ss_mem ss_X_B]. repeat apply Forall_cons; try apply Forall_nil.
    * apply (ts_rok E _ (xr 2) (sp0 - 192)); [exact X2 | lia | lia | intros o Ho; lia | exact HFR].
    * apply (ts_rok E _ (xr 9) v); [exact X9 | lia | lia | intros o Ho; lia | exact HND].
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, ss_X_B, tvo_node_B.
    cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite !ts_bv_some. rewrite X2, X9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I].
    cbn [ss_facts ss_X_B f_atoms atoms_ok tvo_atoms_B]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X2, X9, X64.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; try lia. all: rewrite Zminus_mod, Hal16; reflexivity.
- unfold sh_ok, tvo_SH_B. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E TVO_BX_B (xr 9) v 56 v 0 56); [exact HRAv | | | lia | lia |].
  + unfold TVO_BX_B, U. rewrite (tv_den_atom E 64 SHADOW_OFF X64) by (unfold SHADOW_OFF; lia).
    apply unsigned_lit_small. unfold SHADOW_OFF; lia.
  + unfold U. rewrite (tv_den_atom E (xr 9) v X9) by lia. apply unsigned_lit_small. lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ==== THE LOOP's helpers at image B (B twin of S10TxValue.v 37251f6b9a5: tv_SEG, tv_kont_seg, tv_mregs_ok,
   tv_lregs_sym, tv_lregs_step, tv_bregs_sym, tv_bregs_pres, tv_reg_off, tv_lam_low, tv_t_high; B's loop registers
   s5 = 56 i, s8 = 8 i, s10 = i and B's frame of 192) ==== *)
(* a call's continuation to the loop segment at offset pc, after the pieces P, at item i *)
Definition tvo_SEG (P : list (list Z)) (pc i : Z) : Prop :=
  forall lyc Sc Hpc Wc memc mdc kj b rg, tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P -> tv_spill Wc memc -> tvo_lregs rg i ->
    SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) QF.
Lemma tvo_kont_seg : forall Wc ms Q P pc i, tvo_SEG (P ++ Q) pc i ->
  tv_spill Wc (ms_mem ms) -> tvo_lregs (ms_regs ms) i -> getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + pc) ->
  tv_kont Wc ms Q P.
Proof.
intros Wc ms Q P pc i HSEG HSP HLR R1 ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 HL2 Kfr HP. rewrite R1.
apply (HSEG ly2 S2 Hp2 W2 mem2 md2 kj2 b2 regs2 HL2).
- exact (proj2 (tv_frame_keep _ _ _ _ Kfr) HSP).
- exact (tvo_lregs_pres _ _ i HLR HP).
Qed.

(* the loop states' registers are their symbolic registers tvo_mregs_B *)
Lemma tvo_mregs_ok : forall rg obj kd ky nx ix kp, tv_mregs_B rg ->
  regs_ok (TE regs rg (tvo_more obj kd ky nx ix kp)) tvo_mregs_B rg.
Proof.
intros rg obj kd ky nx ix kp (R2 & R9 & R18 & R20 & R23 & R27 & R25).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_lt as Hc47.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
set (E := TE regs rg (tvo_more obj kd ky nx ix kp)).
assert (X9 : bv_unsigned (ew E (xr 9)) = v).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X64 : bv_unsigned (ew E 64) = SHADOW_OFF).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth app]. apply unsigned_lit_small.
  unfold SHADOW_OFF; lia. }
unfold tvo_mregs_B.
apply tv_regs_ok_set; [|reflexivity|rewrite R25; reflexivity].
apply tv_regs_ok_set; [|reflexivity|rewrite R27; symmetry; apply (tvo_sh_val E (xr 9) v 24 X9 X64); lia].
apply tv_regs_ok_set; [|reflexivity|rewrite R23; symmetry; apply (tv_den_off E (xr 9) 24 v X9); lia].
apply tv_regs_ok_set; [|reflexivity|rewrite R20; symmetry; apply (tv_den_off E (xr 9) 40 v X9); lia].
apply tv_regs_ok_set; [|reflexivity|rewrite R18; symmetry; replace (shadow_addr v) with (shadow_addr (v + 0))
  by (rewrite Z.add_0_r; reflexivity); apply (tvo_sh_val E (xr 9) v 0 X9 X64); lia].
apply te_regs_ok.
Qed.

(* a run that kept the loop registers (their symbolic values are tvo_mregs_B's) keeps tvo_lregs *)
Definition TVO_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma tvo_lregs_sym : forall (H : word -> bool) obj kd ky nx i0 kp ss ms rg i,
  st_ok SEGS (TE regs rg (tvo_more obj kd ky nx i0 kp)) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (sr_get tvo_mregs_B r)) TVO_KEPT = true ->
  tvo_lregs rg i -> tvo_lregs (ms_regs ms) i.
Proof.
intros H obj kd ky nx i0 kp ss ms rg i HS Hf HLR. rewrite forallb_forall in Hf.
pose proof (tvo_mregs_ok rg obj kd ky nx i0 kp (proj1 HLR)) as HOK.
assert (K : forall r : bv 5, In r TVO_KEPT -> getr (ms_regs ms) r = getr rg r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), (sv_eqb_eq _ _ (Hf r Hr)). symmetry. exact (HOK r). }
unfold tvo_lregs, tv_mregs_B in *.
rewrite !K by (unfold TVO_KEPT; repeat (first [left; reflexivity | right])). exact HLR.
Qed.

(* the loop registers after the step `addi s10,s10,1; addi s8,s8,8; addi s5,s5,56` (B 0x856c8 .. 0x856d0) *)
Definition TVO_KEPT2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 27]%bv.
Lemma tvo_lregs_step : forall (H : word -> bool) obj kd ky nx i0 kp ss ms rg i,
  st_ok SEGS (TE regs rg (tvo_more obj kd ky nx i0 kp)) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (sr_get tvo_mregs_B r)) TVO_KEPT2 = true ->
  tvo_lregs rg i -> getr (ms_regs ms) 21 = w64 (56 * (i + 1)) -> getr (ms_regs ms) 24 = w64 (8 * (i + 1)) ->
  getr (ms_regs ms) 26 = w64 (i + 1) -> tvo_lregs (ms_regs ms) (i + 1).
Proof.
intros H obj kd ky nx i0 kp ss ms rg i HS Hf HLR R21' R24' R26'. rewrite forallb_forall in Hf.
pose proof (tvo_mregs_ok rg obj kd ky nx i0 kp (proj1 HLR)) as HOK.
assert (K : forall r : bv 5, In r TVO_KEPT2 -> getr (ms_regs ms) r = getr rg r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), (sv_eqb_eq _ _ (Hf r Hr)). symmetry. exact (HOK r). }
destruct HLR as ((R2 & R9 & R18 & R20 & R23 & R27 & R25) & R3 & R4 & R8 & R19 & _ & R22 & _ & _).
unfold tvo_lregs, tv_mregs_B. rewrite R21', R24', R26'.
rewrite !K by (unfold TVO_KEPT2; repeat (first [left; reflexivity | right])).
repeat split; first [reflexivity | assumption].
Qed.

(* the base registers of X (tv_bregs_B) from a loop state's run, and across a call *)
Definition TVO_KEPTB : list (bv 5) := [2; 3; 4; 8; 9; 18]%bv.
Lemma tvo_bregs_sym : forall (H : word -> bool) obj kd ky nx i0 kp ss ms rg i,
  st_ok SEGS (TE regs rg (tvo_more obj kd ky nx i0 kp)) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (sr_get tvo_mregs_B r)) TVO_KEPTB = true ->
  tvo_lregs rg i -> tv_bregs_B (ms_regs ms).
Proof.
intros H obj kd ky nx i0 kp ss ms rg i HS Hf HLR. rewrite forallb_forall in Hf.
pose proof (tvo_mregs_ok rg obj kd ky nx i0 kp (proj1 HLR)) as HOK.
assert (K : forall r : bv 5, In r TVO_KEPTB -> getr (ms_regs ms) r = getr rg r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), (sv_eqb_eq _ _ (Hf r Hr)). symmetry. exact (HOK r). }
destruct HLR as ((R2 & R9 & R18 & _) & R3 & R4 & R8 & _).
unfold tv_bregs_B. rewrite !K by (unfold TVO_KEPTB; repeat (first [left; reflexivity | right])).
repeat split; assumption.
Qed.
Lemma tv_bregs_B_pres : forall rg rg', tv_bregs_B rg -> aregs_preserved rg rg' -> tv_bregs_B rg'.
Proof.
intros rg rg' (R2 & R9 & R18 & R3 & R4 & R8) HP. unfold tv_bregs_B.
rewrite (tv_ap rg rg' HP 2%bv) by ts_cs. rewrite (tv_ap rg rg' HP 9%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 18%bv) by ts_cs. rewrite (tv_ap rg rg' HP 3%bv) by ts_cs.
rewrite (tv_ap rg rg' HP 4%bv) by ts_cs. rewrite (tv_ap rg rg' HP 8%bv) by ts_cs.
repeat split; assumption.
Qed.

(* a register of the form `atom + k` *)
Lemma tv_reg_off : forall (rgs : bvmap 5 word) (r : bv 5) E n k x, getr rgs r = Z_to_bv 64 (bv_unsigned (ew E n) + k) ->
  ew E n = w64 x -> 0 <= x < 2 ^ 64 -> getr rgs r = w64 (x + k).
Proof. intros rgs r E n k x Q Ex Hx. rewrite Q, Ex. unfold w64. rewrite unsigned_lit_small by exact Hx. reflexivity. Qed.

(* a harness block lies below alloc_ceiling, so below the record *)
Lemma tv_lam_low : forall x k, In (x, k) Lam -> 4096 <= x /\ x + k <= YM05.alloc_ceiling /\ x mod 16 = 0 /\ in_app x k.
Proof.
intros x k Hin. pose proof HPRE as (HAR & _).
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran x k _ _ HLED Hin) as (Hk0 & Hab & _ & H16 & _).
change (@cf_head CfParams_preset) with 16 in Hab.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & Happ & _).
assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hrq in Hc, Happ. split; [lia|]. split; [lia|]. split; [exact H16|].
unfold in_app in *. lia.
Qed.
Lemma tv_t_high : YM05.alloc_ceiling + 16 <= t.
Proof.
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & _) & _).
pose proof HPLACE as (_ & Htlo & _). lia.
Qed.

(* a block's footprint facts move with its bytes' view; a node's facts move with the same memory *)
Lemma tv_bvis_av : forall (Wc : world SEGS) m m' x k, (forall a, aview SEGS (w_H Wc) m' a = aview SEGS (w_H Wc) m a) ->
  prhtx_bvis Wc m x k -> prhtx_bvis Wc m' x k.
Proof.
intros Wc m m' x k AV (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
split; [eapply range_addressable_agree; [|exact B6]; intros y _; apply AV|].
split; [intros Hk s0 Hs0; rewrite AV; exact (B7 Hk s0 Hs0)|].
intros a Ha. rewrite AV. exact (B8 a Ha).
Qed.
Lemma tv_node_same : forall (Wc : world SEGS) m m' p x Dx, (forall y, rdW Wc m' y = rdW Wc m y) ->
  PRH_Reader.pj_nodeR SEGS (rdW Wc m) (prh_lin Lam) p x Dx -> PRH_Reader.pj_nodeR SEGS (rdW Wc m') (prh_lin Lam) p x Dx.
Proof.
intros Wc m m' p x Dx Hm HN. apply (tv_nodeR_frame x _ _ _ p Dx HN). intros y _. split.
- unfold mbyte. rewrite Hm. reflexivity.
- intros Hw. unfold writable_at, wview in *. rewrite Hm. exact Hw.
Qed.

(* pretty's register test (s3 = pretty, a 32-bit int sign-extended) *)
Lemma tv_pretty_mod : pretty mod 2 ^ 64 = 0 <-> pretty = 0.
Proof.
split; [|intros ->; reflexivity]. intros H.
destruct (Z_le_gt_dec 0 pretty) as [h|h]; [rewrite Z.mod_small in H by lia; exact H|].
exfalso. rewrite <- (Z_mod_plus_full pretty 1) in H. rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma tv_pp_true : pretty <> 0 -> PP = true.
Proof. intros H. apply negb_true_iff, Z.eqb_neq. exact H. Qed.
Lemma tv_pp_false : pretty = 0 -> PP = false.
Proof. intros ->. reflexivity. Qed.

(* a 64-bit value below 2 ^ 63 is its own signed reading *)
Lemma tvo_swrap_small : forall x, 0 <= x < 2 ^ 63 -> bv_swrap 64 x = x.
Proof.
intros x Hx. unfold bv_swrap. change (bv_half_modulus 64) with 9223372036854775808.
unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
rewrite Z.mod_small by lia. lia.
Qed.
(* the values of UBSan's checks in the loop at i <= 2 ^ 42 (atoms 58 = s10 = i, 65 = kids): the index bound
   `srli a2,s10,0x3c` (B 0x855fc), the kid pointer kids + 56 i (B 0x8566c .. 0x85674) and the multiplication
   overflow test `mulh` / `srai` / `xor` / `snez` (B 0x85688 .. 0x85698) *)
Lemma tvo_U_srl60 : forall E i, U E (SOff 58 0) = i -> 0 <= i <= 2 ^ 42 ->
  U E (SAlu ALU_SRL (SOff 58 0) (SLit 60)) = U E (SLit 0).
Proof.
intros E i Hi Hr. rewrite U_SAlu, Hi, !U_SLit. cbn [zalu_raw].
replace (Z.land (zcanon 60) 63) with 60 by reflexivity.
rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small i) by lia. reflexivity.
Qed.
Lemma tvo_U_kid : forall E i kd, U E (SOff 58 0) = i -> U E (SOff 65 0) = kd -> 0 <= i <= 2 ^ 42 -> 0 <= kd <= 2 ^ 47 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 58 0) (SLit 56)) (SOff 65 0)) = 56 * i + kd.
Proof.
intros E i kd Hi Hk Hir Hkr. rewrite U_SAlu, U_SMd, Hi, Hk, U_SLit. cbn [zalu_raw zmd_raw].
replace (zcanon 56) with 56 by reflexivity.
unfold zcanon, M64. rewrite (Z.mod_small (i * 56)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma tvo_U_mulh : forall E i, U E (SOff 58 0) = i -> 0 <= i <= 2 ^ 42 ->
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 58 0) (SLit 56))
     (SAlu ALU_SRA (SMd M_MUL (SOff 58 0) (SLit 56)) (SLit 63)))) = U E (SLit 0).
Proof.
intros E i Hi Hr. rewrite !U_SAlu, !U_SMd, Hi, !U_SLit. cbn [zalu_raw zmd_raw].
replace (zcanon 56) with 56 by reflexivity. replace (zcanon 63) with 63 by reflexivity.
replace (zcanon 0) with 0 by reflexivity. replace (Z.land 63 63) with 63 by reflexivity.
rewrite (tvo_swrap_small i) by lia. rewrite (tvo_swrap_small 56) by lia.
assert (E1 : Z.shiftr (i * 56) (Z.of_N 64) = 0).
{ rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
assert (E2 : zcanon (i * 56) = i * 56) by (unfold zcanon, M64; apply Z.mod_small; lia).
rewrite E1, E2. rewrite (tvo_swrap_small (i * 56)) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (i * 56)) by lia.
reflexivity.
Qed.

(* ---- the base state X's registers (sp, s1 = v, s2 = shadow v, gp, tp, s0 = t) from a run of an X state ---- *)
Definition tvo_xregs_B : list sv := sr_set cur_atoms 18%bv (tvo_sh_B (SOff (xr 9) 0)).
Lemma tvo_bregs_okX : forall rg obj kd ky nx ix kp, tv_bregs_B rg ->
  regs_ok (TE regs rg (tvo_more obj kd ky nx ix kp)) tvo_xregs_B rg.
Proof.
intros rg obj kd ky nx ix kp (R2 & R9 & R18 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_lt as Hc47.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
set (E := TE regs rg (tvo_more obj kd ky nx ix kp)).
assert (X9 : bv_unsigned (ew E (xr 9)) = v).
{ unfold E, xr. rewrite (te_cur regs rg _ 9%bv 9) by reflexivity. rewrite R9. apply unsigned_lit_small. lia. }
assert (X64 : bv_unsigned (ew E 64) = SHADOW_OFF).
{ unfold E, tvo_more. rewrite (te_more_lt regs rg _ 0) by lia. cbn [nth app]. apply unsigned_lit_small.
  unfold SHADOW_OFF; lia. }
unfold tvo_xregs_B.
apply tv_regs_ok_set; [|reflexivity|rewrite R18; symmetry; replace (shadow_addr v) with (shadow_addr (v + 0))
  by (rewrite Z.add_0_r; reflexivity); apply (tvo_sh_val E (xr 9) v 0 X9 X64); lia].
apply te_regs_ok.
Qed.
Lemma tvo_bregs_symX : forall (H : word -> bool) obj kd ky nx i0 kp ss ms rg,
  st_ok SEGS (TE regs rg (tvo_more obj kd ky nx i0 kp)) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (sr_get tvo_xregs_B r)) TVO_KEPTB = true ->
  tv_bregs_B rg -> tv_bregs_B (ms_regs ms).
Proof.
intros H obj kd ky nx i0 kp ss ms rg HS Hf HBR. rewrite forallb_forall in Hf.
pose proof (tvo_bregs_okX rg obj kd ky nx i0 kp HBR) as HOK.
assert (K : forall r : bv 5, In r TVO_KEPTB -> getr (ms_regs ms) r = getr rg r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), (sv_eqb_eq _ _ (Hf r Hr)). symmetry. exact (HOK r). }
destruct HBR as (R2 & R9 & R18 & R3 & R4 & R8).
unfold tv_bregs_B. rewrite !K by (unfold TVO_KEPTB; repeat (first [left; reflexivity | right])).
repeat split; assumption.
Qed.

(* ---- the facts below alloc_ceiling (the node, the blocks and their shadow) move with the view there ---- *)
Lemma tv_ra_low : forall (Wc : world SEGS) m m' x k,
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) m' a = aview SEGS (w_H Wc) m a) ->
  0 <= x -> x + k <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H Wc) m) SHADOW_OFF x k -> range_addressable (aview SEGS (w_H Wc) m') SHADOW_OFF x k.
Proof.
intros Wc m m' x k AV Hx Hk H. pose proof asan_consts as (C1 & _).
eapply range_addressable_agree; [|exact H]. intros y Hy. apply AV.
unfold shadow_of_addr, SHADOW_OFF.
assert (0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.
Lemma tv_bvis_low : forall (Wc : world SEGS) m m' x k,
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) m' a = aview SEGS (w_H Wc) m a) ->
  prhtx_bvis Wc m x k -> prhtx_bvis Wc m' x k.
Proof.
intros Wc m m' x k AV (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_lt as Hc47.
assert (SH : forall y, 0 <= y < 2 ^ 47 -> 0 <= shadow_addr y < 2147450880 + 2 ^ 44).
{ intros y Hy. unfold shadow_addr, SHADOW_OFF.
  assert (0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
split; [exact (tv_ra_low Wc m m' x k AV ltac:(lia) ltac:(lia) B6)|].
split.
{ intros Hk s Hs. rewrite AV; [exact (B7 Hk s Hs)|].
  pose proof (SH x ltac:(lia)) as S0. pose proof (SH (x + k - 1) ltac:(lia)) as S1.
  pose proof (Z.mul_div_le (shadow_addr x) 8 ltac:(lia)) as M0.
  pose proof (Z.mul_div_le (shadow_addr (x + k - 1)) 8 ltac:(lia)) as M1.
  pose proof (Z.div_pos (shadow_addr x) 8 ltac:(lia) ltac:(lia)) as P0. lia. }
intros a Ha. rewrite AV; [exact (B8 a Ha)|].
pose proof (Z.mul_div_le (k + 7) 8 ltac:(lia)) as M2. pose proof (Z.div_pos (k + 7) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* ---- the live state across one of the caller's own runs that wrote only its frame [sp0 - 192, sp0) (with the run's
   memnorm keep); the run's journal is tv_liveR's at WR, REBASED (the batch) ---- *)
Lemma tv_live_frame : forall lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' b P,
  tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P ->
  AJR (STKV + dw) (sp0 + dw) FP0 ly (set_depot (st_depot Sc) S) Hp W mem md [] lyc Sc Hpc Wc memc' mdc' kj' ->
  (forall x : word, (bv_unsigned x < sp0 - 192 \/ sp0 <= bv_unsigned x) -> rdW Wc memc' x = rdW Wc memc x) ->
  tv_saved Wc memc' -> TVMN memc memc' ->
  tv_liveR WR lyc Sc Hpc Wc memc' mdc' kj' b P.
Proof.
intros lyc Sc Hpc Wc memc memc' mdc mdc' kj kj' b P
  (HJ & HWIN & (cap & fc & ow & pre & (HTX0 & HPS & HMN0 & HDEAD & HWS)) & HRO & HFK & HRAc & HBVc & _) HJ' RD HSV' HMNk.
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & _).
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLYc.
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (AV : forall a, 0 <= a < 2 ^ 64 -> (a < sp0 - 192 \/ sp0 <= a) ->
  aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. unfold aview, mbyte. rewrite (RD (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn. }
assert (AVL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a)
  by (intros a Ha; apply AV; lia).
assert (ROlow : forall a, in_roP SEGS RLO RHI a -> 0 <= a < YM05.alloc_ceiling).
{ intros a Hro. assert (Hi : in_img SEGS a).
  { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
  pose proof (@pa_segs_low _ _ PA a Hi). lia. }
split; [exact HJ'|]. split; [intros a Ha Hn; rewrite AV by lia; exact (HWIN a Ha Hn)|].
split; [exists cap, fc, ow, pre; split; [|split; [exact HPS | split; [exact (TVMN_trans mem memc memc' HMN0 HMNk) |
  split; [exact HDEAD | exact HWS]]]];
  apply (tx_state_keep B ARx LAWS S1ImgB.pst_in_img_B Lam regs dw ly S Hp t b0 len0 cap0 f0 txt peak cnt fail ran most own
  b cap fc ow (TxModel.plen P) (concat P) pre lyc Sc Hpc Wc memc memc' mdc (sp0 - 192) sp0 HTX0 HARc);
  [|lia|lia|exact RD]; rewrite Etop; lia|].
split; [intros a Hro Hno Her; rewrite (AVL a (ROlow a Hro)); exact (HRO a Hro Hno Her)|].
split; [intros x Hx; rewrite AVL; [exact (HFK x Hx)|];
  destruct (tv_foot_low ly S Hp W mem md Lam peak cnt fail ran most own v D x HAR0 HLED HHOME HDLAM Hx); lia|].
split; [exact (tv_ra_low Wc memc memc' v 56 AVL ltac:(lia) ltac:(lia) HRAc)|].
split; [rewrite Forall_forall in HBVc |- *; intros bk Hbk; exact (tv_bvis_low Wc memc memc' _ _ AVL (HBVc bk Hbk))|].
exact HSV'.
Qed.

(* ---- THE LIVE STATE at the opening call (nothing appended): the frame written, the view off [sp0 - 192, sp0) the
   entry's, the run position the entry's, the memnorm keep of the runs so far; the entry's journal REBASED to the entry
   depot (YCbqGwild.ajournal_xw_rebase at WS = [], as BTxLine's tl_main), DEAD trivially, no wild growth yet ---- *)
Lemma tv_live_init : forall memc mdc kj,
  AJ (STKV + dw) (sp0 + dw) FP0 ly S Hp W mem md [] ly S Hp W memc mdc kj ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 192 <= a < sp0) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  tv_saved W memc -> TVMN mem memc ->
  tv_live ly S Hp W memc mdc kj b0 [].
Proof.
intros memc mdc kj HJ KA HSV HMNc.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & _).
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
destruct (tv_facts_at memc mdc 192 (proj1 HJ) ltac:(lia) ltac:(lia) KA) as (HRODc & HRECc & HINVc & HTRc & HLEDc).
assert (KAL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KA; lia).
split; [exact (YCbqGwild.ajournal_xw_rebase (SK := SK) SEGS B PST ARx _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ [] HJ)|].
split; [intros a Ha _; apply KA; lia|].
split.
{ exists cap0, f0, own, [].
  split; [|split; [exact (tx_pos_init rp_sm rp_x rp_os rp_i rp_H0 rp_hist len0 cap0 f0 S HPOS)|]].
  2: { split; [exact HMNc|]. split; [exact (fun E => E)|].
       exists []. split; [rewrite app_nil_r; apply incl_refl | intros _; unfold YCbqGwild.wbudget; cbn; lia]. }
  unfold tx_state. cbn [length Z.of_nat TxModel.tx_capf TxModel.zsum TxModel.plen concat map].
  rewrite Z.add_0_r, app_nil_r.
  split; [lia|]. split; [lia|]. split; [reflexivity|].
  split; [|split; [exact (tx_out_nil len0 cap0 f0 own b0) | split; [exact HTRc | split; [exact HROOM | exact HLEDc]]]].
  split; [exact HRECc|]. split; [exact HINVc|].
  split; [apply (tv_place_av ly S W regs regs mem memc dw t eq_refl ltac:(lia) ltac:(lia));
    [intros a Ha; apply KA; lia | intros a Ha; apply KA; lia | exact HPLACE]|].
  split; [reflexivity|]. split; [apply prhtx_grow_refl | lia]. }
split; [exact HRODc|].
split; [intros x Hx; apply KAL; destruct (tv_foot_low ly S Hp W mem md Lam peak cnt fail ran most own v D x HAR HLED HHOME HDLAM Hx);
  lia|].
split; [exact (tv_ra_low W mem memc v 56 KAL ltac:(lia) ltac:(lia) HRA)|].
split; [rewrite Forall_forall in HBV |- *; intros bk Hbk; exact (tv_bvis_low W mem memc _ _ KAL (HBV bk Hbk))|].
exact HSV.
Qed.

(* the node's str field at a live state after the opening call (its bytes are the entry's) *)
Lemma tv_hdr_now : forall lyc Sc Hpc Wc memc mdc kj b P ty0 num0 str0 kids0 keys0 n0 cap1,
  tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P ->
  PRH_Reader.pj_hdrR SEGS (rdW W mem) v ty0 num0 str0 kids0 keys0 n0 cap1 ->
  0 <= str0 < 2 ^ 64 /\ val_mem SEGS (rdW Wc memc) (v + 16) 8 str0.
Proof.
intros lyc Sc Hpc Wc memc mdc kj b P ty0 num0 str0 kids0 keys0 n0 cap1 (_ & _ & _ & _ & HFK & _)
  (_ & _ & _ & (Rs & Vs) & _).
split; [exact Rs|]. apply (ts_vm_av (w_H W) (w_H Wc) mem memc _ 8 _); [|exact Vs].
intros j Hj. apply HFK. left. lia.
Qed.

(* ==== THE OPEN ARM (tags 5 / 6), one model for both brackets ==== *)
Section o.
Variables (ob : bool) (its : list (option (list Z) * PjTree.jv)) (num str kids keys cap : Z).
#[local] Notation NIT := (length its).
Definition TV_TY : Z := if ob then 6 else 5.
Definition TV_OPEN : Z := if ob then 123 else 91.
Definition TV_CLOSE : Z := if ob then 125 else 93.
(* the brackets' literals in the read-only band (B: .str.20 "{" 0x21200, .str.21 "[" 0x21220, .str.25 "}" 0x212a0, .str.26 "]" 0x212c0;
   DERIVED, the same offsets as image A's) *)
Definition TV_OPOFF : Z := if ob then 70144 else 70176.
Definition TV_CLOFF : Z := if ob then 70304 else 70336.
Hypothesis HHDR : PRH_Reader.pj_hdrR SEGS (rdW W mem) v TV_TY num str kids keys (Z.of_nat NIT) cap.
Hypothesis Hncap : Z.of_nat NIT <= cap.
Hypothesis HKB : (0 < NIT)%nat -> In (kids, 56 * cap) D /\ (ob = true -> In (keys, 8 * cap) D).
Hypothesis HITEM : forall i, (i < NIT)%nat -> exists Dx,
  PRH_Reader.pj_nodeR SEGS (rdW W mem) (prh_lin Lam) (kids + 56 * Z.of_nat i) (snd (nth i its (None, PjTree.JNull))) Dx /\
  incl Dx D.
Hypothesis HKEY : forall i, (i < NIT)%nat ->
  match fst (nth i its (None, PjTree.JNull)) with
  | Some nm => ob = true /\ exists x k, PRH_Reader.rd_u64 SEGS (rdW W mem) (keys + 8 * Z.of_nat i) x /\
      PRH_Reader.pj_cstrR SEGS (rdW W mem) (prh_lin Lam) x k nm /\ In (x, k) D
  | None => ob = false
  end.
Hypothesis HDK : forall i, (i < NIT)%nat ->
  (PjTree.depth (snd (nth i its (None, PjTree.JNull))) < PjTree.depth tv)%nat.
Hypothesis EPC : TxModel.tvp tv PP d = [TV_OPEN] :: tvI_go PP d 0 its ++ tv_close its PP d ++ [[TV_CLOSE]].
(* the pieces after the opening bracket and i items *)
Definition tvo_Pl (i : nat) : list (list Z) := [[TV_OPEN]] ++ tvI_go PP d 0 (firstn i its).
Lemma tvo_close_eq : (0 < NIT)%nat -> tv_close its PP d = WriterValue.wind PP d.
Proof. intros H. unfold tv_close. destruct its; [cbn in H; lia | reflexivity]. Qed.

(* the all-read-only loop states write nothing *)
Ltac tv_awr_ro := lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
Ltac tv_nowr HFr := intros x; apply HFr; let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros (r & Hr & Ha); cbv [ss_M_B ss_X_B ss_P_B ss_mem app In tvo_node_B tvo_keyslot_B] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia|]); destruct Hr.

(* rewrites every `ew (TE r0 rc mo) n` of the goal into the entry register, the current register or the extra *)
Ltac tv_ewc := repeat match goal with |- context [ew (TE ?r0 ?rc ?mo) ?n] =>
  let nn := eval vm_compute in n in
  lazymatch eval vm_compute in (Nat.ltb nn 32) with
  | true => let r := eval cbv [nth YP01.all_regs] in (nth nn YP01.all_regs 0%bv) in
      rewrite (te_entry r0 rc mo r nn) by reflexivity
  | false => lazymatch eval vm_compute in (Nat.ltb nn 64) with
    | true => let kk := eval vm_compute in (Nat.sub nn 32) in
        let r := eval cbv [nth YP01.all_regs] in (nth kk YP01.all_regs 0%bv) in
        change (ew (TE r0 rc mo) n) with (ew (TE r0 rc mo) (32 + kk)%nat);
        rewrite (te_cur r0 rc mo r kk) by reflexivity
    | false => lazymatch eval vm_compute in (Nat.ltb nn 240) with
      | true => let j := eval vm_compute in (Nat.sub nn 64) in
          change (ew (TE r0 rc mo) n) with (ew (TE r0 rc mo) (64 + j)%nat);
          rewrite (te_more_lt r0 rc mo j) by lia; cbn [nth app tvo_more]
      | false => rewrite (te_img r0 rc mo n) by (unfold A_TEXT, A_LIM; lia)
      end
    end
  end end.

(* ---- X: after the closing tx_line (B 0x85704, offset 16440): the shadow check, the type, the closing bracket, the
   epilogue, `j tx_put` ---- *)
Lemma tvo_seg_X : forall lyc Sc Hpc Wc memc mdc kj b rg,
  tv_liveR WR lyc Sc Hpc Wc memc mdc kj b (tvo_Pl NIT ++ tv_close its PP d) -> tv_bregs_B rg ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + 16440)) memc (seg_rom SEGS)) mdc) QF.
Proof.
intros lyc Sc Hpc Wc memc mdc kj b rg HL HLR.
pose proof HLR as (R2 & R9 & R18 & R3 & R4 & R8).
destruct (tv_fields_now lyc Sc Hpc Wc memc mdc kj b _ _ _ _ _ _ _ _ HL HHDR)
  as ((Hty & Vty) & (Hkd & Vkd) & (Hky & Vky) & (Hn & Vn)).
pose proof HL as (HJ & _ & HTX & HRO & _ & HRAc & _ & HSV).
pose proof HTX as (capX & fcX & owX & preX & _ & _ & HMN & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof tv_stk_facts as (SK0 & SK1 & _). pose proof (tv_stkv nn) as ESK.
pose proof (@pa_val_range _ _ PA (A_OBJ 2)) as RV2.
destruct (tv_X_entry_B 16440 TV_TY rg Wc memc kids keys (Z.of_nat NIT) HLR HSV
  Hty Vty Hkd Vkd Hky Vky Hn Vn HRAc) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) 0 0))) by apply te_env.
assert (HAE : env_agree 32 (Ereg regs (map (getr rg) all_regs ++ tvo_more false kids keys (Z.of_nat NIT) 0 0))
  (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) 0 0)))
  by (split; [intros k Hk; unfold TE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EP : (tvo_Pl NIT ++ tv_close its PP d) ++ [[TV_CLOSE]] = TxModel.tvp tv PP d).
{ unfold tvo_Pl. rewrite firstn_all, EPC. cbn [app]. rewrite <- !app_assoc. reflexivity. }
unfold TV_TY, TV_CLOSE, TV_CLOFF in *. destruct ob.
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: assert (Hm : forall x, rdW Wc (ms_mem ms) x = rdW Wc memc x) by tv_nowr HFr.
all: pose proof (tv_live_same lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ b _ HL HJ Hm HMN) as HL2.
all: clear HF HG HFr.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
all: prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19.
all: prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23.
all: prreg HS (24%bv : bv 5) Q24; prreg HS (25%bv : bv 5) Q25; prreg HS (26%bv : bv 5) Q26; prreg HS (27%bv : bv 5) Q27.
all: prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12.
all: cbn [app] in EP.
all: pose proof (ajxR_ar HJ) as HARf.
all: pose proof HL2 as (_ & _ & _ & HRO2 & _).
all: lazymatch goal with HS0 : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- SRrG _ _ _ (mkCfg ?msx ?mdx) _ =>
  lazymatch type of Q11 with _ = Z_to_bv 64 (bv_unsigned (ew _ 243) + ?off) =>
  lazymatch type of EP with _ ++ [[?c]] = _ =>
  destruct (tv_lit_src_at lyc Sc Hpc Wc (ms_mem msx) mdx off [c] HARf HRO2
    ltac:(cbn; tauto) ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
    as (HSRC & HKEPT & HDISJ);
  refine (tv_tail_close Wc Ex ssx msx mdx lyc Sc Hpc _ b _ (VAL (A_OBJ 2) + off) [c] HS0
    ltac:(vm_compute; reflexivity) _ HL2 _ _ _ _ _ _ _ _ HSRC HKEPT HDISJ EP)
  end end end.
all: try (rewrite (st_ok_restrict_mkst SEGS (w_H Wc) _ _ _ HS eq_refl) at 1; reflexivity).
all: try (unfold spZ at 1; rewrite Q2; tv_ewc; rewrite R2; unfold w64;
  replace (bv_unsigned (Z_to_bv 64 (sp0 - 192))) with (sp0 - 192) by (rewrite unsigned_lit_small; lia);
  rewrite unsigned_lit_small by lia; lia).
all: try (apply tv_aregs13; [ apply bv_eq; rewrite Q2; tv_ewc; rewrite R2; unfold w64;
    replace (bv_unsigned (Z_to_bv 64 (sp0 - 192))) with (sp0 - 192) by (rewrite unsigned_lit_small; lia);
    rewrite unsigned_lit_small by lia; unfold spZ; lia
  | rewrite Q3; tv_ewc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact R3
  | rewrite Q4; tv_ewc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact R4
  | .. ];
  lazymatch goal with Q : getr (ms_regs ?m) ?r = _ |- getr (ms_regs ?m) ?r = _ =>
    rewrite Q; tv_ewc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity end).
all: try (rewrite Q1; tv_ewc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity).
all: try (rewrite Q3; tv_ewc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact R3).
all: try (rewrite Q4; tv_ewc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact R4).
all: try (rewrite Q10; tv_ewc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact R8).
all: try (rewrite Q11; tv_ewc; rewrite unsigned_lit_small by (change 243%nat with (A_OBJ 2); lia); reflexivity).
all: try (rewrite Q12; reflexivity).
Qed.

(* ---- a seated branch condition from the values (the UBSan checks, the loop test, pretty, i = 0) ---- *)
Lemma tvo_bc : forall c x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y) =
  match c with
  | BC_EQ => x =? y | BC_NE => negb (x =? y)
  | BC_LTU => x <? y | BC_GEU => negb (x <? y)
  | BC_LT => bv_signed (Z_to_bv 64 x) <? bv_signed (Z_to_bv 64 y)
  | BC_GE => negb (bv_signed (Z_to_bv 64 x) <? bv_signed (Z_to_bv 64 y))
  end.
Proof.
intros c x y Hx Hy. destruct c; cbn [branch_taken];
  unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?unsigned_lit_small by lia; reflexivity.
Qed.
Lemma tvo_cond : forall E c a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  (match c with BC_EQ => x = y | BC_NE => x <> y | BC_LTU => x < y | BC_GEU => y <= x | _ => False end) ->
  acond_ok E (mkAC c a b).
Proof.
intros E c a b x y Ha Hb Hx Hy H. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite Ha, Hb, tvo_bc by lia.
destruct c; try contradiction.
- apply Z.eqb_eq. exact H.
- apply negb_true_iff. apply Z.eqb_neq. exact H.
- apply Z.ltb_lt. exact H.
- apply negb_true_iff. apply Z.ltb_ge. exact H.
Qed.

(* ---- the pieces at each point of the loop, and the model bound every call site asks ---- *)
Lemma tvo_split : forall i, (i <= NIT)%nat ->
  tvo_Pl i ++ tvI_go PP d i (skipn i its) ++ tv_close its PP d ++ [[TV_CLOSE]] = TxModel.tvp tv PP d.
Proof.
intros i Hi. unfold tvo_Pl.
assert (G : tvI_go PP d 0 its = tvI_go PP d 0 (firstn i its) ++ tvI_go PP d i (skipn i its)).
{ rewrite <- (firstn_skipn i its) at 1. rewrite tvI_go_app, firstn_length_le by lia. reflexivity. }
rewrite EPC, G. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma tvo_pref : forall P1 P2, P1 ++ P2 = TxModel.tvp tv PP d ->
  Z.of_nat (length (concat P1)) + Z.of_nat (length (concat P2)) = Z.of_nat (length ADD).
Proof.
intros P1 P2 H. rewrite <- s10v_tvp_wv, <- H, concat_app, length_app. lia.
Qed.
Lemma tvo_peel : forall i, (i < NIT)%nat ->
  tvI_go PP d i (skipn i its) =
  (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ tvI_key PP (fst (nth i its (None, PjTree.JNull))) ++
   TxModel.tvp (snd (nth i its (None, PjTree.JNull))) PP (d + 1)) ++ tvI_go PP d (Datatypes.S i) (skipn (Datatypes.S i) its).
Proof.
intros i Hi.
assert (E : skipn i its = nth i its (None, PjTree.JNull) :: skipn (Datatypes.S i) its).
{ clear -Hi. revert its Hi. induction i as [|i IH]; intros l Hl.
  - destruct l as [|x r]; [cbn in Hl; lia | reflexivity].
  - destruct l as [|x r]; [cbn in Hl; lia|]. cbn [skipn nth]. apply IH. cbn in Hl. lia. }
rewrite E. destruct (nth i its (None, PjTree.JNull)) as [ko x]. cbn [tvI_go fst snd].
rewrite <- !app_assoc. reflexivity.
Qed.
(* the pieces at the loop head after i items, as a prefix *)
Lemma tvo_Pl_S : forall i, (i < NIT)%nat ->
  tvo_Pl (Datatypes.S i) = tvo_Pl i ++ WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++
    tvI_key PP (fst (nth i its (None, PjTree.JNull))) ++ TxModel.tvp (snd (nth i its (None, PjTree.JNull))) PP (d + 1).
Proof.
intros i Hi. unfold tvo_Pl. rewrite (tvI_go_firstn_S PP d its i Hi).
destruct (nth i its (None, PjTree.JNull)) as [ko x]. rewrite (tvI_go_one PP d i ko x).
cbn [fst snd]. rewrite <- !app_assoc. reflexivity.
Qed.

(* ---- the loop's block facts: the kids array (and for an object the keys array) is a harness block, so the counts
   and the arrays' addresses are bounded ---- *)
Lemma tvo_cnt_facts : (0 < NIT)%nat ->
  4096 <= kids /\ kids + 56 * cap <= YM05.alloc_ceiling /\ 1 <= cap /\ Z.of_nat NIT <= 2 ^ 42 /\
  (ob = true -> 4096 <= keys /\ keys + 8 * cap <= YM05.alloc_ceiling).
Proof.
intros Hn. pose proof HPRE as (HAR & _). pose proof alloc_ceiling_lt as Hc47.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (HKB Hn) as (Hink & Hinky).
assert (Hcap1 : 1 <= cap) by lia.
assert (HB : forall x m, In (x, m) D -> 0 <= m -> 4096 <= x /\ x + m <= YM05.alloc_ceiling).
{ intros x m Hin Hm.
  destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran x m _ _ HLED (HDLAM _ Hin)) as (Hk0 & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & Happ & _).
  pose proof (@cf_head_nonneg CfParams_preset) as Hh0.
  assert (Hrq : req_size (m + cf_head) = m + cf_head)
    by (change (@cf_head CfParams_preset) with 16; unfold req_size; destruct (Z.eqb_spec (m + 16) 0); lia).
  rewrite Hrq in Hc. change (@cf_head CfParams_preset) with 16 in Hc, H4096. lia. }
destruct (HB kids (56 * cap) Hink ltac:(lia)) as (Hk1 & Hk2).
split; [exact Hk1|]. split; [exact Hk2|]. split; [exact Hcap1|].
split; [lia|].
intros Hob. destruct (HB keys (8 * cap) (Hinky Hob) ltac:(lia)) as (Hy1 & Hy2). split; [exact Hy1 | exact Hy2].
Qed.

(* ---- a seated branch condition from the values of its two sides ---- *)
Lemma tvo_condU : forall E c a b,
  (match c with BC_EQ => U E a = U E b | BC_NE => U E a <> U E b | BC_LTU => U E a < U E b
   | BC_GEU => U E b <= U E a | _ => False end) -> acond_ok E (mkAC c a b).
Proof.
intros E c a b H. pose proof (U_range E a) as Ia. pose proof (U_range E b) as Ib. unfold M64 in Ia, Ib.
apply (tvo_cond E c a b (U E a) (U E b) (denot_lit_U E a) (denot_lit_U E b) Ia Ib). destruct c; exact H.
Qed.

(* ---- the prefix every call site of item i asks (tv_call_core's premise, which cuts the call's run window out of the
   text's own): the pieces before the call, the call's pieces Q, then the rest of the text ---- *)
Lemma tvo_len : forall i A Q Bq, (i < NIT)%nat ->
  A ++ Q ++ Bq = WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++
    tvI_key PP (fst (nth i its (None, PjTree.JNull))) ++ TxModel.tvp (snd (nth i its (None, PjTree.JNull))) PP (d + 1) ->
  exists R, (tvo_Pl i ++ A) ++ Q ++ R = TxModel.tvp tv PP d.
Proof.
intros i A Q Bq Hi E.
exists (Bq ++ tvI_go PP d (Datatypes.S i) (skipn (Datatypes.S i) its) ++ tv_close its PP d ++ [[TV_CLOSE]]).
rewrite <- (tvo_split i) by lia. rewrite (tvo_peel i Hi), <- E. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma tvo_len_close : exists R, tvo_Pl NIT ++ tv_close its PP d ++ R = TxModel.tvp tv PP d.
Proof.
exists [[TV_CLOSE]]. rewrite <- (tvo_split NIT) by lia. rewrite skipn_all. cbn [tvI_go app]. rewrite <- ?app_assoc.
reflexivity.
Qed.

(* ---- the i-th item at a live state (B twin of S10TxValue.v 37251f6b9a5 tv_item_now) ---- *)
Lemma tv_item_now : forall i lyc Sc Hpc Wc memc mdc kj b P, (i < NIT)%nat -> tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P ->
  exists Dx, PRH_Reader.pj_nodeR SEGS (rdW Wc memc) (prh_lin Lam) (kids + 56 * Z.of_nat i)
      (snd (nth i its (None, PjTree.JNull))) Dx /\
    (forall bk, In bk Dx -> In bk Lam) /\ prhtx_home Lam lyc Sc (kids + 56 * Z.of_nat i) 56 /\
    range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (kids + 56 * Z.of_nat i) 56 /\
    Forall (fun bk => prhtx_bvis Wc memc (fst bk) (snd bk)) Dx /\
    (kids + 56 * Z.of_nat i + 56 <= t \/ t + 28 <= kids + 56 * Z.of_nat i) /\
    (PjTree.depth (snd (nth i its (None, PjTree.JNull))) < PjTree.depth tv)%nat.
Proof.
intros i lyc Sc Hpc Wc memc mdc kj b P Hi HL.
destruct (HITEM i Hi) as (Dx & HNx & Hinc). destruct (HKB ltac:(lia)) as [HKD _].
pose proof HL as (_ & _ & _ & _ & HFK & _ & HBVc & _).
pose proof HPRE as (HAR & _).
pose proof asan_consts as (C1 & _).
destruct (tv_lam_low kids (56 * cap) (HDLAM _ HKD)) as (Hk4 & Hkc & _ & _).
pose proof tv_t_high as Hth.
exists Dx. split; [|split; [|split; [|split; [|split; [|split; [|exact (HDK i Hi)]]]]]].
- apply (tv_nodeR_frame _ (rdW W mem) (rdW Wc memc) (prh_lin Lam) _ Dx HNx).
  intros x Hx. assert (HxD : PRH_Reader.pj_footR v D x).
  { destruct Hx as [Hx | (bk & Hbk & Hx)].
    - right. exists (kids, 56 * cap). split; [exact HKD | unfold PRH_Reader.pj_holdsR; cbn [fst snd]; lia].
    - right. exists bk. split; [apply Hinc; exact Hbk | exact Hx]. }
  pose proof (HFK x HxD) as E.
  destruct (tv_foot_low ly S Hp W mem md Lam peak cnt fail ran most own v D x HAR HLED HHOME HDLAM HxD) as [Hb Hn].
  split; [exact (mbyte_of_aview SEGS (w_H W) (w_H Wc) mem memc x E)|].
  intros Hw. exact (tv_wr_av2 W Wc mem memc x ltac:(lia) Hn E Hw).
- intros bk Hbk. apply HDLAM. apply Hinc. exact Hbk.
- left. exists kids, (56 * cap). split; [apply HDLAM; exact HKD | lia].
- pose proof (proj1 (Forall_forall _ _) HBVc _ HKD) as (_ & _ & _ & _ & _ & HRAk & _). cbn [fst snd] in HRAk.
  apply (range_addressable_sub _ SHADOW_OFF kids (56 * cap)); [exact HRAk | lia | lia].
- rewrite Forall_forall in HBVc |- *. intros bk Hbk. apply HBVc. apply Hinc. exact Hbk.
- left. lia.
Qed.

(* ---- the i-th key (an object) at a live state, in tv_keyf_B's order (B twin of S10TxValue.v tv_key_now) ---- *)
Lemma tv_key_now : forall i nm lyc Sc Hpc Wc memc mdc kj b P, (i < NIT)%nat ->
  fst (nth i its (None, PjTree.JNull)) = Some nm -> tv_liveR WR lyc Sc Hpc Wc memc mdc kj b P ->
  ob = true /\ exists x k, PRH_Reader.pj_cstrR SEGS (rdW Wc memc) (prh_lin Lam) x k nm /\ prhtx_bvis Wc memc x k /\
    0 <= Z.of_nat i /\ 4096 <= keys /\ keys + 8 * Z.of_nat i + 8 <= YM05.alloc_ceiling /\
    (keys + 8 * Z.of_nat i) mod 8 = 0 /\ in_app (keys + 8 * Z.of_nat i) 8 /\
    (keys + 8 * Z.of_nat i + 8 <= v \/ v + 56 <= keys + 8 * Z.of_nat i) /\
    0 <= x < 2 ^ 64 /\ val_mem SEGS (rdW Wc memc) (keys + 8 * Z.of_nat i) 8 x /\
    range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat i) 8.
Proof.
intros i nm lyc Sc Hpc Wc memc mdc kj b P Hi Hko HL.
pose proof (HKEY i Hi) as HK. rewrite Hko in HK. destruct HK as (Hob & x & k & (Hx & Vx) & Hc & Hxk).
destruct (HKB ltac:(lia)) as [_ HYD]. specialize (HYD Hob).
pose proof HL as (_ & _ & _ & _ & HFK & _ & HBVc & _).
pose proof asan_consts as (C1 & _).
destruct (tv_lam_low keys (8 * cap) (HDLAM _ HYD)) as (Hy4 & Hyc & Hy16 & Hyapp).
assert (FK : forall a, PRH_Reader.pj_footR v D a -> mbyte SEGS (rdW Wc memc) a = mbyte SEGS (rdW W mem) a).
{ intros a Ha. exact (mbyte_of_aview SEGS (w_H W) (w_H Wc) mem memc a (HFK a Ha)). }
split; [exact Hob|]. exists x, k.
split.
{ apply (PRH_Reader.pj_cstrR_frame SEGS (rdW W mem) (rdW Wc memc) (prh_lin Lam) x k nm Hc). intros a Ha. apply FK.
  right. exists (x, k). split; [exact Hxk | unfold PRH_Reader.pj_holdsR; cbn [fst snd]; exact Ha]. }
split; [exact (proj1 (Forall_forall _ _) HBVc _ Hxk)|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [apply Z.mod_divide in Hy16 as [q Hq]; [|lia]; rewrite Hq;
  replace (q * 16 + 8 * Z.of_nat i) with ((2 * q + Z.of_nat i) * 8) by lia; apply Z.mod_mul; lia|].
split; [unfold in_app in *; lia|].
split.
{ pose proof HNODE as HN. destruct tv; cbn [PRH_Reader.pj_nodeR] in HN; destruct HN as (_ & HAp & _);
  (destruct (Z_le_gt_dec (keys + 8 * Z.of_nat i + 8) v) as [h|h]; [left; exact h|]);
  (destruct (Z_le_gt_dec (v + 56) (keys + 8 * Z.of_nat i)) as [h'|h']; [right; exact h'|]);
  exfalso; apply (HAp (keys, 8 * cap) (Z.max v (keys + 8 * Z.of_nat i)) HYD);
  unfold PRH_Reader.pj_holdsR; cbn [fst snd]; lia. }
split; [exact Hx|].
split.
{ intros j Hj. rewrite FK; [exact (Vx j Hj)|]. right. exists (keys, 8 * cap). split; [exact HYD|].
  unfold PRH_Reader.pj_holdsR. cbn [fst snd]. lia. }
pose proof (proj1 (Forall_forall _ _) HBVc _ HYD) as (_ & _ & _ & _ & _ & HRAk & _). cbn [fst snd] in HRAk.
apply (range_addressable_sub _ SHADOW_OFF keys (8 * cap)); [exact HRAk | lia | lia].
Qed.

(* ---- the loop segments' tactics (B twins of S10TxValue.v's tv_reg, tv_callregs_tac, tv_pretty_hc, tv_seg_open,
   tv_seg_after, tv_same at B's registers) ---- *)
Ltac tv_reg Q := rewrite Q; tv_ewc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Ltac tv_ewc_in H := revert H; tv_ewc; intro H.
(* memory a run did not write *)
Ltac tv_same HFr H :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?Hh ?mA) (mrestrict _ ?mB) =>
    assert (H : forall y, mrestrict Hh mB y = mrestrict Hh mA y) by tv_nowr HFr end.
(* the call registers of a loop state's call: sp, gp, tp, s0 = t, a0 = t, ra (below the ceiling: the return pc's slot,
   tv_ret_ceil) *)
Ltac tvo_callregs_tac HS HMR R3 R4 R8 :=
  let QQ1 := fresh "QQ1" in let QQ2 := fresh "QQ2" in let QQ3 := fresh "QQ3" in let QQ4 := fresh "QQ4" in
  let QQ8 := fresh "QQ8" in let QQ10 := fresh "QQ10" in let HBB := fresh "HBB" in
  prreg HS (1%bv : bv 5) QQ1; prreg HS (2%bv : bv 5) QQ2; prreg HS (3%bv : bv 5) QQ3; prreg HS (4%bv : bv 5) QQ4;
  prreg HS (8%bv : bv 5) QQ8; prreg HS (10%bv : bv 5) QQ10;
  split; [tv_reg QQ2; exact (proj1 HMR)|]; split; [tv_reg QQ3; exact R3|]; split; [tv_reg QQ4; exact R4|];
  split; [tv_reg QQ8; exact R8|]; split; [tv_reg QQ10; exact R8|];
  split; [rewrite QQ1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]|];
  unfold raZ; rewrite QQ1; pose proof (@pa_B_ok _ _ PA) as HBB; rewrite unsigned_lit_small by lia;
  split; [lia | apply tv_ret_ceil; cbn [TV_RETS_B In]; repeat (first [left; reflexivity | right])].
(* pretty's branch condition (atom 51 = s3) as a test on pretty mod 2 ^ 64 *)
Ltac tv_pretty_hc Hc R19 :=
  rewrite (U_atom _ 51 (pretty mod 2 ^ 64)) in Hc by
    (first [tv_ewc; rewrite R19, H12; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
            change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity
           | pose proof (Z.mod_pos_bound pretty (2 ^ 64) ltac:(lia)); lia]).
(* the opening of a loop segment: the live facts and the node's fields *)
Ltac tvo_open :=
  intros lyc Sc Hpc Wc memc mdc kj b rg HL HSP HLR;
  pose proof HLR as (HMR & R3 & R4 & R8 & R19 & R21 & R22 & R24 & R26);
  destruct (tv_fields_now lyc Sc Hpc Wc memc mdc kj b _ _ _ _ _ _ _ _ HL HHDR)
    as ((Hty & Vty) & (Hkd & Vkd) & (Hky & Vky) & (Hn & Vn));
  pose proof HL as (HJ & _ & HTX & HRO & _ & HRAc & _ & HSV);
  pose proof HTX as (capX & fcX & owX & preX & _ & _ & HMN & _);
  pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _);
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5); pose proof alloc_ceiling_lt as Hc47;
  pose proof tv_stk_facts as (SK0 & SK1 & SK2 & SK3 & SK4 & SK5 & SK6); pose proof (tv_stkv nn) as ESK;
  pose proof (@pa_val_range _ _ PA (A_OBJ 2)) as RV2.
(* after a run that wrote nothing: the live state, the loop registers, the spills at the run's end *)
Ltac tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP i :=
  assert (Hm : forall y, rdW Wc (ms_mem ms) y = rdW Wc memc y) by tv_nowr HFr;
  assert (AV : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a)
    by (intros a; unfold aview, mbyte; rewrite Hm; reflexivity);
  let HMNx := lazymatch goal with Hx : TVMN mem (ms_mem ms) |- _ => Hx end in
  pose proof (tv_live_same lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ b _ HL HJ Hm HMNx) as HL2;
  clear HF HG HFr;
  pose proof (tvo_lregs_sym _ false kids keys (Z.of_nat NIT) i 0 _ ms rg i HS ltac:(vm_compute; reflexivity) HLR)
    as HLRc;
  assert (HSPc : tv_spill Wc (ms_mem ms))
    by (apply (proj2 (tv_frame_keep Wc Wc memc (ms_mem ms) ltac:(intros a _; apply AV))); exact HSP).

(* ---- L: the loop head (B 0x8559c, offset 16080): `beqz s10`; for i <> 0 the comma `jal tx_put` (.str.22 ',',
   band offset 70208, the spill 64(sp)), returning to C1 ---- *)
Lemma tvo_seg_L : forall i, (i < NIT)%nat ->
  tvo_SEG (tvo_Pl i ++ WriterValue.wcomma i) 16100 (Z.of_nat i) -> tvo_SEG (tvo_Pl i) TVO_LH_B (Z.of_nat i).
Proof.
intros i Hi HNEXT. tvo_open.
destruct (tvo_cnt_facts ltac:(lia)) as (Hk4 & Hkc & Hcap1 & Hn42 & _).
destruct (tv_M_entry_B TVO_LH_B TV_TY false rg Wc memc kids keys (Z.of_nat NIT) (Z.of_nat i) 0 [] HMR HSV HSP
  Hty Vty ltac:(lia) Vkd Hky Vky ltac:(lia) Vn ltac:(lia) R26 HRAc ltac:(discriminate) I) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0))) by apply te_env.
assert (HLENC : i <> 0%nat -> exists R, tvo_Pl i ++ [[44]] ++ R = TxModel.tvp tv PP d).
{ intros Hi0.
  destruct (tvo_len i [] [[44]] (WriterValue.wind PP (d + 1) ++ tvI_key PP (fst (nth i its (None, PjTree.JNull))) ++
    TxModel.tvp (snd (nth i its (None, PjTree.JNull))) PP (d + 1)) Hi
    ltac:(unfold WriterValue.wcomma; rewrite (proj2 (Nat.eqb_neq i 0) Hi0); reflexivity)) as (R & ER).
  exists R. rewrite app_nil_r in ER. exact ER. }
assert (HN1 : i <> 0%nat -> tvo_SEG (tvo_Pl i ++ [[44]]) 16100 (Z.of_nat i)).
{ intros Hi0. unfold WriterValue.wcomma in HNEXT. rewrite (proj2 (Nat.eqb_neq i 0) Hi0) in HNEXT. exact HNEXT. }
assert (HN0 : i = 0%nat -> tvo_SEG (tvo_Pl i) 16100 (Z.of_nat i)).
{ intros Hi0. subst i. cbn [WriterValue.wcomma Nat.eqb] in HNEXT. rewrite app_nil_r in HNEXT. exact HNEXT. }
clear HNEXT.
pose (BR := paj_branchR (PI := PA) WR).
unfold TV_TY in *. destruct ob.
all: psrr_branch_tok (RUNIR mem) BR HS SHOK TV_SPAN.
all: rewrite branch_eq_U, U_SLit in Hc; change (zcanon 0) with 0 in Hc.
all: rewrite (U_atom _ 58 (Z.of_nat i)) in Hc by (first [tv_ewc; exact R26 | lia]).
1,3: apply Z.eqb_eq in Hc; assert (Hi0 : i = 0%nat) by lia;
  paj_run_to_tok_x_inv (RUNTOIR mem) HS HJ SHOK HMN TV_SPAN 16100; [tv_awr_ro|];
  tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP (Z.of_nat i);
  pmkst HS; exact (HN0 Hi0 _ _ _ _ _ _ _ _ _ HL2 HSPc HLRc).
all: apply Z.eqb_neq in Hc; assert (Hi0 : i <> 0%nat) by lia.
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP (Z.of_nat i).
all: prreg HS (1%bv : bv 5) Q1; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12.
all: pose proof HL2 as (HJ2 & _ & _ & HRO2 & _).
all: destruct (tv_lit_src_at lyc Sc Hpc Wc (ms_mem ms) _ 70208 [44] (proj1 HJ2) HRO2
  ltac:(cbn; tauto) ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
all: lazymatch type of HL2 with tv_liveR _ _ _ _ _ _ ?mdx ?kjx _ ?Px =>
  apply (tv_put_call Wc _ _ ms mdx lyc Sc Hpc kjx b Px (VAL (A_OBJ 2) + 70208) [44] HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
all: try (tv_ewc; reflexivity).
all: try exact HL2.
all: try (tvo_callregs_tac HS HMR R3 R4 R8).
all: try (rewrite Q11; tv_ewc; rewrite unsigned_lit_small by (change 243%nat with (A_OBJ 2); lia); reflexivity).
all: try (rewrite Q12; reflexivity).
all: try exact HSRC.
all: try exact HKEPT.
all: try exact HDISJ.
all: try exact (HLENC Hi0).
all: try (apply (tvo_kont_seg Wc ms _ _ 16100 (Z.of_nat i)); [exact (HN1 Hi0) | exact HSPc | exact HLRc | exact Q1]).
Qed.

(* ---- C1: after the comma (B 0x855b0, offset 16100): `beqz s3`; for pretty the depth flag s9 = 0 and the item's
   tx_line(t, d + 1), returning to T ---- *)
Lemma tvo_seg_C1 : forall i, (i < NIT)%nat ->
  tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1))) 16120 (Z.of_nat i) ->
  tvo_SEG (tvo_Pl i ++ WriterValue.wcomma i) 16100 (Z.of_nat i).
Proof.
intros i Hi HNEXT. tvo_open.
destruct (tvo_cnt_facts ltac:(lia)) as (Hk4 & Hkc & Hcap1 & Hn42 & _).
destruct (tv_M_entry_B 16100 TV_TY false rg Wc memc kids keys (Z.of_nat NIT) (Z.of_nat i) 0 [] HMR HSV HSP
  Hty Vty ltac:(lia) Vkd Hky Vky ltac:(lia) Vn ltac:(lia) R26 HRAc ltac:(discriminate) I) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0))) by apply te_env.
pose proof (HDK i Hi) as HDKi.
assert (Hd1 : 0 <= d + 1 <= 2 ^ 31 - 1) by lia.
assert (HLENL : pretty <> 0 -> exists R, (tvo_Pl i ++ WriterValue.wcomma i) ++ WriterValue.wind true (d + 1) ++ R =
  TxModel.tvp tv PP d).
{ intros Hpr.
  apply (tvo_len i (WriterValue.wcomma i) (WriterValue.wind true (d + 1))
    (tvI_key PP (fst (nth i its (None, PjTree.JNull))) ++ TxModel.tvp (snd (nth i its (None, PjTree.JNull))) PP (d + 1)) Hi).
  rewrite (tv_pp_true Hpr), <- ?app_assoc. reflexivity. }
assert (HN1 : pretty <> 0 -> tvo_SEG ((tvo_Pl i ++ WriterValue.wcomma i) ++ WriterValue.wind true (d + 1)) 16120 (Z.of_nat i)).
{ intros Hpr. rewrite <- app_assoc, <- (tv_pp_true Hpr). exact HNEXT. }
assert (HN0 : pretty = 0 -> tvo_SEG (tvo_Pl i ++ WriterValue.wcomma i) 16120 (Z.of_nat i)).
{ intros Hpr. rewrite (tv_pp_false Hpr) in HNEXT. cbn [WriterValue.wind] in HNEXT. rewrite app_nil_r in HNEXT. exact HNEXT. }
clear HNEXT.
pose (BR := paj_branchR (PI := PA) WR).
unfold TV_TY in *. destruct ob.
all: psrr_branch_tok (RUNIR mem) BR HS SHOK TV_SPAN.
all: rewrite branch_eq_U, U_SLit in Hc; change (zcanon 0) with 0 in Hc.
all: tv_pretty_hc Hc R19.
1,3: apply Z.eqb_eq, tv_pretty_mod in Hc;
  paj_run_to_tok_x_inv (RUNTOIR mem) HS HJ SHOK HMN TV_SPAN 16120; [tv_awr_ro|];
  tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP (Z.of_nat i);
  pmkst HS; exact (HN0 Hc _ _ _ _ _ _ _ _ _ HL2 HSPc HLRc).
all: apply Z.eqb_neq in Hc; assert (Hpr : pretty <> 0) by (intros E; apply Hc; rewrite E; reflexivity).
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP (Z.of_nat i).
all: prreg HS (1%bv : bv 5) Q1; prreg HS (11%bv : bv 5) Q11.
all: lazymatch type of HL2 with tv_liveR _ _ _ _ _ _ ?mdx ?kjx _ ?Px =>
  apply (tv_line_call Wc _ _ ms mdx lyc Sc Hpc kjx b Px (d + 1) HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
all: try (tv_ewc; reflexivity).
all: try exact HL2.
all: try (tvo_callregs_tac HS HMR R3 R4 R8).
all: try (tv_reg Q11; exact R22).
all: try exact Hd1.
all: try exact (HLENL Hpr).
all: try (apply (tvo_kont_seg Wc ms _ _ 16120 (Z.of_nat i)); [exact (HN1 Hpr) | exact HSPc | exact HLRc | exact Q1]).
Qed.

(* ---- T: after the item's tx_line (B 0x855c4, offset 16120): the node's shadow and tag; an array goes on to Sp
   (0x8565c); an object checks its i-th key slot (the seated UBSan conditions i >> 60 = 0 and keys + 8 i >= keys;
   the others the engine decides from the facts), reads the key and calls `jal tx_string`, returning to K ---- *)
Lemma tvo_seg_T : forall i, (i < NIT)%nat ->
  (fst (nth i its (None, PjTree.JNull)) = None ->
     tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ tvI_key PP None)) 16272 (Z.of_nat i)) ->
  (forall nm, fst (nth i its (None, PjTree.JNull)) = Some nm ->
     tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ TxModel.strp nm)) 16236 (Z.of_nat i)) ->
  tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1))) 16120 (Z.of_nat i).
Proof.
intros i Hi HNA HNO. pose proof (HKEY i Hi) as HK.
destruct (nth i its (None, PjTree.JNull)) as [[nm|] xv] eqn:Enth; cbn [fst] in HNA, HNO, HK.
- (* an object: its i-th key *)
  destruct HK as (Hob & _).
  specialize (HNO nm eq_refl). clear HNA.
  intros lyc Sc Hpc Wc memc mdc kj b rg HL HSP HLR.
  destruct (tv_key_now i nm lyc Sc Hpc Wc memc mdc kj b _ Hi ltac:(rewrite Enth; reflexivity) HL)
    as (_ & xk & k & HSTR & HBVS & HKF9).
  assert (HLENS : exists R, (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1))) ++ TxModel.strp nm ++ R =
    TxModel.tvp tv PP d).
  { apply (tvo_len i _ (TxModel.strp nm) ([[58]] ++ (if PP then [[32]] else []) ++ TxModel.tvp xv PP (d + 1)) Hi).
    rewrite Enth. cbn [fst snd tvI_key]. rewrite <- ?app_assoc. reflexivity. }
  assert (HN' : tvo_SEG ((tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1))) ++ TxModel.strp nm) 16236
    (Z.of_nat i)) by (rewrite <- !app_assoc; exact HNO).
  clear HNO.
  pose proof HLR as (HMR & R3 & R4 & R8 & R19 & R21 & R22 & R24 & R26).
  destruct (tv_fields_now lyc Sc Hpc Wc memc mdc kj b _ _ _ _ _ _ _ _ HL HHDR)
    as ((Hty & Vty) & (Hkd & Vkd) & (Hky & Vky) & (Hn & Vn)).
  assert (ETY : TV_TY = 6) by (unfold TV_TY; rewrite Hob; reflexivity). rewrite ETY in Hty, Vty.
  pose proof HL as (HJ & _ & HTX & HRO & _ & HRAc & _ & HSV). pose proof HTX as (capX & fcX & owX & preX & _ & _ & HMN & _).
  pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
  pose proof tv_stk_facts as (SK0 & SK1 & SK2 & SK3 & SK4 & SK5 & SK6). pose proof (tv_stkv nn) as ESK.
  destruct (tvo_cnt_facts ltac:(lia)) as (Hk4 & Hkc & Hcap1 & Hn42 & _).
  pose proof HKF9 as (Hi0 & Hky4 & Hkyc & _).
  assert (U58 : U (TE regs rg (tvo_more true kids keys (Z.of_nat NIT) (Z.of_nat i) xk)) (SOff 58 0) = Z.of_nat i)
    by (apply (U_atom _ 58 (Z.of_nat i)); [tv_ewc; exact R26 | lia]).
  assert (U66 : U (TE regs rg (tvo_more true kids keys (Z.of_nat NIT) (Z.of_nat i) xk)) (SOff 66 0) = keys)
    by (apply (U_atom _ 66 keys); [tv_ewc; reflexivity | lia]).
  assert (U68 : U (TE regs rg (tvo_more true kids keys (Z.of_nat NIT) (Z.of_nat i) xk)) (SOff 68 0) = keys + 8 * Z.of_nat i)
    by (apply (U_atom _ 68 (keys + 8 * Z.of_nat i)); [tv_ewc; reflexivity | lia]).
  assert (HCS : conds_ok (TE regs rg (tvo_more true kids keys (Z.of_nat NIT) (Z.of_nat i) xk))
    [mkAC BC_EQ (SAlu ALU_SRL (SOff 58 0) (SLit 60)) (SLit 0); mkAC BC_GEU (SOff 68 0) (SOff 66 0)]).
  { split; [|split; [|exact I]]; apply tvo_condU; cbv iota beta.
    - apply (tvo_U_srl60 _ (Z.of_nat i) U58). lia.
    - rewrite U66, U68. lia. }
  destruct (tv_M_entry_B 16120 6 true rg Wc memc kids keys (Z.of_nat NIT) (Z.of_nat i) xk _ HMR HSV HSP Hty Vty
    ltac:(lia) Vkd Hky Vky ltac:(lia) Vn ltac:(lia) R26 HRAc (fun _ => conj R24 HKF9) HCS) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more true kids keys (Z.of_nat NIT) (Z.of_nat i) xk))) by apply te_env.
  paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
  assert (Hm : forall y, rdW Wc (ms_mem ms) y = rdW Wc memc y) by tv_nowr HFr.
  assert (AV : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a)
    by (intros a; unfold aview, mbyte; rewrite Hm; reflexivity).
  pose proof (tv_live_same lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ b _ HL HJ Hm HMN) as HL2.
  clear HF HG HFr.
  pose proof (tvo_lregs_sym _ true kids keys (Z.of_nat NIT) (Z.of_nat i) xk _ ms rg (Z.of_nat i) HS
    ltac:(vm_compute; reflexivity) HLR) as HLRc.
  assert (HSPc : tv_spill Wc (ms_mem ms))
    by (apply (proj2 (tv_frame_keep Wc Wc memc (ms_mem ms) ltac:(intros a _; apply AV))); exact HSP).
  prreg HS (1%bv : bv 5) Q1; prreg HS (11%bv : bv 5) Q11.
  lazymatch type of HL2 with tv_liveR _ _ _ _ _ _ ?mdx ?kjx _ ?Px =>
    apply (tv_str_call Wc _ _ ms mdx lyc Sc Hpc kjx b Px xk k nm HS
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
  all: try (tv_ewc; reflexivity).
  all: try exact HL2.
  all: try (tvo_callregs_tac HS HMR R3 R4 R8).
  all: try (tv_reg Q11; reflexivity).
  all: try (apply (PRH_Reader.pj_cstrR_frame SEGS (rdW Wc memc) (rdW Wc (ms_mem ms)) (prh_lin Lam) xk k nm HSTR);
    intros y _; unfold mbyte; rewrite Hm; reflexivity).
  all: try exact (tv_bvis_av Wc memc (ms_mem ms) xk k AV HBVS).
  all: try exact HLENS.
  all: try (apply (tvo_kont_seg Wc ms _ _ 16236 (Z.of_nat i)); [exact HN' | exact HSPc | exact HLRc | exact Q1]).
- (* an array: on to Sp *)
  pose proof HK as Hob. specialize (HNA eq_refl). clear HNO.
  cbn [tvI_key] in HNA. rewrite app_nil_r in HNA.
  tvo_open.
  destruct (tvo_cnt_facts ltac:(lia)) as (Hk4 & Hkc & Hcap1 & Hn42 & _).
  assert (ETY : TV_TY = 5) by (unfold TV_TY; rewrite Hob; reflexivity). rewrite ETY in Hty, Vty.
  destruct (tv_M_entry_B 16120 5 false rg Wc memc kids keys (Z.of_nat NIT) (Z.of_nat i) 0 [] HMR HSV HSP Hty Vty
    ltac:(lia) Vkd Hky Vky ltac:(lia) Vn ltac:(lia) R26 HRAc ltac:(discriminate) I) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0))) by apply te_env.
  paj_run_to_tok_x_inv (RUNTOIR mem) HS HJ SHOK HMN TV_SPAN 16272; [tv_awr_ro|].
  tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP (Z.of_nat i).
  pmkst HS. exact (HNA _ _ _ _ _ _ _ _ _ HL2 HSPc HLRc).
Qed.

(* ---- K: after the key (B 0x85638, offset 16236): `jal tx_put` of ':' (.str.23, band offset 70240, the spill
   40(sp)), returning to Co ---- *)
Lemma tvo_seg_K : forall i nm, (i < NIT)%nat -> fst (nth i its (None, PjTree.JNull)) = Some nm ->
  tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ (TxModel.strp nm ++ [[58]]))) 16252
    (Z.of_nat i) ->
  tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ TxModel.strp nm)) 16236 (Z.of_nat i).
Proof.
intros i nm Hi Hko HNEXT.
destruct (nth i its (None, PjTree.JNull)) as [ko xv] eqn:Enth. cbn [fst] in Hko. subst ko.
assert (HLENq : exists R, (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ TxModel.strp nm)) ++
  [[58]] ++ R = TxModel.tvp tv PP d).
{ apply (tvo_len i _ [[58]] ((if PP then [[32]] else []) ++ TxModel.tvp xv PP (d + 1)) Hi).
  rewrite Enth. cbn [fst snd tvI_key]. rewrite <- ?app_assoc. reflexivity. }
assert (HN' : tvo_SEG ((tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ TxModel.strp nm)) ++ [[58]])
  16252 (Z.of_nat i)) by (rewrite <- !app_assoc; exact HNEXT).
clear HNEXT.
tvo_open.
destruct (tvo_cnt_facts ltac:(lia)) as (Hk4 & Hkc & Hcap1 & Hn42 & _).
destruct (tv_M_entry_B 16236 TV_TY false rg Wc memc kids keys (Z.of_nat NIT) (Z.of_nat i) 0 [] HMR HSV HSP
  Hty Vty ltac:(lia) Vkd Hky Vky ltac:(lia) Vn ltac:(lia) R26 HRAc ltac:(discriminate) I) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0))) by apply te_env.
unfold TV_TY in *. destruct ob.
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP (Z.of_nat i).
all: prreg HS (1%bv : bv 5) Q1; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12.
all: pose proof HL2 as (HJ2 & _ & _ & HRO2 & _).
all: destruct (tv_lit_src_at lyc Sc Hpc Wc (ms_mem ms) _ 70240 [58] (proj1 HJ2) HRO2
  ltac:(cbn; tauto) ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
all: lazymatch type of HL2 with tv_liveR _ _ _ _ _ _ ?mdx ?kjx _ ?Px =>
  apply (tv_put_call Wc _ _ ms mdx lyc Sc Hpc kjx b Px (VAL (A_OBJ 2) + 70240) [58] HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
all: try (tv_ewc; reflexivity).
all: try exact HL2.
all: try (tvo_callregs_tac HS HMR R3 R4 R8).
all: try (rewrite Q11; tv_ewc; rewrite unsigned_lit_small by (change 243%nat with (A_OBJ 2); lia); reflexivity).
all: try (rewrite Q12; reflexivity).
all: try exact HSRC.
all: try exact HKEPT.
all: try exact HDISJ.
all: try exact HLENq.
all: try (apply (tvo_kont_seg Wc ms _ _ 16252 (Z.of_nat i)); [exact HN' | exact HSPc | exact HLRc | exact Q1]).
Qed.

(* ---- Co: after the colon (B 0x85648, offset 16252): `beqz s3`; for pretty ' ' (.str.24, band offset 70272, the
   spill 32(sp)), on to Sp ---- *)
Lemma tvo_seg_Co : forall i nm, (i < NIT)%nat -> fst (nth i its (None, PjTree.JNull)) = Some nm ->
  tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ tvI_key PP (Some nm))) 16272 (Z.of_nat i) ->
  tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ (TxModel.strp nm ++ [[58]]))) 16252
    (Z.of_nat i).
Proof.
intros i nm Hi Hko HNEXT.
destruct (nth i its (None, PjTree.JNull)) as [ko xv] eqn:Enth. cbn [fst] in Hko. subst ko.
assert (HLENq : pretty <> 0 -> exists R,
  (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++ (TxModel.strp nm ++ [[58]]))) ++ [[32]] ++ R =
  TxModel.tvp tv PP d).
{ intros Hpr.
  apply (tvo_len i _ [[32]] (TxModel.tvp xv PP (d + 1)) Hi).
  rewrite Enth. cbn [fst snd tvI_key]. rewrite (tv_pp_true Hpr), <- !app_assoc. reflexivity. }
assert (HN1 : pretty <> 0 -> tvo_SEG ((tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++
  (TxModel.strp nm ++ [[58]]))) ++ [[32]]) 16272 (Z.of_nat i)).
{ intros Hpr. cbn [tvI_key] in HNEXT. rewrite (tv_pp_true Hpr) in HNEXT |- *. rewrite <- !app_assoc. exact HNEXT. }
assert (HN0 : pretty = 0 -> tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++
  (TxModel.strp nm ++ [[58]]))) 16272 (Z.of_nat i)).
{ intros Hpr. cbn [tvI_key] in HNEXT. rewrite (tv_pp_false Hpr) in HNEXT |- *. rewrite app_nil_r in HNEXT. exact HNEXT. }
clear HNEXT.
tvo_open.
destruct (tvo_cnt_facts ltac:(lia)) as (Hk4 & Hkc & Hcap1 & Hn42 & _).
destruct (tv_M_entry_B 16252 TV_TY false rg Wc memc kids keys (Z.of_nat NIT) (Z.of_nat i) 0 [] HMR HSV HSP
  Hty Vty ltac:(lia) Vkd Hky Vky ltac:(lia) Vn ltac:(lia) R26 HRAc ltac:(discriminate) I) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0))) by apply te_env.
pose (BR := paj_branchR (PI := PA) WR).
unfold TV_TY in *. destruct ob.
all: psrr_branch_tok (RUNIR mem) BR HS SHOK TV_SPAN.
all: rewrite branch_eq_U, U_SLit in Hc; change (zcanon 0) with 0 in Hc.
all: tv_pretty_hc Hc R19.
1,3: apply Z.eqb_eq, tv_pretty_mod in Hc;
  paj_run_to_tok_x_inv (RUNTOIR mem) HS HJ SHOK HMN TV_SPAN 16272; [tv_awr_ro|];
  tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP (Z.of_nat i);
  pmkst HS; exact (HN0 Hc _ _ _ _ _ _ _ _ _ HL2 HSPc HLRc).
all: apply Z.eqb_neq in Hc; assert (Hpr : pretty <> 0) by (intros E; apply Hc; rewrite E; reflexivity).
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: tvo_after lyc Sc Hpc Wc memc mdc kj b rg ms HL HJ HFr HF HG HS HLR HSP (Z.of_nat i).
all: prreg HS (1%bv : bv 5) Q1; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12.
all: pose proof HL2 as (HJ2 & _ & _ & HRO2 & _).
all: destruct (tv_lit_src_at lyc Sc Hpc Wc (ms_mem ms) _ 70272 [32] (proj1 HJ2) HRO2
  ltac:(cbn; tauto) ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
all: lazymatch type of HL2 with tv_liveR _ _ _ _ _ _ ?mdx ?kjx _ ?Px =>
  apply (tv_put_call Wc _ _ ms mdx lyc Sc Hpc kjx b Px (VAL (A_OBJ 2) + 70272) [32] HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
all: try (tv_ewc; reflexivity).
all: try exact HL2.
all: try (tvo_callregs_tac HS HMR R3 R4 R8).
all: try (rewrite Q11; tv_ewc; rewrite unsigned_lit_small by (change 243%nat with (A_OBJ 2); lia); reflexivity).
all: try (rewrite Q12; reflexivity).
all: try exact HSRC.
all: try exact HKEPT.
all: try exact HDISJ.
all: try exact (HLENq Hpr).
all: try (apply (tvo_kont_seg Wc ms _ _ 16272 (Z.of_nat i)); [exact (HN1 Hpr) | exact HSPc | exact HLRc | exact Q1]).
Qed.

(* ---- Sp: after the space (B 0x8565c, offset 16272): the kids field's shadow, kids + 56 i under UBSan's pointer
   checks (seated: kids + 56 i >= kids, and the `mulh` overflow test 0) and the depth flag s9 = 0, then
   `jal tx_value` (t, kids + 56 i, pretty, d + 1): the recursion, returning to I ---- *)
Lemma tvo_seg_Sp : forall i, (i < NIT)%nat -> tvo_SEG (tvo_Pl (Datatypes.S i)) 16364 (Z.of_nat i) ->
  tvo_SEG (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++
    tvI_key PP (fst (nth i its (None, PjTree.JNull))))) 16272 (Z.of_nat i).
Proof.
intros i Hi HNEXT. tvo_open.
destruct (tvo_cnt_facts ltac:(lia)) as (Hk4 & Hkc & Hcap1 & Hn42 & _).
assert (U58 : U (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0)) (SOff 58 0) = Z.of_nat i)
  by (apply (U_atom _ 58 (Z.of_nat i)); [tv_ewc; exact R26 | lia]).
assert (U65 : U (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0)) (SOff 65 0) = kids)
  by (apply (U_atom _ 65 kids); [tv_ewc; reflexivity | lia]).
assert (HCS : conds_ok (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0))
  [mkAC BC_GEU (SAlu ALU_ADD (SMd M_MUL (SOff 58 0) (SLit 56)) (SOff 65 0)) (SOff 65 0);
   mkAC BC_EQ (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 58 0) (SLit 56))
     (SAlu ALU_SRA (SMd M_MUL (SOff 58 0) (SLit 56)) (SLit 63)))) (SLit 0)]).
{ split; [|split; [|exact I]]; apply tvo_condU; cbv iota beta.
  - rewrite (tvo_U_kid _ (Z.of_nat i) kids U58 U65) by lia. rewrite U65. lia.
  - apply (tvo_U_mulh _ (Z.of_nat i) U58). lia. }
destruct (tv_M_entry_B 16272 TV_TY false rg Wc memc kids keys (Z.of_nat NIT) (Z.of_nat i) 0 _ HMR HSV HSP
  Hty Vty ltac:(lia) Vkd Hky Vky ltac:(lia) Vn ltac:(lia) R26 HRAc ltac:(discriminate) HCS) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0))) by apply te_env.
destruct (tv_item_now i lyc Sc Hpc Wc memc mdc kj b _ Hi HL) as (Dx & HNx & HDx & HHx & HRAx & HBVx & HAPx & HDKx).
assert (EPS : (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++
    tvI_key PP (fst (nth i its (None, PjTree.JNull))))) ++ TxModel.tvp (snd (nth i its (None, PjTree.JNull))) PP (d + 1) =
  tvo_Pl (Datatypes.S i)) by (rewrite (tvo_Pl_S i Hi), <- !app_assoc; reflexivity).
assert (Enn : nn = Nat.succ (Nat.pred nn)) by (symmetry; apply Nat.succ_pred; lia).
assert (HLENV : exists R, (tvo_Pl i ++ (WriterValue.wcomma i ++ WriterValue.wind PP (d + 1) ++
    tvI_key PP (fst (nth i its (None, PjTree.JNull))))) ++
  TxModel.tvp (snd (nth i its (None, PjTree.JNull))) PP (d + 1) ++ R = TxModel.tvp tv PP d).
{ apply (tvo_len i _ _ [] Hi). rewrite app_nil_r, <- !app_assoc. reflexivity. }
rewrite <- EPS in HNEXT. clear EPS.
unfold TV_TY in *. destruct ob.
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: assert (Hm : forall y, rdW Wc (ms_mem ms) y = rdW Wc memc y) by tv_nowr HFr.
all: assert (AV : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a)
  by (intros a; unfold aview, mbyte; rewrite Hm; reflexivity).
all: pose proof (tv_live_same lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ b _ HL HJ Hm HMN) as HL2.
all: clear HF HG HFr.
all: pose proof (tvo_lregs_sym _ false kids keys (Z.of_nat NIT) (Z.of_nat i) 0 _ ms rg (Z.of_nat i) HS
  ltac:(vm_compute; reflexivity) HLR) as HLRc.
all: assert (HSPc : tv_spill Wc (ms_mem ms))
  by (apply (proj2 (tv_frame_keep Wc Wc memc (ms_mem ms) ltac:(intros a _; apply AV))); exact HSP).
all: prreg HS (1%bv : bv 5) Q1; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12; prreg HS (13%bv : bv 5) Q13.
all: lazymatch type of HL2 with tv_liveR _ _ _ _ _ _ ?mdx ?kjx _ ?Px =>
  apply (tv_val_call Wc _ _ ms mdx lyc Sc Hpc kjx b Px (Nat.pred nn) (kids + 56 * Z.of_nat i)
    (snd (nth i its (None, PjTree.JNull))) Dx Enn HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
all: try (tv_ewc; reflexivity).
all: try exact HL2.
all: try (tvo_callregs_tac HS HMR R3 R4 R8).
all: try (tv_reg Q11; rewrite R21; unfold w64; apply bv_eq; cbn [alu64 alu]; rewrite bv_add_unsigned, !Z_to_bv_unsigned;
  unfold bv_wrap; rewrite <- Zplus_mod; f_equal; lia).
all: try (tv_reg Q12; rewrite R19; exact H12).
all: try (tv_reg Q13; exact R22).
all: try lia.
all: try exact (tv_node_same Wc memc (ms_mem ms) _ _ _ Hm HNx).
all: try exact HDx.
all: try exact HHx.
all: try (eapply range_addressable_agree; [|exact HRAx]; intros y _; apply AV).
all: try (rewrite Forall_forall in HBVx |- *; intros bk Hbk; exact (tv_bvis_av Wc memc (ms_mem ms) _ _ AV (HBVx bk Hbk))).
all: try exact HAPx.
all: try exact HLENV.
all: try (apply (tvo_kont_seg Wc ms _ _ 16364 (Z.of_nat i)); [exact HNEXT | exact HSPc | exact HLRc | exact Q1]).
Qed.

(* ---- I: after the item's tx_value (B 0x856b8, offset 16364): n's shadow (the spill 80(sp)), n re-read, i := i + 1
   (s10, s8, s5); `bltu s10,a0` back to the loop head, or out: s5 := (n = 0) = 0, `beqz s3`, for pretty the
   closing tx_line(t, d) (the spill 24(sp)), then X ---- *)
Lemma tvo_seg_I : forall i, (i < NIT)%nat ->
  ((Datatypes.S i < NIT)%nat -> tvo_SEG (tvo_Pl (Datatypes.S i)) TVO_LH_B (Z.of_nat (Datatypes.S i))) ->
  tvo_SEG (tvo_Pl (Datatypes.S i)) 16364 (Z.of_nat i).
Proof.
intros i Hi HLH.
assert (HCC : tv_close its PP d = WriterValue.wind PP d) by (apply tvo_close_eq; lia).
pose proof tvo_len_close as HLC. rewrite HCC in HLC.
pose proof tvo_seg_X as HX.
tvo_open.
destruct (tvo_cnt_facts ltac:(lia)) as (Hk4 & Hkc & Hcap1 & Hn42 & _).
destruct (tv_M_entry_B 16364 TV_TY false rg Wc memc kids keys (Z.of_nat NIT) (Z.of_nat i) 0 [] HMR HSV HSP
  Hty Vty ltac:(lia) Vkd Hky Vky ltac:(lia) Vn ltac:(lia) R26 HRAc ltac:(discriminate) I) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) (Z.of_nat i) 0))) by apply te_env.
pose (BR := paj_branchR (PI := PA) WR).
unfold TV_TY in *. destruct ob.
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: assert (Hm : forall y, rdW Wc (ms_mem ms) y = rdW Wc memc y) by tv_nowr HFr.
all: assert (AV : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a)
  by (intros a; unfold aview, mbyte; rewrite Hm; reflexivity).
all: pose proof (tv_live_same lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ b _ HL HJ Hm HMN) as HL1.
all: clear HF HG HFr.
all: psrr_branch_tok (RUNIR mem) BR HS SHOK TV_SPAN.
all: rewrite branch_ltu_U, U_SOff, (U_atom _ 67 (Z.of_nat NIT)) in Hc by (first [tv_ewc; reflexivity | lia]).
all: tv_ewc_in Hc; rewrite R26 in Hc; unfold w64 in Hc; rewrite unsigned_lit_small in Hc by lia.
all: rewrite YP0m.zcanon_small in Hc by (unfold M64; lia).
all: rename ms into msA.
(* back to the head with i + 1 *)
1,3: apply Z.ltb_lt in Hc; assert (Hlt : (Datatypes.S i < NIT)%nat) by lia;
  paj_run_to_tok_x_inv (RUNTOIR mem) HS HJ SHOK HMN TV_SPAN TVO_LH_B; [tv_awr_ro|];
  tv_same HFr Hm2;
  pose proof (tv_live_same _ _ _ _ _ _ _ _ _ _ _ _ HL1 HJ Hm2 HMN) as HL2;
  assert (AV2 : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a)
    by (intros a; rewrite <- (AV a); unfold aview, mbyte; rewrite Hm2; reflexivity);
  assert (HSP2 : tv_spill Wc (ms_mem ms))
    by (apply (proj2 (tv_frame_keep Wc Wc memc (ms_mem ms) ltac:(intros a _; apply AV2))); exact HSP);
  clear HF HG HFr;
  prreg HS (21%bv : bv 5) Q21; prreg HS (24%bv : bv 5) Q24; prreg HS (26%bv : bv 5) Q26;
  assert (N26 : getr (ms_regs ms) 26 = w64 (Z.of_nat i + 1))
    by (apply (tv_reg_off _ _ _ 58 1 (Z.of_nat i) Q26); [tv_ewc; exact R26 | lia]);
  assert (N21 : getr (ms_regs ms) 21 = w64 (56 * (Z.of_nat i + 1)))
    by (replace (56 * (Z.of_nat i + 1)) with (56 * Z.of_nat i + 56) by lia;
        apply (tv_reg_off _ _ _ 53 56 (56 * Z.of_nat i) Q21); [tv_ewc; exact R21 | lia]);
  assert (N24 : getr (ms_regs ms) 24 = w64 (8 * (Z.of_nat i + 1)))
    by (replace (8 * (Z.of_nat i + 1)) with (8 * Z.of_nat i + 8) by lia;
        apply (tv_reg_off _ _ _ 56 8 (8 * Z.of_nat i) Q24); [tv_ewc; exact R24 | lia]);
  pose proof (tvo_lregs_step _ false kids keys (Z.of_nat NIT) (Z.of_nat i) 0 _ ms rg (Z.of_nat i) HS
    ltac:(vm_compute; reflexivity) HLR N21 N24 N26) as HLRn;
  rewrite <- (Nat2Z.inj_succ i : Z.of_nat (Datatypes.S i) = Z.of_nat i + 1) in HLRn;
  pmkst HS; exact (HLH Hlt _ _ _ _ _ _ _ _ _ HL2 HSP2 HLRn).
(* the loop is done: S i = NIT *)
all: apply Z.ltb_ge in Hc; assert (HSN : Datatypes.S i = NIT) by lia.
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: tv_same HFr Hm2.
all: pose proof (tv_live_same _ _ _ _ _ _ _ _ _ _ _ _ HL1 HJ Hm2 HMN) as HL2.
all: clear HF HG HFr.
all: psrr_branch_tok (RUNIR mem) BR HS SHOK TV_SPAN.
all: rewrite branch_eq_U, U_SLit in Hc0; change (zcanon 0) with 0 in Hc0.
all: tv_pretty_hc Hc0 R19.
all: rename ms into msB.
(* pretty = 0: on to X *)
1,3: apply Z.eqb_eq, tv_pretty_mod in Hc0;
  paj_run_to_tok_x_inv (RUNTOIR mem) HS HJ SHOK HMN TV_SPAN 16440; [tv_awr_ro|];
  tv_same HFr Hm3;
  pose proof (tv_live_same _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ Hm3 HMN) as HL3;
  clear HF HG HFr;
  pose proof (tvo_bregs_sym _ false kids keys (Z.of_nat NIT) (Z.of_nat i) 0 _ ms rg (Z.of_nat i) HS
    ltac:(vm_compute; reflexivity) HLR) as HBR;
  assert (EPX : tvo_Pl NIT ++ tv_close its PP d = tvo_Pl (Datatypes.S i))
    by (rewrite HCC, (tv_pp_false Hc0), <- HSN; cbn [WriterValue.wind]; apply app_nil_r);
  rewrite EPX in HX;
  pmkst HS; exact (HX _ _ _ _ _ _ _ _ _ HL3 HBR).
(* pretty <> 0: the closing tx_line(t, d) *)
all: apply Z.eqb_neq in Hc0; assert (Hpr : pretty <> 0) by (intros E; apply Hc0; rewrite E; reflexivity).
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: tv_same HFr Hm4.
all: pose proof (tv_live_same _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ Hm4 HMN) as HL4.
all: clear HF HG HFr.
all: pose proof (tvo_bregs_sym _ false kids keys (Z.of_nat NIT) (Z.of_nat i) 0 _ ms rg (Z.of_nat i) HS
  ltac:(vm_compute; reflexivity) HLR) as HBR.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (11%bv : bv 5) Q11.
all: assert (HLENX : exists R, tvo_Pl (Datatypes.S i) ++ WriterValue.wind true d ++ R = TxModel.tvp tv PP d)
  by (rewrite HSN; rewrite (tv_pp_true Hpr) in HLC |- *; exact HLC).
all: lazymatch type of HL4 with tv_liveR _ _ _ _ _ _ ?mdx ?kjx _ ?Px =>
  apply (tv_line_call Wc _ _ ms mdx lyc Sc Hpc kjx b Px d HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) end.
all: try (tv_ewc; reflexivity).
all: try exact HL4.
all: try (tvo_callregs_tac HS HMR R3 R4 R8).
all: try (tv_reg Q11; exact H13).
all: try (split; [exact Hd0 | lia]).
all: try exact HLENX.
all: intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 HL5 Kfr HP.
all: rewrite Q1.
all: assert (EPX : tvo_Pl NIT ++ tv_close its PP d = tvo_Pl (Datatypes.S i) ++ WriterValue.wind true d).
all: try (rewrite HCC, (tv_pp_true Hpr), <- HSN; reflexivity).
all: rewrite EPX in HX.
all: exact (HX _ _ _ _ _ _ _ _ _ HL5 (tv_bregs_B_pres _ _ HBR HP)).
Qed.

(* ==== THE LOOP, by induction on the items left ==== *)
Lemma tvo_loop : forall k i, (i < NIT)%nat -> (NIT - i)%nat = k -> tvo_SEG (tvo_Pl i) TVO_LH_B (Z.of_nat i).
Proof.
induction k as [|k IH]; intros i Hi Hk; [lia|].
assert (HI : tvo_SEG (tvo_Pl (Datatypes.S i)) 16364 (Z.of_nat i))
  by (apply (tvo_seg_I i Hi); intros Hlt; apply (IH (Datatypes.S i) Hlt); rewrite Nat.sub_succ_r, Hk; reflexivity).
pose proof (tvo_seg_Sp i Hi HI) as HSp.
apply (tvo_seg_L i Hi). apply (tvo_seg_C1 i Hi). apply (tvo_seg_T i Hi).
- intros Hko. rewrite Hko in HSp. exact HSp.
- intros nm Hko. apply (tvo_seg_K i nm Hi Hko). apply (tvo_seg_Co i nm Hi Hko). rewrite Hko in HSp. exact HSp.
Qed.

(* ---- E: the empty bracket's close (B 0x856f0, offset 16420; n = 0, s5 = 1): `beqz s3` and `bnez s5`, both to X with
   nothing appended between the brackets ---- *)
Lemma tvo_seg_E : NIT = 0%nat -> forall lyc Sc Hpc Wc memc mdc kj b rg,
  tv_liveR WR lyc Sc Hpc Wc memc mdc kj b (tvo_Pl 0) -> tv_bregs_B rg -> getr rg 19 = getr regs 12 ->
  getr rg 21 = w64 1 ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + TV_CLOSE_OFF_B)) memc (seg_rom SEGS)) mdc) QF.
Proof.
intros HN0 lyc Sc Hpc Wc memc mdc kj b rg HL HBR R19 R21.
pose proof tvo_seg_X as HX.
assert (EPX : tvo_Pl NIT ++ tv_close its PP d = tvo_Pl 0)
  by (rewrite HN0; destruct its; [apply app_nil_r | cbn in HN0; discriminate]).
rewrite EPX in HX.
destruct (tv_fields_now lyc Sc Hpc Wc memc mdc kj b _ _ _ _ _ _ _ _ HL HHDR)
  as ((Hty & Vty) & (Hkd & Vkd) & (Hky & Vky) & (Hn & Vn)).
pose proof HL as (HJ & _ & HTX & HRO & _ & HRAc & _ & HSV). pose proof HTX as (capX & fcX & owX & preX & _ & _ & HMN & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (tv_X_entry_B TV_CLOSE_OFF_B TV_TY rg Wc memc kids keys (Z.of_nat NIT) HBR HSV Hty Vty Hkd Vkd Hky Vky Hn Vn HRAc)
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (TE regs rg (tvo_more false kids keys (Z.of_nat NIT) 0 0))) by apply te_env.
pose (BR := paj_branchR (PI := PA) WR).
unfold TV_TY, TV_CLOSE_OFF_B in *. destruct ob.
all: psrr_branch_tok (RUNIR mem) BR HS SHOK TV_SPAN.
all: rewrite branch_eq_U, U_SLit in Hc; change (zcanon 0) with 0 in Hc.
all: tv_pretty_hc Hc R19.
(* pretty = 0: `beqz s3` to X *)
1,3: paj_run_to_tok_x_inv (RUNTOIR mem) HS HJ SHOK HMN TV_SPAN 16440; [tv_awr_ro|];
  tv_same HFr Hm; pose proof (tv_live_same _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm HMN) as HL2; clear HF HG HFr;
  pose proof (tvo_bregs_symX _ false kids keys (Z.of_nat NIT) 0 0 _ _ rg HS ltac:(vm_compute; reflexivity) HBR) as HBR2;
  pmkst HS; exact (HX _ _ _ _ _ _ _ _ _ HL2 HBR2).
(* pretty <> 0: `bnez s5` with s5 = 1 to X *)
all: paj_run_tok_x_inv (RUNIR mem) HS HJ SHOK HMN TV_SPAN; [tv_awr_ro|].
all: tv_same HFr Hm.
all: pose proof (tv_live_same _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm HMN) as HL1.
all: clear HF HG HFr.
all: psrr_branch_tok (RUNIR mem) BR HS SHOK TV_SPAN.
all: rewrite branch_ne_U, U_SLit, (U_atom _ 53 1) in Hc0 by (first [tv_ewc; exact R21 | lia]).
all: change (zcanon 0) with 0 in Hc0.
1,3: paj_run_to_tok_x_inv (RUNTOIR mem) HS HJ SHOK HMN TV_SPAN 16440; [tv_awr_ro|];
  tv_same HFr Hm2; pose proof (tv_live_same _ _ _ _ _ _ _ _ _ _ _ _ HL1 HJ Hm2 HMN) as HL2; clear HF HG HFr;
  pose proof (tvo_bregs_symX _ false kids keys (Z.of_nat NIT) 0 0 _ _ rg HS ltac:(vm_compute; reflexivity) HBR) as HBR2;
  pmkst HS; exact (HX _ _ _ _ _ _ _ _ _ HL2 HBR2).
all: exfalso; vm_compute in Hc0; discriminate Hc0.
Qed.

(* ---- P: after the opening bracket (B 0x8550c, offset 15936): s4 = v + 40, n's shadow, n; for n = 0 the close seam
   (tv_run_n0_B) and E, else the loop's set-up (tvo_run_P_nz) and the loop ---- *)
Lemma tvo_seg_P : forall lyc Sc Hpc Wc memc mdc kj b rg,
  tv_liveR WR lyc Sc Hpc Wc memc mdc kj b (tvo_Pl 0) -> tv_bregs_B rg -> getr rg 19 = getr regs 12 -> getr rg 21 = w64 1 ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + TV_RET_OPEN_B)) memc (seg_rom SEGS)) mdc) QF.
Proof.
intros lyc Sc Hpc Wc memc mdc kj b rg HL HBR R19 R21.
destruct (tv_fields_now lyc Sc Hpc Wc memc mdc kj b _ _ _ _ _ _ _ _ HL HHDR)
  as ((Hty & Vty) & (Hkd & Vkd) & (Hky & Vky) & (Hn & Vn)).
destruct (tv_hdr_now lyc Sc Hpc Wc memc mdc kj b _ _ _ _ _ _ _ _ HL HHDR) as (Hst & Vst).
pose proof HL as (HJ & HWIN & HTX & HRO & HFK & HRAc & HBVc & HSV).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFWIN as (Hdw0 & Hdw16 & Hdtop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & SK2 & SK3 & SK4 & SK5 & SK6). pose proof (tv_stkv nn) as ESK.
pose proof (Nat2Z.is_nonneg nn) as Hnn0.
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
pose proof HBR as (R2 & R9 & R18 & R3 & R4 & R8).
pose proof (ajxR_pres HJ) as HPRS.
assert (Hsp : spZ rg = sp0 - 192) by (unfold spZ at 1; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hpres : forall a, sp0 - 192 <= a < sp0 -> apresent (w_H Wc) memc a) by (intros a Ha; apply HPRS; lia).
destruct (Nat.eq_dec NIT 0) as [HN0 | HN0].
- (* n = 0: the close seam, then E *)
  apply (tv_run_n0_B STKV dw sp0 ly _ Hp W mem md lyc Sc Hpc Wc rg memc mdc kj FP0 TV_TY v str kids keys d QF HJ
    ltac:(lia) Hdw0 Hsp Hal16 ltac:(lia) ltac:(lia) R9 Hv0 Hv8 Hvc Hvapp ltac:(lia) Hpres
    ltac:(destruct HSV as (_ & H72 & H16 & H24); split;
      [replace (sp0 - 192 + 16) with (sp0 - 176) by lia; exact H16
      | split; [replace (sp0 - 192 + 24) with (sp0 - 168) by lia; exact H24
               | replace (sp0 - 192 + 72) with (sp0 - 120) by lia; exact H72]])
    ltac:(lia) Hty Vty Hst Vst Hkd Vkd Hky Vky ltac:(rewrite HN0 in Vn; exact Vn) HRAc).
  intros E' ss' ms' mdc' kj' HS' Hrv' HJ' Hsp' P1 P3 P4 P8 P9 P18 P19 P21 HSL KP KR HMN'.
  assert (HSV' : tv_saved Wc (ms_mem ms')).
  { destruct HSV as (HSV1 & _). destruct HSL as (L16 & L24 & L72). split; [|split; [|split]].
    - intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc _ _ 8 _); [|exact (HSV1 j Hj)].
      intros i0 Hi0. apply KP; lia.
    - replace (sp0 - 120) with (sp0 - 192 + 72) by lia. exact L72.
    - replace (sp0 - 176) with (sp0 - 192 + 16) by lia. exact L16.
    - replace (sp0 - 168) with (sp0 - 192 + 24) by lia. exact L24. }
  assert (HL' : tv_liveR WR lyc Sc Hpc Wc (ms_mem ms') mdc' kj' b (tvo_Pl 0)).
  { apply (tv_live_frame lyc Sc Hpc Wc memc (ms_mem ms') mdc mdc' kj kj' b _ HL HJ'); [|exact HSV' | exact HMN'].
    intros x Hx. apply KR. lia. }
  apply (tvo_seg_E HN0 lyc Sc Hpc Wc (ms_mem ms') mdc' kj' b (ms_regs ms') HL').
  + unfold tv_bregs_B. split; [unfold w64; apply bv_eq; rewrite unsigned_lit_small by lia; exact Hsp'|].
    split; [exact P9|]. split; [rewrite P18; exact R18|]. split; [rewrite P3; exact R3|].
    split; [rewrite P4; exact R4 | rewrite P8; exact R8].
  + rewrite P19. exact R19.
  + rewrite P21. exact R21.
- (* n > 0: the set-up, then the loop from item 0 *)
  assert (HdT : (0 < PjTree.depth tv)%nat) by (pose proof (HDK 0%nat ltac:(lia)); lia).
  apply (tvo_run_P_nz lyc Sc Hpc Wc rg memc mdc kj TV_TY kids keys (Z.of_nat NIT) QF HJ Hsp R9 R18 R8
    ltac:(rewrite R19; exact H12) R3 R4 Hpres HSV Hty Vty Hkd Vkd Hky Vky ltac:(lia) Vn HRAc ltac:(lia)).
  intros E' ss' ms' mdc' kj' HS' Hrv' HJ' HLR HSV' HSP' KP KR HMN'.
  assert (HL' : tv_liveR WR lyc Sc Hpc Wc (ms_mem ms') mdc' kj' b (tvo_Pl 0)).
  { apply (tv_live_frame lyc Sc Hpc Wc memc (ms_mem ms') mdc mdc' kj kj' b _ HL HJ'); [|exact HSV' | exact HMN'].
    intros x Hx. apply KR. lia. }
  exact (tvo_loop (NIT - 0) 0 ltac:(lia) eq_refl lyc Sc Hpc Wc (ms_mem ms') mdc' kj' b (ms_regs ms') HL' HSP' HLR).
Qed.

(* ==== THE OPEN ARM from tx_value's entry: the dispatch and the opening bracket (tv_run_open_B, at SRr through
   tv_srr_then: no free before the opening call), the opening `jal tx_put` (tv_put_call, nothing appended yet, the live
   state lifted from wle to WR by tv_liveR_mono), then P ==== *)
Lemma tvo_main : SRW W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) QF.
Proof.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof tv_stk_facts as (SK0 & SK1 & SK2 & SK3 & SK4 & SK5 & SK6). pose proof (tv_stkv nn) as ESK.
pose proof (Nat2Z.is_nonneg nn) as Hnn0.
pose proof HPLACE as (Ht8 & Htlo & Hthi & _).
destruct tv_node_facts as (Hv0 & Hv8 & Hvc & Hvapp & Hvimg).
pose proof HHDR as (_ & (Rt & Vt) & _ & (Rs & Vs) & (Rk & Vk) & (Ry & Vy) & (Rn & Vn) & _).
apply tv_srr_then.
apply (tv_run_open_B TV_TY TV_OPOFF STKV dw ly S Hp W regs mem md ch v str kids keys (Z.of_nat NIT) FP0 _
  ltac:(unfold tv_open_case_B, TV_TY, TV_OPOFF; destruct ob; [right | left]; reflexivity)
  HPRE ltac:(unfold TV_FRAME_B; lia) HFWIN H11 Hv0 Hv8 Hvc Hvapp Hvimg Vt Rs Vs Rk Vk Ry Vy Rn Vn HRA HROD).
intros E' ss' ms' mdc kj HS Hrv Hpcs HE2 HJ Hms Hsp R1 R3 R4 R8 R9 R10 R11 R12 R18 R19 R21 HSL HSAV KA HMN.
apply tv_srr_now.
unfold TV_FRAME_B in Hsp, HSL, HSAV, KA.
assert (HSV : tv_saved W (ms_mem ms')).
{ destruct HSL as (L16 & L24 & L72).
  destruct HSAV as (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27).
  rewrite H13 in L24. unfold w64 in L24. rewrite unsigned_lit_small in L24 by lia.
  split; [|split; [|split]].
  - intros j Hj. do 13 (destruct j as [|j]; [cbn [nth TV_SAVED];
      lazymatch goal with |- val_mem _ _ ?a _ _ =>
        first [ replace a with (sp0 - 192 + 184) by lia; exact S1 | replace a with (sp0 - 192 + 176) by lia; exact S8
              | replace a with (sp0 - 192 + 168) by lia; exact S9 | replace a with (sp0 - 192 + 160) by lia; exact S18
              | replace a with (sp0 - 192 + 152) by lia; exact S19 | replace a with (sp0 - 192 + 144) by lia; exact S20
              | replace a with (sp0 - 192 + 136) by lia; exact S21 | replace a with (sp0 - 192 + 128) by lia; exact S22
              | replace a with (sp0 - 192 + 120) by lia; exact S23 | replace a with (sp0 - 192 + 112) by lia; exact S24
              | replace a with (sp0 - 192 + 104) by lia; exact S25 | replace a with (sp0 - 192 + 96) by lia; exact S26
              | replace a with (sp0 - 192 + 88) by lia; exact S27 ] end|]).
    lia.
  - replace (sp0 - 120) with (sp0 - 192 + 72) by lia. exact L72.
  - replace (sp0 - 176) with (sp0 - 192 + 16) by lia. exact L16.
  - replace (sp0 - 168) with (sp0 - 192 + 24) by lia. exact L24. }
assert (KA' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 192 <= a < sp0) ->
  aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) by (intros a Ha Hn; apply KA; [exact Ha | lia]).
pose proof (tv_liveR_mono _ _ _ _ _ _ _ _ _ (tv_live_init (ms_mem ms') mdc kj HJ KA' HSV HMN)) as HL0.
destruct (tv_facts_at (ms_mem ms') mdc 192 (proj1 HJ) ltac:(lia) ltac:(lia) KA') as (HRODc & _).
assert (Hin : In (TV_OPOFF, Z.of_nat (length [TV_OPEN])) [(69472, 4); (69504, 5); (69536, 4); (70144, 1); (70176, 1);
  (70208, 1); (70240, 1); (70272, 1); (70304, 1); (70336, 1)]) by (unfold TV_OPOFF; destruct ob; cbn; tauto).
destruct (tv_lit_src_at ly S Hp W (ms_mem ms') mdc TV_OPOFF [TV_OPEN] (proj1 HJ) HRODc Hin ltac:(cbn; lia)
  ltac:(intros j Hj; destruct j as [|j]; [unfold TV_OPOFF, TV_OPEN; destruct ob; vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
assert (HLEN1 : exists R, [] ++ [[TV_OPEN]] ++ R = TxModel.tvp tv PP d).
{ exists (tvI_go PP d 0 its ++ tv_close its PP d ++ [[TV_CLOSE]]). rewrite EPC. reflexivity. }
apply (tv_put_call W E' ss' ms' mdc ly S Hp kj b0 [] (VAL (A_OBJ 2) + TV_OPOFF) [TV_OPEN] HS Hrv Hpcs HE2 HL0).
- split; [unfold w64; apply bv_eq; rewrite unsigned_lit_small by lia; exact Hsp|].
  split; [exact R3|]. split; [exact R4|]. split; [rewrite R8; exact H10|]. split; [rewrite R10; exact H10|].
  split; [rewrite R1; unfold TV_RET_OPEN_B; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]|].
  unfold raZ; rewrite R1. unfold TV_RET_OPEN_B. pose proof (@pa_B_ok _ _ PA) as HBB. rewrite unsigned_lit_small by lia.
  split; [lia | apply tv_ret_ceil; cbn [TV_RETS_B In]; left; reflexivity].
- exact R11.
- exact R12.
- exact HSRC.
- exact HKEPT.
- exact HDISJ.
- exact HLEN1.
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 HL2 Kfr HP. rewrite R1.
  change ([] ++ [[TV_OPEN]]) with (tvo_Pl 0) in HL2.
  apply (tvo_seg_P ly2 S2 Hp2 W2 mem2 md2 kj2 b2 regs2 HL2).
  + unfold tv_bregs_B. rewrite (tv_ap _ _ HP 2%bv) by ts_cs. rewrite (tv_ap _ _ HP 9%bv) by ts_cs.
    rewrite (tv_ap _ _ HP 18%bv) by ts_cs. rewrite (tv_ap _ _ HP 3%bv) by ts_cs.
    rewrite (tv_ap _ _ HP 4%bv) by ts_cs. rewrite (tv_ap _ _ HP 8%bv) by ts_cs.
    split; [unfold w64; apply bv_eq; rewrite unsigned_lit_small by lia; exact Hsp|].
    split; [exact R9|]. split; [exact R18|]. split; [exact R3|]. split; [exact R4|]. rewrite R8; exact H10.
  + rewrite (tv_ap _ _ HP 19%bv) by ts_cs. exact R19.
  + rewrite (tv_ap _ _ HP 21%bv) by ts_cs. exact R21.
Qed.

End o.

(* ---- the items of an array / object as the open arm's item list ---- *)
Lemma tv_nth_mapA : forall (l : list PjTree.jv) i,
  nth i (map (fun x => (@None (list Z), x)) l) (None, PjTree.JNull) = (None, nth i l PjTree.JNull).
Proof. induction l as [|x r IH]; intros [|i]; cbn; [reflexivity | reflexivity | reflexivity | apply IH]. Qed.
Lemma tv_nth_mapO : forall (l : list (list Z * PjTree.jv)) i, (i < length l)%nat ->
  nth i (map (fun kx => (Some (fst kx), snd kx)) l) (None, PjTree.JNull) =
  (Some (fst (nth i l ([], PjTree.JNull))), snd (nth i l ([], PjTree.JNull))).
Proof. induction l as [|x r IH]; intros [|i] Hi; cbn in Hi |- *; [lia | lia | reflexivity | apply IH; lia]. Qed.

(* ==== THE FUNCTION at depth bound nn: the node's type picks the arm ==== *)
Lemma tv_main : SRW W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) QF.
Proof.
assert (G : forall x, tv = x -> SRW W (cfg_at SEGS (SIGMA AS_tx_value) regs mem md) QF); [|exact (G tv eq_refl)].
intros x Etv. pose proof HNODE as HN. rewrite Etv in HN.
destruct x as [| | | ntx bits | s | items | members]; cbn [PRH_Reader.pj_nodeR PjTree.tag] in HN;
  destruct HN as (HND & HAP & num & str & kids & keys & n & cap & HH & HC);
  pose proof HH as (_ & (Rt & Vt) & _ & (Rs & Vs) & (Rk & Vk) & (Ry & Vy) & (Rn & Vn) & _).
- (* JNull: .str.3 "null" *)
  apply (tv_main_lit 0 16688 481276 69536 4 [110; 117; 108; 108] str kids keys n ltac:(left; reflexivity)
    Vt Rs Vs Rk Vk Ry Vy Rn Vn eq_refl ltac:(rewrite Etv; reflexivity) ltac:(rewrite Etv; reflexivity)).
  intros j Hj. do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). cbn in Hj. lia.
- (* JFalse: .str.2 "false" *)
  apply (tv_main_lit 1 16704 481292 69504 5 [102; 97; 108; 115; 101] str kids keys n ltac:(right; left; reflexivity)
    Vt Rs Vs Rk Vk Ry Vy Rn Vn eq_refl ltac:(rewrite Etv; reflexivity) ltac:(rewrite Etv; reflexivity)).
  intros j Hj. do 5 (destruct j as [|j]; [vm_compute; reflexivity|]). cbn in Hj. lia.
- (* JTrue: .str "true" *)
  apply (tv_main_lit 2 16624 481212 69472 4 [116; 114; 117; 101] str kids keys n ltac:(right; right; reflexivity)
    Vt Rs Vs Rk Vk Ry Vy Rn Vn eq_refl ltac:(rewrite Etv; reflexivity) ltac:(rewrite Etv; reflexivity)).
  intros j Hj. do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). cbn in Hj. lia.
- (* JNum: the number's text *)
  destruct HC as (_ & _ & _ & _ & _ & k & (_ & Hk & _ & Hnz & Hg) & ED).
  assert (Hin : In (str, k) D) by (rewrite ED; left; reflexivity).
  apply (tv_main_num str kids keys n ntx k Vt Rs Vs Rk Vk Ry Vy Rn Vn Hnz Hg (HDLAM _ Hin) Hk
    (proj1 (Forall_forall _ _) HBV (str, k) Hin)).
  + rewrite Etv. reflexivity.
  + rewrite Etv. cbn. rewrite ?app_nil_r. reflexivity.
- (* JStr: tail-called into tx_string *)
  destruct HC as (_ & _ & _ & _ & k & HSTR & ED).
  assert (Hin : In (str, k) D) by (rewrite ED; left; reflexivity).
  apply (tv_main_str str kids keys n s k Vt Rs Vs Rk Vk Ry Vy Rn Vn HSTR (proj1 (Forall_forall _ _) HBV (str, k) Hin)).
  + rewrite Etv. reflexivity.
  + rewrite Etv. cbn. rewrite ?app_nil_r. first [reflexivity | rewrite <- s10_strp_wstr; reflexivity].
- (* JArr: the open arm, no keys *)
  destruct HC as (Hstr0 & Hky0 & HnE & Hncap & Hcap & Di & ED & HIT).
  set (its := map (fun x => (@None (list Z), x)) items).
  assert (Hlen : length its = length items) by apply length_map.
  assert (A1 : PRH_Reader.pj_hdrR SEGS (rdW W mem) v (TV_TY false) num str kids keys (Z.of_nat (length its)) cap)
    by (change (TV_TY false) with 5; rewrite Hlen, <- HnE; exact HH).
  assert (A2 : Z.of_nat (length its) <= cap) by (rewrite Hlen; lia).
  assert (A3 : (0 < length its)%nat -> In (kids, 56 * cap) D /\ (false = true -> In (keys, 8 * cap) D)).
  { intros Hn0. split; [|discriminate]. rewrite ED. apply in_or_app. left.
    destruct (Z.eqb_spec cap 0) as [E0|E0]; [rewrite Hlen in Hn0; lia | left; reflexivity]. }
  assert (A4 : forall i, (i < length its)%nat -> exists Dx,
    PRH_Reader.pj_nodeR SEGS (rdW W mem) (prh_lin Lam) (kids + 56 * Z.of_nat i) (snd (nth i its (None, PjTree.JNull))) Dx /\
    incl Dx D).
  { intros i Hi. rewrite Hlen in Hi. destruct (tv_items_nth _ items kids Di i HIT Hi) as (D1 & HN1 & Hinc).
    exists D1. unfold its. rewrite tv_nth_mapA. cbn [snd]. split; [exact HN1|].
    intros y Hy. rewrite ED. apply in_or_app. right. exact (Hinc y Hy). }
  assert (A5 : forall i, (i < length its)%nat ->
    match fst (nth i its (None, PjTree.JNull)) with
    | Some nm => false = true /\ exists x k, PRH_Reader.rd_u64 SEGS (rdW W mem) (keys + 8 * Z.of_nat i) x /\
        PRH_Reader.pj_cstrR SEGS (rdW W mem) (prh_lin Lam) x k nm /\ In (x, k) D
    | None => false = false
    end) by (intros i Hi; unfold its; rewrite tv_nth_mapA; reflexivity).
  assert (A6 : forall i, (i < length its)%nat ->
    (PjTree.depth (snd (nth i its (None, PjTree.JNull))) < PjTree.depth tv)%nat).
  { intros i Hi. unfold its. rewrite tv_nth_mapA. cbn [snd]. rewrite Etv. apply PjTree.depth_item.
    apply nth_In. rewrite Hlen in Hi. exact Hi. }
  assert (A7 : TxModel.tvp tv PP d = [TV_OPEN false] :: tvI_go PP d 0 its ++ tv_close its PP d ++ [[TV_CLOSE false]]).
  { rewrite Etv, tvp_arr, tvA_go_I. change (TV_OPEN false) with 91. change (TV_CLOSE false) with 93. unfold its.
    destruct items; reflexivity. }
  eapply (tvo_main false its num str kids keys cap); eassumption.
- (* JObj: the open arm with the members' keys *)
  destruct HC as (Hstr0 & HnE & Hncap & Hcap & Di & ED & HIT).
  set (its := map (fun kx => (Some (fst kx), snd kx)) members).
  assert (Hlen : length its = length members) by apply length_map.
  assert (A1 : PRH_Reader.pj_hdrR SEGS (rdW W mem) v (TV_TY true) num str kids keys (Z.of_nat (length its)) cap)
    by (change (TV_TY true) with 6; rewrite Hlen, <- HnE; exact HH).
  assert (A2 : Z.of_nat (length its) <= cap) by (rewrite Hlen; lia).
  assert (A3 : (0 < length its)%nat -> In (kids, 56 * cap) D /\ (true = true -> In (keys, 8 * cap) D)).
  { intros Hn0. destruct (Z.eqb_spec cap 0) as [E0|E0]; [rewrite Hlen in Hn0; lia|].
    split; [|intros _]; rewrite ED; apply in_or_app; left; cbn; tauto. }
  assert (A4 : forall i, (i < length its)%nat -> exists Dx,
    PRH_Reader.pj_nodeR SEGS (rdW W mem) (prh_lin Lam) (kids + 56 * Z.of_nat i) (snd (nth i its (None, PjTree.JNull))) Dx /\
    incl Dx D).
  { intros i Hi. rewrite Hlen in Hi.
    destruct (tv_mems_nth SEGS _ _ _ members kids keys Di i HIT Hi) as (x & k & D1 & _ & _ & _ & HN1 & Hinc).
    exists D1. unfold its. rewrite (tv_nth_mapO members i Hi). cbn [snd]. split; [exact HN1|].
    intros y Hy. rewrite ED. apply in_or_app. right. exact (Hinc y Hy). }
  assert (A5 : forall i, (i < length its)%nat ->
    match fst (nth i its (None, PjTree.JNull)) with
    | Some nm => true = true /\ exists x k, PRH_Reader.rd_u64 SEGS (rdW W mem) (keys + 8 * Z.of_nat i) x /\
        PRH_Reader.pj_cstrR SEGS (rdW W mem) (prh_lin Lam) x k nm /\ In (x, k) D
    | None => true = false
    end).
  { intros i Hi. rewrite Hlen in Hi. unfold its. rewrite (tv_nth_mapO members i Hi). cbn [fst].
    destruct (tv_mems_nth SEGS _ _ _ members kids keys Di i HIT Hi) as (x & k & D1 & Hx & Hc & Hxk & _ & _).
    split; [reflexivity|]. exists x, k. split; [exact Hx|]. split; [exact Hc|].
    rewrite ED. apply in_or_app. right. exact Hxk. }
  assert (A6 : forall i, (i < length its)%nat ->
    (PjTree.depth (snd (nth i its (None, PjTree.JNull))) < PjTree.depth tv)%nat).
  { intros i Hi. rewrite Hlen in Hi. unfold its. rewrite (tv_nth_mapO members i Hi). cbn [snd]. rewrite Etv.
    apply (PjTree.depth_member members (fst (nth i members ([], PjTree.JNull)))).
    rewrite <- surjective_pairing. apply nth_In. exact Hi. }
  assert (A7 : TxModel.tvp tv PP d = [TV_OPEN true] :: tvI_go PP d 0 its ++ tv_close its PP d ++ [[TV_CLOSE true]]).
  { rewrite Etv, tvp_obj, tvO_go_I. change (TV_OPEN true) with 123. change (TV_CLOSE true) with 125. unfold its.
    destruct members; reflexivity. }
  eapply (tvo_main true its num str kids keys cap); eassumption.
Qed.

End g.

(* ==== The kit's text ttx_value_specX (PRH_FnTx.v 7cf918708def :975-1043: the record's failed f0, the ledger's own,
   (length rp_os <= 4)%nat (:986), guarded room (:991), consumer window (:996) and run premise (:1010), SRW (:1015) over
   ONE budgeted fpostWbmR at WR (:1016), no abort arm, naming the outcome prhtx_out (:1022), DEAD (:1026), the position
   (:1040-1042)) at image B', every depth bound, by induction (the recursion's text is the bound one less) ==== *)
Theorem tx_value_B_holds : forall n, ttx_value_specX (PI := prh_img_B) (PA := PA) B ARx SK CTX0 n.
Proof.
induction n as [|n IH].
all: unfold ttx_value_specX; intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist
  ly S Hp W regs mem md ch dw t v pretty d b0 len0 cap0 f0 own tv D txt Lam peak cnt fail ran most;
  cbv zeta; intros (HPRE & HROD & HHI & HRAC & HFRM) HCL HROOM HPOS HRP4 HROOMW HCONS HDEP H10 H11 H12 H13 HPR Hd0 HdD
    HFWIN HPLACE HTRACE HREC HINV HNODE HDLAM HHOME HRA HBV HAPT HLEN HLED HEVS HLIVE HMAX HFR0.
- eapply tv_main; try eassumption. intros n' E. discriminate E.
- eapply tv_main; try eassumption. intros n' E. injection E as <-. exact IH.
Qed.

End f.
End d.

(* ---- the audit read-outs (the reporting rule): the top lemma's assumptions and statement, and the elaborated bodies of
   every definition this re-fit changed (QT, QF, tv_tx, tv_live) and of the two the record also printed (tv_cf,
   tv_kont), with every implicit argument shown (the Print implicit check) ---- *)
Print Assumptions tx_value_B_holds.
Set Printing Implicit. Unset Printing Notations.
About tx_value_B_holds.
Print QT.
Print QF.
Print tv_tx.
Print tv_live.
Print tv_liveR.
Print tv_cf.
Print tv_kont.
Unset Printing Implicit.

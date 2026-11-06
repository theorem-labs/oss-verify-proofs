(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1138 of its 1209 lines of code are new or changed and 707 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move; the wle' contract, the internal file WLE-CONTRACT.md):
   every journal of this file is at RZW := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (ajournal_xR / ajournal_xwR; so ct_bd's
   journal too) and every stretch statement concludes YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (crt102_tail_B, ct_J_call,
   ct_at_Z, ct_at_F). pj_free's text asks `v <> 0 -> hull_budget S []` at its call: ct_J_call takes
   `hull_budget Sc []` and crt102_tail_B pays it from crt_pos's run position with the Section hypothesis
   HOS4 : (length rp_os <= 4)%nat (the text's own premise) through Crt102HullPos.hull_budget_nil_of_room_pos. The inline
   release and __asan_set_shadow_f5 cross by the engine's R rules YGcallSx.aj_flag_store_xR and
   YGcallMxmn.aj_set_shadow_at_xmR (the engine lemmas are cited; no local copy of them is kept in a Section). *)
(* kb round (the Glue at c580eb0fe37c, the B' twin of lib/A/Prog/Crt102Tail.v at the A' kb head a54cc6d36c2c):
   crt_at_J_B's live state is at kb = prh_wk F_check_round_trip (66), its journal at a budget WS with wbudget [] 66 WS;
   the tail's calls (pj_free, __asan_set_shadow_f5, the inline release) store no wild trace, so the journal stays at WS
   to the `ret` (ct_bd carries it), and QF is the text's budgeted post at that WS (ct_at_F). *)
(* fuzz_preset, image B' (asan-ubsan, pin d663f82d7f488d30, twin c90d4fa54d43160b): THE TAIL of the
   walk of check_round_trip (fuzz_preset.c new:772-781), from the join J (+0x348) to the `ret` (+0x474), against the
   contract text tcheck_round_trip_specX (lib/A/PRH_FnCheck.v). Row T8. Its export is
   crt102_tail_B: `crt_at_J_B .. -> SRr SEGS Wc (crt_cfg fxk CRT_J_OFF_B rg memc mdc) QF`, for EVERY r.
   STATUS: crt102_tail_B is Qed. Its r = 1 arm is dead: crt_at_J_B's field crt_at_J_B_r0 states r = 0 (the killer is
   tcheck_round_trip_specX's entry premise prh_cons_from, PRH_FnCheck 0b6f7b597757 on: the callees' refusal arms are
   dead under it, so no r = 1 state reaches J). Its r = 0 arm reads crt_at_J_B_count's r = 0 arm: crt_pos's position,
   and copy's ORDERED free list Fc with `map (snd + cf_head) Fc = fo crt_tree_J`. Every piece is its own Qed lemma
   (ct_J_call, ct_r0_end, ct_at_Z, ct_at_F, ct_qt_keep, ct_qt_of0 and the helpers). The B' twin of Crt102Tail.v
   (crt102_tail, blob d38ea142ecbc on the base): the same design at the B' registers, offsets, spill constants and
   listing. Written new from the earlier T8 walk at commit 09469fb2a29b (its symbolic states, image
   facts, ct_qt / ct_qt_keep / ct_at_Z / ct_at_F kept; its ct_J_tail and the r = 0-only export crt102_tail_B_r0
   retired), every glue Record read and built by its NAMED FIELDS.

   INPUTS OF RECORD (by path, at commit 8d79ced8f66f; blobs by `git rev-parse --short=12`):
   - pins: B' asan-ubsan sha256 d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, its unstripped twin
     sha256 c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175; this file is image B' only.
   - the glue lib/A/Prog/Crt102Glue.v 918720d3a7b6 (the Records re-cut): crt_at_J_B (fields crt_at_J_B_live / _frm_zero
     / _fregs / _bregs / _ret / _copy_fd / _r0 / _count), crt_live, crt_side (the ledger at `ranc most ownc`, no
     position), crt_frame, crt_bregs_B, crt_pos / crt_pos_at; QT / QF (r = 0, the EXACT end position on the r = 0 arm
     only); lib/B/Prog/Crt102KitB.v 72715b66ca60 (cb_J_B_ccnt24, the class-24 bound at the B' join, CITED).
   - the contract texts: lib/A/PRH_FnPj.v dc0d0aa79c0f (tpj_free_specX: POSITION-FREE entry - closure, room_live_cf,
     `v <> 0 -> ccnt24 S <= L24 + DRV`, pj_foR with copy's order list, prh_head_wide, the ledger with its g_most /
     g_own_ran_out cells - and the position TRANSFER in its post; prhPj_free_evs, prhPj_free_evs_nil,
     prhPj_bulk_nil_pos), lib/A/PRH_PjOrder.v e5917626b82b (pj_foR), lib/A/PRH_FnCheck.v 0844ed8c0608 (the text, its
     post QT), lib/A/PRH_Base.v ee2f5cd7ed35 (fpre, prh_ledger, prh_run_at, prh_run_at_one); lib/A/CfParamsPreset.v
     b60d0f63c926 (preset_head_wide); Spec PresetReqAt.v 43c958024221, PresetRoomPos.v 943d62290e8e,
     PresetRoomPosKeep.v 4377d5b0def1.
   - the image: lib/B/Prog/CrtImgB102.v e07deaef6b0d (the B' image facts at PI_prog_B, no premise: crt_pst_img_B_cf),
     lib/A/Prog/Crt102Img.v 176eec830b61 (the B' cut offsets CRT_PC_B / CRT_J_OFF_B / CRT_Z_OFF_B / CRT_Z5_OFF_B),
     lib/B/PAImg_prog.v 15fab93fe702 (PI_prog_B, PL_prog_B), lib/B/PRH_ImgB.v 3216eca68342, lib/Reusable/YImgTop.v
     d2a97d3111ce; S1Ledger.v 8cf15eeb6311, S10Env.v d8ca1dd59ead.
   - the listing lib/B/Listing_prog.v c97cc46b3e13 (check_round_trip at slot 1111; the tail is its lines 1336-1411 =
     the internal file crt.B.s lines 212-287).
   - the engine: YCbqG c3b5d0111037, YCbqGcall 1baa92bd3c81, YCbqGcallW 49e664902830 (aj_call_xW_sp), YGcallx
     7e1faf965c0d, YGcallSx 17d7d2cdbcd1 (aj_flag_store_x), YC80x 14f84f225e8f, YC1fP 5a3e259a9c67 (paj_ret_at),
     YC1fPx 7814b594066f, YSRrMemnorm 5ffa8525936b, YGcallMxmn b47cf7942c3d (aset_shadow_realizes_xm,
     aj_set_shadow_at_xm, memnorm_frame_of), YGcfRoomLive db11c2a5eb11; Spec PresetLiveBounds f78da450d5f6.
   - rule 24: proves function check_round_trip (B' J -> ret) - proof-index check_round_trip by name: the released
     proofs are plain/ubsan only (address lookups are no evidence: no symbol table); second-agent check CONFIRM, released-branch git grep exit=1
     (recorded in the commit message of 09469fb2a29b; the record
     RULE24.md (sha256 96ef6f3404f0; internal record): no #102 walk of check_round_trip outside this one).
     Written new. Model walks read, not cited: S10TxString.v ts_G_entry / ts_at_G, H5CrtS7.v.

   THE SEGMENTS (offsets from check_round_trip's entry, DERIVED as 4 * the listing slot - 4 * 1111; Crt102Img.v's
   names):
   - J (CRT_J_OFF_B = +0x348): `mv a0, s4; jal pj_free` - one engine run (no region, so no memory change), then the
     call of pj_free's text PJFREE at n = DOC_D through YCbqGcallW.aj_call_xW_sp at window 0 (ct_J_call).
   - Z (CRT_Z_OFF_B = +0x350): the re-poison of copy's seven shadow bytes (`sb s9, 0x1c .. 0x22(s2)`, s9 = -8), the
     retired magic `sd a0, 0(s3)`, the `beqz s7`, then `addi a1, zero, 0x40; mv a0, s2; jal __asan_set_shadow_f5`, the
     call by YGcallMxmn's aj_set_shadow_at_xm (ct_at_Z).
   - F (CRT_Z5_OFF_B = +0x388): `ld a0, 0x1f8(s7); sb zero, 0(a0)` - THE INLINE RELEASE (YGcallSx.aj_flag_store_x) -
     then `j +0xa4`, `mv a0, s5; addi sp, s0, -0xe0`, the thirteen restores, `addi sp, sp, 0xe0`, to the `ret`
     (+0x474, YC1fP.paj_ret_at) (ct_at_F).

   WHAT IS UNREACHABLE, AND WHY.
   - THE r = 1 ARM. crt_at_J_B_r0 states r = 0, so crt_at_J_B_count's r = 1 disjunct contradicts it (crt102_tail_B's
     first case, by discriminate).
   - THE STACK PATH +0x394 .. +0x430 (taken at `beqz s7` when the frame call returned 0). s7 = F (crt_bregs_B_s7) and
     the run's fact on s7's atom is 4096 <= s7 (frames_bounds_x), so the engine decides the branch statically and its
     run never enters it: no run of it exists to walk.

   PJ_FREE'S TEXT. PJFREE is the kit's tpj_free_specX at n = DOC_D, at every float state. Its entry is position-free:
   ct_J_call takes copy's order list F (pj_foR at &copy) and the class-24 bound at the join as premises, and its post
   carries ct_qt0 (QT's facts without the r = 0 position) and the text's POSITION TRANSFER (every position at Sc whose
   next events are prhPj_free_evs F advances exactly by them). crt102_tail_B supplies both premises - F := the ordered
   free list Fc of crt_at_J_B_count's r = 0 arm, the bound from Crt102KitB.cb_J_B_ccnt24 - and turns the transfer of
   crt_pos's position (its run premise is crt_pos's `prh_run_at .. crt_evs_J`, which is prhPj_free_evs Fc since
   `map (snd + cf_head) Fc = fo crt_tree_J`) into QT's end position by ct_r0_end. An empty order list makes no event,
   and the model's HBulk [] is stepped over by prhPj_bulk_nil_pos. The ledger post keeps g_most / g_own_ran_out
   (prh_ledger .. most own): that is how QT's two cells cross the join.

   NUMERALS. LENGTH: 4444 (CRT_PC_B = 4 * 1111, DERIVED; ct_pc), 28 / 35 (copy's shadow bytes s2 + 0x1c .. + 0x22),
   504 / 512 (the flag word at F + fs_frame_bytes 3 - 8; the class-3 frame), 64 (its shadow bytes =
   __asan_set_shadow_f5's a1), 56 (struct pj), 104 / 224 / 240 (the saves below the entry sp, the frame 0xe0, the
   frame plus the realignment), 2 ^ 40 (a slot index bound), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (the shadow
   span, the stack band, the word). WORD: 245 (0xf5, the poison value of the set-shadow call), 2 ^ 64 - 8 (s9 = -8,
   the f8 byte). DERIVED: atom indices (the engine's numbering); 0xffffff00000 / 0xffffff00000 - 64 and
   0x10007fef8000 (the ceiling bound 0x7fffff800000 of asan_consts / 8, and the shadow of the frame's last byte under
   it), used only as bounds. No ADDRESS literal: every code address is pa_val / pa_sigma of PI_prog_B.

   SECTION HYPOTHESES (each with its owner, at its definition below): LAWS (engine AR_laws_x fold; at ARcf
   AR_laws_x_cf), ENV (B's image binding, PALib's pal_env), OWNLOW (engine; at ARcf owned_low_cf), ASFX / FFLX / SFX
   (aj_flag_store_x's three: YG0dcf astack_free_law_cf, AR_flag_law_ok_cf / AR_client_img_law_ok_cf, YGcallScf
   stack_free_x_any), FFLP (AR_flag_law_ok_cf's first conjunct), SETSH (the frame-class row that discharges FCiface
   contracts), PJFREE (the pj_free contract text), and the text's own premises HPRE / HCL / HTREE (the entry of
   tcheck_round_trip_specX). HRQA is stated and unused: the tail's one program call, pj_free, requests nothing. No
   image premise is left: the development is at the B' instance PI_prog_B, and its image facts are CrtImgB102.v's. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base CfParamsPreset PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck PRH_PjOrder PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env Crt102Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
(* the B' instance and its image facts (CrtImgB102: no premise left), the B' cut offsets (Crt102Img) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB CrtImgB102.
(* the class-24 bound at the B' join, cited: Crt102KitB.cb_J_B_ccnt24 *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102KitB.
(* kb round: the A' kit's AJW runners (crt_run_xw, crt_run_xw_inv) and the journal's wild clause (crt_jw_wild), used
   qualified with every implicit argument given at the B' instance *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Kit.
(* the re-hiding move, used qualified: YA0nH (wle', SRrG, SRr', SRr_SRr', the wle' laws),
   YSRrG (SRrG_msteps, SRr'_bind / _mono / _ret), YGcfRehidePost.RZ_cf (preset's zone); pj_free's hull premise from
   the run position: PresetHullBudget and the image-free Crt102HullPos (hull_budget_nil_of_room_pos) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102HullPos.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* the entry offset of check_round_trip in the listing, Crt102Img.v's CRT_PC_B = 4 * CRT_SLOT_B, as a number *)
Lemma ct_pc : CRT_PC_B = 4444.
Proof. reflexivity. Qed.

(* ======================================================================================================== *)
(* image-free (Crt102Tail.v's Section ct and its two list lemmas, copied): the tree over a larger block list, a word
   from its eight bytes, pairwise lists *)
Section ct. Variable segs : list Segment.

Lemma ct_cstr_lblk : forall m (lblk lblk' : Z -> Z -> Prop) a k s, pj_cstrR segs m lblk a k s ->
  (lblk a k -> lblk' a k) -> pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (Hl & Hr) H. exact (conj (H Hl) Hr). Qed.

Lemma ct_mems_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  pj_memsR segs m lblk P a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> incl D1 D -> P (a + 56 * Z.of_nat i) u D1 ->
     P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D H HL HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|].
split; [apply (ct_cstr_lblk m lblk lblk' x k nm Hc); apply HL; left; reflexivity|].
split.
- pose proof (HP 0%nat nm u D1 eq_refl (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_introl Hy)))) as HP0.
  replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. exact (HP0 H1).
- apply (IH (a + 56) (ka + 8) D2 H2).
  + intros y kk Hy. apply HL. right. apply in_or_app. right. exact Hy.
  + intros i nm' u' D1' Hi Hinc HPi.
    specialize (HP (S i) nm' u' D1' Hi (fun y Hy => in_cons _ _ _ (in_or_app _ _ _ (or_intror (Hinc y Hy))))).
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia. exact (HP HPi).
Qed.

(* the tree over a block predicate that holds wherever the old one did, on the tree's own blocks *)
Lemma ct_nodeR_lblk : forall t m (lblk lblk' : Z -> Z -> Prop) p D, pj_nodeR segs m lblk p t D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D H HL; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (ct_cstr_lblk m lblk lblk' str k txt Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (ct_cstr_lblk m lblk lblk' str k s Hc). apply HL. subst D. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hp & Hk)]; [left; exact Hz | right; split; [exact Hp|]].
    apply HL; [|exact Hk]. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di Hi).
  intros i u D1 Hil Hinc HP. rewrite Forall_forall in IH.
  apply (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 HP).
  intros x k Hx. apply HL. apply HDi. apply Hinc. exact Hx.
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
  split.
  { destruct Hcap as [Hz | (Hp & Hk & Hy)]; [left; exact Hz | right; split; [exact Hp|]].
    subst D. rewrite (proj2 (Z.eqb_neq cap 0)) in HL by lia.
    split; [apply HL; [left; reflexivity | exact Hk] | apply HL; [right; left; reflexivity | exact Hy]]. }
  exists Di. split; [exact ED|].
  apply (ct_mems_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di Hi).
  + intros x k Hx. apply HL. apply HDi. exact Hx.
  + intros i nm u D1 Hil Hinc HP. rewrite Forall_forall in IH.
    specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
    apply (IH m lblk lblk' _ D1 HP). intros x k Hx. apply HL. apply HDi. apply Hinc. exact Hx.
Qed.

(* a word from its eight bytes (YCem.v:101 rdword_of_val_mem, restated: YCem's Require closure is cgif's image layer) *)
Lemma ct_rdword_of_vm : forall H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
End ct.

(* pairwise R over a permutation, for a symmetric R (S10TxKit.v s10_pairwise_perm, restated) *)
Lemma ct_pairwise_perm : forall (A : Type) (R : A -> A -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros A R Hs l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [pairwise]; intros H.
- exact H.
- destruct H as [Hx Hl]. split; [|exact (IH Hl)].
  rewrite Forall_forall in Hx |- *. intros z Hz. apply Hx. exact (Permutation_in _ (Permutation_sym P) Hz).
- destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]; subst.
  split; [constructor; [apply Hs; exact Hyx | exact Hx] | split; [exact Hyl | exact Hl]].
- exact (IH2 (IH1 H)).
Qed.
(* an element in both halves of a pairwise list is related to itself *)
Lemma ct_pairwise_app_dup : forall (A : Type) (R : A -> A -> Prop) l1 l2 x,
  pairwise R (l1 ++ l2) -> In x l1 -> In x l2 -> R x x.
Proof.
intros A R l1. induction l1 as [|z l1 IH]; intros l2 x H H1 H2; [destruct H1|].
cbn [pairwise app] in H. destruct H as [Hz Hl]. destruct H1 as [<- | H1].
- rewrite Forall_forall in Hz. apply Hz. apply in_or_app. right. exact H2.
- exact (IH l2 x Hl H1 H2).
Qed.

(* ======================================================================================================== *)
(* THE THREE SYMBOLIC STATES of the tail (S10Env.v's environment TE: atoms 0-31 the entry registers, 32-63 the current
   ones, 64- the segment's extras; xr r = 32 + r). B' registers: s2 = x18, s3 = x19, s4 = x20, s5 = x21, s7 = x23,
   s9 = x25, s11 = x27. *)
(* J: `mv a0, s4; jal pj_free` - no region *)
Definition ss_J : sstate := mkSS (CRT_PC_B + CRT_J_OFF_B) cur_atoms [] None (mkFacts [] [] []).
(* Z: copy's seven shadow bytes through s2 (written f8 = s9), the frame's first word through s3 (the retired magic);
   s7's atom is the frame, and its fact 4096 <= s7 is what the engine reads at `beqz s7`: THE STACK PATH IS NEVER
   ENTERED *)
Definition ss_Z : sstate := mkSS (CRT_PC_B + CRT_Z_OFF_B) cur_atoms
  [ YP09.mkRegion (Some (xr 18)) 28 35 28 35 [];
    YP09.mkRegion (Some (xr 19)) 0 8 0 8 [] ] None
  (mkFacts [(xr 18, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (xr 19, mkAF 4096 (2 ^ 47) 5);
            (xr 23, mkAF 4096 (2 ^ 47) 5)] [] []).
(* F: gp, tp pinned to the entry's and s0 to the entry sp (atom 2); the frame's flag word (F + 504 through s7,
   read-only, its value the flag's address, atom 64), the flag byte (writable), the thirteen saves below the entry sp
   (read-only, the entry registers in CRT_SAVED's order) *)
Definition sr_F : list sv := sr_set (sr_set (sr_set cur_atoms 3%bv (SOff 3 0)) 4%bv (SOff 4 0)) 8%bv (SOff 2 0).
Definition F_saves : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
   YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-104) (CVal 8 (SOff 27 0))].
Definition ss_F : sstate := mkSS (CRT_PC_B + CRT_Z5_OFF_B) sr_F
  [ YP09.mkRegion (Some (xr 23)) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 64 0))];
    YP09.mkRegion (Some 64%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 2%nat) (-104) 0 0 0 F_saves ] None
  (mkFacts [(xr 23, mkAF 4096 (2 ^ 47) 5); (64%nat, mkAF 0 (2 ^ 47) 0); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

(* a register a run did not write (S10TxString.v's tskeep, as Crt102Tail.v's ct_keep) *)
Ltac ct_keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* crt_bregs_B's eleven fields, read by their projections, under the names R<register> *)
Ltac ct_bregs HBR :=
  pose proof (crt_bregs_B_sp HBR) as R2; pose proof (crt_bregs_B_gp HBR) as R3;
  pose proof (crt_bregs_B_tp HBR) as R4; pose proof (crt_bregs_B_s0 HBR) as R8;
  pose proof (crt_bregs_B_s1 HBR) as R9; pose proof (crt_bregs_B_s2 HBR) as R18;
  pose proof (crt_bregs_B_s4 HBR) as R20; pose proof (crt_bregs_B_s3 HBR) as R19;
  pose proof (crt_bregs_B_s7 HBR) as R23; pose proof (crt_bregs_B_s9 HBR) as R25;
  pose proof (crt_bregs_B_s11 HBR) as R27.

(* ======================================================================================================== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* generic in the image's CfImg: the composer supplies the B' record (the generated lib/B/CfImgB.v) *)
Context {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
(* THE B' INSTANCE (lib/B/PAImg_prog.v): its PAImg and its listing's table instance *)
#[local] Existing Instances PAImg_prog.PI_prog_B PAImg_prog.PL_prog_B.
#[local] Notation PA := (PAImg_prog.PI_prog_B).
#[local] Notation PL := (PAImg_prog.PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation STKPF := (@STK_pj_free prh_img_B DOC_D).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).

Lemma ct_fb3 : fs_frame_bytes CRT_CID = 512.
Proof. vm_compute. reflexivity. Qed.
Lemma ct_stk : STKPF + 240 <= STKC /\ ESTACK + 240 <= STKC /\ 0 <= STKPF.
Proof. vm_compute. repeat split; discriminate. Qed.
(* a slot of the listing is an image byte, so below kLowMemEnd (YC1fP.v pa_slot_img's proof, ending at pa_segs_low
   instead of pa_img_range) *)
Lemma ct_slot_low : forall k e, 0 <= k < 2 ^ 40 -> plookup (ptree_of_list B_prog_listing) k = Some e ->
  0 <= BASE + k < kLowMemEnd.
Proof.
intros k e Hk40 Hk. pose proof (@pa_B_ok _ _ PA) as HB.
pose proof (cert_slot asym (clookup (@pa_tbl _ _ PA)) VAL SIGMA B_prog_listing (@pa_cert _ _ PA) k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup (@pa_tbl _ _ PA) (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (@pa_tbl_ok _ _ PA _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (@pa_segs_low _ _ PA _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia. lia.
Qed.
(* the three return sites of the tail's calls and its `ret` are slots *)
Lemma ct_slots : (exists e, plookup (ptree_of_list B_prog_listing) (CRT_PC_B + CRT_Z_OFF_B) = Some e) /\
  (exists e, plookup (ptree_of_list B_prog_listing) (CRT_PC_B + CRT_Z5_OFF_B) = Some e).
Proof. split; eexists; vm_compute; reflexivity. Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the re-hiding move (the wle' contract, the internal file WLE-CONTRACT.md): the journals sit at the world relation
   RZW := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf (ajournal_xR / ajournal_xwR), the relation of QF's journal *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (kb round: crt_at_J_B's live state is at kb = prh_wk F_check_round_trip) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
(* ---- SECTION HYPOTHESES, each with its owner ---- *)
(* the allocator laws (owner: the engine fold, YCbqG c3b5d0111037; at ARcf: AR_laws_x_cf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the runtime's environment (owner: the image binding of B, PALib's pal_env), for the set-shadow rule *)
Hypothesis ENV : api_env SEGS B.
(* runtime-owned bytes lie below the ceiling (owner: the engine, YGcallx.v ARx_owned_low_law; at ARcf: owned_low_cf) *)
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
(* the inline release: exactly the three hypotheses of YGcallSx.v's aj_flag_store_x (owner: the engine's
   discharges at ARcf - ASFX = YG0dcf.v astack_free_law_cf, FFLX = AR_flag_law_ok_cf / AR_client_img_law_ok_cf,
   SFX = YGcallScf.v stack_free_x_any) *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
(* the frame's flag byte is present (at ARcf: AR_flag_law_ok_cf's first conjunct, as H5CrtS7.v
   crt7_fflx and S10TxString.v's FFLP take it) *)
Hypothesis FFLP : forall ly S Hp (W : world SEGS) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos).
(* __asan_set_shadow_f5 at the poison value 0xf5, YGcallMxmn.v's aset_shadow_realizes_xm (owner: the frame-class row
   that discharges FCiface contracts at the instance; YGcallMxmn.v's header gives the payment route), at every float
   state (its walk is generic in fx) *)
Hypothesis SETSH : forall fxk : YK11.FPState,
  aset_shadow_realizes_xm (fx := fxk) SEGS B ARx (SIGMA AS___asan_set_shadow_f5) 245.
(* the callee's contract text: tpj_free_specX (lib/A/PRH_FnPj.v dc0d0aa79c0f:636-689) by name, at n = DOC_D, at
   every float state (its walk is generic in fx), at the caller's universe closure (part of the contract) *)
Variable CTX0 : list (list Z).
Hypothesis PJFREE : forall fxk : YK11.FPState,
  tpj_free_specX (fx := fxk) B ARx SK CTX0 DOC_D.

Section g.
(* ---- the entry: tcheck_round_trip_specX's binders and the premises the tail reads ---- *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (doc : Z) (t : PjTree.jv) (D : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
#[local] Notation sp0 := (spZ regs).
(* tcheck_round_trip_specX's entry premises (the contract: lib/A/PRH_FnCheck.v 0844ed8c0608:1240, :1246, :1248) *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HCL : prh_univ_closure B CTX0.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
(* the text's request bound (the contract: PRH_FnCheck.v 0844ed8c0608:1268), carried, not consumed: the tail's one
   program call, pj_free, requests nothing, so no lemma takes it *)
Hypothesis HRQA : RQA_crt t <= most.
(* THE RUN HAS AT MOST 4 CALLS (the text's premise, PRH_FnCheck.v tcheck_round_trip_specX): pj_free's hull premise is
   paid from crt_pos's run position by Crt102HullPos.hull_budget_nil_of_room_pos, which takes this bound *)
Hypothesis HOS4 : (length rp_os <= 4)%nat.

(* the Section's fx is named: a local FPState binder (fxk) is also an instance candidate *)
#[local] Notation QFB := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x)
  (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
  (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
  (most := most)).
#[local] Notation JB := (crt_at_J_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK)
  (L := B_prog_listing) (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x)
  (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs)
  (mem := mem) (md := md) (doc := doc) (t := t) (D := D) (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran)
  (most := most)).
#[local] Notation CFG := (crt_cfg (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).
#[local] Notation sp1 := (CRT_sp1 (regs := regs)).
#[local] Notation bregsB := (crt_bregs_B (regs := regs)).
#[local] Notation saved := (crt_saved (L := B_prog_listing) (PA := PA) (regs := regs)).

(* ---- the tail's own register and range facts (Crt102Tail.v's, at the B' registers) ---- *)
Lemma ct_sp1_range : sp0 mod 16 = 0 -> 240 <= sp0 -> sp0 - 240 <= sp1 <= sp0 - 224 /\ sp1 mod 32 = 0.
Proof.
intros Hal H. unfold CRT_sp1, CRT_FRAME, CRT_ALIGN. pose proof (Z.mul_div_le (sp0 - 224) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)).
assert (Hm : (sp0 - 224) mod 32 = 0 \/ (sp0 - 224) mod 32 = 16).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.div_mod (sp0 - 224) 16 ltac:(lia)).
  assert ((sp0 - 224) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  pose proof (Z.mod_pos_bound (sp0 - 224) 16 ltac:(lia)). lia. }
split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.
Lemma ct_bregs_pres : forall rg rg' F, bregsB rg F -> aregs_preserved rg rg' -> bregsB rg' F.
Proof.
intros rg rg' F HBR HP.
refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
  crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
  crt_bregs_B_s11 := _ |}.
- rewrite (ts_ap rg rg' 2%bv HP) by ts_cs. exact (crt_bregs_B_sp HBR).
- rewrite (ts_ap rg rg' 3%bv HP) by ts_cs. exact (crt_bregs_B_gp HBR).
- rewrite (ts_ap rg rg' 4%bv HP) by ts_cs. exact (crt_bregs_B_tp HBR).
- rewrite (ts_ap rg rg' 8%bv HP) by ts_cs. exact (crt_bregs_B_s0 HBR).
- rewrite (ts_ap rg rg' 9%bv HP) by ts_cs. exact (crt_bregs_B_s1 HBR).
- rewrite (ts_ap rg rg' 18%bv HP) by ts_cs. exact (crt_bregs_B_s2 HBR).
- rewrite (ts_ap rg rg' 20%bv HP) by ts_cs. exact (crt_bregs_B_s4 HBR).
- rewrite (ts_ap rg rg' 19%bv HP) by ts_cs. exact (crt_bregs_B_s3 HBR).
- rewrite (ts_ap rg rg' 23%bv HP) by ts_cs. exact (crt_bregs_B_s7 HBR).
- rewrite (ts_ap rg rg' 25%bv HP) by ts_cs. exact (crt_bregs_B_s9 HBR).
- rewrite (ts_ap rg rg' 27%bv HP) by ts_cs. exact (crt_bregs_B_s11 HBR).
Qed.
(* the registers a run left alone keep crt_bregs_B *)
Lemma ct_bregs_keep : forall rg rg' F, bregsB rg F ->
  (forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rg' rr = getr rg rr) ->
  bregsB rg' F.
Proof.
intros rg rg' F HBR KR.
refine {| crt_bregs_B_sp := _; crt_bregs_B_gp := _; crt_bregs_B_tp := _; crt_bregs_B_s0 := _; crt_bregs_B_s1 := _;
  crt_bregs_B_s2 := _; crt_bregs_B_s4 := _; crt_bregs_B_s3 := _; crt_bregs_B_s7 := _; crt_bregs_B_s9 := _;
  crt_bregs_B_s11 := _ |}; rewrite KR by (cbn [In]; repeat (first [left; reflexivity | right])).
- exact (crt_bregs_B_sp HBR).
- exact (crt_bregs_B_gp HBR).
- exact (crt_bregs_B_tp HBR).
- exact (crt_bregs_B_s0 HBR).
- exact (crt_bregs_B_s1 HBR).
- exact (crt_bregs_B_s2 HBR).
- exact (crt_bregs_B_s4 HBR).
- exact (crt_bregs_B_s3 HBR).
- exact (crt_bregs_B_s7 HBR).
- exact (crt_bregs_B_s9 HBR).
- exact (crt_bregs_B_s11 HBR).
Qed.

(* ---- QT at a state, the register aside: the facts the tail carries from pj_free's return to the `ret`. ct_qt is QT's
   facts with its room position on the r = 0 arm only, at the exact end position ct_pos_end (Crt102Glue.v's QT: the
   ledger carries most / own as its last two arguments). ct_qt0 is everything else (Crt102Tail.v's ct_qt0): what
   ct_J_call's post gives, before crt102_tail_B adds the position from pj_free's position transfer (ct_qt_of0). ---- *)
Definition ct_pos_end (S' : astate) : Prop :=
  exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
    (rp_i + length (PresetReqAt.round_trip rp_sm t))%nat rp_H0 hist' S'.
Definition ct_qt (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS) (mem' : word -> option byte) (r : Z)
  : Prop :=
  room_live_cf S' /\
  exists Lam' peak' cset cnt' ran' own',
  Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ peak <= peak' /\
  0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0) /\
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
  pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') doc t D /\ (forall bk, In bk D -> In bk Lam') /\
  (* QT's `r = 0` (Crt102Glue.v 918720d3a7b6): THE r = 1 ARM IS DEAD, killed by tround_trip_text_specX's entry
     premise prh_cons_from (kit tip 6557b95928b5, PRH_FnCheck 0b6f7b597757); crt_at_J_B states it too *)
  r = 0 /\
  ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ cnt <= cnt' <= cnt + ck_crt_count t cset) \/
   (r = 0 /\ own' = 0 /\ cnt' = cnt + ck_crt_count t cset /\ ran' = ran /\ ct_pos_end S')).
Definition ct_qt0 (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS) (mem' : word -> option byte) (r : Z)
  : Prop :=
  room_live_cf S' /\
  exists Lam' peak' cset cnt' ran' own',
  Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\ peak <= peak' /\
  0 <= cset <= 3 /\ (forall ms, t = PjTree.JObj ms -> In ck_MOD_AT (map fst ms) -> cset = 0) /\
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
  pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam') doc t D /\ (forall bk, In bk D -> In bk Lam') /\
  r = 0 /\
  ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ cnt <= cnt' <= cnt + ck_crt_count t cset) \/
   (r = 0 /\ own' = 0 /\ cnt' = cnt + ck_crt_count t cset /\ ran' = ran)).
Lemma ct_qt_of0 : forall ly' S' Hp' W' mem' r,
  ct_qt0 ly' S' Hp' W' mem' r -> (r = 0 -> ct_pos_end S') -> ct_qt ly' S' Hp' W' mem' r.
Proof.
intros ly' S' Hp' W' mem' r
  (HRL & Lam' & peak' & cset & cnt' & ran' & own' & HPL & HPA & HPK & Hcs & Hcs0 & HLED & HDOC & HDL & Er0 & HR) HPE.
split; [exact HRL|]. exists Lam', peak', cset, cnt', ran', own'.
refine (conj HPL (conj HPA (conj HPK (conj Hcs (conj Hcs0 (conj HLED (conj HDOC (conj HDL (conj Er0 _))))))))).
destruct HR as [HR1 | (E0 & E1 & E2 & E3)]; [left; exact HR1|].
right. exact (conj E0 (conj E1 (conj E2 (conj E3 (HPE E0))))).
Qed.

(* the document's header sits in one of the entry's fake frames (ck_tree_ok's ck_obj_home), at every later state
   (Crt102Tail.v's ct_doc_frame / ct_doc_bytes, copied) *)
Lemma ct_doc_frame : forall ly2 S2 n,
  layout_le n ly ly2 -> (forall f, In f (frames S) -> In f (frames S2)) ->
  exists cid pos, In (cid, pos) (frames S) /\ In (cid, pos) (frames S2) /\
    frame_addr ly2 cid pos <= doc /\ doc + 56 <= frame_addr ly2 cid pos + fs_frame_bytes cid.
Proof.
intros ly2 S2 n Hle Hfr.
pose proof HTREE as (_ & _ & _ & _ & (cid & pos & Hin & H1 & H2) & _).
exists cid, pos.
assert (E : frame_addr ly2 cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite E. split; [exact Hin|]. split; [exact (Hfr _ Hin)|]. split; assumption.
Qed.
Lemma ct_doc_bytes : forall ly2 S2 Hp2 (W2 : world SEGS) m md2 n,
  ARx ly2 S2 Hp2 W2 m md2 -> layout_le n ly ly2 -> (forall f, In f (frames S) -> In f (frames S2)) ->
  4096 <= doc /\ doc + 56 <= YM05.alloc_ceiling /\
  (forall a, doc <= a < doc + 56 -> apresent (w_H W2) m a /\ ~ aowned B ly2 S2 a /\ ~ in_img SEGS a /\
     in_app a 1).
Proof.
intros ly2 S2 Hp2 W2 m md2 n HAR Hle Hfr.
destruct (ct_doc_frame ly2 S2 n Hle Hfr) as (cid & pos & _ & Hin & H1 & H2).
destruct (frames_bounds_x _ _ _ LAWS ly2 S2 Hp2 W2 m md2 cid pos HAR Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS ly2 S2 Hp2 W2 m md2 cid pos HAR Hin) as (_ & _ & Ffr & _).
split; [lia|]. split; [lia|].
intros a Ha. destruct (Ffr a ltac:(lia)) as [Hpr Ho]. split; [exact Hpr|]. split; [exact Ho|].
split; [exact (frm_img_x _ _ _ LAWS ly2 S2 Hp2 W2 m md2 cid pos a HAR Hin ltac:(lia))|].
unfold in_app in *. destruct Fb3 as (F0 & [FL | [FH1 FH2]]); split; lia.
Qed.
(* the document's header is apart from the class-3 frame the body runs on (the frames of a state are pairwise apart,
   and the class-3 frame heads the list over the entry's) *)
Lemma ct_doc_apart : forall lyc Sc Hpc (Wc : world SEGS) memc mdc pos n,
  ARx lyc Sc Hpc Wc memc mdc -> layout_le n ly lyc -> frames Sc = (CRT_CID, pos) :: frames S ->
  forall a, doc <= a < doc + 56 ->
  ~ (frame_addr lyc CRT_CID pos <= a < frame_addr lyc CRT_CID pos + fs_frame_bytes CRT_CID).
Proof.
intros lyc Sc Hpc Wc memc mdc pos n HAR Hle Hfr a Ha Hx.
destruct (ct_doc_frame lyc Sc n Hle ltac:(intros f Hf; rewrite Hfr; right; exact Hf)) as (cid & pos' & HinS & _ & H1 & H2).
apply in_split in HinS as (l2 & l3 & El).
pose proof (sep_frames_pos_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc (CRT_CID, pos) (cid, pos') [] l2 l3 HAR
  ltac:(rewrite Hfr, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* QT's facts survive a change of memory that misses alloc.c's statics, the document's header and every live block
   (the runtime call and the inline release below), at a state with the same blocks and the same room
   (Crt102Tail.v's ct_qt_keep, copied; its image fact pst_in_img_A is CrtImgB102.v's crt_pst_img_B_cf here) *)
Lemma ct_qt_keep : forall ly2 S2 S2' Hp2 W2 m m' md' r (C : Z -> Prop),
  ct_qt ly2 S2 Hp2 W2 m r ->
  ARx ly2 S2' Hp2 W2 m' md' ->
  ablocks B ly2 S2' = ablocks B ly2 S2 ->
  (room_live_cf S2 -> room_live_cf S2') ->
  (forall i h, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 h S2 ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os i rp_H0 h S2') ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ C a -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) ->
  (forall a, C a -> ~ Exists (in_zr a) PST /\ ~ (doc <= a < doc + 56) /\
     forall p n, In (p, n) (ablocks B ly2 S2) -> ~ (p <= a < p + req_size n)) ->
  (forall a, doc <= a < doc + 56 -> apresent (w_H W2) m' a) ->
  0 <= doc -> doc + 56 <= 2 ^ 64 ->
  ct_qt ly2 S2' Hp2 W2 m' r.
Proof.
intros ly2 S2 S2' Hp2 W2 m m' md' r C
  (HRL & Lam' & peak' & cset & cnt' & ran' & own' & HPL & HPA & HPK & Hcs & Hcs0 & HLED &
   HDOC & HDL & Er0 & HR) HAR' EAB HRLk HRPk HK HC HDP Hd0 Hd1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPSTK : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a).
{ intros a Ha. pose proof (@pa_segs_low _ _ PA a (crt_pst_img_B_cf a Ha)) as Hlow.
  apply HK; [unfold kLowMemEnd in Hlow; lia | intros Hc; exact (proj1 (HC a Hc) Ha)]. }
assert (HBLK : forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) m' (p + i) = aview SEGS (w_H W2) m (p + i)).
{ intros p n i Hin Hi.
  destruct (alx_blocks _ _ _ LAWS ly2 S2' Hp2 W2 m' md' p n HAR' ltac:(rewrite EAB; exact Hin)) as (_ & H4096 & Hc & _).
  apply HK; [lia|]. intros Hcc. exact (proj2 (proj2 (HC _ Hcc)) p n Hin ltac:(lia)). }
assert (HBP : forall p n i, In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> apresent (w_H W2) m' (p + i)).
{ intros p n i Hin Hi.
  destruct (alx_blocks _ _ _ LAWS ly2 S2' Hp2 W2 m' md' p n HAR' ltac:(rewrite EAB; exact Hin)) as (_ & _ & _ & _ & Hb & _).
  exact (proj1 (Hb (p + i) ltac:(lia))). }
assert (HLB : forall a k, In (a, k) Lam' -> 0 <= k /\ In (a - 16, k + 16) (ablocks B ly2 S2)).
{ intros a k Hin. pose proof (prh_ledger_blocks B ly2 S2 Hp2 W2 m Lam' peak' cnt' SIZE_MAXZ ran' most own' HLED) as HF.
  rewrite Forall_forall in HF. destruct (HF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  change (@cf_head CfParams_preset) with 16 in Hab. exact (conj Hk0 Hab). }
assert (HVM : forall a w v, val_mem SEGS (mrestrict (w_H W2) m) a w v ->
  (forall j, (j < w)%nat -> Exists (in_zr (a + Z.of_nat j)) PST) -> val_mem SEGS (mrestrict (w_H W2) m') a w v).
{ intros a w v Hv Hpw. apply (ts_vm_av (w_H W2) (w_H W2) m m' a w v); [|exact Hv].
  intros j Hj. apply HPSTK. apply Hpw. exact Hj. }
split; [exact (HRLk HRL)|].
exists Lam', peak', cset, cnt', ran', own'.
split; [exact HPL|]. split; [rewrite EAB; exact HPA|]. split; [exact HPK|]. split; [exact Hcs|]. split; [exact Hcs0|].
split.
{ apply (S1Ledger.prh_ledger_kept_aview B ly2 S2 Hp2 W2 m ly2 S2' Hp2 W2 m' Lam' peak' cnt' SIZE_MAXZ ran' most own'
    HLED HPSTK).
  - intros a k i Hin Hi. destruct (HLB a k Hin) as (Hk0 & Hab).
    change (@cf_head CfParams_preset) with 16. apply (HBLK (a - 16) (k + 16) i Hab).
    unfold req_size. destruct (Z.eqb_spec (k + 16) 0); lia.
  - intros a k _ Hab. rewrite EAB. exact Hab.
  - apply Permutation_refl. }
split.
{ apply (pj_nodeR_frame SEGS t (mrestrict (w_H W2) m) (mrestrict (w_H W2) m') (prh_lin Lam') doc D HDOC).
  intros x [Hx | ((a, k) & Hb & Hx)].
  - split.
    + apply (mbyte_of_aview SEGS). apply HK; [lia|]. intros Hc. exact (proj1 (proj2 (HC x Hc)) Hx).
    + intros _. apply (apresent_writable SEGS). exact (HDP x Hx).
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx. destruct (HLB a k (HDL _ Hb)) as (Hk0 & Hab).
    assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
    replace x with (a - 16 + (x - (a - 16))) by lia.
    split.
    + apply (mbyte_of_aview SEGS). apply (HBLK (a - 16) (k + 16)); [exact Hab | lia].
    + intros _. apply (apresent_writable SEGS). apply (HBP (a - 16) (k + 16)); [exact Hab | lia]. }
split; [exact HDL|]. split; [exact Er0|].
destruct HR as [HR1 | (E0 & E1 & E2 & E3 & (h2 & HP2))]; [left; exact HR1|].
right. split; [exact E0|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
exists h2. exact (HRPk _ _ HP2).
Qed.

(* ---- THE BOUNDARY the Z and F segments start from: the journal from the entry with the class-3 frame owned, at a
   budget WS within crt_at_J_B's 66 (kb round), QT's facts, the saved words, the frame's flag word, the memory keep,
   the float state, the registers ---- *)
Definition ct_bd (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (rg : bvmap 5 word) (r : Z) : Prop :=
  (exists WS : list (list Z), AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc memc mdc kj WS /\
     YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS) /\
  ct_qt lyc Sc Hpc Wc memc r /\
  saved Wc memc /\
  rdword (aview SEGS (w_H Wc) memc) (frame_addr lyc CRT_CID pos + fs_frame_bytes CRT_CID - 8)
    = Some (flag_addr lyc CRT_CID pos) /\
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS memc) /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  bregsB rg (frame_addr lyc CRT_CID pos) /\ getr rg 21 = w64 r.

(* ---- the symbolic states at concrete machine states (S10TxString.v's ts_G_entry, at the B' registers) ---- *)
Lemma ct_Z_entry : forall fxk (Wc : world SEGS) memc rg F,
  getr rg 18 = w64 (shadow_addr F) -> getr rg 19 = w64 F -> getr rg 23 = w64 F ->
  4096 <= F -> F + 512 <= 2 ^ 47 -> F mod 32 = 0 -> (shadow_addr F + 64 <= F \/ F + 8 <= shadow_addr F) ->
  (forall a, F <= a < F + 8 -> apresent (w_H Wc) memc a) ->
  (forall a, shadow_addr F + 28 <= a < shadow_addr F + 35 -> apresent (w_H Wc) memc a) ->
  st_ok_pi SEGS VAL (TEB regs rg []) ss_Z
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z_OFF_B))) memc (YK11.seg_rom SEGS))).
Proof.
intros fxk Wc memc rg F R18 R19 R23 G1 G2 G3 G4 PF PSH.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := TEB regs rg []).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (Hsh' := Hsh). unfold SHADOW_OFF in Hsh'.
assert (X18 : bv_unsigned (ew E (xr 18)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small. lia. }
assert (X19 : bv_unsigned (ew E (xr 19)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19. apply unsigned_lit_small. lia. }
assert (X23 : bv_unsigned (ew E (xr 23)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 23%bv 23) by reflexivity. rewrite R23. apply unsigned_lit_small. lia. }
apply (ts_st_ok (fx := fxk)).
all: try change (TEB regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 18) (shadow_addr F)); [exact X18 | lia | lia |
      intros o Ho; apply (apresent_writable SEGS); apply PSH; lia | constructor].
  + apply (ts_rok E _ (xr 19) F); [exact X19 | lia | lia |
      intros o Ho; apply (apresent_writable SEGS); apply PF; lia | constructor].
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X18, X19.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X18, X19, X23.
  change (2 ^ 5) with 32. change (2 ^ 0) with 1. unfold SHADOW_OFF in *. repeat split; lia.
Qed.

Lemma ct_F_entry : forall fxk (Wc : world SEGS) memc rg F fl,
  getr rg 23 = w64 F -> getr rg 3 = getr regs 3 -> getr rg 4 = getr regs 4 -> getr rg 8 = w64 sp0 ->
  4096 <= F -> F + 512 <= 2 ^ 47 -> F mod 32 = 0 -> 0 <= fl <= 2 ^ 47 ->
  (fl + 1 <= F + 504 \/ F + 512 <= fl) -> fl + 1 <= sp0 - 104 -> F + 512 <= sp0 - 104 ->
  2 ^ 46 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (F + 504) 8 fl ->
  saved Wc memc -> apresent (w_H Wc) memc fl ->
  st_ok_pi SEGS VAL (TEB regs rg [w64 fl]) ss_F
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z5_OFF_B))) memc (YK11.seg_rom SEGS))).
Proof.
intros fxk Wc memc rg F fl R23 R3 R4 R8 G1 G2 G3 G4 G5 G6 G7 G8 G9 VFL HSV PFL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := TEB regs rg [w64 fl]).
assert (X23 : bv_unsigned (ew E (xr 23)) = F).
{ unfold E, xr. rewrite (te_cur regs rg _ 23%bv 23) by reflexivity. rewrite R23. apply unsigned_lit_small. lia. }
assert (E64 : ew E 64 = w64 fl) by exact (te_more_lt regs rg [w64 fl] 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = fl) by (rewrite E64; apply unsigned_lit_small; lia).
assert (X2 : bv_unsigned (ew E 2) = sp0) by (unfold E; rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
assert (EN : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros r n Hn; unfold E; apply te_entry; exact Hn).
apply (ts_st_ok (fx := fxk)).
all: try change (TEB regs rg [w64 fl]) with E.
- unfold sr_F.
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 2%bv 2%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    rewrite R8; unfold w64, spZ; apply Z_to_bv_bv_unsigned].
  apply YI04.regs_ok_pin; [| intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 4%bv 4%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R4].
  apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |
    cbn [sv_denot]; rewrite (EN 3%bv 3%nat) by reflexivity; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact R3].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 23) F); [exact X23 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ _ 504 8 (SOff 64 0) fl);
      [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact VFL.
  + apply (ts_rok E _ 64 fl); [exact X64 | lia | lia | intros o Ho; apply (apresent_writable SEGS);
      replace (fl + o) with fl by lia; exact PFL | constructor].
  + apply (ts_rok E _ 2 sp0); [exact X2 | lia | lia | intros o Ho; lia |].
    unfold F_saves. repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval vm_compute in (Z.to_nat (- off / 8 - 1)) in
      let r := eval vm_compute in (nth j CRT_SAVED 0%bv) in
      apply (ts_chunk E _ _ off 8 (SOff n 0) (bv_unsigned (getr regs r)));
      [ cbn [sv_denot]; rewrite (EN r n) by reflexivity; rewrite Z.add_0_r; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs r)) as BR; change (bv_modulus 64) with (2 ^ 64) in BR; cbn; lia
      | cbn; lia
      | pose proof (HSV j ltac:(lia)) as V; change (nth j CRT_SAVED 0%bv) with r in V;
        replace (sp0 - 8 * (Z.of_nat j + 1)) with (sp0 + off) in V by (cbn; lia); exact V ]
    end.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X23, X64, X2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X23, X64, X2.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; lia.
Qed.

(* ======================================================================================================== *)
(* ---- F (+0x388): the inline release, the epilogue, `ret` ---- *)
Lemma ct_at_F : forall fxk lyc Sc Hpc Wc memc mdc kj pos rg r,
  ct_bd fxk lyc Sc Hpc Wc memc mdc kj pos rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_Z5_OFF_B rg memc mdc) QFB.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos rg r ((WS & HJ & HB) & HQ & HSV & HFL & HMN & HFZ & HFK & HBR & R21).
ct_bregs HBR.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD & Hhi & HraC).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@YM05.alloc_ceiling_lt rc) as Hc47.
pose proof ct_fb3 as HFB. pose proof ct_stk as (Hk1 & Hk2 & Hk3).
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof HJ as (HARc & HLY0 & HSEC0 & _ & _ & HFRc & _).
assert (Hin : In (CRT_CID, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (F32 & Fapp & Ffr & Fsh).
destruct (FFLX lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (Fown & Fappf & Fimg).
pose proof (OWNLOW lyc Sc Hpc Wc memc mdc _ HARc Fown) as Flow.
pose proof (FFLP lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as Fpr.
rewrite HFB in Fb2, Fb3, Fapp, Ffr, Fsh, HFL.
set (F := frame_addr lyc CRT_CID pos) in *.
set (fl := flag_addr lyc CRT_CID pos) in *.
replace (F + 512 - 8) with (F + 504) in HFL by lia.
assert (Hflf : fl + 1 <= F + 504 \/ F + 512 <= fl).
{ destruct (Z_lt_le_dec fl F) as [Hl|Hl]; [left; lia|]. destruct (Z_le_gt_dec (F + 512) fl) as [Hg|Hg]; [right; lia|].
  exfalso. exact (proj2 (Ffr fl ltac:(lia)) Fown). }
pose proof (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HFL) as VFL.
pose proof (ct_F_entry fxk Wc memc rg F fl R23 R3 R4 R8 ltac:(lia) ltac:(lia) F32 ltac:(lia) Hflf ltac:(lia)
  ltac:(lia) ltac:(lia) Hal16 VFL HSV Fpr) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg [w64 fl]) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEB regs rg [w64 fl])) by apply te_env.
assert (U64 : bv_unsigned (ew (TEB regs rg [w64 fl]) 64) = fl).
{ rewrite (te_more_lt regs rg [w64 fl] 0) by lia. cbn [nth]. apply unsigned_lit_small. lia. }
assert (Hwr : forall a, in_wrange (TEB regs rg [w64 fl]) (ss_mem ss_F) a -> a = fl).
{ intros a (rr & Hr & Ha). cbv [ss_F ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some in Ha.
  - lia.
  - rewrite U64 in Ha. lia.
  - lia. }
unfold crt_cfg.
(* the inline release (YGcallSx.aj_flag_store_xR, at RZW) is an empty-budget rule over ajournal_xR: the journal is rebased to
   the entry whose depot is the current one (YCbqGwild.ajournal_xw_rebaseR) and stepped back to WS after it
   (YCbqGwild.ajournal_xw_unbase0R, from the journal's wild clause Hinc), as Crt102Tail.v's ct_at_F *)
pose proof (Crt102Kit.crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
pose (FSTORE := YGcallSx.aj_flag_store_xR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) ASFX FFLX SFX
  asym pa_wx (clookup pa_tbl) VAL SIGMA B_prog_listing (@pl_tpi _ PL) (@pl_tw _ PL)
  pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text (@pl_lim _ PL) (@pl_len _ PL) (@pl_tpi_eq _ PL)
  (@pl_tw_eq _ PL) RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
(* the run has no inline check: its shadow span is a point far above every region (the flag's lower bound is 0),
   as S10TxString.v's ts_at_G *)
lazymatch type of HS with st_ok_pi _ _ ?E ?ss _ =>
  let K := eval vm_compute in (run_K A_LIM (SLit 0) [] ss) in
  let rr := eval vm_compute in
    (sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss) in
  lazymatch rr with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) K (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL ss = (st', rs))
    by (vm_compute; reflexivity);
  eapply (FSTORE Wc FUEL E K (SLit 0) (2 ^ 63, 2 ^ 63) [] ss st' rs _ STKC sp0 [] ly (set_depot (st_depot Sc) S) Hp W
    mem md [] lyc Sc Hpc _ _ CRT_CID pos _ ltac:(unfold A_LIM; cbn; lia) HEI ltac:(unfold CRT_CID; lia) HS SHOK
    ltac:(vm_compute; reflexivity) Hrun I HJr)
  end end.
- (* no inline check, no obligation *)
  match goal with |- Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') end. apply Forall_nil.
- (* the one write: the flag *)
  intros a HW. right. exact (Hwr a HW).
- (* the flag is 0 after the run *)
  intros ws msr Hlen HSr.
  pose proof (ts_region_nth _ _ _ 1 _ HSr eq_refl) as HR1.
  lazymatch type of HSr with st_ok_pi _ _ (extK ?E0 ?KK ?ws0) _ _ =>
    assert (X64 : bv_unsigned (ew (extK E0 KK ws0) 64) = fl)
      by (rewrite (proj1 (env_agree_extK E0 KK ws0) 64%nat) by (cbv; lia); exact U64) end.
  pose proof (ts_field _ _ 64 fl _ 0 1 0 1 0 1%N (SLit 0) HR1 X64 ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0.
  unfold fl in V0. rewrite V0. f_equal; try (rewrite U_SLit; apply bv_eq; vm_compute; reflexivity).
- (* the epilogue's `ret`: the text's normal arm *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HFr1 HFr2 Hgr.
  cbn [ms_mem mkst] in HFr1, HFr2, Hgr.
  assert (Ews : ws = []) by (destruct ws; [reflexivity | vm_compute in Hlen; discriminate]). subst ws.
  cbn [extK] in HS', SHOK', HEI'.
  assert (K' : forall a, 0 <= a < 2 ^ 64 -> ~ (a = fl) ->
    aview SEGS (w_H Wc) (ms_mem ms') a = aview SEGS (w_H Wc) memc a)
    by (intros a Ha Hn; exact (ts_keep Wc _ (ss_mem ss_F) memc (ms_mem ms') _ HFr2 Hwr a Ha Hn)).
  pose proof HJ' as (HAR' & HLY' & _ & _ & _ & HFR' & _).
  prreg HS' (1%bv : bv 5) Q1. prreg HS' (10%bv : bv 5) Q10.
  assert (X1 : getr (ms_regs ms') 1 = getr regs 1) by (rewrite Q1; apply te_entry; reflexivity).
  assert (X10 : getr (ms_regs ms') 10 = w64 r) by (rewrite Q10, <- R21; te_close).
  (* the `ret` is the plain runner's (YC1fP.paj_ret_at), lifted into SRr' *)
  apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (paj_ret_at (fx := fxk) (PL := PL) (PI := PA) Wc _ _ ms' _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
  intros mat''.
  (* the memory keep across the run *)
  assert (HMN' : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem ms')).
  { intros HM0. pose proof (HMN HM0) as HMc.
    pose (ms0 := @YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z5_OFF_B))) memc (YK11.seg_rom SEGS)).
    first [ exact (memnorm_frame_of (fx := fxk) SEGS (w_H Wc) (TEB regs rg [w64 fl]) (abs_ss VAL ss_F) ms0
              (ms_mem ms') HMc HS HFr1)
          | exact (memnorm_frame_of SEGS (w_H Wc) (TEB regs rg [w64 fl]) (abs_ss VAL ss_F) ms0 (ms_mem ms') HMc HS HFr1) ]. }
  (* QT's facts at the released state *)
  assert (HFS : forall f, In f (frames S) -> In f (frames Sc)) by (intros f Hf; rewrite HFRc; right; exact Hf).
  assert (HFS' : forall f, In f (frames S) -> In f (frames (stack_free_state CRT_CID pos Sc)))
    by (intros f Hf; rewrite HFR'; exact Hf).
  destruct (ct_doc_bytes lyc Sc Hpc Wc memc mdc _ HARc HLY0 HFS) as (Hd4 & Hdc & Hdb).
  destruct (ct_doc_bytes lyc _ Hpc Wc (ms_mem ms') _ _ HAR' HLY' HFS') as (_ & _ & Hdb').
  assert (HQ' : ct_qt lyc (stack_free_state CRT_CID pos Sc) Hpc Wc (ms_mem ms') r).
  { apply (ct_qt_keep lyc Sc _ Hpc Wc memc (ms_mem ms') _ r (fun a => a = fl) HQ HAR').
    - unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
    - intros Hk. apply RL_stack_free. exact Hk.
    - intros i h Hih. apply PresetRoomPosKeep.room_pos_stack_free. exact Hih.
    - exact K'.
    - intros a ->. split; [|split].
      + intros Hx. exact (Fimg (crt_pst_img_B_cf fl Hx)).
      + intros Hx. exact (proj1 (proj2 (Hdb fl Hx)) Fown).
      + intros p n Hpn Hx.
        destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc p n HARc Hpn) as (_ & _ & _ & _ & Hbown & _).
        exact (proj2 (Hbown fl Hx) Fown).
    - intros a Ha. exact (proj1 (Hdb' a Ha)).
    - lia.
    - lia. }
  (* QF is the text's BUDGETED post (kb round): the journal at crt_at_J_B's budget WS, wbudget [] (prh_wk
     F_check_round_trip) WS *)
  unfold QF, fpostFbm, fpostFb, YCbqGwild.apost_base_xbFR.
  exists fxk, lyc, (stack_free_state CRT_CID pos Sc), Hpc, (ms_regs ms'), (ms_mem ms'). eexists. exists kj, WS.
  split.
  { rewrite X1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [exact HFZ|]. split; [exact HFK|]. split; [exact HB|].
  split; [eapply YCbqGwild.ajournal_xw_unbase0R; [|exact Hinc];
    apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW); exact HJ'|].
  split.
  { eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (map (getr rg) all_regs ++ [w64 fl]) HS');
      [| vm_compute; reflexivity].
    split; [intros n Hn; unfold TE; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
  unfold fQmn. split; [split; [|exact HMN'] | exact HMN'].
  unfold QT.
  destruct HQ' as (HRL' & Lam' & peak' & cset & cnt' & ran' & own' & HPL' & HPA' & HPK' &
    Hcs & Hcs0 & HLED' & HDOC' & _ & Er0 & HR').
  split; [exact HRL'|].
  exists Lam', peak', cset, cnt', ran', own'.
  split; [exact HPL'|]. split; [exact HPA'|]. split; [exact HPK'|]. split; [exact Hcs|]. split; [exact Hcs0|].
  split; [exact HLED'|]. split; [exact HDOC'|].
  exists r. split; [exact X10|]. split; [exact Er0 | exact HR'].
Qed.

(* ---- Z (+0x350): the re-poison, the retired magic, the dead `beqz s7`, __asan_set_shadow_f5 ---- *)
Lemma ct_at_Z : forall fxk lyc Sc Hpc Wc memc mdc kj pos rg r,
  ct_bd fxk lyc Sc Hpc Wc memc mdc kj pos rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_Z_OFF_B rg memc mdc) QFB.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos rg r ((WS & HJ & HB) & HQ & HSV & HFL & HMN & HFZ & HFK & HBR & R21).
ct_bregs HBR.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD & Hhi & HraC).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@YM05.alloc_ceiling_lt rc) as Hc47.
pose proof ct_fb3 as HFB. pose proof ct_stk as (Hk1 & Hk2 & Hk3).
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof HJ as (HARc & HLY0 & HSEC0 & _ & _ & HFRc & _).
assert (Hin : In (CRT_CID, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (F32 & Fapp & Ffr & Fsh).
rewrite HFB in Fb2, Fb3, Fapp, Ffr, Fsh, HFL.
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (ct_sp1_range Hal16 ltac:(lia)) as (Hsp1a & Hsp1b).
assert (Hshb : SHADOW_OFF <= shadow_addr F /\ shadow_addr F + 64 <= 0x10007fef8000).
{ unfold shadow_addr, SHADOW_OFF. assert (F / 8 <= 0xffffff00000 - 64) by (apply Z.div_le_upper_bound; lia).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia. }
assert (Hsfd : shadow_addr F + 64 <= F \/ F + 512 <= shadow_addr F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp. unfold SHADOW_OFF, shadow_addr in Hshb.
  unfold shadow_addr, SHADOW_OFF.
  destruct Fapp as (_ & [HL | [HH1 HH2]]); [right | left]; lia. }
assert (PF : forall a, F <= a < F + 8 -> apresent (w_H Wc) memc a) by (intros a Ha; exact (proj1 (Ffr a ltac:(lia)))).
assert (PSH : forall a, shadow_addr F + 28 <= a < shadow_addr F + 35 -> apresent (w_H Wc) memc a).
{ intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia.
  exact (proj1 (Fsh (a - shadow_addr F) ltac:(lia))). }
pose proof (ct_Z_entry fxk Wc memc rg F R18 R19 R23 ltac:(lia) ltac:(lia) F32 ltac:(destruct Hsfd; [left | right]; lia)
  PF PSH) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
assert (U18 : bv_unsigned (ew (TEB regs rg []) (xr 18)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (U19 : bv_unsigned (ew (TEB regs rg []) (xr 19)) = F).
{ unfold xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19. apply unsigned_lit_small. lia. }
assert (Hwr : forall a, in_wrange (TEB regs rg []) (ss_mem ss_Z) a ->
  (shadow_addr F + 28 <= a < shadow_addr F + 35) \/ (F <= a < F + 8)).
{ intros a (rr & Hr & Ha). cbv [ss_Z ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some in Ha.
  - left. rewrite U18 in Ha. lia.
  - right. rewrite U19 in Ha. lia. }
set (P := fun m : word -> option byte => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
assert (HPM : P memc) by exact HMN.
pose (RUN := @Crt102Kit.crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS P
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS).
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (0, 0).
{ (* the writes: the own frame's first word and the shadow of copy *)
  intros a HW. unfold awr_byte, in_frames. right; right; right. exists CRT_CID, pos. split; [left; reflexivity|].
  unfold in_zr. cbn [fst snd]. change (frame_addr lyc CRT_CID pos) with F. rewrite HFB.
  destruct (Hwr a HW) as [Ha | Ha]; [right | left]; lia. }
pmkst HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [ct_keep HS |]). destruct Hr. }
assert (X10 : getr (ms_regs ms) 10 = w64 (shadow_addr F)) by (rewrite Q10, <- R18; te_close).
assert (X11 : getr (ms_regs ms) 11 = w64 64) by (rewrite Q11; reflexivity).
assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z5_OFF_B))) by (rewrite Q1; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite (KR 2%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R2.
  unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hgp' : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite (KR 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R3; exact Hgp).
assert (Htp' : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite (KR 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R4; exact Htp).
assert (HZlow : 0 <= BASE + (CRT_PC_B + CRT_Z5_OFF_B) < kLowMemEnd).
{ destruct ct_slots as [_ (e & He)].
  exact (ct_slot_low (CRT_PC_B + CRT_Z5_OFF_B) e ltac:(pose proof ct_pc; unfold CRT_Z5_OFF_B; lia) He). }
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z5_OFF_B)))).
{ apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PA)); [pose proof ct_pc; unfold CRT_Z5_OFF_B; lia | reflexivity]. }
(* __asan_set_shadow_f5's rule (YGcallMxmn.aj_set_shadow_at_xmR, at RZW; plain SRr, lifted by YA0nH.SRr_SRr') is over
   ajournal_xR: the journal rebased to the current depot and stepped back to WS after it (as ct_at_F's release) *)
pose proof (Crt102Kit.crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hinc.
pose proof HJ as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply YSRrG.SRr'_bind.
{ apply (YA0nH.SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  exact (YGcallMxmn.aj_set_shadow_at_xmR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) ENV
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (SIGMA AS___asan_set_shadow_f5) 245 (SETSH fxk) Wc (ms_regs ms) (ms_mem ms) STKC sp0 [] ly
    (set_depot (st_depot Sc) S) Hp W mem md
    [(CRT_CID, pos)] lyc Sc Hpc _ kj CRT_CID pos (shadow_addr F) 64 (sp1 - sp0)
    (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z5_OFF_B)))
    HJr (or_introl eq_refl) X10 X11 ltac:(lia) ltac:(unfold F; lia)
    ltac:(unfold F; rewrite HFB; lia) Hsp ltac:(lia) ltac:(lia)
    ltac:(lia) Hgp' Htp' X1 Hraw). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Heff & Hfr2 & HMN2).
eapply YCbqGwild.ajournal_xw_unbase0R in HJ2; [|exact Hinc].
pose proof HJ2 as (HAR2 & _).
(* the bytes the stretch and the call wrote: the frame's first word and its shadow *)
assert (HKz : forall a, 0 <= a < 2 ^ 64 -> ~ ((F <= a < F + 8) \/ (shadow_addr F <= a < shadow_addr F + 64)) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. rewrite (Hfr2 a Ha ltac:(intros Hx; apply Hn; right; exact Hx)).
  apply (ts_keep Wc _ (ss_mem ss_Z) memc (ms_mem ms) _ HFr Hwr a Ha).
  intros [Hx | Hx]; apply Hn; [right | left]; lia. }
assert (HFS : forall f, In f (frames S) -> In f (frames Sc)) by (intros f Hf; rewrite HFRc; right; exact Hf).
destruct (ct_doc_bytes lyc Sc Hpc Wc memc mdc _ HARc HLY0 HFS) as (Hd4 & Hdc & Hdb).
destruct (ct_doc_bytes lyc Sc Hpc Wc mem2 md2 _ HAR2 HLY0 HFS) as (_ & _ & Hdb2).
pose proof (ct_doc_apart lyc Sc Hpc Wc memc mdc pos _ HARc HLY0 HFRc) as Hdap. rewrite HFB in Hdap.
apply (ct_at_F fxk lyc Sc Hpc Wc mem2 md2 kj pos regs2 r).
split; [exists WS; split; [exact HJ2 | exact HB]|].
split.
{ apply (ct_qt_keep lyc Sc Sc Hpc Wc memc mem2 md2 r
    (fun a => (F <= a < F + 8) \/ (shadow_addr F <= a < shadow_addr F + 64)) HQ HAR2 eq_refl (fun H => H)
    (fun i h H => H) HKz).
  - intros a Ha. split; [|split].
    + intros Hx. pose proof (crt_pst_img_B_cf a Hx) as Himg. pose proof (@pa_segs_low _ _ PA a Himg) as Hlow.
      destruct Ha as [Ha | Ha].
      * exact (frm_img_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos a HARc Hin
          ltac:(change (frame_addr lyc CRT_CID pos) with F; rewrite HFB; lia) Himg).
      * unfold kLowMemEnd in Hlow. unfold SHADOW_OFF in Hshb. lia.
    + intros Hx. destruct Ha as [Ha | Ha].
      * exact (Hdap a Hx ltac:(change (frame_addr lyc CRT_CID pos) with F; lia)).
      * destruct (Hdb a Hx) as (_ & _ & _ & Happ).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF in Hshb. lia.
    + intros p n Hpn Hx.
      destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc p n HARc Hpn) as (_ & H4096 & Hbc & Hbapp & _).
      destruct Ha as [Ha | Ha].
      * pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc p n CRT_CID pos HARc Hpn Hin) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd. change (frame_addr lyc CRT_CID pos) with F in Hd.
        lia.
      * unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF in Hshb. lia.
  - intros a Ha. exact (proj1 (Hdb2 a Ha)).
  - lia.
  - lia. }
split.
{ intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2); [|exact (HSV j Hj)].
  intros i Hi. apply HKz; [lia|]. unfold SHADOW_OFF in Hshb. lia. }
split.
{ rewrite HFB. change (frame_addr lyc CRT_CID pos) with F. rewrite <- HFL. apply ts_rdword_keep.
  intros j Hj. apply HKz; [lia|]. unfold SHADOW_OFF in Hshb. lia. }
split; [intros HM0; exact (HMN2 (HPM HM0))|].
split; [exact HFZ|]. split; [exact HFK|].
split.
{ change (frame_addr lyc CRT_CID pos) with F. apply (ct_bregs_pres (ms_regs ms) regs2 F); [|exact HP2].
  exact (ct_bregs_keep rg (ms_regs ms) F HBR KR). }
rewrite (ts_ap _ _ 21%bv HP2) by ts_cs.
rewrite (KR 21%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R21.
Qed.

(* ---- J (+0x348): `mv a0, s4; jal pj_free` - the run and the call of the tpj_free_specX text at n = DOC_D
   (PRH_FnPj.v dc0d0aa79c0f), GIVEN copy's order list F and the class-24 bound at the join, its one room premise for a
   non-NULL argument (position-free). Its post is the state at +0x350 that ct_at_Z takes (ct_bd's facts), with ct_qt0
   (QT without its r = 0 position) and the text's POSITION TRANSFER: every position at Sc whose next events are
   prhPj_free_evs F advances exactly by them at S2. pj_free's post gives the blocks back (Lam' with
   Lamc ~ Dc ++ Lam', ablocks with Dc's removed) and the ledger at S2 with the same g_most / g_own_ran_out cells
   (prh_ledger .. most own): that is how QT's two cells cross the join. (Crt102Tail.v's ct_J_call, at the B'
   registers and offsets.) ---- *)
Lemma ct_J_call : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r (F : list (Z * Z)),
  JB fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget Sc [] ->
  pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc F ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF_B rg memc mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k,
       c2 = mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z_OFF_B))) mem2 (YK11.seg_rom SEGS)) md2 /\
       (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 k WS /\
          YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS) /\
       ct_qt0 ly2 S2 Hp2 W2 mem2 r /\
       (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
          (H0 : list Z) (hist : list YG00.chunk),
          PresetRoomPos.iface_room_pos sm x os i H0 hist Sc -> prh_run_at sm x os i (prhPj_free_evs F) ->
          exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPj_free_evs F))%nat H0 hist' S2) /\
       saved W2 mem2 /\
       rdword (aview SEGS (w_H W2) mem2) (frame_addr ly2 CRT_CID pos + fs_frame_bytes CRT_CID - 8)
         = Some (flag_addr ly2 CRT_CID pos) /\
       (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) /\
       bregsB regs2 (frame_addr ly2 CRT_CID pos) /\ getr regs2 21 = w64 r).
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r Fo HJB HC24 HHB HFO.
pose proof (crt_at_J_B_live HJB) as HL. pose proof (crt_at_J_B_bregs HJB) as HBR.
pose proof (crt_at_J_B_ret HJB) as R21. pose proof (crt_at_J_B_r0 HJB) as Hr00.
pose proof (crt_at_J_B_count HJB) as HCS.
(* frm_zero's Z.land / Z.shiftr body is kept behind a thunk for pj_free's fpre, whose fifth conjunct is the entry
   rounding mode of the arms' float state fxk (as Crt102Tail.v's ct_J_call) *)
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact (crt_at_J_B_frm_zero HJB)).
destruct (crt_live_journal HL) as (WSJ & HJ & HBJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPA.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_copy_open HL) as HRA.
pose proof (crt_live_copy_hull HL) as HHV. pose proof (crt_live_memnorm HL) as HMN.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_peak HSD) as HPK.
pose proof (crt_side_room HSD) as HRL. pose proof (crt_side_arodata HSD) as HROD.
pose proof (crt_side_doc HSD) as HDOC. pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof (crt_frame_listed HFRM) as Hin. pose proof (crt_frame_flag_word HFRM) as HFLW.
ct_bregs HBR.
clear HJB HL HSD HFRM.
pose proof HPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HROD0 & Hhi & HraC).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@YM05.alloc_ceiling_lt rc) as Hc47.
pose proof ct_fb3 as HFB. pose proof ct_stk as (Hk1 & Hk2 & Hk3).
pose proof HJ as (HARc & HLY0 & HSEC0 & _ & _ & HFRc & _ & _ & J1 & _).
pose proof HLY0 as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & Eslo & Eshi & _).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc CRT_CID pos HARc Hin) as (F32 & Fapp & Ffr & Fsh).
rewrite HFB in Fb2, Fb3, Fapp, Ffr, Fsh.
set (F := frame_addr lyc CRT_CID pos) in *.
destruct (ct_sp1_range Hal16 ltac:(lia)) as (Hsp1a & Hsp1b).
unfold CRT_OFF_COPY in *.
set (v := F + 224) in *.
(* the run J *)
assert (HS : st_ok_pi SEGS VAL (TEB regs rg []) ss_J
  (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_J_OFF_B))) memc (YK11.seg_rom SEGS)))).
{ apply (ts_st_ok (fx := fxk)); [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEB regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEB regs rg [])) by apply te_env.
pose proof HJ as HJ0.
pose (RUN := @Crt102Kit.crt_run_xw fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS WSJ).
unfold crt_cfg.
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ apply awr_ok_nil. }
apply frame_of_read_only in HF; [|vm_compute; reflexivity]. clear HFr HG.
lazymatch goal with |- YA0nH.SRr' _ _ _ (mkCfg _ ?mdx) _ => set (MDX := mdx) in * end.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1.
assert (KR : forall rr : bv 5, In rr [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) rr = getr rg rr).
{ intros rr Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [ct_keep HS |]). destruct Hr. }
assert (X10 : getr (ms_regs ms) 10 = w64 v) by (rewrite Q10, <- R20; te_close).
assert (X1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z_OFF_B))) by (rewrite Q1; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (sp1 - sp0)).
{ unfold spZ. rewrite (KR 2%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R2.
  unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hgp' : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite (KR 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R3; exact Hgp).
assert (Htp' : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite (KR 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R4; exact Htp).
assert (Es0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite (KR 8%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R8.
  unfold w64. apply unsigned_lit_small. lia. }
assert (HZlow : 0 <= BASE + (CRT_PC_B + CRT_Z_OFF_B) < kLowMemEnd).
{ destruct ct_slots as [(e & He) _].
  exact (ct_slot_low (CRT_PC_B + CRT_Z_OFF_B) e ltac:(pose proof ct_pc; unfold CRT_Z_OFF_B; lia) He). }
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z_OFF_B)))).
{ apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PA)); [pose proof ct_pc; unfold CRT_Z_OFF_B; lia | reflexivity]. }
assert (Hra4' : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z_OFF_B)))).
{ pose proof (@pa_B_ok _ _ PA) as HB. pose proof ct_pc. rewrite unsigned_lit_small by (unfold CRT_Z_OFF_B; lia).
  unfold CRT_Z_OFF_B. lia. }
(* the frame chain at the call: s0 = the entry sp, whose record is the two saved words below it *)
assert (HCH : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem ms)) (sp0 + (sp1 - sp0)) (s0Z (ms_regs ms)) ch1).
{ rewrite Es0, HF. destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((sp0, raZ regs, s0Z regs) :: ch). apply (achain_ly_top ly lyc); [exact Etopc|].
    apply (achain_push ly (aview SEGS (w_H W) mem) (aview SEGS (w_H Wc) memc) sp0 (s0Z regs) (raZ regs) ch
      (sp0 + (sp1 - sp0)) Hch).
    + lia.
    + intros a Ha. apply J1; lia.
    + pose proof (HSV 0%nat ltac:(lia)) as V. change (nth 0 CRT_SAVED 0%bv) with (1%bv : bv 5) in V.
      replace (sp0 - 8 * (Z.of_nat 0 + 1)) with (sp0 - 8) in V by (cbn; lia).
      pose proof (bv_unsigned_in_range 64 (getr regs 1)) as BR. change (bv_modulus 64) with (2 ^ 64) in BR.
      unfold raZ. exact (ct_rdword_of_vm SEGS _ _ _ _ V BR).
    + pose proof (HSV 1%nat ltac:(lia)) as V. change (nth 1 CRT_SAVED 0%bv) with (8%bv : bv 5) in V.
      replace (sp0 - 8 * (Z.of_nat 1 + 1)) with (sp0 - 16) in V by (cbn; lia).
      pose proof (bv_unsigned_in_range 64 (getr regs 8)) as BR. change (bv_modulus 64) with (2 ^ 64) in BR.
      unfold s0Z. exact (ct_rdword_of_vm SEGS _ _ _ _ V BR).
    + exact Hra4.
    + lia.
    + lia.
    + exact Hlt.
    + lia.
  - exists []. left. split; [right; left; rewrite Etopc; lia | reflexivity]. }
destruct HCH as (ch1 & Hch1).
(* the blocks pj_free frees: in Sc's blocks, not in the entry's *)
assert (HDcb : forall a' k', In (a', k') Dc -> 0 <= k' /\ In (a' - cf_head, k' + cf_head) (ablocks B lyc Sc) /\
  ~ In (a' - cf_head, k' + cf_head) (ablocks B ly S)).
{ intros a' k' Hak.
  assert (HinL : In (a', k') Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hak).
  pose proof (prh_ledger_blocks B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc most ownc HLED) as HF0.
  rewrite Forall_forall in HF0. destruct (HF0 (a', k') HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  split; [exact Hk0|]. split; [exact Hab|].
  intros HinS.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hab) as (_ & _ & _ & _ & _ & Hpw).
  pose proof (ct_pairwise_perm _ zdisjoint ltac:(intros x y [H1|H1]; [right|left]; exact H1) _ _
    (Permutation_map (fun b => (fst b, req_size (snd b))) HPA) Hpw) as Hpw'.
  rewrite map_app in Hpw'.
  pose proof (ct_pairwise_app_dup _ _ _ _ _ Hpw' (in_map (fun b => (fst b, req_size (snd b))) _ _ HinS)
    (in_map (fun b => (fst b, req_size (snd b))) _ _
      (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Dc (a', k') Hak))) as Hself.
  unfold zdisjoint in Hself. cbn [fst snd] in Hself. change (@cf_head CfParams_preset) with 16 in *.
  unfold req_size in Hself. destruct (Z.eqb_spec (k' + 16) 0); lia. }
(* pj_free's footprint: copy's 56 bytes and the blocks it frees *)
assert (HFP1 : forall a, inFP (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl Dc)) a ->
  (v <= a < v + 56) \/ exists a' k', In (a', k') Dc /\ a' - cf_head <= a < a' - cf_head + req_size (k' + cf_head)).
{ intros a Ha. rewrite (proj2 (Z.eqb_neq v 0)) in Ha by lia. apply inFP_cons in Ha as [Ha | Ha]; [left; exact Ha|].
  right. destruct Ha as (bb & Hbb & Hab). unfold ablocks_fp, prhPj_hbl in Hbb. rewrite map_map in Hbb.
  apply in_map_iff in Hbb as ((a' & k') & Ebb & Hak). subst bb. cbn [fst snd] in Hab. exists a', k'. split; assumption. }
(* a byte of the frame (3, pos) or of a live block apart from Dc is not in the footprint *)
assert (HFP1f : forall cid pos' a, In (cid, pos') (frames Sc) -> (cid, pos') <> (CRT_CID, pos) ->
  frame_addr lyc cid pos' <= a < frame_addr lyc cid pos' + fs_frame_bytes cid ->
  ~ inFP (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl Dc)) a).
{ intros cid pos' a Hin' Hne Ha Hx. destruct (HFP1 a Hx) as [Hv | (a' & k' & Hak & Hb)].
  - rewrite HFRc in Hin'. cbn [app] in Hin'. destruct Hin' as [E | Hin']; [exact (Hne (eq_sym E))|].
    apply in_split in Hin' as (l2 & l3 & El).
    pose proof (sep_frames_pos_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc (CRT_CID, pos) (cid, pos') [] l2 l3 HARc
      ltac:(rewrite HFRc, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd. change (frame_addr lyc CRT_CID pos) with F in Hd.
    unfold v in Hv. lia.
  - destruct (HDcb a' k' Hak) as (_ & Hab & _).
    pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ cid pos' HARc Hab Hin') as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HFP1s : forall a, F <= a < F + 512 -> ~ (v <= a < v + 56) ->
  ~ inFP (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl Dc)) a).
{ intros a Ha Hnv Hx. destruct (HFP1 a Hx) as [Hv | (a' & k' & Hak & Hb)]; [exact (Hnv Hv)|].
  destruct (HDcb a' k' Hak) as (_ & Hab & _).
  pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hab Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd. change (frame_addr lyc CRT_CID pos) with F in Hd. lia. }
assert (HFP1b : forall a k x, In (a, k) Lamc -> ~ In (a, k) Dc -> a - 16 <= x < a + k ->
  ~ inFP (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl Dc)) x).
{ intros a k x HinL HnD Hx Hfp.
  pose proof (prh_ledger_blocks B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc most ownc HLED) as HF0.
  rewrite Forall_forall in HF0. destruct (HF0 (a, k) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  change (@cf_head CfParams_preset) with 16 in *.
  destruct (HFP1 x Hfp) as [Hv | (a' & k' & Hak & Hb)].
  - pose proof (sep_block_frame_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ CRT_CID pos HARc Hab Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd. change (frame_addr lyc CRT_CID pos) with F in Hd.
    unfold req_size in Hd. destruct (Z.eqb_spec (k + 16) 0); unfold v in Hv; lia.
  - destruct (HDcb a' k' Hak) as (Hk0' & Hab' & _). change (@cf_head CfParams_preset) with 16 in *.
    assert (Hne : (a - 16, k + 16) <> (a' - 16, k' + 16)).
    { intros E. injection E as E1 E2. apply HnD. replace a with a' by lia. replace k with k' by lia. exact Hak. }
    pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hab Hab' Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd, Hb.
    destruct (Z.eqb_spec (k + 16) 0); destruct (Z.eqb_spec (k' + 16) 0); lia. }
eapply YSRrG.SRr'_bind.
{ (* the caller's journal is at crt_at_J_B's budget WSJ: the budgeted window call rule at the callee's empty budget,
     P := (fun WS1 => WS1 = []), at RZW (YCbqGwild.aj_call_xWb_spR); pj_free's post (fpostWmR at wle', the text's
     re-hiding form) by YCbqGwild.fpostW_xb_of_xR (as Crt102Tail.v's ct_J_call) *)
  refine (YCbqGwild.aj_call_xWb_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc _ _ ms STKC sp0
    [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc MDX kj WSJ STKPF 0
    (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl Dc))
    (sp1 - sp0) (Z_to_bv 64 (BASE + (CRT_PC_B + CRT_Z_OFF_B))) ch1 (fun WS1 => WS1 = []) _ HS eq_refl HJ Hsp
    ltac:(lia) ltac:(lia) Hk3 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hgp' Htp' X1 Hraw Hra4' Hch1 _ _).
  - (* the callee: pj_free's text *)
    intros HPREc HWIN. cbn [ss_pc setpc].
    assert (HFPRE : fpre B ARx STKPF lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MDX ch1).
    { split; [exact HPREc|]. split; [rewrite HF; exact HROD|]. split; [rewrite Hsp, Eshi; lia|]. split.
      - unfold raZ. rewrite X1, unsigned_lit_small by lia. lia.
      - exact (HFZ' tt). }
    assert (HSLOT : v <> 0 /\ v < YM05.alloc_ceiling /\
      pj_foR SEGS (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc) DOC_D v Dc Fo /\
      prhPj_slot B STKPF 0 lyc Sc Lamc Wc (ms_regs ms) (ms_mem ms) v).
    { rewrite HF. split; [lia|]. split; [lia|]. split; [exact HFO|].
      unfold prhPj_slot. split; [lia|]. split.
      { right; right; left. exists CRT_CID, pos. split; [exact Hin|]. rewrite HFB. change (frame_addr lyc CRT_CID pos) with F. lia. }
      split.
      { split; [lia|]. intros x Hx. apply (apresent_writable SEGS). exact (proj1 (Ffr x ltac:(lia))). }
      split.
      { unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp. unfold kLowMemEnd, kHighMemEnd.
        destruct Fapp as (_ & [HLo | [HH1 HH2]]); [left; lia | right; split; lia]. }
      split.
      { intros a Ha. split; [exact (proj2 (Ffr a ltac:(lia)))|]. rewrite Hsp. lia. }
      split; [exact HRA | exact HHV]. }
    assert (HLED' : prh_ledger B lyc Sc Hpc Wc (ms_mem ms) Lamc peakc cntc SIZE_MAXZ ranc most ownc)
      by (rewrite HF; exact HLED).
    (* the text's position-free entry: the class-24 bound at the join (the premise HC24), pj_free's hull budget (the
       premise HHB), copy's order list Fo *)
    pose proof (PJFREE fxk most ownc lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MDX ch1 0 v Dc Fo Lamc
      peakc cntc SIZE_MAXZ ranc HFPRE HCL HRL (fun _ => HC24) (fun _ => HHB) X10 HWIN (or_intror HSLOT)
      CfParamsPreset.preset_head_wide HLED') as HPJ.
    unfold cfg_at, w64 in HPJ. unfold fpostWmR, fpostWR in HPJ.
    eapply YSRrG.SRr'_mono; [exact HPJ|].
    intros W' c' _ Hpo. apply YCbqGwild.fpostW_xb_of_xR; [reflexivity | exact Hpo].
  - (* pj_free's footprint is the caller's own frame and the blocks the body made *)
    intros a Ha. destruct (HFP1 a Ha) as [Hv | (a' & k' & Hak & Hb)].
    + right; right; left. exists (CRT_CID, pos). split; [left; reflexivity|]. unfold in_zr, frame_rng. cbn [fst snd].
      rewrite HFB. change (frame_addr lyc CRT_CID pos) with F. unfold v in Hv. lia.
    + right; left. destruct (HDcb a' k' Hak) as (_ & Hab & HnS). exists (a' - cf_head), (k' + cf_head).
      split; [exact Hab|]. split; [exact HnS | exact Hb]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HPW & HJ2 & HJc & _ & HP2 & HQPJ).
subst WS1. rewrite app_nil_r in HJ2.
(* pj_free's post (the text's Q, PRH_FnPj.tpfP_Q) read through its named projections (tpfP_R), never by position: the
   room, THE HULL USE (frees keep both meters; not read past the call), the position transfer, the blocks and the
   ledger *)
destruct HQPJ as (HQPJ & HMN2).
apply PRH_FnPj.tpfP_R_of with (regs' := regs2) (md' := md2) in HQPJ. destruct HQPJ as (Lam' & HQR).
pose proof (PRH_FnPj.tpfP_room HQR) as HRL2. pose proof (PRH_FnPj.tpfP_pos HQR) as HTR.
pose proof (PRH_FnPj.tpfP_lam HQR) as HPL'. pose proof (PRH_FnPj.tpfP_ablocks HQR) as HPA'.
pose proof (PRH_FnPj.tpfP_ledger HQR) as HLED2.
rewrite HF in HJc, HMN2.
pose proof HJc as (HARc2 & Hlyc2 & _ & _ & _ & Hfrs2 & _ & _ & G1 & G2 & _ & G4 & _).
assert (EF2 : frame_addr ly2 CRT_CID pos = F).
{ unfold F, frame_addr. destruct Hlyc2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (EFl2 : flag_addr ly2 CRT_CID pos = flag_addr lyc CRT_CID pos).
{ unfold flag_addr. destruct Hlyc2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (HLY2 : layout_le (length (st_secs S)) ly ly2).
{ pose proof HJ0 as (_ & _ & Hsc0 & _). eapply layout_le_trans; [exact Hsc0 | exact HLY0 | exact Hlyc2]. }
assert (HFS2 : forall f, In f (frames S) -> In f (frames S2)) by (intros f Hf; rewrite Hfrs2, HFRc; right; exact Hf).
destruct (ct_doc_bytes ly2 S2 Hp2 W2 mem2 md2 _ HARc2 HLY2 HFS2) as (Hd4 & Hdc & Hdb2).
(* the blocks of the document *)
assert (HDL' : forall bk, In bk D -> In bk Lam').
{ intros bk Hbk. pose proof (Permutation_in _ HPL' (HDL bk Hbk)) as H1.
  apply in_app_or in H1 as [H1 | H1]; [exfalso; exact (HAP bk H1 Hbk) | exact H1]. }
apply YSRrG.SRr'_ret. exists ly2, S2, Hp2, regs2, mem2, md2, (kj + k1).
split; [first [reflexivity | rewrite <- X1; reflexivity]|].
split; [exists WSJ; split; [exact HJ2 | exact HBJ]|].
rewrite EF2, EFl2.
split.
{ (* QT's facts after pj_free, its r = 0 position aside *)
  unfold ct_qt0. split; [exact HRL2|].
  destruct HCS as (cset & Hcs & Hcs0 & HR).
  exists Lam', peakc, cset, cntc, ranc, ownc.
  split.
  { apply (Permutation_app_inv_l Dc). transitivity Lamc; [symmetry; exact HPL' | exact HPL]. }
  split.
  { apply (Permutation_app_inv_l (prhPj_hbl Dc)). transitivity (ablocks B lyc Sc); [symmetry; exact HPA'|].
    transitivity (ablocks B ly S ++ ck_hblks Dc); [exact HPA | apply Permutation_app_comm]. }
  split; [exact HPK|]. split; [exact Hcs|]. split; [exact Hcs0|]. split; [exact HLED2|].
  split.
  { apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wc) memc) (mrestrict (w_H W2) mem2) (prh_lin Lam') doc D).
    - apply (ct_nodeR_lblk SEGS t _ (prh_lin Lamc) (prh_lin Lam') doc D HDOC). intros x k Hx _. exact (HDL' _ Hx).
    - intros x [Hx | ((a, k) & Hb & Hx)].
      + destruct (ct_doc_frame lyc Sc _ HLY0 ltac:(intros f Hf; rewrite HFRc; right; exact Hf))
          as (cid & pos' & HinS & HinSc & Hd1 & Hd2).
        assert (Hne : (cid, pos') <> (CRT_CID, pos)).
        { intros E. rewrite E in HinS. pose proof (ct_doc_apart lyc Sc Hpc Wc memc mdc pos _ HARc HLY0 HFRc x Hx) as Hap.
          rewrite HFB in Hap. injection E as -> ->. change (frame_addr lyc CRT_CID pos) with F in Hd1, Hd2. rewrite HFB in Hd2.
          apply Hap. change (frame_addr lyc CRT_CID pos) with F. lia. }
        split.
        * apply (mbyte_of_aview SEGS). apply (G4 cid pos' x HinSc); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
          exact (HFP1f cid pos' x HinSc Hne ltac:(lia)).
        * intros _. apply (apresent_writable SEGS). exact (proj1 (Hdb2 x Hx)).
      + unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
        assert (HinL : In (a, k) Lamc) by exact (HDL _ Hb).
        assert (HnD : ~ In (a, k) Dc) by (intros Hc; exact (HAP _ Hc Hb)).
        pose proof (prh_ledger_blocks B lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ ranc most ownc HLED) as HF0.
        rewrite Forall_forall in HF0. destruct (HF0 (a, k) HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
        pose proof (prh_ledger_blocks B ly2 S2 Hp2 W2 mem2 Lam' peakc cntc SIZE_MAXZ ranc most ownc HLED2) as HF2.
        rewrite Forall_forall in HF2. destruct (HF2 (a, k) (HDL' _ Hb)) as (_ & Hab2 & _). cbn [fst snd] in Hab2.
        change (@cf_head CfParams_preset) with 16 in *.
        assert (Hrq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
        replace x with (a - 16 + (x - (a - 16))) by lia.
        split.
        * apply (mbyte_of_aview SEGS). apply (G2 (a - 16) (k + 16) (x - (a - 16)) Hab Hab2); [lia|].
          replace (a - 16 + (x - (a - 16))) with x by lia. exact (HFP1b a k x HinL HnD ltac:(lia)).
        * intros _. apply (apresent_writable SEGS).
          destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HARc2 Hab2) as (_ & _ & _ & _ & Hbp & _).
          exact (proj1 (Hbp (a - 16 + (x - (a - 16))) ltac:(rewrite Hrq; lia))). }
  split; [exact HDL'|].
  (* r = 0 (crt_at_J_B_r0; the r = 1 arm is dead under the text's prh_cons_from), then crt_at_J_B_count's arms in
     QT's order (it states the r = 0 arm as `ranc = ran /\ cntc = ..`) *)
  split; [exact Hr00|].
  destruct HR as [HR1 | (E1 & E2 & E3 & E4 & _)]; [left; exact HR1|].
  right. split; [exact E1|]. split; [exact E2|]. split; [exact E4|]. exact E3. }
(* the position transfer pj_free's text gives: the EXACT advance by its own events *)
split; [exact HTR|].
split.
{ intros j Hj. apply (ts_vm_av (w_H Wc) (w_H W2) memc mem2); [|exact (HSV j Hj)].
  intros i Hi. apply G1; lia. }
split.
{ rewrite HFB. change (frame_addr lyc CRT_CID pos) with F. rewrite <- HFB.
  rewrite <- HFLW. apply ts_rdword_keep. intros j Hj. rewrite HFB.
  apply (G4 CRT_CID pos); [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFB; change (frame_addr lyc CRT_CID pos) with F; lia|].
  apply HFP1s; unfold v; lia. }
split; [intros HM0; exact (HMN2 (HMN HM0))|].
split.
{ apply (ct_bregs_pres (ms_regs ms) regs2 F); [|exact HP2]. exact (ct_bregs_keep rg (ms_regs ms) F HBR KR). }
rewrite (ts_ap _ _ 21%bv HP2) by ts_cs.
rewrite (KR 21%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R21.
Qed.

(* ---- THE r = 0 END POSITION (Crt102Tail.v's ct_evs_J / ct_r0_end, at this file's ct_pos_end). crt_at_J_B_count's
   r = 0 arm gives copy's ORDERED free list Fc with `map (snd + cf_head) Fc = fo crt_tree_J`, so pj_free's request
   list is the model's HBulk, in its order. GIVEN the run premise for pj_free's own events, the position
   transfer lands at QT's end position: one bulk event advances by one; an empty order list makes no event, its
   permutation forces fo = [], and the model's HBulk [] is stepped over (prhPj_bulk_nil_pos). ---- *)
#[local] Notation ctJ := (crt_tree_J (t := t)).
Lemma ct_evs_J : crt_evs_J (t := t) = [PresetReqAt.HBulk (PresetReqAt.fo ctJ)].
(* `clear - t`: destructing the Section variable t would otherwise revert, and so take, HTREE and HRQA *)
Proof. clear - t. unfold crt_evs_J, crt_tree_J. destruct t; reflexivity. Qed.
Lemma ct_r0_end : forall pre (F : list (Z * Z)),
  PresetReqAt.round_trip rp_sm t = pre ++ crt_evs_J (t := t) ->
  prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat (crt_evs_J (t := t)) ->
  Permutation (map (fun b => snd b + cf_head) F) (PresetReqAt.fo ctJ) ->
  forall S2 h, PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (rp_i + length pre + length (prhPj_free_evs F))%nat
    rp_H0 h S2 -> ct_pos_end S2.
Proof.
(* the request bound is not read here: cleared, so lia's reification does not pull it into the term *)
clear HRQA.
intros pre F Epre Hrun Hperm S2 h HP.
rewrite ct_evs_J in Epre, Hrun.
assert (EL : (rp_i + length (PresetReqAt.round_trip rp_sm t))%nat = Datatypes.S (rp_i + length pre)%nat)
  by (rewrite Epre, length_app; cbn [length]; lia).
unfold ct_pos_end. rewrite EL.
destruct F as [|b F'].
- (* no blocks: fo crt_tree_J = [], and the model's HBulk [] is stepped over *)
  cbn [map] in Hperm. apply Permutation_nil in Hperm. rewrite Hperm in Hrun.
  cbn [prhPj_free_evs length] in HP. rewrite Nat.add_0_r in HP.
  apply (proj1 (prh_run_at_one rp_sm rp_x rp_os _ _)) in Hrun.
  exists h. exact (proj1 (prhPj_bulk_nil_pos rp_sm rp_x rp_os _ rp_H0 h S2 Hrun) HP).
- (* the one bulk event *)
  cbn [prhPj_free_evs length] in HP. exists h.
  replace (Datatypes.S (rp_i + length pre)) with (rp_i + length pre + 1)%nat by lia. exact HP.
Qed.

(* ---- THE TAIL, composed: J (+0x348) .. the `ret`, the statement the glue fixes, for EVERY r. Every piece above is
   its own Qed lemma (ct_J_call, ct_r0_end, ct_at_Z, ct_at_F, ct_qt_keep, ct_qt_of0); this script applies them. The
   r = 1 arm is DEAD: crt_at_J_B_r0 states r = 0 (tcheck_round_trip_specX kills it under its entry premise
   prh_cons_from, PRH_FnCheck 0b6f7b597757). The class-24 bound pj_free's text asks at a non-NULL argument is
   Crt102KitB.cb_J_B_ccnt24's, cited. The r = 0 arm reads crt_at_J_B_count's r = 0 arm: copy's ORDERED free list Fc
   (its requests ARE fo crt_tree_J, in order) is pj_free's order list, so pj_free's own events are the model's
   crt_evs_J and crt_pos's run premise supplies them; the position transfer carries crt_pos's position across
   pj_free, and ct_r0_end lands it at QT's end position. NO OPEN GOAL. ---- *)
Theorem crt102_tail_B : forall fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r,
  JB fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF_B rg memc mdc) QFB.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r HJB.
pose proof (crt_at_J_B_frm_zero HJB) as HFZ. pose proof (crt_at_J_B_fregs HJB) as HFK.
assert (HFZ' : unit -> frm_zero (@YK11.fp_csr fxk)) by (intros _; exact HFZ). clear HFZ.
(* the class-24 bound at the join (Crt102KitB.cb_J_B_ccnt24, read off crt_at_J_B_r0 / crt_at_J_B_count) *)
pose proof HJB as HC24. apply Crt102KitB.cb_J_B_ccnt24 in HC24.
(* from copy's order list and pj_free's hull budget at the join: ct_J_call, then ct_at_Z - once the r = 0 end position
   is had from the position transfer *)
assert (KONT : forall F,
  pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc F ->
  PresetHullBudget.hull_budget Sc [] ->
  (forall S2, (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
      (i : nat) (H0 : list Z) (hist : list YG00.chunk),
      PresetRoomPos.iface_room_pos sm x os i H0 hist Sc -> prh_run_at sm x os i (prhPj_free_evs F) ->
      exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPj_free_evs F))%nat H0 hist' S2) ->
    r = 0 -> ct_pos_end S2) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (CFG fxk CRT_J_OFF_B rg memc mdc) QFB).
{ intros F HFO HHB HEND.
  eapply YSRrG.SRr'_bind; [exact (ct_J_call fxk lyc Sc Hpc Wc memc mdc kj pos Lamc peakc cntc ownc ranc Dc rg r
    F HJB HC24 HHB HFO)|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k & -> & HJ2 & HQ0 & HTR & HSV2 & HFL2 & HMN2 &
    HBR2 & R21').
  apply (ct_at_Z fxk ly2 S2 Hp2 W2 mem2 md2 k pos regs2 r).
  exact (conj HJ2 (conj (ct_qt_of0 ly2 S2 Hp2 W2 mem2 r HQ0 (HEND S2 HTR)) (conj HSV2 (conj HFL2 (conj HMN2
    (conj (HFZ' tt) (conj HFK (conj HBR2 R21')))))))). }
pose proof (crt_at_J_B_r0 HJB) as Hr00.
destruct (crt_at_J_B_count HJB) as
  (cset & _ & _ & [(Hr1 & _) | (_ & _ & _ & _ & HPOS & _ & _ & (Fc & HFOc & HFc) & _)]).
- (* r = 1: DEAD. crt_at_J_B_r0 states r = 0, so the tail never sees an r = 1 state *)
  exfalso. rewrite Hr00 in Hr1. discriminate Hr1.
- (* r = 0: copy's order list is crt_at_J_B_count's ORDERED free list Fc; crt_pos's position and run premise *)
  destruct (crt_pos_ex HPOS) as (pre & hist & HA).
  pose proof (crt_pos_split HA) as Epre. pose proof (crt_pos_room HA) as HRP.
  pose proof (crt_pos_run HA) as Hrun.
  assert (Hperm : Permutation (map (fun b => snd b + cf_head) Fc) (PresetReqAt.fo ctJ))
    by (rewrite HFc; apply Permutation_refl).
  assert (HRUN : prh_run_at rp_sm rp_x rp_os (rp_i + length pre)%nat (prhPj_free_evs Fc)).
  { destruct Fc as [|b Fc'].
    - (* no blocks: pj_free makes no event *)
      exact (prhPj_free_evs_nil rp_sm rp_x rp_os _).
    - (* one bulk event, fo crt_tree_J's requests in order: the model's own *)
      change (prhPj_free_evs (b :: Fc')) with [PresetReqAt.HBulk (map (fun b0 => snd b0 + cf_head) (b :: Fc'))].
      rewrite HFc. rewrite ct_evs_J in Hrun. exact Hrun. }
  (* pj_free's hull budget (its fuzz_free calls' admission) from crt_pos's position in a run of at most 4 calls *)
  apply (KONT Fc HFOc (Crt102HullPos.hull_budget_nil_of_room_pos rp_sm rp_x rp_os _ rp_H0 hist Sc HOS4 HRP)).
  intros S2 HTR _. destruct (HTR _ _ _ _ _ _ HRP HRUN) as (h' & HP).
  exact (ct_r0_end pre Fc Epre Hrun Hperm S2 h' HP).
Qed.

End g.
End f.
End w.

(* THE ELABORATED BODIES of this file's Prop-bodied definitions (as Crt102Tail.v prints its own: `Print`, implicits
   on, notations off), printed on every build: ct_qt0 / ct_pos_end / ct_qt bind no FPState; ct_bd takes the Section's
   fx only in `fregs_kept_x fx fxk` and the arms' fxk in `frm_zero (fp_csr fxk)`, as meant. *)
Set Printing Implicit.
Unset Printing Notations.
Print ct_qt0.
Print ct_pos_end.
Print ct_qt.
Print ct_bd.
Unset Printing Implicit.
Set Printing Notations.

Print Assumptions crt102_tail_B.

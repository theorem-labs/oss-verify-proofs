(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 2950 of its 3006 lines of code are new or changed and 395 lines of the source are left out. *)
(* fuzz_preset, slice S5b, lane PV-arms-LC (image A', asan 1be0f53d96cb, the #102 pins): the LITERAL and CONTAINER arms of
   parse_value's dispatch, as two SEGMENT lemmas from VproC's dispatch state (lib/A/VrdPro.v vrd_disp_a) to
   the epilogue state (lib/A/VrdNum.v vrd_epi_a, row 225), which lib/A/VrdEpiA.v vrd_epi_step and
   lib/A/VrdEpiP.v vrd_epi_step_P carry to tparse_value_specX's budgeted post.

   rule 24: no function proved. rule 24: proves no function (kind: segment lemma). Neither arm is a function:
   each takes the state the dispatch hands it and its callee's PUBLISHED text, and stops at the shared
   epilogue's boundary. a working branch 45cffb16b86 (lib/A/Prog/PvLit.v, PvItems.v) is an old-vocabulary reading
   aid over the ORIGINAL images: nothing of it is Required, cited or copied here.

   SET: the kit's cut 7cdbb61b5fa0 (a working branch) with a Theorem Labs lane's green value side on it,
   a working branch e942c5680fa7 (VrdPro.v 257b4f5473ca, VrdNum.v 636d54d20156, VrdArm.v 8866f9b206f2; the
   interface first relayed at preset-tree-at-2026-10-30T06-44-04Z.tsv (sha256 4bb5178564c2; internal record), unchanged in every statement read here). The kit texts this file reads
   are the cut's: PRH_FnParse.v f0d92dcec7e9 (tparse_items_specX, tparse_value_specX), PRH_FnReader.v f1ae32e3b2cd
   (tliteral_specX), PRH_Base.v ef7c8ca98529, PRH_PjOrder.v e5917626b82b, and the engine's wild-budget layer
   lib/Reusable/YCbqGwild.v 0c63874858e4.
   History: first proved on image A in VrdArmLC.v (sha256 007e20a81b45; internal record), re-pointed to image A' and the
   post-implication texts (a working branch 0cac6dd1e116), and re-fit here to the cut interface:
   - THE CURSOR SET CW replaces the run-word list DW in every statement (vrd_disp_a, vrd_epi_a, the callee texts).
     vrd_disp_body appends three conjuncts, each named here by its type: prh_cw_entry B CW at the entry (HCW), the
     wild room against CW at the entry depot (HWR0), and the text below the ceiling (HTC). The container hands the
     first to parse_items at its call state with VrdPro.vrd_cur_entry_call (both halves), and the second unchanged
     (the dispatch moves only fake frames, `S = set_fs f S0`). prh_cur_entry lost its sp - 8 arm (vce_low reads its
     cursor-word bound by name).
   - THE CALL of parse_items is the engine's budgeted caller-window rule YCbqGwild.aj_call_xWFb_sp (the text's post is
     fpostWFbm at wbudget CW 0). The callee's wild budget WS1 comes back in the caller's journal; the rows after the
     call run on its rebased form (ajournal_xw_rebase) and vrd_epi_a's journal `exists WS, ajournal_xw .. WS /\
     wbudget CW 0 WS` is folded back with ajournal_xw_unbase0 at WS := WS1. The literal's text tliteral_specX posts
     no budget (fpostWm), so its journal is the budget-free one at WS := [].
   - vrd_pv_post's two new conjuncts: the FREE ORDER (under cf_head = PresetReqAt.HEAD, pj_foR at every depth bound)
     and pj_ncapR. The container reads both off parse_items' post, the value's free list at '[' / '{' being parse_items'
     (VrdNum.vrd_frees_cont); the literal's node is a leaf with no block, so its order list is [] (PRH_PjOrder.pfo_leaf
     on a hit, VrdNum.vrd_zero_fo on the untouched node of a miss) and the value's free
     list at a keyword is [] (vrd_frees_lit, by PresetFreeFo.jfv_leaf). pj_ncapR of a keyword is True.
   - NO count premise is stated here: parse_items' two live-count premises at the call are vrd_disp_body's entry
     counts (tparse_value_specX's, at S0) at parse_items' own all-granted trace, by vrd_gtrace_cont; the literal has
     none. No `iface_room_pos` entry conjunct: the texts state the position transfer post-implication.
   - THE HULL BUDGET (lib/Spec/PresetHullBudget.v): the container arm runs inside parse_value, so both container
     statements take tparse_value_specX's entry premise `hull_budget S0 (rd_hevs (prhPv_gtrace d ..))` right after
     vrd_disp_a. The call pays parse_items' budget from it: by vrd_gtrace_cont the two all-granted lists are one list,
     and the dispatch moves only fake frames (`S = set_fs f S0`), which keep st_secs (hull_budget_same). vrd_pv_post's
     hull use is the callee's (PRH_FnParse.v tpiP_hull) from the call state S, which has S0's st_secs:
     hull_used_secs gives S0 to S over [], hull_used_app joins the two. The literal reaches no allocator and takes no
     budget; its hull use is hull_used_secs over its empty granted trace.
   - THE OUTCOME OF AN INJECTED READING (the guarded conjunct after THE OUTCOME, in parse_items' post, PRH_FnParse.v
     tpiP_injected, and in vrd_pv_post): the container's is parse_items' at the call state, its events under the
     model's grant list moved to the opener by vrd_cont_model and its window by vrd_gtrace_cont; the literal's is
     vacuous (its granted trace is empty, so the window cnt <= fail < cnt is).
   - THE RE-HIDING RELATION (YA0nH.wle' at preset's zone YGcfRehidePost.RZ_cf): parse_items' text concludes
     SRr' segs RZ_cf with its post's journal at wle' segs RZ_cf, because the subtree it parses frees blocks. So the
     container statements conclude SRr' segs RZ_cf at the post vrd_arm_exitR (wle' segs RZ_cf), whose join is
     VrdNum.vrd_epi_aR at that relation. The proof lifts the dispatch journal ONCE (VrdEpiA.vlift_aj), then runs the
     engine's R forms at wle' segs RZ_cf: the runners paj_run_xR / paj_run_to_xR, the call rule
     YCbqGwild.aj_call_xWFb_spR, the depot moves ajournal_xw_rebaseR / ajournal_xw_unbase0R, SRrG_bind / SRrG_ret, and
     the journal read by the ajxR_* projections. The literal's text tliteral_specX crosses no free: the literal
     statements keep SRr and vrd_arm_exit (vrd_arm_exit is vrd_arm_exitR at wle, vrd_arm_exit_R_wle), and a caller that
     joins both arms lifts the literal's by YA0nH.SRr_SRr' and vrd_arm_exit_wle'.
   - Every kit and engine predicate is read BY NAME, never by position: vrd_disp_body, vrd_disp_a and the literal's
     post by shape (decompose [and], each conjunct renamed by its type, or an explicit shape guard: vdispa);
     parse_items' post by the kit's named projections (PRH_FnParse.v tpiP_R_of and the fields of tpiP_R, the
     consequents tpiP_outcome_ran / _run / _pos, tpiP_RSome_of / tpiP_RNone_of and their fields), so a conjunct the
     kit appends to that post moves no name here; the journal by the engine's ajx_* projections; prh_ledger by
     PRH_Base's ledger projections; prhPv_node, pj_in_okR, src_rd, rd_blocks_move, rd_room, prh_cur_entry, layout_le,
     astk_ok, fwin, vrd_regs, vrd_saved and vrd_frame by the projections and shape guards below (vnd_* / vin_* /
     vsr_* / vbm_* / vrr_live / vce_low / vly_* / vastk / vfw / vregs / vsav12 / vfrm3); fpre's ra bound by tauto on
     fpre alone. Each arm BUILDS its join and its result by name too: vrd_epi_aR through VrdNum's record vrd_epi_R
     (vrd_epi_aR_of_R) and vrd_pv_post through vrd_pv_R / vrd_pv_RSome / vrd_pv_RNone (vrd_pv_post_of_R), each field
     a named goal (?[e_*], ?[p_*], ?[s_*], ?[n_*]), so each proof is attached to its field's name, not its position.
   - A' listing slots: row r of parse_value is listing slot r + 4682, so the two return pcs are A_prog_base + 19596
     (row 217) and + 19624 (row 224).

   GENERIC P (the lead's 17:4xZ ruling, as VstrD's vrd_str_a_okP): each arm is proved for any memory invariant P.
   Neither arm's rows store before or after its call (the runs' frames are empty, so the call memory and the row-225
   memory are the dispatch memory and the callee's return memory, EMc0 / EM2 below), so P needs no runner law: P of
   the dispatch memory is P at the call; across the call P is carried by srr_inv_call from the callee's m-form post
   (parse_items' fpostWFbm and literal's fpostWm, PRH_Base.v fQmn: memnorm kept); and the container's callee asks memnorm AT ENTRY on these
   texts (tparse_items_specX's second premise), which srr_inv_mn gives from P. So the literal arm holds at
   P := True (vrd_lit_aLC_holds, the statement of before), but the container arm does NOT: srr_inv_mn at True is
   false, so its corollary is the instance P := memnorm (vrd_cont_aLC_holds, with memnorm of the dispatch memory).

   ROWS (lines of the neutral listing parse_value.fuzz_preset.asan.s (sha256 227a121e51cd; internal record); row r is
   listing slot A_prog_slot AS_parse_value + (r - 2) of lib/A/Listing_prog.v). No address is typed: every one is
   read from the listing or from PAImg_prog.v.
   - CONTAINER. The object case enters at row 131 (`a2 = 1`, `a0 = s4`, `a1 = s3`, `j` to row 216); the array
     case at row 213 (`a0 = s4`, `a1 = s3`, `a2 = 0`). Both reach row 216 `jal parse_items`, whose return site
     is row 217, and row 217 `j` joins the epilogue at ROW 224 (`mv s5, a0`), one row above row 225.
     parse_items is called AT THE SAME NESTING d: no register carries the depth; parse_items reads it from the
     cursor's third field and raises it itself.
   - LITERAL. "false" enters at row 119 (the `auipc` / `addi` pair of rows 119-120, `a2 = 1`, `j` to row 221),
     "null" at row 152 (rows 152-153 the pair, `a0 = s4`, `a2 = 0`, `j` to row 222), "true" at row 218 (rows
     218-219 the pair, `a2 = 2`), which falls through. All three reach rows 221-223 (`mv a0, s4`, `mv a3, s3`,
     `jal literal`) and FALL THROUGH to ROW 224.

   THE KEYWORD ADDRESS, BY NAME (a Theorem Labs lane's ruling; this lane owns the tie). Each pair's second slot is a
   PAddHi over the read-only atom, and YP0b.v:54-55 makes PAddHi rd rs j a off match `OpImm ALU_ADD` exactly
   when `val (A_HI j) + imm = val a + off`, so the address the hardware builds is `pa_val a + off` of THAT
   SLOT. vrd_kw_addr reads it out of A_prog_listing. No numeral of the address is written anywhere.

   THE KEYWORD'S BYTES. The kit's tliteral_specX (lib/A/PRH_FnReader.v:310-339 at the cut, blob f1ae32e3b2cd) takes cstr_ok and the
   garr8 READ premise with the keyword's NUL and the slack that fills its last granule, which is what
   a Theorem Labs lane's PROVED leaf carries (lib/Prog/literal_xs.v:62-67 at a working branch 4e25a816d2c).
   It no longer takes kept_at, so this lane carries no stand-in for it. That ruling (a Theorem Labs lane 03:35Z) came
   from this lane's measurement: on f0d2e8d4 the asan_globals records at 0xa6c00, 0xa6c40 and 0xa6c80 register
   .str.6 "true", .str.7 "false" and .str.8 "null" with sizes 5, 6 and 5 and size_with_redzone 32, so each
   first shadow granule is 05 / 06 / 05 and in_zs is false for it, and they are image bytes, so the Lam
   disjunct fails too.

   THE LITERAL CALLEE: the literal arm cites tliteral_specX as its callee contract and imports no proof of it.
   History: a Theorem Labs lane proved literal_holds : tliteral_specX (cp := CfParams_preset) (PI := prh_img_A)
   (PA := PI_prog_A) B ARx SK against the kit's text at PRH_FnReader.v blob 48aa30286d84 (a working branch
   3eba7d20dba lib/A/Prog/literal_bridge.v); the cut's text is blob f1ae32e3b2cd.

   NUMERALS. 176 (LENGTH: the dispatch's stack drop below parse_value's entry sp, 160 or 176, VrdPro.v:1089-1091 at the interface);
   119 / 120 / 131 / 152 / 153 / 213 / 215 / 216 / 218 / 219 / 221 / 224 are ROWS (DERIVED: listing slot
   indices); 116 / 102 / 110 / 123 / 91 are WORDs (the grammar's keyword and opener bytes, PjGrammar); 0 / 1 / 2
   are the node's type tags (WORD); 33 and 224 / 512 in the result are the kit's own bounds, cited not written. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YN3v YG0s YP07 YP0a YG0p YP0d YP0c YC80 YImgTop YC1fP YC80x YC1fPx YC80xf
YGcallx YCbqGcall YGcallSx YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoom PresetReqAt PresetLiveBounds
  PresetRoomPos PresetRoomPosKeep PresetRodata PresetFreeFo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive YCbqGwild YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog VrdPro VrdArm VrdNum.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import VrdEpiA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* lia over the arithmetic facts only (VstrD's slia, lib/A/VrdArmStrOk.v): the arms' contexts hold symbolic states,
   journals and run tables, and lia walks every hypothesis. slia first clears each hypothesis that is not an equation,
   an order fact or a propositional combination of them; it is used only where lia closes the goal, so the clearing
   never reaches another goal. *)
#[local] Ltac slia_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with Prop => idtac | _ => fail end;
      lazymatch T with
      | @eq _ _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
      | le _ _ => fail | lt _ _ => fail | ge _ _ => fail | gt _ _ => fail
      | _ /\ _ => fail | _ \/ _ => fail | ~ _ => fail | _ <> _ => fail
      | _ => clear H
      end
  end.
(* lia's cost in these contexts is its case split: it splits every disjunction and every negation (a negated order fact
   or an inequation is a disjunction to lia) in the context, 2 ^ k cases for k of them, and each mod fact adds a
   quotient. slia runs lia first with those facts hidden behind vrd_hold, then with one of them shown at a time, and
   only then over the whole context, as before: it proves the goals it proved before, and fails where it failed. *)
Definition vrd_hold (A : Prop) : Prop := A.
Lemma vrd_hide : forall A : Prop, A -> vrd_hold A.
Proof. intros A H. exact H. Qed.
#[local] Ltac slia_hide :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | vrd_hold _ => fail
      | context [_ \/ _] => apply vrd_hide in H
      | context [~ _] => apply vrd_hide in H
      | _ mod _ = _ => apply vrd_hide in H
      end
  end.
#[local] Ltac slia := slia_clear; first
  [ slia_hide; lia
  | slia_hide; match goal with H : vrd_hold _ |- _ => unfold vrd_hold in H; lia end
  | lia ].

(* ---------------------------------------------------------------------------------------------------- *)
(* 1. THE KEYWORD ADDRESS, read from the listing (no numeral of the address anywhere).                    *)
(* ---------------------------------------------------------------------------------------------------- *)

(* the row of the `addi` that completes each keyword's auipc / addi pair *)
Definition vrd_kw_row (b : Z) : nat :=
  if b =? 116 then 219%nat else if b =? 102 then 120%nat else 153%nat.
(* its listing slot: row r is slot A_prog_slot AS_parse_value + (r - 2) *)
Definition vrd_kw_slot (b : Z) : nat := (A_prog_slot AS_parse_value + (vrd_kw_row b - 2))%nat.
(* the address that slot builds: PAddHi's own `pa_val a + off` (YP0b.v:54-55) *)
Definition vrd_kw_addr (b : Z) : Z :=
  match nth_error A_prog_listing (vrd_kw_slot b) with
  | Some (PAddHi _ _ _ a off) => A_prog_val a + off
  | _ => 0
  end.

(* the three slots really are PAddHi, and the arm's own row really is the auipc that precedes each: read from
   the listing, so this checks the listing, not a pin *)
Remark vrd_kw_slots_are_addhi :
  (exists rd rs j a off, nth_error A_prog_listing (vrd_kw_slot 116) = Some (PAddHi rd rs j a off)) /\
  (exists rd rs j a off, nth_error A_prog_listing (vrd_kw_slot 102) = Some (PAddHi rd rs j a off)) /\
  (exists rd rs j a off, nth_error A_prog_listing (vrd_kw_slot 110) = Some (PAddHi rd rs j a off)).
Proof.
  repeat split; eexists; eexists; eexists; eexists; eexists; vm_compute; reflexivity.
Qed.

(* the three keyword addresses are distinct and lie in one read-only atom's object, 32 bytes apart (the
   asan_globals redzone stride): read from the listing *)
Remark vrd_kw_distinct :
  vrd_kw_addr 102 = vrd_kw_addr 116 + 32 /\ vrd_kw_addr 110 = vrd_kw_addr 116 + 64.
Proof. split; vm_compute; reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------- *)
(* 2. THE EXIT. RQ is VnumC's own vrd_pv_post (lib/A/VrdNum.v:402-425): tparse_value_specX's post at the    *)
(*    join, with rv for s5 and the frames clause at the join; WalkAlive's vrd_epi_step consumes exactly it.   *)
(* ---------------------------------------------------------------------------------------------------- *)

(* a word the memory holds, read back (YCem.v:101 rdword_of_val_mem, copied: YCem's dependency YCeh.v does not build
   on this base, so it cannot be Required here) *)
Lemma vrd_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
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

(* eight present bytes read back as a word *)
Lemma vrd_rdword_present : forall segs H mem a,
  (forall k, 0 <= k < 8 -> apresent H mem (a + k)) ->
  exists w, rdword (aview segs H mem) a = Some w.
Proof.
intros segs H mem a Hp.
assert (B : forall k, 0 <= k < 8 -> exists b, aview segs H mem (a + k) = Some b).
{ intros k Hk. destruct (Hp k Hk) as [Hh [b Hb]]. exists (bv_unsigned b).
  unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
unfold rdword.
destruct (B 0 ltac:(lia)) as [b0 E0]. rewrite Z.add_0_r in E0. rewrite E0.
destruct (B 1 ltac:(lia)) as [b1 E1]. rewrite E1.
destruct (B 2 ltac:(lia)) as [b2 E2]. rewrite E2.
destruct (B 3 ltac:(lia)) as [b3 E3]. rewrite E3.
destruct (B 4 ltac:(lia)) as [b4 E4]. rewrite E4.
destruct (B 5 ltac:(lia)) as [b5 E5]. rewrite E5.
destruct (B 6 ltac:(lia)) as [b6 E6]. rewrite E6.
destruct (B 7 ltac:(lia)) as [b7 E7]. rewrite E7.
eexists. reflexivity.
Qed.

(* ---- NAMED PROJECTIONS of the kit predicates this walk reads: PRH_FnParse.v prhPv_node and rd_blocks_move,
   PRH_Reader.v pj_in_okR, PRH_Base.v src_rd (the ledger has its own, PRH_Base.v ledger_proj). No proof below
   destructures one of them by position: each projection states ONE conjunct and finds it by its type (tauto), so a
   kit change that reorders or widens a predicate fails HERE, loudly, never by a silent rebinding of a name. ---- *)
Section kproj_node.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Context {B : asyms} {STK e : Z} {ly : alayout} {S : astate} {W : world SEGS} {regs : bvmap 5 word}
  {mem : word -> option byte} {Lam : list (Z * Z)} {v : Z}.
Hypothesis HN : prhPv_node B STK e ly S W regs mem Lam v.
Lemma vnd_v4096 : 4096 <= v.
Proof. clear - HN. unfold prhPv_node in HN. tauto. Qed.
Lemma vnd_al8 : v mod 8 = 0.
Proof. clear - HN. unfold prhPv_node in HN. tauto. Qed.
Lemma vnd_rw : pj_rwR SEGS (mrestrict (w_H W) mem) v.
Proof. clear - HN. unfold prhPv_node in HN. tauto. Qed.
Lemma vnd_zero : pj_zeroR SEGS (mrestrict (w_H W) mem) v.
Proof. clear - HN. unfold prhPv_node in HN. tauto. Qed.
Lemma vnd_at : prhReader_at B ly S Lam regs e v 56.
Proof. clear - HN. unfold prhPv_node in HN. tauto. Qed.
Lemma vnd_amr : amem_range v 56.
Proof. clear - HN. unfold prhPv_node in HN. tauto. Qed.
Lemma vnd_own : forall a, v <= a < v + 56 -> ~ aowned B ly S a /\ ~ (spZ regs - STK <= a < spZ regs).
Proof. clear - HN. unfold prhPv_node in HN. tauto. Qed.
Lemma vnd_ra : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56.
Proof. clear - HN. unfold prhPv_node in HN. tauto. Qed.
End kproj_node.

Section kproj_in.
Context {segs : list Segment} {m : word -> option byte} {q text len p d : Z} {tb : list Z}.
Hypothesis HI : pj_in_okR segs m q text len p d tb.
Lemma vin_p : val_mem segs m q 8 p.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_end : val_mem segs m (q + 8) 8 (text + len).
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_d : val_mem segs m (q + 16) 4 d.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_rw : rd_rw segs m q 24.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_q8 : q mod 8 = 0.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_t : 0 < text.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_tl : text + len < 2 ^ 62.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_pp : text <= p <= text + len.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_len : Z.of_nat (length tb) = len.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_g : garr8 segs m text tb.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_qt : q + 24 <= text \/ text + len <= q.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
Lemma vin_d32 : 0 <= d <= 32.
Proof. clear - HI. unfold pj_in_okR in HI. tauto. Qed.
End kproj_in.

Section kproj_src.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Context {W : world SEGS} {mem : word -> option byte} {p : Z} {l : list Z}.
Hypothesis HS : src_rd W mem p l.
Lemma vsr_4096 : 4096 <= p.
Proof. clear - HS. unfold src_rd in HS. tauto. Qed.
Lemma vsr_ceil : p + Z.of_nat (length l) <= YM05.alloc_ceiling.
Proof. clear - HS. unfold src_rd in HS. tauto. Qed.
End kproj_src.

Section kproj_bm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
Context {B : asyms} {ly : alayout} {S : astate} {ly' : alayout} {S' : astate} {D : list (Z * Z)}
  {tr : list ev} {rest : list Z} {d : nat}.
Hypothesis HM : rd_blocks_move B ly S ly' S' D tr rest d.
Lemma vbm_new : forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S).
Proof. clear - HM. unfold rd_blocks_move in HM. tauto. Qed.
Lemma vbm_blocks : Permutation (ablocks B ly' S') (prhReader_ab D ++ ablocks B ly S).
Proof. clear - HM. unfold rd_blocks_move in HM. tauto. Qed.
Lemma vbm_frames : Permutation (frames S') (frames S).
Proof. clear - HM. unfold rd_blocks_move in HM. tauto. Qed.
Lemma vbm_peak : hpeakR tr <= 224 * Z.of_nat (length rest) + 512 * Z.of_nat (PjGrammar.MAXD - d).
Proof. clear - HM. unfold rd_blocks_move in HM. tauto. Qed.
End kproj_bm.

Section kproj_room.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
Lemma vrr_live : forall S gt, rd_room S gt -> room_live_cf S.
Proof. intros S gt H. unfold rd_room in H. tauto. Qed.
End kproj_room.

(* prh_cur_entry's cursor-word half (PRH_Base.v; its first conjunct is the Forall over chains), BY NAME *)
Section kproj_cur.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Lemma vce_low : forall (W : world SEGS) mem regs q, prh_cur_entry W mem regs q ->
  forall F, prh_cursor F -> forall w, prh_word_entry W mem regs (prh_s0 F q - 16) w -> w < YM05.alloc_ceiling.
Proof. intros W mem regs q H F HF. exact (proj2 H F HF). Qed.
End kproj_cur.

(* ---- NAMED PROJECTIONS / SHAPE GUARDS for the engine and dispatch predicates this walk reads by pattern: each states
   the predicate's conjuncts EXPLICITLY (copied from its definition at the cut: YG0f.v layout_le, YCbq.v astk_ok,
   PRH_Base.v fwin, VrdPro.v vrd_regs / vrd_saved / vrd_frame) or finds one by its type (tauto). A change of any of
   these definitions makes the guard fail HERE, loudly; no intro pattern below can rebind a name silently. ---- *)
Section kproj_eng.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Lemma vly_top {n : nat} {ly ly' : alayout} : layout_le n ly ly' -> ly_top ly' = ly_top ly.
Proof. unfold layout_le. tauto. Qed.
Lemma vly_F {n : nat} {ly ly' : alayout} : layout_le n ly ly' -> ly_F ly' = ly_F ly.
Proof. unfold layout_le. tauto. Qed.
Lemma vly_stk_hi {n : nat} {ly ly' : alayout} : layout_le n ly ly' -> ly_stk_hi ly' = ly_stk_hi ly.
Proof. unfold layout_le. tauto. Qed.
Lemma vastk {STK : Z} {ly : alayout} {sp0 : Z} : astk_ok STK ly sp0 ->
  sp0 mod 16 = 0 /\ 0 <= STK /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= sp0 /\ sp0 <= ly_stk_hi ly /\
  ly_stk_hi ly <= 2 ^ 47 /\ ly_bot ly + STK + ACALL_PREFIX < sp0 + ASTACK /\ sp0 <= ly_top ly /\ ly_top ly <= ly_stk_hi ly.
Proof. intros H. exact H. Qed.
Lemma vfw {ly : alayout} {W : world SEGS} {regs : bvmap 5 word} {mem : word -> option byte} {d : Z} :
  fwin ly W regs mem d ->
  0 <= d /\ d mod 16 = 0 /\ spZ regs + d <= ly_top ly /\
  (forall a, spZ regs <= a < spZ regs + d -> apresent (w_H W) mem a).
Proof. intros H. exact H. Qed.
Lemma vregs {regs0 regs : bvmap 5 word} {ly : alayout} {pos q v p' text len : Z} :
  vrd_regs regs0 regs ly pos q v p' text len ->
  getr regs 2 = w64 (spZ regs0 - 160 - (spZ regs0 - 160) mod 32) /\
  getr regs 9 = getr regs 2 /\
  getr regs 8 = w64 (spZ regs0) /\
  getr regs 18 = w64 (frame_addr ly 0 pos) /\
  getr regs 26 = w64 (frame_addr ly 0 pos) /\
  getr regs 19 = w64 v /\ getr regs 20 = w64 q /\
  getr regs 21 = getr regs0 21 /\ getr regs 22 = getr regs0 22 /\ getr regs 25 = getr regs0 25 /\
  getr regs 23 = w64 SHADOW_OFF /\
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) /\
  getr regs 27 = w64 (SHADOW_OFF + q / 8) /\
  getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  getr regs 10 = w64 p' /\ getr regs 12 = w64 (text + len).
Proof. intros H. exact H. Qed.
Lemma vsav12 {m : word -> option byte} {sp0 : Z} {regs0 : bvmap 5 word} : vrd_saved m sp0 regs0 ->
  val_mem SEGS m (sp0 - 8) 8 (raZ regs0) /\ val_mem SEGS m (sp0 - 16) 8 (bv_unsigned (getr regs0 8)).
Proof. intros H. unfold vrd_saved in H. tauto. Qed.
Lemma vfrm3 {W : world SEGS} {m : word -> option byte} {ly : alayout} {pos : Z} : vrd_frame W m ly pos ->
  val_mem SEGS (mrestrict (w_H W) m) (frame_addr ly 0 pos) 8 0x41B58AB3 /\
  val_mem SEGS (mrestrict (w_H W) m) (frame_addr ly 0 pos + 16) 8 (@pa_sigma _ A_prog_listing PI_prog_A AS_parse_value) /\
  val_mem SEGS (mrestrict (w_H W) m) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos).
Proof. intros H. unfold vrd_frame in H. cbv zeta in H. tauto. Qed.
End kproj_eng.

Section t.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the engine laws, in the fold's HL form (the walk's runners and VrdArm's call rules take them) *)
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.

(* ---- the window shift: what the dispatch states at parse_value's ENTRY sp, the callee's text asks at the
   CALL's sp. Both arms call at the dispatch's own sp (VrdPro.v:162, sp = spZ regs0 - 160 - (spZ regs0 - 160)
   mod 32), so the caller window widens by exactly the drop and the two windows have the same TOP. The lower
   part of the widened window is parse_value's own frame, which the journal keeps present; that is the one
   premise these lemmas take. ---- *)

Lemma vrd_fwin_shift : forall ly (W : world segs) regs0 regs mem e delta,
  fwin ly W regs0 mem e ->
  spZ regs = spZ regs0 - delta -> 0 <= delta -> delta mod 16 = 0 ->
  (forall a, spZ regs0 - delta <= a < spZ regs0 -> apresent (w_H W) mem a) ->
  fwin ly W regs mem (e + delta).
Proof.
  intros ly W regs0 regs mem e delta (He0 & He16 & Htop & Hpres) Hsp Hd0 Hd16 Hlow.
  split; [lia|]. split.
  - rewrite Zplus_mod, He16, Hd16. reflexivity.
  - split; [rewrite Hsp; replace (spZ regs0 - delta + (e + delta)) with (spZ regs0 + e) by lia; exact Htop|].
    intros a Ha. rewrite Hsp in Ha.
    destruct (Z_lt_le_dec a (spZ regs0)) as [Hlt|Hge].
    + apply Hlow. lia.
    + apply Hpres. lia.
Qed.

Lemma vrd_reader_at_shift : forall ly S Lam regs0 regs e delta p n,
  prhReader_at B ly S Lam regs0 e p n ->
  spZ regs = spZ regs0 - delta -> 0 <= delta ->
  prhReader_at B ly S Lam regs (e + delta) p n.
Proof.
  intros ly S Lam regs0 regs e delta p n H Hsp Hd0.
  destruct H as [H | [H | [H | (H1 & H2)]]];
  [left; exact H | right; left; exact H | right; right; left; exact H |].
  right; right; right. rewrite Hsp. split; lia.
Qed.

(* the literal's callee asks for the node's FIRST FOUR bytes where parse_value's text gives all 56: every
   placement of prhReader_at is a range that contains the shorter one *)
Lemma vrd_reader_at_narrow : forall ly S Lam regs e p n m,
  prhReader_at B ly S Lam regs e p n -> 0 <= m <= n ->
  prhReader_at B ly S Lam regs e p m.
Proof.
  intros ly S Lam regs e p n m H Hm.
  destruct H as [(a0 & k0 & H1 & H2 & H3) | [(b0 & m0 & H1 & H1b & H2 & H3) |
                 [(cid & pos & H1 & H2 & H3) | (H1 & H2)]]].
  - left. exists a0, k0. split; [exact H1|]. split; lia.
  - right; left. exists b0, m0. split; [exact H1|]. split; [exact H1b|]. split; lia.
  - right; right; left. exists cid, pos. split; [exact H1|]. split; lia.
  - right; right; right. split; lia.
Qed.

(* the same narrowing for the shadow check *)
Lemma vrd_range_narrow : forall m off a n k,
  range_addressable m off a n -> 0 <= k <= n -> range_addressable m off a k.
Proof. intros m off a n k H Hk x Hx. apply H. lia. Qed.

(* the cursor and the node keep their window bounds under the same shift *)
Lemma vrd_in_window_shift : forall regs0 regs e delta a n,
  spZ regs0 <= a -> a + n <= spZ regs0 + e ->
  spZ regs = spZ regs0 - delta -> 0 <= delta ->
  spZ regs <= a /\ a + n <= spZ regs + (e + delta).
Proof. intros regs0 regs e delta a n H1 H2 Hsp Hd. rewrite Hsp. split; lia. Qed.

(* the node clause of rd_pre at the CALL: prhPv_node at parse_value's (STK, e, regs0) gives it at the callee's
   (STK1, e + delta, regs) whenever the callee's frame budget lies inside parse_value's (STK1 + delta <= STK) *)
Lemma vrd_node_shift : forall STK STK1 e delta ly S (W : world segs) regs0 regs mem Lam v,
  prhPv_node B STK e ly S W regs0 mem Lam v ->
  spZ regs = spZ regs0 - delta -> 0 <= delta -> STK1 + delta <= STK ->
  prhPv_node B STK1 (e + delta) ly S W regs mem Lam v.
Proof.
  intros STK STK1 e delta ly S W regs0 regs mem Lam v
    (H4096 & Hal & Hrw & Hz & Hat & Hamr & Hown & Hra) Hsp Hd Hb.
  split; [exact H4096|]. split; [exact Hal|]. split; [exact Hrw|]. split; [exact Hz|].
  split; [exact (vrd_reader_at_shift ly S Lam regs0 regs e delta v 56 Hat Hsp Hd)|].
  split; [exact Hamr|]. split; [|exact Hra].
  intros a Ha. destruct (Hown a Ha) as [Ho Hs]. split; [exact Ho|]. rewrite Hsp. lia.
Qed.

(* the conclusion both arms reach: VnumC's epilogue state at row 225, with the arm's own result in RQ. The entry
   float state is PINNED to the Section's fx (WalkAlive's trap: with fx2 bound, an unpinned implicit can elaborate
   at fx2 and make fregs_kept_x trivial) *)
Definition vrd_arm_exit (d : nat) (CW : list (list Z)) (e q v text len p : Z) (tb : list Z)
  (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : world segs -> config -> Prop :=
  fun W' c' => exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
      (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran
         most own pos rv) W' c'.

(* vrd_arm_exit over a world relation R: a COPY of its body with the join VrdNum.vrd_epi_aR R. The container arm
   reaches it at the re-hiding relation wle' segs RZ_cf (parse_items' text); vrd_arm_exit is the instance at wle
   (vrd_arm_exit_R_wle, by reflexivity), and vrd_arm_exit_wle' lifts a literal arm's exit to the container's
   relation *)
Definition vrd_arm_exitR (R : world segs -> world segs -> Prop) (d : nat) (CW : list (list Z)) (e q v text len p : Z)
  (tb : list Z) (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : world segs -> config -> Prop :=
  fun W' c' => exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_aR (fx := fx) B ARx SK R fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
      (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran
         most own pos rv) W' c'.
Lemma vrd_arm_exit_R_wle : forall d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt fail ran most own,
  vrd_arm_exit d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt fail ran most own =
  vrd_arm_exitR (@wle segs) d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt fail ran most own.
Proof. reflexivity. Qed.
Lemma vrd_arm_exit_wle' : forall d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt fail ran most own
    W' c',
  vrd_arm_exit d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt fail ran most own W' c' ->
  vrd_arm_exitR (wle' segs YGcfRehidePost.RZ_cf) d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt
    fail ran most own W' c'.
Proof.
intros d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt fail ran most own W' c' (fx2 & pos & rv & HE).
unfold vrd_arm_exitR. exists fx2, pos, rv. exact (vrd_epi_a_wle' B ARx SK HE).
Qed.

(* the dispatch state's outer shape, stated explicitly (VrdPro.v vrd_disp_a at the cut interface): a change of it makes
   this guard fail, not an intro pattern bind a wrong name *)
Lemma vdispa {ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own W c} :
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own W c ->
  exists (arm : vrd_arm) (pos p' k : Z) (ly : alayout) (S : astate) (Hp : list Z) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model),
  c = cfg_at segs (@pa_sigma _ A_prog_listing PI_prog_A AS_parse_value + vrd_arm_off arm) regs mem md /\
  vrd_disp_body B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    arm pos p' k ly S Hp W regs mem md.
Proof. intros H. exact H. Qed.

(* ---------------------------------------------------------------------------------------------------- *)
(* 3. THE TWO ARM STATEMENTS, generic in a memory invariant P, and their instances.                       *)
(* ---------------------------------------------------------------------------------------------------- *)

(* THE CONTAINER ARM, rows 131..134 (object) / 213..215 (array), the shared row 216 `jal parse_items` with its
   return site row 217, and row 217 `j` to ROW 224. The call context is the return site of row 216, which is
   row 217's address: slot A_prog_slot AS_parse_value + 215. P: srr_inv_call carries it across the call (the callee's
   m-form post keeps memnorm) and srr_inv_mn gives the callee's memnorm entry premise; P of the dispatch memory last,
   P of the reached memory in the continuation. *)
Definition vrd_cont_aLC_P (P : (word -> option byte) -> Prop) (d : nat) (CTX CTX0 : list (list Z)) (CW : list (list Z))
  : Prop :=
  srr_inv_call segs P -> srr_inv_mn segs P ->
  forall (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
         (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
         (e q v text len p : Z) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
         (W : world segs) (c : config) (o : bool) (b : Z) (yy : list Z),
  tparse_items_specX B ARx SK d CTX CTX0 CW ->
  (* the entry pre, tparse_value_specX's first premise, passed through. It was once MISSING here:
     its last conjuncts, the entry ra's ceiling bound and frm_zero (PRH_Base.v fpre, the cut's :988), are what
     vrd_cur_entry_call asks, and vrd_disp_a does not give it (a state meeting vrd_disp_a with
     raZ regs0 = alloc_ceiling meets every one of its conjuncts) *)
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own W c ->
  (* THE HULL BUDGET, tparse_value_specX's premise at parse_value's entry state S0, passed through: the arm pays
     parse_items' budget from it *)
  PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
  PjGrammar.skip (rest_atR tb text p) = b :: yy -> b = (if o then 123 else 91) ->
  In (A_prog_base + 4 * Z.of_nat (A_prog_slot AS_parse_value + 215) :: raZ regs0 :: spine ch) CTX ->
  (* IMAGE FACT (witness: lib/A/VrdArmLCWit.v vrd_img_stk_items_drop, at prh_img_A, every d) *)
  STK_parse_items d + 176 <= STK_parse_value d ->
  (* IMAGE FACT, the callee's frame budget is not negative, which vrd_call_WF's `0 <= STK1` asks (witness:
     VrdArmLCWit.vrd_img_stk_items_nonneg; every PrhImg gives it by pi_frame_nonneg, VrdArmLCWit.vrd_img_nonneg_any) *)
  0 <= STK_parse_items d ->
  (* IMAGE FACTS: both cursor functions keep s0 = q, which VproC's vrd_cur_entry_call asks (witnesses:
     VrdArmLCWit.vrd_img_s0cur_parse_string / vrd_img_s0cur_parse_items) *)
  pi_s0cur F_parse_string = Some 0 -> pi_s0cur F_parse_items = Some 0 ->
  P (ms_mem (cfg_ms c)) ->
  (* parse_items' text concludes SRr' segs RZ_cf with its journal at wle' segs RZ_cf: so does the arm *)
  SRr' segs YGcfRehidePost.RZ_cf W c (fun W' c' =>
    vrd_arm_exitR (wle' segs YGcfRehidePost.RZ_cf) d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt
      fail ran most own W' c' /\ P (ms_mem (cfg_ms c'))).

(* the container's instance P := memnorm (P := True is NOT an instance: srr_inv_mn at True is false, and
   parse_items' text asks memnorm at entry): memnorm of the dispatch memory, kept to row 225 *)
Definition vrd_cont_aLC (d : nat) (CTX CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
         (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
         (e q v text len p : Z) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
         (W : world segs) (c : config) (o : bool) (b : Z) (yy : list Z),
  tparse_items_specX B ARx SK d CTX CTX0 CW ->
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own W c ->
  PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
  PjGrammar.skip (rest_atR tb text p) = b :: yy -> b = (if o then 123 else 91) ->
  In (A_prog_base + 4 * Z.of_nat (A_prog_slot AS_parse_value + 215) :: raZ regs0 :: spine ch) CTX ->
  STK_parse_items d + 176 <= STK_parse_value d ->
  0 <= STK_parse_items d ->
  pi_s0cur F_parse_string = Some 0 -> pi_s0cur F_parse_items = Some 0 ->
  YAkMemnorm.memnorm segs (ms_mem (cfg_ms c)) ->
  SRr' segs YGcfRehidePost.RZ_cf W c (fun W' c' =>
    vrd_arm_exitR (wle' segs YGcfRehidePost.RZ_cf) d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt
      fail ran most own W' c' /\ YAkMemnorm.memnorm segs (ms_mem (cfg_ms c'))).

(* THE LITERAL ARM, rows 119..122 ("false") / 152..156 ("null") / 218..220 ("true"), the shared rows 221..223
   `jal literal`, falling through to ROW 224. The keyword's address is vrd_kw_addr b, read from the listing;
   its bytes are the kit's own garr8 read premise, stated here at parse_value's ENTRY state, which the arm's rows
   (register moves and one auipc / addi pair; no store) carry to the call unchanged. P: srr_inv_call carries it
   across the call (literal takes no memnorm at entry); P of the dispatch memory last, P of the reached memory in
   the continuation. *)
Definition vrd_lit_aLC_P (P : (word -> option byte) -> Prop) (d : nat) (CTX0 : list (list Z)) (CW : list (list Z))
  : Prop :=
  srr_inv_call segs P ->
  forall (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
         (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
         (e q v text len p : Z) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
         (W : world segs) (c : config) (b ty : Z) (yy cw slack : list Z),
  tliteral_specX B ARx SK ->
  (* the entry pre, tparse_value_specX's first premise, passed through. It was once MISSING here:
     its last conjuncts, the entry ra's ceiling bound and frm_zero (PRH_Base.v fpre, the cut's :988), are what
     vrd_cur_entry_call asks, and vrd_disp_a does not give it (a state meeting vrd_disp_a with
     raZ regs0 = alloc_ceiling meets every one of its conjuncts) *)
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own W c ->
  PjGrammar.skip (rest_atR tb text p) = b :: yy ->
  (b = 116 /\ cw = PjGrammar.w_true /\ ty = 2 \/ b = 102 /\ cw = PjGrammar.w_false /\ ty = 1 \/
   b = 110 /\ cw = PjGrammar.w_null /\ ty = 0) ->
  (* the keyword's bytes and its NUL, AT THE DISPATCH STATE the arm starts from (the arm's rows move registers
     only, so the call reads the same memory). The caller supplies this from its own arodata_okP: the keyword is
     read-only image data, so its view is the image's ROM byte at every state of the run. Stating it at the entry
     state instead would need the three image facts the journal's image clause asks (in_img, not runtime-owned,
     not errno) for every byte of cw ++ 0 :: slack, which is image work this arm does not need. *)
  (forall regs mem md,
     c = cfg_at segs (@pa_sigma _ A_prog_listing PI_prog_A AS_parse_value + vrd_arm_off (vrd_arm_of b)) regs mem md ->
     cstr_ok W mem (vrd_kw_addr b) cw /\
     garr8 segs (mrestrict (w_H W) mem) (vrd_kw_addr b) (cw ++ 0 :: slack)) ->
  vrd_kw_addr b + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= 2 ^ 63 ->
  ~ In 0 cw ->
  (- (vrd_kw_addr b + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack) ->
  vrd_kw_addr b + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= spZ regs0 - STK_parse_value d ->
  (* IMAGE FACT (witness: VrdArmLCWit.vrd_img_stk_literal_drop, at prh_img_A, every d) *)
  STK_literal + 176 <= STK_parse_value d ->
  (* IMAGE FACT, vrd_call_W's `0 <= STK1` (witness: VrdArmLCWit.vrd_img_stk_literal_nonneg) *)
  0 <= STK_literal ->
  P (ms_mem (cfg_ms c)) ->
  SRr segs W c (fun W' c' =>
    vrd_arm_exit d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt fail ran
      most own W' c' /\ P (ms_mem (cfg_ms c'))).

(* the literal's instance P := True: the statement of before, word for word *)
Definition vrd_lit_aLC (d : nat) (CTX0 : list (list Z)) (CW : list (list Z)) : Prop :=
  forall (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
         (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z))
         (e q v text len p : Z) (tb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
         (W : world segs) (c : config) (b ty : Z) (yy cw slack : list Z),
  tliteral_specX B ARx SK ->
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own W c ->
  PjGrammar.skip (rest_atR tb text p) = b :: yy ->
  (b = 116 /\ cw = PjGrammar.w_true /\ ty = 2 \/ b = 102 /\ cw = PjGrammar.w_false /\ ty = 1 \/
   b = 110 /\ cw = PjGrammar.w_null /\ ty = 0) ->
  (forall regs mem md,
     c = cfg_at segs (@pa_sigma _ A_prog_listing PI_prog_A AS_parse_value + vrd_arm_off (vrd_arm_of b)) regs mem md ->
     cstr_ok W mem (vrd_kw_addr b) cw /\
     garr8 segs (mrestrict (w_H W) mem) (vrd_kw_addr b) (cw ++ 0 :: slack)) ->
  vrd_kw_addr b + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= 2 ^ 63 ->
  ~ In 0 cw ->
  (- (vrd_kw_addr b + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack) ->
  vrd_kw_addr b + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= spZ regs0 - STK_parse_value d ->
  STK_literal + 176 <= STK_parse_value d ->
  0 <= STK_literal ->
  SRr segs W c (vrd_arm_exit d CW e q v text len p tb ly0 S0 Hp0 W0 regs0 mem0 md0 Lam peak cnt fail ran
                most own).

End t.

(* ---------------------------------------------------------------------------------------------------- *)
(* 4. THE ARMS' SYMBOLIC ENTRY. Both arms' rows before the call move registers only (no load, no store, no   *)
(*    shadow check), so the symbolic state at an arm's first row needs no region and no fact.               *)
(* ---------------------------------------------------------------------------------------------------- *)

Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

Definition va_facts : facts := mkFacts [] [] [].
(* the symbolic state at listing offset off: the registers as atoms, no region, no fact *)
Definition va_ss (off : Z) : sstate := mkSS off sr_atoms [] None va_facts.
Definition va_env (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PI_prog_A (Ereg regs []).

Lemma va_entry : forall (W : world SEGS) regs mem off,
  st_ok_pi SEGS VAL (va_env regs) (va_ss off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + off)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem off. rewrite restrict_mkst_fx. unfold va_ss, va_env.
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - unfold va_facts. repeat (split || exact I || constructor).
Qed.

End w.

(* ---------------------------------------------------------------------------------------------------- *)
(* 5. THE CONTAINER ARM, PROVED (both cases: object entry row 131, array entry row 213). The walk: the run of  *)
(*    the arm's rows to `jal parse_items` (row 216); VstrC's vrd_call_WF; the parse_items text with its 18      *)
(*    premises; the chain at the call view by VproC's vrd_disp_chain / vrd_cur_entry_call / vrd_cur_chain_call; *)
(*    the post-call run of rows 217 / 224 to row 225; and vrd_epi_a there with RQ = VnumC's vrd_pv_post.        *)
(* ---------------------------------------------------------------------------------------------------- *)

(* ---- the two return pcs are below the ceiling (the callee fpre's last conjunct at each call, the cut's
   PRH_Base.v fpre :988): CLOSED slot lemmas, PRW_StepKit.pa_slot_lt_ceil_b at the listing ---- *)
Section rpc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma vrd_ret217_lt_ceil : A_prog_base + 19596 < YM05.alloc_ceiling.
Proof.
  change A_prog_base with (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
  exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PI_prog_A) 19596 ltac:(lia)
           ltac:(vm_compute; reflexivity)).
Qed.
Lemma vrd_ret224_lt_ceil : A_prog_base + 19624 < YM05.alloc_ceiling.
Proof.
  change A_prog_base with (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
  exact (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PI_prog_A) 19624 ltac:(lia)
           ltac:(vm_compute; reflexivity)).
Qed.
End rpc.

(* ---- the ALL-GRANTED traces the kit text keys its counts and its outcome on (PRH_Charge.v prhPv_gtrace /
   prhPi_gtrace, both at ok = []). At a container the value's is parse_items' at the opener (VrdArm.vrd_cont_model),
   so tparse_value_specX's entry counts, which vrd_disp_body carries at S0, ARE parse_items' count premises, and
   parse_items' outcome clause IS the value's. At a keyword the value makes no allocation event at all. ---- *)
Lemma vrd_gtrace_cont : forall d b y x (o : bool),
  PjGrammar.skip x = b :: y -> b = (if o then 123 else 91) ->
  prhPv_gtrace d x = prhPi_gtrace d o (b :: y).
Proof.
  intros d b y x o Hs Hb. unfold prhPv_gtrace, prhPi_gtrace.
  rewrite (vrd_cont_model prh_jr_strtod d b y x [] o Hs Hb). reflexivity.
Qed.

Lemma vrd_gtrace_lit : forall d b y x, PjGrammar.skip x = b :: y -> (b = 116 \/ b = 102 \/ b = 110) ->
  prhPv_gtrace d x = [].
Proof.
  intros d b y x Hs Hb. unfold prhPv_gtrace.
  rewrite (vrd_lit_model prh_jr_strtod d b y x [] Hs Hb).
  unfold PjGrammar.lit, PjGrammar.jret, PjGrammar.jrefuse.
  lazymatch goal with |- context [PjGrammar.prefixb ?w ?z] => destruct (PjGrammar.prefixb w z) end; reflexivity.
Qed.

(* ---- the FREE ORDER the cut's texts post (PRH_FnParse.v prhPv_frees / prhPi_frees, PresetReqAt.jfv / jf_cont): at a
   container the value's list is parse_items' at the opener (one step of jfv, then the fuel shift of jfl by
   PresetFreeFo.jf_fuel_mono: both fuels exceed what the members after the opener need); at a keyword it is [] (a
   keyword's trace has no block, PresetFreeFo.jfv_leaf). ---- *)
Lemma vrd_frees_lit : forall d b y x ok, PjGrammar.skip x = b :: y -> (b = 116 \/ b = 102 \/ b = 110) ->
  prhPv_frees d x ok = [].
Proof.
  intros d b y x ok Hs Hb.
  assert (Hc : (b =? 123) = false /\ (b =? 91) = false) by (destruct Hb as [-> | [-> | ->]]; split; reflexivity).
  (* a keyword is a leaf (PresetFreeFo.jfv_leaf), by conversion from prhPv_frees and jr_value *)
  transitivity (PresetReqAt.lf (snd (fst (PjGrammar.jr_value ReaderRes.jr_strtod d x ok)))).
  { exact (PresetFreeFo.jfv_leaf ReaderRes.jr_strtod (2 * length x) d x ok ltac:(rewrite Hs; exact Hc)). }
  rewrite (vrd_lit_model ReaderRes.jr_strtod d b y x ok Hs Hb).
  unfold PjGrammar.lit, PjGrammar.jret, PjGrammar.jrefuse.
  lazymatch goal with |- context [PjGrammar.prefixb ?w ?z] => destruct (PjGrammar.prefixb w z) end; reflexivity.
Qed.

Section p.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

Theorem vrd_cont_aLC_P_holds : forall P d CTX CTX0 CW, vrd_cont_aLC_P B ARx SK P d CTX CTX0 CW.
Proof.
  intros P d CTX CTX0 CW. unfold vrd_cont_aLC_P. intros PC PM.
  intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran most own W c o b yy
    HPI HFP HD HHB Hsk Hb HCTX HSTK HSTKi Hs0str Hs0items HP0.
  destruct (vdispa B ARx SK HD) as (arm & pos & p' & k & ly & S & Hp & regs & mem & md & Hc & HB).
  (* vrd_disp_body's conjuncts BY SHAPE, never by position (VrdPro.v grew twice: fe6f39ebc742 replaced one conjunct by four, the
     cut interface (f5eb8e2e6bbf, green at e942c5680fa7) appended three;
     a positional pattern over a body that grew binds its names to the wrong conjuncts and swallows the new ones):
     decompose [and], then each conjunct this walk reads is named by its type. The two string-arm counts stay
     unnamed: neither arm reads them. *)
  unfold vrd_disp_body in HB. decompose [and] HB. clear HB.
  lazymatch goal with X : rest_atR tb text p' = PjGrammar.skip (rest_atR tb text p) |- _ => rename X into Hrest end.
  lazymatch goal with X : p <= p' |- _ => rename X into Hpp1 end.
  lazymatch goal with X : p' <= text + len |- _ => rename X into Hpp2 end.
  assert (Hpp : p <= p' <= text + len) by (split; assumption).
  lazymatch goal with X : match PjGrammar.skip (rest_atR tb text p) with _ => _ end |- _ => rename X into Hmatch end.
  lazymatch goal with X : context [ajournal_x] |- _ => rename X into HJ end.
  lazymatch goal with X : frames S = _ |- _ => rename X into Hfr end.
  lazymatch goal with X : ablocks B ly S = ablocks B ly0 S0 |- _ => rename X into Hab end.
  lazymatch goal with X : Hp = Hp0 |- _ => rename X into HHp end.
  lazymatch goal with X : exists _, S = set_fs _ S0 |- _ => rename X into Hsetfs end.
  lazymatch goal with X : forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a -> _ |- _ =>
    rename X into Hwin end.
  lazymatch goal with X : context [fwin] |- _ => rename X into Hfw end.
  lazymatch goal with X : context [vrd_frame] |- _ => rename X into Hframe end.
  lazymatch goal with X : context [vrd_saved] |- _ => rename X into Hsaved end.
  lazymatch goal with X : context [vrd_regs] |- _ => rename X into Hregs end.
  lazymatch goal with X : exists _, achain ly0 _ (spZ regs0) (s0Z regs0) _ /\ _ |- _ => rename X into Hchain0 end.
  lazymatch goal with X : context [prh_univ_closure] |- _ => rename X into Hclos end.
  lazymatch goal with X : context [prh_cur_entry] |- _ => rename X into Hcur end.
  lazymatch goal with X : (spZ regs0 <= q < spZ regs0 + 16) \/ _ |- _ => rename X into Hcurch end.
  lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W) mem) q text len p' _ tb |- _ => rename X into Hin end.
  lazymatch goal with X : range_addressable (aview _ (w_H W) mem) SHADOW_OFF q 24 |- _ => rename X into Hraq end.
  lazymatch goal with X : context [prhPv_node] |- _ => rename X into Hnode end.
  lazymatch goal with X : context [prh_malloc_univ] |- _ => rename X into Hmu end.
  lazymatch goal with X : spZ regs0 <= q |- _ => rename X into Hq1 end.
  lazymatch goal with X : q + 24 <= spZ regs0 + e |- _ => rename X into Hq2 end.
  lazymatch goal with X : q + 24 <= v \/ v + 56 <= q |- _ => rename X into Hqv end.
  lazymatch goal with X : getr regs0 _ = w64 (as_gp _) |- _ => rename X into Hgp0 end.
  lazymatch goal with X : getr regs0 _ = w64 (as_tp _) |- _ => rename X into Htp0 end.
  lazymatch goal with X : YK0s.ret_ok _ |- _ => rename X into Hra0 end.
  lazymatch goal with X : 4096 <= raZ regs0 |- _ => rename X into Hra4k end.
  lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W0) mem0) q text len p _ tb |- _ => rename X into Hin0 end.
  lazymatch goal with X : (d <= PjGrammar.MAXD)%nat |- _ => rename X into HMAXD end.
  lazymatch goal with X : 0 < len -> _ |- _ => rename X into Htv end.
  lazymatch goal with X : v + 56 <= spZ regs0 \/ spZ regs0 + e <= v |- _ => rename X into Hvwin end.
  lazymatch goal with X : In [cf_pc_realloc_ra0] _ |- _ => rename X into Hr1 end.
  lazymatch goal with X : In (prh_trace _ _ _) _ |- _ => rename X into Hr2 end.
  lazymatch goal with X : Z.of_nat (PjRoundTrip.maxrun tb) < _ |- _ => rename X into Hmax end.
  lazymatch goal with X : cnt + 2 * Z.of_nat (length (rest_atR tb text p')) + 2 < _ |- _ => rename X into Hcnt end.
  lazymatch goal with X : context [src_rd] |- _ => rename X into Hsrc end.
  lazymatch goal with X : context [prhReader_home] |- _ => rename X into Hhome end.
  lazymatch goal with X : context [prh_ledger] |- _ => rename X into Hled end.
  lazymatch goal with X : context [rd_room] |- _ => rename X into Hroom end.
  lazymatch goal with X : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req
                              (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) _) <= _ |- _ => rename X into HC0s end.
  lazymatch goal with X : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls _)
                              (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) _) <= _ |- _ => rename X into HC024 end.
  lazymatch goal with X : Z.of_nat (length (frames S)) + _ <= fs_frames 0 |- _ => rename X into Hfrb end.
  lazymatch goal with X : context [PresetRodata.arodata_okP] |- _ => rename X into Hrod end.
  lazymatch goal with X : frm_zero _ |- _ => rename X into Hfrm end.
  (* the three conjuncts the cut's dispatch text appends (VrdPro.v at a Theorem Labs lane's cut interface f5eb8e2e6bbf):
     the free-trace words of the cursor named in CW, the wild room CW leaves at the entry depot, and the text below
     the ceiling. Named by type like the rest. *)
  lazymatch goal with X : context [prh_cw_entry] |- _ => rename X into HCW end.
  lazymatch goal with X : context [YCbqGwild.wild_room] |- _ => rename X into HWR0 end.
  lazymatch goal with X : text + len < YM05.alloc_ceiling |- _ => rename X into HTC end.
  repeat match goal with X : arm = VA_str -> _ |- _ => clear X end.
  (* fpre's last conjunct, the entry ra below the ceiling, BY NAME (tauto on fpre alone) *)
  assert (Hra0c : raZ regs0 < alloc_ceiling) by (clear - HFP; unfold fpre in HFP; tauto).
  rewrite Hsk in Hmatch. cbv beta iota in Hmatch. decompose [and] Hmatch. clear Hmatch.
  lazymatch goal with X : arm = vrd_arm_of _ |- _ => rename X into Harm end.
  lazymatch goal with X : p' < text + len |- _ => rename X into Hplt end.
  lazymatch goal with X : nth_error tb _ = Some _ |- _ => rename X into Hnth end.
  lazymatch goal with X : PjGrammar.ws _ = false |- _ => rename X into Hws end.
  lazymatch goal with X : getr regs 11 = w64 _ |- _ => rename X into H11 end.
  (* the goal's SRr' is SRrG at wle' segs RZ_cf, the relation of every R rule below *)
  subst c. unfold cfg_at, SRr'.
  (* P of the dispatch memory (the arm's runs write no memory, so it is P at the call and at row 225's memory side) *)
  assert (HPm : P mem) by exact HP0.
  pose proof (va_entry W regs mem (A_prog_sigma AS_parse_value + vrd_arm_off arm - A_prog_base)) as HS.
  assert (EB : @pa_val _ A_prog_listing PI_prog_A A_TEXT = A_prog_base) by reflexivity.
  rewrite EB in HS.
  replace (A_prog_base + (A_prog_sigma AS_parse_value + vrd_arm_off arm - A_prog_base))
    with (A_prog_sigma AS_parse_value + vrd_arm_off arm) in HS by slia.
  change (w64 (pa_sigma AS_parse_value + vrd_arm_off arm)) with (Z_to_bv 64 (A_prog_sigma AS_parse_value + vrd_arm_off arm)).
  assert (HEI : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (va_env regs)) by (unfold va_env; apply Eimg_env).
  assert (SHOK : sh_ok SEGS (SLit 0) [] (va_env regs) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  pose proof (ajx_pres HJ) as HJpres0.
  (* the dispatch journal, lifted ONCE to parse_items' relation wle' segs RZ_cf: the runs and the call below are the
     engine's R forms at that relation. HJ0 keeps the journal at wle for its ajx_* projections *)
  apply (vlift_aj B ARx SK) in HJ.
  pose (RUN := paj_run_xR (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  destruct o; subst b; cbn [vrd_arm_of Z.eqb] in Harm; subst arm; cbn [vrd_arm_off] in HS |- *.
  - paj_run_tok_xR RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    prreg HS (2%bv : bv 5) P2. prreg HS (1%bv : bv 5) P1. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
    prreg HS (18%bv : bv 5) P18. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
    pose proof (vregs Hregs) as (Rsp & R9 & R8 & R18 & R26 & R19 & R20 & R21 & R22 & R25 & R23 & R24 & R27 & R3 & R4 & R10 & R12).
    assert (EW : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                   ew (va_env regs) n = getr regs r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia).
      subst n. apply ew_Ereg_reg. }
    rewrite (EW 2%nat (2%bv : bv 5)) in P2 by (vm_compute; reflexivity || slia).
    pose proof (ajxR_pres HJ) as HJpres. pose proof (ajxR_stk HJ) as HJstk.
    pose proof (vastk HJstk) as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
    pose proof (vfw Hfw) as (He0 & He16 & Hetop & Hepres).
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    assert (Hr16 : spZ regs0 mod 16 = 0)
      by (rewrite Zplus_mod, He16, Z.add_0_r, Zmod_mod in Hsp16; exact Hsp16).
    pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(slia)) as Hm32.
    (* the dispatch's alignment slack is 0 or 16 (spZ regs0 is 16-aligned), stated once for the slia calls below *)
    assert (Hsl16 : (spZ regs0 - 160) mod 32 <= 16) by (clear - Hr16 Hm32; Z.div_mod_to_equations; lia).
    assert (Hx : 0 <= spZ regs0 - 160 - (spZ regs0 - 160) mod 32 < 2 ^ 64) by slia.
    assert (Rregs : spZ regs = spZ regs0 - 160 - (spZ regs0 - 160) mod 32).
    { unfold spZ at 1. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by exact Hx. reflexivity. }
    (* the run wrote no memory: frame_of over the empty region list *)
    assert (KM : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
    { intros a. unfold aview. f_equal. unfold mbyte.
      destruct (Z_le_gt_dec 0 a) as [Ha0|Ha0]; [destruct (Z_lt_ge_dec a (2 ^ 64)) as [Ha1|Ha1]|].
      - symmetry. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _). unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin.
      - symmetry. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _). unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin.
      - symmetry. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _). unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    (* ---- the facts every chain lemma of VproC asks, gathered once ---- *)
    pose proof (vin_p Hin0) as I0p. pose proof (vin_end Hin0) as I0e. pose proof (vin_d Hin0) as I0d. pose proof (vin_rw Hin0) as I0rw. pose proof (vin_q8 Hin0) as I0q8. pose proof (vin_t Hin0) as I0t. pose proof (vin_tl Hin0) as I0tl. pose proof (vin_pp Hin0) as I0pp. pose proof (vin_len Hin0) as I0len. pose proof (vin_g Hin0) as I0g. pose proof (vin_qt Hin0) as I0qt. pose proof (vin_d32 Hin0) as I0d32.
    pose proof (vin_p Hin) as Ip. pose proof (vin_end Hin) as Ie. pose proof (vin_d Hin) as Id. pose proof (vin_rw Hin) as Irw. pose proof (vin_q8 Hin) as Iq8. pose proof (vin_t Hin) as It. pose proof (vin_tl Hin) as Itl. pose proof (vin_pp Hin) as Ipp. pose proof (vin_len Hin) as Ilen. pose proof (vin_g Hin) as Ig. pose proof (vin_qt Hin) as Iqt. pose proof (vin_d32 Hin) as Id32.
    pose proof (vsr_4096 Hsrc) as Hs4096. pose proof (vsr_ceil Hsrc) as Hsac.
    pose proof (ajx_ly HJ0) as HLY0. pose proof (ajx_hi HJ0) as HJkeep.
    assert (Etop : ly_top ly = ly_top ly0)
      by (exact (vly_top HLY0)).
    pose proof (vsav12 Hsaved) as (Sv8 & Sv16).
    assert (EMc0 : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (Sv8r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 8) = Some (raZ regs0))
      by (apply vrd_rdword_of_val_mem; [exact Sv8 | apply bv_unsigned_in_range]).
    assert (Sv16r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 16) = Some (s0Z regs0))
      by (unfold s0Z; apply vrd_rdword_of_val_mem; [exact Sv16 | apply bv_unsigned_in_range]).
    assert (HAGR : forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
                     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a).
    { intros a Ha Hn. destruct (Z_lt_le_dec a (spZ regs0 + e)) as [Hlt|Hge];
      [apply Hwin; [slia | exact Hn] | apply HJkeep; slia]. }
    assert (Hsp8 : spZ regs0 mod 8 = 0) by (clear - Hr16; Z.div_mod_to_equations; lia).
    assert (HVLO : v + 56 <= spZ regs0).
    { destruct Hvwin as [Hv|Hv]; [exact Hv|].
      pose proof (vnd_at Hnode) as Hat. pose proof (vnd_own Hnode) as Hown. exfalso.
      pose proof (ajx_ar HJ0) as HARd. cbv beta in HARd.
      pose proof (vastk HJstk) as (_ & HSTKn & Hceil1 & Hslo1 & _).
      pose proof (@cf_head_nonneg cp) as Hhd0.
      destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                      [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      + pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARd Habk) as (_ & _ & Hcb & _).
        assert (Hk0h : 0 <= k0 + cf_head) by slia.
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq). slia.
      + destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b0 m0 HARd Hinb) as (_ & _ & Hcb & _).
        assert (Hm00 : 0 <= m0) by slia.
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq). slia.
      + destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HARd Hinf) as (_ & Hfc & _). slia.
      + slia. }
    (* the chain at the call view, by VproC's keep lemma vrd_disp_chain *)
    assert (HCH : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms)) (spZ regs) (spZ regs0) ch1 /\
                  spine ch1 = raZ regs0 :: spine ch).
    { rewrite EMc0.
      apply (vrd_disp_chain ly0 ly W0 W mem0 mem regs0 ch q v (spZ regs) p p' Hchain0 Hcur);
        try (apply vrd_rdword_of_val_mem; [exact I0p | slia]);
        try (apply vrd_rdword_of_val_mem; [exact Ip | slia]);
        try exact Iq8; try exact Etop; try exact Hra4k; try exact Sv8r; try exact Sv16r; try exact HAGR;
        try exact HVLO; try exact Hsp8; try (rewrite Rregs; slia); try slia.
      intros a Ha. unfold aview.
      assert (Hk : (Z.to_nat (a - (q + 16)) < 4)%nat) by slia.
      pose proof (I0d _ Hk) as E0. pose proof (Id _ Hk) as E1.
      rewrite Z2Nat.id in E0, E1 by slia.
      replace (q + 16 + (a - (q + 16))) with a in E0, E1 by slia.
      rewrite E0, E1. reflexivity. }
    destruct HCH as (ch1 & Hach & Hspine).
    (* the cursor facts at the CALL state, by vrd_cur_entry_call *)
    rewrite (EW 8%nat (8%bv : bv 5)) in P8 by (vm_compute; reflexivity || slia).
    assert (Hs0 : s0Z (ms_regs ms) = spZ regs0).
    { unfold s0Z. rewrite P8, R8. unfold w64. apply unsigned_lit_small. slia. }
    (* the cursor facts at the CALL state, both halves (VrdPro.vrd_cur_entry_call at the cut interface: the chain
       half prh_cur_entry and the free-trace half prh_cw_entry over CW), named on the way out *)
    assert (HCURc2 : prh_cur_entry W mem (ms_regs ms) q /\ prh_cw_entry B CW W mem (ms_regs ms) q).
    { apply (vrd_cur_entry_call B CW W0 W mem0 mem regs0 (ms_regs ms) q v p Hs0str Hs0items Hcur HCW Hs0);
        try exact Hra0c;
        try exact Hq1; try exact Iq8; try exact Hsp8; try exact Sv8r; try exact Sv16r; try exact HAGR;
        try exact HVLO;
        try (apply vrd_rdword_of_val_mem; [exact I0p | slia]);
        try (clear - I0pp Hs4096; slia);
        try (pose proof (vastk HJstk) as (_ & _ & Hceilx & _); slia);
        try slia.
      assert (Esp2' : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
      rewrite Esp2', Rregs. slia. }
    destruct HCURc2 as [HCURc HCWc].
    (* the cursor's two chain words at the call view: present (the stack window), the low one below alloc_ceiling *)
    assert (HQW : forall F, prh_cursor F -> prh_s0 F q = q ->
              (exists w16, rdword (aview SEGS (w_H W) mem) (q - 16) = Some w16 /\ w16 < alloc_ceiling) /\
              (exists w8, rdword (aview SEGS (w_H W) mem) (q - 8) = Some w8)).
    { intros F HFc HS0.
      assert (Esp2' : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
      destruct (vrd_rdword_present SEGS (w_H W) mem (q - 16)) as (w16 & Hw16).
      { intros kk Hkk. apply HJpres0. pose proof (vastk HJstk) as (_ & HSTKn & _). slia. }
      destruct (vrd_rdword_present SEGS (w_H W) mem (q - 8)) as (w8 & Hw8).
      { intros kk Hkk. apply HJpres0. pose proof (vastk HJstk) as (_ & HSTKn & _). slia. }
      split; [exists w16; split; [exact Hw16|] | exists w8; exact Hw8].
      apply (vce_low _ _ _ _ HCURc F HFc). rewrite HS0. unfold prh_word_entry.
      rewrite Esp2', Rregs.
      destruct (Z.eqb_spec (q - 16) (spZ regs0 - 160 - (spZ regs0 - 160) mod 32 - 8)); [slia|].
      destruct (Z.eqb_spec (q - 16) (spZ regs0 - 160 - (spZ regs0 - 160) mod 32 - 16)); [slia|].
      exact Hw16. }
    (* the value's all-granted trace at the entry cursor IS parse_items' at the call cursor (vrd_gtrace_cont) *)
    assert (EG : prhPv_gtrace d (rest_atR tb text p) = prhPi_gtrace d true (rest_atR tb text p'))
      by (rewrite Hrest, Hsk; exact (vrd_gtrace_cont d 123 yy (rest_atR tb text p) true Hsk eq_refl)).
    eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    (* THE CALL of parse_items, by the engine's BUDGETED caller-window rule over R (YCbqGwild.aj_call_xWFb_spR at
       wle' segs RZ_cf, P := the text's budget wbudget CW 0): the dispatch journal is the budget-free one (WS0 = []),
       the callee's post (tparse_items_specX: SRr' segs RZ_cf, fpostWFbm) brings its own wild budget WS1 back *)
    { eapply (YCbqGwild.aj_call_xWFb_spR SEGS B prh_pst ARx LAWS pa_segs_low (wle' SEGS YGcfRehidePost.RZ_cf)
        (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) W (va_env regs) _ ms
        (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
        ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp _ k [] (STK_parse_items d) (spZ regs0 + e - spZ regs) (rd_fp q v)
        (spZ regs - (spZ regs0 + e)) _ ch1 (YCbqGwild.wbudget CW 0) _ HS eq_refl HJ).
      - unfold spZ at 1. rewrite P2. fold (spZ regs). slia.
      - rewrite Rregs. Z.div_mod_to_equations. lia.
      - rewrite Rregs. slia.
      - exact HSTKi.
      - rewrite Rregs. clear - HSTK Hr16 Hm32. Z.div_mod_to_equations. lia.
      - rewrite Rregs. slia.
      - rewrite Rregs. Z.div_mod_to_equations. lia.
      - slia.
      - rewrite P3, (EW 3%nat (3%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R3. exact Hgp0.
      - rewrite P4, (EW 4%nat (4%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R4. exact Htp0.
      - exact P1.
      - apply (ret_ok_codeptr_v (PI := PI_prog_A)); [slia | reflexivity].
      - rewrite EB. unfold A_prog_base. rewrite unsigned_lit_small by slia. slia.
      - replace (spZ regs0 + e + (spZ regs - (spZ regs0 + e))) with (spZ regs) by slia. rewrite Hs0. exact Hach.
      - intros HPRE1 _.
        cbn [ss_pc setpc].
        assert (EM : ms_mem ms = mem).
        { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
          unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
        assert (Esp2 : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
        refine (HPI ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1
          (spZ regs0 + e - spZ regs) q text len p' tb v true Lam peak cnt fail ran
          most own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
        (* 1 fpre: the call rule's afn_pre_x, the read-only view, and the caller-frame bound *)
        { split; [exact HPRE1|]. split; [intros a H1 H2 H3; rewrite KM; exact (Hrod a H1 H2 H3)|].
          assert (Ehi : ly_stk_hi ly = ly_stk_hi ly0)
            by (exact (vly_stk_hi HLY0)).
          split; [rewrite Esp2, Rregs, Ehi; clear - Hshi He0 Hm32; slia|].
          (* fpre's ra bound (the cut's PRH_Base.v fpre): the return address is the jal's own return pc *)
          unfold raZ at 1. rewrite P1, EB. rewrite unsigned_lit_small by (unfold A_prog_base; slia).
          split; [exact vrd_ret217_lt_ceil | exact Hfrm]. }
        (* 1b memnorm at entry (the cut's tparse_items_specX): the call memory is the dispatch memory, and srr_inv_mn
           reads memnorm off P *)
        { rewrite EM. exact (PM mem HPm). }
        (* 2 the call context *)
        { unfold raZ at 1. rewrite P1, EB. rewrite unsigned_lit_small by (unfold A_prog_base; slia).
          rewrite Hspine.
          replace (A_prog_base + 19596) with (A_prog_base + 4 * Z.of_nat (A_prog_slot AS_parse_value + 215))
            by (vm_compute; reflexivity).
          exact HCTX. }
        (* 3 the universe closure: the body's *)
        { exact Hclos. }
        (* 4 the chain half of the cursor facts at the call state (vrd_cur_entry_call) *)
        { rewrite EMc0. exact HCURc. }
        (* 4b the cursor's free-trace words named in CW, at the call state (vrd_cur_entry_call's second half) *)
        { rewrite EMc0. exact HCWc. }
        (* 5 the entry chain at the call view *)
        { exists ch1. split; [rewrite Esp2, Hs0; exact Hach | rewrite Hspine; reflexivity]. }
        (* 6 the cursor chain at the call sp, by vrd_cur_chain_call *)
        { right. split; [rewrite Esp2, Rregs; slia|].
          assert (HS0 : prh_s0 F_parse_string q = q) by (unfold prh_s0; rewrite Hs0str; slia).
          rewrite HS0, EMc0.
          destruct (HQW F_parse_string (or_introl eq_refl) HS0) as ((w16 & Hw16 & Hw16c) & Hw8).
          pose proof (vastk HJstk) as (_ & _ & _ & _ & _ & _ & _ & Htopx & _).
          apply (vrd_cur_chain_call ly (w_H W) mem (spZ (ms_regs ms)) q w16);
            try exact Hw16; try exact Hw16c; try exact Hw8; try exact Iq8; try (rewrite Esp2, Rregs; slia); slia. }
        (* 7, 8, 9 the argument registers *)
        { rewrite P10, (EW 20%nat (20%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R20. }
        { rewrite P11, (EW 19%nat (19%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R19. }
        { rewrite P12. reflexivity. }
        (* 10 rd_pre at the call *)
        { rewrite EM.
          assert (Hd16 : (spZ regs0 - spZ regs) mod 16 = 0) by (rewrite Rregs; Z.div_mod_to_equations; lia).
          replace (spZ regs0 + e - spZ regs) with (e + (spZ regs0 - spZ regs)) by slia.
          split; [exact Hfrm|]. split; [exact Hmu|]. split; [exact Hr1|]. split; [exact Hr2|].
          split; [exact Hin|].
          split.
          { apply (vrd_fwin_shift ly W regs0 (ms_regs ms) mem e (spZ regs0 - spZ regs) Hfw); [slia | slia | exact Hd16 |].
            intros a Ha. apply HJpres0. rewrite Rregs in Ha. slia. }
          split; [slia|]. split; [slia|].
          split; [exact Hraq|]. split; [exact Hsrc|]. split; [exact Hhome|]. split; [exact Hmax|].
          split; [apply (vrd_node_shift B (STK_parse_value d) (STK_parse_items d) e (spZ regs0 - spZ regs)
                    ly S W regs0 (ms_regs ms) mem Lam v Hnode); [slia | slia | rewrite Rregs; slia]|].
          split; [exact Hqv|]. split; [exact Htv|].
          split.
          { pose proof (vnd_own Hnode) as Hown.
            destruct Hvwin as [Hv1 | Hv1]; [left | right; slia].
            destruct (Z_le_gt_dec (v + 56) (spZ regs0 - STK_parse_value d)) as [Hle|Hgt]; [slia|].
            exfalso. destruct (Hown (v + 55) ltac:(slia)) as [_ Hn]. apply Hn. slia. }
          split; [exact Hled|].
          split; [pose proof (vin_d32 Hin) as Hd32; unfold PjGrammar.MAXD; slia|].
          exact (conj Hcnt HTC). }
        (* 11, 12 the opener *)
        { exact Hplt. }
        { exact Hnth. }
        (* 13 the room, by vrd_gtrace_cont *)
        { rewrite <- EG. exact Hroom. }
        (* 13b the wild room at the call state: the entry's (tparse_value_specX's, which vrd_disp_body carries at S0),
           since the dispatch moves only fake frames (S = set_fs f S0, so st_depot S is st_depot S0 by conversion) *)
        { destruct Hsetfs as (fz & Efz). rewrite Efz. exact HWR0. }
        (* 14, 15 the live counts along the granted events: tparse_value_specX's entry counts, which vrd_disp_body
           carries at S0, at parse_items' own trace (EG); the dispatch state is S0 with only its fake frames moved
           (`S = set_fs f S0`), and rs_live (room_of_cf _) reads no fake frame, so it is the same list *)
        { rewrite <- EG. destruct Hsetfs as (fz & Efz). rewrite Efz.
          change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
            with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)).
          exact HC0s. }
        { rewrite <- EG. destruct Hsetfs as (fz & Efz). rewrite Efz.
          change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
            with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)).
          exact HC024. }
        (* 15b the hull budget at the call state: parse_value's entry budget HHB at parse_items' own list (EG); the
           dispatch moves only fake frames (`S = set_fs f S0`), which keep st_secs, so the counts are the entry's *)
        { rewrite <- EG. destruct Hsetfs as (fz & Efz). rewrite Efz.
          exact (PresetHullBudget.hull_budget_same S0 (set_fs fz S0) _
                   (YGcfSecsStep.secs_same_of_secs S0 (set_fs fz S0) eq_refl) HHB). }
        (* 15 the chain from parse_items' s0 *)
        { assert (HS0 : prh_s0 F_parse_items q = q) by (unfold prh_s0; rewrite Hs0items; slia).
          rewrite HS0, EMc0.
          destruct (HQW F_parse_items (or_intror eq_refl) HS0) as ((w16 & Hw16 & Hw16c) & Hw8).
          pose proof (pi_frame_nonneg F_parse_items) as Hpf.
          pose proof (vastk HJstk) as (_ & _ & _ & _ & _ & _ & _ & Htopx & _).
          apply (vrd_cur_chain_call ly (w_H W) mem (spZ (ms_regs ms) - pi_frame F_parse_items) q w16);
            try exact Hw16; try exact Hw16c; try exact Hw8; try exact Iq8; try (rewrite Esp2, Rregs; slia); slia. }
        (* 15 the frames headroom *)
        { exact Hfrb. }
      - intros a Ha. left. exact Ha. }
    cbv beta. intros W2 c2 HW2
      (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ2 & HJc & HWIN & HP2 & HQ).
    (* the caller's journal over the call carries the callee's wild budget WS1 ([] ++ WS1): rows 217..225 run on its
       REBASED form (YCbqGwild.ajournal_xw_rebaseR: the entry depot moved to the call's, budget []), and the end
       journal is folded back with the composed journal's wild-part inclusion (YCbqGwild.ajournal_xw_unbase0R), all at
       wle' segs RZ_cf *)
    pose proof (ajxR_wild HJ2) as HWild2. cbn [app] in HWild2.
    apply (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx) in HJ2.
    (* rows 217 (`j` to row 224) and 224 (`mv s5, a0`): a fresh symbolic state at the return site, at fx2 *)
    pose proof (va_entry (fx := fx2) W2 regs2 mem2 (vrd_row 217)) as HS2.
    rewrite EB in HS2.
    replace (pa_val A_TEXT + 19596) with (A_prog_base + vrd_row 217) by (rewrite EB; reflexivity).
    assert (HEI2 : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (va_env regs2)) by (unfold va_env; apply Eimg_env).
    assert (SHOK2 : sh_ok SEGS (SLit 0) [] (va_env regs2) (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
    pose (RUNTO2 := paj_run_to_xR (fx := fx2) (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS
      (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    paj_run_to_tok_xR RUNTO2 HS2 HJ2 SHOK2 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (vrd_row 225).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    pmkst HS2.
    prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (26%bv : bv 5) Q26.
    prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
    assert (EW2 : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                    ew (va_env regs2) n = getr regs2 r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
    assert (EM2 : ms_mem ms0 = mem2).
    { apply functional_extensionality. intros x. apply HF0. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (EMc : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    pose proof (ajxR_ly HJc) as HLY.
    assert (EF : ly_F ly2 = ly_F ly) by (exact (vly_F HLY)).
    assert (Efr : frame_addr ly2 0 pos = frame_addr ly 0 pos) by (unfold frame_addr; rewrite EF; reflexivity).
    assert (Efl : flag_addr ly2 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite EF; reflexivity).
    assert (KS8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HP2 8); unfold acallee_saved; slia).
    assert (KS18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HP2 18); unfold acallee_saved; slia).
    assert (KS26 : getr regs2 26 = getr (ms_regs ms) 26) by (apply (HP2 26); unfold acallee_saved; slia).
    assert (KS24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HP2 24); unfold acallee_saved; slia).
    assert (KS3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HP2 3); unfold acallee_saved; slia).
    assert (KS4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HP2 4); unfold acallee_saved; slia).
    Ltac va_cs := first [(vm_compute; reflexivity) | slia].
    (* parse_items' post (PRH_FnParse.v tparse_items_specX), read BY NAME through the kit's projection layer: fQmn's
       two parts (the post and the memnorm keep), then tpiP_R_of gives the outcomes in the text's binder order and the
       record tpiP_R, whose fields name the conjuncts. md2 is the one argument of the post that its body does not
       mention, so it is given by name. *)
    destruct HQ as (HQb & Hmk).
    apply tpiP_R_of with (md' := md2) in HQb.
    destruct HQb as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HRi).
    pose proof (tpiP_run HRi) as Hjr. pose proof (tpiP_ledger HRi) as Hled2. pose proof (tpiP_room HRi) as Hroom2.
    pose proof (tpiP_live HRi) as Hlv2. pose proof (tpiP_pos HRi) as Hrp2. pose proof (tpiP_ledger_move HRi) as Hmove.
    pose proof (tpiP_blocks_move HRi) as Hbm. pose proof (tpiP_bytes HRi) as Hbb. pose proof (tpiP_lsum HRi) as Hlh.
    pose proof (tpiP_arm HRi) as Hres. pose proof (tpiP_hull HRi) as Hhu2.
    (* P across the call: the m-form post's memnorm keep and srr_inv_call; the run to row 225 writes no memory *)
    assert (HPc : P (ms_mem ms)) by (rewrite EMc; exact HPm).
    assert (HPr : P (ms_mem ms0)) by (rewrite EM2; exact (PC (ms_mem ms) mem2 Hmk HPc)).
    assert (Hrv : getr regs2 10 = w64 (match res with Some _ => 0 | None => -1 end))
      by (destruct res as [[t r]|]; cbv beta iota in Hres;
          [exact (tpiPs_ret (tpiP_RSome_of Hres)) | exact (tpiPn_ret (tpiP_RNone_of Hres))]).
    apply (SRrG_ret SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)).
    split; [|exact HPr]. unfold vrd_arm_exitR.
    exists fx2, pos, (match res with Some _ => 0 | None => -1 end).
    (* the join BY NAME: VrdNum's record vrd_epi_R at the join's witnesses (vrd_epi_aR_of_R), one named goal per field *)
    apply vrd_epi_aR_of_R with (regs := ms_regs ms0) (mem := ms_mem ms0)
      (md := with_vm_backing (m_vm_lazy md2) mat0 md2) (ly := ly2) (S := S2) (Hp := Hp2) (k := k + k1).
    refine {| vepi_cfg := ?[e_cfg]; vepi_jrn := ?[e_jrn]; vepi_win := ?[e_win]; vepi_s0 := ?[e_s0]; vepi_s2 := ?[e_s2];
              vepi_s10 := ?[e_s10]; vepi_s8 := ?[e_s8]; vepi_s5 := ?[e_s5]; vepi_gp := ?[e_gp]; vepi_tp := ?[e_tp];
              vepi_ra := ?[e_ra]; vepi_saved := ?[e_saved]; vepi_flag := ?[e_flag]; vepi_frm := ?[e_frm];
              vepi_fregs := ?[e_fregs]; vepi_rq := ?[e_rq] |}.
    [e_cfg]: { rewrite vrd_pc_epi; reflexivity. }
    (* the join's journal at wle' segs RZ_cf: the callee's budget WS1, which its post bounds by wbudget CW 0 (HPW) *)
    [e_jrn]: { exists WS1. split; [|exact HPW].
      eapply (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx); [exact HJ2 | exact HWild2]. }
    [e_win]: { intros a Ha Hn. rewrite EM2, (HWIN a ltac:(slia) Hn), EMc. exact (Hwin a Ha Hn). }
    [e_s0]: { rewrite Q8, (EW2 8%nat (8%bv : bv 5)) by va_cs; rewrite KS8; rewrite P8; exact R8. }
    [e_s2]: { rewrite Efr, Q18, (EW2 18%nat (18%bv : bv 5)) by va_cs; rewrite KS18;
              rewrite P18, (EW 18%nat (18%bv : bv 5)) by va_cs; exact R18. }
    [e_s10]: { rewrite Efr, Q26, (EW2 26%nat (26%bv : bv 5)) by va_cs; rewrite KS26;
               rewrite P26, (EW 26%nat (26%bv : bv 5)) by va_cs; exact R26. }
    [e_s8]: { rewrite Efr, Q24, (EW2 24%nat (24%bv : bv 5)) by va_cs; rewrite KS24;
              rewrite P24, (EW 24%nat (24%bv : bv 5)) by va_cs; exact R24. }
    [e_s5]: { rewrite Q21, (EW2 10%nat (10%bv : bv 5)) by va_cs; exact Hrv. }
    [e_gp]: { rewrite Q3, (EW2 3%nat (3%bv : bv 5)) by va_cs; rewrite KS3;
              rewrite P3, (EW 3%nat (3%bv : bv 5)) by va_cs; exact R3. }
    [e_tp]: { rewrite Q4, (EW2 4%nat (4%bv : bv 5)) by va_cs; rewrite KS4;
              rewrite P4, (EW 4%nat (4%bv : bv 5)) by va_cs; exact R4. }
    [e_ra]: exact Hra0.
    (* the thirteen spilled words: parse_value's own frame below spZ regs0, outside rd_fp q v (the cursor is above
       spZ regs0, the node outside parse_value's stack window), kept by the callee's window clause and both runs *)
    [e_saved]: { assert (KSV : forall a, spZ regs0 - 104 <= a < spZ regs0 ->
                aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
      { intros a Ha. rewrite EM2. rewrite (HWIN a); [rewrite EMc; reflexivity | rewrite Rregs; slia |].
        intros (r & Hrin & Hr). cbn [rd_fp In] in Hrin.
        destruct Hrin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; [slia | slia |].
        pose proof (vnd_own Hnode) as Hown.
        destruct (Hown a Hr) as [_ Hn]. apply Hn. slia. }
      unfold vrd_saved in Hsaved |- *.
      destruct Hsaved as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (eapply val_mem_kept; [|eassumption]; intros kk Hk; cbn in Hk; apply KSV; slia). }
    (* the flag word at F + 56: it lies in parse_value's OWN fake frame, which is below alloc_ceiling, and outside the
       callee's footprint rd_fp q v (the cursor is a stack address above alloc_ceiling; the node cannot meet the frame:
       a block is apart from a frame, another frame is apart from this one, and this frame itself would put the
       descriptor word at F + 16 inside the node's 56 ZEROED bytes). So the callee's journal frames clause keeps it. *)
    [e_flag]: { rewrite Efr, Efl.
      pose proof (ajx_ar HJ0) as HAR. cbv beta in HAR.
      assert (HinF : In (0, pos) (frames S)) by (rewrite Hfr; left; reflexivity).
      destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HFa0 & HFc & HFapp).
      assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFc.
      pose proof (vfrm3 Hframe) as (Hmag & Hsig & Hflag).
      pose proof (vnd_v4096 Hnode) as Hv4096. pose proof (vnd_al8 Hnode) as Hval8. pose proof (vnd_rw Hnode) as Hrw. pose proof (vnd_zero Hnode) as Hzero. pose proof (vnd_at Hnode) as Hat. pose proof (vnd_amr Hnode) as Hamr. pose proof (vnd_own Hnode) as Hown. pose proof (vnd_ra Hnode) as Hra8.
      pose proof (@cf_head_nonneg cp) as Hhd0.
      assert (HvF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> ~ (v <= a < v + 56)).
      { intros a Ha Hav.
        destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                        [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
        - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
          pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
          apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (a0 - cf_head) (k0 + cf_head) a HAR HinF Habk);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hk0h : 0 <= k0 + cf_head) by slia.
          pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq). slia.
        - apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) b0 m0 a HAR HinF Hinb);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hm00 : 0 <= m0) by slia.
          pose proof (req_size_pos m0 Hm00) as (_ & Hrq). slia.
        - rewrite Hfr in Hinf. destruct Hinf as [Ef | Hinf].
          + injection Ef as <- <-.
            assert (Hz16 : val_mem SEGS (mrestrict (w_H W) mem) (frame_addr ly 0 pos + 16) 8 0).
            { apply (vrd_zero_val SEGS (mrestrict (w_H W) mem) v); [exact Hzero | rewrite Hfb in Hhif; slia | rewrite Hfb in Hhif; slia]. }
            pose proof (Hsig 0%nat ltac:(slia)) as E1. pose proof (Hz16 0%nat ltac:(slia)) as E2.
            cbn [Z.of_nat] in E1, E2. rewrite Z.add_0_r in E1, E2.
            rewrite E1 in E2. vm_compute in E2. discriminate E2.
          + apply in_split in Hinf as (l2 & l3 & El).
            pose proof (sep_frames_pos_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (cid, pos') (@nil (Z * Z)) l2 l3 HAR
              ltac:(rewrite Hfr, El; reflexivity)) as Hd.
            unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Hfb in Hd. slia.
        - slia. }
      assert (HqF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> a < q).
      { intros a Ha. pose proof (vastk HJstk) as (_ & _ & Hclo2 & Hlo2 & _). slia. }
      assert (HnFP : forall a, frame_addr ly 0 pos + 56 <= a < frame_addr ly 0 pos + 64 -> ~ inFP (rd_fp q v) a).
      { intros a Ha (r & Hrin & Hr). cbn [rd_fp In] in Hrin.
        destruct Hrin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr;
        [pose proof (HqF a ltac:(slia)); slia | pose proof (HqF a ltac:(slia)); slia | exact (HvF a ltac:(slia) Hr)]. }
      pose proof (ajxR_frm HJc) as HJfr.
      eapply val_mem_kept; [|exact Hflag]. intros kk Hk. cbn in Hk.
      rewrite EM2, <- EMc.
      apply (HJfr 0 pos (frame_addr ly 0 pos + 56 + kk) HinF);
      [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia
      | apply HnFP; slia]. }
    [e_frm]: exact HFZ.
    [e_fregs]: exact HFK.
    (* RQ: parse_items' post read back as parse_value's (VnumC's vrd_pv_post), BY NAME: VrdNum's record vrd_pv_R
       (vrd_pv_post_of_R), one named goal per field. The outcomes, the trace and the blocks are parse_items'
       (vrd_cont_model; the granted traces by EG); the entry state S0 is the call state S up to its fake frames
       (`S = set_fs f S0`), which neither the live list nor the run position reads *)
    [e_rq]: {
      rewrite EM2.
      apply vrd_pv_post_of_R with (ok := ok) (res := res) (tr := tr) (okr := okr) (D := D) (Lam' := Lam')
        (peak' := peak') (cnt' := cnt') (fail' := fail') (ran' := ran').
      pose proof (vrd_rest_shrink tb text p p' (proj1 Hpp)) as Hshr.
      (* the value's free order at the entry cursor IS parse_items' at the call cursor (vrd_frees_cont) *)
      assert (EFR : prhPv_frees d (rest_atR tb text p) ok = prhPi_frees d true (rest_atR tb text p') ok)
        by (rewrite Hrest, Hsk; exact (vrd_frees_cont d (rest_atR tb text p) ok 123 yy true Hsk eq_refl)).
      pose proof (vbm_new Hbm) as Hb1. pose proof (vbm_blocks Hbm) as Hb2. pose proof (vbm_frames Hbm) as Hb3. pose proof (vbm_peak Hbm) as Hb4.
      destruct Hsetfs as (fz & Efz).
      refine {| vpv_run := ?[p_run]; vpv_ledger := ?[p_ledger]; vpv_room := ?[p_room]; vpv_hull := ?[p_hull];
                vpv_live := ?[p_live]; vpv_pos := ?[p_pos]; vpv_outcome := ?[p_outcome]; vpv_injected := ?[p_injected];
                vpv_ledger_move := ?[p_ledger_move]; vpv_fresh := ?[p_fresh]; vpv_blocks := ?[p_blocks];
                vpv_frames := ?[p_frames]; vpv_hpeak := ?[p_hpeak]; vpv_bytes := ?[p_bytes]; vpv_lsum := ?[p_lsum];
                vpv_arm := ?[p_arm] |}.
      [p_run]: { rewrite (vrd_cont_model ReaderRes.jr_strtod d 123 yy (rest_atR tb text p) ok true Hsk eq_refl), <- Hsk,
          <- Hrest.
        exact Hjr. }
      [p_ledger]: exact Hled2.
      [p_room]: exact Hroom2.
      (* the hull use: parse_items' own from the call state S, which has S0's st_secs (`S = set_fs f S0`) *)
      [p_hull]: { rewrite EG.
        assert (HSS : PresetHullBudget.hull_used S0 S [])
          by (apply PresetHullBudget.hull_used_secs; rewrite Efz; reflexivity).
        exact (PresetHullBudget.hull_used_app S0 S S2 [] _ HSS Hhu2). }
      [p_live]: { rewrite Efz in Hlv2.
        change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
          with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) in Hlv2.
        exact Hlv2. }
      [p_pos]: { intros sm x os i Hz0 hist Hpos Hrun.
        assert (HposS : PresetRoomPos.iface_room_pos sm x os i Hz0 hist S)
          by (rewrite Efz; apply PresetRoomPosKeep.room_pos_set_fs; exact Hpos).
        exact (Hrp2 sm x os i Hz0 hist HposS Hrun). }
      [p_outcome]: { intros sm x os i Hz0 hist Hpos Hrun Hcons Hfail. rewrite EG in Hrun, Hcons, Hfail |- *.
        assert (HposS : PresetRoomPos.iface_room_pos sm x os i Hz0 hist S)
          by (rewrite Efz; apply PresetRoomPosKeep.room_pos_set_fs; exact Hpos).
        split; [exact (tpiP_outcome_ran HRi HposS Hrun Hcons Hfail)|].
        split; [|exact (tpiP_outcome_pos HRi HposS Hrun Hcons Hfail)].
        rewrite (vrd_cont_model ReaderRes.jr_strtod d 123 yy (rest_atR tb text p) [] true Hsk eq_refl), <- Hsk, <- Hrest.
        exact (tpiP_outcome_run HRi HposS Hrun Hcons Hfail). }
      (* the injected reading: parse_items' own (tpiP_injected) at the call state. Under the model's grant list the
         value's events are parse_items' at the opener (vrd_cont_model), and the value's window is parse_items' (EG) *)
      [p_injected]: { intros sm x os i Hz0 hist Hpos Hrun Hcons Hwd. rewrite EG in Hwd.
        rewrite (vrd_cont_model ReaderRes.jr_strtod d 123 yy (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))
          true Hsk eq_refl), <- Hsk, <- Hrest in Hrun, Hcons.
        assert (HposS : PresetRoomPos.iface_room_pos sm x os i Hz0 hist S)
          by (rewrite Efz; apply PresetRoomPosKeep.room_pos_set_fs; exact Hpos).
        exact (tpiP_injected HRi HposS Hrun Hcons Hwd). }
      [p_ledger_move]: { rewrite EG; exact Hmove. }
      [p_fresh]: { rewrite <- Hab; exact Hb1. }
      [p_blocks]: { rewrite <- Hab; exact Hb2. }
      [p_frames]: { rewrite <- Hfr; exact Hb3. }
      [p_hpeak]: slia.
      [p_bytes]: { rewrite (blocks_bytes_bsum B ly0 S0), <- Hab, <- (blocks_bytes_bsum B ly S). exact Hbb. }
      [p_lsum]: exact Hlh.
      [p_arm]: {
        destruct res as [[t r]|].
        + (* the granted arm of parse_items' post, BY NAME (tpiP_RSome), read into the value's (vrd_pv_RSome) *)
          cbv beta iota in Hres. apply tpiP_RSome_of in Hres.
          pose proof (tpiPs_in_ok Hres) as HsA. pose proof (tpiPs_node Hres) as HsB.
          pose proof (tpiPs_lsum_le Hres) as HsC. pose proof (tpiPs_freeord Hres) as HsF.
          pose proof (tpiPs_ncap Hres) as HsN. clear Hres.
          refine {| vpvs_rv := ?[s_rv]; vpvs_freeord := ?[s_freeord]; vpvs_in_ok := ?[s_in_ok]; vpvs_node := ?[s_node];
                    vpvs_ncap := ?[s_ncap]; vpvs_lsum_le := ?[s_lsum_le] |}.
          [s_rv]: reflexivity.
          [s_freeord]: { intros Hhd n Hn. rewrite EFR. exact (HsF Hhd n Hn). }
          [s_in_ok]: exact HsA.
          [s_node]: exact HsB.
          [s_ncap]: exact HsN.
          [s_lsum_le]: slia.
        + (* the refused arm of parse_items' post, BY NAME (tpiP_RNone), read into the value's (vrd_pv_RNone) *)
          cbv beta iota in Hres. apply tpiP_RNone_of in Hres.
          pose proof (tpiPn_in_after Hres) as HnA. pose proof (tpiPn_fd Hres) as HnB.
          pose proof (tpiPn_freeord Hres) as HnF. clear Hres.
          refine {| vpvn_rv := ?[n_rv]; vpvn_freeord := ?[n_freeord]; vpvn_in_after := ?[n_in_after];
                    vpvn_fd := ?[n_fd] |}.
          [n_rv]: reflexivity.
          [n_freeord]: { intros Hhd n Hn. rewrite EFR. exact (HnF Hhd n Hn). }
          (* the cursor's depth bound widens from d + 1 to d: pj_in_afterR's own body (PRH_Reader.v) *)
          [n_in_after]: { destruct HnA as (p2 & d2 & HnA'). decompose [and] HnA'. exists p2, d2.
            repeat split; try assumption; slia. }
          [n_fd]: exact HnB. }
    }
  - paj_run_tok_xR RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    prreg HS (2%bv : bv 5) P2. prreg HS (1%bv : bv 5) P1. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
    prreg HS (18%bv : bv 5) P18. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
    pose proof (vregs Hregs) as (Rsp & R9 & R8 & R18 & R26 & R19 & R20 & R21 & R22 & R25 & R23 & R24 & R27 & R3 & R4 & R10 & R12).
    assert (EW : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                   ew (va_env regs) n = getr regs r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia).
      subst n. apply ew_Ereg_reg. }
    rewrite (EW 2%nat (2%bv : bv 5)) in P2 by (vm_compute; reflexivity || slia).
    pose proof (ajxR_pres HJ) as HJpres. pose proof (ajxR_stk HJ) as HJstk.
    pose proof (vastk HJstk) as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
    pose proof (vfw Hfw) as (He0 & He16 & Hetop & Hepres).
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    assert (Hr16 : spZ regs0 mod 16 = 0)
      by (rewrite Zplus_mod, He16, Z.add_0_r, Zmod_mod in Hsp16; exact Hsp16).
    pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(slia)) as Hm32.
    (* the dispatch's alignment slack is 0 or 16 (spZ regs0 is 16-aligned), stated once for the slia calls below *)
    assert (Hsl16 : (spZ regs0 - 160) mod 32 <= 16) by (clear - Hr16 Hm32; Z.div_mod_to_equations; lia).
    assert (Hx : 0 <= spZ regs0 - 160 - (spZ regs0 - 160) mod 32 < 2 ^ 64) by slia.
    assert (Rregs : spZ regs = spZ regs0 - 160 - (spZ regs0 - 160) mod 32).
    { unfold spZ at 1. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by exact Hx. reflexivity. }
    (* the run wrote no memory: frame_of over the empty region list *)
    assert (KM : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
    { intros a. unfold aview. f_equal. unfold mbyte.
      destruct (Z_le_gt_dec 0 a) as [Ha0|Ha0]; [destruct (Z_lt_ge_dec a (2 ^ 64)) as [Ha1|Ha1]|].
      - symmetry. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _). unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin.
      - symmetry. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _). unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin.
      - symmetry. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _). unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    (* ---- the facts every chain lemma of VproC asks, gathered once ---- *)
    pose proof (vin_p Hin0) as I0p. pose proof (vin_end Hin0) as I0e. pose proof (vin_d Hin0) as I0d. pose proof (vin_rw Hin0) as I0rw. pose proof (vin_q8 Hin0) as I0q8. pose proof (vin_t Hin0) as I0t. pose proof (vin_tl Hin0) as I0tl. pose proof (vin_pp Hin0) as I0pp. pose proof (vin_len Hin0) as I0len. pose proof (vin_g Hin0) as I0g. pose proof (vin_qt Hin0) as I0qt. pose proof (vin_d32 Hin0) as I0d32.
    pose proof (vin_p Hin) as Ip. pose proof (vin_end Hin) as Ie. pose proof (vin_d Hin) as Id. pose proof (vin_rw Hin) as Irw. pose proof (vin_q8 Hin) as Iq8. pose proof (vin_t Hin) as It. pose proof (vin_tl Hin) as Itl. pose proof (vin_pp Hin) as Ipp. pose proof (vin_len Hin) as Ilen. pose proof (vin_g Hin) as Ig. pose proof (vin_qt Hin) as Iqt. pose proof (vin_d32 Hin) as Id32.
    pose proof (vsr_4096 Hsrc) as Hs4096. pose proof (vsr_ceil Hsrc) as Hsac.
    pose proof (ajx_ly HJ0) as HLY0. pose proof (ajx_hi HJ0) as HJkeep.
    assert (Etop : ly_top ly = ly_top ly0)
      by (exact (vly_top HLY0)).
    pose proof (vsav12 Hsaved) as (Sv8 & Sv16).
    assert (EMc0 : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (Sv8r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 8) = Some (raZ regs0))
      by (apply vrd_rdword_of_val_mem; [exact Sv8 | apply bv_unsigned_in_range]).
    assert (Sv16r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 16) = Some (s0Z regs0))
      by (unfold s0Z; apply vrd_rdword_of_val_mem; [exact Sv16 | apply bv_unsigned_in_range]).
    assert (HAGR : forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
                     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a).
    { intros a Ha Hn. destruct (Z_lt_le_dec a (spZ regs0 + e)) as [Hlt|Hge];
      [apply Hwin; [slia | exact Hn] | apply HJkeep; slia]. }
    assert (Hsp8 : spZ regs0 mod 8 = 0) by (clear - Hr16; Z.div_mod_to_equations; lia).
    assert (HVLO : v + 56 <= spZ regs0).
    { destruct Hvwin as [Hv|Hv]; [exact Hv|].
      pose proof (vnd_at Hnode) as Hat. pose proof (vnd_own Hnode) as Hown. exfalso.
      pose proof (ajx_ar HJ0) as HARd. cbv beta in HARd.
      pose proof (vastk HJstk) as (_ & HSTKn & Hceil1 & Hslo1 & _).
      pose proof (@cf_head_nonneg cp) as Hhd0.
      destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                      [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      + pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARd Habk) as (_ & _ & Hcb & _).
        assert (Hk0h : 0 <= k0 + cf_head) by slia.
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq). slia.
      + destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b0 m0 HARd Hinb) as (_ & _ & Hcb & _).
        assert (Hm00 : 0 <= m0) by slia.
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq). slia.
      + destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HARd Hinf) as (_ & Hfc & _). slia.
      + slia. }
    (* the chain at the call view, by VproC's keep lemma vrd_disp_chain *)
    assert (HCH : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms)) (spZ regs) (spZ regs0) ch1 /\
                  spine ch1 = raZ regs0 :: spine ch).
    { rewrite EMc0.
      apply (vrd_disp_chain ly0 ly W0 W mem0 mem regs0 ch q v (spZ regs) p p' Hchain0 Hcur);
        try (apply vrd_rdword_of_val_mem; [exact I0p | slia]);
        try (apply vrd_rdword_of_val_mem; [exact Ip | slia]);
        try exact Iq8; try exact Etop; try exact Hra4k; try exact Sv8r; try exact Sv16r; try exact HAGR;
        try exact HVLO; try exact Hsp8; try (rewrite Rregs; slia); try slia.
      intros a Ha. unfold aview.
      assert (Hk : (Z.to_nat (a - (q + 16)) < 4)%nat) by slia.
      pose proof (I0d _ Hk) as E0. pose proof (Id _ Hk) as E1.
      rewrite Z2Nat.id in E0, E1 by slia.
      replace (q + 16 + (a - (q + 16))) with a in E0, E1 by slia.
      rewrite E0, E1. reflexivity. }
    destruct HCH as (ch1 & Hach & Hspine).
    (* the cursor facts at the CALL state, by vrd_cur_entry_call *)
    rewrite (EW 8%nat (8%bv : bv 5)) in P8 by (vm_compute; reflexivity || slia).
    assert (Hs0 : s0Z (ms_regs ms) = spZ regs0).
    { unfold s0Z. rewrite P8, R8. unfold w64. apply unsigned_lit_small. slia. }
    (* the cursor facts at the CALL state, both halves (VrdPro.vrd_cur_entry_call at the cut interface: the chain
       half prh_cur_entry and the free-trace half prh_cw_entry over CW), named on the way out *)
    assert (HCURc2 : prh_cur_entry W mem (ms_regs ms) q /\ prh_cw_entry B CW W mem (ms_regs ms) q).
    { apply (vrd_cur_entry_call B CW W0 W mem0 mem regs0 (ms_regs ms) q v p Hs0str Hs0items Hcur HCW Hs0);
        try exact Hra0c;
        try exact Hq1; try exact Iq8; try exact Hsp8; try exact Sv8r; try exact Sv16r; try exact HAGR;
        try exact HVLO;
        try (apply vrd_rdword_of_val_mem; [exact I0p | slia]);
        try (clear - I0pp Hs4096; slia);
        try (pose proof (vastk HJstk) as (_ & _ & Hceilx & _); slia);
        try slia.
      assert (Esp2' : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
      rewrite Esp2', Rregs. slia. }
    destruct HCURc2 as [HCURc HCWc].
    (* the cursor's two chain words at the call view: present (the stack window), the low one below alloc_ceiling *)
    assert (HQW : forall F, prh_cursor F -> prh_s0 F q = q ->
              (exists w16, rdword (aview SEGS (w_H W) mem) (q - 16) = Some w16 /\ w16 < alloc_ceiling) /\
              (exists w8, rdword (aview SEGS (w_H W) mem) (q - 8) = Some w8)).
    { intros F HFc HS0.
      assert (Esp2' : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
      destruct (vrd_rdword_present SEGS (w_H W) mem (q - 16)) as (w16 & Hw16).
      { intros kk Hkk. apply HJpres0. pose proof (vastk HJstk) as (_ & HSTKn & _). slia. }
      destruct (vrd_rdword_present SEGS (w_H W) mem (q - 8)) as (w8 & Hw8).
      { intros kk Hkk. apply HJpres0. pose proof (vastk HJstk) as (_ & HSTKn & _). slia. }
      split; [exists w16; split; [exact Hw16|] | exists w8; exact Hw8].
      apply (vce_low _ _ _ _ HCURc F HFc). rewrite HS0. unfold prh_word_entry.
      rewrite Esp2', Rregs.
      destruct (Z.eqb_spec (q - 16) (spZ regs0 - 160 - (spZ regs0 - 160) mod 32 - 8)); [slia|].
      destruct (Z.eqb_spec (q - 16) (spZ regs0 - 160 - (spZ regs0 - 160) mod 32 - 16)); [slia|].
      exact Hw16. }
    (* the value's all-granted trace at the entry cursor IS parse_items' at the call cursor (vrd_gtrace_cont) *)
    assert (EG : prhPv_gtrace d (rest_atR tb text p) = prhPi_gtrace d false (rest_atR tb text p'))
      by (rewrite Hrest, Hsk; exact (vrd_gtrace_cont d 91 yy (rest_atR tb text p) false Hsk eq_refl)).
    eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    (* THE CALL of parse_items, by the engine's BUDGETED caller-window rule over R (YCbqGwild.aj_call_xWFb_spR at
       wle' segs RZ_cf, P := the text's budget wbudget CW 0): the dispatch journal is the budget-free one (WS0 = []),
       the callee's post (tparse_items_specX: SRr' segs RZ_cf, fpostWFbm) brings its own wild budget WS1 back *)
    { eapply (YCbqGwild.aj_call_xWFb_spR SEGS B prh_pst ARx LAWS pa_segs_low (wle' SEGS YGcfRehidePost.RZ_cf)
        (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) W (va_env regs) _ ms
        (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
        ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp _ k [] (STK_parse_items d) (spZ regs0 + e - spZ regs) (rd_fp q v)
        (spZ regs - (spZ regs0 + e)) _ ch1 (YCbqGwild.wbudget CW 0) _ HS eq_refl HJ).
      - unfold spZ at 1. rewrite P2. fold (spZ regs). slia.
      - rewrite Rregs. Z.div_mod_to_equations. lia.
      - rewrite Rregs. slia.
      - exact HSTKi.
      - rewrite Rregs. clear - HSTK Hr16 Hm32. Z.div_mod_to_equations. lia.
      - rewrite Rregs. slia.
      - rewrite Rregs. Z.div_mod_to_equations. lia.
      - slia.
      - rewrite P3, (EW 3%nat (3%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R3. exact Hgp0.
      - rewrite P4, (EW 4%nat (4%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R4. exact Htp0.
      - exact P1.
      - apply (ret_ok_codeptr_v (PI := PI_prog_A)); [slia | reflexivity].
      - rewrite EB. unfold A_prog_base. rewrite unsigned_lit_small by slia. slia.
      - replace (spZ regs0 + e + (spZ regs - (spZ regs0 + e))) with (spZ regs) by slia. rewrite Hs0. exact Hach.
      - intros HPRE1 _.
        cbn [ss_pc setpc].
        assert (EM : ms_mem ms = mem).
        { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
          unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
        assert (Esp2 : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
        refine (HPI ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1
          (spZ regs0 + e - spZ regs) q text len p' tb v false Lam peak cnt fail ran
          most own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
        (* 1 fpre: the call rule's afn_pre_x, the read-only view, and the caller-frame bound *)
        { split; [exact HPRE1|]. split; [intros a H1 H2 H3; rewrite KM; exact (Hrod a H1 H2 H3)|].
          assert (Ehi : ly_stk_hi ly = ly_stk_hi ly0)
            by (exact (vly_stk_hi HLY0)).
          split; [rewrite Esp2, Rregs, Ehi; clear - Hshi He0 Hm32; slia|].
          (* fpre's ra bound (the cut's PRH_Base.v fpre): the return address is the jal's own return pc *)
          unfold raZ at 1. rewrite P1, EB. rewrite unsigned_lit_small by (unfold A_prog_base; slia).
          split; [exact vrd_ret217_lt_ceil | exact Hfrm]. }
        (* 1b memnorm at entry (the cut's tparse_items_specX): the call memory is the dispatch memory, and srr_inv_mn
           reads memnorm off P *)
        { rewrite EM. exact (PM mem HPm). }
        (* 2 the call context *)
        { unfold raZ at 1. rewrite P1, EB. rewrite unsigned_lit_small by (unfold A_prog_base; slia).
          rewrite Hspine.
          replace (A_prog_base + 19596) with (A_prog_base + 4 * Z.of_nat (A_prog_slot AS_parse_value + 215))
            by (vm_compute; reflexivity).
          exact HCTX. }
        (* 3 the universe closure: the body's *)
        { exact Hclos. }
        (* 4 the chain half of the cursor facts at the call state (vrd_cur_entry_call) *)
        { rewrite EMc0. exact HCURc. }
        (* 4b the cursor's free-trace words named in CW, at the call state (vrd_cur_entry_call's second half) *)
        { rewrite EMc0. exact HCWc. }
        (* 5 the entry chain at the call view *)
        { exists ch1. split; [rewrite Esp2, Hs0; exact Hach | rewrite Hspine; reflexivity]. }
        (* 6 the cursor chain at the call sp, by vrd_cur_chain_call *)
        { right. split; [rewrite Esp2, Rregs; slia|].
          assert (HS0 : prh_s0 F_parse_string q = q) by (unfold prh_s0; rewrite Hs0str; slia).
          rewrite HS0, EMc0.
          destruct (HQW F_parse_string (or_introl eq_refl) HS0) as ((w16 & Hw16 & Hw16c) & Hw8).
          pose proof (vastk HJstk) as (_ & _ & _ & _ & _ & _ & _ & Htopx & _).
          apply (vrd_cur_chain_call ly (w_H W) mem (spZ (ms_regs ms)) q w16);
            try exact Hw16; try exact Hw16c; try exact Hw8; try exact Iq8; try (rewrite Esp2, Rregs; slia); slia. }
        (* 7, 8, 9 the argument registers *)
        { rewrite P10, (EW 20%nat (20%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R20. }
        { rewrite P11, (EW 19%nat (19%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R19. }
        { rewrite P12. reflexivity. }
        (* 10 rd_pre at the call *)
        { rewrite EM.
          assert (Hd16 : (spZ regs0 - spZ regs) mod 16 = 0) by (rewrite Rregs; Z.div_mod_to_equations; lia).
          replace (spZ regs0 + e - spZ regs) with (e + (spZ regs0 - spZ regs)) by slia.
          split; [exact Hfrm|]. split; [exact Hmu|]. split; [exact Hr1|]. split; [exact Hr2|].
          split; [exact Hin|].
          split.
          { apply (vrd_fwin_shift ly W regs0 (ms_regs ms) mem e (spZ regs0 - spZ regs) Hfw); [slia | slia | exact Hd16 |].
            intros a Ha. apply HJpres0. rewrite Rregs in Ha. slia. }
          split; [slia|]. split; [slia|].
          split; [exact Hraq|]. split; [exact Hsrc|]. split; [exact Hhome|]. split; [exact Hmax|].
          split; [apply (vrd_node_shift B (STK_parse_value d) (STK_parse_items d) e (spZ regs0 - spZ regs)
                    ly S W regs0 (ms_regs ms) mem Lam v Hnode); [slia | slia | rewrite Rregs; slia]|].
          split; [exact Hqv|]. split; [exact Htv|].
          split.
          { pose proof (vnd_own Hnode) as Hown.
            destruct Hvwin as [Hv1 | Hv1]; [left | right; slia].
            destruct (Z_le_gt_dec (v + 56) (spZ regs0 - STK_parse_value d)) as [Hle|Hgt]; [slia|].
            exfalso. destruct (Hown (v + 55) ltac:(slia)) as [_ Hn]. apply Hn. slia. }
          split; [exact Hled|].
          split; [pose proof (vin_d32 Hin) as Hd32; unfold PjGrammar.MAXD; slia|].
          exact (conj Hcnt HTC). }
        (* 11, 12 the opener *)
        { exact Hplt. }
        { exact Hnth. }
        (* 13 the room, by vrd_gtrace_cont *)
        { rewrite <- EG. exact Hroom. }
        (* 13b the wild room at the call state: the entry's (tparse_value_specX's, which vrd_disp_body carries at S0),
           since the dispatch moves only fake frames (S = set_fs f S0, so st_depot S is st_depot S0 by conversion) *)
        { destruct Hsetfs as (fz & Efz). rewrite Efz. exact HWR0. }
        (* 14, 15 the live counts along the granted events: tparse_value_specX's entry counts, which vrd_disp_body
           carries at S0, at parse_items' own trace (EG); the dispatch state is S0 with only its fake frames moved
           (`S = set_fs f S0`), and rs_live (room_of_cf _) reads no fake frame, so it is the same list *)
        { rewrite <- EG. destruct Hsetfs as (fz & Efz). rewrite Efz.
          change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
            with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)).
          exact HC0s. }
        { rewrite <- EG. destruct Hsetfs as (fz & Efz). rewrite Efz.
          change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
            with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)).
          exact HC024. }
        (* 15b the hull budget at the call state, as in the object case *)
        { rewrite <- EG. destruct Hsetfs as (fz & Efz). rewrite Efz.
          exact (PresetHullBudget.hull_budget_same S0 (set_fs fz S0) _
                   (YGcfSecsStep.secs_same_of_secs S0 (set_fs fz S0) eq_refl) HHB). }
        (* 15 the chain from parse_items' s0 *)
        { assert (HS0 : prh_s0 F_parse_items q = q) by (unfold prh_s0; rewrite Hs0items; slia).
          rewrite HS0, EMc0.
          destruct (HQW F_parse_items (or_intror eq_refl) HS0) as ((w16 & Hw16 & Hw16c) & Hw8).
          pose proof (pi_frame_nonneg F_parse_items) as Hpf.
          pose proof (vastk HJstk) as (_ & _ & _ & _ & _ & _ & _ & Htopx & _).
          apply (vrd_cur_chain_call ly (w_H W) mem (spZ (ms_regs ms) - pi_frame F_parse_items) q w16);
            try exact Hw16; try exact Hw16c; try exact Hw8; try exact Iq8; try (rewrite Esp2, Rregs; slia); slia. }
        (* 15 the frames headroom *)
        { exact Hfrb. }
      - intros a Ha. left. exact Ha. }
    cbv beta. intros W2 c2 HW2
      (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ2 & HJc & HWIN & HP2 & HQ).
    (* the caller's journal over the call carries the callee's wild budget WS1 ([] ++ WS1): rows 217..225 run on its
       REBASED form (YCbqGwild.ajournal_xw_rebaseR: the entry depot moved to the call's, budget []), and the end
       journal is folded back with the composed journal's wild-part inclusion (YCbqGwild.ajournal_xw_unbase0R), all at
       wle' segs RZ_cf *)
    pose proof (ajxR_wild HJ2) as HWild2. cbn [app] in HWild2.
    apply (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx) in HJ2.
    (* rows 217 (`j` to row 224) and 224 (`mv s5, a0`): a fresh symbolic state at the return site, at fx2 *)
    pose proof (va_entry (fx := fx2) W2 regs2 mem2 (vrd_row 217)) as HS2.
    rewrite EB in HS2.
    replace (pa_val A_TEXT + 19596) with (A_prog_base + vrd_row 217) by (rewrite EB; reflexivity).
    assert (HEI2 : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (va_env regs2)) by (unfold va_env; apply Eimg_env).
    assert (SHOK2 : sh_ok SEGS (SLit 0) [] (va_env regs2) (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
    pose (RUNTO2 := paj_run_to_xR (fx := fx2) (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS
      (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    paj_run_to_tok_xR RUNTO2 HS2 HJ2 SHOK2 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (vrd_row 225).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    pmkst HS2.
    prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (26%bv : bv 5) Q26.
    prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
    assert (EW2 : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                    ew (va_env regs2) n = getr regs2 r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
    assert (EM2 : ms_mem ms0 = mem2).
    { apply functional_extensionality. intros x. apply HF0. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (EMc : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    pose proof (ajxR_ly HJc) as HLY.
    assert (EF : ly_F ly2 = ly_F ly) by (exact (vly_F HLY)).
    assert (Efr : frame_addr ly2 0 pos = frame_addr ly 0 pos) by (unfold frame_addr; rewrite EF; reflexivity).
    assert (Efl : flag_addr ly2 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite EF; reflexivity).
    assert (KS8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HP2 8); unfold acallee_saved; slia).
    assert (KS18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HP2 18); unfold acallee_saved; slia).
    assert (KS26 : getr regs2 26 = getr (ms_regs ms) 26) by (apply (HP2 26); unfold acallee_saved; slia).
    assert (KS24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HP2 24); unfold acallee_saved; slia).
    assert (KS3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HP2 3); unfold acallee_saved; slia).
    assert (KS4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HP2 4); unfold acallee_saved; slia).
    (* parse_items' post (PRH_FnParse.v tparse_items_specX), read BY NAME through the kit's projection layer: fQmn's
       two parts (the post and the memnorm keep), then tpiP_R_of gives the outcomes in the text's binder order and the
       record tpiP_R, whose fields name the conjuncts. md2 is the one argument of the post that its body does not
       mention, so it is given by name. *)
    destruct HQ as (HQb & Hmk).
    apply tpiP_R_of with (md' := md2) in HQb.
    destruct HQb as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HRi).
    pose proof (tpiP_run HRi) as Hjr. pose proof (tpiP_ledger HRi) as Hled2. pose proof (tpiP_room HRi) as Hroom2.
    pose proof (tpiP_live HRi) as Hlv2. pose proof (tpiP_pos HRi) as Hrp2. pose proof (tpiP_ledger_move HRi) as Hmove.
    pose proof (tpiP_blocks_move HRi) as Hbm. pose proof (tpiP_bytes HRi) as Hbb. pose proof (tpiP_lsum HRi) as Hlh.
    pose proof (tpiP_arm HRi) as Hres. pose proof (tpiP_hull HRi) as Hhu2.
    (* P across the call: the m-form post's memnorm keep and srr_inv_call; the run to row 225 writes no memory *)
    assert (HPc : P (ms_mem ms)) by (rewrite EMc; exact HPm).
    assert (HPr : P (ms_mem ms0)) by (rewrite EM2; exact (PC (ms_mem ms) mem2 Hmk HPc)).
    assert (Hrv : getr regs2 10 = w64 (match res with Some _ => 0 | None => -1 end))
      by (destruct res as [[t r]|]; cbv beta iota in Hres;
          [exact (tpiPs_ret (tpiP_RSome_of Hres)) | exact (tpiPn_ret (tpiP_RNone_of Hres))]).
    apply (SRrG_ret SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf)).
    split; [|exact HPr]. unfold vrd_arm_exitR.
    exists fx2, pos, (match res with Some _ => 0 | None => -1 end).
    (* the join BY NAME: VrdNum's record vrd_epi_R at the join's witnesses (vrd_epi_aR_of_R), one named goal per field *)
    apply vrd_epi_aR_of_R with (regs := ms_regs ms0) (mem := ms_mem ms0)
      (md := with_vm_backing (m_vm_lazy md2) mat0 md2) (ly := ly2) (S := S2) (Hp := Hp2) (k := k + k1).
    refine {| vepi_cfg := ?[e_cfg]; vepi_jrn := ?[e_jrn]; vepi_win := ?[e_win]; vepi_s0 := ?[e_s0]; vepi_s2 := ?[e_s2];
              vepi_s10 := ?[e_s10]; vepi_s8 := ?[e_s8]; vepi_s5 := ?[e_s5]; vepi_gp := ?[e_gp]; vepi_tp := ?[e_tp];
              vepi_ra := ?[e_ra]; vepi_saved := ?[e_saved]; vepi_flag := ?[e_flag]; vepi_frm := ?[e_frm];
              vepi_fregs := ?[e_fregs]; vepi_rq := ?[e_rq] |}.
    [e_cfg]: { rewrite vrd_pc_epi; reflexivity. }
    (* the join's journal at wle' segs RZ_cf: the callee's budget WS1, which its post bounds by wbudget CW 0 (HPW) *)
    [e_jrn]: { exists WS1. split; [|exact HPW].
      eapply (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx); [exact HJ2 | exact HWild2]. }
    [e_win]: { intros a Ha Hn. rewrite EM2, (HWIN a ltac:(slia) Hn), EMc. exact (Hwin a Ha Hn). }
    [e_s0]: { rewrite Q8, (EW2 8%nat (8%bv : bv 5)) by va_cs; rewrite KS8; rewrite P8; exact R8. }
    [e_s2]: { rewrite Efr, Q18, (EW2 18%nat (18%bv : bv 5)) by va_cs; rewrite KS18;
              rewrite P18, (EW 18%nat (18%bv : bv 5)) by va_cs; exact R18. }
    [e_s10]: { rewrite Efr, Q26, (EW2 26%nat (26%bv : bv 5)) by va_cs; rewrite KS26;
               rewrite P26, (EW 26%nat (26%bv : bv 5)) by va_cs; exact R26. }
    [e_s8]: { rewrite Efr, Q24, (EW2 24%nat (24%bv : bv 5)) by va_cs; rewrite KS24;
              rewrite P24, (EW 24%nat (24%bv : bv 5)) by va_cs; exact R24. }
    [e_s5]: { rewrite Q21, (EW2 10%nat (10%bv : bv 5)) by va_cs; exact Hrv. }
    [e_gp]: { rewrite Q3, (EW2 3%nat (3%bv : bv 5)) by va_cs; rewrite KS3;
              rewrite P3, (EW 3%nat (3%bv : bv 5)) by va_cs; exact R3. }
    [e_tp]: { rewrite Q4, (EW2 4%nat (4%bv : bv 5)) by va_cs; rewrite KS4;
              rewrite P4, (EW 4%nat (4%bv : bv 5)) by va_cs; exact R4. }
    [e_ra]: exact Hra0.
    (* the thirteen spilled words: parse_value's own frame below spZ regs0, outside rd_fp q v (the cursor is above
       spZ regs0, the node outside parse_value's stack window), kept by the callee's window clause and both runs *)
    [e_saved]: { assert (KSV : forall a, spZ regs0 - 104 <= a < spZ regs0 ->
                aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
      { intros a Ha. rewrite EM2. rewrite (HWIN a); [rewrite EMc; reflexivity | rewrite Rregs; slia |].
        intros (r & Hrin & Hr). cbn [rd_fp In] in Hrin.
        destruct Hrin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; [slia | slia |].
        pose proof (vnd_own Hnode) as Hown.
        destruct (Hown a Hr) as [_ Hn]. apply Hn. slia. }
      unfold vrd_saved in Hsaved |- *.
      destruct Hsaved as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (eapply val_mem_kept; [|eassumption]; intros kk Hk; cbn in Hk; apply KSV; slia). }
    (* the flag word at F + 56: it lies in parse_value's OWN fake frame, which is below alloc_ceiling, and outside the
       callee's footprint rd_fp q v (the cursor is a stack address above alloc_ceiling; the node cannot meet the frame:
       a block is apart from a frame, another frame is apart from this one, and this frame itself would put the
       descriptor word at F + 16 inside the node's 56 ZEROED bytes). So the callee's journal frames clause keeps it. *)
    [e_flag]: { rewrite Efr, Efl.
      pose proof (ajx_ar HJ0) as HAR. cbv beta in HAR.
      assert (HinF : In (0, pos) (frames S)) by (rewrite Hfr; left; reflexivity).
      destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HFa0 & HFc & HFapp).
      assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFc.
      pose proof (vfrm3 Hframe) as (Hmag & Hsig & Hflag).
      pose proof (vnd_v4096 Hnode) as Hv4096. pose proof (vnd_al8 Hnode) as Hval8. pose proof (vnd_rw Hnode) as Hrw. pose proof (vnd_zero Hnode) as Hzero. pose proof (vnd_at Hnode) as Hat. pose proof (vnd_amr Hnode) as Hamr. pose proof (vnd_own Hnode) as Hown. pose proof (vnd_ra Hnode) as Hra8.
      pose proof (@cf_head_nonneg cp) as Hhd0.
      assert (HvF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> ~ (v <= a < v + 56)).
      { intros a Ha Hav.
        destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                        [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
        - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
          pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
          apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (a0 - cf_head) (k0 + cf_head) a HAR HinF Habk);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hk0h : 0 <= k0 + cf_head) by slia.
          pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq). slia.
        - apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) b0 m0 a HAR HinF Hinb);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hm00 : 0 <= m0) by slia.
          pose proof (req_size_pos m0 Hm00) as (_ & Hrq). slia.
        - rewrite Hfr in Hinf. destruct Hinf as [Ef | Hinf].
          + injection Ef as <- <-.
            assert (Hz16 : val_mem SEGS (mrestrict (w_H W) mem) (frame_addr ly 0 pos + 16) 8 0).
            { apply (vrd_zero_val SEGS (mrestrict (w_H W) mem) v); [exact Hzero | rewrite Hfb in Hhif; slia | rewrite Hfb in Hhif; slia]. }
            pose proof (Hsig 0%nat ltac:(slia)) as E1. pose proof (Hz16 0%nat ltac:(slia)) as E2.
            cbn [Z.of_nat] in E1, E2. rewrite Z.add_0_r in E1, E2.
            rewrite E1 in E2. vm_compute in E2. discriminate E2.
          + apply in_split in Hinf as (l2 & l3 & El).
            pose proof (sep_frames_pos_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (cid, pos') (@nil (Z * Z)) l2 l3 HAR
              ltac:(rewrite Hfr, El; reflexivity)) as Hd.
            unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Hfb in Hd. slia.
        - slia. }
      assert (HqF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> a < q).
      { intros a Ha. pose proof (vastk HJstk) as (_ & _ & Hclo2 & Hlo2 & _). slia. }
      assert (HnFP : forall a, frame_addr ly 0 pos + 56 <= a < frame_addr ly 0 pos + 64 -> ~ inFP (rd_fp q v) a).
      { intros a Ha (r & Hrin & Hr). cbn [rd_fp In] in Hrin.
        destruct Hrin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr;
        [pose proof (HqF a ltac:(slia)); slia | pose proof (HqF a ltac:(slia)); slia | exact (HvF a ltac:(slia) Hr)]. }
      pose proof (ajxR_frm HJc) as HJfr.
      eapply val_mem_kept; [|exact Hflag]. intros kk Hk. cbn in Hk.
      rewrite EM2, <- EMc.
      apply (HJfr 0 pos (frame_addr ly 0 pos + 56 + kk) HinF);
      [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia
      | apply HnFP; slia]. }
    [e_frm]: exact HFZ.
    [e_fregs]: exact HFK.
    (* RQ: parse_items' post read back as parse_value's (VnumC's vrd_pv_post), BY NAME: VrdNum's record vrd_pv_R
       (vrd_pv_post_of_R), one named goal per field. The outcomes, the trace and the blocks are parse_items'
       (vrd_cont_model; the granted traces by EG); the entry state S0 is the call state S up to its fake frames
       (`S = set_fs f S0`), which neither the live list nor the run position reads *)
    [e_rq]: {
      rewrite EM2.
      apply vrd_pv_post_of_R with (ok := ok) (res := res) (tr := tr) (okr := okr) (D := D) (Lam' := Lam')
        (peak' := peak') (cnt' := cnt') (fail' := fail') (ran' := ran').
      pose proof (vrd_rest_shrink tb text p p' (proj1 Hpp)) as Hshr.
      (* the value's free order at the entry cursor IS parse_items' at the call cursor (vrd_frees_cont) *)
      assert (EFR : prhPv_frees d (rest_atR tb text p) ok = prhPi_frees d false (rest_atR tb text p') ok)
        by (rewrite Hrest, Hsk; exact (vrd_frees_cont d (rest_atR tb text p) ok 91 yy false Hsk eq_refl)).
      pose proof (vbm_new Hbm) as Hb1. pose proof (vbm_blocks Hbm) as Hb2. pose proof (vbm_frames Hbm) as Hb3. pose proof (vbm_peak Hbm) as Hb4.
      destruct Hsetfs as (fz & Efz).
      refine {| vpv_run := ?[p_run]; vpv_ledger := ?[p_ledger]; vpv_room := ?[p_room]; vpv_hull := ?[p_hull];
                vpv_live := ?[p_live]; vpv_pos := ?[p_pos]; vpv_outcome := ?[p_outcome]; vpv_injected := ?[p_injected];
                vpv_ledger_move := ?[p_ledger_move]; vpv_fresh := ?[p_fresh]; vpv_blocks := ?[p_blocks];
                vpv_frames := ?[p_frames]; vpv_hpeak := ?[p_hpeak]; vpv_bytes := ?[p_bytes]; vpv_lsum := ?[p_lsum];
                vpv_arm := ?[p_arm] |}.
      [p_run]: { rewrite (vrd_cont_model ReaderRes.jr_strtod d 91 yy (rest_atR tb text p) ok false Hsk eq_refl), <- Hsk,
          <- Hrest.
        exact Hjr. }
      [p_ledger]: exact Hled2.
      [p_room]: exact Hroom2.
      (* the hull use: parse_items' own from the call state S, which has S0's st_secs (`S = set_fs f S0`) *)
      [p_hull]: { rewrite EG.
        assert (HSS : PresetHullBudget.hull_used S0 S [])
          by (apply PresetHullBudget.hull_used_secs; rewrite Efz; reflexivity).
        exact (PresetHullBudget.hull_used_app S0 S S2 [] _ HSS Hhu2). }
      [p_live]: { rewrite Efz in Hlv2.
        change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
          with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) in Hlv2.
        exact Hlv2. }
      [p_pos]: { intros sm x os i Hz0 hist Hpos Hrun.
        assert (HposS : PresetRoomPos.iface_room_pos sm x os i Hz0 hist S)
          by (rewrite Efz; apply PresetRoomPosKeep.room_pos_set_fs; exact Hpos).
        exact (Hrp2 sm x os i Hz0 hist HposS Hrun). }
      [p_outcome]: { intros sm x os i Hz0 hist Hpos Hrun Hcons Hfail. rewrite EG in Hrun, Hcons, Hfail |- *.
        assert (HposS : PresetRoomPos.iface_room_pos sm x os i Hz0 hist S)
          by (rewrite Efz; apply PresetRoomPosKeep.room_pos_set_fs; exact Hpos).
        split; [exact (tpiP_outcome_ran HRi HposS Hrun Hcons Hfail)|].
        split; [|exact (tpiP_outcome_pos HRi HposS Hrun Hcons Hfail)].
        rewrite (vrd_cont_model ReaderRes.jr_strtod d 91 yy (rest_atR tb text p) [] false Hsk eq_refl), <- Hsk, <- Hrest.
        exact (tpiP_outcome_run HRi HposS Hrun Hcons Hfail). }
      (* the injected reading: parse_items' own (tpiP_injected) at the call state. Under the model's grant list the
         value's events are parse_items' at the opener (vrd_cont_model), and the value's window is parse_items' (EG) *)
      [p_injected]: { intros sm x os i Hz0 hist Hpos Hrun Hcons Hwd. rewrite EG in Hwd.
        rewrite (vrd_cont_model ReaderRes.jr_strtod d 91 yy (rest_atR tb text p) (PresetReqAt.okk (Z.to_nat (fail - cnt)))
          false Hsk eq_refl), <- Hsk, <- Hrest in Hrun, Hcons.
        assert (HposS : PresetRoomPos.iface_room_pos sm x os i Hz0 hist S)
          by (rewrite Efz; apply PresetRoomPosKeep.room_pos_set_fs; exact Hpos).
        exact (tpiP_injected HRi HposS Hrun Hcons Hwd). }
      [p_ledger_move]: { rewrite EG; exact Hmove. }
      [p_fresh]: { rewrite <- Hab; exact Hb1. }
      [p_blocks]: { rewrite <- Hab; exact Hb2. }
      [p_frames]: { rewrite <- Hfr; exact Hb3. }
      [p_hpeak]: slia.
      [p_bytes]: { rewrite (blocks_bytes_bsum B ly0 S0), <- Hab, <- (blocks_bytes_bsum B ly S). exact Hbb. }
      [p_lsum]: exact Hlh.
      [p_arm]: {
        destruct res as [[t r]|].
        + (* the granted arm of parse_items' post, BY NAME (tpiP_RSome), read into the value's (vrd_pv_RSome) *)
          cbv beta iota in Hres. apply tpiP_RSome_of in Hres.
          pose proof (tpiPs_in_ok Hres) as HsA. pose proof (tpiPs_node Hres) as HsB.
          pose proof (tpiPs_lsum_le Hres) as HsC. pose proof (tpiPs_freeord Hres) as HsF.
          pose proof (tpiPs_ncap Hres) as HsN. clear Hres.
          refine {| vpvs_rv := ?[s_rv]; vpvs_freeord := ?[s_freeord]; vpvs_in_ok := ?[s_in_ok]; vpvs_node := ?[s_node];
                    vpvs_ncap := ?[s_ncap]; vpvs_lsum_le := ?[s_lsum_le] |}.
          [s_rv]: reflexivity.
          [s_freeord]: { intros Hhd n Hn. rewrite EFR. exact (HsF Hhd n Hn). }
          [s_in_ok]: exact HsA.
          [s_node]: exact HsB.
          [s_ncap]: exact HsN.
          [s_lsum_le]: slia.
        + (* the refused arm of parse_items' post, BY NAME (tpiP_RNone), read into the value's (vrd_pv_RNone) *)
          cbv beta iota in Hres. apply tpiP_RNone_of in Hres.
          pose proof (tpiPn_in_after Hres) as HnA. pose proof (tpiPn_fd Hres) as HnB.
          pose proof (tpiPn_freeord Hres) as HnF. clear Hres.
          refine {| vpvn_rv := ?[n_rv]; vpvn_freeord := ?[n_freeord]; vpvn_in_after := ?[n_in_after];
                    vpvn_fd := ?[n_fd] |}.
          [n_rv]: reflexivity.
          [n_freeord]: { intros Hhd n Hn. rewrite EFR. exact (HnF Hhd n Hn). }
          (* the cursor's depth bound widens from d + 1 to d: pj_in_afterR's own body (PRH_Reader.v) *)
          [n_in_after]: { destruct HnA as (p2 & d2 & HnA'). decompose [and] HnA'. exists p2, d2.
            repeat split; try assumption; slia. }
          [n_fd]: exact HnB. }
    }
Qed.

(* the instance P := memnorm (P := True is not one: srr_inv_mn at True is false). srr_inv_call and srr_inv_mn hold
   at memnorm by their definitions. *)
Theorem vrd_cont_aLC_holds : forall d CTX CTX0 CW, vrd_cont_aLC B ARx SK d CTX CTX0 CW.
Proof.
  intros d CTX CTX0 CW ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran
    most own W c o b yy HPI HFP HD HHB Hsk Hb HCTX HSTK HSTKi Hs0str Hs0items HMN.
  exact (vrd_cont_aLC_P_holds (YAkMemnorm.memnorm SEGS) d CTX CTX0 CW
    (fun m m' Hk Hm => Hk Hm) (fun m Hm => Hm)
    ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran
    most own W c o b yy HPI HFP HD HHB Hsk Hb HCTX HSTK HSTKi Hs0str Hs0items HMN).
Qed.
End p.


(* ---------------------------------------------------------------------------------------------------- *)
(* 6. THE LITERAL ARM, PROVED (the three keywords: "true" entry row 218, "false" row 119, "null" row 152). The *)
(*    walk: the run of the arm's rows to `jal literal` (row 223); VstrC's vrd_call_W; the kit's tliteral_specX with  *)
(*    its 26 premises (the keyword's bytes at the dispatch state, vrd_lit_aLC's premise); the chain at the call   *)
(*    view by VproC's vrd_disp_chain; the run of row 224 to row 225; vrd_epi_a there with RQ = VnumC's           *)
(*    vrd_pv_post: no allocation (S' = S, the ledger unchanged, D = [], lit's trace []), the hit arm's node by    *)
(*    pj_hdrR (type word from the post, the six other words zero from the dispatch's pj_zeroR kept by the callee *)
(*    journal's block / frame clauses), the miss arm's by VnumC's vrd_zero_fd.                                  *)
(*    SPEED (for every walk of this size): before the epilogue's many lia calls, the big hypotheses the rest     *)
(*    does not use (the callee text, the chains, the closure, the arodata view, the cursor-word facts) are       *)
(*    cleared, and the side-condition tactic runs lia on an EMPTY context. Without that the same proof ran over  *)
(*    60 minutes; with it, all three cases build in about 13 minutes.                                           *)
(* ---------------------------------------------------------------------------------------------------- *)

Section pl.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.


Theorem vrd_lit_aLC_P_holds : forall P d CTX0 CW, vrd_lit_aLC_P B ARx SK P d CTX0 CW.
Proof.
  intros P d CTX0 CW. unfold vrd_lit_aLC_P. intros PC.
  intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran most own
    W c b ty yy cw slack
    HPI HFP HD Hsk Hbty Hkw Hw63 Hnul Hslack Hwstk HSTK HSTKi HP0.
  destruct (vdispa B ARx SK HD) as (arm & pos & p' & k & ly & S & Hp & regs & mem & md & Hc & HB).
  (* vrd_disp_body's conjuncts BY SHAPE, never by position (VrdPro.v grew twice: fe6f39ebc742 replaced one conjunct by four, the
     cut interface (f5eb8e2e6bbf, green at e942c5680fa7) appended three;
     a positional pattern over a body that grew binds its names to the wrong conjuncts and swallows the new ones):
     decompose [and], then each conjunct this walk reads is named by its type. The two string-arm counts stay
     unnamed: neither arm reads them. *)
  unfold vrd_disp_body in HB. decompose [and] HB. clear HB.
  lazymatch goal with X : rest_atR tb text p' = PjGrammar.skip (rest_atR tb text p) |- _ => rename X into Hrest end.
  lazymatch goal with X : p <= p' |- _ => rename X into Hpp1 end.
  lazymatch goal with X : p' <= text + len |- _ => rename X into Hpp2 end.
  assert (Hpp : p <= p' <= text + len) by (split; assumption).
  lazymatch goal with X : match PjGrammar.skip (rest_atR tb text p) with _ => _ end |- _ => rename X into Hmatch end.
  lazymatch goal with X : context [ajournal_x] |- _ => rename X into HJ end.
  lazymatch goal with X : frames S = _ |- _ => rename X into Hfr end.
  lazymatch goal with X : ablocks B ly S = ablocks B ly0 S0 |- _ => rename X into Hab end.
  lazymatch goal with X : Hp = Hp0 |- _ => rename X into HHp end.
  lazymatch goal with X : exists _, S = set_fs _ S0 |- _ => rename X into Hsetfs end.
  lazymatch goal with X : forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a -> _ |- _ =>
    rename X into Hwin end.
  lazymatch goal with X : context [fwin] |- _ => rename X into Hfw end.
  lazymatch goal with X : context [vrd_frame] |- _ => rename X into Hframe end.
  lazymatch goal with X : context [vrd_saved] |- _ => rename X into Hsaved end.
  lazymatch goal with X : context [vrd_regs] |- _ => rename X into Hregs end.
  lazymatch goal with X : exists _, achain ly0 _ (spZ regs0) (s0Z regs0) _ /\ _ |- _ => rename X into Hchain0 end.
  lazymatch goal with X : context [prh_univ_closure] |- _ => rename X into Hclos end.
  lazymatch goal with X : context [prh_cur_entry] |- _ => rename X into Hcur end.
  lazymatch goal with X : (spZ regs0 <= q < spZ regs0 + 16) \/ _ |- _ => rename X into Hcurch end.
  lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W) mem) q text len p' _ tb |- _ => rename X into Hin end.
  lazymatch goal with X : range_addressable (aview _ (w_H W) mem) SHADOW_OFF q 24 |- _ => rename X into Hraq end.
  lazymatch goal with X : context [prhPv_node] |- _ => rename X into Hnode end.
  lazymatch goal with X : context [prh_malloc_univ] |- _ => rename X into Hmu end.
  lazymatch goal with X : spZ regs0 <= q |- _ => rename X into Hq1 end.
  lazymatch goal with X : q + 24 <= spZ regs0 + e |- _ => rename X into Hq2 end.
  lazymatch goal with X : q + 24 <= v \/ v + 56 <= q |- _ => rename X into Hqv end.
  lazymatch goal with X : getr regs0 _ = w64 (as_gp _) |- _ => rename X into Hgp0 end.
  lazymatch goal with X : getr regs0 _ = w64 (as_tp _) |- _ => rename X into Htp0 end.
  lazymatch goal with X : YK0s.ret_ok _ |- _ => rename X into Hra0 end.
  lazymatch goal with X : 4096 <= raZ regs0 |- _ => rename X into Hra4k end.
  lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W0) mem0) q text len p _ tb |- _ => rename X into Hin0 end.
  lazymatch goal with X : (d <= PjGrammar.MAXD)%nat |- _ => rename X into HMAXD end.
  lazymatch goal with X : 0 < len -> _ |- _ => rename X into Htv end.
  lazymatch goal with X : v + 56 <= spZ regs0 \/ spZ regs0 + e <= v |- _ => rename X into Hvwin end.
  lazymatch goal with X : In [cf_pc_realloc_ra0] _ |- _ => rename X into Hr1 end.
  lazymatch goal with X : In (prh_trace _ _ _) _ |- _ => rename X into Hr2 end.
  lazymatch goal with X : Z.of_nat (PjRoundTrip.maxrun tb) < _ |- _ => rename X into Hmax end.
  lazymatch goal with X : cnt + 2 * Z.of_nat (length (rest_atR tb text p')) + 2 < _ |- _ => rename X into Hcnt end.
  lazymatch goal with X : context [src_rd] |- _ => rename X into Hsrc end.
  lazymatch goal with X : context [prhReader_home] |- _ => rename X into Hhome end.
  lazymatch goal with X : context [prh_ledger] |- _ => rename X into Hled end.
  lazymatch goal with X : context [rd_room] |- _ => rename X into Hroom end.
  lazymatch goal with X : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req
                              (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) _) <= _ |- _ => rename X into HC0s end.
  lazymatch goal with X : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls _)
                              (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) _) <= _ |- _ => rename X into HC024 end.
  lazymatch goal with X : Z.of_nat (length (frames S)) + _ <= fs_frames 0 |- _ => rename X into Hfrb end.
  lazymatch goal with X : context [PresetRodata.arodata_okP] |- _ => rename X into Hrod end.
  lazymatch goal with X : frm_zero _ |- _ => rename X into Hfrm end.
  (* the three conjuncts the cut's dispatch text appends (VrdPro.v at a Theorem Labs lane's cut interface f5eb8e2e6bbf):
     the free-trace words of the cursor named in CW, the wild room CW leaves at the entry depot, and the text below
     the ceiling. Named by type like the rest. *)
  lazymatch goal with X : context [prh_cw_entry] |- _ => rename X into HCW end.
  lazymatch goal with X : context [YCbqGwild.wild_room] |- _ => rename X into HWR0 end.
  lazymatch goal with X : text + len < YM05.alloc_ceiling |- _ => rename X into HTC end.
  repeat match goal with X : arm = VA_str -> _ |- _ => clear X end.
  (* fpre's last conjunct, the entry ra below the ceiling, BY NAME (tauto on fpre alone) *)
  assert (Hra0c : raZ regs0 < alloc_ceiling) by (clear - HFP; unfold fpre in HFP; tauto).
  rewrite Hsk in Hmatch. cbv beta iota in Hmatch. decompose [and] Hmatch. clear Hmatch.
  lazymatch goal with X : arm = vrd_arm_of _ |- _ => rename X into Harm end.
  lazymatch goal with X : p' < text + len |- _ => rename X into Hplt end.
  lazymatch goal with X : nth_error tb _ = Some _ |- _ => rename X into Hnth end.
  lazymatch goal with X : PjGrammar.ws _ = false |- _ => rename X into Hws end.
  lazymatch goal with X : getr regs 11 = w64 _ |- _ => rename X into H11 end.
  pose proof (vregs Hregs) as (Rsp & R9 & R8 & R18 & R26 & R19 & R20 & R21 & R22 & R25 & R23 & R24 & R27 & R3 & R4 & R10 & R12).
  pose proof (ajx_pres HJ) as HJpres1. pose proof (ajx_stk HJ) as HJstk0.
  subst c. unfold cfg_at.
  (* P of the dispatch memory (the arm's runs write no memory, so it is P at the call and at row 225's memory side) *)
  assert (HPm : P mem) by exact HP0.
  pose proof (va_entry W regs mem (A_prog_sigma AS_parse_value + vrd_arm_off arm - A_prog_base)) as HS.
  assert (EB : @pa_val _ A_prog_listing PI_prog_A A_TEXT = A_prog_base) by reflexivity.
  rewrite EB in HS.
  replace (A_prog_base + (A_prog_sigma AS_parse_value + vrd_arm_off arm - A_prog_base))
    with (A_prog_sigma AS_parse_value + vrd_arm_off arm) in HS by slia.
  change (w64 (pa_sigma AS_parse_value + vrd_arm_off arm)) with (Z_to_bv 64 (A_prog_sigma AS_parse_value + vrd_arm_off arm)).
  assert (HEI : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (va_env regs)) by (unfold va_env; apply Eimg_env).
  assert (SHOK : sh_ok SEGS (SLit 0) [] (va_env regs) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  pose proof (ajx_pres HJ) as HJpres0.
  pose (RUN := paj_run_x (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS).
  destruct Hbty as [(Hb & Hcw & Hty) | [(Hb & Hcw & Hty) | (Hb & Hcw & Hty)]]; subst b; subst cw; subst ty;
  cbn [vrd_arm_of Z.eqb] in Harm; subst arm; cbn [vrd_arm_off] in HS |- *.
  - paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    prreg HS (2%bv : bv 5) P2. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
    prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
    prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
    prreg HS (18%bv : bv 5) P18. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
    pose proof HJ as HJ0b.
    pose proof (vastk HJstk0) as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
    pose proof (vfw Hfw) as (He0 & He16 & Hetop & Hepres).
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(slia)) as Hm32.
    assert (Hr16 : spZ regs0 mod 16 = 0)
      by (rewrite Zplus_mod, He16, Z.add_0_r, Zmod_mod in Hsp16; exact Hsp16).
    (* the dispatch's alignment slack is 0 or 16 (spZ regs0 is 16-aligned), stated once for the slia calls below *)
    assert (Hsl16 : (spZ regs0 - 160) mod 32 <= 16) by (clear - Hr16 Hm32; Z.div_mod_to_equations; lia).
    assert (Hx : 0 <= spZ regs0 - 160 - (spZ regs0 - 160) mod 32 < 2 ^ 64) by slia.
    assert (Rregs : spZ regs = spZ regs0 - 160 - (spZ regs0 - 160) mod 32).
    { unfold spZ at 1. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by exact Hx. reflexivity. }
    assert (EW : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                   ew (va_env regs) n = getr regs r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
    rewrite (EW 2%nat (2%bv : bv 5)) in P2 by (vm_compute; reflexivity || slia).
    assert (KM : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
    { intros a. symmetry. unfold aview. f_equal. unfold mbyte.
      rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    (* ---- the facts every chain lemma of VproC asks, gathered once ---- *)
    pose proof HJstk0 as HJstk.
    pose proof (vin_p Hin0) as I0p. pose proof (vin_end Hin0) as I0e. pose proof (vin_d Hin0) as I0d. pose proof (vin_rw Hin0) as I0rw. pose proof (vin_q8 Hin0) as I0q8. pose proof (vin_t Hin0) as I0t. pose proof (vin_tl Hin0) as I0tl. pose proof (vin_pp Hin0) as I0pp. pose proof (vin_len Hin0) as I0len. pose proof (vin_g Hin0) as I0g. pose proof (vin_qt Hin0) as I0qt. pose proof (vin_d32 Hin0) as I0d32.
    pose proof (vin_p Hin) as Ip. pose proof (vin_end Hin) as Ie. pose proof (vin_d Hin) as Id. pose proof (vin_rw Hin) as Irw. pose proof (vin_q8 Hin) as Iq8. pose proof (vin_t Hin) as It. pose proof (vin_tl Hin) as Itl. pose proof (vin_pp Hin) as Ipp. pose proof (vin_len Hin) as Ilen. pose proof (vin_g Hin) as Ig. pose proof (vin_qt Hin) as Iqt. pose proof (vin_d32 Hin) as Id32.
    pose proof (vsr_4096 Hsrc) as Hs4096. pose proof (vsr_ceil Hsrc) as Hsac.
    pose proof (ajx_ly HJ0) as HLY0. pose proof (ajx_hi HJ0) as HJkeep.
    assert (Etop : ly_top ly = ly_top ly0)
      by (exact (vly_top HLY0)).
    pose proof (vsav12 Hsaved) as (Sv8 & Sv16).
    assert (EMc0 : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (Sv8r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 8) = Some (raZ regs0))
      by (apply vrd_rdword_of_val_mem; [exact Sv8 | apply bv_unsigned_in_range]).
    assert (Sv16r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 16) = Some (s0Z regs0))
      by (unfold s0Z; apply vrd_rdword_of_val_mem; [exact Sv16 | apply bv_unsigned_in_range]).
    assert (HAGR : forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
                     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a).
    { pose proof (vastk HJstk) as (_ & HSTKa & Hceila & Hsloa & _).
      intros a Ha Hn. destruct (Z_lt_le_dec a (spZ regs0 + e)) as [Hlt|Hge].
      - apply Hwin; [clear - Ha Hlt; slia | exact Hn].
      - apply HJkeep; [clear - Ha Hge Hceila Hsloa HSTK HSTKi; slia | clear - Hge; slia]. }
    assert (Hsp8 : spZ regs0 mod 8 = 0) by (clear - Hr16; Z.div_mod_to_equations; lia).
    assert (HVLO : v + 56 <= spZ regs0).
    { destruct Hvwin as [Hv|Hv]; [exact Hv|].
      pose proof (vnd_at Hnode) as Hat. pose proof (vnd_own Hnode) as Hown. exfalso.
      pose proof (ajx_ar HJ0) as HARd. cbv beta in HARd.
      pose proof (vastk HJstk) as (_ & HSTKn & Hceil1 & Hslo1 & _).
      pose proof (@cf_head_nonneg cp) as Hhd0.
      destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                      [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      + pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARd Habk) as (_ & _ & Hcb & _).
        assert (Hk0h : 0 <= k0 + cf_head) by (clear - Hk0 Hhd0; slia).
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        clear - Hle0 Hhi0 Hcb Hrq Hhd0 Hv Hceil1 Hslo1 HSTKn; slia.
      + destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b0 m0 HARd Hinb) as (_ & _ & Hcb & _).
        assert (Hm00 : 0 <= m0) by (clear - Hhib Hleb; slia).
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        clear - Hleb Hhib Hcb Hrq Hv Hceil1 Hslo1 HSTKn; slia.
      + destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HARd Hinf) as (_ & Hfc & _).
        clear - Hlef Hhif Hfc Hv Hceil1 Hslo1 HSTKn; slia.
      + clear - Hw2 Hv; slia. }
    (* the chain at the call view, by VproC's keep lemma vrd_disp_chain *)
    assert (HCH : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms)) (spZ regs) (spZ regs0) ch1 /\
                  spine ch1 = raZ regs0 :: spine ch).
    { rewrite EMc0.
      pose proof (vastk HJstk) as (Hsp16c & HSTK0c & Hceilc & Hsloc & Hshic & H47c & Hbotc & Htopc & Htop2c).
      apply (vrd_disp_chain ly0 ly W0 W mem0 mem regs0 ch q v (spZ regs) p p' Hchain0 Hcur).
      - apply vrd_rdword_of_val_mem; [exact I0p | clear - I0pp I0t I0tl; slia].
      - clear - I0pp Hs4096; slia.
      - clear - I0pp HTC; slia.
      - apply vrd_rdword_of_val_mem; [exact Ip | clear - Ipp It Itl; slia].
      - clear - Ipp HTC; slia.
      - clear - Hq1 Hceilc Hsloc HSTK HSTKi; slia.
      - exact Iq8.
      - exact Etop.
      - clear - Htop2c H47c; slia.
      - clear - Hceilc Hsloc HSTK HSTKi; slia.
      - rewrite Rregs. clear - Hm32; slia.
      - clear - Htopc Hq1 Hq2; slia.
      - exact Hsp8.
      - exact Hra4k.
      - exact Sv8r.
      - exact Sv16r.
      - exact HAGR.
      - exact HVLO.
      - intros a Ha. unfold aview.
        assert (Hk : (Z.to_nat (a - (q + 16)) < 4)%nat) by (clear - Ha; slia).
        pose proof (I0d _ Hk) as E0. pose proof (Id _ Hk) as E1.
        rewrite Z2Nat.id in E0, E1 by (clear - Ha; slia).
        replace (q + 16 + (a - (q + 16))) with a in E0, E1 by ring.
        rewrite E0, E1. reflexivity. }
    destruct HCH as (ch1 & Hach & Hspine).
    rewrite (EW 8%nat (8%bv : bv 5)) in P8 by (vm_compute; reflexivity || slia).
    assert (Hs0 : s0Z (ms_regs ms) = spZ regs0).
    { unfold s0Z. rewrite P8, R8. unfold w64. apply unsigned_lit_small. slia. }
    eapply SRr_bind.
    { eapply (vrd_call_W B ARx SK LAWS W (va_env regs) _ ms (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
        ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp _ k STK_literal (spZ regs0 + e - spZ regs)
        [(q, q + 8); (v, v + 4)] (spZ regs - (spZ regs0 + e)) _ ch1
        _ HS eq_refl HJ).
      - unfold spZ at 1. rewrite P2. fold (spZ regs). slia.
      - rewrite Rregs. Z.div_mod_to_equations. lia.
      - rewrite Rregs. slia.
      - exact HSTKi.
      - rewrite Rregs. slia.
      - slia.
      - rewrite P3, (EW 3%nat (3%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R3. exact Hgp0.
      - rewrite P4, (EW 4%nat (4%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R4. exact Htp0.
      - exact P1.
      - apply (ret_ok_codeptr_v (PI := PI_prog_A)); [slia | reflexivity].
      - rewrite EB. unfold A_prog_base. rewrite unsigned_lit_small by slia. slia.
      - replace (spZ regs0 + e + (spZ regs - (spZ regs0 + e))) with (spZ regs) by slia. rewrite Hs0. exact Hach.
      - intros HPRE1. cbn [ss_pc setpc].
        assert (EM : ms_mem ms = mem).
        { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
          unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
        assert (Esp2 : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
        assert (Hd16 : (spZ regs0 - spZ regs) mod 16 = 0) by (rewrite Rregs; Z.div_mod_to_equations; lia).
        pose proof (vnd_v4096 Hnode) as Hv4096. pose proof (vnd_al8 Hnode) as Hval8. pose proof (vnd_rw Hnode) as Hrw. pose proof (vnd_zero Hnode) as Hzero. pose proof (vnd_at Hnode) as Hat. pose proof (vnd_amr Hnode) as Hamr. pose proof (vnd_own Hnode) as Hown. pose proof (vnd_ra Hnode) as Hra8.
        refine (HPI ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1
          (spZ regs0 + e - spZ regs) q text len p' (Z.of_nat d) tb (vrd_kw_addr 116) PjGrammar.w_true slack 2 v
          Lam peak cnt fail ran most own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
        { split; [exact HPRE1|]. split; [intros a H1 H2 H3; rewrite KM; exact (Hrod a H1 H2 H3)|].
          assert (Ehi : ly_stk_hi ly = ly_stk_hi ly0)
            by (exact (vly_stk_hi HLY0)).
          split; [rewrite Esp2, Rregs, Ehi; clear - Hshi He0 Hm32; slia|].
          (* fpre's ra bound (the cut's PRH_Base.v fpre): the return address is the jal's own return pc *)
          unfold raZ at 1. rewrite P1, EB. rewrite unsigned_lit_small by (unfold A_prog_base; slia).
          split; [exact vrd_ret224_lt_ceil | exact Hfrm]. }
        { rewrite P10, (EW 20%nat (20%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R20. }
        { rewrite P11. unfold vrd_kw_addr, vrd_kw_slot, vrd_kw_row. vm_compute. reflexivity. }
        { rewrite P12. reflexivity. }
        { rewrite P13, (EW 19%nat (19%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R19. }
        { rewrite EM. exact Hin. }
        { rewrite EM. replace (spZ regs0 + e - spZ regs) with (e + (spZ regs0 - spZ regs)) by slia.
          apply (vrd_fwin_shift ly W regs0 (ms_regs ms) mem e (spZ regs0 - spZ regs) Hfw); [slia | slia | exact Hd16 |].
          intros a Ha. apply HJpres1. rewrite Rregs in Ha. slia. }
        { rewrite Esp2. slia. }
        { rewrite Esp2. slia. }
        { rewrite EM. exact Hraq. }
        { rewrite EM. exact Hsrc. }
        { exact Hhome. }
        { rewrite EM. exact (proj1 (Hkw regs mem md eq_refl)). }
        { exact Hw63. }
        { rewrite EM. exact (proj2 (Hkw regs mem md eq_refl)). }
        { exact Hnul. }
        { exact Hslack. }
        { rewrite Esp2, Rregs. right.
          assert (Hm16 : (spZ regs0 - 160) mod 32 = 0 \/ (spZ regs0 - 160) mod 32 = 16).
          { clear - Hr16 Hm32. Z.div_mod_to_equations. lia. }
          clear - Hwstk HSTK HSTKi Hm16. slia. }
        { slia. }
        { slia. }
        { exact Hval8. }
        { replace (spZ regs0 + e - spZ regs) with (e + (spZ regs0 - spZ regs)) by slia.
          apply (vrd_reader_at_narrow B ly S Lam (ms_regs ms) (e + (spZ regs0 - spZ regs)) v 56 4);
          [apply (vrd_reader_at_shift B ly S Lam regs0 (ms_regs ms) e (spZ regs0 - spZ regs) v 56 Hat);
           [rewrite Esp2; slia | slia] | slia]. }
        { rewrite EM. apply (vrd_range_narrow _ _ v 56 4); [exact Hra8 | slia]. }
        { slia. }
        { assert (Hlen0 : 0 < len) by (clear - Ipp Hplt; lia). destruct (Htv Hlen0) as [H|H]; [right; slia | left; slia]. }
        { rewrite EM. exact Hled. }
      - intros a Ha. left. cbn [In rd_fp] in Ha |- *.
        destruct Ha as (r & [<- | [<- | []]] & Hr); cbn [fst snd] in Hr;
        [exists (q, q + 8); cbn [fst snd]; split; [left; reflexivity | slia]
        |exists (v, v + 56); cbn [fst snd]; split; [right; right; left; reflexivity | slia]]. }
    cbv beta. intros W2 c2 HW2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HWIN & HP2 & HQ).
    (* row 224 (`mv s5, a0`), the literal's return site: a fresh symbolic state there, at the same float state *)
    pose proof (va_entry W2 regs2 mem2 (vrd_row 224)) as HS2.
    rewrite EB in HS2.
    replace (pa_val A_TEXT + 19624) with (A_prog_base + vrd_row 224) by (rewrite EB; reflexivity).
    assert (HEI2 : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (va_env regs2)) by (unfold va_env; apply Eimg_env).
    assert (SHOK2 : sh_ok SEGS (SLit 0) [] (va_env regs2) (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
    pose (RUNTO2 := paj_run_to_x (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS).
    paj_run_to_tok_x RUNTO2 HS2 HJ2 SHOK2 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (vrd_row 225).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    pmkst HS2.
    prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (26%bv : bv 5) Q26.
    prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
    (* the big hypotheses the rest does not use: every lia below scans the whole context *)
    clear HPI Hchain0 Hcurch Hclos Hcur HFP Hrod Hkw HAGR HJkeep I0p I0e I0d I0rw I0g I0qt Ip Ie Id Irw Ig Iqt Sv8r Sv16r.
    assert (EW2 : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                    ew (va_env regs2) n = getr regs2 r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
    assert (EM2 : ms_mem ms0 = mem2).
    { apply functional_extensionality. intros x. apply HF0. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (EMc : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    (* the literal's footprint lies inside parse_value's reader cells *)
    assert (HFPs : forall a, inFP [(q, q + 8); (v, v + 4)] a -> inFP (rd_fp q v) a).
    { intros a (r & Hr & Hra). cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra;
      [exists (q, q + 8); split; [left; reflexivity | exact Hra]
      |exists (v, v + 56); cbn [fst snd]; split; [right; right; left; reflexivity | slia]]. }
    pose proof (ajx_ly HJc) as HLY.
    assert (EF : ly_F ly2 = ly_F ly) by (exact (vly_F HLY)).
    assert (Efr : frame_addr ly2 0 pos = frame_addr ly 0 pos) by (unfold frame_addr; rewrite EF; reflexivity).
    assert (Efl : flag_addr ly2 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite EF; reflexivity).
    assert (KS8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HP2 8); unfold acallee_saved; slia).
    assert (KS18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HP2 18); unfold acallee_saved; slia).
    assert (KS26 : getr regs2 26 = getr (ms_regs ms) 26) by (apply (HP2 26); unfold acallee_saved; slia).
    assert (KS24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HP2 24); unfold acallee_saved; slia).
    assert (KS3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HP2 3); unfold acallee_saved; slia).
    assert (KS4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HP2 4); unfold acallee_saved; slia).
    Ltac va_cs2 := first [(vm_compute; reflexivity) | (clear; slia)].
    (* literal's post (the cut's PRH_FnReader.v blob f1ae32e3b2cd): its conjuncts BY SHAPE (decompose [and], then each named by
       its type); the keyword branch is one conjunct *)
    destruct HQ as (HQb & Hmk). decompose [and] HQb. clear HQb.
    lazymatch goal with X : room_live_cf S -> room_live_cf S2 |- _ => rename X into Hrl end.
    lazymatch goal with X : Hp2 = Hp |- _ => rename X into EHp end.
    lazymatch goal with X : S2 = S |- _ => rename X into ES end.
    lazymatch goal with X : ablocks B ly2 S2 = ablocks B ly S |- _ => rename X into Eab2 end.
    lazymatch goal with X : context [prh_ledger _ _ S2] |- _ => rename X into Hled2 end.
    lazymatch goal with X : match PjGrammar.prefixb _ _ with _ => _ end |- _ => rename X into Hbr end.
    (* P across the call: the m-form post's memnorm keep and srr_inv_call; row 224 writes no memory *)
    assert (HPc : P (ms_mem ms)) by (rewrite EMc; exact HPm).
    assert (HPr : P (ms_mem ms0)) by (rewrite EM2; exact (PC (ms_mem ms) mem2 Hmk HPc)).
    set (pre := PjGrammar.prefixb PjGrammar.w_true (rest_atR tb text p')) in Hbr.
    assert (Hrv : getr regs2 10 = w64 (if pre then 0 else -1))
      by (destruct pre; cbv beta iota in Hbr; decompose [and] Hbr; assumption).
    apply SRr_ret. split; [|exact HPr]. unfold vrd_arm_exit.
    exists fx, pos, (if pre then 0 else -1).
    (* the join BY NAME: VrdNum's record vrd_epi_R at the join's witnesses (vrd_epi_aR_of_R at wle), one named goal per
       field *)
    unfold vrd_epi_a.
    apply vrd_epi_aR_of_R with (regs := ms_regs ms0) (mem := ms_mem ms0)
      (md := with_vm_backing (m_vm_lazy md2) mat0 md2) (ly := ly2) (S := S2) (Hp := Hp2) (k := k + k1).
    refine {| vepi_cfg := ?[e_cfg]; vepi_jrn := ?[e_jrn]; vepi_win := ?[e_win]; vepi_s0 := ?[e_s0]; vepi_s2 := ?[e_s2];
              vepi_s10 := ?[e_s10]; vepi_s8 := ?[e_s8]; vepi_s5 := ?[e_s5]; vepi_gp := ?[e_gp]; vepi_tp := ?[e_tp];
              vepi_ra := ?[e_ra]; vepi_saved := ?[e_saved]; vepi_flag := ?[e_flag]; vepi_frm := ?[e_frm];
              vepi_fregs := ?[e_fregs]; vepi_rq := ?[e_rq] |}.
    [e_cfg]: { rewrite vrd_pc_epi; reflexivity. }
    (* vrd_epi_a's journal: the literal's text posts no wild budget (fpostWm), so the journal is the budget-free one
       (ajournal_x is ajournal_xw at []) and wbudget CW 0 [] holds by computation *)
    [e_jrn]: { exists []. split; [exact HJ2 | unfold YCbqGwild.wbudget, YCbqGwild.wfresh; cbn; lia]. }
    [e_win]: { intros a Ha Hn. rewrite EM2, (HWIN a ltac:(slia) (fun H => Hn (HFPs a H))), EMc. exact (Hwin a Ha Hn). }
    [e_s0]: { rewrite Q8, (EW2 8%nat (8%bv : bv 5)) by va_cs2; rewrite KS8; rewrite P8; exact R8. }
    [e_s2]: { rewrite Efr, Q18, (EW2 18%nat (18%bv : bv 5)) by va_cs2; rewrite KS18;
              rewrite P18, (EW 18%nat (18%bv : bv 5)) by va_cs2; exact R18. }
    [e_s10]: { rewrite Efr, Q26, (EW2 26%nat (26%bv : bv 5)) by va_cs2; rewrite KS26;
               rewrite P26, (EW 26%nat (26%bv : bv 5)) by va_cs2; exact R26. }
    [e_s8]: { rewrite Efr, Q24, (EW2 24%nat (24%bv : bv 5)) by va_cs2; rewrite KS24;
              rewrite P24, (EW 24%nat (24%bv : bv 5)) by va_cs2; exact R24. }
    [e_s5]: { rewrite Q21, (EW2 10%nat (10%bv : bv 5)) by va_cs2; exact Hrv. }
    [e_gp]: { rewrite Q3, (EW2 3%nat (3%bv : bv 5)) by va_cs2; rewrite KS3;
              rewrite P3, (EW 3%nat (3%bv : bv 5)) by va_cs2; exact R3. }
    [e_tp]: { rewrite Q4, (EW2 4%nat (4%bv : bv 5)) by va_cs2; rewrite KS4;
              rewrite P4, (EW 4%nat (4%bv : bv 5)) by va_cs2; exact R4. }
    [e_ra]: exact Hra0.
    (* the thirteen spilled words: parse_value's own frame below spZ regs0, outside rd_fp q v (the cursor is above
       spZ regs0, the node outside parse_value's stack window), kept by the callee's window clause and both runs *)
    [e_saved]: { assert (KSV : forall a, spZ regs0 - 104 <= a < spZ regs0 ->
                aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
      { intros a Ha. rewrite EM2. rewrite (HWIN a); [rewrite EMc; reflexivity | rewrite Rregs; slia |].
        intros (r & Hrin & Hr). cbn [In] in Hrin.
        destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; [slia |].
        pose proof (vnd_own Hnode) as Hown.
        destruct (Hown a ltac:(slia)) as [_ Hn]. apply Hn. slia. }
      unfold vrd_saved in Hsaved |- *.
      destruct Hsaved as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (eapply val_mem_kept; [|eassumption]; intros kk Hk; cbn in Hk; apply KSV; slia). }
    (* the flag word at F + 56: it lies in parse_value's OWN fake frame, which is below alloc_ceiling, and outside the
       callee's footprint rd_fp q v (the cursor is a stack address above alloc_ceiling; the node cannot meet the frame:
       a block is apart from a frame, another frame is apart from this one, and this frame itself would put the
       descriptor word at F + 16 inside the node's 56 ZEROED bytes). So the callee's journal frames clause keeps it. *)
    [e_flag]: { rewrite Efr, Efl.
      pose proof (ajx_ar HJ0) as HAR. cbv beta in HAR.
      assert (HinF : In (0, pos) (frames S)) by (rewrite Hfr; left; reflexivity).
      destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HFa0 & HFc & HFapp).
      assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFc.
      pose proof (vfrm3 Hframe) as (Hmag & Hsig & Hflag).
      pose proof (vnd_v4096 Hnode) as Hv4096. pose proof (vnd_al8 Hnode) as Hval8. pose proof (vnd_rw Hnode) as Hrw. pose proof (vnd_zero Hnode) as Hzero. pose proof (vnd_at Hnode) as Hat. pose proof (vnd_amr Hnode) as Hamr. pose proof (vnd_own Hnode) as Hown. pose proof (vnd_ra Hnode) as Hra8.
      pose proof (@cf_head_nonneg cp) as Hhd0.
      assert (HvF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> ~ (v <= a < v + 56)).
      { intros a Ha Hav.
        destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                        [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
        - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
          pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
          apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (a0 - cf_head) (k0 + cf_head) a HAR HinF Habk);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hk0h : 0 <= k0 + cf_head) by slia.
          pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq). slia.
        - apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) b0 m0 a HAR HinF Hinb);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hm00 : 0 <= m0) by slia.
          pose proof (req_size_pos m0 Hm00) as (_ & Hrq). slia.
        - rewrite Hfr in Hinf. destruct Hinf as [Ef | Hinf].
          + injection Ef as <- <-.
            assert (Hz16 : val_mem SEGS (mrestrict (w_H W) mem) (frame_addr ly 0 pos + 16) 8 0).
            { apply (vrd_zero_val SEGS (mrestrict (w_H W) mem) v); [exact Hzero | rewrite Hfb in Hhif; slia | rewrite Hfb in Hhif; slia]. }
            pose proof (Hsig 0%nat ltac:(slia)) as E1. pose proof (Hz16 0%nat ltac:(slia)) as E2.
            cbn [Z.of_nat] in E1, E2. rewrite Z.add_0_r in E1, E2.
            rewrite E1 in E2. vm_compute in E2. discriminate E2.
          + apply in_split in Hinf as (l2 & l3 & El).
            pose proof (sep_frames_pos_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (cid, pos') (@nil (Z * Z)) l2 l3 HAR
              ltac:(rewrite Hfr, El; reflexivity)) as Hd.
            unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Hfb in Hd. slia.
        - slia. }
      assert (HqF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> a < q).
      { intros a Ha. pose proof (vastk HJstk0) as (_ & _ & Hclo2 & Hlo2 & _). slia. }
      assert (HnFP : forall a, frame_addr ly 0 pos + 56 <= a < frame_addr ly 0 pos + 64 ->
                 ~ inFP [(q, q + 8); (v, v + 4)] a).
      { intros a Ha (r & Hrin & Hr). cbn [In] in Hrin.
        destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr;
        [pose proof (HqF a ltac:(slia)); slia | exact (HvF a ltac:(slia) ltac:(slia))]. }
      pose proof (ajx_frm HJc) as HJfr.
      eapply val_mem_kept; [|exact Hflag]. intros kk Hk. cbn in Hk.
      rewrite EM2, <- EMc.
      apply (HJfr 0 pos (frame_addr ly 0 pos + 56 + kk) HinF);
      [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia
      | apply HnFP; slia]. }
    [e_frm]: exact Hfrm.
    [e_fregs]: { intros r _; reflexivity. }
    (* ---- RQ: the literal's post read as parse_value's (VnumC's vrd_pv_post), with no allocation: D = [], BY NAME:
       VrdNum's record vrd_pv_R (vrd_pv_post_of_R), one named goal per field ---- *)
    [e_rq]: {
    pose proof Hled as HLB. apply prh_ledger_bounds in HLB. destruct HLB as (Hlp & Hpk & Hcn & Hfl & Hrn).
    pose proof (vnd_v4096 Hnode) as Hv4096n. pose proof (vnd_al8 Hnode) as Hval8n. pose proof (vnd_rw Hnode) as Hrwn. pose proof (vnd_zero Hnode) as Hzeron. pose proof (vnd_at Hnode) as Hatn. pose proof (vnd_amr Hnode) as Hamrn. pose proof (vnd_own Hnode) as Hownn. pose proof (vnd_ra Hnode) as Hra8n.
    pose proof (ajx_ar HJc) as HAR2. cbv beta in HAR2.
    assert (Ex : rest_atR tb text p' = 116 :: yy) by (rewrite Hrest; exact Hsk).
    (* the node's bytes the call did not write are kept: the node is a harness block, an allocator block or a
       frame (the window case is excluded by HVLO), and the callee journal keeps blocks and frames off FP1 *)
    assert (HNK : forall a, v <= a < v + 56 -> ~ inFP [(q, q + 8); (v, v + 4)] a ->
              aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
    { intros a Ha Hn. rewrite <- EMc.
      pose proof (ajx_ly HJc) as HLYc. pose proof (ajx_blk HJc) as HJb. pose proof (ajx_frm HJc) as HJf.
      destruct Hatn as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                       [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        pose proof (@cf_head_nonneg cp) as Hhd0.
        assert (Hk0h : 0 <= k0 + cf_head) by slia.
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        replace a with ((a0 - cf_head) + (a - (a0 - cf_head))) by slia.
        apply (HJb (a0 - cf_head) (k0 + cf_head) (a - (a0 - cf_head))); [exact Habk | rewrite Eab2; exact Habk | slia |].
        replace ((a0 - cf_head) + (a - (a0 - cf_head))) with a by slia. exact Hn.
      - assert (Hm00 : 0 <= m0) by slia.
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        replace a with (b0 + (a - b0)) by slia.
        apply (HJb b0 m0 (a - b0)); [exact Hinb | rewrite Eab2; exact Hinb | slia |].
        replace (b0 + (a - b0)) with a by slia. exact Hn.
      - apply (HJf cid pos' a Hinf); [left; unfold in_zr, frame_rng; cbn [fst snd]; slia | exact Hn].
      - slia. }
    (* the node bytes beyond the type word, at the end, are the dispatch's: zero *)
    assert (VK : forall a n x, v + 4 <= a -> a + Z.of_nat n <= v + 56 ->
              val_mem SEGS (mrestrict (w_H W) mem) a n x -> val_mem SEGS (mrestrict (w_H W2) mem2) a n x).
    { intros a n x H1 H2 Hv kk Hk.
      rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
      apply HNK; [slia|]. intros (r & Hrin & Hr). cbn [In] in Hrin.
      destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; slia. }
    (* every node byte is present at the end (a block or a frame of the end state), so writable *)
    assert (HWR : forall a, v <= a < v + 56 -> writable_at SEGS (mrestrict (w_H W2) mem2) a).
    { intros a Ha. apply apresent_writable.
      pose proof (ajx_ly HJc) as HLYc.
      assert (EFc : ly_F ly2 = ly_F ly) by (exact (vly_F HLYc)).
      pose proof (vnd_at Hnode) as Hat2.
      destruct Hat2 as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                       [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        pose proof (@cf_head_nonneg cp) as Hhd0.
        assert (Hk0h : 0 <= k0 + cf_head) by slia.
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        rewrite <- Eab2 in Habk.
        destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Habk) as (_ & _ & _ & _ & Hb & _).
        exact (proj1 (Hb a ltac:(slia))).
      - assert (Hm00 : 0 <= m0) by slia.
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        rewrite <- Eab2 in Hinb.
        destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hinb) as (_ & _ & _ & _ & Hb & _).
        exact (proj1 (Hb a ltac:(slia))).
      - assert (Hinf2 : In (cid, pos') (frames S2)) by (rewrite ES; exact Hinf).
        destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos' HAR2 Hinf2) as (_ & _ & Hfp & _).
        assert (Efa : frame_addr ly2 cid pos' = frame_addr ly cid pos') by (unfold frame_addr; rewrite EFc; reflexivity).
        rewrite Efa in Hfp. exact (proj1 (Hfp a ltac:(slia))).
      - slia. }
    rewrite EM2.
    apply vrd_pv_post_of_R with (ok := [])
      (res := if pre then Some (JTrue, skipn (length PjGrammar.w_true) (116 :: yy)) else None) (tr := []) (okr := [])
      (D := []) (Lam' := Lam) (peak' := peak) (cnt' := cnt) (fail' := fail) (ran' := ran).
    (* the literal allocates nothing: its value is the keyword's, at ok = [] (EJ), and its granted trace is
       empty (vrd_gtrace_lit); S2 = S, which is S0 up to its fake frames (`S = set_fs f S0`) *)
    assert (EJ : jr_value ReaderRes.jr_strtod d (rest_atR tb text p) [] =
                 ((if pre then Some (JTrue, skipn (length PjGrammar.w_true) (116 :: yy)) else None), [], [])).
    { rewrite (vrd_lit_model ReaderRes.jr_strtod d 116 yy (rest_atR tb text p) [] Hsk (or_introl eq_refl)).
      cbn [Z.eqb Pos.eqb]. unfold PjGrammar.lit, PjGrammar.jret, PjGrammar.jrefuse. unfold pre. rewrite Ex.
      destruct (PjGrammar.prefixb PjGrammar.w_true (116 :: yy)); reflexivity. }
    pose proof (vrd_gtrace_lit d 116 yy (rest_atR tb text p) Hsk (or_introl eq_refl)) as EG0.
    destruct Hsetfs as (fz & Efz).
    refine {| vpv_run := ?[p_run]; vpv_ledger := ?[p_ledger]; vpv_room := ?[p_room]; vpv_hull := ?[p_hull];
              vpv_live := ?[p_live]; vpv_pos := ?[p_pos]; vpv_outcome := ?[p_outcome]; vpv_injected := ?[p_injected];
              vpv_ledger_move := ?[p_ledger_move]; vpv_fresh := ?[p_fresh]; vpv_blocks := ?[p_blocks];
              vpv_frames := ?[p_frames]; vpv_hpeak := ?[p_hpeak]; vpv_bytes := ?[p_bytes]; vpv_lsum := ?[p_lsum];
              vpv_arm := ?[p_arm] |}.
    [p_run]: exact EJ.
    [p_ledger]: exact Hled2.
    [p_room]: exact (Hrl (vrr_live _ _ Hroom)).
    (* the hull use: the granted trace is empty (EG0) and S2 = S, which has S0's st_secs (`S = set_fs f S0`) *)
    [p_hull]: { rewrite EG0; apply PresetHullBudget.hull_used_secs; rewrite ES, Efz; reflexivity. }
    [p_live]: { rewrite ES, Efz. change (PresetReqAt.rd_hevs []) with (@nil PresetReqAt.hev).
      rewrite PresetReqAt.hlive_from_nil.
      change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
        with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)).
      apply Permutation_refl. }
    [p_pos]: { intros sm x os i Hz0 hist Hpos _. exists hist. rewrite ES, Efz.
      change (length (PresetReqAt.rd_hevs [])) with 0%nat. rewrite Nat.add_0_r.
      apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
    [p_outcome]: { intros sm x os i Hz0 hist Hpos _ _ _. split; [reflexivity|]. split; [rewrite EJ; reflexivity|].
      exists hist. rewrite EG0, ES, Efz.
      change (length (PresetReqAt.rd_hevs [])) with 0%nat. rewrite Nat.add_0_r.
      apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
    (* the injected reading: vacuous, the granted trace is empty (EG0), so the window cnt <= fail < cnt is empty *)
    [p_injected]: { intros sm x os i Hz0 hist _ _ _ Hwd; rewrite EG0 in Hwd; cbn [PjGrammar.calls Z.of_nat] in Hwd;
            exfalso; slia. }
    [p_ledger_move]: { unfold rd_ledger_move. cbn [PjGrammar.calls lszR nliveR hpeakR map length app].
      split; [split; [intros i Hi; cbn in Hi; slia | split; [left; reflexivity | intros i Hi; cbn in Hi; slia]]|].
      split; [rewrite Z.add_0_r, Z.mod_small by slia; reflexivity|].
      split; [split; intros Hc; cbn in Hc; [slia | reflexivity]|].
      split; [apply Permutation_refl|].
      split; [constructor|].
      split; [reflexivity|].
      unfold prh_refused_peak. cbn [List.seq map fold_right]. clear - Hlp. lia. }
    [p_fresh]: { intros aa kk Hak; destruct Hak. }
    [p_blocks]: { rewrite Eab2, Hab; cbn [prhReader_ab map app]; apply Permutation_refl. }
    [p_frames]: { rewrite ES, Hfr; apply Permutation_refl. }
    [p_hpeak]: { cbn [hpeakR]; slia. }
    [p_bytes]: { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly0 S0), Eab2, Hab.
      unfold prh_held. cbn [PjGrammar.held PjGrammar.calls fold_right map Z.of_nat]. slia. }
    [p_lsum]: reflexivity.
    [p_arm]: {
    unfold pre in Hbr |- *. rewrite Ex in Hbr |- *.
    destruct (PjGrammar.prefixb PjGrammar.w_true (116 :: yy)) eqn:Epre.
    + (* the keyword matched: the node is JTrue, the cursor advanced by four *)
      cbv beta iota in Hbr. decompose [and] Hbr. clear Hbr.
      lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W2) mem2) q text len _ _ tb |- _ => rename X into Hin2 end.
      lazymatch goal with X : val_mem _ (mrestrict (w_H W2) mem2) v 4 _ |- _ => rename X into Hty2 end.
      assert (Elen : Z.of_nat (length (116 :: yy)) = text + len - p').
      { rewrite <- Ex. unfold rest_atR. rewrite length_skipn.
        pose proof (vin_pp Hin) as Hpp'. pose proof (vin_len Hin) as Hlen'. slia. }
      assert (Hge4 : 4 <= Z.of_nat (length (116 :: yy))).
      { clear - Epre. destruct yy as [|c1 [|c2 [|c3 yy']]]; cbn in Epre |- *; try discriminate; slia. }
      (* the node's header, shared by its free order and its node clause *)
      assert (HHDl : pj_hdrR SEGS (mrestrict (w_H W2) mem2) v (tag JTrue) 0 0 0 0 0 0).
      {
        split; [split; [exact Hval8n | intros xw Hxw; exact (HWR xw Hxw)]|].
        split; [split; [cbn; slia | exact Hty2]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 8) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 16) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 24) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 32) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 40) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 48) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]].
      }
      assert (HAPl : pj_apartR [] v) by (intros bb x Hb; destruct Hb).
      refine {| vpvs_rv := ?[s_rv]; vpvs_freeord := ?[s_freeord]; vpvs_in_ok := ?[s_in_ok]; vpvs_node := ?[s_node];
                vpvs_ncap := ?[s_ncap]; vpvs_lsum_le := ?[s_lsum_le] |}.
      [s_rv]: reflexivity.
      (* the free order (PRH_PjOrder.pfo_leaf): a leaf with no block frees nothing, and the value's free list at a
         keyword is [] (vrd_frees_lit) *)
      [s_freeord]: { intros _ nn _. exists []. split.
        - exact (PRH_PjOrder.pfo_leaf SEGS _ _ nn v (tag JTrue) 0 0 [] ltac:(constructor) HAPl HHDl (or_introl (conj eq_refl eq_refl))).
        - rewrite (vrd_frees_lit d 116 yy (rest_atR tb text p) [] Hsk (or_introl eq_refl)). reflexivity. }
      [s_in_ok]: { assert (Epos : text + len - Z.of_nat (length (skipn (length PjGrammar.w_true) (116 :: yy))) =
                       p' + Z.of_nat (length PjGrammar.w_true)).
        { rewrite length_skipn. cbn [length PjGrammar.w_true] in *. slia. }
        rewrite Epos. exact Hin2. }
      [s_node]: { split; [constructor|]. split; [intros bb x Hb; destruct Hb|].
        exists 0, 0, 0, 0, 0, 0. split; [exact HHDl | repeat split; reflexivity]. }
      (* the leaf's capacity words: pj_ncapR of a keyword is True *)
      [s_ncap]: exact I.
      [s_lsum_le]: { pose proof (vrd_rest_shrink tb text p p' (proj1 Hpp)) as Hshr. rewrite Ex in Hshr.
        cbn [Ledger.lsum]. rewrite length_skipn. cbn [length PjGrammar.w_true] in *. slia. }
    + (* the keyword did not match: the cursor and the node are untouched *)
      cbv beta iota in Hbr. decompose [and] Hbr. clear Hbr.
      lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W2) mem2) q text len _ _ tb |- _ => rename X into Hin2 end.
      lazymatch goal with X : forall a, q <= a < q + 8 \/ _ -> _ |- _ => rename X into Hkeep end.
      assert (HRW2 : pj_rwR SEGS (mrestrict (w_H W2) mem2) v)
        by (split; [exact Hval8n | intros xw Hxw; exact (HWR xw Hxw)]).
      assert (HZ2 : pj_zeroR SEGS (mrestrict (w_H W2) mem2) v).
      {
        unfold pj_zeroR in *. intros jj Hjj. destruct (Hzeron jj Hjj) as (Hz1 & Hz2). split; [|exact Hz2].
        intros kk Hkk. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 (v + Z.of_nat jj + Z.of_nat kk)).
        + exact (Hz1 kk Hkk).
        + rewrite repeat_length in Hjj. cbn in Hkk.
          destruct (Z_lt_le_dec (v + Z.of_nat jj + Z.of_nat kk) (v + 4)) as [Hlo|Hhi].
          * rewrite <- EMc. apply Hkeep. right. slia.
          * apply HNK; [slia|]. intros (r & Hrin & Hr). cbn [In] in Hrin.
            destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; slia.
      }
      refine {| vpvn_rv := ?[n_rv]; vpvn_freeord := ?[n_freeord]; vpvn_in_after := ?[n_in_after];
                vpvn_fd := ?[n_fd] |}.
      [n_rv]: reflexivity.
      (* the free order of the untouched (zero) node: its order list is [] (VrdNum.vrd_zero_fo), and the value's free
         list at a keyword is [] (vrd_frees_lit) *)
      [n_freeord]: { intros _ nn _. exists []. split.
        - exact (vrd_zero_fo SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) v nn HRW2 HZ2).
        - rewrite (vrd_frees_lit d 116 yy (rest_atR tb text p) [] Hsk (or_introl eq_refl)). reflexivity. }
      [n_in_after]: { pose proof (vin_p Hin2) as J1. pose proof (vin_end Hin2) as J2. pose proof (vin_d Hin2) as J3. pose proof (vin_rw Hin2) as J4. pose proof (vin_q8 Hin2) as J5. pose proof (vin_t Hin2) as J6. pose proof (vin_tl Hin2) as J7. pose proof (vin_pp Hin2) as J8. pose proof (vin_len Hin2) as J9. pose proof (vin_g Hin2) as J10. pose proof (vin_qt Hin2) as J11. pose proof (vin_d32 Hin2) as J12.
        exists p', (Z.of_nat d). split; [slia|]. split; [slia|].
        split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. exact J4. }
      [n_fd]: exact (vrd_zero_fd SEGS _ _ v _ HRW2 HZ2). }
    }
  - paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    prreg HS (2%bv : bv 5) P2. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
    prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
    prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
    prreg HS (18%bv : bv 5) P18. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
    pose proof HJ as HJ0b.
    pose proof (vastk HJstk0) as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
    pose proof (vfw Hfw) as (He0 & He16 & Hetop & Hepres).
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(slia)) as Hm32.
    assert (Hr16 : spZ regs0 mod 16 = 0)
      by (rewrite Zplus_mod, He16, Z.add_0_r, Zmod_mod in Hsp16; exact Hsp16).
    (* the dispatch's alignment slack is 0 or 16 (spZ regs0 is 16-aligned), stated once for the slia calls below *)
    assert (Hsl16 : (spZ regs0 - 160) mod 32 <= 16) by (clear - Hr16 Hm32; Z.div_mod_to_equations; lia).
    assert (Hx : 0 <= spZ regs0 - 160 - (spZ regs0 - 160) mod 32 < 2 ^ 64) by slia.
    assert (Rregs : spZ regs = spZ regs0 - 160 - (spZ regs0 - 160) mod 32).
    { unfold spZ at 1. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by exact Hx. reflexivity. }
    assert (EW : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                   ew (va_env regs) n = getr regs r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
    rewrite (EW 2%nat (2%bv : bv 5)) in P2 by (vm_compute; reflexivity || slia).
    assert (KM : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
    { intros a. symmetry. unfold aview. f_equal. unfold mbyte.
      rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    (* ---- the facts every chain lemma of VproC asks, gathered once ---- *)
    pose proof HJstk0 as HJstk.
    pose proof (vin_p Hin0) as I0p. pose proof (vin_end Hin0) as I0e. pose proof (vin_d Hin0) as I0d. pose proof (vin_rw Hin0) as I0rw. pose proof (vin_q8 Hin0) as I0q8. pose proof (vin_t Hin0) as I0t. pose proof (vin_tl Hin0) as I0tl. pose proof (vin_pp Hin0) as I0pp. pose proof (vin_len Hin0) as I0len. pose proof (vin_g Hin0) as I0g. pose proof (vin_qt Hin0) as I0qt. pose proof (vin_d32 Hin0) as I0d32.
    pose proof (vin_p Hin) as Ip. pose proof (vin_end Hin) as Ie. pose proof (vin_d Hin) as Id. pose proof (vin_rw Hin) as Irw. pose proof (vin_q8 Hin) as Iq8. pose proof (vin_t Hin) as It. pose proof (vin_tl Hin) as Itl. pose proof (vin_pp Hin) as Ipp. pose proof (vin_len Hin) as Ilen. pose proof (vin_g Hin) as Ig. pose proof (vin_qt Hin) as Iqt. pose proof (vin_d32 Hin) as Id32.
    pose proof (vsr_4096 Hsrc) as Hs4096. pose proof (vsr_ceil Hsrc) as Hsac.
    pose proof (ajx_ly HJ0) as HLY0. pose proof (ajx_hi HJ0) as HJkeep.
    assert (Etop : ly_top ly = ly_top ly0)
      by (exact (vly_top HLY0)).
    pose proof (vsav12 Hsaved) as (Sv8 & Sv16).
    assert (EMc0 : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (Sv8r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 8) = Some (raZ regs0))
      by (apply vrd_rdword_of_val_mem; [exact Sv8 | apply bv_unsigned_in_range]).
    assert (Sv16r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 16) = Some (s0Z regs0))
      by (unfold s0Z; apply vrd_rdword_of_val_mem; [exact Sv16 | apply bv_unsigned_in_range]).
    assert (HAGR : forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
                     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a).
    { pose proof (vastk HJstk) as (_ & HSTKa & Hceila & Hsloa & _).
      intros a Ha Hn. destruct (Z_lt_le_dec a (spZ regs0 + e)) as [Hlt|Hge].
      - apply Hwin; [clear - Ha Hlt; slia | exact Hn].
      - apply HJkeep; [clear - Ha Hge Hceila Hsloa HSTK HSTKi; slia | clear - Hge; slia]. }
    assert (Hsp8 : spZ regs0 mod 8 = 0) by (clear - Hr16; Z.div_mod_to_equations; lia).
    assert (HVLO : v + 56 <= spZ regs0).
    { destruct Hvwin as [Hv|Hv]; [exact Hv|].
      pose proof (vnd_at Hnode) as Hat. pose proof (vnd_own Hnode) as Hown. exfalso.
      pose proof (ajx_ar HJ0) as HARd. cbv beta in HARd.
      pose proof (vastk HJstk) as (_ & HSTKn & Hceil1 & Hslo1 & _).
      pose proof (@cf_head_nonneg cp) as Hhd0.
      destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                      [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      + pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARd Habk) as (_ & _ & Hcb & _).
        assert (Hk0h : 0 <= k0 + cf_head) by (clear - Hk0 Hhd0; slia).
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        clear - Hle0 Hhi0 Hcb Hrq Hhd0 Hv Hceil1 Hslo1 HSTKn; slia.
      + destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b0 m0 HARd Hinb) as (_ & _ & Hcb & _).
        assert (Hm00 : 0 <= m0) by (clear - Hhib Hleb; slia).
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        clear - Hleb Hhib Hcb Hrq Hv Hceil1 Hslo1 HSTKn; slia.
      + destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HARd Hinf) as (_ & Hfc & _).
        clear - Hlef Hhif Hfc Hv Hceil1 Hslo1 HSTKn; slia.
      + clear - Hw2 Hv; slia. }
    (* the chain at the call view, by VproC's keep lemma vrd_disp_chain *)
    assert (HCH : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms)) (spZ regs) (spZ regs0) ch1 /\
                  spine ch1 = raZ regs0 :: spine ch).
    { rewrite EMc0.
      pose proof (vastk HJstk) as (Hsp16c & HSTK0c & Hceilc & Hsloc & Hshic & H47c & Hbotc & Htopc & Htop2c).
      apply (vrd_disp_chain ly0 ly W0 W mem0 mem regs0 ch q v (spZ regs) p p' Hchain0 Hcur).
      - apply vrd_rdword_of_val_mem; [exact I0p | clear - I0pp I0t I0tl; slia].
      - clear - I0pp Hs4096; slia.
      - clear - I0pp HTC; slia.
      - apply vrd_rdword_of_val_mem; [exact Ip | clear - Ipp It Itl; slia].
      - clear - Ipp HTC; slia.
      - clear - Hq1 Hceilc Hsloc HSTK HSTKi; slia.
      - exact Iq8.
      - exact Etop.
      - clear - Htop2c H47c; slia.
      - clear - Hceilc Hsloc HSTK HSTKi; slia.
      - rewrite Rregs. clear - Hm32; slia.
      - clear - Htopc Hq1 Hq2; slia.
      - exact Hsp8.
      - exact Hra4k.
      - exact Sv8r.
      - exact Sv16r.
      - exact HAGR.
      - exact HVLO.
      - intros a Ha. unfold aview.
        assert (Hk : (Z.to_nat (a - (q + 16)) < 4)%nat) by (clear - Ha; slia).
        pose proof (I0d _ Hk) as E0. pose proof (Id _ Hk) as E1.
        rewrite Z2Nat.id in E0, E1 by (clear - Ha; slia).
        replace (q + 16 + (a - (q + 16))) with a in E0, E1 by ring.
        rewrite E0, E1. reflexivity. }
    destruct HCH as (ch1 & Hach & Hspine).
    rewrite (EW 8%nat (8%bv : bv 5)) in P8 by (vm_compute; reflexivity || slia).
    assert (Hs0 : s0Z (ms_regs ms) = spZ regs0).
    { unfold s0Z. rewrite P8, R8. unfold w64. apply unsigned_lit_small. slia. }
    eapply SRr_bind.
    { eapply (vrd_call_W B ARx SK LAWS W (va_env regs) _ ms (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
        ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp _ k STK_literal (spZ regs0 + e - spZ regs)
        [(q, q + 8); (v, v + 4)] (spZ regs - (spZ regs0 + e)) _ ch1
        _ HS eq_refl HJ).
      - unfold spZ at 1. rewrite P2. fold (spZ regs). slia.
      - rewrite Rregs. Z.div_mod_to_equations. lia.
      - rewrite Rregs. slia.
      - exact HSTKi.
      - rewrite Rregs. slia.
      - slia.
      - rewrite P3, (EW 3%nat (3%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R3. exact Hgp0.
      - rewrite P4, (EW 4%nat (4%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R4. exact Htp0.
      - exact P1.
      - apply (ret_ok_codeptr_v (PI := PI_prog_A)); [slia | reflexivity].
      - rewrite EB. unfold A_prog_base. rewrite unsigned_lit_small by slia. slia.
      - replace (spZ regs0 + e + (spZ regs - (spZ regs0 + e))) with (spZ regs) by slia. rewrite Hs0. exact Hach.
      - intros HPRE1. cbn [ss_pc setpc].
        assert (EM : ms_mem ms = mem).
        { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
          unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
        assert (Esp2 : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
        assert (Hd16 : (spZ regs0 - spZ regs) mod 16 = 0) by (rewrite Rregs; Z.div_mod_to_equations; lia).
        pose proof (vnd_v4096 Hnode) as Hv4096. pose proof (vnd_al8 Hnode) as Hval8. pose proof (vnd_rw Hnode) as Hrw. pose proof (vnd_zero Hnode) as Hzero. pose proof (vnd_at Hnode) as Hat. pose proof (vnd_amr Hnode) as Hamr. pose proof (vnd_own Hnode) as Hown. pose proof (vnd_ra Hnode) as Hra8.
        refine (HPI ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1
          (spZ regs0 + e - spZ regs) q text len p' (Z.of_nat d) tb (vrd_kw_addr 102) PjGrammar.w_false slack 1 v
          Lam peak cnt fail ran most own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
        { split; [exact HPRE1|]. split; [intros a H1 H2 H3; rewrite KM; exact (Hrod a H1 H2 H3)|].
          assert (Ehi : ly_stk_hi ly = ly_stk_hi ly0)
            by (exact (vly_stk_hi HLY0)).
          split; [rewrite Esp2, Rregs, Ehi; clear - Hshi He0 Hm32; slia|].
          (* fpre's ra bound (the cut's PRH_Base.v fpre): the return address is the jal's own return pc *)
          unfold raZ at 1. rewrite P1, EB. rewrite unsigned_lit_small by (unfold A_prog_base; slia).
          split; [exact vrd_ret224_lt_ceil | exact Hfrm]. }
        { rewrite P10, (EW 20%nat (20%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R20. }
        { rewrite P11. unfold vrd_kw_addr, vrd_kw_slot, vrd_kw_row. vm_compute. reflexivity. }
        { rewrite P12. reflexivity. }
        { rewrite P13, (EW 19%nat (19%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R19. }
        { rewrite EM. exact Hin. }
        { rewrite EM. replace (spZ regs0 + e - spZ regs) with (e + (spZ regs0 - spZ regs)) by slia.
          apply (vrd_fwin_shift ly W regs0 (ms_regs ms) mem e (spZ regs0 - spZ regs) Hfw); [slia | slia | exact Hd16 |].
          intros a Ha. apply HJpres1. rewrite Rregs in Ha. slia. }
        { rewrite Esp2. slia. }
        { rewrite Esp2. slia. }
        { rewrite EM. exact Hraq. }
        { rewrite EM. exact Hsrc. }
        { exact Hhome. }
        { rewrite EM. exact (proj1 (Hkw regs mem md eq_refl)). }
        { exact Hw63. }
        { rewrite EM. exact (proj2 (Hkw regs mem md eq_refl)). }
        { exact Hnul. }
        { exact Hslack. }
        { rewrite Esp2, Rregs. right.
          assert (Hm16 : (spZ regs0 - 160) mod 32 = 0 \/ (spZ regs0 - 160) mod 32 = 16).
          { clear - Hr16 Hm32. Z.div_mod_to_equations. lia. }
          clear - Hwstk HSTK HSTKi Hm16. slia. }
        { slia. }
        { slia. }
        { exact Hval8. }
        { replace (spZ regs0 + e - spZ regs) with (e + (spZ regs0 - spZ regs)) by slia.
          apply (vrd_reader_at_narrow B ly S Lam (ms_regs ms) (e + (spZ regs0 - spZ regs)) v 56 4);
          [apply (vrd_reader_at_shift B ly S Lam regs0 (ms_regs ms) e (spZ regs0 - spZ regs) v 56 Hat);
           [rewrite Esp2; slia | slia] | slia]. }
        { rewrite EM. apply (vrd_range_narrow _ _ v 56 4); [exact Hra8 | slia]. }
        { slia. }
        { assert (Hlen0 : 0 < len) by (clear - Ipp Hplt; lia). destruct (Htv Hlen0) as [H|H]; [right; slia | left; slia]. }
        { rewrite EM. exact Hled. }
      - intros a Ha. left. cbn [In rd_fp] in Ha |- *.
        destruct Ha as (r & [<- | [<- | []]] & Hr); cbn [fst snd] in Hr;
        [exists (q, q + 8); cbn [fst snd]; split; [left; reflexivity | slia]
        |exists (v, v + 56); cbn [fst snd]; split; [right; right; left; reflexivity | slia]]. }
    cbv beta. intros W2 c2 HW2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HWIN & HP2 & HQ).
    (* row 224 (`mv s5, a0`), the literal's return site: a fresh symbolic state there, at the same float state *)
    pose proof (va_entry W2 regs2 mem2 (vrd_row 224)) as HS2.
    rewrite EB in HS2.
    replace (pa_val A_TEXT + 19624) with (A_prog_base + vrd_row 224) by (rewrite EB; reflexivity).
    assert (HEI2 : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (va_env regs2)) by (unfold va_env; apply Eimg_env).
    assert (SHOK2 : sh_ok SEGS (SLit 0) [] (va_env regs2) (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
    pose (RUNTO2 := paj_run_to_x (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS).
    paj_run_to_tok_x RUNTO2 HS2 HJ2 SHOK2 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (vrd_row 225).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    pmkst HS2.
    prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (26%bv : bv 5) Q26.
    prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
    (* the big hypotheses the rest does not use: every lia below scans the whole context *)
    clear HPI Hchain0 Hcurch Hclos Hcur HFP Hrod Hkw HAGR HJkeep I0p I0e I0d I0rw I0g I0qt Ip Ie Id Irw Ig Iqt Sv8r Sv16r.
    assert (EW2 : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                    ew (va_env regs2) n = getr regs2 r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
    assert (EM2 : ms_mem ms0 = mem2).
    { apply functional_extensionality. intros x. apply HF0. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (EMc : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    (* the literal's footprint lies inside parse_value's reader cells *)
    assert (HFPs : forall a, inFP [(q, q + 8); (v, v + 4)] a -> inFP (rd_fp q v) a).
    { intros a (r & Hr & Hra). cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra;
      [exists (q, q + 8); split; [left; reflexivity | exact Hra]
      |exists (v, v + 56); cbn [fst snd]; split; [right; right; left; reflexivity | slia]]. }
    pose proof (ajx_ly HJc) as HLY.
    assert (EF : ly_F ly2 = ly_F ly) by (exact (vly_F HLY)).
    assert (Efr : frame_addr ly2 0 pos = frame_addr ly 0 pos) by (unfold frame_addr; rewrite EF; reflexivity).
    assert (Efl : flag_addr ly2 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite EF; reflexivity).
    assert (KS8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HP2 8); unfold acallee_saved; slia).
    assert (KS18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HP2 18); unfold acallee_saved; slia).
    assert (KS26 : getr regs2 26 = getr (ms_regs ms) 26) by (apply (HP2 26); unfold acallee_saved; slia).
    assert (KS24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HP2 24); unfold acallee_saved; slia).
    assert (KS3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HP2 3); unfold acallee_saved; slia).
    assert (KS4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HP2 4); unfold acallee_saved; slia).
    (* literal's post (the cut's PRH_FnReader.v blob f1ae32e3b2cd): its conjuncts BY SHAPE (decompose [and], then each named by
       its type); the keyword branch is one conjunct *)
    destruct HQ as (HQb & Hmk). decompose [and] HQb. clear HQb.
    lazymatch goal with X : room_live_cf S -> room_live_cf S2 |- _ => rename X into Hrl end.
    lazymatch goal with X : Hp2 = Hp |- _ => rename X into EHp end.
    lazymatch goal with X : S2 = S |- _ => rename X into ES end.
    lazymatch goal with X : ablocks B ly2 S2 = ablocks B ly S |- _ => rename X into Eab2 end.
    lazymatch goal with X : context [prh_ledger _ _ S2] |- _ => rename X into Hled2 end.
    lazymatch goal with X : match PjGrammar.prefixb _ _ with _ => _ end |- _ => rename X into Hbr end.
    (* P across the call: the m-form post's memnorm keep and srr_inv_call; row 224 writes no memory *)
    assert (HPc : P (ms_mem ms)) by (rewrite EMc; exact HPm).
    assert (HPr : P (ms_mem ms0)) by (rewrite EM2; exact (PC (ms_mem ms) mem2 Hmk HPc)).
    set (pre := PjGrammar.prefixb PjGrammar.w_false (rest_atR tb text p')) in Hbr.
    assert (Hrv : getr regs2 10 = w64 (if pre then 0 else -1))
      by (destruct pre; cbv beta iota in Hbr; decompose [and] Hbr; assumption).
    apply SRr_ret. split; [|exact HPr]. unfold vrd_arm_exit.
    exists fx, pos, (if pre then 0 else -1).
    (* the join BY NAME: VrdNum's record vrd_epi_R at the join's witnesses (vrd_epi_aR_of_R at wle), one named goal per
       field *)
    unfold vrd_epi_a.
    apply vrd_epi_aR_of_R with (regs := ms_regs ms0) (mem := ms_mem ms0)
      (md := with_vm_backing (m_vm_lazy md2) mat0 md2) (ly := ly2) (S := S2) (Hp := Hp2) (k := k + k1).
    refine {| vepi_cfg := ?[e_cfg]; vepi_jrn := ?[e_jrn]; vepi_win := ?[e_win]; vepi_s0 := ?[e_s0]; vepi_s2 := ?[e_s2];
              vepi_s10 := ?[e_s10]; vepi_s8 := ?[e_s8]; vepi_s5 := ?[e_s5]; vepi_gp := ?[e_gp]; vepi_tp := ?[e_tp];
              vepi_ra := ?[e_ra]; vepi_saved := ?[e_saved]; vepi_flag := ?[e_flag]; vepi_frm := ?[e_frm];
              vepi_fregs := ?[e_fregs]; vepi_rq := ?[e_rq] |}.
    [e_cfg]: { rewrite vrd_pc_epi; reflexivity. }
    (* vrd_epi_a's journal: the literal's text posts no wild budget (fpostWm), so the journal is the budget-free one
       (ajournal_x is ajournal_xw at []) and wbudget CW 0 [] holds by computation *)
    [e_jrn]: { exists []. split; [exact HJ2 | unfold YCbqGwild.wbudget, YCbqGwild.wfresh; cbn; lia]. }
    [e_win]: { intros a Ha Hn. rewrite EM2, (HWIN a ltac:(slia) (fun H => Hn (HFPs a H))), EMc. exact (Hwin a Ha Hn). }
    [e_s0]: { rewrite Q8, (EW2 8%nat (8%bv : bv 5)) by va_cs2; rewrite KS8; rewrite P8; exact R8. }
    [e_s2]: { rewrite Efr, Q18, (EW2 18%nat (18%bv : bv 5)) by va_cs2; rewrite KS18;
              rewrite P18, (EW 18%nat (18%bv : bv 5)) by va_cs2; exact R18. }
    [e_s10]: { rewrite Efr, Q26, (EW2 26%nat (26%bv : bv 5)) by va_cs2; rewrite KS26;
               rewrite P26, (EW 26%nat (26%bv : bv 5)) by va_cs2; exact R26. }
    [e_s8]: { rewrite Efr, Q24, (EW2 24%nat (24%bv : bv 5)) by va_cs2; rewrite KS24;
              rewrite P24, (EW 24%nat (24%bv : bv 5)) by va_cs2; exact R24. }
    [e_s5]: { rewrite Q21, (EW2 10%nat (10%bv : bv 5)) by va_cs2; exact Hrv. }
    [e_gp]: { rewrite Q3, (EW2 3%nat (3%bv : bv 5)) by va_cs2; rewrite KS3;
              rewrite P3, (EW 3%nat (3%bv : bv 5)) by va_cs2; exact R3. }
    [e_tp]: { rewrite Q4, (EW2 4%nat (4%bv : bv 5)) by va_cs2; rewrite KS4;
              rewrite P4, (EW 4%nat (4%bv : bv 5)) by va_cs2; exact R4. }
    [e_ra]: exact Hra0.
    (* the thirteen spilled words: parse_value's own frame below spZ regs0, outside rd_fp q v (the cursor is above
       spZ regs0, the node outside parse_value's stack window), kept by the callee's window clause and both runs *)
    [e_saved]: { assert (KSV : forall a, spZ regs0 - 104 <= a < spZ regs0 ->
                aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
      { intros a Ha. rewrite EM2. rewrite (HWIN a); [rewrite EMc; reflexivity | rewrite Rregs; slia |].
        intros (r & Hrin & Hr). cbn [In] in Hrin.
        destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; [slia |].
        pose proof (vnd_own Hnode) as Hown.
        destruct (Hown a ltac:(slia)) as [_ Hn]. apply Hn. slia. }
      unfold vrd_saved in Hsaved |- *.
      destruct Hsaved as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (eapply val_mem_kept; [|eassumption]; intros kk Hk; cbn in Hk; apply KSV; slia). }
    (* the flag word at F + 56: it lies in parse_value's OWN fake frame, which is below alloc_ceiling, and outside the
       callee's footprint rd_fp q v (the cursor is a stack address above alloc_ceiling; the node cannot meet the frame:
       a block is apart from a frame, another frame is apart from this one, and this frame itself would put the
       descriptor word at F + 16 inside the node's 56 ZEROED bytes). So the callee's journal frames clause keeps it. *)
    [e_flag]: { rewrite Efr, Efl.
      pose proof (ajx_ar HJ0) as HAR. cbv beta in HAR.
      assert (HinF : In (0, pos) (frames S)) by (rewrite Hfr; left; reflexivity).
      destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HFa0 & HFc & HFapp).
      assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFc.
      pose proof (vfrm3 Hframe) as (Hmag & Hsig & Hflag).
      pose proof (vnd_v4096 Hnode) as Hv4096. pose proof (vnd_al8 Hnode) as Hval8. pose proof (vnd_rw Hnode) as Hrw. pose proof (vnd_zero Hnode) as Hzero. pose proof (vnd_at Hnode) as Hat. pose proof (vnd_amr Hnode) as Hamr. pose proof (vnd_own Hnode) as Hown. pose proof (vnd_ra Hnode) as Hra8.
      pose proof (@cf_head_nonneg cp) as Hhd0.
      assert (HvF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> ~ (v <= a < v + 56)).
      { intros a Ha Hav.
        destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                        [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
        - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
          pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
          apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (a0 - cf_head) (k0 + cf_head) a HAR HinF Habk);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hk0h : 0 <= k0 + cf_head) by slia.
          pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq). slia.
        - apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) b0 m0 a HAR HinF Hinb);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hm00 : 0 <= m0) by slia.
          pose proof (req_size_pos m0 Hm00) as (_ & Hrq). slia.
        - rewrite Hfr in Hinf. destruct Hinf as [Ef | Hinf].
          + injection Ef as <- <-.
            assert (Hz16 : val_mem SEGS (mrestrict (w_H W) mem) (frame_addr ly 0 pos + 16) 8 0).
            { apply (vrd_zero_val SEGS (mrestrict (w_H W) mem) v); [exact Hzero | rewrite Hfb in Hhif; slia | rewrite Hfb in Hhif; slia]. }
            pose proof (Hsig 0%nat ltac:(slia)) as E1. pose proof (Hz16 0%nat ltac:(slia)) as E2.
            cbn [Z.of_nat] in E1, E2. rewrite Z.add_0_r in E1, E2.
            rewrite E1 in E2. vm_compute in E2. discriminate E2.
          + apply in_split in Hinf as (l2 & l3 & El).
            pose proof (sep_frames_pos_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (cid, pos') (@nil (Z * Z)) l2 l3 HAR
              ltac:(rewrite Hfr, El; reflexivity)) as Hd.
            unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Hfb in Hd. slia.
        - slia. }
      assert (HqF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> a < q).
      { intros a Ha. pose proof (vastk HJstk0) as (_ & _ & Hclo2 & Hlo2 & _). slia. }
      assert (HnFP : forall a, frame_addr ly 0 pos + 56 <= a < frame_addr ly 0 pos + 64 ->
                 ~ inFP [(q, q + 8); (v, v + 4)] a).
      { intros a Ha (r & Hrin & Hr). cbn [In] in Hrin.
        destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr;
        [pose proof (HqF a ltac:(slia)); slia | exact (HvF a ltac:(slia) ltac:(slia))]. }
      pose proof (ajx_frm HJc) as HJfr.
      eapply val_mem_kept; [|exact Hflag]. intros kk Hk. cbn in Hk.
      rewrite EM2, <- EMc.
      apply (HJfr 0 pos (frame_addr ly 0 pos + 56 + kk) HinF);
      [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia
      | apply HnFP; slia]. }
    [e_frm]: exact Hfrm.
    [e_fregs]: { intros r _; reflexivity. }
    (* ---- RQ: the literal's post read as parse_value's (VnumC's vrd_pv_post), with no allocation: D = [], BY NAME:
       VrdNum's record vrd_pv_R (vrd_pv_post_of_R), one named goal per field ---- *)
    [e_rq]: {
    pose proof Hled as HLB. apply prh_ledger_bounds in HLB. destruct HLB as (Hlp & Hpk & Hcn & Hfl & Hrn).
    pose proof (vnd_v4096 Hnode) as Hv4096n. pose proof (vnd_al8 Hnode) as Hval8n. pose proof (vnd_rw Hnode) as Hrwn. pose proof (vnd_zero Hnode) as Hzeron. pose proof (vnd_at Hnode) as Hatn. pose proof (vnd_amr Hnode) as Hamrn. pose proof (vnd_own Hnode) as Hownn. pose proof (vnd_ra Hnode) as Hra8n.
    pose proof (ajx_ar HJc) as HAR2. cbv beta in HAR2.
    assert (Ex : rest_atR tb text p' = 102 :: yy) by (rewrite Hrest; exact Hsk).
    (* the node's bytes the call did not write are kept: the node is a harness block, an allocator block or a
       frame (the window case is excluded by HVLO), and the callee journal keeps blocks and frames off FP1 *)
    assert (HNK : forall a, v <= a < v + 56 -> ~ inFP [(q, q + 8); (v, v + 4)] a ->
              aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
    { intros a Ha Hn. rewrite <- EMc.
      pose proof (ajx_ly HJc) as HLYc. pose proof (ajx_blk HJc) as HJb. pose proof (ajx_frm HJc) as HJf.
      destruct Hatn as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                       [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        pose proof (@cf_head_nonneg cp) as Hhd0.
        assert (Hk0h : 0 <= k0 + cf_head) by slia.
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        replace a with ((a0 - cf_head) + (a - (a0 - cf_head))) by slia.
        apply (HJb (a0 - cf_head) (k0 + cf_head) (a - (a0 - cf_head))); [exact Habk | rewrite Eab2; exact Habk | slia |].
        replace ((a0 - cf_head) + (a - (a0 - cf_head))) with a by slia. exact Hn.
      - assert (Hm00 : 0 <= m0) by slia.
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        replace a with (b0 + (a - b0)) by slia.
        apply (HJb b0 m0 (a - b0)); [exact Hinb | rewrite Eab2; exact Hinb | slia |].
        replace (b0 + (a - b0)) with a by slia. exact Hn.
      - apply (HJf cid pos' a Hinf); [left; unfold in_zr, frame_rng; cbn [fst snd]; slia | exact Hn].
      - slia. }
    (* the node bytes beyond the type word, at the end, are the dispatch's: zero *)
    assert (VK : forall a n x, v + 4 <= a -> a + Z.of_nat n <= v + 56 ->
              val_mem SEGS (mrestrict (w_H W) mem) a n x -> val_mem SEGS (mrestrict (w_H W2) mem2) a n x).
    { intros a n x H1 H2 Hv kk Hk.
      rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
      apply HNK; [slia|]. intros (r & Hrin & Hr). cbn [In] in Hrin.
      destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; slia. }
    (* every node byte is present at the end (a block or a frame of the end state), so writable *)
    assert (HWR : forall a, v <= a < v + 56 -> writable_at SEGS (mrestrict (w_H W2) mem2) a).
    { intros a Ha. apply apresent_writable.
      pose proof (ajx_ly HJc) as HLYc.
      assert (EFc : ly_F ly2 = ly_F ly) by (exact (vly_F HLYc)).
      pose proof (vnd_at Hnode) as Hat2.
      destruct Hat2 as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                       [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        pose proof (@cf_head_nonneg cp) as Hhd0.
        assert (Hk0h : 0 <= k0 + cf_head) by slia.
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        rewrite <- Eab2 in Habk.
        destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Habk) as (_ & _ & _ & _ & Hb & _).
        exact (proj1 (Hb a ltac:(slia))).
      - assert (Hm00 : 0 <= m0) by slia.
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        rewrite <- Eab2 in Hinb.
        destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hinb) as (_ & _ & _ & _ & Hb & _).
        exact (proj1 (Hb a ltac:(slia))).
      - assert (Hinf2 : In (cid, pos') (frames S2)) by (rewrite ES; exact Hinf).
        destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos' HAR2 Hinf2) as (_ & _ & Hfp & _).
        assert (Efa : frame_addr ly2 cid pos' = frame_addr ly cid pos') by (unfold frame_addr; rewrite EFc; reflexivity).
        rewrite Efa in Hfp. exact (proj1 (Hfp a ltac:(slia))).
      - slia. }
    rewrite EM2.
    apply vrd_pv_post_of_R with (ok := [])
      (res := if pre then Some (JFalse, skipn (length PjGrammar.w_false) (102 :: yy)) else None) (tr := []) (okr := [])
      (D := []) (Lam' := Lam) (peak' := peak) (cnt' := cnt) (fail' := fail) (ran' := ran).
    (* the literal allocates nothing: its value is the keyword's, at ok = [] (EJ), and its granted trace is
       empty (vrd_gtrace_lit); S2 = S, which is S0 up to its fake frames (`S = set_fs f S0`) *)
    assert (EJ : jr_value ReaderRes.jr_strtod d (rest_atR tb text p) [] =
                 ((if pre then Some (JFalse, skipn (length PjGrammar.w_false) (102 :: yy)) else None), [], [])).
    { rewrite (vrd_lit_model ReaderRes.jr_strtod d 102 yy (rest_atR tb text p) [] Hsk (or_intror (or_introl eq_refl))).
      cbn [Z.eqb Pos.eqb]. unfold PjGrammar.lit, PjGrammar.jret, PjGrammar.jrefuse. unfold pre. rewrite Ex.
      destruct (PjGrammar.prefixb PjGrammar.w_false (102 :: yy)); reflexivity. }
    pose proof (vrd_gtrace_lit d 102 yy (rest_atR tb text p) Hsk (or_intror (or_introl eq_refl))) as EG0.
    destruct Hsetfs as (fz & Efz).
    refine {| vpv_run := ?[p_run]; vpv_ledger := ?[p_ledger]; vpv_room := ?[p_room]; vpv_hull := ?[p_hull];
              vpv_live := ?[p_live]; vpv_pos := ?[p_pos]; vpv_outcome := ?[p_outcome]; vpv_injected := ?[p_injected];
              vpv_ledger_move := ?[p_ledger_move]; vpv_fresh := ?[p_fresh]; vpv_blocks := ?[p_blocks];
              vpv_frames := ?[p_frames]; vpv_hpeak := ?[p_hpeak]; vpv_bytes := ?[p_bytes]; vpv_lsum := ?[p_lsum];
              vpv_arm := ?[p_arm] |}.
    [p_run]: exact EJ.
    [p_ledger]: exact Hled2.
    [p_room]: exact (Hrl (vrr_live _ _ Hroom)).
    (* the hull use: the granted trace is empty (EG0) and S2 = S, which has S0's st_secs (`S = set_fs f S0`) *)
    [p_hull]: { rewrite EG0; apply PresetHullBudget.hull_used_secs; rewrite ES, Efz; reflexivity. }
    [p_live]: { rewrite ES, Efz. change (PresetReqAt.rd_hevs []) with (@nil PresetReqAt.hev).
      rewrite PresetReqAt.hlive_from_nil.
      change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
        with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)).
      apply Permutation_refl. }
    [p_pos]: { intros sm x os i Hz0 hist Hpos _. exists hist. rewrite ES, Efz.
      change (length (PresetReqAt.rd_hevs [])) with 0%nat. rewrite Nat.add_0_r.
      apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
    [p_outcome]: { intros sm x os i Hz0 hist Hpos _ _ _. split; [reflexivity|]. split; [rewrite EJ; reflexivity|].
      exists hist. rewrite EG0, ES, Efz.
      change (length (PresetReqAt.rd_hevs [])) with 0%nat. rewrite Nat.add_0_r.
      apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
    (* the injected reading: vacuous, the granted trace is empty (EG0), so the window cnt <= fail < cnt is empty *)
    [p_injected]: { intros sm x os i Hz0 hist _ _ _ Hwd; rewrite EG0 in Hwd; cbn [PjGrammar.calls Z.of_nat] in Hwd;
            exfalso; slia. }
    [p_ledger_move]: { unfold rd_ledger_move. cbn [PjGrammar.calls lszR nliveR hpeakR map length app].
      split; [split; [intros i Hi; cbn in Hi; slia | split; [left; reflexivity | intros i Hi; cbn in Hi; slia]]|].
      split; [rewrite Z.add_0_r, Z.mod_small by slia; reflexivity|].
      split; [split; intros Hc; cbn in Hc; [slia | reflexivity]|].
      split; [apply Permutation_refl|].
      split; [constructor|].
      split; [reflexivity|].
      unfold prh_refused_peak. cbn [List.seq map fold_right]. clear - Hlp. lia. }
    [p_fresh]: { intros aa kk Hak; destruct Hak. }
    [p_blocks]: { rewrite Eab2, Hab; cbn [prhReader_ab map app]; apply Permutation_refl. }
    [p_frames]: { rewrite ES, Hfr; apply Permutation_refl. }
    [p_hpeak]: { cbn [hpeakR]; slia. }
    [p_bytes]: { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly0 S0), Eab2, Hab.
      unfold prh_held. cbn [PjGrammar.held PjGrammar.calls fold_right map Z.of_nat]. slia. }
    [p_lsum]: reflexivity.
    [p_arm]: {
    unfold pre in Hbr |- *. rewrite Ex in Hbr |- *.
    destruct (PjGrammar.prefixb PjGrammar.w_false (102 :: yy)) eqn:Epre.
    + (* the keyword matched: the node is JFalse, the cursor advanced by four *)
      cbv beta iota in Hbr. decompose [and] Hbr. clear Hbr.
      lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W2) mem2) q text len _ _ tb |- _ => rename X into Hin2 end.
      lazymatch goal with X : val_mem _ (mrestrict (w_H W2) mem2) v 4 _ |- _ => rename X into Hty2 end.
      assert (Elen : Z.of_nat (length (102 :: yy)) = text + len - p').
      { rewrite <- Ex. unfold rest_atR. rewrite length_skipn.
        pose proof (vin_pp Hin) as Hpp'. pose proof (vin_len Hin) as Hlen'. slia. }
      assert (Hge4 : 5 <= Z.of_nat (length (102 :: yy))).
      { clear - Epre. destruct yy as [|c1 [|c2 [|c3 [|c4 yy']]]]; cbn in Epre |- *; try discriminate; slia. }
      (* the node's header, shared by its free order and its node clause *)
      assert (HHDl : pj_hdrR SEGS (mrestrict (w_H W2) mem2) v (tag JFalse) 0 0 0 0 0 0).
      {
        split; [split; [exact Hval8n | intros xw Hxw; exact (HWR xw Hxw)]|].
        split; [split; [cbn; slia | exact Hty2]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 8) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 16) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 24) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 32) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 40) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 48) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]].
      }
      assert (HAPl : pj_apartR [] v) by (intros bb x Hb; destruct Hb).
      refine {| vpvs_rv := ?[s_rv]; vpvs_freeord := ?[s_freeord]; vpvs_in_ok := ?[s_in_ok]; vpvs_node := ?[s_node];
                vpvs_ncap := ?[s_ncap]; vpvs_lsum_le := ?[s_lsum_le] |}.
      [s_rv]: reflexivity.
      (* the free order (PRH_PjOrder.pfo_leaf): a leaf with no block frees nothing, and the value's free list at a
         keyword is [] (vrd_frees_lit) *)
      [s_freeord]: { intros _ nn _. exists []. split.
        - exact (PRH_PjOrder.pfo_leaf SEGS _ _ nn v (tag JFalse) 0 0 [] ltac:(constructor) HAPl HHDl (or_introl (conj eq_refl eq_refl))).
        - rewrite (vrd_frees_lit d 102 yy (rest_atR tb text p) [] Hsk (or_intror (or_introl eq_refl))). reflexivity. }
      [s_in_ok]: { assert (Epos : text + len - Z.of_nat (length (skipn (length PjGrammar.w_false) (102 :: yy))) =
                       p' + Z.of_nat (length PjGrammar.w_false)).
        { rewrite length_skipn. cbn [length PjGrammar.w_false] in *. slia. }
        rewrite Epos. exact Hin2. }
      [s_node]: { split; [constructor|]. split; [intros bb x Hb; destruct Hb|].
        exists 0, 0, 0, 0, 0, 0. split; [exact HHDl | repeat split; reflexivity]. }
      (* the leaf's capacity words: pj_ncapR of a keyword is True *)
      [s_ncap]: exact I.
      [s_lsum_le]: { pose proof (vrd_rest_shrink tb text p p' (proj1 Hpp)) as Hshr. rewrite Ex in Hshr.
        cbn [Ledger.lsum]. rewrite length_skipn. cbn [length PjGrammar.w_false] in *. slia. }
    + (* the keyword did not match: the cursor and the node are untouched *)
      cbv beta iota in Hbr. decompose [and] Hbr. clear Hbr.
      lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W2) mem2) q text len _ _ tb |- _ => rename X into Hin2 end.
      lazymatch goal with X : forall a, q <= a < q + 8 \/ _ -> _ |- _ => rename X into Hkeep end.
      assert (HRW2 : pj_rwR SEGS (mrestrict (w_H W2) mem2) v)
        by (split; [exact Hval8n | intros xw Hxw; exact (HWR xw Hxw)]).
      assert (HZ2 : pj_zeroR SEGS (mrestrict (w_H W2) mem2) v).
      {
        unfold pj_zeroR in *. intros jj Hjj. destruct (Hzeron jj Hjj) as (Hz1 & Hz2). split; [|exact Hz2].
        intros kk Hkk. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 (v + Z.of_nat jj + Z.of_nat kk)).
        + exact (Hz1 kk Hkk).
        + rewrite repeat_length in Hjj. cbn in Hkk.
          destruct (Z_lt_le_dec (v + Z.of_nat jj + Z.of_nat kk) (v + 4)) as [Hlo|Hhi].
          * rewrite <- EMc. apply Hkeep. right. slia.
          * apply HNK; [slia|]. intros (r & Hrin & Hr). cbn [In] in Hrin.
            destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; slia.
      }
      refine {| vpvn_rv := ?[n_rv]; vpvn_freeord := ?[n_freeord]; vpvn_in_after := ?[n_in_after];
                vpvn_fd := ?[n_fd] |}.
      [n_rv]: reflexivity.
      (* the free order of the untouched (zero) node: its order list is [] (VrdNum.vrd_zero_fo), and the value's free
         list at a keyword is [] (vrd_frees_lit) *)
      [n_freeord]: { intros _ nn _. exists []. split.
        - exact (vrd_zero_fo SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) v nn HRW2 HZ2).
        - rewrite (vrd_frees_lit d 102 yy (rest_atR tb text p) [] Hsk (or_intror (or_introl eq_refl))). reflexivity. }
      [n_in_after]: { pose proof (vin_p Hin2) as J1. pose proof (vin_end Hin2) as J2. pose proof (vin_d Hin2) as J3. pose proof (vin_rw Hin2) as J4. pose proof (vin_q8 Hin2) as J5. pose proof (vin_t Hin2) as J6. pose proof (vin_tl Hin2) as J7. pose proof (vin_pp Hin2) as J8. pose proof (vin_len Hin2) as J9. pose proof (vin_g Hin2) as J10. pose proof (vin_qt Hin2) as J11. pose proof (vin_d32 Hin2) as J12.
        exists p', (Z.of_nat d). split; [slia|]. split; [slia|].
        split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. exact J4. }
      [n_fd]: exact (vrd_zero_fd SEGS _ _ v _ HRW2 HZ2). }
    }
  - paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    prreg HS (2%bv : bv 5) P2. prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
    prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
    prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
    prreg HS (18%bv : bv 5) P18. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
    pose proof HJ as HJ0b.
    pose proof (vastk HJstk0) as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
    pose proof (vfw Hfw) as (He0 & He16 & Hetop & Hepres).
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    pose proof (Z.mod_pos_bound (spZ regs0 - 160) 32 ltac:(slia)) as Hm32.
    assert (Hr16 : spZ regs0 mod 16 = 0)
      by (rewrite Zplus_mod, He16, Z.add_0_r, Zmod_mod in Hsp16; exact Hsp16).
    (* the dispatch's alignment slack is 0 or 16 (spZ regs0 is 16-aligned), stated once for the slia calls below *)
    assert (Hsl16 : (spZ regs0 - 160) mod 32 <= 16) by (clear - Hr16 Hm32; Z.div_mod_to_equations; lia).
    assert (Hx : 0 <= spZ regs0 - 160 - (spZ regs0 - 160) mod 32 < 2 ^ 64) by slia.
    assert (Rregs : spZ regs = spZ regs0 - 160 - (spZ regs0 - 160) mod 32).
    { unfold spZ at 1. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by exact Hx. reflexivity. }
    assert (EW : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                   ew (va_env regs) n = getr regs r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
    rewrite (EW 2%nat (2%bv : bv 5)) in P2 by (vm_compute; reflexivity || slia).
    assert (KM : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
    { intros a. symmetry. unfold aview. f_equal. unfold mbyte.
      rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    (* ---- the facts every chain lemma of VproC asks, gathered once ---- *)
    pose proof HJstk0 as HJstk.
    pose proof (vin_p Hin0) as I0p. pose proof (vin_end Hin0) as I0e. pose proof (vin_d Hin0) as I0d. pose proof (vin_rw Hin0) as I0rw. pose proof (vin_q8 Hin0) as I0q8. pose proof (vin_t Hin0) as I0t. pose proof (vin_tl Hin0) as I0tl. pose proof (vin_pp Hin0) as I0pp. pose proof (vin_len Hin0) as I0len. pose proof (vin_g Hin0) as I0g. pose proof (vin_qt Hin0) as I0qt. pose proof (vin_d32 Hin0) as I0d32.
    pose proof (vin_p Hin) as Ip. pose proof (vin_end Hin) as Ie. pose proof (vin_d Hin) as Id. pose proof (vin_rw Hin) as Irw. pose proof (vin_q8 Hin) as Iq8. pose proof (vin_t Hin) as It. pose proof (vin_tl Hin) as Itl. pose proof (vin_pp Hin) as Ipp. pose proof (vin_len Hin) as Ilen. pose proof (vin_g Hin) as Ig. pose proof (vin_qt Hin) as Iqt. pose proof (vin_d32 Hin) as Id32.
    pose proof (vsr_4096 Hsrc) as Hs4096. pose proof (vsr_ceil Hsrc) as Hsac.
    pose proof (ajx_ly HJ0) as HLY0. pose proof (ajx_hi HJ0) as HJkeep.
    assert (Etop : ly_top ly = ly_top ly0)
      by (exact (vly_top HLY0)).
    pose proof (vsav12 Hsaved) as (Sv8 & Sv16).
    assert (EMc0 : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (Sv8r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 8) = Some (raZ regs0))
      by (apply vrd_rdword_of_val_mem; [exact Sv8 | apply bv_unsigned_in_range]).
    assert (Sv16r : rdword (aview SEGS (w_H W) mem) (spZ regs0 - 16) = Some (s0Z regs0))
      by (unfold s0Z; apply vrd_rdword_of_val_mem; [exact Sv16 | apply bv_unsigned_in_range]).
    assert (HAGR : forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
                     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a).
    { pose proof (vastk HJstk) as (_ & HSTKa & Hceila & Hsloa & _).
      intros a Ha Hn. destruct (Z_lt_le_dec a (spZ regs0 + e)) as [Hlt|Hge].
      - apply Hwin; [clear - Ha Hlt; slia | exact Hn].
      - apply HJkeep; [clear - Ha Hge Hceila Hsloa HSTK HSTKi; slia | clear - Hge; slia]. }
    assert (Hsp8 : spZ regs0 mod 8 = 0) by (clear - Hr16; Z.div_mod_to_equations; lia).
    assert (HVLO : v + 56 <= spZ regs0).
    { destruct Hvwin as [Hv|Hv]; [exact Hv|].
      pose proof (vnd_at Hnode) as Hat. pose proof (vnd_own Hnode) as Hown. exfalso.
      pose proof (ajx_ar HJ0) as HARd. cbv beta in HARd.
      pose proof (vastk HJstk) as (_ & HSTKn & Hceil1 & Hslo1 & _).
      pose proof (@cf_head_nonneg cp) as Hhd0.
      destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                      [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      + pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARd Habk) as (_ & _ & Hcb & _).
        assert (Hk0h : 0 <= k0 + cf_head) by (clear - Hk0 Hhd0; slia).
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        clear - Hle0 Hhi0 Hcb Hrq Hhd0 Hv Hceil1 Hslo1 HSTKn; slia.
      + destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b0 m0 HARd Hinb) as (_ & _ & Hcb & _).
        assert (Hm00 : 0 <= m0) by (clear - Hhib Hleb; slia).
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        clear - Hleb Hhib Hcb Hrq Hv Hceil1 Hslo1 HSTKn; slia.
      + destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HARd Hinf) as (_ & Hfc & _).
        clear - Hlef Hhif Hfc Hv Hceil1 Hslo1 HSTKn; slia.
      + clear - Hw2 Hv; slia. }
    (* the chain at the call view, by VproC's keep lemma vrd_disp_chain *)
    assert (HCH : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms)) (spZ regs) (spZ regs0) ch1 /\
                  spine ch1 = raZ regs0 :: spine ch).
    { rewrite EMc0.
      pose proof (vastk HJstk) as (Hsp16c & HSTK0c & Hceilc & Hsloc & Hshic & H47c & Hbotc & Htopc & Htop2c).
      apply (vrd_disp_chain ly0 ly W0 W mem0 mem regs0 ch q v (spZ regs) p p' Hchain0 Hcur).
      - apply vrd_rdword_of_val_mem; [exact I0p | clear - I0pp I0t I0tl; slia].
      - clear - I0pp Hs4096; slia.
      - clear - I0pp HTC; slia.
      - apply vrd_rdword_of_val_mem; [exact Ip | clear - Ipp It Itl; slia].
      - clear - Ipp HTC; slia.
      - clear - Hq1 Hceilc Hsloc HSTK HSTKi; slia.
      - exact Iq8.
      - exact Etop.
      - clear - Htop2c H47c; slia.
      - clear - Hceilc Hsloc HSTK HSTKi; slia.
      - rewrite Rregs. clear - Hm32; slia.
      - clear - Htopc Hq1 Hq2; slia.
      - exact Hsp8.
      - exact Hra4k.
      - exact Sv8r.
      - exact Sv16r.
      - exact HAGR.
      - exact HVLO.
      - intros a Ha. unfold aview.
        assert (Hk : (Z.to_nat (a - (q + 16)) < 4)%nat) by (clear - Ha; slia).
        pose proof (I0d _ Hk) as E0. pose proof (Id _ Hk) as E1.
        rewrite Z2Nat.id in E0, E1 by (clear - Ha; slia).
        replace (q + 16 + (a - (q + 16))) with a in E0, E1 by ring.
        rewrite E0, E1. reflexivity. }
    destruct HCH as (ch1 & Hach & Hspine).
    rewrite (EW 8%nat (8%bv : bv 5)) in P8 by (vm_compute; reflexivity || slia).
    assert (Hs0 : s0Z (ms_regs ms) = spZ regs0).
    { unfold s0Z. rewrite P8, R8. unfold w64. apply unsigned_lit_small. slia. }
    eapply SRr_bind.
    { eapply (vrd_call_W B ARx SK LAWS W (va_env regs) _ ms (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
        ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp _ k STK_literal (spZ regs0 + e - spZ regs)
        [(q, q + 8); (v, v + 4)] (spZ regs - (spZ regs0 + e)) _ ch1
        _ HS eq_refl HJ).
      - unfold spZ at 1. rewrite P2. fold (spZ regs). slia.
      - rewrite Rregs. Z.div_mod_to_equations. lia.
      - rewrite Rregs. slia.
      - exact HSTKi.
      - rewrite Rregs. slia.
      - slia.
      - rewrite P3, (EW 3%nat (3%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R3. exact Hgp0.
      - rewrite P4, (EW 4%nat (4%bv : bv 5)) by (vm_compute; reflexivity || slia). rewrite R4. exact Htp0.
      - exact P1.
      - apply (ret_ok_codeptr_v (PI := PI_prog_A)); [slia | reflexivity].
      - rewrite EB. unfold A_prog_base. rewrite unsigned_lit_small by slia. slia.
      - replace (spZ regs0 + e + (spZ regs - (spZ regs0 + e))) with (spZ regs) by slia. rewrite Hs0. exact Hach.
      - intros HPRE1. cbn [ss_pc setpc].
        assert (EM : ms_mem ms = mem).
        { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
          unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
        assert (Esp2 : spZ (ms_regs ms) = spZ regs) by (unfold spZ at 1; rewrite P2; reflexivity).
        assert (Hd16 : (spZ regs0 - spZ regs) mod 16 = 0) by (rewrite Rregs; Z.div_mod_to_equations; lia).
        pose proof (vnd_v4096 Hnode) as Hv4096. pose proof (vnd_al8 Hnode) as Hval8. pose proof (vnd_rw Hnode) as Hrw. pose proof (vnd_zero Hnode) as Hzero. pose proof (vnd_at Hnode) as Hat. pose proof (vnd_amr Hnode) as Hamr. pose proof (vnd_own Hnode) as Hown. pose proof (vnd_ra Hnode) as Hra8.
        refine (HPI ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1
          (spZ regs0 + e - spZ regs) q text len p' (Z.of_nat d) tb (vrd_kw_addr 110) PjGrammar.w_null slack 0 v
          Lam peak cnt fail ran most own _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
        { split; [exact HPRE1|]. split; [intros a H1 H2 H3; rewrite KM; exact (Hrod a H1 H2 H3)|].
          assert (Ehi : ly_stk_hi ly = ly_stk_hi ly0)
            by (exact (vly_stk_hi HLY0)).
          split; [rewrite Esp2, Rregs, Ehi; clear - Hshi He0 Hm32; slia|].
          (* fpre's ra bound (the cut's PRH_Base.v fpre): the return address is the jal's own return pc *)
          unfold raZ at 1. rewrite P1, EB. rewrite unsigned_lit_small by (unfold A_prog_base; slia).
          split; [exact vrd_ret224_lt_ceil | exact Hfrm]. }
        { rewrite P10, (EW 20%nat (20%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R20. }
        { rewrite P11. unfold vrd_kw_addr, vrd_kw_slot, vrd_kw_row. vm_compute. reflexivity. }
        { rewrite P12. reflexivity. }
        { rewrite P13, (EW 19%nat (19%bv : bv 5)) by (vm_compute; reflexivity || slia). exact R19. }
        { rewrite EM. exact Hin. }
        { rewrite EM. replace (spZ regs0 + e - spZ regs) with (e + (spZ regs0 - spZ regs)) by slia.
          apply (vrd_fwin_shift ly W regs0 (ms_regs ms) mem e (spZ regs0 - spZ regs) Hfw); [slia | slia | exact Hd16 |].
          intros a Ha. apply HJpres1. rewrite Rregs in Ha. slia. }
        { rewrite Esp2. slia. }
        { rewrite Esp2. slia. }
        { rewrite EM. exact Hraq. }
        { rewrite EM. exact Hsrc. }
        { exact Hhome. }
        { rewrite EM. exact (proj1 (Hkw regs mem md eq_refl)). }
        { exact Hw63. }
        { rewrite EM. exact (proj2 (Hkw regs mem md eq_refl)). }
        { exact Hnul. }
        { exact Hslack. }
        { rewrite Esp2, Rregs. right.
          assert (Hm16 : (spZ regs0 - 160) mod 32 = 0 \/ (spZ regs0 - 160) mod 32 = 16).
          { clear - Hr16 Hm32. Z.div_mod_to_equations. lia. }
          clear - Hwstk HSTK HSTKi Hm16. slia. }
        { slia. }
        { slia. }
        { exact Hval8. }
        { replace (spZ regs0 + e - spZ regs) with (e + (spZ regs0 - spZ regs)) by slia.
          apply (vrd_reader_at_narrow B ly S Lam (ms_regs ms) (e + (spZ regs0 - spZ regs)) v 56 4);
          [apply (vrd_reader_at_shift B ly S Lam regs0 (ms_regs ms) e (spZ regs0 - spZ regs) v 56 Hat);
           [rewrite Esp2; slia | slia] | slia]. }
        { rewrite EM. apply (vrd_range_narrow _ _ v 56 4); [exact Hra8 | slia]. }
        { slia. }
        { assert (Hlen0 : 0 < len) by (clear - Ipp Hplt; lia). destruct (Htv Hlen0) as [H|H]; [right; slia | left; slia]. }
        { rewrite EM. exact Hled. }
      - intros a Ha. left. cbn [In rd_fp] in Ha |- *.
        destruct Ha as (r & [<- | [<- | []]] & Hr); cbn [fst snd] in Hr;
        [exists (q, q + 8); cbn [fst snd]; split; [left; reflexivity | slia]
        |exists (v, v + 56); cbn [fst snd]; split; [right; right; left; reflexivity | slia]]. }
    cbv beta. intros W2 c2 HW2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HWIN & HP2 & HQ).
    (* row 224 (`mv s5, a0`), the literal's return site: a fresh symbolic state there, at the same float state *)
    pose proof (va_entry W2 regs2 mem2 (vrd_row 224)) as HS2.
    rewrite EB in HS2.
    replace (pa_val A_TEXT + 19624) with (A_prog_base + vrd_row 224) by (rewrite EB; reflexivity).
    assert (HEI2 : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (va_env regs2)) by (unfold va_env; apply Eimg_env).
    assert (SHOK2 : sh_ok SEGS (SLit 0) [] (va_env regs2) (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
    pose (RUNTO2 := paj_run_to_x (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS).
    paj_run_to_tok_x RUNTO2 HS2 HJ2 SHOK2 (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (vrd_row 225).
    { unfold va_ss; cbn [ss_mem]. apply awr_ok_nil. }
    pmkst HS2.
    prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (26%bv : bv 5) Q26.
    prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4.
    (* the big hypotheses the rest does not use: every lia below scans the whole context *)
    clear HPI Hchain0 Hcurch Hclos Hcur HFP Hrod Hkw HAGR HJkeep I0p I0e I0d I0rw I0g I0qt Ip Ie Id Irw Ig Iqt Sv8r Sv16r.
    assert (EW2 : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.to_nat (bv_unsigned r) = n ->
                    ew (va_env regs2) n = getr regs2 r).
    { intros n r Hn Hr. unfold va_env. rewrite Eimg_low by (unfold A_TEXT; slia). subst n. apply ew_Ereg_reg. }
    assert (EM2 : ms_mem ms0 = mem2).
    { apply functional_extensionality. intros x. apply HF0. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    assert (EMc : ms_mem ms = mem).
    { apply functional_extensionality. intros x. apply HF. intros (r & Hrin & _).
      unfold va_ss in Hrin. cbn [ss_mem] in Hrin. destruct Hrin. }
    (* the literal's footprint lies inside parse_value's reader cells *)
    assert (HFPs : forall a, inFP [(q, q + 8); (v, v + 4)] a -> inFP (rd_fp q v) a).
    { intros a (r & Hr & Hra). cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra;
      [exists (q, q + 8); split; [left; reflexivity | exact Hra]
      |exists (v, v + 56); cbn [fst snd]; split; [right; right; left; reflexivity | slia]]. }
    pose proof (ajx_ly HJc) as HLY.
    assert (EF : ly_F ly2 = ly_F ly) by (exact (vly_F HLY)).
    assert (Efr : frame_addr ly2 0 pos = frame_addr ly 0 pos) by (unfold frame_addr; rewrite EF; reflexivity).
    assert (Efl : flag_addr ly2 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite EF; reflexivity).
    assert (KS8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HP2 8); unfold acallee_saved; slia).
    assert (KS18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HP2 18); unfold acallee_saved; slia).
    assert (KS26 : getr regs2 26 = getr (ms_regs ms) 26) by (apply (HP2 26); unfold acallee_saved; slia).
    assert (KS24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HP2 24); unfold acallee_saved; slia).
    assert (KS3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HP2 3); unfold acallee_saved; slia).
    assert (KS4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HP2 4); unfold acallee_saved; slia).
    (* literal's post (the cut's PRH_FnReader.v blob f1ae32e3b2cd): its conjuncts BY SHAPE (decompose [and], then each named by
       its type); the keyword branch is one conjunct *)
    destruct HQ as (HQb & Hmk). decompose [and] HQb. clear HQb.
    lazymatch goal with X : room_live_cf S -> room_live_cf S2 |- _ => rename X into Hrl end.
    lazymatch goal with X : Hp2 = Hp |- _ => rename X into EHp end.
    lazymatch goal with X : S2 = S |- _ => rename X into ES end.
    lazymatch goal with X : ablocks B ly2 S2 = ablocks B ly S |- _ => rename X into Eab2 end.
    lazymatch goal with X : context [prh_ledger _ _ S2] |- _ => rename X into Hled2 end.
    lazymatch goal with X : match PjGrammar.prefixb _ _ with _ => _ end |- _ => rename X into Hbr end.
    (* P across the call: the m-form post's memnorm keep and srr_inv_call; row 224 writes no memory *)
    assert (HPc : P (ms_mem ms)) by (rewrite EMc; exact HPm).
    assert (HPr : P (ms_mem ms0)) by (rewrite EM2; exact (PC (ms_mem ms) mem2 Hmk HPc)).
    set (pre := PjGrammar.prefixb PjGrammar.w_null (rest_atR tb text p')) in Hbr.
    assert (Hrv : getr regs2 10 = w64 (if pre then 0 else -1))
      by (destruct pre; cbv beta iota in Hbr; decompose [and] Hbr; assumption).
    apply SRr_ret. split; [|exact HPr]. unfold vrd_arm_exit.
    exists fx, pos, (if pre then 0 else -1).
    (* the join BY NAME: VrdNum's record vrd_epi_R at the join's witnesses (vrd_epi_aR_of_R at wle), one named goal per
       field *)
    unfold vrd_epi_a.
    apply vrd_epi_aR_of_R with (regs := ms_regs ms0) (mem := ms_mem ms0)
      (md := with_vm_backing (m_vm_lazy md2) mat0 md2) (ly := ly2) (S := S2) (Hp := Hp2) (k := k + k1).
    refine {| vepi_cfg := ?[e_cfg]; vepi_jrn := ?[e_jrn]; vepi_win := ?[e_win]; vepi_s0 := ?[e_s0]; vepi_s2 := ?[e_s2];
              vepi_s10 := ?[e_s10]; vepi_s8 := ?[e_s8]; vepi_s5 := ?[e_s5]; vepi_gp := ?[e_gp]; vepi_tp := ?[e_tp];
              vepi_ra := ?[e_ra]; vepi_saved := ?[e_saved]; vepi_flag := ?[e_flag]; vepi_frm := ?[e_frm];
              vepi_fregs := ?[e_fregs]; vepi_rq := ?[e_rq] |}.
    [e_cfg]: { rewrite vrd_pc_epi; reflexivity. }
    (* vrd_epi_a's journal: the literal's text posts no wild budget (fpostWm), so the journal is the budget-free one
       (ajournal_x is ajournal_xw at []) and wbudget CW 0 [] holds by computation *)
    [e_jrn]: { exists []. split; [exact HJ2 | unfold YCbqGwild.wbudget, YCbqGwild.wfresh; cbn; lia]. }
    [e_win]: { intros a Ha Hn. rewrite EM2, (HWIN a ltac:(slia) (fun H => Hn (HFPs a H))), EMc. exact (Hwin a Ha Hn). }
    [e_s0]: { rewrite Q8, (EW2 8%nat (8%bv : bv 5)) by va_cs2; rewrite KS8; rewrite P8; exact R8. }
    [e_s2]: { rewrite Efr, Q18, (EW2 18%nat (18%bv : bv 5)) by va_cs2; rewrite KS18;
              rewrite P18, (EW 18%nat (18%bv : bv 5)) by va_cs2; exact R18. }
    [e_s10]: { rewrite Efr, Q26, (EW2 26%nat (26%bv : bv 5)) by va_cs2; rewrite KS26;
               rewrite P26, (EW 26%nat (26%bv : bv 5)) by va_cs2; exact R26. }
    [e_s8]: { rewrite Efr, Q24, (EW2 24%nat (24%bv : bv 5)) by va_cs2; rewrite KS24;
              rewrite P24, (EW 24%nat (24%bv : bv 5)) by va_cs2; exact R24. }
    [e_s5]: { rewrite Q21, (EW2 10%nat (10%bv : bv 5)) by va_cs2; exact Hrv. }
    [e_gp]: { rewrite Q3, (EW2 3%nat (3%bv : bv 5)) by va_cs2; rewrite KS3;
              rewrite P3, (EW 3%nat (3%bv : bv 5)) by va_cs2; exact R3. }
    [e_tp]: { rewrite Q4, (EW2 4%nat (4%bv : bv 5)) by va_cs2; rewrite KS4;
              rewrite P4, (EW 4%nat (4%bv : bv 5)) by va_cs2; exact R4. }
    [e_ra]: exact Hra0.
    (* the thirteen spilled words: parse_value's own frame below spZ regs0, outside rd_fp q v (the cursor is above
       spZ regs0, the node outside parse_value's stack window), kept by the callee's window clause and both runs *)
    [e_saved]: { assert (KSV : forall a, spZ regs0 - 104 <= a < spZ regs0 ->
                aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
      { intros a Ha. rewrite EM2. rewrite (HWIN a); [rewrite EMc; reflexivity | rewrite Rregs; slia |].
        intros (r & Hrin & Hr). cbn [In] in Hrin.
        destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; [slia |].
        pose proof (vnd_own Hnode) as Hown.
        destruct (Hown a ltac:(slia)) as [_ Hn]. apply Hn. slia. }
      unfold vrd_saved in Hsaved |- *.
      destruct Hsaved as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (eapply val_mem_kept; [|eassumption]; intros kk Hk; cbn in Hk; apply KSV; slia). }
    (* the flag word at F + 56: it lies in parse_value's OWN fake frame, which is below alloc_ceiling, and outside the
       callee's footprint rd_fp q v (the cursor is a stack address above alloc_ceiling; the node cannot meet the frame:
       a block is apart from a frame, another frame is apart from this one, and this frame itself would put the
       descriptor word at F + 16 inside the node's 56 ZEROED bytes). So the callee's journal frames clause keeps it. *)
    [e_flag]: { rewrite Efr, Efl.
      pose proof (ajx_ar HJ0) as HAR. cbv beta in HAR.
      assert (HinF : In (0, pos) (frames S)) by (rewrite Hfr; left; reflexivity).
      destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HFa0 & HFc & HFapp).
      assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFc.
      pose proof (vfrm3 Hframe) as (Hmag & Hsig & Hflag).
      pose proof (vnd_v4096 Hnode) as Hv4096. pose proof (vnd_al8 Hnode) as Hval8. pose proof (vnd_rw Hnode) as Hrw. pose proof (vnd_zero Hnode) as Hzero. pose proof (vnd_at Hnode) as Hat. pose proof (vnd_amr Hnode) as Hamr. pose proof (vnd_own Hnode) as Hown. pose proof (vnd_ra Hnode) as Hra8.
      pose proof (@cf_head_nonneg cp) as Hhd0.
      assert (HvF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> ~ (v <= a < v + 56)).
      { intros a Ha Hav.
        destruct Hat as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                        [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
        - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
          pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
          apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (a0 - cf_head) (k0 + cf_head) a HAR HinF Habk);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hk0h : 0 <= k0 + cf_head) by slia.
          pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq). slia.
        - apply (frame_not_block_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) b0 m0 a HAR HinF Hinb);
          [unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia|].
          assert (Hm00 : 0 <= m0) by slia.
          pose proof (req_size_pos m0 Hm00) as (_ & Hrq). slia.
        - rewrite Hfr in Hinf. destruct Hinf as [Ef | Hinf].
          + injection Ef as <- <-.
            assert (Hz16 : val_mem SEGS (mrestrict (w_H W) mem) (frame_addr ly 0 pos + 16) 8 0).
            { apply (vrd_zero_val SEGS (mrestrict (w_H W) mem) v); [exact Hzero | rewrite Hfb in Hhif; slia | rewrite Hfb in Hhif; slia]. }
            pose proof (Hsig 0%nat ltac:(slia)) as E1. pose proof (Hz16 0%nat ltac:(slia)) as E2.
            cbn [Z.of_nat] in E1, E2. rewrite Z.add_0_r in E1, E2.
            rewrite E1 in E2. vm_compute in E2. discriminate E2.
          + apply in_split in Hinf as (l2 & l3 & El).
            pose proof (sep_frames_pos_x SEGS B ARx LAWS ly S Hp W mem md (0, pos) (cid, pos') (@nil (Z * Z)) l2 l3 HAR
              ltac:(rewrite Hfr, El; reflexivity)) as Hd.
            unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Hfb in Hd. slia.
        - slia. }
      assert (HqF : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> a < q).
      { intros a Ha. pose proof (vastk HJstk0) as (_ & _ & Hclo2 & Hlo2 & _). slia. }
      assert (HnFP : forall a, frame_addr ly 0 pos + 56 <= a < frame_addr ly 0 pos + 64 ->
                 ~ inFP [(q, q + 8); (v, v + 4)] a).
      { intros a Ha (r & Hrin & Hr). cbn [In] in Hrin.
        destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr;
        [pose proof (HqF a ltac:(slia)); slia | exact (HvF a ltac:(slia) ltac:(slia))]. }
      pose proof (ajx_frm HJc) as HJfr.
      eapply val_mem_kept; [|exact Hflag]. intros kk Hk. cbn in Hk.
      rewrite EM2, <- EMc.
      apply (HJfr 0 pos (frame_addr ly 0 pos + 56 + kk) HinF);
      [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb; slia
      | apply HnFP; slia]. }
    [e_frm]: exact Hfrm.
    [e_fregs]: { intros r _; reflexivity. }
    (* ---- RQ: the literal's post read as parse_value's (VnumC's vrd_pv_post), with no allocation: D = [], BY NAME:
       VrdNum's record vrd_pv_R (vrd_pv_post_of_R), one named goal per field ---- *)
    [e_rq]: {
    pose proof Hled as HLB. apply prh_ledger_bounds in HLB. destruct HLB as (Hlp & Hpk & Hcn & Hfl & Hrn).
    pose proof (vnd_v4096 Hnode) as Hv4096n. pose proof (vnd_al8 Hnode) as Hval8n. pose proof (vnd_rw Hnode) as Hrwn. pose proof (vnd_zero Hnode) as Hzeron. pose proof (vnd_at Hnode) as Hatn. pose proof (vnd_amr Hnode) as Hamrn. pose proof (vnd_own Hnode) as Hownn. pose proof (vnd_ra Hnode) as Hra8n.
    pose proof (ajx_ar HJc) as HAR2. cbv beta in HAR2.
    assert (Ex : rest_atR tb text p' = 110 :: yy) by (rewrite Hrest; exact Hsk).
    (* the node's bytes the call did not write are kept: the node is a harness block, an allocator block or a
       frame (the window case is excluded by HVLO), and the callee journal keeps blocks and frames off FP1 *)
    assert (HNK : forall a, v <= a < v + 56 -> ~ inFP [(q, q + 8); (v, v + 4)] a ->
              aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
    { intros a Ha Hn. rewrite <- EMc.
      pose proof (ajx_ly HJc) as HLYc. pose proof (ajx_blk HJc) as HJb. pose proof (ajx_frm HJc) as HJf.
      destruct Hatn as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                       [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        pose proof (@cf_head_nonneg cp) as Hhd0.
        assert (Hk0h : 0 <= k0 + cf_head) by slia.
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        replace a with ((a0 - cf_head) + (a - (a0 - cf_head))) by slia.
        apply (HJb (a0 - cf_head) (k0 + cf_head) (a - (a0 - cf_head))); [exact Habk | rewrite Eab2; exact Habk | slia |].
        replace ((a0 - cf_head) + (a - (a0 - cf_head))) with a by slia. exact Hn.
      - assert (Hm00 : 0 <= m0) by slia.
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        replace a with (b0 + (a - b0)) by slia.
        apply (HJb b0 m0 (a - b0)); [exact Hinb | rewrite Eab2; exact Hinb | slia |].
        replace (b0 + (a - b0)) with a by slia. exact Hn.
      - apply (HJf cid pos' a Hinf); [left; unfold in_zr, frame_rng; cbn [fst snd]; slia | exact Hn].
      - slia. }
    (* the node bytes beyond the type word, at the end, are the dispatch's: zero *)
    assert (VK : forall a n x, v + 4 <= a -> a + Z.of_nat n <= v + 56 ->
              val_mem SEGS (mrestrict (w_H W) mem) a n x -> val_mem SEGS (mrestrict (w_H W2) mem2) a n x).
    { intros a n x H1 H2 Hv kk Hk.
      rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
      apply HNK; [slia|]. intros (r & Hrin & Hr). cbn [In] in Hrin.
      destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; slia. }
    (* every node byte is present at the end (a block or a frame of the end state), so writable *)
    assert (HWR : forall a, v <= a < v + 56 -> writable_at SEGS (mrestrict (w_H W2) mem2) a).
    { intros a Ha. apply apresent_writable.
      pose proof (ajx_ly HJc) as HLYc.
      assert (EFc : ly_F ly2 = ly_F ly) by (exact (vly_F HLYc)).
      pose proof (vnd_at Hnode) as Hat2.
      destruct Hat2 as [(a0 & k0 & HinL & Hle0 & Hhi0) | [(b0 & m0 & Hinb & _ & Hleb & Hhib) |
                       [(cid & pos' & Hinf & Hlef & Hhif) | (Hw1 & Hw2)]]].
      - pose proof Hled as HLamF. apply prh_ledger_blocks in HLamF.
        pose proof (proj1 (Forall_forall _ _) HLamF (a0, k0) HinL) as (Hk0 & Habk & _). cbn [fst snd] in Hk0, Habk.
        pose proof (@cf_head_nonneg cp) as Hhd0.
        assert (Hk0h : 0 <= k0 + cf_head) by slia.
        pose proof (req_size_pos (k0 + cf_head) Hk0h) as (_ & Hrq).
        rewrite <- Eab2 in Habk.
        destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Habk) as (_ & _ & _ & _ & Hb & _).
        exact (proj1 (Hb a ltac:(slia))).
      - assert (Hm00 : 0 <= m0) by slia.
        pose proof (req_size_pos m0 Hm00) as (_ & Hrq).
        rewrite <- Eab2 in Hinb.
        destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hinb) as (_ & _ & _ & _ & Hb & _).
        exact (proj1 (Hb a ltac:(slia))).
      - assert (Hinf2 : In (cid, pos') (frames S2)) by (rewrite ES; exact Hinf).
        destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos' HAR2 Hinf2) as (_ & _ & Hfp & _).
        assert (Efa : frame_addr ly2 cid pos' = frame_addr ly cid pos') by (unfold frame_addr; rewrite EFc; reflexivity).
        rewrite Efa in Hfp. exact (proj1 (Hfp a ltac:(slia))).
      - slia. }
    rewrite EM2.
    apply vrd_pv_post_of_R with (ok := [])
      (res := if pre then Some (JNull, skipn (length PjGrammar.w_null) (110 :: yy)) else None) (tr := []) (okr := [])
      (D := []) (Lam' := Lam) (peak' := peak) (cnt' := cnt) (fail' := fail) (ran' := ran).
    (* the literal allocates nothing: its value is the keyword's, at ok = [] (EJ), and its granted trace is
       empty (vrd_gtrace_lit); S2 = S, which is S0 up to its fake frames (`S = set_fs f S0`) *)
    assert (EJ : jr_value ReaderRes.jr_strtod d (rest_atR tb text p) [] =
                 ((if pre then Some (JNull, skipn (length PjGrammar.w_null) (110 :: yy)) else None), [], [])).
    { rewrite (vrd_lit_model ReaderRes.jr_strtod d 110 yy (rest_atR tb text p) [] Hsk (or_intror (or_intror eq_refl))).
      cbn [Z.eqb Pos.eqb]. unfold PjGrammar.lit, PjGrammar.jret, PjGrammar.jrefuse. unfold pre. rewrite Ex.
      destruct (PjGrammar.prefixb PjGrammar.w_null (110 :: yy)); reflexivity. }
    pose proof (vrd_gtrace_lit d 110 yy (rest_atR tb text p) Hsk (or_intror (or_intror eq_refl))) as EG0.
    destruct Hsetfs as (fz & Efz).
    refine {| vpv_run := ?[p_run]; vpv_ledger := ?[p_ledger]; vpv_room := ?[p_room]; vpv_hull := ?[p_hull];
              vpv_live := ?[p_live]; vpv_pos := ?[p_pos]; vpv_outcome := ?[p_outcome]; vpv_injected := ?[p_injected];
              vpv_ledger_move := ?[p_ledger_move]; vpv_fresh := ?[p_fresh]; vpv_blocks := ?[p_blocks];
              vpv_frames := ?[p_frames]; vpv_hpeak := ?[p_hpeak]; vpv_bytes := ?[p_bytes]; vpv_lsum := ?[p_lsum];
              vpv_arm := ?[p_arm] |}.
    [p_run]: exact EJ.
    [p_ledger]: exact Hled2.
    [p_room]: exact (Hrl (vrr_live _ _ Hroom)).
    (* the hull use: the granted trace is empty (EG0) and S2 = S, which has S0's st_secs (`S = set_fs f S0`) *)
    [p_hull]: { rewrite EG0; apply PresetHullBudget.hull_used_secs; rewrite ES, Efz; reflexivity. }
    [p_live]: { rewrite ES, Efz. change (PresetReqAt.rd_hevs []) with (@nil PresetReqAt.hev).
      rewrite PresetReqAt.hlive_from_nil.
      change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S0)))
        with (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)).
      apply Permutation_refl. }
    [p_pos]: { intros sm x os i Hz0 hist Hpos _. exists hist. rewrite ES, Efz.
      change (length (PresetReqAt.rd_hevs [])) with 0%nat. rewrite Nat.add_0_r.
      apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
    [p_outcome]: { intros sm x os i Hz0 hist Hpos _ _ _. split; [reflexivity|]. split; [rewrite EJ; reflexivity|].
      exists hist. rewrite EG0, ES, Efz.
      change (length (PresetReqAt.rd_hevs [])) with 0%nat. rewrite Nat.add_0_r.
      apply PresetRoomPosKeep.room_pos_set_fs. exact Hpos. }
    (* the injected reading: vacuous, the granted trace is empty (EG0), so the window cnt <= fail < cnt is empty *)
    [p_injected]: { intros sm x os i Hz0 hist _ _ _ Hwd; rewrite EG0 in Hwd; cbn [PjGrammar.calls Z.of_nat] in Hwd;
            exfalso; slia. }
    [p_ledger_move]: { unfold rd_ledger_move. cbn [PjGrammar.calls lszR nliveR hpeakR map length app].
      split; [split; [intros i Hi; cbn in Hi; slia | split; [left; reflexivity | intros i Hi; cbn in Hi; slia]]|].
      split; [rewrite Z.add_0_r, Z.mod_small by slia; reflexivity|].
      split; [split; intros Hc; cbn in Hc; [slia | reflexivity]|].
      split; [apply Permutation_refl|].
      split; [constructor|].
      split; [reflexivity|].
      unfold prh_refused_peak. cbn [List.seq map fold_right]. clear - Hlp. lia. }
    [p_fresh]: { intros aa kk Hak; destruct Hak. }
    [p_blocks]: { rewrite Eab2, Hab; cbn [prhReader_ab map app]; apply Permutation_refl. }
    [p_frames]: { rewrite ES, Hfr; apply Permutation_refl. }
    [p_hpeak]: { cbn [hpeakR]; slia. }
    [p_bytes]: { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly0 S0), Eab2, Hab.
      unfold prh_held. cbn [PjGrammar.held PjGrammar.calls fold_right map Z.of_nat]. slia. }
    [p_lsum]: reflexivity.
    [p_arm]: {
    unfold pre in Hbr |- *. rewrite Ex in Hbr |- *.
    destruct (PjGrammar.prefixb PjGrammar.w_null (110 :: yy)) eqn:Epre.
    + (* the keyword matched: the node is JNull, the cursor advanced by four *)
      cbv beta iota in Hbr. decompose [and] Hbr. clear Hbr.
      lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W2) mem2) q text len _ _ tb |- _ => rename X into Hin2 end.
      lazymatch goal with X : val_mem _ (mrestrict (w_H W2) mem2) v 4 _ |- _ => rename X into Hty2 end.
      assert (Elen : Z.of_nat (length (110 :: yy)) = text + len - p').
      { rewrite <- Ex. unfold rest_atR. rewrite length_skipn.
        pose proof (vin_pp Hin) as Hpp'. pose proof (vin_len Hin) as Hlen'. slia. }
      assert (Hge4 : 4 <= Z.of_nat (length (110 :: yy))).
      { clear - Epre. destruct yy as [|c1 [|c2 [|c3 yy']]]; cbn in Epre |- *; try discriminate; slia. }
      (* the node's header, shared by its free order and its node clause *)
      assert (HHDl : pj_hdrR SEGS (mrestrict (w_H W2) mem2) v (tag JNull) 0 0 0 0 0 0).
      {
        split; [split; [exact Hval8n | intros xw Hxw; exact (HWR xw Hxw)]|].
        split; [split; [cbn; slia | exact Hty2]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 8) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 16) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 24) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 32) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 40) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]]|].
        split; [slia | apply VK; [slia | slia | exact (vrd_zero_val SEGS _ v (v + 48) 8 Hzeron ltac:(slia) ltac:(cbn; slia))]].
      }
      assert (HAPl : pj_apartR [] v) by (intros bb x Hb; destruct Hb).
      refine {| vpvs_rv := ?[s_rv]; vpvs_freeord := ?[s_freeord]; vpvs_in_ok := ?[s_in_ok]; vpvs_node := ?[s_node];
                vpvs_ncap := ?[s_ncap]; vpvs_lsum_le := ?[s_lsum_le] |}.
      [s_rv]: reflexivity.
      (* the free order (PRH_PjOrder.pfo_leaf): a leaf with no block frees nothing, and the value's free list at a
         keyword is [] (vrd_frees_lit) *)
      [s_freeord]: { intros _ nn _. exists []. split.
        - exact (PRH_PjOrder.pfo_leaf SEGS _ _ nn v (tag JNull) 0 0 [] ltac:(constructor) HAPl HHDl (or_introl (conj eq_refl eq_refl))).
        - rewrite (vrd_frees_lit d 110 yy (rest_atR tb text p) [] Hsk (or_intror (or_intror eq_refl))). reflexivity. }
      [s_in_ok]: { assert (Epos : text + len - Z.of_nat (length (skipn (length PjGrammar.w_null) (110 :: yy))) =
                       p' + Z.of_nat (length PjGrammar.w_null)).
        { rewrite length_skipn. cbn [length PjGrammar.w_null] in *. slia. }
        rewrite Epos. exact Hin2. }
      [s_node]: { split; [constructor|]. split; [intros bb x Hb; destruct Hb|].
        exists 0, 0, 0, 0, 0, 0. split; [exact HHDl | repeat split; reflexivity]. }
      (* the leaf's capacity words: pj_ncapR of a keyword is True *)
      [s_ncap]: exact I.
      [s_lsum_le]: { pose proof (vrd_rest_shrink tb text p p' (proj1 Hpp)) as Hshr. rewrite Ex in Hshr.
        cbn [Ledger.lsum]. rewrite length_skipn. cbn [length PjGrammar.w_null] in *. slia. }
    + (* the keyword did not match: the cursor and the node are untouched *)
      cbv beta iota in Hbr. decompose [and] Hbr. clear Hbr.
      lazymatch goal with X : pj_in_okR _ (mrestrict (w_H W2) mem2) q text len _ _ tb |- _ => rename X into Hin2 end.
      lazymatch goal with X : forall a, q <= a < q + 8 \/ _ -> _ |- _ => rename X into Hkeep end.
      assert (HRW2 : pj_rwR SEGS (mrestrict (w_H W2) mem2) v)
        by (split; [exact Hval8n | intros xw Hxw; exact (HWR xw Hxw)]).
      assert (HZ2 : pj_zeroR SEGS (mrestrict (w_H W2) mem2) v).
      {
        unfold pj_zeroR in *. intros jj Hjj. destruct (Hzeron jj Hjj) as (Hz1 & Hz2). split; [|exact Hz2].
        intros kk Hkk. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 (v + Z.of_nat jj + Z.of_nat kk)).
        + exact (Hz1 kk Hkk).
        + rewrite repeat_length in Hjj. cbn in Hkk.
          destruct (Z_lt_le_dec (v + Z.of_nat jj + Z.of_nat kk) (v + 4)) as [Hlo|Hhi].
          * rewrite <- EMc. apply Hkeep. right. slia.
          * apply HNK; [slia|]. intros (r & Hrin & Hr). cbn [In] in Hrin.
            destruct Hrin as [<- | [<- | []]]; cbn [fst snd] in Hr; slia.
      }
      refine {| vpvn_rv := ?[n_rv]; vpvn_freeord := ?[n_freeord]; vpvn_in_after := ?[n_in_after];
                vpvn_fd := ?[n_fd] |}.
      [n_rv]: reflexivity.
      (* the free order of the untouched (zero) node: its order list is [] (VrdNum.vrd_zero_fo), and the value's free
         list at a keyword is [] (vrd_frees_lit) *)
      [n_freeord]: { intros _ nn _. exists []. split.
        - exact (vrd_zero_fo SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) v nn HRW2 HZ2).
        - rewrite (vrd_frees_lit d 110 yy (rest_atR tb text p) [] Hsk (or_intror (or_intror eq_refl))). reflexivity. }
      [n_in_after]: { pose proof (vin_p Hin2) as J1. pose proof (vin_end Hin2) as J2. pose proof (vin_d Hin2) as J3. pose proof (vin_rw Hin2) as J4. pose proof (vin_q8 Hin2) as J5. pose proof (vin_t Hin2) as J6. pose proof (vin_tl Hin2) as J7. pose proof (vin_pp Hin2) as J8. pose proof (vin_len Hin2) as J9. pose proof (vin_g Hin2) as J10. pose proof (vin_qt Hin2) as J11. pose proof (vin_d32 Hin2) as J12.
        exists p', (Z.of_nat d). split; [slia|]. split; [slia|].
        split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. exact J4. }
      [n_fd]: exact (vrd_zero_fd SEGS _ _ v _ HRW2 HZ2). }
    }
Qed.

(* the instance P := True: the literal arm's statement of before, word for word *)
Theorem vrd_lit_aLC_holds : forall d CTX0 CW, vrd_lit_aLC B ARx SK d CTX0 CW.
Proof.
  intros d CTX0 CW ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran
    most own W c b ty yy cw slack
    HPI HFP HD Hsk Hbty Hkw Hw63 Hnul Hslack Hwstk HSTK HSTKi.
  eapply SRr_mono.
  { exact (vrd_lit_aLC_P_holds (fun _ => True) d CTX0 CW (fun _ _ _ _ => I)
      ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran
      most own W c b ty yy cw slack
      HPI HFP HD Hsk Hbty Hkw Hw63 Hnul Hslack Hwstk HSTK HSTKi I). }
  cbv beta. intros W' c' _ HX. exact (proj1 HX).
Qed.
End pl.

(* acceptance checks, printed into the build log *)
Print Assumptions vrd_cont_aLC_P_holds.
Print Assumptions vrd_lit_aLC_P_holds.
Print Assumptions vrd_cont_aLC_holds.
Print Assumptions vrd_lit_aLC_holds.
Set Printing All.
Check @vrd_cont_aLC_P_holds.
Check @vrd_lit_aLC_P_holds.
Check @vrd_cont_aLC_holds.
Check @vrd_lit_aLC_holds.
Unset Printing All.
(* the wrong-image check (every PA / L / PI names image A': PI_prog_A / A_prog_listing) *)
Set Printing Implicit. Unset Printing Notations.
About vrd_cont_aLC_P_holds.
About vrd_lit_aLC_P_holds.
About vrd_cont_aLC_holds.
About vrd_lit_aLC_holds.
About vfrm3.
About vdispa.
(* the statements unfolded one level, so every pa_segs / listing / image argument they carry is printed *)
Print vrd_arm_exit.
Print vrd_cont_aLC_P.
Print vrd_lit_aLC_P.
Unset Printing Implicit. Set Printing Notations.

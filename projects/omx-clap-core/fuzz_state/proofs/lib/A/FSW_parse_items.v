(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the ASan walk of parse_items (A 0x84a04) against
   lib/A/FSH_Fn_reader.v's parse_items_spec k - the ENTRY stage and the writer-text model facts. The whole walk is
   FSW_parse_items_holds.v's parse_items_holds (ms = []: FSW_pitems_dev.v; ms <> []: FSW_parse_items_entry.v, then the
   member steps FSW_parse_items_stG / _stP / _stM / _stVc / _stVe.v over FSW_parse_items_loop.v's invariants).

   WHAT IS HERE (stage 1, the ENTRY cut point). parse_items has no fake frame (no `andi sp, sp, -32` in its 429
   instructions), one frame of 144 bytes, and reaches its first symbolic branch at 0x84ad0. This file proves the
   entry state of the walk - the symbolic state pi_ss0 at A_parse_items under the spec's premises, the journal over
   the caller's raised window (top ot), ARU, and the two shadow entries the token run needs - and records the
   MEASURED engine run of the first straight-line segment (entry .. 0x84ad0) as a lemma.

   THE CUT POINTS of the whole walk, measured on the pinned fs.asan (see FSW_parse_items_tbl.v for the table and the
   image shas), for the lanes that continue this file:
     0x84a04  entry                     prologue, depth check, `in->depth := k + 1`, type := 6
     0x84ad0  `bgeu a3,a2`              p + 1 vs in->end: NOT decidable from atom ranges; the walk decides it from
                                        the model (rest_at tb text p = wt ++ rest with wt = '{' :: .. :: '}')
     0x84ae8  ws loop 1 head            per-byte: shadow check (token), `lbu a6,0(a3)`, ws mask test
     0x84b34  after ws loop 1           '}' test (empty object) / fall through to grow
     0x84b68  call grow                 -> 0x84b6c
     0x84bac  member loop head
     0x84bd0  ws loop 2 head            (key)
     0x84c4c  call parse_string         -> 0x84c50
     0x84cbc  ws loop 3 head            (colon)
     0x84d78  call __asan_memset        -> 0x84d7c   (the kid is zeroed)
     0x84d98  call parse_value (k + 1)  -> 0x84d9c
     0x84dd4  ws loop 4 head            (comma / close)
     0x84e60  call grow                 -> 0x84e64   (back to the member loop head)
     0x84e9c  close '}'                 in->depth := k, s2 := 0
     0x84ed4..0x84f10                   epilogue, `ret` at 0x84f10
   The per-byte text loads inside the four ws loops are loads at a SYMBOLIC cursor. As built, the walk does not
   iterate them: with k <= 1 the white space before each stop byte is a concrete byte list per (pr, k), given to the
   engine as a read-only literal window at the cursor atom plus the loop's branch conditions as facts
   (FSW_parse_items_seg.v's header), so each segment runs through its loop with no obligation.
   MEASURED here: with the two shadow entries below, the entry segment raises NO token and NO obligation (the q and
   v checks are `covered`).

   THE ENTRY STATE. Atom 10 is a0 = q (struct pj_in, 24 bytes, in the caller's real frame above sp), atom 11 is
   a1 = v (the struct pj the caller zeroed), atom 12 is a2 = 1 (the object flag; its exact fact is what folds the
   type word to 6, MEASURED), atom 32 the shadow base, and xatom 0..2 are p, in->end and in->depth (FSW_K.v's ATOM
   CONVENTION). The v region carries NO chunks at entry: parse_items only WRITES v before its first call, so
   writability is all the engine needs, and that is exactly pobj's second conjunct.

   THE OTHER STAGES (the member loop's five calls, the close and the return) are in the files named in the first
   paragraph; each is a Qed lemma, none is a named hypothesis.
   PORTED FROM r7 AND FROM bump: NOTHING, and why (brief step 2, a Theorem Labs lane 04:0xZ).
   - a working branch 35255daf2a7 lib/A/Prog/parse_items_arms.v (3,345 lines, 132 Qed) is
     stated in the BESPOKE machine framework: `evt rsegs` / `SR rsegs (mkCfg (mkst ...) md)` over Img0, AsanRT,
     Contract and ALedger, with reader_env / rpost / aledger / a_call_post, and it Requires lib/A/Prog modules
     (parse_items_entry, parse_items_scan, parse_items_seg / _seg2, ALedger, AGlue, grow_c, parse_string_c,
     parse_value_c, asan_memset_c, fuzz_free_c, parse_items.v) that S0 does not carry. S0 states the same walk as
     SRr over YG0d.cfg_at with the symbolic engine (sym_run*_tok, st_ok, ajournal, fpostU): the state type, the
     memory reader and the post shape all differ, so not one of its 132 statements type-checks here. Its framework-
     free lemmas (pia_lsz_ev_eq, pia_lszf_eq, pia_zl_perm, pia_lsum_zl, pia_lsum_lsz, cg_list_ext, pfx_alive_perm)
     are over ALedger's zl / lsum / lsz / held / nlive, which S0 does not have either: it accounts with
     FSH_Fn_reader.v's rd_live / rd_ev / rd_sum and PjGrammar.held, so each would be a restatement, not a port.
     a Theorem Labs lane's file also ASSUMES parse_value's contract (PVC, line 195), parse_string's (PSC, 197) and PSFREE (329).
   - a working branch 955803f9b2e carries the same bespoke family for parse_items (lib/A/Prog/
     parse_items*.v, 0.9 MB). Ruling (a Theorem Labs lane 04:18Z, re-stated by a Theorem Labs lane 04:5xZ): bump is a TEMPLATE
     ONLY, never bridged - a Theorem Labs lane's probe proved the bespoke statements strictly weaker on the refusal paths.
     TAKEN from bump: the STAGE DECOMPOSITION only - which cut points the walk needs and which arms are dead - as
     the table above. No proof text, no statement.
   TAKEN FROM NEITHER, and so proved here: the model-side facts of the writer text (pi_wt_* below), which both
   bespoke files avoid by working over the READER model (jr_items / rest_at) instead of the writer's wvpieces that
   S0's parse_items_spec names.
   RULE 24, independently CONFIRMED: (internal path) (05:0xZ) - no
   released ASan proof of parse_items on origin/main, ossv/recipes, ossv/candidates or release/pau-projects-recipes,
   and none in the delivered package; the only hits are the plain 0x14ffc (6 files) and UBSan 0x155c8 (8 files) walks,
   which are templates, not donors. The index's own address search is NOT RUN for this unit (no symbol table), so
   the address and cross-branch clauses were done by hand and by a second lane.
   CLOSURE (Print Assumptions over every lemma below, log build-20261029T052229Z on a build machine): each is either
   `Closed under the global context` or uses only PrimInt63 / PrimString / PrimArray and, for pitems_entry_run,
   FunctionalExtensionality.functional_extensionality_dep - all on toolchain/allowed-axioms.txt.
   THE ROUTE (as built by the member-step files): a measured run stops at
   TS_stopped (SR_branch c a b); the walk turns that into two arms with Reusable/YA0o.v:267 SRr_sym_branch (it needs
   only st_ok at the stop, and gives st_ok of add_cond ss (mkAC c a b) on the taken arm and of the negated
   condition on the other, through st_ok_add_cond / st_ok_add_cond_neg). Each arm then runs again with
   FSW_K.fsw_run_tok_AJU / fsw_run_to_tok_AJU inside run_post_tok_AJU, exactly as pitems_entry_run does for the
   entry segment. A call stop (TS_stopped SR_fetch at the callee's entry, as pi_run_grow1 / pi_scout_call_ps
   measure) is taken by the callee's spec and resumed with FSW_ret.fsw_after_callU_args or
   FSW_K3.fsw_after_callFPU_args / _ot (the raised window top ot of parse_string and parse_value), and the final
   `ret` with FSW_ret.fsw_retU. The model facts each branch needs are the pi_wt_* / pi_obj_* lemmas below.
   NAMED HYPOTHESES: only the two cell equations TMP_TL_GOT / TMP_TL_CELL, which stand for TfibLib until ACeg builds
   (owner ACeg). The stack's zero shadow on the MACHINE memory comes from FSupoisonStack.fsw_ARU_stack_ra (a Theorem Labs lane's
   poison lane); the interim named hypothesis this file carried for it is gone.
   COPIED donor proofs: A/ACex.v:322,:330 stack_cells8 / RA_stack (as pi_stack_cells8 / pi_RA_stack), unchanged but
   for their names, to keep ACex (and with it AE2k's instance) out of the load closure - the implicit-instance guard
   of FSH_Gen.v:29. The object-vs-image and object-vs-shadow-band steps are NOT copied: FSW_rd.v
   (a working branch 1fa49bd3226) proves them as fsw_pobj_off_img / fsw_pobj_off_shadow.
   BASE, PER LEMMA (soundness label, a Theorem Labs lane 00:2xZ / 00:4xZ / 01:0xZ). Every lemma of this file is built over
   RELOC's FP-keyed core as carried by the kit head a working branch e7266e15dbe (S0 400b2a240b3 +
   reloc-wip 4b90d538804 + hv5 02c96da1fc5 + ret e8fef4c8127: ajournal's image clause WITH the ~ inFP FP exemption,
   awr_byte = awr_byte0 \/ static arm \/ caller-frame arm over fr0, YCbq.v:460-467), plus lib/A/FSupoisonStack.v
   taken BY PATH from a working branch 52f226102ef (whose YCbq.v is the same FP-keyed core). No lemma
   takes a callee spec - no allocator, nothing that writes fuzz/alloc.c's statics:
     measured (vm_compute only, no core clause involved): pi_K_val, pi_frame_val, pi_regions_wf, pi_static_ok,
       pi_run_entry, pi_run_entry_mem, pi_run_eq, pi_obls_84ad0, pi_run_ws0, pi_ws1_static_ok, pi_run_ws1,
       pi_lh_static_ok, pi_run_iter_a / _b / _c;
     proved, no callee spec: pi_stack_cells8, pi_RA_stack, pitems_entry (these three also built over S0's older core
       2bdd415d4f9 at e728a938779), pi_awr_ok and pitems_entry_run (over the FP-keyed core ONLY: they use awr_ok's
       (segs, B, .., own, fr0) arity and its caller-frame arm, and so cover BOTH arms of pobj, i.e. level k = 0 too).
   The call stages are built over this same core (FSW_parse_items_grow.v / _calls.v and the step files).
   Ported from: FSW_K.v, FSW_ret.v / FSW_rd.v (a Theorem Labs lane,
   a working branch e8fef4c8127 via another working branch), FSW_pj.v (a working branch 12a083be217), S0
   a working branch 400b2a240b3 via another working branch at e7266e15dbe. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSW_rd FSW_pj
FSW_parse_items_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Check Reusable.YI16.sink_head. Check Reusable.YI14.sink_syms.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the entry state ---- *)
(* struct pj_in at a0: p at 0, in->end at 8, in->depth at 16 (24 bytes, writable) *)
Definition pi_q_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 0)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))].
(* the result object at a1: 56 writable bytes, zeroed by the caller (parse_items_spec's pj_zero). The zero words
   are CARRIED as chunks - type (4 bytes at 0) and num / str / kids / keys / n / cap (8 bytes at 8 .. 48) - so that
   the engine keeps the fields parse_items never writes, and the post's pj_hdr reads them off the final state. *)
Definition pi_v_region : YP09.region :=
  YP09.mkRegion (Some 11%nat) 0 56 0 56
    [YP09.mkChunk 0 (CVal 4 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
     YP09.mkChunk 24 (CVal 8 (SLit 0)); YP09.mkChunk 32 (CVal 8 (SLit 0)); YP09.mkChunk 40 (CVal 8 (SLit 0));
     YP09.mkChunk 48 (CVal 8 (SLit 0))].
(* the same object once the prologue's type store (0x84a74, 6 = PJ_OBJECT) has replaced the first chunk *)
Definition pi_v_region6 : YP09.region :=
  YP09.mkRegion (Some 11%nat) 0 56 0 56
    [YP09.mkChunk 0 (CVal 4 (SLit 6)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
     YP09.mkChunk 24 (CVal 8 (SLit 0)); YP09.mkChunk 32 (CVal 8 (SLit 0)); YP09.mkChunk 40 (CVal 8 (SLit 0));
     YP09.mkChunk 48 (CVal 8 (SLit 0))].
Definition pi_rs : list YP09.region := [pi_q_region; pi_v_region].
Definition pi_gf : list (nat * afact) :=
  [(10%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (11%nat, mkAF 4096 (2 ^ 47 - 56) 3);
   (12%nat, mkAF 1 1 0);
   (xatom 0, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (xatom 1, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0);
   (xatom 2, mkAF 0 1 0)].
Definition pi_ss0 : sstate := fss0T_args A_parse_items FRAME_parse_items pi_rs pi_gf.
(* one shadow entry per object the inline checks read (the donor's A/ACes.v:28-29 shape) *)
Definition pi_SH : list shent := [mkSHE 10 0 24; mkSHE 11 0 56].
Definition pi_K : nat := run_K 0 fs_Bx pi_SH pi_ss0.
(* the extra env atoms of the entry env: xatom 0 = p, 1 = in->end, 2 = in->depth *)
Definition pi_xs (p e d : Z) : list word := [Z_to_bv 64 p; Z_to_bv 64 e; Z_to_bv 64 d].

(* ---- measured facts about the entry state and the first segment ---- *)
Lemma pi_K_val : pi_K = 36%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_frame_val : FRAME_parse_items = 144.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_regions_wf : regions_wf (fsT_regions_args FRAME_parse_items pi_rs) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_static_ok : sh_static_ok pi_K fs_Bx fs_Bspan pi_SH (ss_facts pi_ss0) (ss_mem pi_ss0) = true.
Proof. vm_compute. reflexivity. Qed.
(* MEASURED: the entry segment runs to 0x84ad0 with no token, no obligation and no reservation *)
Lemma pi_run_entry :
  let r := sym_run_toN_tok tfibsegs pitems_tbl pi_K fs_Bx fs_Bspan pi_SH FUEL 0x84ad0 pi_ss0 in
  snd r = TS_running /\ ss_pc (sh_ss (fst r)) = 0x84ad0 /\ ss_resv (sh_ss (fst r)) = None /\
  sh_j (fst r) = 0%nat /\ sh_obls (fst r) = [] /\ sh_toks (fst r) = [] /\ sh_chk (fst r) = true.
Proof. vm_compute. repeat split. Qed.
(* MEASURED: the type word the prologue stores is 6 = PJ_OBJECT (pf.c:211 `v->type = o ? PJ_OBJECT : PJ_ARRAY`,
   folded because atom 12 = a2 = 1 exactly), in->depth is raised to d + 1, and in->p is already past the
   opening brace (p + 1, stored at 0x84abc) when the walk reaches 0x84ad0 *)
Lemma pi_run_entry_mem :
  let r := sym_run_toN_tok tfibsegs pitems_tbl pi_K fs_Bx fs_Bspan pi_SH FUEL 0x84ad0 pi_ss0 in
  nth_error (ss_mem (sh_ss (fst r))) 3 =
    Some (YP09.mkRegion (Some 10%nat) 0 24 0 24
            [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 1)); YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 1));
             YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0))]) /\
  nth_error (ss_mem (sh_ss (fst r))) 4 =
    Some pi_v_region6.
Proof. vm_compute. split; reflexivity. Qed.

(* MEASURED, stage 2's interface: on the arm where in->p + 1 < in->end (the one the model takes: wt is
   '{' :: .. :: '}'), the run reaches the first text byte of the white-space loop at 0x84af8 and stops there with
   exactly ONE token (a6 := the shadow byte at p + 1, signed) and ONE obligation, range_addressable at (p + 1) of 1
   byte - which rd_text's block discharges (YCbq.range_addressable_of_block). The byte itself is a load at a
   SYMBOLIC cursor: stage 2 supplies a region based at the cursor atom whose chunk is CData over the text bytes
   (YP09.v:104 / YP05.v:219), and re-seats the cursor on a fresh atom at the loop head (FSW_K.fsw_reseat_atom), so
   that one iteration lemma serves every pass and all four white-space loops. *)
Definition pi_st_84ad0 : shst := fst (sym_run_toN_tok tfibsegs pitems_tbl pi_K fs_Bx fs_Bspan pi_SH FUEL 0x84ad0 pi_ss0).
Definition pi_ss_ws0 : sstate := add_cond (sh_ss pi_st_84ad0) (mkAC BC_LTU (SOff (xatom 0) 1) (SOff (xatom 1) 0)).
Lemma pi_run_ws0 :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_K fs_Bx fs_Bspan pi_SH FUEL pi_ss_ws0 in
  (snd r, sh_j (fst r), sh_obls (fst r), ss_pc (sh_ss (fst r))) =
    (TS_stopped (SR_load (Some (xatom 0)) 1), 2%nat, [mkOB (SOff (xatom 0) 1) 1], 0x84af8).
Proof. vm_compute. reflexivity. Qed.

(* MEASURED, and the reason stage 2 needs no new engine step: give the cursor's byte as a CData chunk of a region
   based at the cursor atom (its data list is the text bytes tb; chunk_ok comes from pj_in_ok's `bytes_at segs m text
   tb`), and add one shent for that byte (its range_addressable comes from rd_text's block, YCbq.range_addressable_of
   _block). Then the engine resolves the load - the byte becomes `SData 0 0 1` - the shadow check is `covered`, so no
   obligation is raised at all, and the run stops at the white-space mask test 0x84afc `bltu s5,a6`, a branch on the
   byte VALUE, which the walk decides from FS_DOC_STRS / the writer's text. One iteration of all four white-space
   loops has this shape; the loop head re-seats the cursor on a fresh atom (FSW_K.fsw_reseat_atom) so the region and
   the shent move with it. *)
Definition pi_tb_region : YP09.region :=
  YP09.mkRegion (Some (xatom 0)) 0 2 0 0 [YP09.mkChunk 1 (CData 0 0 1)].
Definition pi_ss_ws1 : sstate :=
  mkSS (ss_pc pi_ss_ws0) (ss_regs pi_ss_ws0) (pi_tb_region :: ss_mem pi_ss_ws0) (ss_resv pi_ss_ws0)
    (ss_facts pi_ss_ws0).
Definition pi_SH1 : list shent := mkSHE (xatom 0) 1 2 :: pi_SH.
Definition pi_K1 : nat := run_K 0 fs_Bx pi_SH1 pi_ss_ws1.
Lemma pi_ws1_static_ok : sh_static_ok pi_K1 fs_Bx fs_Bspan pi_SH1 (ss_facts pi_ss_ws1) (ss_mem pi_ss_ws1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_run_ws1 :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_K1 fs_Bx fs_Bspan pi_SH1 FUEL pi_ss_ws1 in
  (snd r, sh_obls (fst r), ss_pc (sh_ss (fst r))) =
    (TS_stopped (SR_branch BC_LTU (SLit 32) (SData 0 0 1)), [], 0x84afc).
Proof. vm_compute. reflexivity. Qed.

(* ---- two donor proofs, copied (see the header: the implicit-instance guard keeps AD1y / ACex out) ---- *)
(* the entry run as an EQUATION on the named state, so that a walk never asks Rocq to unify against the run itself *)
Lemma pi_run_eq :
  sym_run_toN_tok tfibsegs pitems_tbl pi_K fs_Bx fs_Bspan pi_SH FUEL 0x84ad0 pi_ss0 = (pi_st_84ad0, TS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma pi_obls_84ad0 : sh_obls pi_st_84ad0 = [].
Proof. vm_compute. reflexivity. Qed.

(* ---- MEASURED: one iteration of white-space loop 1, the shape of all four ----
   At the loop head 0x84ae8 the cursor (a0 = a3) is re-seated on a FRESH atom c (FSW_K.fsw_reseat_atom), its byte is
   a CData chunk of a region based at c, and one shent covers [c, c + 1). Then the engine runs the whole iteration
   with NO obligation and no __asan_report_* call reached, and stops only at the three branches that are decided from
   the MODEL, not from the machine:
     0x84afc  `bltu a4,a6`   32 < byte            -> leaves the loop
     0x84b08  `beqz a6`      (mask >> byte) & 1   -> leaves the loop   (mask = 0x100003200 >> ... = 4294977024)
     0x84b20  `bne a3,a2`    c + 1 <> in->end     -> back to 0x84ae8
   On the white-space arm the iteration ends with a0 = a3 = c + 1 AND in->p = c + 1 in the caller's struct pj_in -
   so the loop's invariant is carried by the cursor atom alone, and the induction is over the white-space run that
   ReaderRes.rest_at / the writer's text gives. *)
Definition pi_cb_region : YP09.region :=
  YP09.mkRegion (Some 37%nat) 0 1 0 0 [YP09.mkChunk 0 (CData 0 0 1)].
Definition pi_lh0 : sstate :=
  sh_ss (fst (sym_run_toN_tok tfibsegs pitems_tbl pi_K fs_Bx fs_Bspan pi_SH FUEL 0x84ae8 pi_ss_ws0)).
Definition pi_lh : sstate :=
  add_atom
    (mkSS 0x84ae8
      (sr_set (sr_set (ss_regs pi_lh0) (10%bv : bv 5) (SOff 37 0)) (13%bv : bv 5) (SOff 37 0))
      (pi_cb_region :: ss_mem pi_lh0) (ss_resv pi_lh0) (ss_facts pi_lh0))
    37%nat (mkAF 4096 (2 ^ 47 - 2 ^ 23) 0).
Definition pi_SHl : list shent := mkSHE 37 0 1 :: pi_SH.
Definition pi_Kl : nat := run_K 0 fs_Bx pi_SHl pi_lh.
Definition pi_wsbit : sv := SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SData 0 0 1)) (SLit 1).
Lemma pi_lh_static_ok : sh_static_ok pi_Kl fs_Bx fs_Bspan pi_SHl (ss_facts pi_lh) (ss_mem pi_lh) = true.
Proof. vm_compute. reflexivity. Qed.
(* the loop head to the first value branch *)
Lemma pi_run_iter_a :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_Kl fs_Bx fs_Bspan pi_SHl FUEL pi_lh in
  (snd r, sh_obls (fst r), ss_pc (sh_ss (fst r))) =
    (TS_stopped (SR_branch BC_LTU (SLit 32) (SData 0 0 1)), [], 0x84afc).
Proof. vm_compute. reflexivity. Qed.
(* byte <= 32: on to the mask test *)
Lemma pi_run_iter_b :
  let s := add_cond (sh_ss (fst (sym_runN_tok tfibsegs pitems_tbl pi_Kl fs_Bx fs_Bspan pi_SHl FUEL pi_lh)))
             (mkAC BC_GEU (SLit 32) (SData 0 0 1)) in
  let r := sym_runN_tok tfibsegs pitems_tbl pi_Kl fs_Bx fs_Bspan pi_SHl FUEL s in
  (snd r, sh_obls (fst r), ss_pc (sh_ss (fst r))) =
    (TS_stopped (SR_branch BC_EQ pi_wsbit (SLit 0)), [], 0x84b08).
Proof. vm_compute. reflexivity. Qed.
(* the byte is white space: the iteration closes at the back edge with the cursor and in->p both at c + 1 *)
Lemma pi_run_iter_c :
  let s1 := add_cond (sh_ss (fst (sym_runN_tok tfibsegs pitems_tbl pi_Kl fs_Bx fs_Bspan pi_SHl FUEL pi_lh)))
              (mkAC BC_GEU (SLit 32) (SData 0 0 1)) in
  let s2 := add_cond (sh_ss (fst (sym_runN_tok tfibsegs pitems_tbl pi_Kl fs_Bx fs_Bspan pi_SHl FUEL s1)))
              (mkAC BC_NE pi_wsbit (SLit 0)) in
  let r := sym_run_toN_tok tfibsegs pitems_tbl pi_Kl fs_Bx fs_Bspan pi_SHl FUEL 0x84ae8 s2 in
  (snd r, sh_obls (fst r), ss_pc (sh_ss (fst r)),
   nth 10 (ss_regs (sh_ss (fst r))) (SLit 0), nth 13 (ss_regs (sh_ss (fst r))) (SLit 0),
   nth_error (ss_mem (sh_ss (fst r))) 4) =
    (TS_stopped (SR_branch BC_NE (SOff 37 1) (SOff (xatom 1) 0)), [], 0x84b20, SOff 37 1, SOff 37 1,
     Some (YP09.mkRegion (Some 10%nat) 0 24 0 24
             [YP09.mkChunk 0 (CVal 8 (SOff 37 1)); YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 1));
              YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0))])).
Proof. vm_compute. reflexivity. Qed.

(* ---- model-side facts of the writer text, for the 0x84ad0 branch and the member loop ----
   S0's parse_items_spec gives the bytes at in->p as `rest_at tb text p = wt ++ rest` with
   wt = concat (WriterValue.wvpieces (JObj ms) pr k). The two `concat` steps are restated here rather than taken
   from the Stdlib so that the file does not depend on a lemma name (concat_cons / concat_app) that moved. *)
Lemma pi_concat_cons : forall (x : list Z) (l : list (list Z)), concat (x :: l) = x ++ concat l.
Proof. reflexivity. Qed.
Lemma pi_concat_app : forall (l1 l2 : list (list Z)), concat (l1 ++ l2) = concat l1 ++ concat l2.
Proof.
induction l1 as [|x l1 IH]; intros l2; [reflexivity|].
cbn [app concat]. rewrite IH, app_assoc. reflexivity.
Qed.
Lemma pi_concat_single : forall (x : list Z), concat [x] = x.
Proof. intros x. cbn [concat]. apply app_nil_r. Qed.
(* the writer's text of an object is at least `{` and `}`: whatever the members, the pieces are
   [123] :: <members> ++ <indent> ++ [[125]] (WriterValue.v:29-36) *)
Lemma pi_wt_len2 : forall (ms : list (list Z * PjTree.jv)) (pr : bool) (dd : Z),
  (2 <= length (concat (WriterValue.wvpieces (PjTree.JObj ms) pr dd)))%nat.
Proof.
intros ms pr dd. cbn [WriterValue.wvpieces].
rewrite pi_concat_cons, !pi_concat_app, !pi_concat_single, !length_app. cbn [length]. lia.
Qed.
(* and its first byte is the opening brace the caller already consumed at 0x84abc *)
Lemma pi_wt_head : forall (ms : list (list Z * PjTree.jv)) (pr : bool) (dd : Z),
  nth_error (concat (WriterValue.wvpieces (PjTree.JObj ms) pr dd)) 0 = Some 123.
Proof. intros ms pr dd. cbn [WriterValue.wvpieces]. rewrite pi_concat_cons. reflexivity. Qed.
(* the bytes left at in->p are exactly in->end - in->p (pj_in_ok's text length and p range) *)
Lemma pi_rest_len : forall m q text len p d (tb : list byte),
  PjIn.pj_in_ok tfibsegs m q text len p d tb ->
  Z.of_nat (length (ReaderRes.rest_at tb text p)) = text + len - p.
Proof.
intros m q text len p d tb H.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ H) as (_ & _ & _ & (Hp1 & Hp2) & _ & _ & Hlen & _).
unfold ReaderRes.rest_at, ReaderRes.zb. rewrite length_map, length_skipn.
pose proof (Z2Nat.id (p - text) ltac:(lia)) as Hid. lia.
Qed.
(* STAGE 2's MODEL SIDE: the branch `bgeu a3,a2` at 0x84ad0 compares in->p + 1 with in->end. It is NOT decidable
   from the atom ranges; the walk decides it here, from the spec's own text premise: the writer's object text is at
   least two bytes long and sits at in->p, so in->p + 1 is still inside the text. *)
Lemma pi_p1_lt_end : forall m q text len p d (tb : list byte) ms pr dd rest,
  PjIn.pj_in_ok tfibsegs m q text len p d tb ->
  ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr dd) ++ rest ->
  p + 1 < text + len.
Proof.
intros m q text len p d tb ms pr dd rest H HR.
pose proof (pi_rest_len m q text len p d tb H) as HL.
rewrite HR, length_app in HL. pose proof (pi_wt_len2 ms pr dd) as H2. lia.
Qed.
(* MEASURED: s0 holds q (a0) at 0x84ad0 - the `mv s0, a0` at 0x84a5c is the only write to s0 in the 429
   instructions, and s0 is callee-saved, so s0 = q at all five calls (brief item 4). a1 (atom 11 = v) is likewise
   kept in s4 and the shadow base in s10. *)
Lemma pi_s0_q_84ad0 :
  (nth 8 (ss_regs (sh_ss pi_st_84ad0)) (SLit 0), nth 20 (ss_regs (sh_ss pi_st_84ad0)) (SLit 0)) =
  (SOff 10%nat 0, SOff 11%nat 0).
Proof. vm_compute. reflexivity. Qed.

(* ---- the member decomposition of the writer's object text, for the member loop at 0x84bac ----
   WriterValue.v:29-36 builds an object as [123] :: <members> ++ <closing indent> ++ [[125]], where <members> is an
   anonymous fix over the member list carrying the index i (i = 0 gets no comma, every later one gets one). The fix
   has no name, so it is mirrored here as pi_mgo and the two are proved equal; every later lemma speaks of pi_mgo. *)
Fixpoint pi_mgo (pr : bool) (dd : Z) (i : nat) (l : list (list Z * PjTree.jv)) {struct l} : list (list Z) :=
  match l with
  | [] => []
  | (kk, x) :: r =>
      WriterValue.wcomma i ++ WriterValue.wind pr (dd + 1) ++ WriterSpec.spieces kk
      ++ [WriterValue.wsep pr] ++ WriterValue.wvpieces x pr (dd + 1) ++ pi_mgo pr dd (S i) r
  end.
Lemma pi_obj_pieces : forall (ms : list (list Z * PjTree.jv)) (pr : bool) (dd : Z),
  WriterValue.wvpieces (PjTree.JObj ms) pr dd =
  [123] :: pi_mgo pr dd 0 ms ++ (match ms with [] => [] | _ :: _ => WriterValue.wind pr dd end) ++ [[125]].
Proof.
intros ms pr dd. cbn [WriterValue.wvpieces]. f_equal. f_equal.
generalize 0%nat. induction ms as [|[kk x] ms IH]; intros n; [reflexivity|].
cbn [pi_mgo]. rewrite IH. reflexivity.
Qed.
(* the empty object is exactly `{}`: the 0x84b58 / 0x84b60 test takes the `}` arm at once *)
Lemma pi_obj_nil : forall (pr : bool) (dd : Z),
  concat (WriterValue.wvpieces (PjTree.JObj []) pr dd) = [123; 125].
Proof.
intros pr dd. rewrite pi_obj_pieces. cbn [pi_mgo app].
rewrite pi_concat_cons, pi_concat_single. reflexivity.
Qed.
(* a non-empty object: `{`, the first member's indent (white space), its key string, the separator, the member's
   value, then the rest of the members, the closing indent and `}` *)
Lemma pi_obj_cons : forall kk x (ms : list (list Z * PjTree.jv)) (pr : bool) (dd : Z),
  concat (WriterValue.wvpieces (PjTree.JObj ((kk, x) :: ms)) pr dd) =
  123 :: concat (WriterValue.wind pr (dd + 1)) ++ concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr
       ++ concat (WriterValue.wvpieces x pr (dd + 1)) ++ concat (pi_mgo pr dd 1 ms)
       ++ concat (WriterValue.wind pr dd) ++ [125].
Proof.
intros kk x ms pr dd. rewrite pi_obj_pieces. cbn [pi_mgo WriterValue.wcomma].
rewrite pi_concat_cons, !pi_concat_app, !pi_concat_single.
cbn [app]. rewrite !app_assoc. reflexivity.
Qed.
(* a key string starts with the quote the walk tests at 0x84c40 *)
Lemma pi_spieces_head : forall kk : list Z,
  concat (WriterSpec.spieces kk) = 34 :: concat (WriterSpec.spieces_run [] kk) ++ [34].
Proof.
intros kk. unfold WriterSpec.spieces.
rewrite pi_concat_cons, pi_concat_app, pi_concat_single. reflexivity.
Qed.

(* ---- the white-space bridge: the machine's mask test IS PjGrammar.ws ----
   The loop tests `32 < byte` (0x84afc) and then bit `byte` of 0x100003200 = 4294977024 (0x84b00-0x84b08). The mask
   has exactly the bits 9, 10, 13 and 32, so on 0 <= byte <= 32 the bit is PjGrammar.ws byte, and above 32 ws is
   false - together, the loop consumes exactly the model's white space. *)
Lemma pi_ws_gt32 : forall c, 32 < c -> PjGrammar.ws c = false.
Proof.
intros c H. unfold PjGrammar.ws.
assert (E1 : (c =? 32) = false) by (apply Z.eqb_neq; lia).
assert (E2 : (c =? 9) = false) by (apply Z.eqb_neq; lia).
assert (E3 : (c =? 10) = false) by (apply Z.eqb_neq; lia).
assert (E4 : (c =? 13) = false) by (apply Z.eqb_neq; lia).
rewrite E1, E2, E3, E4. reflexivity.
Qed.
Lemma pi_wsmask : forall c, 0 <= c <= 32 ->
  Z.land (Z.shiftr 4294977024 c) 1 = (if PjGrammar.ws c then 1 else 0).
Proof.
intros c Hc.
assert (E : forallb (fun k => Z.eqb (Z.land (Z.shiftr 4294977024 k) 1) (if PjGrammar.ws k then 1 else 0))
              (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
assert (HIn : In c (map Z.of_nat (seq 0 33))).
{ apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
pose proof (proj1 (forallb_forall _ _) E c HIn) as H. apply Z.eqb_eq. exact H.
Qed.
(* the writer's indent is white space, so the loop runs over it and stops at the next real byte *)
Lemma pi_ws_repeat : forall n, Forall (fun c => PjGrammar.ws c = true) (concat (repeat [32; 32] n)).
Proof.
induction n as [|n IH]; [constructor|].
cbn [repeat]. rewrite pi_concat_cons. apply Forall_app. split; [|exact IH].
repeat constructor.
Qed.
Lemma pi_wind_ws : forall (pr : bool) (dd : Z),
  Forall (fun c => PjGrammar.ws c = true) (concat (WriterValue.wind pr dd)).
Proof.
intros pr dd. unfold WriterValue.wind. destruct pr; [|constructor].
rewrite pi_concat_cons. apply Forall_app. split; [repeat constructor | apply pi_ws_repeat].
Qed.

(* the zeroed object's words, as the v region's chunks need them (pj_zero is bytes_at of 56 zero bytes) *)
Lemma pi_nth_repeat : forall (A : Type) (x : A) n i, (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof. intros A x n. induction n as [|n IH]; intros [|i] H; cbn; try lia; [reflexivity | apply IH; lia]. Qed.
Lemma pi_zero_val : forall m v off n, PjStruct.pj_zero tfibsegs m v -> 0 <= off -> off + Z.of_nat n <= 56 ->
  val_mem tfibsegs m (v + off) n 0.
Proof.
intros m v off n (_ & (_ & _ & HB)) Hoff Hn k Hk.
pose proof (HB (Z.to_nat (off + Z.of_nat k)) ltac:(rewrite repeat_length; lia)) as Hx.
rewrite Z2Nat.id in Hx by lia. rewrite pi_nth_repeat in Hx by lia.
replace (v + off + Z.of_nat k) with (v + (off + Z.of_nat k)) by lia.
assert (L0 : YO0f.le_byte 0 n k = 0).
{ unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. }
rewrite L0. exact Hx.
Qed.

(* A/ACex.v:322 stack_cells8 *)
Lemma pi_stack_cells8 : forall lo hi x, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x -> x + 8 <= hi ->
  lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
intros lo hi x Hlo Hhi H1 H2.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as A. pose proof (Z.div_mod hi 4096 ltac:(lia)) as C.
rewrite Hlo, Z.add_0_r in A. rewrite Hhi, Z.add_0_r in C. split.
- rewrite A. replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite A, C.
  replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8) by lia.
  apply Z_mod_mult.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* until ACeg builds, the two cell equations stand for TfibLib (FSW_K.v's fsw_entryT premises) *)
Hypothesis TMP_TL_GOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis TMP_TL_CELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.

(* A/ACex.v:330 RA_stack, copied *)
Lemma pi_RA_stack : forall ly S (W : world tfibsegs) mem md x n,
  AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 ->
  8 <= n -> range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S W mem md x n HAR Hlo Hhi Hx8 Hn8 Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
destruct (pi_stack_cells8 _ _ x Hpal Hpah ltac:(lia) ltac:(lia)) as [Hm1 Hm2].
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.

(* ---- the write window of the entry state: what the engine's runs are allowed to touch ----
   Over RELOC's core (YCbq.v:460-467 as in S0 400b2a240b3: awr_byte = awr_byte0 \/ static arm \/ caller-frame arm
   with fr0 := frames S, passed after own). The regions of pi_ss0 with a window: the frame [sp - 144, sp) and struct
   pj_in [q, q + 24) are inside the journal's window [ot - STK', ot), STK' = STK + (ot - sp) (awr_byte0's first
   disjunct); the two shadow-base cells are read-only; the object [v, v + 56) is the caller's FP and lies either in
   a live block (pobj's heap arm: awr_byte0's second disjunct) or in a live fake frame of frames S (pobj's frame arm,
   level k = 0, where v is pj_parse's `out` in check_round_trip's class-3 frame: awr_byte's caller-frame arm). Both
   arms of pobj are covered. EXCLUSIVITY comes from FP, not from the arm: the FP the caller passes must cover ONLY
   the object's bytes inside that frame - here exactly [v, v + 56). *)
Lemma pi_awr_ok : forall ly S (W : world tfibsegs) mem regs q ot v text len p d STK FP,
  spZ regs <= q -> q + 24 <= ot -> alloc_ceiling + STK <= spZ regs -> FRAME_parse_items <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v ->
  0 <= q -> q + 24 <= 2 ^ 64 -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  pobj tfibsegs B ly S W mem v ->
  (forall a, v <= a < v + 56 -> inFP FP a) ->
  awr_ok tfibsegs B (Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) (ss_mem pi_ss0)
    (STK + (ot - spZ regs)) ot FP (ablocks B ly S) (ablocks B ly S) ly [] (frames S).
Proof.
intros ly S W mem regs q ot v text len p d STK FP Hsq Hq24 Hceil HSTK H10 H11 Hq0 Hq64 Hv0 Hv64 HPO HFP.
pose proof asan_consts as (C1 & _).
set (E := Ereg regs (fs_extraT ++ pi_xs p (text + len) d)).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 2 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = q)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 10 10%bv eq_refl), H10;
      apply MState.unsigned_lit; lia).
assert (E11 : bv_unsigned (ew E 11) = v)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 11 11%bv eq_refl), H11;
      apply MState.unsigned_lit; lia).
assert (HF : FRAME_parse_items = 144) by reflexivity.
unfold pi_ss0, fss0T_args, fsT_regions_args, fsT_regions, pi_rs.
cbn [ss_mem app].
(* the frame *)
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
  [reflexivity | cbn [fstk YP09.r_base]; rewrite E2; lia
  | cbn [fstk YP09.r_wlo]; lia | cbn [fstk YP09.r_whi]; lia |].
(* the two shadow-base cells: read-only *)
apply awr_ok_cons_ro; [cbn [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
(* struct pj_in, inside the journal's window *)
eapply awr_ok_cons_stack_off with (n := 10%nat) (d := q - ot);
  [reflexivity | cbn [pi_q_region YP09.r_base]; rewrite E10; lia
  | cbn [pi_q_region YP09.r_wlo]; lia | cbn [pi_q_region YP09.r_whi]; lia |].
(* the object: the caller's FP, in a live block or in a live fake frame *)
eapply awr_ok_cons_gen with (k := 11%nat) (b := v);
  [reflexivity | cbn [pi_v_region YP09.r_base]; exact E11 | | apply awr_ok_nil].
intros a Ha. cbn [pi_v_region YP09.r_wlo YP09.r_whi] in Ha.
destruct HPO as [[((cid & pos & Hin & Hcid & Hal & H1 & H2) & _ & _) | ((b & m & Hin & H1 & H2) & _ & _)] _].
- (* frame arm: awr_byte's caller-frame disjunct *)
  right. right. split; [apply HFP; lia|]. exists cid, pos. split; [exact Hin|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia.
- (* heap arm: awr_byte0's FP-in-a-live-block disjunct *)
  left. right. left. split; [apply HFP; lia|]. exists b, m. split; [exact Hin | unfold HEAD in *; lia].
Qed.

(* ---- STAGE 1: the entry state of the walk ---- *)
(* Under parse_items_spec's premises at its entry, the symbolic state pi_ss0 holds at A_parse_items, the journal is
   open over the caller's raised window [sp - STK, ot) at any FP, ARU holds, and the two shadow entries hold. *)
Theorem pitems_entry :
  forall ly S Us (W : world tfibsegs) regs mem md ch FP q ot v text len p (tb : list byte) tcap d STK,
  afn_preU tfibsegs B STK ly S Us W regs mem md ch ->
  FRAME_parse_items <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= spZ regs - STK \/ ot <= v) ->
  0 <= d <= 1 ->
  st_ok tfibsegs (Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) pi_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_parse_items) mem (seg_rom tfibsegs))) /\
  ajournal tfibsegs B (STK + (ot - spZ regs)) ot FP ly S W (unpoison Us mem) md []
    ly S W (unpoison Us mem) md 0 /\
  ARU tfibsegs B ly S Us W mem md /\
  sh_ok tfibsegs fs_Bx pi_SH (Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) (mrestrict (w_H W) mem).
Proof.
intros ly S Us W regs mem md ch FP q ot v text len p tb tcap d STK HPRE HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO HAP Hd.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_ARU B STK ly S Us W regs mem md ch HPRE) as HARU.
pose proof HPRE as (HAPRE & _ & _).
pose proof HAPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (fsw_sp B STK ly S Us W regs mem md ch HPRE) as (_ & HceilSTK & H47sp & HS0).
destruct HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
set (E := Ereg regs (fs_extraT ++ pi_xs p (text + len) d)).
(* register atoms *)
assert (E10 : ew E 10 = Z_to_bv 64 q)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 1)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 12 12%bv eq_refl); exact H12).
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E; rewrite (ew_Ereg_nat regs (fs_extraT ++ pi_xs p (text + len) d) 2 2%bv eq_refl); reflexivity).
(* extra atoms *)
assert (EX0 : ew E (xatom 0) = Z_to_bv 64 p) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (EX1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
assert (EX2 : ew E (xatom 2) = Z_to_bv 64 d) by (unfold E; rewrite fsw_ew_xatom; reflexivity).
(* the object's placement *)
destruct (fsw_pobj_low B ly S W (unpoison Us mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
(* the text block's bounds: p and in->end are heap addresses below alloc_ceiling *)
destruct HTX as (Htx4096 & Htxblk & Htxlen).
destruct (fsw_rblock_low B ly S W (unpoison Us mem) md mem text tcap HAR Htxblk) as (Ht1 & Ht2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0 & Hq64 & Htext0 & Hptx & Htxhi & Hqapart & Htblen & Hq8 & Hdrange).
assert (Hp1 : 4096 <= p) by (unfold HEAD in *; lia).
assert (Hp2 : p <= 2 ^ 47 - 2 ^ 23) by lia.
assert (He1 : 4096 <= text + len) by (unfold HEAD in *; lia).
assert (He2 : text + len <= 2 ^ 47 - 2 ^ 23) by lia.
(* q lies in the stack window *)
assert (Hqlo : ly_stk_lo ly <= q) by lia.
assert (Hqhi : q + 24 <= ly_stk_hi ly) by lia.
assert (Hq46 : 2 ^ 46 <= q) by lia.
assert (Hq47 : q <= 2 ^ 47 - 24) by lia.
(* ---- the regions ---- *)
assert (RQ : YP09.region_ok tfibsegs E (mrestrict (w_H W) mem) pi_q_region).
{ pose proof HIN as (Bp & Be & Bd & Bw & _).
  unfold pi_q_region, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10, (MState.unsigned_lit q) by lia.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. unfold YP09.writable_at. destruct Bw as (_ & _ & Bw3). exact (Bw3 o ltac:(lia)).
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (fsw_pj_chunk8 tfibsegs E (mrestrict (w_H W) mem) q 0 (SOff (xatom 0) 0) p);
        [rewrite Z.add_0_r; split; [lia | exact Bp] | rewrite fsw_SOff0; exact EX0].
    + apply (fsw_pj_chunk8 tfibsegs E (mrestrict (w_H W) mem) q 8 (SOff (xatom 1) 0) (text + len));
        [split; [lia | exact Be] | rewrite fsw_SOff0; exact EX1].
    + apply (fsw_pj_chunk4 tfibsegs E (mrestrict (w_H W) mem) q 16 (SOff (xatom 2) 0) d);
        [split; [lia | exact Bd] | rewrite fsw_SOff0; exact EX2]. }
assert (RV : YP09.region_ok tfibsegs E (mrestrict (w_H W) mem) pi_v_region).
{ unfold pi_v_region, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E11, (MState.unsigned_lit v) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; exact (proj2 HPO o ltac:(lia))|].
  repeat (apply Forall_cons;
    [apply (chunk_ok_val tfibsegs E _ v _ _ (SLit 0) 0);
       [reflexivity | cbn; lia | cbn; lia | apply pi_zero_val; [exact HZERO | lia | cbn; lia]] |]).
  apply Forall_nil. }
(* ---- disjointness ---- *)
assert (HGOT : v + 56 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/
               tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= v).
{ pose proof (fsw_pobj_off_img B ly S W (unpoison Us mem) md mem v HAR HPO) as HO.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, FS_IMG_END in *. lia. }
assert (HCELL : v + 56 <= tfib_D_asan_shadow_memory_dynamic_address \/
                tfib_D_asan_shadow_memory_dynamic_address + 8 <= v).
{ pose proof (fsw_pobj_off_img B ly S W (unpoison Us mem) md mem v HAR HPO) as HO.
  unfold tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *. lia. }
assert (HDJ : YP09.pairwise_disjoint E (fsT_regions_args FRAME_parse_items pi_rs)).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, pi_rs, pi_q_region, pi_v_region,
    extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2, E10, E11, (MState.unsigned_lit q) by lia. rewrite (MState.unsigned_lit v) by lia.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
  assert (HF : FRAME_parse_items = 144) by reflexivity.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
(* ---- the atom facts ---- *)
assert (HGF : atoms_ok E pi_gf).
{ unfold pi_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E11, E12, EX0, EX1, EX2. rewrite !MState.unsigned_lit by lia.
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r.
  split; [split; [lia | split; [exact Hq8 | lia]]|].
  split; [split; [lia | split; [exact Hv8 | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [split; [lia | split; [apply Z.mod_1_r | lia]]|].
  split; [|exact I]. split; [lia | split; [apply Z.mod_1_r | lia]]. }
(* ---- the entry state ---- *)
assert (HS : st_ok tfibsegs E pi_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_parse_items) mem (seg_rom tfibsegs)))).
{ unfold pi_ss0.
  apply (fsw_entryT_argsX B STK FRAME_parse_items ly S Us W regs mem md ch A_parse_items pi_rs pi_gf
    (pi_xs p (text + len) d) TMP_TL_GOT TMP_TL_CELL HPRE ltac:(split; [vm_compute; discriminate | exact HSTK])
    pi_regions_wf); [| exact HDJ | exact HGF].
  constructor; [exact RQ | constructor; [exact RV | constructor]]. }
split; [exact HS|].
(* ---- the journal over the caller's raised window ---- *)
split.
{ exact (fsw_ajournal_init_ot B STK FP ly S Us W regs mem md ch ot HPRE ltac:(lia) Hot16 Hotly Hpot). }
split; [exact HARU|].
(* ---- the two shadow entries ---- *)
unfold sh_ok, pi_SH. constructor; [|constructor; [|constructor]].
- (* q: the stack's shadow is zero (AR's zero_shadow_ranges head) *)
  apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 10%nat q 24 q 0 24);
    [ apply (proj1 (fsw_ARU_stack_ra tfibsegs B (AR_laws_ok tfibsegs B) ly S Us W mem md (w_H W) q 24 HARU
        ltac:(lia) ltac:(lia)));
      exact (pi_RA_stack ly S W (unpoison Us mem) md q 24 HAR Hqlo Hqhi Hq8 ltac:(reflexivity) ltac:(lia))
    | unfold fs_Bx; apply U_atom;
      [unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity | unfold SHADOW_OFF; lia]
    | apply U_atom; [exact E10 | lia]
    | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
- (* v: pobj's own range_addressable; a client object is outside the shadow band (in_app) *)
  apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 11%nat v 56 v 0 56);
    [ destruct HPO as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr
    | unfold fs_Bx; apply U_atom;
      [unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity | unfold SHADOW_OFF; lia]
    | apply U_atom; [exact E11 | lia]
    | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx.
  exact (fsw_pobj_off_shadow B ly S W (unpoison Us mem) md mem v HAR HPO x ltac:(lia)).
Qed.

(* ---- STAGE 1b: the entry RUN. The engine's token run from A_parse_items to the first model branch 0x84ad0,
   as an SRr implication: whatever the rest of the walk proves from the state there (run_post_tok_AJU, the kit's own
   continuation shape) holds at the entry configuration. This is the first step of the walk that RUNS, so it is the
   first that needs awr_ok; over RELOC's core it covers BOTH arms of pobj, so every level k = 0, 1.
   BASE: hv5a e7266e15dbe (S0 400b2a240b3 + reloc-wip 4b90d538804, RELOC's FP-keyed core); no callee spec taken. *)
Theorem pitems_entry_run :
  forall ly S Us (W : world tfibsegs) regs mem md ch q ot v text len p (tb : list byte) tcap d STK FP Q,
  afn_preU tfibsegs B STK ly S Us W regs mem md ch ->
  FRAME_parse_items <= STK ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v -> YK11.getr regs 12 = w64 1 ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  pobj tfibsegs B ly S W mem v -> PjStruct.pj_zero tfibsegs (mrestrict (w_H W) mem) v ->
  (v + 56 <= spZ regs - STK \/ ot <= v) ->
  0 <= d <= 1 ->
  (* the caller's FP over the object *)
  (forall a, v <= a < v + 56 -> inFP FP a) ->
  run_post_tok_AJU B W (Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) pi_K fs_Bx pi_SH pi_ss0 pi_st_84ad0
    (mkst regs (Z_to_bv 64 A_parse_items) mem (seg_rom tfibsegs))
    (STK + (ot - spZ regs)) ot FP ly S W (unpoison Us mem) md [] ly S Us md 0 Q ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_parse_items regs mem md) Q.
Proof.
intros ly S Us W regs mem md ch q ot v text len p tb tcap d STK FP Q
  HPRE HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO HAP Hd HFP HK.
pose proof asan_consts as (C1 & _).
destruct (pitems_entry ly S Us W regs mem md ch FP q ot v text len p tb tcap d STK
  HPRE HSTK H10 H11 H12 HIN HWIN HTX HPO HZERO HAP Hd) as (HS & HJ & HARU & HSH).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof (fsw_sp B STK ly S Us W regs mem md ch HPRE) as (Hal16 & HceilSTK & H47sp & HS0).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & _).
pose proof HPRE as (HAPRE & _ & _). pose proof HAPRE as (HAR & _).
destruct (fsw_pobj_low B ly S W (unpoison Us mem) md mem v HAR HPO) as (Hv4096 & Hvceil).
unfold YG0d.cfg_at.
change (w64 A_parse_items) with (Z_to_bv 64 A_parse_items).
eapply (fsw_run_to_tok_AJU B pitems_tbl pitems_tbl_ok W FUEL 0x84ad0
  (Ereg regs (fs_extraT ++ pi_xs p (text + len) d)) pi_K fs_Bx fs_Bspan pi_SH pi_ss0 pi_st_84ad0 TS_running
  (mkst regs (Z_to_bv 64 A_parse_items) mem (seg_rom tfibsegs))
  (STK + (ot - spZ regs)) ot FP ly S W (unpoison Us mem) md [] ly S Us md 0 Q).
- exact HS.
- cbn [ms_mem mkst]. exact HSH.
- exact pi_static_ok.
- exact pi_run_eq.
- exact I.
- cbn [ms_mem mkst]. exact HARU.
- cbn [ms_mem mkst]. exact HJ.
- rewrite pi_obls_84ad0. constructor.
- exact (pi_awr_ok ly S W mem regs q ot v text len p d STK FP Hsq Hq24 HceilSTK HSTK H10 H11
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HPO HFP).
- exact HK.
Qed.

End W.

(* ---- STAGE 3, MEASURED: out of white-space loop 1, the `}` test, and the two arms it opens ----
   From the loop-head state with the cursor byte as a CData chunk (pi_ss_ws1), the arm `32 < byte` (0x84afc taken)
   is the one the model takes at a non-white-space byte. The run then crosses the empty-object checks - the shadow
   reads of q (0x84b34) and of the cursor (0x84b4c), both COVERED by the two shadow entries, so NO obligation - and
   stops at the model branch 0x84b60 `beq 0x7d, byte`.
   The token budget is 200 here, not pi_K1 = 36: the entry budget is spent by the loop's own shadow reads, and
   sh_static_ok holds at 200 (pi_nws_static_ok), which is all the kit's run lemmas ask of K. *)
Definition pi_K2 : nat := 200.
Definition pi_st_ws1 : shst := fst (sym_runN_tok tfibsegs pitems_tbl pi_K1 fs_Bx fs_Bspan pi_SH1 FUEL pi_ss_ws1).
Definition pi_ss_nws : sstate := add_cond (sh_ss pi_st_ws1) (mkAC BC_LTU (SLit 32) (SData 0 0 1)).
Lemma pi_nws_static_ok :
  sh_static_ok pi_K2 fs_Bx fs_Bspan pi_SH1 (ss_facts pi_ss_nws) (ss_mem pi_ss_nws) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pi_run_b60 :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL pi_ss_nws in
  (snd r, ss_pc (sh_ss (fst r)), sh_obls (fst r), sh_chk (fst r)) =
    (TS_stopped (SR_branch BC_EQ (SLit 125) (SData 0 0 1)), 0x84b60, [], true).
Proof. vm_compute. reflexivity. Qed.
Definition pi_ss_b60 : sstate :=
  sh_ss (fst (sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL pi_ss_nws)).

(* ARM A (the byte is not `}`: the object has members): the walk falls through 0x84b64 `mv a0,s4` and TAKES THE
   FIRST grow CALL at 0x84b68. MEASURED: the engine steps the jal and stops at grow's entry A_grow = 0x83a48 with
   SR_fetch (grow's text is outside parse_items' table), a0 = v (atom 11) and ra = 0x84b6c, raising NO obligation.
   This is the call interface the grow stage consumes: grow_spec's v is this a0, and its `n = cap` arm is the one
   with cap = 0, so Dold0 = [] and `rd_sum Dold0 <= live` is 0 <= live. *)
Lemma pi_run_grow1 :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL
             (add_cond pi_ss_b60 (mkAC BC_NE (SLit 125) (SData 0 0 1))) in
  (snd r, ss_pc (sh_ss (fst r)), sh_obls (fst r),
   nth 10 (ss_regs (sh_ss (fst r))) (SLit 0), nth 1 (ss_regs (sh_ss (fst r))) (SLit 0)) =
    (TS_stopped SR_fetch, 0x83a48, [], SOff 11%nat 0, SLit 0x84b6c).
Proof. vm_compute. reflexivity. Qed.

(* ARM B (the byte IS `}`: the EMPTY object, ms = []): 0x84b60 jumps straight to the close at 0x84e9c, which lowers
   in->depth, sets the result 0 and runs the epilogue. MEASURED: the whole close and epilogue run with NO obligation
   and NO call, and stop at the `ret` 0x84f10 with the jalr target s_ra = SOff 1 0 (the entry ra, restored from the
   frame). So on the empty object parse_items reaches its return with no callee at all - the one complete
   machine path of this function that needs no callee contract. *)
Lemma pi_run_close_empty :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL
             (add_cond pi_ss_b60 (mkAC BC_EQ (SLit 125) (SData 0 0 1))) in
  (snd r, ss_pc (sh_ss (fst r)), sh_obls (fst r), sh_chk (fst r)) =
    (TS_stopped (SR_jalr (SOff 1%nat 0)), 0x84f10, [], true).
Proof. vm_compute. reflexivity. Qed.

(* MEASURED, the whole post of the EMPTY-object path at the `ret`, and it is exactly parse_items_spec's:
     a0 = 0                                   (the spec's `getr regs' 10 = w64 0`)
     sp, s0, s1 back to their entry atoms      (acallee_saved; the epilogue's thirteen reloads)
     struct pj_in at q: in->p = p + 2, in->end unchanged, in->depth = d again
       - and p + 2 = p + length (concat (wvpieces (JObj []) pr dd)) by pi_obj_nil, which is the spec's
         `pj_in_ok ... (p + Z.of_nat (length wt))`, so the model and the machine agree on the empty object
     the result object v: type = 6 = PJ_OBJECT and nothing else written (the spec's rtree for JObj [] with D = []). *)
Lemma pi_close_empty_state :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL
             (add_cond pi_ss_b60 (mkAC BC_EQ (SLit 125) (SData 0 0 1))) in
  (nth 10 (ss_regs (sh_ss (fst r))) (SLit 0), nth 2 (ss_regs (sh_ss (fst r))) (SLit 0),
   nth 8 (ss_regs (sh_ss (fst r))) (SLit 0), nth 9 (ss_regs (sh_ss (fst r))) (SLit 0),
   nth_error (ss_mem (sh_ss (fst r))) 4, nth_error (ss_mem (sh_ss (fst r))) 5) =
    (SLit 0, SOff 2%nat 0, SOff 8%nat 0, SOff 9%nat 0,
     Some (YP09.mkRegion (Some 10%nat) 0 24 0 24
             [YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0)); YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 2));
              YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0))]),
     Some pi_v_region6).
Proof. vm_compute. reflexivity. Qed.

(* ---- SCOUTING MEASUREMENTS of the member path (NOT stages of the composed walk) ----
   These two run the engine from pi_ss_r1, which is the state AT the first grow call with a0 := 0 and grow's POST
   NOT applied (the v region still carries only the type word). So they are measurements of parse_items' TEXT -
   where the segments cut, which checks are covered, what each call's interface is - and not steps of the walk: the
   composed member stage will seat the kit's fss_retT (FSW_ret.v) after grow's post and re-measure there. They are
   kept because every cut point and both call interfaces below are what that stage has to hit.
     pi_scout_memb_c44: from 0x84b6c the run crosses the member-loop set-up (0x84b70-0x84ba8: s6 = v + 0x28,
       s8 = v + 0x18, s2 = shadow (v + 0x28), the three frame slots), the loop head 0x84bac (`beqz s3` folded: the
       object flag is 1), the two shadow reads of q + 8 and q, the in->p / in->end reload and white-space loop 2,
       and stops at the KEY QUOTE TEST 0x84c44 `bne byte, 34` with NO obligation.
     pi_scout_call_ps: on the quote arm it steps the jal at 0x84c4c and stops at parse_string's entry
       A_parse_string = 0x850b8 with a0 = q (atom 10, i.e. s0 - brief item 4: s0 = q at every call) and
       ra = 0x84c50, again with no obligation. That is the argument parse_string_spec takes, and the reason its C5
       chain premise is read at q - which parse_items_spec's new frame-chain premise supplies. *)
Definition pi_ss_r1 : sstate :=
  let s := sh_ss (fst (sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL
                         (add_cond pi_ss_b60 (mkAC BC_NE (SLit 125) (SData 0 0 1))))) in
  mkSS 0x84b6c (sr_set (ss_regs s) (10%bv : bv 5) (SLit 0)) (ss_mem s) (ss_resv s) (ss_facts s).
Lemma pi_scout_memb_c44 :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL pi_ss_r1 in
  (snd r, ss_pc (sh_ss (fst r)), sh_obls (fst r), sh_chk (fst r)) =
    (TS_stopped (SR_branch BC_NE (SData 0 0 1) (SLit 34)), 0x84c44, [], true).
Proof. vm_compute. reflexivity. Qed.
Definition pi_ss_c44 : sstate :=
  sh_ss (fst (sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL pi_ss_r1)).
Lemma pi_scout_call_ps :
  let r := sym_runN_tok tfibsegs pitems_tbl pi_K2 fs_Bx fs_Bspan pi_SH1 FUEL
             (add_cond pi_ss_c44 (mkAC BC_EQ (SData 0 0 1) (SLit 34))) in
  (snd r, ss_pc (sh_ss (fst r)), sh_obls (fst r),
   nth 10 (ss_regs (sh_ss (fst r))) (SLit 0), nth 1 (ss_regs (sh_ss (fst r))) (SLit 0)) =
    (TS_stopped SR_fetch, 0x850b8, [], SOff 10%nat 0, SLit 0x84c50).
Proof. vm_compute. reflexivity. Qed.

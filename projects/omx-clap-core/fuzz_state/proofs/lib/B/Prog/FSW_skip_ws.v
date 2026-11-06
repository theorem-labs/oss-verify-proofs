(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_parse_items.v, with its module paths, module names and numbers changed; 1021 of its 1091 lines of code are new or changed and 499 lines of the source are left out. *)
(* fs program part, READER group, image B (fs.asan-ubsan): the ASan+UBSan walk of skip_ws (A_skip_ws 0x83598,
   pf.c:36-40), against lib/B/FSH_Fn_reader.v:552 skip_ws_spec. skip_ws is OUT OF LINE in image B only (A inlines it
   into pj_parse, parse_value and parse_items), so this is the whole function: entry, the white-space loop and the
   return.

   rule 24: proves function skip_ws, image B (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates,
   origin/release/pau-projects-recipes, the delivered package, live working-branch heads / `proof-index skip_ws`,
   `proof-index skip_ws_spec`, `proof-index 0x83598`, run 05:47Z, re-run 05:57-05:58Z):
     proof-index skip_ws      (exit 0): 4 named, 8 by address, 0 related, 5 lemma(s), an earlier delivery 99 named and 159
                                             name(s) holding it, 141 unreleased
     proof-index skip_ws_spec (exit 3): 0 named, 0 by address, 0 related, 0 lemma(s), 0 by file name, an earlier delivery 5
                                             named and 4 name(s) holding it, 32 unreleased
     proof-index 0x83598      (exit 4): 0 named, 0 by address, 0 related, 0 lemma(s), 0 by file name, an earlier delivery 0
                                             named and 0 name(s) holding it, 98 unreleased
   PORT SOURCE (rule-24 CONFIRM by a Theorem Labs lane 06:02Z): ported from a working branch 83807a02aa29
   (= a working branch 4c7580de8268, same blob c8d767bb5d93):proofs/omx-clap-core/fuzz_state/lib/B/Prog/
   skip_ws.v `skip_ws_holds : skip_ws_contract` (Qed, no admit; skip_loop by induction on end - p; UBSan q & 7,
   p != 0 and p + 1 guards refuted; shadow checks on q, q + 8 and the text; 16-byte frame) and rdn1's
   lib/B/Prog/skip_wsF.v (footprint form). Their walk is RE-STATED here against skip_ws_spec's frame (fpreU / fpostU /
   SRr over W, rd_win, rd_text, wkeep, fs_glob): nothing of theirs is Required and no bridge to skip_ws_contract is
   made (bespoke statements are templates only, a Theorem Labs lane 04:50Z). Ported lemma by lemma:
     skip_ws.v skip_loop            -> skw_loop     (the induction, now on skw_n - i with the model's white-space run)
     skip_ws.v mask_ws              -> skw_wsmask / skw_bit_val  (the 0x100003200 mask IS PjGrammar.ws)
     skip_ws.v eqb0_word / zbr      -> the UBSan guards, now decided by the engine from the atom facts
     skip_ws.v skip_ws_holds        -> skw_entry / skw_exit / skip_ws_holds
   The engine-side shape (entry state, token runs, branch split, the return) follows image B's parse_string walk,
   a working branch f1c071f7f5ce lib/B/FSW_parse_string.v and lib/B/FSW_parse_string_s2.v; the helper
   lemmas copied from that commit's lib/B/FSW_parse_string_defs.v and _s2.v are named here with the skw_ prefix:
     pstr_cells8 -> skw_cells8, pstr_RA_stack -> skw_RA_stack, pstr_RA_stk_mem -> skw_RA_stk_mem,
     pstr_ush_blk -> skw_ush_blk, pstr_RA_unp -> skw_RA_unp, pstr_RA_blk_mem -> skw_RA_blk_mem,
     pstr_text_byte -> skw_text_byte, pstr_val_mem_eq_at -> skw_val_mem_eq_at,
     pstr_frame_none_l -> skw_frame_out, pstr_shx -> skw_shx_denot, pstr_reg_keep -> skw_reg_keep,
     ps2_mbyte_eq -> skw_mbyte_eq, ps2_wr_eq -> skw_wr_eq, ps2_bytes_at_eq -> skw_bytes_at_eq,
     ps2_chunk1_ok -> skw_chunk1_ok, ps2_reg_val -> skw_reg_val, ps2_denot_off -> skw_denot_off,
     ps2_denot_lit -> skw_denot_lit, ps2_ewR -> skw_ewR, ps2_nz -> skw_nz, ps2_req -> skw_req,
     ps2_wins_b / ps2_frame_wins / ps2_awr_wins -> skw_wins_b / skw_frame_wins / skw_awr_wins.
   The white-space model bridge (skw_ws_gt32 / skw_wsmask) is image A's parse_items walk,
   a working branch ab86042f21e lib/A/FSW_parse_items.v:391-409 (pi_ws_gt32 / pi_wsmask), restated.

   THE CODE (capstone 5.0.7, CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC over the pinned
   projects/omx-clap-core/bin/fuzz_state/fuzz_state.asan-ubsan, sha256 5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc0
   08e51491f44c053d204, bytes read at file offset = vaddr - p_vaddr + p_offset of the covering PT_LOAD;
   0x83598 .. 0x83674 = 55 four-byte instructions, table lib/B/Prog/FSW_skip_ws_tbl.v):
     0x83598 addi sp,sp,-16 / 0x8359c sd ra,8(sp)          the 16-byte frame (FSH_Base.FRAME_skip_ws)
     0x835a0 andi a1,a0,7 / 0x835a4 bnez a1 -> 0x83660     UBSAN GUARD 1 (in misaligned): refuted by pj_in_ok's
                                                            q mod 8 = 0 (atom 10 carries al2 = 3)
     0x835a8 .. 0x835b0                                    the shadow base through the GOT word 0x9fc10
     0x835b4 .. 0x835c0 bnez -> 0x83668                    ASAN CHECK 1: the 8 bytes at q (report 0x83668)
     0x835c4 .. 0x835d4 bnez -> 0x83670                    ASAN CHECK 2: the 8 bytes at q + 8 (report 0x83670)
     0x835d8 ld a4,0(a1) / 0x835dc ld a5,0(a0)             in->end, in->p
     0x835e0 bgeu a5,a4 -> 0x83654                         the empty run (p = in->end): straight to the epilogue
     0x835e4 .. 0x835f8                                    a6 = 32, a7 = (1<<32)|(1<<13)|(1<<10)|(1<<9)
                                                            = 4294977024, t0 = 1, a1 = a5
     0x835fc beqz a5 -> 0x83660                            UBSAN GUARD 2 (p = 0): refuted by 4096 <= text <= p
     0x83600 .. 0x8360c bnez -> 0x83644 -> 0x83650         ASAN CHECK 3: the byte at the cursor (report 0x83650)
     0x83610 lbu t1,0(a5) / 0x83614 bltu a6,t1 -> 0x83654  byte > 32: not white space, leave the loop
     0x83618 .. 0x83620 beqz t1 -> 0x83654                 the mask bit: 0 means not white space, leave the loop
     0x83624 addi a1,a1,1 / 0x83628 bgeu t0,a1 -> 0x83660  UBSAN GUARD 3 (p + 1 wraps): refuted by 4096 <= p
     0x8362c lbu t1,0(a3) / 0x83630 bnez -> 0x83664        ASAN CHECK 4: the 8 bytes at q, for the store
                                                            (report 0x83664)
     0x83634 addi a5,a5,1 / 0x83638 sd a5,0(a0)            in->p := p + 1 (the function's only write)
     0x8363c bltu a5,a4 -> 0x835fc                         loop while the new cursor is below in->end
     0x83640 j 0x83654                                     the cursor reached in->end: leave the loop
     0x83654 ld ra,8(sp) / 0x83658 addi sp,sp,16 / 0x8365c ret
   REPORT SITES (a Theorem Labs lane's reloc-check/report-sites-B.tsv rows 73-77), each deciding edge refuted here:
     0x83650 __asan_report_load1  (edge 0x8360c bne -> 0x83644, fallthrough of 0x83648 blt)   skw_loop, ASAN CHECK 3
     0x83660 unimp (UBSan trap)   (edges 0x835a4 bne, 0x835fc beq, 0x83628 bgeu)              skw_entry / skw_loop
     0x83664 __asan_report_store8 (edge 0x83630 bne)                                          skw_loop, ASAN CHECK 4
     0x83668 __asan_report_load8  (edge 0x835c0 bne)                                          skw_entry, ASAN CHECK 1
     0x83670 __asan_report_load8  (edge 0x835d4 bne)                                          skw_entry, ASAN CHECK 2
   Every ASan check is discharged as a token obligation (range_addressable): the two 8-byte checks on q and q + 8 and
   the one before the store from the stack's zero shadow (skw_RA_stk_mem, rd_win puts [q, q + 24) in the stack
   window), the 1-byte check on the cursor from rd_text's live block (skw_RA_blk_mem). Every UBSan guard is decided
   by the engine from the entry atom facts: q is 8-aligned (al2 = 3 on atom 10) and the cursor is in
   [4096, 0x7fffff800000).
   skip_ws calls nothing (only the __asan_report_* above, all unreached), allocates nothing (U' = U, FP = [], 0
   ticks) and writes only in->p, inside the caller's window: ajournal runs at [ot - (STK_skip_ws + (ot - sp)), ot),
   and the post's wkeep keeps every byte of [sp, ot) but in->p's word [q, q + 8) (a working branch
   fc8603a2ee7): the one store is `sd` 0x83638 at q, and skw_keepM tracks exactly the frame and that word.
   THE STATEMENT. skip_ws_holds : @skip_ws_spec fx rc SK tfibsegs B, i.e. lib/B/FSH_Fn_reader.v:552's Prop at segs :=
   tfibsegs (fs.asan-ubsan's loaded segments, the image the walk reads its code from), every sink argument explicit.
   SECTION HYPOTHESES: only HSS : FsShadowSyms B (lib/B/FSH_Base.v, the GOT word 0x9fc10 and the shadow-base cell
   0xa8438 the kit's entry state reads). No callee spec (skip_ws calls none) and no fs_img_facts clause is used.
   No Admitted, no Axiom, no Parameter, no admit. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSupoisonStack.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_skip_ws_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require KindBGlue.
Import ListNotations.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the addresses of the walk ---- *)
Definition SKW_LOOP : Z := 0x835fc.      (* the loop head *)
Definition SKW_EXIT : Z := 0x83654.      (* the epilogue *)
Definition SKW_RET : Z := 0x8365c.       (* the ret *)
(* concrete bounds the engine's range reasoning uses: the caller's struct pj_in is on the real stack, the text block
   is application memory below alloc_ceiling (as lib/B/FSW_parse_string_defs.v's RQLO / RQHI / RTLO / RTHI) *)
Definition RQLO : Z := 2 ^ 46.
Definition RQHI : Z := 2 ^ 47 - 24.
Definition RTLO : Z := 4096.
Definition RTHI : Z := 0x7fffff800000.

(* ---- the entry symbolic state: struct pj_in's first two fields at a0 (atom 10), in->p and in->end as the extra
   atoms xatom 0 / xatom 1, and the 8-byte write window for the in->p store ---- *)
Definition skw_q_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 16 0 8
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 0)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0))].
Definition skw_gf : list (nat * afact) :=
  [(10%nat, mkAF RQLO RQHI 3); (xatom 0, mkAF RTLO RTHI 0); (xatom 1, mkAF RTLO RTHI 0)].
Definition skw_ss0 : sstate := fss0T_args A_skip_ws FRAME_skip_ws [skw_q_region] skw_gf.

(* ---- the loop head 0x835fc: the cursor is a5 = a1 (atom 15), its byte the extra atom 32, the shadow base a2
   (atom 12), the shadow cell of q a3, the mask a7 and the constants a6 = 32, t0 = 1 ---- *)
Definition skw_shx (n b : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff b 0).
Definition skL_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 5%bv (SLit 1)) 17%bv (SLit 4294977024)) 16%bv (SLit 32))
    13%bv (skw_shx 10 12)) 11%bv (SOff 15 0).
Definition skL_regions : list YP09.region :=
  [YP09.mkRegion (Some 15%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
   YP09.mkRegion (Some 10%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 15 0))]].
Definition skL_facts : facts := mkFacts
  [(10%nat, mkAF RQLO RQHI 3); (12%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (14%nat, mkAF RTLO RTHI 0);
   (15%nat, mkAF RTLO RTHI 0); (32%nat, mkAF 0 255 0)] [] [].
Definition skL_ss : sstate := mkSS SKW_LOOP skL_regs skL_regions None skL_facts.
Definition skL_Bx : sv := SOff 12 0.
Definition skL_wsbit : sv := SAlu ALU_AND (SAlu ALU_SRL (SLit 4294977024) (SOff 32 0)) (SLit 1).

(* ---- the epilogue 0x83654: the saved ra in the frame ---- *)
Definition skX_ss : sstate :=
  mkSS SKW_EXIT sr_atoms [YP09.mkRegion (Some 2%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 1 0))]] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
(* what the run leaves in each callee-saved register at the ret: sp back up by the frame, the others their atoms *)
Definition skX_expect (r : bv 5) : sv := if bv_unsigned r =? 2 then SOff 2 16 else SOff (Z.to_nat (bv_unsigned r)) 0.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair the kit's entry state needs (lib/B/FSH_Base.v FsShadowSyms: the GOT word 0x9fc10 and the cell
   0xa8438 of __asan_shadow_memory_dynamic_address) *)
Hypothesis HSS : FsShadowSyms B.
Let TL_got : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address := proj1 HSS.
Let TL_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address := proj2 HSS.

(* ================= helpers ================= *)
(* the stack's shadow reads 0 (lib/B/FSW_parse_string_defs.v pstr_cells8 / pstr_RA_stack) *)
Lemma skw_cells8 : forall lo hi x, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= x -> x + 8 <= hi ->
  lo mod 8 = 0 /\ (hi - lo) mod 8 = 0.
Proof.
intros lo hi x Hlo Hhi H1 H2.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as A. pose proof (Z.div_mod hi 4096 ltac:(lia)) as C.
rewrite Hlo, Z.add_0_r in A. rewrite Hhi, Z.add_0_r in C. split.
- rewrite A. replace (4096 * (lo / 4096)) with ((512 * (lo / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite A, C. replace (4096 * (hi / 4096) - 4096 * (lo / 4096)) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8)
    by lia. apply Z_mod_mult.
Qed.
Lemma skw_RA_stack : forall ly S (W : world tfibsegs) mem md x n,
  AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 -> 8 <= n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S W mem md x n HAR Hlo Hhi Hx8 Hn8 Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity))
  as Hz. cbn [fst snd] in Hz.
destruct (skw_cells8 _ _ x Hpal Hpah ltac:(lia) ltac:(lia)) as [Hm1 Hm2].
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hm1 | exact Hm2 | exact Hz] | lia | lia].
Qed.
Lemma skw_RA_stk_mem : forall ly S U (W : world tfibsegs) mem md x n,
  ARU tfibsegs B ly S U W mem md -> alloc_ceiling <= ly_stk_lo ly -> ly_stk_hi ly <= 2 ^ 47 ->
  ly_stk_lo ly <= x -> x + n <= ly_stk_hi ly -> x mod 8 = 0 -> n mod 8 = 0 -> 8 <= n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S U W mem md x n HARU Hceil H47 Hlo Hhi Hx8 Hn8 Hn.
pose proof HARU as (HAR & _ & _).
apply (proj1 (fsw_ARU_stack_ra tfibsegs B (AR_laws_ok tfibsegs B) ly S U W mem md (w_H W) x n HARU Hlo ltac:(lia))).
exact (skw_RA_stack ly S W (unpoison U mem) md x n HAR Hlo Hhi Hx8 Hn8 Hn).
Qed.
(* no shadow byte of a live block's user bytes is user-poisoned (pstr_ush_blk / pstr_RA_unp / pstr_RA_blk_mem) *)
Lemma skw_ush_blk : forall ly S U (W : world tfibsegs) mem md b n x,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (b, n) (ablocks B ly S) -> b + 16 <= x -> x < b + req_size n -> in_ush U (SHADOW_OFF + x / 8) = false.
Proof.
intros ly S U W mem md b n x HARU FH Hin Hx1 Hx2.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof HARU as (HAR & (OK & _) & _).
destruct (in_ush U (SHADOW_OFF + x / 8)) eqn:E; [exfalso | reflexivity].
apply in_ush_spec in E as (r & Hr & Hlo & Hhi).
pose proof (proj1 (Forall_forall _ _) OK r Hr) as (Hal & _ & _ & _).
destruct (FH r Hr) as (Hsnd & m & Hinm & Hm16).
rewrite Hsnd in Hhi. unfold shadow_addr in Hlo, Hhi.
change (16 / 8) with 2 in Hhi.
assert (H16 : (fst r + 16) / 8 = fst r / 8 + 2)
  by (rewrite (Z.div_mod (fst r) 8 ltac:(lia)) at 1; rewrite Hal, Z.add_0_r;
      replace (8 * (fst r / 8) + 16) with (16 + (fst r / 8) * 8) by lia; rewrite Z.div_add by lia; lia).
destruct (Z.eq_dec (fst r) b) as [Heq | Hne].
- assert (Hge : (fst r + 16) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
- pose proof (req_size_pos m ltac:(destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (fst r) m HAR Hinm)
    as (_ & _ & _ & _ & _ & _ & Hm); lia)) as (_ & Hmle).
  pose proof (sep_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (fst r) m b n HAR Hinm Hin
    ltac:(intros Hq; apply Hne; exact (f_equal fst Hq))) as Hdis.
  unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
  destruct Hdis as [Hd | Hd].
  + assert (Hge : (fst r + 16) / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
  + assert (Hlt : x / 8 < fst r / 8).
    { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as D.
      rewrite Hal, Z.add_0_r in D. lia. }
    lia.
Qed.
Lemma skw_RA_unp : forall U (W : world tfibsegs) mem x n,
  0 <= x -> x + n < 2 ^ 64 ->
  (forall a, x <= a < x + n -> in_ush U (SHADOW_OFF + a / 8) = false) ->
  range_addressable (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF x n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros U W mem x n Hx Hn Hush HRA.
apply (range_addressable_agree (aview tfibsegs (w_H W) (unpoison U mem)) (aview tfibsegs (w_H W) mem)
  SHADOW_OFF x n); [|exact HRA].
intros a Ha. unfold shadow_of_addr. symmetry. apply aview_unpoison_out.
rewrite (wz (SHADOW_OFF + a / 8)); [apply Hush; exact Ha|].
pose proof (Z.div_pos a 8 ltac:(lia)). pose proof (Z.div_lt_upper_bound a 8 (2 ^ 64) ltac:(lia) ltac:(lia)).
unfold SHADOW_OFF. lia.
Qed.
Lemma skw_RA_blk_mem : forall ly S U (W : world tfibsegs) mem md b k x n,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (b, k) (ablocks B ly S) -> b + 16 <= x -> 0 <= n -> x + n <= b + req_size k ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Proof.
intros ly S U W mem md b k x n HARU FH Hin Hx1 Hn0 Hx2.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof HARU as (HAR & _ & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b k HAR Hin) as (_ & Hb4096 & Hceil & _).
pose proof asan_consts as (C1 & _).
destruct (Z.le_gt_cases n 0) as [Hle | Hgt]; [apply range_addressable_nil; lia|].
apply (skw_RA_unp U W mem x n ltac:(lia) ltac:(lia)).
- intros a Ha. exact (skw_ush_blk ly S U W mem md b k a HARU FH Hin ltac:(lia) ltac:(lia)).
- exact (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md b k x n HAR Hin ltac:(lia)
    ltac:(lia)).
Qed.
(* the bytes of the text, as the walk reads them (pstr_text_byte) *)
Lemma skw_text_byte : forall (W : world tfibsegs) m q text len p d (tb : list byte) k (cb : byte),
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) m) q text len p d tb ->
  nth_error tb (Z.to_nat k) = Some cb -> 0 <= k ->
  mbyte tfibsegs (mrestrict (w_H W) m) (text + k) = Some cb.
Proof.
intros W m q text len p d tb k cb HIN Hnth Hk.
assert (Hlt : (Z.to_nat k < length tb)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate).
destruct HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbt & _).
destruct Hbt as (_ & _ & Hb). specialize (Hb (Z.to_nat k) Hlt).
rewrite Z2Nat.id in Hb by exact Hk. rewrite Hnth in Hb. exact Hb.
Qed.
(* memory readers kept across a change that misses the address (ps2_mbyte_eq / ps2_wr_eq / pstr_val_mem_eq_at /
   ps2_bytes_at_eq) *)
Lemma skw_mbyte_eq : forall (H : word -> bool) m m' x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  mbyte tfibsegs (mrestrict H m') x = mbyte tfibsegs (mrestrict H m) x.
Proof. intros H m m' x E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma skw_wr_eq : forall (H : word -> bool) m m' x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  (writable_at tfibsegs (mrestrict H m) x <-> writable_at tfibsegs (mrestrict H m') x).
Proof. intros H m m' x E. unfold writable_at, wview, mrestrict. rewrite E. reflexivity. Qed.
Lemma skw_val_mem_eq_at : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v He Hv k Hk. unfold mbyte, mrestrict. rewrite (He k Hk). exact (Hv k Hk). Qed.
Lemma skw_bytes_at_eq : forall (H : word -> bool) m m' a bs,
  (forall k, (k < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  Mem.bytes_at tfibsegs (mrestrict H m) a bs -> Mem.bytes_at tfibsegs (mrestrict H m') a bs.
Proof.
intros H m m' a bs E (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros k Hk.
rewrite <- (H2 k Hk). unfold Mem.mrd, Mem.wa, mrestrict. rewrite (E k Hk). reflexivity.
Qed.
(* a run's write windows: everything outside them is the memory before the run (pstr_frame_none_l) *)
Lemma skw_frame_out : forall E rs (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs m m' ->
  (forall r, In r rs -> forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a <
     base_val E (YP09.r_base r) + YP09.r_whi r -> P a) ->
  forall x : word, ~ P (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' P HF HP x Hx. apply HF. intros (r & Hin & Hr). apply Hx. exact (HP r Hin _ Hr). Qed.
(* reading the symbolic state (ps2_ewR / ps2_reg_val / ps2_denot_off / ps2_denot_lit / ps2_nz / pstr_shx /
   ps2_chunk1_ok / pstr_reg_keep) *)
Lemma skw_ewR : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof.
intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. unfold w64.
apply unsigned_lit_small; exact Hv.
Qed.
Lemma skw_reg_val : forall (H : word -> bool) E ss ms (r : bv 5) e v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w64 v ->
  YK11.getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r e v HS Hr He. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. exact He. Qed.
Lemma skw_denot_off : forall E n z v w, bv_unsigned (ew E n) = v -> w = v + z -> 0 <= w < 2 ^ 64 ->
  sv_denot E (SOff n z) = w64 w.
Proof.
intros E n z v w Hn Hw Hz. subst w. unfold w64. apply bv_eq. rewrite denot_SOff, Hn, unsigned_lit_small by exact Hz.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma skw_denot_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = w64 z.
Proof.
intros E z Hz. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)).
rewrite U_lit by exact Hz. rewrite unsigned_lit_small by exact Hz. reflexivity.
Qed.
Lemma skw_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H Hc. subst r. apply H. reflexivity. Qed.
Lemma skw_shx_denot : forall E n b x sb, bv_unsigned (ew E n) = x -> bv_unsigned (ew E b) = sb ->
  0 <= x < 2 ^ 64 -> 0 <= sb < 2 ^ 32 -> sv_denot E (skw_shx n b) = w64 (sb + x / 8).
Proof.
intros E n b x sb Hn Hb Hx Hsb. unfold skw_shx, w64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hn, Hb, !Z.add_0_r.
replace (Z.land (zcanon 3) 63) with 3 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id (x / 8)) by (unfold M64; lia).
rewrite (zcanon_id sb) by (unfold M64; lia). rewrite Z.add_comm. apply zcanon_id. unfold M64. lia.
Qed.
(* the walk's arithmetic: the four engine range bounds and the block head, then lia *)
Ltac skw_lia :=
  try unfold RQLO in *; try unfold RQHI in *; try unfold RTLO in *; try unfold RTHI in *;
  try unfold SHADOW_OFF in *; try unfold HEAD in *; lia.
(* a callee-saved register's index, computed (lib/B FSW_indent.v's ics) *)
Ltac skw_ics := unfold acallee_saved;
  repeat (lazymatch goal with |- context [bv_unsigned ?z] =>
    let v := eval vm_compute in (bv_unsigned z) in change (bv_unsigned z) with v end); lia.
(* the write windows of a run, by a boolean check on its region list (lib/B/FSW_parse_string_s2.v ps2_wins_b /
   ps2_frame_wins / ps2_awr_wins) *)
Definition skw_wins_b (ws : list (nat * Z * Z)) (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  existsb (fun w => obase_eqb (YP09.r_base r) (Some (fst (fst w))) && (YP09.r_wlo r =? snd (fst w)) &&
                    (YP09.r_whi r =? snd w)) ws.
Lemma skw_frame_wins : forall E rs m m' (ws : list (nat * Z * Z)),
  frame_of E rs m m' -> forallb (skw_wins_b ws) rs = true ->
  forall x : word, Forall (fun w => ~ (bv_unsigned (ew E (fst (fst w))) + snd (fst w) <= bv_unsigned x <
                                       bv_unsigned (ew E (fst (fst w))) + snd w)) ws -> m' x = m x.
Proof.
intros E rs m m' ws HF Hb x Hx. apply HF. intros (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as Hc. unfold skw_wins_b in Hc.
apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
apply existsb_exists in Hc as (w & Hw & Hc).
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hbase Hlo]. apply Z.eqb_eq in Hlo, Hhi.
pose proof (proj1 (Forall_forall _ _) Hx w Hw) as Hn. cbv beta in Hn.
destruct (YP09.r_base r) as [k|]; [|discriminate]. cbn [obase_eqb] in Hbase. apply Nat.eqb_eq in Hbase. subst k.
cbn [base_val] in Ha. apply Hn. lia.
Qed.
(* the size a block of n bytes reserves (lib/B/FSW_parse_string_defs.v ps2_req) *)
Lemma skw_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
(* read an atom through the token extension of a run's env (lib/B/FSW_parse_string_s2.v ps2_ews) *)
Lemma skw_awr_wins : forall E rs ws STK sp0 FP bl0 blc lyc own fr0,
  forallb (skw_wins_b ws) rs = true ->
  Forall (fun w => forall x, bv_unsigned (ew E (fst (fst w))) + snd (fst w) <= x <
    bv_unsigned (ew E (fst (fst w))) + snd w -> awr_byte tfibsegs B STK sp0 FP bl0 blc lyc own fr0 x) ws ->
  awr_ok tfibsegs B E rs STK sp0 FP bl0 blc lyc own fr0.
Proof.
intros E rs ws STK sp0 FP bl0 blc lyc own fr0 Hb Hw x (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as Hc. unfold skw_wins_b in Hc.
apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
apply existsb_exists in Hc as (w & Hwin & Hc).
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hbase Hlo]. apply Z.eqb_eq in Hlo, Hhi.
pose proof (proj1 (Forall_forall _ _) Hw w Hwin) as Hx. cbv beta in Hx.
destruct (YP09.r_base r) as [k|]; [|discriminate]. cbn [obase_eqb] in Hbase. apply Nat.eqb_eq in Hbase. subst k.
cbn [base_val] in Ha. apply Hx. lia.
Qed.
Ltac skw_ews := repeat (rewrite ew_ewset_other by lia).
Ltac skw_ews_in H := repeat (rewrite ew_ewset_other in H by lia).
Lemma skw_chunk1_ok : forall E m base off e (c : byte), sv_denot E e = w64 (bv_unsigned c) ->
  mbyte tfibsegs m (base + off) = Some c -> YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 e)).
Proof.
intros E m base off e c He Hm i Hi. cbn [YP09.c_len YP09.c_val cv_len] in Hi.
assert (i = 0) by (change (Z.of_N 1) with 1 in Hi; lia). subst i. exists c. cbn [cbyte YP09.c_val YP09.c_off].
rewrite He. unfold byte_of_word, w64. rewrite Z.mul_0_r, Z.shiftr_0_r.
pose proof (YK11.u8_range c). rewrite unsigned_lit_small by lia. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. rewrite Z.add_0_r. exact Hm.
Qed.
Lemma skw_reg_keep : forall (H : word -> bool) E ss ms (r : bv 5) (n : nat) regsL extra,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = ew (Ereg regsL extra) n ->
  Z.of_nat n = bv_unsigned r -> YK11.getr (ms_regs ms) r = YK11.getr regsL r.
Proof.
intros H E ss ms r n regsL extra HS Hr Hn Hnr.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr, fsw_SOff0, Hn.
exact (ew_Ereg_nat regsL extra n r Hnr).
Qed.

(* ---- the white-space mask IS PjGrammar.ws (image A's pi_ws_gt32 / pi_wsmask; the old-form walk's mask_ws) ---- *)
Lemma skw_ws_gt32 : forall c, 32 < c -> PjGrammar.ws c = false.
Proof.
intros c H. unfold PjGrammar.ws.
assert (E1 : (c =? 32) = false) by (apply Z.eqb_neq; lia).
assert (E2 : (c =? 9) = false) by (apply Z.eqb_neq; lia).
assert (E3 : (c =? 10) = false) by (apply Z.eqb_neq; lia).
assert (E4 : (c =? 13) = false) by (apply Z.eqb_neq; lia).
rewrite E1, E2, E3, E4. reflexivity.
Qed.
Lemma skw_wsmask : forall c, 0 <= c <= 32 ->
  Z.land (Z.shiftr 4294977024 c) 1 = (if PjGrammar.ws c then 1 else 0).
Proof.
intros c Hc.
assert (E : forallb (fun k => Z.eqb (Z.land (Z.shiftr 4294977024 k) 1) (if PjGrammar.ws k then 1 else 0))
              (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
assert (HIn : In c (map Z.of_nat (seq 0 33)))
  by (apply in_map_iff; exists (Z.to_nat c); split; [lia|]; apply in_seq; lia).
apply Z.eqb_eq. exact (proj1 (forallb_forall _ _) E c HIn).
Qed.
(* the machine's mask bit at the loop's second test, for a byte at most 32 *)
Lemma skw_bit_val : forall E c, bv_unsigned (ew E 32) = c -> 0 <= c <= 32 ->
  U E skL_wsbit = (if PjGrammar.ws c then 1 else 0).
Proof.
intros E c H32 Hc. unfold skL_wsbit.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, !U_SLit, H32, Z.add_0_r.
replace (Z.land (zcanon c) 63) with c.
2:{ rewrite (zcanon_id c) by (unfold M64; lia). change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia. reflexivity. }
rewrite (zcanon_id 4294977024) by (unfold M64; lia).
assert (Hsr : 0 <= Z.shiftr 4294977024 c <= 4294977024).
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
  assert (Hp : 0 < 2 ^ c) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm : 1 * 4294977024 <= 2 ^ c * 4294977024) by (apply Z.mul_le_mono_nonneg_r; lia).
  rewrite Z.mul_1_l in Hm.
  pose proof (Z.div_le_upper_bound 4294977024 (2 ^ c) 4294977024 Hp Hm).
  lia. }
rewrite (zcanon_id (Z.shiftr 4294977024 c)) by (unfold M64; lia).
rewrite (zcanon_id 1) by (unfold M64; lia).
rewrite (skw_wsmask c Hc). destruct (PjGrammar.ws c); apply zcanon_id; unfold M64; lia.
Qed.

(* ================= the walk, with skip_ws_spec's data fixed ================= *)
Section L.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (q ot text len p d : Z) (tb : list byte)
  (tcap : Z) (wsl rest : list Z) (live peak cnt fail : Z).
Hypothesis HPRE : fpreU tfibsegs B STK_skip_ws ly S U W regs mem md ch.
Hypothesis HHD : FSupoisonU.fs_heads B ly S U.
Hypothesis H10 : YK11.getr regs 10 = w64 q.
Hypothesis HIN : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb.
Hypothesis HWIN : rd_win tfibsegs regs ly W mem q ot.
Hypothesis HTX : rd_text tfibsegs B ly S W mem text len tcap.
Hypothesis HREST : ReaderRes.rest_at tb text p = wsl ++ rest.
Hypothesis HWS : Forall (fun c => PjGrammar.ws c = true) wsl.
Hypothesis HNW : forall c r, rest = c :: r -> PjGrammar.ws c = false.
Hypothesis HGL : fs_glob tfibsegs W mem live peak cnt fail.

Definition skw_n : Z := Z.of_nat (length wsl).
Definition skw_all : list Z := wsl ++ rest.
Definition skw_STKw : Z := STK_skip_ws + (ot - spZ regs).
Definition skw_Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
    PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + skw_n) d tb /\
    wkeep tfibsegs W W' mem mem' (spZ regs) ot q 8 /\
    ablocks B ly' S' = ablocks B ly S /\
    rd_text tfibsegs B ly' S' W' mem' text len tcap /\
    fs_glob tfibsegs W' mem' live peak cnt fail.
Definition skw_POST : world tfibsegs -> config -> Prop :=
  fpostU tfibsegs B skw_STKw ot [] regs ly S U W mem md 0 U skw_Q.
(* every byte outside the frame and the in->p word is the entry's *)
Definition skw_keepM (m' : word -> option byte) : Prop :=
  forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> ~ (q <= bv_unsigned x < q + 8) -> m' x = mem x.

(* ---- the numeric facts of the premises ---- *)
Lemma skw_nums :
  spZ regs mod 16 = 0 /\ alloc_ceiling + 16 <= spZ regs /\ spZ regs <= 2 ^ 47 /\
  alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + 16 <= spZ regs /\ ly_stk_hi ly <= 2 ^ 47 /\
  ly_top ly <= ly_stk_hi ly /\
  spZ regs <= q /\ q + 24 <= ot /\ ot mod 16 = 0 /\ ot <= ly_top ly /\
  0 <= q /\ q mod 8 = 0 /\ 0 < text /\ text <= p <= text + len /\ text + len < 2 ^ 62 /\
  Z.of_nat (length tb) = len /\ 0 <= d <= 32 /\
  4096 + HEAD <= text /\ In (text - HEAD, tcap + HEAD) (ablocks B ly S) /\ 0 < tcap /\ len < tcap /\
  text + tcap <= alloc_ceiling /\ STK_skip_ws = 16 /\ FRAME_skip_ws = 16 /\
  140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (fsw_sp B STK_skip_ws ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hceil & H47 & HS0).
pose proof HPRE as (((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _ & _) & _).
pose proof Hstk as (_ & _ & Hclo & Hslo & Hshi & Hly47 & _ & Htop & Htop2).
pose proof HWIN as (Hq1 & Hq2 & Hotal & Hottop & Hotpres).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Bq0 & Bq1 & Bt0 & Bp & Btl & Bdis & Blen & Bqal & Bd).
pose proof HTX as (Htx1 & Hblk & Htx3).
pose proof Hblk as (Hin & Hal16t & Hpos & _).
assert (Hbb : text + tcap <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (text - HEAD) (tcap + HEAD) HAR Hin)
    as (_ & _ & Hceil2 & _).
  pose proof (req_size_pos (tcap + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrq).
  unfold HEAD in Hceil2, Hrq, Htx1. lia. }
assert (ESTK : STK_skip_ws = 16) by reflexivity.
assert (EFR : FRAME_skip_ws = 16) by reflexivity.
repeat split; try assumption; try lia.
Qed.

(* ---- the model side: the bytes at in->p are ws ++ rest ---- *)
Lemma skw_all_len : Z.of_nat (length skw_all) = text + len - p.
Proof.
pose proof skw_nums as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Bp & _ & Blen & _).
unfold skw_all. rewrite <- HREST. unfold ReaderRes.rest_at, ReaderRes.zb.
rewrite length_map, length_skipn. lia.
Qed.
Lemma skw_byte : forall i, 0 <= i < text + len - p ->
  exists cb : byte, bv_unsigned cb = nth (Z.to_nat i) skw_all 0 /\
    mbyte tfibsegs (mrestrict (w_H W) mem) (p + i) = Some cb.
Proof.
intros i Hi.
pose proof skw_nums as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Bp & _ & Blen & _).
assert (Hlen : (Z.to_nat i < length skw_all)%nat) by (pose proof skw_all_len; lia).
assert (Hne : nth_error (skipn (Z.to_nat (p - text)) tb) (Z.to_nat i) <> None).
{ apply nth_error_Some. rewrite length_skipn. unfold skw_all in Hlen. pose proof skw_all_len as HL.
  unfold skw_all in HL. lia. }
destruct (nth_error (skipn (Z.to_nat (p - text)) tb) (Z.to_nat i)) as [cb|] eqn:Esk; [|contradiction].
exists cb. split.
- assert (Hz : nth_error skw_all (Z.to_nat i) = Some (bv_unsigned cb)).
  { unfold skw_all. rewrite <- HREST. unfold ReaderRes.rest_at, ReaderRes.zb.
    rewrite nth_error_map, Esk. reflexivity. }
  symmetry. apply (nth_error_nth _ _ 0 Hz).
- rewrite nth_error_skipn in Esk.
  replace (p + i) with (text + (p - text + i)) by lia.
  apply (skw_text_byte W mem q text len p d tb (p - text + i) cb HIN); [|lia].
  replace (Z.to_nat (p - text + i)) with (Z.to_nat (p - text) + Z.to_nat i)%nat by lia. exact Esk.
Qed.
Lemma skw_n_le : 0 <= skw_n /\ p + skw_n <= text + len.
Proof.
pose proof skw_all_len as HL. unfold skw_all in HL. rewrite length_app in HL.
unfold skw_n. lia.
Qed.
Lemma skw_ws_lt : forall i, 0 <= i < skw_n -> PjGrammar.ws (nth (Z.to_nat i) skw_all 0) = true.
Proof.
intros i Hi. unfold skw_all. rewrite app_nth1 by (unfold skw_n in Hi; lia).
apply (proj1 (Forall_forall _ _) HWS). apply nth_In. unfold skw_n in Hi. lia.
Qed.
Lemma skw_ws_at_n : skw_n < text + len - p -> PjGrammar.ws (nth (Z.to_nat skw_n) skw_all 0) = false.
Proof.
intros Hlt. pose proof skw_all_len as HL. unfold skw_all in HL. rewrite length_app in HL.
assert (Hr : (0 < length rest)%nat) by (unfold skw_n in Hlt; lia).
unfold skw_all. rewrite app_nth2 by (unfold skw_n; lia).
replace (Z.to_nat skw_n - length wsl)%nat with 0%nat by (unfold skw_n; lia).
destruct rest as [|c0 r0]; [cbn in Hr; lia|]. cbn [nth]. exact (HNW c0 r0 eq_refl).
Qed.

(* a callee-saved register the walk never wrote, read at the ret *)
Lemma skw_cs_atom : forall regsX (r : bv 5) (n : nat),
  YK11.getr regsX r = YK11.getr regs r -> Z.of_nat n = bv_unsigned r ->
  sv_denot (Ereg regsX (@nil word)) (SOff n 0) = YK11.getr regs r.
Proof. intros regsX r n Hr Hn. rewrite fsw_SOff0, (ew_Ereg_nat regsX [] n r Hn). exact Hr. Qed.

(* ---- the epilogue 0x83654 -> the ret: fpostU ---- *)
Lemma skw_exit : forall regsX memX mdX,
  spZ regsX = spZ regs - 16 ->
  YK11.getr regsX 1 = YK11.getr regs 1 ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> YK11.getr regsX r = YK11.getr regs r) ->
  val_mem tfibsegs (mrestrict (w_H W) memX) (spZ regs - 8) 8 (bv_unsigned (YK11.getr regs 1)) ->
  val_mem tfibsegs (mrestrict (w_H W) memX) q 8 (p + skw_n) ->
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) memX) (q + o)) ->
  skw_keepM memX ->
  ajournal tfibsegs B skw_STKw ot [] ly S W (unpoison U mem) md [] ly S W (unpoison U memX) mdX 0 ->
  ARU tfibsegs B ly S U W memX mdX ->
  SRr tfibsegs W (mkCfg (YK11.mkst regsX (Z_to_bv 64 SKW_EXIT) memX (YK11.seg_rom tfibsegs)) mdX) skw_POST.
Proof.
intros regsX memX mdX Hsp HraX Hcs Hfr Hvp Hwq HM HJ HARU.
pose proof skw_nums as (Hal16 & Hceil & H47 & Hslo & Hslo2 & Hshi & Htop2 & Hq1 & Hq2 & Hotal & Hottop &
  Bq0 & Bqal & Bt0 & Bp & Btl & Blen & Bd & Htx1 & Hin & Htc & Hlen2 & Hbb & ESTK & EFR & C1 & C3).
pose proof HPRE as (((HAR0 & Hra & _) & _ & _) & _).
pose proof skw_n_le as (Hn0 & Hnle).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (E2 : bv_unsigned (ew (Ereg regsX (@nil word)) 2) = spZ regs - 16)
  by (rewrite (ew_Ereg_nat regsX [] 2 2%bv eq_refl); exact Hsp).
assert (E1 : ew (Ereg regsX (@nil word)) 1 = YK11.getr regs 1)
  by (rewrite (ew_Ereg_nat regsX [] 1 1%bv eq_refl); exact HraX).
assert (HS : st_ok tfibsegs (Ereg regsX (@nil word)) skX_ss
  (restrict (w_H W) (YK11.mkst regsX (Z_to_bv 64 SKW_EXIT) memX (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold skX_ss. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ (spZ regs - 16) 8 8 (SOff 1 0) (bv_unsigned (YK11.getr regs 1)));
      [rewrite fsw_SOff0, E1; symmetry; apply Z_to_bv_bv_unsigned
      | cbn [Z.of_N]; apply u64_range | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia;
        exact Hfr].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2. change (2 ^ 4) with 16. split; [|exact I].
    split; [lia|]. split; [|lia].
    replace (spZ regs - 16) with (spZ regs + (-1) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
assert (SHOK : sh_ok tfibsegs fs_Bx (@nil shent) (Ereg regsX (@nil word)) (mrestrict (w_H W) memX))
  by apply Forall_nil.
fsw_aj_run_to_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan SKW_RET.
{ unfold skX_ss. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
(* the epilogue writes nothing *)
assert (Hmf : forall y : word, ms_mem ms y = memX y).
{ intros y. refine (skw_frame_out _ _ _ _ (fun _ => False) HF _ y (fun H => H)).
  intros r Hin0 a Ha. unfold skX_ss in Hin0. cbn [ss_mem In] in Hin0. destruct Hin0 as [<-|[]].
  cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
assert (HMX : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
  ~ (q <= bv_unsigned x < q + 8) -> ms_mem ms x = mem x) by (intros x A1 A2; rewrite (Hmf x); exact (HM x A1 A2)).
unfold skw_POST.
refine (fsw_retU B skip_ws_tbl skip_ws_tbl_ok W (Ereg regsX (@nil word)) _ ms _ skw_STKw ot [] regs ly S U W mem md
  ly S U 0 skw_Q HS eq_refl ltac:(vm_compute; reflexivity) _ HJ HARU _ _).
- rewrite (st_ok_restrict_reg tfibsegs _ _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?l 1%bv] => replace (sr_get l 1%bv) with (SOff 1 0) by (vm_compute; reflexivity) end.
  rewrite fsw_SOff0, E1. exact Hra.
- apply (fsw_preserved _ _ _ ms regs skX_expect HS); [vm_compute; reflexivity|].
  intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
  all: lazymatch goal with |- sv_denot _ (skX_expect ?r) = _ =>
    let e := eval vm_compute in (skX_expect r) in change (skX_expect r) with e end.
  all: first
    [ apply (fsw_sp_back regsX [] regs 16); exact E2
    | eapply skw_cs_atom; [apply Hcs; skw_ics | vm_compute; reflexivity] ].
- (* the post's own facts *)
  intros matX. unfold skw_Q.
  assert (HKEEP : forall y, 0 <= y < 2 ^ 64 -> ~ (spZ regs - 16 <= y < spZ regs) -> ~ (q <= y < q + 8) ->
    ms_mem ms (Z_to_bv 64 y) = mem (Z_to_bv 64 y))
    by (intros y Hy A1 A2; apply HMX; rewrite wz by lia; lia).
  assert (Hvp' : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) q 8 (p + skw_n))
    by (apply (skw_val_mem_eq_at _ memX (ms_mem ms)); [intros k Hk; apply Hmf | exact Hvp]).
  split.
  { (* pj_in_ok *)
    destruct HIN as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
    refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 I12))))))))))).
    - apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact Hvp' | lia | lia | lia].
    - apply (skw_bytes_at_eq _ mem (ms_mem ms)); [|exact I2].
      intros k Hk. rewrite Mem.length_le8 in Hk. apply HKEEP; lia.
    - apply (skw_bytes_at_eq _ mem (ms_mem ms)); [|exact I3].
      intros k Hk. rewrite Mem.length_le4 in Hk. apply HKEEP; lia.
    - destruct I4 as (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros o Ho.
      destruct (Z_lt_le_dec o 8) as [Ho8|Ho8].
      + apply (proj1 (skw_wr_eq (w_H W) memX (ms_mem ms) (q + o) (Hmf _))). exact (Hwq o ltac:(lia)).
      + apply (proj1 (skw_wr_eq (w_H W) mem (ms_mem ms) (q + o) (HKEEP (q + o) ltac:(lia) ltac:(lia) ltac:(lia)))).
        exact (W3 o Ho).
    - lia.
    - apply (skw_bytes_at_eq _ mem (ms_mem ms)); [|exact I10]. intros k Hk. apply HKEEP; lia. }
  split.
  { (* wkeep *)
    intros a Ha Hnq. pose proof (HKEEP a ltac:(lia) ltac:(lia) ltac:(lia)) as Ea.
    split; [exact (skw_mbyte_eq (w_H W) mem (ms_mem ms) a Ea) | exact (skw_wr_eq (w_H W) mem (ms_mem ms) a Ea)]. }
  split; [reflexivity|].
  split.
  { (* rd_text *)
    destruct HTX as (T0 & (T1 & T2 & T3 & T4) & T5). split; [exact T0|]. split; [|exact T5].
    split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
    apply (skw_val_mem_eq_at _ mem (ms_mem ms)); [|exact T4]. intros k Hk. apply HKEEP; unfold HEAD in *; lia. }
  (* fs_glob: alloc.c's four statics are image bytes, far below the stack *)
  destruct HGL as (G1 & G2 & G3 & G4 & GR).
  assert (GK : forall g v, 0 <= g -> g + 8 <= 0x5fd000 ->
    val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) g 8 v).
  { intros g v Hg1 Hg2 Hv. apply (skw_val_mem_eq_at _ mem (ms_mem ms)); [|exact Hv].
    intros k Hk. apply HKEEP; lia. }
  cbv [fs_glob fs_glob_at].
  split; [apply GK; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1]|].
  split; [apply GK; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2]|].
  split; [apply GK; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3]|].
  split; [apply GK; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4]|].
  exact GR.
Qed.

(* ---- the loop head 0x835fc, as machine facts at the cursor p + i ---- *)
Definition skL_at (i : Z) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) : Prop :=
  spZ regsL = spZ regs - 16 /\
  YK11.getr regsL 1 = YK11.getr regs 1 /\
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> YK11.getr regsL r = YK11.getr regs r) /\
  YK11.getr regsL 5 = w64 1 /\ YK11.getr regsL 10 = w64 q /\ YK11.getr regsL 11 = w64 (p + i) /\
  YK11.getr regsL 12 = w64 SHADOW_OFF /\ YK11.getr regsL 13 = w64 (SHADOW_OFF + q / 8) /\
  YK11.getr regsL 14 = w64 (text + len) /\ YK11.getr regsL 15 = w64 (p + i) /\
  YK11.getr regsL 16 = w64 32 /\ YK11.getr regsL 17 = w64 4294977024 /\
  val_mem tfibsegs (mrestrict (w_H W) memL) (spZ regs - 8) 8 (bv_unsigned (YK11.getr regs 1)) /\
  val_mem tfibsegs (mrestrict (w_H W) memL) q 8 (p + i) /\
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) memL) (q + o)) /\
  skw_keepM memL /\
  ajournal tfibsegs B skw_STKw ot [] ly S W (unpoison U mem) md [] ly S W (unpoison U memL) mdL 0 /\
  ARU tfibsegs B ly S U W memL mdL.

(* struct pj_in's in->p word, read out of the loop state's q region *)
Lemma skw_qreg : forall E m (z v : Z),
  region_ok tfibsegs E m (YP09.mkRegion (Some 10%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 15 z))]) ->
  bv_unsigned (ew E 10) = q -> bv_unsigned (ew E 15) = v -> 0 <= v + z < 2 ^ 64 ->
  val_mem tfibsegs m q 8 (v + z) /\ (forall o, 0 <= o < 8 -> writable_at tfibsegs m (q + o)).
Proof.
intros E m z v HR H10e H15e Hv. split.
- pose proof (fsw_field E m 10%nat q [YP09.mkChunk 0 (CVal 8 (SOff 15 z))] 0 8 0 8 0 8%N (SOff 15 z) (v + z)
    HR H10e ltac:(left; reflexivity)
    ltac:(exact (skw_denot_off E 15 z v (v + z) H15e eq_refl Hv))
    ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as HV.
  rewrite Z.add_0_r in HV. exact HV.
- intros o Ho. destruct HR as (_ & _ & HW & _).
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in HW. rewrite H10e in HW. exact (HW o Ho).
Qed.
(* the callee-saved registers a run left as their atoms *)
Lemma skw_pres_from : forall (E : env) ss ms regsL extra,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  (forall n : nat, (n < 33)%nat -> ew E n = ew (Ereg regsL extra) n) ->
  aregs_preserved regsL (ms_regs ms).
Proof.
intros E ss ms regsL extra HS Hall Hag.
apply (fsw_preserved _ E ss ms regsL (fun r => SOff (Z.to_nat (bv_unsigned r)) 0) HS Hall).
intros r Hr. pose proof (u5_range r) as Hr5.
rewrite fsw_SOff0, (Hag (Z.to_nat (bv_unsigned r)) ltac:(lia)).
apply (ew_Ereg_nat regsL extra _ r). lia.
Qed.
(* the callee-saved registers but sp a run left as their atoms (the entry's exit, where sp is still down) *)
Definition CS_NOSP : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma skw_in_cs : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 -> In r CS_NOSP.
Proof.
intros r Hr Hr2. unfold acallee_saved in Hr.
assert (Hz : bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
  bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/
  bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
cbv [CS_NOSP In].
repeat match goal with H : _ \/ _ |- _ => destruct H as [Hv|Hv] end;
  repeat (first [ left; apply bv_eq; rewrite Hv; vm_compute; reflexivity | right ]).
Qed.
Lemma skw_cs_keep : forall (E : env) ss ms regs0 extra,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CS_NOSP = true ->
  (forall n : nat, (n < 33)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 2 ->
  YK11.getr (ms_regs ms) r = YK11.getr regs0 r.
Proof.
intros E ss ms regs0 extra HS Hall Hag r Hr Hr2. pose proof (u5_range r) as Hr5.
pose proof (proj1 (forallb_forall _ _) Hall r (skw_in_cs r Hr Hr2)) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS), Hq, fsw_SOff0,
  (Hag (Z.to_nat (bv_unsigned r)) ltac:(lia)).
apply (ew_Ereg_nat regs0 extra _ r). lia.
Qed.

(* the symbolic state of the loop head, from the machine facts at the cursor p + i *)
Lemma skL_ss_ok : forall i regsL memL mdL (cb : byte),
  0 <= i -> p + i < text + len ->
  skL_at i regsL memL mdL ->
  mbyte tfibsegs (mrestrict (w_H W) memL) (p + i) = Some cb ->
  st_ok tfibsegs (Ereg regsL [w64 (bv_unsigned cb)]) skL_ss
    (restrict (w_H W) (YK11.mkst regsL (Z_to_bv 64 SKW_LOOP) memL (YK11.seg_rom tfibsegs))).
Proof.
intros i regsL memL mdL cb Hi0 Hlt HL Hmb.
pose proof skw_nums as (Hal16 & Hceil & H47 & Hslo & Hslo2 & Hshi & Htop2 & Hq1 & Hq2 & Hotal & Hottop &
  Bq0 & Bqal & Bt0 & Bp & Btl & Blen & Bd & Htx1 & Hin & Htc & Hlen2 & Hbb & ESTK & EFR & C1 & C3).
destruct HL as (Lsp & Lra & Lcs & L5 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & LFR & LVP & LWQ & LM & HJ &
  HARU).
pose proof (YK11.u8_range cb) as Hc8.
assert (G10 : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 10) = q)
  by (apply (skw_ewR _ _ 10 10%bv); [reflexivity | exact L10 | lia]).
assert (G12 : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 12) = SHADOW_OFF)
  by (apply (skw_ewR _ _ 12 12%bv); [reflexivity | exact L12 | unfold SHADOW_OFF; lia]).
assert (G14 : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 14) = text + len)
  by (apply (skw_ewR _ _ 14 14%bv); [reflexivity | exact L14 | lia]).
assert (G15 : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 15) = p + i)
  by (apply (skw_ewR _ _ 15 15%bv); [reflexivity | exact L15 | lia]).
assert (G32 : ew (Ereg regsL [w64 (bv_unsigned cb)]) 32 = w64 (bv_unsigned cb)) by reflexivity.
assert (G32u : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 32) = bv_unsigned cb)
  by (rewrite G32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold skL_ss. apply (entry_st_ok_full tfibsegs).
- unfold skL_regs.
  apply regs_ok_pin; [| apply skw_nz; vm_compute; intros Hz; discriminate Hz
    | rewrite (skw_denot_off _ 15 0 (p + i) (p + i) G15 ltac:(lia) ltac:(lia)); exact L11].
  apply regs_ok_pin; [| apply skw_nz; vm_compute; intros Hz; discriminate Hz
    | rewrite (skw_shx_denot _ 10 12 q SHADOW_OFF G10 G12 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)); exact L13].
  apply regs_ok_pin; [| apply skw_nz; vm_compute; intros Hz; discriminate Hz
    | rewrite skw_denot_lit by lia; exact L16].
  apply regs_ok_pin; [| apply skw_nz; vm_compute; intros Hz; discriminate Hz
    | rewrite skw_denot_lit by lia; exact L17].
  apply regs_ok_pin; [| apply skw_nz; vm_compute; intros Hz; discriminate Hz
    | rewrite skw_denot_lit by lia; exact L5].
  apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold skL_regions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite G15. split; [unfold RTLO, RTHI in *; lia|]. split; [unfold RTLO, RTHI in *; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (skw_chunk1_ok _ _ _ _ _ cb); [rewrite fsw_SOff0, G32; reflexivity|].
    rewrite Z.add_0_r. exact Hmb.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite G10. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (LWQ o ltac:(lia))|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ q 0 8 (SOff 15 0) (p + i));
      [ rewrite (skw_denot_off _ 15 0 (p + i) (p + i) G15 ltac:(lia) ltac:(lia)); reflexivity
      | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact LVP].
- unfold skL_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite G10, G15.
  repeat split; first [exact I | skw_lia].
- split; [|split; exact I]. unfold skL_facts. cbn [f_atoms atoms_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite G10, G12, G14, G15, G32u.
  repeat split;
    first [ change (2 ^ 3) with 8; exact Bqal
          | rewrite Z.pow_0_r; apply Z.mod_1_r
          | skw_lia ].
Qed.

(* ---- the two steps every arm of the loop repeats: the memory kept outside the in->p word, and the epilogue ---- *)
Tactic Notation "skw_km" constr(HFh) constr(KMp) constr(mL) constr(HG10) ident(KMn) :=
  lazymatch type of HFh with
  | frame_of _ _ _ ?mB =>
      assert (KMn : forall x : word, ~ (q <= bv_unsigned x < q + 8) -> mB x = mL x);
      [ let xx := fresh "xx" in let Hxx := fresh "Hxx" in
        intros xx Hxx; rewrite <- (KMp xx Hxx);
        refine (skw_frame_wins _ _ _ _ [(10%nat, 0, 8)] HFh ltac:(vm_compute; reflexivity) xx _);
        constructor; [|constructor]; cbn [fst snd]; skw_ews; rewrite HG10; lia
      | idtac ]
  end.
Tactic Notation "skw_km0" constr(HFh) constr(mL) constr(HG10) ident(KMn) :=
  lazymatch type of HFh with
  | frame_of _ _ _ ?mB =>
      assert (KMn : forall x : word, ~ (q <= bv_unsigned x < q + 8) -> mB x = mL x);
      [ let xx := fresh "xx" in let Hxx := fresh "Hxx" in
        intros xx Hxx;
        refine (skw_frame_wins _ _ _ _ [(10%nat, 0, 8)] HFh ltac:(vm_compute; reflexivity) xx _);
        constructor; [|constructor]; cbn [fst snd]; skw_ews; rewrite HG10; lia
      | idtac ]
  end.
(* the epilogue reached from a loop state, with the cursor's word already in in->p *)
Lemma skw_exit_pack : forall i regsL memL mdL regsX memX mdX (v : Z),
  skL_at i regsL memL mdL ->
  aregs_preserved regsL regsX -> YK11.getr regsX 1 = YK11.getr regsL 1 ->
  (forall x : word, ~ (q <= bv_unsigned x < q + 8) -> memX x = memL x) ->
  val_mem tfibsegs (mrestrict (w_H W) memX) q 8 v -> v = p + skw_n ->
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) memX) (q + o)) ->
  ajournal tfibsegs B skw_STKw ot [] ly S W (unpoison U mem) md [] ly S W (unpoison U memX) mdX 0 ->
  ARU tfibsegs B ly S U W memX mdX ->
  SRr tfibsegs W (mkCfg (YK11.mkst regsX (Z_to_bv 64 SKW_EXIT) memX (YK11.seg_rom tfibsegs)) mdX) skw_POST.
Proof.
intros i regsL memL mdL regsX memX mdX v HL XP Hra1 KM HV Hv HWQ HJX HARUX.
pose proof skw_nums as (Hal16 & Hceil & H47 & Hslo & Hslo2 & Hshi & Htop2 & Hq1 & Hq2 & Hotal & Hottop &
  Bq0 & Bqal & Bt0 & Bp & Btl & Blen & Bd & Htx1 & Hin & Htc & Hlen2 & Hbb & ESTK & EFR & C1 & C3).
destruct HL as (Lsp & Lra & Lcs & L5 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & LFR & LVP & LWQ & LM & _ & _).
apply skw_exit.
- unfold spZ. rewrite (fsw_pres regsL regsX 2%bv XP ltac:(skw_ics)). exact Lsp.
- rewrite Hra1. exact Lra.
- intros rr Hrr Hrr2. rewrite (fsw_pres regsL regsX rr XP Hrr). exact (Lcs rr Hrr Hrr2).
- apply (skw_val_mem_eq_at _ memL memX);
    [intros kk Hkk; apply KM; rewrite wz by lia; lia | exact LFR].
- rewrite <- Hv. exact HV.
- exact HWQ.
- intros xx A1 A2. rewrite (KM xx A2). exact (LM xx A1 A2).
- exact HJX.
- exact HARUX.
Qed.

(* ---- the loop 0x835fc: induction on the white-space run still to come ---- *)
Lemma skw_loop : forall (k : nat) (i : Z) regsL memL mdL,
  Z.to_nat (skw_n - i) = k -> 0 <= i <= skw_n -> p + i < text + len ->
  skL_at i regsL memL mdL ->
  SRr tfibsegs W (mkCfg (YK11.mkst regsL (Z_to_bv 64 SKW_LOOP) memL (YK11.seg_rom tfibsegs)) mdL) skw_POST.
Proof.
intros k. induction k as [k IH] using lt_wf_ind.
intros i regsL memL mdL Hk Hi Hlt HL.
pose proof skw_nums as (Hal16 & Hceil & H47 & Hslo & Hslo2 & Hshi & Htop2 & Hq1 & Hq2 & Hotal & Hottop &
  Bq0 & Bqal & Bt0 & Bp & Btl & Blen & Bd & Htx1 & Hin & Htc & Hlen2 & Hbb & ESTK & EFR & C1 & C3).
pose proof skw_n_le as (Hn0 & Hnle).
pose proof HL as HL0.
destruct HL as (Lsp & Lra & Lcs & L5 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & L17 & LFR & LVP & LWQ & LM & HJ &
  HARU).
(* the byte at the cursor *)
destruct (skw_byte i ltac:(lia)) as (cb & Hcv & Hmb0).
pose proof (YK11.u8_range cb) as Hc8.
assert (Hmb : mbyte tfibsegs (mrestrict (w_H W) memL) (p + i) = Some cb).
{ rewrite (skw_mbyte_eq (w_H W) mem memL (p + i)); [exact Hmb0|].
  apply LM; rewrite wz by (unfold HEAD in *; lia); unfold HEAD in *; lia. }
assert (G10 : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 10) = q)
  by (apply (skw_ewR _ _ 10 10%bv); [reflexivity | exact L10 | lia]).
assert (G12 : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 12) = SHADOW_OFF)
  by (apply (skw_ewR _ _ 12 12%bv); [reflexivity | exact L12 | unfold SHADOW_OFF; lia]).
assert (G14 : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 14) = text + len)
  by (apply (skw_ewR _ _ 14 14%bv); [reflexivity | exact L14 | lia]).
assert (G15 : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 15) = p + i)
  by (apply (skw_ewR _ _ 15 15%bv); [reflexivity | exact L15 | lia]).
assert (G32u : bv_unsigned (ew (Ereg regsL [w64 (bv_unsigned cb)]) 32) = bv_unsigned cb)
  by (unfold w64; apply unsigned_lit_small; lia).
(* the memory kept outside in->p, chained over the runs of this pass *)
pose proof (skL_ss_ok i regsL memL mdL cb ltac:(lia) Hlt HL0 Hmb) as HS.
assert (SHOK : sh_ok tfibsegs skL_Bx (@nil shent) (Ereg regsL [w64 (bv_unsigned cb)])
  (mrestrict (w_H W) memL)) by apply Forall_nil.
(* 0x835fc -> the value test 0x83614: the UBSan p != 0 guard and the 1-byte shadow check of the cursor *)
fsw_aj_run_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold skL_Bx. rewrite !U_SOff, G12, G15, !Z.add_0_r. cbn [ms_mem mkst].
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF, RTLO, RTHI in *; lia).
  refine (skw_RA_blk_mem ly S U W memL mdL (text - HEAD) (tcap + HEAD) (p + i) 1 HARU HHD Hin _ _ _);
    [unfold HEAD; lia | lia | rewrite skw_req by (unfold HEAD; lia); unfold HEAD; lia]. }
{ apply (skw_awr_wins _ _ [(10%nat, 0, 8)]); [vm_compute; reflexivity|].
  constructor; [|constructor]. cbn [fst snd]. intros x Hx. rewrite G10 in Hx.
  left; left. unfold skw_STKw. lia. }
skw_km0 HF memL G10 KM1.
srr_branch_tok skip_ws_tbl_ok HS SHOK fs_Bspan.
- (* 32 < the byte: it is no white space, so i = skw_n and the loop leaves at once *)
  rewrite branch_ltu_U, U_SOff, U_SLit in Hc. skw_ews_in Hc. rewrite G32u in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc.
  assert (HiN : i = skw_n).
  { destruct (Z.eq_dec i skw_n) as [Eq|Hne]; [exact Eq | exfalso].
    pose proof (skw_ws_lt i ltac:(lia)) as Hw. rewrite <- Hcv in Hw.
    rewrite (skw_ws_gt32 (bv_unsigned cb) ltac:(lia)) in Hw. discriminate. }
  (* 0x83614 -> the epilogue 0x83654 *)
  fsw_aj_run_to_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan SKW_EXIT.
  { apply (skw_awr_wins _ _ [(10%nat, 0, 8)]); [vm_compute; reflexivity|].
    constructor; [|constructor]. cbn [fst snd]. intros x Hx. skw_ews_in Hx. rewrite G10 in Hx.
    left; left. unfold skw_STKw. lia. }
  skw_km HF0 KM1 memL G10 KM2.
  pose proof (skw_pres_from _ _ _ regsL [w64 (bv_unsigned cb)] HS ltac:(vm_compute; reflexivity)
    ltac:(intros nn Hnn; skw_ews; reflexivity)) as XPc.
  pose proof (skw_reg_keep _ _ _ _ 1%bv 1 regsL [w64 (bv_unsigned cb)] HS ltac:(vm_compute; reflexivity)
    ltac:(skw_ews; reflexivity) eq_refl) as Hra1.
  destruct (skw_qreg _ _ 0 (p + i) (fsw_region_nth _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity))
    ltac:(skw_ews; exact G10) ltac:(skw_ews; exact G15) ltac:(lia)) as (VPc & WQc).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
  exact (skw_exit_pack i regsL memL mdL _ _ _ (p + i + 0) HL0 XPc Hra1 KM2 VPc ltac:(lia) WQc HJ HARU).
- (* the byte is at most 32: the mask test *)
  rewrite branch_ltu_U, U_SOff, U_SLit in Hc. skw_ews_in Hc. rewrite G32u in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc.
  (* 0x83614 -> the mask test 0x83620 *)
  fsw_aj_run_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan.
  { apply (skw_awr_wins _ _ [(10%nat, 0, 8)]); [vm_compute; reflexivity|].
    constructor; [|constructor]. cbn [fst snd]. intros x Hx. skw_ews_in Hx. rewrite G10 in Hx.
    left; left. unfold skw_STKw. lia. }
  skw_km HF0 KM1 memL G10 KM2.
  srr_branch_tok skip_ws_tbl_ok HS SHOK fs_Bspan.
  + (* the mask bit is 0: no white space, so i = skw_n *)
    rewrite branch_eq_U, U_SLit in Hc0.
    rewrite (skw_bit_val _ (bv_unsigned cb)) in Hc0; [| skw_ews; exact G32u | lia].
    rewrite (zcanon_id 0) in Hc0 by (unfold M64; lia). apply Z.eqb_eq in Hc0.
    assert (Hnotws : PjGrammar.ws (bv_unsigned cb) = false)
      by (destruct (PjGrammar.ws (bv_unsigned cb)); [lia | reflexivity]).
    assert (HiN : i = skw_n).
    { destruct (Z.eq_dec i skw_n) as [Eq|Hne]; [exact Eq | exfalso].
      pose proof (skw_ws_lt i ltac:(lia)) as Hw. rewrite <- Hcv, Hnotws in Hw. discriminate. }
    (* 0x83620 -> the epilogue 0x83654 *)
    fsw_aj_run_to_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan SKW_EXIT.
    { apply (skw_awr_wins _ _ [(10%nat, 0, 8)]); [vm_compute; reflexivity|].
      constructor; [|constructor]. cbn [fst snd]. intros x Hx. skw_ews_in Hx. rewrite G10 in Hx.
      left; left. unfold skw_STKw. lia. }
    skw_km HF1 KM2 memL G10 KM3.
    pose proof (skw_pres_from _ _ _ regsL [w64 (bv_unsigned cb)] HS ltac:(vm_compute; reflexivity)
      ltac:(intros nn Hnn; skw_ews; reflexivity)) as XPc.
    pose proof (skw_reg_keep _ _ _ _ 1%bv 1 regsL [w64 (bv_unsigned cb)] HS ltac:(vm_compute; reflexivity)
      ltac:(skw_ews; reflexivity) eq_refl) as Hra1.
    destruct (skw_qreg _ _ 0 (p + i) (fsw_region_nth _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity))
      ltac:(skw_ews; exact G10) ltac:(skw_ews; exact G15) ltac:(lia)) as (VPc & WQc).
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
    exact (skw_exit_pack i regsL memL mdL _ _ _ (p + i + 0) HL0 XPc Hra1 KM3 VPc ltac:(lia) WQc HJ HARU).
  + (* the mask bit is 1: white space, so i < skw_n; the UBSan p + 1 guard, the store, the back edge *)
    rewrite branch_eq_U, U_SLit in Hc0.
    rewrite (skw_bit_val _ (bv_unsigned cb)) in Hc0; [| skw_ews; exact G32u | lia].
    rewrite (zcanon_id 0) in Hc0 by (unfold M64; lia). apply Z.eqb_neq in Hc0.
    assert (Hisws : PjGrammar.ws (bv_unsigned cb) = true)
      by (destruct (PjGrammar.ws (bv_unsigned cb)); [reflexivity | lia]).
    assert (HiLt : i < skw_n).
    { destruct (Z.eq_dec i skw_n) as [Eq|Hne]; [exfalso | lia].
      pose proof (skw_ws_at_n ltac:(lia)) as Hw. rewrite <- Eq, <- Hcv, Hisws in Hw. discriminate. }
    (* 0x83620 -> the back-edge test 0x8363c: the 8-byte shadow check of q and the in->p store *)
    fsw_aj_run_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan.
    { unfold skL_Bx. rewrite !U_SOff. skw_ews. rewrite G12, G10, !Z.add_0_r.
      rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia). cbn [ms_mem mkst].
      exact (skw_RA_stk_mem ly S U W _ _ q 8 HARU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bqal eq_refl
        ltac:(lia)). }
    { apply (skw_awr_wins _ _ [(10%nat, 0, 8)]); [vm_compute; reflexivity|].
      constructor; [|constructor]. cbn [fst snd]. intros x Hx. skw_ews_in Hx. rewrite G10 in Hx.
      left; left. unfold skw_STKw. lia. }
    skw_km HF1 KM2 memL G10 KM3.
    srr_branch_tok skip_ws_tbl_ok HS SHOK fs_Bspan.
    * (* the new cursor is still below in->end: one more pass *)
      rewrite branch_ltu_U, !U_SOff in Hc1. skw_ews_in Hc1. rewrite G14, G15 in Hc1.
      rewrite !zcanon_id in Hc1 by (unfold M64, RTLO, RTHI in *; lia). apply Z.ltb_lt in Hc1.
      fsw_aj_run_to_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan SKW_LOOP.
      { apply (skw_awr_wins _ _ [(10%nat, 0, 8)]); [vm_compute; reflexivity|].
        constructor; [|constructor]. cbn [fst snd]. intros x Hx. skw_ews_in Hx. rewrite G10 in Hx.
        left; left. unfold skw_STKw. lia. }
      skw_km HF2 KM3 memL G10 KM4.
      pose proof (fsw_region_nth _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity)) as RQb.
      pose proof (skw_pres_from _ _ _ regsL [w64 (bv_unsigned cb)] HS ltac:(vm_compute; reflexivity)
        ltac:(intros nn Hnn; skw_ews; reflexivity)) as XPb.
      destruct (skw_qreg _ _ 1 (p + i) RQb ltac:(skw_ews; exact G10) ltac:(skw_ews; exact G15) ltac:(lia))
        as (VPb & WQb).
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
      refine (IH (Z.to_nat (skw_n - (i + 1))) ltac:(lia) (i + 1) _ _ _ eq_refl ltac:(lia) ltac:(lia) _).
      unfold skL_at.
      split; [unfold spZ; rewrite (fsw_pres regsL _ 2%bv XPb ltac:(skw_ics)); exact Lsp|].
      split; [rewrite (skw_reg_keep _ _ _ _ 1%bv 1 regsL [w64 (bv_unsigned cb)] HS
        ltac:(vm_compute; reflexivity) ltac:(skw_ews; reflexivity) eq_refl); exact Lra|].
      split; [intros rr Hrr Hrr2; rewrite (fsw_pres regsL _ rr XPb Hrr); exact (Lcs rr Hrr Hrr2)|].
      split; [refine (skw_reg_val _ _ _ _ 5%bv (SLit 1) 1 HS _ _);
        [vm_compute; reflexivity | apply skw_denot_lit; lia]|].
      split; [rewrite (skw_reg_keep _ _ _ _ 10%bv 10 regsL [w64 (bv_unsigned cb)] HS
        ltac:(vm_compute; reflexivity) ltac:(skw_ews; reflexivity) eq_refl); exact L10|].
      split; [refine (skw_reg_val _ _ _ _ 11%bv (SOff 15 1) (p + (i + 1)) HS _ _);
        [vm_compute; reflexivity | apply (skw_denot_off _ 15 1 (p + i)); [skw_ews; exact G15 | lia | lia]]|].
      split; [rewrite (skw_reg_keep _ _ _ _ 12%bv 12 regsL [w64 (bv_unsigned cb)] HS
        ltac:(vm_compute; reflexivity) ltac:(skw_ews; reflexivity) eq_refl); exact L12|].
      split; [refine (skw_reg_val _ _ _ _ 13%bv (skw_shx 10 12) (SHADOW_OFF + q / 8) HS _ _);
        [vm_compute; reflexivity
        | apply skw_shx_denot; [skw_ews; exact G10 | skw_ews; exact G12 | lia | unfold SHADOW_OFF; lia]]|].
      split; [rewrite (skw_reg_keep _ _ _ _ 14%bv 14 regsL [w64 (bv_unsigned cb)] HS
        ltac:(vm_compute; reflexivity) ltac:(skw_ews; reflexivity) eq_refl); exact L14|].
      split; [refine (skw_reg_val _ _ _ _ 15%bv (SOff 15 1) (p + (i + 1)) HS _ _);
        [vm_compute; reflexivity | apply (skw_denot_off _ 15 1 (p + i)); [skw_ews; exact G15 | lia | lia]]|].
      split; [refine (skw_reg_val _ _ _ _ 16%bv (SLit 32) 32 HS _ _);
        [vm_compute; reflexivity | apply skw_denot_lit; lia]|].
      split; [refine (skw_reg_val _ _ _ _ 17%bv (SLit 4294977024) 4294977024 HS _ _);
        [vm_compute; reflexivity | apply skw_denot_lit; lia]|].
      split; [apply (skw_val_mem_eq_at _ memL _);
        [intros kk Hkk; apply KM4; rewrite wz by lia; lia | exact LFR]|].
      split; [replace (p + (i + 1)) with (p + i + 1) by lia; exact VPb|].
      split; [exact WQb|].
      split; [intros xx A1 A2; rewrite (KM4 xx A2); exact (LM xx A1 A2)|].
      split; [exact HJ | exact HARU].
    * (* the new cursor reached in->end: i + 1 = skw_n, leave the loop *)
      rewrite branch_ltu_U, !U_SOff in Hc1. skw_ews_in Hc1. rewrite G14, G15 in Hc1.
      rewrite !zcanon_id in Hc1 by (unfold M64, RTLO, RTHI in *; lia). apply Z.ltb_ge in Hc1.
      assert (HiN : i + 1 = skw_n).
      { pose proof skw_all_len as HL1. unfold skw_all in HL1. rewrite length_app in HL1. unfold skw_n in *. lia. }
      fsw_aj_run_to_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan SKW_EXIT.
      { apply (skw_awr_wins _ _ [(10%nat, 0, 8)]); [vm_compute; reflexivity|].
        constructor; [|constructor]. cbn [fst snd]. intros x Hx. skw_ews_in Hx. rewrite G10 in Hx.
        left; left. unfold skw_STKw. lia. }
      skw_km HF2 KM3 memL G10 KM4.
      pose proof (skw_pres_from _ _ _ regsL [w64 (bv_unsigned cb)] HS ltac:(vm_compute; reflexivity)
        ltac:(intros nn Hnn; skw_ews; reflexivity)) as XPc.
      pose proof (skw_reg_keep _ _ _ _ 1%bv 1 regsL [w64 (bv_unsigned cb)] HS ltac:(vm_compute; reflexivity)
        ltac:(skw_ews; reflexivity) eq_refl) as Hra1.
      destruct (skw_qreg _ _ 1 (p + i) (fsw_region_nth _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity))
        ltac:(skw_ews; exact G10) ltac:(skw_ews; exact G15) ltac:(lia)) as (VPc & WQc).
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
      exact (skw_exit_pack i regsL memL mdL _ _ _ (p + i + 1) HL0 XPc Hra1 KM4 VPc ltac:(lia) WQc HJ HARU).
Qed.

(* ---- the entry 0x83598: the frame, the UBSan alignment guard, the two 8-byte shadow checks of struct pj_in, and
   the first exit test 0x835e0 ---- *)
Lemma skw_entry : SRr tfibsegs W (YG0d.cfg_at tfibsegs A_skip_ws regs mem md) skw_POST.
Proof.
pose proof skw_nums as (Hal16 & Hceil & H47 & Hslo & Hslo2 & Hshi & Htop2 & Hq1 & Hq2 & Hotal & Hottop &
  Bq0 & Bqal & Bt0 & Bp & Btl & Blen & Bd & Htx1 & Hin & Htc & Hlen2 & Hbb & ESTK & EFR & C1 & C3).
pose proof skw_n_le as (Hn0 & Hnle).
pose proof HWIN as (Hw1 & Hw2 & Hw3 & Hw4 & Hpres).
pose proof (fsw_ARU B STK_skip_ws ly S U W regs mem md ch (proj1 HPRE)) as HARU.
pose proof HPRE as (((HAR0 & Hra & _) & _ & _) & _).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply u64_range).
(* the entry env: atom 32 is the shadow base, xatom 0 = in->p, xatom 1 = in->end *)
assert (E2 : bv_unsigned (ew (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)])) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs (fs_extraT ++ [w64 p; w64 (text + len)]) 2 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)])) 10) = q)
  by (apply (skw_ewR _ _ 10 10%bv); [reflexivity | exact H10 | lia]).
assert (E32 : ew (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)])) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E32u : bv_unsigned (ew (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)])) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
assert (E33 : ew (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)])) 33 = w64 p)
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33u : bv_unsigned (ew (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)])) 33) = p)
  by (rewrite E33; unfold w64; apply unsigned_lit_small; skw_lia).
assert (E34 : ew (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)])) 34 = w64 (text + len))
  by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34u : bv_unsigned (ew (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)])) 34) = text + len)
  by (rewrite E34; unfold w64; apply unsigned_lit_small; skw_lia).
(* struct pj_in's two words on the entry memory *)
assert (Vp : val_mem tfibsegs (mrestrict (w_H W) mem) q 8 p).
{ pose proof (KindBGlue.bytes_at_le8_word tfibsegs (mrestrict (w_H W) mem) q (Z_to_bv 64 p) (proj1 HIN)) as Hw.
  rewrite (wz p ltac:(skw_lia)) in Hw.
  exact (proj2 (val_mem_word_mem tfibsegs (mrestrict (w_H W) mem) q p) Hw). }
assert (Ve : val_mem tfibsegs (mrestrict (w_H W) mem) (q + 8) 8 (text + len)).
{ pose proof (KindBGlue.bytes_at_le8_word tfibsegs (mrestrict (w_H W) mem) (q + 8) (Z_to_bv 64 (text + len))
    (proj1 (proj2 HIN))) as Hw.
  rewrite (wz (text + len) ltac:(skw_lia)) in Hw.
  exact (proj2 (val_mem_word_mem tfibsegs (mrestrict (w_H W) mem) (q + 8) (text + len)) Hw). }
assert (HWR : forall o, 0 <= o < 24 -> writable_at tfibsegs (mrestrict (w_H W) mem) (q + o))
  by (pose proof HIN as (_ & _ & _ & (_ & _ & HW3) & _); exact HW3).
(* the entry symbolic state *)
assert (HS : st_ok tfibsegs (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)]))
  (fss0T_args A_skip_ws FRAME_skip_ws [skw_q_region] skw_gf)
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_skip_ws) mem (YK11.seg_rom tfibsegs)))).
{ apply (fsw_entryT_argsX B STK_skip_ws FRAME_skip_ws ly S U W regs mem md ch A_skip_ws [skw_q_region] skw_gf
    [w64 p; w64 (text + len)] TL_got TL_cell (proj1 HPRE) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)).
  - constructor; [|constructor]. unfold skw_q_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E10.
    split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HWR o ltac:(lia))|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val tfibsegs _ _ q 0 8 (SOff (xatom 0) 0) p);
        [ rewrite fsw_SOff0; change (xatom 0) with 33%nat; rewrite E33; reflexivity
        | cbn [Z.of_N]; skw_lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact Vp].
    + apply (chunk_ok_val tfibsegs _ _ q 8 8 (SOff (xatom 1) 0) (text + len));
        [ rewrite fsw_SOff0; change (xatom 1) with 34%nat; rewrite E34; reflexivity
        | cbn [Z.of_N]; skw_lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Ve].
  - apply pairwise_disjoint_of_extents.
    unfold fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, skw_q_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E10.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
    change FRAME_skip_ws with 16.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; skw_lia | left; skw_lia].
  - unfold skw_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (xatom 0) with 33%nat. change (xatom 1) with 34%nat. rewrite E10, E33u, E34u.
    repeat split;
      first [ change (2 ^ 3) with 8; exact Bqal
            | rewrite Z.pow_0_r; apply Z.mod_1_r
            | skw_lia ]. }
pose proof (fsw_ajournal_init_ot B STK_skip_ws [] ly S U W regs mem md ch ot (proj1 HPRE) ltac:(lia) Hw3
  ltac:(lia) Hpres) as HJ.
assert (SHOK : sh_ok tfibsegs fs_Bx (@nil shent) (Ereg regs (fs_extraT ++ [w64 p; w64 (text + len)]))
  (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold YG0d.cfg_at. change (w64 A_skip_ws) with (Z_to_bv 64 A_skip_ws).
(* 0x83598 -> the exit test 0x835e0 *)
fsw_aj_run_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold fs_Bx. rewrite !U_SOff, E32u, E10. cbn [ms_mem mkst].
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  refine (skw_RA_stk_mem ly S U W mem md (q + 8) 8 HARU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) _ eq_refl
    ltac:(lia)).
  rewrite Zplus_mod, Bqal. reflexivity. }
{ unfold fs_Bx. rewrite !U_SOff, E32u, E10, !Z.add_0_r. cbn [ms_mem mkst].
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (skw_RA_stk_mem ly S U W mem md q 8 HARU ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bqal eq_refl
    ltac:(lia)). }
{ apply (skw_awr_wins _ _ [(2%nat, -16, 0); (10%nat, 0, 8)]); [vm_compute; reflexivity|].
  constructor; [|constructor; [|constructor]]; cbn [fst snd]; intros x Hx;
    [rewrite E2 in Hx | rewrite E10 in Hx]; left; left; unfold skw_STKw; lia. }
assert (KM1 : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
  ~ (q <= bv_unsigned x < q + 8) -> ms_mem ms x = mem x).
{ intros xx A1 A2.
  refine (skw_frame_wins _ _ _ _ [(2%nat, -16, 0); (10%nat, 0, 8)] HF ltac:(vm_compute; reflexivity) xx _).
  constructor; [|constructor; [|constructor]]; cbn [fst snd]; [rewrite E2 | rewrite E10]; lia. }
srr_branch_tok skip_ws_tbl_ok HS SHOK fs_Bspan.
- (* in->p is already in->end: the white-space run is empty and the epilogue follows at once *)
  rewrite branch_geu_U, !U_SOff in Hc. skw_ews_in Hc. rewrite E33u, E34u in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; skw_lia). apply negb_true_iff, Z.ltb_ge in Hc.
  assert (HN0 : skw_n = 0).
  { pose proof skw_all_len as HL1. unfold skw_all in HL1. rewrite length_app in HL1. unfold skw_n. lia. }
  fsw_aj_run_to_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan SKW_EXIT.
  { apply (skw_awr_wins _ _ [(2%nat, -16, 0); (10%nat, 0, 8)]); [vm_compute; reflexivity|].
    constructor; [|constructor; [|constructor]]; cbn [fst snd]; intros x Hx; skw_ews_in Hx;
      [rewrite E2 in Hx | rewrite E10 in Hx]; left; left; unfold skw_STKw; lia. }
  assert (KM2 : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
    ~ (q <= bv_unsigned x < q + 8) -> ms_mem ms0 x = mem x).
  { intros xx A1 A2. rewrite <- (KM1 xx A1 A2).
    refine (skw_frame_wins _ _ _ _ [(2%nat, -16, 0); (10%nat, 0, 8)] HF0 ltac:(vm_compute; reflexivity) xx _).
    constructor; [|constructor; [|constructor]]; cbn [fst snd]; skw_ews; [rewrite E2 | rewrite E10]; lia. }
  (* the frame's saved ra and struct pj_in, out of the state at 0x83654 *)
  pose proof (fsw_region_nth _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as RF.
  pose proof (fsw_field _ _ 2%nat (spZ regs) _ (-16) 0 (-16) 0 (-8) 8%N (SOff 1 0)
    (bv_unsigned (YK11.getr regs 1)) RF ltac:(skw_ews; exact E2) ltac:(left; reflexivity)
    ltac:(rewrite fsw_SOff0; skw_ews;
          rewrite (ew_Ereg_nat regs (fs_extraT ++ [w64 p; w64 (text + len)]) 1 1%bv eq_refl);
          symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(cbn [Z.of_N]; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as VFR.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in VFR.
  pose proof (fsw_region_nth _ _ _ 3%nat _ HS ltac:(vm_compute; reflexivity)) as RQ.
  pose proof (fsw_field _ _ 10%nat q _ 0 16 0 8 0 8%N (SOff 33 0) p RQ ltac:(skw_ews; exact E10)
    ltac:(left; reflexivity) ltac:(rewrite fsw_SOff0; skw_ews; exact E33)
    ltac:(cbn [Z.of_N]; skw_lia) ltac:(cbn [Z.of_N]; lia)) as VQ.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in VQ. rewrite Z.add_0_r in VQ.
  assert (WQ : forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms0)) (q + o)).
  { destruct RQ as (_ & _ & HW & _).
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in HW. skw_ews_in HW. rewrite E10 in HW. exact HW. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
  apply skw_exit.
  + eapply (fsw_reg_off (w_H W) _ _ ms0 2%bv 2 (-16) (spZ regs));
      [exact HS | vm_compute; reflexivity | skw_ews; exact E2 | lia].
  + exact (skw_reg_keep _ _ _ _ 1%bv 1 regs (fs_extraT ++ [w64 p; w64 (text + len)]) HS
      ltac:(vm_compute; reflexivity) ltac:(skw_ews; reflexivity) eq_refl).
  + apply (skw_cs_keep _ _ ms0 regs (fs_extraT ++ [w64 p; w64 (text + len)]) HS ltac:(vm_compute; reflexivity)
      ltac:(intros nn Hnn; skw_ews; reflexivity)).
  + replace (spZ regs - 8) with (spZ regs + -8) by lia. exact VFR.
  + rewrite HN0, Z.add_0_r. exact VQ.
  + exact WQ.
  + intros xx A1 A2. exact (KM2 xx A1 A2).
  + exact HJ.
  + exact HARU.
- (* in->p is below in->end: the loop runs from i = 0 *)
  rewrite branch_geu_U, !U_SOff in Hc. skw_ews_in Hc. rewrite E33u, E34u in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; skw_lia). apply negb_false_iff, Z.ltb_lt in Hc.
  fsw_aj_run_to_tokU skip_ws_tbl_ok HS HJ HARU SHOK fs_Bspan SKW_LOOP.
  { apply (skw_awr_wins _ _ [(2%nat, -16, 0); (10%nat, 0, 8)]); [vm_compute; reflexivity|].
    constructor; [|constructor; [|constructor]]; cbn [fst snd]; intros x Hx; skw_ews_in Hx;
      [rewrite E2 in Hx | rewrite E10 in Hx]; left; left; unfold skw_STKw; lia. }
  assert (KM2 : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) ->
    ~ (q <= bv_unsigned x < q + 8) -> ms_mem ms0 x = mem x).
  { intros xx A1 A2. rewrite <- (KM1 xx A1 A2).
    refine (skw_frame_wins _ _ _ _ [(2%nat, -16, 0); (10%nat, 0, 8)] HF0 ltac:(vm_compute; reflexivity) xx _).
    constructor; [|constructor; [|constructor]]; cbn [fst snd]; skw_ews; [rewrite E2 | rewrite E10]; lia. }
  pose proof (fsw_region_nth _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as RF.
  pose proof (fsw_field _ _ 2%nat (spZ regs) _ (-16) 0 (-16) 0 (-8) 8%N (SOff 1 0)
    (bv_unsigned (YK11.getr regs 1)) RF ltac:(skw_ews; exact E2) ltac:(left; reflexivity)
    ltac:(rewrite fsw_SOff0; skw_ews;
          rewrite (ew_Ereg_nat regs (fs_extraT ++ [w64 p; w64 (text + len)]) 1 1%bv eq_refl);
          symmetry; apply Z_to_bv_bv_unsigned)
    ltac:(cbn [Z.of_N]; apply u64_range) ltac:(cbn [Z.of_N]; lia)) as VFR.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in VFR.
  pose proof (fsw_region_nth _ _ _ 3%nat _ HS ltac:(vm_compute; reflexivity)) as RQ.
  pose proof (fsw_field _ _ 10%nat q _ 0 16 0 8 0 8%N (SOff 33 0) p RQ ltac:(skw_ews; exact E10)
    ltac:(left; reflexivity) ltac:(rewrite fsw_SOff0; skw_ews; exact E33)
    ltac:(cbn [Z.of_N]; skw_lia) ltac:(cbn [Z.of_N]; lia)) as VQ.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in VQ. rewrite Z.add_0_r in VQ.
  assert (WQ : forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms0)) (q + o)).
  { destruct RQ as (_ & _ & HW & _).
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in HW. skw_ews_in HW. rewrite E10 in HW. exact HW. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ _ HS ltac:(vm_compute; reflexivity)). cbn [ss_pc].
  refine (skw_loop (Z.to_nat (skw_n - 0)) 0 _ _ _ eq_refl ltac:(lia) ltac:(lia) _).
  unfold skL_at.
  split; [eapply (fsw_reg_off (w_H W) _ _ ms0 2%bv 2 (-16) (spZ regs));
    [exact HS | vm_compute; reflexivity | skw_ews; exact E2 | lia]|].
  split; [exact (skw_reg_keep _ _ _ _ 1%bv 1 regs (fs_extraT ++ [w64 p; w64 (text + len)]) HS
    ltac:(vm_compute; reflexivity) ltac:(skw_ews; reflexivity) eq_refl)|].
  split; [apply (skw_cs_keep _ _ ms0 regs (fs_extraT ++ [w64 p; w64 (text + len)]) HS
    ltac:(vm_compute; reflexivity) ltac:(intros nn Hnn; skw_ews; reflexivity))|].
  split; [refine (skw_reg_val _ _ _ _ 5%bv (SLit 1) 1 HS _ _);
    [vm_compute; reflexivity | apply skw_denot_lit; lia]|].
  split; [refine (skw_reg_val _ _ _ _ 10%bv (SOff 10 0) q HS _ _);
    [vm_compute; reflexivity | apply (skw_denot_off _ 10 0 q); [skw_ews; exact E10 | lia | lia]]|].
  split; [refine (skw_reg_val _ _ _ _ 11%bv (SOff 33 0) (p + 0) HS _ _);
    [vm_compute; reflexivity | apply (skw_denot_off _ 33 0 p); [skw_ews; exact E33u | lia | skw_lia]]|].
  split; [refine (skw_reg_val _ _ _ _ 12%bv (SOff 32 0) SHADOW_OFF HS _ _);
    [vm_compute; reflexivity | apply (skw_denot_off _ 32 0 SHADOW_OFF);
      [skw_ews; exact E32u | lia | unfold SHADOW_OFF; lia]]|].
  split; [refine (skw_reg_val _ _ _ _ 13%bv (skw_shx 10 32) (SHADOW_OFF + q / 8) HS _ _);
    [vm_compute; reflexivity
    | apply skw_shx_denot; [skw_ews; exact E10 | skw_ews; exact E32u | lia | unfold SHADOW_OFF; lia]]|].
  split; [refine (skw_reg_val _ _ _ _ 14%bv (SOff 34 0) (text + len) HS _ _);
    [vm_compute; reflexivity | apply (skw_denot_off _ 34 0 (text + len)); [skw_ews; exact E34u | lia | skw_lia]]|].
  split; [refine (skw_reg_val _ _ _ _ 15%bv (SOff 33 0) (p + 0) HS _ _);
    [vm_compute; reflexivity | apply (skw_denot_off _ 33 0 p); [skw_ews; exact E33u | lia | skw_lia]]|].
  split; [refine (skw_reg_val _ _ _ _ 16%bv (SLit 32) 32 HS _ _);
    [vm_compute; reflexivity | apply skw_denot_lit; lia]|].
  split; [refine (skw_reg_val _ _ _ _ 17%bv (SLit 4294977024) 4294977024 HS _ _);
    [vm_compute; reflexivity | apply skw_denot_lit; lia]|].
  split; [replace (spZ regs - 8) with (spZ regs + -8) by lia; exact VFR|].
  split; [rewrite Z.add_0_r; exact VQ|].
  split; [exact WQ|].
  split; [intros xx A1 A2; exact (KM2 xx A1 A2)|].
  split; [exact HJ | exact HARU].
Qed.

End L.

(* ================= skip_ws_spec ================= *)
Theorem skip_ws_holds : @skip_ws_spec fx rc SK tfibsegs B.
Proof.
unfold skip_ws_spec.
intros ly S U W regs mem md ch q ot text len p d tb tcap wsl rest live peak cnt fail
  HPRE HHD H10 HIN HWIN HTX HREST HWS HNW HGL.
apply (skw_entry ly S U W regs mem md ch q ot text len p d tb tcap wsl rest live peak cnt fail
  HPRE HHD H10 HIN HWIN HTX HREST HWS HNW HGL).
Qed.

End W.

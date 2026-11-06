(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the SEGMENT CUTS of the ASan walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput.  STATEMENTS ONLY (rule 24): this file proves no function.  It states, for each cut point
   of the walk, the predicate that holds there on every live path, one `seg_Sx_stmt : Prop` per segment, and the
   composition `llvmf_compose_stmt`, so the seven segments are proved in parallel lanes, each lane taking the other
   lanes' STATED predicates as hypotheses. *)

(*   HOW THE CUTS ARE STATED, AND WHY NOT IN THE DONOR'S SYMBOLIC FORM.  cgif_file_fuzzer's harness stations
   (A/ACf5.v:70-80 rt_from with A/ACf7.v:27-180 ss_A2 .. INV_F) pair a CONCRETE SYMBOLIC STATE `ss` -- the
   executor's output at that pc, copied into the file -- with a semantic invariant INV.  A symbolic state can only
   be written down after the previous segment has been run, so that form serialises the lanes.  Here every cut is a
   SEMANTIC predicate over (ly, S, W, regs, mem, md) alone: the journal, the frame and its shadow cells, the heap
   blocks and their contents, the register and spill values that matter, and the input-derived values.  A lane
   rebuilds its own `st_ok_pi` from it, exactly as the donor's A/ACf5.v:187-247 rt_entry rebuilds the entry one.
   The frame regions follow one rule (decided in a review with two Theorem Labs lanes): a Theorem Labs lane's proved
   `frame_setup` (lib/A/P_check_step_frame.v) applies ONLY in S0, right after the class-8 stack malloc, because its
   premise `zero_shadow` of the frame start is made false by S0's own f1 stores.  Every later lane re-adds the
   frame and frame-shadow regions with `st_ok_pi_add_region` (A/Prog/ScenePaLib.v:105) from what the cut CARRIES:
   the presence of both windows and every shadow cell's value (`sc_frame`, `sc_shbg`, the object cells), the flag
   word, and `In (8, fpos) (frames S)` with own = [(8, fpos)] for write permission; presence and not-aowned also
   follow from AR's al_frames and FFL, as cgif's exitN (A/ACk2.v:319-344) uses them.  The cost is one entry block
   per lane; the gain is that the seven lanes are independent.
   The cuts state only POSITIVE facts at the pc.  What a call leaves alone is not restated here: the journal's own
   clauses (YCbq.v:356-364) and each callee's write-set post carry it between cuts.

   WHERE A VALUE LIVES.  A cut names each value by its ROLE and gives its location as a `vloc`: a register, or the
   spill slot [sp1 + off].  The asan and asan-ubsan builds hold the same roles in different places, and sometimes
   in a different KIND of place (asan keeps `step` in [s1+0x50], asan-ubsan keeps it in s7 -- a Theorem Labs lane's
   TWINMAP.md:81), so the whole location table is one parameter, the record `sgeom`.  Section `g` below holds no
   image value; `scene_geom_asan` is the asan table, and lib/AU/P_LLVMFuzzerTestOneInput_seg.v is the
   asan-ubsan one.

   Image: fuzz_scene.asan, sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026, symbols from
   the unstripped twin 6ed872f7cc8c1e426ccbd2a7d1ae20b71d1cb347bd6c2cb9746780771da2a003 (same loaded bytes).
   Every number of `scene_geom_asan` is MEASURED on that image this session (the listing dis-LLVMF.asan.txt); the
   evidence per cut -- why the predicate is true there on every path, and what each segment's post gives the next
   -- is SEG-REVIEW-1.md (sha256 69b1349ab2ef; internal record).  The cut pcs, as offsets in
   LLVMFuzzerTestOneInput (0x82878):
     C1 0x82b78 (+0x300)  after the E parse and the 6-turn mac loop, at `sd a5,0x18(s1)`;
     C2 0x82ca8 (+0x430)  after the fill and xor loops, at the first instruction of the B block;
     C3 0x82d74 (+0x4fc)  the join of B's two arms (check_step 0x82d6c falls through 0x82d70; the "changed" arm's
                          `beqz a0` 0x82d58 targets it), at `andi a0,a1,2`, the whole_transfer guard;
     T  0x82dc4 (+0x54c)  the head of the 343-turn whole_transfer loop (the back edge `bne s6,a0` 0x82e70 targets it);
     TX 0x82e74 (+0x5fc)  the loop exit, before the got / declared checks;
     C5 0x82eb0 (+0x638)  the join of the T arm and the no-T arm (`beqz a0` 0x82d78 and `bne s8,a0` 0x82d84 both
                          target it), before M3's `ld a0,0x38(s1)`;
     C6 0x83020 (+0x7a8)  the join of D's two arms (`j` 0x82f48 targets it), before F2's `mv a0,s4`.
   The segments (HAND1-PLAN.md section 2.2):
     S0 entry .. C1;  S1 C1 .. C2;  S2 C2 .. C3;  S3 one T turn;  S4 C3 .. C5 (the guard, M2, the loop closed over
     S3 by induction, the post-loop checks, bcmp and F1, and the no-T arm);  S5 C5 .. C6 (M3 and D);
     S6 C6 .. the return (F2, F3, the release).

   WHAT THE T-LOOP INVARIANT IS BUILT ON.  `cut_T` is the ASan form of the RELEASED PLAIN invariant of scene's own
   proof, lib/Prog/SceneT.v:18-28 `TMem` (turn :75 scene_T_turn, loop :244 scene_T_loop, entry :272 scene_T_x), over
   the same pure model lib/Prog/SceneBlock.v and lib/Prog/SceneTM.v (`scene_block`, `scene_len`, `scT_off`,
   `scT_src`), which this file Requires.  The `again` buffer's CONTENTS clause carries over with the same shape and
   a different reader: plain
     `rw_cells rsegs m again [CB (scT_off k) (firstn (scT_off k) b); CB (8904 - scT_off k) ja]`
   becomes
     `garr8 segs (mrestrict (w_H W) mem) again (u8s (firstn (Z.to_nat (scT_off k)) b ++ ja))`.
   The WRITABILITY half of `rw_cells` does NOT carry over and is restated: in the ASan model a heap block is
   writable through the journal (`awr_byte` case 3, YCbq.v:463 in_tmp_block, with `aftok`) and readable through its
   shadow (`range_addressable`, from `In (again, 8904) (ablocks B ly S)` and AR's block law), not through a memory
   predicate; that half is `sc_blk_ok` here.  The plain `stk` / `munch` / `wmono` / `mem_inv` clauses have no
   counterpart: the journal carries them.  Everything else of TMem is restated in ASan terms: b's length, the two
   spilled 8904 words ([s1+8] and the declared slot), the mac bytes, and the disjointness of again from body (the
   plain proof also needs again and body apart from the stack frame; here the frame is the FAKE one, which
   AR_sep_law (YG0d.v:475-479) keeps apart from every heap block, so that clause is not restated). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00 YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
(* the pure model of scene's step blocks, from the released plain proof; both files import only BvBase. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- where a value lives at a cut: a register, or the spilled doubleword [sp1 + off] ---- *)
Inductive vloc : Type := VReg (r : bv 5) | VSpill (off : Z).

(* ---- the walk's constants: the entry contract's parameters, in its own order ---- *)
Record swalk : Type := mkSW {
sw_sink : list (Z * Z);          (* SINK_OWNED *)
(* no trailer parameter: the shadow of an image global is a STATIC fact of B (an internal review's item R2, through a Theorem Labs lane's
   CUTS.md:605-609), not a clause of this contract or of a cut *)
sw_entry : Z; sw_ra : Z; sw_ev : Z; sw_live : Z; sw_stk : Z; sw_empty : Z;
sw_xm : Z -> Z; sw_xn : Z -> Z;
sw_rlo : Z; sw_rhi : Z }.

(* ---- the image's geometry and its location table at the seven cuts ---- *)
Record sgeom : Type := mkSG {
(* the fake frame: class, size, and the frame descriptor's four objects *)
sg_cid : Z; sg_frame : Z;
sg_off_blki : Z; sg_off_mac : Z; sg_off_blk : Z; sg_off_expect : Z;
sg_blk_n : Z; sg_mac_n : Z; sg_scene_n : Z; sg_nturns : Z;
(* the frame-shadow cells the walk never changes, as (lo, hi, value) over offsets from shadow_addr F *)
sg_sh_bg : list (Z * Z * Z);
(* the poisoned shadow cells of blk.i and of blk, as half-open offset ranges *)
sg_sh_blki_lo : Z; sg_sh_blki_hi : Z; sg_sh_blk_lo : Z; sg_sh_blk_hi : Z;
(* the cut pcs *)
sg_pc_c1 : Z; sg_pc_c2 : Z; sg_pc_c3 : Z; sg_pc_t : Z; sg_pc_tx : Z; sg_pc_c5 : Z; sg_pc_c6 : Z;
(* C1 *)
sg1_F : vloc; sg1_shF : vloc; sg1_shbase : vloc; sg1_sp1 : vloc; sg1_sp0 : vloc;
sg1_blki : vloc; sg1_blk : vloc; sg1_expect : vloc; sg1_flags : vloc; sg1_rest : vloc;
sg1_cur : vloc; sg1_u16 : vloc; sg1_s7v : vloc; sg1_shexp : vloc; sg1_Fsp : vloc;
sg1_mac : vloc; sg1_step : vloc;
(* C2 *)
sg2_F : vloc; sg2_shF : vloc; sg2_shbase : vloc; sg2_sp1 : vloc; sg2_sp0 : vloc;
sg2_blki : vloc; sg2_blk : vloc; sg2_expect : vloc; sg2_body : vloc; sg2_nprime : vloc;
sg2_s7v : vloc; sg2_shexp : vloc; sg2_Fsp : vloc; sg2_mac : vloc; sg2_step : vloc;
(* the two slots S1 fills and only C5 reads back: a second place holding F, and n'' *)
sg2_Fb : vloc; sg2_nn : vloc;
(* the flags byte: S1 spills it and S2 reloads it before C3 *)
sg2_flags : vloc;
(* C3 *)
sg3_F : vloc; sg3_Fb : vloc; sg3_shF : vloc; sg3_sp1 : vloc; sg3_sp0 : vloc;
sg3_blki : vloc; sg3_expect : vloc; sg3_nprime : vloc; sg3_flags : vloc; sg3_step : vloc;
sg3_shexp : vloc; sg3_Fsp : vloc; sg3_mac : vloc; sg3_body : vloc; sg3_nn : vloc;
(* T and TX *)
sgT_got : vloc; sgT_k : vloc; sgT_shF : vloc; sgT_sp1 : vloc; sgT_sp0 : vloc;
sgT_blki : vloc; sgT_srcA : vloc; sgT_srcB : vloc; sgT_f8 : vloc; sgT_n1 : vloc;
(* constants the loop head of THIS build keeps that the other does not (asan: s2 = 8905, the bound of the
   `bgeu s8,s2` guard at 0x82e20; asan-ubsan tests `bltu s11,s8` against 8904 and has no such register) *)
sgT_extra : list (vloc * Z);
(* where this build keeps ~again, if it keeps it (asan-ubsan hoists `not a0` into [s1+0x50]; asan has none) *)
sgT_nagain : option vloc;
sgT_again : vloc; sgT_body : vloc; sgT_decl : vloc; sgT_nprime : vloc;
sgT_Fsp : vloc; sgT_mac : vloc; sgT_shexp : vloc;
(* the three slots the loop never writes and C5 reads back *)
sgT_expect : vloc; sgT_Fb : vloc; sgT_nn : vloc;
(* a second register holding `body` at the loop head, where this build keeps one *)
sgT_body2 : option vloc;
(* TX: the second register holding `got` at the exit (the latch copies it, and the exit check reads this one) *)
sgTX_got2 : vloc;
(* C5 *)
sg5_F : vloc; sg5_shF : vloc; sg5_sp1 : vloc; sg5_sp0 : vloc; sg5_nprime : vloc;
sg5_expect : vloc; sg5_shexp : vloc; sg5_Fsp : vloc; sg5_mac : vloc; sg5_body : vloc; sg5_nn : vloc;
(* C6 *)
sg6_F : vloc; sg6_shF : vloc; sg6_sp1 : vloc; sg6_sp0 : vloc;
sg6_before : vloc; sg6_body : vloc; sg6_Fsp : vloc }.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {LS : lib_shape}.
Context {SK : YI16.sink_head}.

Section g.
(* The generic section: segs, B, the meter, the walk's constants and the image's table are explicit arguments of
   every definition, so each name's argument order is the one written here and the asan-ubsan twin instantiates the
   same names. *)
Definition u8s (l : list byte) : list Z := map (fun x : byte => bv_unsigned x) l.
Definition sx16 (v : Z) : Z := if v <? 32768 then v else v - 65536.

Definition vat (segs : list Segment) (sp1 : Z) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (l : vloc) (v : Z) : Prop :=
match l with
| VReg r => getr regs r = w64 v
| VSpill off => rdword (aview segs (w_H W) mem) (sp1 + off) = Some v
end.

(* ---- the entry facts every cut keeps.  They are the contract's pre minus the input list and the leaf. ---- *)
Definition sc_base0 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk)
(ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(p n T : Z) : Prop :=
afn_pre segs B (sw_stk WK) ly S W regs mem md [] /\
raZ regs = sw_ra WK /\ getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = sw_empty WK) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
frames S = [] /\ st_nev S + sw_ev WK <= EV_MAX /\ blocks_bytes S + sw_live WK <= LIVE_MAX /\
arodata_okS segs B (sw_rlo WK) (sw_rhi WK) (aview segs (w_H W) mem) /\
scene_sink_none segs (sw_sink WK) (mrestrict (w_H W) mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\ Fs.fs_sorted (m_fs md) = true /\
(* the trailer's shadow is not here: see sc_img *)
mo_ok MT S T.
Definition sc_base (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (cx : rtcx segs) : Prop :=
sc_base0 segs B MT WK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_T cx) /\
c_sp1 cx = 32 * ((spZ (c_regs cx) - 224) / 32).

(* ---- the journal from the entry state to the cut.  own is exactly the entry's fake frame: every callee returns
   through apost_base, whose own list is empty (SceneBase.v), and the intrinsics keep own. ---- *)
Definition sc_j (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) (cx : rtcx segs)
(ly3 : alayout) (S3 : astate) (W3 : world segs) (mem3 : word -> option byte) (md3 : Model) (ev : Z) : Prop :=
ajournal segs B (sw_stk WK) (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(sg_cid IM, c_fpos cx)] ly3 S3 W3 mem3 md3 ev /\
frames S3 = [(sg_cid IM, c_fpos cx)] /\ mo_le MT (c_S cx) S3 (c_T cx).

(* ---- the fake frame: its bytes and its shadow window are present, and the flag word still points at the flag.
   These are the facts a lane needs to re-add the frame and frame-shadow regions (see the header). ---- *)
Definition sc_F (segs : list Segment) (IM : sgeom) (cx : rtcx segs) : Z := rt_F (sg_cid IM) cx.
Definition sc_frame (segs : list Segment) (IM : sgeom) (cx : rtcx segs) (W3 : world segs)
(mem3 : word -> option byte) : Prop :=
rdword (aview segs (w_H W3) mem3) (sc_F segs IM cx + fs_frame_bytes (sg_cid IM) - 8)
= Some (rt_FL (sg_cid IM) cx) /\
(forall a, sc_F segs IM cx <= a < sc_F segs IM cx + fs_frame_bytes (sg_cid IM) -> apresent (w_H W3) mem3 a) /\
(forall a, shadow_addr (sc_F segs IM cx) <= a < shadow_addr (sc_F segs IM cx) + fs_frame_bytes (sg_cid IM) / 8 ->
apresent (w_H W3) mem3 a).
(* ---- the 13 callee-saved words of the entry's caller, in the real-stack save area [sp0 - 104, sp0): the prologue
   stores ra, s0 .. s11 at sp0 - 8, sp0 - 16, .., sp0 - 104 (asan 0x82880-0x828b0, asan-ubsan 0x828ac-0x828dc, the
   same offsets) and the epilogue reloads them (asan 0x83088-0x830b8, asan-ubsan 0x831c4-0x831f4).  They are live
   at every cut and no journal clause keeps stack-window bytes, so every cut carries them; S6 needs them for
   aregs_preserved and the return to RA. ---- *)
Definition sc_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition sc_saves (segs : list Segment) (cx : rtcx segs) (W3 : world segs) (mem3 : word -> option byte) : Prop :=
forall j, 0 <= j < 13 ->
rdword (aview segs (w_H W3) mem3) (spZ (c_regs cx) - 8 - 8 * j)
= Some (bv_unsigned (getr (c_regs cx) (nth (Z.to_nat j) sc_saved_regs 0%bv))).

(* ---- frame-shadow cells, by offset from shadow_addr F ---- *)
Definition sc_shr (segs : list Segment) (IM : sgeom) (cx : rtcx segs) (W3 : world segs)
(mem3 : word -> option byte) (lo hi v : Z) : Prop :=
forall o, lo <= o < hi -> aview segs (w_H W3) mem3 (shadow_addr (sc_F segs IM cx) + o) = Some v.
Definition sc_shbg (segs : list Segment) (IM : sgeom) (cx : rtcx segs) (W3 : world segs)
(mem3 : word -> option byte) : Prop :=
Forall (fun t => sc_shr segs IM cx W3 mem3 (fst (fst t)) (snd (fst t)) (snd t)) (sg_sh_bg IM).
(* a frame object whose shadow the walk has opened: cgif's block_shadow (YG0v.v:36-39), which block_shadow_range
   (YG0v.v:61-62) turns into range_addressable for any sub-range *)
Definition sc_open (segs : list Segment) (IM : sgeom) (cx : rtcx segs) (W3 : world segs)
(mem3 : word -> option byte) (off len : Z) : Prop :=
block_shadow (aview segs (w_H W3) mem3) SHADOW_OFF (sc_F segs IM cx + off) len.

(* ---- a heap block of this walk: where it may be written, and that it is not the caller's ---- *)
Definition sc_blk_ok (segs : list Segment) (B : asyms) (WK : swalk) (cx : rtcx segs) (b n : Z) : Prop :=
4096 <= b /\ zone2 b (req_size n) /\ b + req_size n <= alloc_ceiling /\ b mod 16 = 0 /\
(forall blc lyq ownq i, In (b, n) blc -> 0 <= i < req_size n ->
awr_byte (sw_stk WK) (spZ (c_regs cx)) [] (ablocks B (c_ly cx) (c_S cx)) blc lyq ownq (b + i)) /\
aftok [] (ablocks B (c_ly cx) (c_S cx)) (b, n).

(* ---- what every cut keeps about the machine and the image: the stack pointer and the two fixed registers that
   every journal rule asks for (YC5d.v:59-61, J_StackSz.v), and the read-only bytes (the walk reads the three GOT
   words after C1, and build_scene_step reads TAIL_TRAILER's bytes).  The SHADOW of an image global is NOT here:
   it is runtime-owned (it lies in the shadow of lm_zone, YG0n.v:227), so no call keeps it
   (astack_malloc_realizes YG0d.v:298-299 keeps only bytes that are not aowned; acall_kept YCbq.v:823-834 keeps
   only addresses >= alloc_ceiling, heap blocks, image bytes and frames), and a cut that carried it could not be
   re-established after the walk's first stack-malloc.  Those facts are static facts of B instead
   (P_LLVMFuzzerTestOneInput.v's HB_Z_TT / HB_C_TT / HZS_PL / HB_C_PL), read at any state through AR. ---- *)
Definition sc_img (segs : list Segment) (B : asyms) (WK : swalk) (cx : rtcx segs)
(W3 : world segs) (mem3 : word -> option byte) (regs3 : bvmap 5 word) : Prop :=
spZ regs3 = c_sp1 cx /\ getr regs3 3 = w64 (as_gp B) /\ getr regs3 4 = w64 (as_tp B) /\
arodata_okS segs B (sw_rlo WK) (sw_rhi WK) (aview segs (w_H W3) mem3).

(* ---- the input-derived values.  `bs i` is the i-th input byte and 0 beyond the end, as the released plain
   model's lib/Prog/SceneRun.v:100 gbz has it; the entry reads at most 11 bytes (5 of the header, 6 of mac). ---- *)
Definition sc_PB (segs : list Segment) (cx : rtcx segs) (i v : Z) : Prop :=
0 <= v < 256 /\ val_mem segs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx + i) 1 v.
Definition sc_in (segs : list Segment) (cx : rtcx segs) (bs : Z -> Z) : Prop :=
forall i, 0 <= i < 11 -> 0 <= bs i < 256 /\ (i < c_n cx -> sc_PB segs cx i (bs i)) /\ (c_n cx <= i -> bs i = 0).
Definition sc_cur (segs : list Segment) (cx : rtcx segs) : Z := c_p cx + Z.min (c_n cx) 11.
Definition sc_rest (segs : list Segment) (cx : rtcx segs) : Z := c_n cx - Z.min (c_n cx) 11.
Definition sc_flags (bs : Z -> Z) : Z := bs 0.
Definition sc_u16 (bs : Z -> Z) : Z := bs 1 + 256 * bs 2.
Definition sc_step (bs : Z -> Z) : Z := sx16 (bs 3 + 256 * bs 4).
Definition sc_s7v (bs : Z -> Z) : Z := sx16 (256 * bs 4).
Definition sc_nprime (IM : sgeom) (bs : Z -> Z) : Z :=
if Z.land (bs 0) 1 =? 0 then sc_u16 bs else sg_scene_n IM.
Definition sc_nn (IM : sgeom) (bs : Z -> Z) : Z :=
if sc_nprime IM bs =? 0 then 1 else sc_nprime IM bs.
Definition sc_macb (bs : Z -> Z) : list Z := [bs 5; bs 6; bs 7; bs 8; bs 9; bs 10].
Definition sc_whole (IM : sgeom) (bs : Z -> Z) : Prop :=
Z.land (bs 0) 2 <> 0 /\ sc_nprime IM bs = sg_scene_n IM.

(* =================================================================================================================
   CUT C1 -- 0x82b78, after the E parse and the 6-turn mac loop.  own = [(8, fpos)], no heap block yet, ev = 0.
   The frame is poisoned except `mac`, which the store at 0x82b1c opened to 6 bytes.
   ================================================================================================================= *)
Definition cut_C1 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) (cx : rtcx segs)
(ly3 : alayout) (S3 : astate) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(bs : Z -> Z) : Prop :=
sc_j segs B MT WK IM cx ly3 S3 W3 mem3 md3 0 /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\ blocks_bytes S3 = blocks_bytes (c_S cx) /\
sc_frame segs IM cx W3 mem3 /\ sc_saves segs cx W3 mem3 /\ sc_shbg segs IM cx W3 mem3 /\
sc_shr segs IM cx W3 mem3 (sg_sh_blki_lo IM) (sg_sh_blki_hi IM) 0xf8 /\
sc_shr segs IM cx W3 mem3 (sg_sh_blk_lo IM) (sg_sh_blk_hi IM) 0xf8 /\
sc_open segs IM cx W3 mem3 (sg_off_mac IM) (sg_mac_n IM) /\
sc_img segs B WK cx W3 mem3 regs3 /\
sc_in segs cx bs /\
garr8 segs (mrestrict (w_H W3) mem3) (sc_F segs IM cx + sg_off_mac IM) (sc_macb bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_sp0 IM) (spZ (c_regs cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_sp1 IM) (c_sp1 cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_F IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_Fsp IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_shF IM) (shadow_addr (sc_F segs IM cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_shbase IM) SHADOW_OFF /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_blki IM) (sc_F segs IM cx + sg_off_blki IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_blk IM) (sc_F segs IM cx + sg_off_blk IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_expect IM) (sc_F segs IM cx + sg_off_expect IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_mac IM) (sc_F segs IM cx + sg_off_mac IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_shexp IM)
(shadow_addr (sc_F segs IM cx) + sg_off_expect IM / 8) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_flags IM) (sc_flags bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_u16 IM) (sc_u16 bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_rest IM) (sc_rest segs cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_cur IM) (sc_cur segs cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_step IM) (sc_step bs mod 2 ^ 64) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg1_s7v IM) (sc_s7v bs mod 2 ^ 64).

(* =================================================================================================================
   CUT C2 -- 0x82ca8, the first instruction of the B block.  One heap block (body, nn), written by the fill loop and
   then by the xor loop; its contents are an arbitrary byte list of that length, as the released plain proof has
   them (lib/Prog/SceneB.v:144-156 QBa, whose `bb` is existential).  ev = 1.
   ================================================================================================================= *)
Definition cut_C2 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) (cx : rtcx segs)
(ly3 : alayout) (S3 : astate) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(bs : Z -> Z) (body : Z) (bb : list byte) : Prop :=
sc_j segs B MT WK IM cx ly3 S3 W3 mem3 md3 1 /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(body, sc_nn IM bs)] /\
blocks_bytes S3 <= blocks_bytes (c_S cx) + req_size (sc_nn IM bs) /\
sc_blk_ok segs B WK cx body (sc_nn IM bs) /\
Z.of_nat (length bb) = sc_nn IM bs /\ garr8 segs (mrestrict (w_H W3) mem3) body (u8s bb) /\
sc_frame segs IM cx W3 mem3 /\ sc_saves segs cx W3 mem3 /\ sc_shbg segs IM cx W3 mem3 /\
sc_shr segs IM cx W3 mem3 (sg_sh_blki_lo IM) (sg_sh_blki_hi IM) 0xf8 /\
sc_shr segs IM cx W3 mem3 (sg_sh_blk_lo IM) (sg_sh_blk_hi IM) 0xf8 /\
sc_open segs IM cx W3 mem3 (sg_off_mac IM) (sg_mac_n IM) /\
sc_img segs B WK cx W3 mem3 regs3 /\
sc_in segs cx bs /\ 1 <= sc_nn IM bs <= 65535 /\
garr8 segs (mrestrict (w_H W3) mem3) (sc_F segs IM cx + sg_off_mac IM) (sc_macb bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_sp0 IM) (spZ (c_regs cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_sp1 IM) (c_sp1 cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_F IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_Fsp IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_shF IM) (shadow_addr (sc_F segs IM cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_shbase IM) SHADOW_OFF /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_blki IM) (sc_F segs IM cx + sg_off_blki IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_blk IM) (sc_F segs IM cx + sg_off_blk IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_expect IM) (sc_F segs IM cx + sg_off_expect IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_mac IM) (sc_F segs IM cx + sg_off_mac IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_shexp IM)
(shadow_addr (sc_F segs IM cx) + sg_off_expect IM / 8) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_body IM) body /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_nprime IM) (sc_nprime IM bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_Fb IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_nn IM) (sc_nn IM bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_flags IM) (sc_flags bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_step IM) (sc_step bs mod 2 ^ 64) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg2_s7v IM) (sc_s7v bs mod 2 ^ 64).

(* =================================================================================================================
   CUT C3 -- 0x82d74, the join of B's two arms, at the whole_transfer guard.  B wrote only `blk` (the frame object
   the unpoison stores 0x82cac-0x82cd0 opened) and read `body`; the heap is as at C2.  `blk`'s own bytes are dead
   from here on -- the two arms leave different contents there -- so the cut does not name them.  ev = 1.
   ================================================================================================================= *)
Definition cut_C3 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) (cx : rtcx segs)
(ly3 : alayout) (S3 : astate) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(bs : Z -> Z) (body : Z) (bb : list byte) : Prop :=
sc_j segs B MT WK IM cx ly3 S3 W3 mem3 md3 1 /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(body, sc_nn IM bs)] /\
blocks_bytes S3 <= blocks_bytes (c_S cx) + req_size (sc_nn IM bs) /\
sc_blk_ok segs B WK cx body (sc_nn IM bs) /\
Z.of_nat (length bb) = sc_nn IM bs /\ garr8 segs (mrestrict (w_H W3) mem3) body (u8s bb) /\
sc_frame segs IM cx W3 mem3 /\ sc_saves segs cx W3 mem3 /\ sc_shbg segs IM cx W3 mem3 /\
sc_shr segs IM cx W3 mem3 (sg_sh_blki_lo IM) (sg_sh_blki_hi IM) 0xf8 /\
sc_open segs IM cx W3 mem3 (sg_off_blk IM) (sg_blk_n IM) /\
sc_open segs IM cx W3 mem3 (sg_off_mac IM) (sg_mac_n IM) /\
sc_img segs B WK cx W3 mem3 regs3 /\
sc_in segs cx bs /\ 1 <= sc_nn IM bs <= 65535 /\
garr8 segs (mrestrict (w_H W3) mem3) (sc_F segs IM cx + sg_off_mac IM) (sc_macb bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_sp0 IM) (spZ (c_regs cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_sp1 IM) (c_sp1 cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_F IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_Fb IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_Fsp IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_shF IM) (shadow_addr (sc_F segs IM cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_blki IM) (sc_F segs IM cx + sg_off_blki IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_expect IM) (sc_F segs IM cx + sg_off_expect IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_mac IM) (sc_F segs IM cx + sg_off_mac IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_shexp IM)
(shadow_addr (sc_F segs IM cx) + sg_off_expect IM / 8) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_body IM) body /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_nn IM) (sc_nn IM bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_nprime IM) (sc_nprime IM bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_flags IM) (sc_flags bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg3_step IM) (sc_step bs mod 2 ^ 64).

(* =================================================================================================================
   CUT T (k) -- 0x82dc4, the head of the whole_transfer loop.  The ASan form of lib/Prog/SceneT.v:18-28 TMem at turn
   k.  The arm runs only when flags & 2 and n' = 8904, so body's length is SCENE_N and its contents are the list b
   the whole loop rebuilds.  `got` = scT_off k (lib/Prog/SceneTM.v:7), `declared` = 0 at k = 0 and SCENE_N after,
   and `again` holds b's first scT_off k bytes followed by anything.
   blk.i is POISONED at the loop head: each turn opens it at 0x82dc4-0x82dd8 and re-poisons it at 0x82e50-0x82e64,
   so `block_shadow` of blk.i is a fact INSIDE the turn, after 0x82dd8, and never at this cut.  ev = 2.
   ================================================================================================================= *)
Definition cut_T (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) (cx : rtcx segs)
(ly3 : alayout) (S3 : astate) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(bs : Z -> Z) (body again : Z) (b : list byte) (k : Z) : Prop :=
0 <= k <= sg_nturns IM /\ sc_whole IM bs /\
sc_j segs B MT WK IM cx ly3 S3 W3 mem3 md3 2 /\
ablocks B ly3 S3
= (ablocks B (c_ly cx) (c_S cx) ++ [(body, sg_scene_n IM)]) ++ [(again, sg_scene_n IM)] /\
blocks_bytes S3 <= blocks_bytes (c_S cx) + req_size (sg_scene_n IM) + req_size (sg_scene_n IM) /\
sc_blk_ok segs B WK cx body (sg_scene_n IM) /\ sc_blk_ok segs B WK cx again (sg_scene_n IM) /\
(again + sg_scene_n IM <= body \/ body + sg_scene_n IM <= again) /\
Z.of_nat (length b) = sg_scene_n IM /\ garr8 segs (mrestrict (w_H W3) mem3) body (u8s b) /\
(exists ja : list byte,
Z.of_nat (length ja) = sg_scene_n IM - scT_off k /\
garr8 segs (mrestrict (w_H W3) mem3) again (u8s (firstn (Z.to_nat (scT_off k)) b ++ ja))) /\
sc_frame segs IM cx W3 mem3 /\ sc_saves segs cx W3 mem3 /\ sc_shbg segs IM cx W3 mem3 /\
sc_shr segs IM cx W3 mem3 (sg_sh_blki_lo IM) (sg_sh_blki_hi IM) 0xf8 /\
sc_open segs IM cx W3 mem3 (sg_off_blk IM) (sg_blk_n IM) /\
sc_open segs IM cx W3 mem3 (sg_off_mac IM) (sg_mac_n IM) /\
sc_img segs B WK cx W3 mem3 regs3 /\
sc_in segs cx bs /\
garr8 segs (mrestrict (w_H W3) mem3) (sc_F segs IM cx + sg_off_mac IM) (sc_macb bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_sp0 IM) (spZ (c_regs cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_sp1 IM) (c_sp1 cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_Fsp IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_shF IM) (shadow_addr (sc_F segs IM cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_blki IM) (sc_F segs IM cx + sg_off_blki IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_srcA IM) (sc_F segs IM cx + sg_off_blki IM + 7) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_srcB IM) (sc_F segs IM cx + sg_off_blki IM + 9) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_mac IM) (sc_F segs IM cx + sg_off_mac IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_shexp IM)
(shadow_addr (sc_F segs IM cx) + sg_off_expect IM / 8) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_body IM) body /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_again IM) again /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_nprime IM) (sg_scene_n IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_got IM) (scT_off k) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_k IM) k /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_decl IM) (if k =? 0 then 0 else sg_scene_n IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_n1 IM) (sg_scene_n IM) /\
Forall (fun lv => vat segs (c_sp1 cx) W3 mem3 regs3 (fst lv) (snd lv)) (sgT_extra IM) /\
match sgT_nagain IM with
| Some l => vat segs (c_sp1 cx) W3 mem3 regs3 l (2 ^ 64 - 1 - again)
| None => True
end /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_expect IM) (sc_F segs IM cx + sg_off_expect IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_Fb IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_nn IM) (sc_nn IM bs) /\
match sgT_body2 IM with
| Some l => vat segs (c_sp1 cx) W3 mem3 regs3 l body
| None => True
end /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_f8 IM) (2 ^ 64 - 8).
(* CUT TX -- 0x82e74, the loop exit: the turn invariant at k = NTURNS, where scT_off NTURNS = SCENE_N, so `got` and
   `declared` are both SCENE_N and `again` holds b in full (lib/Prog/SceneTM.v:88 scT_again_all).  The two checks
   that follow (0x82e84, 0x82e8c) are therefore decided, not refuted. *)
Definition cut_TX (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) (cx : rtcx segs)
(ly3 : alayout) (S3 : astate) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(bs : Z -> Z) (body again : Z) (b : list byte) : Prop :=
cut_T segs B MT WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body again b (sg_nturns IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgT_got IM) (sg_scene_n IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sgTX_got2 IM) (sg_scene_n IM).

(* =================================================================================================================
   CUT C5 -- 0x82eb0, the join of the T arm and the no-T arm, before M3.  On the T arm `again` was freed, so the
   block list is a PERMUTATION of the entry's plus body, not an append.  ev <= 3 (M1, and on the T arm M2 and F1).
   ================================================================================================================= *)
Definition cut_C5 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) (cx : rtcx segs)
(ly3 : alayout) (S3 : astate) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(bs : Z -> Z) (body : Z) (bb : list byte) (ev : Z) : Prop :=
1 <= ev <= 3 /\ sc_j segs B MT WK IM cx ly3 S3 W3 mem3 md3 ev /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(body, sc_nn IM bs)]) /\
blocks_bytes S3 <= blocks_bytes (c_S cx) + req_size (sc_nn IM bs) /\
sc_blk_ok segs B WK cx body (sc_nn IM bs) /\
Z.of_nat (length bb) = sc_nn IM bs /\ garr8 segs (mrestrict (w_H W3) mem3) body (u8s bb) /\
sc_frame segs IM cx W3 mem3 /\ sc_saves segs cx W3 mem3 /\ sc_shbg segs IM cx W3 mem3 /\
sc_shr segs IM cx W3 mem3 (sg_sh_blki_lo IM) (sg_sh_blki_hi IM) 0xf8 /\
sc_open segs IM cx W3 mem3 (sg_off_blk IM) (sg_blk_n IM) /\
sc_open segs IM cx W3 mem3 (sg_off_mac IM) (sg_mac_n IM) /\
sc_img segs B WK cx W3 mem3 regs3 /\
sc_in segs cx bs /\ 1 <= sc_nn IM bs <= 65535 /\
garr8 segs (mrestrict (w_H W3) mem3) (sc_F segs IM cx + sg_off_mac IM) (sc_macb bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_sp0 IM) (spZ (c_regs cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_sp1 IM) (c_sp1 cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_F IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_Fsp IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_shF IM) (shadow_addr (sc_F segs IM cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_expect IM) (sc_F segs IM cx + sg_off_expect IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_mac IM) (sc_F segs IM cx + sg_off_mac IM) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_shexp IM)
(shadow_addr (sc_F segs IM cx) + sg_off_expect IM / 8) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_body IM) body /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_nn IM) (sc_nn IM bs) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg5_nprime IM) (sc_nprime IM bs).

(* =================================================================================================================
   CUT C6 -- 0x83020, the join of D's two arms, before F2 and F3.  Two heap blocks are live (body and before, both
   of nn bytes).  D left the frame shadow as it found it: the set_shadow_00 of `expect` at 0x82fac is undone by the
   set_shadow_f8 at 0x8301c on the same arm, and the other arm touches no shadow.  The contents of body, before and
   expect are dead from here on.  ev <= 4.
   ================================================================================================================= *)
Definition cut_C6 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) (cx : rtcx segs)
(ly3 : alayout) (S3 : astate) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(bs : Z -> Z) (body before : Z) (ev : Z) : Prop :=
2 <= ev <= 4 /\ sc_j segs B MT WK IM cx ly3 S3 W3 mem3 md3 ev /\
Permutation (ablocks B ly3 S3)
((ablocks B (c_ly cx) (c_S cx) ++ [(body, sc_nn IM bs)]) ++ [(before, sc_nn IM bs)]) /\
blocks_bytes S3 <= blocks_bytes (c_S cx) + req_size (sc_nn IM bs) + req_size (sc_nn IM bs) /\
sc_blk_ok segs B WK cx body (sc_nn IM bs) /\ sc_blk_ok segs B WK cx before (sc_nn IM bs) /\
sc_frame segs IM cx W3 mem3 /\ sc_saves segs cx W3 mem3 /\ sc_shbg segs IM cx W3 mem3 /\
sc_shr segs IM cx W3 mem3 (sg_sh_blki_lo IM) (sg_sh_blki_hi IM) 0xf8 /\
sc_open segs IM cx W3 mem3 (sg_off_blk IM) (sg_blk_n IM) /\
sc_open segs IM cx W3 mem3 (sg_off_mac IM) (sg_mac_n IM) /\
sc_img segs B WK cx W3 mem3 regs3 /\
sc_in segs cx bs /\ 1 <= sc_nn IM bs <= 65535 /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg6_sp0 IM) (spZ (c_regs cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg6_sp1 IM) (c_sp1 cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg6_F IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg6_Fsp IM) (sc_F segs IM cx) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg6_shF IM) (shadow_addr (sc_F segs IM cx)) /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg6_body IM) body /\
vat segs (c_sp1 cx) W3 mem3 regs3 (sg6_before IM) before.

(* ---- the return post: the contract's post at the leaf scene's shape gives (no I/O, a0 = 0).  The sink head and
   the shape are passed EXPLICITLY (gate 6h): left implicit, Coq could resolve them to a global instance (the
   released plain YI5b.src0_sink_head, or cgif's AE2k.tfib_sink_head) and the statement would then speak about
   another unit's sink. ---- *)
Definition sc_ret (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (cx : rtcx segs)
: world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' ev,
c' = cfg_at segs (sw_ra WK) regs' mem' md' /\
@scene_tfib_lib_post_x rc SK segs (sw_sink WK) (sw_ev WK) (sw_stk WK) B MT (sw_xn WK)
(c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx)
(LL 0 (m_fs (c_md cx)) []) ly' S' W' regs' mem' md' ev.

(* ---- "from this cut, the rest of the walk realizes POST" ---- *)
Definition sc_from_C1 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom)
(cx : rtcx segs) (POST : world segs -> config -> Prop) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3 bs,
cut_C1 segs B MT WK IM cx ly3 S3 W3 regs3 mem3 md3 bs ->
SRr segs W3 (cfg_at segs (sg_pc_c1 IM) regs3 mem3 md3) POST.
Definition sc_from_C2 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom)
(cx : rtcx segs) (POST : world segs -> config -> Prop) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3 bs body bb,
cut_C2 segs B MT WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body bb ->
SRr segs W3 (cfg_at segs (sg_pc_c2 IM) regs3 mem3 md3) POST.
Definition sc_from_C3 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom)
(cx : rtcx segs) (POST : world segs -> config -> Prop) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3 bs body bb,
cut_C3 segs B MT WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body bb ->
SRr segs W3 (cfg_at segs (sg_pc_c3 IM) regs3 mem3 md3) POST.
Definition sc_from_T (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom)
(cx : rtcx segs) (POST : world segs -> config -> Prop) (k : Z) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3 bs body again b,
cut_T segs B MT WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body again b k ->
SRr segs W3 (cfg_at segs (sg_pc_t IM) regs3 mem3 md3) POST.
Definition sc_from_TX (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom)
(cx : rtcx segs) (POST : world segs -> config -> Prop) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3 bs body again b,
cut_TX segs B MT WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body again b ->
SRr segs W3 (cfg_at segs (sg_pc_tx IM) regs3 mem3 md3) POST.
Definition sc_from_C5 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom)
(cx : rtcx segs) (POST : world segs -> config -> Prop) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3 bs body bb ev,
cut_C5 segs B MT WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body bb ev ->
SRr segs W3 (cfg_at segs (sg_pc_c5 IM) regs3 mem3 md3) POST.
Definition sc_from_C6 (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom)
(cx : rtcx segs) (POST : world segs -> config -> Prop) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3 bs body before ev,
cut_C6 segs B MT WK IM cx ly3 S3 W3 regs3 mem3 md3 bs body before ev ->
SRr segs W3 (cfg_at segs (sg_pc_c6 IM) regs3 mem3 md3) POST.

(* =================================================================================================================
   THE SEVEN SEGMENT STATEMENTS.  Each is "the next cut carries POST -> this cut carries POST", so a lane proving
   one segment takes the other lanes' statements as Section hypotheses and never sees their proofs.
   ================================================================================================================= *)
(* S0: the prologue, the class-8 stack malloc at 0x828ec, the frame header, the whole frame poison (including
   __asan_set_shadow_f8 at 0x829e0), the E input parse and the 6-turn mac loop with its unpoison store 0x82b1c.
   S0 also chooses the frame position, so its continuation is quantified over it, as the donor's A/ACez.v:46-55
   tfib_lib_A_seg quantifies over fpos / sp1 / E0. *)
Definition seg_S0_stmt (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n T (POST : world segs -> config -> Prop),
sc_base0 segs B MT WK ly S W regs mem md p n T ->
(forall fpos E0,
sc_from_C1 segs B MT WK IM (mkRTCX segs ly S W regs mem md p n fpos (32 * ((spZ regs - 224) / 32)) E0 T) POST) ->
SRr segs W (cfg_at segs (sw_entry WK) regs mem md) POST.
(* S1: n' and n'' (0x82b80-0x82b98), the malloc at 0x82b9c, the fill loop over reac_scene_placeholder and the xor
   loop over the rest of the input. *)
Definition seg_S1_stmt (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) : Prop :=
forall cx POST, sc_base segs B MT WK cx ->
sc_from_C2 segs B MT WK IM cx POST -> sc_from_C1 segs B MT WK IM cx POST.
(* S2: the B block: the blk unpoison 0x82cac-0x82cd0, __asan_memset 0x82ce0, reac_ctrl_build_scene_step 0x82cfc, its
   result check 0x82d28, the 34-turn "changed" loop and check_step 0x82d6c. *)
Definition seg_S2_stmt (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) : Prop :=
forall cx POST, sc_base segs B MT WK cx ->
sc_from_C3 segs B MT WK IM cx POST -> sc_from_C2 segs B MT WK IM cx POST.
(* S3: ONE whole_transfer turn, 0x82dc4 .. 0x82e70: the blk.i unpoison, reac_ctrl_build_scene_step 0x82dec, the
   declared / n_k reads, the got bound 0x82e20, check_step 0x82e30, __asan_memcpy 0x82e4c into again + got, and the
   blk.i re-poison.  The turn ends at the head of turn k+1, or at the loop exit when k + 1 = NTURNS. *)
Definition seg_S3_turn_stmt (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) : Prop :=
forall cx POST k, sc_base segs B MT WK cx -> 0 <= k < sg_nturns IM ->
(k + 1 < sg_nturns IM -> sc_from_T segs B MT WK IM cx POST (k + 1)) -> sc_from_TX segs B MT WK IM cx POST ->
sc_from_T segs B MT WK IM cx POST k.
(* S4: all of T outside one turn: the guard 0x82d74-0x82d84, the malloc at 0x82d90, the loop entry at k = 0, the
   closure of the loop by induction over S3, the got / declared checks 0x82e84 and 0x82e8c, the bcmp 0x82e9c and the
   free 0x82ea8; and the no-T arm, which jumps straight to C5. *)
Definition seg_S4_stmt (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) : Prop :=
forall cx POST, sc_base segs B MT WK cx ->
(forall k, 0 <= k < sg_nturns IM ->
(k + 1 < sg_nturns IM -> sc_from_T segs B MT WK IM cx POST (k + 1)) -> sc_from_TX segs B MT WK IM cx POST ->
sc_from_T segs B MT WK IM cx POST k) ->
sc_from_C5 segs B MT WK IM cx POST -> sc_from_C3 segs B MT WK IM cx POST.
(* S5: the malloc at 0x82eb4 and the D block: memcpy 0x82ee0, reac_ctrl_scene_set_mac 0x82ef4, the bcmp chain, the
   two reac_ctrl_scene_build calls, and on the r = 0 arm the expect build (set_shadow_00 0x82fac, memset 0x82fc4,
   the three tag stores, memcpy 0x82ff8, bcmp 0x8300c, set_shadow_f8 0x8301c). *)
Definition seg_S5_stmt (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) : Prop :=
forall cx POST, sc_base segs B MT WK cx ->
sc_from_C6 segs B MT WK IM cx POST -> sc_from_C5 segs B MT WK IM cx POST.
(* S6: the two frees 0x83024 and 0x8302c, the re-poison 0x83030-0x83048, the release magic 0x83058,
   __asan_stack_free_8 0x8306c, a0 = 0 and the epilogue. *)
Definition seg_S6_stmt (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom) : Prop :=
forall cx, sc_base segs B MT WK cx ->
sc_from_C6 segs B MT WK IM cx (sc_ret segs B MT WK cx).

(* The top composition: S0 ; S1 ; S2 ; S4[S3] ; S5 ; S6 = the entry contract.  HLIBK is the shape's leaf equation;
   for scene_shape it is LIBK pl fs K = K (LL 0 fs []), because this harness does no I/O (HAND1-PLAN.md section
   4.2).  No other premise is needed: the composition applies S0 at POST := sc_ret, and turns sc_ret into the
   contract's K through the contract's own third premise, as the donor's A/ACfj.v:180-207 lx_leaf_fail and
   A/ACfj.v:242-257 do. *)
Definition llvmf_compose_stmt (segs : list Segment) (B : asyms) (MT : ameter_ops)
(WK : swalk) (IM : sgeom) : Prop :=
(forall (pl : list byte) (fs : Fs.Fs) (K : lleaf -> TSet), LIBK pl fs K = K (LL 0 fs [])) ->
seg_S0_stmt segs B MT WK IM ->
seg_S1_stmt segs B MT WK IM ->
seg_S2_stmt segs B MT WK IM ->
seg_S3_turn_stmt segs B MT WK IM ->
seg_S4_stmt segs B MT WK IM ->
seg_S5_stmt segs B MT WK IM ->
seg_S6_stmt segs B MT WK IM ->
@scene_tfib_lib_contract_x fx rc SK LS segs (sw_sink WK)
(sw_entry WK) (sw_ra WK) (sw_ev WK) (sw_live WK) (sw_stk WK) (sw_empty WK)
B MT (sw_xm WK) (sw_xn WK) (sw_rlo WK) (sw_rhi WK).
End g.
End d.

(* =================================================================================================================
   THE ASAN TABLE.  Every number is MEASURED on fuzz_scene.asan (the listing dis-LLVMF.asan.txt, 585 insns, pinned_equal);
   the register numbers are the RISC-V numbers of the registers the listing uses at that pc.  The evidence for each
   row is SEG-REVIEW-1.md.
   ================================================================================================================= *)
Definition RV_s0 : bv 5 := 8%bv.
Definition RV_s1 : bv 5 := 9%bv.
Definition RV_s2 : bv 5 := 18%bv.
Definition RV_s3 : bv 5 := 19%bv.
Definition RV_s4 : bv 5 := 20%bv.
Definition RV_s5 : bv 5 := 21%bv.
Definition RV_s6 : bv 5 := 22%bv.
Definition RV_s7 : bv 5 := 23%bv.
Definition RV_s8 : bv 5 := 24%bv.
Definition RV_s9 : bv 5 := 25%bv.
Definition RV_s10 : bv 5 := 26%bv.
Definition RV_s11 : bv 5 := 27%bv.
Definition RV_a1 : bv 5 := 11%bv.
Definition RV_a5 : bv 5 := 15%bv.
Definition RV_a6 : bv 5 := 16%bv.
Definition RV_a7 : bv 5 := 17%bv.
(* the cut pcs, as offsets in LLVMFuzzerTestOneInput *)
Definition SEG_C1_off : Z := 0x300.
Definition SEG_C2_off : Z := 0x430.
Definition SEG_C3_off : Z := 0x4fc.
Definition SEG_T_off : Z := 0x54c.
Definition SEG_TX_off : Z := 0x5fc.
Definition SEG_C5_off : Z := 0x638.
Definition SEG_C6_off : Z := 0x7a8.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
(* The frame of LLVMFuzzerTestOneInput, from the descriptor at 0x196aa:
   "4 32 34 9 blk.i:174 112 6 7 mac:214 144 34 7 blk:233 224 8904 10 expect:300".
   The frame shadow the walk never changes (sg_sh_bg), over offsets from shadow_addr F: the f1 redzone, the three f2
   gaps, the f8 run of `expect` (written by __asan_set_shadow_f8 at 0x829e0 and restored at 0x8301c) and the f3
   tail.  MEASURED: the 63 inline stores 0x82960-0x829d0, the set_shadow_f8 call and the 35 inline stores
   0x829ec-0x82a74 cover exactly [shF, shF + 0x498) = 9408 / 8 bytes.
   The poisoned cells of blk.i are [4, 9) and of blk are [0x12, 0x17): 34 bytes is four full granules and a
   two-byte one, so each object has five shadow cells. *)
Definition scene_geom_asan : sgeom := {|
sg_cid := 8; sg_frame := 9408;
sg_off_blki := 32; sg_off_mac := 112; sg_off_blk := 144; sg_off_expect := 224;
sg_blk_n := 34; sg_mac_n := 6; sg_scene_n := 8904; sg_nturns := 343;
sg_sh_bg := [(0, 4, 0xf1); (9, 0xe, 0xf2); (0xf, 0x12, 0xf2); (0x17, 0x1c, 0xf2);
(0x1c, 0x475, 0xf8); (0x475, 0x498, 0xf3)];
sg_sh_blki_lo := 4; sg_sh_blki_hi := 9; sg_sh_blk_lo := 0x12; sg_sh_blk_hi := 0x17;
sg_pc_c1 := BASE + AF_LLVMFuzzerTestOneInput + SEG_C1_off;
sg_pc_c2 := BASE + AF_LLVMFuzzerTestOneInput + SEG_C2_off;
sg_pc_c3 := BASE + AF_LLVMFuzzerTestOneInput + SEG_C3_off;
sg_pc_t := BASE + AF_LLVMFuzzerTestOneInput + SEG_T_off;
sg_pc_tx := BASE + AF_LLVMFuzzerTestOneInput + SEG_TX_off;
sg_pc_c5 := BASE + AF_LLVMFuzzerTestOneInput + SEG_C5_off;
sg_pc_c6 := BASE + AF_LLVMFuzzerTestOneInput + SEG_C6_off;
(* C1 0x82b78: s7 = F (0x828f0), s3 = shF (0x8295c), s10 = SHADOW_OFF (0x828d8), s9 = blk.i (0x82aec),
   s11 = blk (0x82af4), a5 = expect (0x82afc), a6 = flags (0x82a94), s5 = the remaining input count,
   s6 = the input cursor, s8 = the raw u16 (0x82b28), s2 = sx16(256*b4) (0x82b0c);
   spills [s1+0x20] = shF + 0x1c (0x82a7c), [s1+0x28] = F (0x82af8), [s1+0x30] = mac (0x82b20),
   [s1+0x50] = step (0x82b18). *)
sg1_F := VReg RV_s7; sg1_shF := VReg RV_s3; sg1_shbase := VReg RV_s10;
sg1_sp1 := VReg RV_s1; sg1_sp0 := VReg RV_s0;
sg1_blki := VReg RV_s9; sg1_blk := VReg RV_s11; sg1_expect := VReg RV_a5;
sg1_flags := VReg RV_a6; sg1_rest := VReg RV_s5; sg1_cur := VReg RV_s6; sg1_u16 := VReg RV_s8;
sg1_s7v := VReg RV_s2;
sg1_shexp := VSpill 0x20; sg1_Fsp := VSpill 0x28; sg1_mac := VSpill 0x30; sg1_step := VSpill 0x50;
(* C2 0x82ca8: s4 = F (0x82c20, from s7), a7 = body (0x82ba4), s8 = n' (0x82b8c or 0x82b28), s6 = the cursor,
   s7 = sx16(256*b4) (0x82c2c); s9, s11, s3, s10, s1, s0 as at C1; the spills are C1's plus
   [s1+0x18] = expect (0x82b78). *)
sg2_F := VReg RV_s4; sg2_shF := VReg RV_s3; sg2_shbase := VReg RV_s10;
sg2_sp1 := VReg RV_s1; sg2_sp0 := VReg RV_s0;
sg2_blki := VReg RV_s9; sg2_blk := VReg RV_s11; sg2_expect := VSpill 0x18;
sg2_body := VReg RV_a7; sg2_nprime := VReg RV_s8; sg2_s7v := VReg RV_s7;
sg2_shexp := VSpill 0x20; sg2_Fsp := VSpill 0x28; sg2_mac := VSpill 0x30; sg2_step := VSpill 0x50;
(* [s1+0x18] = expect and [s1+0x38] = n'' are written in S1 (0x82b78, 0x82b98) and read back at C5; nothing
   between C2 and C5 writes either, so C2 and the loop head must carry them.  F is also at [s1+0x28]. *)
sg2_Fb := VSpill 0x28; sg2_nn := VSpill 0x38;
(* flags: `sd a6,0x48(s1)` 0x82b7c, reloaded at 0x82d54 / 0x82d70 *)
sg2_flags := VSpill 0x48;
(* C3 0x82d74: s7 = F (0x82d2c) and s4 = F (0x82c20), s8 = n', s5 = step (0x82cf4), a1 = flags (0x82d54 on the
   "changed" arm, 0x82d70 on the check_step arm), s9 = blk.i, s3 = shF;
   spills [s1+0x58] = body (0x82ce8), [s1+0x38] = n'' (0x82b98), [s1+0x18] = expect, [s1+0x30] = mac,
   [s1+0x20] = shF + 0x1c, [s1+0x28] = F.  s11 and s2 are NOT in the cut: the two arms leave them different
   (s11 = blk on one arm and blk + 34 on the other), and nothing reads them again. *)
sg3_F := VReg RV_s7; sg3_Fb := VReg RV_s4; sg3_shF := VReg RV_s3;
sg3_sp1 := VReg RV_s1; sg3_sp0 := VReg RV_s0;
sg3_blki := VReg RV_s9; sg3_expect := VSpill 0x18;
sg3_nprime := VReg RV_s8; sg3_flags := VReg RV_a1; sg3_step := VReg RV_s5;
sg3_shexp := VSpill 0x20; sg3_Fsp := VSpill 0x28; sg3_mac := VSpill 0x30;
sg3_body := VSpill 0x58; sg3_nn := VSpill 0x38;
(* T 0x82dc4: s4 = got (0x82d9c, 0x82e68), s6 = k (0x82da0, 0x82e60), s9 = blk.i, s7 = blk.i + 9 (0x82db0),
   s11 = 8904 (0x82dbc), s2 = 8905 (0x82dc0), s5 = -8 (0x82db8), s3 = shF;
   spills [s1+0x40] = declared (0x82da4, 0x82e08), [s1+0x48] = blk.i + 7 (0x82dac), [s1+0x50] = again (0x82d94),
   [s1+0x58] = body, [s1+0x08] = n' (0x82d88), [s1+0x10] = F (0x82d8c), [s1+0x30] = mac,
   [s1+0x20] = shF + 0x1c.  s10 is NOT in the cut: 0x82e18 overwrites it with n_k, and no ASan check runs after
   0x82ca8, so the walk needs the runtime shadow base only up to C2. *)
sgT_got := VReg RV_s4; sgT_k := VReg RV_s6; sgT_shF := VReg RV_s3;
sgT_sp1 := VReg RV_s1; sgT_sp0 := VReg RV_s0;
sgT_blki := VReg RV_s9; sgT_srcA := VSpill 0x48; sgT_srcB := VReg RV_s7;
sgT_f8 := VReg RV_s5; sgT_n1 := VReg RV_s11;
sgT_extra := [(VReg RV_s2, 8905)]; sgT_nagain := None;
sgT_again := VSpill 0x50; sgT_body := VSpill 0x58; sgT_decl := VSpill 0x40;
sgT_nprime := VSpill 0x08; sgT_Fsp := VSpill 0x10; sgT_mac := VSpill 0x30; sgT_shexp := VSpill 0x20;
(* the loop writes only [s1+0x40] (0x82e08) among the spill slots, so these three keep their S1 / S4 values *)
sgT_expect := VSpill 0x18; sgT_Fb := VSpill 0x28; sgT_nn := VSpill 0x38; sgT_body2 := None;
(* TX: the latch's `mv s4,s8` 0x82e68 leaves got in both; the exit check `bne s8,a0` 0x82e84 reads s8 *)
sgTX_got2 := VReg RV_s8;
(* C5 0x82eb0: s8 = n' (0x82eac on the T arm, unchanged on the other), s7 = F (0x82e7c on the T arm, 0x82d2c on
   the other), s3 = shF; spills [s1+0x38] = n'', [s1+0x58] = body, [s1+0x18] = expect, [s1+0x30] = mac,
   [s1+0x20] = shF + 0x1c, [s1+0x28] = F. *)
sg5_F := VReg RV_s7; sg5_shF := VReg RV_s3; sg5_sp1 := VReg RV_s1; sg5_sp0 := VReg RV_s0;
sg5_nprime := VReg RV_s8; sg5_expect := VSpill 0x18; sg5_shexp := VSpill 0x20;
sg5_Fsp := VSpill 0x28; sg5_mac := VSpill 0x30; sg5_body := VSpill 0x58; sg5_nn := VSpill 0x38;
(* C6 0x83020: s4 = before (0x82ebc), s2 = body (0x82f08 on the r <> 0 arm, 0x83000 on the r = 0 arm), s7 = F,
   s3 = shF, [s1+0x28] = F. *)
sg6_F := VReg RV_s7; sg6_shF := VReg RV_s3; sg6_sp1 := VReg RV_s1; sg6_sp0 := VReg RV_s0;
sg6_before := VReg RV_s4; sg6_body := VReg RV_s2; sg6_Fsp := VSpill 0x28 |}.
End a.

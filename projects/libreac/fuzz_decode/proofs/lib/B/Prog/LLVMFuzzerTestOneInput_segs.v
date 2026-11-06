(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segs: the INTERFACE of the image-B (asan-ubsan) walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput. It holds three things and no stepping:
   1. a state predicate at each of the walk's cut points, named llvm_b_st_<offset from DEC_A_LLVMF>;
   2. the nine segment statements llvm_b_<group>_stmt, each "from the previous cut point's state, the machine
      SRr-realizes the next cut point's state", over the callee contracts that segment discharges;
   3. the composition dec_llvmf_holds_of_segs, proved: the nine statements give dec_llvmf_holds_stmt
      (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:212-246), in cgif_file_fuzzer's lib/A/ACfj.v:230-259 form
      (SRr_bind / SRr_mono / srz_enter, the last copied here as dec_srz_enter from cgif lib/A/ACfh.v:47).
   The file is image A's twin, lib/A/Prog/LLVMFuzzerTestOneInput_segs.v (a working branch
   a33c9308971), in the same order and with the same names, llvm_a_ / dec_a_ read llvm_b_ / dec_b_.

   The cut points, decoded from the audited listing lib/B/Prog/DecodeBList.v (slot k at offset 4 * k):

     llvm_b_entry   +0x000..+0x070  ends at jal __asan_stack_malloc_0     post at +0x074
     llvm_b_early   +0x074..+0x278  ends at jal malloc #1                 post at +0x27c (early edge +0x104 -> +0xae0)
     llvm_b_copy    +0x27c..+0x414  ends at jal malloc #2                 post at +0x418
     llvm_b_inspect +0x418..+0x5c8  ends at jal reac_decode               post at +0x5cc
     llvm_b_crt1    +0x5cc..+0x6ec  ends at jal reac_decode_plain_le      post at +0x6f0
     llvm_b_cmp     +0x6f0..+0x83c  ends at jal reac_upstream_channels    post at +0x840
     llvm_b_up      +0x840..+0x968  ends at jal reac_upstream_decode #3   post at +0x96c
     llvm_b_exit    +0x96c..+0xb80  ends at ret                           post = the slot post (second entry +0xae0)
     llvm_b_trap    +0xb84..+0xca0  no statement: every branch into it is refuted inside the segment that holds it

   +0xb84 is the UBSan trap (`unimp`, reached by 35 guarded branches, listed at each segment below), +0xb88 the
   abort tail (__asan_handle_no_return; abort), +0xb94..+0xca0 the ASan report slow paths. Every __asan_report_*
   RETURNS, so the four in-line report calls (+0x64c, +0x75c, +0x954, +0xa74) and every out-of-line report block are
   refuted, never treated as terminal.

   Where image B differs from image A (the same C code; the asan-ubsan build allocates registers differently):
   - B keeps the fake frame in caller-saved registers a6 / a7 (frame) and t0 (its shadow address) from +0x074 to
     the size test, then spills them to 16(s1) / 0(s1) / 8(s1) (+0x10c, +0x258, +0x110) and reloads them only at
     +0xacc..+0xadc for the teardown. So dec_b_fr (registers a6 / a7 / t0) holds at +0x104 and +0xae0 only, and
     the body states carry dec_b_frs (those three spill slots) where image A carries its s3 / s5 / s11.
   - The size is in s3 and the length in s4 (A: s4 / s10); the copy is in s11 (A: s4); the spill area at s1 has
     B's own offsets (24 len, 32 shadow base, 40 copy, 56 / 64 / 72 the geometry, 80 copy + 50, 88 buffer).
   - B's early join is +0xae0, inside the teardown (after the re-poison of the local), where A's is +0x9a8.
   - The 35 UBSan guards into +0xb84 exist only in B.

   Where each predicate comes from: the released UBSAN walk of the same C function at 568db058c1d, clause by clause:
     lib/U/Prog/fd_segments_c.v:39-55  fd_inv        -> dec_b_core (the journal, the frame, sp, gp/tp, the payload)
     lib/U/Prog/fd_segments_c.v:56-61  fd_mode_ok    -> dec_b_mode_ok
     lib/U/Prog/fd_segments_c.v:66-77  fd_seg_post   -> the shape of every llvm_b_st_*
     lib/U/Prog/fd_entry.v:130-141     fd_entry_post -> llvm_b_st_27c
     lib/U/Prog/fd_segments_c.v:78-80  fd_up_regs    -> llvm_b_st_840
     lib/U/Prog/fd_segments_c.v:81     fd_exit_regs  -> llvm_b_st_ae0
     lib/U/Prog/fd_exit.v:17-22        llvm_saved_cells -> dec_b_saved (13 words)
     lib/U/Prog/LLVMFuzzerTestOneInput_early.v:15-16,60  llvm_early_cond / llvm_early -> llvm_b_st_104 and
                                                        llvm_b_early_ret_stmt (the `2 ^ 26 <= size` edge)
   What the released posts do not have, because only the ASan images have it: the shadow base, the ASan frame
   record with its redzone poison and the eight shadow bytes, the fake frame and its spills, and the caller-journal
   facts (ajournal / own / mo_ok / mo_le) this image's contract is written in.

   The C-level facts are the leaves' own models (lib/B/Prog/reac_*_c.v), which the leaf contracts
   lib/B/Prog/reac_*_cg.v state their results in; no C semantics is restated here. *)
From Stdlib Require Import ZArith NArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YI00 YI04 YG0v YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_frame_is_reac_cg reac_frame_clean_len_cg
  reac_frame_counter_cg reac_frame_inspect_cg reac_decode_cg reac_decode_plain_le_cg reac_upstream_channels_cg
  reac_upstream_decode_cg check_braid_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_decode_c reac_decode_plain_le_c
  reac_frame_inspect_c reac_upstream_channels_c reac_upstream_decode_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module DShape := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.DecodeShape.
Module CDec := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_c.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_c.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_inspect_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_channels_c.
Module CUp := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_decode_c.
Module LIsReac := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_is_reac_cg.
Module LCleanLen := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_clean_len_cg.
Module LCounter := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_counter_cg.
Module LInspect := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_inspect_cg.
Module LDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_cg.
Module LPlainLe := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_cg.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_channels_cg.
Module LUpDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_decode_cg.
Module LCheckBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_cg.

(* The shadow bytes this function writes for its own frame; the listing's own immediates
   (li a0,-15 / li a0,-8 / li a4,-13 / li a0,-11 at +0x0e8 / +0x0d0 / +0x0b4 / +0xaf0). *)
Definition DEC_SH_LEFT : Z := 0xf1.
Definition DEC_SH_MID : Z := 0xf8.
Definition DEC_SH_RIGHT : Z := 0xf3.
Definition DEC_SH_UAR : Z := 0xf5.
(* The fill byte the harness writes before every decode (memset at +0x5b4 / +0x6d4 / +0x8d8). *)
Definition DEC_FILL : Z := 0xa5.
(* The frame class this function's __asan_stack_malloc_0 call allocates (li a0,64 at +0x6c): class 0, 64 bytes. *)
Definition DEC_FCLASS : Z := 0.
(* The 13 callee-saved words the prologue stores (+0x008..+0x038) and the epilogue reloads (+0xb48..+0xb78),
   as (byte below the entry sp, register number); the released llvm_saved_cells of lib/U/Prog/fd_exit.v:17-22
   at image B's frame of 224 bytes (the same offsets as image A's). *)
Definition dec_b_saved_at : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24); (88, 25);
   (96, 26); (104, 27)].
(* The three bytes fuzz_in / fuzz_u8 take off the input before fuzz_take, and what is left for fuzz_dup:
   the released en_k / en_len of lib/U/Prog/LLVMFuzzerTestOneInput_c.v, restated here so that no plain-image
   file is imported into lib/B. In B the body pointer s8 = p + dec_b_u n and the length s4 = dec_b_len n at +0x254
   on all four size paths (n = 0, 1, 2, >= 3). *)
Definition dec_b_u (n : Z) : Z := Z.min n 3.
Definition dec_b_len (n : Z) : Z := Z.max (n - 3) 0.
(* The mode geometry the dispatch reads and the output length the harness asks malloc for:
   out_len = nch * ns * 3 when both are positive, else 0, and olen = out_len ? out_len : 1
   (+0x3c8..+0x40c: s6 = prod, s8 = fits0, s10 = olen); the released fd_olen of lib/U/Prog/fd_down.v:25
   (1 <= fd_olen <= 48387). *)
Definition dec_b_prod (nch ns : Z) : Z := ((nch mod 2 ^ 32) * (ns mod 2 ^ 32)) mod 2 ^ 64.
Definition dec_b_fits0 (nch ns : Z) : Z := if (0 <? nch) && (0 <? ns) then 1 else 0.
Definition dec_b_olen (nch ns : Z) : Z := if (0 <? nch) && (0 <? ns) then 3 * nch * ns else 1.
(* The upstream output length: out_len = nch * 12 * 3 when nch > 0, else 0, and olen = out_len ? out_len : 1
   (+0x8a4..+0x8bc, s8); the released up_olen of lib/U/Prog/fd_up.v:38 (1 <= up_olen <= 1440). *)
Definition dec_b_uolen (nch : Z) : Z := if 0 <? nch then 36 * nch else 1.

(* ------------------------------------------------------------------ *)
(* 1. The meter and event ladders                                       *)
(* ------------------------------------------------------------------ *)

(* What the rest of the walk still spends, from each cut point. The sizes are the released bounds:
   the payload copy at most n bytes, the decode buffer at most 48387 (fd_down.v:25 olen_bounds), the upstream
   buffer at most 1440 (fd_up.v:38 up_olen_bounds), and each check_round_trip at most dec_crt_cost_max
   (LLVMFuzzerTestOneInput_cg.v:206-207). *)
Definition dec_rest_96c (MT : ameter_ops) : Z := dec_crt_cost_max MT + mo_free MT + mo_free MT.
Definition dec_rest_840 (MT : ameter_ops) : Z := mo_malloc MT 1440 + dec_rest_96c MT.
Definition dec_rest_6f0 (MT : ameter_ops) : Z := mo_free MT + dec_rest_840 MT.
Definition dec_rest_5cc (MT : ameter_ops) : Z := dec_crt_cost_max MT + dec_rest_6f0 MT.
Definition dec_rest_418 (MT : ameter_ops) : Z := dec_rest_5cc MT.
Definition dec_rest_27c (MT : ameter_ops) : Z := mo_malloc MT 48387 + dec_rest_418 MT.
Definition dec_rest_074 (MT : ameter_ops) (n : Z) : Z := mo_malloc MT n + dec_rest_27c MT.
Definition dec_rest_ae0 (MT : ameter_ops) : Z := 0.
(* What the walk has spent at each cut point. *)
Definition dec_spent_074 (MT : ameter_ops) : Z := 0.
Definition dec_spent_27c (MT : ameter_ops) (n : Z) : Z := mo_malloc MT n.
Definition dec_spent_418 (MT : ameter_ops) (n : Z) : Z := dec_spent_27c MT n + mo_malloc MT 48387.
Definition dec_spent_5cc (MT : ameter_ops) (n : Z) : Z := dec_spent_418 MT n.
Definition dec_spent_6f0 (MT : ameter_ops) (n : Z) : Z := dec_spent_5cc MT n + dec_crt_cost_max MT.
Definition dec_spent_840 (MT : ameter_ops) (n : Z) : Z := dec_spent_6f0 MT n + mo_free MT.
Definition dec_spent_96c (MT : ameter_ops) (n : Z) : Z := dec_spent_840 MT n + mo_malloc MT 1440.
Definition dec_spent_ae0 (MT : ameter_ops) (n : Z) : Z := dec_spent_96c MT n + dec_rest_96c MT.

(* spent + rest is the cost the statement's premise bounds by XL (LLVMFuzzerTestOneInput_cg.v:208-210, :244). *)
Lemma dec_cost_ladder : forall (MT : ameter_ops) (n : Z),
  dec_spent_074 MT + dec_rest_074 MT n = dec_llvmf_cost MT n /\
  dec_spent_27c MT n + dec_rest_27c MT = dec_llvmf_cost MT n /\
  dec_spent_418 MT n + dec_rest_418 MT = dec_llvmf_cost MT n /\
  dec_spent_5cc MT n + dec_rest_5cc MT = dec_llvmf_cost MT n /\
  dec_spent_6f0 MT n + dec_rest_6f0 MT = dec_llvmf_cost MT n /\
  dec_spent_840 MT n + dec_rest_840 MT = dec_llvmf_cost MT n /\
  dec_spent_96c MT n + dec_rest_96c MT = dec_llvmf_cost MT n /\
  dec_spent_ae0 MT n + dec_rest_ae0 MT = dec_llvmf_cost MT n.
Proof.
intros MT n. unfold dec_spent_ae0, dec_spent_96c, dec_spent_840, dec_spent_6f0, dec_spent_5cc, dec_spent_418,
  dec_spent_27c, dec_spent_074, dec_rest_074, dec_rest_27c, dec_rest_418, dec_rest_5cc, dec_rest_6f0,
  dec_rest_840, dec_rest_96c, dec_rest_ae0, dec_llvmf_cost.
repeat split; ring.
Qed.

(* The model events of the walk: one per malloc and free of this function, six per check_round_trip
   (check_round_trip_cg.v DEC_CRT_EV); eighteen in all, far inside DEC_EV_LIB = 2000. *)
Definition dec_ev_074 : Z := 0.
Definition dec_ev_27c : Z := 1.
Definition dec_ev_418 : Z := 2.
Definition dec_ev_5cc : Z := 2.
Definition dec_ev_6f0 : Z := 8.
Definition dec_ev_840 : Z := 9.
Definition dec_ev_96c : Z := 10.
Definition dec_ev_ae0 : Z := 18.
Lemma dec_ev_in_lib : dec_ev_ae0 <= DEC_EV_LIB.
Proof. unfold dec_ev_ae0, DEC_EV_LIB. lia. Qed.
Section seg. Context {rc : YM05.RunCeil}.
(* The Section of lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:171-185, variable for variable, so that
   dec_llvmf_holds_stmt can be stated here at the same arguments. *)
Local Abbreviation tfib_sink_head := dec_B_sink_head.          (* cgif lib/YE2k.v:44 at fuzz_decode's sink head *)
Variable asink_syms : Type.                                    (* a Theorem Labs lane's lib/Reusable/YE00.v:32 *)
Variable tfib_K : asink_syms.                                  (* a Theorem Labs lane's lib/A/AE2k.v:43 form *)
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The frozen statement (a Theorem Labs lane 774ffa170e8) states HSINK_KEPT / HMETA_KEPT as premises of dec_llvmf_holds_stmt
   (the composition intros them) and puts rom_view into the slot pre dec_lib_pre_x; HROM is that conjunct. *)
Lemma HROM : forall (fx : YK11.FPState) ly S (W : world segs) regs mem md p n pl M,
  @dec_lib_pre_x fx rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
    regs ly S W mem md p n pl M ->
  rom_view segs W mem.
Proof. intros * HP. unfold dec_lib_pre_x in HP. decompose [and] HP. assumption. Qed.

(* ------------------------------------------------------------------ *)
(* 0. The entry context, carried by every predicate                     *)
(* ------------------------------------------------------------------ *)

(* Everything the entry fixes and the whole walk reads: the caller's configuration, the slot's arguments, and the
   one value the prologue invents, the fake-stack frame position fpos (cgif's rtcx, lib/A/ACf5.v:45-48; the
   released walk carries the same data as the explicit arguments stk/L0/A0/regs0/mem0/md0 of
   lib/U/Prog/fd_entry.v:130). *)
Record dctx := mkDCtx {
  d_fx : YK11.FPState;
  d_ly : alayout;
  d_S : astate;
  d_W : world segs;
  d_regs : bvmap 5 word;
  d_mem : word -> option byte;
  d_md : Model;
  d_p : Z;
  d_n : Z;
  d_pl : list byte;
  d_M : Z;
  d_fpos : Z }.

Definition d_sp0 (cx : dctx) : Z := spZ (d_regs cx).
(* sp after `addi sp,sp,-224` (+0x000) and `andi sp,sp,-32` (+0x040); s1 is set from it at +0x044 and never
   rewritten. cgif's c_sp1, lib/A/ACf5.v:59. *)
Definition d_sp1 (cx : dctx) : Z := 32 * ((d_sp0 cx - 224) / 32).
(* The fake frame of class 0 and its flag byte; cgif's rt_F / rt_FL, lib/A/ACf5.v:64-65. *)
Definition d_F (cx : dctx) : Z := frame_addr (d_ly cx) DEC_FCLASS (d_fpos cx).
Definition d_FL (cx : dctx) : Z := flag_addr (d_ly cx) DEC_FCLASS (d_fpos cx).
(* t0 = (a7 >> 3) + s2 at +0x0d4. *)
Definition d_SH (cx : dctx) : Z := shadow_addr (d_F cx).
(* The bytes fuzz_dup copies, i.e. what every callee of this function sees as the frame. *)
Definition d_body (cx : dctx) : list byte := skipn (Z.to_nat (dec_b_u (d_n cx))) (d_pl cx).
(* The meter budget of one call. *)
Definition d_T (cx : dctx) : Z := XL (d_n cx).

(* The slot's pre at the entry configuration (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:104-118); cgif's rt_base,
   lib/A/ACf5.v:52. Every segment but the entry takes it as a premise, as cgif's rt_from does. *)
Definition dec_b_base (cx : dctx) : Prop :=
  @dec_lib_pre_x (d_fx cx) rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
    (d_regs cx) (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) (d_p cx) (d_n cx) (d_pl cx) (d_M cx).

(* The entry's read-only view (HROM at this context). Every segment after the entry takes it beside
   dec_b_base and carries it to its own call sites through the journal's image clause
   (lib/Reusable/YCbq.v:362); no cut-point predicate repeats it. *)
Definition dec_b_rom (cx : dctx) : Prop := rom_view segs (d_W cx) (d_mem cx).


(* ------------------------------------------------------------------ *)
(* 2. The pieces every cut point shares                                 *)
(* ------------------------------------------------------------------ *)

(* The 13 saved words are still the caller's: what the epilogue reloads at +0xb48..+0xb78, and so what makes
   aregs_preserved true at the return. The released lib/U/Prog/fd_entry.v:141 carries the same words as
   `rw_cells rsegs mem (spZ regs0 - 116) (.. llvm_saved_cells regs0)`. *)
Definition dec_b_saved (cx : dctx) (r : reader) : Prop :=
  Forall (fun o : Z * Z => rdword r (d_sp0 cx - fst o) = Some (bv_unsigned (YK11.getr (d_regs cx) (Z_to_bv 5 (snd o)))))
    dec_b_saved_at.

(* One 8-byte slot of the realigned spill area at s1. Image B's stores: 112 (+0x100, the frame), 16 / 8 (+0x10c /
   +0x110, the fake-stack pointer and the shadow address), 0 (+0x258, the frame), 72 / 56 / 32 / 64 (+0x3d4 /
   +0x3e4 / +0x3ec / +0x3f0), 88 (+0x418), 24 / 40 (+0x434 / +0x438), 80 (+0x658), 48 (+0x7bc). The released walk
   has no counterpart: its frame is addressed off sp. *)
Definition dec_b_slot (cx : dctx) (r : reader) (off v : Z) : Prop := rdword r (d_sp1 cx + off) = Some v.

(* The frame invariant of every point of the body: the caller's journal with the one fake frame owned, the
   realigned stack, gp/tp, the saved words, the fake frame itself with the flag pointer in its last word, and the
   caller's payload block untouched. The released lib/U/Prog/fd_segments_c.v:39-55 fd_inv, clause for clause:
   MR/WF/bounded -> ajournal (which carries AR at the current state), sp facts -> spZ regs' = d_sp1,
   writable_at of the frame -> apresent of the fake frame, getr regs 4 -> gp/tp, In (frame,len)/blk_data ->
   the payload block and garr8. What fd_inv has no counterpart for is the fake frame and its flag word, which
   only the ASan images have. s0 = the entry sp from +0x03c and s1 = d_sp1 from +0x044, both kept to the
   epilogue. *)
Definition dec_b_core (cx : dctx) (ly' : alayout) (S' : astate) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
  @ajournal rc tfib_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' k /\
  frames S' = [(DEC_FCLASS, d_fpos cx)] /\
  YK11.getr regs' 8 = w64 (d_sp0 cx) /\
  YK11.getr regs' 9 = w64 (d_sp1 cx) /\
  spZ regs' = d_sp1 cx /\
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\ d_sp1 cx mod 32 = 0 /\
  YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  dec_b_saved cx (aview segs (w_H W') mem') /\
  4096 <= d_F cx /\ d_F cx mod 32 = 0 /\
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W') mem' a) /\
  rdword (aview segs (w_H W') mem') (d_F cx + 56) = Some (d_FL cx) /\
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B ly' S')) /\
  garr8 segs (rd W' mem') (d_p cx) (map (fun b : byte => bv_unsigned b) (d_pl cx)).

(* The three caller-saved registers that hold the fake frame from +0x080 to the spills and again from the
   reloads (+0xacc..+0xadc) to the epilogue: t0 (its shadow address, +0x0d4), a6 (the non-null fake-stack
   pointer, +0x074) and a7 (the frame base, +0x080). Image A keeps the same three values in s11 / s3 / s5. *)
Definition dec_b_fr (cx : dctx) (regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 5 = w64 (d_SH cx) /\ YK11.getr regs' 16 = w64 (d_F cx) /\ YK11.getr regs' 17 = w64 (d_F cx).

(* The same three values in their spill slots, which is where the body keeps them: 8(s1) the shadow address
   (+0x110), 16(s1) the fake-stack pointer (+0x10c), 0(s1) the frame (+0x258); the teardown reloads them into
   t0 / a6 / a7 at +0xacc / +0xad8 / +0xadc. Image B alone. *)
Definition dec_b_frs (cx : dctx) (r : reader) : Prop :=
  dec_b_slot cx r 0 (d_F cx) /\ dec_b_slot cx r 8 (d_SH cx) /\ dec_b_slot cx r 16 (d_F cx).

(* The eight shadow bytes of the fake frame: the left redzone the prologue writes at +0x0ec..+0x0f8, the two
   bytes of the 12-byte local (0 and 4 while it is live, written at +0x184 / +0x188 or +0x1f0 / +0x1f4; 0xf8 once
   it is poisoned, +0x0d8 / +0x0dc and again +0xad0 / +0xad4), and the right redzone at +0x0e0..+0x0e4. *)
Definition dec_b_fsh (cx : dctx) (r : reader) (b4 b5 : Z) : Prop :=
  (forall i, 0 <= i < 4 -> r (d_SH cx + i) = Some DEC_SH_LEFT) /\
  r (d_SH cx + 4) = Some b4 /\ r (d_SH cx + 5) = Some b5 /\
  (forall i, 6 <= i < 8 -> r (d_SH cx + i) = Some DEC_SH_RIGHT).

(* The mode the dispatch selected and the geometry behind it. The table modes are LOADED: the slots at +0x1a0,
   +0x21c, +0x230 and +0x23c are PLdHi, i.e. `ld s5, %lo(..)(a1)` from the 8-byte pointer word decodeb_obj 4 /
   4 / 5 / 6 (PaTable.v:56-57; the words 0x99f60 / 0x99f68 / 0x99f70 hold 0x20d60 / 0x20da0 / 0x20d80 in
   fuzz_decode.asan-ubsan, the three 12-byte tables in the read-only PT_LOAD). The fourth mode is the 12-byte
   local at a7 + 32 (+0x108, s5 = d_F + 32, its fields at +0x24 / +0x28 when the input asks custom geometry,
   +0x24c / +0x250). The released lib/U/Prog/fd_segments_c.v:56-61 fd_mode_ok, with S - FD_KEEP replaced by the
   frame's local. *)
Definition dec_b_mode_ok (cx : dctx) (W' : world segs) (mem' : word -> option byte) (mode nch ns : Z) : Prop :=
  (rdword (aview segs (w_H W') mem') (decodeb_obj 4) = Some mode \/
   rdword (aview segs (w_H W') mem') (decodeb_obj 5) = Some mode \/
   rdword (aview segs (w_H W') mem') (decodeb_obj 6) = Some mode \/
   mode = d_F cx + 32) /\
  -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
  val_mem segs (rd W' mem') (mode + 4) 4%nat (nch mod 2 ^ 32) /\
  val_mem segs (rd W' mem') (mode + 8) 4%nat (ns mod 2 ^ 32).
(* The addressability of mode + 4 .. mode + 12, which the copy segment's shadow checks at +0x3a0..+0x3c0 need,
   is NOT a state clause: for a table it comes from dec_crt_cells (the frozen statement's shadow rows, through AR's
   am_const, at every state), for the local from dec_b_fsh (granules 0 and 4). *)

(* The fill the harness leaves in a buffer no decoder wrote (memset 0xa5, then a refused call writes nothing). *)
Definition dec_b_filled (W' : world segs) (mem' : word -> option byte) (q len : Z) : Prop :=
  forall i, 0 <= i < len -> aview segs (w_H W') mem' (q + i) = Some DEC_FILL.

(* ------------------------------------------------------------------ *)
(* 3. The state at each cut point                                       *)
(* ------------------------------------------------------------------ *)

(* +0x074 — the return of __asan_stack_malloc_0 (+0x070). a0 is the frame the call returned; a6/a7/t0 are not
   set yet (they are written at +0x074, +0x080 and +0x0d4), the frame's shadow is still all zero (the poison is
   at +0x0d8..+0x0f8), and nothing is allocated or metered yet. s2 is the shadow base (+0x060), s3 the size
   (+0x048), s8 the data pointer (+0x064).
   Follows: lib/U/Prog/fd_segments_c.v:66-77 fd_seg_post's shape; there is no released counterpart for the call
   itself (the released images have no fake stack): the post is YG0d.v astack_malloc_realizes'. *)
Definition llvm_b_st_074 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x074)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' dec_ev_074 /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) /\
    mo_le MT (d_S cx) S' (dec_spent_074 MT) /\ mo_ok MT S' (dec_rest_074 MT (d_n cx)) /\
    YK11.getr regs' 10 = w64 (d_F cx) /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 19 = w64 (d_n cx) /\
    YK11.getr regs' 24 = w64 (d_p cx) /\
    zero_shadow (aview segs (w_H W') mem') SHADOW_OFF (d_F cx) 64.

(* +0x104 — the early edge only: the machine is at the `bnez a0` of the size test (+0x0fc..+0x104) and a0, the
   top 38 bits of the size, is not zero. The frame record and its poison are written, the local is still
   poisoned (its unpoison is at +0x184 / +0x1f0), 112(s1) holds the frame, and the frame is still in a6/a7/t0
   (the spills to 16(s1) / 8(s1) are at +0x10c / +0x110, after the branch).
   Follows: lib/U/Prog/LLVMFuzzerTestOneInput_early.v:15-16 llvm_early_cond (`2 ^ 26 <= u`) and :60 llvm_early.
   dec_b_base pins 0 <= n < 2 ^ 26 (LLVMFuzzerTestOneInput_cg.v:109), so this state is unreachable from the
   slot pre; the edge is kept as its own statement because the listing has it. *)
Definition llvm_b_st_104 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x104)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' dec_ev_074 /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) /\
    mo_le MT (d_S cx) S' (dec_spent_074 MT) /\ mo_ok MT S' (dec_rest_074 MT (d_n cx)) /\
    dec_b_fr cx regs' /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 10 = w64 (Z.shiftr (d_n cx) 26) /\
    2 ^ 26 <= d_n cx /\
    dec_b_fsh cx (aview segs (w_H W') mem') DEC_SH_MID DEC_SH_MID /\
    dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x27c — the return of malloc #1 (+0x278), the payload copy fuzz_dup asks for. a0 is the new block; the
   dispatch has run, so s4 is the copy's length, s8 the body pointer, s5/s7/s6 the mode and its two fields, and
   the frame's local holds `custom` (the three sw at +0x194..+0x19c or +0x204..+0x20c). The frame is in its three
   spill slots. The copy is not filled yet: __asan_memcpy is at +0x298. The two UBSan guards on the body
   pointer (+0x260, +0x270) have been refuted.
   Follows: lib/U/Prog/fd_entry.v:130-141 fd_entry_post — its `getr regs 9 = len`, `getr regs 25 = frame` and
   `getr regs 19 = mode` are s4, s11 (from +0x27c on) and s5 here, its fd_mode_ok is dec_b_mode_ok, and its
   `(forall a k, In (a,k) (blocks L0 A0) -> a <> frame)` is the appended block of amalloc04_rule
   (lib/Reusable/YC5d.v:73). *)
Definition llvm_b_st_27c (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x27c)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' dec_ev_27c /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] /\
    4096 <= res /\
    mo_le MT (d_S cx) S' (dec_spent_27c MT (d_n cx)) /\ mo_ok MT S' (dec_rest_27c MT) /\
    dec_b_frs cx (aview segs (w_H W') mem') /\
    YK11.getr regs' 10 = w64 res /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 19 = w64 (d_n cx) /\
    YK11.getr regs' 24 = w64 (d_p cx + dec_b_u (d_n cx)) /\
    YK11.getr regs' 20 = w64 (dec_b_len (d_n cx)) /\
    YK11.getr regs' 21 = w64 mode /\
    YK11.getr regs' 23 = w64 (mode + 4) /\
    YK11.getr regs' 22 = w64 (mode + 8) /\
    dec_b_mode_ok cx W' mem' mode nch ns /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x418 — the return of malloc #2 (+0x414), the decode buffer. The copy is filled, reac_frame_is_reac and
   reac_frame_clean_len have been called and their abort edges (+0x284, +0x314, +0x328, +0x330, +0x358, +0x39c)
   refuted, and the geometry has been read out of the mode (+0x3bc / +0x3c4: s7 = nch sign-extended, s6 = prod,
   s8 = fits0, s10 = olen) and spilled.
   Follows: lib/U/Prog/fd_down.v:67's state after `g_malloc` — the released fd_down does the same malloc with
   the same olen bounds (fd_down.v:25 olen_bounds, 1 <= olen <= 48387). *)
Definition llvm_b_st_418 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x418)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' dec_ev_418 /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++
                       [(out, dec_b_olen nch ns)] /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_418 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_418 MT) /\
    dec_b_frs cx (aview segs (w_H W') mem') /\
    YK11.getr regs' 10 = w64 out /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 27 = w64 res /\
    YK11.getr regs' 20 = w64 (dec_b_len (d_n cx)) /\
    YK11.getr regs' 21 = w64 mode /\
    YK11.getr regs' 22 = w64 (dec_b_prod nch ns) /\
    YK11.getr regs' 23 = w64 nch /\
    YK11.getr regs' 24 = w64 (dec_b_fits0 nch ns) /\
    YK11.getr regs' 26 = w64 (dec_b_olen nch ns) /\
    dec_b_mode_ok cx W' mem' mode nch ns /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    dec_b_slot cx (aview segs (w_H W') mem') 32 SHADOW_OFF /\
    dec_b_slot cx (aview segs (w_H W') mem') 56 (ns mod 2 ^ 32) /\
    dec_b_slot cx (aview segs (w_H W') mem') 64 (nch mod 2 ^ 32) /\
    dec_b_slot cx (aview segs (w_H W') mem') 72 (ns mod 2 ^ 64) /\
    dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x5cc — the return of reac_decode (+0x5c8). reac_frame_inspect and reac_frame_counter have been called and
   the frame-field checks have run, so s3 is the harness's `wellformed` (+0x504, checked against inspect's high
   half at +0x520); s2 holds `fits` (+0x5a0), the shadow base being in 32(s1) since +0x3ec; s6 is the buffer
   (+0x5a8); the buffer holds the decoder's output or is still the 0xa5 fill.
   Follows: lib/U/Prog/fd_down.v:67's state after the reac_decode leaf; the return value and the two buffer
   cases are reac_decode_cg.v's dleaf_post (decode_ok / braid_out of lib/B/Prog/reac_decode_c.v). *)
Definition llvm_b_st_5cc (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x5cc)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' dec_ev_5cc /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++
                       [(out, dec_b_olen nch ns)] /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_5cc MT (d_n cx)) /\ mo_ok MT S' (dec_rest_5cc MT) /\
    dec_b_frs cx (aview segs (w_H W') mem') /\
    YK11.getr regs' 10 = w64 (if CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns then ns else -1) /\
    YK11.getr regs' 18 = w64 (if dec_b_prod nch ns <? 481 then 1 else 0) /\
    YK11.getr regs' 19 = w64 (if CInsp.inspect_wf (dec_b_len (d_n cx)) (d_body cx) then 1 else 0) /\
    YK11.getr regs' 20 = w64 (dec_b_len (d_n cx)) /\
    YK11.getr regs' 21 = w64 mode /\
    YK11.getr regs' 22 = w64 out /\
    YK11.getr regs' 23 = w64 nch /\
    YK11.getr regs' 24 = w64 (dec_b_fits0 nch ns) /\
    YK11.getr regs' 26 = w64 (dec_b_olen nch ns) /\
    YK11.getr regs' 27 = w64 res /\
    dec_b_mode_ok cx W' mem' mode nch ns /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = true ->
       garr8 segs (rd W' mem') out
         (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns))) /\
    (CDec.decode_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = false ->
       dec_b_filled W' mem' out (dec_b_olen nch ns)) /\
    dec_b_slot cx (aview segs (w_H W') mem') 24 (dec_b_len (d_n cx)) /\
    dec_b_slot cx (aview segs (w_H W') mem') 32 SHADOW_OFF /\
    dec_b_slot cx (aview segs (w_H W') mem') 40 res /\
    dec_b_slot cx (aview segs (w_H W') mem') 56 (ns mod 2 ^ 32) /\
    dec_b_slot cx (aview segs (w_H W') mem') 64 (nch mod 2 ^ 32) /\
    dec_b_slot cx (aview segs (w_H W') mem') 72 (ns mod 2 ^ 64) /\
    dec_b_slot cx (aview segs (w_H W') mem') 88 out /\
    dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x6f0 — the return of reac_decode_plain_le (+0x6ec). The decode result has been checked (+0x5ec), the scan
   loop L1 (+0x5fc..+0x63c) has shown a refused decode left the fill, 80(s1) holds copy + 50 (+0x658),
   check_round_trip #1 (only when 0 < ns <= 12) and check_braid #1 (whenever the decode succeeded) have run, and
   __asan_memset has refilled the buffer. s2 carries the buffer (+0x6c8), s6 the length (+0x6dc), s11 the copy
   (+0x6c0).
   Follows: lib/U/Prog/fd_down.v:67 after `g_crt` and the plain_le leaf; the return value and the two buffer
   cases are reac_decode_plain_le_cg.v (plain_ok / plain_out, lib/B/Prog/reac_decode_plain_le_c.v). *)
Definition llvm_b_st_6f0 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x6f0)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' dec_ev_6f0 /\
    (* a Permutation from here on: check_round_trip #1's dec_crt_post (check_round_trip_cg.v:133) gives only
       that, and ablocks (YG01.v:212) has no canonical order *)
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++
                                    [(out, dec_b_olen nch ns)]) /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_6f0 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_6f0 MT) /\
    dec_b_frs cx (aview segs (w_H W') mem') /\
    (* Of the caller-saved registers only a0 is stated: the segment ends at the plain_le leaf, whose dleaf_post
       (LeafCgKit.v:86-96) keeps the callee-saved set (aregs_preserved) and a0 alone. Image B holds nothing the
       next segment reads in a caller-saved register here (image A dropped its a6 / a7 clauses for this reason). *)
    YK11.getr regs' 10 = w64 (if CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns then ns else -1) /\
    YK11.getr regs' 18 = w64 out /\
    (* s3 is the harness's `wellformed && fits0 && fits` of the plain check, built at +0x5cc..+0x5d4 out of s3,
       s8 and s2; under the geometry of dec_b_mode_ok it is plain_ok, which is what the `bne a0,a1` at +0x6fc of
       the next segment needs (its expected value is s3 - 1 | ns, +0x6f0..+0x6f8). *)
    YK11.getr regs' 19 = w64 (if CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns then 1 else 0) /\
    YK11.getr regs' 20 = w64 (dec_b_len (d_n cx)) /\
    YK11.getr regs' 21 = w64 mode /\
    YK11.getr regs' 22 = w64 (dec_b_len (d_n cx)) /\
    YK11.getr regs' 23 = w64 nch /\
    YK11.getr regs' 26 = w64 (dec_b_olen nch ns) /\
    YK11.getr regs' 27 = w64 res /\
    dec_b_mode_ok cx W' mem' mode nch ns /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = true ->
       garr8 segs (rd W' mem') out
         (map (fun b : byte => bv_unsigned b) (CPlain.plain_out (d_body cx) nch ns))) /\
    (CPlain.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = false ->
       dec_b_filled W' mem' out (dec_b_olen nch ns)) /\
    dec_b_slot cx (aview segs (w_H W') mem') 24 (dec_b_len (d_n cx)) /\
    dec_b_slot cx (aview segs (w_H W') mem') 32 SHADOW_OFF /\
    dec_b_slot cx (aview segs (w_H W') mem') 40 res /\
    dec_b_slot cx (aview segs (w_H W') mem') 56 (ns mod 2 ^ 32) /\
    dec_b_slot cx (aview segs (w_H W') mem') 64 (nch mod 2 ^ 32) /\
    dec_b_slot cx (aview segs (w_H W') mem') 72 (ns mod 2 ^ 64) /\
    dec_b_slot cx (aview segs (w_H W') mem') 80 (res + 50) /\
    dec_b_slot cx (aview segs (w_H W') mem') 88 out /\
    dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x840 — the return of reac_upstream_channels (+0x83c). The plain result has been checked (+0x6fc), the scan
   loop L2 (+0x70c..+0x74c) and the bcmp double loop L3/L4 (+0x7c0..+0x820) have run and their abort edges are
   refuted, the decode buffer has been freed (+0x834), and s6 / s11 are back to the length and the copy
   (+0x824 / +0x828, or kept on the paths that skip the loops). a0 is the channel count. s2 / s3 / s5 / s7..s10 are
   left by the loops (or not) and are not stated.
   Follows: lib/U/Prog/fd_up.v:55's entry state, i.e. lib/U/Prog/fd_segments_c.v:78-80 fd_up_regs
   (len, frame, frame + 50) — here s6, s11 and 80(s1) — plus reac_upstream_channels_cg.v's return
   (upstream_result of lib/B/Prog/reac_upstream_channels_c.v). *)
Definition llvm_b_st_840 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x840)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' dec_ev_840 /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))]) /\
    4096 <= res /\
    mo_le MT (d_S cx) S' (dec_spent_840 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_840 MT) /\
    dec_b_frs cx (aview segs (w_H W') mem') /\
    YK11.getr regs' 10 = w64 (CChan.upstream_result (dec_b_len (d_n cx))) /\
    YK11.getr regs' 22 = w64 (dec_b_len (d_n cx)) /\
    YK11.getr regs' 27 = w64 res /\
    dec_b_mode_ok cx W' mem' mode nch ns /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (* Every slot below is stored before +0x6f0 on every path (32 at +0x3ec, 24 / 40 at +0x434 / +0x438, 80 at
       +0x658, 112 at +0x100), so none is conditional. The cmp segment's only store, 48(s1) = 3 * ns at +0x7bc,
       is skipped by the `blez a0` at +0x764 when the plain check failed (a0 = if plain_ok .. then ns else -1,
       llvm_b_st_6f0) and by the `blez s7` at +0x780 when nch <= 0; nothing at or after +0x830 reads it, so it is
       not stated (image A guards its four such slots by plain_ok instead). *)
    dec_b_slot cx (aview segs (w_H W') mem') 24 (dec_b_len (d_n cx)) /\
    dec_b_slot cx (aview segs (w_H W') mem') 32 SHADOW_OFF /\
    dec_b_slot cx (aview segs (w_H W') mem') 40 res /\
    dec_b_slot cx (aview segs (w_H W') mem') 80 (res + 50) /\
    dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x96c — the return of reac_upstream_decode #3 (+0x968). The channel count has been checked against the
   harness's own geometry (+0x8a0), the upstream buffer has been allocated (+0x8c4) and filled with 0xa5
   (+0x8d8), the two refusing calls have run (+0x8e8, +0x8fc) and the scan loop L5 (+0x914..+0x958) has shown
   they wrote nothing. a0 is the third call's return; s2 is the shadow base again (+0x870 / +0x898), s5 the channel
   count (+0x840), s7 the upstream buffer (+0x8cc), s8 its length, s9 its complement (+0x914, read by the scan
   loop L6 of the next segment).
   Follows: lib/U/Prog/fd_up.v:55 after its `g_malloc` and the upstream leaves; the return value and the written
   range are reac_upstream_decode_cg.v (up_ok / up_nch of lib/B/Prog/reac_upstream_decode_c.v). *)
Definition llvm_b_st_96c (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res upb mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x96c)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' dec_ev_96c /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_b_len (d_n cx))] ++
                                    [(upb, dec_b_uolen (CChan.upstream_result (dec_b_len (d_n cx))))]) /\
    4096 <= res /\ 4096 <= upb /\
    mo_le MT (d_S cx) S' (dec_spent_96c MT (d_n cx)) /\ mo_ok MT S' (dec_rest_96c MT) /\
    dec_b_frs cx (aview segs (w_H W') mem') /\
    YK11.getr regs' 10 =
      w64 (if CUp.up_ok res upb (dec_b_len (d_n cx)) (d_body cx) then 12 else -1) /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 21 = w64 (CChan.upstream_result (dec_b_len (d_n cx))) /\
    YK11.getr regs' 22 = w64 (dec_b_len (d_n cx)) /\
    YK11.getr regs' 23 = w64 upb /\
    YK11.getr regs' 24 = w64 (dec_b_uolen (CChan.upstream_result (dec_b_len (d_n cx)))) /\
    YK11.getr regs' 25 = w64 (Z.lnot upb) /\
    YK11.getr regs' 27 = w64 res /\
    dec_b_mode_ok cx W' mem' mode nch ns /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (CUp.up_ok res upb (dec_b_len (d_n cx)) (d_body cx) = true ->
       garr8 segs (rd W' mem') upb
         (map (fun b : byte => bv_unsigned b)
            (CDec.braid_out (d_body cx) (CUp.up_nch (dec_b_len (d_n cx))) 12))) /\
    (CUp.up_ok res upb (dec_b_len (d_n cx)) (d_body cx) = false ->
       dec_b_filled W' mem' upb (dec_b_uolen (CChan.upstream_result (dec_b_len (d_n cx))))) /\
    (* As at llvm_b_st_840, all unconditional: the up segment (+0x840..+0x968) stores no slot. *)
    dec_b_slot cx (aview segs (w_H W') mem') 24 (dec_b_len (d_n cx)) /\
    dec_b_slot cx (aview segs (w_H W') mem') 32 SHADOW_OFF /\
    dec_b_slot cx (aview segs (w_H W') mem') 40 res /\
    dec_b_slot cx (aview segs (w_H W') mem') 80 (res + 50) /\
    dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0xae0 — the join of the two returns: the normal path arrives from free #3 (+0xac4) with the local
   re-poisoned (+0xad0 / +0xad4) and t0 / a6 / a7 reloaded from their spill slots (+0xacc / +0xad8 / +0xadc); the
   early path jumps here straight from +0x104 with the local never unpoisoned and the frame still in t0 / a6 / a7.
   Both leave the same picture: every block this function took is gone, the frame's eight shadow bytes are the
   entry poison, and t0 / a6 / a7 carry the frame for the teardown (the freed magic into 0(a7) at +0xae8, the
   0xf5 poison through t0 at +0xaf0..+0xb10, the flag byte through 56(a6) at +0xb14 / +0xb18).
   Follows: lib/U/Prog/fd_segments_c.v:81 fd_exit_regs (the frame pointer alone) and
   lib/U/Prog/LLVMFuzzerTestOneInput_early.v:60 llvm_early, which joins the same teardown on that image. *)
Definition llvm_b_st_ae0 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0xae0)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core cx ly' S' W' regs' mem' md' k /\ k <= dec_ev_ae0 /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx)) /\
    mo_le MT (d_S cx) S' (dec_spent_ae0 MT (d_n cx)) /\
    dec_b_fr cx regs' /\
    dec_b_fsh cx (aview segs (w_H W') mem') DEC_SH_MID DEC_SH_MID.

(* The slot's post at the return (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:141-146), at the one leaf
   decode_shape's LIBK hands the continuation (lib/FrameSlotK.v:40: LIBK pl fs K = K (LL 0 fs [])). *)
Definition dec_b_post (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
    c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    @dec_lib_post_x rc asink_syms tfib_K asink_none ameta_inv B MT XL
      (d_regs cx) (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) (d_p cx) (d_n cx) (d_M cx)
      (YO09.LL 0 (m_fs (d_md cx)) []) ly' S' W' regs' mem' md' k.

(* ------------------------------------------------------------------ *)
(* 4. The nine segment statements                                       *)
(* ------------------------------------------------------------------ *)

(* +0x000 .. +0x070. Prologue, 13 saves, s0/s1, s3 = size, the shadow base out of the GOT word and the cell
   (+0x04c..+0x060, which is why dec_crt_cells is a premise), the use-after-return flag (+0x054..+0x068), and the
   class-0 stack malloc. The frame position fpos the call picks is the existential the rest of the walk is built on
   (cgif lib/A/ACez.v:46-57, whose `exists fpos sp1 E0` this is: sp1 is a closed form of sp here and there is
   no symbolic env). No branch of this segment leaves it. *)
Definition llvm_b_entry_stmt : Prop :=
  pc_stack_malloc (as_code B) 0 = decodeb_sigma DB___asan_stack_malloc_0 ->
  dec_crt_cells B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B ->
  (forall fx : YK11.FPState, @astack_malloc_realizes fx rc segs B 0) ->
  forall (fx : YK11.FPState) ly S (W : world segs) regs mem md p n pl M,
    @dec_lib_pre_x fx rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
      regs ly S W mem md p n pl M ->
    rom_view segs W mem ->
    (forall nn, 0 <= nn -> dec_llvmf_cost MT nn <= XL nn) ->
    SRr segs W (@cfg_at fx segs DEC_A_LLVMF regs mem md)
      (fun W' c' => exists fpos,
         llvm_b_st_074 (mkDCtx fx ly S W regs mem md p n pl M fpos) W' c').

(* +0x074 .. +0x278. a6/a7/t0, the ASan frame record and its redzone poison, the size test (+0x0fc..+0x104,
   whose taken edge is llvm_b_st_104), the spills of the frame (+0x100, +0x10c, +0x110, +0x258), the three fuzz_u8
   reads with their shadow checks, the length dispatch, the mode select, the local's unpoison, and malloc #1.
   Refuted inside: the three ASan report guards +0x130 (-> +0xbbc), +0x158 (-> +0xc0c), +0x1d0 (-> +0xc48), and
   the five UBSan guards into +0xb84: +0x120, +0x148, +0x1c0 (data pointer + 1 / + 2 / + 3 wraps), +0x260
   (body + length wraps), +0x270 (null-offset check of the body pointer). *)
Definition llvm_b_early_stmt : Prop :=
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B ->
  (* The mode select loads its table pointer from decodeb_obj 4 / 5 / 6 (RELRO words, outside rom_view) and the
     state after malloc #1 reads the table at mode + 4 / + 8: dec_crt_cells carries those cells as as_const rows
     (a Theorem Labs lane's frozen statement, nine rows per image), re-read at every state through AR's am_const. *)
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc tfib_sink_head segs B MT) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_b_base cx -> dec_b_rom cx -> llvm_b_st_074 cx W' c' ->
    SRr segs W' c' (fun W2 c2 => llvm_b_st_27c cx W2 c2 \/ llvm_b_st_104 cx W2 c2).

(* +0x104 -> +0xae0: the `bnez a0` of the size test taken. Nothing but the jump: the teardown that follows is
   llvm_b_exit_stmt's second entry. dec_b_base pins n < 2 ^ 26, so the state this starts from is unreachable;
   the statement is kept because the listing's edge is (lib/U/Prog/LLVMFuzzerTestOneInput_early.v:60). *)
Definition llvm_b_early_ret_stmt : Prop :=
  AR_laws segs B -> ameter_laws MT ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_b_base cx -> dec_b_rom cx -> llvm_b_st_104 cx W' c' ->
    SRr segs W' c' (llvm_b_st_ae0 cx).

(* +0x27c .. +0x414. The NULL check of the copy (+0x284, refuted by 4096 <= res), __asan_memcpy, the two
   reac_frame_is_reac calls (+0x2a4, +0x30c) with the two shadow-checked header reads, reac_frame_clean_len and
   the abort edges of the is_reac / clean-length algebra (+0x314, +0x328, +0x330, +0x358, +0x39c), the two
   four-byte shadow checks on the mode fields (+0x3ac -> +0xb94, +0x3c0 -> +0xba8, each with its slow path back),
   the geometry spills, and malloc #2.
   Refuted inside: the ASan report guards +0x2cc (-> +0xc18), +0x2f4 (-> +0xc54) and the report_load4 calls of the
   two slow paths (+0xba4, +0xbb8); the abort edges above into +0xb88; and the three UBSan guards into +0xb84:
   +0x2b0 (copy null), +0x2b8 (copy + 12 wraps), +0x2e0 (copy + 13 wraps). *)
Definition llvm_b_copy_stmt : Prop :=
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (decodeb_sigma DB___asan_memcpy)) ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LIsReac.dec_reac_frame_is_reac_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCleanLen.dec_reac_frame_clean_len_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_b_base cx -> dec_b_rom cx -> llvm_b_st_27c cx W' c' ->
    SRr segs W' c' (llvm_b_st_418 cx).

(* +0x418 .. +0x5c8. The NULL check of the decode buffer (+0x41c), reac_frame_inspect, the frame-field checks
   with their four shadow checks, the inspect / counter abort edges (+0x520, +0x590, +0x59c), reac_frame_counter,
   __asan_memset of the buffer, and reac_decode.
   Refuted inside: the ASan report guards +0x468 (-> +0xbdc), +0x498 (-> +0xc38), +0x4c8 (-> +0xc74), +0x4f8
   (-> +0xc94), +0x55c (-> +0xbec), +0x578 (-> +0xbfc); the abort edges +0x41c, +0x520, +0x590, +0x59c into +0xb88;
   and the eight UBSan guards into +0xb84: +0x440, +0x528 (copy null), +0x44c, +0x47c, +0x4ac, +0x4dc, +0x534,
   +0x540 (copy + 12 / + 13 / + 0x5d2 / + 0x5d3 / + 14 / + 15 wraps). The call of reac_decode also discharges
   image B's three UBSan premises of the leaf (lib/B/Prog/reac_decode_c.v: copy non-null when the length is 1492,
   mode non-null and 4-aligned when the frame is well formed, buffer non-null when the decode succeeds). *)
Definition llvm_b_inspect_stmt : Prop :=
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decodeb_sigma DB___asan_memset)) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCounter.dec_reac_frame_counter_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LInspect.dec_reac_frame_inspect_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LDecode.dec_reac_decode_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_b_base cx -> dec_b_rom cx -> llvm_b_st_418 cx W' c' ->
    SRr segs W' c' (llvm_b_st_5cc cx).

(* +0x5cc .. +0x6ec. The decode-result check (+0x5ec), the scan loop L1 with its shadow slow path
   (+0x5fc..+0x650), the spill of copy + 50 (+0x658), check_round_trip #1 (+0x68c, when 0 < ns <= 12),
   check_braid #1 (+0x6bc, when the decode succeeded), __asan_memset, and reac_decode_plain_le.
   Refuted inside: the in-line report call +0x64c of L1's slow path (it returns and would fall into +0x650); the
   abort edges +0x5ec, +0x650 into +0xb88; and the five UBSan guards into +0xb84: +0x608 (buffer + i wraps),
   +0x66c, +0x69c (copy null), +0x678, +0x6a8 (copy + 50 wraps). The call of reac_decode_plain_le also discharges
   image B's three UBSan premises of the leaf (lib/B/Prog/reac_decode_plain_le_c.v). *)
Definition llvm_b_crt1_stmt : Prop :=
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decodeb_sigma DB___asan_memset)) ->
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decodeb_sigma DB_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_b_base cx -> dec_b_rom cx -> llvm_b_st_5cc cx W' c' ->
    SRr segs W' c' (llvm_b_st_6f0 cx).

(* +0x6f0 .. +0x83c. The plain-result check (+0x6fc), the scan loop L2 (+0x70c..+0x760), the bcmp double loop
   L3/L4 (+0x784..+0x820) with its __interceptor_trampoline_bcmp call (+0x7f0), the mismatch abort edge (+0x82c),
   free #1 of the decode buffer (+0x834), and reac_upstream_channels.
   Refuted inside: the in-line report call +0x75c of L2's slow path; the abort edges +0x6fc, +0x760, +0x82c into
   +0xb88; and the five UBSan guards into +0xb84: +0x718 (buffer + i wraps), +0x768 (copy null), +0x774 (copy + 50
   wraps), +0x7d4 (buffer + offset wraps), +0x7d8 (copy + 50 + offset wraps). *)
Definition llvm_b_cmp_stmt : Prop :=
  pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @abcmp_realizes fx rc segs B (decodeb_sigma DB___interceptor_trampoline_bcmp)) ->
  (forall fx : YK11.FPState, @afree04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LUpChannels.dec_reac_upstream_channels_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_b_base cx -> dec_b_rom cx -> llvm_b_st_6f0 cx W' c' ->
    SRr segs W' c' (llvm_b_st_840 cx).

(* +0x840 .. +0x968. The channel-count check (+0x8a0), malloc #3 (+0x8c4), its NULL check (+0x8c8), __asan_memset
   of the upstream buffer, the two refusing reac_upstream_decode calls (+0x8e8, +0x8fc) and their two abort edges
   (+0x904, +0x908), the scan loop L5 (+0x914..+0x958) and its abort edge (+0x958), and reac_upstream_decode #3.
   Refuted inside: the in-line report call +0x954 of L5's slow path; the abort edges +0x8a0, +0x8c8, +0x904,
   +0x908, +0x958 into +0xb88; and the one UBSan guard into +0xb84: +0x918 (upstream buffer + i wraps). *)
Definition llvm_b_up_stmt : Prop :=
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decodeb_sigma DB___asan_memset)) ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LUpDecode.dec_reac_upstream_decode_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_b_base cx -> dec_b_rom cx -> llvm_b_st_840 cx W' c' ->
    SRr segs W' c' (llvm_b_st_96c cx).

(* +0x96c .. +0xb80, with the second entry at +0xae0. The four shadow-checked upstream header checks
   (+0x970..+0xa20), the result check (+0xa24), the scan loop L6 (+0xa2c..+0xa78), check_round_trip #2 (+0xaa0)
   and check_braid #2 (+0xab4) when the upstream decode succeeded, free #2 (+0xabc) and free #3 (+0xac4), the
   shadow teardown (+0xac8..+0xb3c: the local re-poisoned, the freed magic, then the fake frame's 0xf5 and its flag
   byte), a0 = 0, the 13 reloads, and `ret`.
   Refuted inside: the ASan report guards +0x990 (-> +0xbcc), +0x9b8 (-> +0xc28), +0x9e4 (-> +0xc64), +0xa0c
   (-> +0xc84) and the in-line report call +0xa74 of L6's slow path; the abort edges +0xa24, +0xa78 into +0xb88;
   and the eight UBSan guards into +0xb84: +0x974, +0xa80 (copy null), +0x97c, +0x9a4 (copy + 12 / + 13 wraps),
   +0x9d0, +0x9f8 (copy + len - 2 / - 1 wraps), +0xa34 (upstream buffer + i wraps), +0xa88 (copy + 50 wraps).
   HSINK_KEPT and HMETA_KEPT are needed here and nowhere else: the post asks asink_none and ameta_inv at the
   return memory, which differs from the entry memory by the fake frame and its shadow. *)
Definition llvm_b_exit_stmt : Prop :=
  pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  (* dec_b_post asks mo_le .. (XL n) and the walk spends dec_spent_ae0 MT n = dec_llvmf_cost MT n
     (dec_cost_ladder); this is the statement's own bound between the two (LLVMFuzzerTestOneInput_cg.v:244). *)
  (forall nn, 0 <= nn -> dec_llvmf_cost MT nn <= XL nn) ->
  astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx : YK11.FPState, @afree04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decodeb_sigma DB_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx) ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_b_base cx -> dec_b_rom cx -> (llvm_b_st_96c cx W' c' \/ llvm_b_st_ae0 cx W' c') ->
    SRr segs W' c' (dec_b_post cx).

(* ------------------------------------------------------------------ *)
(* 5. The composition                                                   *)
(* ------------------------------------------------------------------ *)

(* The slot post with the frame position the entry invented still existentially quantified: what the chain
   below proves and what the contract's own continuation asks for (cgif lib/A/ACfj.v:252's
   `(fpos & sp1 & E0 & HPOST)`). *)
Definition dec_b_post_ex (fx : YK11.FPState) (ly : alayout) (S : astate) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) :
    world segs -> config -> Prop :=
  fun W' c' => exists fpos, dec_b_post (mkDCtx fx ly S W regs mem md p n pl M fpos) W' c'.

(* cgif lib/A/ACfh.v:47, copied: an SRr obligation whose post is "AI gives srealizes" is a srealizes. *)
Lemma dec_srz_enter : forall (W : world segs) (c : config) (T : TSet),
  AI segs (w_H W) (w_A W) (cfg_model c) ->
  SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) ->
  srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

(* The walk from the nine segments, as cgif's lib/A/ACfj.v:230-259 composes its stages. *)
Theorem dec_llvmf_holds_of_segs :
  llvm_b_entry_stmt -> llvm_b_early_stmt -> llvm_b_early_ret_stmt -> llvm_b_copy_stmt ->
  llvm_b_inspect_stmt -> llvm_b_crt1_stmt -> llvm_b_cmp_stmt -> llvm_b_up_stmt -> llvm_b_exit_stmt ->
  dec_llvmf_holds_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS asink_img_laws ro_below_ofl
    RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
intros ENTRY EARLY EARLYRET COPY INSPECT CRT1 CMP UP EXIT.
unfold dec_llvmf_holds_stmt.
intros HPCM HPCF HPCS HCELLS HROS HRNE HUTR LAWS ML MTL MTF SMP ASF FFL AIL HSINK_KEPT HMETA_KEPT ROB ASM0 AMEMSET
  AMEMCPY
  AMALLOC AFREE ABCMP
  ACRT LIS LCL LCT LIN LDE LPL LUC LUD LCB HXL.
intros fx ly S W regs mem md p n pl M K HAI HPRE HK.
change (@LIBK DShape.decode_shape pl (m_fs md) K) with (K (YO09.LL 0 (m_fs md) [])).
eapply dec_srz_enter; [exact HAI|].
eapply (SRr_mono segs W (@cfg_at fx segs DEC_A_LLVMF regs mem md)
          (dec_b_post_ex fx ly S W regs mem md p n pl M)).
- (* the chain *)
  eapply SRr_bind;
    [ exact (ENTRY HPCS HCELLS LAWS ML MTL MTF SMP ASM0 fx ly S W regs mem md p n pl M HPRE
               (HROM fx ly S W regs mem md p n pl M HPRE) HXL) |].
  intros W1 c1 _ (fpos & H074).
  set (cx := mkDCtx fx ly S W regs mem md p n pl M fpos) in *.
  assert (HB : dec_b_base cx) by exact HPRE.
  assert (HR : dec_b_rom cx) by exact (HROM fx ly S W regs mem md p n pl M HPRE).
  eapply SRr_bind; [ exact (EARLY HPCM HUTR HCELLS HROS HRNE LAWS ML MTL AMALLOC cx W1 c1 HB HR H074) |].
  intros W2 c2 _ [H27c | H104].
  + eapply SRr_bind; [ exact (COPY HPCM HUTR HCELLS HROS HRNE LAWS ML MTL AMEMCPY AMALLOC LIS LCL cx W2 c2 HB HR
                               H27c) |].
    intros W3 c3 _ H418.
    eapply SRr_bind; [ exact (INSPECT HCELLS HROS HRNE LAWS ML MTL AMEMSET LCT LIN LDE cx W3 c3 HB HR H418) |].
    intros W4 c4 _ H5cc.
    eapply SRr_bind; [ exact (CRT1 HCELLS HROS HRNE LAWS ML MTL MTF AMEMSET ACRT LCB LPL cx W4 c4 HB HR H5cc) |].
    intros W5 c5 _ H6f0.
    eapply SRr_bind; [ exact (CMP HPCF HUTR HCELLS HROS HRNE LAWS ML MTL ABCMP AFREE LUC cx W5 c5 HB HR H6f0) |].
    intros W6 c6 _ H840.
    eapply SRr_bind; [ exact (UP HPCM HUTR HCELLS HROS HRNE LAWS ML MTL AMEMSET AMALLOC LUD cx W6 c6 HB HR H840) |].
    intros W7 c7 _ H96c.
    eapply SRr_mono;
      [ exact (EXIT HPCF HUTR HCELLS HROS HRNE LAWS ML MTL MTF HXL ASF FFL AFREE ACRT LCB HSINK_KEPT HMETA_KEPT
                 cx W7 c7
                 HB HR (or_introl H96c)) |].
    intros W8 c8 _ HP. unfold dec_b_post_ex. exists fpos. exact HP.
  + eapply SRr_bind; [ exact (EARLYRET LAWS MTL cx W2 c2 HB HR H104) |].
    intros W3 c3 _ Hae0.
    eapply SRr_mono;
      [ exact (EXIT HPCF HUTR HCELLS HROS HRNE LAWS ML MTL MTF HXL ASF FFL AFREE ACRT LCB HSINK_KEPT HMETA_KEPT
                 cx W3 c3
                 HB HR (or_intror Hae0)) |].
    intros W8 c8 _ HP. unfold dec_b_post_ex. exists fpos. exact HP.
- intros W' c' Hwle HP HAI'. unfold dec_b_post_ex in HP. destruct HP as (fpos & HP).
  apply (HK (YO09.LL 0 (m_fs md) []) W' c' Hwle HAI'). exact HP.
Qed.

End seg.

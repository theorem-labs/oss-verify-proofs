(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_segs: the INTERFACE of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput.
   It holds three things and no stepping:
   1. a state predicate at each of the walk's cut points, named llvm_a_st_<offset from DEC_A_LLVMF>;
   2. the nine segment statements llvm_a_<group>_stmt, each "from the previous cut point's state, the machine
      SRr-realizes the next cut point's state", over the callee contracts that segment discharges;
   3. the composition dec_llvmf_holds_of_segs, proved: the nine statements give dec_llvmf_holds_stmt
      (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:210-245), in cgif_file_fuzzer's lib/A/ACfj.v:230-259 form
      (SRr_bind / SRr_mono / srz_enter, the last copied here as dec_srz_enter from cgif lib/A/ACfh.v:47).

   The cut points and the segment names are a Theorem Labs lane's image-B plan at image A's offsets
   (ltoia-segments.md; every offset is decoded from the audited listing
   lib/A/Prog/DecodeList.v in map-code.md section 2):

     llvm_a_entry   +0x000..+0x070  ends at jal __asan_stack_malloc_0     post at +0x074
     llvm_a_early   +0x074..+0x230  ends at jal malloc #1                 post at +0x234 (early edge +0x104 -> +0x9a8)
     llvm_a_copy    +0x234..+0x3bc  ends at jal malloc #2                 post at +0x3c0
     llvm_a_inspect +0x3c0..+0x4f8  ends at jal reac_decode               post at +0x4fc
     llvm_a_crt1    +0x4fc..+0x5f8  ends at jal reac_decode_plain_le      post at +0x5fc
     llvm_a_cmp     +0x5fc..+0x744  ends at jal reac_upstream_channels    post at +0x748
     llvm_a_up      +0x748..+0x868  ends at jal reac_upstream_decode #3   post at +0x86c
     llvm_a_exit    +0x86c..+0xa48  ends at ret                           post = the slot post
     llvm_a_trap    +0xa4c..+0xb60  no statement: every branch into it is refuted inside the segment that holds it

   Where each predicate comes from. The released UBSAN walk of the same C function at 568db058c1d proves the same
   block structure on another image; each predicate below names the released post it follows, clause by clause:
     lib/U/Prog/fd_segments_c.v:39-55  fd_inv        -> dec_a_core (the journal, the frame, sp, gp/tp, the payload)
     lib/U/Prog/fd_segments_c.v:56-61  fd_mode_ok    -> dec_a_mode_ok
     lib/U/Prog/fd_segments_c.v:66-77  fd_seg_post   -> the shape of every llvm_a_st_* (exists fx' .. /\ config at
                                                        the cut pc /\ frm_zero /\ fd_inv /\ gp/tp kept /\ blocks /\ kept)
     lib/U/Prog/fd_entry.v:130-141     fd_entry_post -> llvm_a_st_234 (its `getr regs 9/25/19` register triple is
                                                        decode's s10 = len, s4 = copy, s9 = mode here)
     lib/U/Prog/fd_segments_c.v:78-80  fd_up_regs    -> llvm_a_st_748 (len, frame, frame + 50)
     lib/U/Prog/fd_segments_c.v:81     fd_exit_regs  -> llvm_a_st_9a8 (the frame pointer alone)
     lib/U/Prog/fd_exit.v:17-22        llvm_saved_cells -> dec_a_saved (13 words, image A's offsets)
     lib/U/Prog/LLVMFuzzerTestOneInput_early.v:15-16,60  llvm_early_cond / llvm_early -> llvm_a_st_104 and
                                                        llvm_a_early_ret_stmt (the `2 ^ 26 <= size` edge)
   What the released posts do not have, because image A alone has it (map-code.md section 4, "Where image A
   differs"): the shadow base in s2, the ASan frame record at s5 with its redzone poison and the 8 shadow bytes
   at s11, the fake-versus-real frame choice in s3, and the caller-journal facts (ajournal / own / mo_ok / mo_le)
   that this image's contract is written in instead of the released SR/lf_fr form.

   The C-level facts are the leaves' own models (lib/A/Prog/reac_*_c.v), which the leaf contracts
   lib/A/Prog/reac_*_cg.v state their results in; no C semantics is restated here. *)
From Stdlib Require Import ZArith NArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YI00 YI04 YG0v YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require reac_frame_is_reac_cg reac_frame_clean_len_cg
  reac_frame_counter_cg reac_frame_inspect_cg reac_decode_cg reac_decode_plain_le_cg reac_upstream_channels_cg
  reac_upstream_decode_cg check_braid_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require reac_decode_c reac_decode_plain_le_c
  reac_frame_inspect_c reac_upstream_channels_c reac_upstream_decode_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module DShape := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.DecodeShape.
Module CDec := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_c.
Module CPlain := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_plain_le_c.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_c.
Module CChan := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_c.
Module CUp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_decode_c.
Module LIsReac := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_is_reac_cg.
Module LCleanLen := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_clean_len_cg.
Module LCounter := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_counter_cg.
Module LInspect := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_cg.
Module LDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_cg.
Module LPlainLe := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_plain_le_cg.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_cg.
Module LUpDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_decode_cg.
Module LCheckBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.check_braid_cg.

(* The shadow bytes this function writes for its own frame; the listing's own immediates
   (li a0,-15 / li a0,-8 / li a4,-13 / li a0,-11 at +0x0e8 / +0x0d0 / +0x0b4 / +0x9b8). *)
Definition DEC_SH_LEFT : Z := 0xf1.
Definition DEC_SH_MID : Z := 0xf8.
Definition DEC_SH_RIGHT : Z := 0xf3.
Definition DEC_SH_UAR : Z := 0xf5.
(* The fill byte the harness writes before every decode (memset at +0x4e0 / +0x5e4 / +0x7d4). *)
Definition DEC_FILL : Z := 0xa5.
(* The frame class this function's __asan_stack_malloc_0 call allocates (li a0,64 at +0x6c): class 0, 64 bytes. *)
Definition DEC_FCLASS : Z := 0.
(* The 13 callee-saved words the prologue stores (+0x008..+0x038) and the epilogue reloads (+0xa10..+0xa40),
   as (byte below the entry sp, register number); the released llvm_saved_cells of lib/U/Prog/fd_exit.v:17-22
   at image A's frame of 224 bytes. *)
Definition dec_a_saved_at : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24); (88, 25);
   (96, 26); (104, 27)].
(* The three bytes fuzz_in / fuzz_u8 take off the input before fuzz_take, and what is left for fuzz_dup:
   the released en_k / en_len of lib/U/Prog/LLVMFuzzerTestOneInput_c.v, restated here so that no plain-image
   file is imported into lib/A. *)
Definition dec_a_u (n : Z) : Z := Z.min n 3.
Definition dec_a_len (n : Z) : Z := Z.max (n - 3) 0.
(* The mode geometry the dispatch reads and the output length the harness asks malloc for:
   out_len = nch * ns * 3 when both are positive, else 0, and olen = out_len ? out_len : 1
   (+0x374..+0x3b8); the released fd_olen of lib/U/Prog/fd_down.v:25 (1 <= fd_olen <= 48387). *)
Definition dec_a_prod (nch ns : Z) : Z := ((nch mod 2 ^ 32) * (ns mod 2 ^ 32)) mod 2 ^ 64.
Definition dec_a_fits0 (nch ns : Z) : Z := if (0 <? nch) && (0 <? ns) then 1 else 0.
Definition dec_a_olen (nch ns : Z) : Z := if (0 <? nch) && (0 <? ns) then 3 * nch * ns else 1.
(* The upstream output length: out_len = nch * 12 * 3 when nch > 0, else 0, and olen = out_len ? out_len : 1
   (+0x7a0..+0x7bc); the released up_olen of lib/U/Prog/fd_up.v:38 (1 <= up_olen <= 1440). *)
Definition dec_a_uolen (nch : Z) : Z := if 0 <? nch then 36 * nch else 1.

(* ------------------------------------------------------------------ *)
(* 1. The meter and event ladders                                       *)
(* ------------------------------------------------------------------ *)

(* What the rest of the walk still spends, from each cut point. The sizes are the released bounds:
   the payload copy at most n bytes, the decode buffer at most 48387 (fd_down.v:25 olen_bounds), the upstream
   buffer at most 1440 (fd_up.v:38 up_olen_bounds), and each check_round_trip at most dec_crt_cost_max
   (LLVMFuzzerTestOneInput_cg.v:204-205). *)
Definition dec_rest_86c (MT : ameter_ops) : Z := dec_crt_cost_max MT + mo_free MT + mo_free MT.
Definition dec_rest_748 (MT : ameter_ops) : Z := mo_malloc MT 1440 + dec_rest_86c MT.
Definition dec_rest_5fc (MT : ameter_ops) : Z := mo_free MT + dec_rest_748 MT.
Definition dec_rest_4fc (MT : ameter_ops) : Z := dec_crt_cost_max MT + dec_rest_5fc MT.
Definition dec_rest_3c0 (MT : ameter_ops) : Z := dec_rest_4fc MT.
Definition dec_rest_234 (MT : ameter_ops) : Z := mo_malloc MT 48387 + dec_rest_3c0 MT.
Definition dec_rest_074 (MT : ameter_ops) (n : Z) : Z := mo_malloc MT n + dec_rest_234 MT.
Definition dec_rest_9a8 (MT : ameter_ops) : Z := 0.
(* What the walk has spent at each cut point. *)
Definition dec_spent_074 (MT : ameter_ops) : Z := 0.
Definition dec_spent_234 (MT : ameter_ops) (n : Z) : Z := mo_malloc MT n.
Definition dec_spent_3c0 (MT : ameter_ops) (n : Z) : Z := dec_spent_234 MT n + mo_malloc MT 48387.
Definition dec_spent_4fc (MT : ameter_ops) (n : Z) : Z := dec_spent_3c0 MT n.
Definition dec_spent_5fc (MT : ameter_ops) (n : Z) : Z := dec_spent_4fc MT n + dec_crt_cost_max MT.
Definition dec_spent_748 (MT : ameter_ops) (n : Z) : Z := dec_spent_5fc MT n + mo_free MT.
Definition dec_spent_86c (MT : ameter_ops) (n : Z) : Z := dec_spent_748 MT n + mo_malloc MT 1440.
Definition dec_spent_9a8 (MT : ameter_ops) (n : Z) : Z := dec_spent_86c MT n + dec_rest_86c MT.

(* spent + rest is the cost the statement's premise bounds by XL (LLVMFuzzerTestOneInput_cg.v:206-208, :242). *)
Lemma dec_cost_ladder : forall (MT : ameter_ops) (n : Z),
  dec_spent_074 MT + dec_rest_074 MT n = dec_llvmf_cost MT n /\
  dec_spent_234 MT n + dec_rest_234 MT = dec_llvmf_cost MT n /\
  dec_spent_3c0 MT n + dec_rest_3c0 MT = dec_llvmf_cost MT n /\
  dec_spent_4fc MT n + dec_rest_4fc MT = dec_llvmf_cost MT n /\
  dec_spent_5fc MT n + dec_rest_5fc MT = dec_llvmf_cost MT n /\
  dec_spent_748 MT n + dec_rest_748 MT = dec_llvmf_cost MT n /\
  dec_spent_86c MT n + dec_rest_86c MT = dec_llvmf_cost MT n /\
  dec_spent_9a8 MT n + dec_rest_9a8 MT = dec_llvmf_cost MT n.
Proof.
intros MT n. unfold dec_spent_9a8, dec_spent_86c, dec_spent_748, dec_spent_5fc, dec_spent_4fc, dec_spent_3c0,
  dec_spent_234, dec_spent_074, dec_rest_074, dec_rest_234, dec_rest_3c0, dec_rest_4fc, dec_rest_5fc,
  dec_rest_748, dec_rest_86c, dec_rest_9a8, dec_llvmf_cost.
repeat split; ring.
Qed.

(* The model events of the walk: one per malloc and free of this function, six per check_round_trip
   (check_round_trip_cg.v:46 DEC_CRT_EV); eighteen in all, far inside DEC_EV_LIB = 2000. *)
Definition dec_ev_074 : Z := 0.
Definition dec_ev_234 : Z := 1.
Definition dec_ev_3c0 : Z := 2.
Definition dec_ev_4fc : Z := 2.
Definition dec_ev_5fc : Z := 8.
Definition dec_ev_748 : Z := 9.
Definition dec_ev_86c : Z := 10.
Definition dec_ev_9a8 : Z := 18.
Lemma dec_ev_in_lib : dec_ev_9a8 <= DEC_EV_LIB.
Proof. unfold dec_ev_9a8, DEC_EV_LIB. lia. Qed.
Section seg. Context {rc : YM05.RunCeil}.
(* The Section of lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:169-182, variable for variable, so that
   dec_llvmf_holds_stmt can be stated here at the same arguments. *)
Local Abbreviation tfib_sink_head := dec_A_sink_head.          (* cgif lib/A/AE2k.v:44 at fuzz_decode's sink head *)
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
Local Abbreviation segs := decodesegs0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The frozen statement (a Theorem Labs lane 774ffa170e8, cb1f9b4724e) states HSINK_KEPT / HMETA_KEPT as premises of
   dec_llvmf_holds_stmt (the composition intros them under those names and passes them to llvm_a_exit_stmt, the
   one segment that needs them) and puts rom_view (lib/Reusable/YG0d.v:382) into the slot pre dec_lib_pre_x.
   HROM is that conjunct: the entry configuration shows the image's read-only bytes as the image holds them, and
   the journal's image clause (lib/Reusable/YCbq.v:362) carries it to every later read, kept off the owned statics
   and errno by check_round_trip_cg.v's dec_ro_rd_scoped (from dec_ro_rd_unowned / dec_rom_no_errno). *)
Lemma HROM : forall (fx : YK11.FPState) ly S (W : world segs) regs mem md p n pl M,
  @dec_lib_pre_x fx rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
    regs ly S W mem md p n pl M ->
  rom_view segs W mem.
Proof.
intros fx ly S W regs mem md p n pl M HPRE. unfold dec_lib_pre_x in HPRE.
decompose [and] HPRE. assumption.
Qed.

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
(* s11 = (s5 >> 3) + s2 at +0x0d4. *)
Definition d_SH (cx : dctx) : Z := shadow_addr (d_F cx).
(* The bytes fuzz_dup copies, i.e. what every callee of this function sees as the frame. *)
Definition d_body (cx : dctx) : list byte := skipn (Z.to_nat (dec_a_u (d_n cx))) (d_pl cx).
(* The meter budget of one call. *)
Definition d_T (cx : dctx) : Z := XL (d_n cx).

(* The slot's pre at the entry configuration (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:102-116); cgif's rt_base,
   lib/A/ACf5.v:52. Every segment but the entry takes it as a premise, as cgif's rt_from does. *)
Definition dec_a_base (cx : dctx) : Prop :=
  @dec_lib_pre_x (d_fx cx) rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
    (d_regs cx) (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) (d_p cx) (d_n cx) (d_pl cx) (d_M cx).

(* The entry's read-only view (HROM at this context). Every segment that calls a leaf takes it beside
   dec_a_base and carries it to its own call sites through the journal's image clause
   (lib/Reusable/YCbq.v:362); no cut-point predicate repeats it. *)
Definition dec_a_rom (cx : dctx) : Prop := rom_view segs (d_W cx) (d_mem cx).


(* ------------------------------------------------------------------ *)
(* 2. The pieces every cut point shares                                 *)
(* ------------------------------------------------------------------ *)

(* The 13 saved words are still the caller's: what the epilogue reloads at +0xa10..+0xa40, and so what makes
   aregs_preserved true at the return. The released lib/U/Prog/fd_entry.v:141 carries the same words as
   `rw_cells rsegs mem (spZ regs0 - 116) (.. llvm_saved_cells regs0)`. *)
Definition dec_a_saved (cx : dctx) (r : reader) : Prop :=
  Forall (fun o : Z * Z => rdword r (d_sp0 cx - fst o) = Some (bv_unsigned (YK11.getr (d_regs cx) (Z_to_bv 5 (snd o)))))
    dec_a_saved_at.

(* One 8-byte slot of the realigned spill area at s1 (the stores at +0x100, +0x370..+0x398, +0x3dc, +0x46c,
   +0x4f0, +0x58c, +0x670..+0x68c). The released walk has no counterpart: its frame is addressed off sp. *)
Definition dec_a_slot (cx : dctx) (r : reader) (off v : Z) : Prop := rdword r (d_sp1 cx + off) = Some v.

(* The frame invariant of every point of the body: the caller's journal with the one fake frame owned, the
   realigned stack, gp/tp, the saved words, the fake frame itself with the flag pointer in its last word, and the
   caller's payload block untouched. The released lib/U/Prog/fd_segments_c.v:39-55 fd_inv, clause for clause:
   MR/WF/bounded -> ajournal (which carries AR at the current state), sp facts -> spZ regs' = d_sp1,
   writable_at of the frame -> apresent of the fake frame, getr regs 4 -> gp/tp, In (frame,len)/blk_data ->
   the payload block and garr8. What fd_inv has no counterpart for is the fake frame and its flag word, which
   only the ASan image has. *)
Definition dec_a_core (cx : dctx) (ly' : alayout) (S' : astate) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
  @ajournal rc tfib_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' k /\
  frames S' = [(DEC_FCLASS, d_fpos cx)] /\
  YK11.getr regs' 8 = w64 (d_sp0 cx) /\
  YK11.getr regs' 9 = w64 (d_sp1 cx) /\
  spZ regs' = d_sp1 cx /\
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\ d_sp1 cx mod 32 = 0 /\
  YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  dec_a_saved cx (aview segs (w_H W') mem') /\
  4096 <= d_F cx /\ d_F cx mod 32 = 0 /\
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W') mem' a) /\
  rdword (aview segs (w_H W') mem') (d_F cx + 56) = Some (d_FL cx) /\
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B ly' S')) /\
  garr8 segs (rd W' mem') (d_p cx) (map (fun b : byte => bv_unsigned b) (d_pl cx)).

(* The three callee-saved registers that hold the fake frame through the body: s3 (the non-null fake-stack
   pointer, +0x074), s5 (the frame base, +0x080) and s11 (its shadow address, +0x0d4). Image A alone. *)
Definition dec_a_fr (cx : dctx) (regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 19 = w64 (d_F cx) /\ YK11.getr regs' 21 = w64 (d_F cx) /\ YK11.getr regs' 27 = w64 (d_SH cx).

(* The eight shadow bytes of the fake frame: the left redzone the prologue writes at +0x0ec..+0x0f8, the two
   bytes of the 12-byte local (0 and 4 while it is live, 0xf8 once it is poisoned), and the right redzone at
   +0x0e0..+0x0e4. Image A alone. *)
Definition dec_a_fsh (cx : dctx) (r : reader) (b4 b5 : Z) : Prop :=
  (forall i, 0 <= i < 4 -> r (d_SH cx + i) = Some DEC_SH_LEFT) /\
  r (d_SH cx + 4) = Some b4 /\ r (d_SH cx + 5) = Some b5 /\
  (forall i, 6 <= i < 8 -> r (d_SH cx + i) = Some DEC_SH_RIGHT).

(* The mode the dispatch selected and the geometry behind it: the table POINTER loaded from one of the three
   8-byte cells decode_obj 4 / 5 / 6 (in image A's read-only-after-relocation range, not in the read-only load)
   by `ld s7, %lo(obj)(aX)` (PLdHi at DecodeList.v:116, :151, :156, :159; PaTable.v:56-57 makes PLdHi a load of
   the word AT val a + off), or the 12-byte local at s5 + 32. So mode is the word stored in the cell, not the
   cell's address (found by a Theorem Labs lane's image-B lane, 2026-10-29 03:39Z). The released
   lib/U/Prog/fd_segments_c.v:56-61 fd_mode_ok, with S - FD_KEEP replaced by the frame's local. *)
Definition dec_a_mode_ok (cx : dctx) (W' : world segs) (mem' : word -> option byte) (mode nch ns : Z) : Prop :=
  (rdword (aview segs (w_H W') mem') (decode_obj 4) = Some mode \/
   rdword (aview segs (w_H W') mem') (decode_obj 5) = Some mode \/
   rdword (aview segs (w_H W') mem') (decode_obj 6) = Some mode \/ mode = d_F cx + 32) /\
  -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
  val_mem segs (rd W' mem') (mode + 4) 4%nat (nch mod 2 ^ 32) /\
  val_mem segs (rd W' mem') (mode + 8) 4%nat (ns mod 2 ^ 32).

(* The fill the harness leaves in a buffer no decoder wrote (memset 0xa5, then a refused call writes nothing). *)
Definition dec_a_filled (W' : world segs) (mem' : word -> option byte) (q len : Z) : Prop :=
  forall i, 0 <= i < len -> aview segs (w_H W') mem' (q + i) = Some DEC_FILL.

(* ------------------------------------------------------------------ *)
(* 3. The state at each cut point                                       *)
(* ------------------------------------------------------------------ *)

(* +0x074 — the return of __asan_stack_malloc_0 (+0x070). a0 is the frame the call returned; s3/s5/s11 are not
   set yet (they are written at +0x074, +0x080 and +0x0d4), the frame's shadow is still all zero (the poison is
   at +0x0d8..+0x0f8), and nothing is allocated or metered yet.
   Follows: lib/U/Prog/fd_segments_c.v:66-77 fd_seg_post's shape; there is no released counterpart for the call
   itself (the released images have no fake stack): the post is YG0d.v:285-300 astack_malloc_realizes'. *)
Definition llvm_a_st_074 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x074)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' dec_ev_074 /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) /\
    mo_le MT (d_S cx) S' (dec_spent_074 MT) /\ mo_ok MT S' (dec_rest_074 MT (d_n cx)) /\
    YK11.getr regs' 10 = w64 (d_F cx) /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 (d_n cx) /\
    YK11.getr regs' 24 = w64 (d_p cx) /\
    zero_shadow (aview segs (w_H W') mem') SHADOW_OFF (d_F cx) 64.

(* +0x104 — the early edge only: the machine is at the `bnez a0` of the size test (+0x0fc..+0x104) and a0, the
   top 38 bits of the size, is not zero. The frame record and its poison are written, the local is still
   poisoned (its unpoison is at +0x148), and 112(s1) holds the frame.
   Follows: lib/U/Prog/LLVMFuzzerTestOneInput_early.v:15-16 llvm_early_cond (`2 ^ 26 <= u`) and :60 llvm_early.
   dec_a_base pins 0 <= n < 2 ^ 26 (LLVMFuzzerTestOneInput_cg.v:107), so this state is unreachable from the
   slot pre; the edge is kept as its own statement because the listing has it. *)
Definition llvm_a_st_104 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x104)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' dec_ev_074 /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) /\
    mo_le MT (d_S cx) S' (dec_spent_074 MT) /\ mo_ok MT S' (dec_rest_074 MT (d_n cx)) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 10 = w64 (Z.shiftr (d_n cx) 26) /\
    2 ^ 26 <= d_n cx /\
    dec_a_fsh cx (aview segs (w_H W') mem') DEC_SH_MID DEC_SH_MID /\
    dec_a_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x234 — the return of malloc #1 (+0x230), the payload copy fuzz_dup asks for. a0 is the new block; the
   dispatch has run, so s10 is the copy's length, s8 the body pointer, s9/s7/s6 the mode and its two fields, and
   the frame's local holds `custom` (the three sw at +0x154..+0x15c or +0x1d4..+0x1dc). The copy is not filled
   yet: __asan_memcpy is at +0x250.
   Follows: lib/U/Prog/fd_entry.v:130-141 fd_entry_post — its `getr regs 9 = len`, `getr regs 25 = frame` and
   `getr regs 19 = mode` are s10, s4 (from +0x234 on) and s9 here, its fd_mode_ok is dec_a_mode_ok, and its
   `(forall a k, In (a,k) (blocks L0 A0) -> a <> frame)` is the appended block of amalloc04_rule
   (lib/Reusable/YC5d.v:73). *)
Definition llvm_a_st_234 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x234)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' dec_ev_234 /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] /\
    4096 <= res /\
    mo_le MT (d_S cx) S' (dec_spent_234 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_234 MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 10 = w64 res /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 (d_n cx) /\
    YK11.getr regs' 24 = w64 (d_p cx + dec_a_u (d_n cx)) /\
    YK11.getr regs' 26 = w64 (dec_a_len (d_n cx)) /\
    YK11.getr regs' 25 = w64 mode /\
    YK11.getr regs' 23 = w64 (mode + 4) /\
    YK11.getr regs' 22 = w64 (mode + 8) /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4 /\
    dec_a_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x3c0 — the return of malloc #2 (+0x3bc), the decode buffer. The copy is filled, reac_frame_is_reac and
   reac_frame_clean_len have been called and their two abort edges (+0x2b8, +0x2cc..+0x340) refuted, and the
   geometry has been read out of the mode and spilled.
   Follows: lib/U/Prog/fd_down.v:67's state after `g_malloc` — the released fd_down does the same malloc with
   the same olen bounds (fd_down.v:25 olen_bounds, 1 <= olen <= 48387). *)
Definition llvm_a_st_3c0 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x3c0)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' dec_ev_3c0 /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                       [(out, dec_a_olen nch ns)] /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_3c0 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_3c0 MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 10 = w64 out /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 26 = w64 (dec_a_len (d_n cx)) /\
    YK11.getr regs' 24 = w64 (dec_a_prod nch ns) /\
    YK11.getr regs' 25 = w64 (dec_a_olen nch ns) /\
    YK11.getr regs' 23 = w64 (ns mod 2 ^ 32) /\
    YK11.getr regs' 22 = w64 (mode + 8) /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 32 (dec_a_fits0 nch ns) /\
    dec_a_slot cx (aview segs (w_H W') mem') 48 (nch mod 2 ^ 64) /\
    dec_a_slot cx (aview segs (w_H W') mem') 64 mode /\
    dec_a_slot cx (aview segs (w_H W') mem') 80 (nch mod 2 ^ 32) /\
    dec_a_slot cx (aview segs (w_H W') mem') 88 (ns mod 2 ^ 64) /\
    dec_a_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x4fc — the return of reac_decode (+0x4f8). reac_frame_inspect and reac_frame_counter have been called and
   the five frame-field checks have run, so s10 is the harness's `wellformed`; s2 holds `fits` (+0x4d0), the
   shadow base having been spilled to 40(s1) at +0x46c; the buffer holds the decoder's output or is still the
   0xa5 fill.
   Follows: lib/U/Prog/fd_down.v:67's state after the reac_decode leaf; the return value and the two buffer
   cases are reac_decode_cg.v:97's dleaf_post (decode_ok / braid_out of lib/A/Prog/reac_decode_c.v:12, :23). *)
Definition llvm_a_st_4fc (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x4fc)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' dec_ev_4fc /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                       [(out, dec_a_olen nch ns)] /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_4fc MT (d_n cx)) /\ mo_ok MT S' (dec_rest_4fc MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 10 = w64 (if CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then ns else -1) /\
    YK11.getr regs' 18 = w64 (if dec_a_prod nch ns <? 481 then 1 else 0) /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 22 = w64 out /\
    YK11.getr regs' 23 = w64 (ns mod 2 ^ 32) /\
    YK11.getr regs' 24 = w64 (dec_a_prod nch ns) /\
    YK11.getr regs' 25 = w64 (dec_a_olen nch ns) /\
    YK11.getr regs' 26 = w64 (if CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) then 1 else 0) /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
       garr8 segs (rd W' mem') out
         (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns))) /\
    (CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = false ->
       dec_a_filled W' mem' out (dec_a_olen nch ns)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 32 (dec_a_fits0 nch ns) /\
    dec_a_slot cx (aview segs (w_H W') mem') 40 SHADOW_OFF /\
    dec_a_slot cx (aview segs (w_H W') mem') 48 (nch mod 2 ^ 64) /\
    dec_a_slot cx (aview segs (w_H W') mem') 56 (dec_a_len (d_n cx)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 64 mode /\
    dec_a_slot cx (aview segs (w_H W') mem') 72 out /\
    dec_a_slot cx (aview segs (w_H W') mem') 80 (nch mod 2 ^ 32) /\
    dec_a_slot cx (aview segs (w_H W') mem') 88 (ns mod 2 ^ 64) /\
    dec_a_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x5fc — the return of reac_decode_plain_le (+0x5f8). The decode result has been checked (+0x524), the scan
   loop L1 (+0x544..+0x570) has shown a refused decode left the fill, check_round_trip #1 and check_braid #1
   have run, and __asan_memset has refilled the buffer. s3 carries the buffer here and s7 the frame: the two were
   swapped at +0x590 and are swapped back at +0x610.
   Follows: lib/U/Prog/fd_down.v:67 after `g_crt` and the plain_le leaf; the return value and the two buffer
   cases are reac_decode_plain_le_cg.v:192 (plain_ok / plain_out, lib/A/Prog/reac_decode_plain_le_c.v:12, :18). *)
Definition llvm_a_st_5fc (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res out mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x5fc)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' dec_ev_5fc /\
    (* a Permutation from here on: check_round_trip #1's dec_crt_post (check_round_trip_cg.v:142) gives only
       that, and ablocks (YG01.v:212) has no canonical order *)
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                    [(out, dec_a_olen nch ns)]) /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S' (dec_spent_5fc MT (d_n cx)) /\ mo_ok MT S' (dec_rest_5fc MT) /\
    YK11.getr regs' 19 = w64 out /\ YK11.getr regs' 23 = w64 (d_F cx) /\
    YK11.getr regs' 21 = w64 (d_F cx) /\ YK11.getr regs' 27 = w64 (d_SH cx) /\
    YK11.getr regs' 10 = w64 (if CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then ns else -1) /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 22 = w64 (dec_a_len (d_n cx)) /\
    (* s8 is the harness's `wellformed && fits` of the plain check, built at +0x500..+0x50c out of s10, 32(s1)
       and the +0x4d0 size test; under the geometry of dec_a_mode_ok it is plain_ok, which is what the
       `bne a0,a1` at +0x604 of the next segment needs. *)
    YK11.getr regs' 24 = w64 (if CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then 1 else 0) /\
    YK11.getr regs' 25 = w64 (dec_a_olen nch ns) /\
    YK11.getr regs' 26 = w64 (ns mod 2 ^ 64) /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
       garr8 segs (rd W' mem') out
         (map (fun b : byte => bv_unsigned b) (CPlain.plain_out (d_body cx) nch ns))) /\
    (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = false ->
       dec_a_filled W' mem' out (dec_a_olen nch ns)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 32 (ns mod 2 ^ 32) /\
    dec_a_slot cx (aview segs (w_H W') mem') 40 SHADOW_OFF /\
    dec_a_slot cx (aview segs (w_H W') mem') 48 (nch mod 2 ^ 64) /\
    dec_a_slot cx (aview segs (w_H W') mem') 56 (dec_a_len (d_n cx)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 64 mode /\
    dec_a_slot cx (aview segs (w_H W') mem') 72 out /\
    dec_a_slot cx (aview segs (w_H W') mem') 80 (nch mod 2 ^ 32) /\
    dec_a_slot cx (aview segs (w_H W') mem') 88 (ns mod 2 ^ 64) /\
    dec_a_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x748 — the return of reac_upstream_channels (+0x744). The plain result has been checked (+0x604), the scan
   loop L2 (+0x624..+0x650) and the bcmp double loop L3/L4 (+0x6c0..+0x714) have run and their abort edges are
   refuted, the decode buffer has been freed (+0x738), and the five spilled callee-saved registers are back
   (+0x718..+0x72c). a0 is the channel count.
   Follows: lib/U/Prog/fd_up.v:55's entry state, i.e. lib/U/Prog/fd_segments_c.v:78-80 fd_up_regs
   (len, frame, frame + 50) — here s10, s4 and 64(s1) — plus reac_upstream_channels_cg.v:337's return
   (upstream_result of lib/A/Prog/reac_upstream_channels_c.v:17). *)
Definition llvm_a_st_748 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x748)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' dec_ev_748 /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))]) /\
    4096 <= res /\
    mo_le MT (d_S cx) S' (dec_spent_748 MT (d_n cx)) /\ mo_ok MT S' (dec_rest_748 MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 10 = w64 (CChan.upstream_result (dec_a_len (d_n cx))) /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 26 = w64 (dec_a_len (d_n cx)) /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (* the four words stored at +0x680..+0x68c, which the `blez a0` at +0x674 skips when the plain check failed
       (a0 = if plain_ok .. then ns else -1, llvm_a_st_5fc); nothing at or after +0x734 reads them *)
    (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
       dec_a_slot cx (aview segs (w_H W') mem') 8 res /\
       dec_a_slot cx (aview segs (w_H W') mem') 16 (d_SH cx) /\
       dec_a_slot cx (aview segs (w_H W') mem') 24 (d_F cx) /\
       dec_a_slot cx (aview segs (w_H W') mem') 48 (d_F cx)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 40 SHADOW_OFF /\
    dec_a_slot cx (aview segs (w_H W') mem') 56 (dec_a_len (d_n cx)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 64 (res + 50) /\
    dec_a_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x86c — the return of reac_upstream_decode #3 (+0x868). The channel count has been checked against the
   harness's own geometry (+0x79c), the upstream buffer has been allocated (+0x7c0) and filled with 0xa5
   (+0x7d4), the two refusing calls have run (+0x7e4, +0x7f8) and the scan loop L5 (+0x818..+0x844) has shown
   they wrote nothing. a0 is the third call's return.
   Follows: lib/U/Prog/fd_up.v:55 after its `g_malloc` and the upstream leaves; the return value and the written
   range are reac_upstream_decode_cg.v:91 (up_ok / up_nch of lib/A/Prog/reac_upstream_decode_c.v:14, :18). *)
Definition llvm_a_st_86c (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (res upb mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x86c)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' dec_ev_86c /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                                    [(upb, dec_a_uolen (CChan.upstream_result (dec_a_len (d_n cx))))]) /\
    4096 <= res /\ 4096 <= upb /\
    mo_le MT (d_S cx) S' (dec_spent_86c MT (d_n cx)) /\ mo_ok MT S' (dec_rest_86c MT) /\
    dec_a_fr cx regs' /\
    YK11.getr regs' 10 =
      w64 (if CUp.up_ok res upb (dec_a_len (d_n cx)) (d_body cx) then 12 else -1) /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 20 = w64 res /\
    YK11.getr regs' 22 = w64 (CChan.upstream_result (dec_a_len (d_n cx))) /\
    YK11.getr regs' 23 = w64 upb /\
    YK11.getr regs' 24 = w64 (dec_a_uolen (CChan.upstream_result (dec_a_len (d_n cx)))) /\
    YK11.getr regs' 26 = w64 (dec_a_len (d_n cx)) /\
    dec_a_mode_ok cx W' mem' mode nch ns /\
    dec_a_fsh cx (aview segs (w_H W') mem') 0 4 /\
    garr8 segs (rd W' mem') res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    (CUp.up_ok res upb (dec_a_len (d_n cx)) (d_body cx) = true ->
       garr8 segs (rd W' mem') upb
         (map (fun b : byte => bv_unsigned b)
            (CDec.braid_out (d_body cx) (CUp.up_nch (dec_a_len (d_n cx))) 12))) /\
    (CUp.up_ok res upb (dec_a_len (d_n cx)) (d_body cx) = false ->
       dec_a_filled W' mem' upb (dec_a_uolen (CChan.upstream_result (dec_a_len (d_n cx))))) /\
    (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
       dec_a_slot cx (aview segs (w_H W') mem') 8 res /\
       dec_a_slot cx (aview segs (w_H W') mem') 16 (d_SH cx) /\
       dec_a_slot cx (aview segs (w_H W') mem') 24 (d_F cx) /\
       dec_a_slot cx (aview segs (w_H W') mem') 48 (d_F cx)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 40 SHADOW_OFF /\
    dec_a_slot cx (aview segs (w_H W') mem') 56 (dec_a_len (d_n cx)) /\
    dec_a_slot cx (aview segs (w_H W') mem') 64 (res + 50) /\
    dec_a_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* +0x9a8 — the join of the two returns: the normal path arrives from free #3 (+0x998) with the local
   re-poisoned (+0x99c..+0x9a4), and the early path jumps here straight from +0x104 with the local never
   unpoisoned. Both leave the same picture: every block this function took is gone, the frame's eight shadow
   bytes are the entry poison, and s3/s5/s11 still carry the frame.
   Follows: lib/U/Prog/fd_segments_c.v:81 fd_exit_regs (the frame pointer alone) and
   lib/U/Prog/LLVMFuzzerTestOneInput_early.v:60 llvm_early, which joins the same teardown on that image. *)
Definition llvm_a_st_9a8 (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x9a8)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_a_core cx ly' S' W' regs' mem' md' k /\ k <= dec_ev_9a8 /\
    Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx)) /\
    mo_le MT (d_S cx) S' (dec_spent_9a8 MT (d_n cx)) /\
    dec_a_fr cx regs' /\
    dec_a_fsh cx (aview segs (w_H W') mem') DEC_SH_MID DEC_SH_MID.

(* The slot's post at the return (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:139-144), at the one leaf
   decode_shape's LIBK hands the continuation (lib/FrameSlotK.v:40: LIBK pl fs K = K (LL 0 fs [])). *)
Definition dec_a_post (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
    c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    @dec_lib_post_x rc asink_syms tfib_K asink_none ameta_inv B MT XL
      (d_regs cx) (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) (d_p cx) (d_n cx) (d_M cx)
      (YO09.LL 0 (m_fs (d_md cx)) []) ly' S' W' regs' mem' md' k.

(* ------------------------------------------------------------------ *)
(* 4. The nine segment statements                                       *)
(* ------------------------------------------------------------------ *)

(* +0x000 .. +0x070. Prologue, 13 saves, s0/s1, the shadow base out of the GOT word and the cell
   (+0x054..+0x060, which is why dec_crt_cells is a premise), the use-after-return flag, and the class-0
   stack malloc. The frame position fpos the call picks is the existential the rest of the walk is built on
   (cgif lib/A/ACez.v:46-57, whose `exists fpos sp1 E0` this is: sp1 is a closed form of sp here and there is
   no symbolic env). *)
Definition llvm_a_entry_stmt : Prop :=
  pc_stack_malloc (as_code B) 0 = decode_sigma DS___asan_stack_malloc_0 ->
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
         llvm_a_st_074 (mkDCtx fx ly S W regs mem md p n pl M fpos) W' c').

(* +0x074 .. +0x230. s3/s5/s11, the ASan frame record and its redzone poison, the size test (+0x0fc..+0x104,
   whose taken edge is llvm_a_st_104), the three fuzz_u8 reads with their shadow checks (+0x118, +0x174,
   +0x1a0), the length dispatch, the mode-table select, the local's unpoison, and malloc #1. *)
Definition llvm_a_early_stmt : Prop :=
  pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B ->
  (* the mode-table select's three PLdHi loads of decode_obj 4 / 5 / 6 (+0x160, +0x1ec, +0x200, +0x20c) read
     the pointer cells, whose values only the as_const rows of dec_crt_cells B give *)
  dec_crt_cells B ->
  (* the tables' +4 / +8 words are DEC_RO_RD bytes: the journal's image clause gives them from HROM once
     dec_ro_rd_scoped keeps them off the owned statics and errno *)
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc tfib_sink_head segs B MT) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_a_base cx -> dec_a_rom cx -> llvm_a_st_074 cx W' c' ->
    SRr segs W' c' (fun W2 c2 => llvm_a_st_234 cx W2 c2 \/ llvm_a_st_104 cx W2 c2).

(* +0x104 -> +0x9a8: the `bnez a0` of the size test taken. Nothing but the jump: the teardown that follows is
   llvm_a_exit_stmt's second entry. dec_a_base pins n < 2 ^ 26, so the state this starts from is unreachable;
   the statement is kept because the listing's edge is (lib/U/Prog/LLVMFuzzerTestOneInput_early.v:60). *)
Definition llvm_a_early_ret_stmt : Prop :=
  AR_laws segs B -> ameter_laws MT ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_a_base cx -> dec_a_rom cx -> llvm_a_st_104 cx W' c' ->
    SRr segs W' c' (llvm_a_st_9a8 cx).

(* +0x234 .. +0x3bc. The NULL check of the copy (+0x23c, refuted by 4096 <= res), __asan_memcpy, the two
   reac_frame_is_reac calls with their two shadow-checked header reads, reac_frame_clean_len and the five
   abort edges of the clean-length algebra (+0x2b8, +0x2cc, +0x2d4, +0x2fc, +0x340), the two four-byte shadow
   checks on the mode fields (+0x344, +0x354), the geometry spills, and malloc #2. *)
Definition llvm_a_copy_stmt : Prop :=
  pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B ->
  (* read-only reads after the entry memory: the two ÷36 constants of the clean-length test, `ld a1` of
     decode_obj 7 at +0x2dc and `ld a3` of decode_obj 8 at +0x2e8, and reac_frame_clean_len's own reads of the same
     words (DEC_RO_RD); the journal's image clause gives them from HROM once dec_ro_rd_scoped keeps them off the
     owned statics and errno *)
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (decode_sigma DS___asan_memcpy)) ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LIsReac.dec_reac_frame_is_reac_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCleanLen.dec_reac_frame_clean_len_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_a_base cx -> dec_a_rom cx -> llvm_a_st_234 cx W' c' ->
    SRr segs W' c' (llvm_a_st_3c0 cx).

(* +0x3c0 .. +0x4f8. The NULL check of the decode buffer (+0x3c0), reac_frame_inspect, the five frame-field
   checks with their five shadow checks, reac_frame_counter, the inspect/counter abort edges (+0x474, +0x4c0,
   +0x4cc), __asan_memset of the buffer, and reac_decode. *)
Definition llvm_a_inspect_stmt : Prop :=
  dec_crt_cells B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decode_sigma DS___asan_memset)) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCounter.dec_reac_frame_counter_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LInspect.dec_reac_frame_inspect_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LDecode.dec_reac_decode_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_a_base cx -> dec_a_rom cx -> llvm_a_st_3c0 cx W' c' ->
    SRr segs W' c' (llvm_a_st_4fc cx).

(* +0x4fc .. +0x5f8. The decode-result check (+0x524), the scan loop L1 with its shadow slow path
   (+0x544..+0x584), check_round_trip #1, check_braid #1, __asan_memset, and reac_decode_plain_le. *)
Definition llvm_a_crt1_stmt : Prop :=
  dec_crt_cells B ->
  (* read-only reads after the entry memory: check_round_trip #1 takes dec_rom_view_rd at its call memory (the
     read-only view at the DEC_RO_RD bytes, check_round_trip_cg.v), its braid leaf reading FCLAMP_HI; the journal's
     image clause gives it from HROM once dec_ro_rd_scoped keeps those bytes off the owned statics and errno *)
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decode_sigma DS___asan_memset)) ->
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decode_sigma DS_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_a_base cx -> dec_a_rom cx -> llvm_a_st_4fc cx W' c' ->
    SRr segs W' c' (llvm_a_st_5fc cx).

(* +0x5fc .. +0x744. The plain-result check (+0x604), the scan loop L2 (+0x624..+0x664), the bcmp double loop
   L3/L4 with its __interceptor_trampoline_bcmp call, the mismatch abort edge (+0x730), free #1 of the decode
   buffer, and reac_upstream_channels. *)
Definition llvm_a_cmp_stmt : Prop :=
  pc_wrap_free (as_code B) = decode_sigma DS___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B ->
  (* read-only reads after the entry memory: reac_upstream_channels's ÷36 multiplier (the word at decode_obj 9,
     its UPSTREAM_DIV36_AT); the journal's image clause gives it from HROM once dec_ro_rd_scoped keeps it off the
     owned statics and errno *)
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @abcmp_realizes fx rc segs B (decode_sigma DS___interceptor_trampoline_bcmp)) ->
  (forall fx : YK11.FPState, @afree04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LUpChannels.dec_reac_upstream_channels_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_a_base cx -> dec_a_rom cx -> llvm_a_st_5fc cx W' c' ->
    SRr segs W' c' (llvm_a_st_748 cx).

(* +0x748 .. +0x868. The channel-count check (+0x79c), malloc #3, its NULL check (+0x7c4), __asan_memset of the
   upstream buffer, the two refusing reac_upstream_decode calls and their two abort edges (+0x800, +0x804), the
   scan loop L5 (+0x818..+0x854) and its abort edge (+0x858), and reac_upstream_decode #3. *)
Definition llvm_a_up_stmt : Prop :=
  pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B ->
  (* read-only reads after the entry memory: `ld a1` of decode_obj 9 at +0x75c (the ÷36 multiplier of the
     channel check) and reac_upstream_decode's read of the same word; the journal's image clause gives them from
     HROM once dec_ro_rd_scoped keeps them off the owned statics and errno *)
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decode_sigma DS___asan_memset)) ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LUpDecode.dec_reac_upstream_decode_cg) fx) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_a_base cx -> dec_a_rom cx -> llvm_a_st_748 cx W' c' ->
    SRr segs W' c' (llvm_a_st_86c cx).

(* +0x86c .. +0xa48, with the second entry at +0x9a8. The four shadow-checked upstream header checks, the scan
   loop L6 (+0x914..+0x954), check_round_trip #2, check_braid #2, free #2 and free #3, the shadow teardown
   (+0x99c..+0xa04: the freed magic, then the fake frame's 0xf5 and its flag byte), the 13 reloads, and `ret`.
   HSINK_KEPT and HMETA_KEPT are needed here and nowhere else: the post asks asink_none and ameta_inv at the
   return memory, which differs from the entry memory by the fake frame and its shadow. *)
Definition llvm_a_exit_stmt : Prop :=
  pc_wrap_free (as_code B) = decode_sigma DS___interceptor_trampoline_free ->
  dec_llvmf_utraces RA_LLVMF B ->
  dec_crt_cells B ->
  (* read-only reads after the entry memory: check_round_trip #2 takes dec_rom_view_rd at its call memory (the
     read-only view at the DEC_RO_RD bytes, check_round_trip_cg.v), its braid leaf reading FCLAMP_HI; the journal's
     image clause gives it from HROM once dec_ro_rd_scoped keeps those bytes off the owned statics and errno *)
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  (* dec_a_post asks mo_le .. (XL n) and the walk spends dec_spent_9a8 MT n = dec_llvmf_cost MT n
     (dec_cost_ladder); this is the statement's own bound between the two (LLVMFuzzerTestOneInput_cg.v:242). *)
  (forall nn, 0 <= nn -> dec_llvmf_cost MT nn <= XL nn) ->
  astack_free_law segs B -> frame_flag_lawP segs B ->
  (forall fx : YK11.FPState, @afree04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decode_sigma DS_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx) ->
  (* HSINK_KEPT / HMETA_KEPT, in dec_llvmf_holds_stmt's own text (LLVMFuzzerTestOneInput_cg.v:231-236) *)
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  forall (cx : dctx) (W' : world segs) (c' : config),
    dec_a_base cx -> dec_a_rom cx -> (llvm_a_st_86c cx W' c' \/ llvm_a_st_9a8 cx W' c') ->
    SRr segs W' c' (dec_a_post cx).

(* ------------------------------------------------------------------ *)
(* 5. The composition                                                   *)
(* ------------------------------------------------------------------ *)

(* The slot post with the frame position the entry invented still existentially quantified: what the chain
   below proves and what the contract's own continuation asks for (cgif lib/A/ACfj.v:252's
   `(fpos & sp1 & E0 & HPOST)`). *)
Definition dec_a_post_ex (fx : YK11.FPState) (ly : alayout) (S : astate) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) :
    world segs -> config -> Prop :=
  fun W' c' => exists fpos, dec_a_post (mkDCtx fx ly S W regs mem md p n pl M fpos) W' c'.

(* cgif lib/A/ACfh.v:47, copied: an SRr obligation whose post is "AI gives srealizes" is a srealizes. *)
Lemma dec_srz_enter : forall (W : world segs) (c : config) (T : TSet),
  AI segs (w_H W) (w_A W) (cfg_model c) ->
  SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) ->
  srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

(* The walk from the nine segments, as cgif's lib/A/ACfj.v:230-259 composes its stages. *)
Theorem dec_llvmf_holds_of_segs :
  llvm_a_entry_stmt -> llvm_a_early_stmt -> llvm_a_early_ret_stmt -> llvm_a_copy_stmt ->
  llvm_a_inspect_stmt -> llvm_a_crt1_stmt -> llvm_a_cmp_stmt -> llvm_a_up_stmt -> llvm_a_exit_stmt ->
  dec_llvmf_holds_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS asink_img_laws ro_below_ofl
    RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
intros ENTRY EARLY EARLYRET COPY INSPECT CRT1 CMP UP EXIT.
unfold dec_llvmf_holds_stmt.
intros HPCM HPCF HPCS HCELLS HROZ HRNE HUTR LAWS ML MTL MTF SMP ASF FFL AIL HSINK_KEPT HMETA_KEPT ROB ASM0 AMEMSET
  AMEMCPY AMALLOC AFREE ABCMP ACRT LIS LCL LCT LIN LDE LPL LUC LUD LCB HXL.
intros fx ly S W regs mem md p n pl M K HAI HPRE HK.
change (@LIBK DShape.decode_shape pl (m_fs md) K) with (K (YO09.LL 0 (m_fs md) [])).
eapply dec_srz_enter; [exact HAI|].
eapply (SRr_mono segs W (@cfg_at fx segs DEC_A_LLVMF regs mem md)
          (dec_a_post_ex fx ly S W regs mem md p n pl M)).
- (* the chain *)
  eapply SRr_bind;
    [ exact (ENTRY HPCS HCELLS LAWS ML MTL MTF SMP ASM0 fx ly S W regs mem md p n pl M HPRE (HROM fx ly S W regs mem md p n pl M HPRE) HXL) |].
  intros W1 c1 _ (fpos & H074).
  set (cx := mkDCtx fx ly S W regs mem md p n pl M fpos) in *.
  assert (HB : dec_a_base cx) by exact HPRE.
  assert (HR : dec_a_rom cx) by exact (HROM fx ly S W regs mem md p n pl M HPRE).
  eapply SRr_bind; [ exact (EARLY HPCM HUTR HCELLS HROZ HRNE LAWS ML MTL AMALLOC cx W1 c1 HB HR H074) |].
  intros W2 c2 _ [H234 | H104].
  + eapply SRr_bind; [ exact (COPY HPCM HUTR HCELLS HROZ HRNE LAWS ML MTL AMEMCPY AMALLOC LIS LCL cx W2 c2 HB HR H234) |].
    intros W3 c3 _ H3c0.
    eapply SRr_bind; [ exact (INSPECT HCELLS LAWS ML MTL AMEMSET LCT LIN LDE cx W3 c3 HB HR H3c0) |].
    intros W4 c4 _ H4fc.
    eapply SRr_bind; [ exact (CRT1 HCELLS HROZ HRNE LAWS ML MTL MTF AMEMSET ACRT LCB LPL cx W4 c4 HB HR H4fc) |].
    intros W5 c5 _ H5fc.
    eapply SRr_bind; [ exact (CMP HPCF HUTR HCELLS HROZ HRNE LAWS ML MTL ABCMP AFREE LUC cx W5 c5 HB HR H5fc) |].
    intros W6 c6 _ H748.
    eapply SRr_bind; [ exact (UP HPCM HUTR HCELLS HROZ HRNE LAWS ML MTL AMEMSET AMALLOC LUD cx W6 c6 HB HR H748) |].
    intros W7 c7 _ H86c.
    eapply SRr_mono;
      [ exact (EXIT HPCF HUTR HCELLS HROZ HRNE LAWS ML MTL MTF HXL ASF FFL AFREE ACRT LCB HSINK_KEPT HMETA_KEPT cx W7 c7 HB HR
                 (or_introl H86c)) |].
    intros W8 c8 _ HP. unfold dec_a_post_ex. exists fpos. exact HP.
  + eapply SRr_bind; [ exact (EARLYRET LAWS MTL cx W2 c2 HB HR H104) |].
    intros W3 c3 _ H9a8.
    eapply SRr_mono;
      [ exact (EXIT HPCF HUTR HCELLS HROZ HRNE LAWS ML MTL MTF HXL ASF FFL AFREE ACRT LCB HSINK_KEPT HMETA_KEPT cx W3 c3 HB HR
                 (or_intror H9a8)) |].
    intros W8 c8 _ HP. unfold dec_a_post_ex. exists fpos. exact HP.
- intros W' c' Hwle HP HAI'. unfold dec_a_post_ex in HP. destruct HP as (fpos & HP).
  apply (HK (YO09.LL 0 (m_fs md) []) W' c' Hwle HAI'). exact HP.
Qed.

End seg.

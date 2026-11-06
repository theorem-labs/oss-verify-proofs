(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 2971 of its 3154 lines of code are new or changed and 4870 lines of the source are left out. *)
(* fuzz_preset, slice S5b, image A (asan): the BOUNDARY STATE of parse_value's entry segment -- the register save,
   the ASan frame, the white-space skip and the dispatch -- which the four arm lanes consume.

   Lane VproA of worker a Theorem Labs lane. rule 24: no function is proved here.

   WHAT THE SEGMENT IS. Rows of the neutral listing of the pinned rebuilt image
   (parse_value's disassembly in the #102 pin A' image; a row is a line of that disassembly, so row N is at
   0x85f10 + 4 * (N - 2)):
     rows  1.. 19  the frame: sp -= 0xa0, ra and the 13 callee-saved registers to [sp0 - 0xa0, sp0), s0 = sp0,
                   sp &= -0x20, s1 = sp, s3 = v (a1), s4 = q (a0), s7 = the shadow offset (read through the GOT word
                   A_OBJ 0 and the cell A_OBJ 12), and the use-after-return flag through the GOT word A_OBJ 1;
     rows 20.. 43  the frame allocation. Row 29 loads 0x40 and row 30 is `jal -0x48438 <frame_alloc_0>`
                   (__asan_stack_malloc_0, class 0). TWO ARMS, joining at parse_value+0x80:
                     rows 31-32  s2 = the returned FAKE frame;
                     rows 33-43  s2 = 0, and the frame is built on the REAL stack with a page probe.
                   THE REAL-STACK ARM IS EXCLUDED BY A PREMISE, not proved -- see THE CLASS-FULL ARM below;
     rows 44.. 62  the frame header words at s10 (kCurrentStackFrameMagic 0x41B58AB3, the descriptor, the function's
                   own pc) and the 8 shadow bytes at s8 = shadow_addr s10: f1 f1 f1 f1 f8 f3 f3 f3;
     rows 63..101  the white-space skip over {0x09, 0x0a, 0x0d, 0x20} (= PjGrammar.ws): the loop re-reads in->p and
                   the text byte and writes in->p back. Its ASan slow block falls through to `jal errpath_load1` at
                   row 101, an ASan REPORT: that call is UNREACHABLE under the premises and is discharged from the
                   shadow premises (src_rd's range_addressable over the text), never by assuming a contract for an
                   errpath_* symbol;
     rows 102..130 the dispatch on the first non-white byte, down to the branch that selects the arm.

   WHERE EACH ARM LANE STARTS. vrd_arm_off below, as offsets from parse_value's entry, each confirmed against the
   listing's own `<parse_value+0x...>` annotation on the branch that reaches it:
     VA_eof   +0x1e4 (row 123)  p = end: s5 = -1, then the shared epilogue
     VA_false +0x1d4 (row 119)  byte 0x66      VA_obj  +0x204 (row 131)  byte 0x7b
     VA_str   +0x214 (row 135)  byte 0x22      VA_null +0x258 (row 152)  byte 0x6e
     VA_num   +0x26c (row 157)  any other byte VA_arr  +0x34c (row 213)  byte 0x5b
     VA_true  +0x360 (row 218)  byte 0x74
   Each arm lane therefore starts at the arm's OWN first row, and this segment sets no argument register for any arm:
   the dispatch state is the SAME on every arm, and only the byte differs. That is one group of rows away from
   brief-vstr's reading, which starts the string arm at row 142 (the `jal parse_string`) and the container arm at row
   213: rows 135..141 (the shadow gate of v and the store `v->type = 4`) are the STRING ARM's here, not this
   segment's, and rows 131..133 / 213..215 (the three argument moves) are the CONTAINER ARM's. a Theorem Labs lane relayed this
   split as the boundary of record. With it, this segment writes no byte of v. Its only stores go to its own stack
   window, to its own fake frame and that frame's shadow, and to the cursor's p word, and the plain awr_byte admits
   all of them. Every store to v belongs to an arm lane. When v lies in a CALLER's live fake frame (prhReader_at's
   third disjunct), the arm lane runs that row with YC80xf.paj_run_xf, whose write premise awr_ok_fr admits a byte
   that the footprint rd_fp q v names inside a frame of the journal's entry state (YCbqG.v:522 wr_fp_frame). So no
   lane narrows the node premise.

   THE CLASS-FULL ARM. When class 0 is full, frame_alloc_0 returns NULL, rows 33..43 build the frame on the REAL
   stack, and rows 50..61 write the 8 non-zero shadow bytes at shadow_addr s10 with s10 inside
   [ly_stk_lo ly, ly_stk_hi ly). ARcf contains ARmcf, whose field amc_zshadow (YG0ncf.v:102) is zshadow_ok, and
   zero_shadow_ranges (YG0n.v:189) begins with the whole stack range: every shadow byte of the stack is 0. So no
   state of that arm satisfies ARx, hence none satisfies ajournal_x, and no post of the frozen form can hold there.
   This lane measured that, and tparse_value_specX now carries the excluding premise
     Z.of_nat (length (frames S)) + Z.of_nat (Nat.succ (PjGrammar.MAXD - d)) <= fs_frames 0
   (the recursion-aware form of cgif's own constant, YC20.v:139 `length (frames S) <= 8`). vrd_disp_a hands on the
   same bound with one frame taken, which is exactly parse_items' premise at the same nesting.

   CALLEE CONTRACTS. One callee is reached before the dispatch: frame_alloc_0. Its contract is the PROVED
   FCm0s.stack_malloc0_contract_x (a Theorem Labs lane's PresetFrameClasses lane, over FCiface.fs_iface), not a hypothesis;
   tfibsegs (AB1v.v:3) and rsegs (Img0.v:3) are both Asan.M.loaded_segments, so it applies at PI_prog_A unchanged.
   The step it does not give is the apath witness its own premise asks for: that is H_fs_progress_0, the cf twin of
   cgif's stack_malloc_progressP (YCbq.v:803), discharged at the instance by YG05cf.stack_malloc_progress_cf at
   ARmcf's amc_wf. No contract is assumed for any errpath_* symbol.

   THE MEMORY INVARIANT IN EVERY SEGMENT (a Theorem Labs lane's 12:18Z ruling): an SRr post is opaque once Qed, so an end-state
   memory invariant must be in the segment's STATEMENT; the generic SRr_memnorm was measured NOT provable (a Theorem Labs lane),
   so it cannot be added afterwards. Each call-free segment lemma X has a twin X_inv
     forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> <X's premises> -> P (the start memory) ->
       SRr SEGS W c (fun W' c' => <X's post> W' c' /\ P (ms_mem (cfg_ms c')))
   (YSRrMemnorm.v, a working branch 161f89a71b4 blob a1c1ece77b14: the runs are its paj_run_x_inv /
   paj_run_to_x_inv, the twins of the paj_run_x / paj_run_to_x this walk uses; no run here is an xf run, so
   YC80xf_inv.v is not needed), and X itself is the corollary at P := fun _ => True (vrd_true_laws, vrd_srr_drop), its
   statement byte-identical to c773f2a0dde's. The two segments that cross the class-0 frame call (vrd_seg1, vrd_pro_a)
   get a *_P lemma BESIDE the old one, not a corollary chain: P crosses the call by srr_inv_call through the memnorm
   keep of YGcallMxmn.aj_stack_malloc_at_xm (a working branch 8e33ecc4965b blob 87de220caca2), and that
   rule needs the class-0 contract WITH the keep: the PROVED FCm01xm.stack_malloc0_contract_xm B ARx FSI TB, cited
   (lib/A/FCm01xm.v blob 0078db007a0f with the frame-class walks generalised over a memory predicate, FCm0s.v blob
   1e98e4a49385 / FCm1s.v blob ecdb46b7cc62, all by path from a working branch d05d97a3600, on the
   18-field engine pair the record texts 51daa1e80a99 carry). So the *_P lemmas have no premise beyond srr_inv_laws and
   srr_inv_call. The old vrd_seg1 / vrd_pro_a keep their proofs over the proved FCm0s.stack_malloc0_contract_x. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0ncf YG0dcf YG0sshcf YGcfRoomPre YGcfRoomKeep YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallMx YGcallSx FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW YN0d YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoom PresetReqAt PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img CfParamsPreset FCm0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FCm01xm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the arms of the dispatch, and the pc each arm lane starts at ---- *)

Inductive vrd_arm : Type :=
| VA_eof | VA_false | VA_obj | VA_str | VA_null | VA_num | VA_arr | VA_true.

Definition vrd_arm_off (arm : vrd_arm) : Z :=
  match arm with
  | VA_eof => 0x1e4 | VA_false => 0x1d4 | VA_obj => 0x204 | VA_str => 0x214
  | VA_null => 0x258 | VA_num => 0x26c | VA_arr => 0x34c | VA_true => 0x360
  end.

(* the arm the dispatch tree selects for a first non-white byte b: rows 110..130 compare b against 0x6d, then
   0x22 / 0x5b / 0x66 below it and 0x6e / 0x74 / 0x7b above it, and every other byte falls to the number arm *)
Definition vrd_arm_of (b : Z) : vrd_arm :=
  if b =? 34 then VA_str
  else if b =? 91 then VA_arr
  else if b =? 102 then VA_false
  else if b =? 110 then VA_null
  else if b =? 116 then VA_true
  else if b =? 123 then VA_obj
  else VA_num.

Section c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the room is the kit's invariant room_live_cf (class PrhRoomLive, PRH_Base.v), carried, not counted; the realloc
   trace pc is CfImg.cf_pc_realloc_ra0, cited directly. No named-hypothesis context is left here. *)
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the pieces of the dispatch state ---- *)

(* the 13 callee-saved words parse_value wrote to [sp0 - 0xa0, sp0) (rows 3..16), which its epilogue reloads *)
Definition vrd_saved (m : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
  val_mem segs m (sp0 - 8) 8 (raZ regs0) /\
  val_mem segs m (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem segs m (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
  val_mem segs m (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
  val_mem segs m (sp0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
  val_mem segs m (sp0 - 48) 8 (bv_unsigned (getr regs0 20)) /\
  val_mem segs m (sp0 - 56) 8 (bv_unsigned (getr regs0 21)) /\
  val_mem segs m (sp0 - 64) 8 (bv_unsigned (getr regs0 22)) /\
  val_mem segs m (sp0 - 72) 8 (bv_unsigned (getr regs0 23)) /\
  val_mem segs m (sp0 - 80) 8 (bv_unsigned (getr regs0 24)) /\
  val_mem segs m (sp0 - 88) 8 (bv_unsigned (getr regs0 25)) /\
  val_mem segs m (sp0 - 96) 8 (bv_unsigned (getr regs0 26)) /\
  val_mem segs m (sp0 - 104) 8 (bv_unsigned (getr regs0 27)).

(* the shadow of the class-0 frame after rows 53..61. Granule 4 is 0xf8 (use-after-scope) -- it is the `end` local
   that the number arm unpoisons at row 157 -- and granules 5..7 are 0xf3 (right redzone). *)
Definition vrd_frame_shadow : list Z := [0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf3; 0xf3; 0xf3].

(* the ASan frame this call owns: its header words (rows 46..48), the flag word the allocator wrote at the end of the
   class-0 frame (fs_frame_bytes 0 = 64, so F + 56; aj_stack_malloc_at_x's post, which this segment never overwrites)
   and its shadow. The epilogue reads that word at row 238 and clears the flag through it. *)
Definition vrd_frame (W : world segs) (m : word -> option byte) (ly : alayout) (pos : Z) : Prop :=
  let F := frame_addr ly 0 pos in
  val_mem segs (mrestrict (w_H W) m) F 8 0x41B58AB3 /\
  val_mem segs (mrestrict (w_H W) m) (F + 16) 8 (pa_sigma AS_parse_value) /\
  val_mem segs (mrestrict (w_H W) m) (F + 56) 8 (flag_addr ly 0 pos) /\
  (forall i, 0 <= i < 8 ->
     aview segs (w_H W) m (SHADOW_OFF + F / 8 + i) = Some (nth (Z.to_nat i) vrd_frame_shadow 0)).

(* the registers at the dispatch. s0 = the entry sp, sp = s1 = the 32-aligned frame, s2 = s10 = the fake frame,
   s3 = v, s4 = q, s7 = the shadow offset, s8 = shadow_addr s10, s11 = shadow_addr q; s5, s6, s9 still hold the
   caller's values; a0 = the cursor after the white space, a2 = in->end. *)
Definition vrd_regs (regs0 regs : bvmap 5 word) (ly : alayout) (pos q v p' text len : Z) : Prop :=
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

(* the dispatch state without its pc equation: the arm and its witnesses are parameters (VrdNum's vrd_num266_a
   states the same state at another pc and cites this body) *)
Definition vrd_disp_body
  (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)) (CTX0 : list (list Z)) (CW : list (list Z))
  (e q v text len p : Z) (d : nat) (tb : list Z)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  (arm : vrd_arm) (pos p' k : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  (* the white space the loop consumed, and the byte that chose the arm *)
  rest_atR tb text p' = PjGrammar.skip (rest_atR tb text p) /\
  p <= p' <= text + len /\
  match PjGrammar.skip (rest_atR tb text p) with
  | [] => arm = VA_eof /\ p' = text + len
  | b :: _ => arm = vrd_arm_of b /\ p' < text + len /\
              nth_error tb (Z.to_nat (p' - text)) = Some b /\ PjGrammar.ws b = false /\
              getr regs 11 = w64 b
  end /\
  (* the journal of the segment, at the caller-window stack of the frozen post *)
  ajournal_x (SK := SK) segs B prh_pst ARx (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
    ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k /\
  frames S = (0, pos) :: frames S0 /\ ablocks B ly S = ablocks B ly0 S0 /\ Hp = Hp0 /\
  (* the only allocator change of the segment is the fake-frame take (stack_malloc's post), so blocks_bytes and the
     live requests read the dispatch state as the entry state (YG01.blocks_set_fs) *)
  (exists f, S = set_fs f S0) /\
  (* the caller's window outside the written cells is untouched *)
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a) /\
  fwin ly W regs0 mem e /\
  (* the frame, the saved registers, the register map. The CHAINS are the text's premises VERBATIM AT THE ENTRY STATE
     (tparse_value_specX, the kit's cut 7cdbb61b5fa0, PRH_FnParse.v blob f0d92dcec7e9): the entry call chain up to its
     spine, the call-graph universe closure and the cursor's stop word named at entry, and the partitioned cursor
     chain (the cursor set CW, prh_cw_entry, in the slot the deleted sp - 8 arm of prh_cur_entry vacated, is APPENDED
     at the end below). A chain at the dispatch view is not derivable (the white-space loop stores [q, q+8), which the
     entry chain may read: the refutation recorded in that file's header); each arm owns the chain at its own call,
     through the kit's closure read at its call state. *)
  vrd_frame W mem ly pos /\
  vrd_saved (rdW W mem) (spZ regs0) regs0 /\
  vrd_regs regs0 regs ly pos q v p' text len /\
  (exists ch', achain ly0 (aview segs (w_H W0) mem0) (spZ regs0) (s0Z regs0) ch' /\ spine ch' = spine ch) /\
  prh_univ_closure B CTX0 /\ prh_cur_entry W0 mem0 regs0 q /\
  ((spZ regs0 <= q < spZ regs0 + 16) \/
   (spZ regs0 + 16 <= q /\
    exists ch', achain ly0 (aview segs (w_H W0) mem0) (spZ regs0) (prh_s0 F_parse_string q) ch')) /\
  (* the cursor, advanced and written back; the node, untouched; the text, at home *)
  pj_in_okR segs (rdW W mem) q text len p' (Z.of_nat d) tb /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 24 /\
  prhPv_node B (STK_parse_value d) e ly S W regs0 mem Lam v /\
  (* carried from rd_pre unchanged (PRH_FnParse.v blob 94232293d483, rd_pre :175-195): the arms that call a
     reader function need prh_malloc_univ and the two realloc universe facts, the stores to v at rows 140 and 148 need
     the cursor and the text apart from the node, and parse_items' own rd_pre at the container arm needs the maxrun
     bound and the count bound. The count bound is at the ADVANCED cursor p', by vrd_rest_shrink. *)
  prh_malloc_univ B /\ spZ regs0 <= q /\ q + 24 <= spZ regs0 + e /\ (q + 24 <= v \/ v + 56 <= q) /\
  (* the entry gp, tp and return address with its lower bound (fpre's afn_pre_x), which every arm's call rule, the
     chain at its call (vrd_disp_chain) and the epilogue ask *)
  getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 (as_tp B) /\ YK0s.ret_ok (getr regs0 1) /\
  4096 <= raZ regs0 /\
  (* the cursor AT THE ENTRY VIEW (W0, mem0), at the entry's p: rd_pre's own pj_in_okR, verbatim. The body's other
     cursor fact (above) is at the DISPATCH view and names the advanced p'; the white-space loop overwrote the entry
     word, so only this conjunct names it (vrd_disp_chain's p0) *)
  pj_in_okR segs (rdW W0 mem0) q text len p (Z.of_nat d) tb /\
  (* the depth bound, rd_pre's own, verbatim *)
  (d <= PjGrammar.MAXD)%nat /\
  (* the text apart from the node WHEN THERE IS A TEXT: rd_pre's own guarded conjunct, verbatim (PRH_FnParse.v blob
     94232293d483) *)
  (0 < len -> text + len <= v \/ v + 56 <= text) /\
  (* the node is outside the granted real-stack window (rd_pre, PRH_FnParse.v blob 5bba1f6e0daa), verbatim *)
  (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) /\
  In [cf_pc_realloc_ra0] (as_universe B) /\ In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (as_universe B) /\
  Z.of_nat (PjRoundTrip.maxrun tb) < 2 ^ 30 /\
  cnt + 2 * Z.of_nat (length (rest_atR tb text p')) + 2 < 2 ^ 64 - 1 /\
  src_rd W mem text tb /\ prhReader_home B ly S Hp Lam text len /\
  (* the ledger: no heap move at all in this segment; g_most / g_own_ran_out (most, own) ride unchanged *)
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own /\
  rd_room S (prhPv_gtrace d (rest_atR tb text p)) /\
  (* THE LIVE COUNTS (a Theorem Labs lane's Option A). (a) tparse_value_specX's two ENTRY premises VERBATIM, at the entry state
     S0 (PRH_FnParse.v blob 94232293d483, the counts along the ALL-GRANTED events of the value): every arm derives its
     own callee's counts from them (the number arm's row-270 sec_cnt / ccnt24 bounds by PresetRun.pkR >= the start
     count; the container arm's parse_items counts, prhPv_gtrace at '[' / '{' being prhPi_gtrace's events) *)
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S0))
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S0))
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  (* (b) parse_string's two count premises AT THE STRING ARM'S CALL (tparse_string_specX, PRH_FnReader.v blob
     fb7b12dfa169 :524-527, with its p := p', the call cursor of row 142, and its S := the dispatch state, which rows
     135..141 leave as it is). GUARDED by the arm: at any other arm prhPs_evs (rest_atR tb text (p' + 1)) [] is a list
     the value never makes, and (a) does not bound it. Measured by this lane's reviewer: the text `1` then 6983 bytes
     `a` then the quote byte 34 takes the number arm, whose one request is the token's HMal 18 (class 2), while
     prhPs_evs of the rest is [HMal 7000] (class 24), so at a live class-24 count of exactly L24 + DRV (a) holds and the
     unguarded form fails *)
  (arm = VA_str ->
   Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
     (prhPs_evs (rest_atR tb text (p' + 1)) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV) /\
  (arm = VA_str ->
   Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
     (prhPs_evs (rest_atR tb text (p' + 1)) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV) /\
  (* one class-0 frame is taken, so what is left is exactly parse_items' own premise at this nesting *)
  Z.of_nat (length (frames S)) + Z.of_nat (PjGrammar.MAXD - d) <= fs_frames 0 /\
  (* the read-only view rides on, and the float state has not moved (nothing reaches strtod yet) *)
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  frm_zero (@YK11.fp_csr fx) /\
  (* THREE ENTRY FACTS OF THE KIT'S CUT 7cdbb61b5fa0 (PRH_FnParse.v blob f0d92dcec7e9), VERBATIM AT THE ENTRY STATE, APPENDED
     at the END so that a positional destruct moves only its last name (which then fails loudly, as the cut's own
     rd_pre append does): (1) the cursor set CW, tparse_value_specX's prh_cw_entry, which the string arm turns into
     parse_string's prh_cw_ok and the container arm into parse_items' prh_cw_entry at their call states
     (vrd_cur_entry_call); (2) the wild budget against CW, tparse_value_specX's room conjunct, which both arms hand on
     at their call state, whose depot is the entry's (the dispatch makes no allocator call but the frame take,
     `exists f, S = set_fs f S0` above); (3) rd_pre's appended ceiling `text + len < alloc_ceiling`, which the
     container arm's parse_items rd_pre asks for. *)
  prh_cw_entry B CW W0 mem0 regs0 q /\
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S0) /\
  text + len < YM05.alloc_ceiling.

(* ---- THE BOUNDARY: the state at the first row of the selected arm ----
   It is a post in the engine's form (world -> config -> Prop). The arm lemmas take it as a premise and conclude at
   the join VrdNum.vrd_epi_a with the arm's result VrdNum.vrd_pv_post: the string arm VrdArmStrOk.vrd_str_a_okP, the
   number arm VrdNumA.vrd_num_a_P, the container and literal arms VrdArmLC.vrd_cont_aLC_P_holds /
   vrd_lit_aLC_P_holds. Each reads its arm tag off the first non-white byte. Everything an arm lane needs is an
   explicit conjunct: the pc,
   the journal from parse_value's entry (at the WIDENED caller window (STK + e) (sp0 + e) the frozen post uses, with
   this call's own fake frame as the journal's `own`), the frame and which arm built it, the saved registers, the
   register map, the cursor and its advanced p, the untouched node, the text, the ledger (NO move: this segment
   allocates no heap block), the room, the frames headroom left for the subtree, the read-only view and the chain. *)
Definition vrd_disp_a
  (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)) (CTX0 : list (list Z)) (CW : list (list Z))
  (e q v text len p : Z) (d : nat) (tb : list Z)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : world segs -> config -> Prop :=
  fun W c =>
  exists (arm : vrd_arm) (pos p' k : Z) (ly : alayout) (S : astate) (Hp : list Z)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
  (* the arm's first row *)
  c = cfg_at segs (pa_sigma AS_parse_value + vrd_arm_off arm) regs mem md /\
  vrd_disp_body ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    arm pos p' k ly S Hp W regs mem md.

(* ---- THE CHAINS AT AN ARM'S CALL (a Theorem Labs lane's request; WalkCrsA's measurement). An arm's call of parse_items /
   parse_string / literal needs four chain facts AT THE CALL VIEW: vrd_call_W / vrd_call_WF premise 12 (the chain from
   the call's s0, which is parse_value's ENTRY sp: vrd_regs gives getr regs 8 = w64 (spZ regs0) and no arm row writes
   s0) - vrd_disp_chain; the callee's prh_cur_entry at the call state (its premise 4) - vrd_cur_entry_call; and the
   chains from the cursor's s0 (its premises 6 and 14) - vrd_cur_chain_call.
   VIEWS, everywhere below: (W0, mem0, regs0) is parse_value's ENTRY state; (W', m') is a CALL view: any later view
   that holds parse_value's two saved words at spZ regs0 - 8 / - 16 (vrd_saved) and agrees with the ENTRY view at and
   above spZ regs0 except at the cursor's p word [q, q + 8). (The dispatch writes nothing else at or above spZ regs0:
   vrd_disp_body's window clause outside rd_fp q v, the depth word [q + 16, q + 20) equal in both views by pj_in_okR,
   the node below alloc_ceiling; the arms write their node and their own frame only.) ---- *)

(* an aview word is a nonnegative number *)
Lemma vrd_rdword_nonneg : forall (H : word -> bool) (m : word -> option byte) a w,
  rdword (aview segs H m) a = Some w -> 0 <= w.
Proof.
intros H m a w Hw. unfold rdword in Hw.
assert (Hb : forall x y, aview segs H m x = Some y -> 0 <= y).
{ intros x y Hx. unfold aview in Hx. destruct (mbyte segs (mrestrict H m) x) as [z|]; [|discriminate].
  cbn [option_map] in Hx. injection Hx as <-. pose proof (bv_unsigned_in_range 8 z). lia. }
destruct (aview segs H m a) as [b0|] eqn:E0; [|discriminate].
destruct (aview segs H m (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview segs H m (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview segs H m (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview segs H m (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview segs H m (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview segs H m (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview segs H m (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
pose proof (Hb _ _ E0). pose proof (Hb _ _ E1). pose proof (Hb _ _ E2). pose proof (Hb _ _ E3).
pose proof (Hb _ _ E4). pose proof (Hb _ _ E5). pose proof (Hb _ _ E6). pose proof (Hb _ _ E7). lia.
Qed.

Lemma vrd_mod8_sub : forall x, x mod 8 = 0 -> (x - 8) mod 8 = 0 /\ (x - 16) mod 8 = 0.
Proof.
intros x Hx. split;
  [replace (x - 8) with (x + (-1) * 8) by lia | replace (x - 16) with (x + (-2) * 8) by lia];
  rewrite Z_mod_plus_full; exact Hx.
Qed.

(* a frame-pointer chain read through a second loader that agrees on every aligned word but the one at q: no frame keeps
   its saved ra at q (fp <> q + 8), and a frame whose saved-s0 slot is q (fp = q + 16, image B's parse_items shape) is
   cut there in both readings, because both words at q are below the frame. The spine and the frame pointers survive;
   that frame's nfp component becomes the second loader's word. *)
Lemma vrd_fpchain_keep : forall (ld ld' : Z -> option Z) (top q p0 pp : Z) (ch : list (Z * Z * Z)) (bp : Z),
  fpchain ld bp top ch -> Forall (fun r => fst (fst r) <> q + 8) ch -> bp mod 8 = 0 -> bp < top ->
  (forall a, bp - 16 <= a -> a + 8 <= top -> a mod 8 = 0 -> a <> q -> ld' a = ld a) ->
  q mod 8 = 0 -> ld q = Some p0 -> 4096 <= p0 -> p0 < q -> ld' q = Some pp -> pp < q ->
  exists ch2, fpchain ld' bp top ch2 /\ spine ch2 = spine ch /\
    map (fun r : Z * Z * Z => fst (fst r)) ch2 = map (fun r : Z * Z * Z => fst (fst r)) ch.
Proof.
intros ld ld' top q p0 pp ch. induction ch as [|[[fp ra] nfp] rest IH];
  intros bp Hf HX Hb8 Hbt Hag Hq8 Hp0 Hp4 Hpq Hpp Hppq.
- cbn [fpchain] in Hf. destruct Hf as (r & Hr & Hr4).
  destruct (Z.eq_dec (bp - 8) q) as [E|N].
  { exfalso. rewrite E, Hp0 in Hr. injection Hr as <-. lia. }
  exists []. split; [|split; reflexivity]. cbn [fpchain]. exists r. split; [|exact Hr4].
  rewrite Hag; [exact Hr | lia | lia | exact (proj1 (vrd_mod8_sub bp Hb8)) | exact N].
- cbn [fpchain] in Hf. destruct Hf as (-> & Hfp8 & Hra & Hnfp & Hra4 & Hrest).
  apply Forall_cons_iff in HX as [Hfq HXr]. cbn [fst] in Hfq.
  pose proof (vrd_mod8_sub bp Hb8) as (M8 & M16).
  assert (Hra' : ld' (bp - 8) = Some ra) by (rewrite Hag; [exact Hra | lia | lia | exact M8 | lia]).
  destruct (Z.eq_dec (bp - 16) q) as [E | N].
  + rewrite E, Hp0 in Hnfp. injection Hnfp as <-.
    assert (Hb1 : bad_next bp top p0 = true)
      by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
    rewrite Hb1 in Hrest. subst rest.
    exists [(bp, ra, pp)]. split; [|split; reflexivity].
    cbn [fpchain]. split; [reflexivity|]. split; [exact Hfp8|]. split; [exact Hra'|].
    split; [rewrite E; exact Hpp|]. split; [exact Hra4|].
    assert (Hb2 : bad_next bp top pp = true)
      by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
    rewrite Hb2. reflexivity.
  + assert (Hnfp' : ld' (bp - 16) = Some nfp) by (rewrite Hag; [exact Hnfp | lia | lia | exact M16 | exact N]).
    destruct (bad_next bp top nfp) eqn:Hb; rewrite ?Hb in Hrest; cbv iota in Hrest.
    * subst rest. exists [(bp, ra, nfp)]. split; [|split; reflexivity].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hfp8|]. split; [exact Hra'|]. split; [exact Hnfp'|].
      split; [exact Hra4|]. rewrite Hb. reflexivity.
    * pose proof Hb as Hb0. unfold bad_next in Hb.
      apply orb_false_iff in Hb as [Hb Hb3]. apply orb_false_iff in Hb as [Hb1 Hb2].
      apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply negb_false_iff, Z.eqb_eq in Hb3.
      destruct (IH nfp Hrest HXr Hb3 ltac:(lia)
                  ltac:(intros a Ha1 Ha2 Ha3 Ha4; apply Hag; [lia | exact Ha2 | exact Ha3 | exact Ha4])
                  Hq8 Hp0 Hp4 Hpq Hpp Hppq) as (ch3 & Hf3 & Hs3 & Hm3).
      exists ((bp, ra, nfp) :: ch3). split.
      -- cbn [fpchain]. split; [reflexivity|]. split; [exact Hfp8|]. split; [exact Hra'|]. split; [exact Hnfp'|].
         split; [exact Hra4|]. rewrite Hb0. exact Hf3.
      -- split.
         ++ change (spine ((bp, ra, nfp) :: ch3)) with (ra :: spine ch3). rewrite Hs3. reflexivity.
         ++ cbn [map fst]. rewrite Hm3. reflexivity.
Qed.

(* a frame-pointer chain at the CALL view that holds a record at fp = q + 8 gives an ENTRY-view chain that holds one
   too, cut right there by a layout whose top is q + 32. Every record before it has fp <= q, so it reads only words
   below q, where the two views agree; the record itself reads its nfp at q - 8 (agreed) and its saved ra at q, the
   entry's own word p0 >= 4096. With top q + 32 the earlier records still continue (each nfp is at most q + 8 <
   q + 16 = top - 16), and the record at q + 8 is cut (an aligned nfp above q + 8 is at least q + 16). *)
Lemma vrd_chain_cut : forall (ld ld' : Z -> option Z) (top q p0 : Z) (ch : list (Z * Z * Z)) (bp : Z),
  fpchain ld' bp top ch -> Exists (fun r => fst (fst r) = q + 8) ch ->
  (forall a, bp - 16 <= a -> a + 8 <= q -> ld' a = ld a) ->
  q mod 8 = 0 -> ld q = Some p0 -> 4096 <= p0 ->
  exists ch0, fpchain ld bp (q + 32) ch0 /\ Exists (fun r => fst (fst r) = q + 8) ch0.
Proof.
intros ld ld' top q p0 ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hch Hex Hag Hq8 Hp0 Hp4;
  [inversion Hex|].
cbn [fpchain] in Hch. destruct Hch as (-> & Hal & H8 & H16 & Hra & Hrest).
apply Exists_cons in Hex. destruct Hex as [Hhd | Htl].
- cbn [fst] in Hhd. subst bp.
  exists [(q + 8, p0, nfp)]. split; [|apply Exists_cons_hd; reflexivity].
  cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|].
  split; [replace (q + 8 - 8) with q by lia; exact Hp0|].
  split; [rewrite <- (Hag (q + 8 - 16)) by lia; exact H16|].
  split; [exact Hp4|].
  assert (Hb : bad_next (q + 8) (q + 32) nfp = true).
  { unfold bad_next. destruct (Z.leb_spec nfp (q + 8)); [reflexivity|].
    destruct (Z.leb_spec (q + 32 - 16) nfp); [reflexivity|].
    cbn [orb]. apply negb_true_iff, Z.eqb_neq. intros Hn.
    pose proof (Z.div_mod nfp 8 ltac:(lia)) as Dn. pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. lia. }
  rewrite Hb. reflexivity.
- destruct (bad_next bp top nfp) eqn:Hb; rewrite ?Hb in Hrest; cbv iota in Hrest; [subst rest; inversion Htl|].
  unfold bad_next in Hb.
  apply orb_false_iff in Hb as [Hb Hb3]. apply orb_false_iff in Hb as [Hb1 Hb2].
  apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply negb_false_iff, Z.eqb_eq in Hb3.
  assert (Hnq : nfp <= q + 8).
  { pose proof (fpchain_fps_increase _ _ _ _ Hrest) as Hinc. rewrite Forall_forall in Hinc.
    pose proof Htl as Htl'. apply Exists_exists in Htl' as (r & Hr & Er). pose proof (Hinc r Hr) as Hle.
    cbv beta in Hle. lia. }
  assert (Hbq : bp <= q).
  { pose proof (Z.div_mod nfp 8 ltac:(lia)) as Dn. pose proof (Z.div_mod bp 8 ltac:(lia)) as Db. lia. }
  destruct (IH nfp Hrest Htl ltac:(intros a Ha1 Ha2; apply Hag; lia) Hq8 Hp0 Hp4) as (ch1 & Hf1 & Hx1).
  exists ((bp, ra, nfp) :: ch1). split; [|apply Exists_cons_tl; exact Hx1].
  cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|].
  split; [rewrite <- (Hag (bp - 8)) by lia; exact H8|].
  split; [rewrite <- (Hag (bp - 16)) by lia; exact H16|].
  split; [exact Hra|].
  assert (Hb' : bad_next bp (q + 32) nfp = false).
  { unfold bad_next. apply orb_false_iff. split; [apply orb_false_iff; split; apply Z.leb_gt; lia|].
    apply negb_false_iff, Z.eqb_eq. exact Hb3. }
  rewrite Hb'. exact Hf1.
Qed.

(* SHAPE 1, vrd_call_W / vrd_call_WF premise 12: the chain from parse_value's entry sp at the CALL view. Its first
   record is parse_value's own (saved ra, saved s0); the rest is the ENTRY chain from s0Z regs0 (the text's plain
   premise, blob e21b8b02d69e) read off the call view by vrd_fpchain_keep.
   prh_cur_entry's first conjunct (PRH_Base.v blob ee6c7a38d6b6, record texts a working branch 51daa1e80a99: no
   entry chain from s0, in any layout, keeps a record at fp = q + 8) is what makes it hold: the text permits a caller
   chain record at fp = q + 8, whose SAVED-RA slot is the cursor's p word; the white-space loop stores p' there
   (row 95), so without it no call-view chain has spine raZ regs0 :: spine ch (bad_next cannot help: it is the ra, not
   the nfp). *)
Lemma vrd_disp_chain : forall (ly0 lyc : alayout) (W0 W' : world segs) (mem0 m' : word -> option byte)
    (regs0 : bvmap 5 word) (ch : list (Z * Z * Z)) (q v spc p0 pp : Z),
  (exists ch', achain ly0 (aview segs (w_H W0) mem0) (spZ regs0) (s0Z regs0) ch' /\ spine ch' = spine ch) ->
  prh_cur_entry W0 mem0 regs0 q ->
  rdword (aview segs (w_H W0) mem0) q = Some p0 -> 4096 <= p0 -> p0 < alloc_ceiling ->
  rdword (aview segs (w_H W') m') q = Some pp -> pp < alloc_ceiling ->
  alloc_ceiling <= q -> q mod 8 = 0 ->
  ly_top lyc = ly_top ly0 -> ly_top ly0 <= 2 ^ 64 ->
  alloc_ceiling <= spZ regs0 -> spc + 16 <= spZ regs0 -> spZ regs0 < ly_top ly0 - 16 -> spZ regs0 mod 8 = 0 ->
  4096 <= raZ regs0 ->
  rdword (aview segs (w_H W') m') (spZ regs0 - 8) = Some (raZ regs0) ->
  rdword (aview segs (w_H W') m') (spZ regs0 - 16) = Some (s0Z regs0) ->
  (* the CALL view against the ENTRY view: equal at and above the entry sp off the reader's cells rd_fp q v (what
     vrd_disp_body's window clause gives, a Theorem Labs lane's 09:3xZ decision), the node below the entry sp, and the depth
     bytes [q + 16, q + 20) equal (no arm row writes the cursor before its call: rows 131-134, 152-156, 213-216,
     218-223; pj_in_okR names the same depth at the entry and at the dispatch) *)
  (forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W') m' a = aview segs (w_H W0) mem0 a) ->
  v + 56 <= spZ regs0 ->
  (forall a, q + 16 <= a < q + 20 -> aview segs (w_H W') m' a = aview segs (w_H W0) mem0 a) ->
  exists ch1, achain lyc (aview segs (w_H W') m') spc (spZ regs0) ch1 /\ spine ch1 = raZ regs0 :: spine ch.
Proof.
intros ly0 lyc W0 W' mem0 m' regs0 ch q v spc p0 pp HCH HCE Hp0 Hp4 Hpc Hpp Hppc Hqc Hq8 Hly Htop
  Hceil Hspc Hst Hal Hra4 Hr8 Hr16 HM' Hv HD.
pose proof (proj1 HCE) as HC0.
(* at and above the entry sp, only the cursor's p word may differ *)
assert (HM : forall a, spZ regs0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
  aview segs (w_H W') m' a = aview segs (w_H W0) mem0 a).
{ intros a Ha Hq. destruct (Z_lt_le_dec a (q + 16)) as [H1|H1]; [|destruct (Z_lt_le_dec a (q + 20)) as [H2|H2]];
  [| apply HD; lia |];
  (apply HM'; [exact Ha|]; intros (r & Hin & Hr); cbn [rd_fp In] in Hin;
   destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia). }
destruct HCH as (ch' & Hch & Hsp).
(* no entry frame keeps its saved ra at q: prh_cur_entry's first conjunct, at the entry layout *)
pose proof (HC0 ly0 ch' Hch) as HXc.
pose proof (Z.div_mod q 8 ltac:(lia)) as DQ. rewrite Hq8, Z.add_0_r in DQ.
destruct (bad_next (spZ regs0) (ly_top ly0) (s0Z regs0)) eqn:Hbad.
- exists [(spZ regs0, raZ regs0, s0Z regs0)].
  assert (Hc0 : ch' = []).
  { destruct Hch as [(_ & Hc) | (H1 & H2 & H3 & _)]; [exact Hc|].
    unfold bad_next in Hbad.
    apply orb_true_iff in Hbad as [Hbad | Hbad]; [apply orb_true_iff in Hbad as [Hbad | Hbad]|].
    + apply Z.leb_le in Hbad. lia.
    + apply Z.leb_le in Hbad. lia.
    + apply negb_true_iff, Z.eqb_neq in Hbad. exfalso. exact (Hbad H3). }
  subst ch'. split.
  + unfold achain. right. rewrite Hly. split; [lia|]. split; [lia|]. split; [exact Hal|]. split.
    * cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hr8|]. split; [exact Hr16|].
      split; [exact Hra4|]. rewrite Hbad. reflexivity.
    * constructor; [cbn [fst]; lia | constructor].
  + rewrite <- Hsp. reflexivity.
- pose proof Hbad as Hbad0.
  unfold bad_next in Hbad. apply orb_false_iff in Hbad as [Hbad Hb3]. apply orb_false_iff in Hbad as [Hb1 Hb2].
  apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply negb_false_iff, Z.eqb_eq in Hb3.
  destruct Hch as [([Hc | [Hc | Hc]] & _) | (H1 & H2 & H3 & H4 & H5)];
    [lia | lia | exfalso; exact (Hc Hb3) |].
  assert (Hag : forall a, s0Z regs0 - 16 <= a -> a + 8 <= ly_top ly0 -> a mod 8 = 0 -> a <> q ->
    rdword (aview segs (w_H W') m') a = rdword (aview segs (w_H W0) mem0) a).
  { intros a Ha1 Ha2 Ha3 Ha4.
    pose proof (Z.div_mod a 8 ltac:(lia)) as DA. rewrite Ha3, Z.add_0_r in DA.
    apply rdword_ext. intros k Hk. apply HM; [lia|]. lia. }
  destruct (vrd_fpchain_keep _ _ (ly_top ly0) q p0 pp ch' (s0Z regs0) H4 HXc H3 ltac:(lia) Hag Hq8
              Hp0 Hp4 ltac:(lia) Hpp ltac:(lia)) as (ch2 & Hf2 & Hs2 & Hm2).
  exists ((spZ regs0, raZ regs0, s0Z regs0) :: ch2). split.
  + unfold achain. right. rewrite Hly. split; [lia|]. split; [lia|]. split; [exact Hal|]. split.
    * cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hr8|]. split; [exact Hr16|].
      split; [exact Hra4|]. rewrite Hbad0. exact Hf2.
    * constructor; [cbn [fst]; lia|].
      apply (proj1 (Forall_map (fun r : Z * Z * Z => fst (fst r)) (fun z => spc + 16 <= z) ch2)).
      rewrite Hm2. apply (proj2 (Forall_map (fun r : Z * Z * Z => fst (fst r)) (fun z => spc + 16 <= z) ch')).
      eapply Forall_impl; [|exact H5]. intros r Hr. cbn beta in Hr |- *. lia.
  + change (spine ((spZ regs0, raZ regs0, s0Z regs0) :: ch2)) with (raZ regs0 :: spine ch2).
    rewrite Hs2, Hsp. reflexivity.
Qed.

(* SHAPE 2, the callee's premise 4: the cursor premises at the CALL state (regsc, the call's registers, whose sp is
   below parse_value's frame), from the same premises at parse_value's ENTRY state: prh_cur_entry, and the cursor set
   CW's prh_cw_entry (the kit's cut 7cdbb61b5fa0, PRH_Base.v blob ef7c8ca98529: prh_cur_entry's sp - 8 arm is DELETED and
   prh_cw_entry states, for the same word, that the free's trace is in CW or the word is the code word). On image A
   both cursor functions keep s0 = q (pi_s0cur = Some 0, PRH_Img.v), so the two named words are at q - 8 and q - 16:
   window words outside the p word, or parse_value's own saved ra / s0 when q is spZ regs0 or spZ regs0 + 8, which
   the entry state names by prh_word_entry's two special cases.
   The FIRST conjunct of prh_cur_entry (no chain from the call's s0 keeps a record at fp = q + 8) is
   PROVED here, with no premise about the call state's chain. At an arm's call s0Z regsc is parse_value's entry sp
   (vrd_regs: getr regs 8 = w64 (spZ regs0); no arm row writes s0), so a call-view chain is parse_value's own record
   at spZ regs0 <= q, then a chain from s0Z regs0. If s0Z regs0 = spZ regs0 + 8, its one record reads its nfp at
   spZ regs0 - 8, the saved ra, below the ceiling (fpre, PRH_Base.v blob ee6c7a38d6b6), so it is cut; it is at q + 8
   only when q = spZ regs0, where the entry state puts the saved s0 (the word at q - 16) below the ceiling, against
   s0Z regs0 = spZ regs0 + 8. Otherwise s0Z regs0 >= spZ regs0 + 16, and a record at q + 8 would give one in an ENTRY
   chain (vrd_chain_cut: the views agree below q, and the entry's word at q is p0 >= 4096), which the entry state's
   first conjunct forbids. *)
Lemma vrd_cur_entry_call : forall (CW : list (list Z)) (W0 W' : world segs) (mem0 m' : word -> option byte)
    (regs0 regsc : bvmap 5 word) (q v p0 : Z),
  pi_s0cur F_parse_string = Some 0 -> pi_s0cur F_parse_items = Some 0 ->
  prh_cur_entry W0 mem0 regs0 q -> prh_cw_entry B CW W0 mem0 regs0 q ->
  s0Z regsc = spZ regs0 -> alloc_ceiling <= spZ regs0 -> raZ regs0 < alloc_ceiling ->
  rdword (aview segs (w_H W0) mem0) q = Some p0 -> 4096 <= p0 ->
  spZ regs0 <= q -> q + 8 <= 2 ^ 64 -> q mod 8 = 0 -> spZ regs0 mod 8 = 0 -> spZ regsc + 16 <= spZ regs0 ->
  rdword (aview segs (w_H W') m') (spZ regs0 - 8) = Some (raZ regs0) ->
  rdword (aview segs (w_H W') m') (spZ regs0 - 16) = Some (s0Z regs0) ->
  (forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W') m' a = aview segs (w_H W0) mem0 a) ->
  v + 56 <= spZ regs0 ->
  prh_cur_entry W' m' regsc q /\ prh_cw_entry B CW W' m' regsc q.
Proof.
intros CW W0 W' mem0 m' regs0 regsc q v p0 Hps Hpi HCE HCW Hs0c Hceil HraC Hp0 Hp4 Hq Hq64 Hq8 Hs8 Hsc Hr8 Hr16
  HM Hv.
pose proof (Z.div_mod q 8 ltac:(lia)) as DQ. rewrite Hq8, Z.add_0_r in DQ.
pose proof (Z.div_mod (spZ regs0) 8 ltac:(lia)) as DS. rewrite Hs8, Z.add_0_r in DS.
assert (Hwin : forall a, spZ regs0 <= a -> a + 8 <= q ->
  rdword (aview segs (w_H W') m') a = rdword (aview segs (w_H W0) mem0) a).
{ intros a Ha1 Ha2. apply rdword_ext. intros k Hk. apply HM; [lia|].
  intros (r & Hin & Hr). cbn [rd_fp In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia. }
(* the word at q - 8, read at the call state, is the one the entry state names there *)
assert (Hw8 : forall w, prh_word_entry W' m' regsc (q - 8) w -> prh_word_entry W0 mem0 regs0 (q - 8) w).
{ intros w Hw. unfold prh_word_entry in Hw |- *.
  rewrite (proj2 (Z.eqb_neq (q - 8) (spZ regsc - 8))) in Hw by lia.
  rewrite (proj2 (Z.eqb_neq (q - 8) (spZ regsc - 16))) in Hw by lia.
  destruct (Z.eq_dec q (spZ regs0)) as [Eq | Nq].
  + rewrite (proj2 (Z.eqb_eq (q - 8) (spZ regs0 - 8))) by lia.
    rewrite Eq, Hr8 in Hw. injection Hw as <-. reflexivity.
  + rewrite (proj2 (Z.eqb_neq (q - 8) (spZ regs0 - 8))) by lia.
    rewrite (proj2 (Z.eqb_neq (q - 8) (spZ regs0 - 16))) by lia.
    rewrite <- (Hwin (q - 8)) by lia. exact Hw. }
assert (Hs0F : forall F, prh_cursor F -> prh_s0 F q = q)
  by (intros F HF; unfold prh_s0; destruct HF as [-> | ->]; [rewrite Hps | rewrite Hpi]; lia).
split; [split|].
{ intros ly chc Hac. rewrite Hs0c in Hac. rewrite Forall_forall. intros r Hr Er.
  assert (Hex : Exists (fun r0 : Z * Z * Z => fst (fst r0) = q + 8) chc)
    by (apply Exists_exists; exists r; split; [exact Hr | exact Er]).
  clear r Hr Er.
  destruct Hac as [(_ & ->) | (A1 & A2 & A3 & A4 & A5)]; [inversion Hex|].
  destruct chc as [|[[fp0 ra0] nfp0] tl]; [inversion Hex|].
  cbn [fpchain] in A4. destruct A4 as (-> & _ & _ & H16c & _ & Hrest).
  rewrite Hr16 in H16c. injection H16c as E0. subst nfp0.
  apply Exists_cons in Hex. destruct Hex as [Hhd | Htl]; [cbn [fst] in Hhd; lia|].
  destruct (bad_next (spZ regs0) (ly_top ly) (s0Z regs0)) eqn:Hb; rewrite ?Hb in Hrest; cbv iota in Hrest;
    [subst tl; inversion Htl|].
  unfold bad_next in Hb. apply orb_false_iff in Hb as [Hb Hb3]. apply orb_false_iff in Hb as [Hb1 Hb2].
  apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply negb_false_iff, Z.eqb_eq in Hb3.
  pose proof (Z.div_mod (s0Z regs0) 8 ltac:(lia)) as D0. rewrite Hb3, Z.add_0_r in D0.
  destruct (Z.eq_dec (s0Z regs0) (spZ regs0 + 8)) as [E8 | N8].
  - (* the record at spZ regs0 + 8 reads its nfp at spZ regs0 - 8 (the saved ra, below the ceiling): cut there *)
    destruct tl as [|[[fp1 ra1] nfp1] tl2]; [inversion Htl|].
    cbn [fpchain] in Hrest. destruct Hrest as (-> & _ & _ & H16d & _ & Hrest2).
    replace (s0Z regs0 - 16) with (spZ regs0 - 8) in H16d by lia.
    rewrite Hr8 in H16d. injection H16d as E1. subst nfp1.
    assert (Hb1' : bad_next (s0Z regs0) (ly_top ly) (raZ regs0) = true)
      by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
    rewrite Hb1' in Hrest2. cbv iota in Hrest2. subst tl2.
    apply Exists_cons in Htl. destruct Htl as [Hhd1 | Htl1]; [|inversion Htl1].
    cbn [fst] in Hhd1.
    (* so q = spZ regs0, and the entry's word at q - 16 is the saved s0, which the entry state puts below the ceiling *)
    pose proof (proj2 HCE F_parse_string (or_introl eq_refl)) as Hc16.
    assert (Hs0q : prh_s0 F_parse_string q = q) by (unfold prh_s0; rewrite Hps; lia).
    rewrite Hs0q in Hc16.
    assert (Hw16 : prh_word_entry W0 mem0 regs0 (q - 16) (s0Z regs0)).
    { unfold prh_word_entry.
      rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regs0 - 8))) by lia.
      rewrite (proj2 (Z.eqb_eq (q - 16) (spZ regs0 - 16))) by lia. reflexivity. }
    pose proof (Hc16 _ Hw16). lia.
  - (* s0Z regs0 >= spZ regs0 + 16: the ENTRY chain from s0, cut by a layout of top q + 32, would hold a record at
       q + 8, which prh_cur_entry's first conjunct at the entry state forbids *)
    assert (H16s : spZ regs0 + 16 <= s0Z regs0) by lia.
    destruct (vrd_chain_cut (rdword (aview segs (w_H W0) mem0)) (rdword (aview segs (w_H W') m'))
                (ly_top ly) q p0 tl (s0Z regs0) Hrest Htl
                ltac:(intros a Ha1 Ha2; apply Hwin; lia) Hq8 Hp0 Hp4) as (ch0 & Hf0 & Hx0).
    pose proof (fpchain_fps_increase _ _ _ _ Hf0) as Hinc.
    assert (Hs0q8 : s0Z regs0 <= q + 8).
    { rewrite Forall_forall in Hinc. pose proof Hx0 as Hx0'. apply Exists_exists in Hx0' as (r & Hr & Er).
      pose proof (Hinc r Hr) as Hle. cbv beta in Hle. lia. }
    assert (Hach : achain (ALayout 0 0 0 0 0 0 0 0 (q + 32) 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0))
                     (aview segs (w_H W0) mem0) (spZ regs0) (s0Z regs0) ch0).
    { unfold achain. right. cbn [ly_top]. split; [lia|]. split; [lia|]. split; [exact Hb3|]. split; [exact Hf0|].
      eapply Forall_impl; [|exact Hinc]. intros r Hr. cbv beta in Hr |- *. lia. }
    pose proof (proj1 HCE _ _ Hach) as HF0. rewrite Forall_forall in HF0.
    apply Exists_exists in Hx0 as (r & Hr & Er). exact (HF0 r Hr Er). }
{ intros F HF. pose proof (proj2 HCE F HF) as Hc16. rewrite (Hs0F F HF) in Hc16 |- *.
  intros w Hw. apply Hc16. unfold prh_word_entry in Hw |- *.
  rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regsc - 8))) in Hw by lia.
  rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regsc - 16))) in Hw by lia.
  destruct (Z.eq_dec q (spZ regs0 + 8)) as [Eq8 | N8]; [|destruct (Z.eq_dec q (spZ regs0)) as [Eq0 | N0]].
  + rewrite (proj2 (Z.eqb_eq (q - 16) (spZ regs0 - 8))) by lia.
    replace (q - 16) with (spZ regs0 - 8) in Hw by lia. rewrite Hr8 in Hw. injection Hw as <-. reflexivity.
  + rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regs0 - 8))) by lia.
    rewrite (proj2 (Z.eqb_eq (q - 16) (spZ regs0 - 16))) by lia.
    replace (q - 16) with (spZ regs0 - 16) in Hw by lia. rewrite Hr16 in Hw. injection Hw as <-. reflexivity.
  + rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regs0 - 8))) by lia.
    rewrite (proj2 (Z.eqb_neq (q - 16) (spZ regs0 - 16))) by lia.
    rewrite <- (Hwin (q - 16)) by lia. exact Hw. }
(* the cursor set: the entry state's prh_cw_entry at the same word *)
{ intros F r w HF Hr Hw. apply (HCW F r w HF Hr). rewrite (Hs0F F HF) in Hw |- *. exact (Hw8 w Hw). }
Qed.

(* SHAPES 3 and 4, the callee's premises 6 and 14: a chain from the cursor's s0 = q (image A, prh_s0 F q = q) at the
   CALL view, for any sp at least 16 below q (premise 14's sp is the call's sp - pi_frame F_parse_items; premise 6's is
   the call's sp). The word at q - 16 is below alloc_ceiling (vrd_cur_entry_call's prh_cur_entry at the call state),
   so the chain is one record, cut at once - or empty, if the word at q - 8 is below 4096. *)
Lemma vrd_cur_chain_call : forall (lyc : alayout) (H : word -> bool) (m : word -> option byte) (spx q w16 : Z),
  alloc_ceiling <= q -> q < ly_top lyc - 16 -> q mod 8 = 0 -> spx + 16 <= q ->
  rdword (aview segs H m) (q - 16) = Some w16 -> w16 < alloc_ceiling ->
  (exists w8, rdword (aview segs H m) (q - 8) = Some w8) ->
  exists ch, achain lyc (aview segs H m) spx q ch.
Proof.
intros lyc H m spx q w16 Hc Ht Hal Hsp H16 Hw16 (w8 & H8).
pose proof (vrd_rdword_nonneg H m (q - 8) w8 H8) as Hw8.
destruct (Z_lt_le_dec w8 4096) as [Hlt | Hge].
- exists []. unfold achain. right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [|constructor].
  cbn [fpchain]. exists w8. split; [exact H8 | lia].
- exists [(q, w8, w16)]. unfold achain. right. split; [lia|]. split; [lia|]. split; [exact Hal|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact H8|]. split; [exact H16|].
    split; [exact Hge|].
    assert (Hb : bad_next q (ly_top lyc) w16 = true)
      by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
    rewrite Hb. reflexivity.
  + constructor; [cbn [fst]; lia | constructor].
Qed.

(* ---- THE NODE IS APART FROM parse_value's OWN FAKE FRAME (a Theorem Labs lane's request for WalkCrsA's flag word at the join,
   row 225). STATE: any one state (W, mem) that holds the frame (vrd_frame) and the node's shadow
   (prhPv_node's range_addressable) - in vrd_disp_body, THE DISPATCH STATE. An overlap puts a node byte inside the
   frame, whose shadow byte is 0xf1, 0xf8 or 0xf3 (vrd_frame_shadow), not addressable. The 64 is fs_frame_bytes 0. *)
Lemma vrd_node_frame_disj : forall (W : world segs) (mem : word -> option byte) (ly : alayout) (pos v : Z),
  vrd_frame W mem ly pos -> frame_addr ly 0 pos mod 8 = 0 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 56 ->
  v + 56 <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= v.
Proof.
intros W mem ly pos v Fr HF8 Hra.
destruct (Z.le_gt_cases (v + 56) (frame_addr ly 0 pos)) as [H|H]; [left; exact H|].
destruct (Z.le_gt_cases (frame_addr ly 0 pos + 64) v) as [H'|H']; [right; exact H'|].
exfalso.
remember (Z.max v (frame_addr ly 0 pos)) as x eqn:Hx.
destruct (Hra x ltac:(lia)) as (s & Hs & Hok). unfold shadow_of_addr in Hs.
pose proof (Z.div_mod (frame_addr ly 0 pos) 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
assert (Hx8 : x / 8 = frame_addr ly 0 pos / 8 + (x - frame_addr ly 0 pos) / 8).
{ replace x with ((x - frame_addr ly 0 pos) + frame_addr ly 0 pos / 8 * 8) at 1 by lia.
  rewrite Z.div_add by lia. lia. }
assert (Hi0 : 0 <= (x - frame_addr ly 0 pos) / 8) by (apply Z.div_pos; lia).
assert (Hi8 : (x - frame_addr ly 0 pos) / 8 < 8) by (apply Z.div_lt_upper_bound; lia).
destruct Fr as (_ & _ & _ & Fs).
pose proof (Fs ((x - frame_addr ly 0 pos) / 8) (conj Hi0 Hi8)) as Hs2.
replace (SHADOW_OFF + frame_addr ly 0 pos / 8 + (x - frame_addr ly 0 pos) / 8) with (SHADOW_OFF + x / 8) in Hs2
  by lia.
rewrite Hs2 in Hs. injection Hs as Es.
assert (Hc : forall j, 0 <= j < 8 -> 8 <= nth (Z.to_nat j) vrd_frame_shadow 0).
{ intros j Hj.
  assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) as Hj8 by lia.
  destruct Hj8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; unfold vrd_frame_shadow; simpl; lia. }
pose proof (Hc _ (conj Hi0 Hi8)) as Hc8. assert (Hs8 : 8 <= s) by (rewrite <- Es; exact Hc8). clear - Hs8 Hok.
unfold saddr_ok in Hok. destruct Hok as [Hok | (_ & Hok)]; lia.
Qed.

End c.

(* the unread rest only shrinks as the cursor advances, so rd_pre's count bound at p gives the same bound at the
   advanced cursor p' of the dispatch (parse_items' own rd_pre asks for it there) *)
Lemma vrd_rest_shrink : forall tb text p p', p <= p' ->
  (length (rest_atR tb text p') <= length (rest_atR tb text p))%nat.
Proof.
  intros tb text p p' Hp. unfold rest_atR. rewrite !length_skipn. lia.
Qed.

(* rd_pre's and tparse_value_specX's frames bound is on `length (frames S)`, while
   FCm0s.stack_malloc0_contract_x asks for `count_cid 0 (frames S)` (the kit's own texts, PRH_FnTx.v:213 and
   PRH_FnEx.v:243, use the count form): the length form is the stronger of the two. *)
Lemma vrd_count_le_length : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof.
  intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
  destruct (c =? cid); lia.
Qed.

(* ---- the two pure facts the dispatch walk turns on. They are restatements, in this tree's vocabulary, of
   pre338r2 45cffb16b86's parse_value_disp.mask_ws and lts_109 (READING AID ONLY: that branch is in the old
   vocabulary and over the original images, nothing of it is merged, bridged or cited as evidence here). ---- *)

(* the white-space mask the loop builds in a4: rows 87..89 are `lui a0, 0x800; addiw a0, a0, 0x13; slli a4, a0, 9`,
   so a4 = 0x800013 << 9 = 4294977024, whose set bits are 9, 10, 13 and 32 *)
Definition vrd_ws_mask : Z := 4294977024.

(* row 96 exits the loop when 32 < b, and rows 97..99 keep the byte exactly when bit b of the mask is set: the two
   together are PjGrammar.ws, which is what ties this segment's loop to the grammar's own skip *)
Lemma vrd_mask_ws : forall b, 0 <= b <= 32 ->
  Z.land (Z.shiftr vrd_ws_mask (b mod 64)) 1 = (if PjGrammar.ws b then 1 else 0).
Proof.
  intros b Hb.
  assert (Hall : forallb (fun x => Z.eqb (Z.land (Z.shiftr vrd_ws_mask (x mod 64)) 1)
                                         (if PjGrammar.ws x then 1 else 0))
                         (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall.
  apply Z.eqb_eq, Hall, in_map_iff. exists (Z.to_nat b).
  split; [lia | apply in_seq; lia].
Qed.

(* and no white-space byte is above the loop's 32, so row 96's exit is sound in the other direction *)
Lemma vrd_ws_le_32 : forall b, PjGrammar.ws b = true -> 0 <= b <= 32.
Proof.
  intros b H. unfold PjGrammar.ws in H.
  repeat (apply Bool.orb_true_iff in H as [H|H]); apply Z.eqb_eq in H; lia.
Qed.

(* the dispatch tree of rows 110..130 is TWO levels: row 112 pivots on 0x6d (109), rows 113..118 test
   0x22 / 0x5b / 0x66 below it and rows 125..130 test 0x6e / 0x74 / 0x7b above it, every other byte falling to the
   number arm. vrd_arm_of is exactly that tree, which is what lets an arm lane read its tag off the byte alone. *)
Lemma vrd_arm_of_pivot : forall b,
  vrd_arm_of b =
  (if 109 <? b
   then (if b =? 110 then VA_null else if b =? 116 then VA_true else if b =? 123 then VA_obj else VA_num)
   else (if b =? 34 then VA_str else if b =? 91 then VA_arr else if b =? 102 then VA_false else VA_num)).
Proof.
  intros b. unfold vrd_arm_of. destruct (Z.ltb_spec 109 b) as [Hlt|Hge].
  - rewrite (proj2 (Z.eqb_neq b 34)) by lia.
    rewrite (proj2 (Z.eqb_neq b 91)) by lia.
    rewrite (proj2 (Z.eqb_neq b 102)) by lia. reflexivity.
  - rewrite (proj2 (Z.eqb_neq b 110)) by lia.
    rewrite (proj2 (Z.eqb_neq b 116)) by lia.
    rewrite (proj2 (Z.eqb_neq b 123)) by lia. reflexivity.
Qed.

(* a white-space byte never selects an arm: the loop consumes it, so every arm tag comes from a byte the grammar's
   skip has already stopped at *)
Lemma vrd_ws_not_arm : forall b, PjGrammar.ws b = true -> vrd_arm_of b = VA_num.
Proof.
  intros b H. pose proof (vrd_ws_le_32 b H) as Hb. unfold vrd_arm_of.
  rewrite (proj2 (Z.eqb_neq b 34)) by lia. rewrite (proj2 (Z.eqb_neq b 91)) by lia.
  rewrite (proj2 (Z.eqb_neq b 102)) by lia. rewrite (proj2 (Z.eqb_neq b 110)) by lia.
  rewrite (proj2 (Z.eqb_neq b 116)) by lia. rewrite (proj2 (Z.eqb_neq b 123)) by lia. reflexivity.
Qed.

(* the string arm is chosen by the quote alone *)
Lemma vrd_arm_of_str : forall b, vrd_arm_of b = VA_str -> b = 34.
Proof.
  intros b. unfold vrd_arm_of.
  destruct (b =? 34) eqn:E1; [intros _; apply Z.eqb_eq; exact E1|].
  destruct (b =? 91), (b =? 102), (b =? 110), (b =? 116), (b =? 123); intros Hc; discriminate Hc.
Qed.

(* the unread rest at a cursor inside the text is the byte there, then the rest after it *)
Lemma vrd_skipn_nth : forall (l : list Z) n, (n < length l)%nat -> skipn n l = nth n l 0 :: skipn (S n) l.
Proof.
induction l as [|x t IH]; intros n Hn; [cbn in Hn; lia|].
destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hn. lia.
Qed.
Lemma vrd_rest_cons : forall tb text p, text <= p -> p - text < Z.of_nat (length tb) ->
  rest_atR tb text p = nth (Z.to_nat (p - text)) tb 0 :: rest_atR tb text (p + 1).
Proof.
intros tb text p H1 H2. unfold rest_atR.
replace (Z.to_nat (p + 1 - text)) with (S (Z.to_nat (p - text))) by lia.
apply vrd_skipn_nth. lia.
Qed.
Lemma vrd_rest_end : forall tb text len, Z.of_nat (length tb) = len -> rest_atR tb text (text + len) = [].
Proof. intros tb text len H. unfold rest_atR. replace (Z.to_nat (text + len - text)) with (length tb) by lia. apply skipn_all. Qed.
Lemma vrd_skip_stop : forall b r, PjGrammar.ws b = false -> PjGrammar.skip (b :: r) = b :: r.
Proof. intros b r H. cbn. rewrite H. reflexivity. Qed.
Lemma vrd_skip_go : forall b r, PjGrammar.ws b = true -> PjGrammar.skip (b :: r) = PjGrammar.skip r.
Proof. intros b r H. cbn. rewrite H. reflexivity. Qed.
(* a byte above 32 is no white space *)
Lemma vrd_gt32_not_ws : forall b, 32 < b -> PjGrammar.ws b = false.
Proof. intros b H. destruct (PjGrammar.ws b) eqn:E; [|reflexivity]. pose proof (vrd_ws_le_32 b E). lia. Qed.

(* ================================================================================================================
   THE WALK of the entry segment. Every state is rebuilt from the CURRENT registers (E = Eimg (Ereg regs extras),
   ss with sr_atoms), so every symbolic value is an atom of a register and no term grows across a run.
   ================================================================================================================ *)

Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
(* the image binding of B (the kit's PALib: the GOT words, the shadow cell, the use-after-return GOT word) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.
(* IMAGE FACT, the one PALib does not carry: where the use-after-return CELL is. PALib fixes the GOT word
   (pal_got_uar: as_got_uar B = VAL (A_OBJ 1)) but not the cell that word points at, and the walk needs it to put a
   region on that cell and to keep it apart from the three GOT / shadow-cell words. The owner of PALib discharges it
   by adding a field; in image A the cell is __asan_option_detect_stack_use_after_return. *)
Hypothesis UARC : 4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kLowMemEnd /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= as_uar_cell B).

(* parse_value's entry, as a byte offset from the listing's base *)
Definition vrd_PC : Z := A_prog_sigma AS_parse_value - A_prog_base.
(* the shadow base of every instrumented check of this function: the atom that holds SHADOW_OFF *)
Definition vrd_Bx : sv := SOff 32 0.
Definition vrd_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* the entry state: the 192 bytes below the entry sp (the 176 of the frame and the 16 of alignment slack), the GOT
   word and the shadow cell (s7 is read through them), and the use-after-return GOT word and its cell *)
Definition vrd_e_regions : smem :=
  [ stack_region 192; got_regionP; bcell_regionP 32;
    YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))] ].
Definition vrd_e_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] A_alias_hints.
Definition ss_vrd_e : sstate := mkSS vrd_PC sr_atoms vrd_e_regions None vrd_e_facts.
Definition vrd_e_env (regs : bvmap 5 word) : env :=
  @Eimg _ A_prog_listing PI_prog_A (Ereg regs [w64 SHADOW_OFF; w64 (as_uar_cell B)]).

(* a 4-byte constant cell of the runtime, as the engine's memory wants it *)
Lemma vrd_val_mem_of_rd32 : forall (H : word -> bool) mem a v,
  rd32 (aview SEGS H mem) a v -> val_mem SEGS (mrestrict H mem) a 4 v.
Proof.
  intros H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb. unfold aview in Hb.
  destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; cbn [option_map] in Hb; [|discriminate].
  injection Hb as Hb. pose proof (bv_unsigned_in_range 8 b) as Hr8.
  unfold bv_modulus in Hr8. cbn in Hr8. rewrite Hb in Hr8.
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  cbn [Z.of_N]. rewrite Hb. symmetry. apply Z.mod_small. cbn. lia.
Qed.

Lemma vrd_entry : forall STK ly S Hp W regs mem md ch,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 192 <= STK ->
  st_ok_pi SEGS VAL (vrd_e_env regs) ss_vrd_e
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_PC)) mem (seg_rom SEGS))).
Proof.
intros STK ly S Hp W regs mem md ch HPRE H192.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof UARC as (U1 & U2 & U3 & U4 & U5).
destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kgotu).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
rewrite (pal_got_uar B PAL) in Kgotu.
pose proof (@pa_obj_img _ A_prog_listing PI_prog_A 0%nat ltac:(lia)) as Hg0.
pose proof (@pa_obj_img _ A_prog_listing PI_prog_A 1%nat ltac:(lia)) as Hg1.
pose proof (@pa_obj_img _ A_prog_listing PI_prog_A 12%nat ltac:(lia)) as Hg12.
change (@pa_lo _ A_prog_listing PI_prog_A) with IMG_LO in Hg0, Hg1, Hg12.
change (@pa_hi _ A_prog_listing PI_prog_A) with IMG_TOP in Hg0, Hg1, Hg12.
unfold IMG_LO, IMG_TOP in Hg0, Hg1, Hg12.
pose proof (pal_got_cell B PAL) as Hgc. pose proof (pal_got_uar_disj B PAL) as (Hgu0 & Hgu12).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := vrd_e_env regs) in *.
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew E 32 = w64 SHADOW_OFF)
  by (subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (as_uar_cell B))
  by (subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold vrd_e_env; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; unfold vrd_e_env; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold vrd_e_env; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v)
  by (intros n v Hn Hv; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv).
unfold ss_vrd_e, vrd_PC. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold vrd_e_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (@pa_val_range _ A_prog_listing PI_prog_A (A_OBJ 0)); lia).
    unfold IMG_LO, IMG_TOP in Hg0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (@pa_val_range _ A_prog_listing PI_prog_A (A_OBJ 12)); cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (@pa_val_range _ A_prog_listing PI_prog_A (A_OBJ 12)); lia).
    unfold IMG_LO, IMG_TOP in Hg12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 vrd_Bx SHADOW_OFF);
      [cbn [sv_denot vrd_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (@pa_val_range _ A_prog_listing PI_prog_A (A_OBJ 1)); lia).
    unfold IMG_LO, IMG_TOP in Hg1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33%nat 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgotu).
  + rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
      [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (vrd_val_mem_of_rd32 (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold vrd_e_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (@pa_val_range _ A_prog_listing PI_prog_A (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (@pa_val_range _ A_prog_listing PI_prog_A (A_OBJ 1)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (@pa_val_range _ A_prog_listing PI_prog_A (A_OBJ 12)); lia).
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold IMG_LO, IMG_TOP in Hg0, Hg1, Hg12.
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [vrd_e_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 0) with 1.
    repeat split; try exact I; try exact Hal16; try (rewrite Z.mod_1_r; reflexivity); try lia.
  + apply A_alias_hints_ok. intros a Ha. subst E. unfold vrd_e_env.
    rewrite (@Eimg_img _ A_prog_listing PI_prog_A _ a Ha).
    apply unsigned_lit_small. exact (A_prog_val_range a).
Qed.

(* ---- the walk's further Section hypotheses; each is a positive fact the instance supplies ---- *)
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable SK : YI16.sink_head.
(* YGcallx's owned-low law (AR_laws_cf's alc_owned_low at the instance) *)
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
(* YGcallSx's model progress of the frame-area malloc is PROVED at any relation: YGcallScf.stack_malloc_x_any *)
Let SMX := stack_malloc_x_any SEGS ARx.
(* the two arguments of the PROVED class-0 frame contract FCm0s.stack_malloc0_contract_x (its segments tfibsegs and
   this listing's rsegs are both Asan.M.loaded_segments) *)
Hypothesis FSI : fs_iface SEGS B ARx.
Hypothesis TB : AF0m.TfibSyms B.

(* the recursion's stack bound covers the frame call's ESTACK window (PrhImg's pi_frame_nonneg) *)
Lemma vrd_stk_big : forall d, 16384 <= STK_parse_value d.
Proof.
intros d. unfold STK_parse_value, LEAF_pv_pi, zmaxl. cbn [fold_right].
unfold STK_RT_STRTOD, ESTACK.
pose proof (pi_frame_nonneg F_parse_value) as H1. pose proof (pi_frame_nonneg F_parse_items) as H2.
assert (H3 : 0 <= pi_frame F_parse_value + pi_frame F_parse_items) by lia.
pose proof (Z.mul_nonneg_nonneg (Z.of_nat (S (PjGrammar.MAXD - d))) _ (Nat2Z.is_nonneg _) H3) as H.
lia.
Qed.

(* the return slot of the frame call (row 31, parse_value + 0x74) *)
Definition vrd_R31 : Z := vrd_PC + 116.
(* the 32-aligned frame base of rows 17..18: sp0 - 0xa0 rounded down to 32 *)
Definition vrd_A (sp0 : Z) : Z := sp0 - 160 - (sp0 - 160) mod 32.

Let RUN := paj_run_x (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS.

(* the state right after the frame call returned (row 31) *)
Definition vrd_p31 (STK e q v : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists S2 regs2 mem1 mem2 md2 pos k,
    c' = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + vrd_R31)) mem2 (seg_rom SEGS)) md2 /\
    ajournal_x (SK := SK) SEGS B prh_pst ARx (STK + e) (spZ regs + e) (rd_fp q v)
      ly S Hp W mem md [(0, pos)] ly S2 Hp W mem2 md2 k /\
    frames S2 = (0, pos) :: frames S /\ ~ In (0, pos) (frames S) /\ ablocks B ly S2 = ablocks B ly S /\
    blocks_bytes S2 = blocks_bytes S /\ (exists f, S2 = set_fs f S) /\
    getr regs2 10 = w64 (frame_addr ly 0 pos) /\
    getr regs2 2 = w64 (vrd_A (spZ regs)) /\ getr regs2 9 = w64 (vrd_A (spZ regs)) /\
    getr regs2 8 = w64 (spZ regs) /\ getr regs2 19 = w64 v /\ getr regs2 20 = w64 q /\
    getr regs2 23 = w64 SHADOW_OFF /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
    getr regs2 21 = getr regs 21 /\ getr regs2 22 = getr regs 22 /\ getr regs2 25 = getr regs 25 /\
    zero_shadow (aview SEGS (w_H W) mem2) SHADOW_OFF (frame_addr ly 0 pos) (fs_frame_bytes 0) /\
    rdword (aview SEGS (w_H W) mem2) (frame_addr ly 0 pos + fs_frame_bytes 0 - 8) = Some (flag_addr ly 0 pos) /\
    (forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + fs_frame_bytes 0 -> apresent (w_H W) mem2 a) /\
    vrd_saved (rdW W mem2) (spZ regs) regs /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
       aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) /\
    acall_kept_x SEGS B ly S W mem1 W mem2 (vrd_A (spZ regs) - ESTACK) (vrd_A (spZ regs)) (fun _ => False).

(* bytes whose views agree carry a value *)
Lemma vrd_val_mem_keep : forall (W : world SEGS) mem mem' a n v,
  (forall k, (k < n)%nat -> aview SEGS (w_H W) mem' (a + Z.of_nat k) = aview SEGS (w_H W) mem (a + Z.of_nat k)) ->
  val_mem SEGS (rdW W mem) a n v -> val_mem SEGS (rdW W mem') a n v.
Proof.
intros W mem mem' a n v Hk Hv k Hlt. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem' (a + Z.of_nat k) (Hk k Hlt)).
exact (Hv k Hlt).
Qed.

(* a callee-saved register at its bv name (YCbq's aregs_preserved is stated at Z_to_bv 5 r) *)
Lemma vrd_kept : forall (regs regs' : bvmap 5 word) (z : Z) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof.
intros regs regs' z r H Hc Hz. pose proof (H z Hc) as HH.
rewrite <- Hz, Z_to_bv_bv_unsigned in HH. exact HH.
Qed.

(* a word chunk of a region of a symbolic state names the value at its offset *)
Lemma vrd_save_of_st_ok : forall E ss ms (H : word -> bool) r0 i,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r0 ->
  forall o (n : nat) v, In (YP09.mkChunk o (CVal 8 (SOff n 0))) (YP09.r_chunks r0) ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r0) + o) 8 v.
Proof.
intros E ss ms H r0 i HS Hi o n v Hin Hn Hv.
pose proof (st_ok_chunk SEGS E ss (restrict H ms) i r0 _ HS Hi Hin) as Hc.
exact (val_of_chunk_ok SEGS E _ _ o 8 (SOff n 0) v Hc
  ltac:(cbn [sv_denot]; rewrite Hn, Z.add_0_r, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Lemma vrd_mod32_cases : forall x, 0 <= x -> x mod 16 = 0 -> x mod 32 = 0 \/ x mod 32 = 16.
Proof.
intros x Hx H16.
pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as Hb.
assert (H : (x mod 32) mod 16 = 0)
  by (rewrite <- (Znumtheory.Zmod_div_mod 16 32 x ltac:(lia) ltac:(lia) ltac:(exists 2; reflexivity)); exact H16).
pose proof (Z.div_mod (x mod 32) 16 ltac:(lia)) as Hd. rewrite H, Z.add_0_r in Hd.
pose proof (Z.div_pos (x mod 32) 16 ltac:(lia) ltac:(lia)).
assert ((x mod 32) / 16 <= 1) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.

(* the frame base of rows 17..18 lies 160 or 176 bytes below a 16-aligned entry sp, and is 32-aligned *)
Lemma vrd_A_bounds : forall sp0, sp0 mod 16 = 0 -> 160 <= sp0 ->
  sp0 - 176 <= vrd_A sp0 /\ vrd_A sp0 <= sp0 - 160 /\ vrd_A sp0 mod 32 = 0.
Proof.
intros sp0 H16 H160.
assert (Hm : (sp0 - 160) mod 32 = 0 \/ (sp0 - 160) mod 32 = 16).
{ apply vrd_mod32_cases; [lia|]. rewrite <- Z.add_opp_r, Z.add_mod, H16 by lia. reflexivity. }
unfold vrd_A. pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as Hd.
split; [destruct Hm as [Hm|Hm]; rewrite Hm; lia|]. split; [destruct Hm as [Hm|Hm]; rewrite Hm; lia|].
replace (sp0 - 160 - (sp0 - 160) mod 32) with ((sp0 - 160) / 32 * 32) by lia. apply Z_mod_mult.
Qed.

Lemma vrd_seg1 : forall d ly S Hp W regs mem md ch e q v,
  afn_pre_x SEGS B ARx (STK_parse_value d) ly S Hp W regs mem md ch ->
  fwin ly W regs mem e ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v ->
  count_cid 0 (frames S) < fs_frames 0 ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_parse_value) regs mem md)
    (vrd_p31 (STK_parse_value d) e q v ly S Hp W regs mem md).
Proof.
intros d ly S Hp W regs mem md ch e q v HPRE HWIN H10 H11 Hcnt.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big d) as HSTK.
assert (HJ0 : ajournal_x (SK := SK) SEGS B prh_pst ARx (STK_parse_value d + e) (spZ regs + e) (rd_fp q v)
   ly S Hp W mem md [] ly S Hp W mem md 0)
  by exact (ajournal_x_init_W (SK := SK) SEGS B prh_pst ARx _ e (rd_fp q v) ly S Hp W regs mem md ch HPRE HWIN).
assert (HS : st_ok_pi SEGS VAL (vrd_e_env regs) ss_vrd_e
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_PC)) mem (seg_rom SEGS))))
  by (apply (vrd_entry _ ly S Hp W regs mem md ch HPRE); lia).
set (E := vrd_e_env regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold vrd_e_env; apply Eimg_env).
assert (SHOK : sh_ok SEGS vrd_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold cfg_at. change (w64 (SIGMA AS_parse_value)) with (Z_to_bv 64 (BASE + vrd_PC)).
paj_run_tok_x RUN HS HJ0 SHOK vrd_Bspan.
{ unfold ss_vrd_e, vrd_e_regions, stack_region, got_regionP, bcell_regionP. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- e));
  [reflexivity | cbn [YP09.r_base]; rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
(* ---- at the call of __asan_stack_malloc_0 (row 30) ---- *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (25%bv : bv 5) R25.
assert (EV : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat regs _ n r Hr)).
assert (E32 : ew E 32 = w64 SHADOW_OFF)
  by (subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
(* the frame base of rows 17..18 *)
assert (US1 : U E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) = vrd_A (spZ regs)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Usp.
  rewrite (zcanon_id (spZ regs + -160)) by (unfold M64; lia).
  change (zcanon (-32)) with (Z.land (- 2 ^ 5) (Z.ones 64)).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite land_neg_pow2 by lia.
  unfold vrd_A. change (2 ^ 5) with 32.
  replace (spZ regs + -160) with (spZ regs - 160) by lia.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)).
  unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (HspT : spZ (ms_regs ms) = vrd_A (spZ regs)) by (unfold spZ at 1; rewrite R2; exact US1).
assert (US1b : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)) = vrd_A (spZ regs)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, US1, (zcanon_id 0) by (unfold M64; lia).
  rewrite Z.add_0_r. apply zcanon_id. unfold M64, vrd_A.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)). lia. }
assert (HA9 : bv_unsigned (getr (ms_regs ms) 9) = vrd_A (spZ regs)) by (rewrite R9; exact US1b).
assert (Hm32 : (spZ regs - 160) mod 32 = 0 \/ (spZ regs - 160) mod 32 = 16).
{ apply vrd_mod32_cases; [lia|]. rewrite <- Z.add_opp_r, Z.add_mod, Hal16 by lia. reflexivity. }
assert (HAb : spZ regs - 176 <= vrd_A (spZ regs) <= spZ regs - 160)
  by (unfold vrd_A; destruct Hm32 as [H32|H32]; rewrite H32; lia).
assert (HAm16 : (vrd_A (spZ regs) - (spZ regs + e)) mod 16 = 0).
{ unfold vrd_A.
  pose proof (Z.div_mod e 16 ltac:(lia)) as Hdd. rewrite He16, Z.add_0_r in Hdd.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as Hds. rewrite Hal16, Z.add_0_r in Hds.
  destruct Hm32 as [H32|H32]; rewrite H32;
  [ replace (spZ regs - 160 - 0 - (spZ regs + e)) with ((-10 - e / 16) * 16) by lia
  | replace (spZ regs - 160 - 16 - (spZ regs + e)) with ((-11 - e / 16) * 16) by lia ];
  apply Z_mod_mult. }
assert (VR31 : vrd_R31 = 18852) by (vm_compute; reflexivity).
assert (SM0 : SIGMA AS___asan_stack_malloc_0 = pc_stack_malloc (as_code B) 0)
  by (rewrite (AF0m.ts_code B TB); vm_compute; reflexivity).
(* what the prologue's stores left alone: everything outside the 192 bytes below the entry sp *)
assert (KEEP1 : forall z, 0 <= z < 2 ^ 64 -> ~ (spZ regs - 192 <= z < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) z = aview SEGS (w_H W) mem z).
{ intros z Hz Hnot. apply aview_eq_of. apply HFr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  intros (r & Hin & Hr). unfold ss_vrd_e, vrd_e_regions, stack_region, got_regionP, bcell_regionP in Hin.
  cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia |]).
  destruct Hin. }
(* the saves of rows 3..16, as chunks of the stack region *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (vrd_save_of_st_ok E ss ms (w_H W) r0 0 HS ltac:(vm_compute; reflexivity)) as HSV;
  assert (HB0 : base_val E (YP09.r_base r0) = spZ regs) by (cbn [base_val YP09.r_base]; exact Usp) end.
(* ---- the frame call: aj_stack_malloc_at_x over the proved class-0 contract ---- *)
rewrite SM0.
pose proof (FCm0s.stack_malloc0_contract_x B ARx FSI TB) as ASM0.
eapply SRr_bind.
{ eapply (aj_stack_malloc_at_x (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A) (pal_env B PAL)
    OWNLOW SMX 0 ASM0 ltac:(lia)
    W (ms_regs ms) (ms_mem ms) (STK_parse_value d + e) (spZ regs + e) (rd_fp q v) ly S Hp W mem md [] ly S Hp _ 0
    (vrd_A (spZ regs) - (spZ regs + e)) (Z_to_bv 64 (BASE + vrd_R31)) HJ0).
  - rewrite HspT. lia.
  - exact HAm16.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, (EV 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp.
  - rewrite R4, (EV 4%nat 4%bv ltac:(lia) eq_refl). exact Htp.
  - rewrite R1, VR31. reflexivity.
  - rewrite VR31. apply (ret_ok_codeptr_v (PI := PI_prog_A)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta. intros W' c' Hwle (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
  & Hbb2 & Hz & Hflagw & Hfpres & HKept & HJc & Hsetfs).
replace (spZ regs + e + (vrd_A (spZ regs) - (spZ regs + e))) with (vrd_A (spZ regs)) in HKept by lia.
pose proof HKept as (K1 & K2 & K3 & K4 & K5 & K6).
apply SRr_ret. split; [reflexivity|].
exists S2, regs2, (ms_mem ms), mem2, md2, pos, 0.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact Eab|].
split; [exact Hbb2|]. split; [exact Hsetfs|]. split; [exact Ha0|].
assert (KR : forall z (r : bv 5), acallee_saved z -> bv_unsigned r = z -> getr regs2 r = getr (ms_regs ms) r)
  by (intros z r Hz0 Hr0; exact (vrd_kept _ _ z r HP2 Hz0 Hr0)).
split.
{ rewrite (KR 2 2%bv ltac:(unfold acallee_saved; lia) eq_refl). unfold w64. rewrite <- HspT. unfold spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite (KR 9 9%bv ltac:(unfold acallee_saved; lia) eq_refl). unfold w64. rewrite <- HA9.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite (KR 8 8%bv ltac:(unfold acallee_saved; lia) eq_refl), R8, E2. unfold w64, spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite (KR 19 19%bv ltac:(unfold acallee_saved; lia) eq_refl), R19, (EV 11%nat 11%bv ltac:(lia) eq_refl). exact H11. }
split.
{ rewrite (KR 20 20%bv ltac:(unfold acallee_saved; lia) eq_refl), R20, (EV 10%nat 10%bv ltac:(lia) eq_refl). exact H10. }
split.
{ rewrite (KR 23 23%bv ltac:(unfold acallee_saved; lia) eq_refl), R23. exact E32. }
split; [rewrite (KR 3 3%bv ltac:(unfold acallee_saved; lia) eq_refl), R3; exact (EV 3%nat 3%bv ltac:(lia) eq_refl)|].
split; [rewrite (KR 4 4%bv ltac:(unfold acallee_saved; lia) eq_refl), R4; exact (EV 4%nat 4%bv ltac:(lia) eq_refl)|].
split; [rewrite (KR 21 21%bv ltac:(unfold acallee_saved; lia) eq_refl), R21; exact (EV 21%nat 21%bv ltac:(lia) eq_refl)|].
split; [rewrite (KR 22 22%bv ltac:(unfold acallee_saved; lia) eq_refl), R22; exact (EV 22%nat 22%bv ltac:(lia) eq_refl)|].
split; [rewrite (KR 25 25%bv ltac:(unfold acallee_saved; lia) eq_refl), R25; exact (EV 25%nat 25%bv ltac:(lia) eq_refl)|].
split; [exact Hz|]. split; [exact Hflagw|]. split; [exact Hfpres|].
split; [| split; [exact KEEP1 | exact HKept]].
unfold vrd_saved, raZ. repeat split.
all: lazymatch goal with |- val_mem _ _ (spZ ?rg - ?o) 8 (bv_unsigned (getr _ ?r)) =>
  apply (vrd_val_mem_keep W (ms_mem ms) mem2);
  [intros k Hk; apply K1; [lia | lia] |];
  replace (spZ rg - o) with (spZ rg + (- o)) by lia; rewrite <- HB0;
  apply (HSV (- o) (Z.to_nat (bv_unsigned r)));
  [vm_compute; repeat (first [left; reflexivity | right])
  | rewrite Z_to_bv_bv_unsigned; apply EV; vm_compute; [lia | reflexivity]
  | apply bv_unsigned_in_range] end.
Qed.

(* vrd_seg1 WITH the memory invariant (header): the same walk, P carried by paj_run_x_inv through rows 1..30 and
   across the class-0 frame call by srr_inv_call through the keep of YGcallMxmn.aj_stack_malloc_at_xm. That rule needs
   the class-0 contract with the keep: the PROVED FCm01xm.stack_malloc0_contract_xm B ARx FSI TB (header). *)
Lemma vrd_seg1_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall d ly S Hp W regs mem md ch e q v,
  afn_pre_x SEGS B ARx (STK_parse_value d) ly S Hp W regs mem md ch ->
  fwin ly W regs mem e ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v ->
  count_cid 0 (frames S) < fs_frames 0 ->
  P mem ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_parse_value) regs mem md)
    (fun W' c' => vrd_p31 (STK_parse_value d) e q v ly S Hp W regs mem md W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL d ly S Hp W regs mem md ch e q v HPRE HWIN H10 H11 Hcnt HPM.
pose proof (FCm01xm.stack_malloc0_contract_xm B ARx FSI TB) as HSM0.
pose proof (paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW) as RUNI.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big d) as HSTK.
assert (HJ0 : ajournal_x (SK := SK) SEGS B prh_pst ARx (STK_parse_value d + e) (spZ regs + e) (rd_fp q v)
   ly S Hp W mem md [] ly S Hp W mem md 0)
  by exact (ajournal_x_init_W (SK := SK) SEGS B prh_pst ARx _ e (rd_fp q v) ly S Hp W regs mem md ch HPRE HWIN).
assert (HS : st_ok_pi SEGS VAL (vrd_e_env regs) ss_vrd_e
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_PC)) mem (seg_rom SEGS))))
  by (apply (vrd_entry _ ly S Hp W regs mem md ch HPRE); lia).
set (E := vrd_e_env regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold vrd_e_env; apply Eimg_env).
assert (SHOK : sh_ok SEGS vrd_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold cfg_at. change (w64 (SIGMA AS_parse_value)) with (Z_to_bv 64 (BASE + vrd_PC)).
paj_run_tok_x_inv RUNI HS HJ0 SHOK HPM vrd_Bspan.
{ unfold ss_vrd_e, vrd_e_regions, stack_region, got_regionP, bcell_regionP. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- e));
  [reflexivity | cbn [YP09.r_base]; rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
(* ---- at the call of __asan_stack_malloc_0 (row 30) ---- *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (25%bv : bv 5) R25.
assert (EV : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat regs _ n r Hr)).
assert (E32 : ew E 32 = w64 SHADOW_OFF)
  by (subst E; unfold vrd_e_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
(* the frame base of rows 17..18 *)
assert (US1 : U E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) = vrd_A (spZ regs)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Usp.
  rewrite (zcanon_id (spZ regs + -160)) by (unfold M64; lia).
  change (zcanon (-32)) with (Z.land (- 2 ^ 5) (Z.ones 64)).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite land_neg_pow2 by lia.
  unfold vrd_A. change (2 ^ 5) with 32.
  replace (spZ regs + -160) with (spZ regs - 160) by lia.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)).
  unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (HspT : spZ (ms_regs ms) = vrd_A (spZ regs)) by (unfold spZ at 1; rewrite R2; exact US1).
assert (US1b : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)) = vrd_A (spZ regs)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, US1, (zcanon_id 0) by (unfold M64; lia).
  rewrite Z.add_0_r. apply zcanon_id. unfold M64, vrd_A.
  pose proof (Z.mod_pos_bound (spZ regs - 160) 32 ltac:(lia)). lia. }
assert (HA9 : bv_unsigned (getr (ms_regs ms) 9) = vrd_A (spZ regs)) by (rewrite R9; exact US1b).
assert (Hm32 : (spZ regs - 160) mod 32 = 0 \/ (spZ regs - 160) mod 32 = 16).
{ apply vrd_mod32_cases; [lia|]. rewrite <- Z.add_opp_r, Z.add_mod, Hal16 by lia. reflexivity. }
assert (HAb : spZ regs - 176 <= vrd_A (spZ regs) <= spZ regs - 160)
  by (unfold vrd_A; destruct Hm32 as [H32|H32]; rewrite H32; lia).
assert (HAm16 : (vrd_A (spZ regs) - (spZ regs + e)) mod 16 = 0).
{ unfold vrd_A.
  pose proof (Z.div_mod e 16 ltac:(lia)) as Hdd. rewrite He16, Z.add_0_r in Hdd.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as Hds. rewrite Hal16, Z.add_0_r in Hds.
  destruct Hm32 as [H32|H32]; rewrite H32;
  [ replace (spZ regs - 160 - 0 - (spZ regs + e)) with ((-10 - e / 16) * 16) by lia
  | replace (spZ regs - 160 - 16 - (spZ regs + e)) with ((-11 - e / 16) * 16) by lia ];
  apply Z_mod_mult. }
assert (VR31 : vrd_R31 = 18852) by (vm_compute; reflexivity).
assert (SM0 : SIGMA AS___asan_stack_malloc_0 = pc_stack_malloc (as_code B) 0)
  by (rewrite (AF0m.ts_code B TB); vm_compute; reflexivity).
(* what the prologue's stores left alone: everything outside the 192 bytes below the entry sp *)
assert (KEEP1 : forall z, 0 <= z < 2 ^ 64 -> ~ (spZ regs - 192 <= z < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) z = aview SEGS (w_H W) mem z).
{ intros z Hz Hnot. apply aview_eq_of. apply HFr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  intros (r & Hin & Hr). unfold ss_vrd_e, vrd_e_regions, stack_region, got_regionP, bcell_regionP in Hin.
  cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia |]).
  destruct Hin. }
(* the saves of rows 3..16, as chunks of the stack region *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (vrd_save_of_st_ok E ss ms (w_H W) r0 0 HS ltac:(vm_compute; reflexivity)) as HSV;
  assert (HB0 : base_val E (YP09.r_base r0) = spZ regs) by (cbn [base_val YP09.r_base]; exact Usp) end.
(* ---- the frame call: YGcallMxmn.aj_stack_malloc_at_xm over the class-0 contract with the keep ---- *)
rewrite SM0.
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_stack_malloc_at_xm (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A)
    (pal_env B PAL) OWNLOW SMX 0 HSM0 ltac:(lia)
    W (ms_regs ms) (ms_mem ms) (STK_parse_value d + e) (spZ regs + e) (rd_fp q v) ly S Hp W mem md [] ly S Hp _ 0
    (vrd_A (spZ regs) - (spZ regs + e)) (Z_to_bv 64 (BASE + vrd_R31)) HJ0).
  - rewrite HspT. lia.
  - exact HAm16.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, (EV 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp.
  - rewrite R4, (EV 4%nat 4%bv ltac:(lia) eq_refl). exact Htp.
  - rewrite R1, VR31. reflexivity.
  - rewrite VR31. apply (ret_ok_codeptr_v (PI := PI_prog_A)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta. intros W' c' Hwle (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
  & Hbb2 & Hz & Hflagw & Hfpres & HKept & HJc & Hsetfs & Hmn).
replace (spZ regs + e + (vrd_A (spZ regs) - (spZ regs + e))) with (vrd_A (spZ regs)) in HKept by lia.
pose proof HKept as (K1 & K2 & K3 & K4 & K5 & K6).
(* the invariant across the call: the callee's memnorm keep, through srr_inv_call *)
apply SRr_ret. split; [|cbn [cfg_ms ms_mem]; exact (PCALL _ _ Hmn HPM)].
split; [reflexivity|].
exists S2, regs2, (ms_mem ms), mem2, md2, pos, 0.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact Eab|].
split; [exact Hbb2|]. split; [exact Hsetfs|]. split; [exact Ha0|].
assert (KR : forall z (r : bv 5), acallee_saved z -> bv_unsigned r = z -> getr regs2 r = getr (ms_regs ms) r)
  by (intros z r Hz0 Hr0; exact (vrd_kept _ _ z r HP2 Hz0 Hr0)).
split.
{ rewrite (KR 2 2%bv ltac:(unfold acallee_saved; lia) eq_refl). unfold w64. rewrite <- HspT. unfold spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite (KR 9 9%bv ltac:(unfold acallee_saved; lia) eq_refl). unfold w64. rewrite <- HA9.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite (KR 8 8%bv ltac:(unfold acallee_saved; lia) eq_refl), R8, E2. unfold w64, spZ.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ rewrite (KR 19 19%bv ltac:(unfold acallee_saved; lia) eq_refl), R19, (EV 11%nat 11%bv ltac:(lia) eq_refl). exact H11. }
split.
{ rewrite (KR 20 20%bv ltac:(unfold acallee_saved; lia) eq_refl), R20, (EV 10%nat 10%bv ltac:(lia) eq_refl). exact H10. }
split.
{ rewrite (KR 23 23%bv ltac:(unfold acallee_saved; lia) eq_refl), R23. exact E32. }
split; [rewrite (KR 3 3%bv ltac:(unfold acallee_saved; lia) eq_refl), R3; exact (EV 3%nat 3%bv ltac:(lia) eq_refl)|].
split; [rewrite (KR 4 4%bv ltac:(unfold acallee_saved; lia) eq_refl), R4; exact (EV 4%nat 4%bv ltac:(lia) eq_refl)|].
split; [rewrite (KR 21 21%bv ltac:(unfold acallee_saved; lia) eq_refl), R21; exact (EV 21%nat 21%bv ltac:(lia) eq_refl)|].
split; [rewrite (KR 22 22%bv ltac:(unfold acallee_saved; lia) eq_refl), R22; exact (EV 22%nat 22%bv ltac:(lia) eq_refl)|].
split; [rewrite (KR 25 25%bv ltac:(unfold acallee_saved; lia) eq_refl), R25; exact (EV 25%nat 25%bv ltac:(lia) eq_refl)|].
split; [exact Hz|]. split; [exact Hflagw|]. split; [exact Hfpres|].
split; [| split; [exact KEEP1 | exact HKept]].
unfold vrd_saved, raZ. repeat split.
all: lazymatch goal with |- val_mem _ _ (spZ ?rg - ?o) 8 (bv_unsigned (getr _ ?r)) =>
  apply (vrd_val_mem_keep W (ms_mem ms) mem2);
  [intros k Hk; apply K1; [lia | lia] |];
  replace (spZ rg - o) with (spZ rg + (- o)) by lia; rewrite <- HB0;
  apply (HSV (- o) (Z.to_nat (bv_unsigned r)));
  [vm_compute; repeat (first [left; reflexivity | right])
  | rewrite Z_to_bv_bv_unsigned; apply EV; vm_compute; [lia | reflexivity]
  | apply bv_unsigned_in_range] end.
Qed.


(* ---- run 2: from the frame call's return (row 31) to the first cursor test (row 77) ----
   atoms: the registers (sr_atoms: s1 = 9, a0 = 10 = the frame F, s4 = 20 = q, s7 = 23 = SHADOW_OFF), and four
   extras: 32 = shadow_addr F, 33 = p (in->p), 34 = text + len (in->end), 35 = shadow_addr q. The run writes the
   frame's shadow, a region inside the shadow band, so it runs WITHOUT the token engine (empty band, as WalkS8a's
   ex_value entry does): the two shadow bytes of q it reads are chunks of their own region, named by alias. *)
Definition vrd_Bx2 : sv := SLit 0.
Definition vrd_Bspan2 : Z * Z := (0, 0).
Definition vrd_r31_regions : smem :=
  [ YP09.mkRegion (Some 20%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))];
    YP09.mkRegion (Some 10%nat) 0 64 0 24 [];
    YP09.mkRegion (Some 32%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 9%nat) 48 56 48 56 [];
    YP09.mkRegion (Some 35%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0)); YP09.mkChunk 1 (CVal 1 (SLit 0))] ].
Definition vrd_r31_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 45) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 5); (20%nat, mkAF 4096 (2 ^ 47) 3);
           (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 2);
           (35%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)]
    []
    ((SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 23 0), SOff 32 0) ::
     (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SOff 23 0), SOff 35 0) ::
     (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 8) (SLit 3)) (SOff 23 0), SOff 35 1) :: A_alias_hints).
Definition ss_vrd_31 : sstate := mkSS vrd_R31 sr_atoms vrd_r31_regions None vrd_r31_facts.

(* the listing slots of the rows the walk stops at (row n is at parse_value + 4 (n - 2)) *)
Definition vrd_R77 : Z := vrd_PC + 300.
Definition vrd_R83 : Z := vrd_PC + 324.
Definition vrd_R102 : Z := vrd_PC + 400.

(* the shadow-address expressions the code builds, `(x + c) >> 3 + s7`, evaluated *)
Lemma vrd_U_shadow : forall E n c m,
  0 <= bv_unsigned (ew E n) + c < 2 ^ 64 -> 0 <= bv_unsigned (ew E m) + (bv_unsigned (ew E n) + c) / 8 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) =
  bv_unsigned (ew E m) + (bv_unsigned (ew E n) + c) / 8.
Proof.
intros E n c m H1 H2. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite (zcanon_id (bv_unsigned (ew E n) + c)) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (bv_unsigned (ew E n) + c) 8 ltac:(lia) ltac:(lia)).
assert ((bv_unsigned (ew E n) + c) / 8 <= bv_unsigned (ew E n) + c) by (apply Z.div_le_upper_bound; lia).
rewrite (zcanon_id ((bv_unsigned (ew E n) + c) / 8)) by (unfold M64; lia).
pose proof (bv_unsigned_in_range 64 (ew E m)) as Hrm. change (bv_modulus 64) with (2 ^ 64) in Hrm.
rewrite Z.add_0_r. rewrite (zcanon_id (bv_unsigned (ew E m))) by (unfold M64; lia).
rewrite Z.add_comm. apply zcanon_id. unfold M64. lia.
Qed.

(* a one-byte literal chunk of a region names the byte the memory holds *)
Lemma vrd_aview_chunk_byte : forall E ss ms (H : word -> bool) r0 i,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r0 ->
  forall off z, In (YP09.mkChunk off (CVal 1 (SLit z))) (YP09.r_chunks r0) ->
  aview SEGS H (ms_mem ms) (base_val E (YP09.r_base r0) + off) = Some (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0)).
Proof.
intros E ss ms H r0 i HS Hi off z Hin.
pose proof (st_ok_chunk SEGS E ss (restrict H ms) i r0 _ HS Hi Hin) as Hc.
destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb & Hm). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb.
injection Hb as <-. unfold aview. cbn [YP09.c_off ms_mem restrict] in Hm. rewrite Z.add_0_r in Hm. rewrite Hm.
reflexivity.
Qed.

(* a byte whose view is 0, as a one-byte value *)
Lemma vrd_val_mem1 : forall (H : word -> bool) mem x,
  aview SEGS H mem x = Some 0 -> val_mem SEGS (mrestrict H mem) x 1 0.
Proof.
intros H mem x Hx k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hx.
destruct (mbyte SEGS (mrestrict H mem) x) as [b|] eqn:Eb; cbn [option_map] in Hx; [|discriminate].
injection Hx as Hx. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hx. reflexivity.
Qed.

(* an unsigned compare of two in-range literals *)
Lemma vrd_geu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. unfold branch_taken, bv_ltu. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

(* a word chunk of a region names the value at its offset (any symbolic value) *)
Lemma vrd_val_of_st_ok : forall E ss ms (H : word -> bool) r0 i,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r0 ->
  forall o e v, In (YP09.mkChunk o (CVal 8 e)) (YP09.r_chunks r0) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r0) + o) 8 v.
Proof.
intros E ss ms H r0 i HS Hi o e v Hin Hn Hv.
pose proof (st_ok_chunk SEGS E ss (restrict H ms) i r0 _ HS Hi Hin) as Hc.
exact (val_of_chunk_ok SEGS E _ _ o 8 e v Hc Hn ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* the cursor's numeric facts, by name *)
Lemma vrd_in_facts : forall m q text len p d tb, pj_in_okR SEGS m q text len p d tb ->
  q mod 8 = 0 /\ 0 < text /\ text + len < 2 ^ 62 /\ text <= p /\ p <= text + len /\
  Z.of_nat (length tb) = len /\ (q + 24 <= text \/ text + len <= q).
Proof. intros m q text len p d tb H. unfold pj_in_okR in H. tauto. Qed.

Let RUNTO := paj_run_to_x (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS.
Let BR := paj_branch (PI := PI_prog_A).

(* ---- the memory invariant (header): the trivial one, at which each X_inv collapses to X; dropping it from a post
   (SRr is monotone in its post); and SRr_ret for a post that carries it (its P half is the run's last memory) ---- *)
Lemma vrd_true_laws : srr_inv_laws SEGS (fun _ => True).
Proof. split; intros; exact I. Qed.
Lemma vrd_srr_drop : forall (W : world SEGS) (c : config) (Q : world SEGS -> config -> Prop)
    (P : (word -> option byte) -> Prop),
  SRr SEGS W c (fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c'))) -> SRr SEGS W c Q.
Proof. intros W c Q P H. eapply SRr_bind; [exact H|]. intros W' c' _ (HQ & _). apply SRr_ret. exact HQ. Qed.
Ltac vrd_retP HPM := apply SRr_ret; split; [|cbn [cfg_ms ms_mem] in HPM |- *; exact HPM].


(* ---- the white-space loop (rows 83..101), one iteration from the loop head ----
   atoms: a0 = 10 = a1 = 11 = the cursor, a2 = 12 = in->end, s4 = 20 = q, s7 = 23 = SHADOW_OFF, s11 = 27 = q's
   shadow address; a3 and a4 hold their literals (32 and the mask); one extra: 32 = the text byte at the cursor.
   The text byte's shadow gate runs on the token engine (band = the shadow, base s7): its slow block (rows 99..100)
   leaves one obligation, range_addressable at the cursor, which the text's own src_rd discharges. *)
Definition vrd_BxL : sv := SOff 23 0.
Definition vrd_SHL : list shent := [mkSHE 20 0 24].
Definition vrd_lp_regs : list sv := sr_set (sr_set sr_atoms (13%bv) (SLit 32)) (14%bv) (SLit vrd_ws_mask).
Definition vrd_lp_regions : smem :=
  [ YP09.mkRegion (Some 20%nat) 0 24 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 10 0))];
    YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
    YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ].
Definition vrd_lp_facts : facts :=
  mkFacts [(10%nat, mkAF 4096 0x7fffff800000 0); (11%nat, mkAF 4096 0x7fffff800000 0); (12%nat, mkAF 0 (2 ^ 62) 0);
           (20%nat, mkAF 4096 (2 ^ 47 - 24) 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (27%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition ss_vrd_lp : sstate := mkSS vrd_R83 vrd_lp_regs vrd_lp_regions None vrd_lp_facts.

(* ---- INSTANCE FACTS the walk after the frame call needs; each is a positive fact the instance supplies ---- *)
(* the laws' head size is the allocator's (AR_laws_cf at the instance) *)
Hypothesis HLc : HL = cf_head.
(* the image's symbol facts (YG0n.asyms_ok: the registered zero-shadow globals) *)
Hypothesis SYMS : asyms_ok B.
(* IMAGE FACT, IelemE's VrdIStep.v convention (same name, same statement): every image byte's shadow is readable *)
Hypothesis H_imgvis : forall ly' S' Hp' W' mem' md' a, ARx ly' S' Hp' W' mem' md' -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W') mem' (shadow_addr a) <> None.
(* IMAGE FACT: alloc.c's statics (the ledger globals) are image bytes the runtime does not own, apart from errno
   (S1ImgA.pst_in_img_A for the first) *)
Hypothesis H_pst : forall a, Exists (in_zr a) prh_pst ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* PARAMETER FACT: the allocator's block head holds at least the 8-byte size word prh_hblock reads (16 in the
   preset's CfParams) *)
Hypothesis H_cfhead : 8 <= cf_head.
(* INSTANCE FACT (a Theorem Labs lane's ruling: ONE name, a Section hypothesis in every file whose proofs use it, never a state
   conjunct): the allocator's head is the model's HEAD (preset alloc.c's 16), so the callee texts' requests (cf_head)
   meet the model's events (PresetReqAt.rd_hevs, HEAD). Used here by vrd_pkR_str (vrd_disp_body's string counts from
   the entry counts). Witness at the REAL instance: vrd_HI_head_preset at the end of this file, by reflexivity at
   CfParams_preset. *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.

(* a class's live-frame count is at most the number of live frames *)
Lemma vrd_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p0] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia. Qed.

(* the ledger's hidden bases, read through S1Ledger (prh_ledger_iff, prh_hp_fresh): with S1Ledger.prh_ledger_hblock
   for the heads, no proof in this file destructs prh_ledger or prh_glob by position, so a conjunct the kit adds to
   either costs nothing here *)
Lemma vrd_ledger_hp : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own h,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In h Hp -> exists k, In (h + cf_head, k) Lam.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own h HLd Hh.
pose proof (proj2 (proj1 (S1Ledger.prh_ledger_iff (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran most own) HLd))
  as HB.
destruct (in_dec Z.eq_dec (h + cf_head) (map fst Lam)) as [Hi | Hn].
- apply in_map_iff in Hi as ([a k] & Ea & Hin). cbn [fst] in Ea. subst a. exists k. exact Hin.
- exfalso. exact (S1Ledger.prh_hp_fresh (PA := PI_prog_A) B ly S Hp W mem Lam h HB Hn Hh).
Qed.

(* parse_string's events at a string value are a PREFIX of the value's: at skip x = 34 :: y, jr_value's string arm is
   jr_string y bound to the rest (PjGrammar.jrv; the kit's prhPs_evs_of_value reads the same arm), and prhPs_evs y []
   is jr_string y []'s model list under HI_head (prhPs_evs_model). A peak over a prefix is at most the peak over the
   whole (PresetRun.pkR_app), so tparse_value_specX's entry counts bound parse_string's at the string arm. *)
Lemma vrd_pkR_str : forall (f : Z -> bool) (L : list Z) (d : nat) (x y : list Z),
  PjGrammar.skip x = 34 :: y ->
  (PresetRun.pkR f L (prhPs_evs y []) <= PresetRun.pkR f L (PresetReqAt.rd_hevs (prhPv_gtrace d x)))%nat.
Proof.
intros f L d x y Hs. unfold prhPv_gtrace, PjGrammar.jr_value. cbn [PjGrammar.jrv].
rewrite Hs. cbv beta iota. change (34 =? 123) with false. change (34 =? 91) with false.
change (34 =? 34) with true. cbv beta iota.
match goal with
| |- context [PjGrammar.jbind (PjGrammar.jr_string y) ?k []] =>
    destruct (prhReader_jbind_pre _ _ (PjGrammar.jr_string y) k []) as [t Ht]; rewrite Ht
end.
rewrite (prhPs_evs_model y [] HI_head).
assert (E : forall a b, PresetReqAt.rd_hevs (a ++ b) = PresetReqAt.rd_hevs a ++ PresetReqAt.rd_hevs b)
  by (intros a b; unfold PresetReqAt.rd_hevs; apply flat_map_app).
rewrite E, PresetRun.pkR_app. apply Nat.le_max_l.
Qed.

(* ---- the walk after the frame call: the entry data and the post-call facts are fixed ---- *)
Section post.
Variables (d : nat) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (e q v text len p : Z) (tb : list Z)
  (S2 : astate) (mem1 mem2 : word -> option byte) (pos : Z).
Hypothesis HPRE : afn_pre_x SEGS B ARx (STK_parse_value d) ly S Hp W regs mem md ch.
Hypothesis HWIN : fwin ly W regs mem e.
Hypothesis HIN : pj_in_okR SEGS (rdW W mem) q text len p (Z.of_nat d) tb.
Hypothesis Hq1 : spZ regs <= q.
Hypothesis Hq2 : q + 24 <= spZ regs + e.
Hypothesis Hfrs2 : frames S2 = (0, pos) :: frames S.
Hypothesis Hnin : ~ In (0, pos) (frames S).
Hypothesis Eab : ablocks B ly S2 = ablocks B ly S.
Hypothesis Hflag : rdword (aview SEGS (w_H W) mem2) (frame_addr ly 0 pos + fs_frame_bytes 0 - 8) = Some (flag_addr ly 0 pos).
Hypothesis Hfp : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + fs_frame_bytes 0 -> apresent (w_H W) mem2 a.
Hypothesis KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
  aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a.
Hypothesis HKept : acall_kept_x SEGS B ly S W mem1 W mem2 (vrd_A (spZ regs) - ESTACK) (vrd_A (spZ regs)) (fun _ => False).

#[local] Notation F := (frame_addr ly 0 pos).
#[local] Notation SF := (SHADOW_OFF + frame_addr ly 0 pos / 8).
#[local] Notation AF := (vrd_A (spZ regs)).
#[local] Notation STKe := (STK_parse_value d + e).
#[local] Notation AJp := (fun memc mdc k =>
  ajournal_x (SK := SK) SEGS B prh_pst ARx (STK_parse_value d + e) (spZ regs + e) (rd_fp q v)
    ly S Hp W mem md [(0, pos)] ly S2 Hp W memc mdc k).

(* the walk's state after run 2: the journal from entry, every byte but the four written windows as after the call,
   the frame written, the cursor's p word, and the registers every later row reads *)
Definition vrd_mid (pc pcur : Z) (Rx : bvmap 5 word -> Prop) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regsc memc mdc k,
    c' = mkCfg (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc /\
    AJp memc mdc k /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) -> ~ (SF <= a < SF + 8) ->
       ~ (q <= a < q + 8) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem2 a) /\
    vrd_frame W memc ly pos /\
    val_mem SEGS (rdW W memc) q 8 pcur /\
    getr regsc 2 = w64 AF /\ getr regsc 9 = w64 AF /\ getr regsc 8 = w64 (spZ regs) /\
    getr regsc 18 = w64 F /\ getr regsc 26 = w64 F /\ getr regsc 19 = w64 v /\ getr regsc 20 = w64 q /\
    getr regsc 21 = getr regs 21 /\ getr regsc 22 = getr regs 22 /\ getr regsc 25 = getr regs 25 /\
    getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\
    getr regsc 23 = w64 SHADOW_OFF /\ getr regsc 24 = w64 SF /\ getr regsc 27 = w64 (SHADOW_OFF + q / 8) /\
    getr regsc 12 = w64 (text + len) /\ Rx regsc.

(* the loop head's own registers (rows 78..82): a0 = a1 = the cursor, a3 = 32, a4 = the white-space mask *)
Definition vrd_loopregs (pcur : Z) (regsc : bvmap 5 word) : Prop :=
  getr regsc 10 = w64 pcur /\ getr regsc 11 = w64 pcur /\ getr regsc 13 = w64 32 /\ getr regsc 14 = w64 vrd_ws_mask.

Lemma vrd_seg2_inv : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall regs2 md2 k,
  AJp mem2 md2 k ->
  getr regs2 10 = w64 F -> getr regs2 2 = w64 AF -> getr regs2 9 = w64 AF ->
  getr regs2 8 = w64 (spZ regs) -> getr regs2 19 = w64 v -> getr regs2 20 = w64 q ->
  getr regs2 23 = w64 SHADOW_OFF -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 25 = getr regs 25 ->
  P mem2 ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + vrd_R31)) mem2 (seg_rom SEGS)) md2)
    (fun W' c' => ((p = text + len /\ vrd_mid vrd_R102 p (fun _ => True) W' c') \/
                   (p < text + len /\ vrd_mid vrd_R83 p (vrd_loopregs p) W' c')) /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW regs2 md2 k HJ R10 R2 R9 R8 R19 R20 R23 R3 R4 R21 R22 R25 HPM.
pose proof (paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW) as RUNI.
pose proof (paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW) as RUNTOI.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big d) as HSTK.
pose proof HIN as (Ip & Iend & Idep & Irw & Iq8 & It0 & It62 & Itp1 & Itp2 & Ilen & Itb & Iqt & Id).
pose proof HKept as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (proj1 HJ) as HAR2. cbv beta in HAR2.
assert (HinF : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (alx_frames SEGS B ARx LAWS ly S2 Hp W mem2 md2 0 pos HAR2 HinF) as (HFal & HFapp & HFpres2 & HFSpres).
pose proof (frames_bounds_x SEGS B ARx LAWS ly S2 Hp W mem2 md2 0 pos HAR2 HinF) as (HF4096 & HFceil & _).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity.
rewrite HFB in HFapp, HFpres2, HFSpres, HFceil, Hflag, Hfp.
change (64 / 8) with 8 in HFSpres.
pose proof (vrd_A_bounds (spZ regs) Hal16 ltac:(lia)) as (HAb1 & HAb2 & HAal).
assert (HF8 : F mod 8 = 0)
  by (rewrite (Z.div_mod F 32) by lia; rewrite HFal, Z.add_0_r;
      replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult).
assert (HF8' : F / 8 = 4 * (F / 32))
  by (rewrite (Z.div_mod F 32) at 1 by lia; rewrite HFal, Z.add_0_r;
      replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z.div_mul; lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
pose proof (Z.div_mod q 8 ltac:(lia)) as DQ. rewrite Iq8, Z.add_0_r in DQ.
(* the bytes at and above the entry sp, from entry to the call's return *)
assert (TR : forall a n v0, spZ regs <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rdW W mem) a n v0 -> val_mem SEGS (rdW W mem2) a n v0).
{ intros a n v0 Ha Hn Hv. apply (vrd_val_mem_keep W mem1 mem2); [intros k0 Hk0; apply K1; lia|].
  apply (vrd_val_mem_keep W mem mem1); [intros k0 Hk0; apply KEEP1; lia | exact Hv]. }
(* the fresh state at row 31 *)
remember (@Eimg _ A_prog_listing PI_prog_A (Ereg regs2 [w64 SF; w64 p; w64 (text + len); w64 (SHADOW_OFF + q / 8)]))
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (UV : forall n (r : bv 5) z, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> getr regs2 r = w64 z ->
  0 <= z < 2 ^ 64 -> bv_unsigned (ew E n) = z).
{ intros n r z Hn Hr Hz Hz64. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs2 _ n r Hr), Hz. apply unsigned_lit_small. exact Hz64. }
assert (UX : forall j z, (j < 4)%nat ->
  nth j [w64 SF; w64 p; w64 (text + len); w64 (SHADOW_OFF + q / 8)] (Z_to_bv 64 0) = w64 z ->
  0 <= z < 2 ^ 64 -> bv_unsigned (ew E (32 + j)) = z).
{ intros j z Hj Hz Hz64. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra regs2 _ j), Hz. apply unsigned_lit_small. exact Hz64. }
assert (E9 : bv_unsigned (ew E 9) = AF) by (apply (UV 9%nat 9%bv); [lia | reflexivity | exact R9 | lia]).
assert (E10 : bv_unsigned (ew E 10) = F) by (apply (UV 10%nat 10%bv); [lia | reflexivity | exact R10 | lia]).
assert (E20 : bv_unsigned (ew E 20) = q) by (apply (UV 20%nat 20%bv); [lia | reflexivity | exact R20 | lia]).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (apply (UV 23%nat 23%bv); [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia]).
assert (E32 : bv_unsigned (ew E 32) = SF) by (apply (UX 0%nat); [lia | reflexivity | unfold SHADOW_OFF; lia]).
assert (E33 : bv_unsigned (ew E 33) = p) by (apply (UX 1%nat); [lia | reflexivity | lia]).
assert (E34 : bv_unsigned (ew E 34) = text + len) by (apply (UX 2%nat); [lia | reflexivity | lia]).
assert (E35 : bv_unsigned (ew E 35) = SHADOW_OFF + q / 8) by (apply (UX 3%nat); [lia | reflexivity | unfold SHADOW_OFF; lia]).
assert (Zq0 : aview SEGS (w_H W) mem2 (SHADOW_OFF + q / 8) = Some 0)
  by (apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W mem2 md2 q HAR2); lia).
assert (Zq1 : aview SEGS (w_H W) mem2 (SHADOW_OFF + q / 8 + 1) = Some 0).
{ replace (SHADOW_OFF + q / 8 + 1) with (SHADOW_OFF + (q + 1 * 8) / 8) by (rewrite Z.div_add by lia; lia).
  apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W mem2 md2 (q + 1 * 8) HAR2); lia. }
assert (HS : st_ok_pi SEGS VAL E ss_vrd_31
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + vrd_R31)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_vrd_31. apply pa_entry_st_ok_full.
  - subst E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold vrd_r31_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 33 0) p);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. apply TR; [lia | cbn; lia | exact Ip].
      * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 34 0) (text + len));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        apply TR; [lia | cbn; lia | exact Iend].
    + rewrite E10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hfp. lia.
    + rewrite E32. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (SF + o) with (shadow_addr F + o) by (unfold shadow_addr; lia). exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite E9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr2 & _).
      apply Hpr2. lia.
    + rewrite E35. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. apply vrd_val_mem1. exact Zq0.
      * apply (chunk_ok_val SEGS E _ _ 1 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        apply vrd_val_mem1. exact Zq1.
  - apply pairwise_disjoint_of_extents. unfold vrd_r31_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E10, E20, E32, E35.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    unfold alloc_ceiling, ASAN_CEIL, SHADOW_OFF, kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *.
    destruct HFapp as (HFa0 & [HFa1 | (HFa1 & HFa2)]);
    repeat match goal with |- _ /\ _ => split end; lia.
  - split; [|split; [exact I|]].
    + cbn [vrd_r31_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E10, E20, E23, E32, E35.
      change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 2) with 4. change (2 ^ 0) with 1.
      rewrite !Z.mod_1_r.
      assert (HSF4 : SF mod 4 = 0)
        by (replace SF with ((536862720 + F / 32) * 4) by (unfold SHADOW_OFF; lia); apply Z_mod_mult).
      unfold alloc_ceiling, ASAN_CEIL, SHADOW_OFF in *.
      repeat match goal with |- _ /\ _ => split end;
        try exact HAal; try exact HFal; try exact Iq8; try exact HSF4; try exact I; try lia.
    + cbn [vrd_r31_facts f_alias alias_ok].
      split.
      { apply U_inj. rewrite U_SOff, E32, Z.add_0_r, (zcanon_id SF) by (unfold M64, SHADOW_OFF in *; lia).
        rewrite vrd_U_shadow by (rewrite ?E10, ?E23, ?Z.add_0_r; unfold SHADOW_OFF in *; lia).
        rewrite E10, E23, Z.add_0_r. reflexivity. }
      split.
      { apply U_inj. rewrite U_SOff, E35, Z.add_0_r, (zcanon_id (SHADOW_OFF + q / 8)) by (unfold M64, SHADOW_OFF in *; lia).
        rewrite vrd_U_shadow by (rewrite ?E20, ?E23, ?Z.add_0_r; unfold SHADOW_OFF in *; lia).
        rewrite E20, E23, Z.add_0_r. reflexivity. }
      split.
      { apply U_inj. rewrite U_SOff, E35, (zcanon_id (SHADOW_OFF + q / 8 + 1)) by (unfold M64, SHADOW_OFF in *; lia).
        rewrite vrd_U_shadow by (rewrite ?E20, ?E23; pose proof (Z.div_pos (q + 8) 8 ltac:(lia) ltac:(lia));
                                 pose proof (Z.div_le_upper_bound (q + 8) 8 (q + 8) ltac:(lia) ltac:(lia));
                                 unfold SHADOW_OFF in *; lia).
        rewrite E20, E23. replace (q + 8) with (q + 1 * 8) by lia. rewrite Z.div_add by lia. lia. }
      exact (A_alias_hints_ok E HEI). }
assert (SHOK : sh_ok SEGS vrd_Bx2 [] E (rdW W mem2)) by apply Forall_nil.
(* the write premise and the frame of every run from a state of this shape *)
assert (AWR : forall c1 c2 c3 c4 c5, awr_ok E
   [YP09.mkRegion (Some 20%nat) 0 24 0 0 c1; YP09.mkRegion (Some 10%nat) 0 64 0 24 c2;
    YP09.mkRegion (Some 32%nat) 0 8 0 8 c3; YP09.mkRegion (Some 9%nat) 48 56 48 56 c4;
    YP09.mkRegion (Some 35%nat) 0 2 0 0 c5]
   (STK_parse_value d + e) (spZ regs + e) (rd_fp q v) (ablocks B ly S) (ablocks B ly S2) ly [(0, pos)]).
{ intros c1 c2 c3 c4 c5.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F); [reflexivity | exact E10 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros z Hzr. right; right; right. exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite HFB. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat SF); [reflexivity | exact E32 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros z Hzr. right; right; right. exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite HFB. change (64 / 8) with 8. lia. }
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (AF - (spZ regs + e)));
    [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (FRM : forall c1 c2 c3 c4 c5 (m m' : word -> option byte), frame_of E
   [YP09.mkRegion (Some 20%nat) 0 24 0 0 c1; YP09.mkRegion (Some 10%nat) 0 64 0 24 c2;
    YP09.mkRegion (Some 32%nat) 0 8 0 8 c3; YP09.mkRegion (Some 9%nat) 48 56 48 56 c4;
    YP09.mkRegion (Some 35%nat) 0 2 0 0 c5] m m' ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) -> ~ (SF <= a < SF + 8) ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
{ intros c1 c2 c3 c4 c5 m m' Hf a Ha H1 H2 H3. apply Hf.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  intros (r & Hin & Hr). cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E9, ?E10, ?E20, ?E32, ?E35 in Hr; lia |]).
  destruct Hin. }
paj_run_tok_x_inv RUNI HS HJ SHOK HPM vrd_Bspan2.
{ unfold ss_vrd_31, vrd_r31_regions. cbn [ss_mem]. apply AWR. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) ->
  ~ (SF <= a < SF + 8) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha H1 H2 H3. apply aview_eq_of. unfold ss_vrd_31, vrd_r31_regions in HFr. cbn [ss_mem] in HFr.
  exact (FRM _ _ _ _ _ _ _ HFr a Ha H1 H2 H3). }
clear HF HFr HG.
(* the register facts of the fresh environment *)
assert (EVn : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ n r Hr)).
assert (EXn : forall j, (j < 4)%nat ->
  ew E (32 + j) = nth j [w64 SF; w64 p; w64 (text + len); w64 (SHADOW_OFF + q / 8)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ j)).
assert (VR102 : vrd_R102 = 19136) by (vm_compute; reflexivity).
assert (VR83 : vrd_R83 = 19060) by (vm_compute; reflexivity).
assert (X32 : ew E 32 = w64 SF) by exact (EXn 0%nat ltac:(lia)).
assert (X33 : ew E 33 = w64 p) by exact (EXn 1%nat ltac:(lia)).
assert (X34 : ew E 34 = w64 (text + len)) by exact (EXn 2%nat ltac:(lia)).
assert (X35 : ew E 35 = w64 (SHADOW_OFF + q / 8)) by exact (EXn 3%nat ltac:(lia)).
assert (FAPP : F + 64 <= SHADOW_OFF \/ 17594333495296 <= F)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; destruct HFapp as (_ & [? | (? & ?)]); lia).
assert (HSIG : SIGMA AS_parse_value = BASE + 18736) by (vm_compute; reflexivity).
(* ---- at row 77: bgeu a1, a2, the cursor against in->end ---- *)
psrr_branch_tok RUNI BR HS SHOK vrd_Bspan2.
all: cbn [sv_denot] in Hc; rewrite ?E33, ?E34, ?Z.add_0_r in Hc; rewrite vrd_geu in Hc by lia.
- assert (Hpe : p = text + len) by (apply negb_true_iff, Z.ltb_ge in Hc; lia).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM vrd_Bspan2 vrd_R102.
  { lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply AWR. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) ->
    ~ (SF <= a < SF + 8) -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha H1 H2 H3. rewrite <- (KA a Ha H1 H2 H3). apply aview_eq_of.
    lazymatch type of HFr with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
    exact (FRM _ _ _ _ _ _ _ HFr a Ha H1 H2 H3). }
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let rq := eval vm_compute in (nth 0 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    let rf := eval vm_compute in (nth 1 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    let rs := eval vm_compute in (nth 2 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (vrd_val_of_st_ok E (abs_ss VAL ss) ms0 (w_H W) rq 0 HS ltac:(vm_compute; reflexivity)) as HVQ;
    pose proof (vrd_val_of_st_ok E (abs_ss VAL ss) ms0 (w_H W) rf 1 HS ltac:(vm_compute; reflexivity)) as HVF;
    pose proof (vrd_aview_chunk_byte E (abs_ss VAL ss) ms0 (w_H W) rs 2 HS ltac:(vm_compute; reflexivity)) as HVS
  end.
  cbn [base_val YP09.r_base] in HVQ, HVF, HVS. rewrite E20 in HVQ. rewrite E10 in HVF. rewrite E32 in HVS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  pmkst HS. rewrite <- VR102.
  vrd_retP HPM. left. split; [exact Hpe|].
  split; [reflexivity|]. do 4 eexists. split; [reflexivity|]. split; [exact HJ|].
  split; [intros a Ha H1 H2 H3 H4; exact (KB a Ha H1 H2 H3)|].
  split.
  { unfold vrd_frame. cbv zeta. split; [|split; [|split]].
    - rewrite <- (Z.add_0_r (frame_addr ly 0 pos)) at 1.
      apply (HVF 0 (SLit 1102416563)); [vm_compute; repeat (first [left; reflexivity | right]) | reflexivity | lia].
    - apply (HVF 16 (SOff 240 18736)); [vm_compute; repeat (first [left; reflexivity | right]) | |].
      + rewrite HSIG. exact (codeptr_val E 18736 HEI).
      + rewrite HSIG. pose proof (@pa_B_ok _ A_prog_listing PI_prog_A). lia.
    - apply (vrd_val_mem_keep W mem2 (ms_mem ms0)); [intros k0 Hk0; apply KB; unfold SHADOW_OFF in *; lia|].
      replace (frame_addr ly 0 pos + 56) with (frame_addr ly 0 pos + 64 - 8) by lia.
      apply val_mem_of_rdword. exact Hflag.
    - intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc8 by lia.
      destruct Hc8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ rewrite (HVS 0 18446744073709551601) | rewrite (HVS 1 18446744073709551601)
      | rewrite (HVS 2 18446744073709551601) | rewrite (HVS 3 18446744073709551601)
      | rewrite (HVS 4 18446744073709551608) | rewrite (HVS 5 18446744073709551603)
      | rewrite (HVS 6 18446744073709551603) | rewrite (HVS 7 18446744073709551603) ];
      solve [ vm_compute; reflexivity | vm_compute; repeat (first [left; reflexivity | right]) ]. }
  split.
  { rewrite <- (Z.add_0_r q) at 1.
    apply (HVQ 0 (SOff 33 0)); [vm_compute; repeat (first [left; reflexivity | right]) | | lia].
    cbn [sv_denot]. rewrite E33, Z.add_0_r. reflexivity. }
  split; [rewrite Q2, (EVn 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
  split; [rewrite Q9, (EVn 9%nat 9%bv ltac:(lia) eq_refl); exact R9|].
  split; [rewrite Q8, (EVn 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
  split; [rewrite Q18, (EVn 10%nat 10%bv ltac:(lia) eq_refl); exact R10|].
  split; [rewrite Q26, (EVn 10%nat 10%bv ltac:(lia) eq_refl); exact R10|].
  split; [rewrite Q19, (EVn 19%nat 19%bv ltac:(lia) eq_refl); exact R19|].
  split; [rewrite Q20, (EVn 20%nat 20%bv ltac:(lia) eq_refl); exact R20|].
  split; [rewrite Q21, (EVn 21%nat 21%bv ltac:(lia) eq_refl); exact R21|].
  split; [rewrite Q22, (EVn 22%nat 22%bv ltac:(lia) eq_refl); exact R22|].
  split; [rewrite Q25, (EVn 25%nat 25%bv ltac:(lia) eq_refl); exact R25|].
  split; [rewrite Q3, (EVn 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
  split; [rewrite Q4, (EVn 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
  split; [rewrite Q23, (EVn 23%nat 23%bv ltac:(lia) eq_refl); exact R23|].
  split; [rewrite Q24; exact X32|].
  split; [rewrite Q27; exact X35|].
  split; [rewrite Q12; exact X34|].
  exact I.
- assert (Hpe : p < text + len) by (apply negb_false_iff, Z.ltb_lt in Hc; lia).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM vrd_Bspan2 vrd_R83.
  { lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    apply AWR. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) ->
    ~ (SF <= a < SF + 8) -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha H1 H2 H3. rewrite <- (KA a Ha H1 H2 H3). apply aview_eq_of.
    lazymatch type of HFr with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
    exact (FRM _ _ _ _ _ _ _ HFr a Ha H1 H2 H3). }
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let rq := eval vm_compute in (nth 0 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    let rf := eval vm_compute in (nth 1 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    let rs := eval vm_compute in (nth 2 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (vrd_val_of_st_ok E (abs_ss VAL ss) ms0 (w_H W) rq 0 HS ltac:(vm_compute; reflexivity)) as HVQ;
    pose proof (vrd_val_of_st_ok E (abs_ss VAL ss) ms0 (w_H W) rf 1 HS ltac:(vm_compute; reflexivity)) as HVF;
    pose proof (vrd_aview_chunk_byte E (abs_ss VAL ss) ms0 (w_H W) rs 2 HS ltac:(vm_compute; reflexivity)) as HVS
  end.
  cbn [base_val YP09.r_base] in HVQ, HVF, HVS. rewrite E20 in HVQ. rewrite E10 in HVF. rewrite E32 in HVS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
  pmkst HS. rewrite <- VR83.
  vrd_retP HPM. right. split; [exact Hpe|].
  split; [reflexivity|]. do 4 eexists. split; [reflexivity|]. split; [exact HJ|].
  split; [intros a Ha H1 H2 H3 H4; exact (KB a Ha H1 H2 H3)|].
  split.
  { unfold vrd_frame. cbv zeta. split; [|split; [|split]].
    - rewrite <- (Z.add_0_r (frame_addr ly 0 pos)) at 1.
      apply (HVF 0 (SLit 1102416563)); [vm_compute; repeat (first [left; reflexivity | right]) | reflexivity | lia].
    - apply (HVF 16 (SOff 240 18736)); [vm_compute; repeat (first [left; reflexivity | right]) | |].
      + rewrite HSIG. exact (codeptr_val E 18736 HEI).
      + rewrite HSIG. pose proof (@pa_B_ok _ A_prog_listing PI_prog_A). lia.
    - apply (vrd_val_mem_keep W mem2 (ms_mem ms0)); [intros k0 Hk0; apply KB; unfold SHADOW_OFF in *; lia|].
      replace (frame_addr ly 0 pos + 56) with (frame_addr ly 0 pos + 64 - 8) by lia.
      apply val_mem_of_rdword. exact Hflag.
    - intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hc8 by lia.
      destruct Hc8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ rewrite (HVS 0 18446744073709551601) | rewrite (HVS 1 18446744073709551601)
      | rewrite (HVS 2 18446744073709551601) | rewrite (HVS 3 18446744073709551601)
      | rewrite (HVS 4 18446744073709551608) | rewrite (HVS 5 18446744073709551603)
      | rewrite (HVS 6 18446744073709551603) | rewrite (HVS 7 18446744073709551603) ];
      solve [ vm_compute; reflexivity | vm_compute; repeat (first [left; reflexivity | right]) ]. }
  split.
  { rewrite <- (Z.add_0_r q) at 1.
    apply (HVQ 0 (SOff 33 0)); [vm_compute; repeat (first [left; reflexivity | right]) | | lia].
    cbn [sv_denot]. rewrite E33, Z.add_0_r. reflexivity. }
  split; [rewrite Q2, (EVn 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
  split; [rewrite Q9, (EVn 9%nat 9%bv ltac:(lia) eq_refl); exact R9|].
  split; [rewrite Q8, (EVn 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
  split; [rewrite Q18, (EVn 10%nat 10%bv ltac:(lia) eq_refl); exact R10|].
  split; [rewrite Q26, (EVn 10%nat 10%bv ltac:(lia) eq_refl); exact R10|].
  split; [rewrite Q19, (EVn 19%nat 19%bv ltac:(lia) eq_refl); exact R19|].
  split; [rewrite Q20, (EVn 20%nat 20%bv ltac:(lia) eq_refl); exact R20|].
  split; [rewrite Q21, (EVn 21%nat 21%bv ltac:(lia) eq_refl); exact R21|].
  split; [rewrite Q22, (EVn 22%nat 22%bv ltac:(lia) eq_refl); exact R22|].
  split; [rewrite Q25, (EVn 25%nat 25%bv ltac:(lia) eq_refl); exact R25|].
  split; [rewrite Q3, (EVn 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
  split; [rewrite Q4, (EVn 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
  split; [rewrite Q23, (EVn 23%nat 23%bv ltac:(lia) eq_refl); exact R23|].
  split; [rewrite Q24; exact X32|].
  split; [rewrite Q27; exact X35|].
  split; [rewrite Q12; exact X34|].
  unfold vrd_loopregs. split; [rewrite Q10; exact X33|]. split; [rewrite Q11; exact X33|].
  split; [rewrite Q13; reflexivity | rewrite Q14; reflexivity].
Qed.

(* the statement before the invariant (c773f2a0dde), byte-identical: vrd_seg2_inv at P := fun _ => True *)
Lemma vrd_seg2 : forall regs2 md2 k,
  AJp mem2 md2 k ->
  getr regs2 10 = w64 F -> getr regs2 2 = w64 AF -> getr regs2 9 = w64 AF ->
  getr regs2 8 = w64 (spZ regs) -> getr regs2 19 = w64 v -> getr regs2 20 = w64 q ->
  getr regs2 23 = w64 SHADOW_OFF -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 25 = getr regs 25 ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + vrd_R31)) mem2 (seg_rom SEGS)) md2)
    (fun W' c' => (p = text + len /\ vrd_mid vrd_R102 p (fun _ => True) W' c') \/
                  (p < text + len /\ vrd_mid vrd_R83 p (vrd_loopregs p) W' c')).
Proof.
intros regs2 md2 k HJ R10 R2 R9 R8 R19 R20 R23 R3 R4 R21 R22 R25.
exact (vrd_srr_drop _ _ _ (fun _ => True) (vrd_seg2_inv (fun _ => True) vrd_true_laws regs2 md2 k HJ R10 R2 R9 R8
  R19 R20 R23 R3 R4 R21 R22 R25 I)).
Qed.

(* ---- the text: where it lives, and that no store of the segment reaches it ---- *)
Variables (Lam : list (Z * Z)) (peak cnt fail ran most own : Z).
Hypothesis HLED : prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own.
Hypothesis HHOME : prhReader_home B ly S Hp Lam text len.
Hypothesis HSRC : src_rd W mem text tb.

Lemma vrd_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PI_prog_A a Hr)].
Qed.

(* a text byte lies in a live allocator block of the entry state (a harness block's or another), or in an image
   byte that is neither runtime-owned nor errno *)
Lemma vrd_text_where : forall i, 0 <= i < len ->
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= text + i < b + req_size m) \/
  (in_img SEGS (text + i) /\ ~ Exists (in_zr (text + i)) (as_owned_static B) /\
   ~ (as_errno B <= text + i < as_errno B + 4)).
Proof.
intros i Hi. pose proof cf_head_nonneg as Hch.
destruct HHOME as [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] | (b & m & Hin & Hnhp & Hb & Hm)].
- left. pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ b m _ _ HLED Hin)
    as (Hm0 & Hab & _). cbn [fst snd] in *.
  exists (b - cf_head), (m + cf_head). split; [exact Hab|].
  assert (Hmc : 0 <= m + cf_head) by lia. pose proof (req_size_pos (m + cf_head) Hmc). lia.
- right. destruct (Hro (text + i) ltac:(lia)) as (Hr & Hno & Her).
  split; [exact (vrd_ro_img _ Hr) | split; [exact Hno | exact Her]].
- right. destruct (Hro (text + i) ltac:(lia)) as (Hr & Hno & Her & _).
  split; [exact (vrd_ro_img _ Hr) | split; [exact Hno | exact Her]].
- left. exists b, m. split; [exact Hin|]. pose proof (req_size_pos m ltac:(lia)). lia.
Qed.

(* the text after the frame call is the text at entry *)
Lemma vrd_text_kept2 : forall i, 0 <= i < len ->
  aview SEGS (w_H W) mem2 (text + i) = aview SEGS (w_H W) mem (text + i).
Proof.
intros i Hi.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HSRC as (_ & Ht4096 & Htc & _).
pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ilen & _).
pose proof HKept as (K1 & K2 & K3 & _).
pose proof (vrd_stk_big d) as HSTK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_in_facts _ _ _ _ _ _ _ HIN) as (_ & _ & _ & _ & _ & Ilen' & _).
assert (T1 : 0 <= text + i < 2 ^ 64) by lia.
assert (T2 : ~ (spZ regs - 192 <= text + i < spZ regs)) by lia.
rewrite <- (KEEP1 (text + i) T1 T2).
destruct (vrd_text_where i Hi) as [(b & m & Hin & Hbm) | (Himg & Hno & Her)].
- replace (text + i) with (b + (text + i - b)) by lia. apply (K2 b m); [exact Hin | lia | intros []].
- exact (K3 _ Himg Hno Her).
Qed.

(* the text is application memory: a live block (in_app) or an image byte (below the low shadow) *)
Lemma vrd_text_app : forall i, 0 <= i < len ->
  text + i < kLowMemEnd \/ (kHighMemBeg <= text + i /\ text + i < ASAN_CEIL).
Proof.
intros i Hi. pose proof HPRE as (HAR & _).
destruct (vrd_text_where i Hi) as [(b & m & Hin & Hbm) | (Himg & _ & _)].
- destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & _ & Happ & _).
  unfold in_app, kLowShadowBeg, kLowMemEnd in *. lia.
- pose proof (@pa_segs_low _ _ PI_prog_A _ Himg) as Hl. lia.
Qed.

(* no text byte is in the class-0 frame this call took, nor in that frame's shadow *)
Lemma vrd_text_off : forall m mdx, ARx ly S2 Hp W m mdx -> forall i, 0 <= i < len ->
  ~ (F <= text + i < F + 64) /\ ~ (SF <= text + i < SF + 8).
Proof.
intros m mdx HAR2 i Hi.
assert (HinF : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (frames_bounds_x SEGS B ARx LAWS ly S2 Hp W m mdx 0 pos HAR2 HinF) as (HF4096 & HFceil & HFapp).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity. rewrite HFB in HFceil, HFapp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_text_app i Hi) as Happ.
pose proof (Z.div_le_upper_bound F 8 F ltac:(lia) ltac:(lia)) as HF8.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF0.
split.
- destruct (vrd_text_where i Hi) as [(b & k & Hin & Hbk) | (Himg & _ & _)].
  + rewrite <- Eab in Hin. pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 Hp W m mdx b k 0 pos HAR2 Hin HinF) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd. lia.
  + intros Hr. destruct (alx_client_img SEGS B ARx LAWS ly S2 Hp W m mdx (text + i) HAR2
      ltac:(right; left; exists 0, pos; split; [exact HinF | rewrite HFB; lia])) as [_ Hni].
    exact (Hni Himg).
- assert (HF8u : F / 8 < 2 ^ 44 - 8) by (apply Z.div_lt_upper_bound; lia).
  unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling, SHADOW_OFF in *. lia.
Qed.


(* a range inside a registered zero-shadow global is addressable in any state *)
Lemma vrd_zs_addr : forall ly' S' Hp' m mdx a n, ARx ly' S' Hp' W m mdx -> in_zs B a n ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n.
Proof.
intros ly' S' Hp' m mdx a n HA (q' & m' & Hin & Hq & Hqm).
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ SYMS) (q', m') Hin) as (Z1 & Z2 & Z3 & Z4 & Z5).
cbn [fst snd] in *.
pose proof (alx_zshadow SEGS B ARx LAWS ly' S' Hp' W m mdx (q', m') HA ltac:(unfold zero_shadow_ranges; right; exact Hin))
  as Hz. cbn [fst snd] in Hz.
apply (range_addressable_sub _ SHADOW_OFF q' m' a n); [exact (zero_shadow_range _ SHADOW_OFF q' m' Z3 Z4 Hz) | lia | lia].
Qed.

(* the text is addressable in every state of the walk after the call (the shadow is re-derived from the laws:
   the frame call's contract keeps no shadow byte it does not own) *)
Lemma vrd_text_addr : forall m mdx, ARx ly S2 Hp W m mdx ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF text len.
Proof.
intros m mdx HAR2. pose proof cf_head_nonneg as Hch.
pose proof (vrd_in_facts _ _ _ _ _ _ _ HIN) as (_ & _ & _ & _ & _ & Ilen & _).
destruct HHOME as [[(b & k & Hin & Hb & Hk) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] | (b & k & Hin & Hnhp & Hb & Hk)].
- pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ b k _ _ HLED Hin)
    as (Hk0 & Hab & Hhp & _). cbn [fst snd] in *.
  rewrite <- Eab in Hab.
  destruct (Z.eq_dec len 0) as [H0|H0]; [apply range_addressable_nil; lia|].
  pose proof (alx_hshadow SEGS B ARx LAWS ly S2 Hp W m mdx (b - cf_head) (k + cf_head) HAR2 Hab Hhp) as [Hbs _].
  rewrite HLc in Hbs. unfold req_size in Hbs. destruct (Z.eqb_spec (k + cf_head) 0) as [Hz0|Hz0]; [lia|].
  replace (b - cf_head + cf_head) with b in Hbs by lia. replace (k + cf_head - cf_head) with k in Hbs by lia.
  eapply block_shadow_range; [exact Hbs | lia | lia].
- exact (vrd_zs_addr ly S2 Hp m mdx text len HAR2 Hzs).
- intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzg | (vv & Hcell & Hv)]).
  + pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    destruct (vrd_zs_addr ly S2 Hp m mdx (x - x mod 8) 8 HAR2 Hzg x ltac:(lia)) as (s & Hs & Hok).
    exists s. split; [exact Hs | exact Hok].
  + exists vv. split; [| unfold saddr_ok; lia].
    pose proof (alx_const_cells SEGS B ARx LAWS ly S2 Hp W m mdx HAR2) as HC.
    pose proof (proj1 (Forall_forall _ _) HC _ (Hcell ly)) as Hh.
    unfold cell_holds, z1, c1 in Hh. cbn [c_at c_w c_val aeval] in Hh. specialize (Hh 0%nat ltac:(lia)).
    rewrite Z.add_0_r in Hh. unfold shadow_of_addr. unfold shadow_addr in Hh. rewrite Hh. f_equal.
    unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    change (2 ^ 8) with 256.
    assert (Hv8 : 0 <= vv < 256) by (pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
    rewrite (Z.mod_small vv 256 Hv8). exact (Z.mod_small vv 256 Hv8).
- destruct (Z.eq_dec len 0) as [H0|H0]; [apply range_addressable_nil; lia|].
  rewrite <- Eab in Hin.
  assert (Hnh : forall h, In h Hp -> ~ (b <= h < b + req_size k)).
  { intros h Hh Hr. destruct (vrd_ledger_hp _ _ _ _ _ _ _ _ _ _ _ _ h HLED Hh) as (k' & Hin').
    set (a' := h + cf_head) in Hin'. assert (Eh : h = a' - cf_head) by (unfold a'; lia). clearbody a'. subst h.
    pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ a' k' _ _ HLED Hin')
      as (Hk0' & Hab' & _). cbn [fst snd] in *.
    rewrite <- Eab in Hab'.
    destruct (Z.eq_dec (a' - cf_head) b) as [Eb|Nb]; [rewrite Eb in Hh; exact (Hnhp Hh)|].
    assert (Hne : (b, k) <> (a' - cf_head, k' + cf_head)) by (intros E; injection E as E1 _; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S2 Hp W m mdx _ _ _ _ HAR2 Hin Hab' Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. assert (Hkc : 0 <= k' + cf_head) by lia.
    pose proof (req_size_pos (k' + cf_head) Hkc). lia. }
  destruct (alx_shadow SEGS B ARx LAWS ly S2 Hp W m mdx b k HAR2 Hin Hnh) as [Hbs _].
  assert (Hk0 : 0 <= k) by lia. pose proof (req_size_pos k Hk0).
  eapply block_shadow_range; [exact Hbs | lia | lia].
Qed.

(* ---- the white-space loop: the invariant at the loop head and the exit at row 102 ---- *)
Definition vrd_lpP (pcur : Z) : world SEGS -> config -> Prop := fun W' c' =>
  p <= pcur < text + len /\ PjGrammar.skip (rest_atR tb text p) = PjGrammar.skip (rest_atR tb text pcur) /\
  vrd_mid vrd_R83 pcur (vrd_loopregs pcur) W' c'.
Definition vrd_exQ : world SEGS -> config -> Prop := fun W' c' =>
  exists p', p <= p' <= text + len /\ rest_atR tb text p' = PjGrammar.skip (rest_atR tb text p) /\
  vrd_mid vrd_R102 p' (fun _ => True) W' c'.

(* a store into the cursor's p word keeps every other fact of the mid state *)
Lemma vrd_keep_q : forall memc memn, 0 <= F -> F + 64 <= q -> SF + 8 <= q -> q + 8 <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) -> ~ (SF <= a < SF + 8) ->
     ~ (q <= a < q + 8) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem2 a) ->
  vrd_frame W memc ly pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) -> aview SEGS (w_H W) memn a = aview SEGS (w_H W) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) -> ~ (SF <= a < SF + 8) ->
     ~ (q <= a < q + 8) -> aview SEGS (w_H W) memn a = aview SEGS (w_H W) mem2 a) /\
  vrd_frame W memn ly pos.
Proof.
intros memc memn HF0 HFq HSq Hq64 Kc Fr Kn.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8.
split.
- intros a Ha H1 H2 H3 H4. rewrite (Kn a Ha H4). exact (Kc a Ha H1 H2 H3 H4).
- unfold vrd_frame in *. cbv zeta in *. destruct Fr as (F1 & F2 & F3 & F4).
  split; [|split; [|split]].
  + apply (vrd_val_mem_keep W memc memn); [intros k0 Hk0; apply Kn; lia | exact F1].
  + apply (vrd_val_mem_keep W memc memn); [intros k0 Hk0; apply Kn; lia | exact F2].
  + apply (vrd_val_mem_keep W memc memn); [intros k0 Hk0; apply Kn; lia | exact F3].
  + intros i Hi. rewrite (Kn (SHADOW_OFF + F / 8 + i)); [exact (F4 i Hi) | unfold SHADOW_OFF in *; lia | lia].
Qed.

Lemma vrd_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_LTU (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold branch_taken, bv_ltu. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma vrd_ne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y).
Proof. intros x y Hx Hy. unfold branch_taken. rewrite bv_eqb_unsigned, !unsigned_lit_small by lia. reflexivity. Qed.

(* row 91's test, rows 89..91 (srl / andi / beqz) over the mask a4 = vrd_ws_mask: taken exactly when the byte is no
   white space (vrd_mask_ws's fact, by computation over the 33 bytes the loop gets here with) *)
Lemma vrd_ws_bit : forall b, 0 <= b <= 32 ->
  branch_taken BC_EQ (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 4294977024) (Z_to_bv 64 b)) (Z_to_bv 64 1))
    (Z_to_bv 64 0) = negb (PjGrammar.ws b).
Proof.
intros b Hb. rewrite <- (Z2Nat.id b) by lia. assert (Hk : (Z.to_nat b < 33)%nat) by lia.
generalize (Z.to_nat b) Hk. clear b Hb Hk. intros k Hk.
do 33 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(* the loop proof's bookkeeping, one tactic each: the bytes off the cursor word after a run (KM), a run's write
   premise, the cursor word at the end of a run, the registers the mid state names, and the mid state itself *)
Ltac vrd_km FRL E20 KM memc :=
  lazymatch goal with HFr : frame_of ?E' ?rs (mrestrict _ ?m) (mrestrict _ ?m') |- _ =>
    let rs' := eval vm_compute in rs in change rs with rs' in HFr;
    let KM2 := fresh "KM" in
    assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
              aview SEGS (w_H W) m' a = aview SEGS (w_H W) memc a)
      by (intros za zHa zH1; rewrite (FRL E' _ _ _ m m' HFr ltac:(exact E20) za zHa zH1); exact (KM za zHa zH1));
    clear KM HFr; rename KM2 into KM
  end.
Ltac vrd_awr AWRL E20 :=
  lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  apply AWRL; exact E20.
Ltac vrd_hq HS pnew ev HQn Eat E20 :=
  lazymatch type of HS with st_ok_pi _ _ ?EF ?ss _ =>
    let rq := eval vm_compute in (nth 0 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (vrd_val_of_st_ok EF (abs_ss VAL ss) _ (w_H W) rq 0 HS ltac:(vm_compute; reflexivity) 0 ev pnew
       ltac:(vm_compute; repeat (first [left; reflexivity | right]))
       ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Eat; rewrite ?Z.add_0_r; reflexivity)
       ltac:(lia)) as HQn;
    replace (base_val EF (YP09.r_base rq) + 0) with q in HQn
      by (cbn [base_val YP09.r_base ew ewset Nat.eqb]; rewrite E20; lia)
  end.
Ltac vrd_prregs HS :=
  let f r := let Q := fresh "Q" in prreg HS r Q in
  f (2%bv : bv 5); f (3%bv : bv 5); f (4%bv : bv 5); f (8%bv : bv 5); f (9%bv : bv 5); f (12%bv : bv 5);
  f (18%bv : bv 5); f (19%bv : bv 5); f (20%bv : bv 5); f (21%bv : bv 5); f (22%bv : bv 5); f (23%bv : bv 5);
  f (24%bv : bv 5); f (25%bv : bv 5); f (26%bv : bv 5); f (27%bv : bv 5).
Ltac vrd_reg_goal EVn :=
  match goal with
  | Q : getr ?rs ?r = ew ?E ?n, R : getr ?rc ?r = ?x |- getr ?rs ?r = ?x =>
      rewrite Q, (EVn n r ltac:(lia) eq_refl); exact R
  end.
Ltac vrd_mid_close HQn HJ KM Kc Fr HF0 HFq HSq Hq64 memc EVn :=
  split; [reflexivity|]; do 4 eexists; split; [reflexivity|]; split; [exact HJ|];
  split; [intros za zHa zH1 zH2 zH3 zH4; rewrite (KM za zHa zH4); exact (Kc za zHa zH1 zH2 zH3 zH4)|];
  split; [exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr KM))|];
  split; [exact HQn|];
  do 16 (split; [vrd_reg_goal EVn|]).

Lemma vrd_loop_step_inv : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall pcur W' c', vrd_lpP pcur W' c' -> P (ms_mem (cfg_ms c')) ->
  SRr SEGS W' c' (fun W2 c2 => (vrd_exQ W2 c2 \/
    exists pc', (0 <= text + len - pc' < text + len - pcur) /\ vrd_lpP pc' W2 c2) /\ P (ms_mem (cfg_ms c2))).
Proof.
intros P PLAW pcur W' c' (Hpc & Hsk & -> & regsc & memc & mdc & k & -> & HJ & Kc & Fr & HQc & R2 & R9 & R8 & R18 & R26 &
  R19 & R20 & R21 & R22 & R25 & R3 & R4 & R23 & R24 & R27 & R12 & R10 & R11 & R13 & R14) HPM.
cbn [cfg_ms ms_mem] in HPM.
pose proof (paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW) as RUNI.
pose proof (paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW) as RUNTOI.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big d) as HSTK.
pose proof (vrd_in_facts _ _ _ _ _ _ _ HIN) as (Iq8 & It0 & It62 & Itp1 & Itp2 & Ilen & Iqt).
pose proof HSRC as (Hgarr & Ht4096 & Htc & _).
pose proof (proj1 HJ) as HAR2. cbv beta in HAR2.
assert (HinF : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (frames_bounds_x SEGS B ARx LAWS ly S2 Hp W memc mdc 0 pos HAR2 HinF) as (HF4096 & HFceil & HFapp).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity. rewrite HFB in HFceil, HFapp.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8a.
pose proof (Z.div_le_upper_bound F 8 F ltac:(lia) ltac:(lia)) as HF8b.
pose proof (vrd_A_bounds (spZ regs) Hal16 ltac:(lia)) as (HAb1 & HAb2 & HAal).
pose proof (Z.div_mod q 8 ltac:(lia)) as DQ. rewrite Iq8, Z.add_0_r in DQ.
(* the text byte at the cursor *)
set (i := pcur - text).
assert (Hi : 0 <= i < len) by (subst i; lia).
destruct (Hgarr (Z.to_nat i) ltac:(lia)) as (Hb1 & Hb256).
set (b := nth (Z.to_nat i) tb 0) in *.
replace (text + Z.of_nat (Z.to_nat i)) with pcur in Hb1 by (subst i; lia).
destruct (vrd_text_off memc mdc HAR2 i Hi) as [O1 O2].
assert (Kt : aview SEGS (w_H W) memc pcur = aview SEGS (w_H W) mem pcur).
{ replace pcur with (text + i) by (subst i; lia).
  rewrite (Kc (text + i)); [exact (vrd_text_kept2 i Hi) | lia | lia | lia | lia | destruct Iqt; lia]. }
assert (TB1 : val_mem SEGS (rdW W memc) pcur 1 b).
{ apply (vrd_val_mem_keep W mem memc); [|exact Hb1].
  intros k0 Hk0. replace k0 with 0%nat by lia. rewrite Z.add_0_r. exact Kt. }
pose proof (vrd_text_app i Hi) as Happ.
(* the fresh state at the loop head *)
remember (@Eimg _ A_prog_listing PI_prog_A (Ereg regsc [w64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EVn : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ n r Hr)).
assert (X32 : ew E 32 = w64 b)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (UV : forall n (r : bv 5) z, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> getr regsc r = w64 z ->
  0 <= z < 2 ^ 64 -> bv_unsigned (ew E n) = z)
  by (intros n r z Hn Hr Hz Hz64; rewrite (EVn n r Hn Hr), Hz; apply unsigned_lit_small; exact Hz64).
assert (E10 : bv_unsigned (ew E 10) = pcur) by (apply (UV 10%nat 10%bv); [lia | reflexivity | exact R10 | lia]).
assert (E11 : bv_unsigned (ew E 11) = pcur) by (apply (UV 11%nat 11%bv); [lia | reflexivity | exact R11 | lia]).
assert (E12 : bv_unsigned (ew E 12) = text + len) by (apply (UV 12%nat 12%bv); [lia | reflexivity | exact R12 | lia]).
assert (E20 : bv_unsigned (ew E 20) = q) by (apply (UV 20%nat 20%bv); [lia | reflexivity | exact R20 | lia]).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (apply (UV 23%nat 23%bv); [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia]).
assert (E27 : bv_unsigned (ew E 27) = SHADOW_OFF + q / 8)
  by (apply (UV 27%nat 27%bv); [lia | reflexivity | exact R27 | unfold SHADOW_OFF; lia]).
assert (E32 : bv_unsigned (ew E 32) = b) by (rewrite X32; apply unsigned_lit_small; lia).
assert (Zq0 : aview SEGS (w_H W) memc (SHADOW_OFF + q / 8) = Some 0)
  by (apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W memc mdc q HAR2); lia).
assert (HS0 : st_ok_pi SEGS VAL E (mkSS vrd_R83 sr_atoms vrd_lp_regions None vrd_lp_facts)
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + vrd_R83)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold vrd_lp_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E20. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS).
        pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr2 & _). apply Hpr2. lia. }
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 10 0) pcur);
        [cbn [sv_denot]; rewrite E10, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact HQc.
    + rewrite E11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ pcur 0 1 (SOff 32 0) b);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact TB1.
    + rewrite E27. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply vrd_val_mem1. exact Zq0.
  - apply pairwise_disjoint_of_extents. unfold vrd_lp_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E20, E11, E27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; lia.
  - split; [|split; [exact I | exact I]].
    cbn [vrd_lp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E10, E11, E12, E20, E23, E27, E32.
    change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    unfold alloc_ceiling, ASAN_CEIL, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; try exact Iq8; try exact I; try lia. }
assert (HS : st_ok_pi SEGS VAL E ss_vrd_lp
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + vrd_R83)) memc (seg_rom SEGS)))).
{ unfold ss_vrd_lp, vrd_lp_regs.
  pose proof (st_ok_pi_pin_reg' E _ _ 13%bv 32 HS0 ltac:(cbn [restrict ms_regs mkst]; exact R13) eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' E _ _ 14%bv vrd_ws_mask H1 ltac:(cbn [restrict ms_regs mkst]; exact R14) eq_refl) as H2.
  exact H2. }
clear HS0.
assert (SHOK : sh_ok SEGS vrd_BxL vrd_SHL E (rdW W memc)).
{ apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. unfold vrd_BxL.
    rewrite !U_SOff, E23, E20, !Z.add_0_r, (zcanon_id SHADOW_OFF), (zcanon_id q) by (unfold M64, SHADOW_OFF; lia).
    replace (24 - 0) with 24 by lia.
    intros x Hx. exists 0. split; [| left; reflexivity].
    apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W memc mdc x HAR2); lia.
  - unfold app_apart. cbn [she_m she_lo she_hi]. unfold vrd_BxL.
    rewrite !U_SOff, E23, E20, !Z.add_0_r, (zcanon_id SHADOW_OFF), (zcanon_id q) by (unfold M64, SHADOW_OFF; lia).
    intros a Ha. unfold alloc_ceiling, ASAN_CEIL, SHADOW_OFF in *. lia. }
assert (AWRL : forall E' c1 c2 c3, bv_unsigned (ew E' 20) = q -> awr_ok E'
   [YP09.mkRegion (Some 20%nat) 0 24 0 8 c1; YP09.mkRegion (Some 11%nat) 0 1 0 0 c2;
    YP09.mkRegion (Some 27%nat) 0 1 0 0 c3]
   (STK_parse_value d + e) (spZ regs + e) (rd_fp q v) (ablocks B ly S) (ablocks B ly S2) ly [(0, pos)]).
{ intros E' c1 c2 c3 He.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat q); [reflexivity | exact He | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (FRL : forall E' c1 c2 c3 (m m' : word -> option byte), frame_of E'
   [YP09.mkRegion (Some 20%nat) 0 24 0 8 c1; YP09.mkRegion (Some 11%nat) 0 1 0 0 c2;
    YP09.mkRegion (Some 27%nat) 0 1 0 0 c3] (rdW W m) (rdW W m') -> bv_unsigned (ew E' 20) = q ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a).
{ intros E' c1 c2 c3 m m' Hf He a Ha H1. apply aview_eq_of. apply Hf.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  intros (r & Hin & Hr). cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?He in Hr; lia |]).
  destruct Hin. }
assert (HF0 : 0 <= F) by lia.
assert (HFq : F + 64 <= q)
  by (unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; lia).
assert (HF8u : F / 8 < 2 ^ 44)
  by (apply Z.div_lt_upper_bound; unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *;
      lia).
assert (HSq : SF + 8 <= q)
  by (unfold SHADOW_OFF, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; lia).
assert (Hq64 : q + 8 <= 2 ^ 64) by lia.
assert (VR102 : vrd_R102 = 19136) by (vm_compute; reflexivity).
assert (VR83 : vrd_R83 = 19060) by (vm_compute; reflexivity).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
paj_run_tok_x_inv RUNI HS HJ SHOK HPM vrd_Bspan.
{ unfold vrd_BxL. rewrite !U_SOff, E23, E10, !Z.add_0_r, (zcanon_id SHADOW_OFF), (zcanon_id pcur)
    by (unfold M64, SHADOW_OFF; lia).
  exact (range_addressable_sub _ SHADOW_OFF text len pcur 1 (vrd_text_addr memc mdc HAR2) ltac:(lia) ltac:(lia)). }
{ vrd_awr AWRL E20. }
vrd_km FRL E20 KM memc. clear HF HG.
(* ---- row 88: bltu a3, a5, 32 against the byte ---- *)
psrr_branch_tok RUNI BR HS SHOK vrd_Bspan.
all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E32, ?Z.add_0_r in Hc; rewrite vrd_ltu in Hc by lia.
- (* 32 < b: the byte is no white space; exit at row 102 with the cursor where it is *)
  assert (Hb32 : 32 < b) by (apply Z.ltb_lt in Hc; exact Hc). clear Hc.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM vrd_Bspan vrd_R102.
  { vrd_awr AWRL E20. }
  vrd_km FRL E20 KM memc. clear HF HG.
  vrd_hq HS pcur (SOff 10 0) HQn E10 E20.
  vrd_prregs HS. pmkst HS. rewrite <- VR102.
  vrd_retP HPM. left. exists pcur. split; [lia|]. split.
  { rewrite Hsk, (vrd_rest_cons tb text pcur) by lia. symmetry. apply vrd_skip_stop. apply vrd_gt32_not_ws.
    exact Hb32. }
  vrd_mid_close HQn HJ KM Kc Fr HF0 HFq HSq Hq64 memc EVn. exact I.
- assert (Hb32 : b <= 32) by (apply Z.ltb_ge in Hc; exact Hc). clear Hc.
  paj_run_tok_x_inv RUNI HS HJ SHOK HPM vrd_Bspan.
  { vrd_awr AWRL E20. }
  vrd_km FRL E20 KM memc. clear HF HG.
  (* ---- row 91: beqz on bit b of the white-space mask ---- *)
  psrr_branch_tok RUNI BR HS SHOK vrd_Bspan.
  all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E32, ?Z.add_0_r in Hc; rewrite vrd_ws_bit in Hc by lia.
  + (* bit b clear: the byte is no white space; exit at row 102 with the cursor where it is *)
    assert (Hws : PjGrammar.ws b = false) by (apply negb_true_iff in Hc; exact Hc). clear Hc.
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM vrd_Bspan vrd_R102.
    { vrd_awr AWRL E20. }
    vrd_km FRL E20 KM memc. clear HF HG.
    vrd_hq HS pcur (SOff 10 0) HQn E10 E20.
    vrd_prregs HS. pmkst HS. rewrite <- VR102.
    vrd_retP HPM. left. exists pcur. split; [lia|]. split.
    { rewrite Hsk, (vrd_rest_cons tb text pcur) by lia. symmetry. apply vrd_skip_stop. exact Hws. }
    vrd_mid_close HQn HJ KM Kc Fr HF0 HFq HSq Hq64 memc EVn. exact I.
  + (* bit b set: white space; rows 92..97 store p + 1 into the cursor and test it against the end *)
    assert (Hws : PjGrammar.ws b = true) by (apply negb_false_iff in Hc; exact Hc). clear Hc.
    paj_run_tok_x_inv RUNI HS HJ SHOK HPM vrd_Bspan.
    { vrd_awr AWRL E20. }
    vrd_km FRL E20 KM memc. clear HF HG.
    (* ---- row 97: bne a1, a2, p + 1 against the end ---- *)
    psrr_branch_tok RUNI BR HS SHOK vrd_Bspan.
    all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E11, ?E12, ?Z.add_0_r in Hc.
    all: rewrite vrd_ne in Hc by lia.
    * (* p + 1 is not the end: back to the loop head, one byte further *)
      assert (Hne : pcur + 1 <> text + len) by (apply negb_true_iff, Z.eqb_neq in Hc; exact Hc). clear Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM vrd_Bspan vrd_R83.
      { vrd_awr AWRL E20. }
      vrd_km FRL E20 KM memc. clear HF HG.
      vrd_hq HS (pcur + 1) (SOff 11 1) HQn E11 E20.
      vrd_prregs HS. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
      prreg HS (13%bv : bv 5) T13. prreg HS (14%bv : bv 5) T14.
      pmkst HS. rewrite <- VR83.
      vrd_retP HPM. right. exists (pcur + 1). split; [lia|]. split; [lia|]. split.
      { rewrite Hsk, (vrd_rest_cons tb text pcur) by lia. apply vrd_skip_go. exact Hws. }
      vrd_mid_close HQn HJ KM Kc Fr HF0 HFq HSq Hq64 memc EVn.
      unfold vrd_loopregs.
      split; [rewrite T10, E10; reflexivity|]. split; [rewrite T11, E11; reflexivity|].
      split; [rewrite T13; reflexivity | rewrite T14; reflexivity].
    * (* p + 1 is the end: row 98 jumps to row 102 with the cursor at the end *)
      assert (He : pcur + 1 = text + len) by (apply negb_false_iff, Z.eqb_eq in Hc; exact Hc). clear Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM vrd_Bspan vrd_R102.
      { vrd_awr AWRL E20. }
      vrd_km FRL E20 KM memc. clear HF HG.
      vrd_hq HS (pcur + 1) (SOff 11 1) HQn E11 E20.
      vrd_prregs HS. pmkst HS. rewrite <- VR102.
      vrd_retP HPM. left. exists (pcur + 1). split; [lia|]. split.
      { rewrite He, (vrd_rest_end tb text len Ilen), Hsk, (vrd_rest_cons tb text pcur) by lia.
        rewrite vrd_skip_go by exact Hws. rewrite He, (vrd_rest_end tb text len Ilen). reflexivity. }
      vrd_mid_close HQn HJ KM Kc Fr HF0 HFq HSq Hq64 memc EVn. exact I.
Qed.

(* the statement before the invariant (c773f2a0dde), byte-identical: vrd_loop_step_inv at P := fun _ => True *)
Lemma vrd_loop_step : forall pcur W' c', vrd_lpP pcur W' c' ->
  SRr SEGS W' c' (fun W2 c2 => vrd_exQ W2 c2 \/
    exists pc', (0 <= text + len - pc' < text + len - pcur) /\ vrd_lpP pc' W2 c2).
Proof.
intros pcur W' c' H.
exact (vrd_srr_drop _ _ _ (fun _ => True) (vrd_loop_step_inv (fun _ => True) vrd_true_laws pcur W' c' H I)).
Qed.

(* the white-space loop, by SRr_loopZ over the bytes left, with the invariant beside the loop head's vrd_lpP *)
Lemma vrd_loop_inv : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall pcur W' c', vrd_lpP pcur W' c' -> P (ms_mem (cfg_ms c')) ->
  SRr SEGS W' c' (fun W2 c2 => vrd_exQ W2 c2 /\ P (ms_mem (cfg_ms c2))).
Proof.
intros P PLAW pcur W' c' H HPM.
eapply SRr_loopZ with (m := fun x => text + len - x)
  (P := fun x W2 c2 => vrd_lpP x W2 c2 /\ P (ms_mem (cfg_ms c2))); [|exact (conj H HPM)].
intros x W2 c2 (HLx & HP2).
eapply SRr_bind; [exact (vrd_loop_step_inv P PLAW x W2 c2 HLx HP2)|].
intros W3 c3 _ ([HE | (pc' & Hm & HL')] & HP3); apply SRr_ret;
  [left; exact (conj HE HP3) | right; exists pc'; split; [exact Hm | exact (conj HL' HP3)]].
Qed.

(* the statement before the invariant (c773f2a0dde), byte-identical: vrd_loop_inv at P := fun _ => True *)
Lemma vrd_loop : forall pcur W' c', vrd_lpP pcur W' c' -> SRr SEGS W' c' vrd_exQ.
Proof.
intros pcur W' c' H.
exact (vrd_srr_drop _ _ _ (fun _ => True) (vrd_loop_inv (fun _ => True) vrd_true_laws pcur W' c' H I)).
Qed.

(* rows 31..101: from the frame call's return to row 102, the cursor past the white space *)
Lemma vrd_seg23_inv : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall regs2 md2 k,
  AJp mem2 md2 k ->
  getr regs2 10 = w64 F -> getr regs2 2 = w64 AF -> getr regs2 9 = w64 AF ->
  getr regs2 8 = w64 (spZ regs) -> getr regs2 19 = w64 v -> getr regs2 20 = w64 q ->
  getr regs2 23 = w64 SHADOW_OFF -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 25 = getr regs 25 ->
  P mem2 ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + vrd_R31)) mem2 (seg_rom SEGS)) md2)
    (fun W' c' => vrd_exQ W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW regs2 md2 k HJ R10 R2 R9 R8 R19 R20 R23 R3 R4 R21 R22 R25 HPM.
pose proof (vrd_in_facts _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Itp1 & Itp2 & Ilen & _).
eapply SRr_bind; [exact (vrd_seg2_inv P PLAW regs2 md2 k HJ R10 R2 R9 R8 R19 R20 R23 R3 R4 R21 R22 R25 HPM)|].
intros W' c' _ ([(Hpe & Hm) | (Hpe & Hm)] & HP2).
- apply SRr_ret. split; [|exact HP2]. exists p. split; [lia|]. split; [|exact Hm].
  rewrite Hpe, (vrd_rest_end tb text len Ilen). reflexivity.
- apply (vrd_loop_inv P PLAW p); [split; [lia|]; split; [reflexivity | exact Hm] | exact HP2].
Qed.

(* the statement before the invariant (c773f2a0dde), byte-identical: vrd_seg23_inv at P := fun _ => True *)
Lemma vrd_seg23 : forall regs2 md2 k,
  AJp mem2 md2 k ->
  getr regs2 10 = w64 F -> getr regs2 2 = w64 AF -> getr regs2 9 = w64 AF ->
  getr regs2 8 = w64 (spZ regs) -> getr regs2 19 = w64 v -> getr regs2 20 = w64 q ->
  getr regs2 23 = w64 SHADOW_OFF -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 25 = getr regs 25 ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + vrd_R31)) mem2 (seg_rom SEGS)) md2) vrd_exQ.
Proof.
intros regs2 md2 k HJ R10 R2 R9 R8 R19 R20 R23 R3 R4 R21 R22 R25.
exact (vrd_srr_drop _ _ _ (fun _ => True) (vrd_seg23_inv (fun _ => True) vrd_true_laws regs2 md2 k HJ R10 R2 R9 R8
  R19 R20 R23 R3 R4 R21 R22 R25 I)).
Qed.

(* ---- THE CLOSING into vrd_disp_a: the entry facts the dispatch state carries verbatim, the post-call facts of the
   frame call (vrd_p31), and the image facts the keeps need. Each is a positive fact the instance supplies. ---- *)
Variables (CTX0 : list (list Z)) (CW : list (list Z)).
Hypothesis HRD : rd_pre B (STK_parse_value d) ly S Hp W regs mem Lam peak cnt fail ran most own e q text len p d tb v.
Hypothesis HARO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Hypothesis HCHN : exists ch', achain ly (aview SEGS (w_H W) mem) (spZ regs) (s0Z regs) ch' /\ spine ch' = spine ch.
Hypothesis HCLO : prh_univ_closure B CTX0.
Hypothesis HCUR : prh_cur_entry W mem regs q.
(* the cursor set and the wild budget, tparse_value_specX's (the kit's cut, PRH_FnParse.v blob f0d92dcec7e9 :279, :302) *)
Hypothesis HCW : prh_cw_entry B CW W mem regs q.
Hypothesis HCUC : (spZ regs <= q < spZ regs + 16) \/
  (spZ regs + 16 <= q /\ exists ch', achain ly (aview SEGS (w_H W) mem) (spZ regs) (prh_s0 F_parse_string q) ch').
Hypothesis HROOM : rd_room S (prhPv_gtrace d (rest_atR tb text p)).
Hypothesis HWR : YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S).
(* tparse_value_specX's two live-count premises (PRH_FnParse.v blob 94232293d483), verbatim *)
Hypothesis HSEC0 : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
  (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV.
Hypothesis HL240 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
  (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Hypothesis HFRC : Z.of_nat (length (frames S)) + Z.of_nat (Nat.succ (PjGrammar.MAXD - d)) <= fs_frames 0.
Hypothesis HSF : exists f, S2 = set_fs f S.
Hypothesis HSV : vrd_saved (rdW W mem2) (spZ regs) regs.

(* a covering hull covers a sub-range; the hull of a range 64 bytes inside the image is the shadow of image bytes
   (FuzzStrdup.v's sd_hull_sub / sd_hull_img, restated over this file's imports) *)
Lemma vrd_hull_sub : forall (rd : reader) p0 m dd n, shadow_hull_vis rd p0 m -> p0 <= dd -> dd + n <= p0 + m -> 0 < n ->
  shadow_hull_vis rd dd n.
Proof.
intros rd p0 m dd n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p0 dd Hpd) as M1. pose proof (shadow_mono (dd + n - 1) (p0 + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
  by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma vrd_hull_img : forall a n s, 0 < n -> IMG_LO + 64 <= a -> a + n + 64 <= IMG_TOP ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ IMG_LO <= 8 * (s - SHADOW_OFF) < IMG_TOP.
Proof.
intros a n s Hn Hlo Hhi Hs. unfold IMG_LO, IMG_TOP in *. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.

(* the text's shadow hull at any later state (IelemE's vrd_src_at argument, at a state of the same blocks) *)
Lemma vrd_text_hull : forall m mdx, ARx ly S2 Hp W m mdx -> 0 < len ->
  shadow_hull_vis (aview SEGS (w_H W) m) text len.
Proof.
intros m mdx HAR2 Hn. pose proof cf_head_nonneg as Hch.
pose proof (vrd_in_facts _ _ _ _ _ _ _ HIN) as (_ & _ & _ & _ & _ & Ilen & _).
destruct HHOME as [[(b & k & Hin & Hb & Hk) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] | (b & k & Hin & Hnhp & Hb & Hk)].
- pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ b k _ _ HLED Hin)
    as (Hk0 & Hab & Hhp & _). cbn [fst snd] in *.
  rewrite <- Eab in Hab.
  pose proof (alx_hshadow SEGS B ARx LAWS ly S2 Hp W m mdx (b - cf_head) (k + cf_head) HAR2 Hab Hhp) as [_ Hhu].
  rewrite HLc in Hhu. replace (b - cf_head + cf_head) with b in Hhu by lia.
  assert (Hreq : req_size (k + cf_head) - cf_head = k)
    by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  rewrite Hreq in Hhu. apply (vrd_hull_sub _ b k text len); [apply Hhu | lia | lia | exact Hn]. lia.
- intros s0 Hs. destruct (vrd_hull_img text len s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
  exact (H_imgvis _ _ _ _ _ _ _ HAR2 Hr).
- intros s0 Hs. destruct (vrd_hull_img text len s0 Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
  exact (H_imgvis _ _ _ _ _ _ _ HAR2 Hr).
- rewrite <- Eab in Hin.
  assert (Hnh : forall h, In h Hp -> ~ (b <= h < b + req_size k)).
  { intros h Hh Hr. destruct (vrd_ledger_hp _ _ _ _ _ _ _ _ _ _ _ _ h HLED Hh) as (k' & Hin').
    set (a' := h + cf_head) in Hin'. assert (Eh : h = a' - cf_head) by (unfold a'; lia). clearbody a'. subst h.
    pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ a' k' _ _ HLED Hin')
      as (Hk0' & Hab' & _). cbn [fst snd] in *.
    rewrite <- Eab in Hab'.
    destruct (Z.eq_dec (a' - cf_head) b) as [Eb|Nb]; [rewrite Eb in Hh; exact (Hnhp Hh)|].
    assert (Hne : (b, k) <> (a' - cf_head, k' + cf_head)) by (intros E; injection E as E1 _; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S2 Hp W m mdx _ _ _ _ HAR2 Hin Hab' Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. assert (Hkc : 0 <= k' + cf_head) by lia.
    pose proof (req_size_pos (k' + cf_head) Hkc). lia. }
  destruct (alx_shadow SEGS B ARx LAWS ly S2 Hp W m mdx b k HAR2 Hin Hnh) as [_ Hhu].
  assert (Hk0 : 0 <= k) by lia. pose proof (req_size_pos k Hk0).
  apply (vrd_hull_sub _ b (req_size k) text len Hhu); lia.
Qed.

(* the node at any later state of the segment, given the memory relation the walk keeps (memc against mem2 off the
   four written windows): its bytes kept through the frame call (acall_kept_x) and the prologue (KEEP1), its
   presence and ownership from the laws at that state, its shadow from the laws (a block) or kept (an old frame) *)
Lemma vrd_node_keep : forall memc mdc, ARx ly S2 Hp W memc mdc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) -> ~ (SF <= a < SF + 8) ->
     ~ (q <= a < q + 8) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem2 a) ->
  prhPv_node B (STK_parse_value d) e ly S2 W regs memc Lam v.
Proof.
intros memc mdc HAR2 Kd.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big d) as HSTK.
pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RNODE & RQV & _ & RVW & RLED & _).
pose proof RNODE as (N4096 & N8 & Nrw & Nz & Nat & Namr & Nown & Nra).
pose proof HKept as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof cf_head_nonneg as Hch.
assert (HinF : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (frames_bounds_x SEGS B ARx LAWS ly S2 Hp W memc mdc 0 pos HAR2 HinF) as (HF4096 & HFceil & HFapp).
pose proof (alx_frames SEGS B ARx LAWS ly S2 Hp W memc mdc 0 pos HAR2 HinF) as (HFal & _).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity. rewrite HFB in HFceil, HFapp.
pose proof (vrd_A_bounds (spZ regs) Hal16 ltac:(lia)) as (HAb1 & HAb2 & HAal).
assert (HF8v : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (HF8m : F mod 8 = 0)
  by (rewrite (Znumtheory.Zmod_div_mod 8 32 F ltac:(lia) ltac:(lia) ltac:(exists 4; reflexivity)), HFal; reflexivity).
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8m, Z.add_0_r in DF.
pose proof (Z.div_mod v 8 ltac:(lia)) as DV. rewrite N8, Z.add_0_r in DV.
(* where the node lies: an allocator block (every ledger block is one) or a frame of the entry state *)
assert (Hwhere : (exists b m, In (b, m) (ablocks B ly S) /\ b <= v /\ v + 56 <= b + req_size m) \/
                 (exists cid pos', In (cid, pos') (frames S) /\ frame_addr ly cid pos' <= v /\
                    v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid)).
{ destruct Nat as [(a0 & k0 & Hin & Hle & Hhi) | [(b0 & m0 & Hin & _ & Hle & Hhi) | [(cid & pos' & Hin & Hle & Hhi)
    | (Hw1 & Hw2)]]].
  - left. pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ RLED Hin)
      as (Hk0 & Hab & _). cbn [fst snd] in *.
    exists (a0 - cf_head), (k0 + cf_head). split; [exact Hab|].
    assert (Hkc : 0 <= k0 + cf_head) by lia. pose proof (req_size_pos (k0 + cf_head) Hkc). lia.
  - left. exists b0, m0. split; [exact Hin|].
    assert (Hm0 : 0 <= m0) by lia. pose proof (req_size_pos m0 Hm0). lia.
  - right. exists cid, pos'. split; [exact Hin | lia].
  - exfalso. destruct RVW; lia. }
(* the node's bytes are the entry's *)
assert (NK : forall a, v <= a < v + 56 -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct Hwhere as [(b & m & Hin & Hb & Hm) | (cid & pos' & Hin & Hf1 & Hf2)].
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & Hb4 & Hbc & Hbapp & _).
    assert (Hin2 : In (b, m) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 Hp W memc mdc b m 0 pos HAR2 Hin2 HinF) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd.
    replace a with (b + (a - b)) by lia.
    rewrite (Kd (b + (a - b))).
    + rewrite (K2 b m (a - b) Hin ltac:(lia) (fun x => x)). apply KEEP1; lia.
    + lia.
    + lia.
    + lia.
    + unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling, SHADOW_OFF in *. lia.
    + lia.
  - pose proof (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR Hin) as (Hc4 & Hcc & Hcapp).
    destruct (in_split _ _ Hin) as (l1 & l2 & El).
    assert (Hdj : zdisjoint (frame_rng ly (0, pos)) (frame_rng ly (cid, pos'))).
    { apply (sep_frames_pos_x SEGS B ARx LAWS ly S2 Hp W memc mdc (0, pos) (cid, pos') [] l1 l2 HAR2).
      rewrite Hfrs2, El. reflexivity. }
    unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj. rewrite HFB in Hdj.
    rewrite (Kd a).
    + rewrite (K4 cid pos' a Hin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia) (fun x => x)).
      apply KEEP1; lia.
    + lia.
    + lia.
    + lia.
    + unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling, SHADOW_OFF in *. lia.
    + lia. }
split; [exact N4096|]. split; [exact N8|].
split.
{ split; [exact N8|]. intros x Hx. apply (apresent_writable SEGS).
  destruct Hwhere as [(b & m & Hin & Hb & Hm) | (cid & pos' & Hin & Hf1 & Hf2)].
  - assert (Hin2 : In (b, m) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
    destruct (alx_blocks SEGS B ARx LAWS ly S2 Hp W memc mdc b m HAR2 Hin2) as (_ & _ & _ & _ & Hpr & _).
    exact (proj1 (Hpr x ltac:(lia))).
  - assert (Hin2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin).
    pose proof (alx_frames SEGS B ARx LAWS ly S2 Hp W memc mdc cid pos' HAR2 Hin2) as (_ & _ & Hpr & _).
    exact (proj1 (Hpr x ltac:(lia))). }
split.
{ intros j Hj. destruct (Nz j Hj) as (Hv0 & Hr0). split; [|exact Hr0].
  apply (vrd_val_mem_keep W mem memc); [|exact Hv0]. intros k0 Hk0. replace k0 with 0%nat by lia.
  rewrite Z.add_0_r. apply NK. rewrite repeat_length in Hj. lia. }
split.
{ destruct Nat as [H1 | [(b0 & m0 & Hin & Hn & Hle & Hhi) | [(cid & pos' & Hin & Hle & Hhi) | H4]]].
  - left. exact H1.
  - right. left. rewrite Eab. exists b0, m0. split; [exact Hin|]. split; [exact Hn|]. split; [exact Hle | exact Hhi].
  - right. right. left. exists cid, pos'. split; [rewrite Hfrs2; right; exact Hin|]. split; [exact Hle | exact Hhi].
  - right. right. right. exact H4. }
split; [exact Namr|].
split.
{ intros a Ha. split; [|exact (proj2 (Nown a Ha))].
  destruct Hwhere as [(b & m & Hin & Hb & Hm) | (cid & pos' & Hin & Hf1 & Hf2)].
  - assert (Hin2 : In (b, m) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
    destruct (alx_blocks SEGS B ARx LAWS ly S2 Hp W memc mdc b m HAR2 Hin2) as (_ & _ & _ & _ & Hpr & _).
    exact (proj2 (Hpr a ltac:(lia))).
  - assert (Hin2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin).
    pose proof (alx_frames SEGS B ARx LAWS ly S2 Hp W memc mdc cid pos' HAR2 Hin2) as (_ & _ & Hpr & _).
    exact (proj2 (Hpr a ltac:(lia))). }
destruct Nat as [(a0 & k0 & Hin & Hle & Hhi) | [(b0 & m0 & Hin & Hn & Hle & Hhi) | [(cid & pos' & Hin & Hle & Hhi)
  | (Hw1 & Hw2)]]].
- (* a ledger block: the hidden harness block's shadow past its head *)
  pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ RLED Hin)
    as (Hk0 & Hab & Hhp & _). cbn [fst snd] in *.
  rewrite <- Eab in Hab.
  pose proof (alx_hshadow SEGS B ARx LAWS ly S2 Hp W memc mdc (a0 - cf_head) (k0 + cf_head) HAR2 Hab Hhp)
    as [Hbs _].
  rewrite HLc in Hbs. replace (a0 - cf_head + cf_head) with a0 in Hbs by lia.
  assert (Hreq : req_size (k0 + cf_head) - cf_head = k0)
    by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
  rewrite Hreq in Hbs. eapply block_shadow_range; [exact Hbs | lia | lia].
- (* an allocator block outside the ledger: no harness head lies in it *)
  assert (Hm0 : 0 <= m0) by lia. pose proof (req_size_pos m0 Hm0) as Hrm.
  assert (Hnh : forall h, In h Hp -> ~ (b0 <= h < b0 + req_size m0)).
  { intros h Hh Hr. destruct (vrd_ledger_hp _ _ _ _ _ _ _ _ _ _ _ _ h RLED Hh) as (k' & Hin').
    set (a' := h + cf_head) in Hin'. assert (Eh : h = a' - cf_head) by (unfold a'; lia). clearbody a'. subst h.
    pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B _ _ _ _ _ _ _ _ _ _ a' k' _ _ RLED Hin')
      as (Hk0' & Hab' & _). cbn [fst snd] in *.
    assert (Hkc : 0 <= k' + cf_head) by lia. pose proof (req_size_pos (k' + cf_head) Hkc) as Hrk.
    destruct (Z.eq_dec b0 (a' - cf_head)) as [Eb | Nb].
    - destruct (Z.eq_dec m0 (k' + cf_head)) as [Em | Nm].
      + apply Hn. rewrite Eb, Em. replace (a' - cf_head + cf_head) with a' by lia.
        replace (k' + cf_head - cf_head) with k' by lia. exact Hin'.
      + assert (Hne : (b0, m0) <> (a' - cf_head, k' + cf_head)) by (intros E; injection E as _ E2; exact (Nm E2)).
        pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin Hab' Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    - assert (Hne : (b0, m0) <> (a' - cf_head, k' + cf_head)) by (intros E; injection E as E1 _; exact (Nb E1)).
      pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin Hab' Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (Hin2 : In (b0, m0) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
  destruct (alx_shadow SEGS B ARx LAWS ly S2 Hp W memc mdc b0 m0 HAR2 Hin2 Hnh) as [Hbs _].
  eapply block_shadow_range; [exact Hbs | lia | lia].
- (* a frame of the entry state: its shadow is kept from the entry *)
  pose proof (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR Hin) as (Hc4 & Hcc & Hcapp).
  pose proof (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos' HAR Hin) as (Hcal & _).
  set (F' := frame_addr ly cid pos') in *. set (fs' := fs_frame_bytes cid) in *.
  assert (HF'8m : F' mod 8 = 0)
    by (rewrite (Znumtheory.Zmod_div_mod 8 32 F' ltac:(lia) ltac:(lia) ltac:(exists 4; reflexivity)), Hcal;
        reflexivity).
  pose proof (Z.div_mod F' 8 ltac:(lia)) as DF'. rewrite HF'8m, Z.add_0_r in DF'.
  destruct (in_split _ _ Hin) as (l1 & l2 & El).
  assert (Hdj : zdisjoint (frame_rng ly (0, pos)) (frame_rng ly (cid, pos'))).
  { apply (sep_frames_pos_x SEGS B ARx LAWS ly S2 Hp W memc mdc (0, pos) (cid, pos') [] l1 l2 HAR2).
    rewrite Hfrs2, El. reflexivity. }
  unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj. rewrite HFB in Hdj. fold F' fs' in Hdj.
  assert (Hsum : (F' + fs') / 8 = F' / 8 + fs' / 8)
    by (rewrite DF' at 1; rewrite Z.mul_comm, Z.div_add_l by lia; reflexivity).
  assert (Hv7 : (v + 56) / 8 = v / 8 + 7)
    by (replace (v + 56) with ((v / 8 + 7) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (Hvf : (v + 56) / 8 <= (F' + fs') / 8) by (apply Z.div_le_mono; lia).
  assert (Hfv : F' / 8 <= v / 8) by (apply Z.div_le_mono; lia).
  assert (HFF : F / 8 + 8 <= F' / 8 \/ F' / 8 + fs' / 8 <= F / 8).
  { destruct Hdj as [Hd | Hd].
    - left. assert (H1 : (F + 64) / 8 <= F' / 8) by (apply Z.div_le_mono; lia).
      replace (F + 64) with ((F / 8 + 8) * 8) in H1 by lia. rewrite Z.div_mul in H1 by lia. exact H1.
    - right. rewrite <- Hsum. apply Z.div_le_mono; lia. }
  assert (Hv44 : v / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  intros x Hx. destruct (Nra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in Hs |- *. rewrite <- Hs.
  assert (Hx1 : v / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (Hx2 : x / 8 < v / 8 + 7) by (apply Z.div_lt_upper_bound; lia).
  rewrite (Kd (SHADOW_OFF + x / 8)).
  + rewrite (K4 cid pos' (SHADOW_OFF + x / 8) Hin
               ltac:(right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F' fs'; lia) (fun y => y)).
    apply KEEP1; unfold SHADOW_OFF in *; lia.
  + unfold SHADOW_OFF in *; lia.
  + unfold SHADOW_OFF in *; lia.
  + unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling, SHADOW_OFF in *. lia.
  + lia.
  + unfold SHADOW_OFF in *; lia.
- exfalso. destruct RVW; lia.
Qed.

Lemma vrd_disp_close : forall (arm : vrd_arm) (p' : Z) (regsc : bvmap 5 word) (memc : word -> option byte)
    (mdc : Model) (k : Z),
  p <= p' <= text + len -> rest_atR tb text p' = PjGrammar.skip (rest_atR tb text p) ->
  match PjGrammar.skip (rest_atR tb text p) with
  | [] => arm = VA_eof /\ p' = text + len
  | b :: _ => arm = vrd_arm_of b /\ p' < text + len /\ nth_error tb (Z.to_nat (p' - text)) = Some b /\
              PjGrammar.ws b = false /\ getr regsc 11 = w64 b
  end ->
  AJp memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (AF + 48 <= a < AF + 56) -> ~ (F <= a < F + 24) -> ~ (SF <= a < SF + 8) ->
     ~ (q <= a < q + 8) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem2 a) ->
  vrd_frame W memc ly pos -> val_mem SEGS (rdW W memc) q 8 p' ->
  vrd_regs regs regsc ly pos q v p' text len ->
  vrd_disp_a B ARx SK ly S Hp W regs mem md ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own W
    (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (vrd_PC + vrd_arm_off arm))) memc (seg_rom SEGS)) mdc).
Proof.
intros arm p' regsc memc mdc k Hpp' Hrest Harm HJ Kd Fr HQn HRG.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big d) as HSTK.
pose proof HIN as (Ip & Iend & Idep & Irw & Iq8 & It0 & It62 & Itp & Ilen & Itb & Iqt & Id1 & Id2).
pose proof HRD as (RFZ & RMU & RU1 & RU2 & RIN & RFW & RQ1 & RQ2 & RQA & RSRC & RHOME & RMAX & RNODE & RQV & RTV
  & RVW & RLED & RD & RCNT & RCEIL).
pose proof HKept as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (proj1 HJ) as HAR2. cbv beta in HAR2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & J10 & J11 & J12 & _ & J14 & _).
assert (HinF : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (frames_bounds_x SEGS B ARx LAWS ly S2 Hp W memc mdc 0 pos HAR2 HinF) as (HF4096 & HFceil & HFapp).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity. rewrite HFB in HFceil, HFapp.
pose proof (vrd_A_bounds (spZ regs) Hal16 ltac:(lia)) as (HAb1 & HAb2 & HAal).
assert (HF8u : F / 8 < 2 ^ 44)
  by (apply Z.div_lt_upper_bound; unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *;
      lia).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8a.
assert (HFsp : F + 64 <= spZ regs - STK_parse_value d)
  by (unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; lia).
assert (HSFsp : SF + 8 <= spZ regs - STK_parse_value d)
  by (unfold SHADOW_OFF, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; lia).
(* the dispatch memory at and above the entry sp, off the cursor's p word, is the entry memory *)
assert (KW : forall a, spZ regs <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a).
{ intros a Ha Hq. rewrite (Kd a) by lia. rewrite (K1 a) by lia. apply KEEP1; lia. }
exists arm, pos, p', k, ly, S2, Hp, regsc, memc, mdc. split.
{ unfold cfg_at. replace (SIGMA AS_parse_value + vrd_arm_off arm) with (BASE + (vrd_PC + vrd_arm_off arm));
    [reflexivity|].
  change (SIGMA AS_parse_value) with (BASE + vrd_PC). lia. }
unfold vrd_disp_body.
split; [exact Hrest|]. split; [exact Hpp'|]. split; [exact Harm|]. split; [exact HJ|].
split; [exact Hfrs2|]. split; [exact Eab|]. split; [reflexivity|]. split; [exact HSF|].
(* the caller's window off the reader's cells *)
split.
{ intros a Ha Hn. apply KW; [lia|]. intros Hq. apply Hn. hnf. exists (q, q + 8).
  split; [left; reflexivity | cbn [fst snd]; lia]. }
(* the window is present *)
split.
{ split; [exact He0|]. split; [exact He16|]. split; [exact Hetop|]. intros a Ha. apply J14. lia. }
split; [exact Fr|].
(* the saved registers *)
split.
{ pose proof HSV as HSV'. unfold vrd_saved in HSV' |- *.
  assert (KS : forall a n v0, spZ regs - 104 <= a -> a + Z.of_nat n <= spZ regs ->
    val_mem SEGS (rdW W mem2) a n v0 -> val_mem SEGS (rdW W memc) a n v0).
  { intros a n v0 H1 H2 Hv0. apply (vrd_val_mem_keep W mem2 memc); [|exact Hv0].
    intros k0 Hk0. apply Kd; lia. }
  destruct HSV' as (S01 & S02 & S03 & S04 & S05 & S06 & S07 & S08 & S09 & S10 & S11 & S12 & S13).
  repeat split; (apply KS; [lia | cbn; lia | assumption]). }
split; [exact HRG|].
split; [exact HCHN|]. split; [exact HCLO|]. split; [exact HCUR|]. split; [exact HCUC|].
(* the text's bytes are the entry's *)
pose proof RSRC as (_ & H4096 & Hceilt & Hamr & _ & _).
assert (TK : forall i, 0 <= i < len -> aview SEGS (w_H W) memc (text + i) = aview SEGS (w_H W) mem (text + i)).
{ intros i Hi. destruct (vrd_text_off memc mdc HAR2 i Hi) as [O1 O2].
  rewrite (Kd (text + i)); [exact (vrd_text_kept2 i Hi) | lia | lia | lia | lia | destruct Iqt; lia]. }
assert (GT : garr8 SEGS (rdW W memc) text tb).
{ intros j Hj. destruct (Itb j Hj) as (Hv0 & Hr0). split; [|exact Hr0].
  apply (vrd_val_mem_keep W mem memc); [|exact Hv0]. intros k0 Hk0. replace k0 with 0%nat by lia.
  rewrite Z.add_0_r. apply TK. lia. }
(* the cursor at the dispatch view *)
split.
{ unfold pj_in_okR. split; [exact HQn|].
  split; [apply (vrd_val_mem_keep W mem memc); [intros k0 Hk0; apply KW; lia | exact Iend]|].
  split; [apply (vrd_val_mem_keep W mem memc); [intros k0 Hk0; apply KW; lia | exact Idep]|].
  split; [intros x Hx; apply (apresent_writable SEGS); apply J14; lia|].
  split; [exact Iq8|]. split; [exact It0|]. split; [exact It62|]. split; [lia|]. split; [exact Ilen|].
  split; [exact GT|]. split; [exact Iqt | exact (conj Id1 Id2)]. }
(* the cursor's shadow: stack shadow *)
split.
{ intros x Hx. exists 0. split; [| left; reflexivity]. unfold shadow_of_addr.
  apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W memc mdc x HAR2). lia. }
(* the node *)
split; [exact (vrd_node_keep memc mdc HAR2 Kd)|].
(* carried from rd_pre and fpre *)
split; [exact RMU|]. split; [exact Hq1|]. split; [exact Hq2|]. split; [exact RQV|].
split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hra|]. split; [exact Hra4|].
split; [exact HIN|]. split; [exact RD|].
split; [exact RTV|]. split; [exact RVW|]. split; [exact RU1|]. split; [exact RU2|]. split; [exact RMAX|].
split; [pose proof (vrd_rest_shrink tb text p p' ltac:(lia)); lia|].
(* the text, at home *)
split.
{ split; [exact GT|]. split; [exact H4096|]. split; [exact Hceilt|]. split; [exact Hamr|].
  split; [rewrite Ilen; exact (vrd_text_addr memc mdc HAR2)|].
  intros Hn. rewrite Ilen in Hn |- *. exact (vrd_text_hull memc mdc HAR2 Hn). }
split; [unfold prhReader_home; rewrite Eab; exact HHOME|].
(* the ledger: no heap move in this segment *)
assert (BK : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  aview SEGS (w_H W) memc (b + i) = aview SEGS (w_H W) mem (b + i)).
{ intros b m i Hin Hi.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & Hb4 & Hbc & Hbapp & _).
  assert (Hin2 : In (b, m) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S2 Hp W memc mdc b m 0 pos HAR2 Hin2 HinF) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd.
  assert (HF8v : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
  rewrite (Kd (b + i)).
  - rewrite (K2 b m i Hin Hi (fun x => x)). apply KEEP1; lia.
  - lia.
  - lia.
  - lia.
  - unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling, SHADOW_OFF in *. lia.
  - lia. }
split.
{ (* the ledger at the dispatch state by S1Ledger.prh_ledger_kept_aview: prh_ledger / prh_glob are never
     destructed by position here (the statics are carried as the set prh_pst, each head by prh_ledger_hblock), so a
     conjunct the kit adds to either costs this proof nothing *)
  apply (S1Ledger.prh_ledger_kept_aview (PA := PI_prog_A) B ly S Hp W mem ly S2 Hp W memc Lam peak cnt fail ran most own
    RLED).
  - intros a Ha. destruct (H_pst a Ha) as (Hi & Hno & Her).
    pose proof (@pa_segs_low _ _ PI_prog_A _ Hi) as Hlow.
    rewrite (Kd a).
    + rewrite (K3 _ Hi Hno Her). apply KEEP1; lia.
    + lia.
    + lia.
    + intros Hr. destruct (alx_client_img SEGS B ARx LAWS ly S2 Hp W memc mdc a HAR2
        ltac:(right; left; exists 0, pos; split; [exact HinF | rewrite HFB; lia])) as [_ Hni]. exact (Hni Hi).
    + unfold kLowMemEnd, SHADOW_OFF in *. lia.
    + lia.
  - intros a0 k0 i Hin Hi.
    pose proof (S1Ledger.prh_ledger_hblock (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran a0 k0 most own RLED
      Hin)
      as Hhb.
    unfold prh_hblock in Hhb.
    pose proof (proj1 Hhb) as Hk0. pose proof (proj1 (proj2 Hhb)) as Hab.
    assert (Hhd : 8 <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
    apply (BK (a0 - cf_head) (k0 + cf_head) i Hab). lia.
  - intros a0 k0 _ Hab. rewrite Eab. exact Hab.
  - apply Permutation_refl. }
(* the room, across the frame take *)
split.
{ destruct HSF as (f & Ef). rewrite Ef. pose proof HROOM as (R1 & R2 & R3).
  split; [exact (RL_set_fs S f R1)|]. split; [exact R2 | exact R3]. }
(* the live counts: (a) tparse_value_specX's own, at the entry state, verbatim *)
split; [exact HSEC0|]. split; [exact HL240|].
(* (b) parse_string's at the string arm, from (a): its events are a prefix of the value's (vrd_pkR_str), and the
   frame take leaves the live requests as they are *)
assert (HSTR : arm = VA_str -> PjGrammar.skip (rest_atR tb text p) = 34 :: rest_atR tb text (p' + 1)).
{ intros Ea. pose proof (vrd_in_facts _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Ht1 & _ & Ht2 & _).
  revert Harm Hrest. destruct (PjGrammar.skip (rest_atR tb text p)) as [|b r]; intros Harm Hrest.
  - destruct Harm as (Ea' & _). rewrite Ea in Ea'. discriminate Ea'.
  - destruct Harm as (Ea' & Hlt & _). rewrite Ea in Ea'. symmetry in Ea'.
    pose proof (vrd_arm_of_str b Ea') as ->.
    rewrite (vrd_rest_cons tb text p') in Hrest by (clear - Ht1 Ht2 Hpp' Hlt; lia).
    injection Hrest as _ Er. rewrite Er. reflexivity. }
split.
{ intros Ea. destruct HSF as (fz & Ef). rewrite Ef.
  change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S))) with (PresetRoom.rs_live (YGcfRoom.room_of_cf S)).
  pose proof (vrd_pkR_str YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) d _ _ (HSTR Ea)) as Hk.
  clear - Hk HSEC0. lia. }
split.
{ intros Ea. destruct HSF as (fz & Ef). rewrite Ef.
  change (PresetRoom.rs_live (YGcfRoom.room_of_cf (set_fs fz S))) with (PresetRoom.rs_live (YGcfRoom.room_of_cf S)).
  pose proof (vrd_pkR_str (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) d _ _
    (HSTR Ea)) as Hk.
  clear - Hk HL240. lia. }
split.
{ rewrite Hfrs2. cbn [length].
  rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_succ in HFRC. lia. }
(* the read-only view *)
split.
{ intros a Hro Hno Her. pose proof (vrd_ro_img a Hro) as Hi.
  pose proof (@pa_segs_low _ _ PI_prog_A _ Hi) as Hlow.
  rewrite (Kd a).
  - rewrite (K3 a Hi Hno Her). rewrite (KEEP1 a) by lia. exact (HARO a Hro Hno Her).
  - lia.
  - lia.
  - intros Hr. destruct (alx_client_img SEGS B ARx LAWS ly S2 Hp W memc mdc a HAR2
      ltac:(right; left; exists 0, pos; split; [exact HinF | rewrite HFB; lia])) as [_ Hni]. exact (Hni Hi).
  - unfold kLowMemEnd, SHADOW_OFF in *. lia.
  - lia. }
split; [exact RFZ|].
(* the three entry facts of the kit's cut, verbatim at the entry state *)
split; [exact HCW|]. split; [exact HWR | exact RCEIL].
Qed.

(* ---- THE DISPATCH, rows 102..130: the cursor word and its shadow (row 102..105), then the byte at the cursor and
   its shadow gate (rows 106..110), then the two-level tree of rows 112..130. The rows store nothing, so every arm
   row closes by vrd_disp_close. ---- *)
Lemma vrd_lt : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
intros x y Hx Hy. unfold branch_taken, bv_lts.
rewrite (YK11.bv_signed_small (Z_to_bv 64 x)), (YK11.bv_signed_small (Z_to_bv 64 y))
  by (rewrite unsigned_lit_small by lia; lia).
rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma vrd_eq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold branch_taken. rewrite bv_eqb_unsigned, !unsigned_lit_small by lia. reflexivity. Qed.
(* the grammar's skip stops at a byte that is no white space *)
Lemma vrd_skip_head : forall l b r, PjGrammar.skip l = b :: r -> PjGrammar.ws b = false.
Proof.
induction l as [|x t IH]; intros b r H; cbn in H; [discriminate|].
destruct (PjGrammar.ws x) eqn:Ex; [exact (IH b r H) | injection H as -> _; exact Ex].
Qed.

Definition vrd_R106 : Z := vrd_PC + 416.
Definition vrd_d_regions : smem :=
  [ YP09.mkRegion (Some 20%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ].
Definition vrd_d_facts : facts :=
  mkFacts [(12%nat, mkAF 0 (2 ^ 62) 0); (20%nat, mkAF 4096 (2 ^ 47) 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (27%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0); (32%nat, mkAF 0 (2 ^ 62) 0)] [] [].
Definition ss_vrd_102 : sstate := mkSS vrd_R102 sr_atoms vrd_d_regions None vrd_d_facts.
Definition vrd_b_regions : smem :=
  [ YP09.mkRegion (Some 20%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 10 0))];
    YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
    YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ].
Definition vrd_b_facts : facts :=
  mkFacts [(10%nat, mkAF 4096 0x7fffff800000 0); (12%nat, mkAF 0 (2 ^ 62) 0); (20%nat, mkAF 4096 (2 ^ 47 - 24) 3);
           (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (27%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
           (32%nat, mkAF 0 255 0)] [] [].
Definition ss_vrd_106 : sstate := mkSS vrd_R106 sr_atoms vrd_b_regions None vrd_b_facts.

(* a run over regions with empty write windows keeps every byte *)
Ltac vrd_km0 KM memc :=
  lazymatch goal with HFr : frame_of ?E' ?rs (mrestrict _ ?m) (mrestrict _ ?m') |- _ =>
    let rs' := eval vm_compute in rs in change rs with rs' in HFr;
    let KM2 := fresh "KM" in
    assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) memc a)
      by (intros za zHa; etransitivity; [|exact (KM za zHa)]; apply aview_eq_of; apply HFr;
          intros (zr & zHin & zHr); cbn [In] in zHin;
          repeat (destruct zHin as [<- | zHin]; [cbn [YP09.r_wlo YP09.r_whi] in zHr; lia |]); destruct zHin);
    clear KM HFr; rename KM2 into KM
  end.
Ltac vrd_awr0 :=
  lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Lemma vrd_dispatch_inv : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall W' c', vrd_exQ W' c' -> P (ms_mem (cfg_ms c')) ->
  SRr SEGS W' c' (fun W2 c2 => vrd_disp_a B ARx SK ly S Hp W regs mem md ch CTX0 CW e q v text len p d tb Lam peak cnt
    fail ran most own W2 c2 /\ P (ms_mem (cfg_ms c2))).
Proof.
intros P PLAW W' c' (p' & Hpp' & Hrest & -> & regsc & memc & mdc & k & -> & HJ & Kc & Fr & HQc & R2 & R9 & R8 & R18 &
  R26 & R19 & R20 & R21 & R22 & R25 & R3 & R4 & R23 & R24 & R27 & R12 & _) HPM.
cbn [cfg_ms ms_mem] in HPM.
pose proof (paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW) as RUNI.
pose proof (paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW) as RUNTOI.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big d) as HSTK.
pose proof (vrd_in_facts _ _ _ _ _ _ _ HIN) as (Iq8 & It0 & It62 & Itp1 & Itp2 & Ilen & Iqt).
pose proof HSRC as (Hgarr & Ht4096 & Htc & _).
pose proof (proj1 HJ) as HAR2. cbv beta in HAR2.
assert (HinF : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (frames_bounds_x SEGS B ARx LAWS ly S2 Hp W memc mdc 0 pos HAR2 HinF) as (HF4096 & HFceil & HFapp).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity. rewrite HFB in HFceil, HFapp.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8a.
pose proof (vrd_A_bounds (spZ regs) Hal16 ltac:(lia)) as (HAb1 & HAb2 & HAal).
pose proof (Z.div_mod q 8 ltac:(lia)) as DQ. rewrite Iq8, Z.add_0_r in DQ.
assert (HF0 : 0 <= F) by lia.
assert (HFq : F + 64 <= q)
  by (unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; lia).
assert (HF8u : F / 8 < 2 ^ 44)
  by (apply Z.div_lt_upper_bound; unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *;
      lia).
assert (HSq : SF + 8 <= q)
  by (unfold SHADOW_OFF, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; lia).
assert (Hq64 : q + 8 <= 2 ^ 64) by lia.
(* ---- rows 102..105 ---- *)
remember (@Eimg _ A_prog_listing PI_prog_A (Ereg regsc [w64 p'])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EVn : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ n r Hr)).
assert (X32 : ew E 32 = w64 p')
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (UV : forall n (r : bv 5) z, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> getr regsc r = w64 z ->
  0 <= z < 2 ^ 64 -> bv_unsigned (ew E n) = z)
  by (intros n r z Hn Hr Hz Hz64; rewrite (EVn n r Hn Hr), Hz; apply unsigned_lit_small; exact Hz64).
assert (E12 : bv_unsigned (ew E 12) = text + len) by (apply (UV 12%nat 12%bv); [lia | reflexivity | exact R12 | lia]).
assert (E20 : bv_unsigned (ew E 20) = q) by (apply (UV 20%nat 20%bv); [lia | reflexivity | exact R20 | lia]).
assert (E23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (apply (UV 23%nat 23%bv); [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia]).
assert (E27 : bv_unsigned (ew E 27) = SHADOW_OFF + q / 8)
  by (apply (UV 27%nat 27%bv); [lia | reflexivity | exact R27 | unfold SHADOW_OFF; lia]).
assert (E32 : bv_unsigned (ew E 32) = p') by (rewrite X32; apply unsigned_lit_small; lia).
assert (Zq0 : aview SEGS (w_H W) memc (SHADOW_OFF + q / 8) = Some 0)
  by (apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W memc mdc q HAR2); lia).
assert (HS : st_ok_pi SEGS VAL E ss_vrd_102
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + vrd_R102)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold vrd_d_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p');
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact HQc.
    + rewrite E27. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply vrd_val_mem1. exact Zq0.
  - apply pairwise_disjoint_of_extents. unfold vrd_d_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E20, E27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; lia.
  - split; [|split; [exact I | exact I]].
    cbn [vrd_d_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E12, E20, E23, E27, E32.
    change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    unfold alloc_ceiling, ASAN_CEIL, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; try exact Iq8; try exact I; try lia. }
assert (SHOK : sh_ok SEGS vrd_Bx2 [] E (rdW W memc)) by apply Forall_nil.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
paj_run_tok_x_inv RUNI HS HJ SHOK HPM vrd_Bspan2.
{ vrd_awr0. }
vrd_km0 KM memc. clear HF HG.
(* ---- row 105: bgeu a0, a2, the cursor against the end ---- *)
psrr_branch_tok RUNI BR HS SHOK vrd_Bspan2.
all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E32, ?E12, ?Z.add_0_r in Hc; rewrite vrd_geu in Hc by lia.
- (* the cursor is at the end: the EOF arm *)
  assert (Hpe : p' = text + len) by (apply negb_true_iff, Z.ltb_ge in Hc; lia). clear Hc.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM vrd_Bspan2 (vrd_PC + vrd_arm_off VA_eof).
  { vrd_awr0. }
  vrd_km0 KM memc. clear HF HG.
  vrd_hq HS p' (SOff 32 0) HQn E32 E20.
  vrd_prregs HS. prreg HS (10%bv : bv 5) T10. prreg HS (2%bv : bv 5) T2. prreg HS (9%bv : bv 5) T9.
  pmkst HS.
  assert (VE : vrd_PC + vrd_arm_off VA_eof = 19220) by (vm_compute; reflexivity). rewrite <- VE.
  vrd_retP HPM.
  eapply (vrd_disp_close VA_eof p' _ _ _ _ Hpp' Hrest).
  + rewrite <- Hrest, Hpe, (vrd_rest_end tb text len Ilen). split; reflexivity.
  + exact HJ.
  + intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4).
  + exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))).
  + exact HQn.
  + unfold vrd_regs.
    split; [rewrite T2, (EVn 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
    split; [rewrite T9, T2, (EVn 9%nat 9%bv ltac:(lia) eq_refl), (EVn 2%nat 2%bv ltac:(lia) eq_refl), R9, R2;
            reflexivity|].
    do 13 (split; [vrd_reg_goal EVn|]).
    split; [rewrite T10; exact X32 | vrd_reg_goal EVn].
- (* a byte to read: rows 106.. *)
  assert (Hlt : p' < text + len) by (apply negb_false_iff, Z.ltb_lt in Hc; lia). clear Hc.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM vrd_Bspan2 vrd_R106.
  { vrd_awr0. }
  vrd_km0 KM memc. clear HF HG.
  vrd_prregs HS. prreg HS (10%bv : bv 5) T10.
  pmkst HS.
  assert (VR106 : vrd_R106 = 19152) by (vm_compute; reflexivity). rewrite <- VR106.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rB _ ?mB _) ?mdB0) _ =>
    set (regsB := rB) in *; set (memB := mB) in *; set (mdB := mdB0) in * end.
  assert (B2 : getr regsB 2 = w64 AF) by vrd_reg_goal EVn.
  assert (B9 : getr regsB 9 = w64 AF) by vrd_reg_goal EVn.
  assert (B8 : getr regsB 8 = w64 (spZ regs)) by vrd_reg_goal EVn.
  assert (B18 : getr regsB 18 = w64 F) by vrd_reg_goal EVn.
  assert (B26 : getr regsB 26 = w64 F) by vrd_reg_goal EVn.
  assert (B19 : getr regsB 19 = w64 v) by vrd_reg_goal EVn.
  assert (B20 : getr regsB 20 = w64 q) by vrd_reg_goal EVn.
  assert (B21 : getr regsB 21 = getr regs 21) by vrd_reg_goal EVn.
  assert (B22 : getr regsB 22 = getr regs 22) by vrd_reg_goal EVn.
  assert (B25 : getr regsB 25 = getr regs 25) by vrd_reg_goal EVn.
  assert (B3 : getr regsB 3 = getr regs 3) by vrd_reg_goal EVn.
  assert (B4 : getr regsB 4 = getr regs 4) by vrd_reg_goal EVn.
  assert (B23 : getr regsB 23 = w64 SHADOW_OFF) by vrd_reg_goal EVn.
  assert (B24 : getr regsB 24 = w64 SF) by vrd_reg_goal EVn.
  assert (B27 : getr regsB 27 = w64 (SHADOW_OFF + q / 8)) by vrd_reg_goal EVn.
  assert (B12 : getr regsB 12 = w64 (text + len)) by vrd_reg_goal EVn.
  assert (B10 : getr regsB 10 = w64 p') by (rewrite T10; exact X32).
  (* the byte at the cursor *)
  set (i := p' - text). assert (Ei : i = p' - text) by reflexivity.
  assert (Hi : 0 <= i < len) by lia.
  destruct (Hgarr (Z.to_nat i) ltac:(lia)) as (Hb1 & Hb256).
  set (b := nth (Z.to_nat i) tb 0) in *.
  replace (text + Z.of_nat (Z.to_nat i)) with p' in Hb1 by lia.
  destruct (vrd_text_off memc mdc HAR2 i Hi) as [O1 O2].
  assert (Kt : aview SEGS (w_H W) memB p' = aview SEGS (w_H W) mem p').
  { rewrite (KM p') by lia. replace p' with (text + i) by lia.
    rewrite (Kc (text + i)); [exact (vrd_text_kept2 i Hi) | lia | lia | lia | lia | destruct Iqt; lia]. }
  assert (TB1 : val_mem SEGS (rdW W memB) p' 1 b).
  { apply (vrd_val_mem_keep W mem memB); [|exact Hb1].
    intros k0 Hk0. replace k0 with 0%nat by lia. rewrite Z.add_0_r. exact Kt. }
  assert (HQB : val_mem SEGS (rdW W memB) q 8 p').
  { apply (vrd_val_mem_keep W memc memB); [|exact HQc]. intros k0 Hk0. apply KM. lia. }
  pose proof (proj1 HJ) as HARB. cbv beta in HARB.
  pose proof (vrd_text_app i Hi) as Happ.
  remember (@Eimg _ A_prog_listing PI_prog_A (Ereg regsB [w64 b])) as E' eqn:HE'.
  assert (HEI' : img_env VAL A_LIM E') by (subst E'; apply Eimg_env).
  assert (EVn' : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regsB r)
    by (intros n r Hn Hr; subst E'; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsB _ n r Hr)).
  assert (X32' : ew E' 32 = w64 b)
    by (subst E'; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsB _ 0)).
  assert (UV' : forall n (r : bv 5) z, (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> getr regsB r = w64 z ->
    0 <= z < 2 ^ 64 -> bv_unsigned (ew E' n) = z)
    by (intros n r z Hn Hr Hz Hz64; rewrite (EVn' n r Hn Hr), Hz; apply unsigned_lit_small; exact Hz64).
  assert (E'10 : bv_unsigned (ew E' 10) = p') by (apply (UV' 10%nat 10%bv); [lia | reflexivity | exact B10 | lia]).
  assert (E'12 : bv_unsigned (ew E' 12) = text + len)
    by (apply (UV' 12%nat 12%bv); [lia | reflexivity | exact B12 | lia]).
  assert (E'20 : bv_unsigned (ew E' 20) = q) by (apply (UV' 20%nat 20%bv); [lia | reflexivity | exact B20 | lia]).
  assert (E'23 : bv_unsigned (ew E' 23) = SHADOW_OFF)
    by (apply (UV' 23%nat 23%bv); [lia | reflexivity | exact B23 | unfold SHADOW_OFF; lia]).
  assert (E'27 : bv_unsigned (ew E' 27) = SHADOW_OFF + q / 8)
    by (apply (UV' 27%nat 27%bv); [lia | reflexivity | exact B27 | unfold SHADOW_OFF; lia]).
  assert (E'32 : bv_unsigned (ew E' 32) = b) by (rewrite X32'; apply unsigned_lit_small; lia).
  assert (ZqB : aview SEGS (w_H W) memB (SHADOW_OFF + q / 8) = Some 0)
    by (apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W memB mdB q HARB); lia).
  assert (HS' : st_ok_pi SEGS VAL E' ss_vrd_106
      (restrict (w_H W) (mkst regsB (Z_to_bv 64 (BASE + vrd_R106)) memB (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E'; apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold vrd_b_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite E'20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E' _ q 0 8 (SOff 10 0) p');
          [cbn [sv_denot]; rewrite E'10, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact HQB.
      + rewrite E'10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E' _ p' 0 1 (SOff 32 0) b);
          [cbn [sv_denot]; rewrite E'32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact TB1.
      + rewrite E'27. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E' _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. apply vrd_val_mem1. exact ZqB.
    - apply pairwise_disjoint_of_extents. unfold vrd_b_regions, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E'20, E'10, E'27.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL, alloc_ceiling, SHADOW_OFF in *.
      repeat match goal with |- _ /\ _ => split end; lia.
    - split; [|split; [exact I | exact I]].
      cbn [vrd_b_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E'10, E'12, E'20, E'23, E'27, E'32.
      change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      unfold alloc_ceiling, ASAN_CEIL, SHADOW_OFF in *.
      repeat match goal with |- _ /\ _ => split end; try exact Iq8; try exact I; try lia. }
  assert (SHOK' : sh_ok SEGS vrd_BxL vrd_SHL E' (rdW W memB)).
  { apply Forall_cons; [|apply Forall_nil]. split.
    - cbn [she_m she_lo she_hi]. unfold vrd_BxL.
      rewrite !U_SOff, E'23, E'20, !Z.add_0_r, (zcanon_id SHADOW_OFF), (zcanon_id q) by (unfold M64, SHADOW_OFF; lia).
      replace (24 - 0) with 24 by lia.
      intros x Hx. exists 0. split; [| left; reflexivity].
      apply (alx_zshadow_byte SEGS B ARx LAWS ly S2 Hp W memB mdB x HARB); lia.
    - unfold app_apart. cbn [she_m she_lo she_hi]. unfold vrd_BxL.
      rewrite !U_SOff, E'23, E'20, !Z.add_0_r, (zcanon_id SHADOW_OFF), (zcanon_id q) by (unfold M64, SHADOW_OFF; lia).
      intros a Ha. unfold alloc_ceiling, ASAN_CEIL, SHADOW_OFF in *. lia. }
  clear HS SHOK.
  paj_run_tok_x_inv RUNI HS' HJ SHOK' HPM vrd_Bspan.
  { unfold vrd_BxL. rewrite !U_SOff, E'23, E'10, !Z.add_0_r, (zcanon_id SHADOW_OFF), (zcanon_id p')
      by (unfold M64, SHADOW_OFF; lia).
    exact (range_addressable_sub _ SHADOW_OFF text len p' 1 (vrd_text_addr memB mdB HARB) ltac:(lia) ltac:(lia)). }
  { vrd_awr0. }
  vrd_km0 KM memc. clear HF HG.
  (* ---- row 112: blt a3, a1, 109 against the byte ---- *)
  psrr_branch_tok RUNI BR HS' SHOK' vrd_Bspan.
  all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E'32, ?Z.add_0_r in Hc.
  all: rewrite vrd_lt in Hc by lia.
  { (* the byte is above 109: rows 125..130 *)
    assert (Hhi : 109 < b) by (apply Z.ltb_lt in Hc; lia). clear Hc.
    paj_run_tok_x_inv RUNI HS' HJ SHOK' HPM vrd_Bspan.
    { vrd_awr0. }
    vrd_km0 KM memc. clear HF HG.
    psrr_branch_tok RUNI BR HS' SHOK' vrd_Bspan.
    all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E'32, ?Z.add_0_r in Hc.
    all: rewrite vrd_eq in Hc by lia.
    { assert (Hb : b = 110) by (apply Z.eqb_eq in Hc; lia). clear Hc.
      paj_run_to_tok_x_inv RUNTOI HS' HJ SHOK' HPM vrd_Bspan (vrd_PC + vrd_arm_off VA_null).
      { vrd_awr0. }
      vrd_km0 KM memc. clear HF HG.
      vrd_hq HS' p' (SOff 10 0) HQn E'10 E'20.
      vrd_prregs HS'. prreg HS' (10%bv : bv 5) U10. prreg HS' (11%bv : bv 5) U11.
      prreg HS' (2%bv : bv 5) U2. prreg HS' (9%bv : bv 5) U9.
      pmkst HS'.
      assert (VA : vrd_PC + vrd_arm_off VA_null = 19336) by (vm_compute; reflexivity). rewrite <- VA.
      vrd_retP HPM. eapply (vrd_disp_close VA_null p' _ _ _ _ Hpp' Hrest).
      { rewrite <- Hrest, (vrd_rest_cons tb text p') by lia. cbv beta iota.
        change (nth (Z.to_nat (p' - text)) tb 0) with b.
        split; [rewrite Hb; reflexivity|]. split; [exact Hlt|].
        split; [unfold b, i; apply nth_error_nth'; lia|].
        split; [apply (vrd_skip_head (rest_atR tb text p) b (rest_atR tb text (p' + 1))); rewrite <- Hrest;
                apply vrd_rest_cons; lia|].
        rewrite U11; exact X32'. }
      { exact HJ. }
      { intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4). }
      { exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))). }
      { exact HQn. }
      { unfold vrd_regs.
        split; [rewrite U2, (EVn' 2%nat 2%bv ltac:(lia) eq_refl); exact B2|].
        split; [rewrite U9, U2, (EVn' 9%nat 9%bv ltac:(lia) eq_refl), (EVn' 2%nat 2%bv ltac:(lia) eq_refl), B9, B2;
                reflexivity|].
        do 13 (split; [vrd_reg_goal EVn'|]).
        split; [rewrite U10, (EVn' 10%nat 10%bv ltac:(lia) eq_refl); exact B10 | vrd_reg_goal EVn']. }
    }
    assert (Hn1 : b <> 110) by (apply Z.eqb_neq in Hc; lia). clear Hc.
    paj_run_tok_x_inv RUNI HS' HJ SHOK' HPM vrd_Bspan.
    { vrd_awr0. }
    vrd_km0 KM memc. clear HF HG.
    psrr_branch_tok RUNI BR HS' SHOK' vrd_Bspan.
    all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E'32, ?Z.add_0_r in Hc.
    all: rewrite vrd_eq in Hc by lia.
    { assert (Hb : b = 116) by (apply Z.eqb_eq in Hc; lia). clear Hc.
      paj_run_to_tok_x_inv RUNTOI HS' HJ SHOK' HPM vrd_Bspan (vrd_PC + vrd_arm_off VA_true).
      { vrd_awr0. }
      vrd_km0 KM memc. clear HF HG.
      vrd_hq HS' p' (SOff 10 0) HQn E'10 E'20.
      vrd_prregs HS'. prreg HS' (10%bv : bv 5) U10. prreg HS' (11%bv : bv 5) U11.
      prreg HS' (2%bv : bv 5) U2. prreg HS' (9%bv : bv 5) U9.
      pmkst HS'.
      assert (VA : vrd_PC + vrd_arm_off VA_true = 19600) by (vm_compute; reflexivity). rewrite <- VA.
      vrd_retP HPM. eapply (vrd_disp_close VA_true p' _ _ _ _ Hpp' Hrest).
      { rewrite <- Hrest, (vrd_rest_cons tb text p') by lia. cbv beta iota.
        change (nth (Z.to_nat (p' - text)) tb 0) with b.
        split; [rewrite Hb; reflexivity|]. split; [exact Hlt|].
        split; [unfold b, i; apply nth_error_nth'; lia|].
        split; [apply (vrd_skip_head (rest_atR tb text p) b (rest_atR tb text (p' + 1))); rewrite <- Hrest;
                apply vrd_rest_cons; lia|].
        rewrite U11; exact X32'. }
      { exact HJ. }
      { intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4). }
      { exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))). }
      { exact HQn. }
      { unfold vrd_regs.
        split; [rewrite U2, (EVn' 2%nat 2%bv ltac:(lia) eq_refl); exact B2|].
        split; [rewrite U9, U2, (EVn' 9%nat 9%bv ltac:(lia) eq_refl), (EVn' 2%nat 2%bv ltac:(lia) eq_refl), B9, B2;
                reflexivity|].
        do 13 (split; [vrd_reg_goal EVn'|]).
        split; [rewrite U10, (EVn' 10%nat 10%bv ltac:(lia) eq_refl); exact B10 | vrd_reg_goal EVn']. }
    }
    assert (Hn2 : b <> 116) by (apply Z.eqb_neq in Hc; lia). clear Hc.
    paj_run_tok_x_inv RUNI HS' HJ SHOK' HPM vrd_Bspan.
    { vrd_awr0. }
    vrd_km0 KM memc. clear HF HG.
    psrr_branch_tok RUNI BR HS' SHOK' vrd_Bspan.
    all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E'32, ?Z.add_0_r in Hc.
    all: rewrite vrd_ne in Hc by lia.
    { assert (Hn3 : b <> 123) by (apply negb_true_iff, Z.eqb_neq in Hc; lia). clear Hc.
      paj_run_to_tok_x_inv RUNTOI HS' HJ SHOK' HPM vrd_Bspan (vrd_PC + vrd_arm_off VA_num).
      { vrd_awr0. }
      vrd_km0 KM memc. clear HF HG.
      vrd_hq HS' p' (SOff 10 0) HQn E'10 E'20.
      vrd_prregs HS'. prreg HS' (10%bv : bv 5) U10. prreg HS' (11%bv : bv 5) U11.
      prreg HS' (2%bv : bv 5) U2. prreg HS' (9%bv : bv 5) U9.
      pmkst HS'.
      assert (VA : vrd_PC + vrd_arm_off VA_num = 19356) by (vm_compute; reflexivity). rewrite <- VA.
      vrd_retP HPM. eapply (vrd_disp_close VA_num p' _ _ _ _ Hpp' Hrest).
      { rewrite <- Hrest, (vrd_rest_cons tb text p') by lia. cbv beta iota.
        change (nth (Z.to_nat (p' - text)) tb 0) with b.
        split; [rewrite vrd_arm_of_pivot, (proj2 (Z.ltb_lt 109 b) Hhi), (proj2 (Z.eqb_neq b 110) Hn1), (proj2 (Z.eqb_neq b 116) Hn2), (proj2 (Z.eqb_neq b 123) Hn3); reflexivity|]. split; [exact Hlt|].
        split; [unfold b, i; apply nth_error_nth'; lia|].
        split; [apply (vrd_skip_head (rest_atR tb text p) b (rest_atR tb text (p' + 1))); rewrite <- Hrest;
                apply vrd_rest_cons; lia|].
        rewrite U11; exact X32'. }
      { exact HJ. }
      { intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4). }
      { exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))). }
      { exact HQn. }
      { unfold vrd_regs.
        split; [rewrite U2, (EVn' 2%nat 2%bv ltac:(lia) eq_refl); exact B2|].
        split; [rewrite U9, U2, (EVn' 9%nat 9%bv ltac:(lia) eq_refl), (EVn' 2%nat 2%bv ltac:(lia) eq_refl), B9, B2;
                reflexivity|].
        do 13 (split; [vrd_reg_goal EVn'|]).
        split; [rewrite U10, (EVn' 10%nat 10%bv ltac:(lia) eq_refl); exact B10 | vrd_reg_goal EVn']. }
    }
    assert (Hb : b = 123) by (apply negb_false_iff, Z.eqb_eq in Hc; lia). clear Hc.
    paj_run_to_tok_x_inv RUNTOI HS' HJ SHOK' HPM vrd_Bspan (vrd_PC + vrd_arm_off VA_obj).
    { vrd_awr0. }
    vrd_km0 KM memc. clear HF HG.
    vrd_hq HS' p' (SOff 10 0) HQn E'10 E'20.
    vrd_prregs HS'. prreg HS' (10%bv : bv 5) U10. prreg HS' (11%bv : bv 5) U11.
    prreg HS' (2%bv : bv 5) U2. prreg HS' (9%bv : bv 5) U9.
    pmkst HS'.
    assert (VA : vrd_PC + vrd_arm_off VA_obj = 19252) by (vm_compute; reflexivity). rewrite <- VA.
    vrd_retP HPM. eapply (vrd_disp_close VA_obj p' _ _ _ _ Hpp' Hrest).
    { rewrite <- Hrest, (vrd_rest_cons tb text p') by lia. cbv beta iota.
      change (nth (Z.to_nat (p' - text)) tb 0) with b.
      split; [rewrite Hb; reflexivity|]. split; [exact Hlt|].
      split; [unfold b, i; apply nth_error_nth'; lia|].
      split; [apply (vrd_skip_head (rest_atR tb text p) b (rest_atR tb text (p' + 1))); rewrite <- Hrest;
              apply vrd_rest_cons; lia|].
      rewrite U11; exact X32'. }
    { exact HJ. }
    { intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4). }
    { exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))). }
    { exact HQn. }
    { unfold vrd_regs.
      split; [rewrite U2, (EVn' 2%nat 2%bv ltac:(lia) eq_refl); exact B2|].
      split; [rewrite U9, U2, (EVn' 9%nat 9%bv ltac:(lia) eq_refl), (EVn' 2%nat 2%bv ltac:(lia) eq_refl), B9, B2;
              reflexivity|].
      do 13 (split; [vrd_reg_goal EVn'|]).
      split; [rewrite U10, (EVn' 10%nat 10%bv ltac:(lia) eq_refl); exact B10 | vrd_reg_goal EVn']. }
  }
  (* the byte is at most 109: rows 113..118 *)
  assert (Hlo : b <= 109) by (apply Z.ltb_ge in Hc; lia). clear Hc.
  paj_run_tok_x_inv RUNI HS' HJ SHOK' HPM vrd_Bspan.
  { vrd_awr0. }
  vrd_km0 KM memc. clear HF HG.
  psrr_branch_tok RUNI BR HS' SHOK' vrd_Bspan.
  all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E'32, ?Z.add_0_r in Hc.
  all: rewrite vrd_eq in Hc by lia.
  { assert (Hb : b = 34) by (apply Z.eqb_eq in Hc; lia). clear Hc.
    paj_run_to_tok_x_inv RUNTOI HS' HJ SHOK' HPM vrd_Bspan (vrd_PC + vrd_arm_off VA_str).
    { vrd_awr0. }
    vrd_km0 KM memc. clear HF HG.
    vrd_hq HS' p' (SOff 10 0) HQn E'10 E'20.
    vrd_prregs HS'. prreg HS' (10%bv : bv 5) U10. prreg HS' (11%bv : bv 5) U11.
    prreg HS' (2%bv : bv 5) U2. prreg HS' (9%bv : bv 5) U9.
    pmkst HS'.
    assert (VA : vrd_PC + vrd_arm_off VA_str = 19268) by (vm_compute; reflexivity). rewrite <- VA.
    vrd_retP HPM. eapply (vrd_disp_close VA_str p' _ _ _ _ Hpp' Hrest).
    { rewrite <- Hrest, (vrd_rest_cons tb text p') by lia. cbv beta iota.
      change (nth (Z.to_nat (p' - text)) tb 0) with b.
      split; [rewrite Hb; reflexivity|]. split; [exact Hlt|].
      split; [unfold b, i; apply nth_error_nth'; lia|].
      split; [apply (vrd_skip_head (rest_atR tb text p) b (rest_atR tb text (p' + 1))); rewrite <- Hrest;
              apply vrd_rest_cons; lia|].
      rewrite U11; exact X32'. }
    { exact HJ. }
    { intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4). }
    { exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))). }
    { exact HQn. }
    { unfold vrd_regs.
      split; [rewrite U2, (EVn' 2%nat 2%bv ltac:(lia) eq_refl); exact B2|].
      split; [rewrite U9, U2, (EVn' 9%nat 9%bv ltac:(lia) eq_refl), (EVn' 2%nat 2%bv ltac:(lia) eq_refl), B9, B2;
              reflexivity|].
      do 13 (split; [vrd_reg_goal EVn'|]).
      split; [rewrite U10, (EVn' 10%nat 10%bv ltac:(lia) eq_refl); exact B10 | vrd_reg_goal EVn']. }
  }
  assert (Hn1 : b <> 34) by (apply Z.eqb_neq in Hc; lia). clear Hc.
  paj_run_tok_x_inv RUNI HS' HJ SHOK' HPM vrd_Bspan.
  { vrd_awr0. }
  vrd_km0 KM memc. clear HF HG.
  psrr_branch_tok RUNI BR HS' SHOK' vrd_Bspan.
  all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E'32, ?Z.add_0_r in Hc.
  all: rewrite vrd_eq in Hc by lia.
  { assert (Hb : b = 91) by (apply Z.eqb_eq in Hc; lia). clear Hc.
    paj_run_to_tok_x_inv RUNTOI HS' HJ SHOK' HPM vrd_Bspan (vrd_PC + vrd_arm_off VA_arr).
    { vrd_awr0. }
    vrd_km0 KM memc. clear HF HG.
    vrd_hq HS' p' (SOff 10 0) HQn E'10 E'20.
    vrd_prregs HS'. prreg HS' (10%bv : bv 5) U10. prreg HS' (11%bv : bv 5) U11.
    prreg HS' (2%bv : bv 5) U2. prreg HS' (9%bv : bv 5) U9.
    pmkst HS'.
    assert (VA : vrd_PC + vrd_arm_off VA_arr = 19580) by (vm_compute; reflexivity). rewrite <- VA.
    vrd_retP HPM. eapply (vrd_disp_close VA_arr p' _ _ _ _ Hpp' Hrest).
    { rewrite <- Hrest, (vrd_rest_cons tb text p') by lia. cbv beta iota.
      change (nth (Z.to_nat (p' - text)) tb 0) with b.
      split; [rewrite Hb; reflexivity|]. split; [exact Hlt|].
      split; [unfold b, i; apply nth_error_nth'; lia|].
      split; [apply (vrd_skip_head (rest_atR tb text p) b (rest_atR tb text (p' + 1))); rewrite <- Hrest;
              apply vrd_rest_cons; lia|].
      rewrite U11; exact X32'. }
    { exact HJ. }
    { intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4). }
    { exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))). }
    { exact HQn. }
    { unfold vrd_regs.
      split; [rewrite U2, (EVn' 2%nat 2%bv ltac:(lia) eq_refl); exact B2|].
      split; [rewrite U9, U2, (EVn' 9%nat 9%bv ltac:(lia) eq_refl), (EVn' 2%nat 2%bv ltac:(lia) eq_refl), B9, B2;
              reflexivity|].
      do 13 (split; [vrd_reg_goal EVn'|]).
      split; [rewrite U10, (EVn' 10%nat 10%bv ltac:(lia) eq_refl); exact B10 | vrd_reg_goal EVn']. }
  }
  assert (Hn2 : b <> 91) by (apply Z.eqb_neq in Hc; lia). clear Hc.
  paj_run_tok_x_inv RUNI HS' HJ SHOK' HPM vrd_Bspan.
  { vrd_awr0. }
  vrd_km0 KM memc. clear HF HG.
  psrr_branch_tok RUNI BR HS' SHOK' vrd_Bspan.
  all: cbn [sv_denot ew ewset Nat.eqb] in Hc; rewrite ?E'32, ?Z.add_0_r in Hc.
  all: rewrite vrd_ne in Hc by lia.
  { assert (Hn3 : b <> 102) by (apply negb_true_iff, Z.eqb_neq in Hc; lia). clear Hc.
    paj_run_to_tok_x_inv RUNTOI HS' HJ SHOK' HPM vrd_Bspan (vrd_PC + vrd_arm_off VA_num).
    { vrd_awr0. }
    vrd_km0 KM memc. clear HF HG.
    vrd_hq HS' p' (SOff 10 0) HQn E'10 E'20.
    vrd_prregs HS'. prreg HS' (10%bv : bv 5) U10. prreg HS' (11%bv : bv 5) U11.
    prreg HS' (2%bv : bv 5) U2. prreg HS' (9%bv : bv 5) U9.
    pmkst HS'.
    assert (VA : vrd_PC + vrd_arm_off VA_num = 19356) by (vm_compute; reflexivity). rewrite <- VA.
    vrd_retP HPM. eapply (vrd_disp_close VA_num p' _ _ _ _ Hpp' Hrest).
    { rewrite <- Hrest, (vrd_rest_cons tb text p') by lia. cbv beta iota.
      change (nth (Z.to_nat (p' - text)) tb 0) with b.
      split; [rewrite vrd_arm_of_pivot, (proj2 (Z.ltb_ge 109 b) Hlo), (proj2 (Z.eqb_neq b 34) Hn1), (proj2 (Z.eqb_neq b 91) Hn2), (proj2 (Z.eqb_neq b 102) Hn3); reflexivity|]. split; [exact Hlt|].
      split; [unfold b, i; apply nth_error_nth'; lia|].
      split; [apply (vrd_skip_head (rest_atR tb text p) b (rest_atR tb text (p' + 1))); rewrite <- Hrest;
              apply vrd_rest_cons; lia|].
      rewrite U11; exact X32'. }
    { exact HJ. }
    { intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4). }
    { exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))). }
    { exact HQn. }
    { unfold vrd_regs.
      split; [rewrite U2, (EVn' 2%nat 2%bv ltac:(lia) eq_refl); exact B2|].
      split; [rewrite U9, U2, (EVn' 9%nat 9%bv ltac:(lia) eq_refl), (EVn' 2%nat 2%bv ltac:(lia) eq_refl), B9, B2;
              reflexivity|].
      do 13 (split; [vrd_reg_goal EVn'|]).
      split; [rewrite U10, (EVn' 10%nat 10%bv ltac:(lia) eq_refl); exact B10 | vrd_reg_goal EVn']. }
  }
  assert (Hb : b = 102) by (apply negb_false_iff, Z.eqb_eq in Hc; lia). clear Hc.
  paj_run_to_tok_x_inv RUNTOI HS' HJ SHOK' HPM vrd_Bspan (vrd_PC + vrd_arm_off VA_false).
  { vrd_awr0. }
  vrd_km0 KM memc. clear HF HG.
  vrd_hq HS' p' (SOff 10 0) HQn E'10 E'20.
  vrd_prregs HS'. prreg HS' (10%bv : bv 5) U10. prreg HS' (11%bv : bv 5) U11.
  prreg HS' (2%bv : bv 5) U2. prreg HS' (9%bv : bv 5) U9.
  pmkst HS'.
  assert (VA : vrd_PC + vrd_arm_off VA_false = 19204) by (vm_compute; reflexivity). rewrite <- VA.
  vrd_retP HPM. eapply (vrd_disp_close VA_false p' _ _ _ _ Hpp' Hrest).
  { rewrite <- Hrest, (vrd_rest_cons tb text p') by lia. cbv beta iota.
    change (nth (Z.to_nat (p' - text)) tb 0) with b.
    split; [rewrite Hb; reflexivity|]. split; [exact Hlt|].
    split; [unfold b, i; apply nth_error_nth'; lia|].
    split; [apply (vrd_skip_head (rest_atR tb text p) b (rest_atR tb text (p' + 1))); rewrite <- Hrest;
            apply vrd_rest_cons; lia|].
    rewrite U11; exact X32'. }
  { exact HJ. }
  { intros a Ha H1 H2 H3 H4. rewrite (KM a Ha). exact (Kc a Ha H1 H2 H3 H4). }
  { exact (proj2 (vrd_keep_q memc _ HF0 HFq HSq Hq64 Kc Fr (fun a Ha _ => KM a Ha))). }
  { exact HQn. }
  { unfold vrd_regs.
    split; [rewrite U2, (EVn' 2%nat 2%bv ltac:(lia) eq_refl); exact B2|].
    split; [rewrite U9, U2, (EVn' 9%nat 9%bv ltac:(lia) eq_refl), (EVn' 2%nat 2%bv ltac:(lia) eq_refl), B9, B2;
            reflexivity|].
    do 13 (split; [vrd_reg_goal EVn'|]).
    split; [rewrite U10, (EVn' 10%nat 10%bv ltac:(lia) eq_refl); exact B10 | vrd_reg_goal EVn']. }
Qed.

(* the statement before the invariant (c773f2a0dde), byte-identical: vrd_dispatch_inv at P := fun _ => True *)
Lemma vrd_dispatch : forall W' c', vrd_exQ W' c' ->
  SRr SEGS W' c' (vrd_disp_a B ARx SK ly S Hp W regs mem md ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own).
Proof.
intros W' c' H.
exact (vrd_srr_drop _ _ _ (fun _ => True) (vrd_dispatch_inv (fun _ => True) vrd_true_laws W' c' H I)).
Qed.

(* rows 31..130: from the frame call's return to the dispatch *)
Lemma vrd_post_inv : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall regs2 md2 k,
  AJp mem2 md2 k ->
  getr regs2 10 = w64 F -> getr regs2 2 = w64 AF -> getr regs2 9 = w64 AF ->
  getr regs2 8 = w64 (spZ regs) -> getr regs2 19 = w64 v -> getr regs2 20 = w64 q ->
  getr regs2 23 = w64 SHADOW_OFF -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 25 = getr regs 25 ->
  P mem2 ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + vrd_R31)) mem2 (seg_rom SEGS)) md2)
    (fun W' c' => vrd_disp_a B ARx SK ly S Hp W regs mem md ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
      most own W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW regs2 md2 k HJ R10 R2 R9 R8 R19 R20 R23 R3 R4 R21 R22 R25 HPM.
eapply SRr_bind; [exact (vrd_seg23_inv P PLAW regs2 md2 k HJ R10 R2 R9 R8 R19 R20 R23 R3 R4 R21 R22 R25 HPM)|].
intros W' c' _ (HQ & HP2). exact (vrd_dispatch_inv P PLAW W' c' HQ HP2).
Qed.

(* the statement before the invariant (c773f2a0dde), byte-identical: vrd_post_inv at P := fun _ => True *)
Lemma vrd_post : forall regs2 md2 k,
  AJp mem2 md2 k ->
  getr regs2 10 = w64 F -> getr regs2 2 = w64 AF -> getr regs2 9 = w64 AF ->
  getr regs2 8 = w64 (spZ regs) -> getr regs2 19 = w64 v -> getr regs2 20 = w64 q ->
  getr regs2 23 = w64 SHADOW_OFF -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 25 = getr regs 25 ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + vrd_R31)) mem2 (seg_rom SEGS)) md2)
    (vrd_disp_a B ARx SK ly S Hp W regs mem md ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
      most own).
Proof.
intros regs2 md2 k HJ R10 R2 R9 R8 R19 R20 R23 R3 R4 R21 R22 R25.
exact (vrd_srr_drop _ _ _ (fun _ => True) (vrd_post_inv (fun _ => True) vrd_true_laws regs2 md2 k HJ R10 R2 R9 R8
  R19 R20 R23 R3 R4 R21 R22 R25 I)).
Qed.

End post.

(* ---- THE SEGMENT LEMMA: parse_value's entry segment, rows 1..130, from tparse_value_specX's premises (the kit's cut
   7cdbb61b5fa0, PRH_FnParse.v blob f0d92dcec7e9; the two it does not use - memnorm and In (raZ regs :: spine ch) CTX -
   are left out) to the dispatch state vrd_disp_a. ---- *)
Theorem vrd_pro_a : forall (d : nat) ly S Hp W regs mem md ch (CTX0 : list (list Z)) (CW : list (list Z))
    e q text len p (tb : list Z) v Lam peak cnt fail ran most own,
  fpre B ARx (STK_parse_value d) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  prh_cur_entry W mem regs q ->
  prh_cw_entry B CW W mem regs q ->
  (exists ch', achain ly (aview SEGS (w_H W) mem) (spZ regs) (s0Z regs) ch' /\ spine ch' = spine ch) ->
  ((spZ regs <= q < spZ regs + 16) \/
   (spZ regs + 16 <= q /\ exists ch', achain ly (aview SEGS (w_H W) mem) (spZ regs) (prh_s0 F_parse_string q) ch')) ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v ->
  rd_pre B (STK_parse_value d) ly S Hp W regs mem Lam peak cnt fail ran most own e q text len p d tb v ->
  rd_room S (prhPv_gtrace d (rest_atR tb text p)) ->
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  Z.of_nat (length (frames S)) + Z.of_nat (Nat.succ (PjGrammar.MAXD - d)) <= fs_frames 0 ->
  SRr SEGS W (cfg_at SEGS (pa_sigma AS_parse_value) regs mem md)
    (vrd_disp_a B ARx SK ly S Hp W regs mem md ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
      most own).
Proof.
intros d ly S Hp W regs mem md ch CTX0 CW e q text len p tb v Lam peak cnt fail ran most own
  HFP HCLO HCUR HCW HCHN HCUC H10 H11 HRD HROOM HWR HSEC0 HL240 HFRC.
(* fpre's first two conjuncts by projection (the kit's fpre grows at its end: PRH_Base.v blob ee6c7a38d6b6 adds the
   return address bound) *)
pose proof (proj1 HFP) as HPRE. pose proof (proj1 (proj2 HFP)) as HARO.
pose proof HRD as (RFZ & RMU & RU1 & RU2 & HIN & HWIN & Hq1 & Hq2 & RQA & HSRC & HHOME & RMAX & RNODE & RQV & RTV
  & RVW & HLED & RD & RCNT & RCEIL).
assert (Hcnt : count_cid 0 (frames S) < fs_frames 0).
{ pose proof (vrd_count_le 0 (frames S)) as Hc.
  assert (H1 : 1 <= Z.of_nat (Nat.succ (PjGrammar.MAXD - d)))
    by (rewrite Nat2Z.inj_succ; pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)); lia).
  eapply Z.le_lt_trans; [exact Hc|].
  apply Z.lt_le_trans with (m := Z.of_nat (length (frames S)) + Z.of_nat (Nat.succ (PjGrammar.MAXD - d)));
    [lia | exact HFRC]. }
eapply SRr_bind; [exact (vrd_seg1 d ly S Hp W regs mem md ch e q v HPRE HWIN H10 H11 Hcnt)|].
intros W' c' _ (-> & S2 & regs2 & mem1 & mem2 & md2 & pos & k & -> & HJ2 & Hfrs2 & Hnin & Eab & Hbb2 & HSF & R10 & R2
  & R9 & R8 & R19 & R20 & R23 & R3 & R4 & R21 & R22 & R25 & Hz & Hflag & Hfp & HSV & KEEP1 & HKept).
eapply vrd_post; eassumption.
Qed.

(* vrd_pro_a WITH the memory invariant (header): P at entry gives P at the dispatch state. It crosses the class-0
   frame call, so it takes srr_inv_call; the class-0 contract with the keep is the PROVED
   FCm01xm.stack_malloc0_contract_xm B ARx FSI TB (header). vrd_pro_a above stays as it is, over the proved
   FCm0s.stack_malloc0_contract_x. *)
Theorem vrd_pro_a_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall (d : nat) ly S Hp W regs mem md ch (CTX0 : list (list Z)) (CW : list (list Z))
    e q text len p (tb : list Z) v Lam peak cnt fail ran most own,
  fpre B ARx (STK_parse_value d) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 ->
  prh_cur_entry W mem regs q ->
  prh_cw_entry B CW W mem regs q ->
  (exists ch', achain ly (aview SEGS (w_H W) mem) (spZ regs) (s0Z regs) ch' /\ spine ch' = spine ch) ->
  ((spZ regs <= q < spZ regs + 16) \/
   (spZ regs + 16 <= q /\ exists ch', achain ly (aview SEGS (w_H W) mem) (spZ regs) (prh_s0 F_parse_string q) ch')) ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v ->
  rd_pre B (STK_parse_value d) ly S Hp W regs mem Lam peak cnt fail ran most own e q text len p d tb v ->
  rd_room S (prhPv_gtrace d (rest_atR tb text p)) ->
  YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S) ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  Z.of_nat (length (frames S)) + Z.of_nat (Nat.succ (PjGrammar.MAXD - d)) <= fs_frames 0 ->
  P mem ->
  SRr SEGS W (cfg_at SEGS (pa_sigma AS_parse_value) regs mem md)
    (fun W' c' => vrd_disp_a B ARx SK ly S Hp W regs mem md ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
      most own W' c' /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL d ly S Hp W regs mem md ch CTX0 CW e q text len p tb v Lam peak cnt fail ran most own
  HFP HCLO HCUR HCW HCHN HCUC H10 H11 HRD HROOM HWR HSEC0 HL240 HFRC HPM.
(* fpre's first two conjuncts by projection *)
pose proof (proj1 HFP) as HPRE. pose proof (proj1 (proj2 HFP)) as HARO.
pose proof HRD as (RFZ & RMU & RU1 & RU2 & HIN & HWIN & Hq1 & Hq2 & RQA & HSRC & HHOME & RMAX & RNODE & RQV & RTV
  & RVW & HLED & RD & RCNT & RCEIL).
assert (Hcnt : count_cid 0 (frames S) < fs_frames 0).
{ pose proof (vrd_count_le 0 (frames S)) as Hc.
  assert (H1 : 1 <= Z.of_nat (Nat.succ (PjGrammar.MAXD - d)))
    by (rewrite Nat2Z.inj_succ; pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)); lia).
  eapply Z.le_lt_trans; [exact Hc|].
  apply Z.lt_le_trans with (m := Z.of_nat (length (frames S)) + Z.of_nat (Nat.succ (PjGrammar.MAXD - d)));
    [lia | exact HFRC]. }
eapply SRr_bind; [exact (vrd_seg1_P P PLAW PCALL d ly S Hp W regs mem md ch e q v HPRE HWIN H10 H11 Hcnt HPM)|].
intros W' c' _ ((-> & S2 & regs2 & mem1 & mem2 & md2 & pos & k & -> & HJ2 & Hfrs2 & Hnin & Eab & Hbb2 & HSF & R10 &
  R2 & R9 & R8 & R19 & R20 & R23 & R3 & R4 & R21 & R22 & R25 & Hz & Hflag & Hfp & HSV & KEEP1 & HKept) & HP2).
cbn [cfg_ms ms_mem] in HP2.
eapply vrd_post_inv; eassumption.
Qed.

End w.

(* ---- SATISFIABILITY AT THE REAL INSTANCE (VERIFY 21:4xZ, check 1) of what this restatement adds to the dispatch
   state and to vrd_pro_a, at the unit's own CfParams (CfParams_preset: cf_head = 16) and the allocator's start state
   init_state - never at a trivial meter. ---- *)

(* the Section hypothesis HI_head *)
Lemma vrd_HI_head_preset : @cf_head CfParams_preset = PresetReqAt.HEAD.
Proof. reflexivity. Qed.

(* the four live-count conjuncts, (a) and (b) of vrd_disp_body, at the start state with the string arm taken
   (the text "ab" quoted, tb = [34; 97; 98; 34], the cursor at its first byte, d = 0): parse_value's granted trace and
   parse_string's both make the one fuzz_malloc of 3 + 16 bytes, so each count is 1 against LSEC + DRV and L24 + DRV
   (both above 3). The guarded pair is engaged, not vacuous: the arm here IS VA_str. *)
Lemma vrd_disp_counts_sat : forall text,
  vrd_arm_of 34 = VA_str /\
  PjGrammar.skip (rest_atR [34; 97; 98; 34] text text) = 34 :: rest_atR [34; 97; 98; 34] text (text + 1) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf init_state))
    (PresetReqAt.rd_hevs (prhPv_gtrace 0 (rest_atR [34; 97; 98; 34] text text)))) <=
    PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf init_state))
    (PresetReqAt.rd_hevs (prhPv_gtrace 0 (rest_atR [34; 97; 98; 34] text text)))) <=
    PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf init_state))
    (prhPs_evs (cp := CfParams_preset) (rest_atR [34; 97; 98; 34] text (text + 1)) [])) <=
    PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf init_state))
    (prhPs_evs (cp := CfParams_preset) (rest_atR [34; 97; 98; 34] text (text + 1)) [])) <=
    PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros text. unfold rest_atR.
replace (Z.to_nat (text - text)) with 0%nat by lia. replace (Z.to_nat (text + 1 - text)) with 1%nat by lia.
vm_compute. repeat split; first [reflexivity | intro Hc; discriminate Hc].
Qed.

Print Assumptions vrd_pro_a.
Print Assumptions vrd_pro_a_P.
Print Assumptions vrd_HI_head_preset.
Print Assumptions vrd_disp_counts_sat.

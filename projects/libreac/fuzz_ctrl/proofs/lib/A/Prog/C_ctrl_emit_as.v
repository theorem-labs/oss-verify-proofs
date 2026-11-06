(* ctrl_emit_as (0x849d8) on fuzz_ctrl's ASan build, image A: the cgif caller-journal contract, STATEMENT ONLY.
   No proof of the walk is in this file; `pb_ctrl_emit_as_stmt` states what the walk proves.

   The call cases. reac_ctrl_build_as tail-jumps here (`j 849d8` at 0x849a0) once per turn of
   LLVMFuzzerTestOneInput's kind latch (0x8194c addiw / 0x81958 bne back to 0x815cc, kind = 0..6). The arguments:
   p = the caller's frame variable `out.i` (class-6 side-stack frame, offset 544, 1492 bytes);
   f = row r of CTRL_FRAMES (A_OBJ 21 + 24 r), with r in {3..9} read from the switch table A_OBJ 20 = [3,5,6,7,8,4,9];
   md = a BOX_CATALOGUE entry (A_OBJ 17 + 296 i); d = 6 bytes of the same class-6 frame (`our`, offset 2624);
   s = A_OBJ 4 (round_trip.box, a registered global of 6 bytes); c16 = 0x1234;
   n = reac_box_model_upstream_width's result; g = 0; ns = 0.
   Rows 3..9 have k = r, tm = 0 and ao = al = rec_off = rec_len = 0, and their gate bytes (c, L, G, A) are CROW below.
   So the catalogue search, the md+16 reload and the L = 2 arm are never reached. The hidden field md+56 is read on
   rows 4 and 9. reac_braid_encode (0x84d20) runs on rows 5..8 at ns = 0. ctrl_finish stamps p+49 on rows 3 and 5 and
   writes nothing on the other rows.

   The call writes the caller's [p, p + R), so the contract is in cgif's caller-journal form
   (projects/cgif/cgif_file_fuzzer/proofs/lib/YC20.v:311-365; grant's CtrlFinish.v shape). It needs no apost_base.

   The walk, route (a) (a Theorem Labs lane's spec draft ctrl_emit_as-spec.md section 8 (a working note, not in this delivery)):
   ctrl's proved run ctrl_emit_asF.v (a file of a working branch, not in this delivery) is lifted through the bridge in two stretches,
   [0x849d8 .. the ctrl_lay_block call) and [0x84cf0 .. ret]. The single cgif step between them is TLAY at slot 3972
   (0x84cec), because only ctrl_lay_block's run contains a fake-stack allocation. memset, memcpy, reac_braid_encode and
   ctrl_finish run inside the lifted stretches as their _F contracts.

   Segments and the read-only premise (two Theorem Labs lanes, 23:37Z). The contract is stated over the walk's
   segment list SEGS := AB1v.tfibsegs. That is the list the core's lib contract, a Theorem Labs lane's cut layer and
   a Theorem Labs lane's tctrl_lay_block_spec use; it is not an abstract PA image's pa_segs. The PA values (VAL, BASE,
   pa_relro_lo, pa_relro_hi) are those of the image instance PI_ctrl (CtrlImg.v), whose pa_segs is tfibsegs. So
   CtrlCallerJ's shapes, which are stated over pa_segs, apply by conversion. The read-only premise is arodata_okS
   (core YE01.v), as in a Theorem Labs lane's ctl_base. The PA layer's arodata_okP is reached from it by a Theorem Labs lane's
   arodata_okP_of_S.

   Why a Definition and not a Theorem. A committed file holds no Admitted. The Section's hypotheses are therefore
   named binders of `pb_ctrl_emit_as_stmt`. Coq would drop Hypothesis declarations that no term uses, so they are
   not declared. The walk file states `Theorem pb_ctrl_emit_as : tctrl_emit_as_spec ...` under the same
   hypotheses, and `pb_ctrl_emit_as_stmt` follows from it by `intros`.

   Instances. ajournal and tctrl_lay_block_spec take {SK : Reusable.YI16.sink_head}. Each use passes the Section's ASan
   instance by name, (SK := SK), so that no global instance is inferred. tctrl_emit_as_post, tctrl_emit_as_spec and
   pb_ctrl_emit_as_stmt take {SK}, and a caller passes SK the same way. CtrlCallerJ's shapes and PALib take the PA
   instance by name, (PI := PI_ctrl).

   Requires. C_ctrl_lay_block (a working branch b3f8a5cf908: tctrl_lay_block_spec,
   TLAY_STK, EV_LAY, tfr_hull, A_FRAMES, A_CAT, ROW_BYTES, CAT_BYTES). Through it, C_reac_box_model_block, which is a
   statement-only contract (lib/A/Prog/C_reac_box_model_block.v, pb_reac_box_model_block_stmt): a Theorem Labs lane's file, landed, no longer a stand-in of a Theorem Labs lane's 4 Definitions.

   No achain premise and no `cl` binder (a Theorem Labs lane, 00:04Z): the only possible consumer was TLAY, and
   tctrl_lay_block_spec has no achain premise. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six modules that exist both as the core's lib/Reusable/<X> and as ctrl's lib/A/Reusable/<X> (YI04, YI16,
   YK11, YK1b, YM05, YO09) are Required, never Imported, and every use names the core's copy as
   lib.Reusable.<X> (porter a Theorem Labs lane 04:03Z and 04:33Z): the _F closure also loads ctrl's copies (through
   A/Contract.v), a short or `Reusable.`-prefixed name resolves to the copy loaded last, and even the Require
   must name the core's directory -- `From ...lib Require Reusable.X` matches ctrl's copy too. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlImg CtrlPaLib CtrlBase CtrlRo
CtrlCallerJ C_ctrl_lay_block.
(* ctrl's address-free model files and the callee contracts that run inside the lifted stretches. They belong to the
   closure of the _F files and are built over ctrl's plain lib.Lib, so they are Required without Import (glue closure
   rule, Theorem Labs lanes 23:38Z; lib.Lib's getr / mkst / seg_rom differ from Reusable.YK11's) and named with their module. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth RcLay RcFin RcEmit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require
asan_memset_cF asan_memcpy_cF reac_braid_encode_ns0_c ctrl_finish_c.
(* The lifted stretches' run-state facts are NOT premises here: the glue gets them from this statement's
   `ajournal` premise (AR at the cut) through a Theorem Labs lane's lib/A/ProgWorld.v, so that no route-(a) term enters
   the cgif-form statement a Theorem Labs lane consumes (a Theorem Labs lane, 2026-10-29 04:3xZ). *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* `lib.Reusable.<X>` names the core's copy only: ctrl's copy is lib.A.Reusable.<X>, of which `lib.Reusable.<X>` is
   not a suffix, while a bare `Reusable.<X>` is a suffix of both and resolves to whichever was loaded last. *)
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation SEGS := AB1v.tfibsegs.
#[local] Notation VAL := (@pa_val _ ctrl_listing PI_ctrl).
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
#[local] Notation PA_RLO := (@pa_relro_lo _ ctrl_listing PI_ctrl).
#[local] Notation PA_RHI := (@pa_relro_hi _ ctrl_listing PI_ctrl).
(* The core's register access, state constructor and segment rom, named through their qualified module
   (lib.Reusable.YK11 is Required, not Imported; see the Require block). Parsing only: the terms are
   lib.Reusable.YK11.getr / .mkst / .seg_rom. *)
#[local] Notation getr := lib.Reusable.YK11.getr (only parsing).
#[local] Notation mkst := lib.Reusable.YK11.mkst (only parsing).
#[local] Notation seg_rom := lib.Reusable.YK11.seg_rom (only parsing).
(* ---- the image objects the call cases name. A_FRAMES = 21, A_CAT = 17, ROW_BYTES = 24 and CAT_BYTES = 296 are
   C_ctrl_lay_block's. No auipc pair of this function names A_OBJ 21 or A_OBJ 4: the row pointer and round_trip.box
   arrive in registers. ---- *)
Definition A_BOX : nat := 4%nat.       (* round_trip.box 0x21140 (CtrlAddr.v:74): the 6 bytes a4 points at *)
(* The four gate bytes of row r (row[20] = c, row[21] = L, row[22] = G, row[23] = A), read from the image's
   CTRL_FRAMES rows 3..9. *)
Definition EM_C (r : Z) : Z := if (r =? 3) || (r =? 5) then 1 else 0.
Definition EM_L (r : Z) : Z := if (r =? 3) || (r =? 4) || (r =? 9) then 1 else 0.
Definition EM_G (r : Z) : Z := if (r =? 4) || (r =? 9) then 1 else 0.
Definition EM_A (r : Z) : Z := if (r =? 5) || (r =? 6) || (r =? 7) || (r =? 8) then 1 else 0.
(* The whole 24-byte row r of CTRL_FRAMES, as the image holds it for r in 3..9: cd ea r 0^17 c L G A. *)
Definition CROW (r : Z) : list byte :=
  [Z_to_bv 8 0xcd; Z_to_bv 8 0xea; Z_to_bv 8 r] ++ repeat (Z_to_bv 8 0) 17 ++
  [Z_to_bv 8 (EM_C r); Z_to_bv 8 (EM_L r); Z_to_bv 8 (EM_G r); Z_to_bv 8 (EM_A r)].
(* The stack the call needs. The own frame is 128 (`addi sp,sp,-128` at 0x849d8, no `andi`) and ctrl_lay_block is
   the deepest callee, so 128 + TLAY_STK = 4608. The lifted run assumes the window [S - 4640, S)
   (ctrl_emit_asF.v:223,253,301,326; ctrl's CTRL_EMIT_AS_K = 4640, ctrl_emit_as_c.v:14), so the constant is
   raised to 4640. *)
Definition TEMIT_STK : Z := Z.max (128 + TLAY_STK) 4640.
(* The function makes no allocator call and takes no frame itself; only ctrl_lay_block's run counts events. *)
Definition EV_EMIT : Z := EV_LAY.
Section e.
Variable B : asyms.
Variable GLOBS : list (Z * Z).     (* the registered globals, as tctrl_lay_block_spec takes them *)
Definition tctrl_emit_as_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p md c16 n r : Z) (mb nb db sb : list byte) : world SEGS -> config -> Prop :=
  let E := RcEmit.em_E (EM_L r) (EM_G r) n (RcEmit.em_hid mb) in
  let len := RcEmit.em_len (EM_L r) n in
  let R := if E then len else 0 in
  (* rows 3..9: ao = al = 0 and g = 0, so ctrl's block ly_lay .. is the catalogue block ly_Z .. *)
  let blk := RcFin.fin (EM_C r) 0 0 (RcLay.ly_Z md mb nb (RcLay.ly_bb r)) in
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + (if E then EV_EMIT else 0)) /\
  aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
  getr regs2 10 = w64 R /\
  (E = true ->
     garr8 SEGS (mrestrict (w_H W2) mem2) p
       (map bv_unsigned (RcEmit.em_fr db sb (c16 mod 65536) (Z_to_bv 8 0xcd) (Z_to_bv 8 0xea) blk len))) /\
  tcj_kept (PI := PI_ctrl) B TEMIT_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => p <= a < p + R).
Definition tctrl_emit_as_spec (a : Z) (rlo rhi : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p md d c16 n r i ns : Z) (mb nb db sb : list byte),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->      (* the caller's journal *)
  arodata_okS SEGS B rlo rhi (aview SEGS (w_H W) memc) ->        (* row, catalogue, box *)
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  (* the arguments, exactly the values reac_ctrl_build_as's tail jump leaves *)
  getr regs 10 = w64 p ->                                                         (* a0 *)
  getr regs 11 = w64 (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) -> 3 <= r <= 9 ->     (* a1 = f *)
  getr regs 12 = w64 md -> md = VAL (A_OBJ A_CAT) + CAT_BYTES * i -> 0 <= i < 11 ->   (* a2 *)
  getr regs 13 = w64 d ->                                                         (* a3 *)
  getr regs 14 = w64 (VAL (A_OBJ A_BOX)) ->                                       (* a4 *)
  getr regs 15 = w64 c16 -> 0 <= c16 < 2 ^ 64 ->                                  (* a5 *)
  getr regs 16 = w64 n -> - 2 ^ 31 <= n < 2 ^ 31 ->                               (* a6 *)
  getr regs 17 = w64 0 ->                                                         (* a7 = g = 0 *)
  getr regs 29 = w64 ns -> - 2 ^ 31 <= ns <= 0 ->     (* t4, read back at 0x84d08 for the braid arm *)
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TEMIT_STK -> spZ regs <= sp0 ->
  (* room for ctrl_lay_block's class-1 frame and reac_box_model_block's class-0 frame *)
  count_cid 1 (frames Sc) < fs_frames 1 -> count_cid 0 (frames Sc) < fs_frames 0 ->
  (* the caller's output buffer: 1492 bytes of its class-6 frame, of which [p, p + R) are written *)
  0 < p -> p mod 8 = 0 -> p + 1492 <= 2 ^ 47 - 8 -> amem_range p 1492 ->
  (forall x, p <= x < p + 1492 -> ~ in_img SEGS x) ->
  twr_ok (PI := PI_ctrl) B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 1492 ->
  afobj SEGS B lyc Sc W memc p 1492 ->
  (* The buffer and the source lie in a LIVE FRAME OF CLASS >= 2, so they are apart from the class-0 and
     class-1 side-stack frames that ctrl_lay_block's and reac_box_model_block's requests take. The lifted
     stretches take that apartness (the last conjunct of RcAsanFP.fp, `fp_dj D (fp_w [0;1] FS)`, which
     ProgWorld's ctl_fp_of_AR also leaves to the call site); afobj fixes no class, and this call's own room
     premises allow live class-0 / class-1 frames. True of the call: both are in LLVMFuzzerTestOneInput's
     class-6 frame (out.i at offset 544, our at offset 2624). *)
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= p /\
                   p + 1492 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  (exists cid pos, In (cid, pos) (frames Sc) /\ 2 <= cid /\ frame_addr lyc cid pos <= d /\
                   d + 6 <= frame_addr lyc cid pos + fs_frame_bytes cid) ->
  tfr_hull lyc Sc p 1492 ->
  (* the two 6-byte sources: d in the same caller frame, s in the image *)
  length db = 6%nat -> garr8 SEGS (mrestrict (w_H W) memc) d (map bv_unsigned db) ->
  tsrc_ok (PI := PI_ctrl) W memc (spZ regs) d 6 -> (forall x, d <= x < d + 6 -> ~ in_img SEGS x) ->
  (p + 1492 <= d \/ d + 6 <= p) ->
  (d + 6 <= spZ regs - TEMIT_STK \/ spZ regs <= d) ->
  (* d is 8-aligned (the frame variable `our` at offset 2624 of the 64-aligned class-6 frame). The lifted run's
     header copy needs d + 7 in application memory (ctrl_emit_asF2.v APD); tsrc_ok's amem_range gives d + 6
     only, and alignment rules out the one edge where d + 6 is the last byte of low memory. *)
  d mod 8 = 0 ->
  length sb = 6%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ A_BOX)) (map bv_unsigned sb) ->
  (* the catalogue entry: read here on rows 4 and 9 (md+56), and by ctrl_lay_block on every row *)
  garr8 SEGS (mrestrict (w_H W) memc) md (map bv_unsigned mb) -> length mb = 296%nat ->
  (* the name bytes, live exactly when ly_bb r is 5 or 6 (r = 4 or 9): tctrl_lay_block_spec's premise *)
  ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) -> RcSynth.has mb <> 0 -> RcSynth.rname mb <> 0 ->
     RcBox.name_ok nb /\
     garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname mb) (map bv_unsigned nb) /\
     (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname mb /\ RcSynth.rname mb + Z.of_nat (length nb) <= q + sz) /\
     (forall x, RcSynth.rname mb <= x < RcSynth.rname mb + Z.of_nat (length nb) -> in_roP SEGS rlo rhi x /\
        ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4))) ->
  SRr SEGS W (cfg_at SEGS a regs memc mdc)
    (tctrl_emit_as_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p md c16 n r mb nb db sb).
(* What the walk proves, with the Section's hypotheses as named binders (route (a): one owner's contract per
   callee). RLO / RHI are the read-only range of the RO premise, as a Theorem Labs lane's ctl_base takes them. *)
Variables RLO RHI : Z.
Definition pb_ctrl_emit_as_stmt : Prop :=
  forall (TL : PALib (PI := PI_ctrl) B) (LAWS : AR_laws SEGS B) (ML : model_laws (as_universe B))
    (* inside the lifted stretches: the _F contracts that ctrl's proved run takes (ctrl_emit_asF.v:244-248) *)
    (HMSF : asan_memset_cF.asan_memset_contract_F)          (* a Theorem Labs lane; asan_memset_holds_F *)
    (HMCF : asan_memcpy_cF.asan_memcpy_contract_F)          (* a Theorem Labs lane; asan_memcpy_holds_F *)
    (HBRF : reac_braid_encode_ns0_c.reac_braid_encode_ns0_contract_F)   (* a Theorem Labs lane's lift *)
    (HFNF : ctrl_finish_c.ctrl_finish_contract_F)            (* a Theorem Labs lane's lift *)
    (* the one cgif cut: ctrl_lay_block, whose run holds __asan_stack_malloc_1 *)
    (TLAY : tctrl_lay_block_spec (SK := SK) B GLOBS (BASE + AF_ctrl_lay_block) PA_RLO PA_RHI)
    (* No binder about raw memory across the call: a Theorem Labs lane measured that the core's
       astack_malloc_realizes (lib/Reusable/YG0d.v:285-303) gives only VIEW facts, so no clause about the
       bytes the world hides is provable across ctrl_lay_block. The second lifted stretch is RE-BASED on the
       memory the call returns instead, and the facts it needs there come from this statement's premises
       through TLAY's post and ProgWorld (a Theorem Labs lane, 2026-10-29 05:0xZ). *)
    (* What the image holds. The row table and the catalogue are REGISTERED GLOBALS, not whole-granule
       zero-shadow ranges: under a Theorem Labs lane's corrected zero-shadow list an `in_zs` fact over either is FALSE,
       which would make this statement vacuous (a Theorem Labs lane, 04:49Z). Both are therefore named through
       globs_marked, as round_trip.box already was. The sizes are the REGISTERED sizes, read from the image's
       own asan_globals table (section asan_globals, 57 entries at 0xa4380, between __start_asan_globals
       0xa4380 and __stop_asan_globals 0xa51c0, of (internal path)):
         CTRL_FRAMES    beg 0x9f7e0  size 264  (= 11 * ROW_BYTES)  size_with_redzone 352
         BOX_CATALOGUE  beg 0x9e800  size 3256 (= 11 * CAT_BYTES)  size_with_redzone 4064
         round_trip.box beg 0x21140  size 6                        size_with_redzone 32 *)
    (HIMGSH : img_shadow_vis SEGS B)
    (HGM : globs_marked SEGS B GLOBS)
    (HFR_glob : In (VAL (A_OBJ A_FRAMES), 11 * ROW_BYTES) GLOBS)
    (HFR_al : VAL (A_OBJ A_FRAMES) mod 8 = 0)
    (HCAT_glob : In (VAL (A_OBJ A_CAT), 11 * CAT_BYTES) GLOBS)
    (HCAT_al : VAL (A_OBJ A_CAT) mod 8 = 0)
    (HBOX_glob : In (VAL (A_OBJ A_BOX), 6) GLOBS)
    (HROWS : forall r, 3 <= r <= 9 -> forall (H : word -> bool) mem,
       arodata_okS SEGS B RLO RHI (aview SEGS H mem) ->
       garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_FRAMES) + ROW_BYTES * r) (map bv_unsigned (CROW r)))
    (HFR_rng : IMG_LO + 64 <= VAL (A_OBJ A_FRAMES) /\ VAL (A_OBJ A_FRAMES) + 11 * ROW_BYTES + 64 <= IMG_HI)
    (HCAT_rng : IMG_LO + 64 <= VAL (A_OBJ A_CAT) /\ VAL (A_OBJ A_CAT) + 11 * CAT_BYTES + 64 <= IMG_HI)
    (HBOX_rng : IMG_LO + 64 <= VAL (A_OBJ A_BOX) /\ VAL (A_OBJ A_BOX) + 6 + 64 <= IMG_HI)
    (* The walk carries arodata_okS across the ctrl_lay_block call: the read-only range is image memory, and
       the lifted stretches write only the stack window, the output buffer and the side stack for frames, none
       of which is image memory. Same name and form as cgif YC20.v:56 (a Theorem Labs lane, 2026-10-29 00:45Z). *)
    (RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a),
  tctrl_emit_as_spec (BASE + AF_ctrl_emit_as) RLO RHI.
End e.
End b.

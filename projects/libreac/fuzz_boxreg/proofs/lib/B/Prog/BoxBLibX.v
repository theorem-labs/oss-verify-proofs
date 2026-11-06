(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCfn.v (origin/ossv/recipes c8557374ad2), the ASan+UBSan twin of lib/A/ACfn.v, as lib/A/Prog/BoxLibX.v copies ACfn.v for the ASan build, with its module paths changed, its addresses moved to libreac/fuzz_boxreg's ASan+UBSan build (fuzz_boxreg.asan-ubsan), its names given the B forms of lib/B/Prog (A_ -> AB_, RA_ -> RAB_, a B suffix on the constants, tfib_ -> tbfib_, so that a file may import both), and the three changes below. *)
(* The whole-run contract of LLVMFuzzerTestOneInput on fuzz_boxreg.asan-ubsan (0x7ffac, 1058 instructions): the
   hypothesis that the ported ASan+UBSan top (TFIB_TB, lib/A/BoxTFIB.v) consumes, in cgif's shape (tbfib_lib_pre_x,
   tbfib_lib_post_x, tbfib_lib_contract_x, tbfib_lib_contract_x_all). Statement only.
   Values (each measured on fuzz_boxreg.asan-ubsan with elfdis):
   - AB_LLVMF = boxb_text + AF_LLVMFuzzerTestOneInput = 0x7ffac (BoxBAddr.v, BoxBList.v).
   - RAB_LLVMF = 0x7fea8: the driver's only call of the function is target_run's `jal` at 0x7fea4 (target_run
     0x7fddc); 0x7fea8 is the instruction after it.
   - AB_EMPTY = 0x5d3a20 (symbol oft_aligned_copy.empty): for n = 0 target_run branches at 0x7fe34 to 0x7fe84 and
     passes a0 = s4 + 0x10, s4 = 0x5d3a10 (auipc/addi at 0x7fe10, symbol target_run.initialized). For n > 0 it passes
     the __wrap_malloc copy of the input (0x7fe3c, memcpy at 0x7fe50): a heap block of length n.
   - EV_LIBB = 2000, cgif's value: one run makes at most 2 + 2 * 64 = 130 allocator events (registry malloc 0x8017c
     and free 0x80e58; one read_name malloc and one free in each of at most 64 loop iterations; PROGRAM.md P3 section
     4). 130 <= 2000, and the top's composition is written for 2000 (4 * 2000 + 3 <= EV_MAX = 8192), so the exact
     value is not needed.
   - LIVE_LIBB = 2 ^ 33, cgif's value: one run holds at most 288 + 48 = 336 live bytes above the entry's blocks.
   - LLVMF_STKB = 32768, cgif's value, a bound: the function's own machine stack is at most 688 bytes (addi
     sp,sp,-0x100 at 0x7ffac, andi sp,sp,-0x20 at 0x7ffec (16 more), then without a side-stack frame the 0x1a0-byte
     frame below it at 0x80034 .. 0x8004c); its deepest callee needs ASTACK + 48 = 16432 (read_name: frame 0x30 and the
     __wrap_malloc call, whose acall_pre needs ASTACK = 16384, YG0d.v); its own malloc and free calls need ASTACK;
     reac_boxreg_add needs 80 + reac_boxreg_find's 80 + 2 * ESTACK, check 144 + 2 * ESTACK, the bcmp wrapper
     2 * ESTACK (abcmp_realizes). 688 + 16432 = 17120 <= 32768. The strncmp wrapper (__wrap_strncmp 0x41458, called at
     0x80698, 0x808a4, 0x80c3c) has no contract in lib/Reusable yet; it has 32768 - 688 = 32080 bytes of room.
   Changes from cgif's shape (each because fuzz_boxreg's tree and images differ from cgif's):
   - cgif's pre and post state asink_none segs tfib_K and ameta_inv segs tfib_K (lib/YE00.v, lib/YE01.v, over the
     stdio and malloc-meta record tfib_K of lib/YE2k.v), and arodata_okS segs B (lib/YE01.v). None of these three
     files is in fuzz_boxreg's tree, and fuzz_boxreg.asan-ubsan holds no "/tmp/out.gif" string (YE00.v astdio_env
     needs it at ak_path), so cgif's sink record has no instance here. The sink and meta invariants are therefore two
     variables of the section, SINKN (in place of asink_none segs tfib_K) and METAI (in place of ameta_inv segs
     tfib_K), which the ported top instantiates; tbfib_lib_contract_x_all takes them as its two last arguments.
     fuzz_grant instead copies lib/Reusable/YE00.v and lib/Reusable/YE01.v (a working branch f8f56869a0c) and
     lib/A/AB1v.v and lib/A/AE2k.v (03b974dd117, its tfib_K moved to fuzz_grant.asan), and its lib/A/ACfn.v uses them
     unchanged.
   - arodata_okS segs B RLO RHI is lib/A/Prog/BoxBase.v's arodata_okP segs RLO RHI B: the same read-only predicate
     (in_roP is arodata_okS's premise), with the arguments in BoxBase.v's order.
   - segs is BoxBImg.v's boxb_segs (images.AsanUbsan's loaded segments, cgif's tfibsegs of lib/YB1v.v), and the sink
     head is the section's context {SK : YI16.sink_head}, as in every spec of lib/B/Prog (cgif takes it from YE2k.v's
     instance tfib_sink_head).
   Hazards of the function (for its proof):
   - Its ASan frame: if the GOT-loaded use-after-return flag is set it calls __asan_stack_malloc_3 (a0 = 0x1a0) at
     0x8001c (a side-stack frame); otherwise it takes the 0x1a0 bytes on the machine stack with a stack probe that
     stores 8 zero bytes 4096 bytes below the 32-aligned sp (0x80040 .. 0x80048). It writes the frame's shadow
     (0x80088 .. 0x80160). On every exit (0x80e64) it writes the retired-frame magic 0x45e0360e into the frame's
     first word, then calls __asan_set_shadow_f5 (0x80e80, side-stack frame) or clears the frame's shadow
     (0x80e90 .. 0x80f5c), and returns a0 = 0 (0x80f60).
   - n >= 2 ^ 26 returns 0 at once (srli a0, s4, 0x1a at 0x80140; bnez at 0x80164); the registry is __wrap_malloc
     (0x120) at 0x8017c (a NULL result branches at 0x80180 to the abort path) and __wrap_free at 0x80e58.
   - The UBSan checks branch to the trap `unimp` at 0x80fac (25 branch sites, the first at 0x801a4); the
     __asan_report_* calls and __asan_handle_no_return + abort (0x80fa4, 0x80fa8) do not return. LIBK at box_shape is
     K (LL 0 fs []) (lib/A/BoxShape.v), so the proof must show each of these paths unreachable.
   - Image difference: the asan build (lib/A/Prog/BoxLibX.v) has no UBSan checks, calls lowest_free where this build
     inlines its loops (calling range_free), and has no read_mac.
   - No f* or csr instruction occurs in the function (measured), so the fixed FP state fx of the section is sound. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBList BoxBAddr BoxBImg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition AB_LLVMF : Z := boxb_text + AF_LLVMFuzzerTestOneInput.
Definition RAB_LLVMF : Z := 0x7fea8.
Definition AB_EMPTY : Z := 0x5d3a20.
Definition EV_LIBB : Z := 2000.
Definition LIVE_LIBB : Z := 2 ^ 33.
Definition LLVMF_STKB : Z := 32768.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable SINKN : (word -> option byte) -> Model -> Prop.
Variable METAI : alayout -> (word -> option byte) -> Z -> Prop.
Local Notation segs := boxb_segs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition tbfib_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STKB ly S W regs mem md [] /\
raZ regs = RAB_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = AB_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIBB <= EV_MAX /\ blocks_bytes S + LIVE_LIBB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) /\
SINKN (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
METAI ly (rd W mem) M /\
mo_ok MT S (XM_LIB n) /\
(* the rounding mode at the harness entry, as in lib/A/Prog/BoxLibX.v: the core's fx-slot premise
   (a Theorem Labs lane, bd0315ce146 ACfn.v:104), handed down to the snprintf wrapper. *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Definition tbfib_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STKB (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIBB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
SINKN (rd W' mem') md' /\
METAI ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition tbfib_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tbfib_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = @cfg_at fx' segs RAB_LLVMF regs' mem' md' /\
(forall k0 : bv 5, bv_unsigned k0 <> 10 -> Sem.reg_get (@fp_regs fx') k0 = Sem.reg_get (@fp_regs fx) k0) /\
(@fp_csr fx' = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0) /\
tbfib_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs AB_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End a.
Definition tbfib_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} {SK : YI16.sink_head} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z)
(SINKN : (word -> option byte) -> Model -> Prop) (METAI : alayout -> (word -> option byte) -> Z -> Prop) : Prop :=
forall fx : YK11.FPState, @tbfib_lib_contract_x fx rc LS SK B MT XM_LIB XN_LIB RLO RHI SINKN METAI.
(* ---- the proof: pb_bllvmf_libx, the walk of lib/B/Prog/BoxBLx*.v closed at box_shape (lib/A/BoxShape.v: LIBK is
   K (LL 0 fs [])) ---- *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YC5d YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import BoxShape.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBReacBoxregInit BoxBCheck BoxBReadMac BoxBReadName BoxBRangeFree BoxBReacBoxregFind
BoxBReacBoxregDeclare BoxBReacBoxregAdd BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB SetShadowDef SnprintfDefB StrncmpViewB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxRo.
From OSSVerify.libreac.fuzz_boxreg.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxLoop
BoxBLxEntry BoxBLxTop BoxBLxCase0 BoxBLxCase1 BoxBLxCase2 BoxBLxCase3 BoxBLxJoinRow BoxBLxExit.
Section h. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable SINKN : (word -> option byte) -> Model -> Prop.
Variable METAI : alayout -> (word -> option byte) -> Z -> Prop.
(* ---- the Section hypotheses: the callee contracts, the runtime entries and the facts on B and MT the walk uses
   (BoxBLxDefs.v lx_hyps, field by field; the facts on the listing's objects are proved below for PI_boxb) ---- *)
Hypothesis LAWS : forall `{fx : YK11.FPState}, AR_laws boxb_segs B.
Hypothesis TL : forall `{fx : YK11.FPState}, PALib B.
Hypothesis TLF : forall `{fx : YK11.FPState}, PALibF B.
(* B's allocator constants fix the start-up shadow of the five globals (BoxBLxDefs.v lx_glob_cells). *)
Hypothesis GCELLS : forall `{fx : YK11.FPState} ly c, In c (lx_glob_cells boxb_val) -> In c (as_const B ly).
(* The image's read-only bytes the walk reads (verbatim the six facts of BoxBClose.v's W_ENTRY_B): ZERO, read_mac.base,
   "%s", musl memchr's constants, and the two "" strings. *)
Hypothesis ROMB_ZERO : absn_rom_bytes boxb_segs B 0x20cc0 (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis ROMB_MACB : absn_rom_bytes boxb_segs B 0x20d00 [0; 0x40; 0xab; 0; 0].
Hypothesis ROMB_FMT : absn_rom_bytes boxb_segs B 0x20d40 ABSN_FMT.
Hypothesis ROMB_MCH : absn_rom_bytes boxb_segs B MCH_LOB MCH_CONSTSB.
Hypothesis ROMS_E5 : absn_rom_str boxb_segs B 0x20ce0 [].
Hypothesis ROMS_E11 : absn_rom_str boxb_segs B 0x20d60 [].
(* Every allocator-owned byte of the read-only image is a const cell carrying the image's word (strncmp's
   rom_viewO, lib/B/Rt/StrncmpViewB.v abfm_rom_viewO_of_AR). *)
Hypothesis PINNED : abfm_ro_owned_pinned boxb_segs B.
Hypothesis ISV : forall `{fx : YK11.FPState}, img_shadow_vis boxb_segs B.
Hypothesis ML : forall `{fx : YK11.FPState}, model_laws (as_universe B).
Hypothesis MTL : forall `{fx : YK11.FPState}, ameter_laws MT.
Hypothesis MTFL : forall `{fx : YK11.FPState}, ameter_fs_laws MT.
Hypothesis ASM3 : forall `{fx : YK11.FPState}, astack_malloc_realizes boxb_segs B 3.
Hypothesis SMP : forall `{fx : YK11.FPState}, stack_malloc_progressP B.
Hypothesis ASF : forall `{fx : YK11.FPState}, astack_free_law boxb_segs B.
Hypothesis FFL : forall `{fx : YK11.FPState}, frame_flag_lawP boxb_segs B.
Hypothesis AMALLOC4 : forall `{fx : YK11.FPState}, amalloc04_rule boxb_segs B MT.
Hypothesis AFREE4 : forall `{fx : YK11.FPState}, afree04_rule boxb_segs B MT.
Hypothesis AMEMCPY : forall `{fx : YK11.FPState}, aintrin_realizes boxb_segs B OCpy (boxb_sigma BB___asan_memcpy).
Hypothesis ABCMP : forall `{fx : YK11.FPState}, abcmp_realizes boxb_segs B (boxb_sigma BB___interceptor_trampoline_bcmp).
Hypothesis ASTRNCMP : forall `{fx : YK11.FPState},
  abstrncmp_realizes boxb_segs B (boxb_sigma BB___interceptor_trampoline_strncmp).
Hypothesis ASETSH : forall `{fx : YK11.FPState}, aset_shadow_realizes boxb_segs B (boxb_sigma BB___asan_set_shadow_f5) 0xf5.
Hypothesis TINIT : forall `{fx : YK11.FPState}, tbreac_boxreg_init_spec B.
Hypothesis TCHECK : forall `{fx : YK11.FPState}, tbcheck_spec B.
Hypothesis TREADMAC : forall `{fx : YK11.FPState}, tbread_mac_spec B.
Hypothesis TREADNAME : forall `{fx : YK11.FPState}, tbread_name_spec B MT.
Hypothesis TRANGEFREE : forall `{fx : YK11.FPState}, tbrange_free_spec B.
Hypothesis TFIND : forall `{fx : YK11.FPState}, tbreac_boxreg_find_spec B.
Hypothesis TDECLARE : forall `{fx : YK11.FPState}, tbreac_boxreg_declare_spec B.
Hypothesis TADD : forall `{fx : YK11.FPState}, tbreac_boxreg_add_spec B.
Hypothesis TSETNAME : forall `{fx : YK11.FPState}, tbreac_boxreg_set_name_spec B.
(* read_name's malloc trace (its return address 0x81438) is in the universe. *)
Hypothesis RNTRACE : In [pc_malloc_ra0 (as_code B); AB_read_name_mallocRA] (as_universe B).
(* The read-only range the contract is stated over covers the image's GNU_RELRO segment (BoxBImg.v pa_relro_lo /
   pa_relro_hi), the range the callee contracts read. *)
Hypothesis HRO : forall rd, arodata_okP boxb_segs RLO RHI B rd -> arodata_okP boxb_segs 0x98d78 0x99fd0 B rd.
(* The call traces of the malloc and free wrappers at this function's four call sites are in the universe. *)
Hypothesis HTR : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
  raZ regs = RAB_LLVMF ->
  (pcf = pc_malloc_ra0 (as_code B) /\ In (raZ regsT - boxb_text) LX_MSITES) \/
  (pcf = pc_free_ra0 (as_code B) /\ In (raZ regsT - boxb_text) LX_FSITES) ->
  In (call_trace0 pcf regsT (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
     (as_universe B).
(* The budget: the call spends at most LX_NEED, which the caller grants (cgif's HXL). *)
Hypothesis HXL : forall n, LX_NEED MT <= XM_LIB n /\ XM_LIB n <= XN_LIB n.
(* The sink and meta invariants survive a journal that opens no sink (cgif's asink_none_kept / ameta_inv_kept,
   lib/YE01.v, under AIL). *)
Hypothesis SINKN_KEPT : forall `{fx : YK11.FPState} STK sp0 FP ly S (W : world boxb_segs) mem md own ly' S' W' mem' md' k,
  ajournal boxb_segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> ~ YI16.sink_open_fp FP ->
  SINKN (mrestrict (w_H W) mem) md -> SINKN (mrestrict (w_H W') mem') md'.
Hypothesis METAI_KEPT : forall `{fx : YK11.FPState} STK sp0 FP ly S (W : world boxb_segs) mem md own ly' S' W' mem' md' k M,
  ajournal boxb_segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  METAI ly (mrestrict (w_H W) mem) M -> METAI ly' (mrestrict (w_H W') mem') M.

(* ---- the facts on the listing's objects at PI_boxb, by computation on fuzz_boxreg.asan-ubsan's segments ---- *)
Lemma boxb_in_rom0 : forall a, 0x10000 <= a < 0x10000 + 0x1efb8 -> in_rom boxb_segs a.
Proof.
  intros a Ha. exists AsanUbsan.AsanUbsan_segment_000. split; [left; reflexivity|].
  split; [vm_compute; reflexivity|].
  match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
  lia.
Qed.

(* The globals' read-only bytes, from the six W_ENTRY_B facts (the addresses are boxb_val's, by computation). *)
Lemma boxb_rom_bytes : forall g, In g LX_GLOB_BYTES -> absn_rom_bytes boxb_segs B (boxb_val (A_OBJ (fst g))) (snd g).
Proof.
  intros g Hg. unfold LX_GLOB_BYTES in Hg. cbn [In] in Hg.
  destruct Hg as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [fst snd];
    match goal with |- context [boxb_val ?o] =>
      let v := eval vm_compute in (boxb_val o) in change (boxb_val o) with v end.
  - exact ROMB_ZERO.
  - exact (proj1 ROMS_E5).
  - exact ROMB_MACB.
  - exact ROMB_FMT.
  - exact (proj1 ROMS_E11).
Qed.

(* Every byte of [0x20cc0, 0x20d68) (the five globals' slots) is a byte of the image. *)
Definition boxb_rom_some_chk : bool :=
  forallb (fun k => match seg_rom boxb_segs (Z_to_bv 64 (0x20cc0 + Z.of_nat k)) with Some _ => true | None => false end)
    (seq 0 168).
Lemma boxb_rom_some : forall a, 0x20cc0 <= a < 0x20d68 -> seg_rom boxb_segs (Z_to_bv 64 a) <> None.
Proof.
  intros a Ha. assert (H : boxb_rom_some_chk = true) by (vm_compute; reflexivity).
  unfold boxb_rom_some_chk in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - 0x20cc0)) ltac:(apply in_seq; lia)).
  replace (0x20cc0 + Z.of_nat (Z.to_nat (a - 0x20cc0))) with a in H by lia.
  destruct (seg_rom boxb_segs (Z_to_bv 64 a)); [discriminate | discriminate H].
Qed.

(* "%s" with its NUL: the bytes from ROMB_FMT, the rest of the NUL's 8-byte word bytes of the image. *)
Lemma boxb_rom_fmt : absn_rom_str boxb_segs B (boxb_val (A_OBJ 10)) [37; 115].
Proof.
  match goal with |- context [boxb_val ?o] =>
    let v := eval vm_compute in (boxb_val o) in change (boxb_val o) with v end.
  split; [exact ROMB_FMT|].
  intros a Ha.
  assert (Hwe : absn_word_end 0x20d40 (Z.of_nat (length [37; 115])) = 0x20d48) by reflexivity.
  rewrite Hwe in Ha. change (Z.of_nat (length [37; 115])) with 2 in Ha.
  split; [apply boxb_in_rom0; lia | apply boxb_rom_some; lia].
Qed.

(* Each global starts a 32-byte slot and lies 64 bytes or more inside the image's read range. *)
Definition boxb_globs_place_chk : bool :=
  forallb (fun g => let a := boxb_val (A_OBJ (fst g)) in
    (a mod 32 =? 0) && (IMG_LO + 64 <=? a) && (a + snd g + 64 <=? IMG_HI)) LX_GLOBS.
Lemma boxb_globs_place : forall g, In g LX_GLOBS ->
  boxb_val (A_OBJ (fst g)) mod 32 = 0 /\
  (IMG_LO + 64 <= boxb_val (A_OBJ (fst g)) /\ boxb_val (A_OBJ (fst g)) + snd g + 64 <= IMG_HI).
Proof.
  intros g Hg. assert (H : boxb_globs_place_chk = true) by (vm_compute; reflexivity).
  unfold boxb_globs_place_chk in H. rewrite forallb_forall in H. specialize (H g Hg). cbv beta in H.
  apply andb_prop in H as [H12 H3]. apply andb_prop in H12 as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. split; [exact H1 | split; [exact H2 | exact H3]].
Qed.

(* The hypothesis record of the walk at PI_boxb: the Section hypotheses and the object facts above. *)
Lemma lx_hyps_boxb `{fx : YK11.FPState} : @lx_hyps fx rc SK PI_boxb B MT.
Proof.
  constructor.
  - exact LAWS.
  - exact TL.
  - exact TLF.
  - constructor.
    all: try change (@pa_val _ boxb_listing PI_boxb) with boxb_val.
    all: try change (@pa_segs _ boxb_listing PI_boxb) with boxb_segs.
    + exact GCELLS.
    + intros g Hg. exact (proj1 (boxb_globs_place g Hg)).
    + intros g Hg. exact (proj2 (boxb_globs_place g Hg)).
    + vm_compute. discriminate.
    + exact PINNED.
    + exact boxb_rom_bytes.
    + split; [|split].
      * change (boxb_val (A_OBJ 5)) with 0x20ce0. exact ROMS_E5.
      * change (boxb_val (A_OBJ 11)) with 0x20d60. exact ROMS_E11.
      * exact boxb_rom_fmt.
    + exact ISV.
    + exact ROMB_MCH.
  - exact ML.
  - exact MTL.
  - exact MTFL.
  - exact ASM3.
  - exact SMP.
  - exact ASF.
  - exact FFL.
  - exact AMALLOC4.
  - exact AFREE4.
  - exact AMEMCPY.
  - exact ABCMP.
  - exact ASTRNCMP.
  - exact ASETSH.
  - exact TINIT.
  - exact TCHECK.
  - exact TREADMAC.
  - exact TREADNAME.
  - exact TRANGEFREE.
  - exact TFIND.
  - exact TDECLARE.
  - exact TADD.
  - exact TSETNAME.
  - exact RNTRACE.
Qed.

(* The post-condition of the walk relative to the entry's FP state fx0: the end configuration is at some fxe that
   the calls of the snprintf wrapper (inside declare / set_name) reached from fx0 (BoxBLxDefs.v lx_fxr). *)
Definition lx_postE (fx0 : YK11.FPState) : lxcx -> world boxb_segs -> config -> Prop :=
  fun cx W c => exists fxe : YK11.FPState, lx_fxr fx0 fxe /\ @lx_post fxe rc SK PI_boxb B MT cx W c.

(* The exit phase, at any FP state the run reached from fx0. *)
Lemma lx_exitE : forall fx0 fx : YK11.FPState, lx_fxr fx0 fx ->
  lx_from B MT (lx_postE fx0) (LI_X (fx := fx) (PI := PI_boxb) B MT).
Proof.
  intros fx0 fx Hfx.
  apply (lx_from_mono B MT (@lx_post fx rc SK PI_boxb B MT) (lx_postE fx0)).
  - intros cx W c HP. exists fx. split; [exact Hfx | exact HP].
  - exact (@lx_exit fx rc SK PI_boxb B MT (@lx_hyps_boxb fx)).
Qed.

(* The whole walk, from the function's first slot to its post-condition, from an entry FP state with rounding mode 0
   (tbfib_lib_pre_x's last conjunct; the declare / set_name specs take it at each call, lx_fxr_rm0). *)
Lemma lx_all_fx (fx0 : YK11.FPState) : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx0)) 5) 7 = 0 ->
  @lx_start fx0 rc PI_boxb B MT (lx_postE fx0).
Proof.
  intros HRM0.
  apply (@lx_entry fx0 rc SK PI_boxb B MT (@lx_hyps_boxb fx0)).
  refine (lx_loop B MT (lx_postE fx0) fx0 _ _ _ fx0 0 (lx_fxr_refl fx0)).
  - intros fx i Hfx HT. exact (@lx_top fx rc SK PI_boxb B MT (@lx_hyps_boxb fx) _ i (lx_exitE fx0 fx Hfx) HT).
  - intros fx c i Hfx Hc HK.
    assert (c = 0 \/ c = 1 \/ c = 2 \/ c = 3) as [-> | [-> | [-> | ->]]] by lia.
    + exact (@lx_case0 fx rc SK PI_boxb B MT (fun fx' => @lx_hyps_boxb fx') _ i (lx_fxr_rm0 fx0 fx HRM0 Hfx) HK).
    + exact (@lx_case1 fx rc SK PI_boxb B MT (@lx_hyps_boxb fx) _ i (HK fx (lx_fxr_refl fx))).
    + exact (@lx_case2 fx rc SK PI_boxb B MT (@lx_hyps_boxb fx) _ i (HK fx (lx_fxr_refl fx))).
    + exact (@lx_case3 fx rc SK PI_boxb B MT (fun fx' => @lx_hyps_boxb fx') _ i (lx_fxr_rm0 fx0 fx HRM0 Hfx) HK).
  - intros fx i Hfx HJ. exact (@lx_join fx rc SK PI_boxb B MT (@lx_hyps_boxb fx) _ i (lx_exitE fx0 fx Hfx) HJ).
Qed.

Theorem pb_bllvmf_libx : @tbfib_lib_contract_x_all rc box_shape SK B MT XM_LIB XN_LIB RLO RHI SINKN METAI.
Proof.
  intros fx ly S W regs mem md p n pl M K HAI HPRE HK.
  destruct HPRE as (HFN & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK
    & HRM0).
  pose proof (@MTL fx) as MTLf.
  set (cx := @mkLXCX rc PI_boxb ly S W regs mem md p pl (XM_LIB n)).
  assert (HB : @lx_base rc PI_boxb B MT cx).
  { unfold lx_base, cx, lc_n, lsp0, lch. cbn [lc_ly lc_S lc_W lc_regs lc_mem lc_md lc_p lc_pl lc_T].
    rewrite <- Hnpl.
    split; [exact HFN|]. split; [exact Hp|]. split; [exact Hn|].
    split; [destruct Hpn as [[Hn0 Hp0] | Hblk];
            [left; split; [exact Hn0 | rewrite Hp0; unfold AB_EMPTY; lia] | right; exact Hblk]|].
    split; [exact HPL|]. split; [exact Hfr|]. split; [exact Hev|]. split; [exact Hlive|].
    split; [exact (HRO _ HROS)|].
    split; [exact HMOK|]. split; [exact (proj1 (HXL n))|].
    intros pcf regsT Hsite. exact (HTR ly regs regsT pcf Hra Hsite). }
  change (LIBK pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
  apply (SRr_srealizes boxb_segs W (cfg_at boxb_segs AB_LLVMF regs mem md) (lx_postE fx cx)).
  - exact (lx_all_fx fx HRM0 cx HB).
  - exact HAI.
  - intros W' c' Hwle HAI' HPOST.
    destruct HPOST as (fxe & [Hfr10 Hcsr] & ly' & S' & regs' & mem' & md' & k & Ec & HJ & Hk & HPR & Ha0 & HPerm & HMLE & HFkeep).
    cbn [cx lc_ly lc_S lc_W lc_regs lc_mem lc_md lc_p lc_pl lc_T lsp0] in Ec, HJ, HPR, HPerm, HMLE, HFkeep.
    destruct (@lx_journal_io rc SK PI_boxb B LX_STK (spZ regs) ly S W mem md [] ly' S' W' mem' md' k HJ)
      as [Efds Efs].
    apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
    exists fxe, ly', S', regs', mem', md', k.
    split.
    { rewrite Ec. unfold cfg_at. f_equal. f_equal.
      unfold w64. rewrite <- Hra. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
    split; [exact Hfr10|]. split; [exact Hcsr|].
    unfold tbfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
    split; [exact (@lx_journal_fp rc SK PI_boxb B LX_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k HJ)|].
    split; [exact Hk|]. split; [exact HPR|]. split; [exact Ha0|]. split; [exact HPerm|].
    split; [intros fd; rewrite Efds; reflexivity|].
    split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
    split; [exact (@SINKN_KEPT fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ sink_closed_nil HSNK)|].
    split; [exact (@METAI_KEPT fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM)|].
    split; [exact (mle_weaken MT S S' (XM_LIB n) (XN_LIB n) MTLf HMLE (proj2 (HXL n)))|].
    intros i Hi. apply HFkeep. unfold lc_n. cbn [cx lc_pl]. lia.
Qed.
End h.

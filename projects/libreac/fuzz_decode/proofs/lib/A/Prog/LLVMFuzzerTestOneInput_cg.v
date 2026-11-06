(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACfn.v for libreac/fuzz_decode's ASan build (statements only): A_LLVMF at fuzz_decode's listing, RA_LLVMF / A_EMPTY and the core names not yet on the unit as Section Variables, the float-state return of lib/YL0g.v, the runtime cells as constant cells of the asyms record, the read-only image view in the pre, and the walk's statement over its callee contracts; module paths changed. *)
(* LLVMFuzzerTestOneInput_cg: the slot contract of fuzz_decode.asan's LLVMFuzzerTestOneInput (decode_text of
   lib/A/Prog/DecodeAddr.v, AF_LLVMFuzzerTestOneInput = 0 of lib/A/Prog/DecodeList.v), as STATEMENTS only (no proof).
   It is cgif_file_fuzzer's tfib_lib_contract_x (origin/ossv/recipes c8557374ad2e,
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfn.v:33-71) instantiated at fuzz_decode's names, with two changes:
   - check_round_trip, which this function calls, writes float registers (its own float code and its callee
     reac_braid_encode), so the return configuration is cgif's exists-fx' form with the rounding mode kept zero, and
     the entry asks a zero rounding mode (cgif lib/YL0g.v:58-64 lib_contract);
   - the walk's statement asks the runtime cells the program leaves read (asan_cells) as constant cells of B
     (check_round_trip_cg.v dec_crt_cells), which AR keeps at every state, as cgif keeps its own (lib/A/AF0m.v:28).
   Everything else is ACfn.v's text.

   Core definitions not yet on fuzz_decode are Section Variables named and typed as cgif_file_fuzzer names them; the
   driver's two addresses RA_LLVMF and A_EMPTY (ACfn.v:21-22 Definitions) are Section Variables too, to be fixed from
   fuzz_decode's own image by the driver's relocation. Measured in the original images (target_run's
   `jal LLVMFuzzerTestOneInput` + 4, and oft_aligned_copy.empty = target_run.initialized + 16): image A 0x7ff60 /
   0x5d3420, image B 0x7ffac / 0x5d39a0. Every sink_head / lib_shape / FPState instance is passed explicitly, and the
   plain build's global instances are removed below so that none can be inferred. *)
From Stdlib Require Import ZArith NArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr DecodeList check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require reac_frame_is_reac_cg reac_frame_clean_len_cg
  reac_frame_counter_cg reac_frame_inspect_cg reac_decode_cg reac_decode_plain_le_cg reac_upstream_channels_cg
  reac_upstream_decode_cg check_braid_cg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module DShape := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.DecodeShape.
Module DImg := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Img0.
Module DCells := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AsanCells.
Module DMem := OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib.Mem.
Module LIsReac := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_is_reac_cg.
Module LCleanLen := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_clean_len_cg.
Module LCounter := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_counter_cg.
Module LInspect := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_cg.
Module LDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_cg.
Module LPlainLe := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_plain_le_cg.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_channels_cg.
Module LUpDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_upstream_decode_cg.
Module LCheckBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.check_braid_cg.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ACfn.v:20, :23-25 at fuzz_decode's names. *)
Definition DEC_A_LLVMF : Z := decode_text + AF_LLVMFuzzerTestOneInput.
Definition DEC_EV_LIB : Z := 2000.
Definition DEC_LIVE_LIB : Z := 2 ^ 33.
Definition DEC_LLVMF_STK : Z := 32768.

(* The nine runtime cells of asan_cells (lib/A/AsanCells.v:55-65) that live in the file: the seven GOT words and
   real_memcpy / real_memset (.data). Their stated values are fuzz_decode.asan's own bytes. The other eight are .bss
   (image value 0) and are set by start-up or never written (see dec_lib_pre_x). *)
Definition dec_img_bytes (a : Z) (n : nat) : list (option Z) :=
  map (fun i => option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom DImg.rsegs (DMem.wa (a + Z.of_nat i))))
    (seq 0 n).
Definition dec_cell_bytes (bs : list byte) : list (option Z) := map (fun b : byte => Some (bv_unsigned b)) bs.
Lemma dec_asan_cells_file :
  dec_img_bytes DCells.GOT_CELL_K 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.CELL_K)) /\
  dec_img_bytes DCells.GOT_UAR 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.UAR)) /\
  dec_img_bytes DCells.GOT_REPLACE 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.REPLACE)) /\
  dec_img_bytes DCells.GOT_HIEND 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.HIEND)) /\
  dec_img_bytes DCells.GOT_MIDBEG 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.MIDBEG)) /\
  dec_img_bytes DCells.GOT_MIDEND 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.MIDEND)) /\
  dec_img_bytes DCells.GOT_REAL_MEMSET 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.REAL_MEMSET)) /\
  dec_img_bytes DCells.REAL_MEMCPY 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.MUSL_MEMCPY)) /\
  dec_img_bytes DCells.REAL_MEMSET 8 = dec_cell_bytes (DMem.le8 (DMem.wa DCells.MUSL_MEMSET)).
Proof. repeat split; vm_compute; reflexivity. Qed.

(* The sink names (asink_syms, tfib_K, asink_none, ameta_inv, asink_img_laws) are a Theorem Labs lane's sink form,
   a working branch 4d244de18f0 (in pg-core c8e8b0fa5ec): its astdio_env (lib/Reusable/YE00.v:103) asks no string
   bytes, which are only in asink_strs (:108, for the file-output arm). cgif's own lib/YE00.v:100-106 astdio_env asks the
   sink's path, mode, "rwa" and trailer strings, which neither fuzz_decode image holds (a Theorem Labs lane, 2026-10-28 23:46Z), so
   cgif's asink_none in this pre would leave it unsatisfiable. *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Local Abbreviation tfib_sink_head := dec_A_sink_head.        (* cgif lib/A/AE2k.v:44 at fuzz_decode's own sink head *)
Variable asink_syms : Type.                                    (* a Theorem Labs lane's lib/Reusable/YE00.v:32 Record asink_syms *)
Variable tfib_K : asink_syms.                                  (* a Theorem Labs lane's lib/A/AE2k.v:43 form, at fuzz_decode's cells *)
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.  (* a Theorem Labs lane's lib/Reusable/YE00.v:125 *)
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.  (* a Theorem Labs lane's lib/Reusable/YE01.v:141 *)
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.  (* a Theorem Labs lane's lib/Reusable/YE01.v:190 *)
Variables RA_LLVMF A_EMPTY : Z.                                (* cgif lib/A/ACfn.v:21-22 *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* ACfn.v:33-46 and the zero rounding mode of YL0g.v:58.
   With them, the read-only image view rom_view (YG0d.v:382), an entry fact as cgif's amemchr0_realizes carries it
   (YG0d.v:394); the journal's image clause (YCbq.v:362) keeps it to every call outside the owned statics and errno,
   which the read-only reads avoid by check_round_trip_cg.v's dec_ro_rd_scoped. *)
Definition dec_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) : Prop :=
  @afn_pre rc segs B DEC_LLVMF_STK ly S W regs mem md [] /\
  raZ regs = RA_LLVMF /\
  YK11.getr regs 10 = w64 p /\ YK11.getr regs 11 = w64 n /\
  ((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
  n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
  frames S = [] /\ st_nev S + DEC_EV_LIB <= EV_MAX /\ blocks_bytes S + DEC_LIVE_LIB <= LIVE_MAX /\
  arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
  rom_view segs W mem /\
  asink_none segs tfib_K (rd W mem) md /\
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
  Fs.fs_sorted (m_fs md) = true /\
  ameta_inv segs tfib_K ly (rd W mem) M /\
  mo_ok MT S (XM_LIB n) /\
  frm_zero (@fp_csr fx).

(* ACfn.v:47-58. *)
Definition dec_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (p n : Z) (M : Z) (l : lleaf)
    (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (md' : Model) (k : Z) : Prop :=
  @ajournal rc tfib_sink_head segs B DEC_LLVMF_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' k /\
  k <= DEC_EV_LIB /\
  aregs_preserved regs regs' /\ YK11.getr regs' 10 = w64 0 /\
  Permutation (ablocks B ly' S') (ablocks B ly S) /\
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
  m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  asink_none segs tfib_K (rd W' mem') md' /\
  ameta_inv segs tfib_K ly' (rd W' mem') M /\
  mo_le MT S S' (XN_LIB n) /\
  (forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).

(* ACfn.v:59-69; the return configuration in YL0g.v:60-62's exists-fx' form. *)
Definition dec_lib_contract_x : Prop :=
  forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
    AI segs (w_H W) (w_A W) md ->
    dec_lib_pre_x regs ly S W mem md p n pl M ->
    (forall (l : lleaf) (W' : world segs) (c' : config),
       wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
       (exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
          c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          dec_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
       srealizes segs c' (K l)) ->
    srealizes segs (@cfg_at fx segs DEC_A_LLVMF regs mem md) (@LIBK LS pl (m_fs md) K).
End a.

(* ACfn.v:71. *)
Definition dec_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape}
    (asink_syms : Type) (tfib_K : asink_syms)
    (asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop)
    (ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop)
    (arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop)
    (RA_LLVMF A_EMPTY : Z) (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
  forall fx : YK11.FPState,
    @dec_lib_contract_x fx rc LS asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY
      B MT XM_LIB XN_LIB RLO RHI.

(* The return addresses of this function's calls of check_round_trip, malloc and free, as offsets from its entry (the
   jal is 4 bytes before): check_round_trip at +0x5b4 and +0x974; malloc at +0x230, +0x3bc and +0x7c0; free at +0x738,
   +0x990 and +0x998. *)
Definition DEC_LLVMF_RA_CRT : list Z := map (fun o => DEC_A_LLVMF + o) [0x5b8; 0x978].
Definition DEC_LLVMF_RA_MALLOC : list Z := map (fun o => DEC_A_LLVMF + o) [0x234; 0x3c0; 0x7c4].
Definition DEC_LLVMF_RA_FREE : list Z := map (fun o => DEC_A_LLVMF + o) [0x73c; 0x994; 0x99c].

(* The statement the walk (cgif's lib/A/ACfj.v:84-260 composition, at fuzz_decode's callees) will prove: the callee
   contracts give the slot, at the unit's shape decode_shape and with XL as both meter bounds (ACfj.v:258). *)
Section h. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := dec_A_sink_head.        (* cgif lib/A/AE2k.v:44 at fuzz_decode's own sink head *)
Variable asink_syms : Type.                                    (* a Theorem Labs lane's lib/Reusable/YE00.v:32 *)
Variable tfib_K : asink_syms.                                  (* a Theorem Labs lane's lib/A/AE2k.v:43 form, at fuzz_decode's cells *)
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.  (* a Theorem Labs lane's lib/Reusable/YE00.v:125 *)
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.  (* a Theorem Labs lane's lib/Reusable/YE01.v:141 *)
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.  (* a Theorem Labs lane's lib/Reusable/YE01.v:190 *)
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.  (* a Theorem Labs lane's lib/Reusable/YE01.v:28, at SK := tfib_sink_head *)
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.        (* cgif lib/YC20.v:49, at SK := tfib_sink_head *)
Variables RA_LLVMF A_EMPTY : Z.                                (* cgif lib/A/ACfn.v:21-22 *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The frame-pointer chain at this function's calls. It sets s0 to its entry sp at +0x3c (`addi s0, sp, 224`) and
   keeps it until the epilogue; the frame record below s0 holds RA_LLVMF and the caller's s0, whose chain is empty by
   the entry premise (afn_pre ... [] in dec_lib_pre_x). So the chain's return addresses are [RA_LLVMF], or [] when s0
   lies within 16 bytes of ly_top (YCbq.v:218 achain, YG0d.v:218 chain_pre): cgif's pattern in lib/A/ACej.v:26-46
   (CTX_read_frameconfig, TRACES_LLVMFuzzerTestOneInput). The contexts of the two check_round_trip calls are therefore
   their return address followed by one of these (cgif lib/A/ACej.v CTX_* lists, which ACfj.v uses). *)
Definition CTX_check_round_trip : list (list Z) := flat_map (fun r => [[r]; [r; RA_LLVMF]]) DEC_LLVMF_RA_CRT.
(* The traces of this function's own malloc and free calls, which the call rules ask to be in the trace universe
   (YC5d.v:66, :86); cgif's TfibLib record fixes the universe (lib/A/ACeh.v tl_universe), decode's is not yet fixed. *)
(* pc_malloc_ra0 / pc_free_ra0 of B are the long-branch values of image A, 0x52204 / 0x520a4 (a Theorem Labs lane's audit rows
   T1-T12). *)
Definition dec_llvmf_utraces : Prop :=
  forall sp, In sp [[]; [RA_LLVMF]] ->
    (forall r, In r DEC_LLVMF_RA_MALLOC -> In (dec_utrace (pc_malloc_ra0 (as_code B)) (r :: sp)) (as_universe B)) /\
    (forall r, In r DEC_LLVMF_RA_FREE -> In (dec_utrace (pc_free_ra0 (as_code B)) (r :: sp)) (as_universe B)).

(* The meter of one call at input length n: the payload copy (at most n bytes), the decode buffer (at most
   127 * 127 * 3 bytes), the upstream buffer (at most 40 * 12 * 3 bytes), their three frees, and at most two calls of
   check_round_trip at their largest geometry (4 * 480, 8 * 127 and 3 * 480 bytes, three frees). *)
Definition dec_crt_cost_max : Z :=
  mo_malloc MT 1920 + mo_malloc MT 1016 + mo_malloc MT 1440 + (mo_free MT + mo_free MT + mo_free MT).
Definition dec_llvmf_cost (n : Z) : Z :=
  mo_malloc MT n + mo_malloc MT 48387 + mo_malloc MT 1440 + (mo_free MT + mo_free MT + mo_free MT) +
  (dec_crt_cost_max + dec_crt_cost_max).

Definition dec_llvmf_holds_stmt : Prop :=
  (* The code addresses of the call rules (cgif's PALib form, lib/YC1f.v:309-310) and of the class-0 stack malloc
     (astack_malloc_realizes at pc_stack_malloc, YG0d.v:290); memset, memcpy, bcmp and calloc take the listing's
     address directly. *)
  pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = decode_sigma DS___interceptor_trampoline_free ->
  pc_stack_malloc (as_code B) 0 = decode_sigma DS___asan_stack_malloc_0 ->
  dec_crt_cells B ->
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  dec_llvmf_utraces ->
  AR_laws segs B -> model_laws (as_universe B) -> ameter_laws MT -> ameter_fs_laws MT ->
  stack_malloc_progressP B -> astack_free_law segs B -> frame_flag_lawP segs B ->
  asink_img_laws segs B tfib_K ->
  (* HSINK_KEPT / HMETA_KEPT: cgif's asink_none_kept / ameta_inv_kept (used at lib/A/ACfj.v:193 / :199) specialised
     to one journal step; discharged by asink_none_kept / ameta_inv_kept of the Theorem Labs lane asink_img_laws record
     (lib/Reusable/YE01.v:28) when the core lands. *)
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ~ YI16.sink_open_fp FP ->
     asink_none segs tfib_K (rd W0 mem0) md0 -> asink_none segs tfib_K (rd W' mem') md') ->
  (forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
     @ajournal rc tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
     ameta_inv segs tfib_K ly (rd W0 mem0) M -> ameta_inv segs tfib_K ly' (rd W' mem') M) ->
  ro_below_ofl segs RLO RHI ->
  (* class 0 (a0 = 64 at +0x6c, the call at +0x70): the cgif-AR walk of record, a Theorem Labs lane's
     lib/A/Rt/StackMalloc0.v:513 stack_malloc0_contract (a working branch 5251b347350), relocated to fuzz_decode
     with the core. *)
  (forall fx : YK11.FPState, @astack_malloc_realizes fx rc segs B 0) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decode_sigma DS___asan_memset)) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (decode_sigma DS___asan_memcpy)) ->
  (forall fx : YK11.FPState, @amalloc04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @afree04_rule fx rc tfib_sink_head segs B MT) ->
  (forall fx : YK11.FPState, @abcmp_realizes fx rc segs B (decode_sigma DS___interceptor_trampoline_bcmp)) ->
  (forall fx : YK11.FPState,
     @dec_check_round_trip_cg fx rc B MT (decode_sigma DS_check_round_trip) CTX_check_round_trip) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LIsReac.dec_reac_frame_is_reac_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCleanLen.dec_reac_frame_clean_len_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCounter.dec_reac_frame_counter_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LInspect.dec_reac_frame_inspect_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LDecode.dec_reac_decode_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LUpChannels.dec_reac_upstream_channels_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LUpDecode.dec_reac_upstream_decode_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx) ->
  (forall n, 0 <= n -> dec_llvmf_cost n <= XL n) ->
  @dec_lib_contract_x_all rc DShape.decode_shape asink_syms tfib_K asink_none ameta_inv arodata_okS
    RA_LLVMF A_EMPTY B MT XL XL RLO RHI.
End h.

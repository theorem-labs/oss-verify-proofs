(* fs program part, statement base over fs.asan-ubsan (build B): the same names as lib/A/FSH_Base.v at this build's
   numerals. Only what carries B numerals is here; the image-generic half is lib/A/FSH_Gen.v (FSH_Fn_FORM.md section 0).
   Definitions only (rule 24: no function proved).
   B differs from A in code layout: fuzz/alloc.c's own() and preset_file.c's skip_ws are out of line (43 target
   functions), several frames differ, and the UBSan checks trap inline (no __ubsan_* call in target code: the callee list
   of fsh_base_measure.asan-ubsan.txt has none). The .rodata strings and formats sit at the same addresses as in A.
   Every numeral is MEASURED from the unstripped twin
   (internal path) (its PT_LOAD contents equal the
   pinned fs.asan-ubsan's, sha256 5ac5ce09..., except 24 bytes at 0x10028..0x102ca: the ELF header's e_shoff / e_shnum /
   e_shstrndx and the .note.gnu.build-id descriptor; no numeral below lies there) by `python3 (internal path) <twin>`
   (output (internal path)), each from B's own symbol table and disassembly, not by mapping A's:
   "sym X" = X's .symtab st_value (`readelf -sW`), "sec X" = sh_addr / sh_size (`readelf -SW`), "dis" = the instruction.
   Ported from: lib/A/FSH_Base.v (this branch), itself a Theorem Labs lane's FMH_Base.v (a working branch e48bf3cce32 .. a1902517c68). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20 FSH_Gen.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- fs.asan-ubsan: the harness entry and its driver context ---- *)
Definition FS_LLVMF : Z := 0x80f8c.        (* sym LLVMFuzzerTestOneInput *)
Definition FS_RA_LLVMF : Z := 0x80e88.     (* dis: target_run (sym 0x80dbc) `jal` LLVMFuzzerTestOneInput at 0x80e84 *)
Definition FS_EMPTY : Z := 0x5daaa0.       (* sym oft_aligned_copy.empty *)
(* relro: .data.rel.ro start .. .got end (sec .data.rel.ro 0x9f6b0 +0x500; sec .got 0x9fbb0 +0xd58) *)
Definition FS_RLO : Z := 0x9f6b0.
Definition FS_RHI : Z := 0xa0908.

(* ---- fs.asan-ubsan: the 43 target functions (T: rows of FsBinMatch.data/fs-functions.asan-ubsan.tsv), each sym <name> ---- *)
(* LLVMFuzzerTestOneInput is FS_LLVMF above (the name A_LLVMF is the core's, A/ACfn.v:20) *)
Definition A_check_no_overread : Z := 0x8124c.
Definition A_check_bounded_alloc : Z := 0x81618.
Definition A_check_as_written : Z := 0x8164c.
Definition A_check_reject_clean : Z := 0x81b5c.
Definition A_check_round_trip : Z := 0x81b9c.
Definition A_check_reject_clean_starved : Z := 0x82670.
Definition A_past_nul : Z := 0x82894.
Definition A_asan_module_ctor : Z := 0x829f0.
Definition A_asan_module_dtor : Z := 0x82a28.
Definition A_fuzz_malloc : Z := 0x82a58.
Definition A_own : Z := 0x82acc.                       (* B only: alloc.c own() out of line *)
Definition A_fuzz_realloc : Z := 0x82bc4.
Definition A_fuzz_strdup : Z := 0x82d60.
Definition A_fuzz_free : Z := 0x82dbc.
Definition A_fuzz_alloc_live : Z := 0x82eec.
Definition A_fuzz_alloc_peak : Z := 0x82ef8.
Definition A_fuzz_alloc_peak_reset : Z := 0x82f04.
Definition A_fuzz_alloc_fail : Z := 0x82f18.
Definition A_pj_parse : Z := 0x82f3c.
Definition A_parse_value : Z := 0x82fcc.
Definition A_skip_ws : Z := 0x83598.                   (* B only: preset_file.c skip_ws out of line *)
Definition A_pj_free : Z := 0x83674.
Definition A_pj_get : Z := 0x83894.
Definition A_pj_get_str : Z := 0x83a54.
Definition A_pj_set : Z := 0x83adc.
Definition A_grow : Z := 0x83ca8.
Definition A_pj_string : Z := 0x83e58.
Definition A_pj_object : Z := 0x83f1c.
Definition A_pj_write : Z := 0x83f94.
Definition A_write_value : Z := 0x84010.
Definition A_put : Z := 0x8449c.
Definition A_preset_base64_encode : Z := 0x84700.
Definition A_preset_base64_decode : Z := 0x84c4c.
Definition A_parse_items : Z := 0x84e70.
Definition A_parse_string : Z := 0x85534.
Definition A_literal : Z := 0x85b3c.
Definition A_hex4 : Z := 0x85c88.
Definition A_put_utf8 : Z := 0x85d8c.
Definition A_put_string : Z := 0x85fc8.
Definition A_indent : Z := 0x86368.
Definition A_wrap_getenv : Z := 0x863d8.
Definition A_wrap_getpid : Z := 0x863e0.

(* ---- fs.asan-ubsan: runtime entries the target code calls (dis: the jal / j of the 43 functions; sites listed in
   fsh_base_measure.asan-ubsan.txt) ---- *)
Definition PC_strlen : Z := 0x426c4.          (* sym __wrap_strlen -> __interceptor_strlen 0x42754 *)
Definition PC_strcmp : Z := 0x426cc.          (* sym __wrap_strcmp -> __interceptor_strcmp 0x42c80 *)
Definition PC_bcmp : Z := 0x426d8.            (* sym __wrap_bcmp *)
Definition PC_memchr : Z := 0x426dc.          (* sym __wrap_memchr -> __interceptor_memchr 0x43ea0 *)
Definition PC_snprintf : Z := 0x42704.        (* sym __wrap_snprintf -> __interceptor_snprintf 0x45fb8 *)
Definition PC_memcpy : Z := 0x51d90.          (* sym __asan_memcpy *)
Definition PC_memset : Z := 0x5222c.          (* sym __asan_memset *)
Definition PC_free : Z := 0x530e0.            (* sym __wrap_free *)
Definition PC_malloc : Z := 0x530e4.          (* sym __wrap_malloc *)
Definition PC_realloc : Z := 0x530e8.         (* sym __wrap_realloc -> __interceptor_realloc 0x534e4 *)
Definition PC_poison : Z := 0x54904.          (* sym __asan_poison_memory_region (caller: own 0x82b58) *)
Definition PC_unpoison : Z := 0x54aa4.        (* sym __asan_unpoison_memory_region *)
Definition PC_set_shadow_f5 : Z := 0x550a0.   (* sym __asan_set_shadow_f5 *)
Definition PC_stack_malloc_0 : Z := 0x3d4f4.  (* sym __asan_stack_malloc_0 *)
Definition PC_stack_malloc_1 : Z := 0x3d668.  (* sym __asan_stack_malloc_1 *)
Definition PC_stack_malloc_3 : Z := 0x3d7f8.  (* sym __asan_stack_malloc_3 *)
Definition PC_strtod : Z := 0x98b78.          (* sym strtod; caller parse_value 0x83468 *)

(* ---- fs.asan-ubsan: fuzz/alloc.c statics, canary cells, put_string's strings, g_b64 ---- *)
Definition G_FAIL : Z := 0xa41c0.             (* sym g_fail_at, .data, initial ff..ff *)
Definition G_LIVE : Z := 0x5daac0.            (* sym g_live *)
Definition G_PEAK : Z := 0x5daae0.            (* sym g_peak *)
Definition G_COUNT : Z := 0x5dab00.           (* sym g_count *)
Definition FS_GOT_canary : Z := 0xa0898.      (* dis: the .got word equal to sym __stack_chk_guard *)
Definition FS_canary : Z := 0x5fb470.         (* sym __stack_chk_guard *)
(* the ASan shadow-offset cell: sym __asan_shadow_memory_dynamic_address 0xa8438 (8 bytes) and the one .got word equal
   to it, 0x9fc10 (unstripped twin, pyelftools). FsShadowSyms as lib/A/FSH_Base.v states it at A's cells (0x9f6f0 /
   0xa7f38, AB1w.v names), here at B's; there is no relocated-core name file for B. *)
Definition FS_GOT_shadow : Z := 0x9fc10.
Definition FS_shadow_cell : Z := 0xa8438.
Definition FsShadowSyms (B : asyms) : Prop :=
  as_got_shadow B = FS_GOT_shadow /\
  as_shadow_cell B = FS_shadow_cell.
Definition FMT_esc_chr : Z := 0x21260.        (* "\\%c" (put_string auipc+addi 0x8613c) *)
Definition FMT_esc_u : Z := 0x212e0.          (* "\\u%04x" (0x8612c) *)
Definition STR_esc_n : Z := 0x21280.          (* "\\n" (0x86124) *)
Definition STR_esc_t : Z := 0x212a0.          (* "\\t" (0x8611c) *)
Definition STR_esc_r : Z := 0x212c0.          (* "\\r" (0x86134) *)
Definition G_B64 : Z := 0x21060.              (* sym g_b64 *)
(* the musl ofl_head cell (symtab `ofl_head` 0x5fbb28, 8 bytes, local object, of the unstripped twin; the pinned file is
   stripped) and build B's sink_head built from it. A plain Definition, not an Instance: B sites pass it with `@`
   (FSH_Gen.v / FSH_Harness.v remove the inferable plain and image-A instances). Image A's is 0x5fb628, AE2k.v's
   tfib_sink_head. *)
Definition FS_OFL_HEAD : Z := 0x5fbb28.
Definition fsB_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := FS_OFL_HEAD |}.
(* the end of the image: the last RW PT_LOAD (p_vaddr 0xa1920 + p_memsz 0x55b3f0 = 0x5fcd10, pinned = unstripped) rounded
   up to the page; the ASan analogue of the plain STRTOD_GLOBALS_TOP *)
Definition FS_IMG_END : Z := 0x5fd000.
Definition FS_IMG_END_SH : Z := FS_IMG_END / 8.
(* RELOC's IMG_TOP (lib/Reusable/YImgTop.v) is the same value: fs.asan-ubsan's last PT_LOAD ends 0x5fcd10 and rounds to
   the same page as fs.asan's 0x5fc810 *)
Lemma FS_IMG_END_is_IMG_TOP : IMG_TOP = FS_IMG_END.
Proof. reflexivity. Qed.
Definition STRTOD_GLOBALS_TOP : Z := 0x5fd000.

(* ---- own real-stack frames (dis; method as lib/A/FSH_Base.v): FRAME_f = prologue (+ 31 + X for the six fake-frame
   functions, whose fallback probe store reaches (re-aligned sp) - 4096, PROBE_f) ---- *)
Definition FRAME_LLVMF : Z := 96 + 31 + 64.                    (* X = 64, class 0 at 0x80ff4 *)
Definition FRAME_check_no_overread : Z := 160 + 31 + 128.      (* X = 128, class 1 at 0x812bc *)
Definition FRAME_check_bounded_alloc : Z := 16.
Definition FRAME_check_as_written : Z := 64.
Definition FRAME_check_reject_clean : Z := 16.
Definition FRAME_check_round_trip : Z := 192 + 31 + 480.       (* X = 480, class 3 at 0x81c10 *)
Definition FRAME_check_reject_clean_starved : Z := 128 + 31 + 64.   (* X = 64, class 0 at 0x826e0 *)
Definition FRAME_past_nul : Z := 64.
Definition FRAME_fuzz_malloc : Z := 16.
Definition FRAME_own : Z := 32.
Definition FRAME_fuzz_realloc : Z := 32.
Definition FRAME_fuzz_strdup : Z := 32.
Definition FRAME_fuzz_free : Z := 32.
Definition FRAME_fuzz_alloc : Z := 0.
Definition FRAME_pj_parse : Z := 48.
Definition FRAME_parse_value : Z := 160 + 31 + 64.             (* X = 64, class 0 at 0x8303c *)
Definition FRAME_skip_ws : Z := 16.
Definition FRAME_pj_free : Z := 128.
Definition FRAME_pj_get : Z := 96.
Definition FRAME_pj_get_str : Z := 16.
Definition FRAME_pj_set : Z := 48.
Definition FRAME_grow : Z := 96.
Definition FRAME_pj_string : Z := 32.
Definition FRAME_pj_object : Z := 32.
Definition FRAME_pj_write : Z := 64.
Definition FRAME_write_value : Z := 192.
Definition FRAME_put : Z := 112.
Definition FRAME_preset_base64_encode : Z := 48.
Definition FRAME_preset_base64_decode : Z := 128.
Definition FRAME_parse_items : Z := 144.
Definition FRAME_parse_string : Z := 144.
Definition FRAME_literal : Z := 80.
Definition FRAME_hex4 : Z := 16.
Definition FRAME_put_utf8 : Z := 16.
Definition FRAME_put_string : Z := 192 + 31 + 64.              (* X = 64, class 0 at 0x86038 *)
Definition FRAME_indent : Z := 32.
Definition PROBE_LLVMF : Z := 96 + 31 + PROBE_PAGE.
Definition PROBE_check_no_overread : Z := 160 + 31 + PROBE_PAGE.
Definition PROBE_check_round_trip : Z := 192 + 31 + PROBE_PAGE.
Definition PROBE_check_reject_clean_starved : Z := 128 + 31 + PROBE_PAGE.
Definition PROBE_parse_value : Z := 160 + 31 + PROBE_PAGE.
Definition PROBE_put_string : Z := 192 + 31 + PROBE_PAGE.

(* ---- STK_f (method as lib/A/FSH_Base.v; B's call graph: fuzz_malloc tail-calls own, fuzz_realloc calls and tail-calls
   own and tail-calls fuzz_malloc, own calls the poison entry, pj_parse / parse_value / parse_items call skip_ws) ---- *)
Definition STK_fuzz_alloc : Z := FRAME_fuzz_alloc.
Definition STK_own : Z := FRAME_own + zmaxl [STK_RT_POISON].
Definition STK_fuzz_malloc : Z := FRAME_fuzz_malloc + zmaxl [STK_RT_ALLOC; STK_own].
Definition STK_fuzz_free : Z := FRAME_fuzz_free + zmaxl [STK_RT_ALLOC; STK_RT_POISON].
Definition STK_fuzz_realloc : Z := FRAME_fuzz_realloc + zmaxl [STK_RT_REALLOC; STK_RT_POISON; STK_fuzz_malloc; STK_own].
Definition STK_fuzz_strdup : Z := FRAME_fuzz_strdup + zmaxl [STK_RT_STR; STK_RT_INTRIN; STK_fuzz_malloc].
Definition STK_past_nul : Z := FRAME_past_nul + zmaxl [STK_RT_ALLOC; STK_RT_INTRIN].
Definition STK_preset_base64_encode : Z := FRAME_preset_base64_encode + zmaxl [STK_fuzz_malloc].
Definition STK_preset_base64_decode : Z :=
  FRAME_preset_base64_decode + zmaxl [STK_RT_STR; STK_fuzz_malloc; STK_fuzz_free].
Definition STK_check_bounded_alloc : Z := FRAME_check_bounded_alloc.
Definition STK_check_reject_clean : Z := FRAME_check_reject_clean + zmaxl [STK_fuzz_alloc].
Definition STK_check_as_written : Z := FRAME_check_as_written + zmaxl [STK_RT_STR; STK_RT_BCMP; STK_RT_ALLOC].
Definition STK_check_no_overread : Z :=
  Z.max PROBE_check_no_overread (FRAME_check_no_overread + zmaxl [STK_RT_FAKE; STK_RT_BCMP; STK_RT_INTRIN;
    STK_RT_ALLOC; STK_past_nul; STK_preset_base64_decode; STK_fuzz_free]).
Definition STK_check_reject_clean_starved : Z :=
  Z.max PROBE_check_reject_clean_starved (FRAME_check_reject_clean_starved + zmaxl [STK_RT_FAKE; STK_fuzz_alloc;
    STK_preset_base64_decode; STK_check_reject_clean; STK_preset_base64_encode]).
Definition STK_skip_ws : Z := FRAME_skip_ws.
Definition STK_hex4 : Z := FRAME_hex4.
Definition STK_put_utf8 : Z := FRAME_put_utf8.
Definition STK_literal : Z := FRAME_literal + zmaxl [STK_RT_STR; STK_RT_BCMP].
Definition STK_parse_string : Z := FRAME_parse_string + zmaxl [STK_fuzz_malloc; STK_hex4; STK_put_utf8; STK_fuzz_free].
Definition STK_pj_get : Z := FRAME_pj_get + zmaxl [STK_RT_STR].
Definition STK_pj_get_str : Z := FRAME_pj_get_str + zmaxl [STK_pj_get].
Definition STK_grow : Z := FRAME_grow + zmaxl [STK_fuzz_realloc].
Definition STK_pj_string : Z := FRAME_pj_string + zmaxl [STK_RT_INTRIN; STK_fuzz_strdup].
Definition STK_pj_object : Z := FRAME_pj_object + zmaxl [STK_RT_INTRIN].
Fixpoint STK_pj_free (m : nat) : Z :=
  FRAME_pj_free + zmaxl [STK_RT_INTRIN; STK_fuzz_free; match m with O => 0 | S m' => STK_pj_free m' end].
Definition STK_pj_set : Z := FRAME_pj_set + zmaxl [STK_RT_INTRIN; STK_pj_get; STK_pj_free 2; STK_grow; STK_fuzz_strdup].
Definition STK_parse_items_of (pv : Z) : Z :=
  FRAME_parse_items + zmaxl [STK_RT_INTRIN; STK_skip_ws; STK_grow; STK_parse_string; pv; STK_fuzz_free].
Fixpoint STK_parse_value (m : nat) : Z :=
  Z.max PROBE_parse_value (FRAME_parse_value + zmaxl [STK_RT_FAKE; STK_RT_INTRIN; STK_RT_STRTOD; STK_skip_ws;
    STK_parse_string; STK_literal; STK_fuzz_malloc;
    match m with O => 0 | S m' => STK_parse_items_of (STK_parse_value m') end]).
Definition STK_parse_items (m : nat) : Z := STK_parse_items_of (STK_parse_value m).
Definition STK_pj_parse : Z := FRAME_pj_parse + zmaxl [STK_RT_INTRIN; STK_parse_value 2; STK_skip_ws; STK_pj_free 2].
Definition STK_put : Z := FRAME_put + zmaxl [STK_RT_INTRIN; STK_fuzz_realloc].
Definition STK_indent : Z := FRAME_indent + zmaxl [STK_put].
Definition STK_put_string : Z :=
  Z.max PROBE_put_string (FRAME_put_string + zmaxl [STK_RT_FAKE; STK_RT_STR; STK_RT_PRINTF; STK_RT_INTRIN; STK_put]).
Fixpoint STK_write_value (m : nat) : Z :=
  FRAME_write_value + zmaxl [STK_RT_STR; STK_put; STK_indent; STK_put_string;
    match m with O => 0 | S m' => STK_write_value m' end].
Definition STK_pj_write : Z := FRAME_pj_write + zmaxl [STK_RT_INTRIN; STK_write_value 2; STK_put; STK_fuzz_free].
Definition STK_check_round_trip : Z :=
  Z.max PROBE_check_round_trip (FRAME_check_round_trip + zmaxl [STK_RT_FAKE; STK_RT_STR; STK_RT_BCMP; STK_RT_ALLOC;
    STK_RT_INTRIN; STK_preset_base64_encode; STK_preset_base64_decode; STK_pj_object; STK_pj_string; STK_pj_set;
    STK_pj_write; STK_pj_parse; STK_pj_get; STK_pj_get_str; STK_fuzz_free; STK_pj_free 2]).
Definition STK_LLVMF : Z :=
  Z.max PROBE_LLVMF (FRAME_LLVMF + zmaxl [STK_RT_FAKE; STK_RT_STR; STK_RT_ALLOC; STK_RT_INTRIN; STK_check_no_overread;
    STK_fuzz_alloc; STK_preset_base64_decode; STK_check_bounded_alloc; STK_check_as_written; STK_check_round_trip;
    STK_check_reject_clean; STK_check_reject_clean_starved; STK_fuzz_free]).

(* the fake-frame functions are the same six as in A (sites above), so FSH_Gen.v's FRL_* apply *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Definition fs_glob (W : world segs) (mem : word -> option byte) (live peak cnt fail : Z) : Prop :=
  fs_glob_at segs G_LIVE G_PEAK G_COUNT G_FAIL W mem live peak cnt fail.
Definition fs_stat (W : world segs) (mem : word -> option byte) (live cnt : Z) : Prop :=
  exists peak, fs_glob W mem live peak cnt SIZE_MAXZ.
Definition str_homeA (ly : alayout) (S : astate) (U : list (Z * Z)) (p n : Z) : Prop :=
  str_homeA_at segs B FS_RLO FS_RHI ly S U p n.
(* cstr_kept is in lib/B/FSH_Rt.v, beside the read-only string table it names *)
Definition fs_canary (W : world segs) (mem : word -> option byte) : Prop := fs_canary_at segs FS_GOT_canary FS_canary W mem.
Definition fpreU (STK : Z) ly S (U : list (Z * Z)) (W : world segs) regs mem md ch : Prop :=
  fpreU_at segs B FS_RLO FS_RHI STK ly S U W regs mem md ch.
Definition fpre (STK : Z) ly S (W : world segs) regs mem md ch : Prop :=
  fpre_at segs B FS_RLO FS_RHI STK ly S W regs mem md ch.
End c.

(* fs program part, statement base over fs.asan: the build's numerals (the 41 target functions, the runtime entries the
   target code calls, the driver call site, the image ranges and cells, the own frames, STK_f) and the names
   instantiated at them (fs_glob, fs_stat, str_homeA, fs_canary, fpre, fpreU; cstr_kept is in FSH_Rt.v, where the
   read-only string table it names lives). The image-generic half
   (wrappers, string premises, runtime contract shapes, source constants) is lib/A/FSH_Gen.v, stated once for both builds;
   lib/B/FSH_Base.v holds the same names over fs.asan-ubsan. Definitions only (rule 24: no function proved).
   Ported from: a Theorem Labs lane's proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Base.v (a working branch e48bf3cce32, with the
   FMH_* text of 706affbdbe6, 3e0aa997be6, 137702429de, a1902517c68); donor proofs/cgif/cgif_file_fuzzer/lib.
   Every numeral is MEASURED from the unstripped twin
   (internal path) (its PT_LOAD contents equal the pinned
   fs.asan's, sha256 64b53ff8..., except 25 bytes at 0x10028..0x102cb: the ELF header's e_shoff / e_shnum / e_shstrndx and
   the .note.gnu.build-id descriptor; no numeral below lies there) by `python3 (internal path) <twin>` (pyelftools +
   capstone 5.0.7; output (internal path)): "sym X" = X's .symtab st_value (the Value column of
   `readelf -sW`), "sec X" = section X's sh_addr / sh_size (`readelf -SW`), "dis" = the named instruction. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AB1w.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- fs.asan: the harness entry and its driver context ---- *)
Definition FS_LLVMF : Z := 0x80f1c.        (* sym LLVMFuzzerTestOneInput *)
Definition FS_RA_LLVMF : Z := 0x80e18.     (* dis: target_run (sym 0x80d4c) `jal` LLVMFuzzerTestOneInput at 0x80e14 *)
Definition FS_EMPTY : Z := 0x5da5a0.       (* sym oft_aligned_copy.empty (fm's FM_EMPTY 0x5d43e0 is the same symbol) *)
(* relro: .data.rel.ro start .. .got end (sec .data.rel.ro 0x9f190 +0x500; sec .got 0x9f690 +0xd58) *)
Definition FS_RLO : Z := 0x9f190.
Definition FS_RHI : Z := 0xa03e8.

(* ---- fs.asan: the 41 target functions (the T: rows of FsBinMatch.data/fs-functions.asan.tsv), each sym <name> ---- *)
(* fuzz_state.c (LLVMFuzzerTestOneInput is FS_LLVMF above: the name A_LLVMF is the core's, A/ACfn.v:20) *)
Definition A_check_no_overread : Z := 0x811c8.
Definition A_check_bounded_alloc : Z := 0x81560.
Definition A_check_as_written : Z := 0x81590.
Definition A_check_reject_clean : Z := 0x81a60.
Definition A_check_round_trip : Z := 0x81a9c.
Definition A_check_reject_clean_starved : Z := 0x82508.
Definition A_past_nul : Z := 0x82728.
Definition A_asan_module_ctor : Z := 0x82844.
Definition A_asan_module_dtor : Z := 0x8287c.
(* fuzz/alloc.c *)
Definition A_fuzz_malloc : Z := 0x828ac.
Definition A_fuzz_realloc : Z := 0x829e8.
Definition A_fuzz_strdup : Z := 0x82ce4.
Definition A_fuzz_free : Z := 0x82d40.
Definition A_fuzz_alloc_live : Z := 0x82e5c.
Definition A_fuzz_alloc_peak : Z := 0x82e68.
Definition A_fuzz_alloc_peak_reset : Z := 0x82e74.
Definition A_fuzz_alloc_fail : Z := 0x82e88.
(* src/preset_file.c *)
Definition A_pj_parse : Z := 0x82eac.
Definition A_parse_value : Z := 0x82f9c.
Definition A_pj_free : Z := 0x83570.
Definition A_pj_get : Z := 0x83720.
Definition A_pj_get_str : Z := 0x83868.
Definition A_pj_set : Z := 0x838e8.
Definition A_grow : Z := 0x83a48.
Definition A_pj_string : Z := 0x83be4.
Definition A_pj_object : Z := 0x83c9c.
Definition A_pj_write : Z := 0x83d08.
Definition A_write_value : Z := 0x83d84.
Definition A_put : Z := 0x8418c.
Definition A_preset_base64_encode : Z := 0x84390.
Definition A_preset_base64_decode : Z := 0x8481c.
Definition A_parse_items : Z := 0x84a04.
Definition A_parse_string : Z := 0x850b8.
Definition A_literal : Z := 0x856cc.
Definition A_hex4 : Z := 0x857f4.
Definition A_put_utf8 : Z := 0x858d0.
Definition A_put_string : Z := 0x85ad8.
Definition A_indent : Z := 0x85e4c.
(* the driver's wrappers (wrap_getenv.c, wrap_getpid.c) *)
Definition A_wrap_getenv : Z := 0x85ebc.
Definition A_wrap_getpid : Z := 0x85ec4.

(* ---- fs.asan: the runtime entries the target code calls (dis: every `jal` / `j` of the 41 functions whose target lies
   outside them; the call sites are listed in fsh_base_measure.asan.txt). The string / memory entries are the
   interceptor trampolines `__wrap_*` (as fm's PC_* are). fs calls no strchr, strncmp, strncasecmp, strstr or isalnum. *)
Definition PC_strlen : Z := 0x42654.          (* sym __wrap_strlen -> __interceptor_strlen 0x426e4 *)
Definition PC_strcmp : Z := 0x4265c.          (* sym __wrap_strcmp -> __interceptor_strcmp 0x42c10 *)
Definition PC_bcmp : Z := 0x42668.            (* sym __wrap_bcmp *)
Definition PC_memchr : Z := 0x4266c.          (* sym __wrap_memchr -> __interceptor_memchr 0x43e30 *)
Definition PC_snprintf : Z := 0x42694.        (* sym __wrap_snprintf -> __interceptor_snprintf 0x45f48 *)
Definition PC_memcpy : Z := 0x51d20.          (* sym __asan_memcpy *)
Definition PC_memset : Z := 0x521bc.          (* sym __asan_memset *)
Definition PC_free : Z := 0x53070.            (* sym __wrap_free *)
Definition PC_malloc : Z := 0x53074.          (* sym __wrap_malloc *)
Definition PC_realloc : Z := 0x53078.         (* sym __wrap_realloc -> __interceptor_realloc 0x53474 *)
Definition PC_poison : Z := 0x54894.          (* sym __asan_poison_memory_region *)
Definition PC_unpoison : Z := 0x54a34.        (* sym __asan_unpoison_memory_region *)
Definition PC_set_shadow_f5 : Z := 0x55030.   (* sym __asan_set_shadow_f5 *)
Definition PC_stack_malloc_0 : Z := 0x3d484.  (* sym __asan_stack_malloc_0 *)
Definition PC_stack_malloc_1 : Z := 0x3d5f8.  (* sym __asan_stack_malloc_1 *)
Definition PC_stack_malloc_3 : Z := 0x3d788.  (* sym __asan_stack_malloc_3 *)
Definition PC_strtod : Z := 0x9865c.          (* sym strtod; its only caller is parse_value 0x8343c *)

(* ---- fs.asan: fuzz/alloc.c statics (alloc.c:30): non-owned program statics, each sym <name> (32-byte asan globals) ---- *)
Definition G_FAIL : Z := 0xa3ca0.             (* g_fail_at, .data, initial bytes ff..ff (SIZE_MAX) *)
Definition G_LIVE : Z := 0x5da5c0.            (* g_live, .bss *)
Definition G_PEAK : Z := 0x5da5e0.            (* g_peak, .bss *)
Definition G_COUNT : Z := 0x5da600.           (* g_count, .bss *)
(* the stack-protector cells musl's printf_core reads (fm FM_GOT_canary / FM_canary): the .got slot holding
   &__stack_chk_guard (dis: the one .got word equal to sym __stack_chk_guard) and sym __stack_chk_guard *)
Definition FS_GOT_canary : Z := 0xa0378.
Definition FS_canary : Z := 0x5faf70.
(* the ASan shadow-offset cell: sym __asan_shadow_memory_dynamic_address 0xa7f38 (8 bytes) and the one .got word equal
   to it, 0x9f6f0 (unstripped twin, pyelftools), in the relocated core's names (lib/A/AB1w.v:594, :605). FsShadowSyms is
   the one named shadow-cell hypothesis of fs's runtime walks, text of a working branch 3210d71ee38
   lib/A/FSstrlen.v:586-588. It is discharged by lib/A/ACeg.v's TfibLib (tl_got_shadow, tl_shadow_cell; A_GOT_shadow
   0x9f6f0, A_shadow_glob 0xa7f38) once lib/A/ACej.v builds. The two numerals are image A's, so it is here and not in
   FSH_Gen.v; lib/B/FSH_Base.v states B's. *)
Definition FsShadowSyms (B : asyms) : Prop :=
  as_got_shadow B = AB1w.tfib_D_GOT_asan_shadow_memory_dynamic_address /\
  as_shadow_cell B = AB1w.tfib_D_asan_shadow_memory_dynamic_address.
(* put_string's escape strings (.rodata; dis: auipc+addi at 0x85c18..0x85c4c, stored at 0x18..0x38(s1); bytes read) *)
Definition FMT_esc_chr : Z := 0x21260.        (* "\\%c", snprintf(esc, 8, ...) for the double quote and '\\' (pf.c:498) *)
Definition FMT_esc_u : Z := 0x212e0.          (* "\\u%04x", snprintf(esc, 8, ...) for the other c < 0x20 (pf.c:506) *)
Definition STR_esc_n : Z := 0x21280.          (* "\\n": __asan_memcpy(esc, ., 3), pf.c:500 compiled to a copy *)
Definition STR_esc_t : Z := 0x212a0.          (* "\\t", pf.c:502 *)
Definition STR_esc_r : Z := 0x212c0.          (* "\\r", pf.c:504 *)
Definition G_B64 : Z := 0x21060.              (* sym g_b64 (65 bytes + redzone), memchr's table in preset_base64_decode *)
(* the musl ofl_head cell: symtab `ofl_head` 0x5fb628 (8 bytes, local object) of the unstripped twin; equal to the value in
   AE2k.v's tfib_sink_head, which A sites pass with `@` (the inferable instances are removed, FSH_Gen.v / FSH_Harness.v) *)
Definition FS_OFL_HEAD : Z := 0x5fb628.
(* the end of fs.asan's image: the last RW PT_LOAD (p_vaddr 0xa1400 + p_memsz 0x55b410 = 0x5fc810, the same program
   header in the pinned and the unstripped file) rounded up to the page. The same value carries RELOC's name IMG_TOP
   (lib/Reusable/YImgTop.v, a Notation the core's bound proofs need as a literal), and the lemma below ties the two. *)
Definition FS_IMG_END : Z := 0x5fd000.
Definition FS_IMG_END_SH : Z := FS_IMG_END / 8.
Lemma FS_IMG_END_is_IMG_TOP : IMG_TOP = FS_IMG_END.
Proof. reflexivity. Qed.
(* the released plain contracts carry strtod_c.STRTOD_GLOBALS_TOP (0x55000, fs.plain's image end 0x54010 page-rounded)
   below the stack window; the ASan analogue is the image end (astk_ok's alloc_ceiling <= ly_stk_lo, YCbq.v:331-333,
   already puts the window above it) *)
Definition STRTOD_GLOBALS_TOP : Z := 0x5fd000.

(* ---- own real-stack frames (dis: prologue `addi sp,sp,-N`; `andi sp,sp,-32` adds at most 31; the six functions with
   an __asan_stack_malloc_* call put their object X on the real stack when it answers NULL: `addi aX,sp,-X`,
   `andi rY,aX,-32`, then a probe loop `sub sp,sp,4096; sd zero,0(sp); blt rY,sp` that stores one word at
   (re-aligned sp) - 4096, then `mv sp,rY`). FRAME_f = the sp drop at f's call sites = N (+ 31 + X). PROBE_f = the
   deepest own store of the six = N + 31 + 4096 (PROBE_PAGE, FSH_Gen.v). STK_f (below) := Z.max PROBE_f (FRAME_f + the most
   a callee needs) for the six, FRAME_f + the most a callee needs for the rest; so LLVMFuzzerTestOneInput's bound is at
   least 4096 + its frame (ENTRY). On the fallback path the six also write their real frame's STACK SHADOW (0xf1 / 0xf8 /
   0xf3 redzones, 0xf5 or 0 at exit), which AR's zero stack shadow (YG0n.v:187-190, 217) does not allow: the fallback is
   live only if __asan_stack_malloc_* answers NULL, i.e. its class is full (YG00.v:569-578); FSH_Fn_FORM.md section 2. ---- *)
Definition FRAME_LLVMF : Z := 96 + 31 + 64.                    (* X = 64, class-0 frame at 0x80f84 *)
Definition FRAME_check_no_overread : Z := 160 + 31 + 128.      (* X = 128, class 1 at 0x81238 *)
Definition FRAME_check_bounded_alloc : Z := 16.
Definition FRAME_check_as_written : Z := 48.
Definition FRAME_check_reject_clean : Z := 16.
Definition FRAME_check_round_trip : Z := 192 + 31 + 480.       (* X = 480, class 3 at 0x81b10 *)
Definition FRAME_check_reject_clean_starved : Z := 128 + 31 + 64.   (* X = 64, class 0 at 0x82578 *)
Definition FRAME_past_nul : Z := 64.
Definition FRAME_fuzz_malloc : Z := 32.
Definition FRAME_fuzz_realloc : Z := 64.
Definition FRAME_fuzz_strdup : Z := 32.
Definition FRAME_fuzz_free : Z := 32.
Definition FRAME_fuzz_alloc : Z := 0.                          (* the four leaf counters: no frame *)
Definition FRAME_pj_parse : Z := 48.
Definition FRAME_parse_value : Z := 160 + 31 + 64.             (* X = 64, class 0 at 0x8300c *)
Definition FRAME_pj_free : Z := 96.
Definition FRAME_pj_get : Z := 80.
Definition FRAME_pj_get_str : Z := 16.
Definition FRAME_pj_set : Z := 48.
Definition FRAME_grow : Z := 80.
Definition FRAME_pj_string : Z := 32.
Definition FRAME_pj_object : Z := 32.
Definition FRAME_pj_write : Z := 64.
Definition FRAME_write_value : Z := 176.
Definition FRAME_put : Z := 112.
Definition FRAME_preset_base64_encode : Z := 32.
Definition FRAME_preset_base64_decode : Z := 112.
Definition FRAME_parse_items : Z := 144.
Definition FRAME_parse_string : Z := 144.
Definition FRAME_literal : Z := 80.
Definition FRAME_hex4 : Z := 16.
Definition FRAME_put_utf8 : Z := 16.
Definition FRAME_put_string : Z := 192 + 31 + 64.              (* X = 64, class 0 at 0x85b48 *)
Definition FRAME_indent : Z := 32.
Definition PROBE_LLVMF : Z := 96 + 31 + PROBE_PAGE.
Definition PROBE_check_no_overread : Z := 160 + 31 + PROBE_PAGE.
Definition PROBE_check_round_trip : Z := 192 + 31 + PROBE_PAGE.
Definition PROBE_check_reject_clean_starved : Z := 128 + 31 + PROBE_PAGE.
Definition PROBE_parse_value : Z := 160 + 31 + PROBE_PAGE.
Definition PROBE_put_string : Z := 192 + 31 + PROBE_PAGE.


(* ---- STK_f: the stack each target function's walk may use below its entry sp (afn_pre STK; donor TNEWGIF_STK style,
   lib/YC20.v:18-42): own frame + the most any callee needs (dis: the call graph in fsh_base_measure.asan.txt; tail calls
   included; the abort / __asan_report_* / __asan_handle_no_return calls are on dead paths and not counted). The three
   recursive functions are level-indexed by m = the recursion levels still below (depth <= 2, FSH_Fn_FORM.md 3b): the
   level-k spec uses STK_<f> (2 - k). ---- *)
Definition STK_fuzz_alloc : Z := FRAME_fuzz_alloc.
Definition STK_fuzz_malloc : Z := FRAME_fuzz_malloc + zmaxl [STK_RT_ALLOC; STK_RT_POISON].
Definition STK_fuzz_free : Z := FRAME_fuzz_free + zmaxl [STK_RT_ALLOC; STK_RT_POISON].
Definition STK_fuzz_realloc : Z := FRAME_fuzz_realloc + zmaxl [STK_RT_REALLOC; STK_RT_POISON; STK_fuzz_malloc].
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
(* reader *)
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
  FRAME_parse_items + zmaxl [STK_RT_INTRIN; STK_grow; STK_parse_string; pv; STK_fuzz_free].
Fixpoint STK_parse_value (m : nat) : Z :=
  Z.max PROBE_parse_value (FRAME_parse_value + zmaxl [STK_RT_FAKE; STK_RT_INTRIN; STK_RT_STRTOD; STK_parse_string;
    STK_literal; STK_fuzz_malloc; match m with O => 0 | S m' => STK_parse_items_of (STK_parse_value m') end]).
Definition STK_parse_items (m : nat) : Z := STK_parse_items_of (STK_parse_value m).
Definition STK_pj_parse : Z := FRAME_pj_parse + zmaxl [STK_RT_INTRIN; STK_parse_value 2; STK_pj_free 2].
(* writer *)
Definition STK_put : Z := FRAME_put + zmaxl [STK_RT_INTRIN; STK_fuzz_realloc].
Definition STK_indent : Z := FRAME_indent + zmaxl [STK_put].
Definition STK_put_string : Z :=
  Z.max PROBE_put_string (FRAME_put_string + zmaxl [STK_RT_FAKE; STK_RT_STR; STK_RT_PRINTF; STK_RT_INTRIN; STK_put]).
Fixpoint STK_write_value (m : nat) : Z :=
  FRAME_write_value + zmaxl [STK_RT_STR; STK_put; STK_indent; STK_put_string;
    match m with O => 0 | S m' => STK_write_value m' end].
Definition STK_pj_write : Z := FRAME_pj_write + zmaxl [STK_RT_INTRIN; STK_write_value 2; STK_put; STK_fuzz_free].
(* the round trip and the entry *)
Definition STK_check_round_trip : Z :=
  Z.max PROBE_check_round_trip (FRAME_check_round_trip + zmaxl [STK_RT_FAKE; STK_RT_STR; STK_RT_BCMP; STK_RT_ALLOC;
    STK_RT_INTRIN; STK_preset_base64_encode; STK_preset_base64_decode; STK_pj_object; STK_pj_string; STK_pj_set;
    STK_pj_write; STK_pj_parse; STK_pj_get; STK_pj_get_str; STK_fuzz_free; STK_pj_free 2]).
(* <= the shared core's LLVMF_STK = 32768 (A/ACfn.v:25) *)
Definition STK_LLVMF : Z :=
  Z.max PROBE_LLVMF (FRAME_LLVMF + zmaxl [STK_RT_FAKE; STK_RT_STR; STK_RT_ALLOC; STK_RT_INTRIN; STK_check_no_overread;
    STK_fuzz_alloc; STK_preset_base64_decode; STK_check_bounded_alloc; STK_check_as_written; STK_check_round_trip;
    STK_check_reject_clean; STK_check_reject_clean_starved; STK_fuzz_free]).

(* ---- the build's fake-frame bound: the six fake-frame functions (dis: the __asan_stack_malloc_* call sites)
   LLVMFuzzerTestOneInput 0x80f84 (class 0), check_no_overread 0x81238 (1), check_reject_clean_starved 0x82578 (0),
   check_round_trip 0x81b10 (3), parse_value 0x8300c (0), put_string 0x85b48 (0): the same in both builds, so the
   FRL_* constants of FSH_Gen.v apply. ---- *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* ---- the names instantiated at fs.asan's numerals (fm FMH_Base.v / FMH_Fn.v spellings) ---- *)
(* fuzz/alloc.c's statics (alloc.c:30): g_live, g_peak, g_count, g_fail_at *)
Definition fs_glob (W : world segs) (mem : word -> option byte) (live peak cnt fail : Z) : Prop :=
  fs_glob_at segs G_LIVE G_PEAK G_COUNT G_FAIL W mem live peak cnt fail.
(* the harness invariant: no reader allocation is set to fail (g_fail_at = SIZE_MAX), g_live = live (fm fm_stat; fs's
   plain omx_GI, Prog/Ledger.v:55-56, has live = 0 and fail = 2^64 - 1 at every call) *)
Definition fs_stat (W : world segs) (mem : word -> option byte) (live cnt : Z) : Prop :=
  exists peak, fs_glob W mem live peak cnt SIZE_MAXZ.
(* where a string the caller keeps across a program call lives, as fs_img_facts' home predicate (FSH_Gen.v
   fs_img_facts_at). The per-string form a spec carries is FSH_Rt.v's cstr_kept, which names the table entry. *)
Definition str_homeA (ly : alayout) (S : astate) (U : list (Z * Z)) (p n : Z) : Prop :=
  str_homeA_at segs B FS_RLO FS_RHI ly S U p n.
(* the stack-protector cells musl's printf_core reads *)
Definition fs_canary (W : world segs) (mem : word -> option byte) : Prop := fs_canary_at segs FS_GOT_canary FS_canary W mem.
(* the per-function premise in U form (primary) and its U = [] form (FSH_Gen.v fpreU_of_pre) *)
Definition fpreU (STK : Z) ly S (U : list (Z * Z)) (W : world segs) regs mem md ch : Prop :=
  fpreU_at segs B FS_RLO FS_RHI STK ly S U W regs mem md ch.
Definition fpre (STK : Z) ly S (W : world segs) regs mem md ch : Prop :=
  fpre_at segs B FS_RLO FS_RHI STK ly S W regs mem md ch.
End c.

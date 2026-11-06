(* fs program part, runtime half over fs.asan: the runtime contracts fs's target code needs beyond the donor's AsanAPI
   (lib/Reusable/YG0d.v:530-545) and FSupoisonU's ARU forms, instantiated at fs.asan's entries; fs's snprintf formats and
   read-only strings; the image facts as one constant fact (fs_img_facts) and the reader-cell discipline (rd_cells).
   The contract shapes are FSH_Gen.v's (generic in pc, stated once for both builds); lib/B/FSH_Rt.v holds the same names
   over fs.asan-ubsan. Statements only.
   Ported from: a Theorem Labs lane's proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Rt.v (a working branch e48bf3cce32: FM_SN_FMTS,
   FmRt) and FMH_Fn.v at 137702429de (FM_RO_STRS, fm_img_facts). fs drops fm's strncmp / strncasecmp / strstr / strchr /
   isalnum entries (not linked or not called: fsh_base_measure.asan.txt callee list) and adds strcmp, memchr with any byte,
   and the "\\%c" / "\\u%04x" formats. Every numeral MEASURED as in FSH_Base.v ((internal path),
   section ".rodata strings the target functions address": auipc + addi pairs in the target code, bytes read). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20 FSH_Gen FSH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonU SetShadowDefU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* fs's snprintf formats (put_string 0x85d04 is the one snprintf call; size 8): "\\%c" for the double quote and '\\' (pf.c:498) and
   "\\u%04x" for the other c < 0x20 (pf.c:506). The bytes at each address are these pieces' fmt_bytes. *)
Definition FS_SN_FMTS : list (Z * list fpiece) :=
  [(FMT_esc_chr, [FLit [92]; FChr]);
   (FMT_esc_u, [FLit [92; 117]; FHex4])].

(* the read-only strings fs's code passes to the reader and the runtime (strlen, strcmp, memchr, memcpy, bcmp), besides
   the formats: the document's keys and values (check_round_trip 0x82130..0x82260), the writer's punctuation and literals
   (write_value, indent, pj_write, put_string), the reader's literals (parse_value: literal (in, "true") ...), put_string's
   memcpy sources, and g_b64's 64 letters (memchr (g_b64, c, 65) in preset_base64_decode). Registered asan globals with
   redzones (.str.N). *)
Definition FS_RO_STRS : list (Z * list Z) :=
  [(0x20ea0, [111; 114; 103; 46; 111; 112; 101; 110; 109; 105; 120; 101; 114; 46; 112; 114; 101; 115; 101; 116; 47; 50]);
                                                              (* "org.openmixer.preset/2" *)
   (0x20ee0, [102; 111; 114; 109; 97; 116]);                   (* "format" *)
   (0x20f00, [115; 116; 97; 116; 101]);                        (* "state" *)
   (0x20f20, [99; 97; 114; 114; 105; 101; 115]);               (* "carries" *)
   (0x20f40, [98; 97; 115; 101; 54; 52]);                      (* "base64" *)
   (0x20f60, [101; 110; 99; 111; 100; 105; 110; 103]);         (* "encoding" *)
   (0x20f80, [112; 114; 101; 115; 101; 116]);                  (* "preset" *)
   (0x20fa0, [99; 111; 110; 116; 101; 120; 116]);              (* "context" *)
   (0x20fc0, [98; 121; 116; 101; 115]);                        (* "bytes" *)
   (0x21020, []);                                              (* "" (pj_string, write_value) *)
   (0x21040, [10]);                                            (* "\n" *)
   (0x210e0, [116; 114; 117; 101]);                            (* "true" *)
   (0x21100, [102; 97; 108; 115; 101]);                        (* "false" *)
   (0x21120, [110; 117; 108; 108]);                            (* "null" *)
   (0x21140, [48]);                                            (* "0" *)
   (0x21160, [123]);                                           (* "{" *)
   (0x21180, [91]);                                            (* "[" *)
   (0x211a0, [44]);                                            (* "," *)
   (0x211c0, [58; 32]);                                        (* ": " *)
   (0x211e0, [58]);                                            (* ":" *)
   (0x21200, [125]);                                           (* "}" *)
   (0x21220, [93]);                                            (* "]" *)
   (0x21240, [34]);                                            (* the double quote, 34 *)
   (0x21300, [32; 32]);                                        (* "  " *)
   (STR_esc_n, [92; 110]);                                     (* "\\n" *)
   (STR_esc_t, [92; 116]);                                     (* "\\t" *)
   (STR_esc_r, [92; 114]);                                     (* "\\r" *)
   (G_B64, map WriterSpec.b64c (map Z.of_nat (seq 0 64)))].    (* g_b64, WriterSpec.b64_table's letters *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* snprintf at fs's formats and stack-protector cells *)
Definition asnprintf_realizes (pc : Z) : Prop := asnprintf_realizes_at segs B FS_SN_FMTS FS_GOT_canary FS_canary pc.

(* the image facts fs's code and runtime calls take, one constant fact about B (fm_img_facts): lanes take it as a Section
   hypothesis; the final instance proves it once for fs's TfibB *)
Definition fs_img_facts : Prop :=
  fs_img_facts_at segs B FS_RLO FS_RHI FS_GOT_canary FS_canary FS_RO_STRS FS_SN_FMTS FS_PSTAT_FP.

(* the reader-cell discipline (the released plain check_round_trip_c.v:43 ReaderRes.rd_cells: ro_agree and the canary
   cells), on the ASan side: rom_view and fs_canary, both given by fs_img_facts at every AR state *)
Definition rd_cells (W : world segs) (mem : word -> option byte) : Prop := rom_view segs W mem /\ fs_canary segs W mem.

(* where a read-only string a caller keeps across a program call lives (a working branch lib/A/FMH_Fn.v:84-86,
   table-arm shape): in a live block, or as a TABLE entry of FS_RO_STRS / FS_SN_FMTS. The generic home predicate
   str_homeA_at (FSH_Gen.v, FSH_Base.str_homeA) stays what fs_img_facts proves; a spec must name the table entry, because
   fs_img_facts re-derives cstr_ok after a call only for table entries, so a generic read-only arm would leave the string
   unusable at the next call (ALLOC a Theorem Labs lane). The FS_SN_FMTS arm is kept though fs's only snprintf call (put_string's
   \u%04x arm) is unreachable on fs's document (plain_bytes, WRITER): it costs nothing and keeps the two tables symmetric.
   The block arm takes the caller's poison set U (the U of its fpreU / fs_heads): the string and its NUL avoid every
   range of U, so no byte of it is a user-poisoned head (shadow 0xf7, where the interceptor would report). A block of
   ablocks carries no mark of whether it has a fuzz head (fuzz_malloc blocks do; past_nul's and check_round_trip's
   __wrap_malloc blocks do not), so a fixed `b + HEAD <= p` would be wrong for the headless ones; U names exactly the
   heads that are poisoned now. *)
Definition cstr_kept (ly : alayout) (S : astate) (U : list (Z * Z)) (p : Z) (l : list Z) : Prop :=
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= p /\ p + Z.of_nat (length l) + 1 <= b + m /\
     forall r, In r U -> p + Z.of_nat (length l) + 1 <= fst r \/ fst r + snd r <= p)
  \/ In (p, l) FS_RO_STRS
  \/ (exists ps, In (p, ps) FS_SN_FMTS /\ l = fmt_bytes ps).

(* the runtime interface fs's walks take beyond the donor's AsanAPI and FSupoisonU (donor AsanAPI style, fm FmRt): each
   in ARU form, since fs calls them while reader heads are poisoned; the U = [] forms follow (FSH_Gen.v *_of_U,
   FSupoisonU.v *_of_U, SetShadowDefU.aset_shadow_realizes_of_U).
   Each entry is this build's PC_* (lib/A/FSH_Base.v, sym of the unstripped twin). The allocator and fake-frame contracts
   (FSupoisonU.amalloc_realizesU / afree_realizesU / astack_malloc_realizesU) take no pc: they enter at pc_wrap_malloc /
   pc_wrap_free / pc_stack_malloc cid of as_code B. Their fields pin that pc to PC_* (first conjunct) beside the contract
   (second conjunct), so a walk at a measured `jal PC_*` rewrites its pc and applies the contract.
   FSH_Fn_entry.v's FsEntryRt states the entry's OWN runtime use at the as_code B pcs, and fs_entry_goal takes it
   instead of this whole record (a Theorem Labs lane 25c141b8cb6): fe_malloc, fe_free and fe_stack_malloc_0 are exactly the
   second conjuncts of fr_malloc, fr_free and fr_stack_malloc_0; fe_memchr is fr_memchr; fe_memcpy (at
   pc_asan_memcpy (as_code B)) is fr_memcpy once pc_asan_memcpy (as_code B) = PC_memcpy, which the final asyms of this
   build gives by computation. A callee's closing theorem adds its own runtime premise when it is composed in.
   The fields are lib/B/FSH_Rt.v's, word for word, at this build's PC_*. *)
Record FsRt : Prop := {
  fr_strlen : astrlen_realizesU segs B PC_strlen;
  fr_strcmp : astrcmp_realizesU segs B PC_strcmp;
  fr_memchr : amemchr_realizesU segs B PC_memchr;
  fr_snprintf : asnprintf_realizes PC_snprintf;
  fr_bcmp : FSupoisonU.abcmp_realizesU segs B PC_bcmp;
  fr_memcpy : FSupoisonU.aintrin_realizesU segs B OCpy PC_memcpy;
  fr_memset : FSupoisonU.aintrin_realizesU segs B OSet PC_memset;
  fr_set_shadow_f5 : SetShadowDefU.aset_shadow_realizesU segs B PC_set_shadow_f5 0xf5;
  fr_malloc : pc_wrap_malloc (as_code B) = PC_malloc /\ FSupoisonU.amalloc_realizesU segs B;
  fr_free : pc_wrap_free (as_code B) = PC_free /\ FSupoisonU.afree_realizesU segs B;
  fr_stack_malloc_0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\ FSupoisonU.astack_malloc_realizesU segs B 0;
  fr_stack_malloc_1 : pc_stack_malloc (as_code B) 1 = PC_stack_malloc_1 /\ FSupoisonU.astack_malloc_realizesU segs B 1;
  fr_stack_malloc_3 : pc_stack_malloc (as_code B) 3 = PC_stack_malloc_3 /\ FSupoisonU.astack_malloc_realizesU segs B 3
}.
End c.

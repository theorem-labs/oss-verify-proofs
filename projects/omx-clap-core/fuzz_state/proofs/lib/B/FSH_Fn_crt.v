(* fs program part, lane CRT: the ASan contract of check_round_trip (fs.asan-ubsan 0x81b9c, 693 insns (26 more than A: UBSan trap mode, 0 __ubsan_handle_* calls); fuzz_state.c:278-314
   with round_trip_document fs.c:229-264 inlined), in the donor's per-function form through S0's wrappers
   (lib/A/FSH_Gen.v afn_preU / apost_baseU, lib/A/FSH_Base.v fpreU and the fs numerals). The meaning of every value
   comes from fs's released plain contract lib/Prog/check_round_trip_c.v:28-57 and its document model
   lib/Prog/check_round_trip_stages_b.v; that plain proof is also the control-flow template for the walk.
   Statements only: nothing here is proved. Lane table: (internal path) row CRT.
   Ported from (form only; the content is new, from the released contract above): a Theorem Labs lane
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Fn.v check_round_trip_spec (a working branch e48bf3cce32), in the
   U form of FSH_Fn_FORM.md section 1. A new file: no licence lines (internal). rule 24: no function proved.

   U form throughout (a Theorem Labs lane, 20:42Z): fuzz_malloc poisons a 16-byte head per block, so every program function
   runs with live heads. There is no U = [] form of this spec. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState check_round_trip_stages_b.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* STATEMENT ONLY. The callee specs this function's WALK will consume (encode, decode, the five pj_string and six
   pj_set, pj_write, pj_parse, pj_get, pj_get_str, the two pj_free, the four fuzz_free, the two malloc and two free
   through the interceptors, strlen / strcmp / bcmp, and the class-3 fake-frame pair with the set_shadow_f5 shim)
   are NOT premises of the statement: a Theorem Labs lane states each function on its own (FMH_Fn.v) and the proof file takes
   what it needs as Section hypotheses. They are listed with their owners and call sites in this lane's
   (internal), and they go into the lane table's "Named hypotheses" rows when the walk lands.

   No call context. The spec once took a CTX list and the premise `In (raZ regs :: spine ch) CTX`; both are DROPPED
   (stream owner 05:05Z): their only use was to feed the CTX premises of crt's callees, all of which chain down to an
   allocator call, and every one of those callee specs dropped its CTX in the same S0 commit. The allocator calls rely
   on C5's `In (call_trace ..) (as_universe B) \/ st_nev S < EV_MAX` instead. MEASURED for the record: check_round_trip
   has exactly ONE call site in the binary, in LLVMFuzzerTestOneInput at 0x81158 (return address 0x8115c). *)

(* ---- check_round_trip ----
   a0 = t (the base64 text), a1 = bd (the decoded body), a2 = |bs| (its length): released check_round_trip_c.v:30-32.
   The run, in order (MEASURED, every `jal` of 0x81b9c..0x8266c): the class-3 frame; encode; malloc want and malloc
   same; decode; five pj_string and six pj_set building the document; pj_write; pj_parse; pj_get and pj_get_str; a
   second decode; two bcmp; then four fuzz_free, two pj_free and two free. 36 allocations and 36 frees, with at most
   two reallocs inside pj_write's growth: EV_check_round_trip = 2 * 36 + 3 * 2 (FSH_Gen.v:57).
   The document is fixed by the harness, so the released crt_doc_ok (check_round_trip_stages_b.v:188-196) gives what
   pj_write and pj_parse need of it: pj_wf, depth <= 2, a 15-entry allocation trace, each entry + 16 <= CRT_SIZE,
   |wdoc| + 1 < 2^22 and dec_size (b64_enc bs) + 16 <= CRT_SIZE. depth <= 2 is why the live fake frames stay inside
   the donor's room, so the premise below is the caller's own frame only. crt_doc_ok's own two hypotheses (bytes_ok bs
   and |bs| <= 9 * 2^18 + 2) are NOT premises here, exactly as they are not premises of the released contract: the
   walk derives them from b64_dec (zs tb) = Some bs and |tb| <= 3 * 2^20 (9 * 2^18 is 3/4 of 3 * 2^20). *)
(* the released bound on check_round_trip's g_count increment: released check_round_trip_c.v:17. g_count is the
   allocator's call counter; frees never touch it, and the true increment of one call is at most 68. *)
Definition CRT_ALLOCS : Z := 68.
Definition check_round_trip_spec : Prop :=
  forall ly S U W regs mem md ch t bd (tb : list byte) (bs : list Z) live cnt,
  (* the donor's per-function entry premises in U form over fs's relro image, and the shape of U (FSH_Fn_FORM.md sec 1) *)
  fpreU segs B STK_check_round_trip ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  (* room above the entry sp for the chain each program call pushes: crt may be entered with an empty chain ch, so
     YCbq.achain_push's `sp0 < ly_top ly - 16` is not derivable from the chain. The donor states it the same way (cgif
     A/ACid.v:59 fl_baseX, AChf.v Htop32); the caller LLVMFuzzerTestOneInput gives it from its own frame *)
  spZ regs + 32 <= ly_top ly ->
  (* crt is a callee of LLVMFuzzerTestOneInput, whose class-0 frame is the one fake frame live (FORM sec 2) *)
  Z.of_nat (length (frames S)) <= FRL_CHECK ->
  (* arguments: released :30-32 *)
  getr regs 10 = w64 t -> getr regs 11 = w64 bd -> getr regs 12 = w64 (Z.of_nat (length bs)) ->
  (* the text and its NUL, no NUL inside it, and its length bound: released :33-35. MEASURED, LLVMFuzzerTestOneInput
     0x810c0..0x81100: t = malloc(size + 1) through the interceptor, __asan_memcpy of the input, then a NUL. The released
     contract also states SLACK bytes after the NUL; they serve musl's word-wise strlen, and under ASan they lie past the
     malloc'd size in the poisoned tail of the block. crt reaches t only through the byte-wise strlen / strcmp
     interceptors, so the ASan spec needs the bytes up to the NUL and nothing beyond. *)
  zbytes_at segs W mem t (HState.zs (tb ++ [Z_to_bv 8 0])) -> ~ In (Z_to_bv 8 0) tb ->
  Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
  (* the text is outside this call's own stack window: released :36 *)
  (forall a, t <= a < t + Z.of_nat (length tb) + 1 -> ~ HState.in_window (spZ regs) STK_check_round_trip a) ->
  (* t lies INSIDE an allocator block (released :37-38, `blocks L A`): a plain malloc block, so no user-poisoned head *)
  (exists pt kt, In (pt, kt) (ablocks B ly S) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
  (* and overlaps no user-poisoned head of U: the walk reads t's shadow, and U's heads read poisoned there. The block
     itself carries no head (plain malloc), but another block's head may abut it, so this is stated, not derived.
     ENTRY pays it at its call from AR's block separation (a Theorem Labs lane 07:52Z) *)
  Forall (fun q => t + Z.of_nat (length tb) + 1 <= fst q \/ fst q + snd q <= t) U ->
  (* the body is the text's decoding: released :39-40 *)
  WriterSpec.b64_dec (HState.zs tb) = Some bs -> bd <> 0 -> zbytes_at segs W mem bd (HState.zs (HState.bz bs)) ->
  (* bd is a fuzz_malloc block of size k >= |bs| (released :41, `In (bd, k) Lam`). MEASURED, 0x81120: bd is
     preset_base64_decode's result, which allocates its bound, not the exact length, so the size is >= and not = *)
  (exists k, fs_rblock segs B ly S W mem bd k /\ Z.of_nat (length bs) <= k) ->
  (* fs's allocator statics, and no allocation of this call is set to fail: released :42, :46 *)
  fs_stat segs W mem live cnt -> quiet cnt SIZE_MAXZ EV_check_round_trip ->
  (* room above the live bytes for what this call allocates. Every allocating callee asks a headroom premise of its
     caller - pj_string `live + n < 2^64`, pj_set `live + rd_live tr < 2^64`, pj_write `live + 2 * w_cap st' < 2^64` -
     and fs_stat alone gives only live <= peak < 2^64, so no call site could discharge one. LIVE_check_round_trip
     bounds every live increase on this call's path (24 644 335 by trace). The released contract had it through the
     ledger; the caller LLVMFuzzerTestOneInput holds the same shape (live + ACfn.LIVE_LIB < 2^64, ACfn.LIVE_LIB = 2^33) *)
  live + LIVE_check_round_trip < 2 ^ 64 ->
  (* the reader-cell discipline and the stack bound: released :43-44. The released strtod-globals bound (:44) is NOT
     restated: its ASan analogue is the image end, which the donor's layout premise inside fpreU already puts below the
     stack window (FSH_Base.v:119-122). frm_zero (:45) is not restated either: on the ASan side fx is fixed (FORM sec 1) *)
  rd_cells segs W mem -> spZ regs <= 2 ^ 47 ->
  (* the donor's room premises *)
  st_nev S + EV_check_round_trip <= EV_MAX -> blocks_bytes S + LIVE_check_round_trip <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_check_round_trip regs mem md)
    (apost_baseU segs B STK_check_round_trip FS_PSTAT_FP regs ly S W mem md EV_check_round_trip U U
      (fun ly' S' W' regs' mem' md' =>
         (* FP = FS_PSTAT_FP (owner 21:23Z form change): crt changes fs's alloc.c statics (g_live / g_peak /
            g_count) transitively, through its four fuzz_free calls and the fuzz_malloc inside its reader and writer
            callees, so its post states fs_stat at a new count. With FP = [] the journal's image clause would freeze
            those statics, so that post would contradict its own journal. *)
         (* it returns, and every block it took it gave back: released :54-56 (cnt <= cnt' <= cnt + CRT_ALLOCS, keeps,
            ublocks_kept). The block part is one permutation here. U' = U for the same reason: every head crt poisons
            through fuzz_malloc is unpoisoned again by the matching fuzz_free or pj_free, and its two direct malloc
            blocks (0x81da0, 0x81db4) go through the interceptor, which adds no head (FORM: the net-neutral rule).
            The count part is the released bound, not an equality: g_count is the allocator's call counter (bumped by
            the allocations, never by a free; realloc growth inside pj_write depends on |text|), so its increment is
            not fixed. It is at most CRT_ALLOCS, the released check_round_trip_c.v:17 constant - not
            EV_check_round_trip, which is the st_nev event budget and counts the frees as well. *)
         Permutation (ablocks B ly' S') (ablocks B ly S) /\
         (exists cnt', cnt <= cnt' <= cnt + CRT_ALLOCS /\ fs_stat segs W' mem' live cnt') /\
         (* the read-only image is unchanged: released :49-50 (ASan side: rom_view, FORM sec 1) *)
         rom_view segs W' mem')).

End c.

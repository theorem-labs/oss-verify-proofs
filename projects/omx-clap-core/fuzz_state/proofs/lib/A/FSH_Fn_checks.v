(* fs program part, CHECKS group: the ASan contracts of four harness checks of fuzz_state.asan, in the donor's per-function
   form (cgif_file lib/YC21.v:33-132, lib/A/ACfn.v; afn_pre, a CTX premise for functions that allocate, argument
   registers, data premises, st_nev / blocks_bytes room, SRr to the return address through ajournal), in S0's U FORM
   (lib/A/FSH_Gen.v fpreU / fpostU, FSupoisonU.fs_heads: every fs function runs with live user-poisoned heads).
   Statements only (rule 24: no function proved).

   Ported from: a Theorem Labs lane's proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Fn.v:245-288 (a working branch
   706affbdbe6: check_bounded_alloc_spec, check_as_written_spec, check_reject_clean_spec,
   check_reject_clean_starved_spec), re-fitted to fs's code; fs's released plain contracts
   (origin/ossv/recipes c8557374ad2e lib/Prog/check_bounded_alloc_c.v:11-21, check_reject_clean_c.v:11-30,
   check_as_written_c.v:24-62, check_reject_clean_starved_c.v:18-52) for each function's functional premises and post;
   the callees' specs (lib/A/FSH_Fn_writer.v decode_spec / encode_spec, a Theorem Labs lane) for what the starved check must
   supply them. Numerals: lib/A/FSH_Base.v (fs.asan) and lib/A/FSH_Gen.v; measured facts in
   (internal path).
   Lane CHECKS (check_as_written, check_reject_clean_starved; a Theorem Labs lane: check_reject_clean,
   check_bounded_alloc), (internal path). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* fs.c:41 B64_ALLOC_BOUND; plain check_bounded_alloc_c.v:9 *)
Definition b64_alloc_bound (n : Z) : Z := n / 4 * 3 + 3.
(* the request bytes check_as_written holds at once (MEASURED, fs.asan: __wrap_malloc at 0x815d8 = want, fs.c:167, size
   b64_alloc_bound |tb|; at 0x815f4 = six, fs.c:71, size max |tb| 1; six is freed at 0x8197c (fs.c:102) before want's
   tail free at 0x819cc (fs.c:185), so the peak is want + six): with |tb| <= PRESET_FILE_MAX_BYTES = 3 * 2^20 that is
   at most 2,359,299 + 3,145,728 = 5,505,027 < 2^23 = 8,388,608 (the room the donor's malloc asks, YG0d.v:256,
   blocks_bytes S + n <= LIVE_MAX, at each of the two calls; plain check_as_written_c.v:44-45 room_slots) *)
Definition LIVE_check_as_written : Z := 2 ^ 23.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
(* the image facts, a stated interface proved once for fs's TfibB (FSH_Fn_FORM.md section 1) *)
Hypothesis IMG : fs_img_facts segs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the decoder's answer for the text tb (plain check_as_written_c.v:24-27, used at :39 and
   check_reject_clean_starved_c.v:38), on the ASan view: refused (body NULL, len SIZE_MAX, plain :25), or the bytes bs at
   bd (plain :26-27; src_rd = present, addressable, shadow visible, what the bcmp interceptor reads), bd the body of a
   live reader block (fs_rblock: its chunk (bd - HEAD, m + HEAD) in ablocks, plain :40's `In (bd, k) Lam /\ l <= k`)
   whose 16-byte head is user-poisoned: `In (bd - HEAD, HEAD) U`, the pair shape of FSupoisonU.fs_heads (a Theorem Labs lane,
   fs_heads: snd r = 16 and (fst r, m) in ablocks) and of FSupoisonU.ARU_free_outside's `In (P, 16) U` *)
Definition caw_answerA (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world segs) (mem : word -> option byte)
    (tb : list Z) (bd l : Z) : Prop :=
  (WriterSpec.b64_dec tb = None /\ bd = 0 /\ l = SIZE_MAXZ) \/
  (exists bs m, WriterSpec.b64_dec tb = Some bs /\ bd <> 0 /\ l = Z.of_nat (length bs) /\
     src_rd segs W mem bd bs /\ fs_rblock segs B ly S W mem bd m /\ l <= m /\ In (bd - HEAD, HEAD) U).

(* check_bounded_alloc 0x81560 (fs.c:157-163; plain check_bounded_alloc_c.v:11-21): held = a0 (regs 10), n = a1
   (regs 11) as unsigned words, `held <= b64_alloc_bound n` = plain :14, so the abort is dead; a leaf, 16-byte frame on
   every path (0x81560-0x81584, (internal path)); no counter, block or head changes (plain :16-19: only a1 / a2
   change) *)
Definition check_bounded_alloc_spec : Prop :=
  forall ly S U W regs mem md ch held n live peak cnt fail,
  fpreU segs B STK_check_bounded_alloc ly S U W regs mem md ch -> fs_heads B ly S U ->
  fs_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 held -> getr regs 11 = w64 n -> 0 <= held < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  held <= b64_alloc_bound n ->
  SRr segs W (cfg_at segs A_check_bounded_alloc regs mem md)
    (fpostU segs B STK_check_bounded_alloc (spZ regs) [] regs ly S U W mem md 0 U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\ fs_glob segs W' mem' live peak cnt fail)).

(* check_reject_clean 0x81a60 (fs.c:188-202; plain check_reject_clean_c.v:11-30): body = NULL (a0, plain :18),
   len = SIZE_MAX (a1, plain :19), live_before = fuzz_alloc_live () (a2, plain :20; g_live at G_LIVE read through
   fs_glob, plain :16 bytes_at G_LIVE), so the three aborts are dead; post: memory changed only in its frame (plain :26
   munch [sp - 16, sp) = fpostU's window), counters and blocks unchanged. Called from LLVMFuzzerTestOneInput (0x810ec)
   and from check_reject_clean_starved (0x8264c) *)
Definition check_reject_clean_spec : Prop :=
  forall ly S U W regs mem md ch live peak cnt fail,
  fpreU segs B STK_check_reject_clean ly S U W regs mem md ch -> fs_heads B ly S U ->
  (* no extra premise here (a Theorem Labs lane ruling 01:37Z): its prover a Theorem Labs lane walks fuzz_alloc_live INLINE (3 words
     auipc / ld / ret, one run A 0x81a60 .. 0x82e5c .. 0x82e64 .. return 0x81a90; a working branch
     bab265ebece lib/A/FSH_check_reject_clean.v:4, :114), so no callee spec and no achain over s0 is formed and
     fs_glob's live < 2^64 suffices. The achain_low route (s0 = live via `mv s0, a2` A 0x81a78 / B 0x81b74 before
     `jal fuzz_alloc_live` A 0x81a7c / B 0x81b78) would need a bound on live, but the proof does not take it. *)
  fs_glob segs W mem live peak cnt fail ->
  getr regs 10 = w64 0 -> getr regs 11 = w64 SIZE_MAXZ -> getr regs 12 = w64 live ->
  SRr segs W (cfg_at segs A_check_reject_clean regs mem md)
    (fpostU segs B STK_check_reject_clean (spZ regs) [] regs ly S U W mem md 0 U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\ fs_glob segs W' mem' live peak cnt fail)).

(* check_as_written 0x81590 (fs.c:165-186; plain check_as_written_c.v:29-62): want = malloc (B64_ALLOC_BOUND |tb|)
   (fs.c:167, call 0x815d8), six = malloc (max |tb| 1) in the inlined expected_body (fs.c:71, 0x815f4), free (six)
   (fs.c:102, 0x8197c), same_body's bcmp (fs.c:183, 0x819a4), free (want) by a tail call (fs.c:185, `j` 0x819cc).
   The harness's own malloc / free: straight to the ASan interceptors __wrap_malloc / __wrap_free, not fuzz_malloc,
   so fuzz/alloc.c's statics and the user-poisoned heads are unchanged; 2 M + 2 F = EV_check_as_written events. Every
   abort (fs.c:171, :76, :177, :183) is dead: the two mallocs are granted (the forced-only world, YG0d.v:527), and
   caw_answerA is the decoder's answer.
   Premises, each from the plain contract: t / bd / l in a0-a2 (plain :32); the text tb NUL-terminated at t with the
   slack strlen's word reads need (cstr_ok, plain :33-34); inside a live block or the read-only image (cstr_kept =
   str_homeA, plain :38; this also keeps it outside the stack window, plain :36-37); |tb| <= 3 * 2^20 (plain :35);
   caw_answerA (plain :39-40); the reader ledger (fs_glob, plain :41); room for the two requests (plain :43-45). Post:
   the blocks the same up to order (plain :59 blocks L' A' = blocks L A), counters unchanged (plain :61 ledger with the
   same Lam peak cnt fail), memory changed only in the window and in the two freed chunks (fpostU's ajournal; plain
   :56-58 call_post_k with the touched set w / s). *)
(* NO CTX premise (a Theorem Labs lane 05:03Z general CTX rule): its only use was the four allocator calls' trace-in-universe
   clause, which C5 now gives as `In (call_trace ...) (as_universe B) \/ st_nev S < EV_MAX`, the second disjunct from
   `st_nev S + EV_check_as_written <= EV_MAX` below. *)
Definition check_as_written_spec : Prop :=
  forall ly S U W regs mem md ch t bd l (tb : list Z) live peak cnt fail,
  fpreU segs B STK_check_as_written ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 t -> getr regs 11 = w64 bd -> getr regs 12 = w64 l ->
  cstr_ok segs W mem t tb -> cstr_kept B ly S U t tb -> Z.of_nat (length tb) <= PRESET_FILE_MAX_BYTES ->
  caw_answerA ly S U W mem tb bd l ->
  fs_glob segs W mem live peak cnt fail ->
  st_nev S + EV_check_as_written <= EV_MAX -> blocks_bytes S + LIVE_check_as_written <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_check_as_written regs mem md)
    (fpostU segs B STK_check_as_written (spZ regs) [] regs ly S U W mem md EV_check_as_written U
       (fun ly' S' W' regs' mem' md' =>
          Permutation (ablocks B ly' S') (ablocks B ly S) /\ fs_glob segs W' mem' live peak cnt fail)).

(* check_reject_clean_starved 0x82508 (fs.c:206-226; plain check_reject_clean_starved_c.v:28-52).
   WHY THERE ARE NO ALLOCATOR EVENTS (EV_check_reject_clean_starved = 0): a consequence of the premises, not one of
   them. fs_glob (G_COUNT holds cnt, G_FAIL holds SIZE_MAX) and `quiet cnt SIZE_MAXZ 2` (cnt + 2 < 2^63 < SIZE_MAX)
   give: fuzz_alloc_fail (0) (fs.c:213) stores g_fail_at := g_count + 0 = cnt (alloc.c:140, the `k < SIZE_MAX - g_count`
   arm); preset_base64_decode's one fuzz_malloc (pf.c:608; decode reaches it on every path, as the plain proof
   check_reject_clean_starved.v:663 shows) runs failing () with g_count = g_fail_at (alloc.c:35), so it stores
   g_fail_at := SIZE_MAX, g_count := cnt + 1 and returns NULL without reaching ASan malloc (alloc.c:37-38, :63):
   fs.asan fuzz_malloc 0x828e8 `bne a3, a4` (g_count, g_fail_at) falls through to 0x828ec-0x828f8 (a0 := 0;
   g_fail_at := -1; `j 0x829ac`, the epilogue), past the function's only `jal __wrap_malloc` (0x82908); fs.asan-ubsan
   fuzz_malloc 0x82a80 `bne a2, a3` falls through to 0x82a84-0x82a8c (g_fail_at := -1; `j 0x82ab8`: a0 := 0, ret), past
   its only `jal __wrap_malloc` (0x82a9c) (MEASURED, capstone on the pinned images). fuzz_alloc_fail (SIZE_MAX)
   (fs.c:215) stores SIZE_MAX (alloc.c:140's second arm); check_reject_clean sees NULL / SIZE_MAX / live. When body is
   not NULL the same holds for fs.c:219-221 and preset_base64_encode's fuzz_malloc (pf.c:579), g_count := cnt + 2.
   decode / encode return NULL on the refusal without a free (pf.c:613, :582). Nothing is held (fs.c:224).
   Premises from the plain contract: t / bd / l (plain :31), the text (plain :32-34, :37), |tb| (plain :34),
   caw_answerA (plain :38-39), the ledger with fail = SIZE_MAX (plain :40) and the counter bound (plain :40
   cnt + 2 < 2^63 = quiet); bytes_ok tb and the room / event premises are what the decode / encode specs ask
   (FSH_Fn_writer.v decode_spec, encode_spec); plain :42 hs_room is the plain twin. Post: blocks unchanged (plain :49),
   the ledger with cnt + 1 / cnt + 2 (plain :51).
   Its object `n` lives in its class-0 fake frame (__asan_stack_malloc_0 at 0x82578, 64 bytes), granted because at most
   FRL_CHECK = 1 fake frame is live at its call (LLVMFuzzerTestOneInput's class-0 frame) and fs_frames 0 > 1
   (YG00.v:559), so count_cid 0 (frames S) < fs_frames 0 (astack_malloc_realizes, YG0d.v:287): the walk does not take
   the real-stack fallback (FSH_Fn_FORM.md section 2).
   FP = FS_PSTAT_FP (owner 21:23Z form): it writes fuzz/alloc.c's g_count / g_fail_at (fuzz_alloc_fail, the refused
   fuzz_malloc's failing ()), lib/A/FSPstat.v. The other three checks write no static (check_as_written's malloc /
   free go straight to the ASan interceptors; check_reject_clean only reads g_live): FP = []. *)
(* NO CTX premise (a Theorem Labs lane 05:03Z general CTX rule): it was passed only to decode / encode, whose specs drop
   their CTX in the same change (their only use was fuzz_malloc's trace clause). *)
Definition check_reject_clean_starved_spec : Prop :=
  forall ly S U W regs mem md ch t bd l (tb : list Z) live peak cnt,
  fpreU segs B STK_check_reject_clean_starved ly S U W regs mem md ch -> fs_heads B ly S U ->
  (* room for its frame link above sp (donor cgif ACid.v:59 fl_baseX; a Theorem Labs lane's achain-push audit 00:27Z, a Theorem Labs lane
     ruling 00:44Z: the premise, not a CTX-depth hypothesis). NOT derivable here (MEASURED, capstone, both images): s0 is
     the frame pointer at all 9 program calls (`addi s0, sp, 0x80` A 0x82540 / B 0x826a8, not rewritten before them:
     fuzz_alloc_live 0x8260c / 0x82678, fuzz_alloc_fail 0x82624 / 0x8263c / 0x82658 / 0x82670, decode 0x82630,
     check_reject_clean 0x8264c, encode 0x82664; B +0x168), so achain_push needs fp < ly_top ly - 16; afn_preU's
     astk_ok gives only `sp0 <= ly_top ly`, and the chain route needs ch <> [] (the donor's CTX depth hypothesis HDEEP,
     cgif A/ACb8.v:76). Its caller LLVMFuzzerTestOneInput discharges it from its own frame *)
  spZ regs + 32 <= ly_top ly ->
  Z.of_nat (length (frames S)) <= FRL_CHECK ->
  getr regs 10 = w64 t -> getr regs 11 = w64 bd -> getr regs 12 = w64 l ->
  cstr_ok segs W mem t tb -> cstr_kept B ly S U t tb -> WriterSpec.bytes_ok tb ->
  (* the text premise decode's spec asks (FSH_Fn_writer.v decode_spec_ff), verbatim: cstr_kept's format arm
     (FS_SN_FMTS) is not one of wsrc_kept's arms, so decode's premise is stated here too (a Theorem Labs lane ruling 00:44Z) *)
  FSH_Fn_writer.wsrc_kept B segs ly S U W mem 0 t (tb ++ [0]) ->
  Z.of_nat (length tb) <= PRESET_FILE_MAX_BYTES ->
  caw_answerA ly S U W mem tb bd l ->
  fs_glob segs W mem live peak cnt SIZE_MAXZ -> quiet cnt SIZE_MAXZ 2 ->
  (* resources BY THIS CALL'S OWN TRACE (a Theorem Labs lane D6 / a Theorem Labs lane 00:18Z; the former LIVE_check_reject_clean_starved
     constant is gone with the writer's LIVE_decode / LIVE_encode): the function itself holds NO request bytes and
     ticks nothing (both reader allocations are refused in failing (), see above), so every term below is only what
     its two callees ask BEFORE they run - decode's dec_ev / dec_size (FSH_Fn_writer.v decode_spec_ff) and, when
     bd <> 0, encode's EV_preset_base64_encode / enc_size l (encode_spec) - which this walk passes on verbatim *)
  st_nev S + FSH_Fn_writer.dec_ev tb + EV_preset_base64_encode <= EV_MAX ->
  blocks_bytes S + (FSH_Fn_writer.dec_size tb + HEAD) <= LIVE_MAX ->
  live + FSH_Fn_writer.dec_size tb < 2 ^ 64 ->
  (bd <> 0 -> blocks_bytes S + (FSH_Fn_writer.enc_size l + HEAD) <= LIVE_MAX /\
              live + FSH_Fn_writer.enc_size l < 2 ^ 64) ->
  SRr segs W (cfg_at segs A_check_reject_clean_starved regs mem md)
    (fpostU segs B STK_check_reject_clean_starved (spZ regs) FS_PSTAT_FP regs ly S U W mem md EV_check_reject_clean_starved U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\
          fs_glob segs W' mem' live peak (if bd =? 0 then cnt + 1 else cnt + 2) SIZE_MAXZ)).

End c.

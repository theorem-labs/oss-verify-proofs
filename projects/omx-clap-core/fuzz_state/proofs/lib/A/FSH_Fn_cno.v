(* lib/A/FSH_Fn_cno.v - LANE CNO program part: ASan contracts for check_no_overread (0x811c8) and past_nul (0x82728)
   of fuzz_state.asan, in the donor per-function U-form (FSH_Fn_FORM.md section 1; a Theorem Labs lane FMH_Fn
   check_no_overread_spec, a working branch a1902517c68). Functional facts = fuzz_state's RELEASED plain
   lib/Prog/check_no_overread_c.v (nor_ops :18-22) and lib/Prog/past_nul_c.v (pn_copy :16, restated locally so the
   slot-named AllocSlots.v dependency of those files is not imported). Statements only (rule 24: no function proved).
   *** FLAGS for a Theorem Labs lane (confirm before I prove):
     (1) ROOM PREMISE is the donor st_nev/EV_MAX + blocks_bytes/LIVE_MAX, NOT res_ok_slots/hs_room (lane rule 3).
     (2) cno post: blocks unchanged + cnt+3 (plain post ledger cnt+3), U'=U (net-neutral 6M+6F).
     (3) past_nul post: returns block (res, n+18) [asan (res-HEAD, n+18+HEAD)], pn_copy at res, cnt+1,
         U' = U ++ [(res - HEAD, HEAD)] (the new 16-byte poisoned head). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer.  (* dec_size, used qualified *)
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* restated from the released plain lib/Prog/past_nul_c.v:16 (pn_copy over list Z; the released file's is over list byte
   via Z_to_bv 8): the source bytes, then 0, (c mod 256), 65 ('A'), and 15 zero bytes. *)
Definition pn_copy (db : list Z) (c : Z) : list Z := db ++ [0; c mod 256; 65] ++ repeat 0 15%nat.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis IMG : fs_img_facts segs B.

(* check_no_overread 0x811c8 (plain lib/Prog/check_no_overread_c.v:30): reads db at d (no NUL, len <= 3 MiB), decodes it
   3x with 3 paired head malloc/free of (len+18) and the decoder's malloc/free, aborts on overread, returns; blocks
   unchanged; 6 malloc + 6 free (EV_check_no_overread = 12, FSH_Gen.v:54); class-1 fake frame; peak < LIVE (2^24). *)
Definition check_no_overread_spec : Prop :=
  forall ly S U W regs mem md ch d (db : list Z) live peak cnt fail,
  fpreU segs B STK_check_no_overread ly S U W regs mem md ch ->
  FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CHECK ->
  (* Needed, not derivable from this spec's own facts: check_no_overread builds a frame pointer (prologue 0x81204
     `addi s0, sp, 0xa0`, A), so s0 = sp0 at all its program-call sites and each callee's chain needs achain_push,
     which requires fp < ly_top - 16; with the entry chain ch = [] fpreU / astk_ok gives only sp0 <= ly_top ly
     (YCbq.v:335), and STK_check_no_overread bounds room below sp0, not above. Donor: cgif ACid.v:59 fl_baseX.
     The caller LLVMFuzzerTestOneInput proves it from its own frame. *)
  spZ regs + 32 <= ly_top ly ->
  getr regs 10 = w64 d -> getr regs 11 = w64 (Z.of_nat (length db)) ->
  src_rd segs W mem d db -> Forall (fun c => c <> 0) db ->
  (0 < Z.of_nat (length db) -> exists b m, In (b, m) (ablocks B ly S) /\ b <= d /\ d + Z.of_nat (length db) <= b + m) ->
  Z.of_nat (length db) <= PRESET_FILE_MAX_BYTES ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail 3 ->
  (* headroom for the three decode buffers live at once: decode_spec asks live + dec_size tb < 2^64, and the three
     preset_base64_decode calls (A 0x81398 0x813a8 0x813b8) all precede the three fuzz_free calls (0x81420..), on the
     same db, each successful buffer staying live; fs_glob bounds only live <= peak < 2^64. Trace-derived (exact on the
     all-success path); the caller LLVMFuzzerTestOneInput discharges it from its own headroom. *)
  live + 3 * A.FSH_Fn_writer.dec_size db < 2 ^ 64 ->
  st_nev S + EV_check_no_overread <= EV_MAX ->
  blocks_bytes S + LIVE_check_no_overread <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_check_no_overread regs mem md)
    (fpostU segs B STK_check_no_overread (spZ regs) FS_PSTAT_FP regs ly S U W mem md EV_check_no_overread U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\
          exists peak', peak <= peak' /\ fs_glob segs W' mem' live peak' (cnt + 3) fail)).

(* past_nul 0x82728 (plain lib/Prog/past_nul_c.v:27 past_nul_contract): mallocs one block of (n + 18) bytes via the
   HARNESS allocator (__wrap_malloc 0x53074 directly, NOT fuzz_malloc), result returned UNSHIFTED (no fuzz HEAD, no
   poison edge, fuzz ledger statics unchanged); copies the n source bytes at d then NUL, c, 'A' and 15 zero bytes
   (pn_copy db c), leaves the block live. 1 malloc event (EV_past_nul = 1). Post lifts past_nul_c.v:47,50
   (blocks ++ (res, n+18), ledger live/peak/cnt/fail UNCHANGED). No fake frame. FP = [] (no static write). *)
Definition past_nul_spec : Prop :=
  forall ly S U W regs mem md ch d n c (db : list Z) live peak cnt fail,
  fpreU segs B STK_past_nul ly S U W regs mem md ch ->
  FSupoisonU.fs_heads B ly S U ->
  getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 c ->
  0 <= c < 2 ^ 64 -> 0 <= n <= 2 ^ 22 -> Z.of_nat (length db) = n ->
  src_rd segs W mem d db ->
  (0 < n -> exists b m, In (b, m) (ablocks B ly S) /\ b <= d /\ d + n <= b + m) ->
  fs_glob segs W mem live peak cnt fail -> quiet cnt fail 1 ->
  st_nev S + EV_past_nul <= EV_MAX ->
  blocks_bytes S + (n + 18) <= LIVE_MAX -> n + 18 < MALLOC_MAX ->
  SRr segs W (cfg_at segs A_past_nul regs mem md)
    (fun W' c' => exists res,
       apost_baseU segs B STK_past_nul [] regs ly S W mem md EV_past_nul U U
         (fun ly' S' W' regs' mem' md' =>
            getr regs' 10 = w64 res /\ res <> 0 /\ res mod 16 = 0 /\
            ablocks B ly' S' = ablocks B ly S ++ [(res, n + 18)] /\
            fs_heads B ly' S' U /\
            zbytes_at segs W' mem' res (pn_copy db c) /\
            fs_glob segs W' mem' live peak cnt fail) W' c').

End c.

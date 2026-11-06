(* lib/B/FSH_Fn_cno.v - LANE CNO program part, B twin (fs.asan-ubsan): ASan contracts for check_no_overread
   (B 0x8124c) and past_nul (B 0x82894), donor per-function U-form (FSH_Fn_FORM.md section 1). Image-generic text lives
   in lib/A (A.FSH_Gen / A.FSupoison / A.FSupoisonU / A.FSH_YC20); this file carries only the B numerals via B.FSH_Base /
   B.FSH_Rt / B.FSPstat. The spec text is IDENTICAL to lib/A/FSH_Fn_cno.v; every numeral (A_check_no_overread,
   STK_check_no_overread, FS_PSTAT_FP, ...) is named, resolving to B's value. Statements only (rule 24: no function proved).
   STEP 1 B: statements only; the B walk waits for RELOC-B's lib/Reusable/Y* core (~01:00Z, a Theorem Labs lane 21:34Z). Same
   flags as A: FP = FS_PSTAT_FP (posts write g_count); room premise st_nev/EV_MAX + blocks_bytes/LIVE_MAX (not slot). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_writer.  (* dec_size, used qualified *)
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* restated from the released plain lib/Prog/past_nul_c.v:16 (over list Z). *)
Definition pn_copy (db : list Z) (c : Z) : list Z := db ++ [0; c mod 256; 65] ++ repeat 0 15%nat.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis IMG : fs_img_facts segs B.

Definition check_no_overread_spec : Prop :=
  forall ly S U W regs mem md ch d (db : list Z) live peak cnt fail,
  fpreU segs B STK_check_no_overread ly S U W regs mem md ch ->
  FSupoisonU.fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CHECK ->
  (* Needed, not derivable from this spec's own facts: check_no_overread builds a frame pointer (B prologue 0x81288
     `addi s0, sp, 0xa0`; s0 unchanged until the epilogue 0x815b4 `ld s0, 0x90(sp)`), so s0 = sp0 at all eight
     program-call sites (past_nul 0x8137c 0x81390; preset_base64_decode 0x81444 0x81454 0x81464; fuzz_free 0x814cc
     0x814d4 0x814dc; capstone over fs.asan-ubsan sha256 5ac5ce0954f8) and each callee's chain needs achain_push,
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
     preset_base64_decode calls (B 0x81444 0x81454 0x81464) all precede the three fuzz_free calls (0x814cc..), on the
     same db, each successful buffer staying live; fs_glob bounds only live <= peak < 2^64. Trace-derived (exact on the
     all-success path); the caller LLVMFuzzerTestOneInput discharges it from its own headroom. *)
  live + 3 * B.FSH_Fn_writer.dec_size db < 2 ^ 64 ->
  st_nev S + EV_check_no_overread <= EV_MAX ->
  blocks_bytes S + LIVE_check_no_overread <= LIVE_MAX ->
  SRr segs W (cfg_at segs A_check_no_overread regs mem md)
    (fpostU segs B STK_check_no_overread (spZ regs) FS_PSTAT_FP regs ly S U W mem md EV_check_no_overread U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\
          exists peak', peak <= peak' /\ fs_glob segs W' mem' live peak' (cnt + 3) fail)).

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

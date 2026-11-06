(* fs program part, lane ENTRY, IMAGE B (fs.asan-ubsan, sha256 5ac5ce0954f8...): the twin of lib/A/FSH_Fn_entry.v
   (a working branch c97b870fa10, folded in S0). Same names and the same three-premise order (TfibLib, TfibSyms,
   FsEntryTraces, LIBK), every address and frame image B's own: no term here uses image A's content.
   rule 24: proves no function (kind: statement text). Statement only, besides the image-neutral lemma fs_fake_granted,
   restated here so this file does not load lib/A/FSH_Fn_entry.v.
   MEASURED on image B (capstone 5.0.7 over the unstripped fs.asan-ubsan b1566a1ca816, a Theorem Labs lane 2026-10-29):
   - LLVMFuzzerTestOneInput 0x80f8c (FSH_Base.FS_LLVMF), its caller's return address 0x80e88 (FSH_Base.FS_RA_LLVMF); the
     call order is A's (A 0x80f1c), 19 `jal` sites, the same callees in the same order.
   - callee call sites, return address = `jal` pc + 4: check_no_overread 0x810b8 -> 0x810bc, preset_base64_decode
     0x81120 -> 0x81124, check_as_written 0x81144 -> 0x81148, check_round_trip 0x81158 -> 0x8115c,
     check_reject_clean_starved 0x8117c -> 0x81180, fuzz_free 0x81184 -> 0x81188 (A: 0x8104c / 0x810a4 / 0x810c8 /
     0x810dc / 0x81100 / 0x81108).
   - the entry's own runtime sites: __asan_stack_malloc_0 0x80ff4, memchr trampoline 0x81090, malloc trampoline 0x810c0
     (ra 0x810c4), __asan_memcpy 0x810dc, free trampoline 0x8118c (ra 0x81190). FsEntryRt states the runtime contracts
     at these sites (memchr at lib/B/FSH_Base.v's PC_memchr). These are the entry's OWN runtime uses: a callee's closing
     theorem adds its own runtime premises when composed, so fs_entry_goal takes no lib/B/FSH_Rt.v FsRt (the mirror of
     lib/A/FSH_Fn_entry.v, 25c141b8cb6).
   - the allocator call traces' inner return address (the GetCurrentPc `jal`'s return inside the interceptor, i.e.
     call_trace's ipc): __interceptor_malloc 0x532bc + 0xc8 = 0x53384 (`jal 0x205b0` at 0x53380), __interceptor_free
     0x530ec + 0x138 = 0x53224 (`jal 0x20710` at 0x53220); A's 0x53314 / 0x531b4 sit at the same offsets, and the A and
     B interceptors have identical mnemonic sequences (348 and 464 bytes).
   IMAGE-B CORE: TfibLib and TfibSyms are image B's own twins, lib/B/YCeg.v (Record TfibLib :27) and lib/B/YF0m.v
   (Record TfibSyms :909), from RELOC-B (a working branch 8d433ea5180); this file lands in S0 together with that
   core. The contract concluded is lib/B/FSH_Harness.v's fs_lib_contract_x at build B, whose sink / meta cells are its
   Section variable K (asink_syms) and whose sink head is the context SK - both are explicit here, to be instantiated
   by B's core (FSH_Base.fsB_sink_head and B's asink_syms); when the B harness switches to B's YCfn, only the
   conclusion's name changes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YCbp YC5d YI00 YI04 YI16 YK06 YO09 YM05
YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSH_Harness.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Fn_alloc FSH_Fn_checks FSH_Fn_cno FSH_Fn_crt FSH_Fn_writer.
(* image B's TfibLib (RELOC-B, lib/B/YCeg.v) and TfibSyms (lib/B/YF0m.v), by Require only, as A takes ACeg / AF0m *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0m.
Import ListNotations.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Lemma count_cid_le_length : forall cid (l : list (Z * Z)), count_cid cid l <= Z.of_nat (length l).
Proof.
  intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
  destruct (c =? cid); lia.
Qed.

(* every fake-frame class fs.asan-ubsan uses (0, 1, 3, as in A: a Theorem Labs lane's row-set check, 03:35Z) has room whenever
   at most FRL_MAX frames are live *)
Lemma fs_fake_granted : forall cid (l : list (Z * Z)),
  0 <= cid <= 3 -> Z.of_nat (length l) <= FRL_MAX -> count_cid cid l < fs_frames cid.
Proof.
  intros cid l Hc Hl. pose proof (count_cid_le_length cid l) as Hle.
  unfold fs_frames, kStackSizeLog. rewrite Z.shiftl_1_l.
  assert (Hp : 2 ^ 11 <= 2 ^ (20 - 6 - cid)) by (apply Z.pow_le_mono_r; lia).
  unfold FRL_MAX in Hl. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

Record FsEntryRt : Prop := {
  fe_stack_malloc_0 : astack_malloc_realizesU segs B 0;
  fe_stack_free : astack_free_law segs B;
  fe_malloc : amalloc_realizesU segs B;
  fe_free : afree_realizesU segs B;
  fe_memcpy : aintrin_realizesU segs B OCpy (pc_asan_memcpy (as_code B));
  fe_memchr : amemchr_realizesU segs B PC_memchr
}.
End c.

(* the trivial meter bound the harness contract is instantiated at (A's file, same definition) *)
Definition XL0 : Z -> Z := fun _ => 0.

(* SK is an EXPLICIT variable, never inferred (see the guard above); K is the build's sink / meta cells, the Section
   variable of lib/B/FSH_Harness.v's contract *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable SK : YI16.sink_head.
Variable K : asink_syms.
Variable B : asyms.
#[local] Abbreviation segs := fsbsegs.

Record FsEntryFns : Prop := {
  en_no_overread : @check_no_overread_spec fx rc SK segs B;
  en_alloc_live : @fuzz_alloc_live_spec fx rc SK segs B;
  en_alloc_peak_reset : @fuzz_alloc_peak_reset_spec fx rc SK segs B;
  en_decode : @decode_spec_ff fx rc SK B segs;
  en_alloc_peak : @fuzz_alloc_peak_spec fx rc SK segs B;
  en_bounded_alloc : @check_bounded_alloc_spec fx rc SK segs B;
  en_as_written : @check_as_written_spec fx rc SK segs B;
  en_round_trip : @check_round_trip_spec fx rc SK segs B;
  en_reject_clean : @check_reject_clean_spec fx rc SK segs B;
  en_starved : @check_reject_clean_starved_spec fx rc SK segs B;
  en_free : @fuzz_free_spec fx rc SK segs B
}.

Definition fs_entry_goal : Prop :=
  (forall pl fs K', LIBK pl fs K' = K' (LL 0 fs [])) ->
  YCeg.TfibLib B -> YF0m.TfibSyms B ->
  @FsEntryRt fx rc segs B -> @fs_img_facts rc segs B -> FsEntryFns ->
  @fs_lib_contract_x fx rc LS SK B ameter_triv XL0 XL0 K.
End e.

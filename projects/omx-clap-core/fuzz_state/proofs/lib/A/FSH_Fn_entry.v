(* fs program part, lane ENTRY (LLVMFuzzerTestOneInput 0x80f1c, fs.c:316-341): what the entry walk takes besides the
   callee specs of the other lanes (ALLOC FSH_Fn_alloc.v, CHECKS FSH_Fn_checks.v, CNO, CRT, WRITER's
   preset_base64_decode). The entry's own contract is FSH_Harness.v fs_lib_contract_x (S0); it is not restated here.
   1. fs_fake_granted (proved): every __asan_stack_malloc_<cid> call of fs (cid 0, 1, 3) is granted, because at most
      FRL_MAX fake frames are live at any call (the FRL_ constants of FSH_Gen.v) and fs_frames cid >= 2^11 (YG00.v:559,
      kStackSizeLog 20).
      So astack_malloc_realizesU's grant premise (FSupoisonU.v, after YG0d.v:287) holds at every site, the stack_malloc
      path that answers PNull (YG00.v:573-574) is not taken, and the real-stack fallback (`andi`, the 4096 probe, the
      stack-shadow redzones; the FRAME_ comment of FSH_Base.v) is dead code: FSH_Fn_FORM.md section 2 / 7.1's open point needs
      no stack-shadow design.
   2. FsEntryRt: the runtime contracts the entry calls at its own sites (dis 0x80f84 stack_malloc_0, 0x81020 memchr,
      0x81050 malloc, 0x8106c __asan_memcpy, 0x8110c free) in the U form of FSH_Fn_FORM.md section 4, with the donor's
      stack-free law (YG0d.v:300), at the pcs the donor's law bundle names (YG0d.v:533-537); memchr at FSH_Base.v's
      PC_memchr. These are the entry's OWN runtime uses: a callee's closing theorem adds its own runtime premises when
      composed, so fs_entry_goal takes no FSH_Rt.v FsRt. Port-from: cgif_file A/ACfi.v:107-114 (the callee contracts
      as Section hypotheses of the entry walk), A/AD1q.v:43-45, YG0d.v:533-544. Statement only, besides lemma 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YCbp YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v ACfn FSH_Harness.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSH_Fn_alloc FSH_Fn_checks FSH_Fn_cno FSH_Fn_crt FSH_Fn_writer.
(* TfibLib (A/ACeg.v, owner RELOC) by Require only: ACeg's closure (YCe5) restates core names, and no sink instance
   is (re)activated here *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require ACeg.
(* TfibSyms (A/AF0m.v, owner RELOC) by Require only, for the sink's image laws (A/AD1u.v tfib_AIL) and errno's place
   (ts_errno) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0m.
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

(* every fake-frame class fs uses (0 LLVMFuzzerTestOneInput / starved / parse_value / put_string, 1 check_no_overread,
   3 check_round_trip; FSH_Base.v) has room whenever at most FRL_MAX frames are live *)
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

(* ---- the entry walk's statement (proof: FSW_entry.v, after FSW_K milestone 3) ----
   The callee specs the walk consumes. CTX DROP (a Theorem Labs lane 2026-10-29T05:05Z, owner rulings 05:05Z / 05:13Z): every
   callee spec lost its CTX premise and binder (the allocator calls now rely on C5's `In (call_trace ..) (as_universe B)
   \/ st_nev S < EV_MAX`), so the CTX lists, site_ctx, FsEntryCtx and FsEntryTraces are gone from this goal. The call
   sites, for the walk (dis fs.asan, return address = the `jal` at r - 4): check_no_overread 0x8104c,
   preset_base64_decode 0x810a4, check_as_written 0x810c8, check_round_trip 0x810dc, check_reject_clean_starved 0x81100,
   fuzz_free 0x81108; the entry's own malloc 0x81050 (ra 0x81054) and free 0x8110c (ra 0x81110). preset_base64_decode is
   taken in its fake-frame form decode_spec_ff: fs_fake_granted makes the class-0 frame live, and `len` is its offset 32. *)

(* the trivial meter bound fs's harness contract is instantiated at (cgif_file A/ACfi.v:56) *)
Definition XL0 : Z -> Z := fun _ => 0.

(* SK is an EXPLICIT variable: the plain build's `#[global] Instance src0_sink_head` (Reusable/YI5b.v:12) must never be
   inferred here; the ASan sink head is passed by whoever instantiates fs_entry_goal. *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable SK : YI16.sink_head.
Variable B : asyms.
#[local] Abbreviation segs := tfibsegs.

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

(* the library shape the harness contract is used at: fs's checksum shape (lib/ZTraceSpec.v:14-20) and COMP's
   ag_shape checksum_shape both discharge the first premise by eq_refl; the premise keeps the Section's LS and does not
   load the plain ZTraceSpec instance *)
Definition fs_entry_goal : Prop :=
  (forall pl fs K, LIBK pl fs K = K (LL 0 fs [])) ->
  ACeg.TfibLib B -> AF0m.TfibSyms B ->
  @FsEntryRt fx rc segs B -> @fs_img_facts rc segs B -> FsEntryFns ->
  @fs_lib_contract_x fx rc LS B ameter_triv XL0 XL0.
End e.

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Definition PREFIX_LC_STR : Z := 0x10416.
Definition PREFIX_UC_STR : Z := 0x1038a.
Definition FMT_WHOLE_STR : Z := 0x1044b.
Definition prefix_uc : list Z := [80; 82; 69; 70; 73; 88].
Definition fmt_whole : list Z := [60; 37; 115; 62].

Definition img_strings (m : word -> option byte) : Prop :=
  bytes_at rsegs m PREFIX_LC_STR (map (Z_to_bv 8) (prefix_lc ++ [0])) /\
  bytes_at rsegs m PREFIX_UC_STR (map (Z_to_bv 8) (prefix_uc ++ [0])) /\
  bytes_at rsegs m FMT_WHOLE_STR (map (Z_to_bv 8) (fmt_whole ++ [0])).

Definition stat_writes (a : Z) : Prop := G_LIVE <= a < G_COUNT + 8 \/ G_FAIL <= a < G_FAIL + 8.

Definition off_statics (a n : Z) : Prop :=
  (a + n <= G_LIVE \/ G_COUNT + 8 <= a) /\ (a + n <= G_FAIL \/ G_FAIL + 8 <= a).

Definition quiet (cnt fail N : Z) : Prop := fail = 2 ^ 64 - 1 /\ 0 <= cnt /\ cnt + N < 2 ^ 63.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.

Definition statics_facts : Prop :=
  forall a, alloc_statics a -> in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE).

Definition statics_free : Prop :=
  forall L A mem md a, MR L A mem md -> alloc_statics a -> ~ owned B L A a.

Definition errno_low : Prop := errno_addr B + 4 <= alloc_ceiling.

Definition ctx_owned : Prop :=
  forall L A mem md a, MR L A mem md -> ms_ctx B <= a < ms_ctx B + CTX_SIZE -> owned B L A a.

Definition guard_cells (mem : word -> option byte) : Prop :=
  word_mem segs mem (ms_got_guard B) (ms_guard B) /\ exists g, word_mem segs mem (ms_guard B) g.

Definition guard_syms : Prop := ms_got_guard B = 0x1e0b8 /\ ms_guard B = 0x4f6c8.

Definition statics_noerrno : Prop :=
  forall a, alloc_statics a -> ~ (errno_addr B <= a < errno_addr B + 4).

Definition malloc_syms_omx : Prop := ms_malloc B = 0x14ce0 /\ ms_free B = 0x14ba0.

Definition bpost (K : Z) (E : Z -> Prop) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  blocks L' A' = blocks L A /\
  (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte segs mem' (a + i) = mbyte segs mem (a + i)) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k B K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, scratch_k B K regs a -> writable_at segs mem' a) /\
  ro_agree segs mem' /\ guard_kept B mem mem'.

End KB.

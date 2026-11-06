From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition rwin (K S a : Z) : Prop := (S - K <= a < S) \/ (errno_addr B <= a < errno_addr B + 4).

Definition never_owned (a : Z) : Prop := forall L0 A0 mem0 md0, MR L0 A0 mem0 md0 -> ~ owned B L0 A0 a.

Definition rstep (K S : Z) (E g : Z -> Prop)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (forall a k, In (a, k) (blocks L A) -> 0 < k -> ~ g a -> In (a, k) (blocks L' A')) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ rwin K S a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> never_owned a -> ~ rwin K S a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a k i, In (a, k) (blocks L A) -> ~ g a -> 0 <= i < k -> ~ E (a + i) ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) /\
  (forall a, rwin K S a -> writable_at segs mem' a).

End K.

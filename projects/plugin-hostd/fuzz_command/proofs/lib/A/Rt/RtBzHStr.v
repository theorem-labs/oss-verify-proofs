(* fm runtime layer: the strncmp interceptor's contract in the donor's per-call form (YG0d.v:317-419: ecall_pre,
   argument registers, range premises on aview, SRr to the return address with AR kept, callee-saved registers kept,
   same_but_materialized, a memory frame), the pure model of its answer, and the posts of a runtime call that writes
   nothing but its stack window (rt_post_ro; rt_post_roU inside fm's user-poison window). Statements only; no program
   module. The walk is in lib/A/RtLStrncmp.v; the program part (lib/A/FMH_Rt.v) re-exports this file. *)
(* Relocated to plugin-hostd/fuzz_command from omx-clap-core/fuzz_manifest's program-free split
   (proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_RtStr.v): module paths; fm's poison-window post (rt_post_roU) left
   out. The interceptor of this image is ___interceptor_strncmp 0x45f58. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtBzHBase.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure model of the answer ---- *)
(* strncmp (s1, s2, k) = 0: the first k bytes of each string with its NUL agree (C stops at the first NUL) *)
Definition strn_eq (k : nat) (l1 l2 : list Z) : Prop := firstn k (l1 ++ [0]) = firstn k (l2 ++ [0]).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* the post of a call that writes nothing but its stack window: return to ra, AR kept, a0 = v with R v *)
Definition rt_post_ro (STK : Z) ly S W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* strncmp interceptor (0x45f58): compares itself, READ_RANGE (s1, min (i1 + 1, n)), (s2, min (i2 + 1, n)) *)
Definition astrncmp_realizes (pc : Z) : Prop :=
  forall ly S W regs mem md x y n (l1 l2 : list Z),
  ecall_pre_k segs B STK_RT_STR ly S W regs mem md -> rom_viewN segs B W mem -> rom_viewO segs B W mem ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  cstr_ok segs W mem x l1 -> cstr_ok segs W mem y l2 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (rt_post_ro STK_RT_STR ly S W regs mem md (fun v => v = 0 <-> strn_eq (Z.to_nat n) l1 l2)).
End c.

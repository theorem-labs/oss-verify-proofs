From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import VerbsB.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Let segs := ms_segs B.

(* The memory facts every fuzz_command Kind B contract carries in its start state and gives back at
   its return: read-only segments agree with the image, the GNU_RELRO range holds its image bytes,
   and the stack guard word holds some canary and is writable. The canary is existential: no frame
   claim keeps the guard word across an allocator call (AllocExtra.ax_statics gives some value). *)
Definition cmd_mem (mem : word -> option byte) : Prop :=
  ro_agree segs mem /\ G_img_c B frame_RELRO mem /\
  (exists can, le_at B mem SSP_GUARD_B (Mem.le8 can)) /\
  (forall i, 0 <= i < 8 -> writable_at segs mem (SSP_GUARD_B + i)).

Definition in_live (L : layout) (A : astate) (O : list (Z * Z)) (a len : Z) : Prop :=
  exists p k, In (p, k) (blocks L A) /\ ~ In p (map fst O) /\ p <= a /\ a + len <= p + k.

Definition blocks_stay (L : layout) (A : astate) (O : list (Z * Z)) (L' : layout) (A' : astate) : Prop :=
  forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> In pn (blocks L' A').

(* call_post_k with the block-bytes clause restricted to blocks whose (address, size) is not in O:
   a function that frees the recorder-owned blocks O and lets later allocations reuse their slots
   cannot keep those bytes. Everything else is call_post_k's text. *)
Definition call_post_ko (MR : MR_t) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (E : Z -> Prop) (O : list (Z * Z))
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k B stk regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ In (ptr_addr L p) (map fst O) -> 0 <= i < n ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k B stk regs a -> writable_at segs mem' a).

End K.

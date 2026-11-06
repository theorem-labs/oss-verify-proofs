From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat RtFDefs.
Import ListNotations.
Open Scope Z_scope.

(* ___interceptor_vfprintf 0x497a4 of the pinned fuzz_command.asan (45 instructions, objdump), entered through the
   trampoline 0x45174 (one j), which musl vsnprintf calls at 0x9e52c:
     0x497a4  addi sp,-48; save ra, s0, s1, s2 at sp+40 .. sp+16; s2 = a2, s0 = a1, s1 = a0; sd a2, 8(sp)
     0x497c8  jal TryAsanInitFromRtl 0x5f640: lb of the init cell 0xb1d98 (a record cell, 1), so it returns 1
     0x497cc  beqz a0 (not taken); a0 = [0xa63e0] = 0x142be8 (record); sd a2, 0(sp) (the va_copy)
     0x497e4  beqz on the byte 0x142be8 + 84 (check_printf, a record cell, 1): not taken
     0x497f8  jal printf_common 0x48cdc (a0 = 0x1ecc1, a1 = fmt, a2 = the copy of ap)
     0x49800  a3 = [0xa8190] = 0x9b364 (REAL(vfprintf), record); a0, a1, a2 = the arguments; 0x49810 jalr a3
     0x49814  restore ra, s0, s1, s2; addi sp,48; ret (a0 = musl's return value)
   The path at 0x4982c (TryAsanInitFromRtl returns 0) is not taken under the record. The interceptor's window is its
   frame and the larger of the two callee windows below it: musl vfprintf's (K, any) and printf_common's (PCOM_STK). *)
Definition VFI_FRAME : Z := 48.
Definition PC_vfi_pcom_ret : Z := 0x497fc.
Definition PC_vfi_ret : Z := 0x49814.
Definition vfi_stk (K : Z) : Z := VFI_FRAME + Z.max PCOM_STK K.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.

Local Notation PRE stk := (ecall_pre_stk segs B stk).
Local Notation RD stk := (aread_ok segs stk).
Local Notation STR := (astr_at segs).
Local Notation POST stk := (art_post segs B stk).

(* A pre-condition of an entry: a property of the state it starts in. *)
Definition apre_t : Type :=
alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

(* musl vfprintf at [pc], for one pre-condition [P] and one post-condition in art_post form at the window [K], with the
   footprint [E] (outside its window it writes only E) and [Q] of the value it returns in a0 and the memory it leaves.
   A contract over all arguments gives one of these per call: P pins the arguments, E and Q are the ones of those
   arguments. *)
Definition avf_realizes (K : Z) (P : apre_t) (E : Z -> Prop) (Q : word -> (word -> option byte) -> Prop)
(pc : Z) : Prop :=
forall ly S W regs mem md,
PRE K ly S W regs mem md -> P ly S W regs mem md ->
SRr segs W (cfg_at segs pc regs mem md)
(POST K ly S W regs mem md E (fun regs' mem' => Q (getr regs' 10) mem')).

(* The state (regs1, mem1, md1) in which the interceptor, entered in (regs, mem, md), calls musl vfprintf at 0x49810:
   the stack pointer 48 lower, the return address 0x49814, the three arguments, gp, tp and s3 .. s11 as at entry, the
   memory as at entry outside the interceptor's frame and printf_common's window below it, every present byte still
   present. *)
Definition avfi_call (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
getr regs1 2 = w64 (spZ regs - VFI_FRAME) /\ getr regs1 1 = w64 PC_vfi_ret /\
getr regs1 10 = getr regs 10 /\ getr regs1 11 = getr regs 11 /\ getr regs1 12 = getr regs 12 /\
getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
(forall r, 19 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
AR segs B ly S W mem1 md1 /\ same_but_materialized md md1 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - VFI_FRAME - PCOM_STK <= a < spZ regs) ->
aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a).

(* The interceptor at [pc] (0x497a4, or the trampoline 0x45174), for the pre-condition [Pi] at its entry, printf_common's
   premises (RtFDefs.v apcommon_realizes: the format, the va_list slots, the arguments) at its window, a footprint E
   that keeps out of its own frame, and the same post-condition as musl vfprintf's at the window vfi_stk K. *)
Definition avfi_realizes (K : Z) (Pi : apre_t) (E : Z -> Prop) (Q : word -> (word -> option byte) -> Prop)
(pc : Z) : Prop :=
forall ly S W regs mem md f ap fmt ps args T rs D N,
PRE (vfi_stk K) ly S W regs mem md -> Pi ly S W regs mem md ->
getr regs 11 = w64 f -> getr regs 12 = w64 ap -> 0 < f ->
STR W mem f (PF.pf_bytes fmt) ->
PF.pf_parse fmt = Some ps -> PF.pf_text ps args = Some T ->
RD (vfi_stk K) W regs mem f (Z.of_nat (length fmt) + 1) ->
atail_vis segs W mem (f + Z.of_nat (length fmt)) ->
aslots_ok segs (vfi_stk K) W regs mem ap rs ->
apf_args_ok segs (vfi_stk K) W regs mem D N rs args ->
rt_rom_view segs B W mem ->
(forall a, spZ regs - VFI_FRAME <= a < spZ regs -> ~ E a) ->
SRr segs W (cfg_at segs pc regs mem md)
(POST (vfi_stk K) ly S W regs mem md E (fun regs' mem' => Q (getr regs' 10) mem')).

(* THE TRANSFORMER. For any window K, pre-conditions Pi (at the interceptor's entry) and P (at musl vfprintf's entry)
   such that Pi gives P in every state the interceptor calls musl in, and any post (E, Q): if musl vfprintf 0x9b364
   realizes P -> (E, Q) at K, the interceptor realizes Pi and printf_common's premises -> (E, Q) at vfi_stk K, at
   0x497a4 and at the trampoline 0x45174. A contract that keeps a sink in its caller's frame (the SNK form of
   omx-clap-core/fuzz_manifest lib/A/FMsnprintfI.v) takes P = the sink and its cells, E = the sink cells and the
   destination, Q = the returned length and the new sink. *)
Definition avfi_transform : Prop :=
forall K (Pi P : apre_t) (E : Z -> Prop) (Q : word -> (word -> option byte) -> Prop),
(forall ly S W regs mem md regs1 mem1 md1,
Pi ly S W regs mem md -> avfi_call ly S W regs mem md regs1 mem1 md1 -> P ly S W regs1 mem1 md1) ->
avf_realizes K P E Q PC_musl_vfprintf ->
avfi_realizes K Pi E Q PC_vfprintf_icpt /\ avfi_realizes K Pi E Q PC_vfprintf_tramp.

End c.
End b.

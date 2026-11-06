(* reac-pw/fuzz_link, image A (pin 059dae63e07c): the LAST flush of link's memory FILE, at process exit, AFTER the
   memory-checking runtime's module destructor.

   The exit path (lib/A/AE23.v): LLVMFuzzerTestOneInput returns, the driver calls exit, and the destructor list is
   run: X2 = 0x8864c (lib/A/AE37.v x2_realizes, in the form `xret_realizes_noar`) rewrites the shadow of every
   global -- g_said's shadow bytes 0x800bdfdc..0x800be25c among them -- and the runtime's own cell 0xa6d80. After
   X2 there is NO AR: the frame itself states X2 in the no-AR form, because its post breaks the shadow invariant
   AR carries. Then __stdio_exit walks the open-file list and calls close_file on link's FILE, whose flush is
   mwrite(f, 0, 0) (AMemFileT06.v, head), and mwrite's copy is the memcpy interceptor 0x52d74.

   So the contract of that flush cannot be the one of LinkRwDefs.v (`amwrite_mf_flush_realizes`), whose premise
   `ecall_pre` opens with `AR segs B ly S W mem md` and whose buffer premise `amf_buf_ok` asks `~ aowned B ly S a`.
   This file states the same flush over PLAIN MEMORY FACTS, so that it can be applied where AR is gone. It uses
   the no-AR vocabulary of the frame's lib/A/AsanNoAR.v:
   - `aecall_pre_noar segs B K`: what `ecall_pre` says minus AR -- the return register, the aligned stack pointer
     above kHighMemBeg + K, the K present bytes below it, and gp / tp;
   - `acells_ok segs m icpt_rodata`: the runtime's own cells the memcpy interceptor reads (lib/A/AE2y.v
     icpt_rodata). None of them is in X2's write set, so the caller carries them across X2 from the AR state
     before it (lib/A/AE31.v icpt_cells_of_AR);
   - `aintrin_noar_realizes OCpy icpt_rodata K 0x52d74`: the memcpy interceptor without AR, which the frame proves
     (lib/A/AE31.v memcpy_icpt_noar_realizes, for every K >= ESTACK).
   and adds the group's own two:
   - `amf_buf_ok_noar`: what `amf_buf_ok` says minus `~ aowned B ly S a` -- every byte of g_said writable and
     outside the window, the range in application memory, addressable in the shadow map, its shadow hull readable.
     (Addressability is a fact ABOUT THE MEMORY, and X2 has just written those shadow bytes, so the caller must
     carry it from X2's post, not from AR.)
   - `amf_block_noar`: the FILE's 1304 bytes with no allocator ledger to hold them;
   and the flush itself, `amwrite_mf_flush_noar_realizes cells pc`, the statement this group owes the exit lane.

   The FILE's words, the pending bytes and the cookie are the same vocabulary as everywhere else in this group
   (LinkMfDefs.v amf_k, amf_dyn, amf_pend, azbytes, amf_n1), because it is the same FILE.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AE2y AsanNoAR AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable MS : amemfile_syms.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* `amf_buf_ok` (LinkMfDefs.v) minus `~ aowned B ly S a`: g_said's bytes writable and outside the window, the
   range in application memory, addressable in the shadow map, its shadow hull readable. The addressability is
   a fact about the memory, and the module destructor has just rewritten those shadow bytes, so the caller
   carries it from the destructor's post, not from AR. *)
Definition amf_buf_ok_noar (K : Z) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  0 <= amf_buf MS /\ amf_buf MS + amf_size MS <= 2 ^ 63 /\ 0 < amf_size MS < 2 ^ 32 /\
  (forall a, amf_buf MS <= a < amf_buf MS + amf_size MS ->
     writable_at segs (rd W mem) a /\ ~ (spZ regs - K <= a < spZ regs)) /\
  amem_range (amf_buf MS) (amf_size MS) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (amf_buf MS) (amf_size MS) /\
  shadow_hull_vis (aview segs (w_H W) mem) (amf_buf MS) (amf_size MS).

(* The FILE's block, with no allocator ledger to hold it: its bytes present, writable and off the image. *)
Definition amf_block_noar (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (K f : Z) : Prop :=
  0 < f /\ f + AMF_BLOCK <= 2 ^ 63 /\ f mod 16 = 0 /\
  (forall a, f <= a < f + AMF_BLOCK ->
     apresent (w_H W) mem a /\ writable_at segs (rd W mem) a /\ ~ in_img segs a /\
     ~ (spZ regs - K <= a < spZ regs)) /\
  amem_range f AMF_BLOCK /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF f AMF_BLOCK /\
  shadow_hull_vis (aview segs (w_H W) mem) f AMF_BLOCK.


(* mwrite(f, 0, 0) at the post-destructor state: the same case split and the same post as
   `amwrite_mf_flush_realizes` (LinkRwDefs.v), with AR dropped on both sides, the interceptor's own cells
   carried by the caller, and the hidden-byte clause the no-AR forms add. *)
Definition amwrite_mf_flush_noar_realizes (cells : list (Z * Z * list (Z * N * Z))) (pc : Z) : Prop :=
  forall W regs mem md (f k fl om wend wpos wbase pos len : Z) (pb : list Z),
  aecall_pre_noar segs B AMW_STK W regs mem ->
  acells_ok segs (rd W mem) cells ->
  getr regs 10 = w64 f -> getr regs 11 = w64 0 -> getr regs 12 = w64 0 ->
  amf_block_noar W regs mem AMW_STK f ->
  amf_k segs MS (rd W mem) f k ->
  amf_dyn segs MS (rd W mem) f fl om wend wpos wbase pos len ->
  amf_pend segs (rd W mem) f pb -> Z.of_nat (length pb) = k ->
  amf_buf_ok_noar AMW_STK W regs mem ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       let n1 := amf_n1 MS k pos in
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 0 /\
       amf_k segs MS (rd W mem') f 0 /\ amf_pend segs (rd W mem') f pb /\
       azbytes segs (rd W mem') (amf_buf MS + pos) (firstn (Z.to_nat n1) pb) /\
       (n1 < k -> amf_dyn segs MS (rd W mem') f (Z.lor fl AF_ERR) om 0 0 0 (pos + n1) (Z.max len (pos + n1))) /\
       (n1 = k -> amf_dyn segs MS (rd W mem') f fl om wend wbase wbase (pos + k) (Z.max len (pos + k))) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - AMW_STK <= a < spZ regs) -> ~ (f <= a < f + AMF_ZEROED) ->
          ~ (amf_buf MS <= a < amf_buf MS + amf_size MS) -> ~ (as_errno B <= a < as_errno B + 4) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       hs_kept (w_H W) mem mem' /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (forall a, spZ regs - AMW_STK <= a < spZ regs -> apresent (w_H W) mem' a)).

End x.

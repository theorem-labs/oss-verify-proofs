(* libreac/fuzz_boxreg: amem8_of_block, the +8 address bound of the snprintf contract's string argument (P3 of R2,
   lib/A/Rt/SnprintfDef.v / lib/B/Rt/SnprintfDefB.v) for a string that lies inside a heap block, from AR_blocks_law
   alone. Image-neutral (any segs, any B with AR_laws): both images' declare walks use it.
   Why a new helper: a Theorem Labs lane's amem8_of_high (lib/A/Rt/FMsnprintfSx.v) needs kHighMemBeg <= d and 8 bytes of room below
   alloc_ceiling. AR_blocks_law's in_app also admits a block in low memory, and a block may end exactly at
   alloc_ceiling. The bound holds anyway: a low block lies below kLowShadowBeg = kLowMemEnd - 0x1000, and a high block
   below alloc_ceiling <= ASAN_CEIL, far below kHighMemEnd.
   Measured and first proved in the Theorem Labs lane scratch (a Theorem Labs lane's boxpa/r2-sites.md, appendix).
   Rule 24: proves no function (kind: segment lemma; an address-arithmetic fact from the allocator's block law). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
(* A string at a inside the heap block (p, m), its NUL at most the block's last byte: amem_range a (w + 8). *)
Lemma amem8_of_block : forall ly S W mem md p m a w, AR_laws segs B ->
  AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> 0 <= w -> a + w + 1 <= p + req_size m ->
  amem_range a (w + 8).
Proof.
intros ly S W mem md p m a w LAWS HAR Hin H1 H2 H3.
destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hin) as (_ & H4096 & Hceil & Happ & _).
pose proof ASAN_CEIL_range as [CR _].
unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
End s.

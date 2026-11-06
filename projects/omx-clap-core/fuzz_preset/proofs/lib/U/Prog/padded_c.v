From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of the #102 twin pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan (sha256
   27566683952ebd54...), the unstripped twin of the pinned fuzz_preset.ubsan 45b0357d18ff66cd... (facts 8f3e7e1a07f1):
     padded FUNC LOCAL 0x1448c size 148 (37 insns): addi sp, sp, -0x30; ra, s0..s3 saved at sp + 0x28 .. sp + 8;
     s1 = fill, s2 = size, s3 = data; jal malloc (0x18390) with a0 = size + 16; s0 = a0; a NULL goes to 0x144f0, which
     stores 1 into g_own_ran_out (0x35250) and returns NULL; otherwise memcpy (0x22520) of size bytes when size <> 0,
     UBSan's pointer-overflow test `not a0, s0; bltu a0, s2` (trap at 0x1451c), memset (0x22924) of 16 bytes of fill
     at s0 + size; returns s0.  Its only caller is check_no_overread (jal at 0x1389c, 0x138b0, 0x138c4).
   Source: fuzz_preset.c of #102, lines 509-521: padded(data, size, fill) = noted(malloc(size + FUZZ_PAD)) and, when it
   is not NULL, the copy of the input followed by FUZZ_PAD = 16 bytes of fill.
   Under rf_room the malloc is not refused (malloc_contract_r), so the NULL arm is not reached: g_own_ran_out is not
   written, and the post is malloc's (malloc_ret_r, at padded's stack bound PADDED_K) with the block holding the copy.
   The pointer-overflow trap is not reached either: q + size + 16 <= alloc_ceiling < 2 ^ 63 (fresh_block). *)
Definition PADDED : Z := 0x1448c.
Definition PADDED_F : Z := 48.
Definition PADDED_K : Z := PADDED_F + ALLOC_STACK.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition padded_contract : Prop :=
  forall L A regs mem md b (d n fill : Z) (x : list byte),
    call_pre_k B MR PADDED_K L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 fill ->
    0 <= fill < 256 -> Z.of_nat (length x) = n -> n <= 0x300000 ->
    Mem.bytes_at segs mem d x ->
    (x <> [] -> exists a k, In (a, k) (blocks L A) /\ a <= d /\ d + n <= a + k) ->
    rf_ok F A b -> rf_room F b (n + 16) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PADDED) mem (seg_rom segs)) md)
      (fun c' => malloc_ret_r B API F PADDED_K L A regs mem md (n + 16) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           Mem.bytes_at segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10)) (x ++ repeat (Z_to_bv 8 fill) 16)).

End K.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec.
Import ListNotations.
Open Scope Z_scope.

(** fuzz_catalogue_row (catalogue.c:29-35; 136 bytes, 34 instructions at 0x15d64 in the plain image; frame 48 bytes,
    saves ra, s0-s4 at sp-8 .. sp-48). With s2 = s, s1 = n, it walks s0 = FUZZ_CATALOGUE + 0x128 i for i = 0..10 (s4
    counts 11 down to 0), loads the token pointer `ld s3,0(s0)`, calls strlen(token) (0x15d9c, `jal 0x1ec30`) and, when
    it is n, bcmp(token, s, n) (0x15db0, `jal 0x1e42c`, bcmp = `j memcmp`); bcmp's 0 returns s0, else the next row.
    After row 10 it returns 0. It reads the table (.data.rel.ro, in the rw- segment [0x20000, 0x22000), so mem_inv
    does not fix it: hence the table premise), the tokens (.rodata, read-only: mem_inv makes those reads come from the
    image) and the n bytes at s (only through bcmp, and only when some token has length n: 5, 6 or 11). It writes
    only its frame [sp - 48, sp); strlen and bcmp use no stack (their contracts' munch []).

    Callee contracts its walk takes as premises (the released forms, relocated to this image):
    strlen_contract (Prog/strlen_c.v, STRLEN = 0x1ec30: bytes_at token (tok ++ NUL :: slack) with slack to the next
    8-byte boundary, from .rodata) and bcmp_contract (Prog/bcmp_c.v, BCMP = 0x1e42c, memcmp_model).

    Call site (LLVMFuzzerTestOneInput, plain): 0x12e18 `jal fuzz_catalogue_row`, reached only when strlen(spec) <> 0
    and flags & 7 = 0, with
      a0 = s0 = spec, the malloc'd block holding s ++ [NUL] (memcpy at 0x12d34, `sb zero` at 0x12d3c);
      a1 = s2 = tok, the harness's scan `while (tok < len && spec[tok] != ':')` = colon_idx s <= len;
      sp = S - 64 (the harness frame).
    Why each premise holds there: sb = firstn tok s, the first tok bytes of the block (tok <= len); the stack region
    [lo, sp) with lo = S - 65536 is the frame's stack (FR's stk and writability), above alloc_ceiling, so outside the
    image, and the block (below alloc_ceiling <= lo) lies below it; the table is in frame_RELRO [0x20a98, 0x21818), so
    FR's relro gives its image bytes; mem_inv holds of the memory the cut runs on (normalize, as in ctrl's b4_mid). *)
Definition FUZZ_CATALOGUE_ROW : Z := 0x15d64.
Definition FUZZ_CATALOGUE : Z := 0x20ad0.
Definition FCR_STACK : Z := 48.

Definition fuzz_catalogue_row_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sb : list byte) (lo : Z),
    bytes_at rsegs m (bv_unsigned a0) sb ->
    bv_unsigned a1 = Z.of_nat (length sb) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + FCR_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    (bv_unsigned a0 + Z.of_nat (length sb) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (row_ptr FUZZ_CATALOGUE sb))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - FCR_STACK, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_CATALOGUE_ROW) fc None m (seg_rom rsegs)).

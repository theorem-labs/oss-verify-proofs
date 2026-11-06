From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import tolower_c.
Import ListNotations.
Open Scope bv_scope.

(** musl strcasecmp (160 bytes, 40 instructions at 0x1ea28 in the plain image; frame 32 bytes, saves ra, s0, s1, s2 at
    sp-8 .. sp-32). It reads l (a0) and r (a1) byte by byte up to and including the first NUL of l, or of r, or the
    first index whose bytes differ after tolower (two `jal tolower` per index, at TOLOWER = 0x1eac8), never past a NUL,
    and returns the 32-bit difference of the two lowered bytes at that index. It writes only its frame; tolower
    writes no memory. Every call site in segconf (reac_segconf_parse_file: 0x14ffc, 0x15010, 0x15024, 0x15038,
    0x15160, 0x15178, 0x151a0, 0x151b4) tests the result against zero only, so the contract states the zero test:
    r = 0 exactly when the two strings are equal after tolower. The ubsan copy (U/Prog/strcasecmp_c.v, 0x1f3c4) is
    the same code at another address. *)
Definition STRCASECMP : Z := 0x1ea28.

Definition lower_eq (ls rs : list byte) : Prop :=
  map zlower (map bv_unsigned ls) = map zlower (map bv_unsigned rs).

Definition strcasecmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (ls rs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists r t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (ls ++ [Z_to_bv 8 0])
    /\ bytes_at rsegs m' (bv_unsigned a1) (rs ++ [Z_to_bv 8 0])
    /\ (r = Z_to_bv 64 0 <-> lower_eq ls rs).

Definition strcasecmp_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) (ls ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) ls ->
  bytes_at rsegs m (bv_unsigned a1) (rs ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) rs ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length ls) + 1 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length rs) + 1 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  evt rsegs (strcasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRCASECMP) fc None m (seg_rom rsegs)).

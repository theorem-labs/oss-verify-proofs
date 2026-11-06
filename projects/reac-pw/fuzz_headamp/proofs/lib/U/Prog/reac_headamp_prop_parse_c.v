From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_headamp_prop_parse(props, out, max) (reac_headamp_prop.c:102-106; 8 bytes, 2 instructions at 0x14cc8 in the
    UBSan image):
      0x14cc8 mv a3,zero; 0x14ccc j 0x14cd0 (reac_headamp_prop_parse_result).
    The plain file's tail jump (lib/Prog/reac_headamp_prop_parse_c.v): reac_headamp_prop_parse_result_contract at
    R = 0 (its res traps 0x14d20 / 0x15158 are skipped with res = NULL).

    Call site (LLVMFuzzerTestOneInput, UBSan): 0x14818 `jal reac_headamp_prop_parse` (the only one), with
    sp = S - 608 and a0 = s5 (0x1480c), a1 = s3 = out (0x14810), a2 = s2 = cap (0x14814), the first parse's
    arguments; out reset to 0xa5 at 0x14808 after memcpy(first, out, 3 rc) at 0x147f8.
    Why each premise holds there: those of the first call, as in the plain file: U/Prog/HeadSites.v parse_site_plain. *)
Definition HA_PARSE : Z := 0x14cc8.

Definition reac_headamp_prop_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (null : bool) (lo P O cap : Z)
         (bs : list byte) (ev can : word),
    a0 = Z_to_bv 64 (if null then 0 else P) -> a1 = Z_to_bv 64 O -> a2 = Z_to_bv 64 cap ->
    parse_args m lo (bv_unsigned sp) tp P O cap 0 bs ev can ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PARSE_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    frm0 fc -> mem_inv rsegs m ->
    evt rsegs
      (parse_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo O 0 (parse_props (parse_arg null bs) cap))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HA_PARSE) fc None m (seg_rom rsegs)).

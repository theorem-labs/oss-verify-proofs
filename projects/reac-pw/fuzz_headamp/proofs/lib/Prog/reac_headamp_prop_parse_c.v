From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_headamp_prop_parse(props, out, max) (reac_headamp_prop.c:102-106; 8 bytes, 2 instructions at 0x14874 in the
    plain image):
      0x14874 mv a3,zero; 0x14878 j 0x1487c (reac_headamp_prop_parse_result).
    A tail jump with res = NULL: no frame, ra kept, so reac_headamp_prop_parse_result returns to this function's
    caller. Its contract is reac_headamp_prop_parse_result_contract's at R = 0, whatever a3 holds on entry: the same
    answer parse_props (parse_arg null bs) cap (a0 = rc, out[0, 3n) = the cells), no store at any res, the same other
    writes (parse_post with R = 0: parse_writes has no res region). Its walk is these two steps and that contract.

    Call site (LLVMFuzzerTestOneInput, plain): 0x141a0 `jal reac_headamp_prop_parse` (the only one), with
    sp = S - 560 and
      a0 = s5 = (null ? 0 : pod) (0x14194), a1 = s3 = out (0x14198), a2 = s2 = cap (0x1419c): the arguments of the
      first parse at 0x140bc, kept in callee-saved registers across every call since;
    out reset to 0xa5 by memset(out, 0xa5, 3cap + 3) at 0x14190, after memcpy(first, out, 3 rc) at 0x14180.
    Why each premise holds there: those of the first call (reac_headamp_prop_parse_result_c.v's header), with the
    same pod bytes (since 0x140bc main and its callees wrote only out, first, x, res, the stack and errno; the pod
    block is apart from all of them), the same out block (writable: wmono), errno still a writable cell (the first
    parse's post) and the SSP cells unchanged (outside every munch): Prog/HeadSites.v parse_site_plain derives them from
    headamp_plain_contract's premises. *)
Definition HA_PARSE : Z := 0x14874.

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

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_role (fuzz_segconf.c:431-455; at 0x14824 in the image 3776ca44d75c; no frame on the path that returns (the 16-byte frame is set up only on the abort path, which the
    premise makes dead)).
    got_set (a0) <> want->role_set (`lw 0x14`, compared as full registers) or got_set and got (a1) <> want->role
    (`lw 0x10`) aborts.

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. With o the reader's answer (SegModel.r_role: Some r = "returned 1 and *out = r"), the premise is check_seg's first
    conjunct: match o with Some r => ms_role_set g && (r =? ms_role g) | None => negb (ms_role_set g) end = true.

    Callee contracts its walk takes as premises: none.

    Call site (LLVMFuzzerTestOneInput): 0x13b20 `jal check_role` with a0 = set, reac_segconf_role's result (0 or 1), a1 = r, main's cell loaded
    with `lw` (the role, 0..4, when set; still 0x5a when not), a2 = g = &m->seg[i] (16-aligned block + 256 i). *)
Definition CHECK_ROLE : Z := 0x14824.
Definition CHECK_ROLE_STACK : Z := 0.

Definition check_role_pre (m : word -> option byte) (sp lo gotset got want : Z) (o : option Z) (g : mseg) : Prop :=
  want mod 4 = 0 /\ mseg_at rsegs m want g /\ apart want MSEG_SIZE lo sp /\
  gotset = (match o with Some _ => 1 | None => 0 end) /\
  (match o with Some r => got = r /\ r < 2 ^ 31 | None => True end) /\
  (match o with Some r => ms_role_set g && (r =? ms_role g) | None => negb (ms_role_set g) end) = true /\
  stack_ok rsegs m lo sp CHECK_ROLE_STACK /\ mem_inv rsegs m.

Definition check_role_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (o : option Z) (g : mseg),
    check_role_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) o g ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_ROLE) fc None m (seg_rom rsegs)).

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_model (fuzz_segconf.c:457-468; at 0x14848 in the image 3776ca44d75c; frame 16 bytes).
    !same_text(got, want->model_set ? want->model : NULL) aborts: want_p = model_set ? want + 0x24 : 0 (`lw 0x20`,
    seqz/addi/and); got = want_p returns; got = 0 or model_set = 0 aborts; else strcmp(got, want + 0x24) = 0.

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. With o the reader's answer (SegModel.r_model: Some s = a non-NULL pointer to the C string s), the premise is
    check_seg's second conjunct: same_text o (if ms_model_set g then Some (ms_model g) else None) = true.

    Callee contracts its walk takes as premises: strcmp_contract (Prog/strcmp_c.v, 0x1ebf8).

    Call site (LLVMFuzzerTestOneInput): 0x13b34 `jal check_model` with a0 = reac_segconf_model's result (seg_spec.model_ptr: NULL or a field of the
    reader's block), a1 = g = &m->seg[i]. *)
Definition CHECK_MODEL : Z := 0x14848.
Definition CHECK_MODEL_STACK : Z := 16.

Definition check_model_pre (m : word -> option byte) (sp lo got want : Z) (o : option (list Z)) (g : mseg) : Prop :=
  want mod 4 = 0 /\ mseg_at rsegs m want g /\ apart want MSEG_SIZE lo sp /\
  ocstrz_at rsegs m got o /\ (match o with Some s => apart got (Z.of_nat (length s) + 1) lo sp | None => True end) /\
  same_text o (if ms_model_set g then Some (ms_model g) else None) = true /\
  stack_ok rsegs m lo sp CHECK_MODEL_STACK /\ mem_inv rsegs m.

Definition check_model_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (o : option (list Z)) (g : mseg),
    check_model_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) o g ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([(bv_unsigned sp - CHECK_MODEL_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_MODEL) fc None m (seg_rom rsegs)).

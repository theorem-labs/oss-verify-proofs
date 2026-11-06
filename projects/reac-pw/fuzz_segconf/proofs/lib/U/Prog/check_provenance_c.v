From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** check_provenance (fuzz_segconf.c:485-500; at 0x14b68 in the UBSan image 1696d6c34ffd; frame 32 bytes).
    !same_text(role_file, want->role_set ? want->role_file : NULL) or the same for ignore_file aborts, each as in
    check_model: want + 0x3c under role_set (`lw 0x14`), want + 0x9c under ignore_set (`lw 0x1c`), pointer
    equality first, then strcmp.
    UBSan: every check traps to the function's own `unimp`; the alignment, bounds and no-wrap facts of the premise
    (pointers 16- or 4-aligned, n <= 32, the objects inside the address space) make each trap branch fall through.

    The premise is exactly the spine's condition under which the check does not abort, on the encodings of its
    arguments; the abort branch (`jal abort`) is then dead. Post: it returns with no byte changed outside its frame
    and its callees' frames below sp. With orf / oif the reader's answers (SegModel.r_role_file, r_ignore_file), the premise is check_seg's last two
    conjuncts.

    Callee contracts its walk takes as premises: strcmp_contract (Prog/strcmp_c.v under lib/U, 0x1f594), twice.

    Call site (LLVMFuzzerTestOneInput): 0x13cec `jal check_provenance` with a0 = reac_segconf_role_file's result, a1 =
    reac_segconf_ignore_file's result (seg_spec.role_file_ptr / ignore_file_ptr), a2 = g = &m->seg[i]. *)
Definition CHECK_PROVENANCE : Z := 0x14b68.
Definition CHECK_PROVENANCE_STACK : Z := 32.

Definition check_provenance_pre (m : word -> option byte) (sp lo rf igf want : Z) (orf oif : option (list Z))
    (g : mseg) : Prop :=
  want mod 4 = 0 /\ mseg_at rsegs m want g /\ apart want MSEG_SIZE lo sp /\
  ocstrz_at rsegs m rf orf /\ (match orf with Some s => apart rf (Z.of_nat (length s) + 1) lo sp | None => True end) /\
  ocstrz_at rsegs m igf oif /\ (match oif with Some s => apart igf (Z.of_nat (length s) + 1) lo sp | None => True end) /\
  same_text orf (if ms_role_set g then Some (ms_role_file g) else None) = true /\
  same_text oif (if ms_ignore_set g then Some (ms_ignore_file g) else None) = true /\
  stack_ok rsegs m lo sp CHECK_PROVENANCE_STACK /\ mem_inv rsegs m.

Definition check_provenance_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (orf oif : option (list Z)) (g : mseg),
    check_provenance_pre m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) orf oif g ->
    evt rsegs
      (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
         m
         ([(bv_unsigned sp - CHECK_PROVENANCE_STACK, bv_unsigned sp)])
         lo
         (fun _ => True))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_PROVENANCE) fc None m (seg_rom rsegs)).

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import refuse_c cross_check_c reac_segconf_parse_file_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_segconf_parse(c, text) (reac_segconf.c:327-332; at 0x15e7c in the UBSan image 1696d6c34ffd; 72 bytes, 18 instructions, frame 0x20,
    saves ra, s0 = c, s1; level-3 identical in the two builds): n = reac_segconf_parse_file(c, text, "reac-pw.conf")
    (the label at seg_spec.STR_BASE in .rodata), cross_check(c), return n.

    Post in the spine's terms: a0 = snd (SegModel.r_parse rc s), c holds fst (r_parse rc s). It writes its frame,
    its callees' frames and seg_spec.RC_PARSE_W c (cross_check's writes are inside it).

    Callee contracts its walk takes as premises: reac_segconf_parse_file_contract (with lab = Some S_base, the label's
    bytes from the image by mem_inv) and cross_check_contract.

    Call site: LLVMFuzzerTestOneInput 0x13c14 (c, the last file's text), after m_file and m_cross. *)
Definition REAC_SEGCONF_PARSE : Z := 0x15e7c.
Definition PARSE_STACK : Z := 0x20 + PARSE_FILE_STACK.

Definition reac_segconf_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (rc : rconf) (s : list Z),
    reader_pre PARSE_STACK m fc (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) rc s ->
    evt rsegs
      (ret_post_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
         (snd (r_parse rc s))
         m
         ((bv_unsigned sp - PARSE_STACK, bv_unsigned sp) :: RC_PARSE_W (bv_unsigned a0))
         lo
         (fun m' => rconf_at rsegs m' (bv_unsigned a0) (fst (r_parse rc s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_SEGCONF_PARSE) fc None m (seg_rom rsegs)).

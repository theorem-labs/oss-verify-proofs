(** The walk of fuzz_segconf's check_provenance in the plain image (Prog/check_provenance_c.v), written new for
    reac-pw/fuzz_segconf. strcmp is a premise (strcmp_contract, Prog/strcmp_c.v, 0x1ebf8), called twice. The pure
    lemmas are check_model's (Prog/check_model.v).

    Code (image 3776ca44d75c):
      0x148a0 addi sp,sp,-32; sd ra,24(sp); sd s0,16(sp); sd s1,8(sp); mv s1,a2; mv s0,a1
      0x148b8 lw a2,0x14(a2); seqz a3,a2; addi a1,s1,0x3c; addi a3,a3,-1; and a3,a3,a1
      0x148cc beq a0,a3 -> 0x148e0; beqz a0 -> abort; beqz a2 -> abort; jal strcmp; bnez a0 -> abort
      0x148e0 lw a0,0x1c(s1); seqz a2,a0; addi a1,s1,0x9c; addi a2,a2,-1; and a2,a2,a1
      0x148f4 beq s0,a2 -> 0x1490c; beqz s0 -> abort; beqz a0 -> abort; mv a0,s0; jal strcmp; bnez a0 -> abort
      0x1490c ld ra,24(sp); ld s0,16(sp); ld s1,8(sp); addi sp,sp,32; ret; 0x14920 jal abort
    The role_file check (want + 0x3c under role_set) ends at 0x148e0 on each of its paths; the ignore_file check
    (want + 0x9c under ignore_set) from there is SECOND below. Each is check_model's pattern: same_text leaves NULL
    under a clear flag, or a C string equal to the field under a set flag. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec strcmp_c check_provenance_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_model.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_model.
Import ListNotations.
Open Scope Z_scope.

Theorem check_provenance_holds : strcmp_contract -> check_provenance_contract.
Proof.
  intros SC. unfold strcmp_contract, STRCMP in SC.
  unfold check_provenance_contract, check_provenance_pre, CHECK_PROVENANCE, CHECK_PROVENANCE_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    orf oif g
    (AL & (bs & BS & ENC) & AP & OC1 & AO1 & OC2 & AO2 & SAME1 & SAME2 & (ST & DP & SPA & NR) & MI).
  unfold apart, MSEG_SIZE in AP.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1. cbn in RA1.
  pose proof (bv_unsigned_in_range 64 a2) as RA2. unfold bv_modulus in RA2. cbn in RA2.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct ENC as (LEN & _ & _ & FR1 & _ & FI2 & _ & _ & CRF & CIF & _).
  pose proof (bytes_at_bound _ _ _ _ BS) as BB.
  pose proof (ck_fld_at rsegs m _ _ MS_ROLE_SET 4 BS ltac:(unfold MS_ROLE_SET; lia) ltac:(lia)
                ltac:(unfold MS_ROLE_SET; rewrite LEN; lia)) as BF1.
  pose proof (ck_fld_at rsegs m _ _ MS_IGNORE_SET 4 BS ltac:(unfold MS_IGNORE_SET; lia) ltac:(lia)
                ltac:(unfold MS_IGNORE_SET; rewrite LEN; lia)) as BF2.
  pose proof (ck_fld_at rsegs m _ _ MS_ROLE_FILE 96 BS ltac:(unfold MS_ROLE_FILE; lia) ltac:(lia)
                ltac:(unfold MS_ROLE_FILE; rewrite LEN; lia)) as BRF.
  pose proof (ck_fld_at rsegs m _ _ MS_IGNORE_FILE 96 BS ltac:(unfold MS_IGNORE_FILE; lia) ltac:(lia)
                ltac:(unfold MS_IGNORE_FILE; rewrite LEN; lia)) as BIF.
  destruct (ck_cstrz rsegs m _ _ _ _ BRF CRF) as (sy1 & BY1 & ZY1 & NY1 & LY1).
  destruct (ck_cstrz rsegs m _ _ _ _ BIF CIF) as (sy2 & BY2 & ZY2 & NY2 & LY2).
  unfold flag_enc in FR1, FI2. rewrite FR1 in BF1. rewrite FI2 in BF2.
  unfold MS_ROLE_SET in BF1. unfold MS_IGNORE_SET in BF2. unfold MS_ROLE_FILE in BY1. unfold MS_IGNORE_FILE in BY2.
  clear FR1 FI2 BRF BIF CRF CIF BS.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
  do 2 zstep.
  (* SECOND, 0x148e0: the ignore_file check, with s0 = ignore_file pointer, s1 = want, ra a0-a3 any. *)
  lazymatch goal with |- evt _ ?Q _ =>
    assert (SECOND : forall x1 x10 x11 x12 x13 : word,
      evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a1 a2 x10 x11 x12 x13 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 84192) fc None M1 (seg_rom rsegs)))
  end.
  { intros x1 x10 x11 x12 x13.
    revert BF2 SAME2. destruct (ms_ignore_set g) eqn:EI; destruct oif as [s|]; intros BF2 SAME2;
      cbn [same_text] in SAME2; cbv beta iota in BF2; try discriminate SAME2.
    - (* ignore_set = 1, the ignore_file answer a C string equal to the field *)
      apply Z.eqb_eq in SAME2.
      destruct OC2 as (NZ1 & gy & BGY & ZGY & NIN). subst s.
      assert (NGY : ~ In (Z_to_bv 8 0) gy) by (intros H; apply NIN; exact (in_map bv_unsigned _ _ H)).
      rewrite <- ZY2 in SAME2. apply (proj1 (bridge_strcmp gy sy2 NGY NY2)) in SAME2. subst sy2.
      unfold apart, zs in AO2. rewrite length_map in AO2.
      ck_transport BGY.
      rewrite ck_le4_1 in BF2.
      assert (RDF : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned a2 + 28)) 4 =
                    Some [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by exact (ck_read_all rsegs M1 _ _ BF2).
      do 5 zstep.
      replace ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615 by reflexivity.
      rewrite ck_land_ones by lia.
      (* beq s0, a2: taken (pointer = want + 0x9c) to the return *)
      zstep. if_cases K.
      + do 5 zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I.
      + (* beqz s0: not NULL; beqz a0: ignore_set = 1 *)
        zstep. if_cases K1; [exfalso; zify_cond K1; lia|].
        zstep. if_false.
        (* mv a0,s0; jal strcmp(ignore_file pointer, want + 0x9c) *)
        zstep. zstep.
        eapply evt_cut.
        { eapply SC; [exact BGY | exact NGY | rewrite unsigned_lit by lia; exact BY2 | exact NGY]. }
        intros ms' (r & y11 & y12 & y13 & -> & HR). ck_fix_ret.
        assert (R0 : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r.
        (* bnez a0: strcmp returned 0 *)
        zstep. if_false.
        do 5 zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I.
    - (* ignore_set = 0, the answer NULL *)
      rewrite ck_le4_0 in BF2. cbn [ocstrz_at] in OC2.
      assert (RDF : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned a2 + 28)) 4 =
                    Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by exact (ck_read_all rsegs M1 _ _ BF2).
      do 5 zstep.
      replace ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) with 0 by reflexivity.
      rewrite Z.land_0_l.
      zstep. if_cases K; [|exfalso; zify_cond K; lia].
      do 5 zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I. }
  (* The role_file check, 0x148b8 to 0x148e0. *)
  revert BF1 SAME1. destruct (ms_role_set g) eqn:ER; destruct orf as [s|]; intros BF1 SAME1;
    cbn [same_text] in SAME1; cbv beta iota in BF1; try discriminate SAME1.
  - (* role_set = 1, the role_file answer a C string equal to the field *)
    apply Z.eqb_eq in SAME1.
    destruct OC1 as (NZ0 & gx & BGX & ZGX & NIN). subst s.
    assert (NGX : ~ In (Z_to_bv 8 0) gx) by (intros H; apply NIN; exact (in_map bv_unsigned _ _ H)).
    rewrite <- ZY1 in SAME1. apply (proj1 (bridge_strcmp gx sy1 NGX NY1)) in SAME1. subst sy1.
    unfold apart, zs in AO1. rewrite length_map in AO1.
    ck_transport BGX.
    rewrite ck_le4_1 in BF1.
    assert (RDF : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned a2 + 20)) 4 =
                  Some [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by exact (ck_read_all rsegs M1 _ _ BF1).
    do 5 zstep.
    replace ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615 by reflexivity.
    rewrite ck_land_ones by lia.
    (* beq a0, a3: taken (pointer = want + 0x3c) to SECOND *)
    zstep. if_cases K.
    + apply SECOND.
    + (* beqz a0: not NULL; beqz a2: role_set = 1 *)
      zstep. if_cases K1; [exfalso; zify_cond K1; lia|].
      zstep. if_false.
      (* jal strcmp(role_file pointer, want + 0x3c) *)
      zstep.
      eapply evt_cut.
      { eapply SC; [exact BGX | exact NGX | rewrite unsigned_lit by lia; exact BY1 | exact NGX]. }
      intros ms' (r & y11 & y12 & y13 & -> & HR). ck_fix_ret.
      assert (R0 : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r.
      (* bnez a0: strcmp returned 0 *)
      zstep. if_false.
      apply SECOND.
  - (* role_set = 0, the answer NULL *)
    rewrite ck_le4_0 in BF1. cbn [ocstrz_at] in OC1.
    assert (RDF : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned a2 + 20)) 4 =
                  Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by exact (ck_read_all rsegs M1 _ _ BF1).
    do 5 zstep.
    replace ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) with 0 by reflexivity.
    rewrite Z.land_0_l.
    zstep. if_cases K; [|exfalso; zify_cond K; lia].
    apply SECOND.
Qed.

(** The walk of fuzz_segconf's check_model in the UBSan image (U/Prog/check_model_c.v), written new for
    reac-pw/fuzz_segconf. strcmp is a premise (strcmp_contract, U/Prog/strcmp_c.v, 0x1f594). The pure lemmas are
    the plain walk's (Prog/check_model.v).

    Code (image 1696d6c34ffd): the plain walk's with the
    alignment test of want first:
      0x14af4 addi sp,sp,-16; 0x14af8 sd ra,8(sp); 0x14afc andi a2,a1,3; 0x14b00 bnez a2 -> 0x14b3c unimp
      0x14b04 lw a2,0x20(a1); seqz a3,a2; addi a1,a1,0x24; addi a3,a3,-1; and a3,a3,a1
      0x14b18 beq a0,a3 -> 0x14b2c; 0x14b1c beqz a0 -> abort; 0x14b20 beqz a2 -> abort
      0x14b24 jal strcmp; 0x14b28 bnez a0 -> abort
      0x14b2c ld ra,8(sp); addi sp,sp,16; ret; 0x14b38 jal abort; 0x14b3c unimp
    want mod 4 = 0 (the premise) makes the trap branch fall through. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strcmp_c check_model_c.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_model.
Import ListNotations.
Open Scope Z_scope.

Theorem check_model_holds : strcmp_contract -> check_model_contract.
Proof.
  intros SC. unfold strcmp_contract, STRCMP in SC.
  unfold check_model_contract, check_model_pre, CHECK_MODEL, CHECK_MODEL_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo o g
    (AL & (bs & BS & ENC) & AP & OC & AO & SAME & (ST & DP & SPA & NR) & MI).
  unfold apart, MSEG_SIZE in AP.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1. cbn in RA1.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct ENC as (LEN & _ & _ & _ & _ & _ & FM & CM & _ & _ & _).
  pose proof (bytes_at_bound _ _ _ _ BS) as BB.
  pose proof (ck_fld_at rsegs m _ _ MS_MODEL_SET 4 BS ltac:(unfold MS_MODEL_SET; lia) ltac:(lia)
                ltac:(unfold MS_MODEL_SET; rewrite LEN; lia)) as BF.
  pose proof (ck_fld_at rsegs m _ _ MS_MODEL 24 BS ltac:(unfold MS_MODEL; lia) ltac:(lia)
                ltac:(unfold MS_MODEL; rewrite LEN; lia)) as BM0.
  destruct (ck_cstrz rsegs m _ _ _ _ BM0 CM) as (sy & BY & ZY & NY & LY).
  unfold flag_enc in FM. rewrite FM in BF. unfold MS_MODEL_SET in BF. unfold MS_MODEL in BY.
  clear FM BM0 CM.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  revert BF SAME. destruct (ms_model_set g) eqn:EMS; destruct o as [s|]; intros BF SAME;
    cbn [same_text] in SAME; cbv beta iota in BF; try discriminate SAME.
  - (* model_set = 1, got = the C string s, equal to the model *)
    apply Z.eqb_eq in SAME.
    destruct OC as (NZ0 & gx & BGX & ZGX & NIN). subst s.
    assert (NGX : ~ In (Z_to_bv 8 0) gx) by (intros H; apply NIN; exact (in_map bv_unsigned _ _ H)).
    rewrite <- ZY in SAME. apply (proj1 (bridge_strcmp gx sy NGX NY)) in SAME. subst sy.
    unfold apart, zs in AO. rewrite length_map in AO.
    rewrite ck_le4_1 in BF. clear NIN.
    carve_frame 16%nat ST.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
    (* andi a2,a1,3; bnez a2 -> unimp: want is 4-aligned *)
    zstep. zstep. if_cases KA; [exfalso; zify_cond KA; rewrite ?ck_land3 in KA; lia|].
    assert (RDF : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned a1 + 32)) 4 =
                  Some [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by exact (ck_read_all rsegs M1 _ _ BF).
    do 5 zstep.
    replace ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615 by reflexivity.
    rewrite ck_land_ones by lia.
    (* beq a0, a3: taken (got = want + 0x24) to the return *)
    zstep. if_cases K.
    + zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I.
    + (* beqz a0: got <> NULL *)
      zstep. if_cases K1; [exfalso; zify_cond K1; lia|].
      (* beqz a2: model_set = 1 *)
      zstep. if_false.
      (* jal strcmp(got, want + 0x24) *)
      zstep.
      eapply evt_cut.
      { eapply SC; [exact BGX | exact NGX | rewrite unsigned_lit by lia; exact BY | exact NGX]. }
      intros ms' (r & x11 & x12 & x13 & -> & HR). ck_fix_ret.
      assert (R0 : r = Z_to_bv 64 0) by (apply HR; reflexivity). subst r.
      (* bnez a0: strcmp returned 0 *)
      zstep. if_false.
      zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I.
  - (* model_set = 0, got = NULL *)
    rewrite ck_le4_0 in BF.
    carve_frame 16%nat ST.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
    zstep. zstep. if_cases KA; [exfalso; zify_cond KA; rewrite ?ck_land3 in KA; lia|].
    assert (RDF : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned a1 + 32)) 4 =
                  Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by exact (ck_read_all rsegs M1 _ _ BF).
    do 5 zstep.
    replace ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) with 0 by reflexivity.
    rewrite Z.land_0_l.
    (* beq a0, a3 with a0 = a3 = 0: taken to the return *)
    zstep. if_cases K; [|exfalso; zify_cond K; cbn [ocstrz_at] in OC; lia].
    zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). finish; try exact I.
Qed.

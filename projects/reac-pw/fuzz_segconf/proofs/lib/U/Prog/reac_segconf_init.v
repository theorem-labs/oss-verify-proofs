(** reac_segconf_init (UBSan build, 0x15238): proof of [reac_segconf_init_contract] (U/Prog/reac_segconf_init_c.v)
    from memset's contract (U/Prog/memset_c.v). The UBSan code is the plain code (level-3 identical, no check): this
    is lib/Prog/reac_segconf_init.v over the UBSan image.

    Code (the UBSan binary): `lui a1,4; addiw a2,a1,0xe8; mv a1,zero; j memset`
    (0x1f2cc). No frame: the tail call runs memset(c, 0, 16616) with the caller's ra and sp, so memset's post is the
    function's: a0 = c kept, [c, c + 16616) written with zeros (Z_to_bv 8 (0 mod 256) = ZERO), which encode rconf0
    (seg_spec.rconf_enc_zero); the stack region [lo, sp) is apart from c, so it stays present. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import memset_c reac_segconf_init_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_segconf_init_holds : memset_contract -> reac_segconf_init_contract.
Proof.
  intros HMS. unfold reac_segconf_init_contract, REAC_SEGCONF_INIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    (Hc0 & Hc16 & [junk HR] & (ST & HK & HS16 & HW) & HAP & MI).
  step. step. step. step.
  (* memset's entry 0x1e930 with a1 = 0, a2 = 16616, the caller's ra. *)
  eapply evt_cut.
  { eapply HMS with (junk := junk); [ | exact MI]. rewrite ?unsigned_lit by lia. exact HR. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
              MU & WM & MI' & RW).
  rewrite ?unsigned_lit in MU, RW by lia.
  destruct RW as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply evt_done. unfold ret_post. cbv beta.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [rewrite Z_to_bv_lit_self; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  split.
  { eapply stk_transport_disjoint; [exact ST | exact MU | exact WM |].
    cbn [disjoint_from]. unfold apart, SEG_C_SIZE in *. split; [lia | exact I]. }
  assert (HZ : bytes_at rsegs m' (bv_unsigned a0) (repeat ZERO (Z.to_nat SEG_C_SIZE))) by exact HB.
  split; [exact HZ|].
  exists (repeat ZERO (Z.to_nat SEG_C_SIZE)). split; [exact HZ | exact rconf_enc_zero].
Qed.

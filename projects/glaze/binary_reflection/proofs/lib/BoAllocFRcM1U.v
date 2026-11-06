(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r.BoAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma recycle_lock_4e440 : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 16 = Z_to_bv 64 0x10aec8 -> getr regs 15 = Z_to_bv 64 255 -> getr regs 17 = Z_to_bv 64 1 ->
  rdn BSEGS mem (Z_to_bv 64 0x10aec8) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps BSEGS (mkst regs (0x4e440 : word) mem rom)
    (mkst (regupd (regupd regs 5 (v_lw v)) 6 (Z_to_bv 64 0)) (0x4e45c : word)
          (wbytes mem (Z_to_bv 64 0x10aec8) [Z_to_bv 8 1; b1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H16 H15 H17 Hrd Hv.
  pose proof (xchg_byte_run BSEGS regs (0x4e440 : word) (0x4e444 : word) (0x4e448 : word) (0x4e44c : word)
                (0x4e450 : word) (0x4e454 : word) (0x4e458 : word) (0x4e45c : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 5 16 6 17 15 _ [b0; b1; b2; b3] v 0%nat 1%Z
                F_4e440 eq_refl D_4e440 F_4e444 eq_refl D_4e444 F_4e448 eq_refl D_4e448 F_4e44c eq_refl D_4e44c
                F_4e450 eq_refl D_4e450 F_4e454 eq_refl D_4e454 F_4e458 eq_refl D_4e458) as R.
  rewrite H16, H15, H17 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_lockword | unorm; reflexivity | lia | assumption].
Qed.

(* [comment removed for export] *)
Definition fr_rc0 (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (b1 b2 b3 : byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (LE8 ra0))
    (at_ S (-2224)) (LE8 s0v))
    (at_ S (-2232)) (LE8 s1v))
    (at_ S (-2240)) (LE8 s2v))
    (at_ S (-2248)) (LE8 s3v))
    (at_ S (-2256)) (LE8 s4v))
    (at_ S (-2288)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2280)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2272)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2264)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x10aec8) [Z_to_bv 8 1; b1; b2; b3].
#[local] Hint Unfold fr_rc0 : asfr.

Section RCPRE.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v a2v a3v : word).
  Variables (minsz glen gqb first : Z) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x10ab58 + 728).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 minsz.
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hmin : (0 <= minsz < 2 ^ 64)%Z.
  Hypothesis Hglen : (0 <= glen < 2 ^ 28)%Z.
  Hypothesis Hgqb : (0 <= gqb < 2 ^ 41)%Z.
  Hypothesis Hover : (8192 * glen <= gqb)%Z.                                   (* [comment removed for export] *)
  Hypothesis Hnomerge : (gqb <= 8192 * glen \/ 1638400 * glen <= 100 * gqb)%Z.  (* [comment removed for export] *)
  Hypothesis Hfirst : (0 <= first < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2288)) 80 = true.
  Hypothesis Rlock : rdn BSEGS mem (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis Rglen : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).
  Hypothesis Rgqb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).
  Hypothesis Rfirst : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 896)) 8 = Some (LE8 (Z_to_bv 64 first)).

  #[local] Abbreviation M0 := (fr_rc0 mem S ra0 s0v s1v s2v s3v s4v b1 b2 b3).

  (* [comment removed for export] *)
  Definition rc_base_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2288) /\ getr r 10 = Z_to_bv 64 (0x10ab58 + 728) /\ getr r 11 = Z_to_bv 64 minsz
      /\ getr r 12 = a2v /\ getr r 13 = a3v
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Ltac rc_prefix HV :=
      an F_4e404 D_4e404;                              (* [comment removed for export] *)
      fsd F_4e408 D_4e408 (at_ S (-2216));             (* [comment removed for export] *)
      fsd F_4e40c D_4e40c (at_ S (-2224));             (* [comment removed for export] *)
      fsd F_4e410 D_4e410 (at_ S (-2232));             (* [comment removed for export] *)
      fsd F_4e414 D_4e414 (at_ S (-2240));             (* [comment removed for export] *)
      fsd F_4e418 D_4e418 (at_ S (-2248));             (* [comment removed for export] *)
      fsd F_4e41c D_4e41c (at_ S (-2256));             (* [comment removed for export] *)
      fsd F_4e420 D_4e420 (at_ S (-2288));             (* [comment removed for export] *)
      fsd F_4e424 D_4e424 (at_ S (-2280));             (* [comment removed for export] *)
      fsd F_4e428 D_4e428 (at_ S (-2272));             (* [comment removed for export] *)
      fsd F_4e42c D_4e42c (at_ S (-2264));             (* [comment removed for export] *)
      an F_4e430 D_4e430;                              (* [comment removed for export] *)
      an F_4e434 D_4e434;                              (* [comment removed for export] *)
      an F_4e438 D_4e438;                              (* [comment removed for export] *)
      an F_4e43c D_4e43c;                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (recycle_lock_4e440 _ _ rom _ (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]
      | ];
      av F_4e45c D_4e45c (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity);   (* [comment removed for export] *)
      ab_ft F_4e460 D_4e460 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4e464 D_4e464 (Z_to_bv 64 gqb) Rgqb;      (* [comment removed for export] *)
      cld8 F_4e468 D_4e468 (Z_to_bv 64 glen) Rglen;    (* [comment removed for export] *)
      av F_4e46c D_4e46c (Z_to_bv 64 (8192 * glen)) ltac:(valz);  (* [comment removed for export] *)
      ab_ft F_4e470 D_4e470 ltac:(condz).              (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rc_pre :
    exists r,
      msteps BSEGS (mkst regs (0x4e404 : word) mem rom) (mkst r (0x4e4c0 : word) M0 rom)
      /\ rc_base_regs r /\ getr r 16 = Z_to_bv 64 glen.
  Proof using Rgqb Rglen Rlock Hstk Hnomerge Hover Hgqb Hglen HS H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1 gqb.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_base_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    assert (HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]))).
    { pose proof (lez4_range [Z_to_bv 8 0; b1; b2; b3] eq_refl) as B. rewrite u_Z2bv by lia. reflexivity. }
    destruct (Z_le_gt_dec gqb (8192 * glen)) as [Heq | Hgt].
    - (* [comment removed for export] *)
      wd_eexists. split; [|split].
      + rc_prefix HV.
        ab_tk F_4e474 D_4e474 ltac:(condz).            (* [comment removed for export] *)
        change (wbytes _ _ _) with M0. wd_refl.
      + post.
      + post.
    - (* [comment removed for export] *)
      assert (Hnm : (1638400 * glen <= 100 * gqb)%Z) by (destruct Hnomerge as [X|X]; [lia | exact X]).
      wd_eexists. split; [|split].
      + rc_prefix HV.
        ab_ft F_4e474 D_4e474 ltac:(condz).            (* [comment removed for export] *)
        an F_4e478 D_4e478.                            (* [comment removed for export] *)
        an F_4e47c D_4e47c.                            (* [comment removed for export] *)
        av F_4e480 D_4e480 (Z_to_bv 64 (1638400 * glen)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
        av F_4e484 D_4e484 (Z_to_bv 64 (100 * gqb)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).        (* [comment removed for export] *)
        ab_tk F_4e488 D_4e488 ltac:(condz).            (* [comment removed for export] *)
        change (wbytes _ _ _) with M0. wd_refl.
      + post.
      + post.
  Qed.
End RCPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rc_keep (r r' : bvmap 5 word) : Prop :=
    getr r' 2 = getr r 2 /\ getr r' 10 = getr r 10 /\ getr r' 11 = getr r 11 /\ getr r' 12 = getr r 12 /\ getr r' 13 = getr r 13
    /\ getr r' 8 = getr r 8 /\ getr r' 9 = getr r 9 /\ getr r' 18 = getr r 18 /\ getr r' 19 = getr r 19 /\ getr r' 20 = getr r 20
    /\ getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4
    /\ getr r' 21 = getr r 21 /\ getr r' 22 = getr r 22 /\ getr r' 23 = getr r 23 /\ getr r' 24 = getr r 24
    /\ getr r' 25 = getr r 25 /\ getr r' 26 = getr r 26 /\ getr r' 27 = getr r 27.
(* [comment removed for export] *)
Definition rc_keep1 (r r' : bvmap 5 word) : Prop :=
    getr r' 2 = getr r 2 /\ getr r' 10 = getr r 10 /\ getr r' 12 = getr r 12 /\ getr r' 13 = getr r 13
    /\ getr r' 8 = getr r 8 /\ getr r' 9 = getr r 9 /\ getr r' 18 = getr r 18 /\ getr r' 19 = getr r 19 /\ getr r' 20 = getr r 20
    /\ getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4
    /\ getr r' 21 = getr r 21 /\ getr r' 22 = getr r 22 /\ getr r' 23 = getr r 23 /\ getr r' 24 = getr r 24
    /\ getr r' 25 = getr r 25 /\ getr r' 26 = getr r 26 /\ getr r' 27 = getr r 27.

Lemma rc_keep_trans : forall r1 r2 r3, rc_keep r1 r2 -> rc_keep r2 r3 -> rc_keep r1 r3.
Proof using.
  intros r1 r2 r3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19)
                  (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B19).
  (lazymatch goal with |- ?G => let G' := eval unfold rc_keep in G in change_no_check G' end). repeat split; etransitivity; eassumption.
Qed.

(* [comment removed for export] *)
Ltac fsb F D aa bb :=
  chain_step; [reflexivity
    | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [reflexivity | apply bv_eq; unorm; reflexivity]
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Ltac fldx F D vv :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; try ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; fold_at_vars); autounfold with asfr;
        repeat (wd_rdstep rd8_side)
      | apply bytes_le_to_Z_8 ]
    | step_simpl]; vn.

Section RCHEAD.
  Variables (mem rom : word -> option byte) (S : word) (minsz gqb first : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2288).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x10ab58 + 728).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 minsz.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hmin : (0 <= minsz < 2 ^ 64)%Z.
  Hypothesis Hgqb : (0 <= gqb < 2 ^ 41)%Z.
  Hypothesis Hfirst : (0 <= first < 2 ^ 64)%Z.
  Hypothesis Rt0 : rdn BSEGS mem (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rt16 : rdn BSEGS mem (at_ S (-2272)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rgqb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).
  Hypothesis Rfirst : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 896)) 8 = Some (LE8 (Z_to_bv 64 first)).


  (* [comment removed for export] *)
  Lemma rc_head_loop : (minsz < gqb)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4e4c0 : word) mem rom) (mkst r (0x4e500 : word) mem rom) /\ rc_keep regs r
      /\ getr r 14 = Z_to_bv 64 0 /\ getr r 15 = Z_to_bv 64 0 /\ getr r 5 = Z_to_bv 64 first /\ getr r 16 = getr regs 16.
  Proof using Rfirst Rgqb Rt16 Rt0 Hgqb Hmin H11 H10 H2 S.
    intros Hlt. (lazymatch goal with |- ?G => let G' := eval unfold rc_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4e4c0 D_4e4c0 (Z_to_bv 64 0) Rt0.         (* [comment removed for export] *)
      cld8 F_4e4c4 D_4e4c4 (Z_to_bv 64 0) Rt16.        (* [comment removed for export] *)
      cld8 F_4e4c8 D_4e4c8 (Z_to_bv 64 gqb) Rgqb.      (* [comment removed for export] *)
      ab_ft F_4e4cc D_4e4cc ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e4d0 D_4e4d0 (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      an F_4e4d4 D_4e4d4.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End RCHEAD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_pop1 (mem : word -> option byte) (S : word) (minsz j prev a sz nx glenr B sum : Z) : word -> option byte :=
  let m1 := wbytes mem (Z_to_bv 64 (0x10ab58 + 896)) (LE8 (Z_to_bv 64 nx)) in
  let m2 := if (nx =? 0)%Z then wbytes m1 (Z_to_bv 64 (0x10ab58 + 904)) (LE8 (Z_to_bv 64 0)) else m1 in
  let m3 := wbytes m2 (Z_to_bv 64 (0x10ab58 + 888)) (LE8 (Z_to_bv 64 (glenr - 1))) in
  let m4 := wbytes m3 (Z_to_bv 64 (0x10ab58 + 912)) (LE8 (Z_to_bv 64 (B - sz))) in
  let m5 := wbytes m4 (Z_to_bv 64 a) (LE8 (Z_to_bv 64 0)) in
  let m6 := if (j =? 0)%Z then wbytes m5 (at_ S (-2280)) (LE8 (Z_to_bv 64 a)) else wbytes m5 (Z_to_bv 64 prev) (LE8 (Z_to_bv 64 a)) in
  let m7 := wbytes m6 (at_ S (-2264)) (LE8 (Z_to_bv 64 (sum + sz))) in
  if (minsz <? B - sz)%Z then m7
  else wbytes (wbytes m7 (at_ S (-2288)) (LE8 (Z_to_bv 64 (j + 1)))) (at_ S (-2272)) (LE8 (Z_to_bv 64 a)).

Section RCPOP.
  Variables (mem rom : word -> option byte) (S : word) (minsz j prev a sz nx glenr B sum : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2288).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x10ab58 + 728).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 minsz.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 j.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 prev.
  Hypothesis H16 : getr regs 16 = Z_to_bv 64 glenr.
  Hypothesis H5 : getr regs 5 = Z_to_bv 64 a.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hmin : (0 <= minsz < 2 ^ 64)%Z.
  Hypothesis Hj : (0 <= j < 2 ^ 28)%Z.
  Hypothesis Hglenr : (1 <= glenr < 2 ^ 28)%Z.
  Hypothesis HB : (0 <= sz <= B /\ B < 2 ^ 41)%Z.
  Hypothesis Hsum : (0 <= sum /\ sum + sz < 2 ^ 42)%Z.
  Hypothesis Hnx : (0 <= nx < 2 ^ 64)%Z.
  Hypothesis Ha : (AIMGHI <= a /\ a + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hprev : (j <> 0 -> (AIMGHI <= prev /\ prev + 8192 <= bv_unsigned S - 3584) /\ (prev + 8192 <= a \/ a + 8192 <= prev))%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2288)) 80 = true.
  Hypothesis Hoka : store_ok BSEGS mem (Z_to_bv 64 a) 8 = true.
  Hypothesis Hokp : (j <> 0)%Z -> store_ok BSEGS mem (Z_to_bv 64 prev) 8 = true.
  Hypothesis Rnx : rdn BSEGS mem (Z_to_bv 64 a) 8 = Some (LE8 (Z_to_bv 64 nx)).
  Hypothesis Rsz : rdn BSEGS mem (Z_to_bv 64 (a + 8)) 8 = Some (LE8 (Z_to_bv 64 sz)).
  Hypothesis RB : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 B)).
  Hypothesis Rsum : rdn BSEGS mem (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 sum)).

  Ltac seg1 :=
      ab_ft F_4e500 D_4e500 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4e504 D_4e504 (Z_to_bv 64 nx) Rnx;        (* [comment removed for export] *)
      fsd F_4e508 D_4e508 (Z_to_bv 64 (0x10ab58 + 896)).   (* [comment removed for export] *)
  Ltac seg2 :=
      av F_4e514 D_4e514 (Z_to_bv 64 (glenr - 1)) ltac:(valz);   (* [comment removed for export] *)
      fsd F_4e518 D_4e518 (Z_to_bv 64 (0x10ab58 + 888));   (* [comment removed for export] *)
      cld8 F_4e51c D_4e51c (Z_to_bv 64 sz) Rsz;        (* [comment removed for export] *)
      cld8 F_4e520 D_4e520 (Z_to_bv 64 B) RB;          (* [comment removed for export] *)
      av F_4e524 D_4e524 (Z_to_bv 64 (B - sz)) ltac:(valz);      (* [comment removed for export] *)
      fsd F_4e528 D_4e528 (Z_to_bv 64 (0x10ab58 + 912));   (* [comment removed for export] *)
      an F_4e52c D_4e52c;                              (* [comment removed for export] *)
      fsd F_4e530 D_4e530 (Z_to_bv 64 a).              (* [comment removed for export] *)
  Ltac seg3 :=
      cld8 F_4e4dc D_4e4dc (Z_to_bv 64 sz) Rsz;        (* [comment removed for export] *)
      cld8 F_4e4e0 D_4e4e0 (Z_to_bv 64 sum) Rsum;      (* [comment removed for export] *)
      av F_4e4e4 D_4e4e4 (Z_to_bv 64 (sum + sz)) ltac:(valz);    (* [comment removed for export] *)
      fsd F_4e4e8 D_4e4e8 (at_ S (-2264));             (* [comment removed for export] *)
      fldx F_4e4ec D_4e4ec (Z_to_bv 64 (B - sz));      (* [comment removed for export] *)
      av F_4e4f0 D_4e4f0 (Z_to_bv 64 (j + 1)) ltac:(valz);       (* [comment removed for export] *)
      an F_4e4f4 D_4e4f4;                              (* [comment removed for export] *)
      an F_4e4f8 D_4e4f8.                              (* [comment removed for export] *)

  Definition pop1_regs (r : bvmap 5 word) : Prop :=
      rc_keep regs r /\ getr r 14 = Z_to_bv 64 (j + 1) /\ getr r 15 = Z_to_bv 64 a /\ getr r 16 = Z_to_bv 64 (glenr - 1)
      /\ getr r 5 = Z_to_bv 64 nx /\ getr r 6 = Z_to_bv 64 a.

  Lemma rc_pop1 :
    exists r,
      msteps BSEGS (mkst regs (0x4e500 : word) mem rom)
                   (mkst r (if (minsz <? B - sz)%Z then (0x4e500 : word) else (0x4e55c : word))
                         (fr_pop1 mem S minsz j prev a sz nx glenr B sum) rom)
      /\ pop1_regs r.
  Proof using Rsum RB Rsz Rnx Hokp Hoka Hstk Hprev Ha Hnx Hsum HB Hglenr Hj Hmin HS H5 H16 H15 H14 H11 H10 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold pop1_regs, rc_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr. pose proof (sok_glist mem) as Hokgq.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_pop1 in G in change_no_check G' end).
    destruct (Z.eqb_spec nx 0) as [Enx | Nnx]; destruct (Z.eqb_spec j 0) as [Ej | Nj]; destruct (Z.ltb_spec minsz (B - sz)) as [Hcont | Hexit];
      (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    - (* [comment removed for export] *)
      wd_eexists. split.
      + seg1. ab_ft F_4e50c D_4e50c ltac:(condz). fsd F_4e510 D_4e510 (Z_to_bv 64 (0x10ab58 + 904)).
        seg2. ab_ft F_4e534 D_4e534 ltac:(condz). an F_4e538 D_4e538. fsd F_4e54c D_4e54c (at_ S (-2280)). an F_4e550 D_4e550.
        seg3. ab_ft F_4e4fc D_4e4fc ltac:(condz). wd_refl.
      + post.
    - (* [comment removed for export] *)
      wd_eexists. split.
      + seg1. ab_ft F_4e50c D_4e50c ltac:(condz). fsd F_4e510 D_4e510 (Z_to_bv 64 (0x10ab58 + 904)).
        seg2. ab_ft F_4e534 D_4e534 ltac:(condz). an F_4e538 D_4e538. fsd F_4e54c D_4e54c (at_ S (-2280)). an F_4e550 D_4e550.
        seg3. ab_tk F_4e4fc D_4e4fc ltac:(condz). fsd F_4e554 D_4e554 (at_ S (-2288)). fsd F_4e558 D_4e558 (at_ S (-2272)). wd_refl.
      + post.
    - (* [comment removed for export] *)
      destruct (Hprev Nj) as (Hp1 & Hp2). pose proof (Hokp Nj) as Hokp'.
      wd_eexists. split.
      + seg1. ab_ft F_4e50c D_4e50c ltac:(condz). fsd F_4e510 D_4e510 (Z_to_bv 64 (0x10ab58 + 904)).
        seg2. ab_tk F_4e534 D_4e534 ltac:(condz). fsd F_4e4d8 D_4e4d8 (Z_to_bv 64 prev).
        seg3. ab_ft F_4e4fc D_4e4fc ltac:(condz). wd_refl.
      + post.
    - (* [comment removed for export] *)
      destruct (Hprev Nj) as (Hp1 & Hp2). pose proof (Hokp Nj) as Hokp'.
      wd_eexists. split.
      + seg1. ab_ft F_4e50c D_4e50c ltac:(condz). fsd F_4e510 D_4e510 (Z_to_bv 64 (0x10ab58 + 904)).
        seg2. ab_tk F_4e534 D_4e534 ltac:(condz). fsd F_4e4d8 D_4e4d8 (Z_to_bv 64 prev).
        seg3. ab_tk F_4e4fc D_4e4fc ltac:(condz). fsd F_4e554 D_4e554 (at_ S (-2288)). fsd F_4e558 D_4e558 (at_ S (-2272)). wd_refl.
      + post.
    - (* [comment removed for export] *)
      wd_eexists. split.
      + seg1. ab_tk F_4e50c D_4e50c ltac:(condz).
        seg2. ab_ft F_4e534 D_4e534 ltac:(condz). an F_4e538 D_4e538. fsd F_4e54c D_4e54c (at_ S (-2280)). an F_4e550 D_4e550.
        seg3. ab_ft F_4e4fc D_4e4fc ltac:(condz). wd_refl.
      + post.
    - (* [comment removed for export] *)
      wd_eexists. split.
      + seg1. ab_tk F_4e50c D_4e50c ltac:(condz).
        seg2. ab_ft F_4e534 D_4e534 ltac:(condz). an F_4e538 D_4e538. fsd F_4e54c D_4e54c (at_ S (-2280)). an F_4e550 D_4e550.
        seg3. ab_tk F_4e4fc D_4e4fc ltac:(condz). fsd F_4e554 D_4e554 (at_ S (-2288)). fsd F_4e558 D_4e558 (at_ S (-2272)). wd_refl.
      + post.
    - (* [comment removed for export] *)
      destruct (Hprev Nj) as (Hp1 & Hp2). pose proof (Hokp Nj) as Hokp'.
      wd_eexists. split.
      + seg1. ab_tk F_4e50c D_4e50c ltac:(condz).
        seg2. ab_tk F_4e534 D_4e534 ltac:(condz). fsd F_4e4d8 D_4e4d8 (Z_to_bv 64 prev).
        seg3. ab_ft F_4e4fc D_4e4fc ltac:(condz). wd_refl.
      + post.
    - (* [comment removed for export] *)
      destruct (Hprev Nj) as (Hp1 & Hp2). pose proof (Hokp Nj) as Hokp'.
      wd_eexists. split.
      + seg1. ab_tk F_4e50c D_4e50c ltac:(condz).
        seg2. ab_tk F_4e534 D_4e534 ltac:(condz). fsd F_4e4d8 D_4e4d8 (Z_to_bv 64 prev).
        seg3. ab_tk F_4e4fc D_4e4fc ltac:(condz). fsd F_4e554 D_4e554 (at_ S (-2288)). fsd F_4e558 D_4e558 (at_ S (-2272)). wd_refl.
      + post.
  Qed.
End RCPOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_rcu (mem : word -> option byte) : word -> option byte :=
  wbytes (wbytes mem (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0]) (Z_to_bv 64 0x10aec9) [Z_to_bv 8 0].

Section RCTAIL.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2288).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x10ab58 + 728).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.

  (* [comment removed for export] *)
  Lemma rc_unlock_call :
    exists r, msteps BSEGS (mkst regs (0x4e55c : word) mem rom) (mkst r (0x4e76c : word) (fr_rcu mem) rom)
      /\ rc_keep1 regs r /\ getr r 1 = Z_to_bv 64 0x4e574 /\ getr r 11 = at_ S (-2288).
  Proof using H10 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_keep1 in G in change_no_check G' end). pose proof (u64_range S) as HSr. pose proof (sok_lockword mem) as Hoklk.
    wd_eexists. split.
    - afence F_4e55c D_4e55c.                          (* [comment removed for export] *)
      fsb F_4e560 D_4e560 (Z_to_bv 64 0x10aec8) (Z_to_bv 8 0).   (* [comment removed for export] *)
      afence F_4e564 D_4e564.
      fsb F_4e568 D_4e568 (Z_to_bv 64 0x10aec9) (Z_to_bv 8 0).   (* [comment removed for export] *)
      an F_4e56c D_4e56c.                              (* [comment removed for export] *)
      an F_4e570 D_4e570.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_rcu mem). wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2216)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2224)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2232)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2240)) 8 = Some (LE8 s2v).
  Hypothesis Cs3 : rdn BSEGS mem (at_ S (-2248)) 8 = Some (LE8 s3v).
  Hypothesis Cs4 : rdn BSEGS mem (at_ S (-2256)) 8 = Some (LE8 s4v).
  Lemma rc_epilogue :
    exists r, msteps BSEGS (mkst regs (0x4e574 : word) mem rom) (mkst r ra0 mem rom)
      /\ getr r 2 = at_ S (-2208) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Cs4 Cs3 Cs2 Cs1 Cs0 Cra Hret H2.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4e574 D_4e574 ra0 Cra.                    (* [comment removed for export] *)
      cld8 F_4e578 D_4e578 s0v Cs0.
      cld8 F_4e57c D_4e57c s1v Cs1.
      cld8 F_4e580 D_4e580 s2v Cs2.
      cld8 F_4e584 D_4e584 s3v Cs3.
      cld8 F_4e588 D_4e588 s4v Cs4.
      an F_4e58c D_4e58c.                              (* [comment removed for export] *)
      aret F_4e590 D_4e590 ra0.                        (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End RCTAIL.
End FPGen.
End BoAllocFRc1.
Module BoAllocFRcM1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r.BoAllocF7 BoAllocFRc1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation IBq := 0x10ab58%Z (only parsing).
#[local] Abbreviation M8K := 18446744073709543424%Z (only parsing).      (* [comment removed for export] *)

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition mg_keep (S : word) (r0 r : bvmap 5 word) : Prop :=
    getr r 2 = at_ S (-2304) /\ getr r 10 = Z_to_bv 64 (IBq + 888) /\ getr r 11 = at_ S (-2288)
    /\ getr r 8 = getr r0 8 /\ getr r 9 = getr r0 9 /\ getr r 18 = getr r0 18 /\ getr r 19 = getr r0 19 /\ getr r 20 = getr r0 20
    /\ getr r 3 = getr r0 3 /\ getr r 4 = getr r0 4
    /\ getr r 21 = getr r0 21 /\ getr r 22 = getr r0 22 /\ getr r 23 = getr r0 23 /\ getr r 24 = getr r0 24
    /\ getr r 25 = getr r0 25 /\ getr r 26 = getr r0 26 /\ getr r 27 = getr r0 27.
(* [comment removed for export] *)
Definition mg_head (r : bvmap 5 word) (cur nxt ext : Z) : Prop :=
    getr r 14 = Z_to_bv 64 cur /\ getr r 5 = Z_to_bv 64 nxt /\ getr r 12 = Z_to_bv 64 ext
    /\ getr r 15 = Z_to_bv 64 1021 /\ getr r 16 = Z_to_bv 64 M8K /\ getr r 17 = Z_to_bv 64 8192.

Lemma mg_keep_trans : forall S r0 r1 r2, mg_keep S r0 r1 -> mg_keep S r1 r2 -> mg_keep S r0 r2.
Proof using.
  intros S r0 r1 r2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
                    (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17).
  (lazymatch goal with |- ?G => let G' := eval unfold mg_keep in G in change_no_check G' end). repeat split; try assumption; etransitivity; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MGENTRY.
  Variables (mem rom : word -> option byte) (S ra0 : word) (cur nxt : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2288).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (IBq + 888).
  Hypothesis H11 : getr regs 11 = at_ S (-2288).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hcur : (AIMGHI <= cur /\ cur + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hnxt : (0 < nxt < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 16 = true.
  Hypothesis Rfirst : rdn BSEGS mem (Z_to_bv 64 (IBq + 896)) 8 = Some (LE8 (Z_to_bv 64 cur)).
  Hypothesis Rnext : rdn BSEGS mem (Z_to_bv 64 cur) 8 = Some (LE8 (Z_to_bv 64 nxt)).

  Lemma mg_entry :
    exists r, msteps BSEGS (mkst regs (0x4e5e8 : word) mem rom) (mkst r (0x4e620 : word) (wbytes mem (at_ S (-2296)) (LE8 ra0)) rom)
      /\ mg_keep S regs r /\ mg_head r cur nxt 0.
  Proof using Rnext Rfirst Hstk Hnxt Hcur HS H11 H10 H2 H1.
    (lazymatch goal with |- ?G => let G' := eval unfold mg_keep, mg_head in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4e5e8 D_4e5e8.                              (* [comment removed for export] *)
      fsd F_4e5ec D_4e5ec (at_ S (-2296)).             (* [comment removed for export] *)
      cld8 F_4e5f0 D_4e5f0 (Z_to_bv 64 cur) Rfirst.    (* [comment removed for export] *)
      ab_ft F_4e5f4 D_4e5f4 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e5f8 D_4e5f8 (Z_to_bv 64 nxt) Rnext.     (* [comment removed for export] *)
      ab_ft F_4e5fc D_4e5fc ltac:(condz).              (* [comment removed for export] *)
      an F_4e600 D_4e600.                              (* [comment removed for export] *)
      an F_4e604 D_4e604.                              (* [comment removed for export] *)
      av F_4e608 D_4e608 (Z_to_bv 64 M8K) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av F_4e60c D_4e60c (Z_to_bv 64 8192) ltac:(apply bv_eq; reflexivity).  (* [comment removed for export] *)
      an F_4e610 D_4e610.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End MGENTRY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MGADV.
  Variables (mem rom : word -> option byte) (S : word) (cur nxt ext c1 c2 nn : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HK : mg_keep S regs regs.
  Hypothesis HH : mg_head regs cur nxt ext.
  Hypothesis Hc1 : (0 <= c1 <= 1021)%Z.
  Hypothesis Hc2 : (0 <= c2 <= 1021)%Z.
  Hypothesis Hbig : (1021 < c1 + c2)%Z.
  Hypothesis Hcur : (0 <= cur /\ cur + 8192 <= 2 ^ 63)%Z.
  Hypothesis Hnxt : (0 <= nxt /\ nxt + 8192 <= 2 ^ 63)%Z.
  Hypothesis Hnn : (0 <= nn < 2 ^ 64)%Z.
  Hypothesis Rc1 : rdn BSEGS mem (Z_to_bv 64 (cur + 16)) 8 = Some (LE8 (Z_to_bv 64 c1)).
  Hypothesis Rc2 : rdn BSEGS mem (Z_to_bv 64 (nxt + 16)) 8 = Some (LE8 (Z_to_bv 64 c2)).
  Hypothesis Rnn : rdn BSEGS mem (Z_to_bv 64 nxt) 8 = Some (LE8 (Z_to_bv 64 nn)).

  Lemma mg_adv :
    exists r, msteps BSEGS (mkst regs (0x4e620 : word) mem rom)
                (mkst r (if (nn =? 0)%Z then (0x4e704 : word) else (0x4e620 : word)) mem rom)
      /\ mg_keep S regs r /\ mg_head r nxt nn ext.
  Proof using Rnn Rc2 Rc1 Hnn Hnxt Hcur Hbig Hc2 Hc1 HH HK c2 c1 cur.
    destruct HK as (K2 & K10 & K11 & _). destruct HH as (A14 & A5 & A12 & A15 & A16 & A17).
    (lazymatch goal with |- ?G => let G' := eval unfold mg_keep, mg_head in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    destruct (Z.eqb_spec nn 0) as [E0 | N0].
    - wd_eexists. split.
      + cld8 F_4e620 D_4e620 (Z_to_bv 64 c1) Rc1.        (* [comment removed for export] *)
        cld8 F_4e624 D_4e624 (Z_to_bv 64 c2) Rc2.        (* [comment removed for export] *)
        av F_4e628 D_4e628 (Z_to_bv 64 (c1 + c2)) ltac:(valz).   (* [comment removed for export] *)
        ab_tk F_4e62c D_4e62c ltac:(condz).              (* [comment removed for export] *)
        an F_4e614 D_4e614.                              (* [comment removed for export] *)
        cld8 F_4e618 D_4e618 (Z_to_bv 64 nn) Rnn.        (* [comment removed for export] *)
        ab_tk F_4e61c D_4e61c ltac:(condz).              (* [comment removed for export] *)
        wd_refl.
      + post.
    - wd_eexists. split.
      + cld8 F_4e620 D_4e620 (Z_to_bv 64 c1) Rc1.
        cld8 F_4e624 D_4e624 (Z_to_bv 64 c2) Rc2.
        av F_4e628 D_4e628 (Z_to_bv 64 (c1 + c2)) ltac:(valz).
        ab_tk F_4e62c D_4e62c ltac:(condz).
        an F_4e614 D_4e614.
        cld8 F_4e618 D_4e618 (Z_to_bv 64 nn) Rnn.
        ab_ft F_4e61c D_4e61c ltac:(condz).              (* [comment removed for export] *)
        wd_refl.
      + post.
  Qed.
End MGADV.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MGEXIT.
  Variables (mem rom : word -> option byte) (S ra0 : word) (ext B : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HK : mg_keep S regs regs.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 ext.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HB : (0 <= ext <= B /\ B < 2 ^ 41)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis RB : rdn BSEGS mem (Z_to_bv 64 (IBq + 912)) 8 = Some (LE8 (Z_to_bv 64 B)).
  Hypothesis Rra : rdn BSEGS mem (at_ S (-2296)) 8 = Some (LE8 ra0).

  Lemma mg_exit :
    exists r, msteps BSEGS (mkst regs (0x4e704 : word) mem rom)
                (mkst r ra0 (wbytes mem (Z_to_bv 64 (IBq + 912)) (LE8 (Z_to_bv 64 (B - ext)))) rom)
      /\ getr r 2 = at_ S (-2288)
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rra RB Hret HB HS H12 HK.
    destruct HK as (K2 & K10 & K11 & _). pose proof (u64_range S) as HSr. pose proof (sok_glist mem) as Hokgq.
    wd_eexists. split.
    - cld8 F_4e704 D_4e704 (Z_to_bv 64 B) RB.            (* [comment removed for export] *)
      av F_4e708 D_4e708 (Z_to_bv 64 (B - ext)) ltac:(valz).     (* [comment removed for export] *)
      fsd F_4e70c D_4e70c (Z_to_bv 64 (IBq + 912)).      (* [comment removed for export] *)
      cld8 F_4e710 D_4e710 ra0 Rra.                      (* [comment removed for export] *)
      an F_4e714 D_4e714.                                (* [comment removed for export] *)
      aret F_4e718 D_4e718 ra0.                          (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End MGEXIT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wwb (ws : list word) : list byte := concat (map (fun w : word => LE8 w) ws).
Lemma length_wwb : forall ws, length (wwb ws) = (8 * length ws)%nat.
Proof using. induction ws as [|w r IH]; [reflexivity|]. unfold wwb in *. (lazymatch goal with |- ?G => let G' := eval cbn [map concat] in G in change_no_check G' end). rewrite length_app, IH, length_N_to_le_bytes. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia. Qed.
Definition wws (mem : word -> option byte) (a : Z) (ws : list word) : word -> option byte := wbytes mem (Z_to_bv 64 a) (wwb ws).

(* [comment removed for export] *)
Definition cp_keep (r0 r : bvmap 5 word) : Prop :=
    getr r 2 = getr r0 2 /\ getr r 10 = getr r0 10 /\ getr r 11 = getr r0 11
    /\ getr r 8 = getr r0 8 /\ getr r 9 = getr r0 9 /\ getr r 18 = getr r0 18 /\ getr r 19 = getr r0 19 /\ getr r 20 = getr r0 20
    /\ getr r 3 = getr r0 3 /\ getr r 4 = getr r0 4
    /\ getr r 21 = getr r0 21 /\ getr r 22 = getr r0 22 /\ getr r 23 = getr r0 23 /\ getr r 24 = getr r0 24
    /\ getr r 25 = getr r0 25 /\ getr r 26 = getr r0 26 /\ getr r 27 = getr r0 27
    /\ getr r 14 = getr r0 14 /\ getr r 5 = getr r0 5 /\ getr r 12 = getr r0 12 /\ getr r 15 = getr r0 15 /\ getr r 16 = getr r0 16
    /\ getr r 17 = getr r0 17 /\ getr r 13 = getr r0 13 /\ getr r 6 = getr r0 6.

Lemma mg_copy : forall (rom : word -> option byte) (ws : list word) (regs : bvmap 5 word) (mem : word -> option byte) (src dst : Z),
  ws <> [] ->
  getr regs 7 = Z_to_bv 64 src -> getr regs 28 = Z_to_bv 64 dst -> getr regs 29 = Z_to_bv 64 (src + 8 * Z.of_nat (length ws)) ->
  (0 <= src /\ src + 8 * Z.of_nat (length ws) <= 2 ^ 63)%Z -> (0 <= dst /\ dst + 8 * Z.of_nat (length ws) <= 2 ^ 63)%Z ->
  (src + 8 * Z.of_nat (length ws) <= dst \/ dst + 8 * Z.of_nat (length ws) <= src)%Z ->
  store_ok BSEGS mem (Z_to_bv 64 dst) (8 * length ws) = true ->
  (forall i w, nth_error ws i = Some w -> rdn BSEGS mem (Z_to_bv 64 (src + 8 * Z.of_nat i)) 8 = Some (LE8 w)) ->
  exists r, msteps BSEGS (mkst regs (0x4e658 : word) mem rom) (mkst r (0x4e66c : word) (wws mem dst ws) rom) /\ cp_keep regs r.
Proof using.
  intros rom ws. induction ws as [|w ws' IH]; intros regs mem src dst NE H7 H28 H29 Gs Gd DIS SOK CELLS; [exfalso; exact (NE eq_refl)|].
  cbn [length] in *. rewrite Nat2Z.inj_succ in *.
  assert (R0 : rdn BSEGS mem (Z_to_bv 64 src) 8 = Some (LE8 w)).
  { pose proof (CELLS 0%nat w eq_refl) as C. change (Z.of_nat 0) with 0%Z in C. replace (src + 8 * 0)%Z with src in C by lia. exact C. }
  assert (SOK0 : store_ok BSEGS mem (Z_to_bv 64 dst) 8 = true).
  { eapply (store_ok_sub BSEGS mem (Z_to_bv 64 dst) _ (8 * S (length ws'))); [wd_ulia | exact SOK | wd_ulia | wd_ulia]. }
  assert (EM : wws mem dst (w :: ws') = wws (wbytes mem (Z_to_bv 64 dst) (LE8 w)) (dst + 8) ws').
  { (lazymatch goal with |- ?G => let G' := eval unfold wws, wwb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [map concat] in G in change_no_check G' end). rewrite wbytes_app, length_N_to_le_bytes. f_equal. apply bv_eq. rewrite at_u by (wd_ulia_c). unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
  destruct ws' as [|w2 ws''].
  - (* [comment removed for export] *)
    cbn [length Z.of_nat] in *.
    wd_eexists. split.
    + cld8 F_4e658 D_4e658 w R0.                         (* [comment removed for export] *)
      av F_4e65c D_4e65c (Z_to_bv 64 (src + 8)) ltac:(valz).     (* [comment removed for export] *)
      fsd F_4e660 D_4e660 (Z_to_bv 64 dst).              (* [comment removed for export] *)
      av F_4e664 D_4e664 (Z_to_bv 64 (dst + 8)) ltac:(valz).     (* [comment removed for export] *)
      ab_ft F_4e668 D_4e668 ltac:(condz).                (* [comment removed for export] *)
      rewrite EM. (lazymatch goal with |- ?G => let G' := eval unfold wws, wwb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [map concat wbytes] in G in change_no_check G' end). wd_refl.
    + (lazymatch goal with |- ?G => let G' := eval unfold cp_keep in G in change_no_check G' end). post.
  - (* [comment removed for export] *)
    set (regs1 := regupd (regupd (regupd regs 30 w) 7 (Z_to_bv 64 (src + 8))) 28 (Z_to_bv 64 (dst + 8))).
    assert (SOK1 : store_ok BSEGS (wbytes mem (Z_to_bv 64 dst) (LE8 w)) (Z_to_bv 64 (dst + 8)) (8 * length (w2 :: ws'')) = true).
    { eapply store_ok_mono; [apply wbytes_grows|]. cbn [length] in *. rewrite ?Nat2Z.inj_succ in *.
      eapply (store_ok_sub BSEGS mem (Z_to_bv 64 dst) _ (8 * S (S (length ws'')))); [wd_ulia | exact SOK | wd_ulia | wd_ulia]. }
    assert (CELLS1 : forall i w', nth_error (w2 :: ws'') i = Some w' -> rdn BSEGS (wbytes mem (Z_to_bv 64 dst) (LE8 w)) (Z_to_bv 64 (src + 8 + 8 * Z.of_nat i)) 8 = Some (LE8 w')).
    { intros i w' Hi. assert (Hil : (i < length (w2 :: ws''))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      cbn [length] in *. rewrite ?Nat2Z.inj_succ in *.
      rewrite rdn_wbytes_out; [| rewrite length_N_to_le_bytes; wd_ulia | wd_ulia | rewrite length_N_to_le_bytes; wd_ulia].
      replace (src + 8 + 8 * Z.of_nat i)%Z with (src + 8 * Z.of_nat (S i))%Z by lia. apply CELLS. exact Hi. }
    destruct (IH regs1 (wbytes mem (Z_to_bv 64 dst) (LE8 w)) (src + 8)%Z (dst + 8)%Z ltac:(discriminate)) as (r & RUN & KEEP);
      [(lazymatch goal with |- ?G => let G' := eval unfold regs1 in G in change_no_check G' end); gres; reflexivity | (lazymatch goal with |- ?G => let G' := eval unfold regs1 in G in change_no_check G' end); gres; reflexivity
      | (lazymatch goal with |- ?G => let G' := eval unfold regs1 in G in change_no_check G' end); gres; rewrite H29; f_equal; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite ?Nat2Z.inj_succ; lia
      | cbn [length] in *; rewrite ?Nat2Z.inj_succ in *; lia | cbn [length] in *; rewrite ?Nat2Z.inj_succ in *; lia
      | cbn [length] in *; rewrite ?Nat2Z.inj_succ in *; lia | exact SOK1 | exact CELLS1 |].
    + exists r. split.
      * cld8 F_4e658 D_4e658 w R0.
        av F_4e65c D_4e65c (Z_to_bv 64 (src + 8)) ltac:(valz).
        fsd F_4e660 D_4e660 (Z_to_bv 64 dst).
        av F_4e664 D_4e664 (Z_to_bv 64 (dst + 8)) ltac:(valz).
        ab_tk F_4e668 D_4e668 ltac:(cbn [length] in *; rewrite ?Nat2Z.inj_succ in *; condz).   (* [comment removed for export] *)
        rewrite EM. exact RUN.
      * unfold cp_keep in *. unfold regs1 in KEEP. revert KEEP. gres. intros KEEP. exact KEEP.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MGMHEAD.
  Variables (mem rom : word -> option byte) (S : word) (cur nxt ext c1 s1 : Z) (ws : list word).
  Variable regs : bvmap 5 word.
  Hypothesis HK : mg_keep S regs regs.
  Hypothesis HH : mg_head regs cur nxt ext.
  #[local] Abbreviation c2 := (Z.of_nat (length ws)).
  Hypothesis Hc1 : (0 <= c1)%Z.
  Hypothesis Hfit : (c1 + c2 <= 1021)%Z.
  Hypothesis Hs1 : (8192 <= s1 < 2 ^ 41)%Z.
  Hypothesis Hcur : (0 <= cur /\ cur + 8192 <= 2 ^ 63)%Z.
  Hypothesis Hnxt : (0 <= nxt /\ nxt + 8192 <= 2 ^ 63)%Z.
  Hypothesis Hsep : (cur + 8192 <= nxt \/ nxt + 8192 <= cur)%Z.
  Hypothesis Hokcur : forall k n, (0 <= k)%Z -> (k + Z.of_nat n <= 8192)%Z -> store_ok BSEGS mem (Z_to_bv 64 (cur + k)) n = true.
  Hypothesis Rc1 : rdn BSEGS mem (Z_to_bv 64 (cur + 16)) 8 = Some (LE8 (Z_to_bv 64 c1)).
  Hypothesis Rc2 : rdn BSEGS mem (Z_to_bv 64 (nxt + 16)) 8 = Some (LE8 (Z_to_bv 64 c2)).
  Hypothesis Rs1 : rdn BSEGS mem (Z_to_bv 64 (cur + 8)) 8 = Some (LE8 (Z_to_bv 64 s1)).
  Hypothesis Rws : forall i w, nth_error ws i = Some w -> rdn BSEGS mem (Z_to_bv 64 (nxt + 24 + 8 * Z.of_nat i)) 8 = Some (LE8 w).

  Definition mhead_regs (r : bvmap 5 word) : Prop :=
    mg_keep S regs r /\ mg_head r cur nxt ext /\ getr r 13 = Z_to_bv 64 s1 /\ getr r 6 = Z_to_bv 64 (c1 + c2).

  Lemma mg_mhead :
    exists r, msteps BSEGS (mkst regs (0x4e620 : word) mem rom) (mkst r (0x4e66c : word) (wws mem (cur + 24 + 8 * c1) ws) rom)
      /\ mhead_regs r.
  Proof using Rws Rs1 Rc2 Rc1 Hokcur Hsep Hnxt Hcur Hs1 Hfit Hc1 HH HK.
    destruct HK as (K2 & K10 & K11 & _). destruct HH as (A14 & A5 & A12 & A15 & A16 & A17).
    (lazymatch goal with |- ?G => let G' := eval unfold mhead_regs, mg_keep, mg_head in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    assert (Hq : (1 <= s1 / 2 ^ 13 < 2 ^ 28)%Z) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
    Ltac mh_pre c1 cc s1 Rc1 Rc2 Rs1 :=
      cld8 F_4e620 D_4e620 (Z_to_bv 64 c1) Rc1;          (* [comment removed for export] *)
      cld8 F_4e624 D_4e624 (Z_to_bv 64 cc) Rc2;          (* [comment removed for export] *)
      av F_4e628 D_4e628 (Z_to_bv 64 (c1 + cc)) ltac:(valz);     (* [comment removed for export] *)
      ab_ft F_4e62c D_4e62c ltac:(condz);                (* [comment removed for export] *)
      cld8 F_4e630 D_4e630 (Z_to_bv 64 s1) Rs1;          (* [comment removed for export] *)
      av F_4e634 D_4e634 (Z_to_bv 64 (s1 / 2 ^ 13)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity);   (* [comment removed for export] *)
      ab_ft F_4e638 D_4e638 ltac:(condz).                (* [comment removed for export] *)
    destruct ws as [|w0 ws0] eqn:EW.
    - (* [comment removed for export] *)
      change (Z.of_nat (@length word [])) with 0%Z in *.
      wd_eexists. split.
      + mh_pre c1 0%Z s1 Rc1 Rc2 Rs1.
        ab_tk F_4e63c D_4e63c ltac:(condz).              (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold wws, wwb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [map concat wbytes] in G in change_no_check G' end). wd_refl.
      + post.
    - rewrite <- EW in *. assert (NEw : ws <> []) by (rewrite EW; discriminate).
      assert (Hc2 : (1 <= c2)%Z) by (rewrite EW; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia).
      set (regs1 := regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
                      29 (Z_to_bv 64 c1)) 28 (Z_to_bv 64 c2)) 6 (Z_to_bv 64 (c1 + c2))) 13 (Z_to_bv 64 s1)) 7 (Z_to_bv 64 (s1 / 2 ^ 13))) 7 (Z_to_bv 64 (nxt + 24)))
                      29 (Z_to_bv 64 (8 * c1))) 30 (Z_to_bv 64 (8 * c2))) 28 (Z_to_bv 64 (cur + 8 * c1))) 28 (Z_to_bv 64 (cur + 24 + 8 * c1))) 29 (Z_to_bv 64 (nxt + 24 + 8 * c2))).
      destruct (mg_copy rom ws regs1 mem (nxt + 24)%Z (cur + 24 + 8 * c1)%Z NEw) as (r & RUN & KEEP);
        [(lazymatch goal with |- ?G => let G' := eval unfold regs1 in G in change_no_check G' end); gres; reflexivity | (lazymatch goal with |- ?G => let G' := eval unfold regs1 in G in change_no_check G' end); gres; reflexivity | (lazymatch goal with |- ?G => let G' := eval unfold regs1 in G in change_no_check G' end); gres; f_equal; lia
        | lia | lia | lia
        | replace (cur + 24 + 8 * c1)%Z with (cur + (24 + 8 * c1))%Z by lia; apply Hokcur; lia
        | exact Rws |].
      exists r. split.
      + mh_pre c1 (Z.of_nat (length ws)) s1 Rc1 Rc2 Rs1.
        ab_ft F_4e63c D_4e63c ltac:(condz).              (* [comment removed for export] *)
        av F_4e640 D_4e640 (Z_to_bv 64 (nxt + 24)) ltac:(valz).          (* [comment removed for export] *)
        av F_4e644 D_4e644 (Z_to_bv 64 (8 * c1)) ltac:(valz).            (* [comment removed for export] *)
        av F_4e648 D_4e648 (Z_to_bv 64 (8 * c2)) ltac:(valz).            (* [comment removed for export] *)
        av F_4e64c D_4e64c (Z_to_bv 64 (cur + 8 * c1)) ltac:(valz).      (* [comment removed for export] *)
        av F_4e650 D_4e650 (Z_to_bv 64 (cur + 24 + 8 * c1)) ltac:(valz). (* [comment removed for export] *)
        av F_4e654 D_4e654 (Z_to_bv 64 (nxt + 24 + 8 * c2)) ltac:(valz). (* [comment removed for export] *)
        exact RUN.
      + unfold cp_keep, regs1 in KEEP. revert KEEP. gres. intros KEEP.
        destruct KEEP as (P2 & P10 & P11 & P8 & P9 & P18 & P19 & P20 & P3 & P4 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P14 & P5 & P12 & P15 & P16 & P17 & P13 & P6).
        rewrite P2, P10, P11, P8, P9, P18, P19, P20, P3, P4, P21, P22, P23, P24, P25, P26, P27, P14, P5, P12, P15, P16, P17, P13, P6.
        repeat split; assumption.
  Qed.
End MGMHEAD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma v_add_m8k : forall x, (8192 <= x < 2 ^ 62)%Z -> v_add (Z_to_bv 64 x) (Z_to_bv 64 M8K) = Z_to_bv 64 (x - 8192).
Proof using.
  intros x Hx. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). unorm.
  rewrite Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_modulus in G in change_no_check G' end). replace (x + 18446744073709543424)%Z with ((x - 8192) + 1 * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Definition fr_mga (mem : word -> option byte) (cur nxt s1 s2 cnt nn : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (cur + 8)) (LE8 (Z_to_bv 64 (s1 + s2 - 8192))))
    (Z_to_bv 64 (cur + 16)) (LE8 (Z_to_bv 64 cnt)))
    (Z_to_bv 64 (nxt + 8)) (LE8 (Z_to_bv 64 8192)))
    (Z_to_bv 64 (nxt + 16)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 cur) (LE8 (Z_to_bv 64 nn)).
Definition fr_mgb (m5 : word -> option byte) (S : word) (cur nxt glen lastv tsz tlast : Z) : word -> option byte :=
  let m6 := if (lastv =? nxt)%Z then wbytes m5 (Z_to_bv 64 (IBq + 904)) (LE8 (Z_to_bv 64 cur)) else m5 in
  let m7 := wbytes m6 (Z_to_bv 64 (IBq + 888)) (LE8 (Z_to_bv 64 (glen - 1))) in
  let m8 := wbytes m7 (Z_to_bv 64 nxt) (LE8 (Z_to_bv 64 0)) in
  if (tsz =? 0)%Z then wbytes m8 (at_ S (-2280)) (LE8 (Z_to_bv 64 nxt)) else wbytes m8 (Z_to_bv 64 tlast) (LE8 (Z_to_bv 64 nxt)).
Definition fr_mgc (m9 : word -> option byte) (S : word) (nxt tsz tbytes : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m9
    (at_ S (-2288)) (LE8 (Z_to_bv 64 (tsz + 1))))
    (at_ S (-2272)) (LE8 (Z_to_bv 64 nxt)))
    (at_ S (-2264)) (LE8 (Z_to_bv 64 (tbytes + 8192))).
Definition fr_mg (mem : word -> option byte) (S : word) (cur nxt s1 s2 cnt nn glen lastv tsz tlast tbytes : Z) : word -> option byte :=
  fr_mgc (fr_mgb (fr_mga mem cur nxt s1 s2 cnt nn) S cur nxt glen lastv tsz tlast) S nxt tsz tbytes.

(* [comment removed for export] *)
Section MGA.
  Variables (mem rom : word -> option byte) (S : word) (cur nxt ext s1 s2 cnt nn glen lastv : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HK : mg_keep S regs regs.
  Hypothesis HH : mg_head regs cur nxt ext.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 s1.
  Hypothesis H6 : getr regs 6 = Z_to_bv 64 cnt.
  Hypothesis Hs1 : (8192 <= s1 < 2 ^ 41)%Z.
  Hypothesis Hs2 : (8192 <= s2 < 2 ^ 41)%Z.
  Hypothesis Hglen : (1 <= glen < 2 ^ 28)%Z.
  Hypothesis Hcur : (AIMGHI <= cur /\ cur + 8192 <= 2 ^ 47)%Z.
  Hypothesis Hnxt : (AIMGHI <= nxt /\ nxt + 8192 <= 2 ^ 47)%Z.
  Hypothesis Hsep : (cur + 8192 <= nxt \/ nxt + 8192 <= cur)%Z.
  Hypothesis Hokcur : store_ok BSEGS mem (Z_to_bv 64 cur) 24 = true.
  Hypothesis Hoknxt : store_ok BSEGS mem (Z_to_bv 64 nxt) 24 = true.
  Hypothesis Rs2 : rdn BSEGS mem (Z_to_bv 64 (nxt + 8)) 8 = Some (LE8 (Z_to_bv 64 s2)).
  Hypothesis Rglen : rdn BSEGS mem (Z_to_bv 64 (IBq + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).
  Hypothesis Rnn : rdn BSEGS mem (Z_to_bv 64 nxt) 8 = Some (LE8 (Z_to_bv 64 nn)).
  Hypothesis Rlast : rdn BSEGS mem (Z_to_bv 64 (IBq + 904)) 8 = Some (LE8 (Z_to_bv 64 lastv)).

  Lemma mg_mtail_a :
    exists r, msteps BSEGS (mkst regs (0x4e66c : word) mem rom) (mkst r (0x4e69c : word) (fr_mga mem cur nxt s1 s2 cnt nn) rom)
      /\ mg_keep S regs r /\ mg_head r cur nxt ext /\ getr r 13 = Z_to_bv 64 glen /\ getr r 6 = Z_to_bv 64 nn /\ getr r 7 = Z_to_bv 64 lastv.
  Proof using Rlast Rnn Rglen Rs2 Hoknxt Hokcur Hsep Hnxt Hcur Hglen Hs2 Hs1 H6 H13 HH HK.
    destruct HK as (K2 & K10 & K11 & _). destruct HH as (A14 & A5 & A12 & A15 & A16 & A17).
    (lazymatch goal with |- ?G => let G' := eval unfold mg_keep, mg_head, fr_mga in G in change_no_check G' end).
    wd_eexists. split.
    - cld8 F_4e66c D_4e66c (Z_to_bv 64 s2) Rs2.          (* [comment removed for export] *)
      av F_4e670 D_4e670 (Z_to_bv 64 (s1 + s2)) ltac:(valz).     (* [comment removed for export] *)
      cld8 F_4e674 D_4e674 (Z_to_bv 64 glen) Rglen.      (* [comment removed for export] *)
      av F_4e678 D_4e678 (Z_to_bv 64 (s1 + s2 - 8192)) ltac:(apply v_add_m8k; lia).   (* [comment removed for export] *)
      fsd F_4e67c D_4e67c (Z_to_bv 64 (cur + 8)).        (* [comment removed for export] *)
      fsd F_4e680 D_4e680 (Z_to_bv 64 (cur + 16)).       (* [comment removed for export] *)
      fsd F_4e684 D_4e684 (Z_to_bv 64 (nxt + 8)).        (* [comment removed for export] *)
      fsd F_4e688 D_4e688 (Z_to_bv 64 (nxt + 16)).       (* [comment removed for export] *)
      ab_ft F_4e68c D_4e68c ltac:(condz).                (* [comment removed for export] *)
      cld8 F_4e690 D_4e690 (Z_to_bv 64 nn) Rnn.          (* [comment removed for export] *)
      cld8 F_4e694 D_4e694 (Z_to_bv 64 lastv) Rlast.     (* [comment removed for export] *)
      fsd F_4e698 D_4e698 (Z_to_bv 64 cur).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End MGA.

(* [comment removed for export] *)
Section MGB.
  Variables (mem rom : word -> option byte) (S : word) (cur nxt ext glen lastv tsz tlast : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HK : mg_keep S regs regs.
  Hypothesis HH : mg_head regs cur nxt ext.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 glen.
  Hypothesis H7 : getr regs 7 = Z_to_bv 64 lastv.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hglen : (1 <= glen < 2 ^ 28)%Z.
  Hypothesis Hlastv : (0 <= lastv < 2 ^ 64)%Z.
  Hypothesis Htsz : (0 <= tsz < 2 ^ 28)%Z.
  Hypothesis Hcur : (AIMGHI <= cur /\ cur + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hnxt : (AIMGHI <= nxt /\ nxt + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Htl : (tsz <> 0 -> (AIMGHI <= tlast /\ tlast + 8192 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2288)) 32 = true.
  Hypothesis Hoknxt : store_ok BSEGS mem (Z_to_bv 64 nxt) 8 = true.
  Hypothesis Hoktl : (tsz <> 0)%Z -> store_ok BSEGS mem (Z_to_bv 64 tlast) 8 = true.
  Hypothesis Rtsz : rdn BSEGS mem (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 tsz)).
  Hypothesis Rtlast : rdn BSEGS mem (at_ S (-2272)) 8 = Some (LE8 (Z_to_bv 64 tlast)).

  Lemma mg_mtail_b :
    exists r, msteps BSEGS (mkst regs (0x4e69c : word) mem rom) (mkst r (0x4e6e4 : word) (fr_mgb mem S cur nxt glen lastv tsz tlast) rom)
      /\ mg_keep S regs r /\ mg_head r cur nxt ext /\ getr r 13 = Z_to_bv 64 (tsz + 1).
  Proof using Rtlast Rtsz Hoktl Hoknxt Hstk Htl Hnxt Htsz Hlastv Hglen HS H7 H13 HH HK.
    destruct HK as (K2 & K10 & K11 & _). destruct HH as (A14 & A5 & A12 & A15 & A16 & A17).
    (lazymatch goal with |- ?G => let G' := eval unfold mg_keep, mg_head, fr_mgb in G in change_no_check G' end). pose proof (u64_range S) as HSr. pose proof (sok_glist mem) as Hokgq.
    Ltac mt2n Rtsz :=
      ab_ft F_4e69c D_4e69c ltac:(condz);                (* [comment removed for export] *)
      av F_4e6a0 D_4e6a0 (Z_to_bv 64 (glen - 1)) ltac:(valz);    (* [comment removed for export] *)
      fsd F_4e6a4 D_4e6a4 (Z_to_bv 64 (IBq + 888));      (* [comment removed for export] *)
      cld8 F_4e6a8 D_4e6a8 (Z_to_bv 64 tsz) Rtsz;        (* [comment removed for export] *)
      fsd F_4e6ac D_4e6ac (Z_to_bv 64 nxt).              (* [comment removed for export] *)
    Ltac mt2l Rtsz :=
      ab_tk F_4e69c D_4e69c ltac:(condz);                (* [comment removed for export] *)
      fsd F_4e6c4 D_4e6c4 (Z_to_bv 64 (IBq + 904));      (* [comment removed for export] *)
      av F_4e6c8 D_4e6c8 (Z_to_bv 64 (glen - 1)) ltac:(valz);
      fsd F_4e6cc D_4e6cc (Z_to_bv 64 (IBq + 888));
      cld8 F_4e6d0 D_4e6d0 (Z_to_bv 64 tsz) Rtsz;
      fsd F_4e6d4 D_4e6d4 (Z_to_bv 64 nxt).
    Ltac mt3e :=
      fsd F_4e6dc D_4e6dc (at_ S (-2280));               (* [comment removed for export] *)
      an F_4e6e0 D_4e6e0.                                (* [comment removed for export] *)
    Ltac mt3n Rtlast :=
      cld8 F_4e6b4 D_4e6b4 (Z_to_bv 64 tlast) Rtlast;    (* [comment removed for export] *)
      fsd F_4e6b8 D_4e6b8 (Z_to_bv 64 tlast);            (* [comment removed for export] *)
      av F_4e6bc D_4e6bc (Z_to_bv 64 (tsz + 1)) ltac:(valz);     (* [comment removed for export] *)
      an F_4e6c0 D_4e6c0.                                (* [comment removed for export] *)
    destruct (Z.eqb_spec lastv nxt) as [El | Nl]; destruct (Z.eqb_spec tsz 0) as [Et | Nt]; (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end);
      try (replace (tsz + 1)%Z with 1%Z by lia).
    - wd_eexists. split; [mt2l Rtsz; ab_ft F_4e6d8 D_4e6d8 ltac:(condz); mt3e; wd_refl | post].
    - pose proof (Htl Nt) as Ht1. pose proof (Hoktl Nt) as Hoktl'.
      wd_eexists. split; [mt2l Rtsz; ab_tk F_4e6d8 D_4e6d8 ltac:(condz); mt3n Rtlast; wd_refl | post].
    - wd_eexists. split; [mt2n Rtsz; ab_tk F_4e6b0 D_4e6b0 ltac:(condz); mt3e; wd_refl | post].
    - pose proof (Htl Nt) as Ht1. pose proof (Hoktl Nt) as Hoktl'.
      wd_eexists. split; [mt2n Rtsz; ab_ft F_4e6b0 D_4e6b0 ltac:(condz); mt3n Rtlast; wd_refl | post].
  Qed.
End MGB.

(* [comment removed for export] *)
Section MGC.
  Variables (mem rom : word -> option byte) (S : word) (cur nxt ext nn tsz tbytes : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HK : mg_keep S regs regs.
  Hypothesis HH : mg_head regs cur nxt ext.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 (tsz + 1).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hnn : (0 <= nn < 2 ^ 64)%Z.
  Hypothesis Htb : (0 <= tbytes < 2 ^ 42)%Z.
  Hypothesis Hext : (0 <= ext < 2 ^ 42)%Z.
  Hypothesis Hcur : (AIMGHI <= cur /\ cur + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2288)) 32 = true.
  Hypothesis Rtb : rdn BSEGS mem (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 tbytes)).
  Hypothesis Rcn : rdn BSEGS mem (Z_to_bv 64 cur) 8 = Some (LE8 (Z_to_bv 64 nn)).

  Lemma mg_mtail_c :
    exists r, msteps BSEGS (mkst regs (0x4e6e4 : word) mem rom)
                (mkst r (if (nn =? 0)%Z then (0x4e704 : word) else (0x4e620 : word)) (fr_mgc mem S nxt tsz tbytes) rom)
      /\ mg_keep S regs r /\ mg_head r cur nn (ext + 8192).
  Proof using Rcn Rtb Hstk Hcur Hext Htb Hnn HS H13 HH HK.
    destruct HK as (K2 & K10 & K11 & _). destruct HH as (A14 & A5 & A12 & A15 & A16 & A17).
    (lazymatch goal with |- ?G => let G' := eval unfold mg_keep, mg_head, fr_mgc in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    Ltac mt4 Rtb Rcn :=
      fsd F_4e6e4 D_4e6e4 (at_ S (-2288));               (* [comment removed for export] *)
      fsd F_4e6e8 D_4e6e8 (at_ S (-2272));               (* [comment removed for export] *)
      cld8 F_4e6ec D_4e6ec (Z_to_bv 64 tbytes) Rtb;      (* [comment removed for export] *)
      av F_4e6f0 D_4e6f0 (Z_to_bv 64 (ext + 8192)) ltac:(valz);  (* [comment removed for export] *)
      av F_4e6f4 D_4e6f4 (Z_to_bv 64 (tbytes + 8192)) ltac:(valz);   (* [comment removed for export] *)
      fsd F_4e6f8 D_4e6f8 (at_ S (-2264));               (* [comment removed for export] *)
      cld8 F_4e6fc D_4e6fc (Z_to_bv 64 nn) Rcn.          (* [comment removed for export] *)
    destruct (Z.eqb_spec nn 0) as [En | Nn].
    - wd_eexists. split; [mt4 Rtb Rcn; ab_ft F_4e700 D_4e700 ltac:(condz); wd_refl | post].
    - wd_eexists. split; [mt4 Rtb Rcn; ab_tk F_4e700 D_4e700 ltac:(condz); wd_refl | post].
  Qed.
End MGC.

End FPGen.
End BoAllocFRcM1.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac BoAllocFRcM1.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation IBq := 0x10ab58 (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wws_cons : forall (mem : word -> option byte) a (w : word) ws, 0 <= a -> a + 8 < 2 ^ 64 ->
  wws mem a (w :: ws) = wws (wbytes mem (Z_to_bv 64 a) (LE8 w)) (a + 8) ws.
Proof.
  intros mem a w ws H0 H1. (lazymatch goal with |- ?G => let G' := eval unfold wws, wwb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [map concat] in G in change_no_check G' end). rewrite wbytes_app, length_N_to_le_bytes. f_equal.
  apply bv_eq. rewrite at_u by (wd_ulia_c). unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
Qed.
Lemma wws_out : forall (mem : word -> option byte) a ws (x : word), 0 <= a -> a + 8 * Z.of_nat (length ws) < 2 ^ 64 ->
  (U x < a \/ a + 8 * Z.of_nat (length ws) <= U x) -> wws mem a ws x = mem x.
Proof.
  intros mem a ws x H0 H1 Hx. (lazymatch goal with |- ?G => let G' := eval unfold wws in G in change_no_check G' end). apply wbytes_outside; rewrite length_wwb; wd_ulia.
Qed.
Lemma wws_grows : forall (mem : word -> option byte) a ws, mem_grows mem (wws mem a ws).
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold wws in G in change_no_check G' end). apply wbytes_grows. Qed.
Lemma rdn_wws_out : forall (mem : word -> option byte) a ws (c : Z) (n : nat), 0 <= a -> a + 8 * Z.of_nat (length ws) < 2 ^ 64 ->
  0 <= c -> c + Z.of_nat n < 2 ^ 64 -> (c + Z.of_nat n <= a \/ a + 8 * Z.of_nat (length ws) <= c) ->
  rdn BSEGS (wws mem a ws) (Z_to_bv 64 c) n = rdn BSEGS mem (Z_to_bv 64 c) n.
Proof.
  intros mem a ws c n H0 H1 H2 H3 Hd. (lazymatch goal with |- ?G => let G' := eval unfold wws in G in change_no_check G' end). apply rdn_wbytes_out; rewrite ?length_wwb; wd_ulia.
Qed.
Lemma rdn_wws_nth : forall ws (mem : word -> option byte) a j (w : word), 0 <= a -> a + 8 * Z.of_nat (length ws) < 2 ^ 64 ->
  nth_error ws j = Some w -> rdn BSEGS (wws mem a ws) (Z_to_bv 64 (a + 8 * Z.of_nat j)) 8 = Some (LE8 w).
Proof.
  induction ws as [|w0 r IH]; intros mem a j w H0 H1 Hj; [destruct j; discriminate Hj|].
  cbn [length] in H1. rewrite Nat2Z.inj_succ in H1. rewrite wws_cons by lia. destruct j as [|j].
  - cbn in Hj. injection Hj as <-. change (Z.of_nat 0) with 0. replace (a + 8 * 0) with a by lia.
    rewrite rdn_wws_out by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). apply rdn_wbytes_hit8. unorm. lia.
  - cbn [nth_error] in Hj. replace (a + 8 * Z.of_nat (S j)) with (a + 8 + 8 * Z.of_nat j) by lia. apply IH; [lia | lia | exact Hj].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PIECES.
  Variables (S : word).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.

  Lemma fr_mgc_out : forall (m9 : word -> option byte) nxt tsz tbytes (x : word),
    (U x < U S - 2288 \/ U S - 2280 <= U x) -> (U x < U S - 2272 \/ U S - 2256 <= U x) -> fr_mgc m9 S nxt tsz tbytes x = m9 x.
  Proof using HS.
    intros m9 nxt tsz tbytes x H1 H2. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_mgc in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma fr_mgc_rd : forall (m9 : word -> option byte) nxt tsz tbytes (c : Z) (n : nat),
    0 <= c -> c + Z.of_nat n < 2 ^ 64 -> (c + Z.of_nat n <= U S - 2288 \/ U S - 2256 <= c \/ (U S - 2280 <= c /\ c + Z.of_nat n <= U S - 2272)) ->
    rdn BSEGS (fr_mgc m9 S nxt tsz tbytes) (Z_to_bv 64 c) n = rdn BSEGS m9 (Z_to_bv 64 c) n.
  Proof using HS.
    intros m9 nxt tsz tbytes c n H0 H1 HD. pose proof (u64_range S) as HSr. apply rdn_ext; [wd_ulia|].
    intros x Hx. revert Hx. unorm. intros Hx. apply fr_mgc_out; lia.
  Qed.

  Lemma fr_mgb_out : forall (m5 : word -> option byte) cur nxt glen lastv tsz tlast (x : word),
    0 <= nxt -> nxt + 8 < 2 ^ 64 -> (tsz <> 0 -> 0 <= tlast /\ tlast + 8 < 2 ^ 64) ->
    (U x < IBq + 888 \/ IBq + 896 <= U x) -> (lastv = nxt -> U x < IBq + 904 \/ IBq + 912 <= U x) -> (U x < nxt \/ nxt + 8 <= U x) ->
    (tsz = 0 -> U x < U S - 2280 \/ U S - 2272 <= U x) -> (tsz <> 0 -> U x < tlast \/ tlast + 8 <= U x) ->
    fr_mgb m5 S cur nxt glen lastv tsz tlast x = m5 x.
  Proof using HS.
    intros m5 cur nxt glen lastv tsz tlast x Gn1 Gn2 Gt H1 H2 H3 H4 H5. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_mgb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec tsz 0) as [Et | Nt]; [specialize (H4 Et) | specialize (H5 Nt); specialize (Gt Nt)];
      (destruct (Z.eqb_spec lastv nxt) as [El | Nl]; [specialize (H2 El)|]);
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u by lia; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia; reflexivity.
  Qed.
  Lemma fr_mgb_rd : forall (m5 : word -> option byte) cur nxt glen lastv tsz tlast (c : Z) (n : nat),
    0 <= nxt -> nxt + 8 < 2 ^ 64 -> (tsz <> 0 -> 0 <= tlast /\ tlast + 8 < 2 ^ 64) ->
    0 <= c -> c + Z.of_nat n < 2 ^ 64 ->
    (c + Z.of_nat n <= IBq + 888 \/ IBq + 896 <= c) -> (lastv = nxt -> c + Z.of_nat n <= IBq + 904 \/ IBq + 912 <= c) -> (c + Z.of_nat n <= nxt \/ nxt + 8 <= c) ->
    (tsz = 0 -> c + Z.of_nat n <= U S - 2280 \/ U S - 2272 <= c) -> (tsz <> 0 -> c + Z.of_nat n <= tlast \/ tlast + 8 <= c) ->
    rdn BSEGS (fr_mgb m5 S cur nxt glen lastv tsz tlast) (Z_to_bv 64 c) n = rdn BSEGS m5 (Z_to_bv 64 c) n.
  Proof using HS.
    intros m5 cur nxt glen lastv tsz tlast c n Gn1 Gn2 Gt H0 H0' H1 H2 H3 H4 H5. apply rdn_ext; [wd_ulia|].
    intros x Hx. revert Hx. unorm. intros Hx. apply fr_mgb_out; try assumption; try lia.
  Qed.

  Lemma fr_mga_out : forall (mem : word -> option byte) cur nxt s1 s2 cnt nn (x : word),
    0 <= cur -> cur + 24 < 2 ^ 64 -> 0 <= nxt -> nxt + 24 < 2 ^ 64 ->
    (U x < cur \/ cur + 24 <= U x) -> (U x < nxt + 8 \/ nxt + 24 <= U x) -> fr_mga mem cur nxt s1 s2 cnt nn x = mem x.
  Proof using.
    intros mem cur nxt s1 s2 cnt nn x G1 G2 G3 G4 H1 H2. (lazymatch goal with |- ?G => let G' := eval unfold fr_mga in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma fr_mga_rd : forall (mem : word -> option byte) cur nxt s1 s2 cnt nn (c : Z) (n : nat),
    0 <= cur -> cur + 24 < 2 ^ 64 -> 0 <= nxt -> nxt + 24 < 2 ^ 64 -> 0 <= c -> c + Z.of_nat n < 2 ^ 64 ->
    (c + Z.of_nat n <= cur \/ cur + 24 <= c) -> (c + Z.of_nat n <= nxt + 8 \/ nxt + 24 <= c) ->
    rdn BSEGS (fr_mga mem cur nxt s1 s2 cnt nn) (Z_to_bv 64 c) n = rdn BSEGS mem (Z_to_bv 64 c) n.
  Proof using.
    intros mem cur nxt s1 s2 cnt nn c n G1 G2 G3 G4 H0 H0' H1 H2. apply rdn_ext; [wd_ulia|].
    intros x Hx. revert Hx. unorm. intros Hx. apply fr_mga_out; lia.
  Qed.
End PIECES.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MGMEM.
  Variables (mem : word -> option byte) (S : word) (cur nxt c1 s1 s2 nn glen lastv tsz tlast tbytes : Z) (ws : list word).
  #[local] Abbreviation c2 := (Z.of_nat (length ws)).
  Hypothesis HS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Hc : 0 <= c1 /\ c1 + c2 <= 1021.
  Hypothesis Hcur : AIMGHI <= cur /\ cur + 8192 <= U S - 3584.
  Hypothesis Hnxt : AIMGHI <= nxt /\ nxt + 8192 <= U S - 3584.
  Hypothesis Hsep : cur + 8192 <= nxt \/ nxt + 8192 <= cur.
  Hypothesis Htl : tsz <> 0 -> (AIMGHI <= tlast /\ tlast + 8192 <= U S - 3584)
                                /\ (tlast + 8192 <= cur \/ cur + 8192 <= tlast) /\ (tlast + 8192 <= nxt \/ nxt + 8192 <= tlast).

  #[local] Abbreviation M1 := (wws mem (cur + 24 + 8 * c1) ws).
  #[local] Abbreviation M5 := (fr_mga M1 cur nxt s1 s2 (c1 + c2) nn).
  #[local] Abbreviation M9 := (fr_mgb M5 S cur nxt glen lastv tsz tlast).
  #[local] Abbreviation MM := (fr_mg M1 S cur nxt s1 s2 (c1 + c2) nn glen lastv tsz tlast tbytes).

  Definition mg_foot (x : Z) : Prop :=
    (cur <= x < cur + 24) \/ (cur + 24 + 8 * c1 <= x < cur + 24 + 8 * (c1 + c2)) \/ (nxt <= x < nxt + 24)
    \/ (IBq + 888 <= x < IBq + 896) \/ (lastv = nxt /\ IBq + 904 <= x < IBq + 912)
    \/ (tsz = 0 /\ U S - 2280 <= x < U S - 2272) \/ (tsz <> 0 /\ tlast <= x < tlast + 8)
    \/ (U S - 2288 <= x < U S - 2280) \/ (U S - 2272 <= x < U S - 2256).

  #[local] Set Default Proof Using "HS Hc Hcur Hnxt Hsep Htl".
  Lemma Gtl : tsz <> 0 -> 0 <= tlast /\ tlast + 8 < 2 ^ 64.
  Proof. intros N. destruct (Htl N) as ((A & B) & _). pose proof (u64_range S). clear - A B HS. lia. Qed.

  Lemma fr_mg_out : forall x : word, ~ mg_foot (U x) -> MM x = mem x.
  Proof.
    intros x NF. pose proof (u64_range S) as HSr. pose proof (u64_range x) as Hxr. unfold mg_foot in NF.
    apply Decidable.not_or in NF as [N1 NF]. apply Decidable.not_or in NF as [N2 NF]. apply Decidable.not_or in NF as [N3 NF].
    apply Decidable.not_or in NF as [N4 NF]. apply Decidable.not_or in NF as [N5 NF]. apply Decidable.not_or in NF as [N6 NF].
    apply Decidable.not_or in NF as [N7 NF]. apply Decidable.not_or in NF as [N8 N9].
    (lazymatch goal with |- ?G => let G' := eval unfold fr_mg in G in change_no_check G' end). rewrite fr_mgc_out; [| exact HS | clear - N8; lia | clear - N9; lia].
    rewrite (fr_mgb_out S HS); [| clear - Hnxt; lia | clear - Hnxt HS HSr; lia | exact Gtl | clear - N4; lia | intros E; clear - N5 E; lia | clear - N3; lia
                                | intros E; clear - N6 E; lia | intros E; clear - N7 E; lia].
    rewrite fr_mga_out; [| clear - Hcur; lia | clear - Hcur HS HSr; lia | clear - Hnxt; lia | clear - Hnxt HS HSr; lia | clear - N1; lia | clear - N3; lia].
    apply wws_out; [clear - Hcur Hc; lia | clear - Hcur Hc HS HSr; lia | clear - N2; lia].
  Qed.
  Lemma fr_mg_grows : mem_grows mem MM.
  Proof.
    set (m1 := wws mem (cur + 24 + 8 * c1) ws). assert (G1 : mem_grows mem m1) by apply wws_grows.
    eapply mem_grows_trans; [exact G1|]. clearbody m1. (lazymatch goal with |- ?G => let G' := eval unfold fr_mg, fr_mgc, fr_mgb, fr_mga in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec lastv nxt); destruct (Z.eqb_spec tsz 0); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Qed.

  (* [comment removed for export] *)
  Ltac topc := pose proof (u64_range S) as HSr; (lazymatch goal with |- ?G => let G' := eval unfold fr_mg, fr_mgc in G in change_no_check G' end);
               repeat (wd_rdstep rd8_side).
  Lemma fr_mg_tsize : rdn BSEGS MM (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 (tsz + 1))).  Proof. topc. Qed.
  Lemma fr_mg_tlast : rdn BSEGS MM (at_ S (-2272)) 8 = Some (LE8 (Z_to_bv 64 nxt)).  Proof. topc. Qed.
  Lemma fr_mg_tbytes : rdn BSEGS MM (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 (tbytes + 8192))).  Proof. topc. Qed.

  (* [comment removed for export] *)
  Lemma thru_c : forall c (n : nat), 0 <= c -> c + Z.of_nat n <= U S - 3584 -> rdn BSEGS MM (Z_to_bv 64 c) n = rdn BSEGS M9 (Z_to_bv 64 c) n.
  Proof. intros c n H0 H1. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_mg in G in change_no_check G' end). apply (fr_mgc_rd S HS); [exact H0 | clear - H1 HS HSr; lia | left; clear - H1; lia]. Qed.

  Lemma fr_mg_tfirst : tsz = 0 -> rdn BSEGS MM (at_ S (-2280)) 8 = Some (LE8 (Z_to_bv 64 nxt)).
  Proof.
    intros E. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_mg in G in change_no_check G' end).
    replace (at_ S (-2280)) with (Z_to_bv 64 (U S - 2280) : word) by (apply bv_eq; rewrite at_u by lia; wd_ulia).
    rewrite (fr_mgc_rd S HS) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). (lazymatch goal with |- ?G => let G' := eval unfold fr_mgb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). destruct (Z.eqb_spec tsz 0) as [_ | N]; [| exfalso; exact (N E)].
    replace (Z_to_bv 64 (U S - 2280) : word) with (at_ S (-2280)) by (apply bv_eq; rewrite at_u by lia; wd_ulia). rd_hit8.
  Qed.
  Lemma fr_mg_glen : rdn BSEGS MM (Z_to_bv 64 (IBq + 888)) 8 = Some (LE8 (Z_to_bv 64 (glen - 1))).
  Proof.
    pose proof (u64_range S) as HSr. rewrite thru_c by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HS; lia). (lazymatch goal with |- ?G => let G' := eval unfold fr_mgb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec tsz 0) as [Et | Nt]; [| destruct (Htl Nt) as (Ht1 & _)];
      (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]); (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]); rd_hit8.
  Qed.
  Lemma fr_mg_last : lastv = nxt -> rdn BSEGS MM (Z_to_bv 64 (IBq + 904)) 8 = Some (LE8 (Z_to_bv 64 cur)).
  Proof.
    intros E. pose proof (u64_range S) as HSr. rewrite thru_c by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HS; lia). (lazymatch goal with |- ?G => let G' := eval unfold fr_mgb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec lastv nxt) as [_ | N]; [| exfalso; exact (N E)].
    destruct (Z.eqb_spec tsz 0) as [Et | Nt]; [| destruct (Htl Nt) as (Ht1 & _)];
      (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]); (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
      (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]); rd_hit8.
  Qed.
  Lemma fr_mg_nnext : rdn BSEGS MM (Z_to_bv 64 nxt) 8 = Some (LE8 (Z_to_bv 64 0)).
  Proof.
    pose proof (u64_range S) as HSr. rewrite thru_c by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hnxt; lia). (lazymatch goal with |- ?G => let G' := eval unfold fr_mgb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec tsz 0) as [Et | Nt]; [| destruct (Htl Nt) as (Ht1 & _ & Ht3)];
      (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]); rd_hit8.
  Qed.
  Lemma fr_mg_tlnext : tsz <> 0 -> rdn BSEGS MM (Z_to_bv 64 tlast) 8 = Some (LE8 (Z_to_bv 64 nxt)).
  Proof.
    intros N. destruct (Htl N) as (Ht1 & _). pose proof (u64_range S) as HSr. rewrite thru_c by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Ht1; lia). (lazymatch goal with |- ?G => let G' := eval unfold fr_mgb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec tsz 0) as [E | _]; [exfalso; exact (N E)|]. rd_hit8.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_mg_glen_def : forall x : word, IBq + 888 <= U x < IBq + 896 -> MM x <> None.
  Proof.
    intros x Hx. pose proof (u64_range S) as HSr. (lazymatch goal with |- ?G => let G' := eval unfold fr_mg in G in change_no_check G' end). rewrite fr_mgc_out; [| exact HS | left; clear - Hx HS; lia | left; clear - Hx HS; lia].
    (lazymatch goal with |- ?G => let G' := eval unfold fr_mgb in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec tsz 0) as [Et | Nt]; [| destruct (Htl Nt) as ((T1 & T2) & _)];
      (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, ?at_u by lia; wd_ulia_c | rewrite length_N_to_le_bytes, ?at_u by lia; wd_ulia_c]);
      (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes; wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c]);
      (rewrite wbytes_inside; [discriminate | rewrite length_N_to_le_bytes; wd_ulia_c | rewrite length_N_to_le_bytes; wd_ulia_c]).
  Qed.

  (* [comment removed for export] *)
  Lemma thru_cb : forall c (n : nat), 0 <= c -> c + Z.of_nat n <= U S - 3584 -> AIMGHI <= c ->
    (c + Z.of_nat n <= nxt \/ nxt + 8 <= c) -> (tsz <> 0 -> c + Z.of_nat n <= tlast \/ tlast + 8 <= c) ->
    rdn BSEGS MM (Z_to_bv 64 c) n = rdn BSEGS M5 (Z_to_bv 64 c) n.
  Proof.
    intros c n H0 H1 H2 H3 H4. pose proof (u64_range S) as HSr. rewrite thru_c by assumption.
    apply (fr_mgb_rd S HS); [clear - Hnxt; lia | clear - Hnxt HS HSr; lia | exact Gtl | exact H0 | clear - H1 HS HSr; lia
                            | right; clear - H2; lia | intros _; right; clear - H2; lia | exact H3 | intros _; left; clear - H1; lia | exact H4].
  Qed.
  Ltac cb_side := first [ (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hcur; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hnxt; lia ].
  Lemma fr_mg_cnext : rdn BSEGS MM (Z_to_bv 64 cur) 8 = Some (LE8 (Z_to_bv 64 nn)).
  Proof.
    rewrite thru_cb; [| clear - Hcur; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hcur; lia | clear - Hcur; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsep; lia | intros N; destruct (Htl N) as (_ & T2 & _); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - T2; lia].
    (lazymatch goal with |- ?G => let G' := eval unfold fr_mga in G in change_no_check G' end). rd_hit8.
  Qed.
  Lemma fr_mg_csize : rdn BSEGS MM (Z_to_bv 64 (cur + 8)) 8 = Some (LE8 (Z_to_bv 64 (s1 + s2 - 8192))).
  Proof.
    rewrite thru_cb; [| clear - Hcur; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hcur; lia | clear - Hcur; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsep; lia | intros N; destruct (Htl N) as (_ & T2 & _); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - T2; lia].
    (lazymatch goal with |- ?G => let G' := eval unfold fr_mga in G in change_no_check G' end). pose proof (u64_range S) as HSr. repeat (wd_rdstep rd8_side).
  Qed.
  Lemma fr_mg_ccount : rdn BSEGS MM (Z_to_bv 64 (cur + 16)) 8 = Some (LE8 (Z_to_bv 64 (c1 + c2))).
  Proof.
    rewrite thru_cb; [| clear - Hcur; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hcur; lia | clear - Hcur; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsep; lia | intros N; destruct (Htl N) as (_ & T2 & _); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - T2; lia].
    (lazymatch goal with |- ?G => let G' := eval unfold fr_mga in G in change_no_check G' end). pose proof (u64_range S) as HSr. repeat (wd_rdstep rd8_side).
  Qed.
  Lemma fr_mg_nsize : rdn BSEGS MM (Z_to_bv 64 (nxt + 8)) 8 = Some (LE8 (Z_to_bv 64 8192)).
  Proof.
    rewrite thru_cb; [| clear - Hnxt; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hnxt; lia | clear - Hnxt; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | intros N; destruct (Htl N) as (_ & _ & T3); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - T3; lia].
    (lazymatch goal with |- ?G => let G' := eval unfold fr_mga in G in change_no_check G' end). pose proof (u64_range S) as HSr. clear Htl. destruct Hsep as [Q | Q]; repeat (wd_rdstep rd8_side).
  Qed.
  Lemma fr_mg_ncount : rdn BSEGS MM (Z_to_bv 64 (nxt + 16)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Proof.
    rewrite thru_cb; [| clear - Hnxt; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hnxt; lia | clear - Hnxt; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | intros N; destruct (Htl N) as (_ & _ & T3); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - T3; lia].
    (lazymatch goal with |- ?G => let G' := eval unfold fr_mga in G in change_no_check G' end). pose proof (u64_range S) as HSr. clear Htl. destruct Hsep as [Q | Q]; repeat (wd_rdstep rd8_side).
  Qed.
  Lemma fr_mg_item : forall j (w : word), nth_error ws j = Some w ->
    rdn BSEGS MM (Z_to_bv 64 (cur + 24 + 8 * (c1 + Z.of_nat j))) 8 = Some (LE8 w).
  Proof.
    intros j w Hj. assert (Hjl : (j < length ws)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). pose proof (u64_range S) as HSr.
    rewrite thru_cb; [| clear - Hcur Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hcur Hc Hjl; lia | clear - Hcur Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsep Hc Hjl; lia
                      | intros N; destruct (Htl N) as (_ & T2 & _); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - T2 Hc Hjl; lia].
    rewrite fr_mga_rd; [| clear - Hcur; lia | clear - Hcur HS HSr; lia | clear - Hnxt; lia | clear - Hnxt HS HSr; lia | clear - Hcur Hc; lia
                        | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hcur Hc Hjl HS HSr; lia | right; clear - Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hsep Hc Hjl; lia].
    replace (cur + 24 + 8 * (c1 + Z.of_nat j)) with (cur + 24 + 8 * c1 + 8 * Z.of_nat j) by lia.
    apply rdn_wws_nth; [clear - Hcur Hc; lia | clear - Hcur Hc HS HSr; lia | exact Hj].
  Qed.
End MGMEM.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocF7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
(* [comment removed for export] *)

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma sok_lockword : forall m, store_ok BSEGS m (Z_to_bv 64 0x10aec8) 4 = true.
Proof using. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sok_glist : forall m, store_ok BSEGS m (Z_to_bv 64 0x10aed0) 32 = true.
Proof using. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma v_andi_255_and : forall x : word, v_andi x 255 = v_and x (Z_to_bv 64 255).
Proof using.
  intros x. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1. rewrite v_andi_Z by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. rewrite v_and_Z by lia. reflexivity.
Qed.
Lemma lock_byte0 : forall (b0 b1 b2 b3 : byte) (v : word),
  bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v -> v_andi (v_lw v) 255 = Z_to_bv 64 (bv_unsigned b0).
Proof using.
  intros b0 b1 b2 b3 v Hv. rewrite v_andi_255_and.
  rewrite (and_mask_byte [b0; b1; b2; b3] v (Z_to_bv 64 255) 0 eq_refl Hv ltac:(lia) ltac:(reflexivity)).
  (lazymatch goal with |- ?G => let G' := eval cbn [nth Z.of_nat Z.mul] in G in change_no_check G' end). rewrite Z.mul_1_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma drain_lock_69b04 : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 16 = Z_to_bv 64 0x10aec8 -> getr regs 15 = Z_to_bv 64 255 -> getr regs 17 = Z_to_bv 64 1 ->
  rdn BSEGS mem (Z_to_bv 64 0x10aec8) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps BSEGS (mkst regs (0x4e288 : word) mem rom)
    (mkst (regupd (regupd regs 5 (v_lw v)) 6 (Z_to_bv 64 0)) (0x4e2a4 : word)
          (wbytes mem (Z_to_bv 64 0x10aec8) [Z_to_bv 8 1; b1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H16 H15 H17 Hrd Hv.
  pose proof (xchg_byte_run BSEGS regs (0x4e288 : word) (0x4e28c : word) (0x4e290 : word) (0x4e294 : word)
                (0x4e298 : word) (0x4e29c : word) (0x4e2a0 : word) (0x4e2a4 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 5 16 6 17 15 _ [b0; b1; b2; b3] v 0%nat 1%Z
                F_4e288 eq_refl D_4e288 F_4e28c eq_refl D_4e28c F_4e290 eq_refl D_4e290 F_4e294 eq_refl D_4e294
                F_4e298 eq_refl D_4e298 F_4e29c eq_refl D_4e29c F_4e2a0 eq_refl D_4e2a0) as R.
  rewrite H16, H15, H17 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_lockword | unorm; reflexivity | lia | assumption].
Qed.


(* [comment removed for export] *)
Lemma drain_trylock_4e350 : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 16 = Z_to_bv 64 0x10aec8 -> getr regs 14 = Z_to_bv 64 0xff00 -> getr regs 15 = Z_to_bv 64 0x100 ->
  rdn BSEGS mem (Z_to_bv 64 0x10aec8) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps BSEGS (mkst regs (0x4e350 : word) mem rom)
    (mkst (regupd (regupd regs 17 (v_lw v)) 5 (Z_to_bv 64 0)) (0x4e36c : word)
          (wbytes mem (Z_to_bv 64 0x10aec8) [b0; Z_to_bv 8 1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H16 H14 H15 Hrd Hv.
  pose proof (xchg_byte_run BSEGS regs (0x4e350 : word) (0x4e354 : word) (0x4e358 : word) (0x4e35c : word)
                (0x4e360 : word) (0x4e364 : word) (0x4e368 : word) (0x4e36c : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 17 16 5 15 14 _ [b0; b1; b2; b3] v 1%nat 1%Z
                F_4e350 eq_refl D_4e350 F_4e354 eq_refl D_4e354 F_4e358 eq_refl D_4e358 F_4e35c eq_refl D_4e35c
                F_4e360 eq_refl D_4e360 F_4e364 eq_refl D_4e364 F_4e368 eq_refl D_4e368) as R.
  rewrite H16, H14, H15 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_lockword | unorm; reflexivity | lia | assumption].
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_d7n (mem : word -> option byte) (S ra0 : word) (s0v s1v s2v s3v : word) (T len first lastq qb glen glast gqb : Z) (b1 b2 b3 : byte)
  : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (LE8 ra0))
    (at_ S (-2224)) (LE8 s0v))
    (at_ S (-2232)) (LE8 s1v))
    (at_ S (-2240)) (LE8 s2v))
    (at_ S (-2248)) (LE8 s3v))
    (Z_to_bv 64 0x10aec8) [Z_to_bv 8 1; b1; b2; b3])
    (Z_to_bv 64 glast) (LE8 (Z_to_bv 64 first)))
    (Z_to_bv 64 (0x10ab58 + 888)) (LE8 (Z_to_bv 64 (glen + len))))
    (Z_to_bv 64 (0x10ab58 + 904)) (LE8 (Z_to_bv 64 lastq)))
    (Z_to_bv 64 (T + 80)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (T + 88)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (T + 96)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (0x10ab58 + 912)) (LE8 (Z_to_bv 64 (gqb + qb))))
    (Z_to_bv 64 (T + 104)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0].
(* [comment removed for export] *)
Definition fr_d7e (mem : word -> option byte) (S ra0 : word) (s0v s1v s2v s3v : word) (T len first lastq qb gqb : Z) (b1 b2 b3 : byte)
  : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (LE8 ra0))
    (at_ S (-2224)) (LE8 s0v))
    (at_ S (-2232)) (LE8 s1v))
    (at_ S (-2240)) (LE8 s2v))
    (at_ S (-2248)) (LE8 s3v))
    (Z_to_bv 64 0x10aec8) [Z_to_bv 8 1; b1; b2; b3])
    (Z_to_bv 64 (0x10ab58 + 904)) (LE8 (Z_to_bv 64 lastq)))
    (Z_to_bv 64 (0x10ab58 + 896)) (LE8 (Z_to_bv 64 first)))
    (Z_to_bv 64 (0x10ab58 + 888)) (LE8 (Z_to_bv 64 len)))
    (Z_to_bv 64 (T + 80)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (T + 88)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (T + 96)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (0x10ab58 + 912)) (LE8 (Z_to_bv 64 (gqb + qb))))
    (Z_to_bv 64 (T + 104)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0].
Hint Unfold fr_d7n fr_d7e : asfr.

Section DRAIN.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v a2v a3v : word).
  Variables (T len first lastq qb glen glast gqb : Z) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x10ab58 + 728).
  Hypothesis H11 : getr regs 11 = at_ (Z_to_bv 64 T) 80.
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hlen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Hqb : (0 <= qb < 2 ^ 40)%Z.
  Hypothesis Hglen : (0 <= glen < 2 ^ 40)%Z.
  Hypothesis Hgqb : (0 <= gqb < 2 ^ 40)%Z.
  Hypothesis Hfirst : (0 <= first < 2 ^ 64)%Z.
  Hypothesis Hlastq : (0 <= lastq < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2256)) 48 = true.     (* [comment removed for export] *)
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 (T + 80)) 32 = true.
  (* [comment removed for export] *)
  Hypothesis Rlen : rdn BSEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis Rfirst : rdn BSEGS mem (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 first)).
  Hypothesis Rlastq : rdn BSEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 lastq)).
  Hypothesis Rqb : rdn BSEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis Rglen : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).
  Hypothesis Rgqb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).
  Hypothesis Rmax : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis Rlock : rdn BSEGS mem (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; b1; b2; b3].

  (* [comment removed for export] *)
  #[local] Definition ret_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2208) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  (* [comment removed for export] *)
  Ltac d7_prefix HV :=
      an F_4e260 D_4e260;                              (* [comment removed for export] *)
      fsd F_4e264 D_4e264 (at_ S (-2216));             (* [comment removed for export] *)
      fsd F_4e268 D_4e268 (at_ S (-2224));             (* [comment removed for export] *)
      fsd F_4e26c D_4e26c (at_ S (-2232));             (* [comment removed for export] *)
      fsd F_4e270 D_4e270 (at_ S (-2240));             (* [comment removed for export] *)
      fsd F_4e274 D_4e274 (at_ S (-2248));             (* [comment removed for export] *)
      an F_4e278 D_4e278;                              (* [comment removed for export] *)
      an F_4e27c D_4e27c;                              (* [comment removed for export] *)
      an F_4e280 D_4e280;                              (* [comment removed for export] *)
      an F_4e284 D_4e284;                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (drain_lock_69b04 _ _ rom _ (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]
      | ];
      av F_4e2a4 D_4e2a4 (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity);   (* [comment removed for export] *)
      ab_ft F_4e2a8 D_4e2a8 ltac:(condz);              (* [comment removed for export] *)
      an F_4e2ac D_4e2ac;                              (* [comment removed for export] *)
      ab_ft F_4e2b0 D_4e2b0 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4e2b4 D_4e2b4 (Z_to_bv 64 len) Rlen;      (* [comment removed for export] *)
      ab_ft F_4e2b8 D_4e2b8 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4e2bc D_4e2bc (Z_to_bv 64 glen) Rglen.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac d7_tail :=
      fsd F_4e2fc D_4e2fc (Z_to_bv 64 (T + 80));       (* [comment removed for export] *)
      fsd F_4e300 D_4e300 (Z_to_bv 64 (T + 88));       (* [comment removed for export] *)
      fsd F_4e304 D_4e304 (Z_to_bv 64 (T + 96));       (* [comment removed for export] *)
      cld8 F_4e308 D_4e308 (Z_to_bv 64 qb) Rqb;        (* [comment removed for export] *)
      cld8 F_4e30c D_4e30c (Z_to_bv 64 gqb) Rgqb;      (* [comment removed for export] *)
      av F_4e310 D_4e310 (Z_to_bv 64 (gqb + qb)) ltac:(valz);   (* [comment removed for export] *)
      fsd F_4e314 D_4e314 (Z_to_bv 64 (0x10ab58 + 912));        (* [comment removed for export] *)
      fsd F_4e318 D_4e318 (Z_to_bv 64 (T + 104));      (* [comment removed for export] *)
      afence F_4e31c D_4e31c;                          (* [comment removed for export] *)
      fsb F_4e320 D_4e320 (Z_to_bv 64 0x10aec8) (Z_to_bv 8 0);  (* [comment removed for export] *)
      fldx F_4e324 D_4e324 (Z_to_bv 64 (gqb + qb));    (* [comment removed for export] *)
      cld8 F_4e328 D_4e328 (Z_to_bv 64 (2 ^ 28)) Rmax; (* [comment removed for export] *)
      ab_tk F_4e32c D_4e32c ltac:(condz);              (* [comment removed for export] *)
      fld F_4e378 D_4e378 ra0;                         (* [comment removed for export] *)
      fld F_4e37c D_4e37c s0v;                         (* [comment removed for export] *)
      fld F_4e380 D_4e380 s1v;                         (* [comment removed for export] *)
      fld F_4e384 D_4e384 s2v;                         (* [comment removed for export] *)
      fld F_4e388 D_4e388 s3v;                         (* [comment removed for export] *)
      an F_4e38c D_4e38c;                              (* [comment removed for export] *)
      aret F_4e390 D_4e390 ra0.                        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma drain_nr_n :
    (1 <= glen)%Z -> (gqb + qb <= 2 ^ 28)%Z ->
    (2 ^ 44 <= glast /\ glast + 8192 <= bv_unsigned S - 3584)%Z -> (glast + 8192 <= T \/ T + 4096 <= glast)%Z ->
    store_ok BSEGS mem (Z_to_bv 64 glast) 8 = true ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 904)) 8 = Some (LE8 (Z_to_bv 64 glast)) ->
    exists r,
      msteps BSEGS (mkst regs (0x4e260 : word) mem rom)
                   (mkst r ra0 (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3) rom)
      /\ ret_regs r.
  Proof using Rlock Rmax Rgqb Rglen Rqb Rlastq Rfirst Rlen HokT Hstk Hgqb Hglen Hqb Hlen HT HS H19 H18 H9 H8 H11 H10 H2 Hret H1.
    intros Hglen1 Hsum Hglast HglastT Hokgl Rglast. (lazymatch goal with |- ?G => let G' := eval unfold ret_regs in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    pose proof (sok_lockword mem) as Hoklk. pose proof (sok_glist mem) as Hokgq.
    assert (HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]))).
    { pose proof (lez4_range [Z_to_bv 8 0; b1; b2; b3] eq_refl) as B. rewrite u_Z2bv by lia. reflexivity. }
    wd_eexists. split.
    - d7_prefix HV.
      ab_ft F_4e2c0 D_4e2c0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e2c4 D_4e2c4 (Z_to_bv 64 glast) Rglast.  (* [comment removed for export] *)
      cld8 F_4e2c8 D_4e2c8 (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      cld8 F_4e2cc D_4e2cc (Z_to_bv 64 lastq) Rlastq.  (* [comment removed for export] *)
      av F_4e2d0 D_4e2d0 (Z_to_bv 64 (glen + len)) ltac:(valz).   (* [comment removed for export] *)
      fsd F_4e2d4 D_4e2d4 (Z_to_bv 64 glast);          (* [comment removed for export] *)
      fsd F_4e2d8 D_4e2d8 (Z_to_bv 64 (0x10ab58 + 888)).          (* [comment removed for export] *)
      fsd F_4e2dc D_4e2dc (Z_to_bv 64 (0x10ab58 + 904)).          (* [comment removed for export] *)
      an F_4e2e0 D_4e2e0.                              (* [comment removed for export] *)
      d7_tail.
      change (wbytes _ _ _) with (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3). rewrite ?at_0. wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma drain_nr_e :
    glen = 0%Z -> (gqb + qb <= 2 ^ 28)%Z ->
    exists r,
      msteps BSEGS (mkst regs (0x4e260 : word) mem rom)
                   (mkst r ra0 (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3) rom)
      /\ ret_regs r.
  Proof using Rlock Rmax Rgqb Rglen Rqb Rlastq Rfirst Rlen HokT Hstk Hgqb Hglen Hqb Hlen HT HS H19 H18 H9 H8 H11 H10 H2 Hret H1.
    intros Hglen0 Hsum. (lazymatch goal with |- ?G => let G' := eval unfold ret_regs in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    pose proof (sok_lockword mem) as Hoklk. pose proof (sok_glist mem) as Hokgq.
    assert (HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]))).
    { pose proof (lez4_range [Z_to_bv 8 0; b1; b2; b3] eq_refl) as B. rewrite u_Z2bv by lia. reflexivity. }
    wd_eexists. split.
    - d7_prefix HV.
      subst glen.
      ab_tk F_4e2c0 D_4e2c0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e2e4 D_4e2e4 (Z_to_bv 64 lastq) Rlastq.  (* [comment removed for export] *)
      fsd F_4e2e8 D_4e2e8 (Z_to_bv 64 (0x10ab58 + 904)).          (* [comment removed for export] *)
      cld8 F_4e2ec D_4e2ec (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      fsd F_4e2f0 D_4e2f0 (Z_to_bv 64 (0x10ab58 + 896)).          (* [comment removed for export] *)
      cld8 F_4e2f4 D_4e2f4 (Z_to_bv 64 len) Rlen.      (* [comment removed for export] *)
      fsd F_4e2f8 D_4e2f8 (Z_to_bv 64 (0x10ab58 + 888)).          (* [comment removed for export] *)
      d7_tail.
      change (wbytes _ _ _) with (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3). rewrite ?at_0. wd_refl.
    - post.
  Qed.

End DRAIN.
End FPGen.
End BoAllocF7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits BoAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
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

Section DRAINRC.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v a2v a3v : word).
  Variables (T len first lastq qb glen glast gqb : Z) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Variable minsz : Z.                    (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x10ab58 + 728).
  Hypothesis H11 : getr regs 11 = at_ (Z_to_bv 64 T) 80.
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hlen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Hqb : (0 <= qb < 2 ^ 40)%Z.
  Hypothesis Hglen : (0 <= glen < 2 ^ 40)%Z.
  Hypothesis Hgqb : (0 <= gqb < 2 ^ 40)%Z.
  Hypothesis Hfirst : (0 <= first < 2 ^ 64)%Z.
  Hypothesis Hlastq : (0 <= lastq < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2256)) 48 = true.     (* [comment removed for export] *)
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 (T + 80)) 32 = true.
  (* [comment removed for export] *)
  Hypothesis Rlen : rdn BSEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis Rfirst : rdn BSEGS mem (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 first)).
  Hypothesis Rlastq : rdn BSEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 lastq)).
  Hypothesis Rqb : rdn BSEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis Rglen : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).
  Hypothesis Rgqb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).
  Hypothesis Rmax : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis Rlock : rdn BSEGS mem (Z_to_bv 64 0x10aec8) 4 = Some [Z_to_bv 8 0; b1; b2; b3].


  (* [comment removed for export] *)
  Ltac d7_prefix HV :=
      an F_4e260 D_4e260;                              (* [comment removed for export] *)
      fsd F_4e264 D_4e264 (at_ S (-2216));             (* [comment removed for export] *)
      fsd F_4e268 D_4e268 (at_ S (-2224));             (* [comment removed for export] *)
      fsd F_4e26c D_4e26c (at_ S (-2232));             (* [comment removed for export] *)
      fsd F_4e270 D_4e270 (at_ S (-2240));             (* [comment removed for export] *)
      fsd F_4e274 D_4e274 (at_ S (-2248));             (* [comment removed for export] *)
      an F_4e278 D_4e278;                              (* [comment removed for export] *)
      an F_4e27c D_4e27c;                              (* [comment removed for export] *)
      an F_4e280 D_4e280;                              (* [comment removed for export] *)
      an F_4e284 D_4e284;                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (drain_lock_69b04 _ _ rom _ (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]
      | ];
      av F_4e2a4 D_4e2a4 (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity);   (* [comment removed for export] *)
      ab_ft F_4e2a8 D_4e2a8 ltac:(condz);              (* [comment removed for export] *)
      an F_4e2ac D_4e2ac;                              (* [comment removed for export] *)
      ab_ft F_4e2b0 D_4e2b0 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4e2b4 D_4e2b4 (Z_to_bv 64 len) Rlen;      (* [comment removed for export] *)
      ab_ft F_4e2b8 D_4e2b8 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4e2bc D_4e2bc (Z_to_bv 64 glen) Rglen.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac d7_tail_rc RL2 HV2 minsz Rmin :=
      fsd F_4e2fc D_4e2fc (Z_to_bv 64 (T + 80));       (* [comment removed for export] *)
      fsd F_4e300 D_4e300 (Z_to_bv 64 (T + 88));       (* [comment removed for export] *)
      fsd F_4e304 D_4e304 (Z_to_bv 64 (T + 96));       (* [comment removed for export] *)
      cld8 F_4e308 D_4e308 (Z_to_bv 64 qb) Rqb;        (* [comment removed for export] *)
      cld8 F_4e30c D_4e30c (Z_to_bv 64 gqb) Rgqb;      (* [comment removed for export] *)
      av F_4e310 D_4e310 (Z_to_bv 64 (gqb + qb)) ltac:(valz);   (* [comment removed for export] *)
      fsd F_4e314 D_4e314 (Z_to_bv 64 (0x10ab58 + 912));        (* [comment removed for export] *)
      fsd F_4e318 D_4e318 (Z_to_bv 64 (T + 104));      (* [comment removed for export] *)
      afence F_4e31c D_4e31c;                          (* [comment removed for export] *)
      fsb F_4e320 D_4e320 (Z_to_bv 64 0x10aec8) (Z_to_bv 8 0);  (* [comment removed for export] *)
      fldx F_4e324 D_4e324 (Z_to_bv 64 (gqb + qb));    (* [comment removed for export] *)
      cld8 F_4e328 D_4e328 (Z_to_bv 64 (2 ^ 28)) Rmax; (* [comment removed for export] *)
      ab_ft F_4e32c D_4e32c ltac:(condz);              (* [comment removed for export] *)
      an F_4e330 D_4e330;                              (* [comment removed for export] *)
      an F_4e334 D_4e334;                              (* [comment removed for export] *)
      an F_4e338 D_4e338;                              (* [comment removed for export] *)
      av F_4e33c D_4e33c (Z_to_bv 64 0x10aec8) ltac:(valz);   (* [comment removed for export] *)
      av F_4e340 D_4e340 (Z_to_bv 64 1) ltac:(valz);          (* [comment removed for export] *)
      av F_4e344 D_4e344 (Z_to_bv 64 8) ltac:(valz);          (* [comment removed for export] *)
      an F_4e348 D_4e348;                              (* [comment removed for export] *)
      an F_4e34c D_4e34c;                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (drain_trylock_4e350 _ _ rom _ (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
          | exact RL2
          | exact HV2 ]
      | ];
      an F_4e36c D_4e36c;                              (* [comment removed for export] *)
      av F_4e370 D_4e370 (Z_to_bv 64 (bv_unsigned b1)) ltac:(first [apply (lock_byte1 (Z_to_bv 8 0) b1 b2 b3 _ HV2) | rewrite <- (lock_byte1 (Z_to_bv 8 0) b1 b2 b3 _ HV2); reflexivity]);  (* [comment removed for export] *)
      ab_tk F_4e374 D_4e374 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4e394 D_4e394 (Z_to_bv 64 minsz) Rmin;   (* [comment removed for export] *)
      fld F_4e398 D_4e398 ra0;                         (* [comment removed for export] *)
      fld F_4e39c D_4e39c s0v;                         (* [comment removed for export] *)
      fld F_4e3a0 D_4e3a0 s1v;                         (* [comment removed for export] *)
      fld F_4e3a4 D_4e3a4 s2v;                         (* [comment removed for export] *)
      fld F_4e3a8 D_4e3a8 s3v;                         (* [comment removed for export] *)
      an F_4e3ac D_4e3ac;                              (* [comment removed for export] *)
      an F_4e3b0 D_4e3b0.                              (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Definition rc_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = ra0 /\ getr r 2 = at_ S (-2208) /\ getr r 10 = Z_to_bv 64 (0x10ab58 + 728) /\ getr r 11 = Z_to_bv 64 minsz
      /\ getr r 12 = a2v /\ getr r 13 = a3v
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  (* [comment removed for export] *)
  Lemma lockword_d7n : (2 ^ 44 <= glast /\ glast + 8192 <= bv_unsigned S - 3584)%Z ->
    rdn BSEGS (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3) (Z_to_bv 64 0x10aec8) 4
      = Some [Z_to_bv 8 0; b1; b2; b3].
  Proof using HT HS.
    intros Hglast. pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    change [Z_to_bv 8 0; b1; b2; b3] with ([Z_to_bv 8 0] ++ [b1; b2; b3]). change 4%nat with (1 + 3)%nat.
    apply rdn_cat; [| | wd_ulia].
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). apply rdn1_top. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). unorm. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_d7n in G in change_no_check G' end). rewrite rdn_wbytes_out; [| rd8_side | rd8_side | rd8_side].
      repeat (rewrite rdn_wbytes_out; [| rd8_side | rd8_side | rd8_side]).
      replace (at_ (Z_to_bv 64 0x10aec8) (Z.of_nat 1) : word) with (at_ (Z_to_bv 64 0x10aec8 : word) (Z.of_nat 1)) by reflexivity.
      rewrite (rdn_wbytes_sub BSEGS _ (Z_to_bv 64 0x10aec8) [Z_to_bv 8 1; b1; b2; b3] 1 3); [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | wd_ulia_c].
  Qed.

  Lemma lockword_d7e :
    rdn BSEGS (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3) (Z_to_bv 64 0x10aec8) 4
      = Some [Z_to_bv 8 0; b1; b2; b3].
  Proof using HT HS.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    change [Z_to_bv 8 0; b1; b2; b3] with ([Z_to_bv 8 0] ++ [b1; b2; b3]). change 4%nat with (1 + 3)%nat.
    apply rdn_cat; [| | wd_ulia].
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). apply rdn1_top. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). unorm. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_d7e in G in change_no_check G' end). repeat (rewrite rdn_wbytes_out; [| rd8_side | rd8_side | rd8_side]).
      replace (at_ (Z_to_bv 64 0x10aec8) (Z.of_nat 1) : word) with (at_ (Z_to_bv 64 0x10aec8 : word) (Z.of_nat 1)) by reflexivity.
      rewrite (rdn_wbytes_sub BSEGS _ (Z_to_bv 64 0x10aec8) [Z_to_bv 8 1; b1; b2; b3] 1 3); [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | wd_ulia_c].
  Qed.

  (* [comment removed for export] *)
  Lemma drain_rc_n :
    (1 <= glen)%Z -> (2 ^ 28 < gqb + qb)%Z ->
    (2 ^ 44 <= glast /\ glast + 8192 <= bv_unsigned S - 3584)%Z -> (glast + 8192 <= T \/ T + 4096 <= glast)%Z ->
    store_ok BSEGS mem (Z_to_bv 64 glast) 8 = true ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 904)) 8 = Some (LE8 (Z_to_bv 64 glast)) ->
    bv_unsigned b1 = 0%Z ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 800)) 8 = Some (LE8 (Z_to_bv 64 minsz)) ->
    exists r,
      msteps BSEGS (mkst regs (0x4e260 : word) mem rom)
                   (mkst r (0x4e404 : word)
                         (wbytes (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3)
                                 (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]) rom)
      /\ rc_regs r.
  Proof using Rlock Rmax Rgqb Rglen Rqb Rlastq Rfirst Rlen HokT Hstk Hgqb Hglen Hqb Hlen HT HS H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    intros Hglen1 Hsum Hglast HglastT Hokgl Rglast Hb1 Rmin. (lazymatch goal with |- ?G => let G' := eval unfold rc_regs in G in change_no_check G' end).
    pose proof (lockword_d7n Hglast) as RL2.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    pose proof (sok_lockword mem) as Hoklk. pose proof (sok_glist mem) as Hokgq.
    assert (HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]))).
    { pose proof (lez4_range [Z_to_bv 8 0; b1; b2; b3] eq_refl) as B. rewrite u_Z2bv by lia. reflexivity. }
    wd_eexists. split.
    - d7_prefix HV.
      ab_ft F_4e2c0 D_4e2c0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e2c4 D_4e2c4 (Z_to_bv 64 glast) Rglast.  (* [comment removed for export] *)
      cld8 F_4e2c8 D_4e2c8 (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      cld8 F_4e2cc D_4e2cc (Z_to_bv 64 lastq) Rlastq.  (* [comment removed for export] *)
      av F_4e2d0 D_4e2d0 (Z_to_bv 64 (glen + len)) ltac:(valz).   (* [comment removed for export] *)
      fsd F_4e2d4 D_4e2d4 (Z_to_bv 64 glast);          (* [comment removed for export] *)
      fsd F_4e2d8 D_4e2d8 (Z_to_bv 64 (0x10ab58 + 888)).          (* [comment removed for export] *)
      fsd F_4e2dc D_4e2dc (Z_to_bv 64 (0x10ab58 + 904)).          (* [comment removed for export] *)
      an F_4e2e0 D_4e2e0.                              (* [comment removed for export] *)
      d7_tail_rc RL2 HV minsz Rmin.
      change (wbytes (wbytes _ _ _) (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])
        with (wbytes (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3) (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]).
      rewrite ?at_0. wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma drain_rc_e :
    glen = 0%Z -> (2 ^ 28 < gqb + qb)%Z ->
    bv_unsigned b1 = 0%Z ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 800)) 8 = Some (LE8 (Z_to_bv 64 minsz)) ->
    exists r,
      msteps BSEGS (mkst regs (0x4e260 : word) mem rom)
                   (mkst r (0x4e404 : word)
                         (wbytes (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3)
                                 (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]) rom)
      /\ rc_regs r.
  Proof using Rlock Rmax Rgqb Rglen Rqb Rlastq Rfirst Rlen HokT Hstk Hgqb Hglen Hqb Hlen HT HS H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    intros Hglen0 Hsum Hb1 Rmin. (lazymatch goal with |- ?G => let G' := eval unfold rc_regs in G in change_no_check G' end).
    pose proof lockword_d7e as RL2.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2). unfold hideW in HT2. unfold hideW in HT2.
    pose proof (sok_lockword mem) as Hoklk. pose proof (sok_glist mem) as Hokgq.
    assert (HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3]))).
    { pose proof (lez4_range [Z_to_bv 8 0; b1; b2; b3] eq_refl) as B. rewrite u_Z2bv by lia. reflexivity. }
    wd_eexists. split.
    - d7_prefix HV.
      subst glen.
      ab_tk F_4e2c0 D_4e2c0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e2e4 D_4e2e4 (Z_to_bv 64 lastq) Rlastq.  (* [comment removed for export] *)
      fsd F_4e2e8 D_4e2e8 (Z_to_bv 64 (0x10ab58 + 904)).          (* [comment removed for export] *)
      cld8 F_4e2ec D_4e2ec (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      fsd F_4e2f0 D_4e2f0 (Z_to_bv 64 (0x10ab58 + 896)).          (* [comment removed for export] *)
      cld8 F_4e2f4 D_4e2f4 (Z_to_bv 64 len) Rlen.      (* [comment removed for export] *)
      fsd F_4e2f8 D_4e2f8 (Z_to_bv 64 (0x10ab58 + 888)).          (* [comment removed for export] *)
      d7_tail_rc RL2 HV minsz Rmin.
      change (wbytes (wbytes _ _ _) (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3])
        with (wbytes (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3) (Z_to_bv 64 0x10aec8) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3]).
      rewrite ?at_0. wd_refl.
    - post.
  Qed.
End DRAINRC.
End FPGen.

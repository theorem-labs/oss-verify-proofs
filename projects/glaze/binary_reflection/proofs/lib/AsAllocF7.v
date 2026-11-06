(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
(* [comment removed for export] *)

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma sok_lockword : forall m, store_ok ASEGS m (Z_to_bv 64 0x104288) 4 = true.
Proof using. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sok_glist : forall m, store_ok ASEGS m (Z_to_bv 64 0x104290) 32 = true.
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
Lemma drain_lock_6908c : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 16 = Z_to_bv 64 0x104288 -> getr regs 15 = Z_to_bv 64 255 -> getr regs 17 = Z_to_bv 64 1 ->
  rdn ASEGS mem (Z_to_bv 64 0x104288) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps ASEGS (mkst regs (0x4d818 : word) mem rom)
    (mkst (regupd (regupd regs 5 (v_lw v)) 6 (Z_to_bv 64 0)) (0x4d834 : word)
          (wbytes mem (Z_to_bv 64 0x104288) [Z_to_bv 8 1; b1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H16 H15 H17 Hrd Hv.
  pose proof (xchg_byte_run ASEGS regs (0x4d818 : word) (0x4d81c : word) (0x4d820 : word) (0x4d824 : word)
                (0x4d828 : word) (0x4d82c : word) (0x4d830 : word) (0x4d834 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 5 16 6 17 15 _ [b0; b1; b2; b3] v 0%nat 1%Z
                F_4d810 eq_refl D_4d810 F_4d814 eq_refl D_4d814 F_4d818 eq_refl D_4d818 F_4d81c eq_refl D_4d81c
                F_4d820 eq_refl D_4d820 F_4d824 eq_refl D_4d824 F_4d828 eq_refl D_4d828) as R.
  rewrite H16, H15, H17 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_lockword | unorm; reflexivity | lia | assumption].
Qed.


(* [comment removed for export] *)
Lemma drain_trylock_4d8d8 : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 16 = Z_to_bv 64 0x104288 -> getr regs 14 = Z_to_bv 64 0xff00 -> getr regs 15 = Z_to_bv 64 0x100 ->
  rdn ASEGS mem (Z_to_bv 64 0x104288) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps ASEGS (mkst regs (0x4d8e0 : word) mem rom)
    (mkst (regupd (regupd regs 17 (v_lw v)) 5 (Z_to_bv 64 0)) (0x4d8fc : word)
          (wbytes mem (Z_to_bv 64 0x104288) [b0; Z_to_bv 8 1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H16 H14 H15 Hrd Hv.
  pose proof (xchg_byte_run ASEGS regs (0x4d8e0 : word) (0x4d8e4 : word) (0x4d8e8 : word) (0x4d8ec : word)
                (0x4d8f0 : word) (0x4d8f4 : word) (0x4d8f8 : word) (0x4d8fc : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 17 16 5 15 14 _ [b0; b1; b2; b3] v 1%nat 1%Z
                F_4d8d8 eq_refl D_4d8d8 F_4d8dc eq_refl D_4d8dc F_4d8e0 eq_refl D_4d8e0 F_4d8e4 eq_refl D_4d8e4
                F_4d8e8 eq_refl D_4d8e8 F_4d8ec eq_refl D_4d8ec F_4d8f0 eq_refl D_4d8f0) as R.
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
    (Z_to_bv 64 0x104288) [Z_to_bv 8 1; b1; b2; b3])
    (Z_to_bv 64 glast) (LE8 (Z_to_bv 64 first)))
    (Z_to_bv 64 (0x103f18 + 888)) (LE8 (Z_to_bv 64 (glen + len))))
    (Z_to_bv 64 (0x103f18 + 904)) (LE8 (Z_to_bv 64 lastq)))
    (Z_to_bv 64 (T + 80)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (T + 88)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (T + 96)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (0x103f18 + 912)) (LE8 (Z_to_bv 64 (gqb + qb))))
    (Z_to_bv 64 (T + 104)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x104288) [Z_to_bv 8 0].
(* [comment removed for export] *)
Definition fr_d7e (mem : word -> option byte) (S ra0 : word) (s0v s1v s2v s3v : word) (T len first lastq qb gqb : Z) (b1 b2 b3 : byte)
  : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (LE8 ra0))
    (at_ S (-2224)) (LE8 s0v))
    (at_ S (-2232)) (LE8 s1v))
    (at_ S (-2240)) (LE8 s2v))
    (at_ S (-2248)) (LE8 s3v))
    (Z_to_bv 64 0x104288) [Z_to_bv 8 1; b1; b2; b3])
    (Z_to_bv 64 (0x103f18 + 904)) (LE8 (Z_to_bv 64 lastq)))
    (Z_to_bv 64 (0x103f18 + 896)) (LE8 (Z_to_bv 64 first)))
    (Z_to_bv 64 (0x103f18 + 888)) (LE8 (Z_to_bv 64 len)))
    (Z_to_bv 64 (T + 80)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (T + 88)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (T + 96)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (0x103f18 + 912)) (LE8 (Z_to_bv 64 (gqb + qb))))
    (Z_to_bv 64 (T + 104)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x104288) [Z_to_bv 8 0].
Hint Unfold fr_d7n fr_d7e : asfr.

Section DRAIN.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v a2v a3v : word).
  Variables (T len first lastq qb glen glast gqb : Z) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x103f18 + 728).
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
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2256)) 48 = true.     (* [comment removed for export] *)
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 (T + 80)) 32 = true.
  (* [comment removed for export] *)
  Hypothesis Rlen : rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis Rfirst : rdn ASEGS mem (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 first)).
  Hypothesis Rlastq : rdn ASEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 lastq)).
  Hypothesis Rqb : rdn ASEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis Rglen : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 888)) 8 = Some (LE8 (Z_to_bv 64 glen)).
  Hypothesis Rgqb : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 912)) 8 = Some (LE8 (Z_to_bv 64 gqb)).
  Hypothesis Rmax : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis Rlock : rdn ASEGS mem (Z_to_bv 64 0x104288) 4 = Some [Z_to_bv 8 0; b1; b2; b3].

  (* [comment removed for export] *)
  #[local] Definition ret_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2208) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  (* [comment removed for export] *)
  Ltac d7_prefix HV :=
      an F_4d7e8 D_4d7e8;                              (* [comment removed for export] *)
      fsd F_4d7ec D_4d7ec (at_ S (-2216));             (* [comment removed for export] *)
      fsd F_4d7f0 D_4d7f0 (at_ S (-2224));             (* [comment removed for export] *)
      fsd F_4d7f4 D_4d7f4 (at_ S (-2232));             (* [comment removed for export] *)
      fsd F_4d7f8 D_4d7f8 (at_ S (-2240));             (* [comment removed for export] *)
      fsd F_4d7fc D_4d7fc (at_ S (-2248));             (* [comment removed for export] *)
      an F_4d800 D_4d800;                              (* [comment removed for export] *)
      an F_4d804 D_4d804;                              (* [comment removed for export] *)
      an F_4d808 D_4d808;                              (* [comment removed for export] *)
      an F_4d80c D_4d80c;                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (drain_lock_6908c _ _ rom _ (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]
      | ];
      av F_4d82c D_4d82c (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity);   (* [comment removed for export] *)
      ab_ft F_4d830 D_4d830 ltac:(condz);              (* [comment removed for export] *)
      an F_4d834 D_4d834;                              (* [comment removed for export] *)
      ab_ft F_4d838 D_4d838 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4d83c D_4d83c (Z_to_bv 64 len) Rlen;      (* [comment removed for export] *)
      ab_ft F_4d840 D_4d840 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4d844 D_4d844 (Z_to_bv 64 glen) Rglen.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac d7_tail :=
      fsd F_4d884 D_4d884 (Z_to_bv 64 (T + 80));       (* [comment removed for export] *)
      fsd F_4d888 D_4d888 (Z_to_bv 64 (T + 88));       (* [comment removed for export] *)
      fsd F_4d88c D_4d88c (Z_to_bv 64 (T + 96));       (* [comment removed for export] *)
      cld8 F_4d890 D_4d890 (Z_to_bv 64 qb) Rqb;        (* [comment removed for export] *)
      cld8 F_4d894 D_4d894 (Z_to_bv 64 gqb) Rgqb;      (* [comment removed for export] *)
      av F_4d898 D_4d898 (Z_to_bv 64 (gqb + qb)) ltac:(valz);   (* [comment removed for export] *)
      fsd F_4d89c D_4d89c (Z_to_bv 64 (0x103f18 + 912));        (* [comment removed for export] *)
      fsd F_4d8a0 D_4d8a0 (Z_to_bv 64 (T + 104));      (* [comment removed for export] *)
      afence F_4d8a4 D_4d8a4;                          (* [comment removed for export] *)
      fsb F_4d8a8 D_4d8a8 (Z_to_bv 64 0x104288) (Z_to_bv 8 0);  (* [comment removed for export] *)
      fldx F_4d8ac D_4d8ac (Z_to_bv 64 (gqb + qb));    (* [comment removed for export] *)
      cld8 F_4d8b0 D_4d8b0 (Z_to_bv 64 (2 ^ 28)) Rmax; (* [comment removed for export] *)
      ab_tk F_4d8b4 D_4d8b4 ltac:(condz);              (* [comment removed for export] *)
      fld F_4d900 D_4d900 ra0;                         (* [comment removed for export] *)
      fld F_4d904 D_4d904 s0v;                         (* [comment removed for export] *)
      fld F_4d908 D_4d908 s1v;                         (* [comment removed for export] *)
      fld F_4d90c D_4d90c s2v;                         (* [comment removed for export] *)
      fld F_4d910 D_4d910 s3v;                         (* [comment removed for export] *)
      an F_4d914 D_4d914;                              (* [comment removed for export] *)
      aret F_4d918 D_4d918 ra0.                        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma drain_nr_n :
    (1 <= glen)%Z -> (gqb + qb <= 2 ^ 28)%Z ->
    (2 ^ 44 <= glast /\ glast + 8192 <= bv_unsigned S - 3584)%Z -> (glast + 8192 <= T \/ T + 4096 <= glast)%Z ->
    store_ok ASEGS mem (Z_to_bv 64 glast) 8 = true ->
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 904)) 8 = Some (LE8 (Z_to_bv 64 glast)) ->
    exists r,
      msteps ASEGS (mkst regs (0x4d7f0 : word) mem rom)
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
      ab_ft F_4d848 D_4d848 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4d84c D_4d84c (Z_to_bv 64 glast) Rglast.  (* [comment removed for export] *)
      cld8 F_4d850 D_4d850 (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      cld8 F_4d854 D_4d854 (Z_to_bv 64 lastq) Rlastq.  (* [comment removed for export] *)
      av F_4d858 D_4d858 (Z_to_bv 64 (glen + len)) ltac:(valz).   (* [comment removed for export] *)
      fsd F_4d85c D_4d85c (Z_to_bv 64 glast);          (* [comment removed for export] *)
      fsd F_4d860 D_4d860 (Z_to_bv 64 (0x103f18 + 888)).          (* [comment removed for export] *)
      fsd F_4d864 D_4d864 (Z_to_bv 64 (0x103f18 + 904)).          (* [comment removed for export] *)
      an F_4d868 D_4d868.                              (* [comment removed for export] *)
      d7_tail.
      change (wbytes _ _ _) with (fr_d7n mem S ra0 s0v s1v s2v s3v T len first lastq qb glen glast gqb b1 b2 b3). rewrite ?at_0. wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma drain_nr_e :
    glen = 0%Z -> (gqb + qb <= 2 ^ 28)%Z ->
    exists r,
      msteps ASEGS (mkst regs (0x4d7f0 : word) mem rom)
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
      ab_tk F_4d848 D_4d848 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4d86c D_4d86c (Z_to_bv 64 lastq) Rlastq.  (* [comment removed for export] *)
      fsd F_4d870 D_4d870 (Z_to_bv 64 (0x103f18 + 904)).          (* [comment removed for export] *)
      cld8 F_4d874 D_4d874 (Z_to_bv 64 first) Rfirst.  (* [comment removed for export] *)
      fsd F_4d878 D_4d878 (Z_to_bv 64 (0x103f18 + 896)).          (* [comment removed for export] *)
      cld8 F_4d87c D_4d87c (Z_to_bv 64 len) Rlen.      (* [comment removed for export] *)
      fsd F_4d880 D_4d880 (Z_to_bv 64 (0x103f18 + 888)).          (* [comment removed for export] *)
      d7_tail.
      change (wbytes _ _ _) with (fr_d7e mem S ra0 s0v s1v s2v s3v T len first lastq qb gqb b1 b2 b3). rewrite ?at_0. wd_refl.
    - post.
  Qed.

End DRAIN.
End FPGen.

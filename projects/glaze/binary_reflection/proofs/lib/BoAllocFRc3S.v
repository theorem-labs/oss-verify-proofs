(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc3b.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c.
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

(* [comment removed for export] *)
Lemma cas_state_4e9cc : forall regs mem rom (m hv : word) h1 h2 h3,
  getr regs 12 = m -> getr regs 14 = Z_to_bv 64 255 -> getr regs 13 = Z_to_bv 64 3 ->
  (bv_unsigned m mod 4 = 0)%Z ->
  rdn BSEGS mem m 4 = Some [Z_to_bv 8 3; h1; h2; h3] -> bytes_le_to_Z [Z_to_bv 8 3; h1; h2; h3] = bv_unsigned hv ->
  store_ok BSEGS mem m 4 = true ->
  msteps BSEGS (mkst regs (0x4e9cc : word) mem rom)
    (mkst (regupd (regupd regs 11 (v_lw hv)) 15 (Z_to_bv 64 0)) (0x4e9ec : word) (wbytes mem m [Z_to_bv 8 0; h1; h2; h3]) rom).
Proof using.
  intros regs mem rom m hv h1 h2 h3 H12 H14 H13 Hal Hrd Hv Hok.
  pose proof (cas_byte_run BSEGS regs (0x4e9cc : word) (0x4e9d0 : word) (0x4e9d4 : word) (0x4e9d8 : word)
                (0x4e9dc : word) (0x4e9e0 : word) (0x4e9e4 : word) (0x4e9e8 : word) (0x4e9ec : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ _ 11 12 15 0 14 13 _ _ [Z_to_bv 8 3; h1; h2; h3] hv 0%nat 0%Z
                F_4e9cc eq_refl D_4e9cc F_4e9d0 eq_refl D_4e9d0 F_4e9d4 eq_refl D_4e9d4 F_4e9d8 eq_refl D_4e9d8
                F_4e9dc eq_refl D_4e9dc F_4e9e0 eq_refl D_4e9e0 F_4e9e4 eq_refl D_4e9e4 F_4e9e8 eq_refl D_4e9e8) as R.
  rewrite H12, H14, H13 in R. cbn [firstn skipn app nth] in R.
  apply R; clear R; try (apply reg_neq_of_eqb; reflexivity); try (apply bv_eq; reflexivity); try lia; try assumption.
  all: unorm; reflexivity.
Qed.

Section K2A.
  Variables (mem rom : word -> option byte) (m : Z) (h1 h2 h3 : byte) (hv : word).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 m.
  Hypothesis Hm : (0 <= m < 2 ^ 47 /\ m mod 16 = 0)%Z.
  Hypothesis Rhdr : rdn BSEGS mem (Z_to_bv 64 m) 4 = Some [Z_to_bv 8 3; h1; h2; h3].
  Hypothesis Hhv : bytes_le_to_Z [Z_to_bv 8 3; h1; h2; h3] = bv_unsigned hv.
  Hypothesis Hokh : store_ok BSEGS mem (Z_to_bv 64 m) 4 = true.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma m_mods : (m mod 4 = 0 /\ (8 * m) mod 32 = 0)%Z.
  Proof using Hm hv rom. destruct Hm as (_ & M16). split; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma k2a_run :
    exists r, msteps BSEGS (mkst regs (0x4e9b4 : word) mem rom)
                           (mkst r (0x4e9ec : word) (wbytes mem (Z_to_bv 64 m) [Z_to_bv 8 0; h1; h2; h3]) rom)
      /\ getr r 1 = getr regs 1 /\ getr r 2 = getr regs 2 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hokh Hhv Rhdr Hm H9 hv.
    destruct m_mods as (M4 & M32). destruct Hm as (Hm1 & _).
    assert (Hm4 : (bv_unsigned (Z_to_bv 64 m) mod 4 = 0)%Z) by (unorm; exact M4).
    wd_eexists. split.
    - av F_4e9b4 D_4e9b4 (Z_to_bv 64 m) ltac:(apply v_andi_m4_aligned; exact Hm4).   (* [comment removed for export] *)
      av F_4e9b8 D_4e9b8 (Z_to_bv 64 (8 * m)) ltac:(valz).                          (* [comment removed for export] *)
      an F_4e9bc D_4e9bc.                              (* [comment removed for export] *)
      an F_4e9c0 D_4e9c0.                              (* [comment removed for export] *)
      an F_4e9c4 D_4e9c4.                              (* [comment removed for export] *)
      rewrite (v_sllw_mult32 255) by (first [lia | unorm; exact M32]).
      an F_4e9c8 D_4e9c8.                              (* [comment removed for export] *)
      rewrite (v_sllw_mult32 3) by (first [lia | unorm; exact M32]).
      eapply msteps_trans.
      { eapply (cas_state_4e9cc _ mem rom (Z_to_bv 64 m) hv h1 h2 h3);
          [gres; reflexivity | gres; reflexivity | gres; reflexivity | exact Hm4 | exact Rhdr | exact Hhv | exact Hokh]. }
      wd_refl.
    - post.
  Qed.
End K2A.

Section K2B.
  Variables (mem rom : word -> option byte) (m n : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 m.
  Hypothesis Hm : (0 <= m /\ m + 16 < 2 ^ 47)%Z.
  Hypothesis Hn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis Rnhi : rdn BSEGS mem (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis Rnlo : rdn BSEGS mem (Z_to_bv 64 (m + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma n_split2 : (0 <= n / 2 ^ 32 <= 2 ^ 8 /\ 0 <= n mod 2 ^ 32 < 2 ^ 32 /\ n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n)%Z.
  Proof using Hn. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). repeat split; lia. Qed.
  Lemma up8_andi : v_andi (Z_to_bv 64 (n + 7)) (-8) = Z_to_bv 64 (AsRtRegion.down8 (n + 7)).
  Proof using Hn. rewrite AsRtIcpyS.v_andi_m8. rewrite u_Z2bv by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma k2b_run :
    exists r, msteps BSEGS (mkst regs (0x4e9ec : word) mem rom) (mkst r (0x70080 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x4ea10 /\ getr r 10 = Z_to_bv 64 (m + 16) /\ getr r 11 = Z_to_bv 64 (AsRtRegion.down8 (n + 7)) /\ getr r 12 = Z_to_bv 64 250
      /\ getr r 2 = getr regs 2 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rnlo Rnhi Hn Hm H9.
    destruct n_split2 as (Nh & Nl & Nsum).
    assert (Vh : bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n / 2 ^ 32))).
    { rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2))%Z with (2 ^ 16)%Z. unorm. apply Z.mod_small. lia. }
    assert (Vl : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n mod 2 ^ 32))) by (apply bytes4_small; lia).
    wd_eexists. split.
    - clhu F_4e9ec D_4e9ec (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh.      (* [comment removed for export] *)
      clwu F_4e9f0 D_4e9f0 (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl.  (* [comment removed for export] *)
      av F_4e9f4 D_4e9f4 (Z_to_bv 64 (m + 16)) ltac:(valz).      (* [comment removed for export] *)
      av F_4e9f8 D_4e9f8 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      an F_4e9fc D_4e9fc.                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia).
      av F_4ea00 D_4ea00 (Z_to_bv 64 (n + 7)) ltac:(valz).       (* [comment removed for export] *)
      av F_4ea04 D_4ea04 (Z_to_bv 64 (AsRtRegion.down8 (n + 7))) ltac:(apply up8_andi).   (* [comment removed for export] *)
      an F_4ea08 D_4ea08.                              (* [comment removed for export] *)
      an F_4ea0c D_4ea0c.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End K2B.

(* [comment removed for export] *)
Definition fr_k3 (mem : word -> option byte) (S : word) : word -> option byte :=
  wbytes mem (at_ S (-2456)) (LE8 (Z_to_bv 64 0x4ea14)).
#[local] Hint Unfold fr_k3 : asfr.

Section K3.
  Variables (mem rom : word -> option byte) (S : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2448).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2464)) 16 = true.

  Lemma k3_run :
    exists r, msteps BSEGS (mkst regs (0x4ea10 : word) mem rom) (mkst r (0x78e2c : word) (fr_k3 mem S) rom)
      /\ getr r 1 = Z_to_bv 64 0x78004 /\ getr r 2 = at_ S (-2464)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk HS H2.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4ea10 D_4ea10.                              (* [comment removed for export] *)
      an F_77ff8 D_77ff8.                              (* [comment removed for export] *)
      fsd F_77ffc D_77ffc (at_ S (-2456)).             (* [comment removed for export] *)
      an F_78000 D_78000.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_k3 mem S). wd_refl.
    - post.
  Qed.
End K3.

(* [comment removed for export] *)
Definition fr_k4 (mem : word -> option byte) (T : Z) (j0 j1 : word) : word -> option byte :=
  wbytes (wbytes mem (Z_to_bv 64 (T + 2840)) (LE8 j0)) (Z_to_bv 64 (T + 2848)) (LE8 j1).
#[local] Hint Unfold fr_k4 : asfr.

Section K4.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v cachev : word) (T m n spb c e : Z) (bf0 bf1 : list byte).
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation ab := (spb + c * 2 ^ 32 + e)%Z.
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2464).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 T.
  Hypothesis H8 : getr regs 8 = at_ S (-2392).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 m.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 ab.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 0x10ab58.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 (2 ^ 37).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hm : (AIMGHI <= m /\ m + 16 <= bv_unsigned S - 3584)%Z.
  Hypothesis HmT : (m + 16 <= T \/ T + 4096 <= m)%Z.
  Hypothesis Hn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hce : (1 <= c <= 30 /\ 0 <= e < 2 ^ 32)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Rra : rdn BSEGS mem (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ea14)).
  Hypothesis Rnhi : rdn BSEGS mem (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis Rnlo : rdn BSEGS mem (Z_to_bv 64 (m + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))).
  Hypothesis Rf0 : rdn BSEGS mem (Z_to_bv 64 (T + 2840)) 8 = Some bf0.
  Hypothesis Lf0 : length bf0 = 8%nat.
  Hypothesis Rf1 : rdn BSEGS mem (Z_to_bv 64 (T + 2848)) 8 = Some bf1.
  Hypothesis Lf1 : length bf1 = 8%nat.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 (T + 2840)) 16 = true.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis Rcache : rdn BSEGS mem (at_ S (-2392)) 8 = Some (LE8 cachev).
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2432)) 8 = Some (LE8 s2v).
  Hypothesis Cs3 : rdn BSEGS mem (at_ S (-2440)) 8 = Some (LE8 s3v).
  Hypothesis Cs4 : rdn BSEGS mem (at_ S (-2448)) 8 = Some (LE8 s4v).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma n_split4 : (0 <= n / 2 ^ 32 <= 2 ^ 8 /\ 0 <= n mod 2 ^ 32 < 2 ^ 32 /\ n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n)%Z.
  Proof using Lf1 Lf0 Hn bf1 bf0 cachev rom. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). repeat split; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma k4_run :
    exists r, msteps BSEGS (mkst regs (0x78004 : word) mem rom)
                           (mkst r (0x4eca8 : word) (fr_k4 mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) rom)
      /\ getr r 1 = ra0 /\ getr r 2 = at_ S (-2400)
      /\ getr r 10 = cachev /\ getr r 11 = Z_to_bv 64 0x10ab58 /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = Z_to_bv 64 ab
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Cs4 Cs3 Cs2 Cs1 Cs0 Cra Rcache Rspb HokT Lf1 Rf1 Lf0 Rf0 Rnlo Rnhi Rra Hce Hspb Hn Hm HT HS H20 H19 H18 H9 H8 H10 H2 m.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT3). unfold hideW in HT2. destruct Hce as (Hc & He).
    pose proof (bytes_le_to_Z_bound bf0) as Bf0. rewrite Lf0 in Bf0. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bf0.
    pose proof (bytes_le_to_Z_bound bf1) as Bf1. rewrite Lf1 in Bf1. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bf1.
    pose proof (bytes_le_to_Z_nonneg bf0) as Bf0'. pose proof (bytes_le_to_Z_nonneg bf1) as Bf1'.
    assert (Vf0 : bytes_le_to_Z bf0 = bv_unsigned f0) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vf1 : bytes_le_to_Z bf1 = bv_unsigned f1) by (rewrite u_Z2bv by lia; reflexivity).
    destruct n_split4 as (Nh & Nl & Nsum).
    assert (Vh : bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n / 2 ^ 32))).
    { rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2))%Z with (2 ^ 16)%Z. unorm. apply Z.mod_small. lia. }
    assert (Vl : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n mod 2 ^ 32))) by (apply bytes4_small; lia).
    wd_eexists. split.
    - ab_ft F_78004 D_78004 ltac:(condz).              (* [comment removed for export] *)
      an F_78008 D_78008.                              (* [comment removed for export] *)
      an F_7800c D_7800c.                              (* [comment removed for export] *)
      cld8 F_78010 D_78010 (Z_to_bv 64 0x4ea14) Rra.   (* [comment removed for export] *)
      an F_78014 D_78014.                              (* [comment removed for export] *)
      rt F_78018 D_78018.                              (* [comment removed for export] *)
      clhu F_4ea14 D_4ea14 (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh.      (* [comment removed for export] *)
      clwu F_4ea18 D_4ea18 (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl.  (* [comment removed for export] *)
      cld F_4ea1c D_4ea1c bf1 (Z_to_bv 64 (bytes_le_to_Z bf1)) Rf1 Vf1.   (* [comment removed for export] *)
      cld F_4ea20 D_4ea20 bf0 (Z_to_bv 64 (bytes_le_to_Z bf0)) Rf0 Vf0.   (* [comment removed for export] *)
      av F_4ea24 D_4ea24 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      an F_4ea28 D_4ea28.                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia).
      an F_4ea2c D_4ea2c.                              (* [comment removed for export] *)
      an F_4ea30 D_4ea30.                              (* [comment removed for export] *)
      fsd F_4ea34 D_4ea34 (Z_to_bv 64 (T + 2840)).     (* [comment removed for export] *)
      fsd F_4ea38 D_4ea38 (Z_to_bv 64 (T + 2848)).     (* [comment removed for export] *)
      ab_ft F_4ea3c D_4ea3c ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ea40 D_4ea40 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      ab_ft F_4ea44 D_4ea44 ltac:(condz).              (* [comment removed for export] *)
      av F_4ea48 D_4ea48 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
      ab_ft F_4ea4c D_4ea4c ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ea50 D_4ea50 cachev Rcache.              (* [comment removed for export] *)
      av F_4ea54 D_4ea54 (Z_to_bv 64 (c * 2 ^ 32 + e)) ltac:(valz).   (* [comment removed for export] *)
      an F_4ea58 D_4ea58.                              (* [comment removed for export] *)
      av F_4ea5c D_4ea5c (Z_to_bv 64 c) ltac:(apply (cls_of_off c e); lia).   (* [comment removed for export] *)
      an F_4ea60 D_4ea60.                              (* [comment removed for export] *)
      an F_4ea64 D_4ea64.                              (* [comment removed for export] *)
      an F_4ea68 D_4ea68.                              (* [comment removed for export] *)
      cld8 F_4ea6c D_4ea6c ra0 Cra.                    (* [comment removed for export] *)
      cld8 F_4ea70 D_4ea70 s0v Cs0. cld8 F_4ea74 D_4ea74 s1v Cs1. cld8 F_4ea78 D_4ea78 s2v Cs2.
      cld8 F_4ea7c D_4ea7c s3v Cs3. cld8 F_4ea80 D_4ea80 s4v Cs4.
      an F_4ea84 D_4ea84.                              (* [comment removed for export] *)
      an F_4ea88 D_4ea88.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_k4 mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)). wd_refl.
    - post.
  Qed.
End K4.
End FPGen.
End BoAllocFRc3b.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc3S4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRc3c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Lemma at0_litS4 : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof. intros c Hc. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. reflexivity. Qed.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_k34 (M2 : word -> option byte) (S x21 : word) (m ab n8 T : Z) (j0 j1 : word) : word -> option byte :=
  let M3 := wbytes (ps_frame M2 (at_ S (-2448)) (Z_to_bv 64 0x4ea10) (at_ S (-2392)) (Z_to_bv 64 m) (Z_to_bv 64 ab)
                             (Z_to_bv 64 0x10ab58) (Z_to_bv 64 (2 ^ 37)) x21)
                   (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (repeat (MemsetLibF.cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 n8)))) in
  let M4 := fr_k3 M3 S in
  let M5 := wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) in
  fr_k4 M5 T j0 j1.

Section RUNK34.
  Variables (M2 rom : word -> option byte) (r0 : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 tp tsdp : word) (m spb c e n n8 T tctx cnt mx : Z).
  Variables (cpm : byte) (midend : word) (bf0 bf1 bst bcs : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation ab := (spb + c * 2 ^ 32 + e)%Z.
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  #[local] Abbreviation shlo := (0x7fff8000 + (m + 16) / 8)%Z.
  (* [comment removed for export] *)
  Hypothesis H1 : getr r0 1 = Z_to_bv 64 0x4ea10.
  Hypothesis H2 : getr r0 2 = at_ S (-2448).
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 (m + 16).
  Hypothesis H11 : getr r0 11 = Z_to_bv 64 n8.
  Hypothesis H12 : getr r0 12 = Z_to_bv 64 250.
  Hypothesis H8 : getr r0 8 = at_ S (-2392).
  Hypothesis H9 : getr r0 9 = Z_to_bv 64 m.
  Hypothesis H18 : getr r0 18 = Z_to_bv 64 ab.
  Hypothesis H19 : getr r0 19 = Z_to_bv 64 0x10ab58.
  Hypothesis H20 : getr r0 20 = Z_to_bv 64 (2 ^ 37).
  Hypothesis H21 : getr r0 21 = x21.
  Hypothesis H4 : getr r0 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gspb : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Gce : (1 <= c <= 30 /\ 0 <= e < 2 ^ 32)%Z.
  Hypothesis Gm : (ab <= m /\ m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : ((n <= n8 <= n + 7) /\ n8 mod 8 = 0 /\ 8 <= n8)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis GmT : hideW (m + 16 + n8 <= T \/ T + 4096 <= m)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584)%Z.
  Hypothesis GctxT : hideW (tctx + 4096 <= T \/ T + 4096 <= tctx)%Z.
  Hypothesis Gctxm : hideW (tctx + 4096 <= m \/ m + 16 + n8 <= tctx)%Z.
  Hypothesis Gctxs : hideW (tctx + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= tctx)%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS M2 (at_ S (-2512)) 112 = true.
  Hypothesis Oksh : store_ok BSEGS M2 (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS M2 (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  (* [comment removed for export] *)
  Hypothesis C_gsh : rdn BSEGS M2 (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS M2 (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS M2 (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS M2 (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS M2 (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS M2 (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS M2 (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS M2 (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS M2 (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS M2 (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS M2 (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_kif : rdn BSEGS M2 (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS M2 (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS M2 (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS M2 tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS M2 (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_nhi : rdn BSEGS M2 (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS M2 (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_f0 : rdn BSEGS M2 (Z_to_bv 64 (T + 2840)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS M2 (Z_to_bv 64 (T + 2848)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_spb : rdn BSEGS M2 (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_cache : rdn BSEGS M2 (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + 208))).
  Hypothesis C_ra : rdn BSEGS M2 (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis C_s0 : rdn BSEGS M2 (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis C_s1 : rdn BSEGS M2 (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis C_s2 : rdn BSEGS M2 (at_ S (-2432)) 8 = Some (LE8 s2v).
  Hypothesis C_s3 : rdn BSEGS M2 (at_ S (-2440)) 8 = Some (LE8 s3v).
  Hypothesis C_s4 : rdn BSEGS M2 (at_ S (-2448)) 8 = Some (LE8 s4v).

  Definition k34_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = ra0 /\ getr r 2 = at_ S (-2400) /\ getr r 10 = Z_to_bv 64 (T + 208) /\ getr r 11 = Z_to_bv 64 0x10ab58
      /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = Z_to_bv 64 ab
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = x21 /\ getr r 3 = getr r0 3 /\ getr r 4 = tp
      /\ getr r 22 = getr r0 22 /\ getr r 23 = getr r0 23 /\ getr r 24 = getr r0 24
      /\ getr r 25 = getr r0 25 /\ getr r 26 = getr r0 26 /\ getr r 27 = getr r0 27.

  Theorem run_k34 :
    exists r, msteps BSEGS (mkst r0 (0x70080 : word) M2 rom)
                           (mkst r (0x4eca8 : word) (fr_k34 M2 S x21 m ab n8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) rom)
      /\ k34_regs r.
  Proof using C_s4 C_s3 C_s2 C_s1 C_s0 C_ra C_cache C_spb L_f1 C_f1 L_f0 C_f0 C_nlo C_nhi C_thr C_tctx C_tsdp C_key C_kif C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh OkT Oksh Hstk Gtsdp Gtp Gctxs Gctx GT Gn8 Gn Gm Gce Gspb GS H4 H21 H20 H19 H18 H9 H8 H12 H11 H10 H2 H1 midend cpm tctx tsdp.
    (lazymatch goal with |- ?G => let G' := eval unfold k34_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2). destruct Gce as (Hc & He). destruct Gm as (Gm1 & Gm3 & Gm16).
    destruct Gn8 as (N8b & N8c & N8d). destruct GT as (GT1 & (GTS & GT2) & GT16). destruct Gctx as (Gc1 & Gc2).
    destruct (p16_facts (m + 16) ltac:(clear - Gm16; Z.div_mod_to_equations; lia) ltac:(lia)) as (_ & _ & _ & Mp8 & _).
    destruct (shad_facts2 (m + 16) n8 ltac:(lia) ltac:(lia) ltac:(lia) N8d Mp8 N8c) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). hidehypW SH1.
    assert (SHB : (0x7fff8000 + 0x2001000 <= shlo /\ shlo + n8 / 8 <= 0x10007fff8000)%Z).
    { unfold hideW in SH1. clear - SH1 SH2 SH3 Gs1 Gm1 Hc He N8d. destruct SH1 as [X|X]; lia. }
    Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    Ltac xqh TS Q H := unfold hideW in TS; xq Q H.
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold poison_clob, gct_clob in G in change_no_check G' end); notin)); rch.
    (* [comment removed for export] *)
    assert (PH : poisonH BSEGS both_poison_tab M2 (Z_to_bv 64 (m + 16)) (Z_to_bv 64 n8) (Z_to_bv 64 250) (Z_to_bv 64 0x4ea10) (at_ S (-2448)) cpm midend 0).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm pt_base pt_mset both_poison_tab] in G in change_no_check G' end).
      - exact C_gsh. - exact C_sh. - exact C_gmb. - exact C_mb. - exact C_gme. - exact C_me. - exact C_ghe. - exact C_he.
      - exact C_grm. - exact C_rm.
      - vm_compute. discriminate.
      - apply ret_ok_even. reflexivity.
      - intros _. split; [exact C_cpm | exact C_cpm1].
      - intros Hz. exfalso. revert Hz. unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
        first [clear - GS | idtac]; (repeat constructor; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]).
      - unorm. exact Mp8.
      - unorm. exact N8c.
      - unorm. left. lia.
      - rewrite at_u by lia. lia.
      - eapply (store_ok_sub BSEGS M2 (at_ S (-2512)) _ 112); [rewrite at_u; lia | exact Hstk | rewrite !at_at, !at_u; lia | rewrite !at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. exact Oksh.
      - apply ret_ok_lit; [lia | reflexivity]. }
    destruct (both_poison_shadow M2 rom (Z_to_bv 64 (m + 16)) (Z_to_bv 64 n8) (Z_to_bv 64 250) (Z_to_bv 64 0x4ea10) (at_ S (-2448)) cpm midend 0 r0 PH H1 H2 H10 H11 H12)
      as (r1 & RUN1 & AGP).
    rewrite H8, H9, H18, H19, H20, H21 in RUN1.
    set (M3t := wbytes _ _ _) in RUN1.
    assert (GR3 : mem_grows M2 M3t) by ((lazymatch goal with |- ?G => let G' := eval unfold M3t, ps_frame in G in change_no_check G' end); grows_tac).
    assert (Q3 : forall x : word, ((U x < U S - 2504)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < shlo \/ shlo + n8 / 8 <= U x)%Z -> M3t x = M2 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M3t, ps_frame in G in change_no_check G' end). rewrite !at_at. intros x Hx Hx2.
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by (first [clear - GS | idtac]; lia); try (first [clear - GS Hx | idtac]; lia).
      1: reflexivity.
      all: (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); unorm; rewrite ?Z2Nat.id by (first [clear - Gn8 | idtac]; lia); (first [clear - SH2 Hx2 | idtac]; lia). }
    remember M3t as M3 eqn:EM3 in RUN1, GR3, Q3. subst M3t.
    assert (V2 : getr r1 2 = at_ S (-2448)) by viac AGP (2:reg).
    assert (V8 : getr r1 8 = at_ S (-2392)) by viac AGP (8:reg).
    assert (V9 : getr r1 9 = Z_to_bv 64 m) by viac AGP (9:reg).
    assert (V18 : getr r1 18 = Z_to_bv 64 ab) by viac AGP (18:reg).
    assert (V19 : getr r1 19 = Z_to_bv 64 0x10ab58) by viac AGP (19:reg).
    assert (V20 : getr r1 20 = Z_to_bv 64 (2 ^ 37)) by viac AGP (20:reg).
    assert (V4 : getr r1 4 = tp) by viac AGP (4:reg).
    assert (V21 : getr r1 21 = x21) by viac AGP (21:reg).
    assert (V3 : getr r1 3 = getr r0 3) by viac AGP (3:reg).
    assert (V22 : getr r1 22 = getr r0 22) by viac AGP (22:reg).
    assert (V23 : getr r1 23 = getr r0 23) by viac AGP (23:reg).
    assert (V24 : getr r1 24 = getr r0 24) by viac AGP (24:reg).
    assert (V25 : getr r1 25 = getr r0 25) by viac AGP (25:reg).
    assert (V26 : getr r1 26 = getr r0 26) by viac AGP (26:reg).
    assert (V27 : getr r1 27 = getr r0 27) by viac AGP (27:reg).
    (* [comment removed for export] *)
    destruct (k3_run M3 rom S r1 V2 ltac:(lia)
                ltac:(eapply (store_ok_sub BSEGS M3 (at_ S (-2512)) _ 112); [rewrite at_u; lia | eapply store_ok_mono; [exact GR3 | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]))
      as (r2 & RUN2 & W1 & W2 & W3 & W4 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
    assert (GR4 : mem_grows M2 (fr_k3 M3 S)) by (eapply mem_grows_trans; [exact GR3|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end); grows_tac).
    assert (Q4 : forall x : word, ((U x < U S - 2504)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < shlo \/ shlo + n8 / 8 <= U x)%Z -> fr_k3 M3 S x = M2 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end). intros x Hx Hx2. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. apply Q3; assumption. }
    assert (RA4 : rdn BSEGS (fr_k3 M3 S) (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ea14))) by ((lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end); rd_hit8).
    remember (fr_k3 M3 S) as M4 eqn:EM4 in RUN2, GR4, Q4, RA4.
    (* [comment removed for export] *)
    assert (RET_G : ret_ok (Z_to_bv 64 0x78004)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (GH : gctH BSEGS both_gct_tab M4 (at_ S (-2464)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xq Q4 C_kif. - xq Q4 C_key. - xq Q4 C_tsdp. - xq Q4 C_tctx. - first [clear - Q4 SH2 C_thr Gctxs Gctx Gm Gce Gspb GS | idtac]; (xqh Gctxs Q4 C_thr).
      - unorm. lia.
      - rewrite at_at. eapply (store_ok_sub BSEGS M4 (at_ S (-2512)) _ 112); [rewrite at_u; lia | eapply store_ok_mono; [exact GR4 | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (gct_run BSEGS both_gct_tab both_gct_tab_ok M4 rom r2 (Z_to_bv 64 0x78004) (at_ S (-2464)) tp tsdp ctxw thr GH RET_G W1 W2 ltac:(rewrite W4; exact V4))
      as (r3 & RUN3 & X10 & X11 & AGX).
    cbn [gt_rb both_gct_tab] in RUN3. rewrite at0_litS4 in RUN3 by lia. rewrite at_at in RUN3. change (-2464 + -8)%Z with (-2472)%Z in RUN3.
    assert (GR5 : mem_grows M2 (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)))) by (eapply mem_grows_trans; [exact GR4|]; grows_tac).
    assert (Q5 : forall x : word, ((U x < U S - 2504)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < shlo \/ shlo + n8 / 8 <= U x)%Z ->
                 wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) x = M2 x).
    { intros x Hx Hx2. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. apply Q4; assumption. }
    assert (Y2 : getr r3 2 = at_ S (-2464)) by viac AGX (2:reg).
    assert (Y8 : getr r3 8 = at_ S (-2392)) by viac AGX (8:reg).
    assert (Y9 : getr r3 9 = Z_to_bv 64 m) by viac AGX (9:reg).
    assert (Y18 : getr r3 18 = Z_to_bv 64 ab) by viac AGX (18:reg).
    assert (Y19 : getr r3 19 = Z_to_bv 64 0x10ab58) by viac AGX (19:reg).
    assert (Y20 : getr r3 20 = Z_to_bv 64 (2 ^ 37)) by viac AGX (20:reg).
    assert (Y21 : getr r3 21 = x21) by viac AGX (21:reg).
    assert (Y3 : getr r3 3 = getr r0 3) by viac AGX (3:reg).
    assert (Y4 : getr r3 4 = tp) by viac AGX (4:reg).
    assert (Y22 : getr r3 22 = getr r0 22) by viac AGX (22:reg).
    assert (Y23 : getr r3 23 = getr r0 23) by viac AGX (23:reg).
    assert (Y24 : getr r3 24 = getr r0 24) by viac AGX (24:reg).
    assert (Y25 : getr r3 25 = getr r0 25) by viac AGX (25:reg).
    assert (Y26 : getr r3 26 = getr r0 26) by viac AGX (26:reg).
    assert (Y27 : getr r3 27 = getr r0 27) by viac AGX (27:reg).
    (* [comment removed for export] *)
    assert (RA5 : rdn BSEGS (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004))) (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ea14))).
    { rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. exact RA4. }
    remember (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004))) as M5 eqn:EM5 in RUN3, GR5, Q5, RA5.
    assert (GTk : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z) by (split; [exact GT1 | split; [exact GTS | exact GT2]]).
    destruct (k4_run M5 rom S ra0 s0v s1v s2v s3v s4v (Z_to_bv 64 (T + 208)) T m n spb c e bf0 bf1 r3 Y2 X10 Y8 Y9 Y18 Y19 Y20
                ltac:((first [clear - GS | idtac]; lia)) GTk ltac:((first [clear - Gn8 Gm Gce Gspb | idtac]; lia)) ltac:((first [clear - Gn | idtac]; lia)) ltac:((first [clear - Gspb | idtac]; lia)) ltac:((first [clear - Gce | idtac]; lia)) RA5
                ltac:(xq Q5 C_nhi) ltac:(xq Q5 C_nlo) ltac:(xqh GTS Q5 C_f0) L_f0 ltac:(xqh GTS Q5 C_f1) L_f1
                ltac:(eapply (store_ok_sub BSEGS M5 (Z_to_bv 64 T) _ (Z.to_nat 4096)); [unorm; (first [clear - GT GS | idtac]; lia) | eapply store_ok_mono; [exact GR5 | exact OkT] | unorm; (repeat match goal with H : _ |- _ => clear H end; lia) | unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (repeat match goal with H : _ |- _ => clear H end; lia)])
                ltac:(xq Q5 C_spb) ltac:(xq Q5 C_cache) ltac:(xq Q5 C_ra) ltac:(xq Q5 C_s0) ltac:(xq Q5 C_s1) ltac:(xq Q5 C_s2) ltac:(xq Q5 C_s3) ltac:(xq Q5 C_s4))
      as (r4 & RUN4 & Z1 & Z2 & Z10 & Z11 & Z12 & Z13 & Z8 & Z9 & Z18 & Z19 & Z20 & Z3 & Z4 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    assert (GR6 : mem_grows M2 (fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1))) by (eapply mem_grows_trans; [exact GR5|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_k4 in G in change_no_check G' end); grows_tac).
    assert (Q6 : forall x : word, ((U x < U S - 2504)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < shlo \/ shlo + n8 / 8 <= U x)%Z -> (U x < T + 2840 \/ T + 2856 <= U x)%Z ->
                 fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1) x = M2 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k4 in G in change_no_check G' end). intros x Hx Hx2 Hx3. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try (first [clear - GT GS Hx3 | idtac]; lia). apply Q5; assumption. }
    remember (fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) as M6 eqn:EM6 in RUN4, GR6, Q6.
    (* [comment removed for export] *)
    exists r4. split.
    { subst M6 M5 M4 M3. (lazymatch goal with |- ?G => let G' := eval unfold fr_k34 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      replace (Z_to_bv 64 0x4ea10 : word) with (0x4ea10 : word) in RUN1 at 1 by (apply bv_eq; reflexivity).
      replace (0x78004 : word) with (Z_to_bv 64 0x78004 : word) in RUN4 by (apply bv_eq; reflexivity).
      replace (0x78e2c : word) with (Z_to_bv 64 0x78e2c : word) in RUN2 by (apply bv_eq; reflexivity).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3 | exact RUN4]. }
    repeat match goal with |- _ /\ _ => split end; try assumption; try rch;
      try (viac AGP (21:reg)); try (viac AGX (21:reg)).
  Qed.
End RUNK34.
End FPGen.
End BoAllocFRc3S4.
Module BoAllocFRcS2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_ks1 (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2408)) (LE8 ra0))
    (at_ S (-2416)) (LE8 s0v))
    (at_ S (-2424)) (LE8 s1v))
    (at_ S (-2432)) (LE8 s2v))
    (at_ S (-2440)) (LE8 s3v))
    (at_ S (-2448)) (LE8 s4v).
#[local] Hint Unfold fr_ks1 : asfr.

Section KS1.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v cbv : word) (m spb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2400).
  Hypothesis H10 : getr regs 10 = cbv.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 m.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hm : (0 <= m < 2 ^ 47)%Z.
  Hypothesis Hsec : (m < spb \/ spb + 2 ^ 37 <= m)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2448)) 48 = true.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).

  Definition ks1_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = Z_to_bv 64 0x4e91c /\ getr r 2 = at_ S (-2448) /\ getr r 10 = Z_to_bv 64 0x10ab98 /\ getr r 11 = Z_to_bv 64 m
      /\ getr r 8 = cbv /\ getr r 9 = Z_to_bv 64 m /\ getr r 18 = s2v /\ getr r 19 = Z_to_bv 64 0x10ab58 /\ getr r 20 = Z_to_bv 64 (2 ^ 37)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Ltac ks1a :=
      an F_4e8a4 D_4e8a4;                              (* [comment removed for export] *)
      fsd F_4e8a8 D_4e8a8 (at_ S (-2408));             (* [comment removed for export] *)
      fsd F_4e8ac D_4e8ac (at_ S (-2416));             (* [comment removed for export] *)
      fsd F_4e8b0 D_4e8b0 (at_ S (-2424));             (* [comment removed for export] *)
      fsd F_4e8b4 D_4e8b4 (at_ S (-2432));             (* [comment removed for export] *)
      fsd F_4e8b8 D_4e8b8 (at_ S (-2440));             (* [comment removed for export] *)
      fsd F_4e8bc D_4e8bc (at_ S (-2448));             (* [comment removed for export] *)
      an F_4e8c0 D_4e8c0;                              (* [comment removed for export] *)
      an F_4e8c4 D_4e8c4;                              (* [comment removed for export] *)
      an F_4e8c8 D_4e8c8;                              (* [comment removed for export] *)
      an F_4e8cc D_4e8cc;                              (* [comment removed for export] *)
      cld8 F_4e8d0 D_4e8d0 (Z_to_bv 64 spb) Rspb;      (* [comment removed for export] *)
      an F_4e8d4 D_4e8d4;                              (* [comment removed for export] *)
      an F_4e8d8 D_4e8d8.                              (* [comment removed for export] *)
  Ltac ks1b :=
      an F_4e910 D_4e910;                              (* [comment removed for export] *)
      an F_4e914 D_4e914;                              (* [comment removed for export] *)
      an F_4e918 D_4e918.                              (* [comment removed for export] *)

  Lemma ks1_run :
    exists r, msteps BSEGS (mkst regs (0x4e8a4 : word) mem rom) (mkst r (0x4eb28 : word) (fr_ks1 mem S ra0 s0v s1v s2v s3v s4v) rom)
      /\ ks1_regs r.
  Proof using Rspb Hstk Hsec Hm Hspb HS H20 H19 H18 H9 H8 H11 H10 H2 H1 spb.
    (lazymatch goal with |- ?G => let G' := eval unfold ks1_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    destruct (Z_lt_le_dec m spb) as [LO | HI].
    - wd_eexists. split.
      + ks1a.
        ab_tk F_4e8dc D_4e8dc ltac:(condz).            (* [comment removed for export] *)
        ks1b.
        change (wbytes _ _ _) with (fr_ks1 mem S ra0 s0v s1v s2v s3v s4v). wd_refl.
      + post.
    - assert (HI2 : (spb + 2 ^ 37 <= m)%Z) by (destruct Hsec; lia).
      wd_eexists. split.
      + ks1a.
        ab_ft F_4e8dc D_4e8dc ltac:(condz).            (* [comment removed for export] *)
        av F_4e8e0 D_4e8e0 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
        ab_tk F_4e8e4 D_4e8e4 ltac:(condz).            (* [comment removed for export] *)
        ks1b.
        change (wbytes _ _ _) with (fr_ks1 mem S ra0 s0v s1v s2v s3v s4v). wd_refl.
      + post.
  Qed.
End KS1.

Section KS2.
  Variables (mem rom : word -> option byte) (p spb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 p.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 0x10ab58.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 (2 ^ 37).
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hp : (0 <= p < 2 ^ 47)%Z.
  Hypothesis Hsec : (p < spb \/ spb + 2 ^ 37 <= p)%Z.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).

  Lemma ks2_run :
    exists r, msteps BSEGS (mkst regs (0x4e91c : word) mem rom) (mkst r (0x4ea10 : word) mem rom)
      /\ getr r 18 = Z_to_bv 64 p
      /\ getr r 1 = getr regs 1 /\ getr r 2 = getr regs 2 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rspb Hsec Hp Hspb H20 H19 H10 spb.
    destruct (Z_lt_le_dec p spb) as [LO | HI].
    - wd_eexists. split.
      + an F_4e91c D_4e91c.                            (* [comment removed for export] *)
        cld8 F_4e920 D_4e920 (Z_to_bv 64 spb) Rspb.    (* [comment removed for export] *)
        av F_4e924 D_4e924 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
        ab_ft F_4e928 D_4e928 ltac:(condz).            (* [comment removed for export] *)
        an F_4e92c D_4e92c.                            (* [comment removed for export] *)
        wd_refl.
      + post.
    - assert (HI2 : (spb + 2 ^ 37 <= p)%Z) by (destruct Hsec; lia).
      wd_eexists. split.
      + an F_4e91c D_4e91c.
        cld8 F_4e920 D_4e920 (Z_to_bv 64 spb) Rspb.
        av F_4e924 D_4e924 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz).
        ab_tk F_4e928 D_4e928 ltac:(condz).            (* [comment removed for export] *)
        ab_tk F_4e994 D_4e994 ltac:(condz).            (* [comment removed for export] *)
        wd_refl.
      + post.
  Qed.
End KS2.

Section KS4.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T m n spb p : Z) (bf0 bf1 : list byte).
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2464).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 T.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 m.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 p.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 0x10ab58.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 (2 ^ 37).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hm : (AIMGHI <= m /\ m + 16 <= bv_unsigned S - 3584)%Z.
  Hypothesis HmT : (m + 16 <= T \/ T + 4096 <= m)%Z.
  Hypothesis Hn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hp : (1 <= p < 2 ^ 47)%Z.
  Hypothesis Hsec : (p < spb \/ spb + 2 ^ 37 <= p)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Rra : rdn BSEGS mem (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ea14)).
  Hypothesis Rnhi : rdn BSEGS mem (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis Rnlo : rdn BSEGS mem (Z_to_bv 64 (m + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))).
  Hypothesis Rf0 : rdn BSEGS mem (Z_to_bv 64 (T + 2840)) 8 = Some bf0.
  Hypothesis Lf0 : length bf0 = 8%nat.
  Hypothesis Rf1 : rdn BSEGS mem (Z_to_bv 64 (T + 2848)) 8 = Some bf1.
  Hypothesis Lf1 : length bf1 = 8%nat.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 (T + 2840)) 16 = true.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2432)) 8 = Some (LE8 s2v).
  Hypothesis Cs3 : rdn BSEGS mem (at_ S (-2440)) 8 = Some (LE8 s3v).
  Hypothesis Cs4 : rdn BSEGS mem (at_ S (-2448)) 8 = Some (LE8 s4v).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma n_split4s : (0 <= n / 2 ^ 32 <= 2 ^ 8 /\ 0 <= n mod 2 ^ 32 < 2 ^ 32 /\ n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n)%Z.
  Proof using Lf1 Lf0 Hn bf1 bf0 s4v rom. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). repeat split; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Definition ks4_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = ra0 /\ getr r 2 = at_ S (-2400)
      /\ getr r 10 = Z_to_bv 64 0x10ab98 /\ getr r 11 = Z_to_bv 64 (0x10ab58 + 688) /\ getr r 12 = Z_to_bv 64 p
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma ks4_run :
    exists r, msteps BSEGS (mkst regs (0x78004 : word) mem rom)
                           (mkst r (0x4ee70 : word) (fr_k4 mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) rom)
      /\ ks4_regs r.
  Proof using Cs4 Cs3 Cs2 Cs1 Cs0 Cra Rspb HokT Lf1 Rf1 Lf0 Rf0 Rnlo Rnhi Rra Hsec Hp Hspb Hn Hm HT HS H20 H19 H18 H9 H10 H2 spb m.
    (lazymatch goal with |- ?G => let G' := eval unfold ks4_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT3). unfold hideW in HT2.
    pose proof (bytes_le_to_Z_bound bf0) as Bf0. rewrite Lf0 in Bf0. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bf0.
    pose proof (bytes_le_to_Z_bound bf1) as Bf1. rewrite Lf1 in Bf1. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bf1.
    pose proof (bytes_le_to_Z_nonneg bf0) as Bf0'. pose proof (bytes_le_to_Z_nonneg bf1) as Bf1'.
    assert (Vf0 : bytes_le_to_Z bf0 = bv_unsigned f0) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vf1 : bytes_le_to_Z bf1 = bv_unsigned f1) by (rewrite u_Z2bv by lia; reflexivity).
    destruct n_split4s as (Nh & Nl & Nsum).
    assert (Vh : bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n / 2 ^ 32))).
    { rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2))%Z with (2 ^ 16)%Z. unorm. apply Z.mod_small. lia. }
    assert (Vl : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n mod 2 ^ 32))) by (apply bytes4_small; lia).
    Ltac ks4a Rra Rnhi Rnlo Rf0 Rf1 Vh Vl Vf0 Vf1 Rspb T n :=
      ab_ft F_78004 D_78004 ltac:(condz);              (* [comment removed for export] *)
      an F_78008 D_78008;                              (* [comment removed for export] *)
      an F_7800c D_7800c;                              (* [comment removed for export] *)
      cld8 F_78010 D_78010 (Z_to_bv 64 0x4ea14) Rra;   (* [comment removed for export] *)
      an F_78014 D_78014;                              (* [comment removed for export] *)
      rt F_78018 D_78018;                              (* [comment removed for export] *)
      clhu F_4ea14 D_4ea14 (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh;      (* [comment removed for export] *)
      clwu F_4ea18 D_4ea18 (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl;  (* [comment removed for export] *)
      cld F_4ea1c D_4ea1c bf1 (Z_to_bv 64 (bytes_le_to_Z bf1)) Rf1 Vf1;   (* [comment removed for export] *)
      cld F_4ea20 D_4ea20 bf0 (Z_to_bv 64 (bytes_le_to_Z bf0)) Rf0 Vf0;   (* [comment removed for export] *)
      av F_4ea24 D_4ea24 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz);   (* [comment removed for export] *)
      an F_4ea28 D_4ea28;                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia);
      an F_4ea2c D_4ea2c;                              (* [comment removed for export] *)
      an F_4ea30 D_4ea30;                              (* [comment removed for export] *)
      fsd F_4ea34 D_4ea34 (Z_to_bv 64 (T + 2840));     (* [comment removed for export] *)
      fsd F_4ea38 D_4ea38 (Z_to_bv 64 (T + 2848));     (* [comment removed for export] *)
      ab_ft F_4ea3c D_4ea3c ltac:(condz);              (* [comment removed for export] *)
      cld8 F_4ea40 D_4ea40 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
    Ltac ks4b ra0 s0v s1v s2v s3v s4v Cra Cs0 Cs1 Cs2 Cs3 Cs4 :=
      an F_4eaac D_4eaac;                              (* [comment removed for export] *)
      an F_4eab0 D_4eab0;                              (* [comment removed for export] *)
      an F_4eab4 D_4eab4;                              (* [comment removed for export] *)
      cld8 F_4eab8 D_4eab8 ra0 Cra;                    (* [comment removed for export] *)
      cld8 F_4eabc D_4eabc s0v Cs0; cld8 F_4eac0 D_4eac0 s1v Cs1; cld8 F_4eac4 D_4eac4 s2v Cs2;
      cld8 F_4eac8 D_4eac8 s3v Cs3; cld8 F_4eacc D_4eacc s4v Cs4;
      an F_4ead0 D_4ead0;                              (* [comment removed for export] *)
      an F_4ead4 D_4ead4.                              (* [comment removed for export] *)
    destruct (Z_lt_le_dec p spb) as [LO | HI].
    - wd_eexists. split.
      + ks4a Rra Rnhi Rnlo Rf0 Rf1 Vh Vl Vf0 Vf1 Rspb T n.
        ab_tk F_4ea44 D_4ea44 ltac:(condz).            (* [comment removed for export] *)
        ks4b ra0 s0v s1v s2v s3v s4v Cra Cs0 Cs1 Cs2 Cs3 Cs4.
        change (wbytes _ _ _) with (fr_k4 mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)). wd_refl.
      + post.
    - assert (HI2 : (spb + 2 ^ 37 <= p)%Z) by (destruct Hsec; lia).
      wd_eexists. split.
      + ks4a Rra Rnhi Rnlo Rf0 Rf1 Vh Vl Vf0 Vf1 Rspb T n.
        ab_ft F_4ea44 D_4ea44 ltac:(condz).            (* [comment removed for export] *)
        av F_4ea48 D_4ea48 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
        ab_tk F_4ea4c D_4ea4c ltac:(condz).            (* [comment removed for export] *)
        ks4b ra0 s0v s1v s2v s3v s4v Cra Cs0 Cs1 Cs2 Cs3 Cs4.
        change (wbytes _ _ _) with (fr_k4 mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)). wd_refl.
      + post.
  Qed.
End KS4.
End FPGen.
End BoAllocFRcS2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRc3c.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Lemma at0_litS : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof. intros c Hc. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. reflexivity. Qed.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_k35 (M2 : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 : word) (m ab n8 T c cnt e : Z) (j0 j1 stw : word)
  : word -> option byte :=
  let M3 := wbytes (ps_frame M2 (at_ S (-2448)) (Z_to_bv 64 0x4ea10) (at_ S (-2392)) (Z_to_bv 64 m) (Z_to_bv 64 ab)
                             (Z_to_bv 64 0x10ab58) (Z_to_bv 64 (2 ^ 37)) x21)
                   (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (repeat (MemsetLibF.cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 n8)))) in
  let M4 := fr_k3 M3 S in
  let M5 := wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) in
  let M6 := fr_k4 M5 T j0 j1 in
  fr_k5 M6 S ra0 s0v s1v s2v s3v s4v T c cnt e stw.

Section RUNK35.
  Variables (M2 rom : word -> option byte) (r0 : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 tp tsdp : word) (m spb c e n n8 T tctx cnt mx : Z).
  Variables (cpm : byte) (midend : word) (bf0 bf1 bst bcs : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation ab := (spb + c * 2 ^ 32 + e)%Z.
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  #[local] Abbreviation shlo := (0x7fff8000 + (m + 16) / 8)%Z.
  (* [comment removed for export] *)
  Hypothesis H1 : getr r0 1 = Z_to_bv 64 0x4ea10.
  Hypothesis H2 : getr r0 2 = at_ S (-2448).
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 (m + 16).
  Hypothesis H11 : getr r0 11 = Z_to_bv 64 n8.
  Hypothesis H12 : getr r0 12 = Z_to_bv 64 250.
  Hypothesis H8 : getr r0 8 = at_ S (-2392).
  Hypothesis H9 : getr r0 9 = Z_to_bv 64 m.
  Hypothesis H18 : getr r0 18 = Z_to_bv 64 ab.
  Hypothesis H19 : getr r0 19 = Z_to_bv 64 0x10ab58.
  Hypothesis H20 : getr r0 20 = Z_to_bv 64 (2 ^ 37).
  Hypothesis H21 : getr r0 21 = x21.
  Hypothesis H4 : getr r0 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gspb : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Gce : (1 <= c <= 30 /\ 0 <= e < 2 ^ 32)%Z.
  Hypothesis Gm : (ab <= m /\ m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : ((n <= n8 <= n + 7) /\ n8 mod 8 = 0 /\ 8 <= n8)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis GmT : hideW (m + 16 + n8 <= T \/ T + 4096 <= m)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584)%Z.
  Hypothesis GctxT : hideW (tctx + 4096 <= T \/ T + 4096 <= tctx)%Z.
  Hypothesis Gctxm : hideW (tctx + 4096 <= m \/ m + 16 + n8 <= tctx)%Z.
  Hypothesis Gctxs : hideW (tctx + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= tctx)%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis Gcnt : (0 <= cnt < mx /\ mx <= 16)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS M2 (at_ S (-2512)) 112 = true.
  Hypothesis Oksh : store_ok BSEGS M2 (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS M2 (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  (* [comment removed for export] *)
  Hypothesis C_gsh : rdn BSEGS M2 (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS M2 (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS M2 (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS M2 (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS M2 (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS M2 (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS M2 (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS M2 (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS M2 (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS M2 (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS M2 (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_kif : rdn BSEGS M2 (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS M2 (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS M2 (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS M2 tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS M2 (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_nhi : rdn BSEGS M2 (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS M2 (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_f0 : rdn BSEGS M2 (Z_to_bv 64 (T + 2840)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS M2 (Z_to_bv 64 (T + 2848)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_spb : rdn BSEGS M2 (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_cache : rdn BSEGS M2 (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + 208))).
  Hypothesis C_ra : rdn BSEGS M2 (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis C_s0 : rdn BSEGS M2 (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis C_s1 : rdn BSEGS M2 (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis C_s2 : rdn BSEGS M2 (at_ S (-2432)) 8 = Some (LE8 s2v).
  Hypothesis C_s3 : rdn BSEGS M2 (at_ S (-2440)) 8 = Some (LE8 s3v).
  Hypothesis C_s4 : rdn BSEGS M2 (at_ S (-2448)) 8 = Some (LE8 s4v).
  Hypothesis C_mx : rdn BSEGS M2 (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis C_cnt : rdn BSEGS M2 (Z_to_bv 64 pc_) 4 = Some (LE4 cnt).
  Hypothesis C_cs : rdn BSEGS M2 (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis L_cs : length bcs = 8%nat.
  Hypothesis C_st : rdn BSEGS M2 (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis L_st : length bst = 8%nat.

  Definition k35_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = x21 /\ getr r 3 = getr r0 3 /\ getr r 4 = tp
      /\ getr r 22 = getr r0 22 /\ getr r 23 = getr r0 23 /\ getr r 24 = getr r0 24
      /\ getr r 25 = getr r0 25 /\ getr r 26 = getr r0 26 /\ getr r 27 = getr r0 27.

  Theorem run_k35 :
    exists r, msteps BSEGS (mkst r0 (0x70080 : word) M2 rom)
                           (mkst r ra0 (fr_k35 M2 S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T c cnt e (at_ f0 1) (v_add (Z_to_bv 64 n) f1) stw) rom)
      /\ k35_regs r.
  Proof using L_st C_st L_cs C_cs C_cnt C_mx C_s4 C_s3 C_s2 C_s1 C_s0 C_ra C_cache C_spb L_f1 C_f1 L_f0 C_f0 C_nlo C_nhi C_thr C_tctx C_tsdp C_key C_kif C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh OkT Oksh Hstk Hret Gcnt Gtsdp Gtp Gctxs Gctx GT Gn8 Gn Gm Gce Gspb GS H4 H21 H20 H19 H18 H9 H8 H12 H11 H10 H2 H1 midend cpm mx tctx tsdp.
    (lazymatch goal with |- ?G => let G' := eval unfold k35_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2). destruct Gce as (Hc & He). destruct Gm as (Gm1 & Gm3 & Gm16).
    destruct Gn8 as (N8b & N8c & N8d). destruct GT as (GT1 & (GTS & GT2) & GT16). destruct Gctx as (Gc1 & Gc2).
    destruct (p16_facts (m + 16) ltac:(clear - Gm16; Z.div_mod_to_equations; lia) ltac:(lia)) as (_ & _ & _ & Mp8 & _).
    destruct (shad_facts2 (m + 16) n8 ltac:(lia) ltac:(lia) ltac:(lia) N8d Mp8 N8c) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). hidehypW SH1.
    assert (SHB : (0x7fff8000 + 0x2001000 <= shlo /\ shlo + n8 / 8 <= 0x10007fff8000)%Z).
    { unfold hideW in SH1. clear - SH1 SH2 SH3 Gs1 Gm1 Hc He N8d. destruct SH1 as [X|X]; lia. }
    Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    Ltac xqh TS Q H := unfold hideW in TS; xq Q H.
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold poison_clob, gct_clob in G in change_no_check G' end); notin)); rch.
    (* [comment removed for export] *)
    assert (PH : poisonH BSEGS both_poison_tab M2 (Z_to_bv 64 (m + 16)) (Z_to_bv 64 n8) (Z_to_bv 64 250) (Z_to_bv 64 0x4ea10) (at_ S (-2448)) cpm midend 0).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm pt_base pt_mset both_poison_tab] in G in change_no_check G' end).
      - exact C_gsh. - exact C_sh. - exact C_gmb. - exact C_mb. - exact C_gme. - exact C_me. - exact C_ghe. - exact C_he.
      - exact C_grm. - exact C_rm.
      - vm_compute. discriminate.
      - apply ret_ok_even. reflexivity.
      - intros _. split; [exact C_cpm | exact C_cpm1].
      - intros Hz. exfalso. revert Hz. unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
        repeat constructor; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ].
      - unorm. exact Mp8.
      - unorm. exact N8c.
      - unorm. left. lia.
      - rewrite at_u by lia. lia.
      - eapply (store_ok_sub BSEGS M2 (at_ S (-2512)) _ 112); [rewrite at_u; lia | exact Hstk | rewrite !at_at, !at_u; lia | rewrite !at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. exact Oksh.
      - apply ret_ok_lit; [lia | reflexivity]. }
    destruct (both_poison_shadow M2 rom (Z_to_bv 64 (m + 16)) (Z_to_bv 64 n8) (Z_to_bv 64 250) (Z_to_bv 64 0x4ea10) (at_ S (-2448)) cpm midend 0 r0 PH H1 H2 H10 H11 H12)
      as (r1 & RUN1 & AGP).
    rewrite H8, H9, H18, H19, H20, H21 in RUN1.
    set (M3t := wbytes _ _ _) in RUN1.
    assert (GR3 : mem_grows M2 M3t) by ((lazymatch goal with |- ?G => let G' := eval unfold M3t, ps_frame in G in change_no_check G' end); grows_tac).
    assert (Q3 : forall x : word, ((U x < U S - 2504)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < shlo \/ shlo + n8 / 8 <= U x)%Z -> M3t x = M2 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M3t, ps_frame in G in change_no_check G' end). rewrite !at_at. intros x Hx Hx2.
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by (first [clear - GS | idtac]; lia); try (first [clear - GS Hx | idtac]; lia).
      1: reflexivity.
      all: (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); unorm; rewrite ?Z2Nat.id by (first [clear - Gn8 | idtac]; lia); (first [clear - SH2 Hx2 | idtac]; lia). }
    remember M3t as M3 eqn:EM3 in RUN1, GR3, Q3. subst M3t.
    assert (V2 : getr r1 2 = at_ S (-2448)) by viac AGP (2:reg).
    assert (V8 : getr r1 8 = at_ S (-2392)) by viac AGP (8:reg).
    assert (V9 : getr r1 9 = Z_to_bv 64 m) by viac AGP (9:reg).
    assert (V18 : getr r1 18 = Z_to_bv 64 ab) by viac AGP (18:reg).
    assert (V19 : getr r1 19 = Z_to_bv 64 0x10ab58) by viac AGP (19:reg).
    assert (V20 : getr r1 20 = Z_to_bv 64 (2 ^ 37)) by viac AGP (20:reg).
    assert (V4 : getr r1 4 = tp) by viac AGP (4:reg).
    assert (V21 : getr r1 21 = x21) by viac AGP (21:reg).
    assert (V3 : getr r1 3 = getr r0 3) by viac AGP (3:reg).
    assert (V22 : getr r1 22 = getr r0 22) by viac AGP (22:reg).
    assert (V23 : getr r1 23 = getr r0 23) by viac AGP (23:reg).
    assert (V24 : getr r1 24 = getr r0 24) by viac AGP (24:reg).
    assert (V25 : getr r1 25 = getr r0 25) by viac AGP (25:reg).
    assert (V26 : getr r1 26 = getr r0 26) by viac AGP (26:reg).
    assert (V27 : getr r1 27 = getr r0 27) by viac AGP (27:reg).
    (* [comment removed for export] *)
    destruct (k3_run M3 rom S r1 V2 ltac:(lia)
                ltac:(eapply (store_ok_sub BSEGS M3 (at_ S (-2512)) _ 112); [rewrite at_u; lia | eapply store_ok_mono; [exact GR3 | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]))
      as (r2 & RUN2 & W1 & W2 & W3 & W4 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
    assert (GR4 : mem_grows M2 (fr_k3 M3 S)) by (eapply mem_grows_trans; [exact GR3|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end); grows_tac).
    assert (Q4 : forall x : word, ((U x < U S - 2504)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < shlo \/ shlo + n8 / 8 <= U x)%Z -> fr_k3 M3 S x = M2 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end). intros x Hx Hx2. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. apply Q3; assumption. }
    assert (RA4 : rdn BSEGS (fr_k3 M3 S) (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ea14))) by ((lazymatch goal with |- ?G => let G' := eval unfold fr_k3 in G in change_no_check G' end); rd_hit8).
    remember (fr_k3 M3 S) as M4 eqn:EM4 in RUN2, GR4, Q4, RA4.
    (* [comment removed for export] *)
    assert (RET_G : ret_ok (Z_to_bv 64 0x78004)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (GH : gctH BSEGS both_gct_tab M4 (at_ S (-2464)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xq Q4 C_kif. - xq Q4 C_key. - xq Q4 C_tsdp. - xq Q4 C_tctx. - first [clear - Q4 SH2 C_thr Gctxs Gctx Gm Gce Gspb GS | idtac]; (xqh Gctxs Q4 C_thr).
      - unorm. lia.
      - rewrite at_at. eapply (store_ok_sub BSEGS M4 (at_ S (-2512)) _ 112); [rewrite at_u; lia | eapply store_ok_mono; [exact GR4 | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (gct_run BSEGS both_gct_tab both_gct_tab_ok M4 rom r2 (Z_to_bv 64 0x78004) (at_ S (-2464)) tp tsdp ctxw thr GH RET_G W1 W2 ltac:(rewrite W4; exact V4))
      as (r3 & RUN3 & X10 & X11 & AGX).
    cbn [gt_rb both_gct_tab] in RUN3. rewrite at0_litS in RUN3 by lia. rewrite at_at in RUN3. change (-2464 + -8)%Z with (-2472)%Z in RUN3.
    assert (GR5 : mem_grows M2 (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)))) by (eapply mem_grows_trans; [exact GR4|]; grows_tac).
    assert (Q5 : forall x : word, ((U x < U S - 2504)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < shlo \/ shlo + n8 / 8 <= U x)%Z ->
                 wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) x = M2 x).
    { intros x Hx Hx2. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. apply Q4; assumption. }
    assert (Y2 : getr r3 2 = at_ S (-2464)) by viac AGX (2:reg).
    assert (Y8 : getr r3 8 = at_ S (-2392)) by viac AGX (8:reg).
    assert (Y9 : getr r3 9 = Z_to_bv 64 m) by viac AGX (9:reg).
    assert (Y18 : getr r3 18 = Z_to_bv 64 ab) by viac AGX (18:reg).
    assert (Y19 : getr r3 19 = Z_to_bv 64 0x10ab58) by viac AGX (19:reg).
    assert (Y20 : getr r3 20 = Z_to_bv 64 (2 ^ 37)) by viac AGX (20:reg).
    assert (Y21 : getr r3 21 = x21) by viac AGX (21:reg).
    assert (Y3 : getr r3 3 = getr r0 3) by viac AGX (3:reg).
    assert (Y4 : getr r3 4 = tp) by viac AGX (4:reg).
    assert (Y22 : getr r3 22 = getr r0 22) by viac AGX (22:reg).
    assert (Y23 : getr r3 23 = getr r0 23) by viac AGX (23:reg).
    assert (Y24 : getr r3 24 = getr r0 24) by viac AGX (24:reg).
    assert (Y25 : getr r3 25 = getr r0 25) by viac AGX (25:reg).
    assert (Y26 : getr r3 26 = getr r0 26) by viac AGX (26:reg).
    assert (Y27 : getr r3 27 = getr r0 27) by viac AGX (27:reg).
    (* [comment removed for export] *)
    assert (RA5 : rdn BSEGS (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004))) (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4ea14))).
    { rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. exact RA4. }
    remember (wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004))) as M5 eqn:EM5 in RUN3, GR5, Q5, RA5.
    assert (GTk : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z) by (split; [exact GT1 | split; [exact GTS | exact GT2]]).
    destruct (k4_run M5 rom S ra0 s0v s1v s2v s3v s4v (Z_to_bv 64 (T + 208)) T m n spb c e bf0 bf1 r3 Y2 X10 Y8 Y9 Y18 Y19 Y20
                ltac:((first [clear - GS | idtac]; lia)) GTk ltac:((first [clear - Gn8 Gm Gce Gspb | idtac]; lia)) ltac:((first [clear - Gn | idtac]; lia)) ltac:((first [clear - Gspb | idtac]; lia)) ltac:((first [clear - Gce | idtac]; lia)) RA5
                ltac:(xq Q5 C_nhi) ltac:(xq Q5 C_nlo) ltac:(xqh GTS Q5 C_f0) L_f0 ltac:(xqh GTS Q5 C_f1) L_f1
                ltac:(eapply (store_ok_sub BSEGS M5 (Z_to_bv 64 T) _ (Z.to_nat 4096)); [unorm; (first [clear - GT GS | idtac]; lia) | eapply store_ok_mono; [exact GR5 | exact OkT] | unorm; (repeat match goal with H : _ |- _ => clear H end; lia) | unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (repeat match goal with H : _ |- _ => clear H end; lia)])
                ltac:(xq Q5 C_spb) ltac:(xq Q5 C_cache) ltac:(xq Q5 C_ra) ltac:(xq Q5 C_s0) ltac:(xq Q5 C_s1) ltac:(xq Q5 C_s2) ltac:(xq Q5 C_s3) ltac:(xq Q5 C_s4))
      as (r4 & RUN4 & Z1 & Z2 & Z10 & Z11 & Z12 & Z13 & Z8 & Z9 & Z18 & Z19 & Z20 & Z3 & Z4 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    assert (GR6 : mem_grows M2 (fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1))) by (eapply mem_grows_trans; [exact GR5|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_k4 in G in change_no_check G' end); grows_tac).
    assert (Q6 : forall x : word, ((U x < U S - 2504)%Z \/ (U S - 2448 <= U x)%Z) -> (U x < shlo \/ shlo + n8 / 8 <= U x)%Z -> (U x < T + 2840 \/ T + 2856 <= U x)%Z ->
                 fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1) x = M2 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k4 in G in change_no_check G' end). intros x Hx Hx2 Hx3. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try (first [clear - GT GS Hx3 | idtac]; lia). apply Q5; assumption. }
    remember (fr_k4 M5 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) as M6 eqn:EM6 in RUN4, GR6, Q6.
    (* [comment removed for export] *)
    destruct (k5_run M6 rom S ra0 s0v s1v s2v s3v s4v T spb c e cnt mx bst bcs r4 Z1 Z2 Z10 Z11 Z12 Z13 Z8 Z9 Z18 Z19 Z20
                ltac:((first [clear - GS | idtac]; lia)) ltac:(split; [exact GT1 | split; [split; [exact GTS | exact GT2] | exact GT16]]) ltac:((first [clear - Gspb | idtac]; lia)) Hc He Gcnt Hret L_st L_cs
                ltac:(eapply (store_ok_sub BSEGS M6 (at_ S (-2512)) _ 112); [rewrite at_u; (first [clear - GS | idtac]; lia) | eapply store_ok_mono; [exact GR6 | exact Hstk] | rewrite !at_u; (first [clear - GS | idtac]; lia) | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - GS | idtac]; lia)])
                ltac:(eapply store_ok_mono; [exact GR6 | exact OkT])
                ltac:(xqh GTS Q6 C_mx) ltac:(xqh GTS Q6 C_cnt) ltac:(xqh GTS Q6 C_cs) ltac:(xqh GTS Q6 C_st) ltac:(xqh GTS Q6 C_spb))
      as (r5 & RUN5 & F2 & F8 & F9 & F18 & F19 & F20 & F3 & F4 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    (* [comment removed for export] *)
    exists r5. split.
    { subst M6 M5 M4 M3. (lazymatch goal with |- ?G => let G' := eval unfold fr_k35 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      replace (Z_to_bv 64 0x4ea10 : word) with (0x4ea10 : word) in RUN1 at 1 by (apply bv_eq; reflexivity).
      replace (0x78004 : word) with (Z_to_bv 64 0x78004 : word) in RUN4 by (apply bv_eq; reflexivity).
      replace (0x78e2c : word) with (Z_to_bv 64 0x78e2c : word) in RUN2 by (apply bv_eq; reflexivity).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4 | exact RUN5]. }
    repeat match goal with |- _ /\ _ => split end; try assumption; try rch;
      try (viac AGP (21:reg)); try (viac AGX (21:reg)).
  Qed.
End RUNK35.
End FPGen.

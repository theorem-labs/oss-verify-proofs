(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocF0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_76b0c_77514 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_7ab0c_7b3f4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_8fc84_905f0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_icpt (mem : word -> option byte) (S ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-8)) (word_to_le_bytes 8 ra))
    (at_ S (-16)) (word_to_le_bytes 8 s0))
    (at_ S (-24)) (word_to_le_bytes 8 s1))
    (at_ S (-32)) (word_to_le_bytes 8 s2))
    (at_ S (-40)) (word_to_le_bytes 8 s3))
    (at_ S (-48)) (word_to_le_bytes 8 s4))
    (at_ S (-56)) (word_to_le_bytes 8 s5).

Hint Unfold fr_icpt : asfr.

Section ICPTPRO.
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables S ra p : word.
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = S.
  Hypothesis H10 : getr regs 10 = p.
  Hypothesis HS : (2128 <= bv_unsigned S)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-56)) 56 = true.

  #[local] Abbreviation M1 := (fr_icpt mem S ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).

  Lemma icpt_pro :
    exists r,
      msteps BSEGS (mkst regs (0x6ed6c : word) mem rom) (mkst r (0x7aea8 : word) M1 rom)
      /\ getr r 1 = (0x6eda0 : word) /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p
      /\ getr r 18 = ra /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3 /\ getr r 19 = getr regs 19
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk HS H10 H2 H1.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_6ed6c D_6ed6c.                              (* [comment removed for export] *)
      fsd F_6ed70 D_6ed70 (at_ S (-8)).                (* [comment removed for export] *)
      fsd F_6ed74 D_6ed74 (at_ S (-16)).               (* [comment removed for export] *)
      fsd F_6ed78 D_6ed78 (at_ S (-24)).               (* [comment removed for export] *)
      fsd F_6ed7c D_6ed7c (at_ S (-32)).               (* [comment removed for export] *)
      fsd F_6ed80 D_6ed80 (at_ S (-40)).               (* [comment removed for export] *)
      fsd F_6ed84 D_6ed84 (at_ S (-48)).               (* [comment removed for export] *)
      fsd F_6ed88 D_6ed88 (at_ S (-56)).               (* [comment removed for export] *)
      an F_6ed8c D_6ed8c.                              (* [comment removed for export] *)
      an F_6ed90 D_6ed90.                              (* [comment removed for export] *)
      an F_6ed94 D_6ed94.                              (* [comment removed for export] *)
      an F_6ed98 D_6ed98.                              (* [comment removed for export] *)
      an F_6ed9c D_6ed9c.                              (* [comment removed for export] *)
      wd_refl.
    - post. apply bv_eq; vm_compute; reflexivity.
  Qed.
End ICPTPRO.

(* [comment removed for export] *)
Definition fr_ia (M1 : word -> option byte) (S p ra s3 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes M1
    (at_ S (-2136)) (word_to_le_bytes 8 (0x6eda0 : word)))
    (at_ S (-2144)) (word_to_le_bytes 8 S))
    (at_ S (-2152)) (word_to_le_bytes 8 p))
    (at_ S (-2160)) (word_to_le_bytes 8 ra))
    (at_ S (-2168)) (word_to_le_bytes 8 s3).
(* [comment removed for export] *)
Definition fr_p1 (M1 : word -> option byte) (S p ra s3 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (fr_ia M1 S p ra s3)
    (at_ S (-72)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (at_ S (-2128)) (word_to_le_bytes 8 (at_ S (-2112))))
    (at_ S (-2120)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (at_ S (-72)) (word_to_le_bytes 8 S).

Hint Unfold fr_ia fr_p1 : asfr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma p_div_facts : forall x, (0 <= x < 2 ^ 47)%Z -> (x / 2 ^ 47 = 0 /\ 0 <= x / 2 ^ 32 < 2 ^ 15)%Z.
Proof using. intros x Hx. split; [apply Z.div_small; lia | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]]. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P1TAIL.
  Variable mem : word -> option byte.     (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables S ra p : word.
  Variable s3 : word.
  Variable regs : bvmap 5 word.           (* [comment removed for export] *)
  Variable iab : byte.                    (* [comment removed for export] *)
  Variable pim : list byte.               (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = (0x6eda0 : word).
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H18 : getr regs 18 = ra.
  Hypothesis H19 : getr regs 19 = s3.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S)%Z.      (* [comment removed for export] *)
  Hypothesis HS16 : (bv_unsigned S mod 16 = 0)%Z.
  Hypothesis HShi : (bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (bv_unsigned p < 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2176)) 2176 = true.
  (* [comment removed for export] *)
  Hypothesis Rflag : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 1 = Some [iab].
  Hypothesis Hiab : bv_unsigned iab <> 0%Z.
  Variable q32 : Z.                       (* [comment removed for export] *)
  Hypothesis Hq32 : (bv_unsigned p / 2 ^ 32)%Z = q32.
  Hypothesis Hq32b : (0 <= q32 < 2 ^ 15)%Z.
  Hypothesis Hq47 : (bv_unsigned p / 2 ^ 47 = 0)%Z.
  Hypothesis Rpim : rdn BSEGS mem (Z_to_bv 64 (0x10f3c8 + 8 * q32)) 8 = Some pim.
  Hypothesis Hpim : bytes_le_to_Z pim = 0%Z.
  Hypothesis Rmcs : rdn BSEGS mem (Z_to_bv 64 0x10eebc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 30)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19fce8)).
  Hypothesis Rfum : rdn BSEGS mem (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].

  #[local] Abbreviation M2 := (fr_p1 mem S p ra s3).

  (* [comment removed for export] *)
  Lemma p1_blkA :
    exists r,
      msteps BSEGS (mkst regs (0x7aea8 : word) mem rom) (mkst r (0x6ee44 : word) (fr_ia mem S p ra s3) rom)
      /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p /\ getr r 18 = ra
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hpim Rpim Hq47 Hq32b Hq32 q32 Hiab Rflag Hstk HShi HS H19 H18 H9 H8 H2 H1 pim iab.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. pose proof (u_v_lb_nz iab Hiab) as Hiab'.
    wd_eexists. split.
    - (* [comment removed for export] *)
      an F_7aea8 D_7aea8.                              (* [comment removed for export] *)
      fsd F_7aeac D_7aeac (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_7aeb0 D_7aeb0 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_7aeb4 D_7aeb4 (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_7aeb8 D_7aeb8 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_7aebc D_7aebc (at_ S (-2168)).             (* [comment removed for export] *)
      an F_7aec0 D_7aec0.                              (* [comment removed for export] *)
      an F_7aec4 D_7aec4.                              (* [comment removed for export] *)
      clb F_7aec8 D_7aec8 iab Rflag.                   (* [comment removed for export] *)
      afence F_7aecc D_7aecc.                          (* [comment removed for export] *)
      ab_tk F_7aed0 D_7aed0 ltac:(condz).              (* [comment removed for export] *)
      an F_7afcc D_7afcc.                              (* [comment removed for export] *)
      an F_7afd0 D_7afd0.                              (* [comment removed for export] *)
      fld F_7afd4 D_7afd4 (0x6eda0 : word).            (* [comment removed for export] *)
      fld F_7afd8 D_7afd8 S.                           (* [comment removed for export] *)
      fld F_7afdc D_7afdc p.                           (* [comment removed for export] *)
      fld F_7afe0 D_7afe0 ra.                          (* [comment removed for export] *)
      fld F_7afe4 D_7afe4 s3.                          (* [comment removed for export] *)
      an F_7afe8 D_7afe8.                              (* [comment removed for export] *)
      rt F_7afec D_7afec.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      av F_6eda0 D_6eda0 (Z_to_bv 64 0) ltac:(valz).                                   (* [comment removed for export] *)
      ab_ft F_6eda4 D_6eda4 ltac:(condz).                                             (* [comment removed for export] *)
      av F_6eda8 D_6eda8 (Z_to_bv 64 q32) ltac:(valz).                                 (* [comment removed for export] *)
      av F_6edac D_6edac (Z_to_bv 64 (8 * q32)) ltac:(valz).                           (* [comment removed for export] *)
      av F_6edb0 D_6edb0 (Z_to_bv 64 (0x10f3c0 + 8 * q32)) ltac:(valz).                (* [comment removed for export] *)
      cld F_6edb4 D_6edb4 pim (Z_to_bv 64 0) Rpim Hpim.                               (* [comment removed for export] *)
      afence F_6edb8 D_6edb8.                                                         (* [comment removed for export] *)
      ab_tk F_6edbc D_6edbc ltac:(condz).                                             (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_ia mem S p ra s3). wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma p1_blkB : forall r0,
    getr r0 2 = at_ S (-2128) -> getr r0 8 = S -> getr r0 9 = p -> getr r0 18 = ra ->
    exists r,
      msteps BSEGS (mkst r0 (0x6ee44 : word) (fr_ia mem S p ra s3) rom) (mkst r (0x773c4 : word) M2 rom)
      /\ getr r 1 = Z_to_bv 64 0x6ef00 /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p /\ getr r 18 = Z_to_bv 64 0x6eea4
      /\ getr r 10 = at_ S (-2128) /\ getr r 11 = Z_to_bv 64 0x6eea4 /\ getr r 12 = S /\ getr r 13 = Z_to_bv 64 0
      /\ getr r 14 = Z_to_bv 64 1 /\ getr r 15 = Z_to_bv 64 30
      /\ getr r 19 = Z_to_bv 64 1 /\ getr r 20 = at_ S (-2128) /\ getr r 21 = at_ S (-81)
      /\ getr r 4 = getr r0 4 /\ getr r 3 = getr r0 3
      /\ getr r 22 = getr r0 22 /\ getr r 23 = getr r0 23
      /\ getr r 24 = getr r0 24 /\ getr r 25 = getr r0 25 /\ getr r 26 = getr r0 26 /\ getr r 27 = getr r0 27.
  Proof using Rfum Rgcf Rmcs Hstk HShi HS.
    intros r0 R2 R8 R9 R18.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    assert (bytes_le_to_Z_4_30 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 30)) = bv_unsigned (Z_to_bv 64 30)) by (vm_compute; reflexivity).
    wd_eexists. split.
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end). an F_6ee44 D_6ee44.                              (* [comment removed for export] *)
      an F_6ee48 D_6ee48.                              (* [comment removed for export] *)
      an F_6ee4c D_6ee4c.                              (* [comment removed for export] *)
      an F_6ee50 D_6ee50.                              (* [comment removed for export] *)
      an F_6ee54 D_6ee54.                              (* [comment removed for export] *)
      fsd F_6ee58 D_6ee58 (at_ S (-72)).               (* [comment removed for export] *)
      fsd F_6ee5c D_6ee5c (at_ S (-2128)).             (* [comment removed for export] *)
      fsd F_6ee60 D_6ee60 (at_ S (-2120)).             (* [comment removed for export] *)
      an F_6ee64 D_6ee64.                              (* [comment removed for export] *)
      an F_773b4 D_773b4.                              (* [comment removed for export] *)
      clw F_773b8 D_773b8 (word_to_le_bytes 4 (Z_to_bv 64 30)) (Z_to_bv 64 30) Rmcs bytes_le_to_Z_4_30.  (* [comment removed for export] *)
      afence F_773bc D_773bc.                          (* [comment removed for export] *)
      rt F_773c0 D_773c0.                              (* [comment removed for export] *)
      an F_6ee68 D_6ee68.                              (* [comment removed for export] *)
      ab_tk F_6ee6c D_6ee6c ltac:(condz).              (* [comment removed for export] *)
      an F_6eea0 D_6eea0.                              (* [comment removed for export] *)
      an F_8fe74 D_8fe74.                            (* [comment removed for export] *)
      rt F_8fe78 D_8fe78.                            (* [comment removed for export] *)
      an F_6eea4 D_6eea4.                              (* [comment removed for export] *)
      cld F_6eea8 D_6eea8 (word_to_le_bytes 8 (Z_to_bv 64 0x19fce8)) (Z_to_bv 64 0x19fce8) Rgcf (bytes_le_to_Z_8 (Z_to_bv 64 0x19fce8)).  (* [comment removed for export] *)
      clbu F_6eeac D_6eeac (Z_to_bv 8 1) Rfum.         (* [comment removed for export] *)
      an F_6eeb0 D_6eeb0.                              (* [comment removed for export] *)
      an F_6eeb4 D_6eeb4.                              (* [comment removed for export] *)
      an F_773b4 D_773b4.                              (* [comment removed for export] *)
      clw F_773b8 D_773b8 (word_to_le_bytes 4 (Z_to_bv 64 30)) (Z_to_bv 64 30) Rmcs bytes_le_to_Z_4_30.  (* [comment removed for export] *)
      afence F_773bc D_773bc.                          (* [comment removed for export] *)
      rt F_773c0 D_773c0.                              (* [comment removed for export] *)
      an F_6eeb8 D_6eeb8.                              (* [comment removed for export] *)
      an F_6eebc D_6eebc.                              (* [comment removed for export] *)
      an F_6eec0 D_6eec0.                              (* [comment removed for export] *)
      an F_6eec4 D_6eec4. rewrite v_and_m1_l.          (* [comment removed for export] *)
      an F_6eec8 D_6eec8.                              (* [comment removed for export] *)
      fsd F_6eecc D_6eecc (at_ S (-72)).               (* [comment removed for export] *)
      ab_tk F_6eed0 D_6eed0 ltac:(condz).              (* [comment removed for export] *)
      an F_6eee4 D_6eee4.                              (* [comment removed for export] *)
      an F_6eee8 D_6eee8.                              (* [comment removed for export] *)
      an F_6eeec D_6eeec.                              (* [comment removed for export] *)
      an F_6eef0 D_6eef0.                              (* [comment removed for export] *)
      an F_6eef4 D_6eef4.                              (* [comment removed for export] *)
      an F_6eef8 D_6eef8.                              (* [comment removed for export] *)
      an F_6eefc D_6eefc.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_p1 mem S p ra s3). wd_refl.
    - post.
  Qed.
End P1TAIL.
End FPGen1.
End BoAllocF0.
Require Stdlib.NArith.NArith Stdlib.Strings.PrimString Stdlib.Numbers.Cyclic.Int63.Uint63 Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocF0w.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.

Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wf_hexc (c : PrimString.char63) : bool :=
  ((Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63) || (Uint63.leb 97%uint63 c && Uint63.leb c 102%uint63))%bool.
(* [comment removed for export] *)
Fixpoint wf_hex_ok (s : PrimString.string) (j : Uint63.int) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => (Uint63.ltb (Uint63.add j 1%uint63) (PrimString.length s) && wf_hexc (PrimString.get s j)
             && wf_hexc (PrimString.get s (Uint63.add j 1%uint63)) && wf_hex_ok s (Uint63.add j 2%uint63) n')%bool
  end.

Definition wf_chunk_bytes (c : PrimString.string) : N := Z.to_N (Uint63.to_Z (PrimString.length c) / 2).

Fixpoint wf_chunks_ok (cs : list PrimString.string) (off : N) (n : nat) : bool :=
  match n with
  | O => true
  | S _ =>
      match cs with
      | [] => false
      | c :: rest =>
          let cb := wf_chunk_bytes c in
          if (off <? cb)%N then
            let k := N.to_nat (cb - off) in
            if Nat.leb n k then wf_hex_ok c (Uint63.of_Z (Z.of_N (2 * off))) n
            else (wf_hex_ok c (Uint63.of_Z (Z.of_N (2 * off))) k && wf_chunks_ok rest 0 (n - k))%bool
          else wf_chunks_ok rest (off - cb) n
      end
  end.

Fixpoint wf_first_seg (segs : list Segment) (lo hi : Z) : option Segment :=
  match segs with
  | [] => None
  | s :: rest =>
      let base := Z.of_N (seg_base s) in
      let top := (base + Z.of_N (seg_size s))%Z in
      if (Z.leb base lo && Z.leb hi top)%bool then Some s
      else if (Z.leb hi base || Z.leb top lo)%bool then wf_first_seg rest lo hi
      else None
  end.

Definition wseg_fast (segs : list Segment) (a : word) (n : nat) : bool :=
  (Z.ltb (bv_unsigned a + Z.of_nat n) (2 ^ 64) &&
   match wf_first_seg segs (bv_unsigned a) (bv_unsigned a + Z.of_nat n) with
   | Some seg => seg_writable seg && wf_chunks_ok (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) n
   | None => false
   end)%bool.

Lemma wf_hexc_lt : forall c, wf_hexc c = true -> (hex_nybble c <? 16)%N = true.
Proof.
  intros c H. unfold wf_hexc in H. (lazymatch goal with |- ?G => let G' := eval unfold hex_nybble in G in change_no_check G' end). apply N.ltb_lt.
  destruct (Uint63.leb 48%uint63 c && Uint63.leb c 57%uint63)%bool eqn:E1.
  - apply andb_true_iff in E1 as [E1 E2]. apply Uint63.leb_spec in E1, E2.
    change (Uint63.to_Z 48%uint63) with 48%Z in E1. change (Uint63.to_Z 57%uint63) with 57%Z in E2. lia.
  - cbn [orb] in H. rewrite H. apply andb_true_iff in H as [E3 E4]. apply Uint63.leb_spec in E3, E4.
    change (Uint63.to_Z 97%uint63) with 97%Z in E3. change (Uint63.to_Z 102%uint63) with 102%Z in E4. lia.
Qed.

Lemma wf_hex_ok_spec : forall n s j off,
  Uint63.to_Z j = (2 * Z.of_N off)%Z -> (2 * Z.of_N off + 2 * Z.of_nat n < Uint63.wB)%Z ->
  wf_hex_ok s j n = true -> forall i, (i < n)%nat -> exists b, hex_byte_at s (off + N.of_nat i)%N = Some b.
Proof.
  induction n as [|n IH]; intros s j off Hj Hw H i Hi; [lia|].
  cbn [wf_hex_ok] in H. apply andb_true_iff in H as [H Hrec]. apply andb_true_iff in H as [H Hlo].
  apply andb_true_iff in H as [Hlen Hhi]. pose proof (N2Z.is_nonneg off) as Hoff.
  destruct i as [|i].
  - rewrite N.add_0_r. (lazymatch goal with |- ?G => let G' := eval unfold hex_byte_at in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    assert (Ec : Uint63.of_Z (Z.of_N (2 * off)) = j).
    { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Hj, N2Z.inj_mul. apply Z.mod_small. lia. }
    assert (Ec1 : Uint63.of_Z (Z.of_N (2 * off + 1)) = Uint63.add j 1%uint63).
    { apply Uint63.to_Z_inj. rewrite Uint63.of_Z_spec, Uint63.add_spec, Hj. change (Uint63.to_Z 1%uint63) with 1%Z.
      rewrite N2Z.inj_add, N2Z.inj_mul. change (Z.of_N 2) with 2%Z. change (Z.of_N 1) with 1%Z.
      rewrite (Z.mod_small (2 * Z.of_N off + 1)%Z) by lia. reflexivity. }
    rewrite Ec, Ec1, Hlen. (lazymatch goal with |- ?G => let G' := eval cbn [orb] in G in change_no_check G' end). apply wf_hexc_lt in Hhi. apply wf_hexc_lt in Hlo. rewrite Hhi, Hlo. (lazymatch goal with |- ?G => let G' := eval cbn [andb] in G in change_no_check G' end).
    wd_eexists; reflexivity.
  - destruct (IH s (Uint63.add j 2%uint63) (off + 1)%N) with (i := i) as [b Hb]; [ | lia | exact Hrec | lia | ].
    + rewrite Uint63.add_spec, Hj. change (Uint63.to_Z 2%uint63) with 2%Z. rewrite N2Z.inj_add. rewrite Z.mod_small by lia. lia.
    + exists b. replace (off + N.of_nat (S i))%N with (off + 1 + N.of_nat i)%N by lia. exact Hb.
Qed.

Lemma wf_chunk_hex : forall c off k, (off + N.of_nat k <= wf_chunk_bytes c)%N ->
  wf_hex_ok c (Uint63.of_Z (Z.of_N (2 * off))) k = true -> forall i, (i < k)%nat -> exists b, hex_byte_at c (off + N.of_nat i)%N = Some b.
Proof.
  intros c off k Hk H. pose proof (Uint63.to_Z_bounded (PrimString.length c)) as HL. unfold wf_chunk_bytes in Hk.
  pose proof (N2Z.is_nonneg off) as Hoff.
  assert (Hk' : (Z.of_N off + Z.of_nat k <= Uint63.to_Z (PrimString.length c) / 2)%Z).
  { apply N2Z.inj_le in Hk. rewrite N2Z.inj_add, nat_N_Z, Z2N.id in Hk; [exact Hk|]. apply Z.div_pos; lia. }
  assert (H2 : (2 * (Uint63.to_Z (PrimString.length c) / 2) <= Uint63.to_Z (PrimString.length c))%Z) by (apply Z.mul_div_le; lia).
  apply (wf_hex_ok_spec k c (Uint63.of_Z (Z.of_N (2 * off))) off); [ | lia | exact H].
  rewrite Uint63.of_Z_spec, N2Z.inj_mul. apply Z.mod_small. change (Z.of_N 2) with 2%Z. lia.
Qed.

Lemma wf_chunks_ok_spec : forall cs off n, wf_chunks_ok cs off n = true ->
  forall i, (i < n)%nat -> exists b, segment_byte_at cs (off + N.of_nat i)%N = Some b.
Proof.
  induction cs as [|c rest IH]; intros off n H i Hi.
  - destruct n; [lia | discriminate H].
  - destruct n as [|n0]; [lia|]. cbn [wf_chunks_ok] in H. fold (wf_chunks_ok rest) in H.
    (lazymatch goal with |- ?G => let G' := eval cbn [segment_byte_at] in G in change_no_check G' end). fold (wf_chunk_bytes c).
    destruct (off <? wf_chunk_bytes c)%N eqn:Eo.
    + apply N.ltb_lt in Eo.
      destruct (Nat.leb (S n0) (N.to_nat (wf_chunk_bytes c - off))) eqn:El.
      * apply Nat.leb_le in El.
        assert (Ei : (off + N.of_nat i < wf_chunk_bytes c)%N) by lia.
        apply N.ltb_lt in Ei. rewrite Ei. exact (wf_chunk_hex c off (S n0) ltac:(lia) H i Hi).
      * apply Nat.leb_gt in El. apply andb_true_iff in H as [H1 H2].
        destruct (Nat.lt_ge_cases i (N.to_nat (wf_chunk_bytes c - off))) as [Hlt|Hge].
        -- assert (Ei : (off + N.of_nat i < wf_chunk_bytes c)%N) by lia.
           apply N.ltb_lt in Ei. rewrite Ei. exact (wf_chunk_hex c off (N.to_nat (wf_chunk_bytes c - off)) ltac:(lia) H1 i Hlt).
        -- assert (Ei : (off + N.of_nat i <? wf_chunk_bytes c)%N = false) by (apply N.ltb_ge; lia).
           rewrite Ei.
           destruct (IH 0%N (S n0 - N.to_nat (wf_chunk_bytes c - off))%nat H2 (i - N.to_nat (wf_chunk_bytes c - off))%nat ltac:(lia)) as [b Hb].
           exists b. replace (off + N.of_nat i - wf_chunk_bytes c)%N with (0 + N.of_nat (i - N.to_nat (wf_chunk_bytes c - off)))%N by lia. exact Hb.
    + apply N.ltb_ge in Eo.
      assert (Ei : (off + N.of_nat i <? wf_chunk_bytes c)%N = false) by (apply N.ltb_ge; lia).
      rewrite Ei. destruct (IH (off - wf_chunk_bytes c)%N (S n0) H i Hi) as [b Hb]. exists b.
      replace (off + N.of_nat i - wf_chunk_bytes c)%N with (off - wf_chunk_bytes c + N.of_nat i)%N by lia. exact Hb.
Qed.

Lemma wf_first_seg_find : forall segs lo hi seg, wf_first_seg segs lo hi = Some seg ->
  forall z, (lo <= z)%Z -> (z + 1 <= hi)%Z -> find_segment segs z 1 = Some seg.
Proof.
  induction segs as [|s rest IH]; intros lo hi seg H z H1 H2; [discriminate H|].
  cbn [wf_first_seg] in H. (lazymatch goal with |- ?G => let G' := eval cbn [find_segment] in G in change_no_check G' end).
  destruct (Z.leb (Z.of_N (seg_base s)) lo && Z.leb hi (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - injection H as <-. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    assert (F : (Z.leb (Z.of_N (seg_base s)) z && Z.leb (z + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool = true)
      by (apply andb_true_iff; split; apply Z.leb_le; lia).
    rewrite F. reflexivity.
  - destruct (Z.leb hi (Z.of_N (seg_base s)) || Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) lo)%bool eqn:E2; [|discriminate H].
    assert (F : (Z.leb (Z.of_N (seg_base s)) z && Z.leb (z + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool = false).
    { apply orb_true_iff in E2 as [E2|E2]; apply Z.leb_le in E2; apply andb_false_iff; [left | right]; apply Z.leb_gt; lia. }
    rewrite F. exact (IH lo hi seg H z H1 H2).
Qed.

Lemma wseg_ok_of_seg : forall segs seg n (a : word),
  (bv_unsigned a + Z.of_nat n < 2 ^ 64)%Z ->
  (forall z, (bv_unsigned a <= z)%Z -> (z < bv_unsigned a + Z.of_nat n)%Z -> find_segment segs z 1 = Some seg) ->
  seg_writable seg = true ->
  (forall i, (i < n)%nat -> exists b, segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)) + N.of_nat i)%N = Some b) ->
  (Z.of_N (seg_base seg) <= bv_unsigned a)%Z ->
  wseg_ok segs a n = true.
Proof.
  intros segs seg n. induction n as [|n IH]; intros a Hr Hf Hw Hb Hbase; [reflexivity|].
  (lazymatch goal with |- ?G => let G' := eval cbn [wseg_ok] in G in change_no_check G' end). rewrite (Hf (bv_unsigned a) ltac:(lia) ltac:(lia)).
  destruct (Hb 0%nat ltac:(lia)) as [b0 Hb0]. rewrite N.add_0_r in Hb0. rewrite Hb0, Hw. (lazymatch goal with |- ?G => let G' := eval cbn [andb] in G in change_no_check G' end).
  assert (Ua : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z).
  { rewrite bv_add_unsigned. rewrite bv_wrap_small; [reflexivity|]. pose proof (bv_unsigned_in_range 64 a).
    change (bv_unsigned (1%bv : bv 64)) with 1%Z. (lazymatch goal with |- ?G => let G' := eval unfold bv_modulus in G in change_no_check G' end). lia. }
  apply IH; rewrite ?Ua.
  - lia.
  - intros z H1 H2. apply Hf; lia.
  - exact Hw.
  - intros i Hi. destruct (Hb (S i) ltac:(lia)) as [b Hbi]. exists b.
    replace (Z.to_N (bv_unsigned a + 1 - Z.of_N (seg_base seg)) + N.of_nat i)%N
      with (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)) + N.of_nat (S i))%N by lia. exact Hbi.
  - lia.
Qed.

Lemma wseg_fast_ok : forall segs a n, wseg_fast segs a n = true -> wseg_ok segs a n = true.
Proof.
  intros segs a n H. unfold wseg_fast in H. apply andb_true_iff in H as [Hr H]. apply Z.ltb_lt in Hr.
  destruct (wf_first_seg segs (bv_unsigned a) (bv_unsigned a + Z.of_nat n)) as [seg|] eqn:E; [|discriminate H].
  apply andb_true_iff in H as [Hw Hc].
  destruct n as [|n0]; [reflexivity|].
  assert (Hbase : (Z.of_N (seg_base seg) <= bv_unsigned a)%Z).
  { clear - E. revert E. generalize (bv_unsigned a + Z.of_nat (S n0))%Z as hi. intros hi E.
    induction segs as [|s rest IH]; [discriminate E|]. cbn [wf_first_seg] in E.
    destruct (Z.leb (Z.of_N (seg_base s)) (bv_unsigned a) && Z.leb hi (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:F.
    - injection E as <-. apply andb_true_iff in F as [F1 _]. apply Z.leb_le in F1. exact F1.
    - destruct (_ || _)%bool; [exact (IH E) | discriminate E]. }
  apply (wseg_ok_of_seg segs seg); [exact Hr | | exact Hw | | exact Hbase].
  - intros z H1 H2. apply (wf_first_seg_find segs _ _ seg E z); lia.
  - exact (wf_chunks_ok_spec _ _ _ Hc).
Qed.
(* [comment removed for export] *)

Lemma sok_iaflag : forall m, store_ok BSEGS m (Z_to_bv 64 0x19dc48) 4 = true.
Proof. intros m. apply store_ok_wseg. vm_cast_no_check (eq_refl true). Qed.
Lemma wseg_arena : wseg_ok BSEGS (Z_to_bv 64 0x10f3c0) (Z.to_nat 0x81030) = true.
Proof. apply wseg_fast_ok. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)
Lemma sok_arena : forall m (a : word) n, 0x10f3c0 <= bv_unsigned a -> 0 <= n -> bv_unsigned a + n <= 0x10f3c0 + 0x81030 ->
  store_ok BSEGS m a (Z.to_nat n) = true.
Proof.
  intros m a n H1 H2 H3.
  apply (store_ok_window BSEGS m (Z_to_bv 64 0x10f3c0) a (Z.to_nat 0x81030) (Z.to_nat n) 0x10f3c0 (0x10f3c0 + 0x81030));
    [ reflexivity | rewrite Z2Nat.id by lia; reflexivity | lia | exact wseg_arena | exact H1 | rewrite Z2Nat.id by lia; exact H3 ].
Qed.
End BoAllocF0w.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits BoAllocF0 BoAllocF0w OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_7ab0c_7b3f4.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI.   (* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation ZF n := (repeat (Z_to_bv 8 0) (Z.to_nat n)).

(* [comment removed for export] *)
Ltac fsb F D aa bb :=
  chain_step; [reflexivity
    | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [reflexivity | apply bv_eq; unorm; reflexivity]
      | first [stk_ok | hyp_ok | apply (sok_arena _ _ 1); wd_ulia | eapply (store_ok_sub BSEGS _ (Z_to_bv 64 0x19dc48) _ 4); [wd_ulia | apply sok_iaflag | wd_ulia | wd_ulia_c] ] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Ltac fsda F D aa :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [stk_ok | hyp_ok | apply (sok_arena _ _ 8); wd_ulia] ]
    | step_simpl]; vn.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma ialloc_lock_7aef4 {fx : FPState} : forall regs mem rom (v : word) b0 b2 b3,
  getr regs 13 = Z_to_bv 64 0x19dc48 -> getr regs 11 = Z_to_bv 64 0xff00 -> getr regs 12 = Z_to_bv 64 0x100 ->
  rdn BSEGS mem (Z_to_bv 64 0x19dc48) 4%nat = Some [b0; Z_to_bv 8 0; b2; b3] -> bytes_le_to_Z [b0; Z_to_bv 8 0; b2; b3] = bv_unsigned v ->
  msteps BSEGS (mkst regs (0x7aef4 : word) mem rom)
    (mkst (regupd (regupd regs 15 (v_lw v)) 16 (Z_to_bv 64 0)) (0x7af10 : word)
          (wbytes mem (Z_to_bv 64 0x19dc48) [b0; Z_to_bv 8 1; b2; b3]) rom).
Proof.
  intros regs mem rom v b0 b2 b3 H13 H11 H12 Hrd Hv.
  pose proof (xchg_byte_run BSEGS regs (0x7aef4 : word) (0x7aef8 : word) (0x7aefc : word) (0x7af00 : word)
                (0x7af04 : word) (0x7af08 : word) (0x7af0c : word) (0x7af10 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 15 13 16 12 11 _ [b0; Z_to_bv 8 0; b2; b3] v 1%nat 1%Z
                F_7aef4 eq_refl D_7aef4 F_7aef8 eq_refl D_7aef8 F_7aefc eq_refl D_7aefc F_7af00 eq_refl D_7af00
                F_7af04 eq_refl D_7af04 F_7af08 eq_refl D_7af08 F_7af0c eq_refl D_7af0c) as R.
  rewrite H13, H11, H12 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_iaflag | unorm; reflexivity | lia | assumption].
Qed.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_i1 (mem : word -> option byte) (S p ra s3 : word) (b2 b3 : byte) : word -> option byte :=
  wbytes (fr_ia mem S p ra s3) (Z_to_bv 64 0x19dc48) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3].
Hint Unfold fr_i1 : asfr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BLK_I1.
  Variables (mem rom : word -> option byte) (S ra p s3 : word) (regs : bvmap 5 word) (b2 b3 : byte) (vw : word).
  Hypothesis H1 : getr regs 1 = (0x6eda0 : word).
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H18 : getr regs 18 = ra.
  Hypothesis H19 : getr regs 19 = s3.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2176)) 2176 = true.
  Hypothesis Rflag1 : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rflagw : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3].
  Hypothesis Hvw : bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3] = bv_unsigned vw.

  Lemma blk_i1 :
    exists r,
      msteps BSEGS (mkst regs (0x7aea8 : word) mem rom) (mkst r (0x809a8 : word) (fr_i1 mem S p ra s3 b2 b3) rom)
      /\ getr r 1 = Z_to_bv 64 0x7af44 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = Z_to_bv 64 0x19dc48 /\ getr r 9 = Z_to_bv 64 0x10f3c0
      /\ getr r 10 = Z_to_bv 64 0x1903c8 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 40
      /\ getr r 18 = ra /\ getr r 19 = s3
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hvw Rflagw Rflag1 Hstk HS H19 H18 H9 H8 H2 H1 vw.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - an F_7aea8 D_7aea8.                              (* [comment removed for export] *)
      fsd F_7aeac D_7aeac (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_7aeb0 D_7aeb0 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_7aeb4 D_7aeb4 (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_7aeb8 D_7aeb8 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_7aebc D_7aebc (at_ S (-2168)).             (* [comment removed for export] *)
      an F_7aec0 D_7aec0.                              (* [comment removed for export] *)
      an F_7aec4 D_7aec4.                              (* [comment removed for export] *)
      clb F_7aec8 D_7aec8 (Z_to_bv 8 0) Rflag1.        (* [comment removed for export] *)
      afence F_7aecc D_7aecc.                          (* [comment removed for export] *)
      ab_ft F_7aed0 D_7aed0 ltac:(condz).              (* [comment removed for export] *)
      an F_7aed4 D_7aed4.                              (* [comment removed for export] *)
      an F_7aed8 D_7aed8.                              (* [comment removed for export] *)
      an F_7aedc D_7aedc.                              (* [comment removed for export] *)
      av F_7aee0 D_7aee0 (Z_to_bv 64 0x19dc48) ltac:(valz).   (* [comment removed for export] *)
      av F_7aee4 D_7aee4 (Z_to_bv 64 1) ltac:(valz).          (* [comment removed for export] *)
      av F_7aee8 D_7aee8 (Z_to_bv 64 8) ltac:(valz).          (* [comment removed for export] *)
      an F_7aeec D_7aeec.                              (* [comment removed for export] *)
      an F_7aef0 D_7aef0.                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (ialloc_lock_7aef4 _ _ rom vw (Z_to_bv 8 0) b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
          | rd_addr Rflagw
          | exact Hvw ]
      | ].
      an F_7af10 D_7af10.                              (* [comment removed for export] *)
      av F_7af14 D_7af14 (Z_to_bv 64 0) ltac:(first [apply (lock_byte1_00 b2 b3 vw Hvw) | rewrite <- (lock_byte1_00 b2 b3 vw Hvw); reflexivity]).  (* [comment removed for export] *)
      ab_ft F_7af18 D_7af18 ltac:(condz).              (* [comment removed for export] *)
      lazymatch goal with |- msteps _ (mkst _ _ ?m _) _ =>
        assert (Rf2 : rdn BSEGS m (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 0]) by (apply rdn1_top; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); wd_ulia) end.
      clb F_7af1c D_7af1c (Z_to_bv 8 0) Rf2.           (* [comment removed for export] *)
      ab_ft F_7af20 D_7af20 ltac:(condz).              (* [comment removed for export] *)
      an F_7af24 D_7af24.                              (* [comment removed for export] *)
      an F_7af28 D_7af28.                              (* [comment removed for export] *)
      av F_7af2c D_7af2c (Z_to_bv 64 0x10f3c0) ltac:(valz).   (* [comment removed for export] *)
      av F_7af30 D_7af30 (Z_to_bv 64 0x81008) ltac:(valz).    (* [comment removed for export] *)
      av F_7af34 D_7af34 (Z_to_bv 64 0x1903c8) ltac:(valz).   (* [comment removed for export] *)
      an F_7af38 D_7af38.                              (* [comment removed for export] *)
      an F_7af3c D_7af3c.                              (* [comment removed for export] *)
      an F_7af40 D_7af40.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_i1 mem S p ra s3 b2 b3). wd_refl.
    - post.
  Qed.
End BLK_I1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BLK_I2.
  Variables (mem rom : word -> option byte) (S : word) (regs : bvmap 5 word).
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0x10f3c0.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Lemma blk_i2 :
    exists r,
      msteps BSEGS (mkst regs (0x7af44 : word) mem rom) (mkst r (0x809a8 : word) (wbytes mem (Z_to_bv 64 0x10f3c0) [Z_to_bv 8 0]) rom)
      /\ getr r 1 = Z_to_bv 64 0x7af5c /\ getr r 2 = at_ S (-2176) /\ getr r 8 = getr regs 8 /\ getr r 9 = Z_to_bv 64 0x10f3c0
      /\ getr r 10 = Z_to_bv 64 0x10f3c8 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 262144
      /\ getr r 18 = getr regs 18 /\ getr r 19 = Z_to_bv 64 262144
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using HS H9 H2.
    pose proof (u64_range S) as HSr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - fsb F_7af44 D_7af44 (Z_to_bv 64 0x10f3c0) (Z_to_bv 8 0).    (* [comment removed for export] *)
      av F_7af48 D_7af48 (Z_to_bv 64 0x10f3c8) ltac:(valz).   (* [comment removed for export] *)
      an F_7af4c D_7af4c.                              (* [comment removed for export] *)
      an F_7af50 D_7af50.                              (* [comment removed for export] *)
      an F_7af54 D_7af54.                              (* [comment removed for export] *)
      an F_7af58 D_7af58.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End BLK_I2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BLK_I3.
  Variables (mem rom : word -> option byte) (S : word) (regs : bvmap 5 word).
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0x10f3c0.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 262144.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Lemma blk_i3 :
    exists r,
      msteps BSEGS (mkst regs (0x7af5c : word) mem rom) (mkst r (0x809a8 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x7af74 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = getr regs 8 /\ getr r 9 = Z_to_bv 64 0x10f3c0
      /\ getr r 10 = Z_to_bv 64 0x14f400 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 3456
      /\ getr r 18 = getr regs 18 /\ getr r 19 = Z_to_bv 64 262144
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using HS H19 H9 H2.
    pose proof (u64_range S) as HSr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - av F_7af5c D_7af5c (Z_to_bv 64 0x40040) ltac:(valz).    (* [comment removed for export] *)
      av F_7af60 D_7af60 (Z_to_bv 64 0x14f400) ltac:(valz).   (* [comment removed for export] *)
      an F_7af64 D_7af64.                              (* [comment removed for export] *)
      av F_7af68 D_7af68 (Z_to_bv 64 3456) ltac:(valz).       (* [comment removed for export] *)
      an F_7af6c D_7af6c.                              (* [comment removed for export] *)
      an F_7af70 D_7af70.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End BLK_I3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BLK_I4.
  Variables (mem rom : word -> option byte) (S : word) (regs : bvmap 5 word).
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0x10f3c0.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 262144.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Lemma blk_i4 :
    exists r,
      msteps BSEGS (mkst regs (0x7af74 : word) mem rom) (mkst r (0x809a8 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x7af8c /\ getr r 2 = at_ S (-2176) /\ getr r 8 = getr regs 8 /\ getr r 9 = Z_to_bv 64 0x10f3c0
      /\ getr r 10 = Z_to_bv 64 0x150180 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 262728
      /\ getr r 18 = Z_to_bv 64 0x41000 /\ getr r 19 = Z_to_bv 64 262144
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using HS H19 H9 H2.
    pose proof (u64_range S) as HSr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - an F_7af74 D_7af74.                              (* [comment removed for export] *)
      av F_7af78 D_7af78 (Z_to_bv 64 0x40dc0) ltac:(valz).    (* [comment removed for export] *)
      av F_7af7c D_7af7c (Z_to_bv 64 0x150180) ltac:(valz).   (* [comment removed for export] *)
      av F_7af80 D_7af80 (Z_to_bv 64 262728) ltac:(valz).     (* [comment removed for export] *)
      an F_7af84 D_7af84.                              (* [comment removed for export] *)
      an F_7af88 D_7af88.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End BLK_I4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_i5 (mem : word -> option byte) (pgv : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 0x150180) (LE8 pgv))
    (Z_to_bv 64 0x150188) (LE8 (Z_to_bv 64 0x150190)))
    (Z_to_bv 64 0x19dc48) [Z_to_bv 8 1])
    (Z_to_bv 64 0x19dc49) [Z_to_bv 8 0].
Hint Unfold fr_i5 : asfr.
Section BLK_I5.
  Variables (mem rom : word -> option byte) (S ra p s3 : word) (regs : bvmap 5 word) (PGP : Z) (pgv : word) (q32 : Z).
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0x19dc48.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0x10f3c0.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 0x41000.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (bv_unsigned p < 2 ^ 47)%Z.
  Hypothesis Hq32 : (bv_unsigned p / 2 ^ 32)%Z = q32.
  Hypothesis Hq32b : (0 <= q32 < 2 ^ 15)%Z.
  Hypothesis Hq47 : (bv_unsigned p / 2 ^ 47 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis C36 : rdn BSEGS mem (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6eda0)).
  Hypothesis C44 : rdn BSEGS mem (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C52 : rdn BSEGS mem (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C60 : rdn BSEGS mem (at_ S (-2160)) 8 = Some (LE8 ra).
  Hypothesis C68 : rdn BSEGS mem (at_ S (-2168)) 8 = Some (LE8 s3).
  (* [comment removed for export] *)
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 pgv).
  Hypothesis Hpgv : bv_unsigned pgv <> 0%Z.
  (* [comment removed for export] *)
  Hypothesis Rz : rdn BSEGS mem (Z_to_bv 64 (0x10f3c8 + 8 * q32)) 8 = Some (LE8 (Z_to_bv 64 0)).

  Lemma blk_i5 :
    exists r,
      msteps BSEGS (mkst regs (0x7af8c : word) mem rom) (mkst r (0x6ee44 : word) (fr_i5 mem pgv) rom)
      /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p /\ getr r 18 = ra
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rz Hpgv Rpg HPGP Rgpg C68 C60 C52 C44 C36 Hq47 Hq32b Hq32 HS H18 H9 H8 H2 q32 PGP s3.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - an F_7af8c D_7af8c.                              (* [comment removed for export] *)
      cld8 F_7af90 D_7af90 (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_7af94 D_7af94 pgv Rpg.                    (* [comment removed for export] *)
      ab_tk F_7af98 D_7af98 ltac:(condz).              (* [comment removed for export] *)
      av F_7afa4 D_7afa4 (Z_to_bv 64 0x1503c0) ltac:(valz).   (* [comment removed for export] *)
      av F_7afa8 D_7afa8 (Z_to_bv 64 0x40dd0) ltac:(valz).    (* [comment removed for export] *)
      av F_7afac D_7afac (Z_to_bv 64 0x150190) ltac:(valz).   (* [comment removed for export] *)
      an F_7afb0 D_7afb0.                              (* [comment removed for export] *)
      fsda F_7afb4 D_7afb4 (Z_to_bv 64 0x150180).      (* [comment removed for export] *)
      fsda F_7afb8 D_7afb8 (Z_to_bv 64 0x150188).      (* [comment removed for export] *)
      afence F_7afbc D_7afbc.                          (* [comment removed for export] *)
      fsb F_7afc0 D_7afc0 (Z_to_bv 64 0x19dc48) (Z_to_bv 8 1).   (* [comment removed for export] *)
      afence F_7afc4 D_7afc4.                          (* [comment removed for export] *)
      fsb F_7afc8 D_7afc8 (Z_to_bv 64 0x19dc49) (Z_to_bv 8 0).   (* [comment removed for export] *)
      an F_7afcc D_7afcc.                              (* [comment removed for export] *)
      an F_7afd0 D_7afd0.                              (* [comment removed for export] *)
      cld8 F_7afd4 D_7afd4 (Z_to_bv 64 0x6eda0) C36.   (* [comment removed for export] *)
      cld8 F_7afd8 D_7afd8 S C44.                      (* [comment removed for export] *)
      cld8 F_7afdc D_7afdc p C52.                      (* [comment removed for export] *)
      cld8 F_7afe0 D_7afe0 ra C60.                     (* [comment removed for export] *)
      cld8 F_7afe4 D_7afe4 s3 C68.                     (* [comment removed for export] *)
      an F_7afe8 D_7afe8.                              (* [comment removed for export] *)
      rt F_7afec D_7afec.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      av F_6eda0 D_6eda0 (Z_to_bv 64 0) ltac:(valz).                                   (* [comment removed for export] *)
      ab_ft F_6eda4 D_6eda4 ltac:(condz).                                             (* [comment removed for export] *)
      av F_6eda8 D_6eda8 (Z_to_bv 64 q32) ltac:(valz).                                 (* [comment removed for export] *)
      av F_6edac D_6edac (Z_to_bv 64 (8 * q32)) ltac:(valz).                           (* [comment removed for export] *)
      av F_6edb0 D_6edb0 (Z_to_bv 64 (0x10f3c0 + 8 * q32)) ltac:(valz).                (* [comment removed for export] *)
      cld8 F_6edb4 D_6edb4 (Z_to_bv 64 0) Rz.                                         (* [comment removed for export] *)
      afence F_6edb8 D_6edb8.                                                         (* [comment removed for export] *)
      ab_tk F_6edbc D_6edbc ltac:(condz).                                             (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_i5 mem pgv). wd_refl.
    - post.
  Qed.
End BLK_I5.


(* [comment removed for export] *)
Definition fr_ia0 (mem : word -> option byte) (S p ra s3 : word) (b2 b3 : byte) (pgv : word) (n1 n2 n3 n4 : Z) : word -> option byte :=
  fr_i5 (wbytes (wbytes (wbytes (wbytes (wbytes (fr_i1 mem S p ra s3 b2 b3)
    (Z_to_bv 64 0x1903c8) (ZF n1))
    (Z_to_bv 64 0x10f3c0) [Z_to_bv 8 0])
    (Z_to_bv 64 0x10f3c8) (ZF n2))
    (Z_to_bv 64 0x14f400) (ZF n3))
    (Z_to_bv 64 0x150180) (ZF n4)) pgv.

Section P1I.
  Variables (mem rom : word -> option byte) (S ra p s3 : word) (regs : bvmap 5 word) (b2 b3 : byte) (vw : word).
  Variables (PGP : Z) (pgv : word) (n1 n2 n3 n4 q32 : Z).
  Hypothesis En1 : n1 = 40%Z.
  Hypothesis En2 : n2 = 262144%Z.
  Hypothesis En3 : n3 = 3456%Z.
  Hypothesis En4 : n4 = 262728%Z.
  Hypothesis H1 : getr regs 1 = (0x6eda0 : word).
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H18 : getr regs 18 = ra.
  Hypothesis H19 : getr regs 19 = s3.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (bv_unsigned p < 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2176)) 2176 = true.
  Hypothesis Rflag1 : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rflagw : rdn BSEGS mem (Z_to_bv 64 0x19dc48) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3].
  Hypothesis Hvw : bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3] = bv_unsigned vw.
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI /\ (PGP + 8 <= 0x10f3c0 \/ 0x10f3c0 + 0x81030 <= PGP) /\ (PGP + 8 <= 0x19dc48 \/ 0x19dc4c <= PGP))%Z.
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 pgv).
  Hypothesis Hpgv : bv_unsigned pgv <> 0%Z.
  Hypothesis Hq32 : (bv_unsigned p / 2 ^ 32)%Z = q32.
  Hypothesis Hq32b : (0 <= q32 < 2 ^ 15)%Z.
  Hypothesis Hq47 : (bv_unsigned p / 2 ^ 47 = 0)%Z.

  #[local] Abbreviation MI := (fr_ia0 mem S p ra s3 b2 b3 pgv n1 n2 n3 n4).

  Lemma p1_blkA0 :
    exists r,
      msteps BSEGS (mkst regs (0x7aea8 : word) mem rom) (mkst r (0x6ee44 : word) MI rom)
      /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p /\ getr r 18 = ra
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hq47 Hq32b Hq32 Hpgv Rpg HPGP Rgpg Hvw Rflagw Rflag1 Hstk HS H19 H18 H9 H8 H2 H1 En4 En3 En2 En1 q32 PGP vw.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. pose proof HS as [HS1 HS2].
    Ltac carry AG B r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)); exact B.
    Ltac mset M a n rr ret A1 A10 A11 A12 En :=
      destruct (both_imemset M (Z_to_bv 64 a) (Z_to_bv 64 0) n rom rr (Z_to_bv 64 ret)) as (?rN & ?RUNN & ?AGN);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact A1 | exact A10 | exact A11 | rewrite A12, En; reflexivity | ].
    (* [comment removed for export] *)
    destruct (blk_i1 mem rom S ra p s3 regs b2 b3 vw H1 H2 H8 H9 H18 H19 HS Hstk Rflag1 Rflagw Hvw)
      as (r1 & RUN1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A18 & A19 & A4 & A3 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    set (M1 := fr_i1 mem S p ra s3 b2 b3) in RUN1.
    (* [comment removed for export] *)
    destruct (both_imemset M1 (Z_to_bv 64 0x1903c8) (Z_to_bv 64 0) n1 rom r1 (Z_to_bv 64 0x7af44)) as (r2 & RUN2 & AG2);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact A1 | exact A10 | exact A11 | rewrite A12, En1; reflexivity | ].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in RUN2.
    set (M2 := wbytes M1 (Z_to_bv 64 0x1903c8) (ZF n1)) in RUN2.
    assert (B2 : getr r2 2 = at_ S (-2176)) by carry AG2 A2 (2:reg).
    assert (B9 : getr r2 9 = Z_to_bv 64 0x10f3c0) by carry AG2 A9 (9:reg).
    (* [comment removed for export] *)
    destruct (blk_i2 M2 rom S r2 B2 B9 HS) as (r3 & RUN3 & C1 & C2 & C8 & C9 & C10 & C11 & C12 & C18 & C19 & C4 & C3 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
    set (M3 := wbytes M2 (Z_to_bv 64 0x10f3c0) [Z_to_bv 8 0]) in RUN3.
    (* [comment removed for export] *)
    destruct (both_imemset M3 (Z_to_bv 64 0x10f3c8) (Z_to_bv 64 0) n2 rom r3 (Z_to_bv 64 0x7af5c)) as (r4 & RUN4 & AG4);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact C1 | exact C10 | exact C11 | rewrite C12, En2; reflexivity | ].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in RUN4.
    set (M4 := wbytes M3 (Z_to_bv 64 0x10f3c8) (ZF n2)) in RUN4.
    assert (D2 : getr r4 2 = at_ S (-2176)) by carry AG4 C2 (2:reg).
    assert (D9 : getr r4 9 = Z_to_bv 64 0x10f3c0) by carry AG4 C9 (9:reg).
    assert (D19 : getr r4 19 = Z_to_bv 64 262144) by carry AG4 C19 (19:reg).
    (* [comment removed for export] *)
    destruct (blk_i3 M4 rom S r4 D2 D9 D19 HS) as (r5 & RUN5 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E4 & E3 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
    (* [comment removed for export] *)
    destruct (both_imemset M4 (Z_to_bv 64 0x14f400) (Z_to_bv 64 0) n3 rom r5 (Z_to_bv 64 0x7af74)) as (r6 & RUN6 & AG6);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact E1 | exact E10 | exact E11 | rewrite E12, En3; reflexivity | ].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in RUN6.
    set (M5 := wbytes M4 (Z_to_bv 64 0x14f400) (ZF n3)) in RUN6.
    assert (F2' : getr r6 2 = at_ S (-2176)) by carry AG6 E2 (2:reg).
    assert (F9' : getr r6 9 = Z_to_bv 64 0x10f3c0) by carry AG6 E9 (9:reg).
    assert (F19' : getr r6 19 = Z_to_bv 64 262144) by carry AG6 E19 (19:reg).
    (* [comment removed for export] *)
    destruct (blk_i4 M5 rom S r6 F2' F9' F19' HS) as (r7 & RUN7 & G1 & G2 & G8 & G9 & G10 & G11 & G12 & G18 & G19 & G4 & G3 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    (* [comment removed for export] *)
    destruct (both_imemset M5 (Z_to_bv 64 0x150180) (Z_to_bv 64 0) n4 rom r7 (Z_to_bv 64 0x7af8c)) as (r8 & RUN8 & AG8);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact G1 | exact G10 | exact G11 | rewrite G12, En4; reflexivity | ].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in RUN8.
    set (M6 := wbytes M5 (Z_to_bv 64 0x150180) (ZF n4)) in RUN8.
    assert (K2 : getr r8 2 = at_ S (-2176)) by carry AG8 G2 (2:reg).
    assert (K8 : getr r8 8 = Z_to_bv 64 0x19dc48).
    { rewrite (AG8 (8:reg) ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), G8, (AG6 (8:reg) ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), E8,
              (AG4 (8:reg) ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), C8, (AG2 (8:reg) ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)). exact A8. }
    assert (K9 : getr r8 9 = Z_to_bv 64 0x10f3c0) by carry AG8 G9 (9:reg).
    assert (K18 : getr r8 18 = Z_to_bv 64 0x41000) by carry AG8 G18 (18:reg).
    (* [comment removed for export] *)
    assert (OUT : forall x : word, ((U x < 0x10f3c0)%Z \/ (0x10f3c0 + 0x81030 <= U x)%Z) -> (U x + 1 <= 0x19dc48 \/ 0x19dc4c <= U x)%Z ->
                  (U x < U S - 2176 \/ U S - 2128 <= U x)%Z -> M6 x = mem x).
    { intros x X1 X2 X3. (lazymatch goal with |- ?G => let G' := eval unfold M6, M5, M4, M3, M2, M1, fr_i1, fr_ia in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; unorm; try lia.
      reflexivity. }
    Ltac xo OUT H := eapply rd_same; [ intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    assert (FR : forall k v, (-2168 <= k <= -2136)%Z ->
                 rdn BSEGS (fr_ia mem S p ra s3) (at_ S k) 8 = Some (LE8 v) -> rdn BSEGS M6 (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hk Hr. (lazymatch goal with |- ?G => let G' := eval unfold M6, M5, M4, M3, M2, M1, fr_i1 in G in change_no_check G' end).
      repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]). exact Hr. }
    assert (C36 : rdn BSEGS M6 (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6eda0))).
    { apply FR; [lia|]. replace (Z_to_bv 64 0x6eda0 : word) with (0x6eda0 : word) by (apply bv_eq; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end). rd8_chain. }
    assert (C44 : rdn BSEGS M6 (at_ S (-2144)) 8 = Some (LE8 S)) by (apply FR; [lia | (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end); rd8_chain]).
    assert (C52 : rdn BSEGS M6 (at_ S (-2152)) 8 = Some (LE8 p)) by (apply FR; [lia | (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end); rd8_chain]).
    assert (C60 : rdn BSEGS M6 (at_ S (-2160)) 8 = Some (LE8 ra)) by (apply FR; [lia | (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end); rd8_chain]).
    assert (C68 : rdn BSEGS M6 (at_ S (-2168)) 8 = Some (LE8 s3)) by (apply FR; [lia | (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end); rd8_chain]).
    assert (Rgpg6 : rdn BSEGS M6 (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP))) by xo OUT Rgpg.
    assert (Rpg6 : rdn BSEGS M6 (Z_to_bv 64 PGP) 8 = Some (LE8 pgv)) by xo OUT Rpg.
    assert (Rz6 : rdn BSEGS M6 (Z_to_bv 64 (0x10f3c8 + 8 * q32)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { (lazymatch goal with |- ?G => let G' := eval unfold M6, M5 in G in change_no_check G' end). repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]). (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end).
      replace (0x10f3c8 + 8 * q32)%Z with (bv_unsigned (Z_to_bv 64 0x10f3c8 : word) + 8 * q32)%Z by (wd_ulia).
      apply rdn8_in_fill; wd_ulia. }
    (* [comment removed for export] *)
    destruct (blk_i5 M6 rom S ra p s3 r8 PGP pgv q32 K2 K8 K9 K18 HS Hq32 Hq32b Hq47 C36 C44 C52 C60 C68 Rgpg6 ltac:(lia) Rpg6 Hpgv Rz6)
      as (r9 & RUN9 & L2 & L8 & L9 & L18 & L4 & L3 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
    exists r9. split.
    { replace (Z_to_bv 64 0x7af44 : word) with (0x7af44 : word) in RUN2 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x7af5c : word) with (0x7af5c : word) in RUN4 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x7af74 : word) with (0x7af74 : word) in RUN6 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x7af8c : word) with (0x7af8c : word) in RUN8 by (apply bv_eq; reflexivity).
      change both_imemset_entry with (0x809a8 : word) in RUN2, RUN4, RUN6, RUN8.
      subst M6 M5 M4 M3 M2 M1.
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|]. exact RUN9. }
    Ltac back AG8 G AG6 E AG4 C AG2 A r :=
      rewrite (AG8 r ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), G, (AG6 r ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), E,
              (AG4 r ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), C, (AG2 r ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)); exact A.
    split; [exact L2|]. split; [exact L8|]. split; [exact L9|]. split; [exact L18|].
    split; [rewrite L4; back AG8 G4 AG6 E4 AG4 C4 AG2 A4 (4:reg)|].
    split; [rewrite L3; back AG8 G3 AG6 E3 AG4 C3 AG2 A3 (3:reg)|].
    split; [rewrite L20; back AG8 G20 AG6 E20 AG4 C20 AG2 A20 (20:reg)|].
    split; [rewrite L21; back AG8 G21 AG6 E21 AG4 C21 AG2 A21 (21:reg)|].
    split; [rewrite L22; back AG8 G22 AG6 E22 AG4 C22 AG2 A22 (22:reg)|].
    split; [rewrite L23; back AG8 G23 AG6 E23 AG4 C23 AG2 A23 (23:reg)|].
    split; [rewrite L24; back AG8 G24 AG6 E24 AG4 C24 AG2 A24 (24:reg)|].
    split; [rewrite L25; back AG8 G25 AG6 E25 AG4 C25 AG2 A25 (25:reg)|].
    split; [rewrite L26; back AG8 G26 AG6 E26 AG4 C26 AG2 A26 (26:reg)|].
    rewrite L27; back AG8 G27 AG6 E27 AG4 C27 AG2 A27 (27:reg).
  Qed.
End P1I.

End FPGen1.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocF0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.

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
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-56)) 56 = true.

  #[local] Abbreviation M1 := (fr_icpt mem S ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).

  Lemma icpt_pro :
    exists r,
      msteps ASEGS (mkst regs (0x6e2fc : word) mem rom) (mkst r (0x7a438 : word) M1 rom)
      /\ getr r 1 = (0x6e330 : word) /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p
      /\ getr r 18 = ra /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3 /\ getr r 19 = getr regs 19
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk HS H10 H2 H1.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_6e2f4 D_6e2f4.                              (* [comment removed for export] *)
      fsd F_6e2f8 D_6e2f8 (at_ S (-8)).                (* [comment removed for export] *)
      fsd F_6e2fc D_6e2fc (at_ S (-16)).               (* [comment removed for export] *)
      fsd F_6e300 D_6e300 (at_ S (-24)).               (* [comment removed for export] *)
      fsd F_6e304 D_6e304 (at_ S (-32)).               (* [comment removed for export] *)
      fsd F_6e308 D_6e308 (at_ S (-40)).               (* [comment removed for export] *)
      fsd F_6e30c D_6e30c (at_ S (-48)).               (* [comment removed for export] *)
      fsd F_6e310 D_6e310 (at_ S (-56)).               (* [comment removed for export] *)
      an F_6e314 D_6e314.                              (* [comment removed for export] *)
      an F_6e318 D_6e318.                              (* [comment removed for export] *)
      an F_6e31c D_6e31c.                              (* [comment removed for export] *)
      an F_6e320 D_6e320.                              (* [comment removed for export] *)
      an F_6e324 D_6e324.                              (* [comment removed for export] *)
      wd_refl.
    - post. apply bv_eq; vm_compute; reflexivity.
  Qed.
End ICPTPRO.

(* [comment removed for export] *)
Definition fr_ia (M1 : word -> option byte) (S p ra s3 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes M1
    (at_ S (-2136)) (word_to_le_bytes 8 (0x6e330 : word)))
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
  Hypothesis H1 : getr regs 1 = (0x6e330 : word).
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H18 : getr regs 18 = ra.
  Hypothesis H19 : getr regs 19 = s3.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S)%Z.      (* [comment removed for export] *)
  Hypothesis HS16 : (bv_unsigned S mod 16 = 0)%Z.
  Hypothesis HShi : (bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (bv_unsigned p < 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2176)) 2176 = true.
  (* [comment removed for export] *)
  Hypothesis Rflag : rdn ASEGS mem (Z_to_bv 64 0x197008) 1 = Some [iab].
  Hypothesis Hiab : bv_unsigned iab <> 0%Z.
  Variable q32 : Z.                       (* [comment removed for export] *)
  Hypothesis Hq32 : (bv_unsigned p / 2 ^ 32)%Z = q32.
  Hypothesis Hq32b : (0 <= q32 < 2 ^ 15)%Z.
  Hypothesis Hq47 : (bv_unsigned p / 2 ^ 47 = 0)%Z.
  Hypothesis Rpim : rdn ASEGS mem (Z_to_bv 64 (0x108788 + 8 * q32)) 8 = Some pim.
  Hypothesis Hpim : bytes_le_to_Z pim = 0%Z.
  Hypothesis Rmcs : rdn ASEGS mem (Z_to_bv 64 0x10827c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 30)).
  Hypothesis Rgcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1990a8)).
  Hypothesis Rfum : rdn ASEGS mem (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].

  #[local] Abbreviation M2 := (fr_p1 mem S p ra s3).

  (* [comment removed for export] *)
  Lemma p1_blkA :
    exists r,
      msteps ASEGS (mkst regs (0x7a438 : word) mem rom) (mkst r (0x6e3d4 : word) (fr_ia mem S p ra s3) rom)
      /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p /\ getr r 18 = ra
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hpim Rpim Hq47 Hq32b Hq32 q32 Hiab Rflag Hstk HShi HS H19 H18 H9 H8 H2 H1 pim iab.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. pose proof (u_v_lb_nz iab Hiab) as Hiab'.
    wd_eexists. split.
    - (* [comment removed for export] *)
      an F_7a430 D_7a430.                              (* [comment removed for export] *)
      fsd F_7a434 D_7a434 (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_7a438 D_7a438 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_7a43c D_7a43c (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_7a440 D_7a440 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_7a444 D_7a444 (at_ S (-2168)).             (* [comment removed for export] *)
      an F_7a448 D_7a448.                              (* [comment removed for export] *)
      an F_7a44c D_7a44c.                              (* [comment removed for export] *)
      clb F_7a450 D_7a450 iab Rflag.                   (* [comment removed for export] *)
      afence F_7a454 D_7a454.                          (* [comment removed for export] *)
      ab_tk F_7a458 D_7a458 ltac:(condz).              (* [comment removed for export] *)
      an F_7a554 D_7a554.                              (* [comment removed for export] *)
      an F_7a558 D_7a558.                              (* [comment removed for export] *)
      fld F_7a55c D_7a55c (0x6e330 : word).            (* [comment removed for export] *)
      fld F_7a560 D_7a560 S.                           (* [comment removed for export] *)
      fld F_7a564 D_7a564 p.                           (* [comment removed for export] *)
      fld F_7a568 D_7a568 ra.                          (* [comment removed for export] *)
      fld F_7a56c D_7a56c s3.                          (* [comment removed for export] *)
      an F_7a570 D_7a570.                              (* [comment removed for export] *)
      rt F_7a574 D_7a574.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      av F_6e328 D_6e328 (Z_to_bv 64 0) ltac:(valz).                                   (* [comment removed for export] *)
      ab_ft F_6e32c D_6e32c ltac:(condz).                                             (* [comment removed for export] *)
      av F_6e330 D_6e330 (Z_to_bv 64 q32) ltac:(valz).                                 (* [comment removed for export] *)
      av F_6e334 D_6e334 (Z_to_bv 64 (8 * q32)) ltac:(valz).                           (* [comment removed for export] *)
      av F_6e338 D_6e338 (Z_to_bv 64 (0x108780 + 8 * q32)) ltac:(valz).                (* [comment removed for export] *)
      cld F_6e33c D_6e33c pim (Z_to_bv 64 0) Rpim Hpim.                               (* [comment removed for export] *)
      afence F_6e340 D_6e340.                                                         (* [comment removed for export] *)
      ab_tk F_6e344 D_6e344 ltac:(condz).                                             (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_ia mem S p ra s3). wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma p1_blkB : forall r0,
    getr r0 2 = at_ S (-2128) -> getr r0 8 = S -> getr r0 9 = p -> getr r0 18 = ra ->
    exists r,
      msteps ASEGS (mkst r0 (0x6e3d4 : word) (fr_ia mem S p ra s3) rom) (mkst r (0x76954 : word) M2 rom)
      /\ getr r 1 = Z_to_bv 64 0x6e490 /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p /\ getr r 18 = Z_to_bv 64 0x6e434
      /\ getr r 10 = at_ S (-2128) /\ getr r 11 = Z_to_bv 64 0x6e434 /\ getr r 12 = S /\ getr r 13 = Z_to_bv 64 0
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
    - (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end). an F_6e3cc D_6e3cc.                              (* [comment removed for export] *)
      an F_6e3d0 D_6e3d0.                              (* [comment removed for export] *)
      an F_6e3d4 D_6e3d4.                              (* [comment removed for export] *)
      an F_6e3d8 D_6e3d8.                              (* [comment removed for export] *)
      an F_6e3dc D_6e3dc.                              (* [comment removed for export] *)
      fsd F_6e3e0 D_6e3e0 (at_ S (-72)).               (* [comment removed for export] *)
      fsd F_6e3e4 D_6e3e4 (at_ S (-2128)).             (* [comment removed for export] *)
      fsd F_6e3e8 D_6e3e8 (at_ S (-2120)).             (* [comment removed for export] *)
      an F_6e3ec D_6e3ec.                              (* [comment removed for export] *)
      an F_7693c D_7693c.                              (* [comment removed for export] *)
      clw F_76940 D_76940 (word_to_le_bytes 4 (Z_to_bv 64 30)) (Z_to_bv 64 30) Rmcs bytes_le_to_Z_4_30.  (* [comment removed for export] *)
      afence F_76944 D_76944.                          (* [comment removed for export] *)
      rt F_76948 D_76948.                              (* [comment removed for export] *)
      an F_6e3f0 D_6e3f0.                              (* [comment removed for export] *)
      ab_tk F_6e3f4 D_6e3f4 ltac:(condz).              (* [comment removed for export] *)
      an F_6e428 D_6e428.                              (* [comment removed for export] *)
      an F_8f3fc D_8f3fc.                            (* [comment removed for export] *)
      rt F_8f400 D_8f400.                            (* [comment removed for export] *)
      an F_6e42c D_6e42c.                              (* [comment removed for export] *)
      cld F_6e430 D_6e430 (word_to_le_bytes 8 (Z_to_bv 64 0x1990a8)) (Z_to_bv 64 0x1990a8) Rgcf (bytes_le_to_Z_8 (Z_to_bv 64 0x1990a8)).  (* [comment removed for export] *)
      clbu F_6e434 D_6e434 (Z_to_bv 8 1) Rfum.         (* [comment removed for export] *)
      an F_6e438 D_6e438.                              (* [comment removed for export] *)
      an F_6e43c D_6e43c.                              (* [comment removed for export] *)
      an F_7693c D_7693c.                              (* [comment removed for export] *)
      clw F_76940 D_76940 (word_to_le_bytes 4 (Z_to_bv 64 30)) (Z_to_bv 64 30) Rmcs bytes_le_to_Z_4_30.  (* [comment removed for export] *)
      afence F_76944 D_76944.                          (* [comment removed for export] *)
      rt F_76948 D_76948.                              (* [comment removed for export] *)
      an F_6e440 D_6e440.                              (* [comment removed for export] *)
      an F_6e444 D_6e444.                              (* [comment removed for export] *)
      an F_6e448 D_6e448.                              (* [comment removed for export] *)
      an F_6e44c D_6e44c. rewrite v_and_m1_l.          (* [comment removed for export] *)
      an F_6e450 D_6e450.                              (* [comment removed for export] *)
      fsd F_6e454 D_6e454 (at_ S (-72)).               (* [comment removed for export] *)
      ab_tk F_6e458 D_6e458 ltac:(condz).              (* [comment removed for export] *)
      an F_6e46c D_6e46c.                              (* [comment removed for export] *)
      an F_6e470 D_6e470.                              (* [comment removed for export] *)
      an F_6e474 D_6e474.                              (* [comment removed for export] *)
      an F_6e478 D_6e478.                              (* [comment removed for export] *)
      an F_6e47c D_6e47c.                              (* [comment removed for export] *)
      an F_6e480 D_6e480.                              (* [comment removed for export] *)
      an F_6e484 D_6e484.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_p1 mem S p ra s3). wd_refl.
    - post.
  Qed.
End P1TAIL.
End FPGen1.
End AsAllocF0.
Require Stdlib.NArith.NArith Stdlib.Strings.PrimString Stdlib.Numbers.Cyclic.Int63.Uint63 Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocF0w.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.

Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.
Import OSSVerify.glaze.binary_reflection.images.Asan.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

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

Lemma sok_iaflag : forall m, store_ok ASEGS m (Z_to_bv 64 0x197008) 4 = true.
Proof. intros m. apply store_ok_wseg. vm_cast_no_check (eq_refl true). Qed.
Lemma wseg_arena : wseg_ok ASEGS (Z_to_bv 64 0x108780) (Z.to_nat 0x81038) = true.
Proof. apply wseg_fast_ok. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)
Lemma sok_arena : forall m (a : word) n, 0x108780 <= bv_unsigned a -> 0 <= n -> bv_unsigned a + n <= 0x108780 + 0x81038 ->
  store_ok ASEGS m a (Z.to_nat n) = true.
Proof.
  intros m a n H1 H2 H3.
  apply (store_ok_window ASEGS m (Z_to_bv 64 0x108780) a (Z.to_nat 0x81038) (Z.to_nat n) 0x108780 (0x108780 + 0x81038));
    [ reflexivity | rewrite Z2Nat.id by lia; reflexivity | lia | exact wseg_arena | exact H1 | rewrite Z2Nat.id by lia; exact H3 ].
Qed.
End AsAllocF0w.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocF0i.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFBits AsAllocF0 AsAllocF0w OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
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
      | first [stk_ok | hyp_ok | apply (sok_arena _ _ 1); wd_ulia | eapply (store_ok_sub ASEGS _ (Z_to_bv 64 0x197008) _ 4); [wd_ulia | apply sok_iaflag | wd_ulia | wd_ulia_c] ] ]
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
Lemma ialloc_lock_7a47c {fx : FPState} : forall regs mem rom (v : word) b0 b2 b3,
  getr regs 13 = Z_to_bv 64 0x197008 -> getr regs 11 = Z_to_bv 64 0xff00 -> getr regs 12 = Z_to_bv 64 0x100 ->
  rdn ASEGS mem (Z_to_bv 64 0x197008) 4%nat = Some [b0; Z_to_bv 8 0; b2; b3] -> bytes_le_to_Z [b0; Z_to_bv 8 0; b2; b3] = bv_unsigned v ->
  msteps ASEGS (mkst regs (0x7a484 : word) mem rom)
    (mkst (regupd (regupd regs 15 (v_lw v)) 16 (Z_to_bv 64 0)) (0x7a4a0 : word)
          (wbytes mem (Z_to_bv 64 0x197008) [b0; Z_to_bv 8 1; b2; b3]) rom).
Proof.
  intros regs mem rom v b0 b2 b3 H13 H11 H12 Hrd Hv.
  pose proof (xchg_byte_run ASEGS regs (0x7a484 : word) (0x7a488 : word) (0x7a48c : word) (0x7a490 : word)
                (0x7a494 : word) (0x7a498 : word) (0x7a49c : word) (0x7a4a0 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 15 13 16 12 11 _ [b0; Z_to_bv 8 0; b2; b3] v 1%nat 1%Z
                F_7a47c eq_refl D_7a47c F_7a480 eq_refl D_7a480 F_7a484 eq_refl D_7a484 F_7a488 eq_refl D_7a488
                F_7a48c eq_refl D_7a48c F_7a490 eq_refl D_7a490 F_7a494 eq_refl D_7a494) as R.
  rewrite H13, H11, H12 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_iaflag | unorm; reflexivity | lia | assumption].
Qed.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_i1 (mem : word -> option byte) (S p ra s3 : word) (b2 b3 : byte) : word -> option byte :=
  wbytes (fr_ia mem S p ra s3) (Z_to_bv 64 0x197008) [Z_to_bv 8 0; Z_to_bv 8 1; b2; b3].
Hint Unfold fr_i1 : asfr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BLK_I1.
  Variables (mem rom : word -> option byte) (S ra p s3 : word) (regs : bvmap 5 word) (b2 b3 : byte) (vw : word).
  Hypothesis H1 : getr regs 1 = (0x6e330 : word).
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H18 : getr regs 18 = ra.
  Hypothesis H19 : getr regs 19 = s3.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2176)) 2176 = true.
  Hypothesis Rflag1 : rdn ASEGS mem (Z_to_bv 64 0x197008) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rflagw : rdn ASEGS mem (Z_to_bv 64 0x197008) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3].
  Hypothesis Hvw : bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3] = bv_unsigned vw.

  Lemma blk_i1 :
    exists r,
      msteps ASEGS (mkst regs (0x7a438 : word) mem rom) (mkst r (0x7ff38 : word) (fr_i1 mem S p ra s3 b2 b3) rom)
      /\ getr r 1 = Z_to_bv 64 0x7a4d4 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = Z_to_bv 64 0x197008 /\ getr r 9 = Z_to_bv 64 0x108780
      /\ getr r 10 = Z_to_bv 64 0x189788 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 40
      /\ getr r 18 = ra /\ getr r 19 = s3
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hvw Rflagw Rflag1 Hstk HS H19 H18 H9 H8 H2 H1 vw.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - an F_7a430 D_7a430.                              (* [comment removed for export] *)
      fsd F_7a434 D_7a434 (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_7a438 D_7a438 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_7a43c D_7a43c (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_7a440 D_7a440 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_7a444 D_7a444 (at_ S (-2168)).             (* [comment removed for export] *)
      an F_7a448 D_7a448.                              (* [comment removed for export] *)
      an F_7a44c D_7a44c.                              (* [comment removed for export] *)
      clb F_7a450 D_7a450 (Z_to_bv 8 0) Rflag1.        (* [comment removed for export] *)
      afence F_7a454 D_7a454.                          (* [comment removed for export] *)
      ab_ft F_7a458 D_7a458 ltac:(condz).              (* [comment removed for export] *)
      an F_7a45c D_7a45c.                              (* [comment removed for export] *)
      an F_7a460 D_7a460.                              (* [comment removed for export] *)
      an F_7a464 D_7a464.                              (* [comment removed for export] *)
      av F_7a468 D_7a468 (Z_to_bv 64 0x197008) ltac:(valz).   (* [comment removed for export] *)
      av F_7a46c D_7a46c (Z_to_bv 64 1) ltac:(valz).          (* [comment removed for export] *)
      av F_7a470 D_7a470 (Z_to_bv 64 8) ltac:(valz).          (* [comment removed for export] *)
      an F_7a474 D_7a474.                              (* [comment removed for export] *)
      an F_7a478 D_7a478.                              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (ialloc_lock_7a47c _ _ rom vw (Z_to_bv 8 0) b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]
          | rd_addr Rflagw
          | exact Hvw ]
      | ].
      an F_7a498 D_7a498.                              (* [comment removed for export] *)
      av F_7a49c D_7a49c (Z_to_bv 64 0) ltac:(first [apply (lock_byte1_00 b2 b3 vw Hvw) | rewrite <- (lock_byte1_00 b2 b3 vw Hvw); reflexivity]).  (* [comment removed for export] *)
      ab_ft F_7a4a0 D_7a4a0 ltac:(condz).              (* [comment removed for export] *)
      lazymatch goal with |- msteps _ (mkst _ _ ?m _) _ =>
        assert (Rf2 : rdn ASEGS m (Z_to_bv 64 0x197008) 1 = Some [Z_to_bv 8 0]) by (apply rdn1_top; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); wd_ulia) end.
      clb F_7a4a4 D_7a4a4 (Z_to_bv 8 0) Rf2.           (* [comment removed for export] *)
      ab_ft F_7a4a8 D_7a4a8 ltac:(condz).              (* [comment removed for export] *)
      an F_7a4ac D_7a4ac.                              (* [comment removed for export] *)
      an F_7a4b0 D_7a4b0.                              (* [comment removed for export] *)
      av F_7a4b4 D_7a4b4 (Z_to_bv 64 0x108780) ltac:(valz).   (* [comment removed for export] *)
      av F_7a4b8 D_7a4b8 (Z_to_bv 64 0x81008) ltac:(valz).    (* [comment removed for export] *)
      av F_7a4bc D_7a4bc (Z_to_bv 64 0x189788) ltac:(valz).   (* [comment removed for export] *)
      an F_7a4c0 D_7a4c0.                              (* [comment removed for export] *)
      an F_7a4c4 D_7a4c4.                              (* [comment removed for export] *)
      an F_7a4c8 D_7a4c8.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_i1 mem S p ra s3 b2 b3). wd_refl.
    - post.
  Qed.
End BLK_I1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BLK_I2.
  Variables (mem rom : word -> option byte) (S : word) (regs : bvmap 5 word).
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0x108780.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Lemma blk_i2 :
    exists r,
      msteps ASEGS (mkst regs (0x7a4d4 : word) mem rom) (mkst r (0x7ff38 : word) (wbytes mem (Z_to_bv 64 0x108780) [Z_to_bv 8 0]) rom)
      /\ getr r 1 = Z_to_bv 64 0x7a4ec /\ getr r 2 = at_ S (-2176) /\ getr r 8 = getr regs 8 /\ getr r 9 = Z_to_bv 64 0x108780
      /\ getr r 10 = Z_to_bv 64 0x108788 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 262144
      /\ getr r 18 = getr regs 18 /\ getr r 19 = Z_to_bv 64 262144
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using HS H9 H2.
    pose proof (u64_range S) as HSr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - fsb F_7a4cc D_7a4cc (Z_to_bv 64 0x108780) (Z_to_bv 8 0).    (* [comment removed for export] *)
      av F_7a4d0 D_7a4d0 (Z_to_bv 64 0x108788) ltac:(valz).   (* [comment removed for export] *)
      an F_7a4d4 D_7a4d4.                              (* [comment removed for export] *)
      an F_7a4d8 D_7a4d8.                              (* [comment removed for export] *)
      an F_7a4dc D_7a4dc.                              (* [comment removed for export] *)
      an F_7a4e0 D_7a4e0.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End BLK_I2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BLK_I3.
  Variables (mem rom : word -> option byte) (S : word) (regs : bvmap 5 word).
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0x108780.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 262144.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Lemma blk_i3 :
    exists r,
      msteps ASEGS (mkst regs (0x7a4ec : word) mem rom) (mkst r (0x7ff38 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x7a504 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = getr regs 8 /\ getr r 9 = Z_to_bv 64 0x108780
      /\ getr r 10 = Z_to_bv 64 0x1487c0 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 3456
      /\ getr r 18 = getr regs 18 /\ getr r 19 = Z_to_bv 64 262144
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using HS H19 H9 H2.
    pose proof (u64_range S) as HSr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - av F_7a4e4 D_7a4e4 (Z_to_bv 64 0x40040) ltac:(valz).    (* [comment removed for export] *)
      av F_7a4e8 D_7a4e8 (Z_to_bv 64 0x1487c0) ltac:(valz).   (* [comment removed for export] *)
      an F_7a4ec D_7a4ec.                              (* [comment removed for export] *)
      av F_7a4f0 D_7a4f0 (Z_to_bv 64 3456) ltac:(valz).       (* [comment removed for export] *)
      an F_7a4f4 D_7a4f4.                              (* [comment removed for export] *)
      an F_7a4f8 D_7a4f8.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End BLK_I3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BLK_I4.
  Variables (mem rom : word -> option byte) (S : word) (regs : bvmap 5 word).
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0x108780.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 262144.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Lemma blk_i4 :
    exists r,
      msteps ASEGS (mkst regs (0x7a504 : word) mem rom) (mkst r (0x7ff38 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x7a51c /\ getr r 2 = at_ S (-2176) /\ getr r 8 = getr regs 8 /\ getr r 9 = Z_to_bv 64 0x108780
      /\ getr r 10 = Z_to_bv 64 0x149540 /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 262728
      /\ getr r 18 = Z_to_bv 64 0x41000 /\ getr r 19 = Z_to_bv 64 262144
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using HS H19 H9 H2.
    pose proof (u64_range S) as HSr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - an F_7a4fc D_7a4fc.                              (* [comment removed for export] *)
      av F_7a500 D_7a500 (Z_to_bv 64 0x40dc0) ltac:(valz).    (* [comment removed for export] *)
      av F_7a504 D_7a504 (Z_to_bv 64 0x149540) ltac:(valz).   (* [comment removed for export] *)
      av F_7a508 D_7a508 (Z_to_bv 64 262728) ltac:(valz).     (* [comment removed for export] *)
      an F_7a50c D_7a50c.                              (* [comment removed for export] *)
      an F_7a510 D_7a510.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End BLK_I4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_i5 (mem : word -> option byte) (pgv : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 0x149540) (LE8 pgv))
    (Z_to_bv 64 0x149548) (LE8 (Z_to_bv 64 0x149550)))
    (Z_to_bv 64 0x197008) [Z_to_bv 8 1])
    (Z_to_bv 64 0x197009) [Z_to_bv 8 0].
Hint Unfold fr_i5 : asfr.
Section BLK_I5.
  Variables (mem rom : word -> option byte) (S ra p s3 : word) (regs : bvmap 5 word) (PGP : Z) (pgv : word) (q32 : Z).
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0x197008.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 0x108780.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 0x41000.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (bv_unsigned p < 2 ^ 47)%Z.
  Hypothesis Hq32 : (bv_unsigned p / 2 ^ 32)%Z = q32.
  Hypothesis Hq32b : (0 <= q32 < 2 ^ 15)%Z.
  Hypothesis Hq47 : (bv_unsigned p / 2 ^ 47 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis C36 : rdn ASEGS mem (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e330)).
  Hypothesis C44 : rdn ASEGS mem (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C52 : rdn ASEGS mem (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C60 : rdn ASEGS mem (at_ S (-2160)) 8 = Some (LE8 ra).
  Hypothesis C68 : rdn ASEGS mem (at_ S (-2168)) 8 = Some (LE8 s3).
  (* [comment removed for export] *)
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI)%Z.
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 pgv).
  Hypothesis Hpgv : bv_unsigned pgv <> 0%Z.
  (* [comment removed for export] *)
  Hypothesis Rz : rdn ASEGS mem (Z_to_bv 64 (0x108788 + 8 * q32)) 8 = Some (LE8 (Z_to_bv 64 0)).

  Lemma blk_i5 :
    exists r,
      msteps ASEGS (mkst regs (0x7a51c : word) mem rom) (mkst r (0x6e3d4 : word) (fr_i5 mem pgv) rom)
      /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p /\ getr r 18 = ra
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rz Hpgv Rpg HPGP Rgpg C68 C60 C52 C44 C36 Hq47 Hq32b Hq32 HS H18 H9 H8 H2 q32 PGP s3.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HS as [HS1 HS2].
    wd_eexists. split.
    - an F_7a514 D_7a514.                              (* [comment removed for export] *)
      cld8 F_7a518 D_7a518 (Z_to_bv 64 PGP) Rgpg.      (* [comment removed for export] *)
      cld8 F_7a51c D_7a51c pgv Rpg.                    (* [comment removed for export] *)
      ab_tk F_7a520 D_7a520 ltac:(condz).              (* [comment removed for export] *)
      av F_7a52c D_7a52c (Z_to_bv 64 0x149780) ltac:(valz).   (* [comment removed for export] *)
      av F_7a530 D_7a530 (Z_to_bv 64 0x40dd0) ltac:(valz).    (* [comment removed for export] *)
      av F_7a534 D_7a534 (Z_to_bv 64 0x149550) ltac:(valz).   (* [comment removed for export] *)
      an F_7a538 D_7a538.                              (* [comment removed for export] *)
      fsda F_7a53c D_7a53c (Z_to_bv 64 0x149540).      (* [comment removed for export] *)
      fsda F_7a540 D_7a540 (Z_to_bv 64 0x149548).      (* [comment removed for export] *)
      afence F_7a544 D_7a544.                          (* [comment removed for export] *)
      fsb F_7a548 D_7a548 (Z_to_bv 64 0x197008) (Z_to_bv 8 1).   (* [comment removed for export] *)
      afence F_7a54c D_7a54c.                          (* [comment removed for export] *)
      fsb F_7a550 D_7a550 (Z_to_bv 64 0x197009) (Z_to_bv 8 0).   (* [comment removed for export] *)
      an F_7a554 D_7a554.                              (* [comment removed for export] *)
      an F_7a558 D_7a558.                              (* [comment removed for export] *)
      cld8 F_7a55c D_7a55c (Z_to_bv 64 0x6e330) C36.   (* [comment removed for export] *)
      cld8 F_7a560 D_7a560 S C44.                      (* [comment removed for export] *)
      cld8 F_7a564 D_7a564 p C52.                      (* [comment removed for export] *)
      cld8 F_7a568 D_7a568 ra C60.                     (* [comment removed for export] *)
      cld8 F_7a56c D_7a56c s3 C68.                     (* [comment removed for export] *)
      an F_7a570 D_7a570.                              (* [comment removed for export] *)
      rt F_7a574 D_7a574.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      av F_6e328 D_6e328 (Z_to_bv 64 0) ltac:(valz).                                   (* [comment removed for export] *)
      ab_ft F_6e32c D_6e32c ltac:(condz).                                             (* [comment removed for export] *)
      av F_6e330 D_6e330 (Z_to_bv 64 q32) ltac:(valz).                                 (* [comment removed for export] *)
      av F_6e334 D_6e334 (Z_to_bv 64 (8 * q32)) ltac:(valz).                           (* [comment removed for export] *)
      av F_6e338 D_6e338 (Z_to_bv 64 (0x108780 + 8 * q32)) ltac:(valz).                (* [comment removed for export] *)
      cld8 F_6e33c D_6e33c (Z_to_bv 64 0) Rz.                                         (* [comment removed for export] *)
      afence F_6e340 D_6e340.                                                         (* [comment removed for export] *)
      ab_tk F_6e344 D_6e344 ltac:(condz).                                             (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_i5 mem pgv). wd_refl.
    - post.
  Qed.
End BLK_I5.


(* [comment removed for export] *)
Definition fr_ia0 (mem : word -> option byte) (S p ra s3 : word) (b2 b3 : byte) (pgv : word) (n1 n2 n3 n4 : Z) : word -> option byte :=
  fr_i5 (wbytes (wbytes (wbytes (wbytes (wbytes (fr_i1 mem S p ra s3 b2 b3)
    (Z_to_bv 64 0x189788) (ZF n1))
    (Z_to_bv 64 0x108780) [Z_to_bv 8 0])
    (Z_to_bv 64 0x108788) (ZF n2))
    (Z_to_bv 64 0x1487c0) (ZF n3))
    (Z_to_bv 64 0x149540) (ZF n4)) pgv.

Section P1I.
  Variables (mem rom : word -> option byte) (S ra p s3 : word) (regs : bvmap 5 word) (b2 b3 : byte) (vw : word).
  Variables (PGP : Z) (pgv : word) (n1 n2 n3 n4 q32 : Z).
  Hypothesis En1 : n1 = 40%Z.
  Hypothesis En2 : n2 = 262144%Z.
  Hypothesis En3 : n3 = 3456%Z.
  Hypothesis En4 : n4 = 262728%Z.
  Hypothesis H1 : getr regs 1 = (0x6e330 : word).
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H18 : getr regs 18 = ra.
  Hypothesis H19 : getr regs 19 = s3.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (bv_unsigned p < 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2176)) 2176 = true.
  Hypothesis Rflag1 : rdn ASEGS mem (Z_to_bv 64 0x197008) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rflagw : rdn ASEGS mem (Z_to_bv 64 0x197008) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3].
  Hypothesis Hvw : bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3] = bv_unsigned vw.
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis HPGP : (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI /\ (PGP + 8 <= 0x108780 \/ 0x108780 + 0x81038 <= PGP) /\ (PGP + 8 <= 0x197008 \/ 0x19700c <= PGP))%Z.
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 pgv).
  Hypothesis Hpgv : bv_unsigned pgv <> 0%Z.
  Hypothesis Hq32 : (bv_unsigned p / 2 ^ 32)%Z = q32.
  Hypothesis Hq32b : (0 <= q32 < 2 ^ 15)%Z.
  Hypothesis Hq47 : (bv_unsigned p / 2 ^ 47 = 0)%Z.

  #[local] Abbreviation MI := (fr_ia0 mem S p ra s3 b2 b3 pgv n1 n2 n3 n4).

  Lemma p1_blkA0 :
    exists r,
      msteps ASEGS (mkst regs (0x7a438 : word) mem rom) (mkst r (0x6e3d4 : word) MI rom)
      /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p /\ getr r 18 = ra
      /\ getr r 4 = getr regs 4 /\ getr r 3 = getr regs 3
      /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23
      /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hq47 Hq32b Hq32 Hpgv Rpg HPGP Rgpg Hvw Rflagw Rflag1 Hstk HS H19 H18 H9 H8 H2 H1 En4 En3 En2 En1 q32 PGP vw.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. pose proof HS as [HS1 HS2].
    Ltac carry AG B r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)); exact B.
    Ltac mset M a n rr ret A1 A10 A11 A12 En :=
      destruct (asan_imemset M (Z_to_bv 64 a) (Z_to_bv 64 0) n rom rr (Z_to_bv 64 ret)) as (?rN & ?RUNN & ?AGN);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact A1 | exact A10 | exact A11 | rewrite A12, En; reflexivity | ].
    (* [comment removed for export] *)
    destruct (blk_i1 mem rom S ra p s3 regs b2 b3 vw H1 H2 H8 H9 H18 H19 HS Hstk Rflag1 Rflagw Hvw)
      as (r1 & RUN1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A18 & A19 & A4 & A3 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    set (M1 := fr_i1 mem S p ra s3 b2 b3) in RUN1.
    (* [comment removed for export] *)
    destruct (asan_imemset M1 (Z_to_bv 64 0x189788) (Z_to_bv 64 0) n1 rom r1 (Z_to_bv 64 0x7a4d4)) as (r2 & RUN2 & AG2);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact A1 | exact A10 | exact A11 | rewrite A12, En1; reflexivity | ].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in RUN2.
    set (M2 := wbytes M1 (Z_to_bv 64 0x189788) (ZF n1)) in RUN2.
    assert (B2 : getr r2 2 = at_ S (-2176)) by carry AG2 A2 (2:reg).
    assert (B9 : getr r2 9 = Z_to_bv 64 0x108780) by carry AG2 A9 (9:reg).
    (* [comment removed for export] *)
    destruct (blk_i2 M2 rom S r2 B2 B9 HS) as (r3 & RUN3 & C1 & C2 & C8 & C9 & C10 & C11 & C12 & C18 & C19 & C4 & C3 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
    set (M3 := wbytes M2 (Z_to_bv 64 0x108780) [Z_to_bv 8 0]) in RUN3.
    (* [comment removed for export] *)
    destruct (asan_imemset M3 (Z_to_bv 64 0x108788) (Z_to_bv 64 0) n2 rom r3 (Z_to_bv 64 0x7a4ec)) as (r4 & RUN4 & AG4);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact C1 | exact C10 | exact C11 | rewrite C12, En2; reflexivity | ].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in RUN4.
    set (M4 := wbytes M3 (Z_to_bv 64 0x108788) (ZF n2)) in RUN4.
    assert (D2 : getr r4 2 = at_ S (-2176)) by carry AG4 C2 (2:reg).
    assert (D9 : getr r4 9 = Z_to_bv 64 0x108780) by carry AG4 C9 (9:reg).
    assert (D19 : getr r4 19 = Z_to_bv 64 262144) by carry AG4 C19 (19:reg).
    (* [comment removed for export] *)
    destruct (blk_i3 M4 rom S r4 D2 D9 D19 HS) as (r5 & RUN5 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E4 & E3 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
    (* [comment removed for export] *)
    destruct (asan_imemset M4 (Z_to_bv 64 0x1487c0) (Z_to_bv 64 0) n3 rom r5 (Z_to_bv 64 0x7a504)) as (r6 & RUN6 & AG6);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact E1 | exact E10 | exact E11 | rewrite E12, En3; reflexivity | ].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in RUN6.
    set (M5 := wbytes M4 (Z_to_bv 64 0x1487c0) (ZF n3)) in RUN6.
    assert (F2' : getr r6 2 = at_ S (-2176)) by carry AG6 E2 (2:reg).
    assert (F9' : getr r6 9 = Z_to_bv 64 0x108780) by carry AG6 E9 (9:reg).
    assert (F19' : getr r6 19 = Z_to_bv 64 262144) by carry AG6 E19 (19:reg).
    (* [comment removed for export] *)
    destruct (blk_i4 M5 rom S r6 F2' F9' F19' HS) as (r7 & RUN7 & G1 & G2 & G8 & G9 & G10 & G11 & G12 & G18 & G19 & G4 & G3 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    (* [comment removed for export] *)
    destruct (asan_imemset M5 (Z_to_bv 64 0x149540) (Z_to_bv 64 0) n4 rom r7 (Z_to_bv 64 0x7a51c)) as (r8 & RUN8 & AG8);
      [ lia | wd_ulia | apply sok_arena; wd_ulia | intros _ _; wd_ulia
      | apply ret_ok_lit; [lia | reflexivity] | exact G1 | exact G10 | exact G11 | rewrite G12, En4; reflexivity | ].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in RUN8.
    set (M6 := wbytes M5 (Z_to_bv 64 0x149540) (ZF n4)) in RUN8.
    assert (K2 : getr r8 2 = at_ S (-2176)) by carry AG8 G2 (2:reg).
    assert (K8 : getr r8 8 = Z_to_bv 64 0x197008).
    { rewrite (AG8 (8:reg) ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), G8, (AG6 (8:reg) ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), E8,
              (AG4 (8:reg) ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)), C8, (AG2 (8:reg) ltac:((lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end); notin)). exact A8. }
    assert (K9 : getr r8 9 = Z_to_bv 64 0x108780) by carry AG8 G9 (9:reg).
    assert (K18 : getr r8 18 = Z_to_bv 64 0x41000) by carry AG8 G18 (18:reg).
    (* [comment removed for export] *)
    assert (OUT : forall x : word, ((U x < 0x108780)%Z \/ (0x108780 + 0x81038 <= U x)%Z) -> (U x + 1 <= 0x197008 \/ 0x19700c <= U x)%Z ->
                  (U x < U S - 2176 \/ U S - 2128 <= U x)%Z -> M6 x = mem x).
    { intros x X1 X2 X3. (lazymatch goal with |- ?G => let G' := eval unfold M6, M5, M4, M3, M2, M1, fr_i1, fr_ia in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; unorm; try lia.
      reflexivity. }
    Ltac xo OUT H := eapply rd_same; [ intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    assert (FR : forall k v, (-2168 <= k <= -2136)%Z ->
                 rdn ASEGS (fr_ia mem S p ra s3) (at_ S k) 8 = Some (LE8 v) -> rdn ASEGS M6 (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hk Hr. (lazymatch goal with |- ?G => let G' := eval unfold M6, M5, M4, M3, M2, M1, fr_i1 in G in change_no_check G' end).
      repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]). exact Hr. }
    assert (C36 : rdn ASEGS M6 (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e330))).
    { apply FR; [lia|]. replace (Z_to_bv 64 0x6e330 : word) with (0x6e330 : word) by (apply bv_eq; reflexivity). (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end). rd8_chain. }
    assert (C44 : rdn ASEGS M6 (at_ S (-2144)) 8 = Some (LE8 S)) by (apply FR; [lia | (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end); rd8_chain]).
    assert (C52 : rdn ASEGS M6 (at_ S (-2152)) 8 = Some (LE8 p)) by (apply FR; [lia | (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end); rd8_chain]).
    assert (C60 : rdn ASEGS M6 (at_ S (-2160)) 8 = Some (LE8 ra)) by (apply FR; [lia | (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end); rd8_chain]).
    assert (C68 : rdn ASEGS M6 (at_ S (-2168)) 8 = Some (LE8 s3)) by (apply FR; [lia | (lazymatch goal with |- ?G => let G' := eval unfold fr_ia in G in change_no_check G' end); rd8_chain]).
    assert (Rgpg6 : rdn ASEGS M6 (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP))) by xo OUT Rgpg.
    assert (Rpg6 : rdn ASEGS M6 (Z_to_bv 64 PGP) 8 = Some (LE8 pgv)) by xo OUT Rpg.
    assert (Rz6 : rdn ASEGS M6 (Z_to_bv 64 (0x108788 + 8 * q32)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { (lazymatch goal with |- ?G => let G' := eval unfold M6, M5 in G in change_no_check G' end). repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]). (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end).
      replace (0x108788 + 8 * q32)%Z with (bv_unsigned (Z_to_bv 64 0x108788 : word) + 8 * q32)%Z by (wd_ulia).
      apply rdn8_in_fill; wd_ulia. }
    (* [comment removed for export] *)
    destruct (blk_i5 M6 rom S ra p s3 r8 PGP pgv q32 K2 K8 K9 K18 HS Hq32 Hq32b Hq47 C36 C44 C52 C60 C68 Rgpg6 ltac:(lia) Rpg6 Hpgv Rz6)
      as (r9 & RUN9 & L2 & L8 & L9 & L18 & L4 & L3 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
    exists r9. split.
    { replace (Z_to_bv 64 0x7a4d4 : word) with (0x7a4d4 : word) in RUN2 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x7a4ec : word) with (0x7a4ec : word) in RUN4 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x7a504 : word) with (0x7a504 : word) in RUN6 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x7a51c : word) with (0x7a51c : word) in RUN8 by (apply bv_eq; reflexivity).
      change asan_imemset_entry with (0x7ff38 : word) in RUN2, RUN4, RUN6, RUN8.
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
End AsAllocF0i.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocF2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record gctwH (mem : word -> option byte) (tp tsd key tctx T : Z) (kib : byte) : Prop := GCTWH {
  gc_kib : rdn ASEGS mem (Z_to_bv 64 0x106de0) 1 = Some [kib];
  gc_kibnz : bv_unsigned kib <> 0%Z;
  gc_key : rdn ASEGS mem (Z_to_bv 64 0x106de4) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 key));
  gc_keyr : (0 <= key < 2 ^ 20)%Z;
  gc_tsd : rdn ASEGS mem (Z_to_bv 64 (tp - 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd));
  gc_ctx : rdn ASEGS mem (Z_to_bv 64 (tsd + 8 * key)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tctx));
  gc_T : rdn ASEGS mem (Z_to_bv 64 (tctx + 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 T));
  gc_tp : (88 <= tp < 2 ^ 47)%Z;
  gc_tsdr : (0 <= tsd /\ tsd + 8 * key + 8 < 2 ^ 47)%Z;
  gc_ctxr : (1 <= tctx /\ tctx + 160 < 2 ^ 47)%Z;
  gc_Tr : (0 <= T < 2 ^ 47)%Z }.

Definition fr_gct (mem : word -> option byte) (S : word) (k : Z) (ra : word) : word -> option byte :=
  wbytes mem (at_ S (k - 8)) (word_to_le_bytes 8 ra).
Hint Unfold fr_gct : asfr.

Section GCT.
  Variables (mem rom : word -> option byte) (S : word) (k : Z) (ra : word) (tp tsd key tctx T : Z) (kib : byte).
  Variable regs : bvmap 5 word.
  Hypothesis GH : gctwH mem tp tsd key tctx T kib.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = at_ S k.
  Hypothesis H4 : getr regs 4 = Z_to_bv 64 tp.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hcells : (tp + 8 <= bv_unsigned S - 4096 /\ tsd + 8 * key + 8 <= bv_unsigned S - 4096 /\ tctx + 160 <= bv_unsigned S - 4096)%Z.
  Hypothesis Hk : (-4000 <= k <= 0)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (k - 16)) 16 = true.

End GCT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b1 (mem : word -> option byte) (S p x18 x19 x20 x21 x22 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2136)) (word_to_le_bytes 8 (Z_to_bv 64 0x6e4a4)))
    (at_ S (-2144)) (word_to_le_bytes 8 S))
    (at_ S (-2152)) (word_to_le_bytes 8 p))
    (at_ S (-2160)) (word_to_le_bytes 8 x18))
    (at_ S (-2168)) (word_to_le_bytes 8 x19))
    (at_ S (-2176)) (word_to_le_bytes 8 x20))
    (at_ S (-2184)) (word_to_le_bytes 8 x21))
    (at_ S (-2192)) (word_to_le_bytes 8 x22).
Hint Unfold fr_b1 : asfr.

Section B1.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H18 : getr regs 18 = x18.
  Hypothesis H19 : getr regs 19 = x19.
  Hypothesis H20 : getr regs 20 = x20.
  Hypothesis H21 : getr regs 21 = x21.
  Hypothesis H22 : getr regs 22 = x22.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.

  Lemma b1_run :
    exists r,
      msteps ASEGS (mkst regs (0x6e490 : word) mem rom) (mkst r (0x7cc4c : word) (fr_b1 mem S p x18 x19 x20 x21 x22) rom)
      /\ getr r 1 = Z_to_bv 64 0x4b85c /\ getr r 2 = at_ S (-2192) /\ getr r 8 = at_ S (-2128) /\ getr r 9 = p
      /\ getr r 10 = p /\ getr r 18 = at_ p (-16) /\ getr r 19 = Z_to_bv 64 0x103f18 /\ getr r 20 = Z_to_bv 64 1
      /\ getr r 21 = Z_to_bv 64 0 /\ getr r 22 = Z_to_bv 64 0
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk Hp HS H22 H21 H20 H19 H18 H9 H8 H2.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    wd_eexists. split.
    - an F_6e488 D_6e488.                              (* [comment removed for export] *)
      an F_6e48c D_6e48c.                              (* [comment removed for export] *)
      an F_6e490 D_6e490.                              (* [comment removed for export] *)
      an F_6e494 D_6e494.                              (* [comment removed for export] *)
      an F_6e498 D_6e498.                              (* [comment removed for export] *)
      an F_4b7e0 D_4b7e0.                              (* [comment removed for export] *)
      an F_4b7e4 D_4b7e4.                              (* [comment removed for export] *)
      an F_4b7e8 D_4b7e8.                              (* [comment removed for export] *)
      an F_4b7ec D_4b7ec.                              (* [comment removed for export] *)
      an F_4b7f0 D_4b7f0.                              (* [comment removed for export] *)
      an F_4b7f4 D_4b7f4.                              (* [comment removed for export] *)
      an F_4b7f8 D_4b7f8.                              (* [comment removed for export] *)
      an F_4b7fc D_4b7fc.                              (* [comment removed for export] *)
      an F_4b800 D_4b800.                              (* [comment removed for export] *)
      an F_4b804 D_4b804.                              (* [comment removed for export] *)
      an F_4b808 D_4b808.                              (* [comment removed for export] *)
      fsd F_4b80c D_4b80c (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_4b810 D_4b810 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_4b814 D_4b814 (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_4b818 D_4b818 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_4b81c D_4b81c (at_ S (-2168)).             (* [comment removed for export] *)
      fsd F_4b820 D_4b820 (at_ S (-2176)).             (* [comment removed for export] *)
      fsd F_4b824 D_4b824 (at_ S (-2184)).             (* [comment removed for export] *)
      fsd F_4b828 D_4b828 (at_ S (-2192)).             (* [comment removed for export] *)
      ab_ft F_4b82c D_4b82c ltac:(condz).              (* [comment removed for export] *)
      an F_4b830 D_4b830.                              (* [comment removed for export] *)
      an F_4b834 D_4b834.                              (* [comment removed for export] *)
      an F_4b838 D_4b838.                              (* [comment removed for export] *)
      an F_4b83c D_4b83c.                              (* [comment removed for export] *)
      an F_4b840 D_4b840.                              (* [comment removed for export] *)
      an F_4b844 D_4b844.                              (* [comment removed for export] *)
      an F_4b848 D_4b848.                              (* [comment removed for export] *)
      an F_4b84c D_4b84c.                              (* [comment removed for export] *)
      an F_4b850 D_4b850.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b1 mem S p x18 x19 x20 x21 x22). wd_refl.
    - post.
  Qed.
End B1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b2 (mem : word -> option byte) (S p : word) : word -> option byte :=
  wbytes (wbytes (wbytes mem
    (at_ S (-2200)) (word_to_le_bytes 8 (Z_to_bv 64 0x4b85c)))
    (at_ S (-2208)) (word_to_le_bytes 8 (at_ S (-2128))))
    (at_ S (-2216)) (word_to_le_bytes 8 p).
Hint Unfold fr_b2 : asfr.

Section B2.
  Variables (mem rom : word -> option byte) (S p : word).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x4b85c.
  Hypothesis H2 : getr regs 2 = at_ S (-2192).
  Hypothesis H8 : getr regs 8 = at_ S (-2128).
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H10 : getr regs 10 = p.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis Rhook : rdn ASEGS mem (Z_to_bv 64 0x199048) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Lemma b2_run :
    exists r,
      msteps ASEGS (mkst regs (0x7cc4c : word) mem rom) (mkst r (0x4b85c : word) (fr_b2 mem S p) rom)
      /\ getr r 2 = at_ S (-2192) /\ getr r 8 = at_ S (-2128) /\ getr r 9 = p /\ getr r 10 = Z_to_bv 64 0
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rhook Hstk HS H10 H9 H8 H2 H1.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_7cc44 D_7cc44.                              (* [comment removed for export] *)
      fsd F_7cc48 D_7cc48 (at_ S (-2200)).             (* [comment removed for export] *)
      fsd F_7cc4c D_7cc4c (at_ S (-2208)).             (* [comment removed for export] *)
      fsd F_7cc50 D_7cc50 (at_ S (-2216)).             (* [comment removed for export] *)
      an F_7cc54 D_7cc54.                              (* [comment removed for export] *)
      an F_7cc58 D_7cc58.                              (* [comment removed for export] *)
      an F_7ccf0 D_7ccf0.                              (* [comment removed for export] *)
      rt F_7ccf4 D_7ccf4.                              (* [comment removed for export] *)
      ab_tk F_7cc5c D_7cc5c ltac:(condz).              (* [comment removed for export] *)
      an F_7cc78 D_7cc78.                              (* [comment removed for export] *)
      an F_7cc7c D_7cc7c.                              (* [comment removed for export] *)
      rt F_7ccf8 D_7ccf8.                              (* [comment removed for export] *)
      an F_7cc80 D_7cc80.                              (* [comment removed for export] *)
      an F_7cc84 D_7cc84.                              (* [comment removed for export] *)
      cld8 F_7cc88 D_7cc88 (Z_to_bv 64 0) Rhook.       (* [comment removed for export] *)
      ab_tk F_7cc8c D_7cc8c ltac:(condz).              (* [comment removed for export] *)
      an F_7ccd8 D_7ccd8.                              (* [comment removed for export] *)
      fld F_7ccdc D_7ccdc (Z_to_bv 64 0x4b85c).        (* [comment removed for export] *)
      fld F_7cce0 D_7cce0 (at_ S (-2128)).             (* [comment removed for export] *)
      fld F_7cce4 D_7cce4 p.                           (* [comment removed for export] *)
      an F_7cce8 D_7cce8.                              (* [comment removed for export] *)
      rt F_7ccec D_7ccec.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b2 mem S p). wd_refl.
    - post.
  Qed.
End B2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FREED_CTX0 : Z := 0xffffffff00000000.
Definition fr_b3 (mem : word -> option byte) (p : word) (h1 h2 h3 : byte) : word -> option byte :=
  wbytes (wbytes mem (at_ p (-16)) [Z_to_bv 8 3; h1; h2; h3]) p (word_to_le_bytes 8 (Z_to_bv 64 FREED_CTX0)).
Hint Unfold fr_b3 : asfr.

(* [comment removed for export] *)
Lemma cas_state_667ec : forall regs mem rom (m hv : word) h1 h2 h3,
  getr regs 13 = m -> getr regs 15 = Z_to_bv 64 255 -> getr regs 14 = Z_to_bv 64 2 -> getr regs 16 = Z_to_bv 64 3 ->
  (bv_unsigned m mod 4 = 0)%Z ->
  rdn ASEGS mem m 4 = Some [Z_to_bv 8 2; h1; h2; h3] -> bytes_le_to_Z [Z_to_bv 8 2; h1; h2; h3] = bv_unsigned hv ->
  store_ok ASEGS mem m 4 = true ->
  msteps ASEGS (mkst regs (0x4b8b8 : word) mem rom)
    (mkst (regupd (regupd regs 12 (v_lw hv)) 17 (Z_to_bv 64 0)) (0x4b8d8 : word) (wbytes mem m [Z_to_bv 8 3; h1; h2; h3]) rom).
Proof using.
  intros regs mem rom m hv h1 h2 h3 H13 H15 H14 H16 Hal Hrd Hv Hok.
  pose proof (cas_byte_run ASEGS regs (0x4b8b8 : word) (0x4b8bc : word) (0x4b8c0 : word) (0x4b8c4 : word)
                (0x4b8c8 : word) (0x4b8cc : word) (0x4b8d0 : word) (0x4b8d4 : word) (0x4b8d8 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ _ 12 13 17 16 15 14 _ _ [Z_to_bv 8 2; h1; h2; h3] hv 0%nat 3%Z
                F_4b8b0 eq_refl D_4b8b0 F_4b8b4 eq_refl D_4b8b4 F_4b8b8 eq_refl D_4b8b8 F_4b8bc eq_refl D_4b8bc
                F_4b8c0 eq_refl D_4b8c0 F_4b8c4 eq_refl D_4b8c4 F_4b8c8 eq_refl D_4b8c8 F_4b8cc eq_refl D_4b8cc) as R.
  rewrite H13, H15, H14, H16 in R. cbn [firstn skipn app nth] in R.
  apply R; clear R; try (apply reg_neq_of_eqb; reflexivity); try (apply bv_eq; reflexivity); try lia; try assumption.
  all: unorm; reflexivity.
Qed.

Section B3.
  Variables (mem rom : word -> option byte) (S p : word) (h1 h2 h3 : byte) (hv : word).
  Variable regs : bvmap 5 word.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis H18 : getr regs 18 = at_ p (-16).
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 1.
  Hypothesis Hp : (16 <= bv_unsigned p < 2 ^ 47)%Z.
  Hypothesis Hp16 : (bv_unsigned p mod 16 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis Hh1 : h1 = Z_to_bv 8 0x11 \/ h1 = Z_to_bv 8 0x91.
  Hypothesis Rhdr : rdn ASEGS mem (at_ p (-16)) 4 = Some [Z_to_bv 8 2; h1; h2; h3].
  Hypothesis Hhv : bytes_le_to_Z [Z_to_bv 8 2; h1; h2; h3] = bv_unsigned hv.
  Hypothesis Hokh : store_ok ASEGS mem (at_ p (-16)) 4 = true.
  Hypothesis Hokp : store_ok ASEGS mem p 8 = true.

  Lemma b3_run :
    exists r,
      msteps ASEGS (mkst regs (0x4b85c : word) mem rom) (mkst r (0x4ba44 : word) (fr_b3 mem p h1 h2 h3) rom)
      /\ getr r 18 = at_ p (-16) /\ getr r 20 = Z_to_bv 64 1
      /\ getr r 1 = getr regs 1 /\ getr r 2 = getr regs 2 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9
      /\ getr r 19 = getr regs 19 /\ getr r 21 = getr regs 21
      /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hokp Hokh Hhv Rhdr Hh1 Hp16 Hp H20 H18 H10 hv.
    pose proof (u64_range p) as Hpr.
    destruct (p16_facts (bv_unsigned p) Hp16 ltac:(lia)) as (M4a & M4 & M32 & M8 & M16 & M8b).
    assert (Hm4 : (bv_unsigned (at_ p (-16)) mod 4 = 0)%Z) by (rewrite at_u by lia; exact M4).
    wd_eexists. split.
    - ab_tk F_4b854 D_4b854 ltac:(condz).              (* [comment removed for export] *)
      av F_4b890 D_4b890 (at_ p (-16)) ltac:(apply v_andi_m4_aligned; exact Hm4).   (* [comment removed for export] *)
      av F_4b894 D_4b894 (Z_to_bv 64 (8 * (bv_unsigned p + -16))) ltac:(valz).     (* [comment removed for export] *)
      an F_4b898 D_4b898.                              (* [comment removed for export] *)
      an F_4b89c D_4b89c.                              (* [comment removed for export] *)
      an F_4b8a0 D_4b8a0.                              (* [comment removed for export] *)
      an F_4b8a4 D_4b8a4.                              (* [comment removed for export] *)
      rewrite (v_sllw_mult32 255) by (first [lia | unorm; exact M32]).
      an F_4b8a8 D_4b8a8.                              (* [comment removed for export] *)
      rewrite (v_sllw_mult32 2) by (first [lia | unorm; exact M32]).
      an F_4b8ac D_4b8ac.                              (* [comment removed for export] *)
      rewrite (v_sllw_mult32 3) by (first [lia | unorm; exact M32]).
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_state_667ec _ mem rom (at_ p (-16)) hv h1 h2 h3);
          [gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity | exact Hm4 | exact Rhdr | exact Hhv | exact Hokh]. }
      an F_4b8d0 D_4b8d0.                              (* [comment removed for export] *)
      an F_4b8d4 D_4b8d4.                              (* [comment removed for export] *)
      fsd F_4b8d8 D_4b8d8 p.                           (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := h1);
          [exact F_4b8dc | reflexivity | exact D_4b8dc
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            rewrite wc_rdn_wbytes_out3; [ | rd8_side ];
            replace (at_ p (-15)) with (at_ (at_ p (-16)) (Z.of_nat 1)) by (rewrite at_at; f_equal; lia);
            apply rdn1_wbytes_in; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite at_u; lia] ]
        | step_simpl]; vn.
      av F_4b8e0 D_4b8e0 (Z_to_bv 64 1) ltac:(destruct Hh1 as [E|E]; rewrite E; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4b8e4 D_4b8e4 ltac:(condz).              (* [comment removed for export] *)
      an F_4b8e8 D_4b8e8.                              (* [comment removed for export] *)
      an F_4b8ec D_4b8ec.                              (* [comment removed for export] *)
      ab_tk F_4b8f0 D_4b8f0 ltac:(condz).              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b3 mem p h1 h2 h3). wd_refl.
    - post.
  Qed.
End B3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b4a (mem : word -> option byte) (S : word) : word -> option byte :=
  wbytes mem (at_ S (-2200)) (word_to_le_bytes 8 (Z_to_bv 64 0x4ba48)).
Hint Unfold fr_b4a : asfr.

Section B4A.
  Variables (mem rom : word -> option byte) (S : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2192).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.

  Lemma b4a_run :
    exists r,
      msteps ASEGS (mkst regs (0x4ba44 : word) mem rom) (mkst r (0x783bc : word) (fr_b4a mem S) rom)
      /\ getr r 1 = Z_to_bv 64 0x77594 /\ getr r 2 = at_ S (-2208)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9
      /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk HS H2.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4ba3c D_4ba3c.                              (* [comment removed for export] *)
      an F_77580 D_77580.                              (* [comment removed for export] *)
      fsd F_77584 D_77584 (at_ S (-2200)).             (* [comment removed for export] *)
      an F_77588 D_77588.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b4a mem S). wd_refl.
    - post.
  Qed.
End B4A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b4b (mem : word -> option byte) (T : Z) (j0 j1 : word) : word -> option byte :=
  wbytes (wbytes mem (Z_to_bv 64 (T + 2824)) (word_to_le_bytes 8 j0)) (Z_to_bv 64 (T + 2832)) (word_to_le_bytes 8 j1).
Hint Unfold fr_b4b : asfr.

Section B4B.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 : word) (T n : Z) (bf0 bf1 : list byte).
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H8 : getr regs 8 = at_ S (-2128).
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 T.
  Hypothesis H18 : getr regs 18 = at_ p (-16).
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 0x103f18.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis Rnhi : rdn ASEGS mem (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis Rnlo : rdn ASEGS mem (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))).
  Hypothesis Rf0 : rdn ASEGS mem (Z_to_bv 64 (T + 2824)) 8 = Some bf0.
  Hypothesis Lf0 : length bf0 = 8%nat.
  Hypothesis Rf1 : rdn ASEGS mem (Z_to_bv 64 (T + 2832)) 8 = Some bf1.
  Hypothesis Lf1 : length bf1 = 8%nat.
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 (T + 2824)) 16 = true.
  Hypothesis Rra : rdn ASEGS mem (at_ S (-2200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4ba48)).
  Hypothesis Rs0 : rdn ASEGS mem (at_ S (-2136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e4a4)).
  Hypothesis Rs1 : rdn ASEGS mem (at_ S (-2144)) 8 = Some (word_to_le_bytes 8 S).
  Hypothesis Rs2 : rdn ASEGS mem (at_ S (-2152)) 8 = Some (word_to_le_bytes 8 p).
  Hypothesis Rs3 : rdn ASEGS mem (at_ S (-2160)) 8 = Some (word_to_le_bytes 8 x18).
  Hypothesis Rs4 : rdn ASEGS mem (at_ S (-2168)) 8 = Some (word_to_le_bytes 8 x19).
  Hypothesis Rs5 : rdn ASEGS mem (at_ S (-2176)) 8 = Some (word_to_le_bytes 8 x20).
  Hypothesis Rs6 : rdn ASEGS mem (at_ S (-2184)) 8 = Some (word_to_le_bytes 8 x21).
  Hypothesis Rs7 : rdn ASEGS mem (at_ S (-2192)) 8 = Some (word_to_le_bytes 8 x22).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma n_split : (0 <= n / 2 ^ 32 <= 2 ^ 8 /\ 0 <= n mod 2 ^ 32 < 2 ^ 32 /\ n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n)%Z.
  Proof using Lf1 Lf0 Hn bf1 bf0 x22 rom. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). repeat split; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma b4b_run :
    exists r,
      msteps ASEGS (mkst regs (0x77594 : word) mem rom)
                   (mkst r (0x4fd70 : word) (fr_b4b mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) rom)
      /\ getr r 1 = Z_to_bv 64 0x6e4a4 /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p
      /\ getr r 10 = Z_to_bv 64 0x103f18 /\ getr r 11 = at_ p (-16) /\ getr r 12 = p /\ getr r 13 = at_ S (-2128)
      /\ getr r 18 = x18 /\ getr r 19 = x19 /\ getr r 20 = x20 /\ getr r 21 = x21 /\ getr r 22 = x22
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rs7 Rs6 Rs5 Rs4 Rs3 Rs2 Rs1 Rs0 Rra HokT Lf1 Rf1 Lf0 Rf0 Rnlo Rnhi Hn HT Hp HS H19 H18 H10 H9 H8 H2.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    pose proof (bytes_le_to_Z_bound bf0) as Bf0. rewrite Lf0 in Bf0. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bf0.
    pose proof (bytes_le_to_Z_bound bf1) as Bf1. rewrite Lf1 in Bf1. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bf1.
    pose proof (bytes_le_to_Z_nonneg bf0) as Bf0'. pose proof (bytes_le_to_Z_nonneg bf1) as Bf1'.
    assert (Vf0 : bytes_le_to_Z bf0 = bv_unsigned f0) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vf1 : bytes_le_to_Z bf1 = bv_unsigned f1) by (rewrite u_Z2bv by lia; reflexivity).
    destruct n_split as (Nh & Nl & Nsum).
    assert (Vh : bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n / 2 ^ 32))).
    { rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2))%Z with (2 ^ 16)%Z. unorm. apply Z.mod_small. lia. }
    assert (Vl : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n mod 2 ^ 32))) by (apply bytes4_small; lia).
    wd_eexists. split.
    - ab_ft F_7758c D_7758c ltac:(condz).              (* [comment removed for export] *)
      an F_77590 D_77590.                              (* [comment removed for export] *)
      an F_77594 D_77594.                              (* [comment removed for export] *)
      cld8 F_77598 D_77598 (Z_to_bv 64 0x4ba48) Rra.   (* [comment removed for export] *)
      an F_7759c D_7759c.                              (* [comment removed for export] *)
      rt F_775a0 D_775a0.                              (* [comment removed for export] *)
      clhu F_4ba40 D_4ba40 (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh.  (* [comment removed for export] *)
      clwu F_4ba44 D_4ba44 (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl.  (* [comment removed for export] *)
      cld F_4ba48 D_4ba48 bf1 (Z_to_bv 64 (bytes_le_to_Z bf1)) Rf1 Vf1.   (* [comment removed for export] *)
      cld F_4ba4c D_4ba4c bf0 (Z_to_bv 64 (bytes_le_to_Z bf0)) Rf0 Vf0.   (* [comment removed for export] *)
      av F_4ba50 D_4ba50 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      an F_4ba54 D_4ba54.                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia).
      an F_4ba58 D_4ba58.                              (* [comment removed for export] *)
      an F_4ba5c D_4ba5c.                              (* [comment removed for export] *)
      fsd F_4ba60 D_4ba60 (Z_to_bv 64 (T + 2824)).     (* [comment removed for export] *)
      fsd F_4ba64 D_4ba64 (Z_to_bv 64 (T + 2832)).     (* [comment removed for export] *)
      an F_4ba68 D_4ba68.                              (* [comment removed for export] *)
      an F_4ba6c D_4ba6c.                              (* [comment removed for export] *)
      an F_4ba70 D_4ba70.                              (* [comment removed for export] *)
      an F_4ba74 D_4ba74.                              (* [comment removed for export] *)
      cld8 F_4ba78 D_4ba78 (Z_to_bv 64 0x6e4a4) Rs0.   (* [comment removed for export] *)
      cld8 F_4ba7c D_4ba7c S Rs1.                      (* [comment removed for export] *)
      cld8 F_4ba80 D_4ba80 p Rs2.                      (* [comment removed for export] *)
      cld8 F_4ba84 D_4ba84 x18 Rs3.                    (* [comment removed for export] *)
      cld8 F_4ba88 D_4ba88 x19 Rs4.                    (* [comment removed for export] *)
      cld8 F_4ba8c D_4ba8c x20 Rs5.                    (* [comment removed for export] *)
      cld8 F_4ba90 D_4ba90 x21 Rs6.                    (* [comment removed for export] *)
      cld8 F_4ba94 D_4ba94 x22 Rs7.                    (* [comment removed for export] *)
      an F_4ba98 D_4ba98.                              (* [comment removed for export] *)
      an F_4ba9c D_4ba9c.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b4b mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)). wd_refl.
    - post.
  Qed.
End B4B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b5a (mem : word -> option byte) (S p x18 x19 x20 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2136)) (word_to_le_bytes 8 (Z_to_bv 64 0x6e4a4)))
    (at_ S (-2144)) (word_to_le_bytes 8 S))
    (at_ S (-2152)) (word_to_le_bytes 8 p))
    (at_ S (-2160)) (word_to_le_bytes 8 x18))
    (at_ S (-2168)) (word_to_le_bytes 8 x19))
    (at_ S (-2176)) (word_to_le_bytes 8 x20).
Hint Unfold fr_b5a : asfr.

Section B5A.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 : word).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x6e4a4.
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H11 : getr regs 11 = at_ p (-16).
  Hypothesis H13 : getr regs 13 = at_ S (-2128).
  Hypothesis H18 : getr regs 18 = x18.
  Hypothesis H19 : getr regs 19 = x19.
  Hypothesis H20 : getr regs 20 = x20.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis Rst : rdn ASEGS mem (at_ p (-16)) 1 = Some [Z_to_bv 8 3].

  Lemma b5a_run :
    exists r,
      msteps ASEGS (mkst regs (0x4fd70 : word) mem rom) (mkst r (0x783bc : word) (fr_b5a mem S p x18 x19 x20) rom)
      /\ getr r 1 = Z_to_bv 64 0x4fda8 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = at_ p (-16) /\ getr r 9 = at_ S (-2128)
      /\ getr r 18 = Z_to_bv 64 0x103f18
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rst Hstk Hp HS H20 H19 H18 H13 H11 H10 H9 H8 H2 H1.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    wd_eexists. split.
    - an F_4fd68 D_4fd68.                              (* [comment removed for export] *)
      fsd F_4fd6c D_4fd6c (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_4fd70 D_4fd70 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_4fd74 D_4fd74 (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_4fd78 D_4fd78 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_4fd7c D_4fd7c (at_ S (-2168)).             (* [comment removed for export] *)
      fsd F_4fd80 D_4fd80 (at_ S (-2176)).             (* [comment removed for export] *)
      an F_4fd84 D_4fd84.                              (* [comment removed for export] *)
      clb F_4fd88 D_4fd88 (Z_to_bv 8 3) Rst.           (* [comment removed for export] *)
      an F_4fd8c D_4fd8c.                              (* [comment removed for export] *)
      ab_ft F_4fd90 D_4fd90 ltac:(condz).              (* [comment removed for export] *)
      an F_4fd94 D_4fd94.                              (* [comment removed for export] *)
      an F_4fd98 D_4fd98.                              (* [comment removed for export] *)
      an F_4fd9c D_4fd9c.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b5a mem S p x18 x19 x20). wd_refl.
    - post.
  Qed.
End B5A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section B5B.
  Variables (mem rom : word -> option byte) (S p : word) (T tctx : Z) (bsz : list byte).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H9 : getr regs 9 = at_ S (-2128).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 T.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hctx : (1 <= tctx /\ tctx + 4096 <= bv_unsigned S - 3584)%Z.
  Hypothesis RT0 : rdn ASEGS mem (Z_to_bv 64 T) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tctx)).
  Hypothesis Rtid : rdn ASEGS mem (Z_to_bv 64 (tctx + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis Rbuf : rdn ASEGS mem (at_ S (-2128)) 8 = Some (word_to_le_bytes 8 (at_ S (-2112))).
  Hypothesis Rsz : rdn ASEGS mem (at_ S (-2120)) 8 = Some bsz.
  Hypothesis Lsz : length bsz = 8%nat.

  Lemma b5b_run :
    exists r,
      msteps ASEGS (mkst regs (0x4fda8 : word) mem rom) (mkst r (0x8ea80 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x4fdc8 /\ getr r 2 = at_ S (-2176) /\ getr r 9 = at_ S (-2128)
      /\ getr r 10 = at_ S (-2112) /\ getr r 11 = Z_to_bv 64 (bytes_le_to_Z bsz) /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = Z_to_bv 64 T
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 8 = getr regs 8 /\ getr r 18 = getr regs 18
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Lsz Rsz Rbuf Rtid RT0 Hctx HT HS H10 H9 H2 tctx.
    pose proof (u64_range S) as HSr.
    assert (V0 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 0)) = bv_unsigned (Z_to_bv 64 0)) by (apply bytes4_small; lia).
    pose proof (bytes_le_to_Z_bound bsz) as Bsz. rewrite Lsz in Bsz. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bsz.
    pose proof (bytes_le_to_Z_nonneg bsz) as Bsz0.
    assert (Vsz : bytes_le_to_Z bsz = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bsz))) by (rewrite u_Z2bv by lia; reflexivity).
    wd_eexists. split.
    - ab_ft F_4fda0 D_4fda0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4fda4 D_4fda4 (Z_to_bv 64 tctx) RT0.      (* [comment removed for export] *)
      cld8 F_4fda8 D_4fda8 (at_ S (-2112)) Rbuf.       (* [comment removed for export] *)
      cld F_4fdac D_4fdac bsz (Z_to_bv 64 (bytes_le_to_Z bsz)) Rsz Vsz.   (* [comment removed for export] *)
      clw F_4fdb0 D_4fdb0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) Rtid V0.   (* [comment removed for export] *)
      an F_4fdb4 D_4fdb4.                              (* [comment removed for export] *)
      an F_4fdb8 D_4fdb8.                              (* [comment removed for export] *)
      an F_4fdbc D_4fdbc.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End B5B.
End FPGen.
End AsAllocF2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocF0 AsAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma at0_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_P1 (mem : word -> option byte) (S p ra0 s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
  fr_p1 (fr_icpt mem S ra0 s0 s1 s2 s3 s4 s5) S p ra0 s3.
(* [comment removed for export] *)
Definition fr_P2 (MU : word -> option byte) (S p x22 : word) (T n : Z) (h1 h2 h3 : byte) (bf0 bf1 : list byte) : word -> option byte :=
  let x18 := Z_to_bv 64 0x6e434 in let x19 := Z_to_bv 64 1 in let x20 := at_ S (-2128) in let x21 := at_ S (-81) in
  let M4 := fr_b1 MU S p x18 x19 x20 x21 x22 in
  let M5 := fr_b2 M4 S p in
  let M6 := fr_b3 M5 p h1 h2 h3 in
  let M7 := fr_b4a M6 S in
  let M8 := wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x77594)) in
  let M9 := fr_b4b M8 T (at_ (Z_to_bv 64 (bytes_le_to_Z bf0)) 1) (v_add (Z_to_bv 64 n) (Z_to_bv 64 (bytes_le_to_Z bf1))) in
  let M10 := fr_b5a M9 S p x18 x19 x20 in
  wbytes M10 (at_ S (-2184)) (LE8 (Z_to_bv 64 0x4fda8)).
Hint Unfold fr_P1 fr_P2 : asfr.

(* [comment removed for export] *)
Lemma fr_P1_tag0 : forall (mem : word -> option byte) (S p ra0 s0 s1 s2 s3 s4 s5 : word) (MU : word -> option byte),
  (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z ->
  (forall x : word, MU x <> fr_P1 mem S p ra0 s0 s1 s2 s3 s4 s5 x -> ~ (U S - 2116 <= U x < U S - 2112)%Z) ->
  rdn ASEGS MU (at_ S (-2116)) 4 = Some (LE4 0).
Proof using.
  intros mem S p ra0 s0 s1 s2 s3 s4 s5 MU GS FOOT. pose proof (u64_range S) as HSr.
  assert (SL : rdn ASEGS (fr_P1 mem S p ra0 s0 s1 s2 s3 s4 s5) (at_ S (-2120)) 8 = Some (LE8 (Z_to_bv 64 0))).
  { (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1 in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. rd_hit8. }
  pose proof (MemsetLibF.RefMemcpyLib.rdn_skipn ASEGS _ 8 (at_ S (-2120)) _ 4 SL ltac:(lia)) as X.
  rewrite at_at in X. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Nat.sub Pos.add Z.opp Z.pos_sub Pos.pred_double] in X.
  replace (skipn 4 (LE8 (Z_to_bv 64 0))) with (LE4 0) in X by (vm_compute; reflexivity).
  rewrite <- X. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia.
  destruct (decide (MU x = fr_P1 mem S p ra0 s0 s1 s2 s3 s4 s5 x)) as [E|NE]; [exact E|]. exfalso. apply (FOOT x NE). cbn in Hx. lia.
Qed.

Section RUNI.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S p ra0 tp tsdp P top bot : word) (T tctx n q32 : Z) (D : nat).
  Variables (h1 h2 h3 : byte) (hv : word) (bf0 bf1 : list byte).
  Variable r2 : bvmap 5 word.              (* [comment removed for export] *)
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  (* [comment removed for export] *)
  Hypothesis A2 : getr r2 2 = at_ S (-2128).
  Hypothesis A8 : getr r2 8 = S.
  Hypothesis A9 : getr r2 9 = p.
  Hypothesis A18 : getr r2 18 = ra0.
  Hypothesis A4 : getr r2 4 = getr R 4.
  Hypothesis A3 : getr r2 3 = getr R 3.
  Hypothesis A20 : getr r2 20 = getr R 20.
  Hypothesis A21 : getr r2 21 = getr R 21.
  Hypothesis A22 : getr r2 22 = getr R 22.
  Hypothesis A23 : getr r2 23 = getr R 23.
  Hypothesis A24 : getr r2 24 = getr R 24.
  Hypothesis A25 : getr r2 25 = getr R 25.
  Hypothesis A26 : getr r2 26 = getr R 26.
  Hypothesis A27 : getr r2 27 = getr R 27.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584 /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + 8 <= T \/ T + 4096 <= U p - 16)%Z.      (* [comment removed for export] *)
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx) /\ (tctx + 4096 <= U p - 16 \/ U p + 8 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis Gq32 : (U p / 2 ^ 32 = q32 /\ 0 <= q32 < 2 ^ 15 /\ U p / 2 ^ 47 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn ASEGS mem (Z_to_bv 64 0x10827c) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_fum : rdn ASEGS mem (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn ASEGS mem (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_unw : rdn ASEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_unw_ok : store_ok ASEGS mem (at_ thr 3168) 1 = true.
  Hypothesis C_pg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 P).
  Hypothesis C_P : rdn ASEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn ASEGS mem (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn ASEGS mem (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn ASEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn ASEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn ASEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_sw : rdn ASEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn ASEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn ASEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_hook : rdn ASEGS mem (Z_to_bv 64 0x199048) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_h1 : h1 = Z_to_bv 8 0x11 \/ h1 = Z_to_bv 8 0x91.
  Hypothesis C_hdr : rdn ASEGS mem (at_ p (-16)) 4 = Some [Z_to_bv 8 2; h1; h2; h3].
  Hypothesis C_hv : bytes_le_to_Z [Z_to_bv 8 2; h1; h2; h3] = U hv.
  Hypothesis C_hdr_ok : store_ok ASEGS mem (at_ p (-16)) 4 = true.
  Hypothesis C_p_ok : store_ok ASEGS mem p 8 = true.
  Hypothesis C_nhi : rdn ASEGS mem (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn ASEGS mem (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_f0 : rdn ASEGS mem (Z_to_bv 64 (T + 2824)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn ASEGS mem (Z_to_bv 64 (T + 2832)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_stat_ok : store_ok ASEGS mem (Z_to_bv 64 (T + 2824)) 16 = true.
  Hypothesis C_T0 : rdn ASEGS mem (Z_to_bv 64 T) 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn ASEGS mem (Z_to_bv 64 (tctx + 8)) 4 = Some (LE4 0).
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.

  #[local] Abbreviation M1 := (fr_icpt mem S ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).
  #[local] Abbreviation M3 := (fr_P1 mem S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)).

  (* [comment removed for export] *)
  Lemma fr_P1_outside : forall x : word, (U x < U S - 2176)%Z \/ (U S <= U x)%Z -> M3 x = mem x.
  Proof using L_f1 L_f0 GS bf1 bf0 n.
    intros x Hx. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma fr_P1_grows : mem_grows mem M3.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Ltac xfer OUT H := eapply rd_same; [intros x Hx; apply OUT | | exact H].

  Theorem run_from_6e3cc :
    exists r MU (sz : Z) (bsz : list byte),
      msteps ASEGS (mkst r2 (0x6e3d4 : word) (fr_ia M1 S p ra0 (getr R 19)) rom) (mkst r (0x8ea80 : word) (fr_P2 MU S p (getr R 22) T n h1 h2 h3 bf0 bf1) rom)
      /\ getr r 1 = Z_to_bv 64 0x4fdc8 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = at_ p (-16) /\ getr r 9 = at_ S (-2128)
      /\ getr r 10 = at_ S (-2112) /\ getr r 11 = Z_to_bv 64 (bytes_le_to_Z bsz) /\ getr r 18 = Z_to_bv 64 0x103f18
      /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = thr /\ getr r 21 = at_ S (-81) /\ getr r 22 = getr R 22
      /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 23 = getr R 23 /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27
      /\ (1 <= sz <= 30)%Z /\ (sz <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MU x <> M3 x ->
            (U S - 2272 <= U x < U S - 2128)%Z \/ (U S - 2120 <= U x < U S - 1872)%Z \/ (U S - 72 <= U x < U S - 64)%Z \/ U x = (T + 3168)%Z)
      /\ mem_grows M3 MU
      /\ rdn ASEGS MU (at_ S (-2120)) 4 = Some (LE4 sz) /\ rdn ASEGS MU (at_ S (-2112)) 8 = Some (LE8 (Z_to_bv 64 0x6e434))
      /\ rdn ASEGS MU (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ rdn ASEGS MU (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn ASEGS MU (at_ S (-2116)) 4 = Some (LE4 0).                                  (* [comment removed for export] *)
  Proof.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr.
    pose proof (u64_range P) as HPr.
    destruct GS as (GS1 & GS2 & GS3). destruct Gp as (Gp1 & Gp2 & Gp3). destruct GT as (GT1 & GT2). destruct GT2 as [GTS GT2]. destruct Gctx as (Gc1 & Gc2 & Gc3 & Gc4).
    destruct Gtp as (Gtp1 & Gtp2). destruct Gq32 as (Q1 & Q2 & Q3).
    (* [comment removed for export] *)
    assert (OUT1 : forall x : word, (U x < U S - 56 \/ U S <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold fr_icpt in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GR1 : mem_grows mem M1) by ((lazymatch goal with |- ?G => let G' := eval unfold fr_icpt in G in change_no_check G' end); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    (* [comment removed for export] *)
    Ltac x1 OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    destruct (p1_blkB M1 rom S ra0 p (getr R 19) ltac:(hlia) GS2) with (r0 := r2)
      as (r3 & RUN3 & B1 & B2 & B8 & B9 & B18 & B10 & B11 & B12 & B13 & B14 & B15 & B19 & B20 & B21 & B4 & B3 & B22 & B23 & B24 & B25 & B26 & B27);
      [ | x1 OUT1 C_mcs | x1 OUT1 C_gcf | x1 OUT1 C_fum | exact A2 | exact A8 | exact A9 | exact A18 | ].
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub ASEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (M3' := fr_p1 M1 S p ra0 (getr R 19)) in RUN3.
    assert (EM3 : M3' = M3) by reflexivity. rewrite EM3 in RUN3. clear EM3 M3'.
    pose proof fr_P1_outside as OUT3. pose proof fr_P1_grows as GR3.
    assert (SOK3 : store_ok ASEGS M3 (at_ S (-2304)) 2304 = true) by (eapply store_ok_mono; [exact GR3 | exact Hstk]).
    Ltac x3 OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    assert (UH : uiH ASEGS asan_ui_tab M3 (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi asan_ui_tab] in G in change_no_check G' end).
      - x3 OUT3 C_inited.
      - x3 OUT3 C_unw.
      - eapply store_ok_mono; [exact GR3 | exact C_unw_ok].
      - x3 OUT3 C_pg.
      - x3 OUT3 C_P.
      - rewrite !at_at. eapply (store_ok_sub ASEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite !at_at. eapply (store_ok_sub ASEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - hlia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. hlia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. hlia. }
    assert (GH : gctH ASEGS (ut_gct asan_ui_tab) M3 (at_ (at_ S (-2128)) (-80)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_gct asan_ui_tab gt_tsd asan_gct_tab] in G in change_no_check G' end).
      - x3 OUT3 C_kif.
      - x3 OUT3 C_key.
      - x3 OUT3 C_tsdp.
      - x3 OUT3 C_tctx.
      - x3 OUT3 C_thr.
      - unorm. lia.
      - rewrite !at_at. eapply (store_ok_sub ASEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (SH : stkH ASEGS M3 thr top bot).
    { split.
      - x3 OUT3 C_sw.
      - x3 OUT3 C_top.
      - x3 OUT3 C_bot.
      - exact Gbot.
      - unorm. lia. }
    (* [comment removed for export] *)
    assert (B4' : getr r3 4 = tp) by (rewrite B4, A4; exact HR4).
    assert (RET_U : ret_ok (Z_to_bv 64 0x6e490)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (Rr : rdn ASEGS M3 (at_ S (-8)) 8 = Some (LE8 ra0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT. repeat (wd_rdstep rd8_side). }
    assert (Rw : rdn ASEGS M3 (at_ S (-16)) 8 = Some (LE8 (getr R 8))).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT. repeat (wd_rdstep rd8_side). }
    assert (FPC3 : fpc M3 (bytes_le_to_Z (LE8 (getr R 8))) (U S) D).
    { rewrite bytes_le_to_Z_8. apply (fpc_kept_gen mem _ _ _ Hfpc M3).
      destruct (fpc_shape _ _ _ _ Hfpc) as [ST | FR]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (getr R 8)). rewrite <- (u_Z2bv a) in Ha by (unfold PTRHI in Ha; lia).
      apply OUT3. lia. }
    destruct (asan_ui_run_s r3 M3 rom (Z_to_bv 64 0x6e490) (at_ S (-2128)) tp (at_ S (-2128)) (Z_to_bv 64 0x6e434) S (Z_to_bv 64 1)
                thr top bot tsdp ctxw P RET_U B1 B2 B4' B10 B11 B12 B13 B14 B15 ltac:(wd_ulia) UH GH SH Gtop
                D (LE8 ra0) (LE8 (getr R 8)) Rr (length_N_to_le_bytes _ _) Rw (length_N_to_le_bytes _ _) FPC3)
      as (rU & MU & sz & RUNU & AGU & SZ1 & SZ2 & RDsz & RDpc & RDunw & FOOTUs & GRU).
    (* [comment removed for export] *)
    assert (TAG0 : rdn ASEGS MU (at_ S (-2116)) 4 = Some (LE4 0)).
    { apply (fr_P1_tag0 mem S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) MU GS).
      intros x Hx. pose proof (FOOTUs x Hx) as F. revert F. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. intros F. lia. }
    assert (FOOTU : forall x : word, MU x <> M3 x ->
              (U (at_ S (-2128)) - 144 <= U x < U (at_ S (-2128)))%Z \/ (U (at_ S (-2128)) + 8 <= U x < U (at_ S (-2128)) + 256)%Z
              \/ (U (at_ S (-2128)) + 2056 <= U x < U (at_ S (-2128)) + 2064)%Z \/ U x = (U thr + 3168)%Z).
    { intros x Hx. destruct (FOOTUs x Hx) as [F|[F|[F|[F|F]]]]; [left | right; left | right; left | right; right; left | right; right; right]; try lia; exact F. }
    clear FOOTUs.
    cbn [ut_rb asan_ui_tab] in RUNU. rewrite at0_lit in RUNU by lia.
    replace (485716 : word) with (Z_to_bv 64 485716 : word) in RUN3 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (MUq : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z) \/ (U S <= U x)%Z -> MU x = mem x).
    { intros x Hx. destruct (decide (MU x = M3 x)) as [E|NE].
      - rewrite E. apply OUT3. lia.
      - exfalso. pose proof (FOOTU x NE) as F. revert F. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. intros F. lia. }
    assert (GRU' : mem_grows mem MU) by (eapply mem_grows_trans; [exact GR3 | exact GRU]).
    assert (SOKU : store_ok ASEGS MU (at_ S (-2304)) 2304 = true) by (eapply store_ok_mono; [exact GRU | exact SOK3]).
    Ltac via AG r H := let TT := fresh in pose proof (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold ui_clob, gct_clob in G in change_no_check G' end); notin)) as TT; rewrite H in TT; exact TT.
    (* [comment removed for export] *)
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold ui_clob, gct_clob in G in change_no_check G' end); notin)); rch.
    assert (U2 : getr rU 2 = at_ S (-2128)) by via AGU (2:reg) B2.
    assert (U8 : getr rU 8 = S) by via AGU (8:reg) B8.
    assert (U9 : getr rU 9 = p) by via AGU (9:reg) B9.
    assert (U18 : getr rU 18 = Z_to_bv 64 0x6e434) by via AGU (18:reg) B18.
    assert (U19 : getr rU 19 = Z_to_bv 64 1) by via AGU (19:reg) B19.
    assert (U20 : getr rU 20 = at_ S (-2128)) by via AGU (20:reg) B20.
    assert (U21 : getr rU 21 = at_ S (-81)) by via AGU (21:reg) B21.
    assert (B22' : getr r3 22 = getr R 22) by (rewrite B22; exact A22).
    assert (U22 : getr rU 22 = getr R 22) by via AGU (22:reg) B22'.
    assert (B3' : getr r3 3 = getr R 3) by (rewrite B3; exact A3).
    assert (U3 : getr rU 3 = getr R 3) by via AGU (3:reg) B3'.
    assert (U4 : getr rU 4 = tp) by via AGU (4:reg) B4'.
    assert (B23' : getr r3 23 = getr R 23) by (rewrite B23; exact A23).
    assert (B24' : getr r3 24 = getr R 24) by (rewrite B24; exact A24).
    assert (B25' : getr r3 25 = getr R 25) by (rewrite B25; exact A25).
    assert (B26' : getr r3 26 = getr R 26) by (rewrite B26; exact A26).
    assert (B27' : getr r3 27 = getr R 27) by (rewrite B27; exact A27).
    assert (U23 : getr rU 23 = getr R 23) by via AGU (23:reg) B23'.
    assert (U24 : getr rU 24 = getr R 24) by via AGU (24:reg) B24'.
    assert (U25 : getr rU 25 = getr R 25) by via AGU (25:reg) B25'.
    assert (U26 : getr rU 26 = getr R 26) by via AGU (26:reg) B26'.
    assert (U27 : getr rU 27 = getr R 27) by via AGU (27:reg) B27'.
    (* [comment removed for export] *)
    destruct (b1_run MU rom S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) rU
                U2 U8 U9 U18 U19 U20 U21 U22 ltac:(hlia) ltac:(hlia) SOKU)
      as (r4 & RUN4 & C1 & C2 & C8 & C9 & C10 & C18 & C19 & C20 & C21 & C22 & C3 & C4 & C23 & C24 & C25 & C26 & C27).
    (* [comment removed for export] *)
    Ltac peelq Q :=
      repeat (rewrite wbytes_outside;
              [ | wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
                | wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] ]);
      apply Q; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
    (* [comment removed for export] *)
    Ltac quiet_tac Q := intros x Hx; revert Hx; unfold at_ at 1 2; unorm; intros Hx; peelq Q.
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    Ltac xqh TS Q H := unfold hideW in TS; xq Q H.
    Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
    #[local] Definition quiet (S : word) (T : Z) (x : word) : Prop := ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z) \/ (U S <= U x)%Z.
    (* [comment removed for export] *)
    assert (GR4 : mem_grows mem (fr_b1 MU S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22))).
    { eapply mem_grows_trans; [exact GRU'|]. (lazymatch goal with |- ?G => let G' := eval unfold fr_b1 in G in change_no_check G' end); grows_tac. }
    assert (Q4 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z) \/ (U S <= U x)%Z ->
                 fr_b1 MU S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b1 in G in change_no_check G' end). quiet_tac MUq. }
    remember (fr_b1 MU S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) as M4 eqn:EM4 in RUN4, GR4, Q4.
    (* [comment removed for export] *)
    destruct (b2_run M4 rom S p r4 C1 C2 C8 C9 C10 ltac:(hlia)) as (r5 & RUN5 & D2 & D8 & D9 & D10 & D3 & D4 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
    { eapply store_ok_mono; [exact GR4 | exact Hstk]. }
    { xqh GTS Q4 C_hook. }
    (* [comment removed for export] *)
    assert (GR5 : mem_grows mem (fr_b2 M4 S p)) by (eapply mem_grows_trans; [exact GR4|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_b2 in G in change_no_check G' end); grows_tac).
    assert (Q5 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z) \/ (U S <= U x)%Z -> fr_b2 M4 S p x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b2 in G in change_no_check G' end). quiet_tac Q4. }
    remember (fr_b2 M4 S p) as M5 eqn:EM5 in RUN5, GR5, Q5.
    (* [comment removed for export] *)
    destruct (b3_run M5 rom p h1 h2 h3 hv r5 D10 ltac:(rewrite D18; exact C18) ltac:(rewrite D20; exact C20) ltac:(hlia) Gp3) as (r6 & RUN6 & E18 & E20 & E1 & E2 & E3 & E4 & E8 & E9 & E19 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
    { exact C_h1. }
    { xqh GTS Q5 C_hdr. }
    { exact C_hv. }
    { eapply store_ok_mono; [exact GR5 | exact C_hdr_ok]. }
    { eapply store_ok_mono; [exact GR5 | exact C_p_ok]. }
    (* [comment removed for export] *)
    assert (GR6 : mem_grows mem (fr_b3 M5 p h1 h2 h3)) by (eapply mem_grows_trans; [exact GR5|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_b3 in G in change_no_check G' end); grows_tac).
    assert (Q6 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z) \/ (U S <= U x)%Z ->
                 fr_b3 M5 p h1 h2 h3 x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b3 in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end);
        rewrite ?at_u by lia; try lia. apply Q5. lia. }
    (* [comment removed for export] *)
    assert (Ehh : [h2; h3] = word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
    { pose proof (rdn_skip ASEGS mem (at_ p (-16)) 4 [Z_to_bv 8 2; h1; h2; h3] 2 C_hdr ltac:(lia) ltac:(rewrite at_u; lia)) as X.
      rewrite at_at in X. cbn [skipn Nat.sub] in X.
      replace (-16 + Z.of_nat 2)%Z with (-14)%Z in X by reflexivity. rewrite C_nhi in X. congruence. }
    (* [comment removed for export] *)
    assert (ST6 : rdn ASEGS (fr_b3 M5 p h1 h2 h3) (at_ p (-16)) 1 = Some [Z_to_bv 8 3]).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b3 in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      replace (at_ p (-16)) with (at_ (at_ p (-16)) (Z.of_nat 0)) at 2 by (rewrite at_at; f_equal; lia).
      apply rdn1_wbytes_in; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite at_u; lia]. }
    assert (NH6 : rdn ASEGS (fr_b3 M5 p h1 h2 h3) (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b3 in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      replace (at_ p (-14)) with (at_ (at_ p (-16)) (Z.of_nat 2)) by (rewrite at_at; f_equal; lia).
      rewrite (rdn_wbytes_sub ASEGS M5 (at_ p (-16)) _ 2 2); [(lazymatch goal with |- ?G => let G' := eval cbn [firstn skipn] in G in change_no_check G' end); rewrite Ehh; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite at_u; lia]. }
    remember (fr_b3 M5 p h1 h2 h3) as M6 eqn:EM6 in RUN6, GR6, Q6, ST6, NH6.
    (* [comment removed for export] *)
    assert (E2' : getr r6 2 = at_ S (-2192)) by (rewrite E2; exact D2).
    destruct (b4a_run M6 rom S r6 E2' ltac:(hlia) ltac:(eapply store_ok_mono; [exact GR6 | exact Hstk]))
      as (r7 & RUN7 & F1 & F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    assert (GR7 : mem_grows mem (fr_b4a M6 S)) by (eapply mem_grows_trans; [exact GR6|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end); grows_tac).
    assert (Q7 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z) \/ (U S <= U x)%Z -> fr_b4a M6 S x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end);
        rewrite ?at_u by lia; try lia. apply Q6. lia. }
    assert (RA7 : rdn ASEGS (fr_b4a M6 S) (at_ S (-2200)) 8 = Some (LE8 (Z_to_bv 64 0x4ba48))) by ((lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end); rd_hit8).
    remember (fr_b4a M6 S) as M7 eqn:EM7 in RUN7, GR7, Q7, RA7.
    (* [comment removed for export] *)
    assert (RET_G1 : ret_ok (Z_to_bv 64 0x77594)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (F4' : getr r7 4 = tp) by (rewrite F4, E4, D4, C4; exact U4).
    assert (GH7 : gctH ASEGS asan_gct_tab M7 (at_ S (-2208)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end).
      - xqh GTS Q7 C_kif. - xqh GTS Q7 C_key. - xqh GTS Q7 C_tsdp. - xqh GTS Q7 C_tctx. - xqh GTS Q7 C_thr.
      - unorm. lia.
      - rewrite at_at. eapply (store_ok_sub ASEGS M7 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR7 | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (gct_run ASEGS asan_gct_tab asan_gct_tab_ok M7 rom r7 (Z_to_bv 64 0x77594) (at_ S (-2208)) tp tsdp ctxw thr GH7 RET_G1 F1 F2 F4')
      as (r8 & RUN8 & X10 & X11 & AGX).
    cbn [gt_rb asan_gct_tab] in RUN8. rewrite at0_lit in RUN8 by lia. rewrite at_at in RUN8. cbn [Z.add Z.opp Pos.add] in RUN8.
    replace (492476 : word) with (Z_to_bv 64 492476 : word) in RUN7 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (GR8 : mem_grows mem (wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x77594)))) by (eapply mem_grows_trans; [exact GR7|]; grows_tac).
    assert (Q8 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z) \/ (U S <= U x)%Z ->
                 wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x77594)) x = mem x).
    { intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end);
        rewrite ?at_u by lia; try lia. apply Q7. lia. }
    (* [comment removed for export] *)
    assert (Y2 : getr r8 2 = at_ S (-2208)) by viac AGX (2:reg).
    assert (Y8 : getr r8 8 = at_ S (-2128)) by viac AGX (8:reg).
    assert (Y9 : getr r8 9 = p) by viac AGX (9:reg).
    assert (Y18 : getr r8 18 = at_ p (-16)) by viac AGX (18:reg).
    assert (Y19 : getr r8 19 = Z_to_bv 64 0x103f18) by viac AGX (19:reg).
    assert (Y10 : getr r8 10 = thr) by exact X10.
    assert (Y4 : getr r8 4 = tp) by viac AGX (4:reg).
    assert (Y3 : getr r8 3 = getr R 3) by viac AGX (3:reg).
    assert (Y23 : getr r8 23 = getr R 23) by viac AGX (23:reg).
    assert (Y24 : getr r8 24 = getr R 24) by viac AGX (24:reg).
    assert (Y25 : getr r8 25 = getr R 25) by viac AGX (25:reg).
    assert (Y26 : getr r8 26 = getr R 26) by viac AGX (26:reg).
    assert (Y27 : getr r8 27 = getr R 27) by viac AGX (27:reg).
    (* [comment removed for export] *)
    destruct (b4b_run (wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x77594))) rom S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)
                T n bf0 bf1 r8 Y2 Y8 Y9 Y10 Y18 Y19 ltac:(hlia) ltac:(hlia) ltac:(hlia) Gn)
      as (r9 & RUN9 & G1 & G2 & G8 & G9 & G10 & G11 & G12 & G13 & G18 & G19 & G20 & G21 & G22 & G3 & G4 & G23 & G24 & G25 & G26 & G27).
    { rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. rewrite EM7. (lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. exact NH6. }
    { xqh GTS Q8 C_nlo. }
    { xqh GTS Q8 C_f0. }
    { exact L_f0. }
    { xqh GTS Q8 C_f1. }
    { exact L_f1. }
    { eapply store_ok_mono; [exact GR8 | exact C_stat_ok]. }
    { rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. exact RA7. }
    Ltac dig := repeat (wd_rdstep rd8_side).
    all: try (rewrite EM7, EM6, EM5, EM4; (lazymatch goal with |- ?G => let G' := eval unfold fr_b4a, fr_b3, fr_b2, fr_b1 in G in change_no_check G' end); first [ solve [clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT; dig] | dig ]).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    remember (wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x77594))) as M8 eqn:EM8 in RUN8, RUN9, GR8, Q8.
    assert (GR9 : mem_grows mem (fr_b4b M8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1))) by (eapply mem_grows_trans; [exact GR8|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_b4b in G in change_no_check G' end); grows_tac).
    assert (Q9 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z
                                    /\ (U x < T + 2824 \/ T + 2840 <= U x)%Z) \/ (U S <= U x)%Z ->
                 fr_b4b M8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1) x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b4b in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try lia. apply Q8. lia. }
    assert (ST9 : rdn ASEGS (fr_b4b M8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) (at_ p (-16)) 1 = Some [Z_to_bv 8 3]).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b4b in G in change_no_check G' end). rewrite !rdn_wbytes_out; [ | rd8_side .. ]. rewrite EM8. rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      rewrite EM7. (lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. exact ST6. }
    remember (fr_b4b M8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) as M9 eqn:EM9 in RUN9, GR9, Q9, ST9.
    (* [comment removed for export] *)
    destruct (b5a_run M9 rom S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) r9 G1 G2 G8 G9 G10 G11 G13 G18 G19 G20 ltac:(hlia) ltac:(hlia)
                ltac:(eapply store_ok_mono; [exact GR9 | exact Hstk]) ST9)
      as (r10 & RUN10 & I1 & I2 & I8 & I9 & I18 & I3 & I4 & I21 & I22 & I23 & I24 & I25 & I26 & I27).
    assert (GR10 : mem_grows mem (fr_b5a M9 S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)))) by (eapply mem_grows_trans; [exact GR9|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_b5a in G in change_no_check G' end); grows_tac).
    assert (Q10 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z
                                    /\ (U x < T + 2824 \/ T + 2840 <= U x)%Z) \/ (U S <= U x)%Z ->
                 fr_b5a M9 S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b5a in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. apply Q9. lia. }
    remember (fr_b5a M9 S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128))) as M10 eqn:EM10 in RUN10, GR10, Q10.
    (* [comment removed for export] *)
    assert (RET_G2 : ret_ok (Z_to_bv 64 0x4fda8)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (I4' : getr r10 4 = tp) by rch.
    assert (GH10 : gctH ASEGS asan_gct_tab M10 (at_ S (-2176)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end).
      - xqh GTS Q10 C_kif. - xqh GTS Q10 C_key. - xqh GTS Q10 C_tsdp. - xqh GTS Q10 C_tctx. - xqh GTS Q10 C_thr.
      - unorm. lia.
      - rewrite at_at. eapply (store_ok_sub ASEGS M10 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR10 | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (gct_run ASEGS asan_gct_tab asan_gct_tab_ok M10 rom r10 (Z_to_bv 64 0x4fda8) (at_ S (-2176)) tp tsdp ctxw thr GH10 RET_G2 I1 I2 I4')
      as (r11 & RUN11 & W10 & W11 & AGW).
    cbn [gt_rb asan_gct_tab] in RUN11. rewrite at0_lit in RUN11 by lia. rewrite at_at in RUN11. cbn [Z.add Z.opp Pos.add] in RUN11.
    replace (492476 : word) with (Z_to_bv 64 492476 : word) in RUN10 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (GR11 : mem_grows mem (wbytes M10 (at_ S (-2184)) (LE8 (Z_to_bv 64 0x4fda8)))) by (eapply mem_grows_trans; [exact GR10|]; grows_tac).
    assert (Q11 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z
                                    /\ (U x < T + 2824 \/ T + 2840 <= U x)%Z) \/ (U S <= U x)%Z ->
                 wbytes M10 (at_ S (-2184)) (LE8 (Z_to_bv 64 0x4fda8)) x = mem x).
    { intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. apply Q10. lia. }
    assert (V2 : getr r11 2 = at_ S (-2176)) by viac AGW (2:reg).
    assert (V9 : getr r11 9 = at_ S (-2128)) by viac AGW (9:reg).
    assert (V10 : getr r11 10 = thr) by exact W10.
    (* [comment removed for export] *)
    destruct (rdn_defined_ex ASEGS MU (at_ S (-2120)) 8) as [bsz [Rsz Lsz]].
    { intros i Hi. rewrite at_u in Hi by lia. apply GRU.
      (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1 in G in change_no_check G' end). pose proof (u64_range S).
      rewrite (wbytes_outside); [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, !at_u by lia; wd_ulia_c ].
      rewrite wbytes_inside; [ discriminate | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, !at_u by lia; wd_ulia_c ]. }
    { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    destruct (b5b_run (wbytes M10 (at_ S (-2184)) (LE8 (Z_to_bv 64 0x4fda8))) rom S T tctx bsz r11 V2 V9 V10 ltac:(hlia) ltac:(hlia) ltac:(hlia))
      as (r12 & RUN12 & J1 & J2 & J9 & J10 & J11 & J19 & J20 & J3 & J4 & J8 & J18 & J21 & J22 & J23 & J24 & J25 & J26 & J27).
    { xqh GTS Q11 C_T0. }
    { xqh GTS Q11 C_tid. }
    { (* [comment removed for export] *)
      rewrite EM10, EM9, EM8, EM7, EM6, EM5, EM4. (lazymatch goal with |- ?G => let G' := eval unfold fr_b5a, fr_b4b, fr_b4a, fr_b3, fr_b2, fr_b1 in G in change_no_check G' end).
      repeat (rewrite rdn_wbytes_out; [ | first [solve [clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT; rd8_side] | rd8_side] | first [solve [clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT; rd8_side] | rd8_side] | first [solve [clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT; rd8_side] | rd8_side] ]).
      eapply rd_same; [ intros x Hx; destruct (decide (MU x = M3 x)) as [E|NE]; [rewrite E; reflexivity | exfalso; pose proof (FOOTU x NE) as F; revert F Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; intros F Hx; lia]
                      | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | ].
      (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). dig. }
    { rewrite EM10, EM9, EM8, EM7, EM6, EM5, EM4. (lazymatch goal with |- ?G => let G' := eval unfold fr_b5a, fr_b4b, fr_b4a, fr_b3, fr_b2, fr_b1 in G in change_no_check G' end).
      repeat (rewrite rdn_wbytes_out; [ | first [solve [clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT; rd8_side] | rd8_side] | first [solve [clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT; rd8_side] | rd8_side] | first [solve [clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT; rd8_side] | rd8_side] ]). exact Rsz. }
    { exact Lsz. }
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x6e490 : word) with (0x6e490 : word) in RUNU by (apply bv_eq; reflexivity).
    replace (0x77594 : word) with (Z_to_bv 64 0x77594 : word) in RUN9 by (apply bv_eq; reflexivity).
    replace (0x4fda8 : word) with (Z_to_bv 64 0x4fda8 : word) in RUN12 by (apply bv_eq; reflexivity).
    exists r12, MU, sz, bsz.
    split.
    { subst M10 M9 M8 M7 M6 M5 M4. (lazymatch goal with |- ?G => let G' := eval unfold fr_P2 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUNU|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|].
      eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
      eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11|].
      exact RUN12. }
    rewrite !at_at in RDsz, RDpc. cbn [Z.add Z.opp Pos.add Z.pos_sub] in RDsz, RDpc.
    repeat match goal with |- _ /\ _ => split end; try assumption; try rch; try (viac AGW (8:reg)); try (viac AGW (18:reg));
      try (viac AGW (21:reg)); try (viac AGW (22:reg)); try (viac AGW (3:reg)); try (viac AGW (4:reg)); try (viac AGW (23:reg));
      try (viac AGW (24:reg)); try (viac AGW (25:reg)); try (viac AGW (26:reg)); try (viac AGW (27:reg)); try lia.
    intros x Hx. pose proof (FOOTU x Hx) as F. revert F. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. intros F. lia.
  Qed.
End RUNI.


End FPGen.

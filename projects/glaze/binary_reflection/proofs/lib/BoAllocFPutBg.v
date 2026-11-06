(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFBg1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen.
Context {fx : FPState}.

Section CB1A.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 : word) (T n id : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2176).
  Hypothesis H8 : getr regs 8 = at_ p (-16).
  Hypothesis H9 : getr regs 9 = at_ S (-2128).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 id.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 0x10ab58.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 0.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 T.
  Hypothesis H21 : getr regs 21 = x21.
  Hypothesis H22 : getr regs 22 = x22.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (AIMGHI + 16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hn : (2 ^ 28 < n <= 2 ^ 40)%Z.
  Hypothesis Hid : (0 <= id < 2 ^ 32)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis Hokp : store_ok BSEGS mem p 8 = true.
  Hypothesis Rq0 : rdn BSEGS mem (at_ S (-2136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6ef14)).
  Hypothesis Rq1 : rdn BSEGS mem (at_ S (-2144)) 8 = Some (word_to_le_bytes 8 S).
  Hypothesis Rq2 : rdn BSEGS mem (at_ S (-2152)) 8 = Some (word_to_le_bytes 8 p).
  Hypothesis Rq3 : rdn BSEGS mem (at_ S (-2160)) 8 = Some (word_to_le_bytes 8 x18).
  Hypothesis Rq4 : rdn BSEGS mem (at_ S (-2168)) 8 = Some (word_to_le_bytes 8 x19).
  Hypothesis Rq5 : rdn BSEGS mem (at_ S (-2176)) 8 = Some (word_to_le_bytes 8 x20).
  Hypothesis Rnhi : rdn BSEGS mem (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis Rnlo : rdn BSEGS mem (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))).
  Hypothesis Rmcs : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis Rmsz : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 28))).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma n_split3b : (0 <= n / 2 ^ 32 < 2 ^ 9 /\ 0 <= n mod 2 ^ 32 < 2 ^ 32 /\ n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n
                    /\ id * 2 ^ 32 / 2 ^ 32 = id)%Z.
  Proof using Hid Hn x22 rom. clear - Hid Hn x22 rom. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). repeat split; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma cb1a_run :
    exists r,
      msteps BSEGS (mkst regs (0x50838 : word) mem rom) (mkst r (0x5099c : word) (fr_c1 mem S p x18 x19 x20 x21 x22 id T) rom)
      /\ getr r 1 = Z_to_bv 64 0x6ef14 /\ getr r 2 = at_ S (-2208)
      /\ getr r 14 = at_ p (-16) /\ getr r 15 = Z_to_bv 64 n
      /\ getr r 8 = Z_to_bv 64 (0x10ab58 + 728) /\ getr r 9 = at_ (Z_to_bv 64 T) 80
      /\ getr r 18 = x18 /\ getr r 19 = x19 /\ getr r 20 = x20 /\ getr r 21 = x21 /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rmsz Rmcs Rnlo Rnhi Rq5 Rq4 Rq3 Rq2 Rq1 Rq0 Hokp Hstk Hid Hn HT Hp HS H22 H21 H20 H19 H18 H10 H9 H8 H2.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    destruct n_split3b as (Nh & Nl & Nsum & Idd).
    assert (Vh : bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n / 2 ^ 32))).
    { rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2))%Z with (2 ^ 16)%Z. unorm. apply Z.mod_small. lia. }
    assert (Vl : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n mod 2 ^ 32))) by (apply bytes4_small; lia).
    wd_eexists. split.
    - an F_50838 D_50838.                              (* [comment removed for export] *)
      av F_5083c D_5083c (Z_to_bv 64 (id * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      av F_50840 D_50840 (Z_to_bv 64 id) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite Idd; reflexivity).  (* [comment removed for export] *)
      an F_50844 D_50844. rewrite v_or_0_l.            (* [comment removed for export] *)
      fsd F_50848 D_50848 p.                           (* [comment removed for export] *)
      an F_5084c D_5084c.                              (* [comment removed for export] *)
      clhu F_50850 D_50850 (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh.  (* [comment removed for export] *)
      clwu F_50854 D_50854 (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl.  (* [comment removed for export] *)
      an F_50858 D_50858.                              (* [comment removed for export] *)
      an F_5085c D_5085c.                              (* [comment removed for export] *)
      av F_50860 D_50860 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      an F_50864 D_50864.                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia).
      an F_50868 D_50868.                              (* [comment removed for export] *)
      an F_5086c D_5086c.                              (* [comment removed for export] *)
      cld8 F_50870 D_50870 (Z_to_bv 64 0x6ef14) Rq0.   (* [comment removed for export] *)
      cld8 F_50874 D_50874 S Rq1.                      (* [comment removed for export] *)
      cld8 F_50878 D_50878 p Rq2.                      (* [comment removed for export] *)
      cld8 F_5087c D_5087c x18 Rq3.                    (* [comment removed for export] *)
      cld8 F_50880 D_50880 x19 Rq4.                    (* [comment removed for export] *)
      cld8 F_50884 D_50884 x20 Rq5.                    (* [comment removed for export] *)
      an F_50888 D_50888.                              (* [comment removed for export] *)
      an F_5088c D_5088c.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      an F_50958 D_50958.                              (* [comment removed for export] *)
      fsd F_5095c D_5095c (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_50960 D_50960 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_50964 D_50964 (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_50968 D_50968 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_5096c D_5096c (at_ S (-2168)).             (* [comment removed for export] *)
      fsd F_50970 D_50970 (at_ S (-2176)).             (* [comment removed for export] *)
      fsd F_50974 D_50974 (at_ S (-2184)).             (* [comment removed for export] *)
      fsd F_50978 D_50978 (at_ S (-2192)).             (* [comment removed for export] *)
      an F_5097c D_5097c.                              (* [comment removed for export] *)
      fsd F_50980 D_50980 (at_ S (-2208)).             (* [comment removed for export] *)
      fsd F_50984 D_50984 (at_ S (-2200)).             (* [comment removed for export] *)
      cld8 F_50988 D_50988 (Z_to_bv 64 (2 ^ 20)) Rmcs.  (* [comment removed for export] *)
      an F_5098c D_5098c.                              (* [comment removed for export] *)
      ab_ft F_50990 D_50990 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50994 D_50994 (Z_to_bv 64 (2 ^ 28)) Rmsz.  (* [comment removed for export] *)
      ab_ft F_50998 D_50998 ltac:(condz).              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_c1 mem S p x18 x19 x20 x21 x22 id T). wd_refl.
    - post. all: apply bv_eq; reflexivity.
  Qed.
End CB1A.

Section CB1B.
  Variables (mem rom : word -> option byte) (S mw : word) (spb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H14 : getr regs 14 = mw.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hsec : (bv_unsigned mw < spb \/ spb + 2 ^ 37 <= bv_unsigned mw)%Z.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spb)).

  Lemma cb1b_run :
    exists r,
      msteps BSEGS (mkst regs (0x5099c : word) mem rom) (mkst r (0x4e8a4 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x50a18 /\ getr r 2 = at_ S (-2208) /\ getr r 10 = at_ S (-2208) /\ getr r 11 = mw
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4.
  Proof using Rspb Hsec Hspb H14 H2 spb.
    pose proof (u64_range mw) as Hmr.
    destruct (Z_lt_le_dec (bv_unsigned mw) spb) as [LO | HI].
    - wd_eexists. split.
      + an F_5099c D_5099c.                              (* [comment removed for export] *)
        cld8 F_509a0 D_509a0 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
        ab_tk F_509a4 D_509a4 ltac:(condz).              (* [comment removed for export] *)
        an F_50a0c D_50a0c.                              (* [comment removed for export] *)
        an F_50a10 D_50a10.                              (* [comment removed for export] *)
        an F_50a14 D_50a14.                              (* [comment removed for export] *)
        wd_refl.
      + post. all: try (apply bv_eq; reflexivity).
    - assert (HI2 : (spb + 2 ^ 37 <= bv_unsigned mw)%Z) by (destruct Hsec; lia).
      wd_eexists. split.
      + an F_5099c D_5099c.
        cld8 F_509a0 D_509a0 (Z_to_bv 64 spb) Rspb.
        ab_ft F_509a4 D_509a4 ltac:(condz).              (* [comment removed for export] *)
        an F_509a8 D_509a8.                              (* [comment removed for export] *)
        av F_509ac D_509ac (Z_to_bv 64 (2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
        av F_509b0 D_509b0 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
        ab_tk F_509b4 D_509b4 ltac:(condz).              (* [comment removed for export] *)
        an F_50a0c D_50a0c.
        an F_50a10 D_50a10.
        an F_50a14 D_50a14.
        wd_refl.
      + post. all: try (apply bv_eq; reflexivity).
  Qed.
End CB1B.

Section CB3.
  Variables (mem rom : word -> option byte) (T qb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = at_ (Z_to_bv 64 T) 80.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 (2 ^ 20).
  Hypothesis HT : (4096 <= T /\ T + 4096 <= 2 ^ 47)%Z.
  Hypothesis Hqb : (0 <= qb <= 2 ^ 20)%Z.
  Hypothesis Rqb : rdn BSEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb)).

  Lemma cb3_run :
    exists r,
      msteps BSEGS (mkst regs (0x50a18 : word) mem rom) (mkst r (0x50a34 : word) mem rom)
      /\ getr r 1 = getr regs 1 /\ getr r 2 = getr regs 2 /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4.
  Proof using Rqb Hqb HT H22 H9 qb T.
    assert (Rqb' : rdn BSEGS mem (at_ (at_ (Z_to_bv 64 T) 80) 24) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb))).
    { replace (at_ (at_ (Z_to_bv 64 T) 80) 24) with (Z_to_bv 64 (T + 104)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). exact Rqb. }
    wd_eexists. split.
    - cld8 F_50a18 D_50a18 (Z_to_bv 64 qb) Rqb'.        (* [comment removed for export] *)
      ab_tk F_50a1c D_50a1c ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End CB3.
End FPGen.
End BoAllocFBg1.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFBgM.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section C1MEM.
  Context {fx : FPState}.
  Variables (mem : word -> option byte) (S p x18 x19 x20 x21 x22 : word) (T id : Z).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584.

  #[local] Abbreviation MC := (fr_c1 mem S p x18 x19 x20 x21 x22 id T).
  Ltac prep := pose proof (u64_range S) as HSr; pose proof (u64_range p) as Hpr.
  Ltac lsideC := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac rdC := (lazymatch goal with |- ?G => let G' := eval unfold fr_c1 in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); rewrite ?at_at; repeat (wd_rdstep rd8_side).

  Lemma fr_c1_outside : forall a : word, (U a < U S - 2208 \/ U S - 2128 <= U a) -> (U a < U p \/ U p + 8 <= U a) -> MC a = mem a.
  Proof using Gp GS. prep. intros a A1 A2. (lazymatch goal with |- ?G => let G' := eval unfold fr_c1 in G in change_no_check G' end). rewrite !wbytes_outside by lsideC. reflexivity. Qed.
  Lemma fr_c1_foot : forall a : word, MC a <> mem a -> (U S - 2208 <= U a < U S - 2128) \/ (U p <= U a < U p + 8).
  Proof using Gp GS.
    prep. intros a NE. destruct (decide (U S - 2208 <= U a < U S - 2128)); [tauto|]. destruct (decide (U p <= U a < U p + 8)); [tauto|].
    exfalso. apply NE. apply fr_c1_outside; lia.
  Qed.
  Lemma fr_c1_grows : mem_grows mem MC.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_c1 in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.


  (* [comment removed for export] *)
  Lemma fr_c1_q0 : rdn BSEGS MC (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).        Proof using GS. prep. rdC. Qed.
  Lemma fr_c1_q1 : rdn BSEGS MC (at_ S (-2144)) 8 = Some (LE8 S).                           Proof using GS. prep. rdC. Qed.
  Lemma fr_c1_q2 : rdn BSEGS MC (at_ S (-2152)) 8 = Some (LE8 p).                           Proof using GS. prep. rdC. Qed.
  Lemma fr_c1_q3 : rdn BSEGS MC (at_ S (-2160)) 8 = Some (LE8 x18).                         Proof using GS. prep. rdC. Qed.
  Lemma fr_c1_q4 : rdn BSEGS MC (at_ S (-2168)) 8 = Some (LE8 x19).                         Proof using GS. prep. rdC. Qed.
  Lemma fr_c1_q5 : rdn BSEGS MC (at_ S (-2176)) 8 = Some (LE8 x20).                         Proof using GS. prep. rdC. Qed.
  Lemma fr_c1_q6 : rdn BSEGS MC (at_ S (-2184)) 8 = Some (LE8 x21).                         Proof using GS. prep. rdC. Qed.
  Lemma fr_c1_q7 : rdn BSEGS MC (at_ S (-2192)) 8 = Some (LE8 x22).                         Proof using GS. prep. rdC. Qed.


  (* [comment removed for export] *)
  Lemma fr_c1_rdn_out : forall (a : word) n bs, (U a + Z.of_nat n <= U S - 2208 \/ U S - 2128 <= U a) -> (U a + Z.of_nat n <= U p \/ U p + 8 <= U a) ->
    U a + Z.of_nat n <= 2 ^ 64 -> rdn BSEGS mem a n = Some bs -> rdn BSEGS MC a n = Some bs.
  Proof using Gp GS.
    prep. intros a n bs A1 A2 A3 Hr. apply (rd_same BSEGS MC mem); [| exact A3 | exact Hr].
    intros x Hx. apply fr_c1_outside; lia.
  Qed.
End C1MEM.
End BoAllocFBgM.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemM OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.BoAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB.BoAllocFRunM OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemM OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB.BoAllocFTail.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKSL. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94.AsAinvOpsRc93 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc94 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB.BoAllocF6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcHS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcGS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKSL.BoAllocFRcGL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKSL BoAllocFBg1 BoAllocFBgM OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Section PUTBG.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis SECC : sec_cells bt TSDP.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis SHGATE : HYP_SHADOW_GATE_stmt bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Definition free_putBg_stmt : Prop :=
    forall (h : option Z) fx' (R R' : bvmap 5 word) (M M' M0 : mem) (mdl mdl' : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K1 ret sp m : Z) (p : word)
           (st' : ast) (id : Z),
      let S := getr R 2 in
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p ->
      Lc = L1 ++ (U p, m) :: L2 ->
      WF bt st' Lc FF -> Rep bt st' Lc FF M0 mdl' -> bounds st' Lc B C K1 -> HPc h st' ->
      2 ^ 28 < m ->
      FXOK fx' -> m_halted mdl' = None -> BackingAlgebra.model_ivs_wf mdl' ->
      (forall a : word, M' a <> M0 a -> Xd (U S) (U p) T (U a) /\ M' a <> None) ->
      (forall a : word, M' a <> M a ->
          (Xd (U S) (U p) T (U a) \/ (U S - 2176 - KD <= U a < U S - 2176)
           \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
          /\ M' a <> None) ->
      M' (at_ p (-16)) = Some (Z_to_bv 8 3) ->
      rdn BSEGS M' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)) -> rdn BSEGS M' (at_ S (-2144)) 8 = Some (LE8 S) ->
      rdn BSEGS M' (at_ S (-2152)) 8 = Some (LE8 p) -> rdn BSEGS M' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)) ->
      rdn BSEGS M' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) -> rdn BSEGS M' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))) ->
      rdn BSEGS M' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) -> rdn BSEGS M' (at_ S (-16)) 8 = Some (LE8 (getr R 8)) ->
      rdn BSEGS M' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) -> rdn BSEGS M' (at_ S (-32)) 8 = Some (LE8 (getr R 18)) ->
      rdn BSEGS M' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) -> rdn BSEGS M' (at_ S (-48)) 8 = Some (LE8 (getr R 20)) ->
      rdn BSEGS M' (at_ S (-56)) 8 = Some (LE8 (getr R 21)) ->
      getr R' 2 = at_ S (-2176) -> getr R' 8 = at_ p (-16) -> getr R' 9 = at_ S (-2128) -> getr R' 10 = Z_to_bv 64 id ->
      getr R' 18 = Z_to_bv 64 (IB bt) -> getr R' 19 = Z_to_bv 64 0 -> getr R' 20 = Z_to_bv 64 T -> getr R' 21 = at_ S (-81) ->
      getr R' 22 = getr R 22 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
      getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 -> getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 ->
      0 <= id < 2 ^ 32 ->
      same_except_vm mdl mdl' -> lazy_kept (bt_ia bt) Lc FF mdl mdl' ->
      katD BSEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS)) mdl')
           (free_post BSEGS FXOK both_addrs (AAINV_F bt HP) h MSTK_A R M mdl (L1 ++ L2) FF
                      (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) K1 ret sp).

  Theorem free_putBg : free_putBg_stmt.
  Proof using FAM SHGATE BOOTG HTP G_KD SECC RCC CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_putBg_stmt in G in change_no_check G' end).
    intros h fx' R R' M M' M0 mdl mdl' Lc FF La Lb B C K1 ret sp m p st' id CP HR10 ELc W' RP' BD' HLE BIG
           HFX' HH' MW' DX CHG Hb16 Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6
           Y2 Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y22 Y3 Y4 Y23 Y24 Y25 Y26 Y27 Hid SEV LZ.
    pose proof ceil_rng as CR.
    (* [comment removed for export] *)
    assert (PCcb : (0x4e8a4%bv : word) = Z_to_bv 64 0x4e8a4) by (apply bv_eq; reflexivity).
    assert (PC84 : (0x50a18%bv : word) = Z_to_bv 64 0x50a18) by (apply bv_eq; reflexivity).
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. fold tp in Y4.
    assert (Utp : U tp = 0x641380) by (rewrite CP4; vm_compute; reflexivity).
    unfold IB in Y18. rewrite BT_ia in Y18. cbn [ia_instance both_addrs] in Y18.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & _).
    pose proof CELLNB as CELL_spb. unfold free_cells_nb, IB in CELL_spb. rewrite BT_ia in CELL_spb. cbn [ia_instance both_addrs] in CELL_spb.
    pose proof (free_obls_pf bt) as
      (OBL_nolazy_rt & OBL_freed_private & OBL_rt_private & _ & OBL_blk_geom & _ & OBL_hdr_writable & _ & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_freed_private_stmt in OBL_freed_private. unfold OBL_rt_private_stmt in OBL_rt_private.
    unfold OBL_blk_geom_stmt in OBL_blk_geom. unfold OBL_hdr_writable_stmt in OBL_hdr_writable.
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    destruct (live_range bt st' Lc FF W' (U p) m HinP) as (Lp1 & Lp2 & Lp3 & Lp4).
    destruct (OBL_blk_geom st' Lc FF (U p) m W' HinP) as (GpT & GCp & (AB1 & AB2 & AB3 & AB4)).
    pose proof (blk_above_img bt st' Lc FF W' ltac:((lazymatch goal with |- ?G => let G' := eval unfold img_lo_small in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) (U p) m HinP) as PIMG.
    destruct (up8_facts m ltac:(lia)) as (U8a & U8b & U8c & U8d).
    pose proof (thread_dyn bt st' Lc FF W') as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (QA : 0 <= q_bytes (a_tq st') <= 2 ^ 20).
    { pose proof W' as (_ & _ & (QT & _ & QTB & _) & _). rewrite Forall_forall in QT.
      assert (IT : forall b0 m0 n0, In b0 (a_tq st') -> In (m0, n0) (ba_items b0) -> 0 <= n0).
      { intros b0 m0 n0 Hb0 Hin. destruct (QT b0 Hb0) as (_ & _ & WI). destruct (WI m0 n0 Hin) as [X _]. lia. }
      pose proof (q_bytes_ge (a_tq st') IT) as G1. unfold BATCHSZ in G1. clear - G1 QTB. split; [lia | exact QTB]. }
    (* [comment removed for export] *)
    assert (HPm : is_primary m = false).
    { destruct (is_primary m) eqn:E; [| reflexivity]. exfalso. apply (is_primary_iff m ltac:(lia)) in E. clear - E BIG. lia. }
    assert (IMGLO : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
    destruct (sec_live_idx bt st' Lc FF W' (U p) m HinP HPm) as (i0 & s0 & Hnth0 & Hs0 & Eus0 & Ens0).
    pose proof (sec_geom bt st' Lc FF W' IMGLO s0 Hs0) as G0. cbv zeta in G0.
    destruct G0 as (_ & _ & _ & _ & _ & G6 & G7 & _ & _ & _ & G11 & _).
    rewrite Eus0 in G6, G7. rewrite Ens0 in G7.
    assert (HSEC : U p - 16 < SBEG \/ SBEG + 2 ^ 37 <= U p - 16) by (unfold KSPACE, PG in G11; clear - G6 G7 G11 Lp3; lia).
    clear G6 G7 G11 Hnth0 Hs0 Eus0 Ens0 i0 s0.
    (* [comment removed for export] *)
    pose proof RP' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R8 as [RH _]. destruct (RH (U p) m HinP) as (Hst & H11 & Hnhi & Hnlo & Hw8 & Hz4 & _).
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    pose proof (OBL_hdr_writable st' Lc FF M0 mdl' (U p) m W' RP' HinP) as WHDR.
    clear R2 R3 R4 R5 R6 R7 R9 R10 R11 R12 R15 R16 R17 R18 RH OBL_hdr_writable.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI, PIMG.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, NMAX, SB, KSPACE, PTRLO in *.
    (* [comment removed for export] *)
    assert (XdC : forall z, AIMGLO <= z < AIMGHI -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite CP2; clear -Hz GTI PIMG CPlo CR HSr; lia).
    assert (XdH : forall z, U p - 15 <= z < U p -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b AB2 CP2 CPlo; lia).
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - CP2 CPlo CPhi CR; lia).
    assert (GS24 : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - GSm; lia).
    assert (Gpm : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584) by (clear - PIMG AB2 U8a BIG CP2 CPlo; lia).
    assert (GTm : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; split; lia | clear - GTC CP2 CPlo; lia]. }
    hidehyp GpT. hidehyp GCp. hidehyp GTI. hidehyp GTB. hidehyp AB4. hidehyp GCI. hidehyp GCB. hidehyp GCT'.
    (* [comment removed for export] *)
    assert (EQ0 : forall a : word, ~ Xd (U S) (U p) T (U a) -> M' a = M0 a).
    { intros a Ha. destruct (decide (M' a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M') by (intros a Ha; destruct (decide (M' a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    assert (GRM : mem_grows M M') by (intros a Ha; destruct (decide (M' a = M a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (CHG a N))]).
    (* [comment removed for export] *)
    set (Hd := HID st' mdl').
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdl' z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHp : forall z, U p - 16 <= z < U p + up8 m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; left. exists (U p), m. split; [exact HinP | exact Hz]. }
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    Ltac cell0 EQ0 NH XD C :=
      rewrite rdn_mrestrict; [ | wd_ulia_c | unorm; hoff NH ];
      eapply rd_same; [ intros x Hx; apply EQ0; apply XD; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | wd_ulia_c | exact C ].
    Ltac konst EQ0 R1 NHs XdC C := cell0 EQ0 NHs XdC (const_cell bt _ _ _ _ R1 C).
    assert (K_mcsz : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20)))) by konst EQ0 R1 NHs XdC CELL_mcsz.
    assert (K_msz : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28)))) by konst EQ0 R1 NHs XdC CELL_msz.
    assert (K_spb : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by konst EQ0 R1 NHs XdC CELL_spb.
    assert (K_nhi : rdn BSEGS (mrestrict Hd M') (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (m / 2 ^ 32)))).
    { replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnhi. }
    assert (K_nlo : rdn BSEGS (mrestrict Hd M') (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (m mod 2 ^ 32)))).
    { replace (at_ p (-12)) with (Z_to_bv 64 (U p - 12)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnlo. }
    clear Hnhi Hnlo R1.
    idtac "PROGRESS Bg: cells".
    (* [comment removed for export] *)
    Ltac stk NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
    assert (S_q0 : rdn BSEGS (mrestrict Hd M') (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14))) by stk NHs Cq0.
    assert (S_q1 : rdn BSEGS (mrestrict Hd M') (at_ S (-2144)) 8 = Some (LE8 S)) by stk NHs Cq1.
    assert (S_q2 : rdn BSEGS (mrestrict Hd M') (at_ S (-2152)) 8 = Some (LE8 p)) by stk NHs Cq2.
    assert (S_q3 : rdn BSEGS (mrestrict Hd M') (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))) by stk NHs Cq3.
    assert (S_q4 : rdn BSEGS (mrestrict Hd M') (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))) by stk NHs Cq4.
    assert (S_q5 : rdn BSEGS (mrestrict Hd M') (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))) by stk NHs Cq5.
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS (mrestrict Hd M') (at_ S (-2304)) 2304 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia.
      eapply store_ok_mono; [exact GRM|]. apply CPstk. cbn in Hx. rewrite <- CP2. lia. }
    assert (SOKp : store_ok BSEGS (mrestrict Hd M') p 8 = true).
    { rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHp].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WHDR); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    clear WHDR.
    assert (Gn : 2 ^ 28 < m <= 2 ^ 40) by (clear - BIG Lp3; lia).
    assert (Gspb : 0 <= SBEG /\ SBEG + 2 ^ 37 < 2 ^ 47) by (clear - SB0 SB1 SBH CR; lia).
    (* [comment removed for export] *)
    destruct (cb1a_run (mrestrict Hd M') (seg_rom BSEGS) S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T m id R'
                Y2 Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y22 GS24 Gpm GTm Gn Hid SOKstk SOKp S_q0 S_q1 S_q2 S_q3 S_q4 S_q5 K_nhi K_nlo K_mcsz K_msz)
      as (r1 & RUN1 & A1 & A2 & A14 & A15 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A3 & A4 & A23 & A24 & A25 & A26 & A27).
    set (MC1 := fr_c1 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) id T) in *.
    assert (K_spb1 : rdn BSEGS MC1 (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))).
    { assert (UI : U (Z_to_bv 64 (0x10ab58 + 32)) = 0x10ab58 + 32) by (clear; apply u_Z2bv; lia).
      assert (O1 : U (Z_to_bv 64 (0x10ab58 + 32)) + Z.of_nat 8 <= U S - 2208 \/ U S - 2128 <= U (Z_to_bv 64 (0x10ab58 + 32))) by (rewrite UI; left; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - CP2 CPlo CR; lia).
      assert (O2 : U (Z_to_bv 64 (0x10ab58 + 32)) + Z.of_nat 8 <= U p \/ U p + 8 <= U (Z_to_bv 64 (0x10ab58 + 32))) by (rewrite UI; left; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear - Gpm; lia).
      assert (O3 : U (Z_to_bv 64 (0x10ab58 + 32)) + Z.of_nat 8 <= 2 ^ 64) by (rewrite UI; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); clear; lia).
      (lazymatch goal with |- ?G => let G' := eval unfold MC1 in G in change_no_check G' end).
      exact (fr_c1_rdn_out (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm Gpm _ _ _ O1 O2 O3 K_spb). }
    assert (Um16 : U (at_ p (-16)) = U p - 16) by (rewrite at_u by (clear - Gpm Hpr; lia); reflexivity).
    destruct (cb1b_run MC1 (seg_rom BSEGS) S (at_ p (-16)) SBEG r1 A2 A14 Gspb ltac:(rewrite Um16; exact HSEC) K_spb1)
      as (r2 & RUN2 & E1 & E2 & E10 & E11 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E3 & E4).
    assert (RUN12 : msteps BSEGS (@mkst fx' R' (0x50838%bv : word) (mrestrict Hd M') (seg_rom BSEGS)) (@mkst fx' r2 (0x4e8a4%bv : word) MC1 (seg_rom BSEGS))).
    { eapply msteps_trans; [exact RUN1 | exact RUN2]. }
    clear RUN1 RUN2.
    idtac "PROGRESS Bg: run".
    (* [comment removed for export] *)
    replace (0x50838%bv : word) with (Z_to_bv 64 0x50838 : word) in RUN12 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st' Lc FF M0 mdl' BT_ia RP') asanF_segs_wx (a_aa st')
             (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS)) (@mkst fx' r2 (0x4e8a4%bv : word) MC1 (seg_rom BSEGS)) mdl').
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH'. }
    { rewrite restrict_mkstF. exact RUN12. }
    clear RUN12 K_mcsz K_msz K_spb K_spb1 K_nhi K_nlo S_q0 S_q1 S_q2 S_q3 S_q4 S_q5 SOKstk SOKp.
    intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS))) with M' by reflexivity.
    pose proof (same_but_materialized_frame mdl' mdl3 SBM3) as SF3.
    destruct SF3 as (_ & Evm3 & Elz3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _).
    set (Mfin := munrestrict Hd M' MC1).
    pose proof (fr_c1_grows (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id) as GR13. fold MC1 in GR13.
    pose proof (fr_c1_foot (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm Gpm) as FT13. fold MC1 in FT13.
    assert (VIS : forall a : word, Hd a = false -> Mfin a = MC1 a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> Mfin a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM' : forall a : word, Hd a = false -> mrestrict Hd M' a = M' a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GRfin' : mem_grows M' Mfin).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GR13. rewrite (MrM' a Eh). exact Ha. }
    assert (GRfin : mem_grows M Mfin) by (eapply mem_grows_trans; [exact GRM | exact GRfin']).
    assert (DIFF3 : forall a : word, Mfin a <> M' a -> (U S - 2208 <= U a < U S - 2128) \/ (U p <= U a < U p + 8)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM' a Eh) in NE. exact (FT13 a NE). }
    (* [comment removed for export] *)
    assert (XS : forall k bs0, -2304 <= k -> k + 8 <= 0 -> rdn BSEGS MC1 (at_ S k) 8 = Some bs0 -> rdn BSEGS Mfin (at_ S k) 8 = Some bs0).
    { intros k bs0 Hk1 Hk2 Hr. apply (rd_same BSEGS Mfin MC1); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range|]. rewrite at_u in Hx by lia. cbn in Hx. lia. }
    assert (XI : forall k bs0, -2128 <= k -> k + 8 <= 0 -> rdn BSEGS M' (at_ S k) 8 = Some bs0 -> rdn BSEGS Mfin (at_ S k) 8 = Some bs0).
    { intros k bs0 Hk1 Hk2 Hr. apply (rd_same BSEGS Mfin M'); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. destruct (decide (Mfin x = M' x)) as [E|N]; [exact E|]. exfalso.
      destruct (DIFF3 x N) as [D|D]; [clear - D Hx Hk1; lia | clear - D Hx Hk1 Gpm; lia]. }
    (* [comment removed for export] *)
    assert (DXfin : forall a : word, Mfin a <> M0 a -> Xd (U S) (U p) T (U a) /\ Mfin a <> None).
    { intros a NE. destruct (decide (Mfin a = M' a)) as [E|N].
      - rewrite E in NE |- *. exact (DX a NE).
      - split.
        + (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end). destruct (DIFF3 a N) as [D|D]; [do 3 right; clear - D; lia | right; left; exact D].
        + (* [comment removed for export] *)
          intros EN. apply N. rewrite EN. destruct (M' a) eqn:EM; [| reflexivity]. exfalso.
          assert (NN : M' a <> None) by (rewrite EM; discriminate). exact (GRfin' a NN EN). }
    idtac "PROGRESS Bg: lift".
    set (S2 := at_ S 192).
    assert (US2 : U S2 = U S + 192) by ((lazymatch goal with |- ?G => let G' := eval unfold S2 in G in change_no_check G' end); rewrite at_u by (clear - GSm HSr; lia); reflexivity).
    set (ret2 := Z_to_bv 64 0x50a18 : word).
    set (cbw := at_ S (-2208)).
    assert (HH3 : m_halted mdl3 = None) by (rewrite Eh3; exact HH').
    assert (RX3 : AsAinvOpsRc73.AsAinvRepX3.RepX bt (Xd (U S) (U p) T) st' Lc FF Mfin mdl3).
    { exists M0. split; [exact (Rep_sbm bt st' Lc FF M0 mdl' mdl3 RP' MI3 SBM3) | exact DXfin]. }
    assert (ELc2 : Lc = La ++ (U p - 16 + 16, m) :: Lb) by (replace (U p - 16 + 16) with (U p) by (clear; lia); exact ELc).
    assert (XSH : forall z, Xd (U S) (U p) T z -> z = U p - 16 \/ U p - 16 + 16 <= z < U p - 16 + 24 \/ (bt_thread bt + 2768 <= z < bt_thread bt + 3168) \/ CEIL <= z).
    { intros z Hz. unfold Xd in Hz. destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [left; exact Hz | right; left; clear - Hz; lia | right; right; left; clear - Hz; lia | right; right; right; clear - Hz CP2 CPlo; lia]. }
    assert (E2' : getr r2 2 = at_ S2 (-2400)) by (rewrite E2; (lazymatch goal with |- ?G => let G' := eval unfold S2 in G in change_no_check G' end); rewrite at_at; reflexivity).
    assert (E11' : getr r2 11 = Z_to_bv 64 (U p - 16)) by (rewrite E11; apply bv_eq; rewrite Um16; clear - Gpm Hpr; wd_ulia).
    assert (E4' : getr r2 4 = Z_to_bv 64 (ia_tp (bt_ia bt))) by (rewrite E4, A4, Y4, BT_ia; exact CP4).
    assert (RET2 : ret_ok ret2) by (apply ret_ok_lit; [clear; lia | reflexivity]).
    assert (SOK2 : forall a : word, U S2 - 3584 <= U a < U S2 - 2400 -> Mfin a <> None /\ store_ok BSEGS Mfin a 1%nat = true).
    { intros a Ha. rewrite US2 in Ha. split.
      - apply GRfin. apply store_ok1_heap; [clear - Ha CPlo CP2 CR; lia|]. apply CPstk. rewrite <- CP2. clear - Ha. lia.
      - eapply store_ok_mono; [exact GRfin|]. apply CPstk. rewrite <- CP2. clear - Ha. lia. }
    rewrite PCcb.
    apply (katD_bind BSEGS _ (sec_live_post bt FXOK (2 ^ 20) (2 ^ 28) st' La Lb FF Mfin mdl3 r2 S2 ret2)).
    { exact (sec_live_pf bt FXOK TP TSDP PGP FL MIDEND CPM BT_segs BT_ia CELLS CELLNB RCC SECC HTP BOOTG SHGATE
               fx' (Xd (U S) (U p) T) (2 ^ 20) (2 ^ 28) st' Lc La Lb FF Mfin mdl3 r2 S2 ret2 cbw (U p - 16) m
               HFX' HH3 (model_ivs_wf_sbm mdl' mdl3 SBM3 MW') W' RX3 ELc2 HPm XSH E1 RET2 E2' E10 E11' E4'
               ltac:(rewrite US2; clear - CP2 CP16; Z.div_mod_to_equations; lia) ltac:(rewrite US2; clear - CP2 CPlo; lia)
               ltac:(rewrite US2; (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end); clear - CP2 CPhi; lia) SOK2). }
    intros c' POST.
    destruct POST as (fx3 & i3 & M3 & mdl4 & R3 & Ec & HFX3 & HH4 & MW4 & W3 & RP3 & FR3 & CH3 & LZ3 & SEV3 & RK3).
    subst c'. rewrite BT_ia in CH3, LZ3.
    idtac "PROGRESS Bg: callback".
    set (st3 := op_sec_free st' i3) in *.
    assert (W3wf : WF bt st3 (La ++ Lb) FF) by exact W3.
    (* [comment removed for export] *)
    pose proof RP3 as (_ & _ & R3c & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13c & _).
    destruct R3c as (_ & _ & _ & _ & _ & _ & TQc & _). destruct TQc as (_ & _ & _ & Cqb). unfold T_QC in Cqb. rewrite BT_segs in Cqb.
    replace (T + 80 + 24) with (T + 104) in Cqb by (clear; lia).
    change (a_tq st3) with (a_tq st') in Cqb.
    set (Hd3 := HID st3 mdl4).
    assert (NHs3 : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd3 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st3 mdl4 z R13c Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT3 : forall z, T <= z < T + 4096 -> Hd3 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (OBL_nolazy_rt st3 (La ++ Lb) FF M3 mdl4 z W3wf RP3). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    (* [comment removed for export] *)
    assert (XF3 : forall k bs0, -2208 <= k -> k + 8 <= 0 -> rdn BSEGS Mfin (at_ S k) 8 = Some bs0 -> rdn BSEGS M3 (at_ S k) 8 = Some bs0).
    { intros k bs0 Hk1 Hk2 Hr. apply (rd_same BSEGS M3 Mfin); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply FR3. rewrite US2. clear - Hx Hk1. lia. }
    Ltac stk3 NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
    Ltac c1cell L := let PM := fresh "PM" in pose proof L as PM; exact PM.
    assert (T_q0 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14))).
    { stk3 NHs3 (XF3 (-2136) _ ltac:(lia) ltac:(lia) (XS (-2136) _ ltac:(lia) ltac:(lia) (fr_c1_q0 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm))). }
    assert (T_q1 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-2144)) 8 = Some (LE8 S)).
    { stk3 NHs3 (XF3 (-2144) _ ltac:(lia) ltac:(lia) (XS (-2144) _ ltac:(lia) ltac:(lia) (fr_c1_q1 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm))). }
    assert (T_q2 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-2152)) 8 = Some (LE8 p)).
    { stk3 NHs3 (XF3 (-2152) _ ltac:(lia) ltac:(lia) (XS (-2152) _ ltac:(lia) ltac:(lia) (fr_c1_q2 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm))). }
    assert (T_q3 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))).
    { stk3 NHs3 (XF3 (-2160) _ ltac:(lia) ltac:(lia) (XS (-2160) _ ltac:(lia) ltac:(lia) (fr_c1_q3 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm))). }
    assert (T_q4 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))).
    { stk3 NHs3 (XF3 (-2168) _ ltac:(lia) ltac:(lia) (XS (-2168) _ ltac:(lia) ltac:(lia) (fr_c1_q4 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm))). }
    assert (T_q5 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))).
    { stk3 NHs3 (XF3 (-2176) _ ltac:(lia) ltac:(lia) (XS (-2176) _ ltac:(lia) ltac:(lia) (fr_c1_q5 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm))). }
    assert (T_q6 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81)))).
    { stk3 NHs3 (XF3 (-2184) _ ltac:(lia) ltac:(lia) (XS (-2184) _ ltac:(lia) ltac:(lia) (fr_c1_q6 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm))). }
    assert (T_q7 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-2192)) 8 = Some (LE8 (getr R 22))).
    { stk3 NHs3 (XF3 (-2192) _ ltac:(lia) ltac:(lia) (XS (-2192) _ ltac:(lia) ltac:(lia) (fr_c1_q7 (mrestrict Hd M') S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) T id GSm))). }
    assert (T_i0 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-8)) 8 = Some (LE8 (Z_to_bv 64 ret))).
    { rewrite <- CP1. stk3 NHs3 (XF3 (-8) _ ltac:(lia) ltac:(lia) (XI (-8) _ ltac:(lia) ltac:(lia) Ci0)). }
    assert (T_i1 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-16)) 8 = Some (LE8 (getr R 8))) by stk3 NHs3 (XF3 (-16) _ ltac:(lia) ltac:(lia) (XI (-16) _ ltac:(lia) ltac:(lia) Ci1)).
    assert (T_i2 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-24)) 8 = Some (LE8 (getr R 9))) by stk3 NHs3 (XF3 (-24) _ ltac:(lia) ltac:(lia) (XI (-24) _ ltac:(lia) ltac:(lia) Ci2)).
    assert (T_i3 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-32)) 8 = Some (LE8 (getr R 18))) by stk3 NHs3 (XF3 (-32) _ ltac:(lia) ltac:(lia) (XI (-32) _ ltac:(lia) ltac:(lia) Ci3)).
    assert (T_i4 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-40)) 8 = Some (LE8 (getr R 19))) by stk3 NHs3 (XF3 (-40) _ ltac:(lia) ltac:(lia) (XI (-40) _ ltac:(lia) ltac:(lia) Ci4)).
    assert (T_i5 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-48)) 8 = Some (LE8 (getr R 20))) by stk3 NHs3 (XF3 (-48) _ ltac:(lia) ltac:(lia) (XI (-48) _ ltac:(lia) ltac:(lia) Ci5)).
    assert (T_i6 : rdn BSEGS (mrestrict Hd3 M3) (at_ S (-56)) 8 = Some (LE8 (getr R 21))) by stk3 NHs3 (XF3 (-56) _ ltac:(lia) ltac:(lia) (XI (-56) _ ltac:(lia) ltac:(lia) Ci6)).
    assert (K_qb3 : rdn BSEGS (mrestrict Hd3 M3) (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes (a_tq st'))))).
    { apply (cellZ_restrict Hd3 M3 (T + 104) 8); [exact Cqb | clear - GT4; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHT3]. }
    idtac "PROGRESS Bg: tail cells".
    (* [comment removed for export] *)
    assert (V2 : getr R3 2 = at_ S (-2208)) by (rewrite (regs_kept_lit r2 R3 2 RK3 eq_refl); exact E2).
    assert (V9 : getr R3 9 = at_ (Z_to_bv 64 T) 80) by (rewrite (regs_kept_lit r2 R3 9 RK3 eq_refl), E9; exact A9).
    assert (V22 : getr R3 22 = Z_to_bv 64 (2 ^ 20)) by (rewrite (regs_kept_lit r2 R3 22 RK3 eq_refl), E22; exact A22).
    assert (RETOK : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_lit; [clear - CPr; lia | exact CPe]).
    destruct (cb3_run (mrestrict Hd3 M3) (seg_rom BSEGS) T (q_bytes (a_tq st')) R3 V9 V22 ltac:(clear - GT4 GTC CR; lia) QA K_qb3)
      as (r4 & RUN4 & F1 & F2 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F3 & F4).
    destruct (q_after_drain (mrestrict Hd3 M3) (seg_rom BSEGS) S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)
                (Z_to_bv 64 ret) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) r4
                ltac:(rewrite F2; exact V2) RETOK T_q0 T_q1 T_q2 T_q3 T_q4 T_q5 T_q6 T_q7 T_i0 T_i1 T_i2 T_i3 T_i4 T_i5 T_i6)
      as (r9 & RUN9 & Z2 & Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z3 & Z4 & Z23 & Z24 & Z25 & Z26 & Z27).
    assert (RUN49 : msteps BSEGS (@mkst fx3 R3 ret2 (mrestrict Hd3 M3) (seg_rom BSEGS)) (@mkst fx3 r9 (Z_to_bv 64 ret) (mrestrict Hd3 M3) (seg_rom BSEGS))).
    { (lazymatch goal with |- ?G => let G' := eval unfold ret2 in G in change_no_check G' end). rewrite <- PC84. eapply msteps_trans; [exact RUN4 | exact RUN9]. }
    clear RUN4 RUN9.
    apply (katD_loads bt BT_ia fx3 st3 (La ++ Lb) FF M3 mdl4 R3 r9 _ _ _ RP3 HH4 RUN49).
    intros mdl5 RP5 HH5 SBM5.
    pose proof (same_but_materialized_frame mdl4 mdl5 SBM5) as (_ & _ & Elz5 & _).
    idtac "PROGRESS Bg: tail run".
    (* [comment removed for export] *)
    assert (PRIVp : forall z, (U p - 16 <= z < U p + up8 m \/ sh_lo (U p) <= z < sh_hi (U p) m) -> rt_priv both_addrs (La ++ Lb) FF z).
    { intros z Hz. exact (OBL_freed_private st' Lc FF La Lb (U p) m z W' ELc Hz). }
    assert (PRIVT : forall z, T <= z < T + 4096 -> rt_priv both_addrs (La ++ Lb) FF z).
    { intros z Hz. destruct (OBL_rt_private st' Lc FF z W') as (Z1' & Z2' & Z3'); [(lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); left; exact Hz|].
      split; [exact Z1'|]. split; [exact Z2'|]. intros V. apply Z3'. rewrite ELc. apply app_visible_mono. exact V. }
    assert (CHGfin : forall a : word, M3 a <> M a -> as_changed both_addrs 3584 (La ++ Lb) FF sp a).
    { intros a NE. pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite <- CP2.
      destruct (decide (M3 a = Mfin a)) as [EQ3|N3].
      2:{ destruct (CH3 a N3) as [D _]. unfold rc_changed in D. rewrite US2, BT_ia in D.
          destruct D as [D|[D|D]]; [left; clear - D; lia | right; left; exact D | right; right; left; exact D]. }
      rewrite EQ3 in NE. destruct (decide (Mfin a = M' a)) as [E|N].
      { rewrite E in NE. destruct (CHG a NE) as [[X|[X|[X|X]]] _].
        - unfold Xd in X. destruct X as [X|[X|[X|X]]].
          + right; left. apply PRIVp. left. clear - X U8a BIG. lia.
          + right; left. apply PRIVp. left. clear - X U8a BIG. lia.
          + right; left. apply PRIVT. clear - X. lia.
          + left. clear - X. lia.
        - left. clear - X G_KD. lia.
        - right; left. destruct X as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. intros V. apply X3. rewrite ELc. apply app_visible_mono. exact V.
        - right; right; left. exact X. }
      destruct (DIFF3 a N) as [X|X]; [left; clear - X; lia | right; left; apply PRIVp; left; clear - X U8a BIG; lia]. }
    idtac "PROGRESS Bg: changed".
    (* [comment removed for export] *)
    assert (DEF3 : forall a : word, ~ rt_priv both_addrs (La ++ Lb) FF (U a) -> Mfin a <> None -> M3 a <> None).
    { intros a NP D. destruct (decide (M3 a = Mfin a)) as [E|N]; [rewrite E; exact D|].
      destruct (CH3 a N) as [_ [D3 | D3]]; [exact D3 | exfalso; exact (NP D3)]. }
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold free_post, cfg in G in change_no_check G' end). exists fx3, r9, M3, mdl5.
    split; [reflexivity|]. split; [exact HFX3|].
    split.
    { (* [comment removed for export] *)
      apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; try reflexivity.
      all: rewrite ?F3, ?F4, ?F23, ?F24, ?F25, ?F26, ?F27;
           rewrite ?(regs_kept_lit r2 R3 3 RK3 eq_refl), ?(regs_kept_lit r2 R3 4 RK3 eq_refl), ?(regs_kept_lit r2 R3 23 RK3 eq_refl),
                   ?(regs_kept_lit r2 R3 24 RK3 eq_refl), ?(regs_kept_lit r2 R3 25 RK3 eq_refl), ?(regs_kept_lit r2 R3 26 RK3 eq_refl),
                   ?(regs_kept_lit r2 R3 27 RK3 eq_refl);
           rewrite ?E3, ?E4, ?E23, ?E24, ?E25, ?E26, ?E27, ?A3, ?A4, ?A23, ?A24, ?A25, ?A26, ?A27; assumption. }
    split; [exact CHGfin|].
    split.
    { (* [comment removed for export] *)
      intros a Hin Da. apply DEF3; [| apply GRfin; exact Da].
      intros (_ & NI & _). apply NI. unfold in_errno, ia_errno in Hin. cbn [ia_tp ia_img_lo ia_img_hi both_addrs] in Hin |- *. clear - Hin. lia. }
    split.
    { (* [comment removed for export] *)
      intros a Ha. rewrite <- CP2 in Ha.
      assert (D1 : Mfin a <> None) by (apply GRfin; apply store_ok1_heap; [clear - Ha CPlo CP2 CR; lia|]; apply CPstk; rewrite <- CP2; exact Ha).
      assert (D3 : M3 a <> None) by (apply DEF3; [intros (LT & _); clear - LT Ha CPlo CP2; lia | exact D1]).
      split; [exact D3 | apply store_ok1_def; exact D3]. }
    split.
    { (* [comment removed for export] *)
      exists st3. split; [exact W3wf|]. split; [exact RP5|]. split; [| exact (model_ivs_wf_sbm mdl4 mdl5 SBM5 MW4)].
      split.
      - pose proof W' as WL. unfold WF in WL. rewrite ELc in WL. pose proof BD' as BDL. rewrite ELc in BDL.
        exact (bounds_sec_free_live bt st' La Lb FF (U p) m i3 B C K1 _ _ WL BDL).
      - apply (hp_fin bt HP HPc FAM h st3). apply (hp_neut bt HP HPc FAM h st' st3 HLE); [| apply fk_sec_free | reflexivity].
        intros h' H'. unfold holes_le in H' |- *. exact H'. }
    split.
    { eapply same_except_vm_trans; [exact SEV|]. eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM3|].
      eapply same_except_vm_trans; [exact SEV3 | apply same_but_materialized_except_vm; exact SBM5]. }
    split; [| exact HH5].
    intros a Ha. transitivity (lzb mdl4 a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz5; reflexivity|].
    transitivity (lzb mdl3 a); [exact (LZ3 a Ha)|].
    transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|]. apply LZ.
    destruct Ha as [V|[V|V]]; [left; rewrite ELc; apply app_visible_mono; exact V | right; left; exact V | right; right; exact V].
  Qed.
End PUTBG.

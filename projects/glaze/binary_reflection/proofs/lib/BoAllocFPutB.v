(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocF3a.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

Section C2A.
  Variables (mem rom : word -> option byte) (S p : word).
  Variables (T n len last cnt bsz qb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 (0x10ab58 + 728).
  Hypothesis H9 : getr regs 9 = at_ (Z_to_bv 64 T) 80.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 n.
  Hypothesis H19 : getr regs 19 = at_ S (-2128).
  Hypothesis H20 : getr regs 20 = at_ (Z_to_bv 64 T) 208.
  Hypothesis H21 : getr regs 21 = at_ p (-16).
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 (2 ^ 20).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (AIMGHI + 16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Hlen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hcnt : (1 <= cnt < 1021)%Z.
  Hypothesis Hbsz : (0 <= bsz < 2 ^ 40)%Z.
  Hypothesis Hqb : (0 <= qb <= 2 ^ 20)%Z.
  (* [comment removed for export] *)
  Hypothesis HlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 (T + 80)) 32 = true.
  Hypothesis Hokb : store_ok BSEGS mem (Z_to_bv 64 last) (Z.to_nat 8192) = true.
  (* [comment removed for export] *)
  Hypothesis Rlen : rdn BSEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 len)).
  Hypothesis Rlast : rdn BSEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 last)).
  Hypothesis Rqb : rdn BSEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb)).
  Hypothesis Rbsz : rdn BSEGS mem (Z_to_bv 64 (last + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 bsz)).
  Hypothesis Rcnt : rdn BSEGS mem (Z_to_bv 64 (last + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 cnt)).

  Lemma c2a_run :
    exists r,
      msteps BSEGS (mkst regs (0x50ae4 : word) mem rom) (mkst r (0x50c04 : word) (fr_c2 mem S p T n last cnt bsz qb) rom)
      /\ getr r 2 = at_ S (-2272) /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rcnt Rbsz Rqb Rlast Rlen Hokb HokT Hstk HlastT Hqb Hbsz Hcnt Hlast Hlen Hn HT HS H22 H21 H20 H19 H18 H9 H8 H2 len.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    wd_eexists. split.
    - an F_50ae4 D_50ae4.                              (* [comment removed for export] *)
      an F_50ae8 D_50ae8.                              (* [comment removed for export] *)
      an F_50aec D_50aec.                              (* [comment removed for export] *)
      an F_50af0 D_50af0.                              (* [comment removed for export] *)
      an F_50af4 D_50af4.                              (* [comment removed for export] *)
      an F_50af8 D_50af8.                              (* [comment removed for export] *)
      an F_50b08 D_50b08.                              (* [comment removed for export] *)
      fsd F_50b0c D_50b0c (at_ S (-2216)).             (* [comment removed for export] *)
      fsd F_50b10 D_50b10 (at_ S (-2224)).             (* [comment removed for export] *)
      fsd F_50b14 D_50b14 (at_ S (-2232)).             (* [comment removed for export] *)
      fsd F_50b18 D_50b18 (at_ S (-2240)).             (* [comment removed for export] *)
      fsd F_50b1c D_50b1c (at_ S (-2248)).             (* [comment removed for export] *)
      fsd F_50b20 D_50b20 (at_ S (-2256)).             (* [comment removed for export] *)
      fsd F_50b24 D_50b24 (at_ S (-2264)).             (* [comment removed for export] *)
      cld8 F_50b28 D_50b28 (Z_to_bv 64 len) Rlen.      (* [comment removed for export] *)
      ab_ft F_50b2c D_50b2c ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50b30 D_50b30 (Z_to_bv 64 last) Rlast.    (* [comment removed for export] *)
      cld8 F_50b34 D_50b34 (Z_to_bv 64 cnt) Rcnt.      (* [comment removed for export] *)
      an F_50b38 D_50b38.                              (* [comment removed for export] *)
      ab_tk F_50b3c D_50b3c ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_50bc4 D_50bc4 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50bc8 D_50bc8 (Z_to_bv 64 bsz) Rbsz.      (* [comment removed for export] *)
      av F_50bcc D_50bcc (Z_to_bv 64 (8 * cnt)) ltac:(valz).          (* [comment removed for export] *)
      av F_50bd0 D_50bd0 (Z_to_bv 64 (cnt + 1)) ltac:(valz).          (* [comment removed for export] *)
      av F_50bd4 D_50bd4 (Z_to_bv 64 (last + 8 * cnt)) ltac:(valz).   (* [comment removed for export] *)
      av F_50bd8 D_50bd8 (Z_to_bv 64 (bsz + n)) ltac:(valz).          (* [comment removed for export] *)
      fsd F_50bdc D_50bdc (Z_to_bv 64 (last + 8)).     (* [comment removed for export] *)
      fsd F_50be0 D_50be0 (Z_to_bv 64 (last + 16)).    (* [comment removed for export] *)
      fsd F_50be4 D_50be4 (Z_to_bv 64 (last + 24 + 8 * cnt)).   (* [comment removed for export] *)
      an F_50be8 D_50be8.                              (* [comment removed for export] *)
      cld8 F_50bf8 D_50bf8 (Z_to_bv 64 qb) Rqb.        (* [comment removed for export] *)
      av F_50bfc D_50bfc (Z_to_bv 64 (qb + n)) ltac:(valz).           (* [comment removed for export] *)
      fsd F_50c00 D_50c00 (Z_to_bv 64 (T + 104)).      (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_c2 mem S p T n last cnt bsz qb). rewrite ?at_0. wd_refl.
    - post.
  Qed.
End C2A.
End FPGen.
End BoAllocF3a.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocF6.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

Section QDRAIN.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 ra0 s0v s1v s2v s3v s4v s5v v1 v3 v4 v5 v6 : word) (T qb2 : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2272).
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 (2 ^ 20).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hqb2 : (2 ^ 20 < qb2 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Re0 : rdn BSEGS mem (at_ S (-2216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50afc)).
  Hypothesis Re1 : rdn BSEGS mem (at_ S (-2224)) 8 = Some (word_to_le_bytes 8 v1).
  Hypothesis Re2 : rdn BSEGS mem (at_ S (-2232)) 8 = Some (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 80)).
  Hypothesis Re3 : rdn BSEGS mem (at_ S (-2240)) 8 = Some (word_to_le_bytes 8 v3).
  Hypothesis Re4 : rdn BSEGS mem (at_ S (-2248)) 8 = Some (word_to_le_bytes 8 v4).
  Hypothesis Re5 : rdn BSEGS mem (at_ S (-2256)) 8 = Some (word_to_le_bytes 8 v5).
  Hypothesis Re6 : rdn BSEGS mem (at_ S (-2264)) 8 = Some (word_to_le_bytes 8 v6).
  Hypothesis Rqb2 : rdn BSEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb2)).
  (* [comment removed for export] *)
  Hypothesis Rcb0 : rdn BSEGS mem (at_ S (-2208)) 8 = Some (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 208)).
  Hypothesis Rcb1 : rdn BSEGS mem (at_ S (-2200)) 8 = Some (word_to_le_bytes 8 (at_ S (-2128))).

  (* [comment removed for export] *)
  Lemma q_drain_call :
    exists r,
      msteps BSEGS (mkst regs (0x50c04 : word) mem rom) (mkst r (0x4e260 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x50a34 /\ getr r 2 = at_ S (-2208)
      /\ getr r 10 = v1 /\ getr r 11 = at_ (Z_to_bv 64 T) 80 /\ getr r 12 = at_ (Z_to_bv 64 T) 208 /\ getr r 13 = at_ S (-2128)
      /\ getr r 8 = v1 /\ getr r 9 = at_ (Z_to_bv 64 T) 80 /\ getr r 18 = v3 /\ getr r 19 = v4 /\ getr r 20 = v5 /\ getr r 21 = v6
      /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rcb1 Rcb0 Rqb2 Re6 Re5 Re4 Re3 Re2 Re1 Re0 Hqb2 HT HS H22 H2 qb2.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2).
    wd_eexists. split.
    - cld8 F_50c04 D_50c04 (Z_to_bv 64 0x50afc) Re0.        (* [comment removed for export] *)
      cld8 F_50c08 D_50c08 v1 Re1.                           (* [comment removed for export] *)
      cld8 F_50c0c D_50c0c (at_ (Z_to_bv 64 T) 80) Re2.     (* [comment removed for export] *)
      cld8 F_50c10 D_50c10 v3 Re3.                           (* [comment removed for export] *)
      cld8 F_50c14 D_50c14 v4 Re4.                           (* [comment removed for export] *)
      cld8 F_50c18 D_50c18 v5 Re5.                           (* [comment removed for export] *)
      cld8 F_50c1c D_50c1c v6 Re6.                           (* [comment removed for export] *)
      an F_50c20 D_50c20.                              (* [comment removed for export] *)
      rt F_50c24 D_50c24.                              (* [comment removed for export] *)
      cld8 F_50afc D_50afc (Z_to_bv 64 qb2) Rqb2.      (* [comment removed for export] *)
      ab_tk F_50b00 D_50b00 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50a20 D_50a20 (at_ (Z_to_bv 64 T) 208) Rcb0.   (* [comment removed for export] *)
      cld8 F_50a24 D_50a24 (at_ S (-2128)) Rcb1.           (* [comment removed for export] *)
      an F_50a28 D_50a28.                              (* [comment removed for export] *)
      an F_50a2c D_50a2c.                              (* [comment removed for export] *)
      an F_50a30 D_50a30.                              (* [comment removed for export] *)
      rewrite ?at_0. wd_refl.
    - post.
  Qed.
End QDRAIN.

Section QAFTER.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 ra0 s0v s1v s2v s3v s4v s5v : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Rq0 : rdn BSEGS mem (at_ S (-2136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6ef14)).
  Hypothesis Rq1 : rdn BSEGS mem (at_ S (-2144)) 8 = Some (word_to_le_bytes 8 S).
  Hypothesis Rq2 : rdn BSEGS mem (at_ S (-2152)) 8 = Some (word_to_le_bytes 8 p).
  Hypothesis Rq3 : rdn BSEGS mem (at_ S (-2160)) 8 = Some (word_to_le_bytes 8 x18).
  Hypothesis Rq4 : rdn BSEGS mem (at_ S (-2168)) 8 = Some (word_to_le_bytes 8 x19).
  Hypothesis Rq5 : rdn BSEGS mem (at_ S (-2176)) 8 = Some (word_to_le_bytes 8 x20).
  Hypothesis Rq6 : rdn BSEGS mem (at_ S (-2184)) 8 = Some (word_to_le_bytes 8 x21).
  Hypothesis Rq7 : rdn BSEGS mem (at_ S (-2192)) 8 = Some (word_to_le_bytes 8 x22).
  Hypothesis Ri0 : rdn BSEGS mem (at_ S (-8)) 8 = Some (word_to_le_bytes 8 ra0).
  Hypothesis Ri1 : rdn BSEGS mem (at_ S (-16)) 8 = Some (word_to_le_bytes 8 s0v).
  Hypothesis Ri2 : rdn BSEGS mem (at_ S (-24)) 8 = Some (word_to_le_bytes 8 s1v).
  Hypothesis Ri3 : rdn BSEGS mem (at_ S (-32)) 8 = Some (word_to_le_bytes 8 s2v).
  Hypothesis Ri4 : rdn BSEGS mem (at_ S (-40)) 8 = Some (word_to_le_bytes 8 s3v).
  Hypothesis Ri5 : rdn BSEGS mem (at_ S (-48)) 8 = Some (word_to_le_bytes 8 s4v).
  Hypothesis Ri6 : rdn BSEGS mem (at_ S (-56)) 8 = Some (word_to_le_bytes 8 s5v).

  (* [comment removed for export] *)
  Lemma q_after_drain :
    exists r,
      msteps BSEGS (mkst regs (0x50a34 : word) mem rom) (mkst r ra0 mem rom)
      /\ getr r 2 = S /\ getr r 1 = ra0 /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = x22
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Ri6 Ri5 Ri4 Ri3 Ri2 Ri1 Ri0 Rq7 Rq6 Rq5 Rq4 Rq3 Rq2 Rq1 Rq0 Hret H2 x21 x20 x19 x18 p.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_50a34 D_50a34 (Z_to_bv 64 0x6ef14) Rq0.   (* [comment removed for export] *)
      cld8 F_50a38 D_50a38 S Rq1.                      (* [comment removed for export] *)
      cld8 F_50a3c D_50a3c p Rq2.                      (* [comment removed for export] *)
      cld8 F_50a40 D_50a40 x18 Rq3.                    (* [comment removed for export] *)
      cld8 F_50a44 D_50a44 x19 Rq4.                    (* [comment removed for export] *)
      cld8 F_50a48 D_50a48 x20 Rq5.                    (* [comment removed for export] *)
      cld8 F_50a4c D_50a4c x21 Rq6.                    (* [comment removed for export] *)
      cld8 F_50a50 D_50a50 x22 Rq7.                    (* [comment removed for export] *)
      an F_50a54 D_50a54.                              (* [comment removed for export] *)
      rt F_50a58 D_50a58.                              (* [comment removed for export] *)
      an F_6ef14 D_6ef14.                              (* [comment removed for export] *)
      cld8 F_6ef18 D_6ef18 ra0 Ri0.                    (* [comment removed for export] *)
      cld8 F_6ef1c D_6ef1c s0v Ri1.                    (* [comment removed for export] *)
      cld8 F_6ef20 D_6ef20 s1v Ri2.                    (* [comment removed for export] *)
      cld8 F_6ef24 D_6ef24 s2v Ri3.                    (* [comment removed for export] *)
      cld8 F_6ef28 D_6ef28 s3v Ri4.                    (* [comment removed for export] *)
      cld8 F_6ef2c D_6ef2c s4v Ri5.                    (* [comment removed for export] *)
      cld8 F_6ef30 D_6ef30 s5v Ri6.                    (* [comment removed for export] *)
      an F_6ef34 D_6ef34.                              (* [comment removed for export] *)
      aret F_6ef38 D_6ef38 ra0.                        (* [comment removed for export] *)
      rewrite ?at_0. wd_refl.
    - post.
  Qed.
End QAFTER.
End FPGen.
End BoAllocF6.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRunM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 BoAllocF3a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.BoAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Section RUNM.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S p ra0 tp x22 s0v s1v s2v s3v s4v s5v : word) (T n n8 id fl last cnt bsz qb len : Z) (cpm : byte) (midend : word).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 2 = at_ S (-2176).
  Hypothesis D8 : getr rD 8 = at_ p (-16).
  Hypothesis D9 : getr rD 9 = at_ S (-2128).
  Hypothesis D10 : getr rD 10 = Z_to_bv 64 id.
  Hypothesis D18 : getr rD 18 = Z_to_bv 64 0x10ab58.
  Hypothesis D19 : getr rD 19 = Z_to_bv 64 0.
  Hypothesis D20 : getr rD 20 = thr.
  Hypothesis D21 : getr rD 21 = at_ S (-81).
  Hypothesis D22 : getr rD 22 = x22.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + n8 <= T \/ T + 4096 <= U p - 16)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis Gid : (0 <= id < 2 ^ 32)%Z.
  Hypothesis Gfl : (0 <= fl /\ fl + 4096 <= AIMGHI)%Z.
  Hypothesis Glast : (0x10007fff8000 <= last /\ last + 8192 <= U S - 3584)%Z.
  Hypothesis GlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Glastp : (last + 8192 <= U p - 16 \/ U p + n8 <= last)%Z.
  Hypothesis Gcnt : (1 <= cnt < 1021)%Z.
  Hypothesis Gbsz : (0 <= bsz < 2 ^ 40)%Z.
  Hypothesis Gqb : (0 <= qb <= 2 ^ 20)%Z.
  Hypothesis Glen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Gmid : (U midend < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2304)) 2304 = true.
  Hypothesis Okp : store_ok BSEGS memD p 8 = true.
  Hypothesis Oksh : store_ok BSEGS memD (Z_to_bv 64 (shad p)) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS memD (Z_to_bv 64 (T + 80)) 32 = true.
  Hypothesis Okb : store_ok BSEGS memD (Z_to_bv 64 last) (Z.to_nat 8192) = true.
  (* [comment removed for export] *)
  Hypothesis C_q0 : rdn BSEGS memD (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).
  Hypothesis C_q1 : rdn BSEGS memD (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C_q2 : rdn BSEGS memD (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C_q3 : rdn BSEGS memD (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).
  Hypothesis C_q4 : rdn BSEGS memD (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis C_q5 : rdn BSEGS memD (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).
  Hypothesis C_nhi : rdn BSEGS memD (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS memD (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_mcs : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis C_msz : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis C_gfl : rdn BSEGS memD (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 fl)).
  Hypothesis C_mff : rdn BSEGS memD (Z_to_bv 64 (fl + 48)) 4 = Some (LE4 0).
  Hypothesis C_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_len : rdn BSEGS memD (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis C_last : rdn BSEGS memD (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 last)).
  Hypothesis C_qb : rdn BSEGS memD (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis C_bsz : rdn BSEGS memD (Z_to_bv 64 (last + 8)) 8 = Some (LE8 (Z_to_bv 64 bsz)).
  Hypothesis C_cnt : rdn BSEGS memD (Z_to_bv 64 (last + 16)) 8 = Some (LE8 (Z_to_bv 64 cnt)).

  Theorem run_m3 :
    exists r,
      msteps BSEGS (mkst rD (0x50838 : word) memD rom) (mkst r (0x50c04 : word) (fr_P3 memD S p x22 T n n8 id last cnt bsz qb) rom)
      /\ getr r 2 = at_ S (-2272) /\ getr r 22 = Z_to_bv 64 (2 ^ 20) /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
      /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24 /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.
  Proof using C_cnt C_bsz C_qb C_last C_len C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh C_mff C_gfl C_msz C_mcs C_nlo C_nhi C_q5 C_q4 C_q3 C_q2 C_q1 C_q0 Okb OkT Oksh Okp Hstk Glen Gqb Gbsz Gcnt Glastp GlastT Glast Gfl Gid Gn8 Gn GpT GT Gp GS D4 D22 D21 D20 D19 D18 D10 D9 D8 D1 midend cpm len fl.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    destruct GS as (GS1 & GS2 & GS3). destruct Gp as (Gp1 & Gp2 & Gp3). destruct GT as (GT1 & GT2). destruct GT2 as [GTS GT2]. destruct Gp2 as [GpS Gp2]. destruct Gn8 as (N8a & N8b & N8c & N8d).
    Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    Ltac xqh TS Q H := unfold hideW in TS; xq Q H.
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); notin)); rch.
    (* [comment removed for export] *)
    destruct (c1_run memD rom S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 T n id fl n8 rD
                D1 D8 D9 D10 D18 D19 D20 D21 D22 ltac:(hlia) ltac:(hlia) ltac:(hlia) Gn Gid ltac:(hlia) N8a Hstk Okp
                C_q0 C_q1 C_q2 C_q3 C_q4 C_q5 C_nhi C_nlo C_mcs C_msz C_gfl C_mff)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A3 & A4 & A23 & A24 & A25 & A26 & A27).
    set (M12t := fr_c1 memD S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T) in RUN1.
    assert (GR12 : mem_grows memD M12t) by ((lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end); grows_tac).
    assert (Q12 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M12t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by (first [clear - GS | idtac]; lia); try (first [clear - Gn8 Gp GS Hx | idtac]; lia). reflexivity. }
    remember M12t as M12 eqn:EM12 in RUN1, GR12, Q12. subst M12t.
    (* [comment removed for export] *)
    assert (PH : poisonH BSEGS both_poison_tab M12 p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50ae4) (at_ S (-2208)) cpm midend 0).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm pt_base pt_mset both_poison_tab] in G in change_no_check G' end).
      - xq Q12 C_gsh. - xq Q12 C_sh. - xq Q12 C_gmb. - xq Q12 C_mb. - xq Q12 C_gme. - xq Q12 C_me. - xq Q12 C_ghe. - xq Q12 C_he.
      - xq Q12 C_grm. - xq Q12 C_rm.
      - vm_compute. discriminate.
      - apply ret_ok_even. reflexivity.
      - intros _. split; [xq Q12 C_cpm | exact C_cpm1].
      - intros Hz. exfalso. revert Hz. unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
        first [clear - GS | idtac]; (repeat constructor; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]).
      - destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & M8 & _). exact M8.
      - unorm. exact N8c.
      - unorm. unfold hideW in GpS. destruct GpS as [PS|PS]; [right | left]; lia.
      - rewrite at_u by lia. lia.
      - eapply (store_ok_sub BSEGS M12 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR12 | exact Hstk] | rewrite !at_at, !at_u; lia | rewrite !at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. eapply store_ok_mono; [exact GR12 | exact Oksh].
      - apply ret_ok_lit; [lia | reflexivity]. }
    destruct (both_poison_shadow M12 rom p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50ae4) (at_ S (-2208)) cpm midend 0 r1 PH A1 A2 A10 A11 A12)
      as (r2 & RUN2 & AGP).
    rewrite A8, A9, A18, A19, A20, A21 in RUN2.
    set (M13t := wbytes _ _ _) in RUN2.
    assert (EM13' : M13t = fr_PS M12 S p T n n8) by reflexivity.
    assert (GR13 : mem_grows memD M13t).
    { eapply mem_grows_trans; [exact GR12|]. (lazymatch goal with |- ?G => let G' := eval unfold M13t, ps_frame in G in change_no_check G' end). grows_tac. }
    (* [comment removed for export] *)
    destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & Mp8 & _).
    destruct (shad_facts2 (U p) n8 ltac:(unfold hideW in GpS; lia) ltac:(lia) ltac:(lia) N8d Mp8 N8c) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). hidehypW SH1.
    assert (TSH : hideW (T + 4096 <= 0x7fff8000 + U p / 8 \/ 0x7fff8000 + U p / 8 + n8 / 8 <= T)%Z)
      by (unfold hideW in GTS, GpS |- *; clear -GTS GpS SH2 SH4 Hpr GT2 Gp2; lia).
    assert (Q13 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z /\ (U x < 0x7fff8000 + U p / 8 \/ 0x7fff8000 + U p / 8 + n8 / 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M13t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M13t, ps_frame in G in change_no_check G' end). rewrite !at_at. intros x Hx. pose proof (u64_range p).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by (first [clear - GS | idtac]; lia); try (first [clear - GS Hx | idtac]; lia).
      1: apply Q12; lia.
      all: (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); unorm; rewrite ?Z2Nat.id by (first [clear - Gn8 | idtac]; lia); (first [clear - SH2 Hx Glast | idtac]; lia). }
    remember M13t as M13 eqn:EM13 in RUN2, GR13, Q13. subst M13t.
    (* [comment removed for export] *)
    assert (V2 : getr r2 2 = at_ S (-2208)) by viac AGP (2:reg).
    assert (V8 : getr r2 8 = Z_to_bv 64 (0x10ab58 + 728)) by viac AGP (8:reg).
    assert (V9 : getr r2 9 = at_ (Z_to_bv 64 T) 80) by viac AGP (9:reg).
    assert (V18 : getr r2 18 = Z_to_bv 64 n) by viac AGP (18:reg).
    assert (V19 : getr r2 19 = at_ S (-2128)) by viac AGP (19:reg).
    assert (V20 : getr r2 20 = at_ (Z_to_bv 64 T) 208) by viac AGP (20:reg).
    assert (V21 : getr r2 21 = at_ p (-16)) by viac AGP (21:reg).
    assert (V22 : getr r2 22 = Z_to_bv 64 (2 ^ 20)) by viac AGP (22:reg).
    (* [comment removed for export] *)
    destruct (c2a_run M13 rom S p T n len last cnt bsz qb r2 V2 V8 V9 V18 V19 V20 V21 V22 ltac:((first [clear - GS | idtac]; hlia)) ltac:((first [clear - GT | idtac]; hlia)) Gn Glen ltac:((first [clear - Glast | idtac]; hlia)) Gcnt Gbsz Gqb GlastT
                ltac:(eapply store_ok_mono; [exact GR13 | exact Hstk]) ltac:(eapply store_ok_mono; [exact GR13 | exact OkT])
                ltac:(eapply store_ok_mono; [exact GR13 | exact Okb])
                ltac:(xqh TSH Q13 C_len) ltac:(xqh TSH Q13 C_last) ltac:(xqh TSH Q13 C_qb) ltac:(xqh TSH Q13 C_bsz) ltac:(xqh TSH Q13 C_cnt))
      as (r3 & RUN3 & B2 & B22 & B3 & B4 & B23 & B24 & B25 & B26 & B27).
    (* [comment removed for export] *)
    exists r3. split.
    { subst M13 M12. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3, fr_PS in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [|exact RUN3].
      replace (Z_to_bv 64 0x50ae4 : word) with (0x50ae4 : word) in RUN2 at 1 by (apply bv_eq; reflexivity).
      exact RUN2. }
    first [clear - B27 B26 B25 B24 B23 B4 B3 B22 B2 AGP A27 A26 A25 A24 A23 A4 A3 D4 | idtac]; (repeat match goal with |- _ /\ _ => split end; try assumption; try rch;
      try (viac AGP (3:reg)); try (viac AGP (4:reg)); try (viac AGP (23:reg)); try (viac AGP (24:reg)); try (viac AGP (25:reg));
      try (viac AGP (26:reg)); try (viac AGP (27:reg))).
  Qed.
End RUNM.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RUNME.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S p ra0 tp x22 s0v s1v s2v s3v s4v s5v : word) (T n n8 id fl last qb len cnt24 k spb ba : Z) (cpm : byte) (midend : word) (bst bcs : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 2 = at_ S (-2176).
  Hypothesis D8 : getr rD 8 = at_ p (-16).
  Hypothesis D9 : getr rD 9 = at_ S (-2128).
  Hypothesis D10 : getr rD 10 = Z_to_bv 64 id.
  Hypothesis D18 : getr rD 18 = Z_to_bv 64 0x10ab58.
  Hypothesis D19 : getr rD 19 = Z_to_bv 64 0.
  Hypothesis D20 : getr rD 20 = thr.
  Hypothesis D21 : getr rD 21 = at_ S (-81).
  Hypothesis D22 : getr rD 22 = x22.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + n8 <= T \/ T + 4096 <= U p - 16)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis Gid : (0 <= id < 2 ^ 32)%Z.
  Hypothesis Gfl : (0 <= fl /\ fl + 4096 <= AIMGHI)%Z.
  Hypothesis Glast : (0x10007fff8000 <= last /\ last + 8192 <= U S - 3584)%Z.
  Hypothesis GlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Glastp : (last + 8192 <= U p - 16 \/ U p + n8 <= last)%Z.
  Hypothesis Gqb : (0 <= qb <= 2 ^ 20)%Z.
  Hypothesis GT16 : (T mod 16 = 0)%Z.
  Hypothesis Gcnt24 : (1 <= cnt24 <= 16)%Z.
  Hypothesis Gk : (0 <= k < 2 ^ 32)%Z.
  Hypothesis Gspb : (0 <= spb)%Z.
  Hypothesis Gbak : (spb + 3 * 2 ^ 35 + 16 * k)%Z = ba.
  Hypothesis Gba : (0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584)%Z.
  Hypothesis GbaT : (ba + 8192 <= T \/ T + 4096 <= ba)%Z.
  Hypothesis Gbap : (ba + 8192 <= U p - 16 \/ U p + n8 <= ba)%Z.
  Hypothesis Gbalast : (last + 8192 <= ba \/ ba + 8192 <= last)%Z.
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Glen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Gmid : (U midend < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2304)) 2304 = true.
  Hypothesis Okp : store_ok BSEGS memD p 8 = true.
  Hypothesis Oksh : store_ok BSEGS memD (Z_to_bv 64 (shad p)) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Okba : store_ok BSEGS memD (Z_to_bv 64 ba) 32 = true.
  (* [comment removed for export] *)
  Hypothesis C_q0 : rdn BSEGS memD (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).
  Hypothesis C_q1 : rdn BSEGS memD (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C_q2 : rdn BSEGS memD (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C_q3 : rdn BSEGS memD (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).
  Hypothesis C_q4 : rdn BSEGS memD (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis C_q5 : rdn BSEGS memD (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).
  Hypothesis C_nhi : rdn BSEGS memD (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS memD (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_mcs : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis C_msz : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis C_gfl : rdn BSEGS memD (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 fl)).
  Hypothesis C_mff : rdn BSEGS memD (Z_to_bv 64 (fl + 48)) 4 = Some (LE4 0).
  Hypothesis C_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_qb : rdn BSEGS memD (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis C_cnt24 : rdn BSEGS memD (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 cnt24)).
  Hypothesis C_cs : rdn BSEGS memD (Z_to_bv 64 (T + 2136)) 8 = Some bcs.
  Hypothesis C_k : rdn BSEGS memD (Z_to_bv 64 (T + 2144 + 4 * (cnt24 - 1))) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 k)).
  Hypothesis C_st : rdn BSEGS memD (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis C_spb : rdn BSEGS memD (Z_to_bv 64 0x10ab78) 8 = Some (LE8 (Z_to_bv 64 spb)).

  (* [comment removed for export] *)
  #[local] Definition post3e (r : bvmap 5 word) : Prop :=
      getr r 2 = S /\ getr r 1 = ra0 /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = x22 /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
      /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24 /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.

  Theorem run_m3e :
    rdn BSEGS memD (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    exists r,
      msteps BSEGS (mkst rD (0x50838 : word) memD rom) (mkst r (0x50c04 : word) (fr_P3e memD S p x22 T n n8 id cnt24 k ba qb bst bcs) rom)
      /\ getr r 2 = at_ S (-2272) /\ getr r 22 = Z_to_bv 64 (2 ^ 20) /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
      /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24 /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.
  Proof using C_spb C_st C_k C_cs C_cnt24 C_qb C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh C_mff C_gfl C_msz C_mcs C_nlo C_nhi C_q5 C_q4 C_q3 C_q2 C_q1 C_q0 Okba OkT Oksh Okp Hstk Lbcs Lbst GbaT Gba Gbak Gspb Gk Gcnt24 GT16 Gqb Gfl Gid Gn8 Gn GpT GT Gp GS D4 D22 D21 D20 D19 D18 D10 D9 D8 D1 midend cpm spb fl.
    intros C_len. (lazymatch goal with |- ?G => let G' := eval unfold post3e in G in change_no_check G' end).
    hidehypW GpT. hidehypW GlastT. hidehypW Glastp. hidehypW GbaT. hidehypW Gbap. hidehypW Gbalast.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    destruct GS as (GS1 & GS2 & GS3). destruct Gp as (Gp1 & Gp2 & Gp3). destruct GT as (GT1 & GT2). destruct GT2 as [GTS GT2]. destruct Gp2 as [GpS Gp2]. destruct Gn8 as (N8a & N8b & N8c & N8d).
    Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    Ltac xqh TS Q H := unfold hideW in TS; xq Q H.
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); notin)); rch.
    (* [comment removed for export] *)
    destruct (c1_run memD rom S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 T n id fl n8 rD
                D1 D8 D9 D10 D18 D19 D20 D21 D22 ltac:(hlia) ltac:(hlia) ltac:(hlia) Gn Gid ltac:(hlia) N8a Hstk Okp
                C_q0 C_q1 C_q2 C_q3 C_q4 C_q5 C_nhi C_nlo C_mcs C_msz C_gfl C_mff)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A3 & A4 & A23 & A24 & A25 & A26 & A27).
    set (M12t := fr_c1 memD S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T) in RUN1.
    assert (GR12 : mem_grows memD M12t) by ((lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end); grows_tac).
    assert (Q12 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M12t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by (first [clear - GS | idtac]; lia); try (first [clear - Gn8 Gp GS Hx | idtac]; lia). reflexivity. }
    remember M12t as M12 eqn:EM12 in RUN1, GR12, Q12. subst M12t.
    (* [comment removed for export] *)
    assert (PH : poisonH BSEGS both_poison_tab M12 p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50ae4) (at_ S (-2208)) cpm midend 0).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm pt_base pt_mset both_poison_tab] in G in change_no_check G' end).
      - xq Q12 C_gsh. - xq Q12 C_sh. - xq Q12 C_gmb. - xq Q12 C_mb. - xq Q12 C_gme. - xq Q12 C_me. - xq Q12 C_ghe. - xq Q12 C_he.
      - xq Q12 C_grm. - xq Q12 C_rm.
      - vm_compute. discriminate.
      - apply ret_ok_even. reflexivity.
      - intros _. split; [xq Q12 C_cpm | exact C_cpm1].
      - intros Hz. exfalso. revert Hz. unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
        repeat constructor; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ].
      - destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & M8 & _). exact M8.
      - unorm. exact N8c.
      - unorm. unfold hideW in GpS. destruct GpS as [PS|PS]; [right | left]; lia.
      - rewrite at_u by lia. lia.
      - eapply (store_ok_sub BSEGS M12 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR12 | exact Hstk] | rewrite !at_at, !at_u; lia | rewrite !at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. eapply store_ok_mono; [exact GR12 | exact Oksh].
      - apply ret_ok_lit; [lia | reflexivity]. }
    destruct (both_poison_shadow M12 rom p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50ae4) (at_ S (-2208)) cpm midend 0 r1 PH A1 A2 A10 A11 A12)
      as (r2 & RUN2 & AGP).
    rewrite A8, A9, A18, A19, A20, A21 in RUN2.
    set (M13t := wbytes _ _ _) in RUN2.
    assert (EM13' : M13t = fr_PS M12 S p T n n8) by reflexivity.
    assert (GR13 : mem_grows memD M13t).
    { eapply mem_grows_trans; [exact GR12|]. (lazymatch goal with |- ?G => let G' := eval unfold M13t, ps_frame in G in change_no_check G' end). grows_tac. }
    (* [comment removed for export] *)
    destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & Mp8 & _).
    destruct (shad_facts2 (U p) n8 ltac:(unfold hideW in GpS; lia) ltac:(lia) ltac:(lia) N8d Mp8 N8c) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). hidehypW SH1.
    assert (TSH : hideW (T + 4096 <= 0x7fff8000 + U p / 8 \/ 0x7fff8000 + U p / 8 + n8 / 8 <= T)%Z)
      by (unfold hideW in GTS, GpS |- *; clear -GTS GpS SH2 SH4 Hpr GT2 Gp2; lia).
    assert (Q13 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z /\ (U x < 0x7fff8000 + U p / 8 \/ 0x7fff8000 + U p / 8 + n8 / 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M13t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M13t, ps_frame in G in change_no_check G' end). rewrite !at_at. intros x Hx. pose proof (u64_range p).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by (first [clear - GS | idtac]; lia); try (first [clear - GS Hx | idtac]; lia).
      1: apply Q12; lia.
      all: (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); unorm; rewrite ?Z2Nat.id by lia; lia. }
    remember M13t as M13 eqn:EM13 in RUN2, GR13, Q13. subst M13t.
    (* [comment removed for export] *)
    assert (V2 : getr r2 2 = at_ S (-2208)) by viac AGP (2:reg).
    assert (V8 : getr r2 8 = Z_to_bv 64 (0x10ab58 + 728)) by viac AGP (8:reg).
    assert (V9 : getr r2 9 = at_ (Z_to_bv 64 T) 80) by viac AGP (9:reg).
    assert (V18 : getr r2 18 = Z_to_bv 64 n) by viac AGP (18:reg).
    assert (V19 : getr r2 19 = at_ S (-2128)) by viac AGP (19:reg).
    assert (V20 : getr r2 20 = at_ (Z_to_bv 64 T) 208) by viac AGP (20:reg).
    assert (V21 : getr r2 21 = at_ p (-16)) by viac AGP (21:reg).
    assert (V22 : getr r2 22 = Z_to_bv 64 (2 ^ 20)) by viac AGP (22:reg).
    (* [comment removed for export] *)
    assert (GTw : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z) by hlia.
    destruct (e1e_run M13 rom S p S T n cnt24 k spb ba qb bst bcs r2 V2 V8 V9 V18 V19 V20 V21 V22 ltac:((first [clear - GS | idtac]; hlia)) GTw Gn Gcnt24 Gk Gspb Gbak ltac:((first [clear - Gba | idtac]; hlia)) GbaT ltac:((first [clear - Gqb | idtac]; hlia)) Lbst Lbcs
                ltac:(eapply store_ok_mono; [exact GR13 | exact Hstk]) ltac:(eapply store_ok_mono; [exact GR13 | exact OkT])
                ltac:(eapply store_ok_mono; [exact GR13 | exact Okba])
                ltac:(unfold hideW in GpT; xqh TSH Q13 C_qb) ltac:(unfold hideW in GpT; xqh TSH Q13 C_cnt24) ltac:(unfold hideW in GpT; xqh TSH Q13 C_cs)
                ltac:(unfold hideW in GpT; xqh TSH Q13 C_k) ltac:(unfold hideW in GpT; xqh TSH Q13 C_st) ltac:(xqh TSH Q13 C_spb)
                ltac:(unfold hideW in GpT; xqh TSH Q13 C_len))
      as (r3 & RUN3 & B2 & B22 & B3 & B4 & B23 & B24 & B25 & B26 & B27).
    (* [comment removed for export] *)
    exists r3. split.
    { subst M13 M12. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3e, fr_PS in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [| exact RUN3].
      replace (Z_to_bv 64 0x50ae4 : word) with (0x50ae4 : word) in RUN2 at 1 by (apply bv_eq; reflexivity).
      exact RUN2. }
    repeat match goal with |- _ /\ _ => split end; try assumption; try rch;
      try (viac AGP (3:reg)); try (viac AGP (4:reg)); try (viac AGP (23:reg)); try (viac AGP (24:reg)); try (viac AGP (25:reg));
      try (viac AGP (26:reg)); try (viac AGP (27:reg)).
  Qed.

End RUNME.

Section RUNMF.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S p ra0 tp x22 s0v s1v s2v s3v s4v s5v : word) (T n n8 id fl last qb len cnt24 k spb ba : Z) (cpm : byte) (midend : word) (bst bcs : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 2 = at_ S (-2176).
  Hypothesis D8 : getr rD 8 = at_ p (-16).
  Hypothesis D9 : getr rD 9 = at_ S (-2128).
  Hypothesis D10 : getr rD 10 = Z_to_bv 64 id.
  Hypothesis D18 : getr rD 18 = Z_to_bv 64 0x10ab58.
  Hypothesis D19 : getr rD 19 = Z_to_bv 64 0.
  Hypothesis D20 : getr rD 20 = thr.
  Hypothesis D21 : getr rD 21 = at_ S (-81).
  Hypothesis D22 : getr rD 22 = x22.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + n8 <= T \/ T + 4096 <= U p - 16)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis Gid : (0 <= id < 2 ^ 32)%Z.
  Hypothesis Gfl : (0 <= fl /\ fl + 4096 <= AIMGHI)%Z.
  Hypothesis Glast : (0x10007fff8000 <= last /\ last + 8192 <= U S - 3584)%Z.
  Hypothesis GlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Glastp : (last + 8192 <= U p - 16 \/ U p + n8 <= last)%Z.
  Hypothesis Gqb : (0 <= qb <= 2 ^ 20)%Z.
  Hypothesis GT16 : (T mod 16 = 0)%Z.
  Hypothesis Gcnt24 : (1 <= cnt24 <= 16)%Z.
  Hypothesis Gk : (0 <= k < 2 ^ 32)%Z.
  Hypothesis Gspb : (0 <= spb)%Z.
  Hypothesis Gbak : (spb + 3 * 2 ^ 35 + 16 * k)%Z = ba.
  Hypothesis Gba : (0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584)%Z.
  Hypothesis GbaT : (ba + 8192 <= T \/ T + 4096 <= ba)%Z.
  Hypothesis Gbap : (ba + 8192 <= U p - 16 \/ U p + n8 <= ba)%Z.
  Hypothesis Gbalast : (last + 8192 <= ba \/ ba + 8192 <= last)%Z.
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Glen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Gmid : (U midend < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2304)) 2304 = true.
  Hypothesis Okp : store_ok BSEGS memD p 8 = true.
  Hypothesis Oksh : store_ok BSEGS memD (Z_to_bv 64 (shad p)) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Okba : store_ok BSEGS memD (Z_to_bv 64 ba) 32 = true.
  (* [comment removed for export] *)
  Hypothesis C_q0 : rdn BSEGS memD (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).
  Hypothesis C_q1 : rdn BSEGS memD (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C_q2 : rdn BSEGS memD (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C_q3 : rdn BSEGS memD (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).
  Hypothesis C_q4 : rdn BSEGS memD (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis C_q5 : rdn BSEGS memD (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).
  Hypothesis C_nhi : rdn BSEGS memD (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS memD (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_mcs : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis C_msz : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis C_gfl : rdn BSEGS memD (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 fl)).
  Hypothesis C_mff : rdn BSEGS memD (Z_to_bv 64 (fl + 48)) 4 = Some (LE4 0).
  Hypothesis C_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_qb : rdn BSEGS memD (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis C_cnt24 : rdn BSEGS memD (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 cnt24)).
  Hypothesis C_cs : rdn BSEGS memD (Z_to_bv 64 (T + 2136)) 8 = Some bcs.
  Hypothesis C_k : rdn BSEGS memD (Z_to_bv 64 (T + 2144 + 4 * (cnt24 - 1))) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 k)).
  Hypothesis C_st : rdn BSEGS memD (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis C_spb : rdn BSEGS memD (Z_to_bv 64 0x10ab78) 8 = Some (LE8 (Z_to_bv 64 spb)).

  (* [comment removed for export] *)
  #[local] Definition post3f (r : bvmap 5 word) : Prop :=
      getr r 2 = S /\ getr r 1 = ra0 /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = x22 /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
      /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24 /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.

  Theorem run_m3f :
    rdn BSEGS memD (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 last)) ->
    rdn BSEGS memD (Z_to_bv 64 (last + 16)) 8 = Some (LE8 (Z_to_bv 64 1021)) ->
    store_ok BSEGS memD (Z_to_bv 64 last) 8 = true ->
    rdn BSEGS memD (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 len)) ->
    exists r,
      msteps BSEGS (mkst rD (0x50838 : word) memD rom) (mkst r (0x50c04 : word) (fr_P3f memD S p x22 T n n8 id cnt24 k ba qb last len bst bcs) rom)
      /\ getr r 2 = at_ S (-2272) /\ getr r 22 = Z_to_bv 64 (2 ^ 20) /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
      /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24 /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.
  Proof using C_spb C_st C_k C_cs C_cnt24 C_qb C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh C_mff C_gfl C_msz C_mcs C_nlo C_nhi C_q5 C_q4 C_q3 C_q2 C_q1 C_q0 Okba OkT Oksh Okp Hstk Glen Lbcs Lbst Gbalast GbaT Gba Gbak Gspb Gk Gcnt24 GT16 Gqb Glastp GlastT Glast Gfl Gid Gn8 Gn GpT GT Gp GS D4 D22 D21 D20 D19 D18 D10 D9 D8 D1 midend cpm spb fl.
    intros C_last C_lcnt Oklast C_len. (lazymatch goal with |- ?G => let G' := eval unfold post3f in G in change_no_check G' end).
    hidehypW GpT. hidehypW GlastT. hidehypW Glastp. hidehypW GbaT. hidehypW Gbap. hidehypW Gbalast.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    destruct GS as (GS1 & GS2 & GS3). destruct Gp as (Gp1 & Gp2 & Gp3). destruct GT as (GT1 & GT2). destruct GT2 as [GTS GT2]. destruct Gp2 as [GpS Gp2]. destruct Gn8 as (N8a & N8b & N8c & N8d).
    Ltac grows_tacF := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
    Ltac xqF Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    Ltac xqhF TS Q H := unfold hideW in TS; xqF Q H.
    Ltac rchF := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viacF AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); notin)); rchF.
    (* [comment removed for export] *)
    destruct (c1_run memD rom S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 T n id fl n8 rD
                D1 D8 D9 D10 D18 D19 D20 D21 D22 ltac:(hlia) ltac:(hlia) ltac:(hlia) Gn Gid ltac:(hlia) N8a Hstk Okp
                C_q0 C_q1 C_q2 C_q3 C_q4 C_q5 C_nhi C_nlo C_mcs C_msz C_gfl C_mff)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A3 & A4 & A23 & A24 & A25 & A26 & A27).
    set (M12t := fr_c1 memD S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T) in RUN1.
    assert (GR12 : mem_grows memD M12t) by ((lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end); grows_tacF).
    assert (Q12 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M12t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by (first [clear - GS | idtac]; lia); try (first [clear - Gn8 Gp GS Hx | idtac]; lia). reflexivity. }
    remember M12t as M12 eqn:EM12 in RUN1, GR12, Q12. subst M12t.
    (* [comment removed for export] *)
    assert (PH : poisonH BSEGS both_poison_tab M12 p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50ae4) (at_ S (-2208)) cpm midend 0).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm pt_base pt_mset both_poison_tab] in G in change_no_check G' end).
      - xqF Q12 C_gsh. - xqF Q12 C_sh. - xqF Q12 C_gmb. - xqF Q12 C_mb. - xqF Q12 C_gme. - xqF Q12 C_me. - xqF Q12 C_ghe. - xqF Q12 C_he.
      - xqF Q12 C_grm. - xqF Q12 C_rm.
      - vm_compute. discriminate.
      - apply ret_ok_even. reflexivity.
      - intros _. split; [xqF Q12 C_cpm | exact C_cpm1].
      - intros Hz. exfalso. revert Hz. unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
        repeat constructor; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ].
      - destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & M8 & _). exact M8.
      - unorm. exact N8c.
      - unorm. unfold hideW in GpS. destruct GpS as [PS|PS]; [right | left]; lia.
      - rewrite at_u by lia. lia.
      - eapply (store_ok_sub BSEGS M12 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR12 | exact Hstk] | rewrite !at_at, !at_u; lia | rewrite !at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. eapply store_ok_mono; [exact GR12 | exact Oksh].
      - apply ret_ok_lit; [lia | reflexivity]. }
    destruct (both_poison_shadow M12 rom p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50ae4) (at_ S (-2208)) cpm midend 0 r1 PH A1 A2 A10 A11 A12)
      as (r2 & RUN2 & AGP).
    rewrite A8, A9, A18, A19, A20, A21 in RUN2.
    set (M13t := wbytes _ _ _) in RUN2.
    assert (EM13' : M13t = fr_PS M12 S p T n n8) by reflexivity.
    assert (GR13 : mem_grows memD M13t).
    { eapply mem_grows_trans; [exact GR12|]. (lazymatch goal with |- ?G => let G' := eval unfold M13t, ps_frame in G in change_no_check G' end). grows_tacF. }
    (* [comment removed for export] *)
    destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & Mp8 & _).
    destruct (shad_facts2 (U p) n8 ltac:(unfold hideW in GpS; lia) ltac:(lia) ltac:(lia) N8d Mp8 N8c) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). hidehypW SH1.
    assert (TSH : hideW (T + 4096 <= 0x7fff8000 + U p / 8 \/ 0x7fff8000 + U p / 8 + n8 / 8 <= T)%Z)
      by (unfold hideW in GTS, GpS |- *; clear -GTS GpS SH2 SH4 Hpr GT2 Gp2; lia).
    assert (Q13 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z /\ (U x < 0x7fff8000 + U p / 8 \/ 0x7fff8000 + U p / 8 + n8 / 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M13t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M13t, ps_frame in G in change_no_check G' end). rewrite !at_at. intros x Hx. pose proof (u64_range p).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by (first [clear - GS | idtac]; lia); try (first [clear - GS Hx | idtac]; lia).
      1: apply Q12; lia.
      all: (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); unorm; rewrite ?Z2Nat.id by lia; lia. }
    remember M13t as M13 eqn:EM13 in RUN2, GR13, Q13. subst M13t.
    (* [comment removed for export] *)
    assert (V2 : getr r2 2 = at_ S (-2208)) by viacF AGP (2:reg).
    assert (V8 : getr r2 8 = Z_to_bv 64 (0x10ab58 + 728)) by viacF AGP (8:reg).
    assert (V9 : getr r2 9 = at_ (Z_to_bv 64 T) 80) by viacF AGP (9:reg).
    assert (V18 : getr r2 18 = Z_to_bv 64 n) by viacF AGP (18:reg).
    assert (V19 : getr r2 19 = at_ S (-2128)) by viacF AGP (19:reg).
    assert (V20 : getr r2 20 = at_ (Z_to_bv 64 T) 208) by viacF AGP (20:reg).
    assert (V21 : getr r2 21 = at_ p (-16)) by viacF AGP (21:reg).
    assert (V22 : getr r2 22 = Z_to_bv 64 (2 ^ 20)) by viacF AGP (22:reg).
    (* [comment removed for export] *)
    assert (GTw : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z) by hlia.
    destruct (e1f_run M13 rom S p S T n cnt24 k spb ba qb last len bst bcs r2 V2 V8 V9 V18 V19 V20 V21 V22 ltac:((first [clear - GS | idtac]; hlia)) GTw Gn Gcnt24 Gk Gspb Gbak ltac:((first [clear - Gba | idtac]; hlia)) GbaT ltac:((first [clear - Gqb | idtac]; hlia)) Lbst Lbcs
                ltac:(eapply store_ok_mono; [exact GR13 | exact Hstk]) ltac:(eapply store_ok_mono; [exact GR13 | exact OkT])
                ltac:(eapply store_ok_mono; [exact GR13 | exact Okba])
                ltac:(unfold hideW in GpT; xqhF TSH Q13 C_qb) ltac:(unfold hideW in GpT; xqhF TSH Q13 C_cnt24) ltac:(unfold hideW in GpT; xqhF TSH Q13 C_cs)
                ltac:(unfold hideW in GpT; xqhF TSH Q13 C_k) ltac:(unfold hideW in GpT; xqhF TSH Q13 C_st) ltac:(xqhF TSH Q13 C_spb)
                Glen ltac:((first [clear - Glast | idtac]; hlia)) GlastT Gbalast ltac:(eapply store_ok_mono; [exact GR13 | exact Oklast])
                ltac:(unfold hideW in GpT; xqhF TSH Q13 C_last) ltac:(unfold hideW in Glastp; xqhF TSH Q13 C_lcnt)
                ltac:(unfold hideW in GpT; xqhF TSH Q13 C_len))
      as (r3 & RUN3 & B2 & B22 & B3 & B4 & B23 & B24 & B25 & B26 & B27).
    (* [comment removed for export] *)
    exists r3. split.
    { subst M13 M12. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3f, fr_PS in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [| exact RUN3].
      replace (Z_to_bv 64 0x50ae4 : word) with (0x50ae4 : word) in RUN2 at 1 by (apply bv_eq; reflexivity).
      exact RUN2. }
    repeat match goal with |- _ /\ _ => split end; try assumption; try rchF;
      try (viacF AGP (3:reg)); try (viacF AGP (4:reg)); try (viacF AGP (23:reg)); try (viacF AGP (24:reg)); try (viacF AGP (25:reg));
      try (viacF AGP (26:reg)); try (viacF AGP (27:reg)).
  Qed.
End RUNMF.

End FPGen.
End BoAllocFRunM.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFTail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 BoAllocF6 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Lemma both_priv_lt : forall a, in_wins (ia_priv both_addrs) a -> a < AIMGHI.
Proof.
  intros a (lo & hi & Hin & Hr). cbn [ia_priv both_addrs] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma regs_kept_lit : forall (R R' : bvmap 5 word) (r : bv 5),
  regs_kept R R' -> existsb (Z.eqb (bv_unsigned r)) as_callee_saved = true -> getr R' r = getr R r.
Proof. intros R R' r RK Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply RK. apply in_cs. exact Hr. Qed.

Lemma restrict_mkstT : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_def : forall (m : mem) (a : word), m a <> None -> store_ok BSEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

Section TAIL.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable KDR : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KDR : 0 <= KDR <= 1376.
  Hypothesis HYP_DRAIN : HYP_DRAIN_stmt bt FXOK KDR.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  Lemma katD_loads : forall fx st Lc FF (M : mem) mdl (R R' : bvmap 5 word) (pc pc' : word) (Q : config -> Prop),
    Rep bt st Lc FF M mdl -> m_halted mdl = None ->
    msteps BSEGS (@mkst fx R pc (mrestrict (HID st mdl) M) (seg_rom BSEGS)) (@mkst fx R' pc' (mrestrict (HID st mdl) M) (seg_rom BSEGS)) ->
    (forall mdl', Rep bt st Lc FF M mdl' -> m_halted mdl' = None -> same_but_materialized mdl mdl' ->
        katD BSEGS (mkCfg (@mkst fx R' pc' M (seg_rom BSEGS)) mdl') Q) ->
    katD BSEGS (mkCfg (@mkst fx R pc M (seg_rom BSEGS)) mdl) Q.
  Proof using BT_ia.
    intros fx st Lc FF M mdl R R' pc pc' Q RP HH RUN K.
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14 & _). destruct R14 as (B1 & B2 & _).
    apply (katD_msteps_acct BSEGS (HID st mdl) (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R pc M (seg_rom BSEGS)) (@mkst fx R' pc' (mrestrict (HID st mdl) M) (seg_rom BSEGS)) mdl Q).
    - apply lazy_cover_HID.
    - exact B1.
    - exact B2.
    - exact HH.
    - rewrite restrict_mkstT. exact RUN.
    - intros mdl' MI SBM HC. rewrite unrestrict_mkst.
      change (ms_mem (@mkst fx R pc M (seg_rom BSEGS))) with M. rewrite munrestrict_mrestrict.
      pose proof (same_but_materialized_frame mdl mdl' SBM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh & _).
      apply K; [exact (Rep_sbm bt st Lc FF M mdl mdl' RP MI SBM) | rewrite Eh; exact HH | exact SBM].
  Qed.

  Theorem free_put_tail :
    forall (h : option Z) fx' (R rf : bvmap 5 word) (M Mfin : mem) (mdl mdl3 : Model) (Lc' FF : list (Z * Z)) (B' C' K' ret sp : Z)
           (st1 : ast) (w2 w3 w4 w5 w6 e3 e4 e5 e6 : word),
      let S := getr R 2 in
      (* [comment removed for export] *)
      getr R 1 = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
      U S = sp -> sp mod 16 = 0 -> CEIL + MSTK_A <= sp -> sp + 16 <= PTRHI ->
      getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
      (* [comment removed for export] *)
      FXOK fx' -> m_halted mdl3 = None -> BackingAlgebra.model_ivs_wf mdl3 ->
      WFX bt st1 Lc' FF -> Rep bt st1 Lc' FF Mfin mdl3 -> bounds st1 Lc' B' C' K' -> HPc h st1 ->
      q_bytes (a_gq st1) <= 2 ^ 28 -> a_tq st1 <> [] -> 0 <= q_bytes (a_tq st1) < 2 ^ 40 ->
      (forall z, T <= z < T + PG -> lzb mdl3 z = false) ->
      (* [comment removed for export] *)
      getr rf 2 = at_ S (-2272) -> getr rf 22 = Z_to_bv 64 (2 ^ 20) -> getr rf 3 = getr R 3 -> getr rf 4 = getr R 4 ->
      getr rf 23 = getr R 23 -> getr rf 24 = getr R 24 -> getr rf 25 = getr R 25 -> getr rf 26 = getr R 26 -> getr rf 27 = getr R 27 ->
      (* [comment removed for export] *)
      rdn BSEGS Mfin (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x50afc)) ->
      rdn BSEGS Mfin (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (IB bt + 728))) ->
      rdn BSEGS Mfin (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80)) ->
      rdn BSEGS Mfin (at_ S (-2240)) 8 = Some (LE8 e3) -> rdn BSEGS Mfin (at_ S (-2248)) 8 = Some (LE8 e4) ->
      rdn BSEGS Mfin (at_ S (-2256)) 8 = Some (LE8 e5) -> rdn BSEGS Mfin (at_ S (-2264)) 8 = Some (LE8 e6) ->
      rdn BSEGS Mfin (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)) ->
      rdn BSEGS Mfin (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128))) ->
      rdn BSEGS Mfin (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)) -> rdn BSEGS Mfin (at_ S (-2144)) 8 = Some (LE8 S) ->
      rdn BSEGS Mfin (at_ S (-2152)) 8 = Some (LE8 w2) -> rdn BSEGS Mfin (at_ S (-2160)) 8 = Some (LE8 w3) ->
      rdn BSEGS Mfin (at_ S (-2168)) 8 = Some (LE8 w4) -> rdn BSEGS Mfin (at_ S (-2176)) 8 = Some (LE8 w5) ->
      rdn BSEGS Mfin (at_ S (-2184)) 8 = Some (LE8 w6) -> rdn BSEGS Mfin (at_ S (-2192)) 8 = Some (LE8 (getr R 22)) ->
      rdn BSEGS Mfin (at_ S (-8)) 8 = Some (LE8 (getr R 1)) -> rdn BSEGS Mfin (at_ S (-16)) 8 = Some (LE8 (getr R 8)) ->
      rdn BSEGS Mfin (at_ S (-24)) 8 = Some (LE8 (getr R 9)) -> rdn BSEGS Mfin (at_ S (-32)) 8 = Some (LE8 (getr R 18)) ->
      rdn BSEGS Mfin (at_ S (-40)) 8 = Some (LE8 (getr R 19)) -> rdn BSEGS Mfin (at_ S (-48)) 8 = Some (LE8 (getr R 20)) ->
      rdn BSEGS Mfin (at_ S (-56)) 8 = Some (LE8 (getr R 21)) ->
      (* [comment removed for export] *)
      scratch_ok BSEGS Mfin sp MSTK_A ->
      (forall a : word, Mfin a <> M a -> as_changed (bt_ia bt) MSTK_A Lc' FF sp a) -> mem_grows M Mfin ->
      same_except_vm mdl mdl3 -> lazy_kept (bt_ia bt) Lc' FF mdl mdl3 ->
      katD BSEGS (mkCfg (@mkst fx' rf (Z_to_bv 64 0x50c04) Mfin (seg_rom BSEGS)) mdl3)
           (free_post BSEGS FXOK both_addrs (AAINV_F bt HP) h MSTK_A R M mdl Lc' FF B' C' K' ret sp).
  Proof using FAM HYP_DRAIN G_KDR GEOM BT_ia BT_segs KDR.
    intros h fx' R rf M Mfin mdl mdl3 Lc' FF B' C' K' ret sp st1 w2 w3 w4 w5 w6 e3 e4 e5 e6 S
           HR1 Hret Hret2 HSsp Hsp16 Hsplo Hsphi HR4 HFX HH3 MW3 WX1 RP1 BD1 HLE1 GQ28 TQne QBr LZT
           Z2 Z22 Z3 Z4 Z23 Z24 Z25 Z26 Z27
           Ce0 Ce1 Ce2 Ce3 Ce4 Ce5 Ce6 Ccb0 Ccb1 Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Cq6 Cq7 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6
           SOK CHG GRF SEV LZK.
    pose proof ceil_rng as CR.
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (u64_range S) as HSr.
    rewrite BT_ia in CHG, LZK.
    (* [comment removed for export] *)
    pose proof WX1 as (qt1 & qg1 & Wq1 & _).
    pose proof (thread_dyn bt st1 Lc' FF Wq1) as (GT0 & GTC & GTI & GTB & TPG & _).
    rewrite BT_ia in GTI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI.
    unfold PTRHI in Hsphi. unfold MSTK_A, AS_HEAPLO, AS_LO, PG in *.
    assert (GT4 : 4096 <= T) by (clear - GT0 TPG; Z.div_mod_to_equations; lia).
    assert (RETOK : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_lit; [lia | exact Hret2]).
    assert (GS : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - HSsp Hsplo Hsphi CR; lia).
    assert (GTS : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; split; lia | clear - GTC HSsp Hsplo; lia]. }
    clear GTI GTB.
    (* [comment removed for export] *)
    pose proof RP1 as (_ & _ & R3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & _).
    destruct R3 as (_ & _ & _ & _ & _ & _ & TQ & _). destruct TQ as (_ & _ & _ & Cqb). unfold T_QC in Cqb. rewrite BT_segs in Cqb.
    replace (T + 80 + 24) with (T + 104) in Cqb by lia.
    (* [comment removed for export] *)
    set (Hd := HID st1 mdl3).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st1 mdl3 z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply LZT. exact Hz. }
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    Ltac stk NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
    assert (K_qb : rdn BSEGS (mrestrict Hd Mfin) (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes (a_tq st1))))).
    { apply (cellZ_restrict Hd Mfin (T + 104) 8); [exact Cqb | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHT]. }
    assert (S_e0 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x50afc))) by stk NHs Ce0.
    assert (S_e1 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (IB bt + 728)))) by stk NHs Ce1.
    assert (S_e2 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80))) by stk NHs Ce2.
    assert (S_e3 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2240)) 8 = Some (LE8 e3)) by stk NHs Ce3.
    assert (S_e4 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2248)) 8 = Some (LE8 e4)) by stk NHs Ce4.
    assert (S_e5 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2256)) 8 = Some (LE8 e5)) by stk NHs Ce5.
    assert (S_e6 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2264)) 8 = Some (LE8 e6)) by stk NHs Ce6.
    assert (S_q0 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14))) by stk NHs Cq0.
    assert (S_q1 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2144)) 8 = Some (LE8 S)) by stk NHs Cq1.
    assert (S_q2 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2152)) 8 = Some (LE8 w2)) by stk NHs Cq2.
    assert (S_q3 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2160)) 8 = Some (LE8 w3)) by stk NHs Cq3.
    assert (S_q4 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2168)) 8 = Some (LE8 w4)) by stk NHs Cq4.
    assert (S_q5 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2176)) 8 = Some (LE8 w5)) by stk NHs Cq5.
    assert (S_q6 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2184)) 8 = Some (LE8 w6)) by stk NHs Cq6.
    assert (S_q7 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-2192)) 8 = Some (LE8 (getr R 22))) by stk NHs Cq7.
    assert (S_i0 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-8)) 8 = Some (LE8 (getr R 1))) by stk NHs Ci0.
    assert (S_i1 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-16)) 8 = Some (LE8 (getr R 8))) by stk NHs Ci1.
    assert (S_i2 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-24)) 8 = Some (LE8 (getr R 9))) by stk NHs Ci2.
    assert (S_i3 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-32)) 8 = Some (LE8 (getr R 18))) by stk NHs Ci3.
    assert (S_i4 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-40)) 8 = Some (LE8 (getr R 19))) by stk NHs Ci4.
    assert (S_i5 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-48)) 8 = Some (LE8 (getr R 20))) by stk NHs Ci5.
    assert (S_i6 : rdn BSEGS (mrestrict Hd Mfin) (at_ S (-56)) 8 = Some (LE8 (getr R 21))) by stk NHs Ci6.
    rewrite HR1 in S_i0, Ci0.
    destruct (Z.le_gt_cases (q_bytes (a_tq st1)) (2 ^ 20)) as [QB|QB].
    - (* [comment removed for export] *)
      destruct (q_tail_run (mrestrict Hd Mfin) (seg_rom BSEGS) S w2 w3 w4 w5 w6 (getr R 22) (Z_to_bv 64 ret)
                  (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21)
                  (Z_to_bv 64 (IB bt + 728)) e3 e4 e5 e6 T (q_bytes (a_tq st1)) rf
                  Z2 Z22 GS GTS ltac:(clear - QB QBr; lia) RETOK S_e0 S_e1 S_e2 S_e3 S_e4 S_e5 S_e6 K_qb
                  S_q0 S_q1 S_q2 S_q3 S_q4 S_q5 S_q6 S_q7 S_i0 S_i1 S_i2 S_i3 S_i4 S_i5 S_i6)
        as (r9 & RUN & Y2 & Y1 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y3 & Y4 & Y23 & Y24 & Y25 & Y26 & Y27).
      replace (Z_to_bv 64 0x50c04) with (0x50c04%bv : word) by (apply bv_eq; reflexivity).
      apply (katD_loads fx' st1 Lc' FF Mfin mdl3 rf r9 _ _ _ RP1 HH3 RUN).
      intros mdl4 RP4 HH4 SBM4.
      pose proof (same_but_materialized_frame mdl3 mdl4 SBM4) as (_ & _ & Elz4 & _).
      apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold free_post, cfg in G in change_no_check G' end). exists fx', r9, Mfin, mdl4.
      split; [reflexivity|]. split; [exact HFX|].
      split.
      { apply regs_kept_intro; rewrite ?Y2, ?Y3, ?Y4, ?Y8, ?Y9, ?Y18, ?Y19, ?Y20, ?Y21, ?Y22, ?Y23, ?Y24, ?Y25, ?Y26, ?Y27;
          rewrite ?Z3, ?Z4, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; reflexivity. }
      split; [exact CHG|].
      split; [intros a _ Da; apply GRF; exact Da|].
      split; [exact SOK|].
      split.
      { exists st1. split; [exact (WFX_WF bt st1 Lc' FF WX1 QB GQ28)|]. split; [exact RP4|].
        split; [split; [exact BD1 | exact (hp_fin bt HP HPc FAM h st1 HLE1)] | exact (model_ivs_wf_sbm mdl3 mdl4 SBM4 MW3)]. }
      split; [eapply same_except_vm_trans; [exact SEV | apply same_but_materialized_except_vm; exact SBM4]|].
      split; [| exact HH4].
      intros a Ha. transitivity (lzb mdl3 a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz4; reflexivity|]. exact (LZK a Ha).
    - (* [comment removed for export] *)
      destruct (q_drain_call (mrestrict Hd Mfin) (seg_rom BSEGS) S (Z_to_bv 64 (IB bt + 728)) e3 e4 e5 e6 T (q_bytes (a_tq st1)) rf
                  Z2 Z22 GS GTS ltac:(clear - QB QBr; lia) S_e0 S_e1 S_e2 S_e3 S_e4 S_e5 S_e6 K_qb
                  ltac:(stk NHs Ccb0) ltac:(stk NHs Ccb1))
        as (r1 & RUN1 & X1 & X2 & X10 & X11 & X12 & X13 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X3 & X4 & X23 & X24 & X25 & X26 & X27).
      replace (Z_to_bv 64 0x50c04) with (0x50c04%bv : word) by (apply bv_eq; reflexivity).
      apply (katD_loads fx' st1 Lc' FF Mfin mdl3 rf r1 _ _ _ RP1 HH3 RUN1).
      intros mdl4 RP4 HH4 SBM4.
      pose proof (same_but_materialized_frame mdl3 mdl4 SBM4) as (_ & _ & Elz4 & _).
      replace (0x4e260%bv : word) with (Z_to_bv 64 0x4e260 : word) by (apply bv_eq; reflexivity).
      destruct (sp_facts16 (U S) ltac:(rewrite HSsp; exact Hsp16)) as [_ M16].
      apply (katD_bind BSEGS _ (drain_post bt FXOK KDR st1 Lc' FF Mfin mdl4 r1 (at_ S (-2208)) (Z_to_bv 64 0x50a34))).
      { apply (HYP_DRAIN fx' st1 Lc' FF Mfin mdl4 r1 (at_ S (-2208)) (Z_to_bv 64 0x50a34) (at_ S (-2128)) HFX HH4
                 (model_ivs_wf_sbm mdl3 mdl4 SBM4 MW3) WX1 RP4 TQne ltac:(clear - QBr; lia) GQ28 X1 X2).
        + exact X10.
        + rewrite X11. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_QC in G in change_no_check G' end). unorm. lia.
        + rewrite X12. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC in G in change_no_check G' end). unorm. lia.
        + exact X13.
        + rewrite X4, Z4. exact HR4.
        + rewrite at_u by lia. exact M16.
        + rewrite at_u by lia. lia.
        + (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). rewrite at_u by lia. lia.
        + apply ret_ok_lit; [lia | reflexivity].
        + intros a Ha. rewrite at_u in Ha by lia. apply SOK. rewrite <- HSsp. lia. }
      (* [comment removed for export] *)
      intros c4 POST4.
      destruct POST4 as (fx4 & st3 & M4 & mdl5 & R4 & -> & HFX4 & HH5 & W3 & RP3 & KA & HO & CH4 & LZ4 & RK4 & SEV4 & MW5).
      (* [comment removed for export] *)
      assert (KEPT : forall a : word, U S - 2208 <= U a -> M4 a = Mfin a).
      { intros a Ha. destruct (decide (M4 a = Mfin a)) as [E|N]; [exact E|]. exfalso.
        destruct (CH4 a N) as [D _]. unfold drain_changed in D. rewrite at_u in D by lia. rewrite BT_ia in D.
        destruct D as [D|[(D1 & D2 & D3)|D]]; [lia | clear - D1 Ha Hsplo HSsp; lia | pose proof (both_priv_lt _ D); lia]. }
      assert (XF : forall k v, -2192 <= k -> k + 8 <= 0 -> rdn BSEGS Mfin (at_ S k) 8 = Some (LE8 v) -> rdn BSEGS M4 (at_ S k) 8 = Some (LE8 v)).
      { intros k v Hk1 Hk2 Hr. apply (rd_same BSEGS M4 Mfin); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
        intros x Hx. rewrite at_u in Hx by lia. apply KEPT. cbn in Hx. lia. }
      set (Hd4 := HID st3 mdl5).
      pose proof RP3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13' & _).
      assert (NHs4 : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd4 (Z_to_bv 64 z) = false).
      { intros z Hz Hr. apply (HID_off_zone bt st3 mdl5 z R13' Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
      Ltac stk4 NHs XF C := rewrite rdn_mrestrict; [ apply XF; [lia | lia | exact C] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
      assert (RK2 : getr R4 2 = at_ S (-2208)) by (rewrite <- X2; exact (regs_kept_lit r1 R4 2 RK4 eq_refl)).
      destruct (q_after_drain (mrestrict Hd4 M4) (seg_rom BSEGS) S w2 w3 w4 w5 w6 (getr R 22) (Z_to_bv 64 ret)
                  (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) R4 RK2 RETOK
                  ltac:(stk4 NHs4 XF Cq0) ltac:(stk4 NHs4 XF Cq1) ltac:(stk4 NHs4 XF Cq2) ltac:(stk4 NHs4 XF Cq3)
                  ltac:(stk4 NHs4 XF Cq4) ltac:(stk4 NHs4 XF Cq5) ltac:(stk4 NHs4 XF Cq6) ltac:(stk4 NHs4 XF Cq7)
                  ltac:(stk4 NHs4 XF Ci0) ltac:(stk4 NHs4 XF Ci1) ltac:(stk4 NHs4 XF Ci2) ltac:(stk4 NHs4 XF Ci3)
                  ltac:(stk4 NHs4 XF Ci4) ltac:(stk4 NHs4 XF Ci5) ltac:(stk4 NHs4 XF Ci6))
        as (r9 & RUN9 & Y2 & Y1 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y3 & Y4 & Y23 & Y24 & Y25 & Y26 & Y27).
      replace (Z_to_bv 64 0x50a34) with (0x50a34%bv : word) by (apply bv_eq; reflexivity).
      apply (katD_loads fx4 st3 Lc' FF M4 mdl5 R4 r9 _ _ _ RP3 HH5 RUN9).
      intros mdl6 RP6 HH6 SBM6.
      pose proof (same_but_materialized_frame mdl5 mdl6 SBM6) as (_ & _ & Elz6 & _).
      (* [comment removed for export] *)
      assert (GR4 : forall a : word, ~ rt_priv both_addrs Lc' FF (U a) -> Mfin a <> None -> M4 a <> None).
      { intros a NP Ha. destruct (decide (M4 a = Mfin a)) as [E|N]; [rewrite E; exact Ha|].
        destruct (proj2 (CH4 a N)) as [D|D]; [exact D | exfalso; rewrite BT_ia in D; exact (NP D)]. }
      apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold free_post, cfg in G in change_no_check G' end). exists fx4, r9, M4, mdl6.
      split; [reflexivity|]. split; [exact HFX4|].
      split.
      { (* [comment removed for export] *)
        apply regs_kept_intro; rewrite ?Y2, ?Y3, ?Y4, ?Y8, ?Y9, ?Y18, ?Y19, ?Y20, ?Y21, ?Y22, ?Y23, ?Y24, ?Y25, ?Y26, ?Y27; try reflexivity.
        all: rewrite ?(regs_kept_lit r1 R4 3 RK4 eq_refl), ?(regs_kept_lit r1 R4 4 RK4 eq_refl), ?(regs_kept_lit r1 R4 23 RK4 eq_refl),
                     ?(regs_kept_lit r1 R4 24 RK4 eq_refl), ?(regs_kept_lit r1 R4 25 RK4 eq_refl), ?(regs_kept_lit r1 R4 26 RK4 eq_refl),
                     ?(regs_kept_lit r1 R4 27 RK4 eq_refl);
             rewrite ?X3, ?X4, ?X23, ?X24, ?X25, ?X26, ?X27, ?Z3, ?Z4, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; reflexivity. }
      split.
      { (* [comment removed for export] *)
        intros a NE. destruct (decide (M4 a = Mfin a)) as [E|N].
        { rewrite E in NE. exact (CHG a NE). }
        destruct (CH4 a N) as [D _]. unfold drain_changed in D. rewrite at_u in D by lia. rewrite BT_ia in D.
        (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite <- HSsp.
        destruct D as [D|[D|D]]; [left; lia | right; left; exact D | right; right; left; exact D]. }
      split.
      { (* [comment removed for export] *)
        intros a Hin Da. apply GR4; [| apply GRF; exact Da].
        intros (_ & NI & _). apply NI. unfold in_errno, ia_errno in Hin. cbn [ia_tp ia_img_lo ia_img_hi both_addrs] in Hin |- *. lia. }
      split.
      { (* [comment removed for export] *)
        intros a Ha. destruct (SOK a Ha) as [D1 D2].
        assert (D4 : M4 a <> None) by (apply GR4; [intros (LT & _); unfold MSTK_A in *; lia | exact D1]).
        split; [exact D4 | apply store_ok1_def; exact D4]. }
      split.
      { exists st3. split; [exact W3 | split; [exact RP6 |]].
        split; [| exact (model_ivs_wf_sbm mdl5 mdl6 SBM6 MW5)].
        split; [unfold bounds in BD1 |- *; rewrite KA; exact BD1 | exact (hp_fin bt HP HPc FAM h st3 (hp_neut bt HP HPc FAM h st1 st3 HLE1 (proj1 HO) (proj2 HO) KA))]. }
      split.
      { eapply same_except_vm_trans; [exact SEV|]. eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM4|].
        eapply same_except_vm_trans; [exact SEV4 | apply same_but_materialized_except_vm; exact SBM6]. }
      split; [| exact HH6].
      intros a Ha. transitivity (lzb mdl5 a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz6; reflexivity|].
      transitivity (lzb mdl4 a); [apply LZ4; rewrite BT_ia; exact Ha|].
      transitivity (lzb mdl3 a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz4; reflexivity|]. exact (LZK a Ha).
  Qed.
End TAIL.
End BoAllocFTail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemM OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRunI.BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRun3N.BoAllocFRun3 BoAllocFRunM OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFMemM OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTop0i.BoAllocFTopA BoAllocFTail.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAllocFFam.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma down8_up8 : forall n, AsRtRegion.down8 (n + 7) = up8 n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold AsRtRegion.down8, AsAinvOpsPf3d.AsAinvFreeS.up8 in G in change_no_check G' end). reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section PUTB.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variable KDR : Z.
  Hypothesis G_KDR : 0 <= KDR <= 1376.
  Hypothesis HYP_DRAIN : HYP_DRAIN_stmt bt FXOK KDR.
  (* [comment removed for export] *)
  Hypothesis OPS_WFX_append : forall st Lc FF L1 L2 p n tq' b,
    WF bt st Lc FF -> a_kact st <= KCAP -> Lc = L1 ++ (p, n) :: L2 -> a_tq st = tq' ++ [b] ->
    Z.of_nat (length (ba_items b)) < BATCHCAP -> WFX bt (op_quar_append st (p - 16) n) (L1 ++ L2) FF.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_putB_stmt : Prop :=
    forall (h : option Z) fx' (R R' : bvmap 5 word) (M M' M0 : mem) (mdl mdl' : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K1 ret sp m : Z) (p : word)
           (st' : ast) (id : Z) (tq' : list batch) (b : batch),
      let S := getr R 2 in
      (* [comment removed for export] *)
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> getr R 10 = p ->
      Lc = L1 ++ (U p, m) :: L2 ->
      (* [comment removed for export] *)
      WF bt st' Lc FF -> Rep bt st' Lc FF M0 mdl' -> bounds st' Lc B C K1 -> HPc h st' ->
      a_tq st' = tq' ++ [b] -> Z.of_nat (length (ba_items b)) < BATCHCAP -> m <= 2 ^ 28 ->
      (* [comment removed for export] *)
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

  Theorem free_putB : free_putB_stmt.
  Proof using FAM OPS_WFX_append HYP_DRAIN G_KDR KDR G_KD GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_putB_stmt in G in change_no_check G' end).
    intros h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C K1 ret sp m p st' id tq' b CP HR10 ELc W' RP' BD' HLE ETQ CNT M28
           HFX' HH' MW' DX CHG Hb16 Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6
           Y2 Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y22 Y3 Y4 Y23 Y24 Y25 Y26 Y27 Hid SEV LZ.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. fold tp in Y4.
    assert (Utp : U tp = 0x641380) by (rewrite CP4; vm_compute; reflexivity).
    unfold IB in Y18. rewrite BT_ia in Y18. cbn [ia_instance both_addrs] in Y18.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as
      (OBL_nolazy_rt & OBL_freed_private & OBL_rt_private & _ & OBL_blk_geom & OBL_batch_geom & OBL_hdr_writable & OBL_X_vs_node & OBL_store_private).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_freed_private_stmt in OBL_freed_private. unfold OBL_rt_private_stmt in OBL_rt_private.
    unfold OBL_blk_geom_stmt in OBL_blk_geom. unfold OBL_batch_geom_stmt in OBL_batch_geom.
    unfold OBL_hdr_writable_stmt in OBL_hdr_writable.
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    assert (HinB : In b (a_tq st' ++ a_gq st')) by (apply in_app_iff; left; rewrite ETQ; apply in_app_iff; right; left; reflexivity).
    destruct (live_range bt st' Lc FF W' (U p) m HinP) as (Lp1 & Lp2 & Lp3 & Lp4).
    destruct (OBL_blk_geom st' Lc FF (U p) m W' HinP) as (GpT & GCp & (AB1 & AB2 & AB3 & AB4)).
    pose proof (blk_above_img bt st' Lc FF W' ltac:((lazymatch goal with |- ?G => let G' := eval unfold img_lo_small in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) (U p) m HinP) as PIMG.
    destruct (up8_facts m ltac:(lia)) as (U8a & U8b & U8c & U8d).
    destruct (OBL_batch_geom st' Lc FF b (U p) m W' HinB HinP) as (GBp & GBT & GBlo & GBhi).
    pose proof (thread_dyn bt st' Lc FF W') as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    clear AB3 GCT' GCB.
    destruct (read_tq_last bt st' Lc FF M0 mdl' tq' b W' RP' ETQ) as (Qlen & Qlast & Qbytes & Bnext & Bsize & Bcnt & Bitems & BW & Bcv & Blen & Blo & Bhi).
    clear OBL_blk_geom OBL_batch_geom.
    (* [comment removed for export] *)
    assert (QA : 0 <= q_bytes tq' /\ BATCHSZ <= ba_bytes b /\ q_bytes (a_tq st') = q_bytes tq' + ba_bytes b
                 /\ 1 <= Z.of_nat (length (a_tq st')) <= 2 ^ 8 /\ q_bytes (a_tq st') <= 2 ^ 20).
    { pose proof W' as (_ & _ & (QT & _ & QTB & _) & _). rewrite Forall_forall in QT.
      assert (IT : forall b0, In b0 (a_tq st') -> forall m0 n0, In (m0, n0) (ba_items b0) -> 1 <= n0).
      { intros b0 Hb0 m0 n0 Hin. destruct (QT b0 Hb0) as (_ & _ & WI). destruct (WI m0 n0 Hin) as [X _]. lia. }
      pose proof (q_bytes_ge (a_tq st') IT) as G1.
      assert (G2 : BATCHSZ * Z.of_nat (length tq') <= q_bytes tq').
      { apply q_bytes_ge. intros b0 Hb0. apply IT. rewrite ETQ. apply in_app_iff. left. exact Hb0. }
      assert (G3 : BATCHSZ <= ba_bytes b) by (apply ba_bytes_ge; apply IT; rewrite ETQ; apply in_app_iff; right; left; reflexivity).
      rewrite ETQ, q_bytes_app in QTB, G1 |- *. cbn [q_bytes fold_right] in QTB, G1 |- *. rewrite length_app in G1 |- *. cbn [length] in G1 |- *.
      unfold BATCHSZ in G1, G2, G3, QTB |- *. clear - G1 G2 G3 QTB. repeat split; lia. }
    destruct QA as (QA1 & QA2 & QA3 & QA4 & QA5).
    (* [comment removed for export] *)
    pose proof RP' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R8 as [RH _]. destruct (RH (U p) m HinP) as (Hst & H11 & Hnhi & Hnlo & Hw8 & Hz4 & _).
    destruct (R15 (U p) m HinP) as [WBLK WSH].
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    pose proof R17 as Csb.
    pose proof (OBL_hdr_writable st' Lc FF M0 mdl' (U p) m W' RP' HinP) as WHDR.
    clear R2 R4 R5 R6 R7 R9 R10 R12 R16 R18 RH TQ TPC OBL_hdr_writable.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI, PIMG.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, NMAX, BATCHSZ, BATCHCAP, T_QC, SB, KSPACE, PTRLO in *.
    destruct (p16_facts (U p) Lp4 ltac:(lia)) as (_ & _ & _ & P8 & _ & _).
    destruct (sh_up8 (U p) m P8 ltac:(lia)) as [SHhi SHlo]. unfold SB in SHhi, SHlo.
    destruct (shad_facts2 (U p) (up8 m) ltac:(clear -AB4 Hpr U8a; lia) ltac:(clear - Hpr; lia) ltac:(clear - AB2 CR; lia) U8b P8 U8d) as (D81 & D82 & D83 & D84 & D85 & D86).
    (* [comment removed for export] *)
    assert (XdC : forall z, AIMGLO <= z < AIMGHI -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite CP2; clear -Hz GTI PIMG CPlo CR HSr; lia).
    assert (XdT : forall z, T <= z < T + 2800 -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b CP2 CPlo GTC; lia).
    assert (XdB : forall z, ba_addr b <= z < ba_addr b + 8192 -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GBp GBT GBhi U8b CP2 CPlo; lia).
    assert (XdH : forall z, U p - 15 <= z < U p -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b AB2 CP2 CPlo; lia).
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - CP2 CPlo CPhi CR; lia).
    assert (Gpm : AIMGHI + 16 <= U p /\ (PSIDE (U p) (up8 m) /\ U p + up8 m <= U S - 3584) /\ U p mod 16 = 0).
    { split; [clear - PIMG; lia|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear -AB4 U8a; lia | clear - AB2 U8a CP2 CPlo; lia] | exact Lp4]. }
    assert (GTm : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; split; lia | clear - GTC CP2 CPlo; lia]. }
    assert (Gn8m : 8 <= up8 m /\ up8 m mod 8 = 0 /\ up8 m <= 2 ^ 40) by (clear - U8a U8b U8c U8d M28 Lp3; lia).
    assert (Glm : 0x10007fff8000 <= ba_addr b /\ ba_addr b + 8192 <= U S - 3584) by (clear - GBlo GBhi CP2 CPlo; lia).
    assert (GlTm : ba_addr b + 8192 <= T \/ T + 4096 <= ba_addr b) by (clear - GBT; lia).
    assert (Glpm : ba_addr b + 8192 <= U p - 16 \/ U p + up8 m <= ba_addr b) by (clear - GBp; lia).
    assert (GpTm : U p + up8 m <= T \/ T + 4096 <= U p - 16) by (clear - GpT; lia).
    assert (Gcm : 0 <= Z.of_nat (length (ba_items b)) < 1021) by (clear - CNT; lia).
    hidehyp GpT. hidehyp GCp. hidehyp GCT. hidehyp GBp. hidehyp GBT. hidehyp GlTm. hidehyp Glpm. hidehyp GpTm.
    hidehyp GTI. hidehyp GTB. hidehyp AB4. hidehyp D81. hidehyp GCI.
    (* [comment removed for export] *)
    assert (EQ0 : forall a : word, ~ Xd (U S) (U p) T (U a) -> M' a = M0 a).
    { intros a Ha. destruct (decide (M' a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M') by (intros a Ha; destruct (decide (M' a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    assert (GRM : mem_grows M M') by (intros a Ha; destruct (decide (M' a = M a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (CHG a N))]).
    (* [comment removed for export] *)
    set (Hd := HID st' mdl').
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdl' z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHp : forall z, U p - 16 <= z < U p + up8 m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; left. exists (U p), m. split; [exact HinP | exact Hz]. }
    assert (NHb : forall z, ba_addr b <= z < ba_addr b + 8192 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; right. exists b. split; [exact HinB | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hz]. }
    assert (NHsh : forall z, sh_lo (U p) <= z < sh_hi (U p) m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. exact (B4 (U p) m HinP z Hz). }
    assert (LZT : forall z, T <= z < T + 4096 -> lzb mdl' z = false).
    { intros z Hz. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    clear OBL_nolazy_rt.
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac cell0 EQ0 NH XD C :=
      rewrite rdn_mrestrict; [ | wd_ulia_c | unorm; hoff NH ];
      eapply rd_same; [ intros x Hx; apply EQ0; apply XD; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | wd_ulia_c | exact C ].
    Ltac konst EQ0 R1 NHs XdC C := cell0 EQ0 NHs XdC (const_cell bt _ _ _ _ R1 C).
    assert (K_mcsz : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20)))) by konst EQ0 R1 NHs XdC CELL_mcsz.
    assert (K_msz : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28)))) by konst EQ0 R1 NHs XdC CELL_msz.
    assert (K_gfl : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 FL))) by konst EQ0 R1 NHs XdC CELL_gfl.
    assert (K_mff : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (FL + 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by konst EQ0 R1 NHs XdC CELL_mff.
    assert (K_gsh : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by konst EQ0 R1 NHs XdC CELL_gsh.
    assert (K_sh : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { cbn [ia_rtc_sb both_addrs] in Csb. cell0 EQ0 NHs XdC Csb. }
    assert (K_gmb : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by konst EQ0 R1 NHs XdC CELL_gmb.
    assert (K_mb : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by konst EQ0 R1 NHs XdC CELL_mb.
    assert (K_gme : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by konst EQ0 R1 NHs XdC CELL_gme.
    assert (K_me : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by konst EQ0 R1 NHs XdC CELL_me.
    assert (K_ghe : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by konst EQ0 R1 NHs XdC CELL_ghe.
    assert (K_he : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by konst EQ0 R1 NHs XdC CELL_he.
    assert (K_grm : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by konst EQ0 R1 NHs XdC CELL_grm.
    assert (K_rm : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by konst EQ0 R1 NHs XdC CELL_rm.
    assert (K_cpm : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 CPM]).
    { rewrite <- w2b1 by lia. konst EQ0 R1 NHs XdC CELL_cpm. }
    (* [comment removed for export] *)
    assert (K_len : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (a_tq st')))))) by cell0 EQ0 NHT XdT Qlen.
    assert (K_last : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr b)))).
    { replace (T + 96) with (T + 80 + 16) by lia. cell0 EQ0 NHT XdT Qlast. }
    assert (K_qb : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (q_bytes (a_tq st'))))).
    { replace (T + 104) with (T + 80 + 24) by lia. cell0 EQ0 NHT XdT Qbytes. }
    assert (K_bsz : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (ba_addr b + 8)) 8 = Some (LE8 (Z_to_bv 64 (ba_bytes b)))) by cell0 EQ0 NHb XdB Bsize.
    assert (K_cnt : rdn BSEGS (mrestrict Hd M') (Z_to_bv 64 (ba_addr b + 16)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (ba_items b)))))) by cell0 EQ0 NHb XdB Bcnt.
    assert (K_nhi : rdn BSEGS (mrestrict Hd M') (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (m / 2 ^ 32)))).
    { replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnhi. }
    assert (K_nlo : rdn BSEGS (mrestrict Hd M') (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (m mod 2 ^ 32)))).
    { replace (at_ p (-12)) with (Z_to_bv 64 (U p - 12)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnlo. }
    clear Qlen Qlast Qbytes Bnext Bsize Bcnt Bitems Hnhi Hnlo Csb R1.
    (* [comment removed for export] *)
    Ltac stk NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
    assert (S_q0 : rdn BSEGS (mrestrict Hd M') (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14))) by stk NHs Cq0.
    assert (S_q1 : rdn BSEGS (mrestrict Hd M') (at_ S (-2144)) 8 = Some (LE8 S)) by stk NHs Cq1.
    assert (S_q2 : rdn BSEGS (mrestrict Hd M') (at_ S (-2152)) 8 = Some (LE8 p)) by stk NHs Cq2.
    assert (S_q3 : rdn BSEGS (mrestrict Hd M') (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))) by stk NHs Cq3.
    assert (S_q4 : rdn BSEGS (mrestrict Hd M') (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))) by stk NHs Cq4.
    assert (S_q5 : rdn BSEGS (mrestrict Hd M') (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))) by stk NHs Cq5.
    assert (S_i0 : rdn BSEGS (mrestrict Hd M') (at_ S (-8)) 8 = Some (LE8 (Z_to_bv 64 ret))) by (rewrite <- CP1; stk NHs Ci0).
    assert (S_i1 : rdn BSEGS (mrestrict Hd M') (at_ S (-16)) 8 = Some (LE8 (getr R 8))) by stk NHs Ci1.
    assert (S_i2 : rdn BSEGS (mrestrict Hd M') (at_ S (-24)) 8 = Some (LE8 (getr R 9))) by stk NHs Ci2.
    assert (S_i3 : rdn BSEGS (mrestrict Hd M') (at_ S (-32)) 8 = Some (LE8 (getr R 18))) by stk NHs Ci3.
    assert (S_i4 : rdn BSEGS (mrestrict Hd M') (at_ S (-40)) 8 = Some (LE8 (getr R 19))) by stk NHs Ci4.
    assert (S_i5 : rdn BSEGS (mrestrict Hd M') (at_ S (-48)) 8 = Some (LE8 (getr R 20))) by stk NHs Ci5.
    assert (S_i6 : rdn BSEGS (mrestrict Hd M') (at_ S (-56)) 8 = Some (LE8 (getr R 21))) by stk NHs Ci6.
    clear Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6.
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS (mrestrict Hd M') (at_ S (-2304)) 2304 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia.
      eapply store_ok_mono; [exact GRM|]. apply CPstk. cbn in Hx. rewrite <- CP2. lia. }
    assert (SOKp : store_ok BSEGS (mrestrict Hd M') p 8 = true).
    { rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHp].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WHDR); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (SOKsh : store_ok BSEGS (mrestrict Hd M') (Z_to_bv 64 (shad p)) (Z.to_nat (up8 m / 8)) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). rewrite store_ok_mrestrict; [| unorm; rewrite Z2Nat.id by lia; lia | unorm; rewrite Z2Nat.id by lia; hoff NHsh].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WSH); unorm; rewrite ?Z2Nat.id by lia; lia. }
    assert (SOKT : store_ok BSEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 32 = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHT].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ TW); wd_ulia_c. }
    assert (SOKb : store_ok BSEGS (mrestrict Hd M') (Z_to_bv 64 (ba_addr b)) (Z.to_nat 8192) = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHb].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ BW); wd_ulia_c. }
    clear WHDR WSH WBLK TW BW.
    (* [comment removed for export] *)
    assert (GS3 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gn3 : 1 <= m <= 2 ^ 28) by lia.
    assert (Gn83 : AsRtRegion.down8 (m + 7) = up8 m /\ m <= up8 m <= m + 7 /\ up8 m mod 8 = 0 /\ 8 <= up8 m) by (split; [apply down8_up8 | lia]).
    assert (Gfl3 : 0 <= FL /\ FL + 4096 <= AIMGHI) by lia.
    assert (Gbsz3 : 0 <= ba_bytes b < 2 ^ 40) by lia.
    assert (Gqb3 : 0 <= q_bytes (a_tq st') <= 2 ^ 20) by (clear - QA1 QA2 QA3 QA5; lia).
    pose proof W' as (_ & _ & (_ & _ & _ & QGB & _) & _).

    assert (Glen3 : 1 <= Z.of_nat (length (a_tq st')) < 2 ^ 40) by lia.
    assert (Gcnt3 : 1 <= Z.of_nat (length (ba_items b)) < 1021) by lia.
    assert (Gmid3 : U (Z_to_bv 64 MIDEND) < 2 ^ 64) by (wd_ulia).
    assert (Hret3 : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_lit; [lia | exact CPe]).
    assert (Ccpm1 : U (Z_to_bv 8 CPM) <> 0) by (rewrite (Z_to_bv_small 8 CPM ltac:(change (bv_modulus 8) with 256; lia)); lia).
    assert (D20' : getr R' 20 = Z_to_bv 64 T) by exact Y20.
    (* [comment removed for export] *)
    destruct (run_m3 (mrestrict Hd M') (seg_rom BSEGS) R' S p tp (getr R 22)
                T m (up8 m) id FL (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st')) (Z.of_nat (length (a_tq st')))
                (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND))
      as (rf & RUN3 & Z2 & Z22 & Z3 & Z4 & Z23 & Z24 & Z25 & Z26 & Z27).
    all: try assumption.
    all: try reflexivity.
    all: try (unfold hide in *; assumption).
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    replace (0x50838%bv : word) with (Z_to_bv 64 0x50838 : word) in RUN3 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st' Lc FF M0 mdl' BT_ia RP') asanF_segs_wx (a_aa st')
             (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS))
             (@mkst fx' rf (0x50c04%bv : word) (fr_P3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) (seg_rom BSEGS)) mdl').
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH'. }
    { rewrite restrict_mkstF. exact RUN3. }
    clear RUN3 K_mcsz K_msz K_gfl K_mff K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_cpm K_len K_last K_qb K_bsz K_cnt K_nhi K_nlo
          S_q0 S_q1 S_q2 S_q3 S_q4 S_q5 SOKstk SOKp SOKsh SOKT SOKb.
    intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx' R' (Z_to_bv 64 0x50838) M' (seg_rom BSEGS))) with M' by reflexivity.
    pose proof (same_but_materialized_frame mdl' mdl3 SBM3) as SF3.
    destruct SF3 as (_ & Evm3 & Elz3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _ & _ & _ & Eeg3).
    remember (fr_P3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as M13 eqn:EM13.
    set (Mfin := munrestrict Hd M' M13).
    pose proof (fr_P3_grows (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as GR13.
    feed GR13. rewrite <- EM13 in GR13.
    assert (VIS : forall a : word, Hd a = false -> Mfin a = M13 a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> Mfin a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM' : forall a : word, Hd a = false -> mrestrict Hd M' a = M' a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GRfin' : mem_grows M' Mfin).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GR13. rewrite (MrM' a Eh). exact Ha. }
    assert (GRfin : mem_grows M Mfin) by (eapply mem_grows_trans; [exact GRM | exact GRfin']).
    (* [comment removed for export] *)
    pose proof (fr_P3_foot (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as P3F.
    feed P3F. rewrite <- EM13 in P3F.
    assert (DIFF3 : forall a : word, Mfin a <> M' a ->
              (U S - 2264 <= U a < U S - 2128) \/ (U p <= U a < U p + 8) \/ (0x7fff8000 + U p / 8 <= U a < 0x7fff8000 + U p / 8 + up8 m / 8)
              \/ (ba_addr b + 8 <= U a < ba_addr b + 24)
              \/ (ba_addr b + 24 + 8 * Z.of_nat (length (ba_items b)) <= U a < ba_addr b + 32 + 8 * Z.of_nat (length (ba_items b)))
              \/ (T + 104 <= U a < T + 112)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM' a Eh) in NE. exact (P3F a NE). }
    (* [comment removed for export] *)
    assert (PRIVp : forall z, (U p - 16 <= z < U p + up8 m \/ sh_lo (U p) <= z < sh_hi (U p) m) -> rt_priv both_addrs (L1 ++ L2) FF z).
    { intros z Hz. exact (OBL_freed_private st' Lc FF L1 L2 (U p) m z W' ELc Hz). }
    assert (PRIVT : forall z, (T <= z < T + 4096 \/ ba_addr b <= z < ba_addr b + 8192) -> rt_priv both_addrs (L1 ++ L2) FF z).
    { intros z Hz. destruct (OBL_rt_private st' Lc FF z W') as (Z1' & Z2' & Z3').
      { (lazymatch goal with |- ?G => let G' := eval unfold PG, BATCHSZ in G in change_no_check G' end). destruct Hz as [Hz|Hz]; [left; exact Hz | right; exists b; split; [exact HinB | exact Hz]]. }
      split; [exact Z1'|]. split; [exact Z2'|]. intros V. apply Z3'. rewrite ELc. apply app_visible_mono. exact V. }
    clear OBL_freed_private OBL_rt_private.
    (* [comment removed for export] *)
    assert (XS : forall k bs0, -2304 <= k -> k + 8 <= 0 -> rdn BSEGS M13 (at_ S k) 8 = Some bs0 -> rdn BSEGS Mfin (at_ S k) 8 = Some bs0).
    { intros k bs0 Hk1 Hk2 Hr. apply (rd_same BSEGS Mfin M13); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range|]. rewrite at_u in Hx by lia. cbn in Hx. lia. }
    pose proof (fr_P3_stk (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as P3K.
    feed P3K. rewrite <- EM13 in P3K.
    assert (XH : forall k bs0, -2128 <= k -> k + 8 <= 0 -> rdn BSEGS (mrestrict Hd M') (at_ S k) 8 = Some bs0 -> rdn BSEGS M13 (at_ S k) 8 = Some bs0).
    { intros k bs0 Hk1 Hk2 Hr. apply (rd_same BSEGS M13 (mrestrict Hd M')); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply P3K. lia. }
    replace (0x50c04%bv : word) with (Z_to_bv 64 0x50c04 : word) by (apply bv_eq; reflexivity).
    apply (free_put_tail bt FXOK KDR BT_segs BT_ia GEOM G_KDR HYP_DRAIN HP HPc FAM
             h fx' R rf M Mfin mdl mdl3 (L1 ++ L2) FF (Z.max 0 (B - (m + MBLK))) (Z.max 0 (C - 1)) K1 ret sp
             (op_quar_append st' (U p - 16) m) p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81))
             (Z_to_bv 64 m) (at_ S (-2128)) (at_ (Z_to_bv 64 T) 208) (at_ p (-16))).
    all: rewrite ?BT_ia.
    - exact CP1.
    - exact CPr.
    - exact CPe.
    - exact CP2.
    - exact CP16.
    - exact CPlo.
    - exact CPhi.
    - exact CP4.
    - exact HFX'.
    - rewrite Eh3. exact HH'.
    - exact (model_ivs_wf_sbm mdl' mdl3 SBM3 MW').
    - exact (OPS_WFX_append st' Lc FF L1 L2 (U p) m tq' b W' (hp_kcap bt HP HPc FAM h st' HLE) ELc ETQ CNT).
    - (* [comment removed for export] *)
      assert (XF : forall c bs0, 0 <= c -> c + 8 <= 2 ^ 64 -> (forall z, c <= z < c + 8 -> Hd (Z_to_bv 64 z) = false) ->
                rdn BSEGS M13 (Z_to_bv 64 c) 8 = Some bs0 -> rdn BSEGS Mfin (Z_to_bv 64 c) 8 = Some bs0).
      { intros c bs0 Hc1 Hc2 NH Hr. apply (rd_same BSEGS Mfin M13); [| wd_ulia_c | exact Hr].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NH. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia. }
      pose proof (fr_P3_hdr16 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as P3H. feed P3H.
      pose proof (fr_P3_shadow (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as P3S. feed P3S.
      pose proof (fr_P3_bsz (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as P3B. feed P3B.
      pose proof (fr_P3_cnt (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as P3C. feed P3C.
      pose proof (fr_P3_slot (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as P3L. feed P3L.
      pose proof (fr_P3_qb (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as P3Q. feed P3Q.
      rewrite <- EM13 in P3H, P3S, P3B, P3C, P3L, P3Q.
      apply (OPS_REP_quar_append_pf bt st' Lc FF L1 L2 M0 Mfin mdl' mdl3 (U p) m tq' b W' RP' ELc ETQ CNT).
      * (* [comment removed for export] *)
        intros a NE. pose proof (u64_range a) as Ha. split; cycle 1.
        { destruct (Mfin a) eqn:EF; [discriminate|]. exfalso. apply NE. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
          assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GR0, GRfin' in D. rewrite EF in D. exact (D eq_refl). }
        (lazymatch goal with |- ?G => let G' := eval unfold foot_quar_append in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end).
        destruct (decide (Mfin a = M' a)) as [E|N].
        { rewrite E in NE. destruct (DX a NE) as [X _]. unfold Xd in X. rewrite CP2 in X.
          destruct X as [X|[X|[X|X]]]; [left; exact X | right; left; exact X | do 6 right; left; lia | do 7 right; lia]. }
        destruct (DIFF3 a N) as [X|[X|[X|[X|[X|X]]]]].
        { do 7 right. rewrite CP2 in X. lia. }
        { right; left. exact X. }
        { right; right; left. unfold sh_lo, sh_hi, SB in *. lia. }
        { do 3 right; left. exact X. }
        { do 4 right; left. exact X. }
        { do 5 right; left. lia. }
      * (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. rewrite w2b1 by lia. apply heap_rdn1; [wd_ulia|].
        replace (Z_to_bv 64 (U p - 16)) with (at_ p (-16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
        assert (Eh : Hd (at_ p (-16)) = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ p (-16))); rewrite at_u by lia; apply NHp; lia).
        rewrite (VIS _ Eh). rewrite P3H. rewrite (MrM' _ Eh). exact Hb16.
      * (* [comment removed for export] *)
        intros g Hg. pose proof (granule_idx (U p) m g P8 Hg) as GI.
        (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. rewrite w2b1 by lia. unfold user_granule in Hg. apply heap_rdn1; [(lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); wd_ulia|].
        assert (Eh : Hd (Z_to_bv 64 (SB + g)) = false) by (apply NHsh; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end); lia).
        rewrite (VIS _ Eh). replace (SB + g) with (SB + U p / 8 + (g - U p / 8)) by lia. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). apply P3S. exact GI.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |]. exact P3B.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |]. exact P3C.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. apply XF; [lia | lia | intros z Hz; apply NHb; lia |].
        replace (Z_to_bv 64 (U p - 16)) with (at_ p (-16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). exact P3L.
      * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_QC in G in change_no_check G' end). replace (T + 80 + 24) with (T + 104) by lia.
        apply XF; [lia | lia | intros z Hz; apply NHT; lia |]. exact P3Q.
      * exact SBM3.
      * exact MI3.
    - (* [comment removed for export] *)
      assert (PH0 : 0 <= PHI (L1 ++ L2)).
      { apply PHI_nonneg. intros q n0 Hin.
        assert (Hin' : In (q, n0) Lc).
        { rewrite ELc. apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin]. }
        destruct (live_range bt _ _ _ W' q n0 Hin') as (_ & _ & X & _). lia. }
      unfold bounds in BD' |- *. rewrite (op_quar_append_eq st' tq' b) by exact ETQ. (lazymatch goal with |- ?G => let G' := eval cbn [a_kact set_tq] in G in change_no_check G' end).
      rewrite ELc in BD'. rewrite PHI_app in BD' |- *. cbn [PHI snd fst] in BD'. rewrite length_app in BD' |- *. cbn [length] in BD'.
      rewrite PHI_app in PH0. unfold kcost_free, MBLK in *.
      destruct BD' as (BDa & BDb & BDc). split; [lia|]. split; [lia|]. lia.
    - (* [comment removed for export] *)
      apply (hp_neut bt HP HPc FAM h st' _ HLE); [| apply fk_quar_append | rewrite (op_quar_append_eq st' tq' b) by exact ETQ; reflexivity].
      intros h' H'. rewrite (op_quar_append_eq st' tq' b) by exact ETQ. unfold holes_le in H' |- *. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_tq] in G in change_no_check G' end). exact H'.
    - (* [comment removed for export] *)
      rewrite (op_quar_append_eq st' tq' b) by exact ETQ. (lazymatch goal with |- ?G => let G' := eval cbn [a_gq set_tq] in G in change_no_check G' end). exact QGB.
    - (* [comment removed for export] *)
      rewrite (op_quar_append_eq st' tq' b) by exact ETQ. (lazymatch goal with |- ?G => let G' := eval cbn [a_tq set_tq] in G in change_no_check G' end). intros E. destruct tq'; discriminate E.
    - (* [comment removed for export] *)
      rewrite (op_quar_append_eq st' tq' b) by exact ETQ. (lazymatch goal with |- ?G => let G' := eval cbn [a_tq set_tq] in G in change_no_check G' end). rewrite q_bytes_app. (lazymatch goal with |- ?G => let G' := eval cbn [q_bytes fold_right] in G in change_no_check G' end).
      (lazymatch goal with |- ?G => let G' := eval unfold ba_bytes in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end). rewrite fold_items_app. (lazymatch goal with |- ?G => let G' := eval cbn [fold_right snd] in G in change_no_check G' end).
      unfold ba_bytes in QA2, QA3. clear - QA1 QA2 QA3 QA5 M28 Lp3. lia.
    - (* [comment removed for export] *)
      intros z Hz. transitivity (lzb mdl' z); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|]. apply LZT. exact Hz.
    - exact Z2. - exact Z22. - rewrite Z3; exact Y3. - rewrite Z4; reflexivity. - rewrite Z23; exact Y23. - rewrite Z24; exact Y24.
    - rewrite Z25; exact Y25. - rewrite Z26; exact Y26. - rewrite Z27; exact Y27.
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_e0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_e1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_e2 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_e3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_e4 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_e5 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_e6 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_cb0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_cb1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_q0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_q1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_q2 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_q3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_q4 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_q5 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_q6 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | (let PM := fresh "PM" in pose proof (fr_P3_q7 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id (ba_addr b) (Z.of_nat (length (ba_items b))) (ba_bytes b) (q_bytes (a_tq st'))) as PM; feed PM; rewrite <- EM13 in PM; exact PM)].
    - apply XS; [lia | lia | apply XH; [lia | lia | fold ra0; rewrite CP1; exact S_i0]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i1]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i2]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i3]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i4]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i5]].
    - apply XS; [lia | lia | apply XH; [lia | lia | exact S_i6]].
    - (* [comment removed for export] *)
      intros a Ha. rewrite <- CP2 in Ha. unfold MSTK_A in Ha. split.
      + apply GRfin. apply store_ok1_heap; [clear - Ha CPlo CP2 CR; lia|]. apply CPstk. rewrite <- CP2. lia.
      + eapply store_ok_mono; [exact GRfin|]. apply CPstk. rewrite <- CP2. lia.
    - (* [comment removed for export] *)
      intros a NE. pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). rewrite <- CP2. (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end).
      destruct (decide (Mfin a = M' a)) as [E|N].
      { rewrite E in NE. destruct (CHG a NE) as [[X|[X|[X|X]]] _].
        - unfold Xd in X. destruct X as [X|[X|[X|X]]].
          + right; left. apply PRIVp. left. lia.
          + right; left. apply PRIVp. left. lia.
          + right; left. apply PRIVT. left. lia.
          + left. lia.
        - left. lia.
        - right; left. destruct X as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. intros V. apply X3. rewrite ELc. apply app_visible_mono. exact V.
        - right; right; left. exact X. }
      destruct (DIFF3 a N) as [X|[X|[X|[X|[X|X]]]]].
      + left. lia.
      + right; left. apply PRIVp. left. lia.
      + right; left. apply PRIVp. right. unfold sh_lo, sh_hi, SB in *. lia.
      + right; left. apply PRIVT. right. lia.
      + right; left. apply PRIVT. right. lia.
      + right; left. apply PRIVT. left. lia.
    - exact GRfin.
    - eapply same_except_vm_trans; [exact SEV | apply same_but_materialized_except_vm; exact SBM3].
    - (* [comment removed for export] *) intros a Ha. transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz3; reflexivity|]. apply LZ.
      destruct Ha as [V|[V|V]]; [left; rewrite ELc; apply app_visible_mono; exact V | right; left; exact V | right; right; exact V].
  Qed.
End PUTB.

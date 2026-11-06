(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocF2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_70b0c_71670 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_78b0c_799f4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0.Bo_code_7d08c_7db0c OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_fc94c_fce54 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_fdbac_fdd40 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_fde90_fe69c OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT.Bo_code_fe6a4_fe6b0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record gctwH (mem : word -> option byte) (tp tsd key tctx T : Z) (kib : byte) : Prop := GCTWH {
  gc_kib : rdn BSEGS mem (Z_to_bv 64 0x10da20) 1 = Some [kib];
  gc_kibnz : bv_unsigned kib <> 0%Z;
  gc_key : rdn BSEGS mem (Z_to_bv 64 0x10da24) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 key));
  gc_keyr : (0 <= key < 2 ^ 20)%Z;
  gc_tsd : rdn BSEGS mem (Z_to_bv 64 (tp - 88)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd));
  gc_ctx : rdn BSEGS mem (Z_to_bv 64 (tsd + 8 * key)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tctx));
  gc_T : rdn BSEGS mem (Z_to_bv 64 (tctx + 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 T));
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
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (k - 16)) 16 = true.

End GCT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b1 (mem : word -> option byte) (S p x18 x19 x20 x21 x22 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2136)) (word_to_le_bytes 8 (Z_to_bv 64 0x6ef14)))
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
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.

  Lemma b1_run :
    exists r,
      msteps BSEGS (mkst regs (0x6ef00 : word) mem rom) (mkst r (0x7d6bc : word) (fr_b1 mem S p x18 x19 x20 x21 x22) rom)
      /\ getr r 1 = Z_to_bv 64 0x4c2cc /\ getr r 2 = at_ S (-2192) /\ getr r 8 = at_ S (-2128) /\ getr r 9 = p
      /\ getr r 10 = p /\ getr r 18 = at_ p (-16) /\ getr r 19 = Z_to_bv 64 0x10ab58 /\ getr r 20 = Z_to_bv 64 1
      /\ getr r 21 = Z_to_bv 64 0 /\ getr r 22 = Z_to_bv 64 0
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk Hp HS H22 H21 H20 H19 H18 H9 H8 H2.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    wd_eexists. split.
    - an F_6ef00 D_6ef00.                              (* [comment removed for export] *)
      an F_6ef04 D_6ef04.                              (* [comment removed for export] *)
      an F_6ef08 D_6ef08.                              (* [comment removed for export] *)
      an F_6ef0c D_6ef0c.                              (* [comment removed for export] *)
      an F_6ef10 D_6ef10.                              (* [comment removed for export] *)
      an F_4c258 D_4c258.                              (* [comment removed for export] *)
      an F_4c25c D_4c25c.                              (* [comment removed for export] *)
      an F_4c260 D_4c260.                              (* [comment removed for export] *)
      an F_4c264 D_4c264.                              (* [comment removed for export] *)
      an F_4c268 D_4c268.                              (* [comment removed for export] *)
      an F_4c26c D_4c26c.                              (* [comment removed for export] *)
      an F_4c270 D_4c270.                              (* [comment removed for export] *)
      an F_4c274 D_4c274.                              (* [comment removed for export] *)
      an F_4c278 D_4c278.                              (* [comment removed for export] *)
      an F_4c27c D_4c27c.                              (* [comment removed for export] *)
      an F_4c280 D_4c280.                              (* [comment removed for export] *)
      fsd F_4c284 D_4c284 (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_4c288 D_4c288 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_4c28c D_4c28c (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_4c290 D_4c290 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_4c294 D_4c294 (at_ S (-2168)).             (* [comment removed for export] *)
      fsd F_4c298 D_4c298 (at_ S (-2176)).             (* [comment removed for export] *)
      fsd F_4c29c D_4c29c (at_ S (-2184)).             (* [comment removed for export] *)
      fsd F_4c2a0 D_4c2a0 (at_ S (-2192)).             (* [comment removed for export] *)
      ab_ft F_4c2a4 D_4c2a4 ltac:(condz).              (* [comment removed for export] *)
      an F_4c2a8 D_4c2a8.                              (* [comment removed for export] *)
      an F_4c2ac D_4c2ac.                              (* [comment removed for export] *)
      an F_4c2b0 D_4c2b0.                              (* [comment removed for export] *)
      an F_4c2b4 D_4c2b4.                              (* [comment removed for export] *)
      an F_4c2b8 D_4c2b8.                              (* [comment removed for export] *)
      an F_4c2bc D_4c2bc.                              (* [comment removed for export] *)
      an F_4c2c0 D_4c2c0.                              (* [comment removed for export] *)
      an F_4c2c4 D_4c2c4.                              (* [comment removed for export] *)
      an F_4c2c8 D_4c2c8.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b1 mem S p x18 x19 x20 x21 x22). wd_refl.
    - post.
  Qed.
End B1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b2 (mem : word -> option byte) (S p : word) : word -> option byte :=
  wbytes (wbytes (wbytes mem
    (at_ S (-2200)) (word_to_le_bytes 8 (Z_to_bv 64 0x4c2cc)))
    (at_ S (-2208)) (word_to_le_bytes 8 (at_ S (-2128))))
    (at_ S (-2216)) (word_to_le_bytes 8 p).
Hint Unfold fr_b2 : asfr.

Section B2.
  Variables (mem rom : word -> option byte) (S p : word).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x4c2cc.
  Hypothesis H2 : getr regs 2 = at_ S (-2192).
  Hypothesis H8 : getr regs 8 = at_ S (-2128).
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H10 : getr regs 10 = p.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis Rhook : rdn BSEGS mem (Z_to_bv 64 0x19fc88) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Lemma b2_run :
    exists r,
      msteps BSEGS (mkst regs (0x7d6bc : word) mem rom) (mkst r (0x4c2cc : word) (fr_b2 mem S p) rom)
      /\ getr r 2 = at_ S (-2192) /\ getr r 8 = at_ S (-2128) /\ getr r 9 = p /\ getr r 10 = Z_to_bv 64 0
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rhook Hstk HS H10 H9 H8 H2 H1.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_7d6bc D_7d6bc.                              (* [comment removed for export] *)
      fsd F_7d6c0 D_7d6c0 (at_ S (-2200)).             (* [comment removed for export] *)
      fsd F_7d6c4 D_7d6c4 (at_ S (-2208)).             (* [comment removed for export] *)
      fsd F_7d6c8 D_7d6c8 (at_ S (-2216)).             (* [comment removed for export] *)
      an F_7d6cc D_7d6cc.                              (* [comment removed for export] *)
      an F_7d6d0 D_7d6d0.                              (* [comment removed for export] *)
      an F_7d768 D_7d768.                              (* [comment removed for export] *)
      rt F_7d76c D_7d76c.                              (* [comment removed for export] *)
      ab_tk F_7d6d4 D_7d6d4 ltac:(condz).              (* [comment removed for export] *)
      an F_7d6f0 D_7d6f0.                              (* [comment removed for export] *)
      an F_7d6f4 D_7d6f4.                              (* [comment removed for export] *)
      rt F_7d770 D_7d770.                              (* [comment removed for export] *)
      an F_7d6f8 D_7d6f8.                              (* [comment removed for export] *)
      an F_7d6fc D_7d6fc.                              (* [comment removed for export] *)
      cld8 F_7d700 D_7d700 (Z_to_bv 64 0) Rhook.       (* [comment removed for export] *)
      ab_tk F_7d704 D_7d704 ltac:(condz).              (* [comment removed for export] *)
      an F_7d750 D_7d750.                              (* [comment removed for export] *)
      fld F_7d754 D_7d754 (Z_to_bv 64 0x4c2cc).        (* [comment removed for export] *)
      fld F_7d758 D_7d758 (at_ S (-2128)).             (* [comment removed for export] *)
      fld F_7d75c D_7d75c p.                           (* [comment removed for export] *)
      an F_7d760 D_7d760.                              (* [comment removed for export] *)
      rt F_7d764 D_7d764.                              (* [comment removed for export] *)
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
Lemma cas_state_67264 : forall regs mem rom (m hv : word) h1 h2 h3,
  getr regs 13 = m -> getr regs 15 = Z_to_bv 64 255 -> getr regs 14 = Z_to_bv 64 2 -> getr regs 16 = Z_to_bv 64 3 ->
  (bv_unsigned m mod 4 = 0)%Z ->
  rdn BSEGS mem m 4 = Some [Z_to_bv 8 2; h1; h2; h3] -> bytes_le_to_Z [Z_to_bv 8 2; h1; h2; h3] = bv_unsigned hv ->
  store_ok BSEGS mem m 4 = true ->
  msteps BSEGS (mkst regs (0x4c328 : word) mem rom)
    (mkst (regupd (regupd regs 12 (v_lw hv)) 17 (Z_to_bv 64 0)) (0x4c348 : word) (wbytes mem m [Z_to_bv 8 3; h1; h2; h3]) rom).
Proof using.
  intros regs mem rom m hv h1 h2 h3 H13 H15 H14 H16 Hal Hrd Hv Hok.
  pose proof (cas_byte_run BSEGS regs (0x4c328 : word) (0x4c32c : word) (0x4c330 : word) (0x4c334 : word)
                (0x4c338 : word) (0x4c33c : word) (0x4c340 : word) (0x4c344 : word) (0x4c348 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ _ 12 13 17 16 15 14 _ _ [Z_to_bv 8 2; h1; h2; h3] hv 0%nat 3%Z
                F_4c328 eq_refl D_4c328 F_4c32c eq_refl D_4c32c F_4c330 eq_refl D_4c330 F_4c334 eq_refl D_4c334
                F_4c338 eq_refl D_4c338 F_4c33c eq_refl D_4c33c F_4c340 eq_refl D_4c340 F_4c344 eq_refl D_4c344) as R.
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
  Hypothesis Rhdr : rdn BSEGS mem (at_ p (-16)) 4 = Some [Z_to_bv 8 2; h1; h2; h3].
  Hypothesis Hhv : bytes_le_to_Z [Z_to_bv 8 2; h1; h2; h3] = bv_unsigned hv.
  Hypothesis Hokh : store_ok BSEGS mem (at_ p (-16)) 4 = true.
  Hypothesis Hokp : store_ok BSEGS mem p 8 = true.

  Lemma b3_run :
    exists r,
      msteps BSEGS (mkst regs (0x4c2cc : word) mem rom) (mkst r (0x4c4b4 : word) (fr_b3 mem p h1 h2 h3) rom)
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
    - ab_tk F_4c2cc D_4c2cc ltac:(condz).              (* [comment removed for export] *)
      av F_4c308 D_4c308 (at_ p (-16)) ltac:(apply v_andi_m4_aligned; exact Hm4).   (* [comment removed for export] *)
      av F_4c30c D_4c30c (Z_to_bv 64 (8 * (bv_unsigned p + -16))) ltac:(valz).     (* [comment removed for export] *)
      an F_4c310 D_4c310.                              (* [comment removed for export] *)
      an F_4c314 D_4c314.                              (* [comment removed for export] *)
      an F_4c318 D_4c318.                              (* [comment removed for export] *)
      an F_4c31c D_4c31c.                              (* [comment removed for export] *)
      rewrite (v_sllw_mult32 255) by (first [lia | unorm; exact M32]).
      an F_4c320 D_4c320.                              (* [comment removed for export] *)
      rewrite (v_sllw_mult32 2) by (first [lia | unorm; exact M32]).
      an F_4c324 D_4c324.                              (* [comment removed for export] *)
      rewrite (v_sllw_mult32 3) by (first [lia | unorm; exact M32]).
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_state_67264 _ mem rom (at_ p (-16)) hv h1 h2 h3);
          [gres; reflexivity | gres; reflexivity | gres; reflexivity | gres; reflexivity | exact Hm4 | exact Rhdr | exact Hhv | exact Hokh]. }
      an F_4c348 D_4c348.                              (* [comment removed for export] *)
      an F_4c34c D_4c34c.                              (* [comment removed for export] *)
      fsd F_4c350 D_4c350 p.                           (* [comment removed for export] *)
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := h1);
          [exact F_4c354 | reflexivity | exact D_4c354
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
            rewrite wc_rdn_wbytes_out3; [ | rd8_side ];
            replace (at_ p (-15)) with (at_ (at_ p (-16)) (Z.of_nat 1)) by (rewrite at_at; f_equal; lia);
            apply rdn1_wbytes_in; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite at_u; lia] ]
        | step_simpl]; vn.
      av F_4c358 D_4c358 (Z_to_bv 64 1) ltac:(destruct Hh1 as [E|E]; rewrite E; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4c35c D_4c35c ltac:(condz).              (* [comment removed for export] *)
      an F_4c360 D_4c360.                              (* [comment removed for export] *)
      an F_4c364 D_4c364.                              (* [comment removed for export] *)
      ab_tk F_4c368 D_4c368 ltac:(condz).              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b3 mem p h1 h2 h3). wd_refl.
    - post.
  Qed.
End B3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b4a (mem : word -> option byte) (S : word) : word -> option byte :=
  wbytes mem (at_ S (-2200)) (word_to_le_bytes 8 (Z_to_bv 64 0x4c4b8)).
Hint Unfold fr_b4a : asfr.

Section B4A.
  Variables (mem rom : word -> option byte) (S : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2192).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.

  Lemma b4a_run :
    exists r,
      msteps BSEGS (mkst regs (0x4c4b4 : word) mem rom) (mkst r (0x78e2c : word) (fr_b4a mem S) rom)
      /\ getr r 1 = Z_to_bv 64 0x78004 /\ getr r 2 = at_ S (-2208)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9
      /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk HS H2.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4c4b4 D_4c4b4.                              (* [comment removed for export] *)
      an F_77ff8 D_77ff8.                              (* [comment removed for export] *)
      fsd F_77ffc D_77ffc (at_ S (-2200)).             (* [comment removed for export] *)
      an F_78000 D_78000.                              (* [comment removed for export] *)
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
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 0x10ab58.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hn : (1 <= n <= 2 ^ 40)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis Rnhi : rdn BSEGS mem (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis Rnlo : rdn BSEGS mem (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))).
  Hypothesis Rf0 : rdn BSEGS mem (Z_to_bv 64 (T + 2824)) 8 = Some bf0.
  Hypothesis Lf0 : length bf0 = 8%nat.
  Hypothesis Rf1 : rdn BSEGS mem (Z_to_bv 64 (T + 2832)) 8 = Some bf1.
  Hypothesis Lf1 : length bf1 = 8%nat.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 (T + 2824)) 16 = true.
  Hypothesis Rra : rdn BSEGS mem (at_ S (-2200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4c4b8)).
  Hypothesis Rs0 : rdn BSEGS mem (at_ S (-2136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6ef14)).
  Hypothesis Rs1 : rdn BSEGS mem (at_ S (-2144)) 8 = Some (word_to_le_bytes 8 S).
  Hypothesis Rs2 : rdn BSEGS mem (at_ S (-2152)) 8 = Some (word_to_le_bytes 8 p).
  Hypothesis Rs3 : rdn BSEGS mem (at_ S (-2160)) 8 = Some (word_to_le_bytes 8 x18).
  Hypothesis Rs4 : rdn BSEGS mem (at_ S (-2168)) 8 = Some (word_to_le_bytes 8 x19).
  Hypothesis Rs5 : rdn BSEGS mem (at_ S (-2176)) 8 = Some (word_to_le_bytes 8 x20).
  Hypothesis Rs6 : rdn BSEGS mem (at_ S (-2184)) 8 = Some (word_to_le_bytes 8 x21).
  Hypothesis Rs7 : rdn BSEGS mem (at_ S (-2192)) 8 = Some (word_to_le_bytes 8 x22).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma n_split : (0 <= n / 2 ^ 32 <= 2 ^ 8 /\ 0 <= n mod 2 ^ 32 < 2 ^ 32 /\ n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n)%Z.
  Proof using Lf1 Lf0 Hn bf1 bf0 x22 rom. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). repeat split; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma b4b_run :
    exists r,
      msteps BSEGS (mkst regs (0x78004 : word) mem rom)
                   (mkst r (0x507e0 : word) (fr_b4b mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) rom)
      /\ getr r 1 = Z_to_bv 64 0x6ef14 /\ getr r 2 = at_ S (-2128) /\ getr r 8 = S /\ getr r 9 = p
      /\ getr r 10 = Z_to_bv 64 0x10ab58 /\ getr r 11 = at_ p (-16) /\ getr r 12 = p /\ getr r 13 = at_ S (-2128)
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
    - ab_ft F_78004 D_78004 ltac:(condz).              (* [comment removed for export] *)
      an F_78008 D_78008.                              (* [comment removed for export] *)
      an F_7800c D_7800c.                              (* [comment removed for export] *)
      cld8 F_78010 D_78010 (Z_to_bv 64 0x4c4b8) Rra.   (* [comment removed for export] *)
      an F_78014 D_78014.                              (* [comment removed for export] *)
      rt F_78018 D_78018.                              (* [comment removed for export] *)
      clhu F_4c4b8 D_4c4b8 (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh.  (* [comment removed for export] *)
      clwu F_4c4bc D_4c4bc (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl.  (* [comment removed for export] *)
      cld F_4c4c0 D_4c4c0 bf1 (Z_to_bv 64 (bytes_le_to_Z bf1)) Rf1 Vf1.   (* [comment removed for export] *)
      cld F_4c4c4 D_4c4c4 bf0 (Z_to_bv 64 (bytes_le_to_Z bf0)) Rf0 Vf0.   (* [comment removed for export] *)
      av F_4c4c8 D_4c4c8 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      an F_4c4cc D_4c4cc.                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia).
      an F_4c4d0 D_4c4d0.                              (* [comment removed for export] *)
      an F_4c4d4 D_4c4d4.                              (* [comment removed for export] *)
      fsd F_4c4d8 D_4c4d8 (Z_to_bv 64 (T + 2824)).     (* [comment removed for export] *)
      fsd F_4c4dc D_4c4dc (Z_to_bv 64 (T + 2832)).     (* [comment removed for export] *)
      an F_4c4e0 D_4c4e0.                              (* [comment removed for export] *)
      an F_4c4e4 D_4c4e4.                              (* [comment removed for export] *)
      an F_4c4e8 D_4c4e8.                              (* [comment removed for export] *)
      an F_4c4ec D_4c4ec.                              (* [comment removed for export] *)
      cld8 F_4c4f0 D_4c4f0 (Z_to_bv 64 0x6ef14) Rs0.   (* [comment removed for export] *)
      cld8 F_4c4f4 D_4c4f4 S Rs1.                      (* [comment removed for export] *)
      cld8 F_4c4f8 D_4c4f8 p Rs2.                      (* [comment removed for export] *)
      cld8 F_4c4fc D_4c4fc x18 Rs3.                    (* [comment removed for export] *)
      cld8 F_4c500 D_4c500 x19 Rs4.                    (* [comment removed for export] *)
      cld8 F_4c504 D_4c504 x20 Rs5.                    (* [comment removed for export] *)
      cld8 F_4c508 D_4c508 x21 Rs6.                    (* [comment removed for export] *)
      cld8 F_4c50c D_4c50c x22 Rs7.                    (* [comment removed for export] *)
      an F_4c510 D_4c510.                              (* [comment removed for export] *)
      an F_4c514 D_4c514.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_b4b mem T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)). wd_refl.
    - post.
  Qed.
End B4B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_b5a (mem : word -> option byte) (S p x18 x19 x20 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2136)) (word_to_le_bytes 8 (Z_to_bv 64 0x6ef14)))
    (at_ S (-2144)) (word_to_le_bytes 8 S))
    (at_ S (-2152)) (word_to_le_bytes 8 p))
    (at_ S (-2160)) (word_to_le_bytes 8 x18))
    (at_ S (-2168)) (word_to_le_bytes 8 x19))
    (at_ S (-2176)) (word_to_le_bytes 8 x20).
Hint Unfold fr_b5a : asfr.

Section B5A.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 : word).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = Z_to_bv 64 0x6ef14.
  Hypothesis H2 : getr regs 2 = at_ S (-2128).
  Hypothesis H8 : getr regs 8 = S.
  Hypothesis H9 : getr regs 9 = p.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H11 : getr regs 11 = at_ p (-16).
  Hypothesis H13 : getr regs 13 = at_ S (-2128).
  Hypothesis H18 : getr regs 18 = x18.
  Hypothesis H19 : getr regs 19 = x19.
  Hypothesis H20 : getr regs 20 = x20.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis Rst : rdn BSEGS mem (at_ p (-16)) 1 = Some [Z_to_bv 8 3].

  Lemma b5a_run :
    exists r,
      msteps BSEGS (mkst regs (0x507e0 : word) mem rom) (mkst r (0x78e2c : word) (fr_b5a mem S p x18 x19 x20) rom)
      /\ getr r 1 = Z_to_bv 64 0x50818 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = at_ p (-16) /\ getr r 9 = at_ S (-2128)
      /\ getr r 18 = Z_to_bv 64 0x10ab58
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rst Hstk Hp HS H20 H19 H18 H13 H11 H10 H9 H8 H2 H1.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    wd_eexists. split.
    - an F_507e0 D_507e0.                              (* [comment removed for export] *)
      fsd F_507e4 D_507e4 (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_507e8 D_507e8 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_507ec D_507ec (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_507f0 D_507f0 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_507f4 D_507f4 (at_ S (-2168)).             (* [comment removed for export] *)
      fsd F_507f8 D_507f8 (at_ S (-2176)).             (* [comment removed for export] *)
      an F_507fc D_507fc.                              (* [comment removed for export] *)
      clb F_50800 D_50800 (Z_to_bv 8 3) Rst.           (* [comment removed for export] *)
      an F_50804 D_50804.                              (* [comment removed for export] *)
      ab_ft F_50808 D_50808 ltac:(condz).              (* [comment removed for export] *)
      an F_5080c D_5080c.                              (* [comment removed for export] *)
      an F_50810 D_50810.                              (* [comment removed for export] *)
      an F_50814 D_50814.                              (* [comment removed for export] *)
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
  Hypothesis RT0 : rdn BSEGS mem (Z_to_bv 64 T) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 tctx)).
  Hypothesis Rtid : rdn BSEGS mem (Z_to_bv 64 (tctx + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis Rbuf : rdn BSEGS mem (at_ S (-2128)) 8 = Some (word_to_le_bytes 8 (at_ S (-2112))).
  Hypothesis Rsz : rdn BSEGS mem (at_ S (-2120)) 8 = Some bsz.
  Hypothesis Lsz : length bsz = 8%nat.

  Lemma b5b_run :
    exists r,
      msteps BSEGS (mkst regs (0x50818 : word) mem rom) (mkst r (0x8f4f0 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x50838 /\ getr r 2 = at_ S (-2176) /\ getr r 9 = at_ S (-2128)
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
    - ab_ft F_50818 D_50818 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_5081c D_5081c (Z_to_bv 64 tctx) RT0.      (* [comment removed for export] *)
      cld8 F_50820 D_50820 (at_ S (-2112)) Rbuf.       (* [comment removed for export] *)
      cld F_50824 D_50824 bsz (Z_to_bv 64 (bytes_le_to_Z bsz)) Rsz Vsz.   (* [comment removed for export] *)
      clw F_50828 D_50828 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) Rtid V0.   (* [comment removed for export] *)
      an F_5082c D_5082c.                              (* [comment removed for export] *)
      an F_50830 D_50830.                              (* [comment removed for export] *)
      an F_50834 D_50834.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End B5B.
End FPGen.
End BoAllocF2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF0i.BoAllocF0 BoAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
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
  let x18 := Z_to_bv 64 0x6eea4 in let x19 := Z_to_bv 64 1 in let x20 := at_ S (-2128) in let x21 := at_ S (-81) in
  let M4 := fr_b1 MU S p x18 x19 x20 x21 x22 in
  let M5 := fr_b2 M4 S p in
  let M6 := fr_b3 M5 p h1 h2 h3 in
  let M7 := fr_b4a M6 S in
  let M8 := wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x78004)) in
  let M9 := fr_b4b M8 T (at_ (Z_to_bv 64 (bytes_le_to_Z bf0)) 1) (v_add (Z_to_bv 64 n) (Z_to_bv 64 (bytes_le_to_Z bf1))) in
  let M10 := fr_b5a M9 S p x18 x19 x20 in
  wbytes M10 (at_ S (-2184)) (LE8 (Z_to_bv 64 0x50818)).
Hint Unfold fr_P1 fr_P2 : asfr.

(* [comment removed for export] *)
Lemma fr_P1_tag0 : forall (mem : word -> option byte) (S p ra0 s0 s1 s2 s3 s4 s5 : word) (MU : word -> option byte),
  (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z ->
  (forall x : word, MU x <> fr_P1 mem S p ra0 s0 s1 s2 s3 s4 s5 x -> ~ (U S - 2116 <= U x < U S - 2112)%Z) ->
  rdn BSEGS MU (at_ S (-2116)) 4 = Some (LE4 0).
Proof using.
  intros mem S p ra0 s0 s1 s2 s3 s4 s5 MU GS FOOT. pose proof (u64_range S) as HSr.
  assert (SL : rdn BSEGS (fr_P1 mem S p ra0 s0 s1 s2 s3 s4 s5) (at_ S (-2120)) 8 = Some (LE8 (Z_to_bv 64 0))).
  { (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1 in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. rd_hit8. }
  pose proof (MemsetLibF.RefMemcpyLib.rdn_skipn BSEGS _ 8 (at_ S (-2120)) _ 4 SL ltac:(lia)) as X.
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
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn BSEGS mem (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS mem (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn BSEGS mem (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_unw : rdn BSEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_unw_ok : store_ok BSEGS mem (at_ thr 3168) 1 = true.
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 P).
  Hypothesis C_P : rdn BSEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn BSEGS mem (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS mem (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_sw : rdn BSEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn BSEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn BSEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_hook : rdn BSEGS mem (Z_to_bv 64 0x19fc88) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_h1 : h1 = Z_to_bv 8 0x11 \/ h1 = Z_to_bv 8 0x91.
  Hypothesis C_hdr : rdn BSEGS mem (at_ p (-16)) 4 = Some [Z_to_bv 8 2; h1; h2; h3].
  Hypothesis C_hv : bytes_le_to_Z [Z_to_bv 8 2; h1; h2; h3] = U hv.
  Hypothesis C_hdr_ok : store_ok BSEGS mem (at_ p (-16)) 4 = true.
  Hypothesis C_p_ok : store_ok BSEGS mem p 8 = true.
  Hypothesis C_nhi : rdn BSEGS mem (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS mem (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_f0 : rdn BSEGS mem (Z_to_bv 64 (T + 2824)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS mem (Z_to_bv 64 (T + 2832)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_stat_ok : store_ok BSEGS mem (Z_to_bv 64 (T + 2824)) 16 = true.
  Hypothesis C_T0 : rdn BSEGS mem (Z_to_bv 64 T) 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn BSEGS mem (Z_to_bv 64 (tctx + 8)) 4 = Some (LE4 0).
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

  Theorem run_from_6ee44 :
    exists r MU (sz : Z) (bsz : list byte),
      msteps BSEGS (mkst r2 (0x6ee44 : word) (fr_ia M1 S p ra0 (getr R 19)) rom) (mkst r (0x8f4f0 : word) (fr_P2 MU S p (getr R 22) T n h1 h2 h3 bf0 bf1) rom)
      /\ getr r 1 = Z_to_bv 64 0x50838 /\ getr r 2 = at_ S (-2176) /\ getr r 8 = at_ p (-16) /\ getr r 9 = at_ S (-2128)
      /\ getr r 10 = at_ S (-2112) /\ getr r 11 = Z_to_bv 64 (bytes_le_to_Z bsz) /\ getr r 18 = Z_to_bv 64 0x10ab58
      /\ getr r 19 = Z_to_bv 64 0 /\ getr r 20 = thr /\ getr r 21 = at_ S (-81) /\ getr r 22 = getr R 22
      /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 23 = getr R 23 /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27
      /\ (1 <= sz <= 30)%Z /\ (sz <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MU x <> M3 x ->
            (U S - 2272 <= U x < U S - 2128)%Z \/ (U S - 2120 <= U x < U S - 1872)%Z \/ (U S - 72 <= U x < U S - 64)%Z \/ U x = (T + 3168)%Z)
      /\ mem_grows M3 MU
      /\ rdn BSEGS MU (at_ S (-2120)) 4 = Some (LE4 sz) /\ rdn BSEGS MU (at_ S (-2112)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4))
      /\ rdn BSEGS MU (at_ thr 3168) 1 = Some [Z_to_bv 8 0]
      /\ rdn BSEGS MU (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn BSEGS MU (at_ S (-2116)) 4 = Some (LE4 0).                                  (* [comment removed for export] *)
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
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub BSEGS mem (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    set (M3' := fr_p1 M1 S p ra0 (getr R 19)) in RUN3.
    assert (EM3 : M3' = M3) by reflexivity. rewrite EM3 in RUN3. clear EM3 M3'.
    pose proof fr_P1_outside as OUT3. pose proof fr_P1_grows as GR3.
    assert (SOK3 : store_ok BSEGS M3 (at_ S (-2304)) 2304 = true) by (eapply store_ok_mono; [exact GR3 | exact Hstk]).
    Ltac x3 OUT H := eapply rd_same; [intros x Hx; apply OUT; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                    | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H].
    (* [comment removed for export] *)
    assert (UH : uiH BSEGS both_ui_tab M3 (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi both_ui_tab] in G in change_no_check G' end).
      - x3 OUT3 C_inited.
      - x3 OUT3 C_unw.
      - eapply store_ok_mono; [exact GR3 | exact C_unw_ok].
      - x3 OUT3 C_pg.
      - x3 OUT3 C_P.
      - rewrite !at_at. eapply (store_ok_sub BSEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite !at_at. eapply (store_ok_sub BSEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - hlia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. hlia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. hlia. }
    assert (GH : gctH BSEGS (ut_gct both_ui_tab) M3 (at_ (at_ S (-2128)) (-80)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_gct both_ui_tab gt_tsd both_gct_tab] in G in change_no_check G' end).
      - x3 OUT3 C_kif.
      - x3 OUT3 C_key.
      - x3 OUT3 C_tsdp.
      - x3 OUT3 C_tctx.
      - x3 OUT3 C_thr.
      - unorm. lia.
      - rewrite !at_at. eapply (store_ok_sub BSEGS M3 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | exact SOK3 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (SH : stkH BSEGS M3 thr top bot).
    { split.
      - x3 OUT3 C_sw.
      - x3 OUT3 C_top.
      - x3 OUT3 C_bot.
      - exact Gbot.
      - unorm. lia. }
    (* [comment removed for export] *)
    assert (B4' : getr r3 4 = tp) by (rewrite B4, A4; exact HR4).
    assert (RET_U : ret_ok (Z_to_bv 64 0x6ef00)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (Rr : rdn BSEGS M3 (at_ S (-8)) 8 = Some (LE8 ra0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT. repeat (wd_rdstep rd8_side). }
    assert (Rw : rdn BSEGS M3 (at_ S (-16)) 8 = Some (LE8 (getr R 8))).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1, fr_ia, fr_icpt in G in change_no_check G' end). clear - HSr Hpr GS1 GS2 Gp1 Gp2 GT1 GT2 GpT. repeat (wd_rdstep rd8_side). }
    assert (FPC3 : fpc M3 (bytes_le_to_Z (LE8 (getr R 8))) (U S) D).
    { rewrite bytes_le_to_Z_8. apply (fpc_kept_gen mem _ _ _ Hfpc M3).
      destruct (fpc_shape _ _ _ _ Hfpc) as [ST | FR]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (getr R 8)). rewrite <- (u_Z2bv a) in Ha by (unfold PTRHI in Ha; lia).
      apply OUT3. lia. }
    destruct (both_ui_run_s r3 M3 rom (Z_to_bv 64 0x6ef00) (at_ S (-2128)) tp (at_ S (-2128)) (Z_to_bv 64 0x6eea4) S (Z_to_bv 64 1)
                thr top bot tsdp ctxw P RET_U B1 B2 B4' B10 B11 B12 B13 B14 B15 ltac:(wd_ulia) UH GH SH Gtop
                D (LE8 ra0) (LE8 (getr R 8)) Rr (length_N_to_le_bytes _ _) Rw (length_N_to_le_bytes _ _) FPC3)
      as (rU & MU & sz & RUNU & AGU & SZ1 & SZ2 & RDsz & RDpc & RDunw & FOOTUs & GRU).
    (* [comment removed for export] *)
    assert (TAG0 : rdn BSEGS MU (at_ S (-2116)) 4 = Some (LE4 0)).
    { apply (fr_P1_tag0 mem S p ra0 (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) MU GS).
      intros x Hx. pose proof (FOOTUs x Hx) as F. revert F. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. intros F. lia. }
    assert (FOOTU : forall x : word, MU x <> M3 x ->
              (U (at_ S (-2128)) - 144 <= U x < U (at_ S (-2128)))%Z \/ (U (at_ S (-2128)) + 8 <= U x < U (at_ S (-2128)) + 256)%Z
              \/ (U (at_ S (-2128)) + 2056 <= U x < U (at_ S (-2128)) + 2064)%Z \/ U x = (U thr + 3168)%Z).
    { intros x Hx. destruct (FOOTUs x Hx) as [F|[F|[F|[F|F]]]]; [left | right; left | right; left | right; right; left | right; right; right]; try lia; exact F. }
    clear FOOTUs.
    cbn [ut_rb both_ui_tab] in RUNU. rewrite at0_lit in RUNU by lia.
    replace (488388 : word) with (Z_to_bv 64 488388 : word) in RUN3 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (MUq : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z) \/ (U S <= U x)%Z -> MU x = mem x).
    { intros x Hx. destruct (decide (MU x = M3 x)) as [E|NE].
      - rewrite E. apply OUT3. lia.
      - exfalso. pose proof (FOOTU x NE) as F. revert F. (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end). unorm. intros F. lia. }
    assert (GRU' : mem_grows mem MU) by (eapply mem_grows_trans; [exact GR3 | exact GRU]).
    assert (SOKU : store_ok BSEGS MU (at_ S (-2304)) 2304 = true) by (eapply store_ok_mono; [exact GRU | exact SOK3]).
    Ltac via AG r H := let TT := fresh in pose proof (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold ui_clob, gct_clob in G in change_no_check G' end); notin)) as TT; rewrite H in TT; exact TT.
    (* [comment removed for export] *)
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold ui_clob, gct_clob in G in change_no_check G' end); notin)); rch.
    assert (U2 : getr rU 2 = at_ S (-2128)) by via AGU (2:reg) B2.
    assert (U8 : getr rU 8 = S) by via AGU (8:reg) B8.
    assert (U9 : getr rU 9 = p) by via AGU (9:reg) B9.
    assert (U18 : getr rU 18 = Z_to_bv 64 0x6eea4) by via AGU (18:reg) B18.
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
    destruct (b1_run MU rom S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) rU
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
    assert (GR4 : mem_grows mem (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22))).
    { eapply mem_grows_trans; [exact GRU'|]. (lazymatch goal with |- ?G => let G' := eval unfold fr_b1 in G in change_no_check G' end); grows_tac. }
    assert (Q4 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z) \/ (U S <= U x)%Z ->
                 fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22) x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b1 in G in change_no_check G' end). quiet_tac MUq. }
    remember (fr_b1 MU S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)) as M4 eqn:EM4 in RUN4, GR4, Q4.
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
    { pose proof (rdn_skip BSEGS mem (at_ p (-16)) 4 [Z_to_bv 8 2; h1; h2; h3] 2 C_hdr ltac:(lia) ltac:(rewrite at_u; lia)) as X.
      rewrite at_at in X. cbn [skipn Nat.sub] in X.
      replace (-16 + Z.of_nat 2)%Z with (-14)%Z in X by reflexivity. rewrite C_nhi in X. congruence. }
    (* [comment removed for export] *)
    assert (ST6 : rdn BSEGS (fr_b3 M5 p h1 h2 h3) (at_ p (-16)) 1 = Some [Z_to_bv 8 3]).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b3 in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      replace (at_ p (-16)) with (at_ (at_ p (-16)) (Z.of_nat 0)) at 2 by (rewrite at_at; f_equal; lia).
      apply rdn1_wbytes_in; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite at_u; lia]. }
    assert (NH6 : rdn BSEGS (fr_b3 M5 p h1 h2 h3) (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b3 in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      replace (at_ p (-14)) with (at_ (at_ p (-16)) (Z.of_nat 2)) by (rewrite at_at; f_equal; lia).
      rewrite (rdn_wbytes_sub BSEGS M5 (at_ p (-16)) _ 2 2); [(lazymatch goal with |- ?G => let G' := eval cbn [firstn skipn] in G in change_no_check G' end); rewrite Ehh; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite at_u; lia]. }
    remember (fr_b3 M5 p h1 h2 h3) as M6 eqn:EM6 in RUN6, GR6, Q6, ST6, NH6.
    (* [comment removed for export] *)
    assert (E2' : getr r6 2 = at_ S (-2192)) by (rewrite E2; exact D2).
    destruct (b4a_run M6 rom S r6 E2' ltac:(hlia) ltac:(eapply store_ok_mono; [exact GR6 | exact Hstk]))
      as (r7 & RUN7 & F1 & F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    assert (GR7 : mem_grows mem (fr_b4a M6 S)) by (eapply mem_grows_trans; [exact GR6|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end); grows_tac).
    assert (Q7 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z) \/ (U S <= U x)%Z -> fr_b4a M6 S x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end);
        rewrite ?at_u by lia; try lia. apply Q6. lia. }
    assert (RA7 : rdn BSEGS (fr_b4a M6 S) (at_ S (-2200)) 8 = Some (LE8 (Z_to_bv 64 0x4c4b8))) by ((lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end); rd_hit8).
    remember (fr_b4a M6 S) as M7 eqn:EM7 in RUN7, GR7, Q7, RA7.
    (* [comment removed for export] *)
    assert (RET_G1 : ret_ok (Z_to_bv 64 0x78004)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (F4' : getr r7 4 = tp) by (rewrite F4, E4, D4, C4; exact U4).
    assert (GH7 : gctH BSEGS both_gct_tab M7 (at_ S (-2208)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xqh GTS Q7 C_kif. - xqh GTS Q7 C_key. - xqh GTS Q7 C_tsdp. - xqh GTS Q7 C_tctx. - xqh GTS Q7 C_thr.
      - unorm. lia.
      - rewrite at_at. eapply (store_ok_sub BSEGS M7 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR7 | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (gct_run BSEGS both_gct_tab both_gct_tab_ok M7 rom r7 (Z_to_bv 64 0x78004) (at_ S (-2208)) tp tsdp ctxw thr GH7 RET_G1 F1 F2 F4')
      as (r8 & RUN8 & X10 & X11 & AGX).
    cbn [gt_rb both_gct_tab] in RUN8. rewrite at0_lit in RUN8 by lia. rewrite at_at in RUN8. cbn [Z.add Z.opp Pos.add] in RUN8.
    replace (495148 : word) with (Z_to_bv 64 495148 : word) in RUN7 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (GR8 : mem_grows mem (wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x78004)))) by (eapply mem_grows_trans; [exact GR7|]; grows_tac).
    assert (Q8 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z) \/ (U S <= U x)%Z ->
                 wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x78004)) x = mem x).
    { intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end);
        rewrite ?at_u by lia; try lia. apply Q7. lia. }
    (* [comment removed for export] *)
    assert (Y2 : getr r8 2 = at_ S (-2208)) by viac AGX (2:reg).
    assert (Y8 : getr r8 8 = at_ S (-2128)) by viac AGX (8:reg).
    assert (Y9 : getr r8 9 = p) by viac AGX (9:reg).
    assert (Y18 : getr r8 18 = at_ p (-16)) by viac AGX (18:reg).
    assert (Y19 : getr r8 19 = Z_to_bv 64 0x10ab58) by viac AGX (19:reg).
    assert (Y10 : getr r8 10 = thr) by exact X10.
    assert (Y4 : getr r8 4 = tp) by viac AGX (4:reg).
    assert (Y3 : getr r8 3 = getr R 3) by viac AGX (3:reg).
    assert (Y23 : getr r8 23 = getr R 23) by viac AGX (23:reg).
    assert (Y24 : getr r8 24 = getr R 24) by viac AGX (24:reg).
    assert (Y25 : getr r8 25 = getr R 25) by viac AGX (25:reg).
    assert (Y26 : getr r8 26 = getr R 26) by viac AGX (26:reg).
    assert (Y27 : getr r8 27 = getr R 27) by viac AGX (27:reg).
    (* [comment removed for export] *)
    destruct (b4b_run (wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x78004))) rom S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) (getr R 22)
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
    remember (wbytes M7 (at_ S (-2216)) (LE8 (Z_to_bv 64 0x78004))) as M8 eqn:EM8 in RUN8, RUN9, GR8, Q8.
    assert (GR9 : mem_grows mem (fr_b4b M8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1))) by (eapply mem_grows_trans; [exact GR8|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_b4b in G in change_no_check G' end); grows_tac).
    assert (Q9 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z
                                    /\ (U x < T + 2824 \/ T + 2840 <= U x)%Z) \/ (U S <= U x)%Z ->
                 fr_b4b M8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1) x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b4b in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try lia. apply Q8. lia. }
    assert (ST9 : rdn BSEGS (fr_b4b M8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) (at_ p (-16)) 1 = Some [Z_to_bv 8 3]).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b4b in G in change_no_check G' end). rewrite !rdn_wbytes_out; [ | rd8_side .. ]. rewrite EM8. rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      rewrite EM7. (lazymatch goal with |- ?G => let G' := eval unfold fr_b4a in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. exact ST6. }
    remember (fr_b4b M8 T (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) as M9 eqn:EM9 in RUN9, GR9, Q9, ST9.
    (* [comment removed for export] *)
    destruct (b5a_run M9 rom S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) r9 G1 G2 G8 G9 G10 G11 G13 G18 G19 G20 ltac:(hlia) ltac:(hlia)
                ltac:(eapply store_ok_mono; [exact GR9 | exact Hstk]) ST9)
      as (r10 & RUN10 & I1 & I2 & I8 & I9 & I18 & I3 & I4 & I21 & I22 & I23 & I24 & I25 & I26 & I27).
    assert (GR10 : mem_grows mem (fr_b5a M9 S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)))) by (eapply mem_grows_trans; [exact GR9|]; (lazymatch goal with |- ?G => let G' := eval unfold fr_b5a in G in change_no_check G' end); grows_tac).
    assert (Q10 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z
                                    /\ (U x < T + 2824 \/ T + 2840 <= U x)%Z) \/ (U S <= U x)%Z ->
                 fr_b5a M9 S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) x = mem x).
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_b5a in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. apply Q9. lia. }
    remember (fr_b5a M9 S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128))) as M10 eqn:EM10 in RUN10, GR10, Q10.
    (* [comment removed for export] *)
    assert (RET_G2 : ret_ok (Z_to_bv 64 0x50818)) by (apply ret_ok_lit; [lia | reflexivity]).
    assert (I4' : getr r10 4 = tp) by rch.
    assert (GH10 : gctH BSEGS both_gct_tab M10 (at_ S (-2176)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xqh GTS Q10 C_kif. - xqh GTS Q10 C_key. - xqh GTS Q10 C_tsdp. - xqh GTS Q10 C_tctx. - xqh GTS Q10 C_thr.
      - unorm. lia.
      - rewrite at_at. eapply (store_ok_sub BSEGS M10 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR10 | exact Hstk] | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (gct_run BSEGS both_gct_tab both_gct_tab_ok M10 rom r10 (Z_to_bv 64 0x50818) (at_ S (-2176)) tp tsdp ctxw thr GH10 RET_G2 I1 I2 I4')
      as (r11 & RUN11 & W10 & W11 & AGW).
    cbn [gt_rb both_gct_tab] in RUN11. rewrite at0_lit in RUN11 by lia. rewrite at_at in RUN11. cbn [Z.add Z.opp Pos.add] in RUN11.
    replace (495148 : word) with (Z_to_bv 64 495148 : word) in RUN10 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (GR11 : mem_grows mem (wbytes M10 (at_ S (-2184)) (LE8 (Z_to_bv 64 0x50818)))) by (eapply mem_grows_trans; [exact GR10|]; grows_tac).
    assert (Q11 : forall x : word, ((U x < U S - 2304)%Z /\ U x <> (T + 3168)%Z /\ (U x < U p - 16 \/ (U p - 12 <= U x < U p) \/ U p + 8 <= U x)%Z
                                    /\ (U x < T + 2824 \/ T + 2840 <= U x)%Z) \/ (U S <= U x)%Z ->
                 wbytes M10 (at_ S (-2184)) (LE8 (Z_to_bv 64 0x50818)) x = mem x).
    { intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. apply Q10. lia. }
    assert (V2 : getr r11 2 = at_ S (-2176)) by viac AGW (2:reg).
    assert (V9 : getr r11 9 = at_ S (-2128)) by viac AGW (9:reg).
    assert (V10 : getr r11 10 = thr) by exact W10.
    (* [comment removed for export] *)
    destruct (rdn_defined_ex BSEGS MU (at_ S (-2120)) 8) as [bsz [Rsz Lsz]].
    { intros i Hi. rewrite at_u in Hi by lia. apply GRU.
      (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold fr_P1, fr_p1 in G in change_no_check G' end). pose proof (u64_range S).
      rewrite (wbytes_outside); [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, !at_u by lia; wd_ulia_c ].
      rewrite wbytes_inside; [ discriminate | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, !at_u by lia; wd_ulia_c ]. }
    { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    destruct (b5b_run (wbytes M10 (at_ S (-2184)) (LE8 (Z_to_bv 64 0x50818))) rom S T tctx bsz r11 V2 V9 V10 ltac:(hlia) ltac:(hlia) ltac:(hlia))
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
    replace (Z_to_bv 64 0x6ef00 : word) with (0x6ef00 : word) in RUNU by (apply bv_eq; reflexivity).
    replace (0x78004 : word) with (Z_to_bv 64 0x78004 : word) in RUN9 by (apply bv_eq; reflexivity).
    replace (0x50818 : word) with (Z_to_bv 64 0x50818 : word) in RUN12 by (apply bv_eq; reflexivity).
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

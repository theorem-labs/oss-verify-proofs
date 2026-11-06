(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

Lemma v_or_0_l : forall x : word, v_or (Z_to_bv 64 0) x = x.
Proof using. intros x. (lazymatch goal with |- ?G => let G' := eval unfold v_or in G in change_no_check G' end). rewrite (u_Z2bv 0) by lia. rewrite Z.lor_0_l. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_c1 (mem : word -> option byte) (S p x18 x19 x20 x21 x22 : word) (id T : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    p (word_to_le_bytes 8 (Z_to_bv 64 id)))
    (at_ S (-2136)) (word_to_le_bytes 8 (Z_to_bv 64 0x6ef14)))
    (at_ S (-2144)) (word_to_le_bytes 8 S))
    (at_ S (-2152)) (word_to_le_bytes 8 p))
    (at_ S (-2160)) (word_to_le_bytes 8 x18))
    (at_ S (-2168)) (word_to_le_bytes 8 x19))
    (at_ S (-2176)) (word_to_le_bytes 8 x20))
    (at_ S (-2184)) (word_to_le_bytes 8 x21))
    (at_ S (-2192)) (word_to_le_bytes 8 x22))
    (at_ S (-2208)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 208)))
    (at_ S (-2200)) (word_to_le_bytes 8 (at_ S (-2128))).
Hint Unfold fr_c1 : asfr.

Section C1.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 : word) (T n id fl n8 : Z).
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
  Hypothesis Hn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Hid : (0 <= id < 2 ^ 32)%Z.
  Hypothesis Hfl : (0 <= fl /\ fl + 4096 <= AIMGHI)%Z.
  Hypothesis Hn8 : AsRtRegion.down8 (n + 7) = n8.
  Hypothesis Hn8r : (n <= n8 <= n + 7)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis Hokp : store_ok BSEGS mem p 8 = true.
  (* [comment removed for export] *)
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
  Hypothesis Rgfl : rdn BSEGS mem (Z_to_bv 64 0x105f10) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 fl)).
  Hypothesis Rmff : rdn BSEGS mem (Z_to_bv 64 (fl + 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma n_split3 : (0 <= n / 2 ^ 32 < 2 ^ 8 /\ 0 <= n mod 2 ^ 32 < 2 ^ 32 /\ n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n
                    /\ id * 2 ^ 32 / 2 ^ 32 = id)%Z.
  Proof using Hid Hn x22 rom. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). repeat split; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma c1_run :
    exists r,
      msteps BSEGS (mkst regs (0x50838 : word) mem rom) (mkst r (0x70080 : word) (fr_c1 mem S p x18 x19 x20 x21 x22 id T) rom)
      /\ getr r 1 = Z_to_bv 64 0x50ae4 /\ getr r 2 = at_ S (-2208)
      /\ getr r 10 = p /\ getr r 11 = Z_to_bv 64 n8 /\ getr r 12 = Z_to_bv 64 253
      /\ getr r 8 = Z_to_bv 64 (0x10ab58 + 728) /\ getr r 9 = at_ (Z_to_bv 64 T) 80 /\ getr r 18 = Z_to_bv 64 n
      /\ getr r 19 = at_ S (-2128) /\ getr r 20 = at_ (Z_to_bv 64 T) 208 /\ getr r 21 = at_ p (-16) /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rmff Rgfl Rmsz Rmcs Rnlo Rnhi Rq5 Rq4 Rq3 Rq2 Rq1 Rq0 Hokp Hstk Hn8 Hfl Hid Hn HT Hp HS H22 H21 H20 H19 H18 H10 H9 H8 H2 fl.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    destruct n_split3 as (Nh & Nl & Nsum & Idd).
    assert (Vh : bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n / 2 ^ 32))).
    { rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2))%Z with (2 ^ 16)%Z. unorm. apply Z.mod_small. lia. }
    assert (Vl : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) = bv_unsigned (Z_to_bv 64 (n mod 2 ^ 32))) by (apply bytes4_small; lia).
    assert (V0 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 0)) = bv_unsigned (Z_to_bv 64 0)) by (apply bytes4_small; lia).
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
      ab_tk F_50998 D_50998 ltac:(condz).              (* [comment removed for export] *)
      an F_50a5c D_50a5c.                              (* [comment removed for export] *)
      an F_50a60 D_50a60.                              (* [comment removed for export] *)
      an F_50a64 D_50a64.                              (* [comment removed for export] *)
      an F_50a68 D_50a68.                              (* [comment removed for export] *)
      cld8 F_50a6c D_50a6c (Z_to_bv 64 fl) Rgfl.       (* [comment removed for export] *)
      clw F_50a70 D_50a70 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) Rmff V0.   (* [comment removed for export] *)
      ab_tk F_50a74 D_50a74 ltac:(condzs).             (* [comment removed for export] *)
      clhu F_50abc D_50abc (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh.  (* [comment removed for export] *)
      clwu F_50ac0 D_50ac0 (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl.  (* [comment removed for export] *)
      an F_50ac4 D_50ac4.                              (* [comment removed for export] *)
      av F_50ac8 D_50ac8 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      an F_50acc D_50acc.                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia).
      an F_50ad0 D_50ad0.                              (* [comment removed for export] *)
      av F_50ad4 D_50ad4 (Z_to_bv 64 n8) ltac:(rewrite AsRtIcpyS.v_andi_m8; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite Hn8; reflexivity).  (* [comment removed for export] *)
      an F_50ad8 D_50ad8.                              (* [comment removed for export] *)
      an F_50adc D_50adc.                              (* [comment removed for export] *)
      an F_50ae0 D_50ae0.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_c1 mem S p x18 x19 x20 x21 x22 id T). wd_refl.
    - post. all: apply bv_eq; reflexivity.
  Qed.
End C1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_c2 (mem : word -> option byte) (S p : word) (T n last cnt bsz qb : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (word_to_le_bytes 8 (Z_to_bv 64 0x50afc)))
    (at_ S (-2224)) (word_to_le_bytes 8 (Z_to_bv 64 (0x10ab58 + 728))))
    (at_ S (-2232)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 80)))
    (at_ S (-2240)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (at_ S (-2248)) (word_to_le_bytes 8 (at_ S (-2128))))
    (at_ S (-2256)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 208)))
    (at_ S (-2264)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 (last + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (bsz + n))))
    (Z_to_bv 64 (last + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (cnt + 1))))
    (Z_to_bv 64 (last + 24 + 8 * cnt)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 (T + 104)) (word_to_le_bytes 8 (Z_to_bv 64 (qb + n))).
Hint Unfold fr_c2 : asfr.

Section C2.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 ra0 s0v s1v s2v s3v s4v s5v : word).
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
  Hypothesis Hqb : (0 <= qb /\ qb + n <= 2 ^ 20)%Z.
  (* [comment removed for export] *)
  Hypothesis HlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 (T + 80)) 32 = true.
  Hypothesis Hokb : store_ok BSEGS mem (Z_to_bv 64 last) (Z.to_nat 8192) = true.
  (* [comment removed for export] *)
  Hypothesis Rlen : rdn BSEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 len)).
  Hypothesis Rlast : rdn BSEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 last)).
  Hypothesis Rqb : rdn BSEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb)).
  Hypothesis Rbsz : rdn BSEGS mem (Z_to_bv 64 (last + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 bsz)).
  Hypothesis Rcnt : rdn BSEGS mem (Z_to_bv 64 (last + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 cnt)).
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

End C2.
End FPGen.

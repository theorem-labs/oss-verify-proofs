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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.

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
    (at_ S (-2136)) (word_to_le_bytes 8 (Z_to_bv 64 0x6e4a4)))
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
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 0x103f18.
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
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis Hokp : store_ok ASEGS mem p 8 = true.
  (* [comment removed for export] *)
  Hypothesis Rq0 : rdn ASEGS mem (at_ S (-2136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e4a4)).
  Hypothesis Rq1 : rdn ASEGS mem (at_ S (-2144)) 8 = Some (word_to_le_bytes 8 S).
  Hypothesis Rq2 : rdn ASEGS mem (at_ S (-2152)) 8 = Some (word_to_le_bytes 8 p).
  Hypothesis Rq3 : rdn ASEGS mem (at_ S (-2160)) 8 = Some (word_to_le_bytes 8 x18).
  Hypothesis Rq4 : rdn ASEGS mem (at_ S (-2168)) 8 = Some (word_to_le_bytes 8 x19).
  Hypothesis Rq5 : rdn ASEGS mem (at_ S (-2176)) 8 = Some (word_to_le_bytes 8 x20).
  Hypothesis Rnhi : rdn ASEGS mem (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis Rnlo : rdn ASEGS mem (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))).
  Hypothesis Rmcs : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 808)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis Rmsz : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 792)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis Rgfl : rdn ASEGS mem (Z_to_bv 64 0xff268) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 fl)).
  Hypothesis Rmff : rdn ASEGS mem (Z_to_bv 64 (fl + 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma n_split3 : (0 <= n / 2 ^ 32 < 2 ^ 8 /\ 0 <= n mod 2 ^ 32 < 2 ^ 32 /\ n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n
                    /\ id * 2 ^ 32 / 2 ^ 32 = id)%Z.
  Proof using Hid Hn x22 rom. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). repeat split; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma c1_run :
    exists r,
      msteps ASEGS (mkst regs (0x4fdc8 : word) mem rom) (mkst r (0x6f610 : word) (fr_c1 mem S p x18 x19 x20 x21 x22 id T) rom)
      /\ getr r 1 = Z_to_bv 64 0x50074 /\ getr r 2 = at_ S (-2208)
      /\ getr r 10 = p /\ getr r 11 = Z_to_bv 64 n8 /\ getr r 12 = Z_to_bv 64 253
      /\ getr r 8 = Z_to_bv 64 (0x103f18 + 728) /\ getr r 9 = at_ (Z_to_bv 64 T) 80 /\ getr r 18 = Z_to_bv 64 n
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
    - an F_4fdc0 D_4fdc0.                              (* [comment removed for export] *)
      av F_4fdc4 D_4fdc4 (Z_to_bv 64 (id * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      av F_4fdc8 D_4fdc8 (Z_to_bv 64 id) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite Idd; reflexivity).  (* [comment removed for export] *)
      an F_4fdcc D_4fdcc. rewrite v_or_0_l.            (* [comment removed for export] *)
      fsd F_4fdd0 D_4fdd0 p.                           (* [comment removed for export] *)
      an F_4fdd4 D_4fdd4.                              (* [comment removed for export] *)
      clhu F_4fdd8 D_4fdd8 (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh.  (* [comment removed for export] *)
      clwu F_4fddc D_4fddc (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl.  (* [comment removed for export] *)
      an F_4fde0 D_4fde0.                              (* [comment removed for export] *)
      an F_4fde4 D_4fde4.                              (* [comment removed for export] *)
      av F_4fde8 D_4fde8 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      an F_4fdec D_4fdec.                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia).
      an F_4fdf0 D_4fdf0.                              (* [comment removed for export] *)
      an F_4fdf4 D_4fdf4.                              (* [comment removed for export] *)
      cld8 F_4fdf8 D_4fdf8 (Z_to_bv 64 0x6e4a4) Rq0.   (* [comment removed for export] *)
      cld8 F_4fdfc D_4fdfc S Rq1.                      (* [comment removed for export] *)
      cld8 F_4fe00 D_4fe00 p Rq2.                      (* [comment removed for export] *)
      cld8 F_4fe04 D_4fe04 x18 Rq3.                    (* [comment removed for export] *)
      cld8 F_4fe08 D_4fe08 x19 Rq4.                    (* [comment removed for export] *)
      cld8 F_4fe0c D_4fe0c x20 Rq5.                    (* [comment removed for export] *)
      an F_4fe10 D_4fe10.                              (* [comment removed for export] *)
      an F_4fe14 D_4fe14.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      an F_4fee0 D_4fee0.                              (* [comment removed for export] *)
      fsd F_4fee4 D_4fee4 (at_ S (-2136)).             (* [comment removed for export] *)
      fsd F_4fee8 D_4fee8 (at_ S (-2144)).             (* [comment removed for export] *)
      fsd F_4feec D_4feec (at_ S (-2152)).             (* [comment removed for export] *)
      fsd F_4fef0 D_4fef0 (at_ S (-2160)).             (* [comment removed for export] *)
      fsd F_4fef4 D_4fef4 (at_ S (-2168)).             (* [comment removed for export] *)
      fsd F_4fef8 D_4fef8 (at_ S (-2176)).             (* [comment removed for export] *)
      fsd F_4fefc D_4fefc (at_ S (-2184)).             (* [comment removed for export] *)
      fsd F_4ff00 D_4ff00 (at_ S (-2192)).             (* [comment removed for export] *)
      an F_4ff04 D_4ff04.                              (* [comment removed for export] *)
      fsd F_4ff08 D_4ff08 (at_ S (-2208)).             (* [comment removed for export] *)
      fsd F_4ff0c D_4ff0c (at_ S (-2200)).             (* [comment removed for export] *)
      cld8 F_4ff10 D_4ff10 (Z_to_bv 64 (2 ^ 20)) Rmcs.  (* [comment removed for export] *)
      an F_4ff14 D_4ff14.                              (* [comment removed for export] *)
      ab_ft F_4ff18 D_4ff18 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ff1c D_4ff1c (Z_to_bv 64 (2 ^ 28)) Rmsz.  (* [comment removed for export] *)
      ab_tk F_4ff20 D_4ff20 ltac:(condz).              (* [comment removed for export] *)
      an F_4ffe4 D_4ffe4.                              (* [comment removed for export] *)
      an F_4ffe8 D_4ffe8.                              (* [comment removed for export] *)
      an F_4ffec D_4ffec.                              (* [comment removed for export] *)
      an F_4fff0 D_4fff0.                              (* [comment removed for export] *)
      cld8 F_4fff4 D_4fff4 (Z_to_bv 64 fl) Rgfl.       (* [comment removed for export] *)
      clw F_4fff8 D_4fff8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) Rmff V0.   (* [comment removed for export] *)
      ab_tk F_4fffc D_4fffc ltac:(condzs).             (* [comment removed for export] *)
      clhu F_50044 D_50044 (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))) (Z_to_bv 64 (n / 2 ^ 32)) Rnhi Vh.  (* [comment removed for export] *)
      clwu F_50048 D_50048 (word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32))) (Z_to_bv 64 (n mod 2 ^ 32)) Rnlo Vl.  (* [comment removed for export] *)
      an F_5004c D_5004c.                              (* [comment removed for export] *)
      av F_50050 D_50050 (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      an F_50054 D_50054.                              (* [comment removed for export] *)
      replace (v_or (Z_to_bv 64 (n / 2 ^ 32 * 2 ^ 32)) (Z_to_bv 64 (n mod 2 ^ 32))) with (Z_to_bv 64 n)
        by (rewrite (v_or_shl (Z_to_bv 64 (n mod 2 ^ 32)) (n / 2 ^ 32) 32) by (wd_ulia); f_equal; wd_ulia).
      an F_50058 D_50058.                              (* [comment removed for export] *)
      av F_5005c D_5005c (Z_to_bv 64 n8) ltac:(rewrite AsRtIcpyS.v_andi_m8; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite Hn8; reflexivity).  (* [comment removed for export] *)
      an F_50060 D_50060.                              (* [comment removed for export] *)
      an F_50064 D_50064.                              (* [comment removed for export] *)
      an F_50068 D_50068.                              (* [comment removed for export] *)
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
    (at_ S (-2216)) (word_to_le_bytes 8 (Z_to_bv 64 0x5008c)))
    (at_ S (-2224)) (word_to_le_bytes 8 (Z_to_bv 64 (0x103f18 + 728))))
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
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 (0x103f18 + 728).
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
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 (T + 80)) 32 = true.
  Hypothesis Hokb : store_ok ASEGS mem (Z_to_bv 64 last) (Z.to_nat 8192) = true.
  (* [comment removed for export] *)
  Hypothesis Rlen : rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 len)).
  Hypothesis Rlast : rdn ASEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 last)).
  Hypothesis Rqb : rdn ASEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb)).
  Hypothesis Rbsz : rdn ASEGS mem (Z_to_bv 64 (last + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 bsz)).
  Hypothesis Rcnt : rdn ASEGS mem (Z_to_bv 64 (last + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 cnt)).
  (* [comment removed for export] *)
  Hypothesis Rq0 : rdn ASEGS mem (at_ S (-2136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e4a4)).
  Hypothesis Rq1 : rdn ASEGS mem (at_ S (-2144)) 8 = Some (word_to_le_bytes 8 S).
  Hypothesis Rq2 : rdn ASEGS mem (at_ S (-2152)) 8 = Some (word_to_le_bytes 8 p).
  Hypothesis Rq3 : rdn ASEGS mem (at_ S (-2160)) 8 = Some (word_to_le_bytes 8 x18).
  Hypothesis Rq4 : rdn ASEGS mem (at_ S (-2168)) 8 = Some (word_to_le_bytes 8 x19).
  Hypothesis Rq5 : rdn ASEGS mem (at_ S (-2176)) 8 = Some (word_to_le_bytes 8 x20).
  Hypothesis Rq6 : rdn ASEGS mem (at_ S (-2184)) 8 = Some (word_to_le_bytes 8 x21).
  Hypothesis Rq7 : rdn ASEGS mem (at_ S (-2192)) 8 = Some (word_to_le_bytes 8 x22).
  Hypothesis Ri0 : rdn ASEGS mem (at_ S (-8)) 8 = Some (word_to_le_bytes 8 ra0).
  Hypothesis Ri1 : rdn ASEGS mem (at_ S (-16)) 8 = Some (word_to_le_bytes 8 s0v).
  Hypothesis Ri2 : rdn ASEGS mem (at_ S (-24)) 8 = Some (word_to_le_bytes 8 s1v).
  Hypothesis Ri3 : rdn ASEGS mem (at_ S (-32)) 8 = Some (word_to_le_bytes 8 s2v).
  Hypothesis Ri4 : rdn ASEGS mem (at_ S (-40)) 8 = Some (word_to_le_bytes 8 s3v).
  Hypothesis Ri5 : rdn ASEGS mem (at_ S (-48)) 8 = Some (word_to_le_bytes 8 s4v).
  Hypothesis Ri6 : rdn ASEGS mem (at_ S (-56)) 8 = Some (word_to_le_bytes 8 s5v).

End C2.
End FPGen.

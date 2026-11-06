(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM2.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcS3.BoAllocFHs.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac stk_ok ::= any_ok_r.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wc_has_or T := lazymatch T with
  | _ \/ _ => idtac
  | ?A /\ ?B => first [wc_has_or A | wc_has_or B]
  | ?A <-> ?B => first [wc_has_or A | wc_has_or B]
  | _ -> ?B => wc_has_or B
  end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wc_clear_disj := am_wc_clear_disj.   (* [comment removed for export] *)
Ltac wc_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wc_clear_disj; wc_lia0] | wc_lia0 ].
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Ltac famo F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_amoadd_d with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
      | rd_addr Hr | exact Hv | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Definition fr_e1e (mem : word -> option byte) (S p : word) (T n cnt k ba qb : Z) (bst bcs : list byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (word_to_le_bytes 8 (Z_to_bv 64 0x50afc)))
    (at_ S (-2224)) (word_to_le_bytes 8 (Z_to_bv 64 (0x10ab58 + 728))))
    (at_ S (-2232)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 80)))
    (at_ S (-2240)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (at_ S (-2248)) (word_to_le_bytes 8 (at_ S (-2128))))
    (at_ S (-2256)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 208)))
    (at_ S (-2264)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 (T + 2128)) (word_to_le_bytes 4 (Z_to_bv 64 (cnt - 1))))
    (at_ (Z_to_bv 64 T) 2784) (word_to_le_bytes 8 (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (Z_to_bv 64 (bytes_le_to_Z bcs)))))
    (Z_to_bv 64 ba) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (ba + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n + 8192))))
    (Z_to_bv 64 (ba + 16)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
    (Z_to_bv 64 (ba + 24)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 (T + 88)) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
    (Z_to_bv 64 (T + 80)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
    (Z_to_bv 64 (T + 96)) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
    (Z_to_bv 64 (T + 104)) (word_to_le_bytes 8 (Z_to_bv 64 (qb + (n + 8192)))).
(* [comment removed for export] *)
Definition fr_e1f (mem : word -> option byte) (S p : word) (T n cnt k ba qb last len : Z) (bst bcs : list byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (word_to_le_bytes 8 (Z_to_bv 64 0x50afc)))
    (at_ S (-2224)) (word_to_le_bytes 8 (Z_to_bv 64 (0x10ab58 + 728))))
    (at_ S (-2232)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 80)))
    (at_ S (-2240)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (at_ S (-2248)) (word_to_le_bytes 8 (at_ S (-2128))))
    (at_ S (-2256)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 208)))
    (at_ S (-2264)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 (T + 2128)) (word_to_le_bytes 4 (Z_to_bv 64 (cnt - 1))))
    (at_ (Z_to_bv 64 T) 2784) (word_to_le_bytes 8 (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (Z_to_bv 64 (bytes_le_to_Z bcs)))))
    (Z_to_bv 64 ba) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (ba + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n + 8192))))
    (Z_to_bv 64 (ba + 16)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
    (Z_to_bv 64 (ba + 24)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 last) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
    (Z_to_bv 64 (T + 80)) (word_to_le_bytes 8 (Z_to_bv 64 (len + 1))))
    (Z_to_bv 64 (T + 96)) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
    (Z_to_bv 64 (T + 104)) (word_to_le_bytes 8 (Z_to_bv 64 (qb + (n + 8192)))).
Hint Unfold fr_e1e fr_e1f : asfr.

Section E1.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 ra0 s0v s1v s2v s3v s4v s5v : word).
  Variables (T n cnt k spb ba qb last len : Z) (bst bcs : list byte).
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
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis Hn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Hcnt : (1 <= cnt <= 16)%Z.
  Hypothesis Hk : (0 <= k < 2 ^ 32)%Z.
  Hypothesis Hspb : (0 <= spb)%Z.
  Hypothesis Hbak : (spb + 3 * 2 ^ 35 + 16 * k)%Z = ba.
  Hypothesis Hba : (AIMGHI <= ba /\ ba + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis HbaT : (ba + 8192 <= T \/ T + 4096 <= ba)%Z.
  Hypothesis Hqb : (0 <= qb <= 2 ^ 20)%Z.   (* [comment removed for export] *)
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Hokba : store_ok BSEGS mem (Z_to_bv 64 ba) 32 = true.
  (* [comment removed for export] *)
  Hypothesis Rqb : rdn BSEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb)).
  Hypothesis Rcnt : rdn BSEGS mem (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 cnt)).
  Hypothesis Rcs : rdn BSEGS mem (Z_to_bv 64 (T + 2136)) 8 = Some bcs.
  Hypothesis Rk : rdn BSEGS mem (Z_to_bv 64 (T + 2144 + 4 * (cnt - 1))) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 k)).
  Hypothesis Rst : rdn BSEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 0x10ab78) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spb)).
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

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma cnt_facts : ((cnt - 1) * 2 ^ 32 / 2 ^ 30 = 4 * (cnt - 1) /\ (T + 2784) mod 8 = 0)%Z.
  Proof using Lbcs Lbst Hk HT bcs bst k s5v S rom. split; [| lia]. replace ((cnt - 1) * 2 ^ 32)%Z with (4 * (cnt - 1) * 2 ^ 30)%Z by lia. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  #[local] Definition mid_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2272) /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  (* [comment removed for export] *)
  Ltac e1_prefix Rlen lenv :=
      an F_50ae4 D_50ae4;                              (* [comment removed for export] *)
      an F_50ae8 D_50ae8;                              (* [comment removed for export] *)
      an F_50aec D_50aec;                              (* [comment removed for export] *)
      an F_50af0 D_50af0;                              (* [comment removed for export] *)
      an F_50af4 D_50af4;                              (* [comment removed for export] *)
      an F_50af8 D_50af8;                              (* [comment removed for export] *)
      an F_50b08 D_50b08;                              (* [comment removed for export] *)
      fsd F_50b0c D_50b0c (at_ S (-2216));             (* [comment removed for export] *)
      fsd F_50b10 D_50b10 (at_ S (-2224));             (* [comment removed for export] *)
      fsd F_50b14 D_50b14 (at_ S (-2232));             (* [comment removed for export] *)
      fsd F_50b18 D_50b18 (at_ S (-2240));             (* [comment removed for export] *)
      fsd F_50b1c D_50b1c (at_ S (-2248));             (* [comment removed for export] *)
      fsd F_50b20 D_50b20 (at_ S (-2256));             (* [comment removed for export] *)
      fsd F_50b24 D_50b24 (at_ S (-2264));             (* [comment removed for export] *)
      cld8 F_50b28 D_50b28 (Z_to_bv 64 lenv) Rlen.     (* [comment removed for export] *)

  Lemma e1e_run :
    rdn BSEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    exists r,
      msteps BSEGS (mkst regs (0x50ae4 : word) mem rom) (mkst r (0x50c04 : word) (fr_e1e mem S p T n cnt k ba qb bst bcs) rom)
      /\ mid_regs r.
  Proof using Rspb Rst Rk Rcs Rcnt Rqb Hokba HokT Hstk Lbcs Lbst Hqb HbaT Hba Hbak Hspb Hk Hcnt Hn HT HS H22 H21 H20 H19 H18 H9 H8 H2 spb s5v.
    intros Rlen. (lazymatch goal with |- ?G => let G' := eval unfold mid_regs in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct cnt_facts as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 cnt)) = bv_unsigned (Z_to_bv 64 cnt)) by (apply bytes4_small; lia).
    assert (Vk : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 k)) = bv_unsigned (Z_to_bv 64 k)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - e1_prefix Rlen 0%Z.
      ab_tk F_50b2c D_50b2c ltac:(condz).              (* [comment removed for export] *)
      clw F_50b40 D_50b40 (word_to_le_bytes 4 (Z_to_bv 64 cnt)) (Z_to_bv 64 cnt) Rcnt Vcnt.   (* [comment removed for export] *)
      rewrite (v_lw_small cnt) by lia.
      ab_ft F_50b44 D_50b44 ltac:(condz).              (* [comment removed for export] *)
      av F_50b48 D_50b48 (Z_to_bv 64 (cnt - 1)) ltac:(valz).            (* [comment removed for export] *)
      av F_50b4c D_50b4c (Z_to_bv 64 ((cnt - 1) * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      fsw F_50b50 D_50b50 (Z_to_bv 64 (T + 2128)).    (* [comment removed for export] *)
      av F_50b54 D_50b54 (Z_to_bv 64 (4 * (cnt - 1))) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity).  (* [comment removed for export] *)
      av F_50b58 D_50b58 (Z_to_bv 64 (T + 208 + 4 * (cnt - 1))) ltac:(valz).   (* [comment removed for export] *)
      cld F_50b5c D_50b5c bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs.   (* [comment removed for export] *)
      an F_50b60 D_50b60.                              (* [comment removed for export] *)
      an F_50b64 D_50b64.                              (* [comment removed for export] *)
      clwu F_50b68 D_50b68 (word_to_le_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 64 k) Rk Vk.   (* [comment removed for export] *)
      famo F_50b6c D_50b6c bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst.   (* [comment removed for export] *)
      an F_50b70 D_50b70.                              (* [comment removed for export] *)
      cld8 F_50b74 D_50b74 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      an F_50b78 D_50b78.                              (* [comment removed for export] *)
      av F_50b7c D_50b7c (Z_to_bv 64 (16 * k)) ltac:(valz).               (* [comment removed for export] *)
      av F_50b80 D_50b80 (Z_to_bv 64 (3 * 2 ^ 35)) ltac:(valz).           (* [comment removed for export] *)
      av F_50b84 D_50b84 (Z_to_bv 64 (spb + 3 * 2 ^ 35)) ltac:(valz).     (* [comment removed for export] *)
      av F_50b88 D_50b88 (Z_to_bv 64 ba) ltac:(valz).                     (* [comment removed for export] *)
      ab_ft F_50b8c D_50b8c ltac:(condz).              (* [comment removed for export] *)
      an F_50b90 D_50b90.                              (* [comment removed for export] *)
      an F_50b94 D_50b94.                              (* [comment removed for export] *)
      av F_50b98 D_50b98 (Z_to_bv 64 (n + 8192)) ltac:(valz).             (* [comment removed for export] *)
      cld8 F_50b9c D_50b9c (Z_to_bv 64 0) Rlen.        (* [comment removed for export] *)
      fsd F_50ba0 D_50ba0 (Z_to_bv 64 ba).             (* [comment removed for export] *)
      fsd F_50ba4 D_50ba4 (Z_to_bv 64 (ba + 8)).       (* [comment removed for export] *)
      fsd F_50ba8 D_50ba8 (Z_to_bv 64 (ba + 16)).      (* [comment removed for export] *)
      fsd F_50bac D_50bac (Z_to_bv 64 (ba + 24)).      (* [comment removed for export] *)
      ab_tk F_50bb0 D_50bb0 ltac:(condz).              (* [comment removed for export] *)
      fsd F_50bec D_50bec (Z_to_bv 64 (T + 88)).       (* [comment removed for export] *)
      fsd F_50bf0 D_50bf0 (Z_to_bv 64 (T + 80)).       (* [comment removed for export] *)
      fsd F_50bf4 D_50bf4 (Z_to_bv 64 (T + 96)).       (* [comment removed for export] *)
      cld8 F_50bf8 D_50bf8 (Z_to_bv 64 qb) Rqb.        (* [comment removed for export] *)
      av F_50bfc D_50bfc (Z_to_bv 64 (qb + (n + 8192))) ltac:(valz).     (* [comment removed for export] *)
      fsd F_50c00 D_50c00 (Z_to_bv 64 (T + 104)).      (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_e1e mem S p T n cnt k ba qb bst bcs). wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hlen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis HlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Hlastba : (last + 8192 <= ba \/ ba + 8192 <= last)%Z.
  Hypothesis Hoklast : store_ok BSEGS mem (Z_to_bv 64 last) 8 = true.
  Hypothesis Rlast : rdn BSEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 last)).
  Hypothesis Rlcnt : rdn BSEGS mem (Z_to_bv 64 (last + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1021)).

  Lemma e1f_run :
    rdn BSEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 len)) ->
    exists r,
      msteps BSEGS (mkst regs (0x50ae4 : word) mem rom) (mkst r (0x50c04 : word) (fr_e1f mem S p T n cnt k ba qb last len bst bcs) rom)
      /\ mid_regs r.
  Proof using Rlcnt Rlast Hoklast Hlastba HlastT Hlast Hlen Rspb Rst Rk Rcs Rcnt Rqb Hokba HokT Hstk Lbcs Lbst Hqb HbaT Hba Hbak Hspb Hk Hcnt Hn HT HS H22 H21 H20 H19 H18 H9 H8 H2 spb s5v.
    intros Rlen. (lazymatch goal with |- ?G => let G' := eval unfold mid_regs in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct cnt_facts as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 cnt)) = bv_unsigned (Z_to_bv 64 cnt)) by (apply bytes4_small; lia).
    assert (Vk : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 k)) = bv_unsigned (Z_to_bv 64 k)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - e1_prefix Rlen len.
      ab_ft F_50b2c D_50b2c ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50b30 D_50b30 (Z_to_bv 64 last) Rlast.    (* [comment removed for export] *)
      cld8 F_50b34 D_50b34 (Z_to_bv 64 1021) Rlcnt.    (* [comment removed for export] *)
      an F_50b38 D_50b38.                              (* [comment removed for export] *)
      ab_ft F_50b3c D_50b3c ltac:(condz).              (* [comment removed for export] *)
      clw F_50b40 D_50b40 (word_to_le_bytes 4 (Z_to_bv 64 cnt)) (Z_to_bv 64 cnt) Rcnt Vcnt.   (* [comment removed for export] *)
      rewrite (v_lw_small cnt) by lia.
      ab_ft F_50b44 D_50b44 ltac:(condz).              (* [comment removed for export] *)
      av F_50b48 D_50b48 (Z_to_bv 64 (cnt - 1)) ltac:(valz).            (* [comment removed for export] *)
      av F_50b4c D_50b4c (Z_to_bv 64 ((cnt - 1) * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      fsw F_50b50 D_50b50 (Z_to_bv 64 (T + 2128)).    (* [comment removed for export] *)
      av F_50b54 D_50b54 (Z_to_bv 64 (4 * (cnt - 1))) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity).  (* [comment removed for export] *)
      av F_50b58 D_50b58 (Z_to_bv 64 (T + 208 + 4 * (cnt - 1))) ltac:(valz).   (* [comment removed for export] *)
      cld F_50b5c D_50b5c bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs.   (* [comment removed for export] *)
      an F_50b60 D_50b60.                              (* [comment removed for export] *)
      an F_50b64 D_50b64.                              (* [comment removed for export] *)
      clwu F_50b68 D_50b68 (word_to_le_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 64 k) Rk Vk.   (* [comment removed for export] *)
      famo F_50b6c D_50b6c bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst.   (* [comment removed for export] *)
      an F_50b70 D_50b70.                              (* [comment removed for export] *)
      cld8 F_50b74 D_50b74 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      an F_50b78 D_50b78.                              (* [comment removed for export] *)
      av F_50b7c D_50b7c (Z_to_bv 64 (16 * k)) ltac:(valz).               (* [comment removed for export] *)
      av F_50b80 D_50b80 (Z_to_bv 64 (3 * 2 ^ 35)) ltac:(valz).           (* [comment removed for export] *)
      av F_50b84 D_50b84 (Z_to_bv 64 (spb + 3 * 2 ^ 35)) ltac:(valz).     (* [comment removed for export] *)
      av F_50b88 D_50b88 (Z_to_bv 64 ba) ltac:(valz).                     (* [comment removed for export] *)
      ab_ft F_50b8c D_50b8c ltac:(condz).              (* [comment removed for export] *)
      an F_50b90 D_50b90.                              (* [comment removed for export] *)
      an F_50b94 D_50b94.                              (* [comment removed for export] *)
      av F_50b98 D_50b98 (Z_to_bv 64 (n + 8192)) ltac:(valz).             (* [comment removed for export] *)
      cld8 F_50b9c D_50b9c (Z_to_bv 64 len) Rlen.      (* [comment removed for export] *)
      fsd F_50ba0 D_50ba0 (Z_to_bv 64 ba).             (* [comment removed for export] *)
      fsd F_50ba4 D_50ba4 (Z_to_bv 64 (ba + 8)).       (* [comment removed for export] *)
      fsd F_50ba8 D_50ba8 (Z_to_bv 64 (ba + 16)).      (* [comment removed for export] *)
      fsd F_50bac D_50bac (Z_to_bv 64 (ba + 24)).      (* [comment removed for export] *)
      ab_ft F_50bb0 D_50bb0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50bb4 D_50bb4 (Z_to_bv 64 last) Rlast.    (* [comment removed for export] *)
      fsd F_50bb8 D_50bb8 (Z_to_bv 64 last).           (* [comment removed for export] *)
      av F_50bbc D_50bbc (Z_to_bv 64 (len + 1)) ltac:(valz).              (* [comment removed for export] *)
      an F_50bc0 D_50bc0.                              (* [comment removed for export] *)
      fsd F_50bf0 D_50bf0 (Z_to_bv 64 (T + 80)).       (* [comment removed for export] *)
      fsd F_50bf4 D_50bf4 (Z_to_bv 64 (T + 96)).       (* [comment removed for export] *)
      cld8 F_50bf8 D_50bf8 (Z_to_bv 64 qb) Rqb.        (* [comment removed for export] *)
      av F_50bfc D_50bfc (Z_to_bv 64 (qb + (n + 8192))) ltac:(valz).     (* [comment removed for export] *)
      fsd F_50c00 D_50c00 (Z_to_bv 64 (T + 104)).      (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_e1f mem S p T n cnt k ba qb last len bst bcs). wd_refl.
    - post.
  Qed.
End E1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QTAIL.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 ra0 s0v s1v s2v s3v s4v s5v v1 v3 v4 v5 v6 : word) (T qb2 : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2272).
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 (2 ^ 20).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (AIMGHI + 16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hqb2 : (0 <= qb2 <= 2 ^ 20)%Z.
  Hypothesis Hret : ret_ok ra0.
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

  Lemma q_tail_run :
    exists r,
      msteps BSEGS (mkst regs (0x50c04 : word) mem rom) (mkst r ra0 mem rom)
      /\ getr r 2 = S /\ getr r 1 = ra0 /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = x22
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Ri6 Ri5 Ri4 Ri3 Ri2 Ri1 Ri0 Rq7 Rq6 Rq5 Rq4 Rq3 Rq2 Rq1 Rq0 Rqb2 Re6 Re5 Re4 Re3 Re2 Re1 Re0 Hret Hqb2 HT HS H22 H2 qb2 T v6 v5 v4 v3 v1 x21 x20 x19 x18 p.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HT as (HT1 & HT2). unfold hideW in HT2.
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
      ab_ft F_50b00 D_50b00 ltac:(condz).              (* [comment removed for export] *)
      an F_50b04 D_50b04.                              (* [comment removed for export] *)
      cld8 F_50a34 D_50a34 (Z_to_bv 64 0x6ef14) Rq0.   (* [comment removed for export] *)
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
End QTAIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section E1MEM.
  Variables (M13 : word -> option byte) (S p : word) (T n cnt k ba qb last len : Z) (bst bcs : list byte).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hba : (AIMGHI <= ba /\ ba + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 8192 <= bv_unsigned S - 3584)%Z.
  #[local] Abbreviation U := bv_unsigned.
  #[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
  #[local] Abbreviation Me := (fr_e1e M13 S p T n cnt k ba qb bst bcs).
  #[local] Abbreviation Mf := (fr_e1f M13 S p T n cnt k ba qb last len bst bcs).
  Ltac digE := (lazymatch goal with |- ?G => let G' := eval unfold fr_e1e, fr_e1f in G in change_no_check G' end); repeat (wd_rdstep rd8_side).




















End E1MEM.
End FPGen.

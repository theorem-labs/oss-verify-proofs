(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAllocF5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsAllocFHs.
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

Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

Ltac famo F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_amoadd_d with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
      | rd_addr Hr | exact Hv | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Definition fr_enq (mem : word -> option byte) (S p : word) (T n : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (word_to_le_bytes 8 (Z_to_bv 64 0x5008c)))
    (at_ S (-2224)) (word_to_le_bytes 8 (Z_to_bv 64 (0x103f18 + 728))))
    (at_ S (-2232)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 80)))
    (at_ S (-2240)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (at_ S (-2248)) (word_to_le_bytes 8 (at_ S (-2128))))
    (at_ S (-2256)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 208)))
    (at_ S (-2264)) (word_to_le_bytes 8 (at_ p (-16))).
(* [comment removed for export] *)
Definition fr_e2e (mem : word -> option byte) (S p : word) (T n cnt k ba qb : Z) (bst bcs : list byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
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
Definition fr_e2f (mem : word -> option byte) (S p : word) (T n cnt k ba qb last len : Z) (bst bcs : list byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
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
Hint Unfold fr_enq fr_e2e fr_e2f : asfr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ER1.
  Variables (mem rom : word -> option byte) (S p : word) (T n last len : Z).
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
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis Rcnt0 : rdn ASEGS mem (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  #[local] Definition call_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = Z_to_bv 64 0x501ec /\ getr r 2 = at_ S (-2272)
      /\ getr r 10 = at_ (Z_to_bv 64 T) 208 /\ getr r 11 = at_ (Z_to_bv 64 T) 2128 /\ getr r 12 = Z_to_bv 64 0x103f18 /\ getr r 13 = Z_to_bv 64 24
      /\ getr r 8 = at_ (Z_to_bv 64 T) 2128 /\ getr r 9 = at_ (Z_to_bv 64 T) 208 /\ getr r 18 = at_ p (-16) /\ getr r 19 = at_ (Z_to_bv 64 T) 80
      /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Ltac er1_prefix Rlen lenv :=
      an F_5006c D_5006c; an F_50070 D_50070; an F_50074 D_50074; an F_50078 D_50078; an F_5007c D_5007c;
      an F_50080 D_50080;                              (* [comment removed for export] *)
      an F_50090 D_50090;                              (* [comment removed for export] *)
      fsd F_50094 D_50094 (at_ S (-2216)); fsd F_50098 D_50098 (at_ S (-2224)); fsd F_5009c D_5009c (at_ S (-2232));
      fsd F_500a0 D_500a0 (at_ S (-2240)); fsd F_500a4 D_500a4 (at_ S (-2248)); fsd F_500a8 D_500a8 (at_ S (-2256));
      fsd F_500ac D_500ac (at_ S (-2264));
      cld8 F_500b0 D_500b0 (Z_to_bv 64 lenv) Rlen.     (* [comment removed for export] *)
  Ltac er1_suffix V0 :=
      clw F_500c8 D_500c8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) Rcnt0 V0;   (* [comment removed for export] *)
      try (rewrite (v_lw_small 0) by lia);
      ab_tk F_500cc D_500cc ltac:(condz);              (* [comment removed for export] *)
      an F_501b0 D_501b0;                              (* [comment removed for export] *)
      an F_501b4 D_501b4;                              (* [comment removed for export] *)
      an F_501b8 D_501b8;                              (* [comment removed for export] *)
      an F_501bc D_501bc; an F_501c0 D_501c0; an F_501c4 D_501c4; an F_501c8 D_501c8; an F_501cc D_501cc;
      an F_501d0 D_501d0; an F_501d4 D_501d4; an F_501d8 D_501d8; an F_501dc D_501dc;
      an F_501e0 D_501e0.                              (* [comment removed for export] *)

  Lemma er1e_run :
    rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    exists r, msteps ASEGS (mkst regs (0x50074 : word) mem rom) (mkst r (0x509cc : word) (fr_enq mem S p T n) rom) /\ call_regs r.
  Proof using Rcnt0 Hstk HT HS H22 H21 H20 H19 H18 H9 H8 H2.
    intros Rlen. (lazymatch goal with |- ?G => let G' := eval unfold call_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    assert (V0 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 0)) = bv_unsigned (Z_to_bv 64 0)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - er1_prefix Rlen 0%Z.
      ab_tk F_500b4 D_500b4 ltac:(condz).              (* [comment removed for export] *)
      er1_suffix V0.
      change (wbytes _ _ _) with (fr_enq mem S p T n). wd_refl.
    - post.
  Qed.

  Hypothesis Hlast : (AIMGHI <= last /\ last + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hlen : (1 <= len < 2 ^ 40)%Z.
  Lemma er1f_run :
    rdn ASEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 last)) ->
    rdn ASEGS mem (Z_to_bv 64 (last + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1021)) ->
    rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 len)) ->
    exists r, msteps ASEGS (mkst regs (0x50074 : word) mem rom) (mkst r (0x509cc : word) (fr_enq mem S p T n) rom) /\ call_regs r.
  Proof using Hlen Hlast Rcnt0 Hstk HT HS H22 H21 H20 H19 H18 H9 H8 H2.
    intros Rlast Rlcnt Rlen. (lazymatch goal with |- ?G => let G' := eval unfold call_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    assert (V0 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 0)) = bv_unsigned (Z_to_bv 64 0)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - er1_prefix Rlen len.
      ab_ft F_500b4 D_500b4 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_500b8 D_500b8 (Z_to_bv 64 last) Rlast.    (* [comment removed for export] *)
      cld8 F_500bc D_500bc (Z_to_bv 64 1021) Rlcnt.    (* [comment removed for export] *)
      an F_500c0 D_500c0.                              (* [comment removed for export] *)
      ab_ft F_500c4 D_500c4 ltac:(condz).              (* [comment removed for export] *)
      er1_suffix V0.
      change (wbytes _ _ _) with (fr_enq mem S p T n). wd_refl.
    - post.
  Qed.
End ER1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ER2.
  Variables (mem rom : word -> option byte) (S p : word) (T n cnt k spb ba qb last len : Z) (bst bcs : list byte).
  Variable regs : bvmap 5 word.
  (* [comment removed for export] *)
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 1.
  Hypothesis H2 : getr regs 2 = at_ S (-2272).
  Hypothesis H8 : getr regs 8 = at_ (Z_to_bv 64 T) 2128.
  Hypothesis H9 : getr regs 9 = at_ (Z_to_bv 64 T) 208.
  Hypothesis H18 : getr regs 18 = at_ p (-16).
  Hypothesis H19 : getr regs 19 = at_ (Z_to_bv 64 T) 80.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 n.
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
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Hokba : store_ok ASEGS mem (Z_to_bv 64 ba) 32 = true.
  Hypothesis Rqb : rdn ASEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb)).
  Hypothesis Rcnt : rdn ASEGS mem (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 cnt)).
  Hypothesis Rcs : rdn ASEGS mem (Z_to_bv 64 (T + 2136)) 8 = Some bcs.
  Hypothesis Rk : rdn ASEGS mem (Z_to_bv 64 (T + 2144 + 4 * (cnt - 1))) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 k)).
  Hypothesis Rst : rdn ASEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis Rspb : rdn ASEGS mem (Z_to_bv 64 0x103f38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spb)).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma cnt_facts2 : ((cnt - 1) * 2 ^ 32 / 2 ^ 30 = 4 * (cnt - 1) /\ (T + 2784) mod 8 = 0)%Z.
  Proof using Lbcs Lbst Hk HT bcs bst k p S rom. split; [| lia]. replace ((cnt - 1) * 2 ^ 32)%Z with (4 * (cnt - 1) * 2 ^ 30)%Z by lia. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  #[local] Definition mid_regs2 (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2272) /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Ltac er2_common Vcnt Vk Vcs Vst Hc4 :=
      an F_501e4 D_501e4;                              (* [comment removed for export] *)
      ab_ft F_501e8 D_501e8 ltac:(condz);              (* [comment removed for export] *)
      an F_501ec D_501ec; an F_501f0 D_501f0; an F_501f4 D_501f4;
      clw F_501f8 D_501f8 (word_to_le_bytes 4 (Z_to_bv 64 cnt)) (Z_to_bv 64 cnt) Rcnt Vcnt;   (* [comment removed for export] *)
      rewrite (v_lw_small cnt) by lia;
      an F_501fc D_501fc;                              (* [comment removed for export] *)
      an F_50200 D_50200;                              (* [comment removed for export] *)
      av F_500d0 D_500d0 (Z_to_bv 64 (cnt - 1)) ltac:(valz);
      av F_500d4 D_500d4 (Z_to_bv 64 ((cnt - 1) * 2 ^ 32)) ltac:(valz);
      fsw F_500d8 D_500d8 (Z_to_bv 64 (T + 2128));
      av F_500dc D_500dc (Z_to_bv 64 (4 * (cnt - 1))) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity);
      av F_500e0 D_500e0 (Z_to_bv 64 (T + 208 + 4 * (cnt - 1))) ltac:(valz);
      cld F_500e4 D_500e4 bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs;
      an F_500e8 D_500e8; an F_500ec D_500ec;
      clwu F_500f0 D_500f0 (word_to_le_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 64 k) Rk Vk;
      famo F_500f4 D_500f4 bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst;
      an F_500f8 D_500f8;
      cld8 F_500fc D_500fc (Z_to_bv 64 spb) Rspb;
      an F_50100 D_50100;
      av F_50104 D_50104 (Z_to_bv 64 (16 * k)) ltac:(valz);
      av F_50108 D_50108 (Z_to_bv 64 (3 * 2 ^ 35)) ltac:(valz);
      av F_5010c D_5010c (Z_to_bv 64 (spb + 3 * 2 ^ 35)) ltac:(valz);
      av F_50110 D_50110 (Z_to_bv 64 ba) ltac:(valz);
      ab_ft F_50114 D_50114 ltac:(condz);
      an F_50118 D_50118; an F_5011c D_5011c;
      av F_50120 D_50120 (Z_to_bv 64 (n + 8192)) ltac:(valz).

  Lemma er2e_run :
    rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    exists r, msteps ASEGS (mkst regs (0x501ec : word) mem rom) (mkst r (0x50194 : word) (fr_e2e mem S p T n cnt k ba qb bst bcs) rom) /\ mid_regs2 r.
  Proof using Rspb Rst Rk Rcs Rcnt Rqb Hokba HokT Lbcs Lbst Hqb HbaT Hba Hbak Hspb Hk Hcnt Hn HT HS H22 H21 H19 H18 H9 H8 H2 H10 spb.
    intros Rlen. (lazymatch goal with |- ?G => let G' := eval unfold mid_regs2 in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct cnt_facts2 as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 cnt)) = bv_unsigned (Z_to_bv 64 cnt)) by (apply bytes4_small; lia).
    assert (Vk : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 k)) = bv_unsigned (Z_to_bv 64 k)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - er2_common Vcnt Vk Vcs Vst Hc4.
      cld8 F_50124 D_50124 (Z_to_bv 64 0) Rlen.        (* [comment removed for export] *)
      fsd F_50128 D_50128 (Z_to_bv 64 ba).
      fsd F_5012c D_5012c (Z_to_bv 64 (ba + 8)).
      fsd F_50130 D_50130 (Z_to_bv 64 (ba + 16)).
      fsd F_50134 D_50134 (Z_to_bv 64 (ba + 24)).
      ab_tk F_50138 D_50138 ltac:(condz).              (* [comment removed for export] *)
      fsd F_50174 D_50174 (Z_to_bv 64 (T + 88)).
      fsd F_50178 D_50178 (Z_to_bv 64 (T + 80)).
      fsd F_5017c D_5017c (Z_to_bv 64 (T + 96)).
      cld8 F_50180 D_50180 (Z_to_bv 64 qb) Rqb.
      av F_50184 D_50184 (Z_to_bv 64 (qb + (n + 8192))) ltac:(valz).
      fsd F_50188 D_50188 (Z_to_bv 64 (T + 104)).
      change (wbytes _ _ _) with (fr_e2e mem S p T n cnt k ba qb bst bcs). wd_refl.
    - post.
  Qed.

  Hypothesis Hlen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis HlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Hlastba : (last + 8192 <= ba \/ ba + 8192 <= last)%Z.
  Hypothesis Hoklast : store_ok ASEGS mem (Z_to_bv 64 last) 8 = true.
  Hypothesis Rlast : rdn ASEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 last)).

  Lemma er2f_run :
    rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 len)) ->
    exists r, msteps ASEGS (mkst regs (0x501ec : word) mem rom) (mkst r (0x50194 : word) (fr_e2f mem S p T n cnt k ba qb last len bst bcs) rom) /\ mid_regs2 r.
  Proof using Rlast Hoklast Hlastba HlastT Hlast Hlen Rspb Rst Rk Rcs Rcnt Rqb Hokba HokT Lbcs Lbst Hqb HbaT Hba Hbak Hspb Hk Hcnt Hn HT HS H22 H21 H19 H18 H9 H8 H2 H10 spb.
    intros Rlen. (lazymatch goal with |- ?G => let G' := eval unfold mid_regs2 in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct cnt_facts2 as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 cnt)) = bv_unsigned (Z_to_bv 64 cnt)) by (apply bytes4_small; lia).
    assert (Vk : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 k)) = bv_unsigned (Z_to_bv 64 k)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - er2_common Vcnt Vk Vcs Vst Hc4.
      cld8 F_50124 D_50124 (Z_to_bv 64 len) Rlen.      (* [comment removed for export] *)
      fsd F_50128 D_50128 (Z_to_bv 64 ba).
      fsd F_5012c D_5012c (Z_to_bv 64 (ba + 8)).
      fsd F_50130 D_50130 (Z_to_bv 64 (ba + 16)).
      fsd F_50134 D_50134 (Z_to_bv 64 (ba + 24)).
      ab_ft F_50138 D_50138 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_5013c D_5013c (Z_to_bv 64 last) Rlast.
      fsd F_50140 D_50140 (Z_to_bv 64 last).
      av F_50144 D_50144 (Z_to_bv 64 (len + 1)) ltac:(valz).
      an F_50148 D_50148.
      fsd F_50178 D_50178 (Z_to_bv 64 (T + 80)).
      fsd F_5017c D_5017c (Z_to_bv 64 (T + 96)).
      cld8 F_50180 D_50180 (Z_to_bv 64 qb) Rqb.
      av F_50184 D_50184 (Z_to_bv 64 (qb + (n + 8192))) ltac:(valz).
      fsd F_50188 D_50188 (Z_to_bv 64 (T + 104)).
      change (wbytes _ _ _) with (fr_e2f mem S p T n cnt k ba qb last len bst bcs). wd_refl.
    - post.
  Qed.
End ER2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section E2MEM.
  Variables (MR : word -> option byte) (S p : word) (T n cnt k ba qb last len : Z) (bst bcs : list byte).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hba : (AIMGHI <= ba /\ ba + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 8192 <= bv_unsigned S - 3584)%Z.
  #[local] Abbreviation U := bv_unsigned.
  #[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
  #[local] Abbreviation Me := (fr_e2e MR S p T n cnt k ba qb bst bcs).
  #[local] Abbreviation Mf := (fr_e2f MR S p T n cnt k ba qb last len bst bcs).
  Ltac digE2 := (lazymatch goal with |- ?G => let G' := eval unfold fr_e2e, fr_e2f in G in change_no_check G' end); repeat (wd_rdstep rd8_side).

  Lemma fr_e2e_quiet : forall x : word,
    (U x < T \/ T + 4096 <= U x)%Z -> (U x < ba \/ ba + 32 <= U x)%Z -> Me x = MR x.
  Proof using Hba HT HS.
    intros x A2 A3. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_e2e in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; try lia. reflexivity.
  Qed.
  Lemma fr_e2f_quiet : forall x : word,
    (U x < T \/ T + 4096 <= U x)%Z -> (U x < ba \/ ba + 32 <= U x)%Z -> (U x < last \/ last + 8 <= U x)%Z -> Mf x = MR x.
  Proof using Hlast Hba HT HS.
    intros x A2 A3 A4. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_e2f in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; try lia. reflexivity.
  Qed.
  Lemma fr_e2e_qb : rdn ASEGS Me (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (qb + (n + 8192)))).  Proof using HT HS. pose proof (u64_range S). digE2. Qed.
  Lemma fr_e2f_qb : rdn ASEGS Mf (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 (qb + (n + 8192)))).  Proof using HT HS. pose proof (u64_range S). digE2. Qed.
  Lemma fr_e2e_grows : mem_grows MR Me.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_e2e in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma fr_e2f_grows : mem_grows MR Mf.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_e2f in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  (* [comment removed for export] *)
  Lemma fr_e2e_stack : forall k0 bs0, (-2304 <= k0)%Z -> (k0 + 8 <= 0)%Z ->
    rdn ASEGS MR (at_ S k0) 8 = Some bs0 -> rdn ASEGS Me (at_ S k0) 8 = Some bs0.
  Proof using Hba HT HS.
    intros k0 bs0 H1 H2 Hr. pose proof (u64_range S). rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|].
    intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply fr_e2e_quiet; lia.
  Qed.
  Lemma fr_e2f_stack : forall k0 bs0, (-2304 <= k0)%Z -> (k0 + 8 <= 0)%Z ->
    rdn ASEGS MR (at_ S k0) 8 = Some bs0 -> rdn ASEGS Mf (at_ S k0) 8 = Some bs0.
  Proof using Hlast Hba HT HS.
    intros k0 bs0 H1 H2 Hr. pose proof (u64_range S). rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|].
    intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply fr_e2f_quiet; lia.
  Qed.
End E2MEM.
End FPGen.
End AsAllocF5.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRun3R.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N.AsAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 AsAllocF5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition hideR (P : Prop) : Prop := P.
Ltac hidehypR H := lazymatch type of H with ?T => change T with (hideR T) in H end.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_P3r1 (memD : word -> option byte) (S p x22 : word) (T n n8 id : Z) : word -> option byte :=
  let M12 := fr_c1 memD S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T in
  let M13 := fr_PS M12 S p T n n8 in
  fr_enq M13 S p T n.

(* [comment removed for export] *)
Definition refill_call_regs (S p tp : word) (T n : Z) (rD r : bvmap 5 word) : Prop :=
    getr r 1 = Z_to_bv 64 0x501ec /\ getr r 2 = at_ S (-2272)
    /\ getr r 10 = at_ (Z_to_bv 64 T) 208 /\ getr r 11 = at_ (Z_to_bv 64 T) 2128 /\ getr r 12 = Z_to_bv 64 0x103f18 /\ getr r 13 = Z_to_bv 64 24
    /\ getr r 8 = at_ (Z_to_bv 64 T) 2128 /\ getr r 9 = at_ (Z_to_bv 64 T) 208 /\ getr r 18 = at_ p (-16) /\ getr r 19 = at_ (Z_to_bv 64 T) 80
    /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
    /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
    /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24 /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.

Section RUN3R.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S p ra0 tp x22 s0v s1v s2v s3v s4v s5v : word) (T n n8 id fl last qb len : Z) (cpm : byte) (midend : word).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 2 = at_ S (-2176).
  Hypothesis D8 : getr rD 8 = at_ p (-16).
  Hypothesis D9 : getr rD 9 = at_ S (-2128).
  Hypothesis D10 : getr rD 10 = Z_to_bv 64 id.
  Hypothesis D18 : getr rD 18 = Z_to_bv 64 0x103f18.
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
  Hypothesis Gqb : (0 <= qb /\ qb + n + 8192 <= 2 ^ 20)%Z.
  Hypothesis GT16 : (T mod 16 = 0)%Z.
  Hypothesis Glen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Gmid : (U midend < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS memD (at_ S (-2304)) 2304 = true.
  Hypothesis Okp : store_ok ASEGS memD p 8 = true.
  Hypothesis Oksh : store_ok ASEGS memD (Z_to_bv 64 (shad p)) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok ASEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  (* [comment removed for export] *)
  Hypothesis C_q0 : rdn ASEGS memD (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4)).
  Hypothesis C_q1 : rdn ASEGS memD (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C_q2 : rdn ASEGS memD (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C_q3 : rdn ASEGS memD (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434)).
  Hypothesis C_q4 : rdn ASEGS memD (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis C_q5 : rdn ASEGS memD (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).
  Hypothesis C_i0 : rdn ASEGS memD (at_ S (-8)) 8 = Some (LE8 ra0).
  Hypothesis C_i1 : rdn ASEGS memD (at_ S (-16)) 8 = Some (LE8 s0v).
  Hypothesis C_i2 : rdn ASEGS memD (at_ S (-24)) 8 = Some (LE8 s1v).
  Hypothesis C_i3 : rdn ASEGS memD (at_ S (-32)) 8 = Some (LE8 s2v).
  Hypothesis C_i4 : rdn ASEGS memD (at_ S (-40)) 8 = Some (LE8 s3v).
  Hypothesis C_i5 : rdn ASEGS memD (at_ S (-48)) 8 = Some (LE8 s4v).
  Hypothesis C_i6 : rdn ASEGS memD (at_ S (-56)) 8 = Some (LE8 s5v).
  Hypothesis C_nhi : rdn ASEGS memD (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn ASEGS memD (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_mcs : rdn ASEGS memD (Z_to_bv 64 (0x103f18 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis C_msz : rdn ASEGS memD (Z_to_bv 64 (0x103f18 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis C_gfl : rdn ASEGS memD (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 fl)).
  Hypothesis C_mff : rdn ASEGS memD (Z_to_bv 64 (fl + 48)) 4 = Some (LE4 0).
  Hypothesis C_gsh : rdn ASEGS memD (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578)).
  Hypothesis C_sh : rdn ASEGS memD (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn ASEGS memD (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268)).
  Hypothesis C_mb : rdn ASEGS memD (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn ASEGS memD (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270)).
  Hypothesis C_me : rdn ASEGS memD (Z_to_bv 64 0x108270) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn ASEGS memD (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260)).
  Hypothesis C_he : rdn ASEGS memD (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn ASEGS memD (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0)).
  Hypothesis C_rm : rdn ASEGS memD (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4)).
  Hypothesis C_cpm : rdn ASEGS memD (Z_to_bv 64 0x106ddc) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_qb : rdn ASEGS memD (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis C_cnt0 : rdn ASEGS memD (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Theorem run_p3r1e :
    rdn ASEGS memD (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    exists r,
      msteps ASEGS (mkst rD (0x4fdc8 : word) memD rom) (mkst r (0x509cc : word) (fr_P3r1 memD S p x22 T n n8 id) rom)
      /\ refill_call_regs S p tp T n rD r.
  Proof using C_cnt0 C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh C_mff C_gfl C_msz C_mcs C_nlo C_nhi C_q5 C_q4 C_q3 C_q2 C_q1 C_q0 Oksh Okp Hstk Gfl Gid Gn8 Gn GpT GT Gp GS D4 D22 D21 D20 D19 D18 D10 D9 D8 D1 midend cpm fl.
    intros C_len0. (lazymatch goal with |- ?G => let G' := eval unfold refill_call_regs in G in change_no_check G' end).
    clear Glast GlastT Glastp Glen Gqb C_qb C_i0 C_i1 C_i2 C_i3 C_i4 C_i5 C_i6 Hret.   (* [comment removed for export] *)
    hidehypR GpT.
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
    destruct (c1_run memD rom S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 T n id fl n8 rD
                D1 D8 D9 D10 D18 D19 D20 D21 D22 ltac:(hlia) ltac:(hlia) ltac:(hlia) Gn Gid ltac:(hlia) N8a Hstk Okp
                C_q0 C_q1 C_q2 C_q3 C_q4 C_q5 C_nhi C_nlo C_mcs C_msz C_gfl C_mff)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A3 & A4 & A23 & A24 & A25 & A26 & A27).
    set (M12t := fr_c1 memD S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T) in RUN1.
    assert (GR12 : mem_grows memD M12t) by ((lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end); grows_tac).
    assert (Q12 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M12t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. reflexivity. }
    remember M12t as M12 eqn:EM12 in RUN1, GR12, Q12. subst M12t.
    (* [comment removed for export] *)
    assert (PH : poisonH ASEGS asan_poison_tab M12 p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50074) (at_ S (-2208)) cpm midend 0).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm pt_base pt_mset asan_poison_tab] in G in change_no_check G' end).
      - xq Q12 C_gsh. - xq Q12 C_sh. - xq Q12 C_gmb. - xq Q12 C_mb. - xq Q12 C_gme. - xq Q12 C_me. - xq Q12 C_ghe. - xq Q12 C_he.
      - xq Q12 C_grm. - xq Q12 C_rm.
      - vm_compute. discriminate.
      - apply ret_ok_even. reflexivity.
      - intros _. split; [xq Q12 C_cpm | exact C_cpm1].
      - intros Hz. exfalso. revert Hz. unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
        repeat constructor; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ].
      - destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & M8 & _). exact M8.
      - unorm. exact N8c.
      - unorm. unfold hideW in GpS. destruct GpS as [PS|PS]; [right | left]; lia.
      - rewrite at_u by lia. lia.
      - eapply (store_ok_sub ASEGS M12 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR12 | exact Hstk] | rewrite !at_at, !at_u; lia | rewrite !at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. eapply store_ok_mono; [exact GR12 | exact Oksh].
      - apply ret_ok_lit; [lia | reflexivity]. }
    destruct (asan_poison_shadow M12 rom p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50074) (at_ S (-2208)) cpm midend 0 r1 PH A1 A2 A10 A11 A12)
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
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia.
      1: apply Q12; lia.
      all: (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); unorm; rewrite ?Z2Nat.id by lia; lia. }
    (* [comment removed for export] *)
    Ltac dig := repeat (wd_rdstep rd8_side).
    Ltac slot13 E := (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end); rewrite !at_at;
                   rewrite rdn_wbytes_out; [ | (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); rewrite ?repeat_length; unorm; rewrite ?Z2Nat.id by lia; rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia .. ];
                   dig; rewrite E; (lazymatch goal with |- ?G => let G' := eval unfold fr_c1 in G in change_no_check G' end); dig.
    assert (P0 : rdn ASEGS M13t (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P1 : rdn ASEGS M13t (at_ S (-2144)) 8 = Some (LE8 S)) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P2 : rdn ASEGS M13t (at_ S (-2152)) 8 = Some (LE8 p)) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P3 : rdn ASEGS M13t (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P4 : rdn ASEGS M13t (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P5 : rdn ASEGS M13t (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P6 : rdn ASEGS M13t (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81)))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P7 : rdn ASEGS M13t (at_ S (-2192)) 8 = Some (LE8 x22)) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    remember M13t as M13 eqn:EM13 in RUN2, GR13, Q13, P0, P1, P2, P3, P4, P5, P6, P7. subst M13t.
    (* [comment removed for export] *)
    assert (V2 : getr r2 2 = at_ S (-2208)) by viac AGP (2:reg).
    assert (V8 : getr r2 8 = Z_to_bv 64 (0x103f18 + 728)) by viac AGP (8:reg).
    assert (V9 : getr r2 9 = at_ (Z_to_bv 64 T) 80) by viac AGP (9:reg).
    assert (V18 : getr r2 18 = Z_to_bv 64 n) by viac AGP (18:reg).
    assert (V19 : getr r2 19 = at_ S (-2128)) by viac AGP (19:reg).
    assert (V20 : getr r2 20 = at_ (Z_to_bv 64 T) 208) by viac AGP (20:reg).
    assert (V21 : getr r2 21 = at_ p (-16)) by viac AGP (21:reg).
    assert (V22 : getr r2 22 = Z_to_bv 64 (2 ^ 20)) by viac AGP (22:reg).
    (* [comment removed for export] *)
    assert (GTw : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z) by hlia.
    Ltac finish_r RUN1 RUN2 RUN3 M13 M12 AGP :=
      wd_eexists; split;
      [ subst M13 M12; (lazymatch goal with |- ?G => let G' := eval unfold fr_P3r1, fr_PS in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end);
        eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [| exact RUN3];
        replace (Z_to_bv 64 0x50074 : word) with (0x50074 : word) in RUN2 at 1 by (apply bv_eq; reflexivity);
        exact RUN2
      | repeat match goal with |- _ /\ _ => split end; try assumption; try rch;
        try (viac AGP (3:reg)); try (viac AGP (4:reg)); try (viac AGP (23:reg)); try (viac AGP (24:reg)); try (viac AGP (25:reg));
        try (viac AGP (26:reg)); try (viac AGP (27:reg)) ].
    destruct (er1e_run M13 rom S p T n r2 V2 V8 V9 V18 V19 V20 V21 V22 ltac:(hlia) GTw
                 ltac:(eapply store_ok_mono; [exact GR13 | exact Hstk]) ltac:(unfold hideR in GpT; xqh TSH Q13 C_cnt0) ltac:(unfold hideR in GpT; xqh TSH Q13 C_len0))
        as (r3 & RUN3 & B1 & B2 & B10 & B11 & B12 & B13 & B8 & B9 & B18 & B19 & B21 & B22 & B3 & B4 & B23 & B24 & B25 & B26 & B27).
    finish_r RUN1 RUN2 RUN3 M13 M12 AGP.
  Qed.

End RUN3R.

End FPGen.
End AsAllocFRun3R.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 AsAllocF5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N.AsAllocFRun3 AsAllocFRun3R OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Definition hideM (P : Prop) : Prop := P.

(* [comment removed for export] *)
Definition X2 (S p T m : Z) (z : Z) : Prop := Xd S p T z \/ (sh_lo p <= z < sh_hi p m).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P3R1MEM.
  Variables (memD : word -> option byte) (S p x22 : word) (T n n8 id : Z).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis GpT : hideM (U p + n8 <= T \/ T + 4096 <= U p - 16).
  Lemma TSB_P3R1MEM : hideW ((T + 4096 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= T)%Z).
  Proof using GT n8 p S. pose proof GT as X. unfold hideW in X |- *. lia. Qed.
  Lemma PSB_P3R1MEM : hideW ((U p + n8 <= 0x7fff7000)%Z \/ (0x10007fff8000 + 16 <= U p)%Z).
  Proof using Gp S. pose proof Gp as X. unfold hideW in X |- *. lia. Qed.
  #[local] Abbreviation M := (fr_P3r1 memD S p x22 T n n8 id).

  Lemma shlen8R : shlen (Z_to_bv 64 n8) = n8 / 8.
  Proof using Gn8 GT Gp T p S. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pd8R : 8 * (U p / 8) = U p /\ 8 * (n8 / 8) = n8 /\ AIMGHI / 8 <= U p / 8 /\ U p / 8 + n8 / 8 <= 2 ^ 44.
  Proof using Gn8 GT Gp GS T x22 S memD. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Ltac lsideR := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length, ?shlen8R; rewrite ?Z2Nat.id by lia;
                 (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold shad, at_ in G in change_no_check G' end); wd_ulia.
  Ltac shside := (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); rewrite ?repeat_length; unorm; rewrite ?Z2Nat.id by lia; rewrite ?at_u by lia;
                 (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ length] in G in change_no_check G' end); lia.
  Ltac digR := (lazymatch goal with |- ?G => let G' := eval unfold fr_P3r1, fr_enq, fr_PS, fr_c1, ps_frame in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end);
               repeat (first [ rd_hit8 | rewrite wc_rdn_wbytes_out3; [ | rd8_side ]
                             | rewrite wc_rdn_wbytes_out3; [ | shside ] ]).

  Lemma fr_P3r1_outside : forall a : word,
    (U a < U S - 2272 \/ U S - 2128 <= U a) -> (U a < U p \/ U p + 8 <= U a) ->
    (U a < SB + U p / 8 \/ SB + U p / 8 + n8 / 8 <= U a) -> M a = memD a.
  Proof using Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1.
    intros a A1 A2 A3. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold SB in *.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3r1, fr_enq, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by lsideR. reflexivity.
  Qed.
  Lemma fr_P3r1_foot : forall a : word, M a <> memD a ->
    (U S - 2272 <= U a < U S - 2128) \/ (U p <= U a < U p + 8) \/ (SB + U p / 8 <= U a < SB + U p / 8 + n8 / 8).
  Proof using Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1.
    intros a NE.
    destruct (decide (U S - 2272 <= U a < U S - 2128)); [tauto|].
    destruct (decide (U p <= U a < U p + 8)); [tauto|].
    destruct (decide (SB + U p / 8 <= U a < SB + U p / 8 + n8 / 8)); [tauto|].
    exfalso. apply NE. apply fr_P3r1_outside; lia.
  Qed.
  Lemma fr_P3r1_grows : mem_grows memD M.
  Proof using GT Gp. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. (lazymatch goal with |- ?G => let G' := eval unfold fr_P3r1, fr_enq, fr_PS, fr_c1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Lemma fr_P3r1_e0 : rdn ASEGS M (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x5008c)).           Proof using GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). digR. Qed.
  Lemma fr_P3r1_e1 : rdn ASEGS M (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (0x103f18 + 728))).  Proof using GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). digR. Qed.
  Lemma fr_P3r1_e2 : rdn ASEGS M (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80)).       Proof using GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). digR. Qed.
  Lemma fr_P3r1_e3 : rdn ASEGS M (at_ S (-2240)) 8 = Some (LE8 (Z_to_bv 64 n)).                 Proof using GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). digR. Qed.
  Lemma fr_P3r1_e4 : rdn ASEGS M (at_ S (-2248)) 8 = Some (LE8 (at_ S (-2128))).              Proof using GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). digR. Qed.
  Lemma fr_P3r1_e5 : rdn ASEGS M (at_ S (-2256)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)).      Proof using GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). digR. Qed.
  Lemma fr_P3r1_e6 : rdn ASEGS M (at_ S (-2264)) 8 = Some (LE8 (at_ p (-16))).                 Proof using GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). digR. Qed.
  (* [comment removed for export] *)
  Lemma fr_P3r1_q0 : rdn ASEGS M (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4)).           Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_q1 : rdn ASEGS M (at_ S (-2144)) 8 = Some (LE8 S).                              Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_q2 : rdn ASEGS M (at_ S (-2152)) 8 = Some (LE8 p).                              Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_q3 : rdn ASEGS M (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434)).           Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_q4 : rdn ASEGS M (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).                 Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_q5 : rdn ASEGS M (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).              Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_q6 : rdn ASEGS M (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81))).                Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_q7 : rdn ASEGS M (at_ S (-2192)) 8 = Some (LE8 x22).                            Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_cb0 : rdn ASEGS M (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)).      Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.
  Lemma fr_P3r1_cb1 : rdn ASEGS M (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128))).                Proof using GpT Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold hideM in GpT. digR. Qed.

  (* [comment removed for export] *)
  Lemma fr_P3r1_shadow : forall i, 0 <= i < n8 / 8 -> M (Z_to_bv 64 (SB + U p / 8 + i)) = Some (Z_to_bv 8 0xfd).
  Proof using Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1.
    intros i Hi. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. unfold SB in *.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_P3r1, fr_enq, fr_PS in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite !wbytes_outside by lsideR.
    rewrite wbytes_inside by lsideR.
    f_equal. rewrite nth_repeat_lt; [(lazymatch goal with |- ?G => let G' := eval unfold cbyte in G in change_no_check G' end); unorm; reflexivity|].
    rewrite shlen8R. (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). unorm. lia.
  Qed.
  Lemma fr_P3r1_hdr16 : M (at_ p (-16)) = memD (at_ p (-16)).
  Proof using Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. pose proof (u64_range S). pose proof (u64_range p). pose proof pd8R. apply fr_P3r1_outside; (lazymatch goal with |- ?G => let G' := eval unfold SB, at_ in G in change_no_check G' end); wd_ulia. Qed.
  (* [comment removed for export] *)
  Lemma fr_P3r1_rdn_out : forall (a : word) (k : nat),
    U a + Z.of_nat k <= 2 ^ 64 ->
    (U a + Z.of_nat k <= U S - 2272 \/ U S - 2128 <= U a) -> (U a + Z.of_nat k <= U p \/ U p + 8 <= U a) ->
    (U a + Z.of_nat k <= SB + U p / 8 \/ SB + U p / 8 + n8 / 8 <= U a) ->
    rdn ASEGS M a k = rdn ASEGS memD a k.
  Proof using Gn8 GT Gp GS. pose proof TSB_P3R1MEM as TSB1; unfold hideW in TSB1. pose proof PSB_P3R1MEM as PSB1; unfold hideW in PSB1. intros a k Hk A1 A2 A3. apply rdn_ext; [exact Hk|]. intros x Hx. apply fr_P3r1_outside; lia. Qed.
End P3R1MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section E2MEM2.
  Variables (MR : word -> option byte) (S p : word) (T n cnt k ba qb last len : Z) (bst bcs : list byte).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gp : AIMGHI + 16 <= U p /\ U p + 8 <= U S - 3584.   (* [comment removed for export] *)
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis Gba : 0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584.
  Hypothesis Glast : 0x10007fff8000 <= last /\ last + 8192 <= U S - 3584.
  Hypothesis GbaT : hideM (ba + 8192 <= T \/ T + 4096 <= ba).
  Hypothesis GlastT : hideM (last + 8192 <= T \/ T + 4096 <= last).
  Hypothesis Gbalast : hideM (last + 8192 <= ba \/ ba + 8192 <= last).
  Hypothesis Gbap : hideM (ba + 8192 <= U p - 16 \/ U p + 8 <= ba).
  Hypothesis Glastp : hideM (last + 8192 <= U p - 16 \/ U p + 8 <= last).
  Hypothesis GpT : hideM (U p + 8 <= T \/ T + 4096 <= U p - 16).
  Lemma TSB_E2MEM2 : hideW ((T + 4096 <= 0x7fff8000)%Z \/ (0x10007fff8000 <= T)%Z).
  Proof using GT S. pose proof GT as X. unfold hideW in X |- *. lia. Qed.
  #[local] Abbreviation Me := (fr_e2e MR S p T n cnt k ba qb bst bcs).
  #[local] Abbreviation Mf := (fr_e2f MR S p T n cnt k ba qb last len bst bcs).
  Ltac lside2 := wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac dig2 := (lazymatch goal with |- ?G => let G' := eval unfold fr_e2e, fr_e2f in G in change_no_check G' end); repeat (wd_rdstep rd8_side).

  Lemma fr_e2e_outside : forall a : word,
    (U a < ba \/ ba + 32 <= U a) -> (U a < T + 80 \/ T + 112 <= U a) ->
    (U a < T + 2128 \/ T + 2132 <= U a) -> (U a < T + 2784 \/ T + 2792 <= U a) -> Me a = MR a.
  Proof using Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1.
    intros a A1 A2 A3 A4. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_e2e in G in change_no_check G' end).
    rewrite !wbytes_outside by lside2. reflexivity.
  Qed.
  Lemma fr_e2e_foot : forall a : word, Me a <> MR a ->
    (ba <= U a < ba + 32) \/ (T + 80 <= U a < T + 112) \/ (T + 2128 <= U a < T + 2132) \/ (T + 2784 <= U a < T + 2792).
  Proof using Glast Gba GT Gp GS last. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1.
    intros a NE.
    destruct (decide (ba <= U a < ba + 32)); [tauto|].
    destruct (decide (T + 80 <= U a < T + 112)); [tauto|].
    destruct (decide (T + 2128 <= U a < T + 2132)); [tauto|].
    destruct (decide (T + 2784 <= U a < T + 2792)); [tauto|].
    exfalso. apply NE. apply fr_e2e_outside; lia.
  Qed.
  Lemma fr_e2f_outside : forall a : word,
    (U a < ba \/ ba + 32 <= U a) -> (U a < T + 80 \/ T + 112 <= U a) ->
    (U a < T + 2128 \/ T + 2132 <= U a) -> (U a < T + 2784 \/ T + 2792 <= U a) -> (U a < last \/ last + 8 <= U a) -> Mf a = MR a.
  Proof using Glast Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1.
    intros a A1 A2 A3 A4 A5. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold fr_e2f in G in change_no_check G' end).
    rewrite !wbytes_outside by lside2. reflexivity.
  Qed.
  Lemma fr_e2f_foot : forall a : word, Mf a <> MR a ->
    (ba <= U a < ba + 32) \/ (T + 80 <= U a < T + 112) \/ (T + 2128 <= U a < T + 2132) \/ (T + 2784 <= U a < T + 2792)
    \/ (last <= U a < last + 8).
  Proof using Glast Gba GT Gp GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1.
    intros a NE.
    destruct (decide (ba <= U a < ba + 32)); [tauto|].
    destruct (decide (T + 80 <= U a < T + 112)); [tauto|].
    destruct (decide (T + 2128 <= U a < T + 2132)); [tauto|].
    destruct (decide (T + 2784 <= U a < T + 2792)); [tauto|].
    destruct (decide (last <= U a < last + 8)); [tauto|].
    exfalso. apply NE. apply fr_e2f_outside; lia.
  Qed.

  Lemma fr_e2e_b0 : rdn ASEGS Me (Z_to_bv 64 ba) 8 = Some (LE8 (Z_to_bv 64 0)).                  Proof using GbaT Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GbaT. dig2. Qed.
  Lemma fr_e2e_b8 : rdn ASEGS Me (Z_to_bv 64 (ba + 8)) 8 = Some (LE8 (Z_to_bv 64 (n + 8192))).     Proof using GbaT Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GbaT. dig2. Qed.
  Lemma fr_e2e_b16 : rdn ASEGS Me (Z_to_bv 64 (ba + 16)) 8 = Some (LE8 (Z_to_bv 64 1)).            Proof using GbaT Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GbaT. dig2. Qed.
  Lemma fr_e2e_b24 : rdn ASEGS Me (Z_to_bv 64 (ba + 24)) 8 = Some (LE8 (at_ p (-16))).             Proof using GbaT Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GbaT. dig2. Qed.
  Lemma fr_e2e_q80 : rdn ASEGS Me (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 1)).             Proof using GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). dig2. Qed.
  Lemma fr_e2e_q88 : rdn ASEGS Me (Z_to_bv 64 (T + 88)) 8 = Some (LE8 (Z_to_bv 64 ba)).            Proof using GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). dig2. Qed.
  Lemma fr_e2e_q96 : rdn ASEGS Me (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 ba)).            Proof using GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). dig2. Qed.
  Lemma fr_e2e_cnt : rdn ASEGS Me (Z_to_bv 64 (T + 2128)) 4 = Some (LE4 (cnt - 1)).
  Proof using GbaT Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1.
    pose proof (u64_range S). unfold hideM in GbaT. (lazymatch goal with |- ?G => let G' := eval unfold fr_e2e in G in change_no_check G' end).
    repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]).
    pose proof (rdn_wbytes_hit ASEGS (LE4 (cnt - 1))) as Hh. rewrite length_N_to_le_bytes in Hh. apply Hh. unorm. lia.
  Qed.
  Lemma fr_e2f_b0 : rdn ASEGS Mf (Z_to_bv 64 ba) 8 = Some (LE8 (Z_to_bv 64 0)).                  Proof using Gbalast GbaT Glast Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GbaT, Gbalast. dig2. Qed.
  Lemma fr_e2f_b8 : rdn ASEGS Mf (Z_to_bv 64 (ba + 8)) 8 = Some (LE8 (Z_to_bv 64 (n + 8192))).     Proof using Gbalast GbaT Glast Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GbaT, Gbalast. dig2. Qed.
  Lemma fr_e2f_b16 : rdn ASEGS Mf (Z_to_bv 64 (ba + 16)) 8 = Some (LE8 (Z_to_bv 64 1)).            Proof using Gbalast GbaT Glast Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GbaT, Gbalast. dig2. Qed.
  Lemma fr_e2f_b24 : rdn ASEGS Mf (Z_to_bv 64 (ba + 24)) 8 = Some (LE8 (at_ p (-16))).             Proof using Gbalast GbaT Glast Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GbaT, Gbalast. dig2. Qed.
  Lemma fr_e2f_q80 : rdn ASEGS Mf (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 (len + 1))).     Proof using GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). dig2. Qed.
  Lemma fr_e2f_q96 : rdn ASEGS Mf (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 ba)).            Proof using GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). dig2. Qed.
  Lemma fr_e2f_last : rdn ASEGS Mf (Z_to_bv 64 last) 8 = Some (LE8 (Z_to_bv 64 ba)).               Proof using GlastT Glast GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). unfold hideM in GlastT. dig2. Qed.
  Lemma fr_e2f_cnt : rdn ASEGS Mf (Z_to_bv 64 (T + 2128)) 4 = Some (LE4 (cnt - 1)).
  Proof using GlastT GbaT Glast Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1.
    pose proof (u64_range S). unfold hideM in GbaT, GlastT. (lazymatch goal with |- ?G => let G' := eval unfold fr_e2f in G in change_no_check G' end).
    repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]).
    pose proof (rdn_wbytes_hit ASEGS (LE4 (cnt - 1))) as Hh. rewrite length_N_to_le_bytes in Hh. apply Hh. unorm. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fr_e2f_first : forall a : word, T + 88 <= U a < T + 96 -> Mf a = MR a.
  Proof using GlastT GbaT Glast Gba GT GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1.
    intros a Ha. pose proof (u64_range S). unfold hideM in GbaT, GlastT. (lazymatch goal with |- ?G => let G' := eval unfold fr_e2f in G in change_no_check G' end).
    rewrite !wbytes_outside by lside2. reflexivity.
  Qed.
  Lemma fr_e2e_hdr16 : Me (at_ p (-16)) = MR (at_ p (-16)).
  Proof using GpT Gbap Gba GT Gp GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideM in Gbap, GpT. apply fr_e2e_outside; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia. Qed.
  Lemma fr_e2f_hdr16 : Mf (at_ p (-16)) = MR (at_ p (-16)).
  Proof using GpT Glastp Gbap Glast Gba GT Gp GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). pose proof (u64_range p). unfold hideM in Gbap, Glastp, GpT. apply fr_e2f_outside; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pdiv8R : 0 <= U p / 8 <= 2 ^ 44.
  Proof using GT Gp GS T S MR. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma fr_e2e_shad : forall i, 0 <= i -> U p / 8 + i < 2 ^ 44 -> Me (Z_to_bv 64 (SB + U p / 8 + i)) = MR (Z_to_bv 64 (SB + U p / 8 + i)).
  Proof using Gba GT Gp GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. intros i Hi Hi2. pose proof pdiv8R. apply fr_e2e_outside; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); wd_ulia. Qed.
  Lemma fr_e2f_shad : forall i, 0 <= i -> U p / 8 + i < 2 ^ 44 -> Mf (Z_to_bv 64 (SB + U p / 8 + i)) = MR (Z_to_bv 64 (SB + U p / 8 + i)).
  Proof using Glast Gba GT Gp GS. pose proof TSB_E2MEM2 as TSB1; unfold hideW in TSB1. intros i Hi Hi2. pose proof pdiv8R. apply fr_e2f_outside; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); wd_ulia. Qed.
End E2MEM2.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8p.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma land_m18 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 18) = (a - a mod 2 ^ 18)%Z.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 2 ^ 18)%Z with (Z.ldiff (Z.ones 64) (Z.ones 18)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2 ^ 18) ltac:(lia)). lia.
Qed.
Lemma Z2bv_plus64 : forall a, Z_to_bv 64 (a + 2 ^ 64) = Z_to_bv 64 a.
Proof.
  intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  replace (a + 2 ^ 64)%Z with (a + 1 * 2 ^ 64)%Z by lia. apply Z.mod_add. lia.
Qed.
Lemma v_and_m18 : forall x : word,
  v_and x (Z_to_bv 64 (2 ^ 64 - 2 ^ 18)) = Z_to_bv 64 (bv_unsigned x - bv_unsigned x mod 2 ^ 18).
Proof.
  intros x. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite (u_Z2bv (2 ^ 64 - 2 ^ 18)) by lia.
  rewrite land_m18 by lia. reflexivity.
Qed.

Lemma step_and_at' : forall {fx : FPState} segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_and (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Ltac av_and F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_and_at' with (v := vv); [ exact F | reflexivity | exact D | reflexivity | gres; rwH; imm_norm; tac ]
  | step_simpl ]; vn.

Section FPGen.
Context {fx : FPState}.

Definition pf_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-48)) (LE8 s4v))
    (at_ sp (-56)) (LE8 s5v))
    (at_ sp (-64)) (LE8 s6v).
#[local] Hint Unfold pf_m0 : asfr.

(* [comment removed for export] *)
Definition pf_regs (sp : word) (RIz SPB c : Z) (r : bvmap 5 word) : Prop :=
  getr r 2 = at_ sp (-64) /\ getr r 8 = Z_to_bv 64 RIz
  /\ getr r 18 = Z_to_bv 64 (SPB + c * 2 ^ 32) /\ getr r 21 = Z_to_bv 64 (csize c).

Section HEAD.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v stats : word) (RIz SPB c req au mu : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 RIz.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 req.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hreq : (1 <= req /\ csize c * req <= 2 ^ 18)%Z.
  Hypothesis Hau : (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-64)) 64 = true.
  Hypothesis C_sbeg : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis R_au : rdn ASEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn ASEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).

  #[local] Abbreviation M0 := (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).

  Ltac pf_prologue :=
      an F_50dcc D_50dcc;                              (* [comment removed for export] *)
      fsd F_50dd0 D_50dd0 (at_ sp (-8));               (* [comment removed for export] *)
      fsd F_50dd4 D_50dd4 (at_ sp (-16));              (* [comment removed for export] *)
      fsd F_50dd8 D_50dd8 (at_ sp (-24));              (* [comment removed for export] *)
      fsd F_50ddc D_50ddc (at_ sp (-32));              (* [comment removed for export] *)
      fsd F_50de0 D_50de0 (at_ sp (-40));              (* [comment removed for export] *)
      fsd F_50de4 D_50de4 (at_ sp (-48));              (* [comment removed for export] *)
      fsd F_50de8 D_50de8 (at_ sp (-56));              (* [comment removed for export] *)
      fsd F_50dec D_50dec (at_ sp (-64));              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0;
      an F_50df0 D_50df0;                              (* [comment removed for export] *)
      an F_50df4 D_50df4;                              (* [comment removed for export] *)
      cld8 F_50df8 D_50df8 (Z_to_bv 64 SPB) C_sbeg;    (* [comment removed for export] *)
      an F_50dfc D_50dfc;                              (* [comment removed for export] *)
      av F_50e00 D_50e00 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia);   (* [comment removed for export] *)
      ab_ft F_50e04 D_50e04 ltac:(condz);              (* [comment removed for export] *)
      an F_50e08 D_50e08.                              (* [comment removed for export] *)

  Ltac pf_lo :=
      pf_prologue;
      ab_ft F_50e0c D_50e0c ltac:(condz);              (* [comment removed for export] *)
      av F_50e10 D_50e10 (Z_to_bv 64 (csize c)) ltac:(apply csize_small; lia);   (* [comment removed for export] *)
      cld8 F_50e14 D_50e14 (Z_to_bv 64 au) R_au;       (* [comment removed for export] *)
      cld8 F_50e18 D_50e18 (Z_to_bv 64 mu) R_mu;       (* [comment removed for export] *)
      av F_50e1c D_50e1c (Z_to_bv 64 (csize c * req)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av F_50e20 D_50e20 (Z_to_bv 64 (au + csize c * req)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av F_50e24 D_50e24 (Z_to_bv 64 (SPB + c * 2 ^ 32)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
  Ltac pf_hi :=
      pf_prologue;
      ab_tk F_50e0c D_50e0c ltac:(condz);              (* [comment removed for export] *)
      an F_50e30 D_50e30;                              (* [comment removed for export] *)
      an F_50e34 D_50e34;                              (* [comment removed for export] *)
      an F_50e38 D_50e38;                              (* [comment removed for export] *)
      an F_50e3c D_50e3c;                              (* [comment removed for export] *)
      an F_50e40 D_50e40;                              (* [comment removed for export] *)
      an F_50e44 D_50e44;                              (* [comment removed for export] *)
      an F_50e48 D_50e48;                              (* [comment removed for export] *)
      an F_50e4c D_50e4c;                              (* [comment removed for export] *)
      av F_50e50 D_50e50 (Z_to_bv 64 (csize c)) ltac:(exact (csize_big c ltac:(lia)));   (* [comment removed for export] *)
      cld8 F_50e54 D_50e54 (Z_to_bv 64 au) R_au;       (* [comment removed for export] *)
      cld8 F_50e58 D_50e58 (Z_to_bv 64 mu) R_mu;       (* [comment removed for export] *)
      av F_50e5c D_50e5c (Z_to_bv 64 (csize c * req)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av F_50e60 D_50e60 (Z_to_bv 64 (au + csize c * req)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av F_50e64 D_50e64 (Z_to_bv 64 (SPB + c * 2 ^ 32)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)

  Definition pf_clob : list reg := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31].

  (* [comment removed for export] *)
  Lemma pf_head_map : (mu < au + csize c * req)%Z ->
    exists r, msteps ASEGS (mkst regs (0x50dd4 : word) mem rom) (mkst r (0x50e74 : word) M0 rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 9 = stats /\ getr r 10 = Z_to_bv 64 0x103f18 /\ getr r 12 = Z_to_bv 64 c
      /\ getr r 19 = Z_to_bv 64 (au + csize c * req) /\ getr r 20 = Z_to_bv 64 mu
      /\ regs_agree (fun i : reg => In i pf_clob) regs r.
  Proof using R_mu R_au C_sbeg Hstk HRI HSPB Hau Hreq Hc Hsp H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H2 H1.
    intros Hmap. (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (csize_pos c Hc) as [Hcs1 Hcs2].
    destruct (Z_le_gt_dec c 16) as [Hlo | Hhi].
    - wd_eexists. split.
      + pf_lo.
        ab_tk F_50e28 D_50e28 ltac:(condz).            (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
    - wd_eexists. split.
      + pf_hi.
        ab_ft F_50e68 D_50e68 ltac:(condz).            (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_head_nomap : (au + csize c * req <= mu)%Z ->
    exists r, msteps ASEGS (mkst regs (0x50dd4 : word) mem rom) (mkst r (0x50f48 : word) M0 rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 10 = Z_to_bv 64 0x103f18
      /\ getr r 13 = Z_to_bv 64 au /\ getr r 20 = Z_to_bv 64 mu
      /\ regs_agree (fun i : reg => In i pf_clob) regs r.
  Proof using R_mu R_au C_sbeg Hstk HRI HSPB Hau Hreq Hc Hsp H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H2 H1 stats.
    intros Hmap. (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (csize_pos c Hc) as [Hcs1 Hcs2].
    destruct (Z_le_gt_dec c 16) as [Hlo | Hhi].
    - wd_eexists. split.
      + pf_lo.
        ab_ft F_50e28 D_50e28 ltac:(condz).            (* [comment removed for export] *)
        an F_50e2c D_50e2c.                            (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
    - wd_eexists. split.
      + pf_hi.
        ab_tk F_50e68 D_50e68 ltac:(condz).            (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
  Qed.
End HEAD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MAP.
  Variables (mem rom : word -> option byte) (sp stats : word) (RIz SPB c tot mu : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : pf_regs sp RIz SPB c regs.
  Hypothesis H9 : getr regs 9 = stats.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 tot.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 mu.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Htot : (mu < tot /\ tot <= mu + 2 ^ 18)%Z.
  Hypothesis Hmu : (0 <= mu /\ mu + 2 ^ 18 <= 0xE0000000)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis C_rel : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 40)) 4 = Some (LE4 0xffffffff).
  Hypothesis C_pre : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis R_mm : rdn ASEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)).

  Ltac pf_maptail :=
      av F_50e70 D_50e70 (Z_to_bv 64 (2 ^ 64 - 1 - mu)) ltac:(apply v_not_lit; lia);   (* [comment removed for export] *)
      an F_50e74 D_50e74;                              (* [comment removed for export] *)
      av F_50e78 D_50e78 (Z_to_bv 64 (tot - mu - 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; rewrite <- (Z2bv_plus64 (tot - mu - 1)); f_equal; lia);   (* [comment removed for export] *)
      an F_50e7c D_50e7c;                              (* [comment removed for export] *)
      av_and F_50e80 D_50e80 (Z_to_bv 64 0)
        ltac:(match goal with |- v_and _ ?X = _ => replace X with (Z_to_bv 64 (2 ^ 64 - 2 ^ 18)) by (apply bv_eq; vm_compute; reflexivity) end;
              rewrite v_and_m18; unorm; f_equal; rewrite Z.mod_small by lia; lia);   (* [comment removed for export] *)
      cld8 F_50e84 D_50e84 (Z_to_bv 64 0) R_mm;        (* [comment removed for export] *)
      av F_50e88 D_50e88 (Z_to_bv 64 (2 ^ 18)) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      an F_50e8c D_50e8c;                              (* [comment removed for export] *)
      av F_50e90 D_50e90 (Z_to_bv 64 0xE0000000) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      av F_50e94 D_50e94 (Z_to_bv 64 mu) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);   (* [comment removed for export] *)
      av F_50e98 D_50e98 (Z_to_bv 64 (mu + 2 ^ 18)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);   (* [comment removed for export] *)
      av F_50e9c D_50e9c (Z_to_bv 64 0xE0000001) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      ab_ft F_50ea0 D_50ea0 ltac:(condz);              (* [comment removed for export] *)
      clbu F_50ea4 D_50ea4 (Z_to_bv 8 0) C_pre;        (* [comment removed for export] *)
      av F_50ea8 D_50ea8 (Z_to_bv 64 (SPB + c * 2 ^ 32 + mu)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);   (* [comment removed for export] *)
      ab_tk F_50eac D_50eac ltac:(condz);              (* [comment removed for export] *)
      an F_50ed4 D_50ed4;                              (* [comment removed for export] *)
      av F_50ed8 D_50ed8 (Z_to_bv 64 0x17990) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      an F_50edc D_50edc;                              (* [comment removed for export] *)
      an F_50ee0 D_50ee0;                              (* [comment removed for export] *)
      an F_50ee4 D_50ee4;                              (* [comment removed for export] *)
      an F_50ee8 D_50ee8.                              (* [comment removed for export] *)

  Lemma le4_m1 : bytes_le_to_Z (LE4 0xffffffff) = U (Z_to_bv 64 0xffffffff).
  Proof using. vm_compute. reflexivity. Qed.

  Lemma pf_map :
    exists r, msteps ASEGS (mkst regs (0x50e74 : word) mem rom) (mkst r (0x8a688 : word) mem rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 9 = stats /\ getr r 1 = Z_to_bv 64 0x50ef4
      /\ getr r 11 = Z_to_bv 64 (SPB + c * 2 ^ 32 + mu) /\ getr r 12 = Z_to_bv 64 (2 ^ 18) /\ getr r 13 = Z_to_bv 64 0x17990
      /\ getr r 19 = Z_to_bv 64 (2 ^ 18) /\ getr r 20 = Z_to_bv 64 (SPB + c * 2 ^ 32 + mu) /\ getr r 22 = Z_to_bv 64 0x103f18
      /\ regs_agree (fun i : reg => In i pf_clob) regs r.
  Proof using R_mm C_pre C_rel HRI HSPB Hmu Htot Hc Hsp H20 H19 H10 H9 HR tot.
    destruct HR as (R2 & R8 & R18 & R21). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    destruct (Z.eq_dec mu 0) as [Ez | Nz].
    - wd_eexists. split.
      + ab_tk F_50e6c D_50e6c ltac:(condz).            (* [comment removed for export] *)
        clw F_51028 D_51028 (LE4 0xffffffff) (Z_to_bv 64 0xffffffff) C_rel le4_m1.   (* [comment removed for export] *)
        ab_tk F_5102c D_5102c ltac:(first [condz | vm_compute; reflexivity]).   (* [comment removed for export] *)
        an F_510f0 D_510f0.                            (* [comment removed for export] *)
        an F_510f4 D_510f4.                            (* [comment removed for export] *)
        replace (Z_to_bv 64 0) with (Z_to_bv 64 mu) by (rewrite Ez; reflexivity).
        pf_maptail.
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
    - wd_eexists. split.
      + ab_ft F_50e6c D_50e6c ltac:(condz).            (* [comment removed for export] *)
        pf_maptail.
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
  Qed.
End MAP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MAPPED.
  Variables (mem rom : word -> option byte) (sp : word) (RIz SPB c slot : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : pf_regs sp RIz SPB c regs.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (2 ^ 18).
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 slot.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hslot : (0 < slot < 2 ^ 64)%Z.

  (* [comment removed for export] *)
  Lemma pf_mapped : getr regs 10 = Z_to_bv 64 slot ->
    exists r, msteps ASEGS (mkst regs (0x50ef4 : word) mem rom) (mkst r (0x6f610 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x50f10 /\ getr r 10 = Z_to_bv 64 slot /\ getr r 11 = Z_to_bv 64 (2 ^ 18) /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12; 14]) regs r.
  Proof using Hslot H20 H19 HR c SPB RIz sp.
    intros H10. destruct HR as (R2 & R8 & R18 & R21). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_ft F_50eec D_50eec ltac:(condz).              (* [comment removed for export] *)
      an F_50ef0 D_50ef0.                              (* [comment removed for export] *)
      ab_ft F_50ef4 D_50ef4 ltac:(condz).              (* [comment removed for export] *)
      an F_50ef8 D_50ef8.                              (* [comment removed for export] *)
      an F_50efc D_50efc.                              (* [comment removed for export] *)
      an F_50f00 D_50f00.                              (* [comment removed for export] *)
      an F_50f04 D_50f04.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End MAPPED.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FAIL.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-64).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn ASEGS M (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn ASEGS M (at_ sp (-64)) 8 = Some (LE8 s6v).

  Ltac pf_epi :=
      an F_50fdc D_50fdc;                              (* [comment removed for export] *)
      cld8 F_50fe0 D_50fe0 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_50fe4 D_50fe4 s0v S_s0;                   (* [comment removed for export] *)
      cld8 F_50fe8 D_50fe8 s1v S_s1;                   (* [comment removed for export] *)
      cld8 F_50fec D_50fec s2v S_s2;                   (* [comment removed for export] *)
      cld8 F_50ff0 D_50ff0 s3v S_s3;                   (* [comment removed for export] *)
      cld8 F_50ff4 D_50ff4 s4v S_s4;                   (* [comment removed for export] *)
      cld8 F_50ff8 D_50ff8 s5v S_s5;                   (* [comment removed for export] *)
      cld8 F_50ffc D_50ffc s6v S_s6;                   (* [comment removed for export] *)
      an F_51000 D_51000;                              (* [comment removed for export] *)
      aret F_51004 D_51004 ra.                         (* [comment removed for export] *)

  Definition pf_post0 (r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 0 /\ getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = s6v
    /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22]) regs r.

  (* [comment removed for export] *)
  Lemma pf_fail_map : exists r, msteps ASEGS (mkst regs (0x50ef4 : word) M rom) (mkst r ra M rom) /\ pf_post0 r.
  Proof using S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hret H10 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold pf_post0 in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_50eec D_50eec ltac:(condz).              (* [comment removed for export] *)
      an F_5105c D_5105c.                              (* [comment removed for export] *)
      an F_51060 D_51060.                              (* [comment removed for export] *)
      pf_epi.
      wd_refl.
    - post. ra_solve.
  Qed.
  (* [comment removed for export] *)
  Lemma pf_fail_efs : exists r, msteps ASEGS (mkst regs (0x50f68 : word) M rom) (mkst r ra M rom) /\ pf_post0 r.
  Proof using S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hret H10 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold pf_post0 in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_50f60 D_50f60 ltac:(condz).              (* [comment removed for export] *)
      an F_5105c D_5105c.                              (* [comment removed for export] *)
      an F_51060 D_51060.                              (* [comment removed for export] *)
      pf_epi.
      wd_refl.
    - post. ra_solve.
  Qed.
End FAIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pf_ms (M : word -> option byte) (thr : word) (RIz mu : Z) (v72 v80 vst : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes M
    (at_ thr 2872) (LE8 (v_addi v72 1)))
    (at_ thr 2880) (LE8 (v_add v80 (Z_to_bv 64 (2 ^ 18)))))
    (at_ thr 2792) (LE8 (v_add vst (Z_to_bv 64 (2 ^ 18)))))
    (Z_to_bv 64 (RIz + 48)) (LE8 (Z_to_bv 64 (mu + 2 ^ 18))).
#[local] Hint Unfold pf_ms : asfr.

Section STATS.
  Variables (M rom : word -> option byte) (sp thr v72 v80 vst : word) (RIz SPB c au mu T : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : pf_regs sp RIz SPB c regs.
  Hypothesis H9 : getr regs 9 = at_ thr 2768.
  Hypothesis H10 : getr regs 10 = at_ thr 2800.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (2 ^ 18).
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 0x103f18.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hau : (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 64 /\ T mod 8 = 0)%Z.
  Hypothesis HTRI : (T + 4096 <= RIz \/ RIz + 128 <= T)%Z.
  Hypothesis R_72 : rdn ASEGS M (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn ASEGS M (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis R_st : rdn ASEGS M (at_ thr 2792) 8 = Some (LE8 vst).
  Hypothesis R_au : rdn ASEGS M (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn ASEGS M (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis SOK_T : store_ok ASEGS M thr 4096 = true.
  Hypothesis SOK_RI : store_ok ASEGS M (Z_to_bv 64 RIz) 128 = true.

  Lemma pf_stats :
    exists r, msteps ASEGS (mkst regs (0x50f14 : word) M rom) (mkst r (0x50f48 : word) (pf_ms M thr RIz mu v72 v80 vst) rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 10 = Z_to_bv 64 0x103f18
      /\ getr r 13 = Z_to_bv 64 au /\ getr r 20 = Z_to_bv 64 (mu + 2 ^ 18)
      /\ regs_agree (fun i : reg => In i [9; 10; 11; 12; 13; 20]) regs r.
  Proof using SOK_RI SOK_T R_mu R_au R_st R_80 R_72 HTRI HT HRI Hau Hsp H22 H19 H10 H9 HR T.
    destruct HR as (R2 & R8 & R18 & R21). destruct HT as (UT & T1 & T2 & T3). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - cld8 F_50f0c D_50f0c v72 R_72.                   (* [comment removed for export] *)
      cld8 F_50f10 D_50f10 v80 R_80.                   (* [comment removed for export] *)
      an F_50f14 D_50f14.                              (* [comment removed for export] *)
      an F_50f18 D_50f18.                              (* [comment removed for export] *)
      fsd F_50f1c D_50f1c (at_ thr 2872).              (* [comment removed for export] *)
      fsd F_50f20 D_50f20 (at_ thr 2880).              (* [comment removed for export] *)
      an F_50f24 D_50f24.                              (* [comment removed for export] *)
      av F_50f28 D_50f28 (at_ thr 2792) ltac:(change (v_addi (at_ thr 2768) 24) with (at_ (at_ thr 2768) 24); rewrite at_at; reflexivity).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 vst) (v := vst);
          [exact F_50f2c | reflexivity | exact D_50f2c
          | gres; rwH; rewrite at_u by lia; rewrite UT; rewrite <- Zplus_mod_idemp_l, T3; reflexivity
          | gres; rwH; rd_peel; exact R_st
          | apply bytes_le_to_Z_8
          | gres; rwH; any_ok ]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      cld8 F_50f30 D_50f30 (Z_to_bv 64 mu) R_mu.       (* [comment removed for export] *)
      cld8 F_50f34 D_50f34 (Z_to_bv 64 au) R_au.       (* [comment removed for export] *)
      av F_50f38 D_50f38 (Z_to_bv 64 (mu + 2 ^ 18)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      fsd F_50f3c D_50f3c (Z_to_bv 64 (RIz + 48)).     (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End STATS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section EFSCALL.
  Variables (M rom : word -> option byte) (sp : word) (RIz SPB c au mu nf : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : pf_regs sp RIz SPB c regs.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 au.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 mu.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hau : (0 <= au <= mu /\ mu <= 0xE0000000)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis R_nf : rdn ASEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).

  #[local] Abbreviation newn := ((mu - au) / csize c)%Z.

  Lemma pf_efs_call :
    exists r, msteps ASEGS (mkst regs (0x50f48 : word) M rom) (mkst r (0x4ea98 : word) M rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 1 = Z_to_bv 64 0x50f68
      /\ getr r 10 = Z_to_bv 64 0x103f18 /\ getr r 11 = Z_to_bv 64 RIz /\ getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32)
      /\ getr r 13 = Z_to_bv 64 (nf + newn)
      /\ getr r 9 = Z_to_bv 64 (nf + newn) /\ getr r 19 = Z_to_bv 64 newn /\ getr r 20 = Z_to_bv 64 (mu - au)
      /\ regs_agree (fun i : reg => In i [1; 9; 11; 12; 13; 19; 20]) regs r.
  Proof using R_nf HRI Hnf Hau Hc Hsp H20 H13 H10 HR.
    destruct HR as (R2 & R8 & R18 & R21). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    pose proof (csize_pos c Hc) as [Hcs1 Hcs2].
    assert (Hnn : (0 <= newn <= 0xE0000000)%Z).
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia. }
    wd_eexists. split.
    - cld8 F_50f40 D_50f40 (Z_to_bv 64 nf) R_nf.       (* [comment removed for export] *)
      av F_50f44 D_50f44 (Z_to_bv 64 (mu - au)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      an F_50f48 D_50f48; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] |].   (* [comment removed for export] *)
      match goal with |- context [v_divu ?a ?b] =>
        replace (v_divu a b) with (Z_to_bv 64 newn)
          by (symmetry; apply bv_eq; rewrite v_divu_small by (wd_ulia); unorm; reflexivity) end.
      av F_50f4c D_50f4c (Z_to_bv 64 (nf + newn)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      an F_50f50 D_50f50.                              (* [comment removed for export] *)
      an F_50f54 D_50f54.                              (* [comment removed for export] *)
      an F_50f58 D_50f58.                              (* [comment removed for export] *)
      an F_50f5c D_50f5c.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End EFSCALL.
End FPGen.
End AsAllocM8p.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition efs_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v).
#[local] Hint Unfold efs_m0 : asfr.

Definition efs_post (sp ra s0v s1v s2v s3v : word) (res : Z) (regs r : bvmap 5 word) : Prop :=
  getr r 10 = Z_to_bv 64 res /\ getr r 2 = sp /\ getr r 1 = ra
  /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
  /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19]) regs r.

Section HEAD.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v : word) (RIz rbeg tot mfa : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 RIz.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 rbeg.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 tot.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v. Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Htot : (0 <= tot /\ 4 * tot <= 2 ^ 29)%Z.
  Hypothesis Hmfa : (0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0)%Z.
  Hypothesis Hrbeg : (0 <= rbeg /\ rbeg + 2 ^ 32 < 2 ^ 64)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 48)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-48)) 48 = true.
  Hypothesis R_mfa : rdn ASEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_pre : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 56)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).

  Ltac efs_prologue :=
      an F_4ea90 D_4ea90;                              (* [comment removed for export] *)
      fsd F_4ea94 D_4ea94 (at_ sp (-8));               (* [comment removed for export] *)
      fsd F_4ea98 D_4ea98 (at_ sp (-16));              (* [comment removed for export] *)
      fsd F_4ea9c D_4ea9c (at_ sp (-24));              (* [comment removed for export] *)
      fsd F_4eaa0 D_4eaa0 (at_ sp (-32));              (* [comment removed for export] *)
      fsd F_4eaa4 D_4eaa4 (at_ sp (-40));              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0;
      cld8 F_4eaa8 D_4eaa8 (Z_to_bv 64 mfa) R_mfa;     (* [comment removed for export] *)
      av F_4eaac D_4eaac (Z_to_bv 64 (4 * tot)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia);   (* [comment removed for export] *)
      an F_4eab0 D_4eab0.                              (* [comment removed for export] *)

  Ltac efs_epi :=
      an F_4eb74 D_4eb74;                              (* [comment removed for export] *)
      fld F_4eb78 D_4eb78 ra;                          (* [comment removed for export] *)
      fld F_4eb7c D_4eb7c s0v;                         (* [comment removed for export] *)
      fld F_4eb80 D_4eb80 s1v;                         (* [comment removed for export] *)
      fld F_4eb84 D_4eb84 s2v;                         (* [comment removed for export] *)
      fld F_4eb88 D_4eb88 s3v;                         (* [comment removed for export] *)
      an F_4eb8c D_4eb8c;                              (* [comment removed for export] *)
      aret F_4eb90 D_4eb90 ra.                         (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma efs_enough : (4 * tot <= mfa)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4ea98 : word) mem rom) (mkst r ra M0 rom) /\ efs_post sp ra s0v s1v s2v s3v 1 regs r.
  Proof using R_mfa Hstk HRI Hmfa Htot Hret Hsp H19 H18 H9 H8 H13 H11 H2 H1 RIz.
    intros Hen. (lazymatch goal with |- ?G => let G' := eval unfold efs_post in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - efs_prologue.
      ab_tk F_4eab4 D_4eab4 ltac:(condz).              (* [comment removed for export] *)
      efs_epi.
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma efs_map : (mfa < 4 * tot <= mfa + 2 ^ 18)%Z -> (mfa + 2 ^ 18 <= 2 ^ 29)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4ea98 : word) mem rom) (mkst r (0x8a688 : word) M0 rom)
      /\ getr r 1 = Z_to_bv 64 0x4eb38 /\ getr r 2 = at_ sp (-48)
      /\ getr r 11 = Z_to_bv 64 (rbeg + 0xE0000000 + mfa) /\ getr r 12 = Z_to_bv 64 (2 ^ 18) /\ getr r 13 = Z_to_bv 64 0x19801
      /\ getr r 8 = Z_to_bv 64 (mfa + 2 ^ 18) /\ getr r 9 = Z_to_bv 64 (rbeg + 0xE0000000 + mfa) /\ getr r 18 = Z_to_bv 64 (2 ^ 18)
      /\ getr r 19 = Z_to_bv 64 RIz
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19]) regs r.
  Proof using C_pre R_mfa Hstk HRI Hrbeg Hmfa Htot Hsp H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    intros Hneed Hroom. pose proof (u64_range sp) as Hspr. destruct Hmfa as [Hm1 Hm2].
    wd_eexists. split.
    - efs_prologue.
      ab_ft F_4eab4 D_4eab4 ltac:(condz).              (* [comment removed for export] *)
      an F_4eab8 D_4eab8.                              (* [comment removed for export] *)
      av F_4eabc D_4eabc (Z_to_bv 64 0x3ffff) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_4eac0 D_4eac0 (Z_to_bv 64 (4 * tot + 0x3ffff)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      an F_4eac4 D_4eac4.                              (* [comment removed for export] *)
      av_and F_4eac8 D_4eac8 (Z_to_bv 64 (mfa + 2 ^ 18))
        ltac:(match goal with |- v_and _ ?X = _ => replace X with (Z_to_bv 64 (2 ^ 64 - 2 ^ 18)) by (apply bv_eq; vm_compute; reflexivity) end;
              rewrite v_and_m18; unorm; f_equal; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      an F_4eacc D_4eacc.                              (* [comment removed for export] *)
      av F_4ead0 D_4ead0 (Z_to_bv 64 0x20000001) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4ead4 D_4ead4 ltac:(condz).              (* [comment removed for export] *)
      clbu F_4ead8 D_4ead8 (Z_to_bv 8 0) C_pre.        (* [comment removed for export] *)
      an F_4eadc D_4eadc.                              (* [comment removed for export] *)
      av F_4eae0 D_4eae0 (Z_to_bv 64 0xE0000000) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_4eae4 D_4eae4 (Z_to_bv 64 (rbeg + 0xE0000000)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av F_4eae8 D_4eae8 (Z_to_bv 64 (rbeg + 0xE0000000 + mfa)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      ab_tk F_4eaec D_4eaec ltac:(condz).              (* [comment removed for export] *)
      an F_4eb14 D_4eb14.                              (* [comment removed for export] *)
      av F_4eb18 D_4eb18 (Z_to_bv 64 (2 ^ 18)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      an F_4eb1c D_4eb1c.                              (* [comment removed for export] *)
      av F_4eb20 D_4eb20 (Z_to_bv 64 0x19801) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_4eb24 D_4eb24.                              (* [comment removed for export] *)
      an F_4eb28 D_4eb28.                              (* [comment removed for export] *)
      an F_4eb2c D_4eb2c.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End HEAD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition efs_ms (M : word -> option byte) (thr : word) (RIz mfa : Z) (v72 v80 : word) : word -> option byte :=
  wbytes (wbytes (wbytes M
    (at_ thr 2872) (LE8 (v_addi v72 1)))
    (at_ thr 2880) (LE8 (v_add v80 (Z_to_bv 64 (2 ^ 18)))))
    (Z_to_bv 64 (RIz + 24)) (LE8 (Z_to_bv 64 (mfa + 2 ^ 18))).
#[local] Hint Unfold efs_ms : asfr.

Section TAIL.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v thr v72 v80 : word) (RIz slot mfa T : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).

  Ltac efs_epi2 :=
      an F_4eb74 D_4eb74;                              (* [comment removed for export] *)
      cld8 F_4eb78 D_4eb78 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_4eb7c D_4eb7c s0v S_s0;                   (* [comment removed for export] *)
      cld8 F_4eb80 D_4eb80 s1v S_s1;                   (* [comment removed for export] *)
      cld8 F_4eb84 D_4eb84 s2v S_s2;                   (* [comment removed for export] *)
      cld8 F_4eb88 D_4eb88 s3v S_s3;                   (* [comment removed for export] *)
      an F_4eb8c D_4eb8c;                              (* [comment removed for export] *)
      aret F_4eb90 D_4eb90 ra.                         (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma efs_fail : getr regs 10 = Z_to_bv 64 0 ->
    exists r, msteps ASEGS (mkst regs (0x4eb38 : word) M rom) (mkst r ra M rom) /\ efs_post sp ra s0v s1v s2v s3v 0 regs r.
  Proof using S_s3 S_s2 S_s1 S_s0 S_ra Hret H2.
    intros H10. (lazymatch goal with |- ?G => let G' := eval unfold efs_post in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_4eb30 D_4eb30 ltac:(condz).              (* [comment removed for export] *)
      an F_4ebb4 D_4ebb4.                              (* [comment removed for export] *)
      an F_4ebb8 D_4ebb8.                              (* [comment removed for export] *)
      efs_epi2.
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma efs_mapped : getr regs 10 = Z_to_bv 64 slot -> getr regs 9 = Z_to_bv 64 slot -> getr regs 18 = Z_to_bv 64 (2 ^ 18) -> (0 < slot < 2 ^ 64)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4eb38 : word) M rom) (mkst r (0x6f610 : word) M rom)
      /\ getr r 1 = Z_to_bv 64 0x4eb54 /\ getr r 10 = Z_to_bv 64 slot /\ getr r 11 = Z_to_bv 64 (2 ^ 18) /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12; 14]) regs r.
  Proof using sp.
    intros H10 H9 H18 Hslot. pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_ft F_4eb30 D_4eb30 ltac:(condz).              (* [comment removed for export] *)
      an F_4eb34 D_4eb34.                              (* [comment removed for export] *)
      ab_ft F_4eb38 D_4eb38 ltac:(condz).              (* [comment removed for export] *)
      an F_4eb3c D_4eb3c.                              (* [comment removed for export] *)
      an F_4eb40 D_4eb40.                              (* [comment removed for export] *)
      an F_4eb44 D_4eb44.                              (* [comment removed for export] *)
      an F_4eb48 D_4eb48.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 48)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 48 /\ T mod 8 = 0)%Z.
  Hypothesis HTRI : (T + 4096 <= RIz \/ RIz + 128 <= T)%Z.
  Hypothesis Hmfa : (0 <= mfa <= 2 ^ 29)%Z.
  Hypothesis R_72 : rdn ASEGS M (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn ASEGS M (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOK_T : store_ok ASEGS M thr 4096 = true.
  Hypothesis SOK_RI : store_ok ASEGS M (Z_to_bv 64 RIz) 128 = true.

  Lemma efs_stats : getr regs 10 = at_ thr 2800 -> getr regs 8 = Z_to_bv 64 (mfa + 2 ^ 18) -> getr regs 18 = Z_to_bv 64 (2 ^ 18) ->
    getr regs 19 = Z_to_bv 64 RIz ->
    exists r, msteps ASEGS (mkst regs (0x4eb58 : word) M rom) (mkst r ra (efs_ms M thr RIz mfa v72 v80) rom)
      /\ efs_post sp ra s0v s1v s2v s3v 1 regs r.
  Proof using SOK_RI SOK_T R_80 R_72 HT HRI S_s3 S_s2 S_s1 S_s0 S_ra Hret Hsp H2 T. clear - SOK_RI SOK_T R_80 R_72 HT HRI S_s3 S_s2 S_s1 S_s0 S_ra Hret Hsp H2 T.
    intros H10 H8 H18 H19. (lazymatch goal with |- ?G => let G' := eval unfold efs_post in G in change_no_check G' end). destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - cld8 F_4eb50 D_4eb50 v80 R_80.                   (* [comment removed for export] *)
      cld8 F_4eb54 D_4eb54 v72 R_72.                   (* [comment removed for export] *)
      an F_4eb58 D_4eb58.                              (* [comment removed for export] *)
      an F_4eb5c D_4eb5c.                              (* [comment removed for export] *)
      fsd F_4eb60 D_4eb60 (at_ thr 2872).              (* [comment removed for export] *)
      fsd F_4eb64 D_4eb64 (at_ thr 2880).              (* [comment removed for export] *)
      an F_4eb68 D_4eb68.                              (* [comment removed for export] *)
      fsd F_4eb6c D_4eb6c (Z_to_bv 64 (RIz + 24)).     (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes M _ _) _ _) _ _) with (efs_ms M thr RIz mfa v72 v80).
      an F_4eb70 D_4eb70.                              (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold efs_ms in G in change_no_check G' end).
      efs_epi2.
      wd_refl.
    - post. ra_solve.
  Qed.
End TAIL.
End FPGen.

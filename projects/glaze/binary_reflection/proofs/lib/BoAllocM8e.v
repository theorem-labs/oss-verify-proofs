(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_51a9c_52858 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8p.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_51a9c_52858.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
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
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
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
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-64)) 64 = true.
  Hypothesis C_sbeg : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis R_au : rdn BSEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn BSEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).

  #[local] Abbreviation M0 := (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).

  Ltac pf_prologue :=
      an F_51844 D_51844;                              (* [comment removed for export] *)
      fsd F_51848 D_51848 (at_ sp (-8));               (* [comment removed for export] *)
      fsd F_5184c D_5184c (at_ sp (-16));              (* [comment removed for export] *)
      fsd F_51850 D_51850 (at_ sp (-24));              (* [comment removed for export] *)
      fsd F_51854 D_51854 (at_ sp (-32));              (* [comment removed for export] *)
      fsd F_51858 D_51858 (at_ sp (-40));              (* [comment removed for export] *)
      fsd F_5185c D_5185c (at_ sp (-48));              (* [comment removed for export] *)
      fsd F_51860 D_51860 (at_ sp (-56));              (* [comment removed for export] *)
      fsd F_51864 D_51864 (at_ sp (-64));              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0;
      an F_51868 D_51868;                              (* [comment removed for export] *)
      an F_5186c D_5186c;                              (* [comment removed for export] *)
      cld8 F_51870 D_51870 (Z_to_bv 64 SPB) C_sbeg;    (* [comment removed for export] *)
      an F_51874 D_51874;                              (* [comment removed for export] *)
      av F_51878 D_51878 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia);   (* [comment removed for export] *)
      ab_ft F_5187c D_5187c ltac:(condz);              (* [comment removed for export] *)
      an F_51880 D_51880.                              (* [comment removed for export] *)

  Ltac pf_lo :=
      pf_prologue;
      ab_ft F_51884 D_51884 ltac:(condz);              (* [comment removed for export] *)
      av F_51888 D_51888 (Z_to_bv 64 (csize c)) ltac:(apply csize_small; lia);   (* [comment removed for export] *)
      cld8 F_5188c D_5188c (Z_to_bv 64 au) R_au;       (* [comment removed for export] *)
      cld8 F_51890 D_51890 (Z_to_bv 64 mu) R_mu;       (* [comment removed for export] *)
      av F_51894 D_51894 (Z_to_bv 64 (csize c * req)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av F_51898 D_51898 (Z_to_bv 64 (au + csize c * req)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av F_5189c D_5189c (Z_to_bv 64 (SPB + c * 2 ^ 32)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
  Ltac pf_hi :=
      pf_prologue;
      ab_tk F_51884 D_51884 ltac:(condz);              (* [comment removed for export] *)
      an F_518a8 D_518a8;                              (* [comment removed for export] *)
      an F_518ac D_518ac;                              (* [comment removed for export] *)
      an F_518b0 D_518b0;                              (* [comment removed for export] *)
      an F_518b4 D_518b4;                              (* [comment removed for export] *)
      an F_518b8 D_518b8;                              (* [comment removed for export] *)
      an F_518bc D_518bc;                              (* [comment removed for export] *)
      an F_518c0 D_518c0;                              (* [comment removed for export] *)
      an F_518c4 D_518c4;                              (* [comment removed for export] *)
      av F_518c8 D_518c8 (Z_to_bv 64 (csize c)) ltac:(exact (csize_big c ltac:(lia)));   (* [comment removed for export] *)
      cld8 F_518cc D_518cc (Z_to_bv 64 au) R_au;       (* [comment removed for export] *)
      cld8 F_518d0 D_518d0 (Z_to_bv 64 mu) R_mu;       (* [comment removed for export] *)
      av F_518d4 D_518d4 (Z_to_bv 64 (csize c * req)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av F_518d8 D_518d8 (Z_to_bv 64 (au + csize c * req)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      av F_518dc D_518dc (Z_to_bv 64 (SPB + c * 2 ^ 32)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)

  Definition pf_clob : list reg := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31].

  (* [comment removed for export] *)
  Lemma pf_head_map : (mu < au + csize c * req)%Z ->
    exists r, msteps BSEGS (mkst regs (0x51844 : word) mem rom) (mkst r (0x518e4 : word) M0 rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 9 = stats /\ getr r 10 = Z_to_bv 64 0x10ab58 /\ getr r 12 = Z_to_bv 64 c
      /\ getr r 19 = Z_to_bv 64 (au + csize c * req) /\ getr r 20 = Z_to_bv 64 mu
      /\ regs_agree (fun i : reg => In i pf_clob) regs r.
  Proof using R_mu R_au C_sbeg Hstk HRI HSPB Hau Hreq Hc Hsp H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H2 H1.
    intros Hmap. (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (csize_pos c Hc) as [Hcs1 Hcs2].
    destruct (Z_le_gt_dec c 16) as [Hlo | Hhi].
    - wd_eexists. split.
      + pf_lo.
        ab_tk F_518a0 D_518a0 ltac:(condz).            (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
    - wd_eexists. split.
      + pf_hi.
        ab_ft F_518e0 D_518e0 ltac:(condz).            (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_head_nomap : (au + csize c * req <= mu)%Z ->
    exists r, msteps BSEGS (mkst regs (0x51844 : word) mem rom) (mkst r (0x519b8 : word) M0 rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 10 = Z_to_bv 64 0x10ab58
      /\ getr r 13 = Z_to_bv 64 au /\ getr r 20 = Z_to_bv 64 mu
      /\ regs_agree (fun i : reg => In i pf_clob) regs r.
  Proof using R_mu R_au C_sbeg Hstk HRI HSPB Hau Hreq Hc Hsp H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H2 H1 stats.
    intros Hmap. (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof (csize_pos c Hc) as [Hcs1 Hcs2].
    destruct (Z_le_gt_dec c 16) as [Hlo | Hhi].
    - wd_eexists. split.
      + pf_lo.
        ab_ft F_518a0 D_518a0 ltac:(condz).            (* [comment removed for export] *)
        an F_518a4 D_518a4.                            (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
    - wd_eexists. split.
      + pf_hi.
        ab_tk F_518e0 D_518e0 ltac:(condz).            (* [comment removed for export] *)
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
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 tot.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 mu.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Htot : (mu < tot /\ tot <= mu + 2 ^ 18)%Z.
  Hypothesis Hmu : (0 <= mu /\ mu + 2 ^ 18 <= 0xE0000000)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis C_rel : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff).
  Hypothesis C_pre : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis R_mm : rdn BSEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)).

  Ltac pf_maptail :=
      av F_518e8 D_518e8 (Z_to_bv 64 (2 ^ 64 - 1 - mu)) ltac:(apply v_not_lit; lia);   (* [comment removed for export] *)
      an F_518ec D_518ec;                              (* [comment removed for export] *)
      av F_518f0 D_518f0 (Z_to_bv 64 (tot - mu - 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; rewrite <- (Z2bv_plus64 (tot - mu - 1)); f_equal; lia);   (* [comment removed for export] *)
      an F_518f4 D_518f4;                              (* [comment removed for export] *)
      av_and F_518f8 D_518f8 (Z_to_bv 64 0)
        ltac:(match goal with |- v_and _ ?X = _ => replace X with (Z_to_bv 64 (2 ^ 64 - 2 ^ 18)) by (apply bv_eq; vm_compute; reflexivity) end;
              rewrite v_and_m18; unorm; f_equal; rewrite Z.mod_small by lia; lia);   (* [comment removed for export] *)
      cld8 F_518fc D_518fc (Z_to_bv 64 0) R_mm;        (* [comment removed for export] *)
      av F_51900 D_51900 (Z_to_bv 64 (2 ^ 18)) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      an F_51904 D_51904;                              (* [comment removed for export] *)
      av F_51908 D_51908 (Z_to_bv 64 0xE0000000) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      av F_5190c D_5190c (Z_to_bv 64 mu) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);   (* [comment removed for export] *)
      av F_51910 D_51910 (Z_to_bv 64 (mu + 2 ^ 18)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);   (* [comment removed for export] *)
      av F_51914 D_51914 (Z_to_bv 64 0xE0000001) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      ab_ft F_51918 D_51918 ltac:(condz);              (* [comment removed for export] *)
      clbu F_5191c D_5191c (Z_to_bv 8 0) C_pre;        (* [comment removed for export] *)
      av F_51920 D_51920 (Z_to_bv 64 (SPB + c * 2 ^ 32 + mu)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);   (* [comment removed for export] *)
      ab_tk F_51924 D_51924 ltac:(condz);              (* [comment removed for export] *)
      an F_5194c D_5194c;                              (* [comment removed for export] *)
      av F_51950 D_51950 (Z_to_bv 64 0x178e4) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      an F_51954 D_51954;                              (* [comment removed for export] *)
      an F_51958 D_51958;                              (* [comment removed for export] *)
      an F_5195c D_5195c;                              (* [comment removed for export] *)
      an F_51960 D_51960.                              (* [comment removed for export] *)

  Lemma le4_m1 : bytes_le_to_Z (LE4 0xffffffff) = U (Z_to_bv 64 0xffffffff).
  Proof using. vm_compute. reflexivity. Qed.

  Lemma pf_map :
    exists r, msteps BSEGS (mkst regs (0x518e4 : word) mem rom) (mkst r (0x8b0f8 : word) mem rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 9 = stats /\ getr r 1 = Z_to_bv 64 0x51964
      /\ getr r 11 = Z_to_bv 64 (SPB + c * 2 ^ 32 + mu) /\ getr r 12 = Z_to_bv 64 (2 ^ 18) /\ getr r 13 = Z_to_bv 64 0x178e4
      /\ getr r 19 = Z_to_bv 64 (2 ^ 18) /\ getr r 20 = Z_to_bv 64 (SPB + c * 2 ^ 32 + mu) /\ getr r 22 = Z_to_bv 64 0x10ab58
      /\ regs_agree (fun i : reg => In i pf_clob) regs r.
  Proof using R_mm C_pre C_rel HRI HSPB Hmu Htot Hc Hsp H20 H19 H10 H9 HR tot.
    destruct HR as (R2 & R8 & R18 & R21). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    destruct (Z.eq_dec mu 0) as [Ez | Nz].
    - wd_eexists. split.
      + ab_tk F_518e4 D_518e4 ltac:(condz).            (* [comment removed for export] *)
        clw F_51aa0 D_51aa0 (LE4 0xffffffff) (Z_to_bv 64 0xffffffff) C_rel le4_m1.   (* [comment removed for export] *)
        ab_tk F_51aa4 D_51aa4 ltac:(first [condz | vm_compute; reflexivity]).   (* [comment removed for export] *)
        an F_51b68 D_51b68.                            (* [comment removed for export] *)
        an F_51b6c D_51b6c.                            (* [comment removed for export] *)
        replace (Z_to_bv 64 0) with (Z_to_bv 64 mu) by (rewrite Ez; reflexivity).
        pf_maptail.
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end). ra_solve.
    - wd_eexists. split.
      + ab_ft F_518e4 D_518e4 ltac:(condz).            (* [comment removed for export] *)
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
    exists r, msteps BSEGS (mkst regs (0x51964 : word) mem rom) (mkst r (0x70080 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x51980 /\ getr r 10 = Z_to_bv 64 slot /\ getr r 11 = Z_to_bv 64 (2 ^ 18) /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12; 14]) regs r.
  Proof using Hslot H20 H19 HR c SPB RIz sp.
    intros H10. destruct HR as (R2 & R8 & R18 & R21). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_ft F_51964 D_51964 ltac:(condz).              (* [comment removed for export] *)
      an F_51968 D_51968.                              (* [comment removed for export] *)
      ab_ft F_5196c D_5196c ltac:(condz).              (* [comment removed for export] *)
      an F_51970 D_51970.                              (* [comment removed for export] *)
      an F_51974 D_51974.                              (* [comment removed for export] *)
      an F_51978 D_51978.                              (* [comment removed for export] *)
      an F_5197c D_5197c.                              (* [comment removed for export] *)
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
  Hypothesis S_ra : rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn BSEGS M (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn BSEGS M (at_ sp (-64)) 8 = Some (LE8 s6v).

  Ltac pf_epi :=
      an F_51a54 D_51a54;                              (* [comment removed for export] *)
      cld8 F_51a58 D_51a58 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_51a5c D_51a5c s0v S_s0;                   (* [comment removed for export] *)
      cld8 F_51a60 D_51a60 s1v S_s1;                   (* [comment removed for export] *)
      cld8 F_51a64 D_51a64 s2v S_s2;                   (* [comment removed for export] *)
      cld8 F_51a68 D_51a68 s3v S_s3;                   (* [comment removed for export] *)
      cld8 F_51a6c D_51a6c s4v S_s4;                   (* [comment removed for export] *)
      cld8 F_51a70 D_51a70 s5v S_s5;                   (* [comment removed for export] *)
      cld8 F_51a74 D_51a74 s6v S_s6;                   (* [comment removed for export] *)
      an F_51a78 D_51a78;                              (* [comment removed for export] *)
      aret F_51a7c D_51a7c ra.                         (* [comment removed for export] *)

  Definition pf_post0 (r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 0 /\ getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = s6v
    /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22]) regs r.

  (* [comment removed for export] *)
  Lemma pf_fail_map : exists r, msteps BSEGS (mkst regs (0x51964 : word) M rom) (mkst r ra M rom) /\ pf_post0 r.
  Proof using S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hret H10 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold pf_post0 in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_51964 D_51964 ltac:(condz).              (* [comment removed for export] *)
      an F_51ad4 D_51ad4.                              (* [comment removed for export] *)
      an F_51ad8 D_51ad8.                              (* [comment removed for export] *)
      pf_epi.
      wd_refl.
    - post. ra_solve.
  Qed.
  (* [comment removed for export] *)
  Lemma pf_fail_efs : exists r, msteps BSEGS (mkst regs (0x519d8 : word) M rom) (mkst r ra M rom) /\ pf_post0 r.
  Proof using S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hret H10 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold pf_post0 in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_519d8 D_519d8 ltac:(condz).              (* [comment removed for export] *)
      an F_51ad4 D_51ad4.                              (* [comment removed for export] *)
      an F_51ad8 D_51ad8.                              (* [comment removed for export] *)
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
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 0x10ab58.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hau : (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 64 /\ T mod 8 = 0)%Z.
  Hypothesis HTRI : (T + 4096 <= RIz \/ RIz + 128 <= T)%Z.
  Hypothesis R_72 : rdn BSEGS M (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn BSEGS M (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis R_st : rdn BSEGS M (at_ thr 2792) 8 = Some (LE8 vst).
  Hypothesis R_au : rdn BSEGS M (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn BSEGS M (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis SOK_T : store_ok BSEGS M thr 4096 = true.
  Hypothesis SOK_RI : store_ok BSEGS M (Z_to_bv 64 RIz) 128 = true.

  Lemma pf_stats :
    exists r, msteps BSEGS (mkst regs (0x51984 : word) M rom) (mkst r (0x519b8 : word) (pf_ms M thr RIz mu v72 v80 vst) rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 10 = Z_to_bv 64 0x10ab58
      /\ getr r 13 = Z_to_bv 64 au /\ getr r 20 = Z_to_bv 64 (mu + 2 ^ 18)
      /\ regs_agree (fun i : reg => In i [9; 10; 11; 12; 13; 20]) regs r.
  Proof using SOK_RI SOK_T R_mu R_au R_st R_80 R_72 HTRI HT HRI Hau Hsp H22 H19 H10 H9 HR T.
    destruct HR as (R2 & R8 & R18 & R21). destruct HT as (UT & T1 & T2 & T3). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - cld8 F_51984 D_51984 v72 R_72.                   (* [comment removed for export] *)
      cld8 F_51988 D_51988 v80 R_80.                   (* [comment removed for export] *)
      an F_5198c D_5198c.                              (* [comment removed for export] *)
      an F_51990 D_51990.                              (* [comment removed for export] *)
      fsd F_51994 D_51994 (at_ thr 2872).              (* [comment removed for export] *)
      fsd F_51998 D_51998 (at_ thr 2880).              (* [comment removed for export] *)
      an F_5199c D_5199c.                              (* [comment removed for export] *)
      av F_519a0 D_519a0 (at_ thr 2792) ltac:(change (v_addi (at_ thr 2768) 24) with (at_ (at_ thr 2768) 24); rewrite at_at; reflexivity).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 vst) (v := vst);
          [exact F_519a4 | reflexivity | exact D_519a4
          | gres; rwH; rewrite at_u by lia; rewrite UT; rewrite <- Zplus_mod_idemp_l, T3; reflexivity
          | gres; rwH; rd_peel; exact R_st
          | apply bytes_le_to_Z_8
          | gres; rwH; any_ok ]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      cld8 F_519a8 D_519a8 (Z_to_bv 64 mu) R_mu.       (* [comment removed for export] *)
      cld8 F_519ac D_519ac (Z_to_bv 64 au) R_au.       (* [comment removed for export] *)
      av F_519b0 D_519b0 (Z_to_bv 64 (mu + 2 ^ 18)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      fsd F_519b4 D_519b4 (Z_to_bv 64 (RIz + 48)).     (* [comment removed for export] *)
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
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 au.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 mu.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hau : (0 <= au <= mu /\ mu <= 0xE0000000)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis R_nf : rdn BSEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).

  #[local] Abbreviation newn := ((mu - au) / csize c)%Z.

  Lemma pf_efs_call :
    exists r, msteps BSEGS (mkst regs (0x519b8 : word) M rom) (mkst r (0x4f508 : word) M rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 1 = Z_to_bv 64 0x519d8
      /\ getr r 10 = Z_to_bv 64 0x10ab58 /\ getr r 11 = Z_to_bv 64 RIz /\ getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32)
      /\ getr r 13 = Z_to_bv 64 (nf + newn)
      /\ getr r 9 = Z_to_bv 64 (nf + newn) /\ getr r 19 = Z_to_bv 64 newn /\ getr r 20 = Z_to_bv 64 (mu - au)
      /\ regs_agree (fun i : reg => In i [1; 9; 11; 12; 13; 19; 20]) regs r.
  Proof using R_nf HRI Hnf Hau Hc Hsp H20 H13 H10 HR.
    destruct HR as (R2 & R8 & R18 & R21). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    pose proof (csize_pos c Hc) as [Hcs1 Hcs2].
    assert (Hnn : (0 <= newn <= 0xE0000000)%Z).
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia. }
    wd_eexists. split.
    - cld8 F_519b8 D_519b8 (Z_to_bv 64 nf) R_nf.       (* [comment removed for export] *)
      av F_519bc D_519bc (Z_to_bv 64 (mu - au)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      an F_519c0 D_519c0; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] |].   (* [comment removed for export] *)
      match goal with |- context [v_divu ?a ?b] =>
        replace (v_divu a b) with (Z_to_bv 64 newn)
          by (symmetry; apply bv_eq; rewrite v_divu_small by (wd_ulia); unorm; reflexivity) end.
      av F_519c4 D_519c4 (Z_to_bv 64 (nf + newn)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      an F_519c8 D_519c8.                              (* [comment removed for export] *)
      an F_519cc D_519cc.                              (* [comment removed for export] *)
      an F_519d0 D_519d0.                              (* [comment removed for export] *)
      an F_519d4 D_519d4.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End EFSCALL.
End FPGen.
End BoAllocM8p.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
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
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
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
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-48)) 48 = true.
  Hypothesis R_mfa : rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_pre : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).

  Ltac efs_prologue :=
      an F_4f508 D_4f508;                              (* [comment removed for export] *)
      fsd F_4f50c D_4f50c (at_ sp (-8));               (* [comment removed for export] *)
      fsd F_4f510 D_4f510 (at_ sp (-16));              (* [comment removed for export] *)
      fsd F_4f514 D_4f514 (at_ sp (-24));              (* [comment removed for export] *)
      fsd F_4f518 D_4f518 (at_ sp (-32));              (* [comment removed for export] *)
      fsd F_4f51c D_4f51c (at_ sp (-40));              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0;
      cld8 F_4f520 D_4f520 (Z_to_bv 64 mfa) R_mfa;     (* [comment removed for export] *)
      av F_4f524 D_4f524 (Z_to_bv 64 (4 * tot)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia);   (* [comment removed for export] *)
      an F_4f528 D_4f528.                              (* [comment removed for export] *)

  Ltac efs_epi :=
      an F_4f5ec D_4f5ec;                              (* [comment removed for export] *)
      fld F_4f5f0 D_4f5f0 ra;                          (* [comment removed for export] *)
      fld F_4f5f4 D_4f5f4 s0v;                         (* [comment removed for export] *)
      fld F_4f5f8 D_4f5f8 s1v;                         (* [comment removed for export] *)
      fld F_4f5fc D_4f5fc s2v;                         (* [comment removed for export] *)
      fld F_4f600 D_4f600 s3v;                         (* [comment removed for export] *)
      an F_4f604 D_4f604;                              (* [comment removed for export] *)
      aret F_4f608 D_4f608 ra.                         (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma efs_enough : (4 * tot <= mfa)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4f508 : word) mem rom) (mkst r ra M0 rom) /\ efs_post sp ra s0v s1v s2v s3v 1 regs r.
  Proof using R_mfa Hstk HRI Hmfa Htot Hret Hsp H19 H18 H9 H8 H13 H11 H2 H1 RIz.
    intros Hen. (lazymatch goal with |- ?G => let G' := eval unfold efs_post in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - efs_prologue.
      ab_tk F_4f52c D_4f52c ltac:(condz).              (* [comment removed for export] *)
      efs_epi.
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma efs_map : (mfa < 4 * tot <= mfa + 2 ^ 18)%Z -> (mfa + 2 ^ 18 <= 2 ^ 29)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4f508 : word) mem rom) (mkst r (0x8b0f8 : word) M0 rom)
      /\ getr r 1 = Z_to_bv 64 0x4f5a8 /\ getr r 2 = at_ sp (-48)
      /\ getr r 11 = Z_to_bv 64 (rbeg + 0xE0000000 + mfa) /\ getr r 12 = Z_to_bv 64 (2 ^ 18) /\ getr r 13 = Z_to_bv 64 0x19778
      /\ getr r 8 = Z_to_bv 64 (mfa + 2 ^ 18) /\ getr r 9 = Z_to_bv 64 (rbeg + 0xE0000000 + mfa) /\ getr r 18 = Z_to_bv 64 (2 ^ 18)
      /\ getr r 19 = Z_to_bv 64 RIz
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19]) regs r.
  Proof using C_pre R_mfa Hstk HRI Hrbeg Hmfa Htot Hsp H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    intros Hneed Hroom. pose proof (u64_range sp) as Hspr. destruct Hmfa as [Hm1 Hm2].
    wd_eexists. split.
    - efs_prologue.
      ab_ft F_4f52c D_4f52c ltac:(condz).              (* [comment removed for export] *)
      an F_4f530 D_4f530.                              (* [comment removed for export] *)
      av F_4f534 D_4f534 (Z_to_bv 64 0x3ffff) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_4f538 D_4f538 (Z_to_bv 64 (4 * tot + 0x3ffff)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      an F_4f53c D_4f53c.                              (* [comment removed for export] *)
      av_and F_4f540 D_4f540 (Z_to_bv 64 (mfa + 2 ^ 18))
        ltac:(match goal with |- v_and _ ?X = _ => replace X with (Z_to_bv 64 (2 ^ 64 - 2 ^ 18)) by (apply bv_eq; vm_compute; reflexivity) end;
              rewrite v_and_m18; unorm; f_equal; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      an F_4f544 D_4f544.                              (* [comment removed for export] *)
      av F_4f548 D_4f548 (Z_to_bv 64 0x20000001) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4f54c D_4f54c ltac:(condz).              (* [comment removed for export] *)
      clbu F_4f550 D_4f550 (Z_to_bv 8 0) C_pre.        (* [comment removed for export] *)
      an F_4f554 D_4f554.                              (* [comment removed for export] *)
      av F_4f558 D_4f558 (Z_to_bv 64 0xE0000000) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_4f55c D_4f55c (Z_to_bv 64 (rbeg + 0xE0000000)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av F_4f560 D_4f560 (Z_to_bv 64 (rbeg + 0xE0000000 + mfa)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      ab_tk F_4f564 D_4f564 ltac:(condz).              (* [comment removed for export] *)
      an F_4f58c D_4f58c.                              (* [comment removed for export] *)
      av F_4f590 D_4f590 (Z_to_bv 64 (2 ^ 18)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      an F_4f594 D_4f594.                              (* [comment removed for export] *)
      av F_4f598 D_4f598 (Z_to_bv 64 0x19778) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_4f59c D_4f59c.                              (* [comment removed for export] *)
      an F_4f5a0 D_4f5a0.                              (* [comment removed for export] *)
      an F_4f5a4 D_4f5a4.                              (* [comment removed for export] *)
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
  Hypothesis S_ra : rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).

  Ltac efs_epi2 :=
      an F_4f5ec D_4f5ec;                              (* [comment removed for export] *)
      cld8 F_4f5f0 D_4f5f0 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_4f5f4 D_4f5f4 s0v S_s0;                   (* [comment removed for export] *)
      cld8 F_4f5f8 D_4f5f8 s1v S_s1;                   (* [comment removed for export] *)
      cld8 F_4f5fc D_4f5fc s2v S_s2;                   (* [comment removed for export] *)
      cld8 F_4f600 D_4f600 s3v S_s3;                   (* [comment removed for export] *)
      an F_4f604 D_4f604;                              (* [comment removed for export] *)
      aret F_4f608 D_4f608 ra.                         (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma efs_fail : getr regs 10 = Z_to_bv 64 0 ->
    exists r, msteps BSEGS (mkst regs (0x4f5a8 : word) M rom) (mkst r ra M rom) /\ efs_post sp ra s0v s1v s2v s3v 0 regs r.
  Proof using S_s3 S_s2 S_s1 S_s0 S_ra Hret H2.
    intros H10. (lazymatch goal with |- ?G => let G' := eval unfold efs_post in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_4f5a8 D_4f5a8 ltac:(condz).              (* [comment removed for export] *)
      an F_4f62c D_4f62c.                              (* [comment removed for export] *)
      an F_4f630 D_4f630.                              (* [comment removed for export] *)
      efs_epi2.
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma efs_mapped : getr regs 10 = Z_to_bv 64 slot -> getr regs 9 = Z_to_bv 64 slot -> getr regs 18 = Z_to_bv 64 (2 ^ 18) -> (0 < slot < 2 ^ 64)%Z ->
    exists r, msteps BSEGS (mkst regs (0x4f5a8 : word) M rom) (mkst r (0x70080 : word) M rom)
      /\ getr r 1 = Z_to_bv 64 0x4f5c4 /\ getr r 10 = Z_to_bv 64 slot /\ getr r 11 = Z_to_bv 64 (2 ^ 18) /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12; 14]) regs r.
  Proof using sp.
    intros H10 H9 H18 Hslot. pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_ft F_4f5a8 D_4f5a8 ltac:(condz).              (* [comment removed for export] *)
      an F_4f5ac D_4f5ac.                              (* [comment removed for export] *)
      ab_ft F_4f5b0 D_4f5b0 ltac:(condz).              (* [comment removed for export] *)
      an F_4f5b4 D_4f5b4.                              (* [comment removed for export] *)
      an F_4f5b8 D_4f5b8.                              (* [comment removed for export] *)
      an F_4f5bc D_4f5bc.                              (* [comment removed for export] *)
      an F_4f5c0 D_4f5c0.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 48)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 48 /\ T mod 8 = 0)%Z.
  Hypothesis HTRI : (T + 4096 <= RIz \/ RIz + 128 <= T)%Z.
  Hypothesis Hmfa : (0 <= mfa <= 2 ^ 29)%Z.
  Hypothesis R_72 : rdn BSEGS M (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn BSEGS M (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOK_T : store_ok BSEGS M thr 4096 = true.
  Hypothesis SOK_RI : store_ok BSEGS M (Z_to_bv 64 RIz) 128 = true.

  Lemma efs_stats : getr regs 10 = at_ thr 2800 -> getr regs 8 = Z_to_bv 64 (mfa + 2 ^ 18) -> getr regs 18 = Z_to_bv 64 (2 ^ 18) ->
    getr regs 19 = Z_to_bv 64 RIz ->
    exists r, msteps BSEGS (mkst regs (0x4f5c8 : word) M rom) (mkst r ra (efs_ms M thr RIz mfa v72 v80) rom)
      /\ efs_post sp ra s0v s1v s2v s3v 1 regs r.
  Proof using SOK_RI SOK_T R_80 R_72 HT HRI S_s3 S_s2 S_s1 S_s0 S_ra Hret Hsp H2 T. clear - SOK_RI SOK_T R_80 R_72 HT HRI S_s3 S_s2 S_s1 S_s0 S_ra Hret Hsp H2 T.
    intros H10 H8 H18 H19. (lazymatch goal with |- ?G => let G' := eval unfold efs_post in G in change_no_check G' end). destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - cld8 F_4f5c8 D_4f5c8 v80 R_80.                   (* [comment removed for export] *)
      cld8 F_4f5cc D_4f5cc v72 R_72.                   (* [comment removed for export] *)
      an F_4f5d0 D_4f5d0.                              (* [comment removed for export] *)
      an F_4f5d4 D_4f5d4.                              (* [comment removed for export] *)
      fsd F_4f5d8 D_4f5d8 (at_ thr 2872).              (* [comment removed for export] *)
      fsd F_4f5dc D_4f5dc (at_ thr 2880).              (* [comment removed for export] *)
      an F_4f5e0 D_4f5e0.                              (* [comment removed for export] *)
      fsd F_4f5e4 D_4f5e4 (Z_to_bv 64 (RIz + 24)).     (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes M _ _) _ _) _ _) with (efs_ms M thr RIz mfa v72 v80).
      an F_4f5e8 D_4f5e8.                              (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold efs_ms in G in change_no_check G' end).
      efs_epi2.
      wd_refl.
    - post. ra_solve.
  Qed.
End TAIL.
End FPGen.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
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

Section GPRE.
  Variables (M rom : word -> option byte) (nch PAb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x103f18 + 64).
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 nch.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 nch.          (* [comment removed for export] *)
  Hypothesis Hnch : (0 <= nch < 2 ^ 20)%Z.
  Hypothesis HPA : (0 <= PAb /\ PAb + 2 ^ 23 < 2 ^ 63)%Z.
  Hypothesis R_pab : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 80)) 8 = Some (LE8 (Z_to_bv 64 PAb)).

  Lemma la_grow_pre :
    exists r, msteps ASEGS (mkst regs (0x507b4 : word) M rom) (mkst r (0x8a7d4 : word) M rom)
      /\ getr r 1 = Z_to_bv 64 0x509b0 /\ getr r 11 = Z_to_bv 64 (PAb + 8 * nch) /\ getr r 12 = Z_to_bv 64 0x20000
      /\ getr r 13 = Z_to_bv 64 0 /\ getr r 20 = getr regs 10
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12; 13; 14; 20]) regs r.
  Proof using R_pab HPA Hnch H14 H13 H9.
    destruct HPA as [PA1 PA2].
    wd_eexists. split.
    - ab_tk F_507ac D_507ac ltac:(condz).             (* [comment removed for export] *)
      cld8 F_50984 D_50984 (Z_to_bv 64 PAb) R_pab.     (* [comment removed for export] *)
      an F_50988 D_50988.                              (* [comment removed for export] *)
      av F_5098c D_5098c (Z_to_bv 64 (8 * nch)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_50990 D_50990 (Z_to_bv 64 (PAb + 8 * nch)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      an F_50994 D_50994.                              (* [comment removed for export] *)
      an F_50998 D_50998.                              (* [comment removed for export] *)
      an F_5099c D_5099c.                              (* [comment removed for export] *)
      an F_509a0 D_509a0.                              (* [comment removed for export] *)
      an F_509a4 D_509a4.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End GPRE.

Section BEQNT.
  Variables (M rom : word -> option byte) (nch nres : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 nch.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 nres.
  Hypothesis Hne : (0 <= nch < 2 ^ 20 /\ nch <> nres /\ 0 <= nres < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Lemma la_beq_nt : msteps ASEGS (mkst regs (0x507b4 : word) M rom) (mkst regs (0x507b8 : word) M rom).
  Proof using Hne H14 H13 nres nch.
    destruct Hne as (N1 & N2 & N3).
    ab_ft F_507ac D_507ac ltac:(condz). wd_refl.
  Qed.
End BEQNT.

Section GPOST.
  Variables (M rom : word -> option byte) (nres nch : Z) (res : word).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x103f18 + 64).
  Hypothesis H20 : getr regs 20 = res.
  Hypothesis Hnres : (0 <= nres < 2 ^ 32)%Z.
  Hypothesis R_nres : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).
  Hypothesis R_nch : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis SOK_nres : store_ok ASEGS M (Z_to_bv 64 (0x103f18 + 112)) 8 = true.

  Definition la_mg : word -> option byte := wbytes M (Z_to_bv 64 (0x103f18 + 112)) (LE8 (Z_to_bv 64 (nres + 0x4000))).

  Lemma la_grow_post :
    exists r, msteps ASEGS (mkst regs (0x509b0 : word) M rom) (mkst r (0x507b8 : word) la_mg rom)
      /\ getr r 10 = res /\ getr r 13 = Z_to_bv 64 nch
      /\ regs_agree (fun i : reg => In i [10; 11; 12; 13]) regs r.
  Proof using SOK_nres R_nch R_nres Hnres H20 H9.
    wd_eexists. split.
    - an F_509a8 D_509a8.                              (* [comment removed for export] *)
      cld8 F_509ac D_509ac (Z_to_bv 64 nres) R_nres.   (* [comment removed for export] *)
      cld8 F_509b0 D_509b0 (Z_to_bv 64 nch) R_nch.     (* [comment removed for export] *)
      an F_509b4 D_509b4.                              (* [comment removed for export] *)
      av F_509b8 D_509b8 (Z_to_bv 64 (nres + 0x4000)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      fsd F_509bc D_509bc (Z_to_bv 64 (0x103f18 + 112)).   (* [comment removed for export] *)
      an F_509c0 D_509c0.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End GPOST.

Section T2BG.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v naw curw mxw blw w16 w24 : word)
            (size mb nch PA cz : Z).
  #[local] Abbreviation msz := (la_msz size).
  #[local] Abbreviation idx := (63 - cz)%Z.
  #[local] Abbreviation sumw := (v_add curw (Z_to_bv 64 (la_msz size))).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-96).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0x1041c8.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x103f18 + 64).
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 msz.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 cz.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 nch.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hnch : (0 <= nch < 2 ^ 20)%Z.
  Hypothesis Hcz : (0 <= cz <= 63)%Z.
  Hypothesis Hmb : (AIMGHI <= mb /\ mb + la_msz size < 2 ^ 63)%Z.
  Hypothesis HPA : (AIMGHI <= PA /\ PA + 2 ^ 23 < 2 ^ 63)%Z.
  Hypothesis HPAmb : (PA + 2 ^ 23 <= mb \/ mb + 32 <= PA)%Z.
  Hypothesis Hmbsp : (mb + 32 <= U sp - 96 \/ U sp <= mb)%Z.
  Hypothesis HPAsp : (PA + 2 ^ 23 <= U sp - 96 \/ U sp <= PA)%Z.
  Hypothesis R_pa : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 72)) 8 = Some (LE8 (Z_to_bv 64 PA)).
  Hypothesis R_na : rdn ASEGS M (Z_to_bv 64 0x103fa0) 8 = Some (LE8 naw).
  Hypothesis R_cur : rdn ASEGS M (Z_to_bv 64 0x103fb0) 8 = Some (LE8 curw).
  Hypothesis R_mx : rdn ASEGS M (Z_to_bv 64 0x103fb8) 8 = Some (LE8 mxw).
  Hypothesis R_bl : rdn ASEGS M (Z_to_bv 64 (0x103fc0 + 8 * idx)) 8 = Some (LE8 blw).
  Hypothesis R_16 : rdn ASEGS M (Z_to_bv 64 0x1041d8) 8 = Some (LE8 w16).
  Hypothesis R_24 : rdn ASEGS M (Z_to_bv 64 0x1041e0) 8 = Some (LE8 w24).
  Hypothesis SOK_h : store_ok ASEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_pa : store_ok ASEGS M (Z_to_bv 64 (PA + 8 * nch)) 8 = true.
  Hypothesis SOK_inst : store_ok ASEGS M (Z_to_bv 64 0x103f58) 728 = true.        (* [comment removed for export] *)

  Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn ASEGS M (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn ASEGS M (at_ sp (-64)) 8 = Some (LE8 s6v).
  Hypothesis S_s7 : rdn ASEGS M (at_ sp (-72)) 8 = Some (LE8 s7v).
  Hypothesis S_s8 : rdn ASEGS M (at_ sp (-80)) 8 = Some (LE8 s8v).
  Hypothesis S_s9 : rdn ASEGS M (at_ sp (-88)) 8 = Some (LE8 s9v).

  Definition la_mxg' : word := if (U sumw <? U mxw)%Z then mxw else sumw.

  Definition la_post1g (r : bvmap 5 word) : Prop :=
    getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
    /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
    /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 11; 12; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25]) regs r.

  Ltac t2b_head :=
      cld8 F_507b0 D_507b0 (Z_to_bv 64 PA) R_pa;       (* [comment removed for export] *)
      av F_507b4 D_507b4 (Z_to_bv 64 idx) ltac:(apply xori63; lia);   (* [comment removed for export] *)
      fsd F_507b8 D_507b8 (Z_to_bv 64 (mb + 24));      (* [comment removed for export] *)
      av F_507bc D_507bc (Z_to_bv 64 (8 * nch)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia);   (* [comment removed for export] *)
      av F_507c0 D_507c0 (Z_to_bv 64 (PA + 8 * nch)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      fsd F_507c4 D_507c4 (Z_to_bv 64 (PA + 8 * nch)); (* [comment removed for export] *)
      cld8 F_507c8 D_507c8 naw R_na;                   (* [comment removed for export] *)
      cld8 F_507cc D_507cc curw R_cur;                 (* [comment removed for export] *)
      av F_507d0 D_507d0 (Z_to_bv 64 (nch + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      cld8 F_507d4 D_507d4 mxw R_mx;                   (* [comment removed for export] *)
      an F_507d8 D_507d8;                              (* [comment removed for export] *)
      an F_507dc D_507dc;                              (* [comment removed for export] *)
      fsd F_507e0 D_507e0 (Z_to_bv 64 0x103f90);       (* [comment removed for export] *)
      fsb F_507e4 D_507e4 (Z_to_bv 64 0x103f98) (Z_to_bv 8 0);   (* [comment removed for export] *)
      fsd F_507e8 D_507e8 (Z_to_bv 64 0x103fa0);       (* [comment removed for export] *)
      fsd F_507ec D_507ec (Z_to_bv 64 0x103fb0).       (* [comment removed for export] *)
  Ltac t2b_tail :=
      av F_507f8 D_507f8 (Z_to_bv 64 (8 * idx)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia);   (* [comment removed for export] *)
      av F_507fc D_507fc (Z_to_bv 64 (0x103f58 + 8 * idx)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);   (* [comment removed for export] *)
      cld8 F_50800 D_50800 blw R_bl;                   (* [comment removed for export] *)
      an F_50804 D_50804;                              (* [comment removed for export] *)
      fsd F_50808 D_50808 (Z_to_bv 64 0x103fb8);       (* [comment removed for export] *)
      fsd F_5080c D_5080c (Z_to_bv 64 (0x103fc0 + 8 * idx));   (* [comment removed for export] *)
      av F_50810 D_50810 (Z_to_bv 64 0x1041d8) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 w16) (v := w16);
          [exact F_50814 | reflexivity | exact D_50814
          | gres; rwH; unorm; reflexivity
          | gres; rwH; rd_peel; exact R_16
          | apply bytes_le_to_Z_8
          | gres; rwH; any_ok ]
        | step_simpl]; vn);                            (* [comment removed for export] *)
      av F_50818 D_50818 (Z_to_bv 64 0x1041e0) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 w24) (v := w24);
          [exact F_5081c | reflexivity | exact D_5081c
          | gres; rwH; unorm; reflexivity
          | gres; rwH; rd_peel; exact R_24
          | apply bytes_le_to_Z_8
          | gres; rwH; any_ok ]
        | step_simpl]; vn);                            (* [comment removed for export] *)
      afence F_50820 D_50820;                          (* [comment removed for export] *)
      fsb F_50824 D_50824 (Z_to_bv 64 0x1041c0) (Z_to_bv 8 0);   (* [comment removed for export] *)
      cld8 F_50828 D_50828 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_5082c D_5082c s0v S_s0; cld8 F_50830 D_50830 s1v S_s1; cld8 F_50834 D_50834 s2v S_s2; cld8 F_50838 D_50838 s3v S_s3;
      cld8 F_5083c D_5083c s4v S_s4; cld8 F_50840 D_50840 s5v S_s5; cld8 F_50844 D_50844 s6v S_s6; cld8 F_50848 D_50848 s7v S_s7;
      cld8 F_5084c D_5084c s8v S_s8; cld8 F_50850 D_50850 s9v S_s9;
      an F_50854 D_50854;                              (* [comment removed for export] *)
      aret F_50858 D_50858 ra.                         (* [comment removed for export] *)

  Lemma la_t2bg :
    exists r, msteps ASEGS (mkst regs (0x507b8 : word) M rom)
                           (mkst r ra (la_m2 M mb nch PA idx msz naw sumw la_mxg' blw w16 w24) rom)
      /\ la_post1g r.
  Proof using S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra SOK_inst SOK_pa SOK_h R_24 R_16 R_bl R_mx R_cur R_na R_pa HPAsp Hmbsp HPAmb HPA Hmb Hcz Hnch Hsize Hret Hsp H13 H21 H19 H18 H9 H8 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold la_post1g, la_mxg' in G in change_no_check G' end).
    destruct Hnch as (N1 & N2). destruct Hmb as [MB1 MB2]. destruct HPA as [PA1 PA2]. pose proof (u64_range sp) as Hspr.
    assert (LF : (size + 4096 <= la_msz size <= size + 8191)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct (Z.ltb (U sumw) (U mxw)) eqn:ELT.
    - apply Z.ltb_lt in ELT.
      wd_eexists. split.
      + t2b_head.
        ab_tk F_507f0 D_507f0 ltac:(first [condz | (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); apply Z.ltb_lt; exact ELT]).   (* [comment removed for export] *)
        t2b_tail.
        wd_refl.
      + post. ra_solve.
    - apply Z.ltb_ge in ELT.
      wd_eexists. split.
      + t2b_head.
        ab_ft F_507f0 D_507f0 ltac:(first [condz | (lazymatch goal with |- ?G => let G' := eval unfold c_ltu, bv_ltu in G in change_no_check G' end); apply Z.ltb_ge; exact ELT]).   (* [comment removed for export] *)
        an F_507f4 D_507f4.                            (* [comment removed for export] *)
        t2b_tail.
        wd_refl.
      + post. ra_solve.
  Qed.
End T2BG.

Section T2G.
  Variables (M rom : word -> option byte) (sp stats : word) (size mb nch nres PA cz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hnch : (0 <= nch < 2 ^ 20 /\ 0 <= nres < 2 ^ 64)%Z.
  Hypothesis Hclz : (U (swar_clz (Z_to_bv 64 (la_msz size))) = cz /\ 0 <= cz <= 63)%Z.
  Hypothesis R_nch : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

  (* [comment removed for export] *)
  Lemma la_t2a1g :
    exists r, msteps ASEGS (mkst regs (0x50700 : word) M rom) (mkst r (0x5076c : word) M rom)
      /\ getr r 11 = swar_smear (Z_to_bv 64 (la_msz size)) /\ getr r 13 = Z_to_bv 64 nch
      /\ getr r 12 = Z_to_bv 64 0x5555555555555555 /\ getr r 14 = Z_to_bv 64 0x3333333333333333 /\ getr r 15 = Z_to_bv 64 0x0f0f0f0f0f0f0f0f
      /\ regs_agree (fun i : reg => In i [11; 12; 13; 14; 15; 16]) regs r.
  Proof using R_nch Hnch HR nres stats sp.
    destruct HR as (R2 & R8 & R9 & R18 & R19 & R24). destruct Hnch as (N1 & N3).
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - cld8 F_506f8 D_506f8 (Z_to_bv 64 nch) R_nch.     (* [comment removed for export] *)
      av F_506fc D_506fc (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); unorm; rewrite Z.shiftr_div_pow2 by lia; f_equal; apply Z.div_small; lia).   (* [comment removed for export] *)
      ab_ft F_50700 D_50700 ltac:(condz).              (* [comment removed for export] *)
      an F_50704 D_50704. an F_50708 D_50708. an F_5070c D_5070c. an F_50710 D_50710. an F_50714 D_50714.
      an F_50718 D_50718. an F_5071c D_5071c. an F_50720 D_50720. an F_50724 D_50724. an F_50728 D_50728.
      an F_5072c D_5072c. an F_50730 D_50730. an F_50734 D_50734. an F_50738 D_50738. an F_5073c D_5073c.
      an F_50740 D_50740. an F_50744 D_50744. an F_50748 D_50748. an F_5074c D_5074c. an F_50750 D_50750.
      an F_50754 D_50754. an F_50758 D_50758. an F_5075c D_5075c. an F_50760 D_50760.
      wd_refl.
    - split; [gres; reflexivity|]. split; [gres; reflexivity|].
      split; [gres; apply bv_eq; vm_compute; reflexivity|]. split; [gres; apply bv_eq; vm_compute; reflexivity|].
      split; [gres; apply bv_eq; vm_compute; reflexivity|]. ra_solve.
  Qed.
End T2G.

(* [comment removed for export] *)
Section T2PG.
  Variables (M rom : word -> option byte) (smw : word) (nres : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x103f18 + 64).
  Hypothesis H11 : getr regs 11 = smw.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 0x5555555555555555.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 0x3333333333333333.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 0x0f0f0f0f0f0f0f0f.
  Hypothesis R_nres : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).
  Lemma la_t2a2g :
    exists r, msteps ASEGS (mkst regs (0x5076c : word) M rom) (mkst r (0x507b4 : word) M rom)
      /\ getr r 19 = swar_pop smw /\ getr r 14 = Z_to_bv 64 nres
      /\ regs_agree (fun i : reg => In i [11; 12; 14; 16; 19]) regs r.
  Proof using R_nres H15 H14 H12 H11 H9.
    wd_eexists. split.
    - an F_50764 D_50764. an F_50768 D_50768. an F_5076c D_5076c. an F_50770 D_50770. an F_50774 D_50774. an F_50778 D_50778.
      an F_5077c D_5077c. an F_50780 D_50780.
      cld8 F_50784 D_50784 (Z_to_bv 64 nres) R_nres.   (* [comment removed for export] *)
      an F_50788 D_50788. an F_5078c D_5078c. an F_50790 D_50790. an F_50794 D_50794. an F_50798 D_50798.
      an F_5079c D_5079c. an F_507a0 D_507a0. an F_507a4 D_507a4. an F_507a8 D_507a8.
      wd_refl.
    - split; [gres; rwH; reflexivity|]. split; [gres; reflexivity|]. ra_solve.
  Qed.
End T2PG.

Section T2CG.
  Variables (M rom : word -> option byte) (sp stats : word) (size mb nch nres PA cz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hnch : (0 <= nch < 2 ^ 20 /\ 0 <= nres < 2 ^ 64)%Z.
  Hypothesis Hclz : (U (swar_clz (Z_to_bv 64 (la_msz size))) = cz /\ 0 <= cz <= 63)%Z.
  Hypothesis R_nch : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn ASEGS M (Z_to_bv 64 (0x103f18 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

  Lemma la_t2ag :
    exists r, msteps ASEGS (mkst regs (0x50700 : word) M rom) (mkst r (0x507b4 : word) M rom)
      /\ getr r 19 = Z_to_bv 64 cz /\ getr r 13 = Z_to_bv 64 nch /\ getr r 14 = Z_to_bv 64 nres
      /\ regs_agree (fun i : reg => In i [11; 12; 13; 14; 15; 16; 19]) regs r.
  Proof using R_nres R_nch Hclz Hnch Hsize Hsp HR size stats sp.
    destruct Hclz as [CZ1 CZ2].
    destruct (la_t2a1g M rom sp stats size nch nres regs HR Hnch R_nch) as (r1 & RUN1 & A11 & A13 & A12 & A14 & A15 & AG1).
    assert (A9 : getr r1 9 = Z_to_bv 64 (0x103f18 + 64)).
    { rewrite (AG1 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[E|[E|[E|[E|[]]]]]]]; discriminate E). destruct HR as (_ & _ & R9 & _). exact R9. }
    destruct (la_t2a2g M rom (swar_smear (Z_to_bv 64 (la_msz size))) nres r1 A9 A11 A12 A14 A15 R_nres) as (r2 & RUN2 & B19 & B14 & AG2).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [rewrite B19; fold (swar_clz (Z_to_bv 64 (la_msz size))); rewrite <- CZ1; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [rewrite (AG2 13%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[E|[E|[E|[]]]]]]; discriminate E); exact A13|].
    split; [exact B14|].
    intros x Hx. rewrite (AG2 x) by (intros Hin; apply Hx; cbn [In] in *; tauto). apply AG1. intros Hin; apply Hx; cbn [In] in *; tauto.
  Qed.

End T2CG.
End FPGen.

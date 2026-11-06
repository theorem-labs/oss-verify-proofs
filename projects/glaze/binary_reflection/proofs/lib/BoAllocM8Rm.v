(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocM8g.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub v_and v_or] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
           first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].

Section FPGen.
Context {fx : FPState}.

Definition gfp_frame (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-48)) (LE8 s4v))
    (at_ sp (-56)) (LE8 s5v))
    (at_ sp (-64)) (LE8 s6v))
    (at_ sp (-72)) (LE8 s7v))
    (at_ sp (-80)) (LE8 s8v))
    (at_ sp (-88)) (LE8 s9v))
    (at_ sp (-96)) (LE8 s10v))
    (at_ sp (-104)) (LE8 s11v).
Definition gfp_m1 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (RIz : Z) : word -> option byte :=
  wbytes (gfp_frame mem sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 (2 ^ 60))).
#[local] Hint Unfold gfp_frame gfp_m1 : asfr.

(* [comment removed for export] *)
Definition gfp_regs (sp chp : word) (RIz SPB c n : Z) (r : bvmap 5 word) : Prop :=
  getr r 2 = at_ sp (-128) /\ getr r 8 = Z_to_bv 64 RIz /\ getr r 9 = Z_to_bv 64 0x10ab58 /\ getr r 18 = Z_to_bv 64 (RIz + 8)
  /\ getr r 19 = Z_to_bv 64 (2 ^ 61) /\ getr r 20 = Z_to_bv 64 (SPB + c * 2 ^ 32 + 0xE0000000)
  /\ getr r 21 = chp /\ getr r 22 = Z_to_bv 64 n.

Section PRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v stats chp : word) (SPB c n nf : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = chp.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 n.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v. Hypothesis H23 : getr regs 23 = s7v. Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v. Hypothesis H26 : getr regs 26 = s10v. Hypothesis H27 : getr regs 27 = s11v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hn : (0 <= nf < n /\ n <= 8)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 + 4096 < 2 ^ 63 /\ SPB mod 8 = 0)%Z.
  Hypothesis HRI : (AIMGHI <= SPB /\ RIz + 128 <= U sp - 128)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-128)) 128 = true.
  Hypothesis C_sbeg : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis C_rib : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (SPB + 2 ^ 37))).
  Hypothesis R_mtx : rdn BSEGS mem (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_nf : rdn BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOK_mtx : store_ok BSEGS mem (Z_to_bv 64 RIz) 8 = true.

  #[local] Abbreviation MF := (gfp_frame mem sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v).
  #[local] Abbreviation M1 := (gfp_m1 mem sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v RIz).

  Lemma gfp_pre :
    exists r, msteps BSEGS (mkst regs (0x5153c : word) mem rom) (mkst r (0x51844 : word) M1 rom)
      /\ gfp_regs sp chp RIz SPB c n r /\ getr r 1 = Z_to_bv 64 0x517f8
      /\ getr r 10 = Z_to_bv 64 0x10ab58 /\ getr r 11 = stats /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = Z_to_bv 64 RIz
      /\ getr r 14 = Z_to_bv 64 (n - nf)
      /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28]) regs r.
  Proof using SOK_mtx R_nf R_mtx C_rib C_sbeg Hstk HRI HSPB Hn Hc Hsp H27 H26 H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H2 H1.
    (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as [N1 N2].
    assert (RI8 : (RIz mod 8 = 0)%Z) by (clear - S3 Hc; Z.div_mod_to_equations; lia).
    wd_eexists. split.
    - an F_5153c D_5153c.                              (* [comment removed for export] *)
      fsd F_51540 D_51540 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_51544 D_51544 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_51548 D_51548 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_5154c D_5154c (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_51550 D_51550 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_51554 D_51554 (at_ sp (-48)).              (* [comment removed for export] *)
      fsd F_51558 D_51558 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_5155c D_5155c (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_51560 D_51560 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_51564 D_51564 (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_51568 D_51568 (at_ sp (-88)).              (* [comment removed for export] *)
      fsd F_5156c D_5156c (at_ sp (-96)).              (* [comment removed for export] *)
      fsd F_51570 D_51570 (at_ sp (-104)).             (* [comment removed for export] *)
      change (wbytes _ _ _) with MF.
      an F_51574 D_51574.                              (* [comment removed for export] *)
      an F_51578 D_51578.                              (* [comment removed for export] *)
      an F_5157c D_5157c.                              (* [comment removed for export] *)
      cld8 F_51580 D_51580 (Z_to_bv 64 SPB) C_sbeg.    (* [comment removed for export] *)
      cld8 F_51584 D_51584 (Z_to_bv 64 (SPB + 2 ^ 37)) C_rib.   (* [comment removed for export] *)
      av F_51588 D_51588 (Z_to_bv 64 (128 * c)) ltac:(vz).   (* [comment removed for export] *)
      av F_5158c D_5158c (Z_to_bv 64 (c * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      an F_51590 D_51590.                              (* [comment removed for export] *)
      an F_51594 D_51594.                              (* [comment removed for export] *)
      av F_51598 D_51598 (Z_to_bv 64 (2 ^ 61)) ltac:(vz).   (* [comment removed for export] *)
      av F_5159c D_5159c (Z_to_bv 64 0xE0000000) ltac:(vz).   (* [comment removed for export] *)
      av F_515a0 D_515a0 (Z_to_bv 64 (2 ^ 40)) ltac:(vz).   (* [comment removed for export] *)
      av F_515a4 D_515a4 (Z_to_bv 64 (c * 2 ^ 32 + 0xE0000000)) ltac:(vz).   (* [comment removed for export] *)
      av F_515a8 D_515a8 (Z_to_bv 64 (2 ^ 40 + 1)) ltac:(vz).   (* [comment removed for export] *)
      av F_515ac D_515ac (Z_to_bv 64 (2 ^ 60 + 2 ^ 20)) ltac:(vz).   (* [comment removed for export] *)
      av F_515b0 D_515b0 (Z_to_bv 64 RIz) ltac:(vz).   (* [comment removed for export] *)
      av F_515b4 D_515b4 (Z_to_bv 64 (SPB + c * 2 ^ 32 + 0xE0000000)) ltac:(vz).   (* [comment removed for export] *)
      av F_515b8 D_515b8 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20 - 1)) ltac:(vz).   (* [comment removed for export] *)
      cld8 F_515bc D_515bc (Z_to_bv 64 0) R_mtx.       (* [comment removed for export] *)
      av F_515c0 D_515c0 (Z_to_bv 64 (RIz + 8)) ltac:(vz).   (* [comment removed for export] *)
      av F_515c4 D_515c4 (Z_to_bv 64 (2 ^ 60)) ltac:(vz).   (* [comment removed for export] *)
      an F_515c8 D_515c8.                              (* [comment removed for export] *)
      an F_515cc D_515cc.                              (* [comment removed for export] *)
      an F_515d0 D_515d0.                              (* [comment removed for export] *)
      an F_515d4 D_515d4.                              (* [comment removed for export] *)
      ab_ft F_515d8 D_515d8 ltac:(condz).              (* [comment removed for export] *)
      an F_515dc D_515dc.                              (* [comment removed for export] *)
      an F_515e0 D_515e0.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run BSEGS _ (0x515e4 : word) (0x515e8 : word) (0x515ec : word) (0x515f0 : word) (0x515f4 : word) MF rom
                  _ _ _ _ _ _ _ _ 5 8 7 6 5 17 BC_NE _ _ (LE8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
                  F_515e4 eq_refl D_515e4 F_515e8 eq_refl D_515e8 F_515ec eq_refl D_515ec F_515f0 eq_refl D_515f0).
        all: lazymatch goal with
             | |- v_addi _ _ = _ => first [reflexivity | apply bv_eq; vm_compute; reflexivity]
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; rwH; unorm; exact RI8
             | |- rdn _ _ _ _ = _ => gres; rwH; rd_peel; exact R_mtx
             | |- store_ok _ _ _ _ = true => gres; rwH; any_ok
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite bv_eqb_refl; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres. rwH.
      change (wbytes MF _ _) with M1.
      ab_tk F_515f4 D_515f4 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_5168c D_5168c (Z_to_bv 64 nf) R_nf.       (* [comment removed for export] *)
      ab_tk F_51690 D_51690 ltac:(condz).              (* [comment removed for export] *)
      an F_517dc D_517dc.                              (* [comment removed for export] *)
      an F_517e0 D_517e0.                              (* [comment removed for export] *)
      an F_517e4 D_517e4.                              (* [comment removed for export] *)
      av F_517e8 D_517e8 (Z_to_bv 64 (n - nf)) ltac:(vz).   (* [comment removed for export] *)
      an F_517ec D_517ec.                              (* [comment removed for export] *)
      an F_517f0 D_517f0.                              (* [comment removed for export] *)
      an F_517f4 D_517f4.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v msk : word) (RIz res : Z).
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 128 /\ RIz mod 8 = 0)%Z.
  Hypothesis Hres : (0 <= res <= 1)%Z.
  Hypothesis R_mtx : rdn BSEGS M (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Hypothesis R_msk : rdn BSEGS M (Z_to_bv 64 0x10468) 8 = Some (LE8 msk).
  Hypothesis SOK_mtx : store_ok BSEGS M (Z_to_bv 64 RIz) 8 = true.
  Hypothesis S_ra : rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn BSEGS M (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn BSEGS M (at_ sp (-64)) 8 = Some (LE8 s6v).
  Hypothesis S_s7 : rdn BSEGS M (at_ sp (-72)) 8 = Some (LE8 s7v).
  Hypothesis S_s8 : rdn BSEGS M (at_ sp (-80)) 8 = Some (LE8 s8v).
  Hypothesis S_s9 : rdn BSEGS M (at_ sp (-88)) 8 = Some (LE8 s9v).
  Hypothesis S_s10 : rdn BSEGS M (at_ sp (-96)) 8 = Some (LE8 s10v).
  Hypothesis S_s11 : rdn BSEGS M (at_ sp (-104)) 8 = Some (LE8 s11v).

  Definition gfp_post (regs r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 res /\ getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = s6v
    /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v /\ getr r 26 = s10v /\ getr r 27 = s11v
    /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]) regs r.

  Lemma gfp_tail : forall regs : bvmap 5 word,
    getr regs 2 = at_ sp (-128) -> getr regs 8 = Z_to_bv 64 RIz -> getr regs 9 = Z_to_bv 64 res -> getr regs 19 = Z_to_bv 64 (2 ^ 61) ->
    exists r, msteps BSEGS (mkst regs (0x516d4 : word) M rom) (mkst r ra (wbytes M (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0))) rom)
      /\ gfp_post regs r.
  Proof using S_s11 S_s10 S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra SOK_mtx R_msk R_mtx HRI Hret Hsp msk.
    intros regs H2 H8 H9 H19. (lazymatch goal with |- ?G => let G' := eval unfold gfp_post in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. destruct HRI as (RI1 & RI2 & RI8).
    wd_eexists. split.
    - cld8 F_516d4 D_516d4 (Z_to_bv 64 (2 ^ 60)) R_mtx.   (* [comment removed for export] *)
      an F_516d8 D_516d8.                              (* [comment removed for export] *)
      an F_516dc D_516dc.                              (* [comment removed for export] *)
      an F_516e0 D_516e0.                              (* [comment removed for export] *)
      an F_516e4 D_516e4.                              (* [comment removed for export] *)
      an F_516e8 D_516e8.                              (* [comment removed for export] *)
      an F_516ec D_516ec.                              (* [comment removed for export] *)
      an F_516f0 D_516f0.                              (* [comment removed for export] *)
      cld8 F_516f4 D_516f4 msk R_msk.                  (* [comment removed for export] *)
      an F_516f8 D_516f8.                              (* [comment removed for export] *)
      an F_516fc D_516fc.                              (* [comment removed for export] *)
      an F_51700 D_51700.                              (* [comment removed for export] *)
      an F_51704 D_51704.                              (* [comment removed for export] *)
      an F_51708 D_51708.                              (* [comment removed for export] *)
      an F_5170c D_5170c.                              (* [comment removed for export] *)
      an F_51728 D_51728.                              (* [comment removed for export] *)
      an F_5172c D_5172c.                              (* [comment removed for export] *)
      ab_ft F_51730 D_51730 ltac:(condz).              (* [comment removed for export] *)
      an F_51734 D_51734.                              (* [comment removed for export] *)
      ab_tk F_51738 D_51738 ltac:(condz).              (* [comment removed for export] *)
      an F_5175c D_5175c.                              (* [comment removed for export] *)
      an F_51760 D_51760.                              (* [comment removed for export] *)
      an F_51764 D_51764.                              (* [comment removed for export] *)
      an F_51768 D_51768.                              (* [comment removed for export] *)
      an F_5176c D_5176c.                              (* [comment removed for export] *)
      an F_51770 D_51770.                              (* [comment removed for export] *)
      an F_51774 D_51774.                              (* [comment removed for export] *)
      ab_tk F_51778 D_51778 ltac:(condz).              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_d_run BSEGS _ (0x51710 : word) (0x51714 : word) (0x51718 : word) (0x5171c : word) (0x51720 : word) M rom
                  _ _ _ _ _ _ _ _ 7 8 28 6 7 12 BC_NE _ _ (LE8 (Z_to_bv 64 (2 ^ 60))) (Z_to_bv 64 (2 ^ 60))
                  F_51710 eq_refl D_51710 F_51714 eq_refl D_51714 F_51718 eq_refl D_51718 F_5171c eq_refl D_5171c).
        all: lazymatch goal with
             | |- v_addi _ _ = _ => first [reflexivity | apply bv_eq; vm_compute; reflexivity]
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 8 = 0)%Z => gres; rwH; unorm; exact RI8
             | |- rdn _ _ _ _ = _ => gres; rwH; exact R_mtx
             | |- store_ok _ _ _ _ = true => gres; rwH; exact SOK_mtx
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite bv_eqb_refl; reflexivity
             | |- _ => apply bytes_le_to_Z_8
             end. }
      gres. rwH.
      ab_tk F_51720 D_51720 ltac:(condz).              (* [comment removed for export] *)
      ab_tk F_51788 D_51788 ltac:(condz).              (* [comment removed for export] *)
      an F_5179c D_5179c.                              (* [comment removed for export] *)
      cld8 F_517a0 D_517a0 ra S_ra.                    (* [comment removed for export] *)
      cld8 F_517a4 D_517a4 s0v S_s0.                   (* [comment removed for export] *)
      cld8 F_517a8 D_517a8 s1v S_s1.                   (* [comment removed for export] *)
      cld8 F_517ac D_517ac s2v S_s2.                   (* [comment removed for export] *)
      cld8 F_517b0 D_517b0 s3v S_s3.                   (* [comment removed for export] *)
      cld8 F_517b4 D_517b4 s4v S_s4.                   (* [comment removed for export] *)
      cld8 F_517b8 D_517b8 s5v S_s5.                   (* [comment removed for export] *)
      cld8 F_517bc D_517bc s6v S_s6.                   (* [comment removed for export] *)
      cld8 F_517c0 D_517c0 s7v S_s7.                   (* [comment removed for export] *)
      cld8 F_517c4 D_517c4 s8v S_s8.                   (* [comment removed for export] *)
      cld8 F_517c8 D_517c8 s9v S_s9.                   (* [comment removed for export] *)
      cld8 F_517cc D_517cc s10v S_s10.                 (* [comment removed for export] *)
      cld8 F_517d0 D_517d0 s11v S_s11.                 (* [comment removed for export] *)
      an F_517d4 D_517d4.                              (* [comment removed for export] *)
      aret F_517d8 D_517d8 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma gfp_fail : forall regs : bvmap 5 word, res = 0%Z ->
    getr regs 2 = at_ sp (-128) -> getr regs 8 = Z_to_bv 64 RIz -> getr regs 19 = Z_to_bv 64 (2 ^ 61) -> getr regs 10 = Z_to_bv 64 0 ->
    exists r, msteps BSEGS (mkst regs (0x517f8 : word) M rom) (mkst r ra (wbytes M (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0))) rom)
      /\ gfp_post regs r.
  Proof using S_s11 S_s10 S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra SOK_mtx R_msk R_mtx Hres HRI Hret Hsp msk.
    intros regs Eres H2 H8 H19 H10. pose proof (u64_range sp) as Hspr.
    assert (HEAD : exists r1, msteps BSEGS (mkst regs (0x517f8 : word) M rom) (mkst r1 (0x516d4 : word) M rom)
              /\ getr r1 2 = at_ sp (-128) /\ getr r1 8 = Z_to_bv 64 RIz /\ getr r1 9 = Z_to_bv 64 res /\ getr r1 19 = Z_to_bv 64 (2 ^ 61)
              /\ regs_agree (fun i : reg => In i [9; 10]) regs r1).
    { wd_eexists. split.
      - ab_tk F_517f8 D_517f8 ltac:(condz).            (* [comment removed for export] *)
        an F_5181c D_5181c.                            (* [comment removed for export] *)
        an F_51820 D_51820.                            (* [comment removed for export] *)
        an F_51824 D_51824.                            (* [comment removed for export] *)
        wd_refl.
      - rewrite Eres. post. ra_solve. }
    destruct HEAD as (r1 & RUN1 & A2 & A8 & A9 & A19 & AG1).
    destruct (gfp_tail r1 A2 A8 A9 A19) as (r2 & RUN2 & P2).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    unfold gfp_post in *. destruct P2 as (B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    repeat (split; [assumption|]).
    intros x Hx. rewrite (AG2 x Hx). apply AG1. intros Hin. apply Hx. cbn [In] in *. tauto.
  Qed.
End TAIL.
End FPGen.
End BoAllocM8g.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8h.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7g BoAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
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

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Fixpoint gh_cp (M2 : word -> option byte) (chp : word) (faf : Z -> Z) (lo : Z) (i : nat) : word -> option byte :=
  match i with
  | O => M2
  | S i' => wbytes (gh_cp M2 chp faf lo i') (at_ chp (4 * Z.of_nat i')) (LE4 (faf (lo + Z.of_nat i')%Z))
  end.
Lemma gh_cp_grows : forall M2 chp faf lo i, mem_grows M2 (gh_cp M2 chp faf lo i).
Proof using. induction i as [|i IH]; [apply mem_grows_refl|]. (lazymatch goal with |- ?G => let G' := eval cbn [gh_cp] in G in change_no_check G' end). eapply mem_grows_trans; [exact IH | apply wbytes_grows]. Qed.
Lemma gh_cp_outside : forall M2 chp faf lo i (x : word), (U chp + 4 * Z.of_nat i < 2 ^ 64)%Z ->
  (U x < U chp \/ U chp + 4 * Z.of_nat i <= U x)%Z -> gh_cp M2 chp faf lo i x = M2 x.
Proof using.
  induction i as [|i IH]; intros x Hn Hx; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [gh_cp] in G in change_no_check G' end). pose proof (u64_range chp).
  destruct Hx as [Hx|Hx].
  - rewrite wbytes_below; [apply IH; lia | rewrite length_N_to_le_bytes, at_u by lia; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  - rewrite wbytes_above; [apply IH; lia | rewrite length_N_to_le_bytes, at_u by lia; lia].
Qed.

Definition gh_m2 (MP : word -> option byte) (RIz nf2 n : Z) : word -> option byte :=
  wbytes MP (Z_to_bv 64 (RIz + 16)) (LE8 (Z_to_bv 64 (nf2 - n))).
Definition gh_m4 (MP : word -> option byte) (chp stv : word) (faf : Z -> Z) (RIz nf2 n : Z) : word -> option byte :=
  wbytes (gh_cp (gh_m2 MP RIz nf2 n) chp faf (nf2 - n) (Z.to_nat n)) (Z_to_bv 64 (RIz + 72)) (LE8 (v_add stv (Z_to_bv 64 n))).
Definition gh_m5 (MP : word -> option byte) (chp stv : word) (faf : Z -> Z) (RIz nf2 n : Z) : word -> option byte :=
  wbytes (gh_m4 MP chp stv faf RIz nf2 n) (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0)).

Section OK.
  Variables (MP rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v chp stv msk : word)
            (SPB c n nf2 : Z) (faf : Z -> Z).
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  #[local] Abbreviation FAB := (SPB + c * 2 ^ 32 + 0xE0000000)%Z.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hn : (1 <= n <= 8 /\ n <= nf2 /\ nf2 <= 2 ^ 27)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 + 4096 < 2 ^ 63 /\ SPB mod 8 = 0)%Z.
  Hypothesis HRI : (AIMGHI <= SPB /\ RIz + 128 <= U sp - 128)%Z.
  (* [comment removed for export] *)
  Hypothesis Hchp : ((U chp + 4 * n <= SPB \/ SPB + 2 ^ 37 + 4096 <= U chp) /\ U chp + 4 * n <= U sp - 128 /\ (AIMGHI <= U chp \/ U chp + 4 * n <= AIMGLO))%Z.
  Hypothesis R_nf : rdn BSEGS MP (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf2)).
  Hypothesis R_st : rdn BSEGS MP (Z_to_bv 64 (RIz + 72)) 8 = Some (LE8 stv).
  Hypothesis R_mtx : rdn BSEGS MP (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Hypothesis R_msk : rdn BSEGS MP (Z_to_bv 64 0x10468) 8 = Some (LE8 msk).
  Hypothesis SOK_RI : store_ok BSEGS MP (Z_to_bv 64 RIz) 128 = true.
  Hypothesis SOK_ch : store_ok BSEGS MP chp (Z.to_nat (4 * n)) = true.
  Hypothesis Hfaf : forall j, (nf2 - n <= j < nf2)%Z -> rdn BSEGS MP (Z_to_bv 64 (FAB + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.

  #[local] Abbreviation M2 := (gh_m2 MP RIz nf2 n).
  #[local] Abbreviation CP := (gh_cp (gh_m2 MP RIz nf2 n) chp faf (nf2 - n)).

  Lemma gh_m2_outside : forall x : word, (U x < RIz + 16 \/ RIz + 24 <= U x)%Z -> M2 x = MP x.
  Proof using HRI HSPB Hn Hc Hsp sp.
    intros x Hx. destruct HSPB as (S1 & S2 & S3). (lazymatch goal with |- ?G => let G' := eval unfold gh_m2 in G in change_no_check G' end).
    destruct Hx as [Hx|Hx]; [apply wbytes_below | apply wbytes_above]; wd_lenlit; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma gh_head : forall regs : bvmap 5 word, gfp_regs sp chp RIz SPB c n regs -> getr regs 10 = Z_to_bv 64 1 ->
    exists r, msteps BSEGS (mkst regs (0x517f8 : word) MP rom) (mkst r (0x516b0 : word) M2 rom)
      /\ getr r 2 = at_ sp (-128) /\ getr r 8 = Z_to_bv 64 RIz /\ getr r 19 = Z_to_bv 64 (2 ^ 61)
      /\ getr r 13 = chp /\ getr r 20 = Z_to_bv 64 (FAB + 4 * (nf2 - n)) /\ getr r 11 = at_ chp (4 * n) /\ getr r 14 = Z_to_bv 64 n
      /\ regs_agree (fun i : reg => In i [10; 11; 13; 14; 15; 20]) regs r.
  Proof using SOK_RI R_nf Hchp HRI HSPB Hn Hc Hsp.
    intros regs HR H10. destruct HR as (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R22).
    pose proof (u64_range sp) as Hspr. pose proof (u64_range chp) as Hchr. destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as (N1 & N2 & N3).
    wd_eexists. split.
    - ab_ft F_517f8 D_517f8 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_517fc D_517fc (Z_to_bv 64 nf2) R_nf.      (* [comment removed for export] *)
      an F_51800 D_51800.                              (* [comment removed for export] *)
      ab_ft F_51804 D_51804 ltac:(condz).              (* [comment removed for export] *)
      an F_51808 D_51808.                              (* [comment removed for export] *)
      av F_5180c D_5180c (Z_to_bv 64 (nf2 - n)) ltac:(vz).   (* [comment removed for export] *)
      fsd F_51810 D_51810 (Z_to_bv 64 (RIz + 16)).     (* [comment removed for export] *)
      change (wbytes MP _ _) with M2.
      an F_51814 D_51814.                              (* [comment removed for export] *)
      an F_51818 D_51818.                              (* [comment removed for export] *)
      av F_516a0 D_516a0 (Z_to_bv 64 (4 * (nf2 - n))) ltac:(vz).   (* [comment removed for export] *)
      av F_516a4 D_516a4 (Z_to_bv 64 (FAB + 4 * (nf2 - n))) ltac:(vz).   (* [comment removed for export] *)
      av F_516a8 D_516a8 (Z_to_bv 64 (4 * n)) ltac:(vz).   (* [comment removed for export] *)
      av F_516ac D_516ac (at_ chp (4 * n)) ltac:(rewrite v_add_at by lia; reflexivity).   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma gh_loop : forall (j i : nat) (r : bvmap 5 word),
      (Z.of_nat i + Z.of_nat j = n)%Z -> (1 <= Z.of_nat j)%Z ->
      getr r 13 = at_ chp (4 * Z.of_nat i) -> getr r 20 = Z_to_bv 64 (FAB + 4 * (nf2 - n) + 4 * Z.of_nat i) -> getr r 11 = at_ chp (4 * n) ->
      exists r',
        msteps BSEGS (mkst r (0x516b0 : word) (CP i) rom) (mkst r' (0x516c4 : word) (CP (Z.to_nat n)) rom)
        /\ (forall x : reg, ~ In x [12; 13; 20] -> getr r' x = getr r x).
  Proof using Hfaf SOK_ch Hchp HRI HSPB Hn Hc Hsp sp.
    induction j as [|j IH]; intros i r Hij Hj R13 R20 R11; [lia|].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range chp) as Hchr.
    destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as (N1 & N2 & N3). destruct Hchp as (C1 & C2 & _).
    destruct (Hfaf (nf2 - n + Z.of_nat i)%Z ltac:(lia)) as [Rf Bf].
    assert (RD : rdn BSEGS (CP i) (Z_to_bv 64 (FAB + 4 * (nf2 - n) + 4 * Z.of_nat i)) 4 = Some (LE4 (faf (nf2 - n + Z.of_nat i)%Z))).
    { rewrite <- Rf. replace (FAB + 4 * (nf2 - n + Z.of_nat i))%Z with (FAB + 4 * (nf2 - n) + 4 * Z.of_nat i)%Z by lia.
      apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
      rewrite gh_cp_outside by lia. apply gh_m2_outside. lia. }
    assert (SOK : store_ok BSEGS (CP i) (at_ chp (4 * Z.of_nat i)) 4 = true).
    { eapply store_ok_mono; [eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows]|].
      eapply (store_ok_sub BSEGS MP chp _ (Z.to_nat (4 * n))); [lia | exact SOK_ch | rewrite at_u; lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia]. }
    assert (BODY : exists r1, msteps BSEGS (mkst r (0x516b0 : word) (CP i) rom) (mkst r1 (0x516c0 : word) (CP (S i)) rom)
              /\ getr r1 13 = at_ chp (4 * Z.of_nat (S i)) /\ getr r1 20 = Z_to_bv 64 (FAB + 4 * (nf2 - n) + 4 * Z.of_nat (S i)) /\ getr r1 11 = at_ chp (4 * n)
              /\ (forall x : reg, ~ In x [12; 13; 20] -> getr r1 x = getr r x)).
    { wd_eexists. split.
      - chain_step; [reflexivity
          | eapply step_lw with (bs := LE4 (faf (nf2 - n + Z.of_nat i)%Z)) (v := Z_to_bv 64 (faf (nf2 - n + Z.of_nat i)%Z));
            [exact F_516b0 | reflexivity | exact D_516b0 | gres; rewrite ?R20; imm_norm; rewrite ?v_addi_0; exact RD | apply bytes4_small; lia]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := at_ chp (4 * Z.of_nat i));
            [exact F_516b4 | reflexivity | exact D_516b4
            | gres; rewrite ?R13; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
            | gres; reflexivity
            | exact SOK ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        rewrite (LE4_lw (faf (nf2 - n + Z.of_nat i)%Z)) by lia.
        change (wbytes (CP i) _ _) with (CP (S i)).
        an F_516b8 D_516b8.                                (* [comment removed for export] *)
        an F_516bc D_516bc.                                (* [comment removed for export] *)
        wd_refl.
      - split; [gres; rewrite ?R13, ?at_addi, ?at_at; f_equal; lia|].
        split; [gres; rewrite ?R20; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia|].
        split; [gres; first [exact R11 | rewrite R11; reflexivity]|].
        intros x Hx. gres. rewrite !getr_other; try reflexivity; intros E; apply Hx; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
    destruct BODY as (r1 & RUN1 & Q13 & Q20 & Q11 & QK).
    destruct (Z.eq_dec (Z.of_nat j) 0) as [Zj|NZj].
    - exists r1. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_ft F_516c0 D_516c0 ltac:(rewrite ?Q13, ?Q11; condz).   (* [comment removed for export] *)
        replace (Z.to_nat n) with (S i) by lia. wd_refl.
      + exact QK.
    - destruct (IH (S i) r1 ltac:(lia) ltac:(lia) Q13 Q20 Q11) as (r' & RUN' & QK').
      exists r'. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_tk F_516c0 D_516c0 ltac:(rewrite ?Q13, ?Q11; condz).   (* [comment removed for export] *)
        exact RUN'.
      + intros x Hx. rewrite (QK' x Hx). exact (QK x Hx).
  Qed.

  #[local] Abbreviation M4 := (gh_m4 MP chp stv faf RIz nf2 n).

  Lemma gh_cpn_outside : forall x : word, (U x < U chp \/ U chp + 4 * n <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z ->
    CP (Z.to_nat n) x = MP x.
  Proof using Hchp HRI HSPB Hn Hc Hsp sp.
    intros x Hx Hy. pose proof (u64_range chp). destruct Hn as (N1 & N2 & N3). destruct Hchp as (C1 & C2 & _). pose proof (u64_range sp).
    rewrite gh_cp_outside; [apply gh_m2_outside; exact Hy | rewrite Z2Nat.id by lia; lia | rewrite Z2Nat.id by lia; exact Hx].
  Qed.
  Lemma gh_m4_outside : forall x : word, (U x < U chp \/ U chp + 4 * n <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z ->
    (U x < RIz + 72 \/ RIz + 80 <= U x)%Z -> M4 x = MP x.
  Proof using Hchp HRI HSPB Hn Hc Hsp sp.
    intros x Hx Hy Hz. destruct HSPB as (S1 & S2 & S3). (lazymatch goal with |- ?G => let G' := eval unfold gh_m4 in G in change_no_check G' end).
    destruct Hz as [Hz|Hz]; [rewrite wbytes_below | rewrite wbytes_above]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; try lia;
      apply gh_cpn_outside; assumption.
  Qed.
  Lemma gh_m4_grows : mem_grows MP M4.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gh_m4 in G in change_no_check G' end). eapply mem_grows_trans; [|apply wbytes_grows]. eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows]. Qed.

  (* [comment removed for export] *)
  Lemma gh_stats : forall regs : bvmap 5 word,
    getr regs 8 = Z_to_bv 64 RIz -> getr regs 14 = Z_to_bv 64 n ->
    exists r, msteps BSEGS (mkst regs (0x516c4 : word) (CP (Z.to_nat n)) rom) (mkst r (0x516d4 : word) M4 rom)
      /\ getr r 9 = Z_to_bv 64 1 /\ regs_agree (fun i : reg => In i [9; 11]) regs r.
  Proof using SOK_RI R_st Hchp HRI HSPB Hn Hc Hsp sp.
    intros regs H8 H14. pose proof (u64_range sp) as Hspr. pose proof (u64_range chp) as Hchr.
    destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as (N1 & N2 & N3). destruct Hchp as (C1 & C2 & _).
    assert (Rst3 : rdn BSEGS (CP (Z.to_nat n)) (Z_to_bv 64 (RIz + 72)) 8 = Some (LE8 stv)).
    { rewrite <- R_st. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
      apply gh_cpn_outside; lia. }
    assert (SOK3 : store_ok BSEGS (CP (Z.to_nat n)) (Z_to_bv 64 (RIz + 72)) 8 = true).
    { eapply store_ok_mono; [eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows]|].
      eapply (store_ok_sub BSEGS MP (Z_to_bv 64 RIz) _ 128); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact SOK_RI | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    wd_eexists. split.
    - chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 stv) (v := stv);
          [exact F_516c4 | reflexivity | exact D_516c4 | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; exact Rst3 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                               (* [comment removed for export] *)
      an F_516c8 D_516c8.                                (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := Z_to_bv 64 (RIz + 72));
          [exact F_516cc | reflexivity | exact D_516cc
          | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity
          | gres; rwH; reflexivity
          | exact SOK3 ]
        | step_simpl]; vn.                               (* [comment removed for export] *)
      change (wbytes (CP (Z.to_nat n)) _ _) with M4.
      an F_516d0 D_516d0.                                (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Hypothesis S_ra : rdn BSEGS MP (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS MP (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS MP (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS MP (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS MP (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn BSEGS MP (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn BSEGS MP (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn BSEGS MP (at_ sp (-64)) 8 = Some (LE8 s6v).
  Hypothesis S_s7 : rdn BSEGS MP (at_ sp (-72)) 8 = Some (LE8 s7v).
  Hypothesis S_s8 : rdn BSEGS MP (at_ sp (-80)) 8 = Some (LE8 s8v).
  Hypothesis S_s9 : rdn BSEGS MP (at_ sp (-88)) 8 = Some (LE8 s9v).
  Hypothesis S_s10 : rdn BSEGS MP (at_ sp (-96)) 8 = Some (LE8 s10v).
  Hypothesis S_s11 : rdn BSEGS MP (at_ sp (-104)) 8 = Some (LE8 s11v).

  Theorem gfp_ok : forall regs : bvmap 5 word, gfp_regs sp chp RIz SPB c n regs -> getr regs 10 = Z_to_bv 64 1 ->
    exists r, msteps BSEGS (mkst regs (0x517f8 : word) MP rom) (mkst r ra (gh_m5 MP chp stv faf RIz nf2 n) rom)
      /\ gfp_post sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v 1 regs r.
  Proof using S_s11 S_s10 S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hfaf SOK_ch SOK_RI R_msk R_mtx R_st R_nf Hchp HRI HSPB Hn Hc Hret Hsp msk.
    intros regs HR H10. pose proof (u64_range sp) as Hspr. pose proof (u64_range chp) as Hchr.
    destruct HSPB as (S1 & S2 & S3). destruct HRI as [RI1 RI2]. destruct Hn as (N1 & N2 & N3). destruct Hchp as (C1 & C2 & _).
    destruct (gh_head regs HR H10) as (r1 & RUN1 & A2 & A8 & A19 & A13 & A20 & A11 & A14 & AG1).
    destruct (gh_loop (Z.to_nat n) 0%nat r1 ltac:(rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(rewrite A13; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat] in G in change_no_check G' end); rewrite Z.mul_0_r, at_0; reflexivity)
                ltac:(rewrite A20; f_equal; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) A11) as (r2 & RUN2 & K2).
    assert (NI : forall x : reg, In x [2%bv; 8%bv; 14%bv; 19%bv] -> ~ In x [12%bv; 13%bv; 20%bv] : Prop).
    { intros x Hin Hx. cbn [In] in Hin, Hx.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; destruct Hx as [E|[E|[E|[]]]]; discriminate E. }
    destruct (gh_stats r2 ltac:(rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A8) ltac:(rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A14))
      as (r3 & RUN3 & B9 & AG3).
    (* [comment removed for export] *)
    assert (TR : forall (a : word) (k : nat) bs, (U a + Z.of_nat k <= 2 ^ 64)%Z ->
               (U a + Z.of_nat k <= U chp \/ U chp + 4 * n <= U a)%Z -> (U a + Z.of_nat k <= RIz + 16 \/ RIz + 24 <= U a)%Z ->
               (U a + Z.of_nat k <= RIz + 72 \/ RIz + 80 <= U a)%Z ->
               rdn BSEGS MP a k = Some bs -> rdn BSEGS M4 a k = Some bs).
    { intros a k bs Hk X1 X2 X3 R. rewrite <- R. apply rdn_ext; [exact Hk|]. intros x Hx. apply gh_m4_outside; lia. }
    Ltac trs TR H := apply TR; [first [rewrite at_u by lia | rewrite u_Z2bv by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                               | first [rewrite at_u by lia | rewrite u_Z2bv by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                               | first [rewrite at_u by lia | rewrite u_Z2bv by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                               | first [rewrite at_u by lia | rewrite u_Z2bv by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                               | exact H].
    assert (RI8 : (RIz mod 8 = 0)%Z) by (clear - S3 Hc; Z.div_mod_to_equations; lia).
    destruct (gfp_tail M4 rom sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v msk RIz 1 Hsp Hret
                ltac:(lia) ltac:(trs TR R_mtx) ltac:(trs TR R_msk)
                ltac:(eapply store_ok_mono; [apply gh_m4_grows|];
                      eapply (store_ok_sub BSEGS MP (Z_to_bv 64 RIz) _ 128); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact SOK_RI | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]])
                ltac:(trs TR S_ra) ltac:(trs TR S_s0) ltac:(trs TR S_s1) ltac:(trs TR S_s2) ltac:(trs TR S_s3) ltac:(trs TR S_s4)
                ltac:(trs TR S_s5) ltac:(trs TR S_s6) ltac:(trs TR S_s7) ltac:(trs TR S_s8) ltac:(trs TR S_s9) ltac:(trs TR S_s10) ltac:(trs TR S_s11)
                r3
                ltac:(rewrite (AG3 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[]]]; discriminate E); rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A2)
                ltac:(rewrite (AG3 8%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[]]]; discriminate E); rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A8)
                B9
                ltac:(rewrite (AG3 19%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[]]]; discriminate E); rewrite K2 by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); exact A19))
      as (r4 & RUN4 & P4).
    exists r4. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
    - unfold gfp_post in *. destruct P4 as (B10 & B2 & B1 & B8 & B9' & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG4).
      repeat (split; [assumption|]).
      intros x Hx. rewrite (AG4 x Hx).
      rewrite (AG3 x) by (intros Hin; apply Hx; clear - Hin; cbn [In] in *; tauto).
      rewrite K2 by (intros Hin; apply Hx; clear - Hin; cbn [In] in *; tauto).
      apply AG1. intros Hin; apply Hx; clear - Hin; cbn [In] in *; tauto.
  Qed.
End OK.
End FPGen.
End BoAllocM8h.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m BoAllocM8g BoAllocM8h.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.


Definition r1_mem (M : word -> option byte) (spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (RIz : Z) : word -> option byte :=
  gfp_m1 (wbytes (wbytes (wbytes M (at_ spR (-8)) (LE8 raR)) (at_ spR (-16)) (LE8 s0R)) (at_ spR (-24)) (LE8 s1R))
         (at_ spR (-32)) g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz.

Section R1MEM.
  Variables (segs : list Segment) (M : word -> option byte) (spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (RIz : Z).
  Hypothesis Hsp : 4096 <= U spR /\ U spR < 2 ^ 63.
  Hypothesis HRI : 0 <= RIz /\ RIz + 8 <= U spR - 160.
  #[local] Abbreviation M1 := (r1_mem M spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz).
  #[local] Abbreviation MR := (wbytes (wbytes (wbytes M (at_ spR (-8)) (LE8 raR)) (at_ spR (-16)) (LE8 s0R)) (at_ spR (-24)) (LE8 s1R)).
  #[local] Abbreviation spG := (at_ spR (-32)).

  Lemma r1_frame_outside : forall x : word, (U x < U spR - 160 \/ U spR - 32 <= U x) ->
    gfp_frame MR spG g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 x = MR x.
  Proof using Hsp.
    intros x Hx. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold gfp_frame in G in change_no_check G' end).
    repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                               | rewrite length_N_to_le_bytes, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma r1_mem_outside : forall x : word, (U x < U spR - 160 \/ U spR <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M1 x = M x.
  Proof using HRI Hsp.
    intros x X1 X2. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1 in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite r1_frame_outside by lia.
    repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma r1_mem_grows : mem_grows M M1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1, gfp_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma r1_mem_mrestrict : forall Hd : word -> bool, hid_off Hd (U spR - 160) 160 -> hid_off Hd RIz 8 ->
    r1_mem (mrestrict Hd M) spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz = mrestrict Hd M1.
  Proof using HRI Hsp.
    intros Hd O1 O2. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1, gfp_frame in G in change_no_check G' end).
    rewrite !wbytes_mrestrict; [reflexivity | ..];
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv, ?at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
      first [lia | intros x Hx; apply O1; lia | intros x Hx; apply O2; lia].
  Qed.
  Lemma r1_mem_lock : rdn segs M1 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Proof using HRI Hsp. destruct HRI as [R0 R1]. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1 in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.
  Lemma r1_mem_gslots : forall (k : Z) (v : word),
    In (k, v) [(-8, g_ra); (-16, g0); (-24, g1); (-32, g2); (-40, g3); (-48, g4); (-56, g5); (-64, g6); (-72, g7); (-80, g8); (-88, g9); (-96, g10); (-104, g11)] ->
    rdn segs M1 (at_ spG k) 8 = Some (LE8 v).
  Proof using HRI Hsp.
    intros k v Hin. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1].
    assert (K : -104 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1 in G in change_no_check G' end).
    rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, u_Z2bv, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                              | rewrite !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    (lazymatch goal with |- ?G => let G' := eval unfold gfp_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
  Lemma r1_mem_rslots : forall (k : Z) (v : word), In (k, v) [(-8, raR); (-16, s0R); (-24, s1R)] -> rdn segs M1 (at_ spR k) 8 = Some (LE8 v).
  Proof using HRI Hsp.
    intros k v Hin. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1].
    assert (K : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    rewrite (rdn_ext segs 8 M1 MR (at_ spR k)); [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | ].
    - cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
    - intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. (lazymatch goal with |- ?G => let G' := eval unfold r1_mem, gfp_m1 in G in change_no_check G' end).
      rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      apply r1_frame_outside. lia.
  Qed.
End R1MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
Definition r2_mem (MP : word -> option byte) (pc stv : word) (faf : Z -> Z) (RIz nf2 n : Z) : word -> option byte :=
  wbytes (gh_m5 MP (at_ pc 16) stv faf RIz nf2 n) pc (LE4 n).

Lemma gh_cp_mrestrict : forall (Hd : word -> bool) M2 (chp : word) faf lo i, U chp + 4 * Z.of_nat i < 2 ^ 64 ->
  hid_off Hd (U chp) (4 * Z.of_nat i) -> gh_cp (mrestrict Hd M2) chp faf lo i = mrestrict Hd (gh_cp M2 chp faf lo i).
Proof.
  induction i as [|i IH]; intros Hn Hh; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [gh_cp] in G in change_no_check G' end). pose proof (u64_range chp).
  rewrite IH by (first [lia | eapply hid_off_sub; [exact Hh | lia | lia]]).
  apply wbytes_mrestrict; rewrite length_N_to_le_bytes, at_u by lia; [lia | eapply hid_off_sub; [exact Hh | lia | lia]].
Qed.
Lemma gh_cp_entry : forall segs M2 (chp : word) faf lo (n i : nat), (i < n)%nat -> U chp + 4 * Z.of_nat n < 2 ^ 64 ->
  rdn segs (gh_cp M2 chp faf lo n) (at_ chp (4 * Z.of_nat i)) 4 = Some (LE4 (faf (lo + Z.of_nat i))).
Proof.
  intros segs M2 chp faf lo n. induction n as [|n IH]; intros i Hi Hn; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [gh_cp] in G in change_no_check G' end). pose proof (u64_range chp).
  destruct (Nat.eq_dec i n) as [->|NE].
  - apply rdn_wbytes_hit4. rewrite at_u by lia. lia.
  - rewrite rdn_wbytes_out; [apply IH; lia | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]
                            | rewrite length_N_to_le_bytes, at_u by lia; lia].
Qed.

Section R2MEM.
  Variables (segs : list Segment) (MP : word -> option byte) (pc stv : word) (faf : Z -> Z) (RIz nf2 n : Z).
  Hypothesis Hn : 1 <= n <= 8.
  Hypothesis Hpc : 0 <= U pc /\ U pc + 80 < 2 ^ 63.
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 < 2 ^ 63.
  Hypothesis HD : U pc + 80 <= RIz \/ RIz + 128 <= U pc.
  #[local] Abbreviation M2 := (r2_mem MP pc stv faf RIz nf2 n).

  Lemma r2_mem_outside : forall x : word, (U x < U pc \/ U pc + 4 <= U x) -> (U x < U pc + 16 \/ U pc + 16 + 4 * n <= U x) ->
    (U x < RIz \/ RIz + 8 <= U x) -> (U x < RIz + 16 \/ RIz + 24 <= U x) -> (U x < RIz + 72 \/ RIz + 80 <= U x) -> M2 x = MP x.
  Proof using HD HRI Hpc Hn.
    intros x X1 X2 X3 X4 X5. destruct Hpc as [P0 P1]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r2_mem, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite gh_cp_outside; [ | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia].
    apply MemsetLibF.MemSplit.wbytes_outside; [rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.
  Lemma r2_mem_grows : mem_grows MP M2.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold r2_mem, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end). do 3 (eapply mem_grows_trans; [| apply wbytes_grows]).
    eapply mem_grows_trans; [apply wbytes_grows | apply gh_cp_grows].
  Qed.
  Lemma r2_mem_mrestrict : forall Hd : word -> bool, hid_off Hd (U pc) 80 -> hid_off Hd RIz 128 ->
    r2_mem (mrestrict Hd MP) pc stv faf RIz nf2 n = mrestrict Hd M2.
  Proof using HRI Hpc Hn.
    intros Hd O1 O2. destruct Hpc as [P0 P1]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r2_mem, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end).
    rewrite (wbytes_mrestrict Hd _ MP (Z_to_bv 64 (RIz + 16))) by (rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [lia | eapply hid_off_sub; [exact O2 | lia | lia]]).
    rewrite gh_cp_mrestrict by (rewrite at_u by lia; rewrite Z2Nat.id by lia; first [lia | eapply hid_off_sub; [exact O1 | lia | lia]]).
    rewrite !wbytes_mrestrict; [reflexivity | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
      first [lia | eapply hid_off_sub; [exact O2 | lia | lia] | eapply hid_off_sub; [exact O1 | lia | lia]].
  Qed.
  Lemma r2_mem_rd : 
    rdn segs M2 pc 4 = Some (LE4 n)
    /\ rdn segs M2 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0))
    /\ rdn segs M2 (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 (nf2 - n)))
    /\ (forall i : nat, Z.of_nat i < n -> rdn segs M2 (at_ pc (16 + 4 * Z.of_nat i)) 4 = Some (LE4 (faf (nf2 - n + Z.of_nat i)))).
  Proof using HD HRI Hpc Hn.
    destruct Hpc as [P0 P1]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r2_mem, gh_m5, gh_m4, gh_m2 in G in change_no_check G' end).
    Ltac peel2 := rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, ?u_Z2bv, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite ?u_Z2bv, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                            | rewrite length_N_to_le_bytes, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    split; [|split; [|split]].
    - apply rdn_wbytes_hit4. lia.
    - peel2. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
    - peel2. peel2. peel2.
      rewrite (rdn_ext segs 8 _ (wbytes MP (Z_to_bv 64 (RIz + 16)) (LE8 (Z_to_bv 64 (nf2 - n)))) (Z_to_bv 64 (RIz + 16)));
        [apply rdn_wbytes_hit8; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply gh_cp_outside; rewrite at_u by lia; rewrite Z2Nat.id by lia; lia.
    - intros i Hi. peel2. peel2. peel2.
      replace (at_ pc (16 + 4 * Z.of_nat i)) with (at_ (at_ pc 16) (4 * Z.of_nat i)) by (apply bv_eq; rewrite !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); lia).
      apply gh_cp_entry; [lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; lia].
  Qed.
End R2MEM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition r10_mem (regs : bvmap 5 word) (M : word -> option byte) (spR raR cache g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (RIz : Z) : word -> option byte :=
  gfp_m1 (ic_mem regs M raR spR cache 31) (at_ spR (-32)) g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz.

Lemma ic_mem_mrestrict : forall (Hd : word -> bool) regs M (raR spR cache : word) (k : nat), 32 <= U spR -> U spR < 2 ^ 63 -> U cache + 4096 < 2 ^ 63 -> (Z.of_nat k <= 31) ->
  hid_off Hd (U spR - 32) 32 -> hid_off Hd (U cache) 2560 ->
  ic_mem regs (mrestrict Hd M) raR spR cache k = mrestrict Hd (ic_mem regs M raR spR cache k).
Proof.
  intros Hd regs M raR spR cache k S0 S1 C1. induction k as [|k IH]; intros Hk O1 O2.
  - (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end). rewrite !wbytes_mrestrict; [reflexivity | ..];
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); first [lia | eapply hid_off_sub; [exact O1 | lia | lia]].
  - (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). rewrite IH by (first [lia | assumption]). pose proof (u64_range cache).
    rewrite !wbytes_mrestrict; [reflexivity | ..];
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Pos.to_nat] in G in change_no_check G' end); first [lia | eapply hid_off_sub; [exact O2 | lia | lia]].
Qed.

(* [comment removed for export] *)
Lemma ic_mem_outside_p : forall regs M (raR spR cache : word) (k : nat) (x : word), U cache + 4096 < 2 ^ 63 -> (Z.of_nat k <= 31) ->
  (forall i : Z, 1 <= i <= Z.of_nat k -> (U x < U cache + 80 * i + 4 \/ U cache + 80 * i + 16 <= U x)) ->
  ic_mem regs M raR spR cache k x = rf_m1 regs M raR spR x.
Proof.
  intros regs M raR spR cache k x C1. induction k as [|k IH]; intros Hk Hx; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). pose proof (u64_range cache).
  pose proof (Hx (Z.of_nat (S k)) ltac:(lia)) as Hk1.
  rewrite MemsetLibF.MemSplit.wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  rewrite MemsetLibF.MemSplit.wbytes_outside; [| rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  apply IH; [lia|]. intros i Hi. apply Hx. lia.
Qed.
Lemma ic_mem_mc_p : forall segs regs M (raR spR cache : word) (k : nat) c0, U cache + 4096 < 2 ^ 63 -> 1 <= c0 <= Z.of_nat k -> Z.of_nat k <= 31 ->
  rdn segs (ic_mem regs M raR spR cache k) (at_ cache (80 * c0 + 4)) 4 = Some (LE4 (icmc c0)).
Proof.
  intros segs regs M raR spR cache k c0 C1. revert c0. induction k as [|k IH]; intros c0 Hc Hk; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). pose proof (u64_range cache).
  rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
  destruct (Z.eq_dec c0 (Z.of_nat (S k))) as [->|NE].
  - apply rdn_wbytes_hit4. rewrite at_u by lia. lia.
  - rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
    apply IH; lia.
Qed.
Lemma ic_mem_cs_p : forall segs regs M (raR spR cache : word) (k : nat) c0, U cache + 4096 < 2 ^ 63 -> 1 <= c0 <= Z.of_nat k -> Z.of_nat k <= 31 ->
  rdn segs (ic_mem regs M raR spR cache k) (at_ cache (80 * c0 + 8)) 8 = Some (LE8 (Z_to_bv 64 (iccs c0))).
Proof.
  intros segs regs M raR spR cache k c0 C1. revert c0. induction k as [|k IH]; intros c0 Hc Hk; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [ic_mem] in G in change_no_check G' end). pose proof (u64_range cache).
  destruct (Z.eq_dec c0 (Z.of_nat (S k))) as [->|NE].
  - apply rdn_wbytes_hit8. rewrite at_u by lia. lia.
  - rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
    rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ].
    apply IH; lia.
Qed.

Section R10MEM.
  Variables (segs : list Segment) (regs : bvmap 5 word) (M : word -> option byte) (spR raR cache g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) (RIz : Z).
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U spR /\ U spR + 16 <= 2 ^ 47.
  Hypothesis HRI : 0 <= RIz /\ RIz + 8 <= U spR - 160.
  Hypothesis Hcache : 0 <= U cache /\ U cache + 2640 <= U spR - 160.
  Hypothesis HD : U cache + 2640 <= RIz \/ RIz + 8 <= U cache.
  #[local] Abbreviation M1 := (r10_mem regs M spR raR cache g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz).
  #[local] Abbreviation MI := (ic_mem regs M raR spR cache 31).
  #[local] Abbreviation spG := (at_ spR (-32)).

  Lemma r10_frame_outside : forall x : word, (U x < U spR - 160 \/ U spR - 32 <= U x) ->
    gfp_frame MI spG g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 x = MI x.
  Proof using Hsp.
    intros x Hx. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold gfp_frame in G in change_no_check G' end).
    repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                               | rewrite length_N_to_le_bytes, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma r10_mem_above : forall x : word, (U x < U spR - 160 \/ U spR - 32 <= U x) -> (U x < RIz \/ RIz + 8 <= U x) -> M1 x = MI x.
  Proof using HRI Hsp.
    intros x X1 X2. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. (lazymatch goal with |- ?G => let G' := eval unfold r10_mem, gfp_m1 in G in change_no_check G' end).
    rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    apply r10_frame_outside. exact X1.
  Qed.
  Lemma r10_mem_grows : mem_grows M M1.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold r10_mem, gfp_m1, gfp_frame in G in change_no_check G' end). do 14 (eapply mem_grows_trans; [|apply wbytes_grows]). apply ic_mem_grows.
  Qed.
  Lemma r10_mem_mrestrict : forall Hd : word -> bool, hid_off Hd (U spR - 160) 160 -> hid_off Hd RIz 8 -> hid_off Hd (U cache) 2560 ->
    r10_mem regs (mrestrict Hd M) spR raR cache g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 RIz = mrestrict Hd M1.
  Proof using Hcache HRI Hsp.
    intros Hd O1 O2 O3. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. destruct Hcache as [C0 C1]. (lazymatch goal with |- ?G => let G' := eval unfold r10_mem in G in change_no_check G' end).
    rewrite ic_mem_mrestrict by (first [lia | eapply hid_off_sub; [exact O1 | lia | lia] | exact O3]).
    (lazymatch goal with |- ?G => let G' := eval unfold gfp_m1, gfp_frame in G in change_no_check G' end).
    rewrite !wbytes_mrestrict; [reflexivity | ..];
      wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv, ?at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
      first [lia | intros x Hx; apply O1; lia | intros x Hx; apply O2; lia].
  Qed.
  Lemma r10_mem_lock : rdn segs M1 (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Proof using HRI Hsp. destruct HRI as [R0 R1]. destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold r10_mem, gfp_m1 in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.
  Lemma r10_mem_gslots : forall (k : Z) (v : word),
    In (k, v) [(-8, g_ra); (-16, g0); (-24, g1); (-32, g2); (-40, g3); (-48, g4); (-56, g5); (-64, g6); (-72, g7); (-80, g8); (-88, g9); (-96, g10); (-104, g11)] ->
    rdn segs M1 (at_ spG k) 8 = Some (LE8 v).
  Proof using Hcache HRI Hsp.
    intros k v Hin. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1].
    assert (K : -104 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    (lazymatch goal with |- ?G => let G' := eval unfold r10_mem, gfp_m1 in G in change_no_check G' end).
    rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, u_Z2bv, !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                              | rewrite !at_u by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    (lazymatch goal with |- ?G => let G' := eval unfold gfp_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.
  Lemma r10_mem_outside : forall x : word, (U x < U spR - 160 \/ U spR <= U x) -> (U x < RIz \/ RIz + 8 <= U x) ->
    (forall i : Z, 1 <= i <= 31 -> (U x < U cache + 80 * i + 4 \/ U cache + 80 * i + 16 <= U x)) -> M1 x = M x.
  Proof using Hcache HRI Hsp.
    intros x X1 X2 X3. destruct Hsp as [S1 S2]. destruct Hcache as [C0 C1]. rewrite r10_mem_above by (first [lia | exact X2]).
    rewrite ic_mem_outside_p by (first [lia | exact X3]). (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end).
    repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma r10_mem_rslots : forall (k : Z) (v : word), In (k, v) [(-8, raR); (-16, getr regs 8); (-24, getr regs 9)] -> rdn segs M1 (at_ spR k) 8 = Some (LE8 v).
  Proof using Hcache HRI Hsp.
    intros k v Hin. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. destruct Hcache as [C0 C1].
    assert (K : -24 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    rewrite (rdn_ext segs 8 M1 (rf_m1 regs M raR spR) (at_ spR k)); [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | ].
    - (lazymatch goal with |- ?G => let G' := eval unfold rf_m1 in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
    - intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. rewrite r10_mem_above by lia. apply ic_mem_outside_p; [lia | lia |]. intros i Hi. lia.
  Qed.
  Lemma r10_mem_cells : forall i, 1 <= i <= 31 ->
    rdn segs M1 (at_ cache (80 * i + 4)) 4 = Some (LE4 (icmc i)) /\ rdn segs M1 (at_ cache (80 * i + 8)) 8 = Some (LE8 (Z_to_bv 64 (iccs i))).
  Proof using HD Hcache HRI Hsp.
    intros i Hi. destruct Hsp as [S1 S2]. destruct HRI as [R0 R1]. destruct Hcache as [C0 C1]. split.
    - rewrite (rdn_ext segs 4 M1 MI (at_ cache (80 * i + 4))); [apply ic_mem_mc_p; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply r10_mem_above; lia.
    - rewrite (rdn_ext segs 8 M1 MI (at_ cache (80 * i + 8))); [apply ic_mem_cs_p; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply r10_mem_above; lia.
  Qed.
End R10MEM.

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
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAinvDefs3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma magic_cas_4df2c : forall regs mem rom (ab : word) magicv,
  getr regs 18 = ab -> getr regs 14 = magicv -> (bv_unsigned ab mod 8 = 0)%Z ->
  rdn ASEGS mem ab 8 = Some (LE8 magicv) -> store_ok ASEGS mem ab 8 = true ->
  msteps ASEGS (mkst regs (0x4df34 : word) mem rom)
    (mkst (regupd (regupd regs 13 magicv) 10 (Z_to_bv 64 0)) (0x4df44 : word) (wbytes mem ab (LE8 (Z_to_bv 64 0))) rom).
Proof using.
  intros regs mem rom ab magicv H18 H14 Hal Hrd Hok.
  pose proof (cas_d_run ASEGS regs (0x4df34 : word) (0x4df38 : word) (0x4df3c : word) (0x4df40 : word) (0x4df44 : word) mem rom
                _ _ _ _ _ _ _ _ 13 18 10 0 13 14 _ _ _ (LE8 magicv) magicv
                F_4df2c eq_refl D_4df2c F_4df30 eq_refl D_4df30 F_4df34 eq_refl D_4df34 F_4df38 eq_refl D_4df38) as R.
  rewrite H18 in R.
  apply R; clear R; first [regneq | pc4 | exact Hal | exact Hrd | apply bytes_le_to_Z_8 | exact Hok | idtac].
  (* [comment removed for export] *)
  (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end). gres. rewrite H14. rewrite bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fr_k1 (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (m ab : Z) : word -> option byte :=
  let f := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2408)) (LE8 ra0))
    (at_ S (-2416)) (LE8 s0v))
    (at_ S (-2424)) (LE8 s1v))
    (at_ S (-2432)) (LE8 s2v))
    (at_ S (-2440)) (LE8 s3v))
    (at_ S (-2448)) (LE8 s4v) in
  if (ab =? m)%Z then f else wbytes f (Z_to_bv 64 ab) (LE8 (Z_to_bv 64 0)).

Section K1.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v cbv : word).
  Variables (m spb c d rib au : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation cs := (csize c).
  #[local] Abbreviation idx := (d / cs)%Z.
  #[local] Abbreviation ab := (spb + c * 2 ^ 32 + idx * cs)%Z.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2400).
  Hypothesis H10 : getr regs 10 = cbv.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 m.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hm : (m = spb + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30)%Z.
  Hypothesis Hrib : (AIMGHI <= rib /\ rib + 4096 <= bv_unsigned S - 3584)%Z.          (* [comment removed for export] *)
  Hypothesis Hau : ((idx + 1) * cs <= au /\ au < 2 ^ 64)%Z.                    (* [comment removed for export] *)
  Hypothesis Hab8 : (ab mod 8 = 0)%Z.
  Hypothesis Habs : (ab <> m -> AIMGHI <= ab /\ ab + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2448)) 48 = true.
  Hypothesis Hokab : (ab <> m)%Z -> store_ok ASEGS mem (Z_to_bv 64 ab) 8 = true.
  Hypothesis Rspb : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis Rrib : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 48)) 8 = Some (LE8 (Z_to_bv 64 rib)).
  Hypothesis Rau : rdn ASEGS mem (Z_to_bv 64 (rib + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis Rmagc : rdn ASEGS mem (Z_to_bv 64 0x103b8) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis Rmagic : (ab <> m)%Z -> rdn ASEGS mem (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).

  Definition k1_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2448) /\ getr r 8 = cbv /\ getr r 9 = Z_to_bv 64 m /\ getr r 18 = Z_to_bv 64 ab
      /\ getr r 19 = Z_to_bv 64 0x103f18 /\ getr r 20 = Z_to_bv 64 (2 ^ 37)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Ltac k1a :=
      an F_4de2c D_4de2c;                              (* [comment removed for export] *)
      fsd F_4de30 D_4de30 (at_ S (-2408));             (* [comment removed for export] *)
      fsd F_4de34 D_4de34 (at_ S (-2416));             (* [comment removed for export] *)
      fsd F_4de38 D_4de38 (at_ S (-2424));             (* [comment removed for export] *)
      fsd F_4de3c D_4de3c (at_ S (-2432));             (* [comment removed for export] *)
      fsd F_4de40 D_4de40 (at_ S (-2440));             (* [comment removed for export] *)
      fsd F_4de44 D_4de44 (at_ S (-2448));             (* [comment removed for export] *)
      an F_4de48 D_4de48;                              (* [comment removed for export] *)
      an F_4de4c D_4de4c;                              (* [comment removed for export] *)
      an F_4de50 D_4de50;                              (* [comment removed for export] *)
      an F_4de54 D_4de54;                              (* [comment removed for export] *)
      cld8 F_4de58 D_4de58 (Z_to_bv 64 spb) Rspb;      (* [comment removed for export] *)
      an F_4de5c D_4de5c;                              (* [comment removed for export] *)
      av F_4de60 D_4de60 (Z_to_bv 64 (2 ^ 37)) ltac:(valz);      (* [comment removed for export] *)
      ab_ft F_4de64 D_4de64 ltac:(condz);              (* [comment removed for export] *)
      av F_4de68 D_4de68 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz);   (* [comment removed for export] *)
      ab_ft F_4de6c D_4de6c ltac:(condz);              (* [comment removed for export] *)
      av F_4de70 D_4de70 (Z_to_bv 64 (c * 2 ^ 32 + d)) ltac:(valz);   (* [comment removed for export] *)
      av F_4de74 D_4de74 (Z_to_bv 64 c) ltac:(apply (cls_of_off2 c d); lia);   (* [comment removed for export] *)
      av F_4de78 D_4de78 (Z_to_bv 64 c) ltac:(apply andi31; lia);     (* [comment removed for export] *)
      an F_4de7c D_4de7c;                              (* [comment removed for export] *)
      ab_ft F_4de80 D_4de80 ltac:(condz);              (* [comment removed for export] *)
      an F_4de84 D_4de84.                              (* [comment removed for export] *)
  Ltac k1small :=
      ab_ft F_4de88 D_4de88 ltac:(condz);              (* [comment removed for export] *)
      ab_ft F_4de8c D_4de8c ltac:(condz);              (* [comment removed for export] *)
      av F_4de90 D_4de90 (Z_to_bv 64 cs) ltac:(apply csize_small; lia);   (* [comment removed for export] *)
      an F_4de94 D_4de94.                              (* [comment removed for export] *)
  Ltac k1big :=
      ab_tk F_4de88 D_4de88 ltac:(condz);              (* [comment removed for export] *)
      an F_4deb8 D_4deb8;                              (* [comment removed for export] *)
      an F_4debc D_4debc;                              (* [comment removed for export] *)
      an F_4dec0 D_4dec0;                              (* [comment removed for export] *)
      an F_4dec4 D_4dec4;                              (* [comment removed for export] *)
      an F_4dec8 D_4dec8;                              (* [comment removed for export] *)
      an F_4decc D_4decc;                              (* [comment removed for export] *)
      an F_4ded0 D_4ded0;                              (* [comment removed for export] *)
      an F_4ded4 D_4ded4;                              (* [comment removed for export] *)
      av F_4ded8 D_4ded8 (Z_to_bv 64 cs) ltac:(apply (csize_big c); lia).   (* [comment removed for export] *)
  Ltac k1b CSP :=
      an F_4dedc D_4dedc;                              (* [comment removed for export] *)
      av F_4dee0 D_4dee0 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia);   (* [comment removed for export] *)
      cld8 F_4dee4 D_4dee4 (Z_to_bv 64 rib) Rrib;      (* [comment removed for export] *)
      av F_4dee8 D_4dee8 (Z_to_bv 64 (128 * c)) ltac:(apply cls_shl7; lia);       (* [comment removed for export] *)
      an F_4deec D_4deec;                              (* [comment removed for export] *)
      av F_4def0 D_4def0 (Z_to_bv 64 (spb + c * 2 ^ 32)) ltac:(valz);   (* [comment removed for export] *)
      av F_4def4 D_4def4 (Z_to_bv 64 (rib + 128 * c)) ltac:(valz);      (* [comment removed for export] *)
      cld8 F_4def8 D_4def8 (Z_to_bv 64 au) Rau;        (* [comment removed for export] *)
      av F_4defc D_4defc (Z_to_bv 64 idx) ltac:(apply (idx_divuw c d cs); lia);   (* [comment removed for export] *)
      av F_4df00 D_4df00 (Z_to_bv 64 (idx * cs)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia);   (* [comment removed for export] *)
      av F_4df04 D_4df04 (Z_to_bv 64 ((idx + 1) * cs)) ltac:(valz);     (* [comment removed for export] *)
      an F_4df08 D_4df08;                              (* [comment removed for export] *)
      av F_4df0c D_4df0c (Z_to_bv 64 ab) ltac:(valz);  (* [comment removed for export] *)
      av F_4df10 D_4df10 (Z_to_bv 64 18446744073709551615) ltac:(apply au_mask; lia);   (* [comment removed for export] *)
      an F_4df14 D_4df14; rewrite v_and_m1_l;          (* [comment removed for export] *)
      ab_ft F_4df18 D_4df18 ltac:(condz);              (* [comment removed for export] *)
      ab_ft F_4df1c D_4df1c ltac:(condz).              (* [comment removed for export] *)

  Lemma k1_run :
    exists r, msteps ASEGS (mkst regs (0x4de34 : word) mem rom) (mkst r (0x4df44 : word) (fr_k1 mem S ra0 s0v s1v s2v s3v s4v m ab) rom)
      /\ k1_regs r.
  Proof using Rmagic Rmagc Rau Rrib Rspb Hokab Hstk Habs Hab8 Hau Hrib Hm Hspb HS H20 H19 H18 H9 H8 H11 H10 H2 H1 au rib.
    (lazymatch goal with |- ?G => let G' := eval unfold k1_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. destruct Hm as (Em & Hd & Hc).
    pose proof (csize_pos c Hc) as (CSP & _).
    assert (IDX : (0 <= idx /\ idx * cs <= d /\ d < (idx + 1) * cs)%Z).
    { pose proof (Z.div_mod d cs ltac:(lia)) as DM. pose proof (Z.mod_pos_bound d cs ltac:(lia)) as MB.
      split; [apply Z.div_pos; lia|]. split; nia. }
    (lazymatch goal with |- ?G => let G' := eval unfold fr_k1 in G in change_no_check G' end). destruct (Z.eqb_spec ab m) as [Eab | Nab]; (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    - (* [comment removed for export] *)
      destruct (Z_le_gt_dec c 16) as [Csm | Cbg].
      + wd_eexists. split.
        * k1a. k1small. k1b CSP.
          ab_tk F_4df20 D_4df20 ltac:(condz).          (* [comment removed for export] *)
          wd_refl.
        * post.
      + wd_eexists. split.
        * k1a. k1big. k1b CSP.
          ab_tk F_4df20 D_4df20 ltac:(condz).
          wd_refl.
        * post.
    - (* [comment removed for export] *)
      destruct (Habs Nab) as (Hab1 & Hab2). pose proof (Hokab Nab) as Hokab'. pose proof (Rmagic Nab) as Rmagic'.
      destruct (Z_le_gt_dec c 16) as [Csm | Cbg].
      + wd_eexists. split.
        * k1a. k1small. k1b CSP.
          ab_ft F_4df20 D_4df20 ltac:(condz).          (* [comment removed for export] *)
          an F_4df24 D_4df24.                          (* [comment removed for export] *)
          cld8 F_4df28 D_4df28 (Z_to_bv 64 0xcc6e96b9cc6e96b9) Rmagc.   (* [comment removed for export] *)
          eapply msteps_trans;
          [ eapply (magic_cas_4df2c _ _ rom (Z_to_bv 64 ab) (Z_to_bv 64 0xcc6e96b9cc6e96b9));
              [ gres; rwH; reflexivity | gres; rwH; reflexivity | unorm; exact Hab8 | rd_addr Rmagic' | any_ok ]
          | ].
          wd_refl.
        * post.
      + wd_eexists. split.
        * k1a. k1big. k1b CSP.
          ab_ft F_4df20 D_4df20 ltac:(condz).
          an F_4df24 D_4df24.
          cld8 F_4df28 D_4df28 (Z_to_bv 64 0xcc6e96b9cc6e96b9) Rmagc.
          eapply msteps_trans;
          [ eapply (magic_cas_4df2c _ _ rom (Z_to_bv 64 ab) (Z_to_bv 64 0xcc6e96b9cc6e96b9));
              [ gres; rwH; reflexivity | gres; rwH; reflexivity | unorm; exact Hab8 | rd_addr Rmagic' | any_ok ]
          | ].
          wd_refl.
        * post.
  Qed.
End K1.
End FPGen.

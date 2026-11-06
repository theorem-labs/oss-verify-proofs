(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module BoAllocFRc3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma magic_cas_4e9a4 : forall regs mem rom (ab : word) magicv,
  getr regs 18 = ab -> getr regs 14 = magicv -> (bv_unsigned ab mod 8 = 0)%Z ->
  rdn BSEGS mem ab 8 = Some (LE8 magicv) -> store_ok BSEGS mem ab 8 = true ->
  msteps BSEGS (mkst regs (0x4e9a4 : word) mem rom)
    (mkst (regupd (regupd regs 13 magicv) 10 (Z_to_bv 64 0)) (0x4e9b4 : word) (wbytes mem ab (LE8 (Z_to_bv 64 0))) rom).
Proof using.
  intros regs mem rom ab magicv H18 H14 Hal Hrd Hok.
  pose proof (cas_d_run BSEGS regs (0x4e9a4 : word) (0x4e9a8 : word) (0x4e9ac : word) (0x4e9b0 : word) (0x4e9b4 : word) mem rom
                _ _ _ _ _ _ _ _ 13 18 10 0 13 14 _ _ _ (LE8 magicv) magicv
                F_4e9a4 eq_refl D_4e9a4 F_4e9a8 eq_refl D_4e9a8 F_4e9ac eq_refl D_4e9ac F_4e9b0 eq_refl D_4e9b0) as R.
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
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2448)) 48 = true.
  Hypothesis Hokab : (ab <> m)%Z -> store_ok BSEGS mem (Z_to_bv 64 ab) 8 = true.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis Rrib : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 rib)).
  Hypothesis Rau : rdn BSEGS mem (Z_to_bv 64 (rib + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis Rmagc : rdn BSEGS mem (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis Rmagic : (ab <> m)%Z -> rdn BSEGS mem (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).

  Definition k1_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2448) /\ getr r 8 = cbv /\ getr r 9 = Z_to_bv 64 m /\ getr r 18 = Z_to_bv 64 ab
      /\ getr r 19 = Z_to_bv 64 0x10ab58 /\ getr r 20 = Z_to_bv 64 (2 ^ 37)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Ltac k1a :=
      an F_4e8a4 D_4e8a4;                              (* [comment removed for export] *)
      fsd F_4e8a8 D_4e8a8 (at_ S (-2408));             (* [comment removed for export] *)
      fsd F_4e8ac D_4e8ac (at_ S (-2416));             (* [comment removed for export] *)
      fsd F_4e8b0 D_4e8b0 (at_ S (-2424));             (* [comment removed for export] *)
      fsd F_4e8b4 D_4e8b4 (at_ S (-2432));             (* [comment removed for export] *)
      fsd F_4e8b8 D_4e8b8 (at_ S (-2440));             (* [comment removed for export] *)
      fsd F_4e8bc D_4e8bc (at_ S (-2448));             (* [comment removed for export] *)
      an F_4e8c0 D_4e8c0;                              (* [comment removed for export] *)
      an F_4e8c4 D_4e8c4;                              (* [comment removed for export] *)
      an F_4e8c8 D_4e8c8;                              (* [comment removed for export] *)
      an F_4e8cc D_4e8cc;                              (* [comment removed for export] *)
      cld8 F_4e8d0 D_4e8d0 (Z_to_bv 64 spb) Rspb;      (* [comment removed for export] *)
      an F_4e8d4 D_4e8d4;                              (* [comment removed for export] *)
      av F_4e8d8 D_4e8d8 (Z_to_bv 64 (2 ^ 37)) ltac:(valz);      (* [comment removed for export] *)
      ab_ft F_4e8dc D_4e8dc ltac:(condz);              (* [comment removed for export] *)
      av F_4e8e0 D_4e8e0 (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz);   (* [comment removed for export] *)
      ab_ft F_4e8e4 D_4e8e4 ltac:(condz);              (* [comment removed for export] *)
      av F_4e8e8 D_4e8e8 (Z_to_bv 64 (c * 2 ^ 32 + d)) ltac:(valz);   (* [comment removed for export] *)
      av F_4e8ec D_4e8ec (Z_to_bv 64 c) ltac:(apply (cls_of_off2 c d); lia);   (* [comment removed for export] *)
      av F_4e8f0 D_4e8f0 (Z_to_bv 64 c) ltac:(apply andi31; lia);     (* [comment removed for export] *)
      an F_4e8f4 D_4e8f4;                              (* [comment removed for export] *)
      ab_ft F_4e8f8 D_4e8f8 ltac:(condz);              (* [comment removed for export] *)
      an F_4e8fc D_4e8fc.                              (* [comment removed for export] *)
  Ltac k1small :=
      ab_ft F_4e900 D_4e900 ltac:(condz);              (* [comment removed for export] *)
      ab_ft F_4e904 D_4e904 ltac:(condz);              (* [comment removed for export] *)
      av F_4e908 D_4e908 (Z_to_bv 64 cs) ltac:(apply csize_small; lia);   (* [comment removed for export] *)
      an F_4e90c D_4e90c.                              (* [comment removed for export] *)
  Ltac k1big :=
      ab_tk F_4e900 D_4e900 ltac:(condz);              (* [comment removed for export] *)
      an F_4e930 D_4e930;                              (* [comment removed for export] *)
      an F_4e934 D_4e934;                              (* [comment removed for export] *)
      an F_4e938 D_4e938;                              (* [comment removed for export] *)
      an F_4e93c D_4e93c;                              (* [comment removed for export] *)
      an F_4e940 D_4e940;                              (* [comment removed for export] *)
      an F_4e944 D_4e944;                              (* [comment removed for export] *)
      an F_4e948 D_4e948;                              (* [comment removed for export] *)
      an F_4e94c D_4e94c;                              (* [comment removed for export] *)
      av F_4e950 D_4e950 (Z_to_bv 64 cs) ltac:(apply (csize_big c); lia).   (* [comment removed for export] *)
  Ltac k1b CSP :=
      an F_4e954 D_4e954;                              (* [comment removed for export] *)
      av F_4e958 D_4e958 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia);   (* [comment removed for export] *)
      cld8 F_4e95c D_4e95c (Z_to_bv 64 rib) Rrib;      (* [comment removed for export] *)
      av F_4e960 D_4e960 (Z_to_bv 64 (128 * c)) ltac:(apply cls_shl7; lia);       (* [comment removed for export] *)
      an F_4e964 D_4e964;                              (* [comment removed for export] *)
      av F_4e968 D_4e968 (Z_to_bv 64 (spb + c * 2 ^ 32)) ltac:(valz);   (* [comment removed for export] *)
      av F_4e96c D_4e96c (Z_to_bv 64 (rib + 128 * c)) ltac:(valz);      (* [comment removed for export] *)
      cld8 F_4e970 D_4e970 (Z_to_bv 64 au) Rau;        (* [comment removed for export] *)
      av F_4e974 D_4e974 (Z_to_bv 64 idx) ltac:(apply (idx_divuw c d cs); lia);   (* [comment removed for export] *)
      av F_4e978 D_4e978 (Z_to_bv 64 (idx * cs)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia);   (* [comment removed for export] *)
      av F_4e97c D_4e97c (Z_to_bv 64 ((idx + 1) * cs)) ltac:(valz);     (* [comment removed for export] *)
      an F_4e980 D_4e980;                              (* [comment removed for export] *)
      av F_4e984 D_4e984 (Z_to_bv 64 ab) ltac:(valz);  (* [comment removed for export] *)
      av F_4e988 D_4e988 (Z_to_bv 64 18446744073709551615) ltac:(apply au_mask; lia);   (* [comment removed for export] *)
      an F_4e98c D_4e98c; rewrite v_and_m1_l;          (* [comment removed for export] *)
      ab_ft F_4e990 D_4e990 ltac:(condz);              (* [comment removed for export] *)
      ab_ft F_4e994 D_4e994 ltac:(condz).              (* [comment removed for export] *)

  Lemma k1_run :
    exists r, msteps BSEGS (mkst regs (0x4e8a4 : word) mem rom) (mkst r (0x4e9b4 : word) (fr_k1 mem S ra0 s0v s1v s2v s3v s4v m ab) rom)
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
          ab_tk F_4e998 D_4e998 ltac:(condz).          (* [comment removed for export] *)
          wd_refl.
        * post.
      + wd_eexists. split.
        * k1a. k1big. k1b CSP.
          ab_tk F_4e998 D_4e998 ltac:(condz).
          wd_refl.
        * post.
    - (* [comment removed for export] *)
      destruct (Habs Nab) as (Hab1 & Hab2). pose proof (Hokab Nab) as Hokab'. pose proof (Rmagic Nab) as Rmagic'.
      destruct (Z_le_gt_dec c 16) as [Csm | Cbg].
      + wd_eexists. split.
        * k1a. k1small. k1b CSP.
          ab_ft F_4e998 D_4e998 ltac:(condz).          (* [comment removed for export] *)
          an F_4e99c D_4e99c.                          (* [comment removed for export] *)
          cld8 F_4e9a0 D_4e9a0 (Z_to_bv 64 0xcc6e96b9cc6e96b9) Rmagc.   (* [comment removed for export] *)
          eapply msteps_trans;
          [ eapply (magic_cas_4e9a4 _ _ rom (Z_to_bv 64 ab) (Z_to_bv 64 0xcc6e96b9cc6e96b9));
              [ gres; rwH; reflexivity | gres; rwH; reflexivity | unorm; exact Hab8 | rd_addr Rmagic' | any_ok ]
          | ].
          wd_refl.
        * post.
      + wd_eexists. split.
        * k1a. k1big. k1b CSP.
          ab_ft F_4e998 D_4e998 ltac:(condz).
          an F_4e99c D_4e99c.
          cld8 F_4e9a0 D_4e9a0 (Z_to_bv 64 0xcc6e96b9cc6e96b9) Rmagc.
          eapply msteps_trans;
          [ eapply (magic_cas_4e9a4 _ _ rom (Z_to_bv 64 ab) (Z_to_bv 64 0xcc6e96b9cc6e96b9));
              [ gres; rwH; reflexivity | gres; rwH; reflexivity | unorm; exact Hab8 | rd_addr Rmagic' | any_ok ]
          | ].
          wd_refl.
        * post.
  Qed.
End K1.
End FPGen.
End BoAllocFRc3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc3R.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRc3c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_item (memD : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 : word) (m ab n n8 T c cnt e : Z) (h1 h2 h3 : byte)
           (j0 j1 stw : word) : word -> option byte :=
  let M1 := fr_k1 memD S ra0 s0v s1v s2v s3v s4v m ab in
  let M2 := wbytes M1 (Z_to_bv 64 m) [Z_to_bv 8 0; h1; h2; h3] in
  let M3 := wbytes (ps_frame M2 (at_ S (-2448)) (Z_to_bv 64 0x4ea10) (at_ S (-2392)) (Z_to_bv 64 m) (Z_to_bv 64 ab)
                             (Z_to_bv 64 0x10ab58) (Z_to_bv 64 (2 ^ 37)) x21)
                   (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (repeat (MemsetLibF.cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 n8)))) in
  let M4 := fr_k3 M3 S in
  let M5 := wbytes M4 (at_ S (-2472)) (LE8 (Z_to_bv 64 0x78004)) in
  let M6 := fr_k4 M5 T j0 j1 in
  fr_k5 M6 S ra0 s0v s1v s2v s3v s4v T c cnt e stw.

Definition fr_k12 (memD : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (m ab : Z) (h1 h2 h3 : byte) : word -> option byte :=
  wbytes (fr_k1 memD S ra0 s0v s1v s2v s3v s4v m ab) (Z_to_bv 64 m) [Z_to_bv 8 0; h1; h2; h3].

Section RUNK12.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v : word) (m spb c d rib au n : Z).
  Variables (h1 h2 h3 : byte) (hv : word).
  #[local] Abbreviation cs := (csize c).
  #[local] Abbreviation idx := (d / cs)%Z.
  #[local] Abbreviation ab := (spb + c * 2 ^ 32 + idx * cs)%Z.
  Hypothesis D1 : getr rD 1 = ra0.
  Hypothesis D2 : getr rD 2 = at_ S (-2400).
  Hypothesis D10 : getr rD 10 = at_ S (-2392).
  Hypothesis D11 : getr rD 11 = Z_to_bv 64 m.
  Hypothesis D8 : getr rD 8 = s0v.   Hypothesis D9 : getr rD 9 = s1v.   Hypothesis D18 : getr rD 18 = s2v.
  Hypothesis D19 : getr rD 19 = s3v. Hypothesis D20 : getr rD 20 = s4v.
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gspb : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Gm : (m = spb + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30)%Z.
  Hypothesis Gm2 : (m + 16 <= U S - 3584 /\ m mod 16 = 0)%Z.
  Hypothesis Gab : (ab = m \/ ab + 16 <= m)%Z.
  Hypothesis Gab8 : (ab mod 8 = 0)%Z.
  Hypothesis Grib : (AIMGHI <= rib /\ rib + 4096 <= U S - 3584)%Z.
  Hypothesis Gau : ((idx + 1) * cs <= au /\ au < 2 ^ 64)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2448)) 48 = true.
  Hypothesis Okhdr : store_ok BSEGS memD (Z_to_bv 64 m) 4 = true.
  Hypothesis Okab : (ab <> m)%Z -> store_ok BSEGS memD (Z_to_bv 64 ab) 8 = true.
  Hypothesis C_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_rib : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 rib)).
  Hypothesis C_au : rdn BSEGS memD (Z_to_bv 64 (rib + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis C_magc : rdn BSEGS memD (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis C_magic : (ab <> m)%Z -> rdn BSEGS memD (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis C_hdr : rdn BSEGS memD (Z_to_bv 64 m) 4 = Some [Z_to_bv 8 3; h1; h2; h3].
  Hypothesis Hhv : bytes_le_to_Z [Z_to_bv 8 3; h1; h2; h3] = bv_unsigned hv.
  Hypothesis Hh23 : [h2; h3] = word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)).
  Hypothesis C_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32)).

  #[local] Abbreviation M12 := (fr_k12 memD S ra0 s0v s1v s2v s3v s4v m ab h1 h2 h3).

  Lemma ab_le : (spb <= ab /\ ab <= m /\ 0 <= idx /\ idx * cs <= d /\ d < (idx + 1) * cs /\ 32 <= cs <= 65536)%Z.
  Proof using Gn Gab Gm Gspb n.
    destruct Gm as (Em & Hd & Hc). pose proof (csize_pos c Hc) as (CSP & _).
    pose proof (Z.div_mod d cs ltac:(lia)) as DM. pose proof (Z.mod_pos_bound d cs ltac:(lia)) as MB.
    assert (I0 : (0 <= idx)%Z) by (apply Z.div_pos; lia).
    repeat split; try lia; nia.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_k12_quiet : forall x : word,
    ((U x < U S - 2448)%Z \/ (U S - 2400 <= U x)%Z) -> (U x < m \/ m + 4 <= U x)%Z -> (ab = m \/ U x < ab \/ ab + 8 <= U x)%Z -> M12 x = memD x.
  Proof using Gn Gab Gm2 Gm Gspb GS n.
    intros x H1 H2 H3. pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct Gm2 as (Gm3 & _). destruct Gspb as (Gs1 & Gs2).
    destruct ab_le as (AB1 & AB2 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_k12, fr_k1 in G in change_no_check G' end). destruct (Z.eqb_spec ab m) as [E|N].
    - rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; unorm; try lia. reflexivity.
    - assert (H3' : (U x < ab \/ ab + 8 <= U x)%Z) by (destruct H3 as [H3|H3]; [contradiction | exact H3]).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; unorm; try lia. reflexivity.
  Qed.
  Lemma fr_k12_grows : mem_grows memD M12.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_k12, fr_k1 in G in change_no_check G' end). destruct (Z.eqb_spec ab m); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl. Qed.

  (* [comment removed for export] *)
  Ltac digK := repeat (wd_rdstep rd8_side).
  Ltac frK := pose proof (u64_range S) as HSr; destruct GS as (GS1 & GS2); destruct Gm2 as (Gm3 & _); destruct Gspb as (Gs1 & Gs2);
              destruct ab_le as (AB1 & AB2 & _); (lazymatch goal with |- ?G => let G' := eval unfold fr_k12, fr_k1 in G in change_no_check G' end); destruct (Z.eqb_spec ab m) as [E|N]; digK.
  Lemma fr_k12_ra : rdn BSEGS M12 (at_ S (-2408)) 8 = Some (LE8 ra0).  Proof using Gn Gab Gm2 Gm Gspb GS n. frK. Qed.
  Lemma fr_k12_s0 : rdn BSEGS M12 (at_ S (-2416)) 8 = Some (LE8 s0v).  Proof using Gn Gab Gm2 Gm Gspb GS n. frK. Qed.
  Lemma fr_k12_s1 : rdn BSEGS M12 (at_ S (-2424)) 8 = Some (LE8 s1v).  Proof using Gn Gab Gm2 Gm Gspb GS n. frK. Qed.
  Lemma fr_k12_s2 : rdn BSEGS M12 (at_ S (-2432)) 8 = Some (LE8 s2v).  Proof using Gn Gab Gm2 Gm Gspb GS n. frK. Qed.
  Lemma fr_k12_s3 : rdn BSEGS M12 (at_ S (-2440)) 8 = Some (LE8 s3v).  Proof using Gn Gab Gm2 Gm Gspb GS n. frK. Qed.
  Lemma fr_k12_s4 : rdn BSEGS M12 (at_ S (-2448)) 8 = Some (LE8 s4v).  Proof using Gn Gab Gm2 Gm Gspb GS n. frK. Qed.
  Lemma fr_k12_nhi : rdn BSEGS M12 (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Proof using Hh23 Gn Gab Gm2 Gm Gspb GS.
    destruct Gspb as (Gs1 & Gs2). destruct ab_le as (AB1 & AB2 & _). destruct Gm2 as (Gm3 & _). destruct GS as (GS1 & GS2). pose proof (u64_range S) as HSr.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_k12 in G in change_no_check G' end). rewrite <- Hh23. replace (Z_to_bv 64 (m + 2)) with (at_ (Z_to_bv 64 m) (Z.of_nat 2)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
    apply (rdn_wbytes_sub BSEGS _ (Z_to_bv 64 m) [Z_to_bv 8 0; h1; h2; h3] 2 2); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | wd_ulia_c].
  Qed.


  Definition k12_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = Z_to_bv 64 0x4ea10 /\ getr r 2 = at_ S (-2448)
      /\ getr r 10 = Z_to_bv 64 (m + 16) /\ getr r 11 = Z_to_bv 64 (AsRtRegion.down8 (n + 7)) /\ getr r 12 = Z_to_bv 64 250
      /\ getr r 8 = at_ S (-2392) /\ getr r 9 = Z_to_bv 64 m /\ getr r 18 = Z_to_bv 64 ab
      /\ getr r 19 = Z_to_bv 64 0x10ab58 /\ getr r 20 = Z_to_bv 64 (2 ^ 37)
      /\ getr r 3 = getr rD 3 /\ getr r 4 = getr rD 4
      /\ getr r 21 = getr rD 21 /\ getr r 22 = getr rD 22 /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24
      /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.

  Theorem run_k12 :
    exists r, msteps BSEGS (mkst rD (0x4e8a4 : word) memD rom) (mkst r (0x70080 : word) M12 rom) /\ k12_regs r.
  Proof using C_nlo Hh23 Hhv C_hdr C_magic C_magc C_au C_rib C_spb Okab Okhdr Hstk Gn Gau Grib Gab8 Gab Gm2 Gm Gspb GS D20 D19 D18 D9 D8 D11 D10 D2 D1 hv au rib.
    (lazymatch goal with |- ?G => let G' := eval unfold k12_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    destruct GS as (GS1 & GS2). destruct Gm as (Em & Hd & Hc). destruct Gm2 as (Gm3 & Gm16). destruct Gspb as (Gs1 & Gs2).
    destruct ab_le as (AB1 & AB2 & IDX0 & IDX1 & IDX2 & CSP).
    (* [comment removed for export] *)
    destruct (k1_run memD rom S ra0 s0v s1v s2v s3v s4v (at_ S (-2392)) m spb c d rib au rD
                D1 D2 D10 D11 D8 D9 D18 D19 D20 ltac:(lia) ltac:(lia) ltac:(repeat split; lia) Grib Gau Gab8
                ltac:(intros Nab; lia) Hstk Okab C_spb C_rib C_au C_magc C_magic)
      as (r1 & RUN1 & A2 & A8 & A9 & A18 & A19 & A20 & A3 & A4 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
    set (M1t := fr_k1 memD S ra0 s0v s1v s2v s3v s4v m ab) in RUN1.
    assert (GR1 : mem_grows memD M1t) by ((lazymatch goal with |- ?G => let G' := eval unfold M1t, fr_k1 in G in change_no_check G' end); destruct (Z.eqb_spec ab m); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (Q1 : forall x : word, (m <= U x < m + 8)%Z -> M1t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1t, fr_k1 in G in change_no_check G' end). intros x Hx. destruct (Z.eqb_spec ab m) as [E|N];
        rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; unorm; try lia; reflexivity. }
    remember M1t as M1 eqn:EM1 in RUN1, GR1, Q1. subst M1t.
    (* [comment removed for export] *)
    destruct (k2a_run M1 rom m h1 h2 h3 hv r1 A9 ltac:(lia)
                ltac:(eapply rd_same; [intros x Hx; apply Q1; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia | wd_ulia_c | exact C_hdr])
                Hhv ltac:(eapply store_ok_mono; [exact GR1 | exact Okhdr]))
      as (r2 & RUN2 & B1 & B2 & B3 & B4 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27).
    (* [comment removed for export] *)
    assert (Rnhi2 : rdn BSEGS (wbytes M1 (Z_to_bv 64 m) [Z_to_bv 8 0; h1; h2; h3]) (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))).
    { rewrite <- Hh23. replace (Z_to_bv 64 (m + 2)) with (at_ (Z_to_bv 64 m) (Z.of_nat 2)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (rdn_wbytes_sub BSEGS M1 (Z_to_bv 64 m) [Z_to_bv 8 0; h1; h2; h3] 2 2); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | wd_ulia_c]. }
    assert (Rnlo2 : rdn BSEGS (wbytes M1 (Z_to_bv 64 m) [Z_to_bv 8 0; h1; h2; h3]) (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32))).
    { rewrite rdn_wbytes_out; [| wd_ulia_c | wd_ulia_c | wd_ulia_c].
      eapply rd_same; [intros x Hx; apply Q1; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia | wd_ulia_c | exact C_nlo]. }
    destruct (k2b_run (wbytes M1 (Z_to_bv 64 m) [Z_to_bv 8 0; h1; h2; h3]) rom m n r2 ltac:(rewrite B9; exact A9) ltac:(lia) ltac:(lia) Rnhi2 Rnlo2)
      as (r3 & RUN3 & E1 & E10 & E11 & E12 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
    exists r3. split.
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_k12 in G in change_no_check G' end). subst M1. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    repeat match goal with |- _ /\ _ => split end; try assumption; rch.
  Qed.
End RUNK12.
End FPGen.
End BoAllocFRc3R.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc3T.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Definition fr_item (memD : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 : word) (m ab n8 T c cnt e : Z) (h1 h2 h3 : byte)
           (j0 j1 stw : word) : word -> option byte :=
  fr_k35 (fr_k12 memD S ra0 s0v s1v s2v s3v s4v m ab h1 h2 h3) S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T c cnt e j0 j1 stw.

Section RUNITEM.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 tp tsdp : word) (m spb c d rib au n n8 T tctx cnt mx : Z).
  Variables (h1 h2 h3 : byte) (hv : word) (cpm : byte) (midend : word) (bf0 bf1 bst bcs : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation cs := (csize c).
  #[local] Abbreviation idx := (d / cs)%Z.
  #[local] Abbreviation e := (idx * cs)%Z.
  #[local] Abbreviation ab := (spb + c * 2 ^ 32 + idx * cs)%Z.
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 1 = ra0.
  Hypothesis D2 : getr rD 2 = at_ S (-2400).
  Hypothesis D10 : getr rD 10 = at_ S (-2392).
  Hypothesis D11 : getr rD 11 = Z_to_bv 64 m.
  Hypothesis D8 : getr rD 8 = s0v.   Hypothesis D9 : getr rD 9 = s1v.   Hypothesis D18 : getr rD 18 = s2v.
  Hypothesis D19 : getr rD 19 = s3v. Hypothesis D20 : getr rD 20 = s4v. Hypothesis D21 : getr rD 21 = x21.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gspb : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Gm : (m = spb + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30)%Z.
  Hypothesis Gm2 : (m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0)%Z.
  Hypothesis Gab : (ab = m \/ ab + 16 <= m)%Z.
  Hypothesis Gab8 : (ab mod 8 = 0)%Z.
  Hypothesis Grib : (AIMGHI <= rib /\ rib + 4096 <= U S - 3584)%Z.
  Hypothesis Gau : ((idx + 1) * cs <= au /\ au < 2 ^ 64)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis GabT : (m + 16 + n8 <= T \/ T + 4096 <= ab)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584)%Z.
  Hypothesis Gctxm : (tctx + 4096 <= ab \/ m + 16 + n8 <= tctx)%Z.
  Hypothesis Gctxs : (tctx + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= tctx)%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis Gcnt : (0 <= cnt < mx /\ mx <= 16)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2512)) 112 = true.
  Hypothesis Okhdr : store_ok BSEGS memD (Z_to_bv 64 m) 4 = true.
  Hypothesis Okab : (ab <> m)%Z -> store_ok BSEGS memD (Z_to_bv 64 ab) 8 = true.
  Hypothesis Oksh : store_ok BSEGS memD (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  (* [comment removed for export] *)
  Hypothesis C_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_rib : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 rib)).
  Hypothesis C_au : rdn BSEGS memD (Z_to_bv 64 (rib + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis C_magc : rdn BSEGS memD (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis C_magic : (ab <> m)%Z -> rdn BSEGS memD (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis C_hdr : rdn BSEGS memD (Z_to_bv 64 m) 4 = Some [Z_to_bv 8 3; h1; h2; h3].
  Hypothesis Hhv : bytes_le_to_Z [Z_to_bv 8 3; h1; h2; h3] = bv_unsigned hv.
  Hypothesis Hh23 : [h2; h3] = word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)).
  Hypothesis C_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_kif : rdn BSEGS memD (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS memD (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS memD (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS memD tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS memD (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_f0 : rdn BSEGS memD (Z_to_bv 64 (T + 2840)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS memD (Z_to_bv 64 (T + 2848)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_cache : rdn BSEGS memD (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + 208))).
  Hypothesis C_mx : rdn BSEGS memD (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis C_cnt : rdn BSEGS memD (Z_to_bv 64 pc_) 4 = Some (LE4 cnt).
  Hypothesis C_cs : rdn BSEGS memD (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis L_cs : length bcs = 8%nat.
  Hypothesis C_st : rdn BSEGS memD (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis L_st : length bst = 8%nat.

  Definition item_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = x21 /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
      /\ getr r 22 = getr rD 22 /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24
      /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.

  Theorem rc_item_prim_run :
    exists r, msteps BSEGS (mkst rD (0x4e8a4 : word) memD rom)
                (mkst r ra0 (fr_item memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T c cnt e h1 h2 h3 (at_ f0 1) (v_add (Z_to_bv 64 n) f1) stw) rom)
      /\ item_regs r.
  Proof using L_st C_st L_cs C_cs C_cnt C_mx C_cache L_f1 C_f1 L_f0 C_f0 C_thr C_tctx C_tsdp C_key C_kif C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh C_nlo Hh23 Hhv C_hdr C_magic C_magc C_au C_rib C_spb OkT Oksh Okab Okhdr Hstk Hret Gcnt Gtsdp Gtp Gctxs Gctxm Gctx GabT GT Gn8 Gn Gau Grib Gab8 Gab Gm2 Gm Gspb GS D4 D21 D20 D19 D18 D9 D8 D11 D10 D2 D1 midend cpm hv mx tctx au rib tsdp.
    (lazymatch goal with |- ?G => let G' := eval unfold item_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    assert (Gm2' : (m + 16 <= U S - 3584 /\ m mod 16 = 0)%Z) by (destruct Gm2 as (X1 & X2); destruct Gn8 as (_ & _ & _ & X3); split; [lia | exact X2]).
    assert (Hstk1 : store_ok BSEGS memD (at_ S (-2448)) 48 = true).
    { destruct GS as (GS1 & GS2). eapply (store_ok_sub BSEGS memD (at_ S (-2512)) _ 112); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (run_k12 memD rom rD S ra0 s0v s1v s2v s3v s4v m spb c d rib au n h1 h2 h3 hv D1 D2 D10 D11 D8 D9 D18 D19 D20 GS Gspb Gm Gm2' Gab Gab8 Grib Gau Gn
                Hstk1 Okhdr Okab C_spb C_rib C_au C_magc C_magic C_hdr Hhv Hh23 C_nlo)
      as (r0 & RUN12 & K1 & K2 & K10 & K11 & K12 & K8 & K9 & K18 & K19 & K20 & K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    pose proof (fr_k12_quiet memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS Gspb Gm Gm2' Gab Gn) as QK.
    pose proof (fr_k12_grows memD S ra0 s0v s1v s2v s3v s4v m spb c d h1 h2 h3) as GRK.
    pose proof (BoAllocFRc3R.ab_le m spb c d n Gspb Gm Gab Gn) as (AB1 & AB2 & IDX0 & IDX1 & IDX2 & CSP).
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2). destruct Gm as (Em & Hd & Hc). destruct Gm2 as (Gm3 & Gm16).
    destruct Gn8 as (N8a & N8b & N8c & N8d). destruct GT as (GT1 & (GTS & GT2) & GT16). destruct Gctx as (Gc1 & Gc2).
    pose proof Gctxs as GctxsB. hidehypW GctxsB. pose proof Gctxm as GctxmB. hidehypW GctxmB. clear Gctxs Gctxm.
    (* [comment removed for export] *)
    Ltac xqk QK C := eapply rd_same; [ intros x Hx; apply QK; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                     | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact C ].
    set (M12 := fr_k12 memD S ra0 s0v s1v s2v s3v s4v m ab h1 h2 h3) in *.
    assert (H11' : getr r0 11 = Z_to_bv 64 n8) by (rewrite K11, N8a; reflexivity).
    assert (H21' : getr r0 21 = x21) by (rewrite K21; exact D21).
    assert (H4' : getr r0 4 = tp) by (rewrite K4; exact D4).
    assert (GT' : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z) by (split; [exact GT1 | split; [split; [exact GTS | exact GT2] | exact GT16]]).
    assert (SOK1 : store_ok BSEGS M12 (at_ S (-2512)) 112 = true) by (eapply store_ok_mono; [exact GRK | exact Hstk]).
    assert (SOK2 : store_ok BSEGS M12 (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (n8 / 8)) = true) by (eapply store_ok_mono; [exact GRK | exact Oksh]).
    assert (SOK3 : store_ok BSEGS M12 (Z_to_bv 64 T) (Z.to_nat 4096) = true) by (eapply store_ok_mono; [exact GRK | exact OkT]).
    assert (Gm2'' : (m + 16 <= U S - 3584 /\ m mod 16 = 0)%Z) by (split; [lia | exact Gm16]).
    assert (Gm' : (m = spb + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30)%Z) by (split; [exact Em | split; [exact Hd | exact Hc]]).
    assert (GS' : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z) by (split; assumption).
    assert (Gspb' : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z) by (split; assumption).
    destruct (run_k35 M12 rom r0 S ra0 s0v s1v s2v s3v s4v x21 tp tsdp m spb c e n n8 T tctx cnt mx cpm midend bf0 bf1 bst bcs
                K1 K2 K10 H11' K12 K8 K9 K18 K19 K20 H21' H4' GS' Gspb' ltac:(split; [exact Hc | lia]) ltac:(split; [lia | split; [lia | exact Gm16]]) Gn
                ltac:(split; [exact N8b | split; [exact N8c | exact N8d]]) GT' ltac:(split; [exact Gc1 | exact Gc2]) GctxsB Gtp Gtsdp Gcnt Hret SOK1 SOK2 SOK3
                ltac:(xqk QK C_gsh) ltac:(xqk QK C_sh) ltac:(xqk QK C_gmb) ltac:(xqk QK C_mb) ltac:(xqk QK C_gme) ltac:(xqk QK C_me) ltac:(xqk QK C_ghe) ltac:(xqk QK C_he)
                ltac:(xqk QK C_grm) ltac:(xqk QK C_rm) ltac:(xqk QK C_cpm) C_cpm1 ltac:(xqk QK C_kif) ltac:(xqk QK C_key) ltac:(xqk QK C_tsdp) ltac:(xqk QK C_tctx)
                ltac:(unfold hideW in GctxmB; xqk QK C_thr)
                ltac:(apply (fr_k12_nhi memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn Hh23))
                ltac:(xqk QK C_nlo) ltac:(xqk QK C_f0) L_f0 ltac:(xqk QK C_f1) L_f1 ltac:(xqk QK C_spb) ltac:(xqk QK C_cache)
                ltac:(apply (fr_k12_ra memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s0 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s1 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s2 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s3 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s4 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(xqk QK C_mx) ltac:(xqk QK C_cnt) ltac:(xqk QK C_cs) L_cs ltac:(xqk QK C_st) L_st)
      as (r5 & RUN35 & F2 & F8 & F9 & F18 & F19 & F20 & F21 & F3 & F4 & F22 & F23 & F24 & F25 & F26 & F27).
    exists r5. split.
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_item in G in change_no_check G' end). fold M12. eapply msteps_trans; [exact RUN12 | exact RUN35]. }
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: match goal with |- getr ?rr ?k = getr rD ?k => first [ rewrite F3; exact K3 | rewrite F22; exact K22 | rewrite F23; exact K23 | rewrite F24; exact K24
                                                             | rewrite F25; exact K25 | rewrite F26; exact K26 | rewrite F27; exact K27 ] end.
  Qed.
End RUNITEM.
End FPGen.
End BoAllocFRc3T.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc3T4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3S4.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Definition fr_item34 (memD : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 : word) (m ab n8 T : Z) (h1 h2 h3 : byte)
           (j0 j1 : word) : word -> option byte :=
  fr_k34 (fr_k12 memD S ra0 s0v s1v s2v s3v s4v m ab h1 h2 h3) S x21 m ab n8 T j0 j1.

Section RUNITEM34.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 tp tsdp : word) (m spb c d rib au n n8 T tctx cnt mx : Z).
  Variables (h1 h2 h3 : byte) (hv : word) (cpm : byte) (midend : word) (bf0 bf1 bst bcs : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation cs := (csize c).
  #[local] Abbreviation idx := (d / cs)%Z.
  #[local] Abbreviation e := (idx * cs)%Z.
  #[local] Abbreviation ab := (spb + c * 2 ^ 32 + idx * cs)%Z.
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 1 = ra0.
  Hypothesis D2 : getr rD 2 = at_ S (-2400).
  Hypothesis D10 : getr rD 10 = at_ S (-2392).
  Hypothesis D11 : getr rD 11 = Z_to_bv 64 m.
  Hypothesis D8 : getr rD 8 = s0v.   Hypothesis D9 : getr rD 9 = s1v.   Hypothesis D18 : getr rD 18 = s2v.
  Hypothesis D19 : getr rD 19 = s3v. Hypothesis D20 : getr rD 20 = s4v. Hypothesis D21 : getr rD 21 = x21.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gspb : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Gm : (m = spb + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30)%Z.
  Hypothesis Gm2 : (m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0)%Z.
  Hypothesis Gab : (ab = m \/ ab + 16 <= m)%Z.
  Hypothesis Gab8 : (ab mod 8 = 0)%Z.
  Hypothesis Grib : (AIMGHI <= rib /\ rib + 4096 <= U S - 3584)%Z.
  Hypothesis Gau : ((idx + 1) * cs <= au /\ au < 2 ^ 64)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis GabT : (m + 16 + n8 <= T \/ T + 4096 <= ab)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584)%Z.
  Hypothesis Gctxm : (tctx + 4096 <= ab \/ m + 16 + n8 <= tctx)%Z.
  Hypothesis Gctxs : (tctx + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= tctx)%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2512)) 112 = true.
  Hypothesis Okhdr : store_ok BSEGS memD (Z_to_bv 64 m) 4 = true.
  Hypothesis Okab : (ab <> m)%Z -> store_ok BSEGS memD (Z_to_bv 64 ab) 8 = true.
  Hypothesis Oksh : store_ok BSEGS memD (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  (* [comment removed for export] *)
  Hypothesis C_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_rib : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 rib)).
  Hypothesis C_au : rdn BSEGS memD (Z_to_bv 64 (rib + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis C_magc : rdn BSEGS memD (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis C_magic : (ab <> m)%Z -> rdn BSEGS memD (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis C_hdr : rdn BSEGS memD (Z_to_bv 64 m) 4 = Some [Z_to_bv 8 3; h1; h2; h3].
  Hypothesis Hhv : bytes_le_to_Z [Z_to_bv 8 3; h1; h2; h3] = bv_unsigned hv.
  Hypothesis Hh23 : [h2; h3] = word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)).
  Hypothesis C_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_kif : rdn BSEGS memD (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS memD (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS memD (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS memD tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS memD (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_f0 : rdn BSEGS memD (Z_to_bv 64 (T + 2840)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS memD (Z_to_bv 64 (T + 2848)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_cache : rdn BSEGS memD (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + 208))).

  Definition item34_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = ra0 /\ getr r 2 = at_ S (-2400) /\ getr r 10 = Z_to_bv 64 (T + 208) /\ getr r 11 = Z_to_bv 64 0x10ab58
      /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = Z_to_bv 64 ab
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = x21 /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
      /\ getr r 22 = getr rD 22 /\ getr r 23 = getr rD 23 /\ getr r 24 = getr rD 24
      /\ getr r 25 = getr rD 25 /\ getr r 26 = getr rD 26 /\ getr r 27 = getr rD 27.

  Theorem rc_item34_run :
    exists r, msteps BSEGS (mkst rD (0x4e8a4 : word) memD rom)
                (mkst r (0x4eca8 : word) (fr_item34 memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) rom)
      /\ item34_regs r.
  Proof using C_cache L_f1 C_f1 L_f0 C_f0 C_thr C_tctx C_tsdp C_key C_kif C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh C_nlo Hh23 Hhv C_hdr C_magic C_magc C_au C_rib C_spb OkT Oksh Okab Okhdr Hstk Gtsdp Gtp Gctxs Gctxm Gctx GabT GT Gn8 Gn Gau Grib Gab8 Gab Gm2 Gm Gspb GS D4 D21 D20 D19 D18 D9 D8 D11 D10 D2 D1 midend cpm hv tctx au rib tsdp.
    (lazymatch goal with |- ?G => let G' := eval unfold item34_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    assert (Gm2' : (m + 16 <= U S - 3584 /\ m mod 16 = 0)%Z) by (destruct Gm2 as (X1 & X2); destruct Gn8 as (_ & _ & _ & X3); split; [lia | exact X2]).
    assert (Hstk1 : store_ok BSEGS memD (at_ S (-2448)) 48 = true).
    { destruct GS as (GS1 & GS2). eapply (store_ok_sub BSEGS memD (at_ S (-2512)) _ 112); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (run_k12 memD rom rD S ra0 s0v s1v s2v s3v s4v m spb c d rib au n h1 h2 h3 hv D1 D2 D10 D11 D8 D9 D18 D19 D20 GS Gspb Gm Gm2' Gab Gab8 Grib Gau Gn
                Hstk1 Okhdr Okab C_spb C_rib C_au C_magc C_magic C_hdr Hhv Hh23 C_nlo)
      as (r0 & RUN12 & K1 & K2 & K10 & K11 & K12 & K8 & K9 & K18 & K19 & K20 & K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    pose proof (fr_k12_quiet memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS Gspb Gm Gm2' Gab Gn) as QK.
    pose proof (fr_k12_grows memD S ra0 s0v s1v s2v s3v s4v m spb c d h1 h2 h3) as GRK.
    pose proof (BoAllocFRc3R.ab_le m spb c d n Gspb Gm Gab Gn) as (AB1 & AB2 & IDX0 & IDX1 & IDX2 & CSP).
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2). destruct Gm as (Em & Hd & Hc). destruct Gm2 as (Gm3 & Gm16).
    destruct Gn8 as (N8a & N8b & N8c & N8d). destruct GT as (GT1 & (GTS & GT2) & GT16). destruct Gctx as (Gc1 & Gc2).
    pose proof Gctxs as GctxsB. hidehypW GctxsB. pose proof Gctxm as GctxmB. hidehypW GctxmB. clear Gctxs Gctxm.
    (* [comment removed for export] *)
    Ltac xqk QK C := eapply rd_same; [ intros x Hx; apply QK; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                     | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact C ].
    set (M12 := fr_k12 memD S ra0 s0v s1v s2v s3v s4v m ab h1 h2 h3) in *.
    assert (H11' : getr r0 11 = Z_to_bv 64 n8) by (rewrite K11, N8a; reflexivity).
    assert (H21' : getr r0 21 = x21) by (rewrite K21; exact D21).
    assert (H4' : getr r0 4 = tp) by (rewrite K4; exact D4).
    assert (GT' : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z) by (split; [exact GT1 | split; [split; [exact GTS | exact GT2] | exact GT16]]).
    assert (SOK1 : store_ok BSEGS M12 (at_ S (-2512)) 112 = true) by (eapply store_ok_mono; [exact GRK | exact Hstk]).
    assert (SOK2 : store_ok BSEGS M12 (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (n8 / 8)) = true) by (eapply store_ok_mono; [exact GRK | exact Oksh]).
    assert (SOK3 : store_ok BSEGS M12 (Z_to_bv 64 T) (Z.to_nat 4096) = true) by (eapply store_ok_mono; [exact GRK | exact OkT]).
    assert (Gm2'' : (m + 16 <= U S - 3584 /\ m mod 16 = 0)%Z) by (split; [lia | exact Gm16]).
    assert (Gm' : (m = spb + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30)%Z) by (split; [exact Em | split; [exact Hd | exact Hc]]).
    assert (GS' : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z) by (split; assumption).
    assert (Gspb' : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z) by (split; assumption).
    destruct (run_k34 M12 rom r0 S ra0 s0v s1v s2v s3v s4v x21 tp tsdp m spb c e n n8 T tctx cpm midend bf0 bf1
                K1 K2 K10 H11' K12 K8 K9 K18 K19 K20 H21' H4' GS' Gspb' ltac:(split; [exact Hc | lia]) ltac:(split; [lia | split; [lia | exact Gm16]]) Gn
                ltac:(split; [exact N8b | split; [exact N8c | exact N8d]]) GT' ltac:(split; [exact Gc1 | exact Gc2]) GctxsB Gtp Gtsdp SOK1 SOK2 SOK3
                ltac:(xqk QK C_gsh) ltac:(xqk QK C_sh) ltac:(xqk QK C_gmb) ltac:(xqk QK C_mb) ltac:(xqk QK C_gme) ltac:(xqk QK C_me) ltac:(xqk QK C_ghe) ltac:(xqk QK C_he)
                ltac:(xqk QK C_grm) ltac:(xqk QK C_rm) ltac:(xqk QK C_cpm) C_cpm1 ltac:(xqk QK C_kif) ltac:(xqk QK C_key) ltac:(xqk QK C_tsdp) ltac:(xqk QK C_tctx)
                ltac:(unfold hideW in GctxmB; xqk QK C_thr)
                ltac:(apply (fr_k12_nhi memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn Hh23))
                ltac:(xqk QK C_nlo) ltac:(xqk QK C_f0) L_f0 ltac:(xqk QK C_f1) L_f1 ltac:(xqk QK C_spb) ltac:(xqk QK C_cache)
                ltac:(apply (fr_k12_ra memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s0 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s1 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s2 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s3 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn))
                ltac:(apply (fr_k12_s4 memD S ra0 s0v s1v s2v s3v s4v m spb c d n h1 h2 h3 GS' Gspb' Gm' Gm2'' Gab Gn)))
      as (r5 & RUN35 & F1 & F2 & F10 & F11 & F12 & F13 & F8 & F9 & F18 & F19 & F20 & F21 & F3 & F4 & F22 & F23 & F24 & F25 & F26 & F27).
    exists r5. split.
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_item34 in G in change_no_check G' end). fold M12. eapply msteps_trans; [exact RUN12 | exact RUN35]. }
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: match goal with |- getr ?rr ?k = getr rD ?k => first [ rewrite F3; exact K3 | rewrite F22; exact K22 | rewrite F23; exact K23 | rewrite F24; exact K24
                                                             | rewrite F25; exact K25 | rewrite F26; exact K26 | rewrite F27; exact K27 ] end.
  Qed.
End RUNITEM34.
End FPGen.
End BoAllocFRc3T4.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc3U4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFRc3c BoAllocFRc3R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3S4 BoAllocFRc3T4.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Section ITEM34MEM.
  Variables (memD : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 : word) (m ab n8 T : Z) (h1 h2 h3 : byte) (j0 j1 : word).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gm : 0x10007fff8000 <= ab /\ (ab = m \/ ab + 16 <= m) /\ m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0.
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis GabT : m + 16 + n8 <= T \/ T + 4096 <= ab.
  #[local] Abbreviation M9 := (fr_item34 memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 j0 j1).
  #[local] Abbreviation shlo := (0x7fff8000 + (m + 16) / 8).

  Lemma TSB_IM : (T + 4096 <= 0x7fff7000) \/ (0x10007fff8000 <= T).
  Proof using GT n8 m S. pose proof GT as X. unfold hideW in X. lia. Qed.
  Lemma shlen8I : shlen (Z_to_bv 64 n8) = n8 / 8.
  Proof using Gn8 m. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. reflexivity. Qed.
  Lemma shad_m : shad (Z_to_bv 64 (m + 16)) = shlo.
  Proof using Gn8 Gm GS n8 ab S. pose proof (u64_range S). (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). unorm. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma md8 : 8 * ((m + 16) / 8) = m + 16 /\ 8 * (n8 / 8) = n8 /\ 0x10007fff8000 / 8 <= (m + 16) / 8 /\ (m + 16) / 8 + n8 / 8 <= 2 ^ 44.
  Proof using GT Gn8 Gm GS j1 T ab S memD. pose proof (u64_range S). Z.div_mod_to_equations. lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Ltac lsideI := wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; rewrite ?Z2Nat.id by lia;
                 (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul] in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.

  Ltac wo tac := rewrite wbytes_outside by (tac; lsideI).
  Ltac ro tac := rewrite rdn_wbytes_out by (tac; lsideI).

  Lemma fr_item34_outside : forall a : word,
    (U a < U S - 2512 \/ U S - 2400 <= U a) -> (U a < m \/ m + 4 <= U a) -> (ab = m \/ U a < ab \/ ab + 8 <= U a) ->
    (U a < shlo \/ shlo + n8 / 8 <= U a) ->
    (U a < T + 2840 \/ T + 2856 <= U a) -> M9 a = memD a.
  Proof using GT Gn8 Gm GS.
    intros a A1 A2 A3 A4 A8. pose proof (u64_range S) as HSr. pose proof md8 as MD.
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_item34, fr_k34, fr_k4, fr_k3, fr_k12, fr_k1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite ?shad_m, ?shlen8I.
    do 2 wo ltac:(clear - A8 GT1 GT2 HSr GS1 GS2).                  (* [comment removed for export] *)
    do 2 wo ltac:(clear - A1 HSr GS1 GS2).                          (* [comment removed for export] *)
    wo ltac:(clear - A4 MD HSr GS1 GS2 Gm3 Gm1 Gm2 Gn8).            (* [comment removed for export] *)
    do 7 wo ltac:(clear - A1 HSr GS1 GS2).                          (* [comment removed for export] *)
    wo ltac:(clear - A2 HSr GS1 GS2 Gm3 Gm1 Gm2 Gn8).                   (* [comment removed for export] *)
    destruct (Z.eqb_spec ab m) as [E | N].
    - do 6 wo ltac:(clear - A1 HSr GS1 GS2). reflexivity.
    - assert (A3' : U a < ab \/ ab + 8 <= U a) by (destruct A3 as [A3 | A3]; [contradiction | exact A3]).
      wo ltac:(clear - A3' HSr GS1 GS2 Gm3 Gm1 Gm2 Gn8).
      do 6 wo ltac:(clear - A1 HSr GS1 GS2). reflexivity.
  Qed.
  Lemma fr_item34_foot : forall a : word, M9 a <> memD a ->
    (U S - 2512 <= U a < U S - 2400) \/ (m <= U a < m + 4) \/ (ab <> m /\ ab <= U a < ab + 8) \/ (shlo <= U a < shlo + n8 / 8)
    \/ (T + 2840 <= U a < T + 2856).
  Proof using GabT GT Gn8 Gm GS.
    intros a NE.
    destruct (decide (U S - 2512 <= U a < U S - 2400)) as [|N1]; [am_tauto|].
    destruct (decide (m <= U a < m + 4)) as [|N2]; [am_tauto|].
    destruct (decide (ab <> m /\ ab <= U a < ab + 8)) as [|N3]; [am_tauto|].
    destruct (decide (shlo <= U a < shlo + n8 / 8)) as [|N4]; [am_tauto|].
    destruct (decide (T + 2840 <= U a < T + 2856)) as [|N8]; [am_tauto|].
    exfalso. apply NE. apply fr_item34_outside; [clear - N1; lia | clear - N2; lia | | clear - N4; lia | clear - N8; lia].
    destruct (Z.eq_dec ab m) as [E | N]; [left; exact E | right; clear - N3 N; lia].
  Qed.
  Lemma fr_item34_grows : mem_grows memD M9.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_item34, fr_k34, fr_k4, fr_k3, fr_k12, fr_k1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (Z.eqb_spec ab m); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Qed.

  Lemma fr_item34_shadow : forall i, 0 <= i < n8 / 8 -> M9 (Z_to_bv 64 (shlo + i)) = Some (Z_to_bv 8 0xfa).
  Proof using GabT GT Gn8 Gm GS.
    intros i Hi. pose proof TSB_IM as TSB1. pose proof (u64_range S) as HSr. pose proof md8 as MD.
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & (_ & GT2)). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_item34, fr_k34, fr_k4, fr_k3 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite ?shad_m, ?shlen8I.
    do 2 wo ltac:(clear - Hi TSB1 MD GT1 GT2 HSr GS1 GS2 Gm3 Gm1).
    do 2 wo ltac:(clear - Hi MD HSr GS1 GS2 Gm3 Gm1).
    rewrite wbytes_inside by (clear - Hi MD HSr GS1 GS2 Gm3 Gm1 Gn8; lsideI).
    f_equal. rewrite nth_repeat_lt; [(lazymatch goal with |- ?G => let G' := eval unfold cbyte in G in change_no_check G' end); unorm; reflexivity|].
    unorm. apply Z2Nat.inj_lt; lia.
  Qed.

End ITEM34MEM.

(* [comment removed for export] *)

End FPGen.
End BoAllocFRc3U4.
Require LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc4Sp.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Section RTASPIN.
  Variables (mem rom : word -> option byte).
  Variable regs : bvmap 5 word.
  Variable S : word.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis H2 : getr regs 2 = at_ S (-2640).
  Hypothesis GS : (2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2656)) 16 = true.
  Hypothesis Rg1 : rdn BSEGS mem (Z_to_bv 64 0x105f58) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis Rg2 : rdn BSEGS mem (Z_to_bv 64 0x105f60) 8 = Some (LE8 (Z_to_bv 64 0x19fcdc)).
  Hypothesis Rdy : rdn BSEGS mem (Z_to_bv 64 0x19fcdc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Lemma rta_spin_run : exists r m', msteps BSEGS (mkst regs (0x4f344 : word) mem rom) (mkst r (0x4f674 : word) m' rom).
  Proof using Rdy Rg2 Rg1 Hstk GS H2 H10 S.
    assert (V0 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 0)) = bv_unsigned (Z_to_bv 64 0)) by (apply bytes4_small; lia).
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2).
    wd_eexists. wd_eexists.
    ab_tk F_4f344 D_4f344 ltac:(condz).                (* [comment removed for export] *)
    an F_4f4cc D_4f4cc.                                (* [comment removed for export] *)
    an F_4f650 D_4f650.                                (* [comment removed for export] *)
    fsd F_4f654 D_4f654 (at_ S (-2648)).               (* [comment removed for export] *)
    an F_4f658 D_4f658.                                (* [comment removed for export] *)
    cld8 F_4f65c D_4f65c (Z_to_bv 64 1) Rg1.           (* [comment removed for export] *)
    ab_ft F_4f660 D_4f660 ltac:(condz).                (* [comment removed for export] *)
    an F_4f664 D_4f664.                                (* [comment removed for export] *)
    cld8 F_4f668 D_4f668 (Z_to_bv 64 0x19fcdc) Rg2.    (* [comment removed for export] *)
    clw F_4f66c D_4f66c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) Rdy V0.   (* [comment removed for export] *)
    try (rewrite (v_lw_small 0) by lia).
    ab_ft F_4f670 D_4f670 ltac:(condz).                (* [comment removed for export] *)
    wd_refl.
  Qed.
End RTASPIN.

(* [comment removed for export] *)
Lemma rta_spin_to_spin : forall (r : bvmap 5 word) (M rom : word -> option byte) (model : Model),
  to_spin BSEGS (mkst r (0x4f674 : word) M rom) model.
Proof using.
  intros r M rom model.
  apply (ts_spin_of_step_j BSEGS (mkst r (0x4f674 : word) M rom) model W_4f674 0 0 4%Z);
    [reflexivity | exact F_4f674 | reflexivity | exact D_4f674 | reflexivity | reflexivity].
Qed.
End FPGen.
End BoAllocFRc4Sp.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc4V.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Section FULLMEM.
  Variables (mem : word -> option byte).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (T spb c e mx nf : Z) (ks : list Z) (b80 : list byte) (w9 w22 stw : word).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c).
  #[local] Abbreviation RIz := (spb + 2 ^ 37 + 128 * c).
  #[local] Abbreviation fa := (spb + c * 2 ^ 32 + 0xE0000000).
  #[local] Abbreviation cnt' := (mx - mx / 2).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis GT : 4096 <= T /\ T + 4096 <= U S - 3584.
  Hypothesis Gspb : 0x10007fff8000 <= spb /\ spb + 2 ^ 37 + 4096 <= U S - 3584.
  Hypothesis GTsp : hideW (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T).
  Hypothesis Gc : 1 <= c <= 30.
  Hypothesis Gmx : 2 <= mx <= 16.
  Hypothesis Gnf : 0 <= nf /\ 4 * (nf + mx / 2) <= 2 ^ 29.
  Hypothesis Gks : Z.of_nat (length ks) = mx / 2.

  #[local] Abbreviation MF := (fr_full mem S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx nf ks b80 w9 w22 stw).

  Lemma full_geo : 1 <= mx / 2 <= 8 /\ 1 <= cnt' <= 8 /\ spb + 2 ^ 32 <= fa /\ fa + 4 * nf + 4 * (mx / 2) <= spb + 2 ^ 37
                   /\ spb + 2 ^ 37 <= RIz /\ RIz + 128 <= spb + 2 ^ 37 + 4096.
  Proof using Gnf Gmx Gc.
    clear GS GT Gspb GTsp Gks.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (replace (2 ^ 37) with (32 * 2 ^ 32) by reflexivity; nia). assert (2 ^ 32 <= c * 2 ^ 32) by nia.
    assert (1 <= mx / 2 <= 8 /\ 1 <= mx - mx / 2 <= 8) by (clear - Gmx; Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma fr_full_outside : forall a : word,
    (U a < U S - 2720 \/ U S - 2400 <= U a) -> (U a < pc_ \/ pc_ + 4 <= U a) -> (U a < pc_ + 16 + 4 * cnt' \/ pc_ + 16 + 4 * cnt' + 4 <= U a) ->
    (U a < T + 2784 \/ T + 2792 <= U a) -> (U a < RIz \/ RIz + 8 <= U a) -> (U a < RIz + 16 \/ RIz + 24 <= U a) -> (U a < RIz + 80 \/ RIz + 88 <= U a) ->
    (U a < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U a) -> MF a = mem a.
  Proof using Gks Gnf Gmx Gc Gspb GT GS.
    intros a A1 A2 A3 A4 A5 A6 A7 A8. pose proof (u64_range S) as HSr. pose proof full_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gspb as (Gs1 & Gs2). destruct Gnf as (Gn0 & Gn1).
    assert (GSs : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by lia.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_full in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite (fr_dtl_outside _ S GSs T c cnt' e stw ltac:(lia) Gc ltac:(lia) a ltac:(lia) A2 A3 A4).
    rewrite wbytes_outside by (rewrite length_N_to_le_bytes; wd_ulia).
    rewrite (fr_mro_outside _ S GSs) by lia.
    rewrite fr_rtac_outside by lia.
    rewrite fa_fill_outside by (rewrite ?Gks; lia).
    rewrite efs_m0_outside by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    rewrite (fr_rta0_outside _ S GSs) by lia.
    rewrite (fr_drn_outside _ S GSs) by lia.
    apply (fr_dlf_outside mem S GSs). lia.
  Qed.

  Lemma fr_full_foot : forall a : word, MF a <> mem a ->
    (U S - 2720 <= U a < U S - 2400) \/ (pc_ <= U a < pc_ + 4) \/ (pc_ + 16 + 4 * cnt' <= U a < pc_ + 16 + 4 * cnt' + 4) \/ (T + 2784 <= U a < T + 2792)
    \/ (RIz <= U a < RIz + 8) \/ (RIz + 16 <= U a < RIz + 24) \/ (RIz + 80 <= U a < RIz + 88) \/ (fa + 4 * nf <= U a < fa + 4 * nf + 4 * (mx / 2)).
  Proof using Gks Gnf Gmx Gc Gspb GT GS.
    intros a NE.
    destruct (decide (U S - 2720 <= U a < U S - 2400)) as [|N1]; [am_tauto|].
    destruct (decide (pc_ <= U a < pc_ + 4)) as [|N2]; [am_tauto|].
    destruct (decide (pc_ + 16 + 4 * cnt' <= U a < pc_ + 16 + 4 * cnt' + 4)) as [|N3]; [am_tauto|].
    destruct (decide (T + 2784 <= U a < T + 2792)) as [|N4]; [am_tauto|].
    destruct (decide (RIz <= U a < RIz + 8)) as [|N5]; [am_tauto|].
    destruct (decide (RIz + 16 <= U a < RIz + 24)) as [|N6]; [am_tauto|].
    destruct (decide (RIz + 80 <= U a < RIz + 88)) as [|N7]; [am_tauto|].
    destruct (decide (fa + 4 * nf <= U a < fa + 4 * nf + 4 * (mx / 2))) as [|N8]; [am_tauto|].
    exfalso. apply NE. apply fr_full_outside; [clear - N1; lia | clear - N2; lia | clear - N3; lia | clear - N4; lia | clear - N5; lia | clear - N6; lia | clear - N7; lia | clear - N8; lia].
  Qed.

  Lemma fr_full_grows : mem_grows mem MF.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_full in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    eapply mem_grows_trans; [| apply fr_dtl_grows]. eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply fr_mro_grows].
    eapply mem_grows_trans; [| apply fr_rtac_grows]. eapply mem_grows_trans; [| apply fa_fill_grows]. eapply mem_grows_trans; [| apply efs_m0_grows].
    eapply mem_grows_trans; [| apply fr_rta0_grows]. eapply mem_grows_trans; [| apply fr_drn_grows]. apply fr_dlf_grows.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_full_cnt : rdn BSEGS MF (Z_to_bv 64 pc_) 4 = Some (LE4 (cnt' + 1)).
  Proof using Gnf Gmx Gc GT GS.
    pose proof full_geo as (G1 & G2 & _). destruct GS as (GS1 & GS2). (lazymatch goal with |- ?G => let G' := eval unfold fr_full in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    apply fr_dtl_cnt; [lia | exact GT | exact Gc | lia].
  Qed.
  Lemma fr_full_slot : rdn BSEGS MF (Z_to_bv 64 (pc_ + 16 + 4 * cnt')) 4 = Some (LE4 (e / 16)).
  Proof using Gnf Gmx Gc GT GS.
    pose proof full_geo as (G1 & G2 & _). destruct GS as (GS1 & GS2). (lazymatch goal with |- ?G => let G' := eval unfold fr_full in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    apply fr_dtl_slot; [lia | exact GT | exact Gc | lia].
  Qed.

  Ltac through_dtl :=
    eapply rd_same; [ intros x Hx; apply (fr_dtl_outside _ S ltac:(lia) T c cnt' e stw ltac:(lia) Gc ltac:(lia));
                                     revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; unfold hideW in GTsp; lia
                    | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].

  Lemma fr_full_mu : rdn BSEGS MF (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Proof using Gnf Gmx Gc GTsp Gspb GT GS.
    pose proof (u64_range S) as HSr. pose proof full_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gspb as (Gs1 & Gs2). destruct Gnf as (Gn0 & Gn1).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_full in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). through_dtl. apply rdn_wbytes_hit8. unorm. lia.
  Qed.
  Lemma fr_full_nf : rdn BSEGS MF (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 (nf + mx / 2))).
  Proof using Gnf Gmx Gc GTsp Gspb GT GS.
    pose proof (u64_range S) as HSr. pose proof full_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gspb as (Gs1 & Gs2). destruct Gnf as (Gn0 & Gn1).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_full in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). through_dtl.
    rewrite rdn_wbytes_out by (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia).
    eapply rd_same; [ intros x Hx; apply (fr_mro_outside _ S ltac:(lia)); revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].
    apply fr_rtac_nf. lia.
  Qed.
  Lemma fr_full_fa : forall i k, nth_error ks i = Some k -> rdn BSEGS MF (Z_to_bv 64 (fa + 4 * nf + 4 * Z.of_nat i)) 4 = Some (LE4 k).
  Proof using Gks Gnf Gmx Gc GTsp Gspb GT GS.
    intros i k Hik. pose proof (u64_range S) as HSr. pose proof full_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gspb as (Gs1 & Gs2). destruct Gnf as (Gn0 & Gn1).
    assert (Hi : Z.of_nat i < mx / 2) by (rewrite <- Gks; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_full in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). through_dtl.
    rewrite rdn_wbytes_out by (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia).
    eapply rd_same; [ intros x Hx; apply (fr_mro_outside _ S ltac:(lia)); revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].
    eapply rd_same; [ intros x Hx; apply fr_rtac_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].
    apply fa_fill_cell; [lia | rewrite Gks; lia | exact Hik].
  Qed.
End FULLMEM.
End FPGen.
End BoAllocFRc4V.
Module BoAllocFRc4T.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc3S.BoAllocFRc3S4 BoAllocFRc3T4 BoAllocFRc3U4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R BoAllocFRc4V.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Definition fr_itemF (memD : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (m ab n8 T : Z) (h1 h2 h3 : byte)
           (j0 j1 : word) (spb c e mx nf : Z) (ks : list Z) (b80 : list byte) (w9 w22 stw : word) : word -> option byte :=
  fr_full (fr_item34 memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 j0 j1)
          S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx nf ks b80 w9 w22 stw.

Section RUNITEMF.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S ra0 s0v s1v s2v s3v s4v x21 tp tsdp : word) (m spb c d rib au n n8 T tctx : Z).
  Variables (h1 h2 h3 : byte) (hv : word) (cpm : byte) (midend : word) (bf0 bf1 : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation cs := (csize c).
  #[local] Abbreviation idx := (d / cs)%Z.
  #[local] Abbreviation e := (idx * cs)%Z.
  #[local] Abbreviation ab := (spb + c * 2 ^ 32 + idx * cs)%Z.
  #[local] Abbreviation f0 := (Z_to_bv 64 (bytes_le_to_Z bf0)).
  #[local] Abbreviation f1 := (Z_to_bv 64 (bytes_le_to_Z bf1)).
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 1 = ra0.
  Hypothesis D2 : getr rD 2 = at_ S (-2400).
  Hypothesis D10 : getr rD 10 = at_ S (-2392).
  Hypothesis D11 : getr rD 11 = Z_to_bv 64 m.
  Hypothesis D8 : getr rD 8 = s0v.   Hypothesis D9 : getr rD 9 = s1v.   Hypothesis D18 : getr rD 18 = s2v.
  Hypothesis D19 : getr rD 19 = s3v. Hypothesis D20 : getr rD 20 = s4v. Hypothesis D21 : getr rD 21 = x21.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gspb : (0x10007fff8000 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Gm : (m = spb + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30)%Z.
  Hypothesis Gm2 : (m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0)%Z.
  Hypothesis Gab : (ab = m \/ ab + 16 <= m)%Z.
  Hypothesis Gab8 : (ab mod 8 = 0)%Z.
  Hypothesis Grib : (AIMGHI <= rib /\ rib + 4096 <= U S - 3584)%Z.
  Hypothesis Gau : ((idx + 1) * cs <= au /\ au < 2 ^ 64)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis GabT : (m + 16 + n8 <= T \/ T + 4096 <= ab)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584)%Z.
  Hypothesis Gctxm : (tctx + 4096 <= ab \/ m + 16 + n8 <= tctx)%Z.
  Hypothesis Gctxs : (tctx + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= tctx)%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2512)) 112 = true.
  Hypothesis Okhdr : store_ok BSEGS memD (Z_to_bv 64 m) 4 = true.
  Hypothesis Okab : (ab <> m)%Z -> store_ok BSEGS memD (Z_to_bv 64 ab) 8 = true.
  Hypothesis Oksh : store_ok BSEGS memD (Z_to_bv 64 (shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  (* [comment removed for export] *)
  Hypothesis C_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis C_rib : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 rib)).
  Hypothesis C_au : rdn BSEGS memD (Z_to_bv 64 (rib + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis C_magc : rdn BSEGS memD (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis C_magic : (ab <> m)%Z -> rdn BSEGS memD (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9)).
  Hypothesis C_hdr : rdn BSEGS memD (Z_to_bv 64 m) 4 = Some [Z_to_bv 8 3; h1; h2; h3].
  Hypothesis Hhv : bytes_le_to_Z [Z_to_bv 8 3; h1; h2; h3] = bv_unsigned hv.
  Hypothesis Hh23 : [h2; h3] = word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)).
  Hypothesis C_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_kif : rdn BSEGS memD (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS memD (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS memD (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn BSEGS memD tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS memD (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_f0 : rdn BSEGS memD (Z_to_bv 64 (T + 2840)) 8 = Some bf0.
  Hypothesis L_f0 : length bf0 = 8%nat.
  Hypothesis C_f1 : rdn BSEGS memD (Z_to_bv 64 (T + 2848)) 8 = Some bf1.
  Hypothesis L_f1 : length bf1 = 8%nat.
  Hypothesis C_cache : rdn BSEGS memD (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + 208))).

  (* [comment removed for export] *)
  Variables (x22 x23 x24 x25 x26 x27 : word) (mx nf mfa pgp : Z) (ks : list Z) (b80 b88 b470 bst bcs : list byte).
  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  #[local] Abbreviation RIz := (spb + 2 ^ 37 + 128 * c)%Z.
  #[local] Abbreviation fa := (spb + c * 2 ^ 32 + 0xE0000000)%Z.
  Hypothesis D22 : getr rD 22 = x22. Hypothesis D23 : getr rD 23 = x23. Hypothesis D24 : getr rD 24 = x24.
  Hypothesis D25 : getr rD 25 = x25. Hypothesis D26 : getr rD 26 = x26. Hypothesis D27 : getr rD 27 = x27.
  Hypothesis Erib : rib = (spb + 2 ^ 37)%Z.
  Hypothesis Gspb2 : (spb + 2 ^ 37 + 4096 <= U S - 3584 /\ spb mod 8 = 0)%Z.
  Hypothesis GTsp : hideW (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T)%Z.
  Hypothesis Gmx : (2 <= mx <= 16)%Z.
  Hypothesis Gnf : (0 <= nf /\ 4 * (nf + mx / 2) <= mfa)%Z.
  Hypothesis Gmfa : (0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0)%Z.
  Hypothesis Gks : Z.of_nat (length ks) = (mx / 2)%Z.
  Hypothesis Fks : Forall (fun k => (0 <= k < 2 ^ 31)%Z) ks.
  Hypothesis Gpgp : (AIMGLO <= pgp /\ pgp + 8 <= AIMGHI)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis L80 : length b80 = 8%nat.  Hypothesis L88 : length b88 = 8%nat.  Hypothesis L470 : length b470 = 8%nat.
  Hypothesis Lst : length bst = 8%nat.  Hypothesis Lcs : length bcs = 8%nat.
  Hypothesis HstkF : store_ok BSEGS memD (at_ S (-2720)) 320 = true.
  Hypothesis OkRI : store_ok BSEGS memD (Z_to_bv 64 RIz) 128 = true.
  Hypothesis Okfa : store_ok BSEGS memD (Z_to_bv 64 (fa + 4 * nf)) (4 * length ks) = true.
  Hypothesis C_mx : rdn BSEGS memD (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis C_cnt : rdn BSEGS memD (Z_to_bv 64 pc_) 4 = Some (LE4 mx).
  Hypothesis C_cs : rdn BSEGS memD (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis C_st : rdn BSEGS memD (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis C_src : forall i k, nth_error ks i = Some k -> rdn BSEGS memD (Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i)) 4 = Some (LE4 k).
  Hypothesis C_int : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff).
  Hypothesis C_gpg : rdn BSEGS memD (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 pgp)).
  Hypothesis C_pg : rdn BSEGS memD (Z_to_bv 64 pgp) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_470 : rdn BSEGS memD (Z_to_bv 64 0x10468) 8 = Some b470.
  Hypothesis C_mu : rdn BSEGS memD (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_nf : rdn BSEGS memD (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis C_mfa : rdn BSEGS memD (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_80 : rdn BSEGS memD (Z_to_bv 64 (RIz + 80)) 8 = Some b80.
  Hypothesis C_88 : rdn BSEGS memD (Z_to_bv 64 (RIz + 88)) 8 = Some b88.

  Definition itemF_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = x21 /\ getr r 3 = getr rD 3 /\ getr r 4 = tp
      /\ getr r 22 = x22 /\ getr r 23 = x23 /\ getr r 24 = x24 /\ getr r 25 = x25 /\ getr r 26 = x26 /\ getr r 27 = x27.

  Theorem rc_item_full_run :
    exists r w9 w22, msteps BSEGS (mkst rD (0x4e8a4 : word) memD rom)
                (mkst r ra0 (fr_itemF memD S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 m ab n8 T h1 h2 h3 (at_ f0 1) (v_add (Z_to_bv 64 n) f1)
                                      spb c e mx nf ks b80 w9 w22 stw) rom)
      /\ itemF_regs r.
  Proof using C_88 C_80 C_mfa C_nf C_mu C_470 C_pg C_gpg C_int C_src C_st C_cs C_cnt C_mx Okfa OkRI HstkF Lcs Lst L470 L88 L80 Hret Gpgp Fks Gks Gmfa Gnf Gmx GTsp Gspb2 Erib D27 D26 D25 D24 D23 D22 b470 b88 pgp mfa C_cache L_f1 C_f1 L_f0 C_f0 C_thr C_tctx C_tsdp C_key C_kif C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh C_nlo Hh23 Hhv C_hdr C_magic C_magc C_au C_rib C_spb OkT Oksh Okab Okhdr Hstk Gtsdp Gtp Gctxs Gctxm Gctx GabT GT Gn8 Gn Gau Grib Gab8 Gab Gm2 Gm Gspb GS D4 D21 D20 D19 D18 D9 D8 D11 D10 D2 D1 midend cpm hv tctx au rib tsdp.
    (lazymatch goal with |- ?G => let G' := eval unfold itemF_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    destruct (rc_item34_run memD rom rD S ra0 s0v s1v s2v s3v s4v x21 tp tsdp m spb c d rib au n n8 T tctx h1 h2 h3 hv cpm midend bf0 bf1
                D1 D2 D10 D11 D8 D9 D18 D19 D20 D21 D4 GS Gspb Gm Gm2 Gab Gab8 Grib Gau Gn Gn8 GT GabT Gctx Gctxm Gctxs Gtp Gtsdp Hstk Okhdr Okab Oksh OkT C_spb C_rib C_au C_magc C_magic C_hdr Hhv Hh23 C_nlo C_gsh C_sh C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm C_cpm C_cpm1 C_kif C_key C_tsdp C_tctx C_thr C_f0 L_f0 C_f1 L_f1 C_cache)
      as (r5 & RUN34 & F1 & F2 & F10 & F11 & F12 & F13 & F8 & F9 & F18 & F19 & F20 & F21 & F3 & F4 & F22 & F23 & F24 & F25 & F26 & F27).
    pose proof (BoAllocFRc3R.ab_le m spb c d n Gspb Gm Gab Gn) as (AB1 & AB2 & IDX0 & IDX1 & IDX2 & CSP).
    destruct GS as (GS1 & GS2). destruct Gspb as (Gs1 & Gs2). destruct Gm as (Em & Hd & Hc). destruct Gm2 as (Gm3 & Gm16).
    destruct Gn8 as (N8a & N8b & N8c & N8d). destruct GT as (GT1 & (GTS & GT2) & GT16). destruct Gspb2 as (Gs3 & Gs8).
    assert (I_GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z) by (split; assumption).
    assert (I_Gm : (0x10007fff8000 <= ab /\ (ab = m \/ ab + 16 <= m) /\ m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0)%Z) by (split; [lia | split; [exact Gab | split; [exact Gm3 | exact Gm16]]]).
    assert (I_Gn8 : (8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40)%Z) by lia.
    assert (I_GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z) by (split; [exact GT1 | split; [exact GTS | exact GT2]]).
    pose proof (fr_item34_outside memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 (at_ f0 1) (v_add (Z_to_bv 64 n) f1) I_GS I_Gm I_Gn8 I_GT) as QK.
    pose proof (fr_item34_grows memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) as GRK.
    remember (fr_item34 memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 (at_ f0 1) (v_add (Z_to_bv 64 n) f1)) as M34 eqn:EM34 in RUN34, QK, GRK.
    assert (SHR : (0x7fff8000 + 0x10007fff8000 / 8 <= 0x7fff8000 + (m + 16) / 8 /\ 0x7fff8000 + (m + 16) / 8 + n8 / 8 <= 0x7fff8000 + 2 ^ 44)%Z).
    { clear - AB1 AB2 Gs1 Gm3 GS2 N8d HSr. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|].
      assert ((m + 16) / 8 + n8 / 8 <= (m + 16 + n8) / 8)%Z by (Z.div_mod_to_equations; lia).
      assert ((m + 16 + n8) / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8)%Z with (2 ^ 44)%Z in *. lia. }
    assert (GU1 : (T + 4096 <= AIMGLO \/ AIMGHI <= T)%Z) by (unfold hideW in GTS; exact (proj1 GTS)).
    assert (GU2 : (T + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= T)%Z) by (unfold hideW in GTS; exact (proj2 GTS)).
    assert (GU3 : (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T)%Z) by (unfold hideW in GTsp; exact GTsp).
    pose proof GabT as GU4.
    hidehypW GU1. hidehypW GU2. hidehypW GU3. hidehypW GU4.
    assert (DF : (1 <= mx / 2 <= 8 /\ 1 <= mx - mx / 2 <= 8)%Z) by (clear - Gmx; Z.div_mod_to_equations; lia).
    assert (CB : (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37 /\ 2 ^ 32 <= c * 2 ^ 32)%Z) by (clear - Hc; split; [replace (2 ^ 37)%Z with (32 * 2 ^ 32)%Z by reflexivity; nia | nia]).
    destruct Gnf as (Gnf0 & Gnf1). destruct Gmfa as (Gmf0 & Gmf18). destruct Gpgp as (Gpg0 & Gpg1).
    pose proof (conj HSr (conj GS1 (conj GS2 (conj Gs1 (conj Gs2 (conj Gs3 (conj Hc (conj Hd (conj Em (conj AB1 (conj AB2 (conj GT1 (conj GT2 (conj SHR (conj Gm3 (conj N8d (conj DF (conj CB (conj Gnf0 (conj Gnf1 (conj Gmf0 (conj Gpg0 Gpg1)))))))))))))))))))))) as GEO.
    assert (QI : forall x : word, (AIMGLO <= U x < AIMGHI)%Z -> M34 x = memD x).
    { intros x Hx. apply QK; clear - Hx GU1 GEO; unfold hideW in GU1; lia. }
    assert (QT : forall x : word, (T <= U x < T + 2840)%Z -> M34 x = memD x).
    { intros x Hx. apply QK; clear - Hx GU2 GU4 GEO; unfold hideW in GU2, GU4; lia. }
    assert (QR : forall x : word, (spb + 2 ^ 37 <= U x < spb + 2 ^ 37 + 4096)%Z -> M34 x = memD x).
    { intros x Hx. apply QK; clear - Hx GU3 GEO; unfold hideW in GU3; lia. }
    assert (He' : (0 <= e < 2 ^ 32)%Z) by (clear - IDX0 IDX1 Hd CSP; nia).
    pose proof (conj Gpg0 Gpg1) as GEOI.
    pose proof (conj GT1 (conj GT2 (conj GS2 (conj Hc (conj DF HSr))))) as GEOT.
    pose proof (conj Gs1 (conj Gs3 (conj GS2 (conj Hc HSr)))) as GEOR.
    Ltac xqk GEO Q C :=
       eapply rd_same; [ intros x Hx; apply Q; revert Hx; clear - GEO; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                       | clear - GEO; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact C ].
    idtac "PROGRESS 4T: before dfull".
    destruct (run_dfull M34 rom r5 S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx nf mfa pgp ks b80 b88 b470 bst bcs
                F1 F2 F10 F11 F12 F13 F8 F9 F18 F19 F20 F21
                ltac:(rewrite F22; exact D22) ltac:(rewrite F23; exact D23) ltac:(rewrite F24; exact D24) ltac:(rewrite F25; exact D25)
                ltac:(rewrite F26; exact D26) ltac:(rewrite F27; exact D27)
                I_GS ltac:(split; [exact GT1 | split; [split; [exact GTS | exact GT2] | exact GT16]]) ltac:(split; [exact Gs1 | split; [exact Gs3 | exact Gs8]]) GTsp
                (conj Hc He') Gmx (conj Gnf0 Gnf1) (conj Gmf0 Gmf18) Gks Fks (conj Gpg0 Gpg1) Hret L80 L88 L470 Lst Lcs
                ltac:(eapply store_ok_mono; [exact GRK | exact HstkF]) ltac:(eapply store_ok_mono; [exact GRK | exact OkT])
                ltac:(eapply store_ok_mono; [exact GRK | exact OkRI]) ltac:(eapply store_ok_mono; [exact GRK | exact Okfa])
                ltac:(xqk GEOT QT C_mx) ltac:(xqk GEOT QT C_cnt) ltac:(xqk GEOT QT C_cs) ltac:(xqk GEOT QT C_st)
                ltac:(intros i k Hik; assert (Hi : (Z.of_nat i < mx / 2)%Z) by (rewrite <- Gks; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate);
                      eapply rd_same; [ intros x Hx; apply QT; revert Hx; clear - Hi GEOT; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                       | clear - Hi GEOT; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact (C_src i k Hik) ])
                ltac:(xqk GEOI QI C_spb) ltac:(rewrite <- Erib; xqk GEOI QI C_rib) ltac:(xqk GEOI QI C_int) ltac:(xqk GEOI QI C_gpg) ltac:(xqk GEOI QI C_pg) ltac:(xqk GEOI QI C_470)
                ltac:(xqk GEOR QR C_mu) ltac:(xqk GEOR QR C_nf) ltac:(xqk GEOR QR C_mfa) ltac:(xqk GEOR QR C_80) ltac:(xqk GEOR QR C_88))
      as (r9 & w9 & w22 & RUNF & N2 & N8 & N9 & N18 & N19 & N20 & N3 & N4 & N21 & N22 & N23 & N24 & N25 & N26 & N27).
    idtac "PROGRESS 4T: after dfull".
    exists r9, w9, w22. split.
    { (lazymatch goal with |- ?G => let G' := eval unfold fr_itemF in G in change_no_check G' end). rewrite <- EM34. eapply msteps_trans; [exact RUN34 | exact RUNF]. }
    split; [exact N2|]. split; [exact N8|]. split; [exact N9|]. split; [exact N18|]. split; [exact N19|]. split; [exact N20|]. split; [exact N21|].
    split; [rewrite N3; exact F3|]. split; [rewrite N4; exact F4|].
    split; [exact N22|]. split; [exact N23|]. split; [exact N24|]. split; [exact N25|]. split; [exact N26 | exact N27].
  Qed.
End RUNITEMF.
End FPGen.
End BoAllocFRc4T.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4Rc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc4Vc.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4Rc.BoAllocFRc4Ra OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4Rc.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Section FULLMEMC.
  Variables (mem : word -> option byte).
  Variables (S : word) (T spb c e mx nf : Z) (ks : list Z) (b80 : list byte) (w9 w22 stw : word).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c).
  #[local] Abbreviation RIz := (spb + 2 ^ 37 + 128 * c).
  #[local] Abbreviation fa := (spb + c * 2 ^ 32 + 0xE0000000).
  #[local] Abbreviation cnt' := (mx - mx / 2).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis GT : 4096 <= T /\ T + 4096 <= U S - 3584.
  Hypothesis Gspb : 0x10007fff8000 <= spb /\ spb + 2 ^ 37 + 4096 <= U S - 3584.
  Hypothesis GTsp : hideW (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T).
  Hypothesis Gc : 1 <= c <= 30.
  Hypothesis Gmx : 2 <= mx <= 16.
  Hypothesis Gnf : 0 <= nf /\ 4 * (nf + mx / 2) <= 2 ^ 29.
  Hypothesis Gks : Z.of_nat (length ks) = mx / 2.

  #[local] Abbreviation MF := (fr_fullC mem S T spb c e mx nf ks b80 w9 w22 stw).

  Lemma fullC_geo : 1 <= mx / 2 <= 8 /\ 1 <= cnt' <= 8 /\ spb + 2 ^ 32 <= fa /\ fa + 4 * nf + 4 * (mx / 2) <= spb + 2 ^ 37
                   /\ spb + 2 ^ 37 <= RIz /\ RIz + 128 <= spb + 2 ^ 37 + 4096.
  Proof using Gnf Gmx Gc.
    clear GS GT Gspb GTsp Gks.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (replace (2 ^ 37) with (32 * 2 ^ 32) by reflexivity; nia). assert (2 ^ 32 <= c * 2 ^ 32) by nia.
    assert (1 <= mx / 2 <= 8 /\ 1 <= mx - mx / 2 <= 8) by (clear - Gmx; Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma fr_fullC_outside : forall a : word,
    (U a < U S - 2720 \/ U S - 2400 <= U a) -> (U a < pc_ \/ pc_ + 4 <= U a) -> (U a < pc_ + 16 + 4 * cnt' \/ pc_ + 16 + 4 * cnt' + 4 <= U a) ->
    (U a < T + 2784 \/ T + 2792 <= U a) -> (U a < RIz \/ RIz + 8 <= U a) -> (U a < RIz + 16 \/ RIz + 24 <= U a) -> (U a < RIz + 80 \/ RIz + 88 <= U a) ->
    (U a < fa + 4 * nf \/ fa + 4 * nf + 4 * (mx / 2) <= U a) -> MF a = mem a.
  Proof using Gks Gnf Gmx Gc Gspb GT GS.
    intros a A1 A2 A3 A4 A5 A6 A7 A8. pose proof (u64_range S) as HSr. pose proof fullC_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gspb as (Gs1 & Gs2). destruct Gnf as (Gn0 & Gn1).
    assert (GSs : 2 ^ 24 <= U S /\ U S + 16 <= 2 ^ 47) by lia.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_fullC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    rewrite (fr_dtl_outside _ S GSs T c cnt' e stw ltac:(lia) Gc ltac:(lia) a ltac:(lia) A2 A3 A4).
    rewrite wbytes_outside by (rewrite length_N_to_le_bytes; wd_ulia).
    rewrite (fr_mro_outside _ S GSs) by lia.
    rewrite fr_rtac_outside by lia.
    rewrite fa_fill_outside by (rewrite ?Gks; lia).
    reflexivity.
  Qed.

  Lemma fr_fullC_foot : forall a : word, MF a <> mem a ->
    (U S - 2720 <= U a < U S - 2400) \/ (pc_ <= U a < pc_ + 4) \/ (pc_ + 16 + 4 * cnt' <= U a < pc_ + 16 + 4 * cnt' + 4) \/ (T + 2784 <= U a < T + 2792)
    \/ (RIz <= U a < RIz + 8) \/ (RIz + 16 <= U a < RIz + 24) \/ (RIz + 80 <= U a < RIz + 88) \/ (fa + 4 * nf <= U a < fa + 4 * nf + 4 * (mx / 2)).
  Proof using Gks Gnf Gmx Gc Gspb GT GS.
    intros a NE.
    destruct (decide (U S - 2720 <= U a < U S - 2400)) as [|N1]; [tauto|].
    destruct (decide (pc_ <= U a < pc_ + 4)) as [|N2]; [tauto|].
    destruct (decide (pc_ + 16 + 4 * cnt' <= U a < pc_ + 16 + 4 * cnt' + 4)) as [|N3]; [tauto|].
    destruct (decide (T + 2784 <= U a < T + 2792)) as [|N4]; [tauto|].
    destruct (decide (RIz <= U a < RIz + 8)) as [|N5]; [tauto|].
    destruct (decide (RIz + 16 <= U a < RIz + 24)) as [|N6]; [tauto|].
    destruct (decide (RIz + 80 <= U a < RIz + 88)) as [|N7]; [tauto|].
    destruct (decide (fa + 4 * nf <= U a < fa + 4 * nf + 4 * (mx / 2))) as [|N8]; [tauto|].
    exfalso. apply NE. apply fr_fullC_outside; [clear - N1; lia | clear - N2; lia | clear - N3; lia | clear - N4; lia | clear - N5; lia | clear - N6; lia | clear - N7; lia | clear - N8; lia].
  Qed.

  Lemma fr_fullC_grows : mem_grows mem MF.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_fullC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    eapply mem_grows_trans; [| apply fr_dtl_grows]. eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply fr_mro_grows].
    eapply mem_grows_trans; [| apply fr_rtac_grows]. apply fa_fill_grows.
  Qed.

  (* [comment removed for export] *)
  Lemma fr_fullC_cnt : rdn BSEGS MF (Z_to_bv 64 pc_) 4 = Some (LE4 (cnt' + 1)).
  Proof using Gnf Gmx Gc GT GS.
    pose proof fullC_geo as (G1 & G2 & _). destruct GS as (GS1 & GS2). (lazymatch goal with |- ?G => let G' := eval unfold fr_fullC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    apply fr_dtl_cnt; [lia | exact GT | exact Gc | lia].
  Qed.
  Lemma fr_fullC_slot : rdn BSEGS MF (Z_to_bv 64 (pc_ + 16 + 4 * cnt')) 4 = Some (LE4 (e / 16)).
  Proof using Gnf Gmx Gc GT GS.
    pose proof fullC_geo as (G1 & G2 & _). destruct GS as (GS1 & GS2). (lazymatch goal with |- ?G => let G' := eval unfold fr_fullC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    apply fr_dtl_slot; [lia | exact GT | exact Gc | lia].
  Qed.

  Ltac through_dtl :=
    eapply rd_same; [ intros x Hx; apply (fr_dtl_outside _ S ltac:(lia) T c cnt' e stw ltac:(lia) Gc ltac:(lia));
                                     revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; unfold hideW in GTsp; lia
                    | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].

  Lemma fr_fullC_mu : rdn BSEGS MF (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Proof using Gnf Gmx Gc GTsp Gspb GT GS.
    pose proof (u64_range S) as HSr. pose proof fullC_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gspb as (Gs1 & Gs2). destruct Gnf as (Gn0 & Gn1).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_fullC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). through_dtl. apply rdn_wbytes_hit8. unorm. lia.
  Qed.
  Lemma fr_fullC_nf : rdn BSEGS MF (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 (nf + mx / 2))).
  Proof using Gnf Gmx Gc GTsp Gspb GT GS.
    pose proof (u64_range S) as HSr. pose proof fullC_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gspb as (Gs1 & Gs2). destruct Gnf as (Gn0 & Gn1).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_fullC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). through_dtl.
    rewrite rdn_wbytes_out by (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia).
    eapply rd_same; [ intros x Hx; apply (fr_mro_outside _ S ltac:(lia)); revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].
    apply fr_rtac_nf. lia.
  Qed.
  Lemma fr_fullC_fa : forall i k, nth_error ks i = Some k -> rdn BSEGS MF (Z_to_bv 64 (fa + 4 * nf + 4 * Z.of_nat i)) 4 = Some (LE4 k).
  Proof using Gks Gnf Gmx Gc GTsp Gspb GT GS.
    intros i k Hik. pose proof (u64_range S) as HSr. pose proof fullC_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct GS as (GS1 & GS2). destruct GT as (GT1 & GT2). destruct Gspb as (Gs1 & Gs2). destruct Gnf as (Gn0 & Gn1).
    assert (Hi : Z.of_nat i < mx / 2) by (rewrite <- Gks; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate).
    (lazymatch goal with |- ?G => let G' := eval unfold fr_fullC in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). through_dtl.
    rewrite rdn_wbytes_out by (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia).
    eapply rd_same; [ intros x Hx; apply (fr_mro_outside _ S ltac:(lia)); revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].
    eapply rd_same; [ intros x Hx; apply fr_rtac_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                    | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | ].
    apply fa_fill_cell; [lia | rewrite Gks; lia | exact Hik].
  Qed.
End FULLMEMC.
End FPGen.
End BoAllocFRc4Vc.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRc4W.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFMem BoAllocFRc3T4 BoAllocFRc3U4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R BoAllocFRc4V BoAllocFRc4T.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Section ITEMFMEM.
  Variables (memD : word -> option byte) (S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 : word) (m ab n8 T : Z) (h1 h2 h3 : byte)
            (j0 j1 : word) (spb c e mx nf : Z) (ks : list Z) (b80 : list byte) (w9 w22 stw : word).
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gm : 0x10007fff8000 <= ab /\ (ab = m \/ ab + 16 <= m) /\ m + 16 + n8 <= U S - 3584 /\ m mod 16 = 0.
  Hypothesis Gn8 : 8 <= n8 /\ n8 mod 8 = 0 /\ n8 <= 2 ^ 40.
  Hypothesis GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584).
  Hypothesis GabT : m + 16 + n8 <= T \/ T + 4096 <= ab.
  Hypothesis Gspb : 0x10007fff8000 <= spb /\ spb + 2 ^ 37 + 4096 <= U S - 3584.
  Hypothesis GTsp : hideW (T + 4096 <= spb \/ spb + 2 ^ 37 + 4096 <= T).
  Hypothesis Gc : 1 <= c <= 30.
  Hypothesis Gmx : 2 <= mx <= 16.
  Hypothesis Gnf : 0 <= nf /\ 4 * (nf + mx / 2) <= 2 ^ 29.
  Hypothesis Gks : Z.of_nat (length ks) = mx / 2.

  #[local] Abbreviation MF := (fr_itemF memD S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 m ab n8 T h1 h2 h3 j0 j1 spb c e mx nf ks b80 w9 w22 stw).
  #[local] Abbreviation pc_ := (T + 208 + 80 * c).
  #[local] Abbreviation RIz := (spb + 2 ^ 37 + 128 * c).
  #[local] Abbreviation fa := (spb + c * 2 ^ 32 + 0xE0000000).
  #[local] Abbreviation shlo := (0x7fff8000 + (m + 16) / 8).

  Lemma fr_itemF_foot : forall a : word, MF a <> memD a ->
    (U S - 2720 <= U a < U S - 2400) \/ (m <= U a < m + 4) \/ (ab <> m /\ ab <= U a < ab + 8) \/ (shlo <= U a < shlo + n8 / 8)
    \/ (T + 2840 <= U a < T + 2856)
    \/ (pc_ <= U a < pc_ + 4) \/ (pc_ + 16 + 4 * (mx - mx / 2) <= U a < pc_ + 16 + 4 * (mx - mx / 2) + 4) \/ (T + 2784 <= U a < T + 2792)
    \/ (RIz <= U a < RIz + 8) \/ (RIz + 16 <= U a < RIz + 24) \/ (RIz + 80 <= U a < RIz + 88) \/ (fa + 4 * nf <= U a < fa + 4 * nf + 4 * (mx / 2)).
  Proof using GS Gm Gn8 GT GabT Gspb GTsp Gc Gmx Gnf Gks.
    intros a NE. unfold fr_itemF in NE.
    destruct (decide (fr_item34 memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 j0 j1 a = memD a)) as [E | N].
    - rewrite <- E in NE.
      pose proof (fr_full_foot _ S ra0 s0v s1v s2v s3v s4v x21 x22 x23 x24 x25 x26 x27 T spb c e mx nf ks b80 w9 w22 stw GS
                    ltac:(destruct GT as (X1 & _ & X2); split; assumption) Gspb Gc Gmx Gnf Gks a NE) as F.
      clear - F. tauto.
    - pose proof (fr_item34_foot memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 j0 j1 GS Gm Gn8 GT GabT a N) as F.
      clear - F. destruct F as [F|[F|[F|[F|F]]]]; [left; lia | tauto | tauto | tauto | tauto].
  Qed.

  Lemma fr_itemF_grows : mem_grows memD MF.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold fr_itemF in G in change_no_check G' end). eapply mem_grows_trans; [apply fr_item34_grows | apply fr_full_grows]. Qed.

  Lemma fr_itemF_shadow : forall i, 0 <= i < n8 / 8 -> MF (Z_to_bv 64 (shlo + i)) = Some (Z_to_bv 8 0xfa).
  Proof using GS Gm Gn8 GT GabT Gspb GTsp Gc Gmx Gnf Gks.
    intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold fr_itemF in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. destruct GS as (GS1 & GS2). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4). destruct GT as (GT1 & (GTS & GT2)).
    destruct Gspb as (Gs1 & Gs2). destruct Gn8 as (N1 & N2 & N3).
    assert (SHR : 0x7fff8000 + 0x10007fff8000 / 8 <= shlo /\ shlo + n8 / 8 <= 0x7fff8000 + 2 ^ 44).
    { clear - Gm1 Gm2 Gm3 GS2 N1 HSr. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|].
      assert ((m + 16) / 8 + n8 / 8 <= (m + 16 + n8) / 8) by (Z.div_mod_to_equations; lia).
      assert ((m + 16 + n8) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with (2 ^ 44) in *. lia. }
    assert (TSB : T + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= T) by (unfold hideW in GTS; exact (proj2 GTS)).
    pose proof (full_geo spb c mx nf Gc Gmx Gnf) as (G1 & G2 & G3 & G4 & G5 & G6).
    rewrite fr_full_outside; [apply (fr_item34_shadow memD S ra0 s0v s1v s2v s3v s4v x21 m ab n8 T h1 h2 h3 j0 j1); [split; assumption | split; [assumption | split; [assumption | split; assumption]] | split; [assumption | split; assumption] | split; [assumption | split; assumption] | assumption | exact Hi] | | | | | | | | | | | | | | |];
      try assumption; try (split; assumption);
      rewrite u64_lit by (clear - Hi SHR; lia); clear - Hi SHR TSB HSr GS1 GS2 GT1 GT2 Gs1 Gs2 G1 G2 G3 G4 G5 G6 Gc Gnf; lia.
  Qed.
End ITEMFMEM.
End FPGen.
End BoAllocFRc4W.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK6c.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3T4 BoAllocFRc3U4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R BoAllocFRc4V BoAllocFRc4T BoAllocFRc4W.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma down8_up8K6 : forall n, AsRtRegion.down8 (n + 7) = up8 n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold AsRtRegion.down8, AsAinvOpsPf3d.AsAinvFreeS.up8 in G in change_no_check G' end). lia. Qed.
Lemma rz_16_32_6 : forall r, r mod 16 = 0 -> 16 <= r -> r = 16 \/ 32 <= r.
Proof. intros. lia. Qed.
Lemma mod16_8_6 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros. lia. Qed.
Lemma sh_range_in6 : forall lo len a n8, lo mod 8 = 0 -> len mod 8 = 0 -> a mod 8 = 0 -> n8 mod 8 = 0 -> lo <= a -> a + n8 <= lo + len -> 0 <= n8 ->
  lo / 8 <= a / 8 /\ a / 8 + n8 / 8 <= lo / 8 + len / 8 /\ 8 * (a / 8) = a /\ 8 * (n8 / 8) = n8.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section K6C.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis HTP : TP = ia_tp both_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  Theorem rc_item_full_room_pf : rc_item_stmt bt FXOK arm_prim_full_room.
  Proof using HTP RCF RCC CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_item_stmt in G in change_no_check G' end).
    intros fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest HFX HH MW W RX EGQ ((HP & FULL) & FAR) XSUB XQ XOBJ QDEF
           R1 RET R2 R10 R11 R4 CCB S16 Slo Shi SOK _.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    pose proof RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct RCC as (CELL_rib & CELL_magic & G_tsdp). destruct RCF as (CELL_int & CELL_gpg & CELL_pgv & CELL_470).
    unfold free_cells_nb in CELLNB.
    (* [comment removed for export] *)
    assert (Hq : In (m, n) (quar st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). apply in_flat_map. exists (BATCH ba ((m, n) :: its)). split; [apply in_app_iff; right; rewrite EGQ; left; reflexivity | left; reflexivity]. }
    assert (Hb : In (BATCH ba ((m, n) :: its)) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    pose proof (cinit_of_batch bt st Lc FF qt qg _ W Hb) as CINIT.
    pose proof (quar_chunk bt st Lc FF W m n Hq HP) as G. cbn zeta in G.
    unfold fa_room in FAR. remember (blk_class n) as c eqn:Ec. remember (prim_alloc_beg (m + 16) n) as ab eqn:Eab0.
    destruct G as (Hc & CV & INQ & G4 & G5 & G6).
    destruct (carved_range bt st Lc FF W c ab Hc CV) as (C1 & C2 & C3 & C4 & C5).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    pose proof (csize_pos c Hc) as ((CS1 & CS2) & CS16).
    (* [comment removed for export] *)
    pose proof W as (_ & WC & _). destruct (WC c Hc) as (CLEN & _ & CKS). clear WC.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & MFA18 & _). clear WR1. unfold KFAMAP in MFA18.
    set (mx := cache_max c) in *.
    assert (P_Gmx : 2 <= mx <= 16) by ((lazymatch goal with |- ?G => let G' := eval unfold mx, cache_max, cache_hint in G in change_no_check G' end); clear; lia).
    assert (DF : 1 <= mx / 2 <= 8 /\ 1 <= mx - mx / 2 <= 8) by (clear - P_Gmx; Z.div_mod_to_equations; lia).
    assert (LEN : Z.of_nat (length (a_cache st c)) = mx) by (clear - FULL CLEN; lia).
    set (ks := skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2)) (a_cache st c)).
    assert (LKS : Z.of_nat (length ks) = mx / 2) by ((lazymatch goal with |- ?G => let G' := eval unfold ks in G in change_no_check G' end); rewrite length_skipn; clear - LEN DF; lia).
    assert (FKS : Forall (fun k => 0 <= k < 2 ^ 31) ks).
    { apply Forall_forall. intros k0 Hk. assert (Hin : In k0 (a_cache st c)) by (unfold ks in Hk; rewrite <- (firstn_skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2)) (a_cache st c)); apply in_or_app; right; exact Hk).
      destruct (CKS k0 Hin) as (Kr & CVk). destruct (carved_range bt st Lc FF W c _ Hc CVk) as (D1 & D2 & _).
      pose proof (region_facts bt st Lc FF W c Hc) as RF0. cbn zeta in RF0. destruct RF0 as (_ & E2 & E3 & _).
      unfold chunk_of_compact, fa_beg, region_beg, KREGION, KFAOFF in *. clear - D1 D2 E2 E3 Kr CS1. lia. }
    set (st1 := op_drain_top st c (mx / 2)).
    assert (W1 : WFq bt st1 Lc FF qt qg) by (apply (OPS_WFq_drain_top_pf bt st Lc FF c (mx / 2) qt qg W Hc); [clear - LEN DF; lia | exact FAR]).
    assert (GQ1 : a_gq st1 = a_gq st) by reflexivity.
    assert (CA1 : a_cache st1 c = firstn (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2)) (a_cache st c)).
    { (lazymatch goal with |- ?G => let G' := eval unfold st1, op_drain_top in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache set_reg] in G in change_no_check G' end). apply fupdZ_same. }
    assert (LEN1 : Z.of_nat (length (a_cache st1 c)) = mx - mx / 2) by (rewrite CA1, length_firstn; clear - LEN DF; lia).
    assert (NXF : forall z, foot_drain_top bt st c (mx / 2) z -> ~ X z).
    { intros z Hf Hx. exact (foot_drain_top_not_XB bt st Lc FF qt qg c (mx / 2) z W Hc ltac:(clear - DF; lia) FAR Hf (XSUB z Hx)). }
    set (nf := Z.of_nat (length (r_free (a_reg st c)))) in *.
    assert (NF0 : 0 <= nf) by ((lazymatch goal with |- ?G => let G' := eval unfold nf in G in change_no_check G' end); lia).
    destruct (quar_item_range bt st Lc FF W m n Hq) as (QR1 & QR2 & QR3).
    pose proof (rz_mod16 n) as RM. pose proof (rz_range n) as RZ.
    assert (N64 : n <= 64512) by (apply (is_primary_iff n ltac:(lia)); exact HP).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SPC.
    destruct CV as (j & Hj0 & Hj1 & Eab). pose proof Eab as Eab'. unfold chunk_addr, region_beg, KREGION in Eab'.
    assert (CVc : carved bt st c ab) by (exists j; repeat split; assumption).
    destruct (up8_facts n ltac:(lia)) as (U8a & U8b & U8c & U8d).
    assert (T16 : T mod 16 = 0) by (clear - TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    rewrite BT_ia in GTI, GCI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI.
    unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    unfold fa_beg, reginfo, region_beg, KREGION, KFAOFF, KSPACE, PG, AS_HEAPLO, AS_LO, NMAX, PTRHI in *.
    remember (csize c) as cs eqn:Ecs. set (d := m - SBEG - c * 2 ^ 32).
    assert (Em : m = ab + rz n - 16) by (clear - G4; lia).
    assert (M16 : m mod 16 = 0) by (clear - Em C5 RM; Z.div_mod_to_equations; lia).
    assert (Ed : d = j * cs + (rz n - 16)) by ((lazymatch goal with |- ?G => let G' := eval unfold d in G in change_no_check G' end); clear - Em Eab'; lia).
    assert (Hrz : 0 <= rz n - 16 < cs) by (clear - G5 G4 QR3 RZ; lia).
    assert (Eidx : d / cs = j) by (symmetry; apply (Z.div_unique d cs j (rz n - 16)); [left; exact Hrz | clear - Ed; lia]).
    assert (JJ : (j + 1) * cs = j * cs + cs) by ring.
    assert (JJ0 : 0 <= j * cs) by (clear - Hj0 CS1; nia).
    assert (Hd32 : 0 <= d < 2 ^ 32) by (clear - Ed Hrz JJ JJ0 Hj1 Q3 Q2; lia).
    assert (Eabm : SBEG + c * 2 ^ 32 + d / cs * cs = ab) by (rewrite Eidx; clear - Eab'; lia).
    assert (P8 : (m + 16) mod 8 = 0) by (clear - M16; Z.div_mod_to_equations; lia).
    assert (N8le : m + 16 + up8 n <= ab + cs).
    { apply (up8_le (m + 16) n (ab + cs) P8); [clear - C5 CS16; Z.div_mod_to_equations; lia | exact G5]. }
    destruct (sh_up8 (m + 16) n P8 ltac:(lia)) as [SHhi SHlo]. unfold SB in SHhi, SHlo.
    destruct (sh_range_in6 (SBEG + c * 2 ^ 32) (r_mapped_user (a_reg st c)) (m + 16) (up8 n))
      as (SR1 & SR2 & SR3 & SR4);
      [clear - Q11; Z.div_mod_to_equations; lia | clear - Q13; Z.div_mod_to_equations; lia | exact P8 | exact U8d
      | clear - Em C1 RZ; lia | clear - N8le C2 Q3; lia | clear - U8b; lia |].
    (* [comment removed for export] *)
    pose proof RP as (Rc & Ri & Rt & Rr & _ & _ & _ & Rh & _ & _ & _ & Rs & R13 & R14 & _ & _ & Csb & _ & SHM0).
    first [pose proof (proj1 SHM0) as SHM | pose proof SHM0 as SHM]. clear SHM0.          (* [comment removed for export] *)
    rewrite BT_ia in Csb. cbn [ia_rtc_sb both_addrs] in Csb.
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & Tback & _).
    destruct (TPC c Hc) as (PCcnt & PCmax & PCcs & PCks). rewrite CINIT in PCmax.
    destruct (Rr c Hc) as [(RIm0 & _ & RInf & RImfa & _ & _ & RImu & _ & _ & RIW) (_ & FAW & RWR)]. fold nf in RInf.
    destruct Rh as [_ RHQ]. destruct (RHQ m n Hq) as [(Hst & (b1 & Hb1 & H11) & Hnhi & Hnlo & _ & _ & HMAG) _].
    destruct R14 as (B1 & B2 & _ & _ & BSH & _).
    destruct (BSH c Hc) as [BSHu _].
    rewrite BT_segs in *.
    unfold T_PC, PC_SZ in *. unfold fa_beg, reginfo, region_beg, KREGION, KFAOFF, KSPACE, sh_lo, SB in *.
    replace (m + 16 - 16) with m in * by lia. replace (m + 16 - 15) with (m + 1) in * by lia.
    replace (m + 16 - 14) with (m + 2) in * by lia. replace (m + 16 - 12) with (m + 4) in * by lia.
    assert (Hb1r : 0 <= b1 < 256) by (destruct Hb1; subst; lia).
    (* [comment removed for export] *)
    assert (XZ : forall z, X z -> (0x10ab58 + 888 <= z < 0x10ab58 + 920) \/ SBEG <= z < SBEG + 2 ^ 37).
    { intros z Hz. destruct (XB_zone bt st Lc FF W z (XSUB z Hz)) as [Q | Q]; [left; unfold qhdr, IB in Q; rewrite BT_ia in Q; exact Q | right; exact Q]. }
    assert (XCH : forall z, ab <= z < ab + cs -> ~ X z).
    { intros z Hz Hx. rewrite Ecs in Hz. exact (XB_not_owned bt st Lc FF W z c ab (XSUB z Hx) Hc CVc (or_introl INQ) Hz). }
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHC : forall z, CTX <= z < CTX + 65536 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GC0 GCC CR; lia|]. apply (rep_nolazy_tctx bt st Lc FF M0 mdl W RP). exact Hz. }
    assert (NHR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 CR; lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). exact Hz. }
    assert (NHF : forall z, SBEG + c * 2 ^ 32 + 3758096384 <= z < SBEG + c * 2 ^ 32 + 3758096384 + r_mapped_fa (a_reg st c) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 Q5 Q6 CR Hc; lia|]. apply (rep_nolazy_fa bt st Lc FF M0 mdl W RP c z Hc).
      (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). exact Hz. }
    assert (NHch : forall z, ab <= z < ab + cs -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz C3 C4 SB0 SB1 CR; lia|]. rewrite Ecs in Hz. exact (rep_nolazy_chunk bt st Lc FF M0 mdl W RP c ab z Hc CVc Hz). }
    assert (NHsh : forall z, 0x7fff8000 + (m + 16) / 8 <= z < 0x7fff8000 + (m + 16) / 8 + up8 n / 8 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. apply BSHu. clear - Hz SR1 SR2. lia. }
    (* [comment removed for export] *)
    pose (memD := mrestrict Hd M).
    Ltac cimg XZ SBH NHs := intros z Hz; split; [ intros Hx; destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q; lia | clear - Hz Q SBH; lia]
                                                 | apply NHs; [clear - Hz; lia | right; clear - Hz; lia] ].
    Ltac czl := first [ reflexivity | (vm_compute; discriminate) | (vm_compute; reflexivity) ].
    Ltac konstK Hd M M0 X Rc EQ0 XZ SBH NHs C := apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc C) EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); cimg XZ SBH NHs].
    assert (K_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELLNB.
    assert (K_rib : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (SBEG + 2 ^ 37)))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_rib.
    assert (K_magc : rdn BSEGS memD (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_magic.
    assert (K_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gsh.
    assert (K_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { apply (cellX Hd M M0 X _ _ _ Csb EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); cimg XZ SBH NHs]. }
    assert (K_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gmb.
    assert (K_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_mb.
    assert (K_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gme.
    assert (K_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_me.
    assert (K_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_ghe.
    assert (K_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_he.
    assert (K_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_grm.
    assert (K_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_rm.
    assert (K_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 CPM]).
    { rewrite <- w2b1 by (clear - Gc8; lia). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_cpm. }
    assert (K_kif : rdn BSEGS memD (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]).
    { rewrite <- w2b1 by (clear; lia). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_kif. }
    assert (K_key : rdn BSEGS memD (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (clear - HSr; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_key. }
    subst TP. cbn [ia_tp both_addrs] in CELL_tsdp, Gc9, Gc10.
    assert (Utp : U (getr R 4) = 0x641380) by (rewrite R4; vm_compute; reflexivity).
    assert (K_tsdp : rdn BSEGS memD (at_ (getr R 4) (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ (getr R 4) (-88)) with (Z_to_bv 64 (0x641380 - 88) : word) by (clear - Utp; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; unorm; reflexivity).
      konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_tsdp. }
    assert (K_tctx : rdn BSEGS memD (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc CELL_tctx) EQ0); [clear - Gc1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q G_tsdp; lia | clear - Hz Q SBH Gc2; lia].
      - apply NHs; [clear - Hz Gc1 Gc2; lia | right; clear - Hz Gc1 Gc2; lia]. }
    assert (K_thr : rdn BSEGS memD (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152) : word) by (clear - GC0 GCC CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (cellX Hd M M0 X _ _ _ Tback EQ0); [clear - GC0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GCI; lia | clear - Hz Q SPC; lia].
      - apply NHC. clear - Hz. lia. }
    assert (K_au : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 (r_mapped_user (a_reg st c))))).
    { apply (cellX Hd M M0 X _ _ _ RImu EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q SBH Hc; lia | clear - Hz Q Hc; lia].
      - apply NHR. clear - Hz Hc. lia. }
    assert (K_mx : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c + 4)) 4 = Some (LE4 (cache_max c))).
    { apply (cellX Hd M M0 X _ _ _ PCmax EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI Hc; lia | clear - Hz Q SPT Hc; lia].
      - apply NHT. clear - Hz Hc. lia. }
    assert (K_cnt : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c)) 4 = Some (LE4 (Z.of_nat (length (a_cache st c))))).
    { apply (cellX Hd M M0 X _ _ _ PCcnt EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI Hc; lia | clear - Hz Q SPT Hc; lia].
      - apply NHT. clear - Hz Hc. lia. }
    assert (K_cntF : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c)) 4 = Some (LE4 mx)) by (rewrite <- LEN; exact K_cnt).
    assert (K_int : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff)) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_int.
    assert (K_gpg : rdn BSEGS memD (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 0x19dc60))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gpg.
    assert (K_pgv : rdn BSEGS memD (Z_to_bv 64 0x19dc60) 8 = Some (LE8 (Z_to_bv 64 4096))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_pgv.
    assert (K_470 : rdn BSEGS memD (Z_to_bv 64 0x10468) 8 = Some (LE8 (Z_to_bv 64 0xafffff00000fffff))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_470.
    assert (OFFT : forall z, T <= z < T + 4096 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHT; exact Hz]. intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI; lia | clear - Hz Q SPT; lia]. }
    assert (OFFR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHR; exact Hz]. intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q SBH; lia | clear - Hz Q; lia]. }
    assert (OFFF : forall z, SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf <= z < SBEG + c * 2 ^ 32 + 3758096384 + 4 * (nf + mx / 2) -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHF; clear - Hz FAR NF0; lia]. apply NXF. (lazymatch goal with |- ?G => let G' := eval unfold foot_drain_top, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). fold nf. do 4 right; left. exact Hz. }
    assert (K_src : forall i k0, nth_error ks i = Some k0 -> rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i)) 4 = Some (LE4 k0)).
    { intros i k0 Hik. assert (Hi : Z.of_nat i < mx / 2) by (rewrite <- LKS; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate).
      unfold ks in Hik. rewrite nth_error_skipn in Hik. specialize (PCks _ _ Hik).
      replace (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i) with (T + 208 + 80 * c + 16 + 4 * Z.of_nat (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2) + i))
        by (rewrite Nat2Z.inj_add, Z2Nat.id by (clear - LEN DF; lia); rewrite LEN; clear; lia).
      apply (cellX Hd M M0 X _ _ _ PCks EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR LEN Hi Hc DF P_Gmx; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz LEN Hi Hc DF P_Gmx. lia. }
    assert (K_mu : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { apply (cellX Hd M M0 X _ _ _ RIm0 EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz Hc. lia. }
    assert (K_nf : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 16)) 8 = Some (LE8 (Z_to_bv 64 nf))).
    { apply (cellX Hd M M0 X _ _ _ RInf EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz Hc. lia. }
    assert (K_mfa : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 24)) 8 = Some (LE8 (Z_to_bv 64 (r_mapped_fa (a_reg st c))))).
    { apply (cellX Hd M M0 X _ _ _ RImfa EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz Hc. lia. }
    assert (RDEF : forall i, SBEG + 2 ^ 37 + 128 * c <= i < SBEG + 2 ^ 37 + 128 * c + 128 -> memD (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHR; clear - Hi Hc; lia). apply GR0. apply (writableZ_def M0 _ _ _ RIW). exact Hi. }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 80)) 8) as (b80 & C80 & L80);
      [intros i Hi; apply RDEF; clear - Hi SB0 SB1 CR Hc; revert Hi; unorm; intros Hi; lia | clear - SB0 SB1 CR Hc; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 88)) 8) as (b88 & C88 & L88);
      [intros i Hi; apply RDEF; clear - Hi SB0 SB1 CR Hc; revert Hi; unorm; intros Hi; lia | clear - SB0 SB1 CR Hc; wd_ulia |].
    assert (K_magic : ab <> m -> rdn BSEGS memD (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))).
    { intros NE. pose proof (rz_16_32_6 (rz n) RM ltac:(clear - RZ; lia)) as RZC. destruct (HMAG ltac:(clear - NE Em RZC; lia)) as [MG _]. replace (m + 16 - rz n) with ab in MG by (clear - Em; lia).
      apply (cellX Hd M M0 X _ _ _ MG EQ0); [clear - C3 SB0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR CS1; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [apply XCH | apply NHch]; clear - Hz CS1; lia. }
    assert (OFFm : forall z, m <= z < m + 8 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [apply XCH | apply NHch]; clear - Hz Em RZ G5 QR3; lia. }
    assert (Kh0 : rdn BSEGS memD (Z_to_bv 64 m) 1 = Some [Z_to_bv 8 3]).
    { rewrite <- w2b1 by (clear; lia). apply (cellX Hd M M0 X _ _ _ Hst EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (Kh1 : rdn BSEGS memD (Z_to_bv 64 (m + 1)) 1 = Some [Z_to_bv 8 b1]).
    { rewrite <- w2b1 by (clear - Hb1r; lia). apply (cellX Hd M M0 X _ _ _ H11 EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (Kh2 : rdn BSEGS memD (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))).
    { apply (cellX Hd M M0 X _ _ _ Hnhi EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (K_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32))).
    { apply (cellX Hd M M0 X _ _ _ Hnlo EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    set (h2 := Z_to_bv 8 (U (Z_to_bv 64 (n / 2 ^ 32)))). set (h3 := Z_to_bv 8 (Z.shiftr (U (Z_to_bv 64 (n / 2 ^ 32))) 8)).
    assert (Mrng : 0 <= m /\ m + 16 < 2 ^ 64) by (clear - C3 SB0 Em RZ C4 SB1 CR Hrz; lia).
    assert (K_hdr : rdn BSEGS memD (Z_to_bv 64 m) 4 = Some [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3]).
    { change 4%nat with (1 + (1 + 2))%nat.
      apply (rdn_cat BSEGS memD _ 1 3 [Z_to_bv 8 3]); [exact Kh0 | | clear - Mrng; wd_ulia].
      replace (at_ (Z_to_bv 64 m) (Z.of_nat 1)) with (Z_to_bv 64 (m + 1)) by (clear - Mrng; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (rdn_cat BSEGS memD _ 1 2 [Z_to_bv 8 b1]); [exact Kh1 | | clear - Mrng; wd_ulia].
      replace (at_ (Z_to_bv 64 (m + 1)) (Z.of_nat 1)) with (Z_to_bv 64 (m + 2)) by (clear - Mrng; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      exact Kh2. }
    (* [comment removed for export] *)
    assert (TDEF : forall i, T <= i < T + 4096 -> memD (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hi). apply GR0. apply (writableZ_def M0 _ _ _ TW). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hi. }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2840)) 8) as (bf0 & Cf0 & Lf0);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2848)) 8) as (bf1 & Cf1 & Lf1);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2784)) 8) as (bst & Cst & Lst);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c + 8)) 8) as (bcs & Ccs & Lcs);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR Hc; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR Hc; wd_ulia |].
    (* [comment removed for export] *)
    assert (K_cache : rdn BSEGS memD (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + 208)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite rdn_mrestrict; [exact CCB | clear - HSr Slo Shi CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      rewrite at_u by (clear - HSr Slo Shi CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo Shi CR; lia | apply NHs; [clear - Hz HSr Slo Shi CR; lia | left; clear - Hz Slo; lia]]. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2512)) 112 = true).
    { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (SOKstkF : store_ok BSEGS memD (at_ S (-2720)) 320 = true).
    { replace (at_ S (-2720)) with (Z_to_bv 64 (U S - 2720) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (SOKRI : store_ok BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 128 = true).
    { apply (sokX Hd M M0 _ _ _ _ RIW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - SB1 CR Hc; lia | clear - SB0 Hc; lia |].
      intros z Hz. apply NHR. clear - Hz Hc. cbn in Hz. lia. }
    assert (SOKfa : store_ok BSEGS memD (Z_to_bv 64 (SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf)) (4 * length ks) = true).
    { apply (sokX Hd M M0 _ _ _ _ FAW GR0); [clear - NF0; lia | clear - LKS FAR; lia | clear - SB1 Q5 Q6 CR; lia | clear - SB0 NF0 Hc; lia |].
      intros z Hz. apply NHF. clear - Hz LKS FAR NF0. lia. }
    assert (RWlo : SBEG + c * 2 ^ 32 <= ab /\ ab + cs <= SBEG + c * 2 ^ 32 + r_mapped_user (a_reg st c) /\ SBEG + c * 2 ^ 32 + r_mapped_user (a_reg st c) < 2 ^ 64).
    { clear - C1 C2 Q3 Q2 SB1 CR Hc. lia. }
    assert (SOKhdr : store_ok BSEGS memD (Z_to_bv 64 m) 4 = true).
    { apply (sokX Hd M M0 _ _ m 4 RWR GR0); [clear - RWlo Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - RWlo Em G5 QR3; lia | clear - RWlo; lia | clear - Mrng; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (SOKab : ab <> m -> store_ok BSEGS memD (Z_to_bv 64 ab) 8 = true).
    { intros NE. apply (sokX Hd M M0 _ _ ab 8 RWR GR0); [clear - RWlo; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - RWlo CS1; lia | clear - RWlo; lia | clear - C3 SB0; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHch. clear - Hz CS1. lia. }
    assert (SHB : 0x2008fff7000 <= 0x7fff8000 + (m + 16) / 8 /\ 0x7fff8000 + (m + 16) / 8 + up8 n / 8 <= 0x10007fff8000).
    { clear - SR3 SR4 Em RZ C3 SBH N8le C4 SB1 CR. lia. }
    assert (SOKsh : store_ok BSEGS memD (Z_to_bv 64 (AsRtPoison.shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (up8 n / 8)) = true).
    { replace (AsRtPoison.shad (Z_to_bv 64 (m + 16))) with (0x7fff8000 + (m + 16) / 8) by (clear - Mrng; (lazymatch goal with |- ?G => let G' := eval unfold AsRtPoison.shad in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - SHB; lia | rewrite Z2Nat.id by (clear - SR4 U8b; lia); clear - SHB; lia |].
      rewrite Z2Nat.id by (clear - SR4 U8b; lia). intros z Hz. split; [| apply NHsh; exact Hz].
      apply GR0. apply SHM. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_GAPLO, AS_LO, AS_HEAPLO in G in change_no_check G' end). right. clear - Hz SHB. lia. }
    unfold PG in TW.
    assert (SOKT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd M M0 _ _ T _ TW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    (* [comment removed for export] *)
    subst cs.
    set (hdr := [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3]).
    pose proof (bytes_le_to_Z_bound hdr) as Bhv. cbn [length hdr] in Bhv. pose proof (bytes_le_to_Z_nonneg hdr) as Bhv0.
    assert (P_hv : bytes_le_to_Z [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3] = U (Z_to_bv 64 (bytes_le_to_Z hdr))) by (clear - Bhv Bhv0; unorm; reflexivity).
    assert (P_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - Slo Shi CR; lia).
    assert (P_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 < 2 ^ 47) by (clear - SBH SB1 CR; lia).
    assert (P_Gm : m = SBEG + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30) by (unfold d in *; clear - Hd32 Hc; lia).
    assert (P_Gm2 : m + 16 + up8 n <= U S - 3584 /\ m mod 16 = 0) by (split; [clear - N8le C4 SB1 Slo; lia | exact M16]).
    assert (P_Gab : SBEG + c * 2 ^ 32 + d / csize c * csize c = m \/ SBEG + c * 2 ^ 32 + d / csize c * csize c + 16 <= m).
    { rewrite Eabm. pose proof (rz_16_32_6 (rz n) RM ltac:(clear - RZ; lia)) as RZC. clear - RZC Em. lia. }
    assert (P_Gab8 : (SBEG + c * 2 ^ 32 + d / csize c * csize c) mod 8 = 0) by (rewrite Eabm; apply mod16_8_6; exact C5).
    assert (P_Grib : AIMGHI <= SBEG + 2 ^ 37 /\ SBEG + 2 ^ 37 + 4096 <= U S - 3584) by (clear - SBH SB1 Slo; lia).
    assert (P_Gau : (d / csize c + 1) * csize c <= r_mapped_user (a_reg st c) /\ r_mapped_user (a_reg st c) < 2 ^ 64) by (rewrite Eidx; clear - Hj1 Q3 RWlo SB0 Hc; lia).
    assert (P_Gn : 1 <= n <= 2 ^ 28) by (clear - QR3 N64; lia).
    assert (P_Gn8 : AsRtRegion.down8 (n + 7) = up8 n /\ n <= up8 n <= n + 7 /\ up8 n mod 8 = 0 /\ 8 <= up8 n) by (split; [apply down8_up8K6 | clear - U8a U8b U8c U8d; lia]).
    assert (P_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0).
    { split; [exact GT4|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; lia | clear - GTC Slo; lia] | exact T16]. }
    assert (P_GabT : m + 16 + up8 n <= T \/ T + 4096 <= SBEG + c * 2 ^ 32 + d / csize c * csize c) by (rewrite Eabm; clear - SPT N8le C3 C4; lia).
    assert (P_Gctx : 1 <= CTX /\ CTX + 4096 <= U S - 3584) by (clear - GC0 GCC Slo; lia).
    assert (P_Gctxm : CTX + 4096 <= SBEG + c * 2 ^ 32 + d / csize c * csize c \/ m + 16 + up8 n <= CTX) by (rewrite Eabm; clear - SPC N8le C3 C4; lia).
    assert (P_Gctxs : CTX + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX) by (clear - GCB; lia).
    assert (P_Gtp : AIMGLO + 88 <= U (getr R 4) /\ U (getr R 4) + 8 <= AIMGHI) by (rewrite Utp; clear; lia).
    assert (P_Gtsdp : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (clear - Gc1 Gc2; wd_ulia).
    assert (P_Gspb2 : SBEG + 2 ^ 37 + 4096 <= U S - 3584 /\ SBEG mod 8 = 0) by (split; [clear - SB1 Slo; lia | clear - SB16; Z.div_mod_to_equations; lia]).
    assert (P_GTsp : hideW (T + 4096 <= SBEG \/ SBEG + 2 ^ 37 + 4096 <= T)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact SPT).
    assert (P_Gnf : 0 <= nf /\ 4 * (nf + mx / 2) <= r_mapped_fa (a_reg st c)) by (split; [exact NF0 | exact FAR]).
    assert (P_cpm1 : U (Z_to_bv 8 CPM) <> 0) by (clear - Gc8; rewrite (Z_to_bv_small 8 CPM ltac:(change (bv_modulus 8) with 256; lia)); lia).
    assert (P_magic : SBEG + c * 2 ^ 32 + d / csize c * csize c <> m -> rdn BSEGS memD (Z_to_bv 64 (SBEG + c * 2 ^ 32 + d / csize c * csize c)) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))) by (rewrite Eabm; exact K_magic).
    assert (P_okab : SBEG + c * 2 ^ 32 + d / csize c * csize c <> m -> store_ok BSEGS memD (Z_to_bv 64 (SBEG + c * 2 ^ 32 + d / csize c * csize c)) 8 = true) by (rewrite Eabm; exact SOKab).
    (* [comment removed for export] *)
    destruct (rc_item_full_run memD (seg_rom BSEGS) R S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 4) (Z_to_bv 64 TSDP)
                m SBEG c d (SBEG + 2 ^ 37) (r_mapped_user (a_reg st c)) n (up8 n) T CTX
                (Z_to_bv 8 b1) h2 h3 (Z_to_bv 64 (bytes_le_to_Z hdr)) (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND) bf0 bf1
                R1 R2 R10 R11 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                P_GS P_Gspb P_Gm P_Gm2 P_Gab P_Gab8 P_Grib P_Gau P_Gn P_Gn8 P_GT P_GabT P_Gctx P_Gctxm P_Gctxs P_Gtp P_Gtsdp
                SOKstk SOKhdr P_okab SOKsh SOKT K_spb K_rib K_au K_magc P_magic K_hdr P_hv eq_refl K_nlo
                K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_cpm P_cpm1 K_kif K_key K_tsdp K_tctx K_thr
                Cf0 Lf0 Cf1 Lf1 K_cache
                (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) mx nf (r_mapped_fa (a_reg st c)) 0x19dc60 ks b80 b88
                (LE8 (Z_to_bv 64 0xafffff00000fffff)) bst bcs
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl P_Gspb2 P_GTsp P_Gmx P_Gnf (conj Q6 MFA18) LKS FKS ltac:(clear; lia) RET
                L80 L88 (length_N_to_le_bytes 8 _) Lst Lcs SOKstkF SOKRI SOKfa K_mx K_cntF Ccs Cst K_src K_int K_gpg K_pgv K_470 K_mu K_nf K_mfa C80 C88)
      as (rf & w9 & w22 & RUN & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z3 & Z4 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
    (* [comment removed for export] *)
    rewrite Eabm, Eidx in RUN.
    match type of RUN with msteps _ _ (mkst _ _ ?mf _) => remember mf as MF eqn:EMF end.
    assert (I_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by exact P_GS.
    assert (I_Gm : 0x10007fff8000 <= ab /\ (ab = m \/ ab + 16 <= m) /\ m + 16 + up8 n <= U S - 3584 /\ m mod 16 = 0).
    { rewrite Eabm in P_Gab. split; [clear - C3 SBH; lia|]. split; [exact P_Gab|]. exact P_Gm2. }
    assert (I_Gn8 : 8 <= up8 n /\ up8 n mod 8 = 0 /\ up8 n <= 2 ^ 40) by (clear - U8b U8c U8d N64; lia).
    assert (I_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)) by (destruct P_GT as (X1 & X2 & _); exact (conj X1 X2)).
    assert (I_GabT : m + 16 + up8 n <= T \/ T + 4096 <= ab) by (rewrite Eabm in P_GabT; exact P_GabT).
    assert (I_GT2 : 4096 <= T /\ T + 4096 <= U S - 3584) by (clear - GT4 GTC Slo; lia).
    assert (I_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 + 4096 <= U S - 3584) by (clear - SBH SB1 Slo; lia).
    assert (I_nf : 0 <= nf /\ 4 * (nf + mx / 2) <= 2 ^ 29) by (clear - P_Gnf Q6; lia).
    match type of EMF with
    | MF = fr_itemF ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20 ?a21 ?a22 ?a23 ?a24 ?a25 ?a26 ?a27 ?a28 ?a29 ?a30 ?a31 ?a32 ?a33 ?a34 =>
        pose proof (fr_itemF_foot a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34
                      I_GS I_Gm I_Gn8 I_GT I_GabT I_Gspb P_GTsp Hc P_Gmx I_nf LKS) as FT;
        pose proof (fr_itemF_grows a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34) as GRF;
        pose proof (fr_itemF_shadow a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34
                      I_GS I_Gm I_Gn8 I_GT I_GabT I_Gspb P_GTsp Hc P_Gmx I_nf LKS) as FSH
    end.
    rewrite <- EMF in FT, GRF, FSH.
    pose proof EMF as EMF2. unfold fr_itemF in EMF2.
    match type of EMF2 with
    | MF = fr_full ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20 ?a21 ?a22 ?a23 ?a24 ?a25 ?a26 =>
        pose proof (fr_full_cnt a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 I_GS I_GT2 Hc P_Gmx I_nf) as FCNT;
        pose proof (fr_full_slot a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 I_GS I_GT2 Hc P_Gmx I_nf) as FSLOT;
        pose proof (fr_full_mu a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 I_GS I_GT2 I_Gspb P_GTsp Hc P_Gmx I_nf) as FMU;
        pose proof (fr_full_nf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 I_GS I_GT2 I_Gspb P_GTsp Hc P_Gmx I_nf) as FNF;
        pose proof (fr_full_fa a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 I_GS I_GT2 I_Gspb P_GTsp Hc P_Gmx I_nf LKS) as FFA
    end.
    rewrite <- EMF2 in FCNT, FSLOT, FMU, FNF, FFA. clear EMF2.
    (* [comment removed for export] *)
    replace (0x4e8a4%bv : word) with (Z_to_bv 64 0x4e8a4 : word) in RUN by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x4e8a4) M (seg_rom BSEGS)) (@mkst fx rf ret MF (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4e8a4) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M MF).
    assert (VIS : forall a : word, Hd a = false -> M1 a = MF a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRF. rewrite (MrM a Eh). exact Ha. }
    assert (FOOT1 : forall a : word, M1 a <> M a ->
              (U S - 2720 <= U a < U S - 2400) \/ (m <= U a < m + 4) \/ (ab <> m /\ ab <= U a < ab + 8)
              \/ (0x7fff8000 + (m + 16) / 8 <= U a < 0x7fff8000 + (m + 16) / 8 + up8 n / 8)
              \/ (T + 2840 <= U a < T + 2856)
              \/ (T + 208 + 80 * c <= U a < T + 208 + 80 * c + 4)
              \/ (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) <= U a < T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) + 4)
              \/ (T + 2784 <= U a < T + 2792)
              \/ (SBEG + 2 ^ 37 + 128 * c <= U a < SBEG + 2 ^ 37 + 128 * c + 8) \/ (SBEG + 2 ^ 37 + 128 * c + 16 <= U a < SBEG + 2 ^ 37 + 128 * c + 24)
              \/ (SBEG + 2 ^ 37 + 128 * c + 80 <= U a < SBEG + 2 ^ 37 + 128 * c + 88)
              \/ (SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf <= U a < SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf + 4 * (mx / 2))).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM a Eh) in NE. exact (FT a NE). }
    assert (DEF1 : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    set (k := compact_of SBEG c ab).
    assert (Ek : k = j * csize c / 16).
    { (lazymatch goal with |- ?G => let G' := eval unfold k, compact_of, region_beg, KREGION in G in change_no_check G' end). f_equal. clear - Eab'. lia. }
    assert (Ek0 : k = compact_of SBEG c (prim_alloc_beg (m + 16) n)) by (rewrite <- Eab0; reflexivity).
    assert (NOX : forall a : word, M1 a <> M a -> ~ X (U a) /\ U a < U S - 2400).
    { intros a NE. destruct (FOOT1 a NE) as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]].
      - split; [| clear - F; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q Slo CR; lia | clear - F Q SB1 Slo; lia].
      - split; [apply XCH; clear - F Em RZ G5 QR3; lia | clear - F P_Gm2 U8b; lia].
      - split; [apply XCH; clear - F CS1; lia | clear - F I_Gm U8b; lia].
      - split; [| clear - F SHB Slo CR; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q SHB; lia | clear - F Q SHB SBH; lia].
      - split; [apply (OFFT (U a)); clear - F; lia | clear - F GTC Slo; lia].
      - split; [apply (OFFT (U a)); clear - F Hc; lia | clear - F GTC Slo Hc; lia].
      - split; [apply (OFFT (U a)); clear - F Hc DF P_Gmx; lia | clear - F GTC Slo Hc DF P_Gmx; lia].
      - split; [apply (OFFT (U a)); clear - F; lia | clear - F GTC Slo; lia].
      - split; [apply (OFFR (U a)); clear - F Hc; lia | clear - F SB1 Slo Hc; lia].
      - split; [apply (OFFR (U a)); clear - F Hc; lia | clear - F SB1 Slo Hc; lia].
      - split; [apply (OFFR (U a)); clear - F Hc; lia | clear - F SB1 Slo Hc; lia].
      - split; [apply (OFFF (U a)); clear - F; lia | clear - F SB1 Slo Q5 Q6 FAR NF0; lia]. }
    (* [comment removed for export] *)
    assert (RXa : RepX bt X st1 Lc FF (mid_mem bt st c (mx / 2) M M1) mdl1).
    { apply (drain_mid bt st Lc FF qt qg c (mx / 2) W Hc ltac:(clear - DF; lia) FAR X Xd M M1 mdl mdl1 RX ltac:(clear - LEN DF; lia) XSUB).
      - intros a _ NE. exact (DEF1 a NE).
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end).
        eapply rd_same; [| clear - SB0 SB1 CR Hc; wd_ulia_c | exact FMU].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHR. clear - Hx SB0 SB1 CR Hc. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). fold nf.
        eapply rd_same; [| clear - SB0 SB1 CR Hc; wd_ulia_c | exact FNF].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHR. clear - Hx SB0 SB1 CR Hc. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - intros i k0 Hik. fold ks in Hik.
        assert (Hi : Z.of_nat i < mx / 2) by (rewrite <- LKS; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate).
        (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). fold nf.
        replace (SBEG + c * 2 ^ 32 + 3758096384 + 4 * (nf + Z.of_nat i)) with (SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf + 4 * Z.of_nat i) by (clear; lia).
        eapply rd_same; [| clear - SB0 SB1 CR Q5 Q6 FAR NF0 Hi Hc; wd_ulia_c | exact (FFA i k0 Hik)].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHF. clear - Hx SB0 SB1 CR Q5 Q6 FAR NF0 Hi Hc. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - exact SBM1.
      - exact MI1. }
    (* [comment removed for export] *)
    assert (EGQ1 : a_gq st1 = BATCH ba ((m, n) :: its) :: rest) by (rewrite GQ1; exact EGQ).
    assert (XSUB1 : forall z, X z -> XB bt st1 z) by (intros z Hz; apply XB_drain_top; exact (XSUB z Hz)).
    assert (ROOM1 : Z.of_nat (length (a_cache st1 c)) < cache_max c) by (rewrite LEN1; fold mx; clear - DF; lia).
    assert (MDEFT : forall a : word, T <= U a < T + 4096 -> M a <> None).
    { intros a Ha. apply GR0. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (writableZ_def M0 _ _ _ TW). exact Ha. }
    assert (HFA : forall a : word, M1 a <> mid_mem bt st c (mx / 2) M M1 a -> foot_recycle_prim bt st1 m n c (U a) /\ M1 a <> None).
    { intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold foot_recycle_prim in G in change_no_check G' end). rewrite <- Eab0. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). rewrite <- SHhi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end). rewrite LEN1.
      destruct (mid_mem_diff bt st Lc FF qt qg c (mx / 2) W Hc ltac:(clear - DF; lia) FAR M M1 a NE) as [I | [NE' NFd]].
      - unfold T_PC, PC_SZ in I. split; [right; right; left; exact I | apply GR1; apply MDEFT; clear - I Hc; lia].
      - split; [| exact (DEF1 a NE')].
        destruct (FOOT1 a NE') as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]].
        + do 5 right. clear - F Slo. lia.
        + left. clear - F Em RZ G5 QR3. lia.
        + left. clear - F CS1. lia.
        + right; left. clear - F. lia.
        + do 4 right. left. clear - F. lia.
        + right; right; left. clear - F. lia.
        + right; right; right; left. clear - F. lia.
        + do 4 right. left. clear - F. lia.
        + exfalso. apply NFd. (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end). left. exact F.
        + exfalso. apply NFd. (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end). right; left. exact F.
        + exfalso. apply NFd. (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end). right; right; left. clear - F. lia.
        + exfalso. apply NFd. (lazymatch goal with |- ?G => let G' := eval unfold Fdr, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). fold nf. do 3 right. clear - F. lia. }
    assert (RX1 : AsAinvOpsRc73.AsAinvRepX3.RepX bt X (op_recycle_prim st1 c k) Lc FF M1 mdl1).
    { apply (OPS_REPX_recycle_prim_pf bt X Xd st1 Lc FF (mid_mem bt st c (mx / 2) M M1) M1 mdl1 mdl1 ba m n its rest c k qt qg W1 RXa EGQ1 HP Ec Ek0 ROOM1 XSUB1 XQ XOBJ).
      - intros a Ha. apply GR1. exact (QDEF a Ha).
      - intros a NE. destruct (HFA a NE) as [F D]. split; [left; exact F | exact D].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). rewrite LEN1.
        eapply rd_same; [| clear - GT0 GTC CR Hc; wd_ulia_c | exact FCNT].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT. clear - Hx GT0 GTC CR Hc. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). rewrite LEN1, Ek.
        eapply rd_same; [| clear - GT0 GTC CR Hc DF P_Gmx; wd_ulia_c | exact FSLOT].
        intros x Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT. clear - Hx GT0 GTC CR Hc DF P_Gmx. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
      - intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end). rewrite w2b1 by (clear; lia).
        rewrite <- SHhi in Hi. unfold sh_lo, SB in Hi.
        apply heap_rdn1; [clear - Hi SHB; wd_ulia|].
        rewrite VIS by (apply NHsh; exact Hi).
        replace i with (0x7fff8000 + (m + 16) / 8 + (i - (0x7fff8000 + (m + 16) / 8))) by (clear; lia). apply FSH. clear - Hi. lia.
      - apply same_but_materialized_refl.
      - exact MI1. }
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold rc_step_post in G in change_no_check G' end). exists fx, (op_recycle_prim st1 c k), M1, mdl1, rf.
    split; [reflexivity|]. split; [exact HFX|]. split; [rewrite Eh1; exact HH|]. split; [exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)|].
    split; [exact (OPS_WFq_recycle_prim_pf bt st1 Lc FF ba m n its rest c k qt qg W1 EGQ1 HP Ec Ek0 ROOM1)|].
    split; [exact RX1|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ1; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ1; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ1; reflexivity|].
    split.
    { split; [| exact (fk_trans _ _ _ (fk_drain_top bt st c (mx / 2) (touchable_carved bt st c ab Hc CVc))
                                     (fk_recycle_prim_at bt st1 c k (touchable_alloc bt st st1 c (fun c0 => alloc_drain_top st c (mx / 2) c0) (touchable_carved bt st c ab Hc CVc))))].          (* [comment removed for export] *)
      intros h HL. unfold holes_le in *. (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end). rewrite EGQ1. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg op_cache_push set_cache set_gq] in G in change_no_check G' end). intros c' Hc'. apply HL.
      unfold st1, op_drain_top in Hc'. cbn [a_reg set_cache set_reg] in Hc'. unfold fupdZ in Hc'.
      destruct (Z.eqb c' c) eqn:E; [apply Z.eqb_eq in E; subst c'; cbn [r_uhole r_fhole] in Hc'; exact Hc' | exact Hc']. }
    split; [intros z Hz; exact (XB_recycle_prim bt st1 ba (m, n) its rest c k z EGQ1 (XSUB1 z Hz))|].
    split.
    { intros a Ha. destruct (decide (M1 a = M a)) as [E|NE]; [exact E|]. exfalso. destruct (NOX a NE) as [N1 N2].
      destruct Ha as [Ha|Ha]; [exact (N1 Ha) | clear - Ha N2; lia]. }
    split.
    { intros a NE. split; [| left; exact (DEF1 a NE)]. (lazymatch goal with |- ?G => let G' := eval unfold rc_changed in G in change_no_check G' end).
      destruct (FOOT1 a NE) as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]].
      - left. clear - F. lia.
      - right; left. apply (quar_prim_private bt st Lc FF W m n (U a) Hq HP). rewrite <- Eab0, <- Ec. clear - F Em RZ G5 QR3. lia.
      - right; left. apply (quar_prim_private bt st Lc FF W m n (U a) Hq HP). rewrite <- Eab0, <- Ec. clear - F CS1. lia.
      - right; left. apply (quar_prim_shadow_private bt st Lc FF W m n (U a) Hq HP). rewrite <- SHhi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F Hc. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F Hc DF P_Gmx. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (rt_priv_reginfo bt st Lc FF W c (U a) Hc). (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (rt_priv_reginfo bt st Lc FF W c (U a) Hc). (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (rt_priv_reginfo bt st Lc FF W c (U a) Hc). (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (rt_priv_fa bt st Lc FF W c (U a) Hc). (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). clear - F FAR NF0 Q6. lia. }
    split; [intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity|].
    split; [apply same_but_materialized_except_vm; exact SBM1|].
    apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; try reflexivity. symmetry; exact R2.
  Qed.
End K6C.
End BoAllocFRcK6c.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lcq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK6g.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.

Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Section K6G.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Hypothesis BT_ia : bt_ia bt = both_addrs.

  Lemma repx_call : forall (Y P : Z -> Prop) st Lc FF (M M1 : mem) mdl mdl1 qt qg,
    WFq bt st Lc FF qt qg -> RepX bt Y st Lc FF M mdl ->
    same_but_materialized mdl mdl1 -> MInv (a_aa st) mdl1 ->
    (forall a : word, M1 a <> M a -> (CEIL <= U a \/ P (U a)) /\ M1 a <> None) ->
    RepX bt (fun z => Y z \/ P z) st Lc FF M1 mdl1.
  Proof using BT_ia.
    intros Y P st Lc FF M M1 mdl mdl1 qt qg W (M0 & RP & DX) SBM MI CH.
    set (M0' := fun a : word => if Z_le_dec CEIL (U a) then M1 a else M0 a).
    assert (DEF1 : forall a : word, M1 a <> M0 a -> M1 a <> None).
    { intros a NE. destruct (decide (M1 a = M a)) as [E | N]; [| exact (proj2 (CH a N))].
      rewrite E in *. exact (proj2 (DX a NE)). }
    exists M0'. split.
    - apply (Rep_sbm bt st Lc FF M0' mdl mdl1); [| exact MI | exact SBM].
      apply (Rep_frame_q bt st Lc FF M0 M0' mdl W RP). intros a NE. unfold M0' in NE |- *.
      destruct (Z_le_dec CEIL (U a)) as [G | L]; [| exfalso; exact (NE eq_refl)].
      split; [| exact (DEF1 a NE)]. intros RCa. pose proof (BoAllocM8Lcq.BoAllocM8Lkq.rep_cells_lt_ceil_q bt BT_ia st Lc FF (U a) qt qg W RCa). lia.
    - intros a NE. unfold M0' in NE. destruct (Z_le_dec CEIL (U a)) as [G | L]; [exfalso; exact (NE eq_refl)|].
      split; [| exact (DEF1 a NE)].
      destruct (decide (M1 a = M a)) as [E | N].
      + left. rewrite E in NE. exact (proj1 (DX a NE)).
      + destruct (proj1 (CH a N)) as [G | Pa]; [exfalso; lia | right; exact Pa].
  Qed.

  Definition uncall_mem (Yp Y : Z -> Prop) (Ypd : Xdec Yp) (Yd : Xdec Y) (M0 M : mem) : mem :=
    fun a : word => if Ypd (U a) then (if Yd (U a) then M a else M0 a) else M a.

  Lemma repx_uncall : forall (Yp Y : Z -> Prop) (Ypd : Xdec Yp) (Yd : Xdec Y) st Lc FF (M : mem) mdl,
    RepX bt Yp st Lc FF M mdl ->
    exists M0, Rep bt st Lc FF M0 mdl /\ (forall a : word, M a <> M0 a -> Yp (U a) /\ M a <> None)
               /\ RepX bt Y st Lc FF (uncall_mem Yp Y Ypd Yd M0 M) mdl.
  Proof using.
    intros Yp Y Ypd Yd st Lc FF M mdl (M0 & RP & DX). exists M0. split; [exact RP|]. split; [exact DX|].
    exists M0. split; [exact RP|]. intros a NE. unfold uncall_mem in NE |- *.
    destruct (Ypd (U a)) as [Hp | Np].
    - destruct (Yd (U a)) as [Hy | Ny]; [| exfalso; exact (NE eq_refl)]. split; [exact Hy | exact (proj2 (DX a NE))].
    - exfalso. exact (Np (proj1 (DX a NE))).
  Qed.

End K6G.
End BoAllocFRcK6g.
Require Stdlib.NArith.NArith OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lchq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMQhdr.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lcq OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lchq.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section G.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  Hypothesis QHDR_CONST : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.

  Lemma n3fq_of_boot : BoAllocM8Lcq.N3Fq_stmt bt.
  Proof using BOOTG. exact (AsKSys7b.N3Fq_pf bt (proj1 BOOTG)). Qed.
  Lemma n3fhq_of_boot : AsKSys10.AsKSys7c.N3FHq_stmt bt.
  Proof using BOOTG. exact (AsKSys10.AsKSys7c.N3FHq_pf bt (proj1 BOOTG)). Qed.

  Definition popBf_katwD_q_b {qt qg : Z} := @popBf_katwD_q RC fx bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X n3fq_of_boot QHDR_CONST qt qg.
  Definition popBf_katwD_h_q_b {qt qg : Z} := @popBf_katwD_h_q RC fx bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X n3fhq_of_boot QHDR_CONST qt qg.
End G.
End WithCeil.

(* [comment removed for export] *)
Lemma qhdr_const_both : forall bt a1 a2 a3 a4, bt_ia bt = both_addrs -> bt_consts bt = both_consts a1 a2 a3 a4 ->
  forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.
Proof.
  intros bt a1 a2 a3 a4 EI E z Hz (c & Hin & Hr). unfold IB in Hz. rewrite EI in Hz. cbn [ia_instance both_addrs] in Hz.
  rewrite E in Hin. unfold both_consts in Hin. cbv zeta in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; clear - Hz Hr; lia |]). exact Hin.
Qed.
End BoAllocMQhdr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcPop.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk BoAllocMQhdr.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section POP.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  Hypothesis QHDR_CONST : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.
  Context {qt qg : Z}.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).

  Theorem popBf_any :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v tp gp : word) (tot : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WFq bt st Lc FF qt qg -> AsKSys7b.qroom Lc qt qg -> RepX bt (BoAllocM8La.XL bt X c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) -> a_kact st <= KCAP ->       (* [comment removed for export] *)
    let r := a_reg st c in let mfa := r_mapped_fa r in let lo := fa_beg SBEG c + mfa in
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ (AIMGLO <= z < AIMGHI -> IB bt + 888 <= z < IB bt + 920) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (lo <= z < lo + KFAMAP) /\ ~ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x10ab58 ->
    getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 12 = Z_to_bv 64 (region_beg SBEG c) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (CEIL + 448 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (mfa < 4 * tot <= mfa + 2 ^ 18) ->
    writableZ BSEGS M (U sp - 448) (U sp) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        let st' := add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0 in
        WFq bt st' Lc FF qt qg -> RepX bt (BoAllocM8La.XL bt X c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)
             \/ (T + 2872 <= U a < T + 2888) \/ (reginfo bt c + 24 <= U a < reginfo bt c + 32)) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = sp -> getr r' 1 = ra ->
        getr r' 8 = s0v -> getr r' 9 = s1v -> getr r' 18 = s2v -> getr r' 19 = s3v -> getr r' 20 = s4v -> getr r' 21 = s5v -> getr r' 4 = tp -> getr r' 3 = gp ->
        getr r' 22 = getr regs 22 -> getr r' 23 = getr regs 23 -> getr r' 24 = getr regs 24 -> getr r' 25 = getr regs 25 ->
        katwD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r0 r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_fhole st c) ->
        WFq bt st' Lc FF qt qg -> RepX bt (BoAllocM8La.XL bt X c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 448 <= U a < U sp) /\ M' a <> None) \/ (lo <= U a < lo + KFAMAP)) ->
        regs_agree (fun i : reg => In i efs_clob) regs r0 -> efs_post sp ra s0v s1v s2v s3v 0 r0 r' ->
        katD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x4f508%bv : word) M rom) mdl) Qok Qf.
  Proof using QHDR_CONST PCELLS CELLS MIDEND FL PGP TSDP BOOTG BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v tp gp tot Qok Qf Hc W QR RX HALT MW ROOM FAQ KC r mfa lo XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Htot Hneed WSTK CONT1 CONT0.
    destruct (r_fhole (a_reg st c)) eqn:FH.
    - exact (popBf_katwD_h_q_b (qt := qt) (qg := qg) bt BT_segs BT_ia BOOTG TP TSDP PGP FL MIDEND CELLS PCELLS X QHDR_CONST c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v tp gp tot Qok Qf
               Hc W QR RX HALT MW FH ROOM FAQ KC XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Htot Hneed WSTK CONT1 CONT0).
    - exact (popBf_katwD_q_b (qt := qt) (qg := qg) bt BT_segs BT_ia BOOTG TP TSDP PGP FL MIDEND CELLS PCELLS X QHDR_CONST c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v tp gp tot Qok Qf
               Hc W QR RX HALT MW FH ROOM FAQ KC XOFF H1 H2 H4 H3 Etp H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Htot Hneed WSTK CONT1 CONT0).
  Qed.
End POP.
End WithCeil.
End BoAllocFRcPop.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRcK6m.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvPrist3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFKeep0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R BoAllocFRc4V OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4Rc.BoAllocFRc4Ra OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4Rc BoAllocFRc4Vc BoAllocFRc4Sp.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a BoAllocFRcK6g OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6h.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAllocMDm BoAllocFRcPop.

Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section K6M.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable TSDP : Z.
  Variables (TPm TSDPm PGPm FLm MIDENDm : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis CELLSPIN : free_cells_spin bt.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis HTPm : TPm = ia_tp both_addrs.
  Hypothesis CELLSM : malloc_cells bt TPm TSDPm PGPm FLm MIDENDm.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis QHDR_CONST : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  Definition Yshape (st : ast) (c : Z) (z : Z) : Prop :=
    (AIMGLO <= z < AIMGHI -> 0x10ab58 + 888 <= z < 0x10ab58 + 920)
    /\ ~ (T + 208 + 80 * c <= z < T + 208 + 80 * c + 80) /\ ~ (T + 2784 <= z < T + 2792) /\ ~ (T + 2872 <= z < T + 2888)
    /\ ~ (SBEG + 2 ^ 37 + 128 * c <= z < SBEG + 2 ^ 37 + 128 * c + 128)
    /\ ~ (CTX + 152 <= z < CTX + 160)
    /\ ~ (SBEG + c * 2 ^ 32 + 3758096384 <= z < SBEG + c * 2 ^ 32 + 3758096384 + 2 ^ 29)
    /\ ~ (sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)) <= z < sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)) + KFAMAP / 8)
    /\ z < CEIL.

  Lemma XB_Yshape : forall st Lc FF qt qg c z, WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    XB bt st z -> Yshape st c z.
  Proof using BT_ia.
    intros st Lc FF qt qg c z W Hc ROOM HX. pose proof ceil_rng as CR.
    pose proof (XB_not_T bt st Lc FF W z HX) as NT. pose proof (XB_not_band bt st Lc FF W z HX) as NB. pose proof (XB_below_ceil bt st Lc FF W z HX) as BC.
    pose proof (BoAllocM8Lcq.BoAllocM8Lkq.pk_thread_geom bt BT_ia st Lc FF qt qg W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (BoAllocM8Lcq.BoAllocM8Lkq.pk_thread_geom2 bt st Lc FF qt qg W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    assert (Hc24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    pose proof (region_facts bt st Lc FF W BATCHCLASS Hc24) as RF. cbn zeta in RF. destruct RF as (B1 & B2 & B3 & B4 & B5 & _).
    assert (SLOT : AS_HEAPLO <= fa_beg SBEG c + r_mapped_fa (a_reg st c) /\ fa_beg SBEG c + r_mapped_fa (a_reg st c) + KFAMAP <= CEIL).
    { unfold fa_beg, region_beg, KREGION, KFAOFF, KSPACE, PG, KFAMAP in *. clear - Q1 Q5 Q6 S2 S3 ROOM Hc. lia. }
    destruct (sh_band (fa_beg SBEG c + r_mapped_fa (a_reg st c)) KFAMAP (proj1 SLOT) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); lia) (proj2 SLOT) ltac:(reflexivity)) as (SHB0 & SHB1 & SHB2).
    unfold PG in NT. (lazymatch goal with |- ?G => let G' := eval unfold Yshape in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end).
    destruct (AsAinvOpsRc73.AsAinvOpsRc33.XB_zone bt st Lc FF W z HX) as [[HI Q] | [HS (a & XC & Ha)]].
    - unfold qhdr, IB in Q. rewrite BT_ia in *. cbn [ia_instance ia_img_lo ia_img_hi both_addrs] in *.
      unfold KSPACE, PG, AS_HEAPLO, AS_LO, AS_GAPHI, KFAMAP in *.
      split; [intros _; exact Q|]. split; [clear - NT Hc; lia|]. split; [clear - NT; lia|]. split; [clear - NT; lia|].
      split; [clear - Q S3 Hc; lia|]. split; [clear - Q CIMG; lia|]. split; [clear - Q S3 Hc; lia|]. split; [unfold SB in *; clear - Q SHB0; lia | clear - BC; lia].
    - destruct XC as [CVa _]. destruct (carved_range bt st Lc FF W BATCHCLASS a Hc24 CVa) as (K1 & K2 & K3 & K4 & _). change (csize BATCHCLASS) with 8192 in K2, K4. unfold BATCHSZ in Ha.
      try (rewrite BT_ia in *). cbn [ia_img_lo ia_img_hi both_addrs] in *.
      unfold fa_beg, region_beg, reginfo, KREGION, KFAOFF, KSPACE, PG, AS_HEAPLO, AS_LO, AS_GAPHI, KFAMAP, BATCHCLASS in *.
      split; [intros HI; exfalso; clear - HI HS S3; lia|]. split; [clear - NT Hc; lia|]. split; [clear - NT; lia|]. split; [clear - NT; lia|].
      split; [clear - HS Hc; lia|]. split; [clear - HS CSP; lia|].
      split.
      { clear - Ha K1 K2 B2 B3 Hc. assert (CC : c <= 23 \/ c = 24 \/ 25 <= c) by lia.
        destruct CC as [CC | [CC | CC]]; [assert (c * 2 ^ 32 <= 23 * 2 ^ 32) by nia; lia | subst c; lia | assert (25 * 2 ^ 32 <= c * 2 ^ 32) by nia; lia]. }
      split; [unfold SB in *; clear - NB SHB0 SHB1; lia | clear - BC; lia].
  Qed.

  Lemma XB_famap_meter : forall st c naa z, XB bt st z -> XB bt (add_meter (op_famap st c) 0 naa 0) z.
  Proof using.
    intros st c naa z. apply XB_mono.
    - intros a (j0 & H0 & H1 & H2). exists j0. split; [exact H0|]. split; [| exact H2]. (lazymatch goal with |- ?G => let G' := eval unfold op_famap, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
      destruct (Z.eqb_spec BATCHCLASS c) as [<- | NE]; (lazymatch goal with |- ?G => let G' := eval cbn [r_alloc_user] in G in change_no_check G' end); exact H1.
    - intros a H. left. exact H.
    - intros a H. left. exact H.
    - intros a (k0 & Hk0 & E). exists k0. split; [| exact E]. (lazymatch goal with |- ?G => let G' := eval unfold op_famap, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end).
      destruct (Z.eqb_spec BATCHCLASS c) as [<- | NE]; [(lazymatch goal with |- ?G => let G' := eval cbn [r_free] in G in change_no_check G' end); exact Hk0 | exact Hk0].
  Qed.

  (* [comment removed for export] *)
  Lemma dfull_room : forall st Lc FF qt qg c, WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> ~ fa_room st c ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29.
  Proof using.
    intros st Lc FF qt qg c W Hc NFAR.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((_ & _ & YA) & _). clear WR1.
    pose proof (fa_count_le bt st Lc FF c qt qg W Hc) as FC. pose proof (csize_pos c Hc) as ((CS1 & CS2) & CS16).
    assert (P_Gmx : 2 <= cache_max c <= 16) by ((lazymatch goal with |- ?G => let G' := eval unfold cache_max, cache_hint in G in change_no_check G' end); clear; lia).
    assert (DF : 1 <= cache_max c / 2 <= 8) by (clear - P_Gmx; Z.div_mod_to_equations; lia).
    unfold fa_room in NFAR. unfold AMAX in YA. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
    assert (NF26 : Z.of_nat (length (r_free (a_reg st c))) <= 2 ^ 26) by (clear - FC YA CS1; nia).
    clear - NFAR NF26 DF. lia.
  Qed.

  (* [comment removed for export] *)
  Definition FOOTC (st : ast) (c : Z) (S z : Z) : Prop :=
    let mx := cache_max c in let nf := Z.of_nat (length (r_free (a_reg st c))) in
    (S - 2720 <= z < S - 2400) \/ (T + 208 + 80 * c <= z < T + 208 + 80 * c + 4)
    \/ (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) <= z < T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) + 4) \/ (T + 2784 <= z < T + 2792)
    \/ (SBEG + 2 ^ 37 + 128 * c <= z < SBEG + 2 ^ 37 + 128 * c + 8) \/ (SBEG + 2 ^ 37 + 128 * c + 16 <= z < SBEG + 2 ^ 37 + 128 * c + 24)
    \/ (SBEG + 2 ^ 37 + 128 * c + 80 <= z < SBEG + 2 ^ 37 + 128 * c + 88)
    \/ (SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf <= z < SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf + 4 * (mx / 2)).
  (* [comment removed for export] *)
  Definition dfull_foot (st : ast) (c : Z) (S z : Z) : Prop :=
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    (S - 3088 <= z < S - 2400) \/ (T <= z < T + 4096) \/ (SBEG + 2 ^ 37 + 128 * c <= z < SBEG + 2 ^ 37 + 128 * c + 128)
    \/ (SBEG + c * 2 ^ 32 + 3758096384 <= z < SBEG + c * 2 ^ 32 + 3758096384 + 2 ^ 29)
    \/ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8).

  Lemma dfull_foot_changed : forall st Lc FF qt qg c S z, WFq bt st Lc FF qt qg -> 1 <= c <= 30 -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    dfull_foot st c S z -> rc_changed bt Lc FF S z.
  Proof using.
    intros st Lc FF qt qg c S z W Hc ROOM F. unfold dfull_foot in F. cbv zeta in F. (lazymatch goal with |- ?G => let G' := eval unfold rc_changed in G in change_no_check G' end).
    destruct F as [F | [F | [F | [F | F]]]].
    - left. clear - F. lia.
    - right; left. apply (OBL_rt_private_pf bt st Lc FF W z). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact F.
    - right; left. apply (rt_priv_reginfo bt st Lc FF W c z Hc). (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). exact F.
    - right; left. apply (rt_priv_fa bt st Lc FF W c z Hc). (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). exact F.
    - right; left. exact (rt_priv_fslot_shadow bt st Lc FF W c z Hc ROOM F).
  Qed.

  (* [comment removed for export] *)
  Lemma fk_famap_meter : forall st c naa, touchable bt st c -> free_keeps st (add_meter (op_famap st c) 0 naa 0).
  Proof using.
    intros st c naa TC. split; [| intros s H; exact H].
    intros S0 NS PR. apply AsAllocFFam.AsAinvPrist3.prist_add_meter. exact (AsAllocFFam.AsAinvPrist3.prist_famap S0 st c (touchable_notS bt st c S0 TC NS PR) PR).
  Qed.

  Definition dfull_map_post (fx : FPState) (X P : Z -> Prop) (qt qg : Z) (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model)
             (R : bvmap 5 word) (S ret : word) (c e : Z) (c' : config) : Prop :=
    let mx := cache_max c in let m := mx / 2 in let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    let st' := add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0 in
    exists (Mi MF : mem) mdlF (RF : bvmap 5 word),
      c' = mkCfg (@mkst fx RF ret MF (seg_rom BSEGS)) mdlF
      /\ m_halted mdlF = None /\ BackingAlgebra.model_ivs_wf mdlF /\ MInv (a_aa st') mdlF
      /\ WFq bt st' Lc FF qt qg /\ fa_room st' c
      /\ RepX bt X (op_drain_top st' c m) Lc FF (mid_mem bt st' c m Mi MF) mdlF
      /\ (forall a : word, MF a <> Mi a -> FOOTC st c (U S) (U a) \/ P (U a))
      /\ (forall a : word, MF a <> Mi a -> MF a <> None)
      /\ (forall a : word, MF a <> M a -> rc_changed bt Lc FF (U S) (U a) /\ MF a <> None)
      /\ (forall a : word, (X (U a) \/ P (U a)) \/ U S - 2400 <= U a -> MF a = M a)
      /\ rdn BSEGS MF (Z_to_bv 64 (T + 208 + 80 * c)) 4 = Some (LE4 (mx - m + 1))
      /\ rdn BSEGS MF (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * (mx - m))) 4 = Some (LE4 (e / 16))
      /\ lazy_kept (bt_ia bt) Lc FF mdl mdlF /\ same_except_vm mdl mdlF
      /\ regs_kept R RF.

  Theorem dfull_map_katD : forall fx (X P : Z -> Prop) (Xd : Xdec X) (Pd : Xdec P) qt qg st Lc FF (M : mem) mdl (R : bvmap 5 word) (S ret : word) c e,
    m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WFq bt st Lc FF qt qg -> rc_budget st Lc qt qg -> RepX bt (fun z => X z \/ P z) st Lc FF M mdl ->
    1 <= c <= 30 -> cache_max c <= Z.of_nat (length (a_cache st c)) -> ~ fa_room st c -> a_cinit st = true -> 0 <= e < 2 ^ 32 ->
    (forall z, X z -> XB bt st z) -> (forall z, P z -> Yshape st c z) ->
    getr R 1 = ret -> ret_ok ret -> getr R 2 = at_ S (-2400) ->
    getr R 10 = Z_to_bv 64 (T + 208) -> getr R 11 = Z_to_bv 64 0x10ab58 -> getr R 12 = Z_to_bv 64 c -> getr R 13 = Z_to_bv 64 (SBEG + c * 2 ^ 32 + e) ->
    getr R 4 = Z_to_bv 64 (ia_tp (bt_ia bt)) ->
    CEIL + 3584 <= U S -> U S + 16 <= PTRHI ->
    (forall a : word, U S - 3584 <= U a < U S - 2400 -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x4eca8) M (seg_rom BSEGS)) mdl) (dfull_map_post fx X P qt qg st Lc FF M mdl R S ret c e).
  Proof using QHDR_CONST PCELLS CELLSM HTPm BOOTG CELLSPIN RCF RCC CELLNB BT_ia BT_segs MIDENDm FLm PGPm TSDPm TPm TSDP.
    intros fx X P Xd Pd qt qg st Lc FF M mdl R S ret c e HH MW W QRK RX Hc FULL NFAR CINIT He XSUB PS R1 RET R2 R10 R11 R12 R13r R4 Slo Shi SOK.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    pose proof W as (_ & WC & _). destruct (WC c Hc) as (CLEN & _ & CKS). clear WC.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((_ & _ & YA) & _ & _ & _ & _ & MFA18 & _). clear WR1. unfold KFAMAP in MFA18.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    pose proof (fa_count_le bt st Lc FF c qt qg W Hc) as FC. pose proof (csize_pos c Hc) as ((CS1 & CS2) & CS16).
    set (mx := cache_max c) in *.
    assert (P_Gmx : 2 <= mx <= 16) by ((lazymatch goal with |- ?G => let G' := eval unfold mx, cache_max, cache_hint in G in change_no_check G' end); clear; lia).
    assert (DF : 1 <= mx / 2 <= 8 /\ 1 <= mx - mx / 2 <= 8) by (clear - P_Gmx; Z.div_mod_to_equations; lia).
    assert (LEN : Z.of_nat (length (a_cache st c)) = mx) by (clear - FULL CLEN; lia).
    set (nf := Z.of_nat (length (r_free (a_reg st c)))) in *.
    assert (NF0 : 0 <= nf) by ((lazymatch goal with |- ?G => let G' := eval unfold nf in G in change_no_check G' end); lia).
    assert (NF26 : nf <= 2 ^ 26) by (unfold AMAX in YA; clear - FC YA CS1 NF0; nia).
    unfold fa_room in NFAR. fold mx nf in NFAR.
    set (mfa := r_mapped_fa (a_reg st c)) in *.
    assert (ROOM : mfa + KFAMAP <= 2 ^ 29) by ((lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); clear - NFAR NF26 DF; lia).
    (* [comment removed for export] *)
    assert (FAQ : mfa <= 4 * (r_mapped_user (a_reg st c) / csize c)).
    { apply (AsAinvRoom3.famap_fa_le mfa (nf + mx / 2) _ (csize c)); [clear - CS1; lia | clear - NF0 DF; lia | clear - NFAR; lia |].
      apply (AsAinvRoom3.fa_q_drain bt st Lc FF c qt qg (mx / 2) W Hc). rewrite LEN. clear - DF P_Gmx. lia. }
    assert (I_nf : 0 <= nf /\ 4 * (nf + mx / 2) <= 2 ^ 29) by (clear - NF0 NF26 DF; lia).
    (* [comment removed for export] *)
    assert (YS0 : forall z, X z \/ P z -> Yshape st c z).
    { intros z [Hx | Hp]; [exact (XB_Yshape st Lc FF qt qg c z W Hc ROOM (XSUB z Hx)) | exact (PS z Hp)]. }
    pose proof (BoAllocM8Lcq.BoAllocM8Lkq.pk_thread_geom bt BT_ia st Lc FF qt qg W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (BoAllocM8Lcq.BoAllocM8Lkq.pk_thread_geom2 bt st Lc FF qt qg W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _ & _ & _ & _ & _ & GCT' & SB0 & SB1 & SBH & SB16).
    assert (T16 : T mod 16 = 0) by (clear - T4k; Z.div_mod_to_equations; lia).
    assert (SB8 : SBEG mod 8 = 0) by (clear - SB16; Z.div_mod_to_equations; lia).
    rewrite BT_ia in GTI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI.
    unfold KSPACE, PG, AS_HEAPLO, AS_LO, PTRHI in *.
    (* [comment removed for export] *)
    destruct (dfull_cells bt TSDP BT_segs BT_ia CELLNB RCC RCF CELLSPIN (fun z => X z \/ P z) st Lc FF M mdl qt qg c W RX Hc CINIT) as
      (NHs & NHT & NHR & NHF & K_spb & K_rib & K_int & K_gpg & K_pg & K_470 & KS1 & KS2 & KS3 & K_mx & K_src & K_nf & TDEF & RDEF & SOKT & SOKRI & SOKfa).
    { intros z Hz. destruct (YS0 z Hz) as (Y1 & Y2 & _ & _ & Y5 & _). (lazymatch goal with |- ?G => let G' := eval unfold Cshape in G in change_no_check G' end). split; [exact Y1|]. split; [clear - Y2; lia | clear - Y5; lia]. }
    destruct (dfull_cells_A bt BT_segs (fun z => X z \/ P z) st Lc FF M mdl qt qg c W RX Hc) as (K_cnt & K_mu).
    { intros z Hz. destruct (YS0 z Hz) as (_ & Y2 & _ & _ & Y5 & _). split; [clear - Y2; lia | clear - Y5; lia]. }
    rewrite LEN in K_cnt. fold mx in K_mx. fold nf in K_nf.
    set (Hd := HID st mdl) in *. set (memD := mrestrict Hd M) in *.
    pose proof RX as (M0 & RP & DX).
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _). destruct R14 as (B1 & B2 & _).
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2720)) 320 = true).
    { replace (at_ S (-2720)) with (Z_to_bv 64 (U S - 2720) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    idtac "PROGRESS K6m: cells A".
    (* [comment removed for export] *)
    assert (P_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - Slo Shi CR; lia).
    assert (P_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0).
    { split; [clear - T1 T4k; Z.div_mod_to_equations; lia|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; lia | clear - T2 Slo; lia] | exact T16]. }
    assert (P_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 + 4096 <= U S - 3584 /\ SBEG mod 8 = 0) by (split; [clear - S3; lia | split; [clear - S2 Slo; lia | exact SB8]]).
    assert (P_GTsp : hideW (T + 4096 <= SBEG \/ SBEG + 2 ^ 37 + 4096 <= T)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact TSP).
    destruct (run_dfull_A memD (seg_rom BSEGS) R S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20)
                (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                T SBEG c e mx nf [] (repeat (Z_to_bv 8 0) 8) (repeat (Z_to_bv 8 0) 8) (repeat (Z_to_bv 8 0) 8) (repeat (Z_to_bv 8 0) 8) (repeat (Z_to_bv 8 0) 8)
                R1 R2 R10 R11 R12 R13r eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                P_GS P_GT P_Gspb P_GTsp (conj Hc He) P_Gmx I_nf eq_refl eq_refl eq_refl eq_refl eq_refl
                SOKstk SOKT SOKRI K_mx K_cnt K_spb K_rib K_mu K_nf)
      as (rA & RUNA & RGA & CLA & GRA & OUTA).
    idtac "PROGRESS K6m: run A".
    (* [comment removed for export] *)
    match type of RUNA with msteps _ _ (mkst _ _ ?mf _) => remember mf as MA eqn:EMA end.
    replace (0x4eca8%bv : word) with (Z_to_bv 64 0x4eca8 : word) in RUNA by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x4eca8) M (seg_rom BSEGS)) (@mkst fx rA (0x4f508%bv : word) MA (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUNA. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4eca8) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M MA).
    assert (VIS : forall a : word, Hd a = false -> M1 a = MA a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRA. rewrite (MrM a Eh). exact Ha. }
    assert (DEF1 : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    set (CNT := fun z : Z => T + 208 + 80 * c <= z < T + 208 + 80 * c + 4).
    set (LCK := fun z : Z => SBEG + 2 ^ 37 + 128 * c <= z < SBEG + 2 ^ 37 + 128 * c + 8).
    assert (FOOTA : forall a : word, M1 a <> M a -> (U S - 2640 <= U a < U S - 2400) \/ CNT (U a) \/ LCK (U a)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM a Eh) in NE. (lazymatch goal with |- ?G => let G' := eval unfold CNT, LCK in G in change_no_check G' end).
      destruct (decide (U S - 2640 <= U a < U S - 2400)) as [|N1]; [left; assumption|].
      destruct (decide (T + 208 + 80 * c <= U a < T + 208 + 80 * c + 4)) as [|N2]; [right; left; assumption|].
      destruct (decide (SBEG + 2 ^ 37 + 128 * c <= U a < SBEG + 2 ^ 37 + 128 * c + 8)) as [|N3]; [right; right; assumption|].
      exfalso. apply NE. apply OUTA; [clear - N1; lia | clear - N2; lia | clear - N3; lia]. }
    (* [comment removed for export] *)
    set (Yp := fun z : Z => (X z \/ P z) \/ CNT z).
    assert (Ypd : Xdec (BoAllocM8La.XL bt Yp c)).
    { (lazymatch goal with |- ?G => let G' := eval unfold BoAllocM8La.XL, Yp, CNT in G in change_no_check G' end). apply Xdec_or; [apply Xdec_or; [apply Xdec_or; [exact Xd | exact Pd] | apply Xdec_iv] | apply Xdec_iv]. }
    assert (RXA : RepX bt (BoAllocM8La.XL bt Yp c) st Lc FF M1 mdl1).
    { apply (RepX_mono bt (fun z => (X z \/ P z) \/ (CNT z \/ LCK z))).
      - intros z [H | [H | H]]; (lazymatch goal with |- ?G => let G' := eval unfold BoAllocM8La.XL, Yp in G in change_no_check G' end); [left; left; exact H | left; right; exact H | right; (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); exact H].
      - apply (repx_call bt BT_ia (fun z => X z \/ P z) (fun z => CNT z \/ LCK z) st Lc FF M M1 mdl mdl1 qt qg W RX SBM1 MI1).
        intros a NE. split; [| exact (DEF1 a NE)]. destruct (FOOTA a NE) as [F | [F | F]]; [left; clear - F Slo; lia | right; left; exact F | right; right; exact F]. }
    destruct RGA as (A1 & A2 & A10 & A11 & A12 & A13 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A3 & A4).
    (* [comment removed for export] *)
    set (lo := fa_beg SBEG c + mfa) in *.
    assert (ELO : lo = SBEG + c * 2 ^ 32 + 3758096384 + mfa) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); reflexivity).
    assert (SLOT : 0x10007fff8000 <= lo /\ lo + KFAMAP <= CEIL).
    { rewrite ELO. unfold fa_beg, region_beg, KREGION, KFAOFF, KFAMAP in *. clear - Q1 Q5 Q6 S2 S3 ROOM Hc. lia. }
    destruct (sh_band lo KFAMAP ltac:((lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); exact (proj1 SLOT)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); lia) (proj2 SLOT) ltac:(reflexivity)) as (SHB0 & SHB1 & SHB2).
    fold (sh_lo lo) in SHB0, SHB1, SHB2. unfold AS_GAPHI, AS_HEAPLO in SHB0, SHB1.
    assert (USP : U (at_ S (-2640)) = U S - 2640) by (rewrite at_u by (clear - Slo CR HSr; lia); clear; lia).
    (* [comment removed for export] *)
    assert (ZONE_P : forall z, (U S - 2640 <= z < U S - 2400) \/ CNT z \/ LCK z ->
              ~ ((U S - 2640 - 448 <= z < U S - 2640) \/ (lo <= z < lo + KFAMAP) \/ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8)
                 \/ (T + 2872 <= z < T + 2888) \/ (SBEG + 2 ^ 37 + 128 * c + 24 <= z < SBEG + 2 ^ 37 + 128 * c + 32))).
    { intros z Hz F. unfold CNT, LCK in Hz. unfold KFAMAP in F, ROOM, SHB1.
      destruct Hz as [Hz | [Hz | Hz]]; destruct F as [F | [F | [F | [F | F]]]];
        clear - Hz F ELO Slo S2 S3 Q5 Q6 ROOM Hc SHB0 SHB1 TBAND T2 TSP CR; unfold fa_beg, region_beg, KREGION, KFAOFF in *; lia. }
    assert (CSH : forall z, BoAllocM8La.XL bt Yp c z -> Cshape bt c z).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold Cshape in G in change_no_check G' end). destruct Hz as [[Hz | Hz] | Hz].
      - destruct (YS0 z Hz) as (Y1 & Y2 & _ & _ & Y5 & _). split; [exact Y1|]. split; [clear - Y2; lia | clear - Y5; lia].
      - unfold CNT in Hz. split; [intros HI; exfalso; clear - Hz HI TIMG Hc; lia|]. split; [clear - Hz; lia | clear - Hz TSP Hc; lia].
      - unfold reginfo, KSPACE in Hz. split; [intros HI; exfalso; clear - Hz HI S3 Hc; lia|]. split; [clear - Hz TSP Hc; lia | clear - Hz; lia]. }
    (* [comment removed for export] *)
    apply (katwD_dm BSEGS _ _ (doomed BSEGS)); [| intros c' D; exact D].
    assert (Etp : U (getr rA 4) = TPm) by (rewrite A4, R4, HTPm, BT_ia; reflexivity).
    apply (popBf_any bt BT_segs BT_ia BOOTG TPm TSDPm PGPm FLm MIDENDm CELLSM PCELLS Yp QHDR_CONST c st Lc FF M1 (seg_rom BSEGS) mdl1 rA
             (at_ S (-2640)) (Z_to_bv 64 0x4f344) (getr rA 8) (getr rA 9) (getr rA 18) (getr rA 19) (getr rA 20) (getr rA 21) (getr rA 4) (getr rA 3) (nf + mx / 2)
             _ (doomed BSEGS) Hc W (proj1 QRK) RXA).
    - rewrite Eh1. exact HH.
    - exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW).
    - exact ROOM.
    - exact FAQ.
    - exact (proj2 QRK).
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold mfa lo. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold reginfo, IB, KSPACE in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
      destruct Hz as [Hz | Hz].
      + destruct (YS0 z Hz) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9). fold mfa lo in Y8.
        split; [exact Y5|]. split; [exact Y1|]. split; [exact Y6|]. split; [| exact Y8].
        unfold KFAMAP in *. clear - Y7 Q6 ROOM ELO. lia.
      + unfold CNT in Hz. unfold KFAMAP in *.
        split; [clear - Hz TSP Hc; lia|]. split; [intros HI; exfalso; clear - Hz HI TIMG Hc; lia|]. split; [clear - Hz GCT' Hc; lia|].
        split; [clear - Hz TSP Q5 Q6 ROOM Hc ELO; unfold fa_beg, region_beg, KREGION, KFAOFF in *; lia | clear - Hz SHB0 SHB1 TBAND Hc; lia].
    - exact A1.
    - exact A2.
    - reflexivity.
    - reflexivity.
    - exact Etp.
    - exact A10.
    - rewrite A11. (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). reflexivity.
    - rewrite A12. (lazymatch goal with |- ?G => let G' := eval unfold region_beg, KREGION in G in change_no_check G' end). reflexivity.
    - exact A13.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite USP. clear - Slo Shi CR. lia.
    - apply ret_ok_lit; [clear; lia | reflexivity].
    - clear - I_nf NF0 DF. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold mfa. fold nf in Q7. clear - NFAR Q7 DF. lia.
    - (* [comment removed for export] *)
      rewrite USP. intros i Hi.
      assert (Ei : U (Z_to_bv 64 i : word) = i) by (clear - Hi Slo CR HSr; wd_ulia).
      destruct (SOK (Z_to_bv 64 i)) as [D0 SK0]; [rewrite Ei; clear - Hi; lia|].
      split; [apply GR1; exact D0 | eapply store_ok_mono; [exact GR1 | exact SK0]].
    - (* [comment removed for export] *)
      intros r' M' mdl' st' W' RX' SEV LK MW' HH' FOOTP V10 V2 V1 V8 V9 V18 V19 V20 V21 V4 V3 V22 V23 V24 V25.
      apply katwD_of_katD. rewrite USP in FOOTP. fold mfa lo in FOOTP. unfold reginfo, KSPACE in FOOTP.
      idtac "PROGRESS K6m: installed".
      (* [comment removed for export] *)
      assert (CA' : a_cache st' c = a_cache st c) by reflexivity.
      assert (REG' : a_reg st' c = REG (r_mapped_user (a_reg st c)) (r_alloc_user (a_reg st c)) (mfa + KFAMAP) (r_free (a_reg st c)) (r_uhole (a_reg st c)) false).
      { (lazymatch goal with |- ?G => let G' := eval unfold st', op_famap, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_reg] in G in change_no_check G' end). apply fupdZ_same. }
      assert (NF' : Z.of_nat (length (r_free (a_reg st' c))) = nf) by (rewrite REG'; reflexivity).
      assert (MFA' : r_mapped_fa (a_reg st' c) = mfa + KFAMAP) by (rewrite REG'; reflexivity).
      assert (Q7' : 4 * nf <= mfa) by exact Q7.
      assert (FAR' : fa_room st' c).
      { (lazymatch goal with |- ?G => let G' := eval unfold fa_room in G in change_no_check G' end). rewrite NF', MFA'. fold mx. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). clear - Q7' DF. lia. }
      destruct (dfull_cells bt TSDP BT_segs BT_ia CELLNB RCC RCF CELLSPIN (BoAllocM8La.XL bt Yp c) st' Lc FF M' mdl' qt qg c W' RX' Hc CINIT CSH) as
        (NHs' & NHT' & NHR' & NHF' & K_spb' & K_rib' & K_int' & K_gpg' & K_pg' & K_470' & _ & _ & _ & K_mx' & K_src' & K_nf' & TDEF' & RDEF' & SOKT' & SOKRI' & SOKfa').
      rewrite MFA' in NHF', SOKfa'. rewrite CA' in K_src'.
      set (Hd' := HID st' mdl') in *. set (memD' := mrestrict Hd' M') in *.
      pose proof RX' as (M0' & RP' & DX').
      pose proof RP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14' & _). destruct R14' as (B1' & B2' & _).
      (* [comment removed for export] *)
      set (ks := skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2)) (a_cache st c)).
      assert (LKS : Z.of_nat (length ks) = mx / 2) by ((lazymatch goal with |- ?G => let G' := eval unfold ks in G in change_no_check G' end); rewrite length_skipn; clear - LEN DF; lia).
      assert (FKS : Forall (fun k => 0 <= k < 2 ^ 31) ks).
      { apply Forall_forall. intros k0 Hk. assert (Hin : In k0 (a_cache st c)) by (unfold ks in Hk; rewrite <- (firstn_skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2)) (a_cache st c)); apply in_or_app; right; exact Hk).
        destruct (CKS k0 Hin) as (Kr & CVk). destruct (carved_range bt st Lc FF W c _ Hc CVk) as (D1 & D2 & _).
        unfold chunk_of_compact, fa_beg, region_beg, KREGION, KFAOFF in *. clear - D1 D2 Q2 Q3 Kr CS1. lia. }
      assert (K_srcC : forall i k0, nth_error ks i = Some k0 -> rdn BSEGS memD' (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i)) 4 = Some (LE4 k0)).
      { intros i k0 Hik. unfold ks in Hik. rewrite nth_error_skipn in Hik. specialize (K_src' _ _ Hik).
        replace (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i) with (T + 208 + 80 * c + 16 + 4 * Z.of_nat (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2) + i))
          by (rewrite Nat2Z.inj_add, Z2Nat.id by (clear - LEN DF; lia); rewrite LEN; clear; lia).
        exact K_src'. }
      destruct (rdn_defined_ex BSEGS memD' (Z_to_bv 64 (T + 2784)) 8) as (bst & Cst & Lst);
        [intros i Hi; apply TDEF'; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
      destruct (rdn_defined_ex BSEGS memD' (Z_to_bv 64 (T + 208 + 80 * c + 8)) 8) as (bcs & Ccs & Lcs);
        [intros i Hi; apply TDEF'; clear - Hi GT0 GTC CR Hc; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR Hc; wd_ulia |].
      destruct (rdn_defined_ex BSEGS memD' (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 80)) 8) as (b80 & C80 & L80);
        [intros i Hi; apply RDEF'; clear - Hi SB0 SB1 CR Hc; revert Hi; unorm; intros Hi; lia | clear - SB0 SB1 CR Hc; wd_ulia |].
      destruct (rdn_defined_ex BSEGS memD' (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 88)) 8) as (b88 & C88 & L88);
        [intros i Hi; apply RDEF'; clear - Hi SB0 SB1 CR Hc; revert Hi; unorm; intros Hi; lia | clear - SB0 SB1 CR Hc; wd_ulia |].
      assert (GRP : mem_grows M1 M').
      { intros a Ha. destruct (decide (M' a = M1 a)) as [E | N]; [rewrite E; exact Ha | exact (proj2 (FOOTP a N))]. }
      assert (SOKstk' : store_ok BSEGS memD' (at_ S (-2720)) 320 = true).
      { replace (at_ S (-2720)) with (Z_to_bv 64 (U S - 2720) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
        apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
        - apply GRP. apply GR1. apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. unorm. lia.
        - apply NHs'; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
      assert (SOKfaC : store_ok BSEGS memD' (Z_to_bv 64 (SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf)) (4 * length ks) = true).
      { apply SOKfa'; [clear - NF0; lia | (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); clear - LKS Q7' DF; lia]. }
      (* [comment removed for export] *)
      assert (CLA' : fullA_cells memD' S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                                 (getr R 25) (getr R 26) (getr R 27) T SBEG c e mx).
      { apply (fullA_cells_same MA memD' S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                 (getr R 25) (getr R 26) (getr R 27) T SBEG c e mx); [clear - Slo Shi CR; lia | clear - GT0 GTC CR Hc; lia | clear - SB0 SB1 CR Hc; lia | | exact CLA].
        intros x Hx.
        assert (ZN : (U S - 2640 <= U x < U S - 2400) \/ CNT (U x) \/ LCK (U x)) by exact Hx.
        assert (V0 : Hd x = false /\ Hd' x = false).
        { rewrite <- (Z_to_bv_bv_unsigned 64 x). destruct Hx as [Hx | [Hx | Hx]].
          - split; [apply NHs | apply NHs']; first [clear - Hx HSr Slo CR; lia | left; clear - Hx Slo; lia].
          - split; [apply NHT | apply NHT']; clear - Hx Hc; lia.
          - split; [apply NHR | apply NHR']; clear - Hx Hc; lia. }
        (lazymatch goal with |- ?G => let G' := eval unfold memD' in G in change_no_check G' end). rewrite (mrestrict_off Hd' M' x (proj2 V0)).
        destruct (decide (M' x = M1 x)) as [E | N]; [rewrite E; exact (VIS x (proj1 V0)) | exfalso; exact (ZONE_P (U x) ZN (proj1 (FOOTP x N)))]. }
      assert (E8 : getr r' 8 = Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) by (rewrite V8; exact A8).
      assert (E9 : getr r' 9 = Z_to_bv 64 nf) by (rewrite V9; exact A9).
      assert (E18 : getr r' 18 = Z_to_bv 64 c) by (rewrite V18; exact A18).
      assert (E19 : getr r' 19 = at_ S (-2504)) by (rewrite V19; exact A19).
      assert (E20 : getr r' 20 = Z_to_bv 64 0x10ab58) by (rewrite V20; exact A20).
      assert (E21 : getr r' 21 = Z_to_bv 64 (mx / 2)) by (rewrite V21; exact A21).
      assert (E22 : getr r' 22 = Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2))) by (rewrite V22; exact A22).
      assert (E23 : getr r' 23 = Z_to_bv 64 (nf + mx / 2)) by (rewrite V23; exact A23).
      assert (E24 : getr r' 24 = Z_to_bv 64 (2 ^ 61)) by (rewrite V24; exact A24).
      assert (E25 : getr r' 25 = Z_to_bv 64 (SBEG + c * 2 ^ 32 + 3758096384)) by (rewrite V25; exact A25).
      assert (Gpgp : AIMGLO <= 0x19dc60 /\ 0x19dc60 + 8 <= AIMGHI) by (clear; lia).
      idtac "PROGRESS K6m: cells C".
      (* [comment removed for export] *)
      destruct (run_dfull_C memD' (seg_rom BSEGS) r' S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20)
                  (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                  T SBEG c e mx nf 0x19dc60 ks b80 b88 (LE8 (Z_to_bv 64 0xafffff00000fffff)) bst bcs
                  V10 V2 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25
                  P_GS P_GT P_Gspb P_GTsp (conj Hc He) P_Gmx I_nf LKS FKS Gpgp RET L80 L88 (length_N_to_le_bytes 8 _) Lst Lcs
                  SOKstk' SOKT' SOKRI' SOKfaC Ccs Cst K_srcC K_spb' K_rib' K_int' K_gpg' K_pg' K_470' C80 C88 CLA')
        as (rF & w9 & w22 & RUNC & RGC).
      idtac "PROGRESS K6m: run C".
      match type of RUNC with msteps _ _ (mkst _ _ ?mf _) => remember mf as MFr eqn:EMF end.
      assert (I_GT : 4096 <= T /\ T + 4096 <= U S - 3584) by (clear - P_GT; lia).
      assert (I_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 + 4096 <= U S - 3584) by (clear - P_Gspb; lia).
      assert (FT : forall a : word, MFr a <> memD' a -> FOOTC st c (U S) (U a)) by (rewrite EMF; (lazymatch goal with |- ?G => let G' := eval unfold FOOTC in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); apply fr_fullC_foot; assumption).
      assert (GRF : mem_grows memD' MFr) by (rewrite EMF; apply fr_fullC_grows).
      assert (FCNT : rdn BSEGS MFr (Z_to_bv 64 (T + 208 + 80 * c)) 4 = Some (LE4 (mx - mx / 2 + 1))) by (rewrite EMF; apply fr_fullC_cnt; assumption).
      assert (FSLOT : rdn BSEGS MFr (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2))) 4 = Some (LE4 (e / 16))) by (rewrite EMF; apply fr_fullC_slot; assumption).
      assert (FMU : rdn BSEGS MFr (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 8 = Some (LE8 (Z_to_bv 64 0))) by (rewrite EMF; apply fr_fullC_mu; assumption).
      assert (FNF : rdn BSEGS MFr (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 16)) 8 = Some (LE8 (Z_to_bv 64 (nf + mx / 2)))) by (rewrite EMF; apply fr_fullC_nf; assumption).
      assert (FFA : forall i k, nth_error ks i = Some k -> rdn BSEGS MFr (Z_to_bv 64 (SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf + 4 * Z.of_nat i)) 4 = Some (LE4 k))
        by (rewrite EMF; apply fr_fullC_fa; assumption).
      (* [comment removed for export] *)
      replace (0x4f344%bv : word) with (Z_to_bv 64 0x4f344 : word) in RUNC by (apply bv_eq; reflexivity).
      apply (katD_msteps_acct BSEGS Hd' (HID_off_segments bt st' Lc FF M0' mdl' BT_ia RP') asanF_segs_wx (a_aa st')
               (@mkst fx r' (Z_to_bv 64 0x4f344) M' (seg_rom BSEGS)) (@mkst fx rF ret MFr (seg_rom BSEGS)) mdl').
      { apply lazy_cover_HID. } { exact B1'. } { exact B2'. } { exact HH'. } { rewrite restrict_mkstK. exact RUNC. }
      intros mdlF MIF SBMF HCF. rewrite unrestrict_mkst.
      replace (ms_mem (@mkst fx r' (Z_to_bv 64 0x4f344) M' (seg_rom BSEGS))) with M' by reflexivity.
      pose proof (same_but_materialized_frame mdl' mdlF SBMF) as SFF.
      destruct SFF as (_ & EvmF & ElzF & _ & _ & _ & _ & _ & _ & _ & _ & _ & EhF & _).
      set (MF := munrestrict Hd' M' MFr).
      assert (VIS' : forall a : word, Hd' a = false -> MF a = MFr a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end); apply munrestrict_off; exact Ha).
      assert (HIDv' : forall a : word, Hd' a = true -> MF a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end); apply munrestrict_on; exact Ha).
      assert (MrM' : forall a : word, Hd' a = false -> memD' a = M' a) by (intros a Ha; apply mrestrict_off; exact Ha).
      assert (GRF' : mem_grows M' MF).
      { intros a Ha. destruct (Hd' a) eqn:Eh; [rewrite (HIDv' a Eh); exact Ha | rewrite (VIS' a Eh)]. apply GRF. rewrite (MrM' a Eh). exact Ha. }
      assert (FOOTF : forall a : word, MF a <> M' a -> FOOTC st c (U S) (U a)).
      { intros a NE. destruct (Hd' a) eqn:Eh; [exfalso; apply NE; apply HIDv'; exact Eh|].
        rewrite (VIS' a Eh) in NE. rewrite <- (MrM' a Eh) in NE. exact (FT a NE). }
      assert (DEFF : forall a : word, MF a <> M' a -> MF a <> None).
      { intros a NE E1. apply NE. rewrite E1. destruct (M' a) eqn:E0; [|reflexivity]. exfalso.
        assert (D : M' a <> None) by (rewrite E0; discriminate). apply GRF' in D. exact (D E1). }
      idtac "PROGRESS K6m: lift C".
      (* [comment removed for export] *)
      destruct (repx_uncall bt (BoAllocM8La.XL bt Yp c) X Ypd Xd st' Lc FF M' mdl' RX') as (M0i & RPi & DXi & RXi).
      set (Mi := uncall_mem (BoAllocM8La.XL bt Yp c) X Ypd Xd M0i M') in *.
      assert (XSUB' : forall z, X z -> XB bt st' z) by (intros z Hz; apply XB_famap_meter; exact (XSUB z Hz)).
      assert (PATCH : forall a : word, Mi a <> M' a -> (P (U a) \/ CNT (U a) \/ LCK (U a)) /\ M' a <> M0i a).
      { intros a NE. unfold Mi, uncall_mem in NE. destruct (Ypd (U a)) as [Hp | Np]; [| exfalso; exact (NE eq_refl)].
        destruct (Xd (U a)) as [Hx | Nx]; [exfalso; exact (NE eq_refl)|]. split; [| intros E; apply NE; symmetry; exact E].
        destruct Hp as [[[Hx | Hp] | Hk] | Hl]; [contradiction | left; exact Hp | right; left; exact Hk | right; right; unfold reginfo, KSPACE in Hl; exact Hl]. }
      assert (DEFMi : forall a : word, MF a <> Mi a -> MF a <> None).
      { intros a NE. destruct (decide (MF a = M' a)) as [E | N]; [| exact (DEFF a N)].
        rewrite E in *. assert (NE' : Mi a <> M' a) by (intros Q; apply NE; symmetry; exact Q). exact (proj2 (DXi a (proj2 (PATCH a NE')))). }
      assert (RXa : RepX bt X (op_drain_top st' c (mx / 2)) Lc FF (mid_mem bt st' c (mx / 2) Mi MF) mdlF).
      { apply (drain_mid bt st' Lc FF qt qg c (mx / 2) W' Hc ltac:(clear - DF; lia) FAR' X Xd Mi MF mdl' mdlF RXi ltac:(rewrite CA'; clear - LEN DF; lia) XSUB').
        - intros a _ NE. exact (DEFMi a NE).
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end).
          eapply rd_same; [| clear - SB0 SB1 CR Hc; wd_ulia_c | exact FMU].
          intros x Hx. apply VIS'. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHR'. clear - Hx SB0 SB1 CR Hc. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end). rewrite NF'.
          eapply rd_same; [| clear - SB0 SB1 CR Hc; wd_ulia_c | exact FNF].
          intros x Hx. apply VIS'. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHR'. clear - Hx SB0 SB1 CR Hc. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
        - intros i k Hik. rewrite CA' in Hik. fold ks in Hik.
          assert (Hi : Z.of_nat i < mx / 2) by (rewrite <- LKS; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate).
          (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). rewrite NF'.
          replace (SBEG + c * 2 ^ 32 + 3758096384 + 4 * (nf + Z.of_nat i)) with (SBEG + c * 2 ^ 32 + 3758096384 + 4 * nf + 4 * Z.of_nat i) by (clear; lia).
          eapply rd_same; [| clear - SB0 SB1 CR Q5 Q6 I_nf NF0 Hi Hc; unfold fa_beg, region_beg, KREGION, KFAOFF in *; wd_ulia_c | exact (FFA i k Hik)].
          intros x Hx. apply VIS'. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHF'. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
          clear - Hx SB0 SB1 CR Q5 Q6 Q7' I_nf NF0 Hi Hc DF. unfold fa_beg, region_beg, KREGION, KFAOFF in *. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia.
        - exact SBMF.
        - exact MIF. }
      idtac "PROGRESS K6m: drain_mid".
      (* [comment removed for export] *)
      assert (FOOTPRE : forall a : word, MF a <> M a ->
                ((U S - 2640 <= U a < U S - 2400) \/ CNT (U a) \/ LCK (U a))
                \/ ((U S - 2640 - 448 <= U a < U S - 2640) \/ (lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)
                    \/ (T + 2872 <= U a < T + 2888) \/ (SBEG + 2 ^ 37 + 128 * c + 24 <= U a < SBEG + 2 ^ 37 + 128 * c + 32))
                \/ FOOTC st c (U S) (U a)).
      { intros a NE. destruct (decide (MF a = M' a)) as [E | N]; [| right; right; exact (FOOTF a N)].
        rewrite E in NE. destruct (decide (M' a = M1 a)) as [E1 | N1]; [rewrite E1 in NE; left; exact (FOOTA a NE) | right; left; exact (proj1 (FOOTP a N1))]. }
      assert (OFFALL : forall a : word, MF a <> M a -> ~ (X (U a) \/ P (U a)) /\ U a < U S - 2400 /\ dfull_foot st c (U S) (U a)).
      { intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold dfull_foot in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold mfa lo.
        assert (YN : forall Q : Prop, (Yshape st c (U a) -> Q -> False) -> Q -> ~ (X (U a) \/ P (U a))) by (intros Q HQ Hq HY; exact (HQ (YS0 _ HY) Hq)).
        unfold Yshape in YN. fold mfa lo in YN. unfold FOOTC, CNT, LCK in FOOTPRE. cbv zeta in FOOTPRE. fold mx nf in FOOTPRE.
        rewrite ELO in *. unfold fa_beg, region_beg, KREGION, KFAOFF, KFAMAP in *.
        assert (YY : (X (U a) \/ P (U a)) -> Yshape st c (U a)) by (intros HY; exact (YS0 _ HY)).
        unfold Yshape in YY. fold mfa lo in YY. clear YN.
        (* [comment removed for export] *)
        destruct (FOOTPRE a NE) as [[F | [F | F]] | [[F | [F | [F | [F | F]]]] | [F | [F | [F | [F | [F | [F | [F | F]]]]]]]]].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9); clear - F Y9 Slo CR; lia|]. split; [clear - F; lia | left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & Y2 & _); clear - F Y2; lia|]. split; [clear - F T2 Slo CR Hc; lia | right; left; clear - F Hc; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & Y5 & _); clear - F Y5; lia|]. split; [clear - F S2 Slo CR Hc; lia | right; right; left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9); clear - F Y9 Slo CR; lia|]. split; [clear - F; lia | left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & _ & _ & Y7 & _); clear - F Y7 Q6 ROOM; lia|]. split; [clear - F S2 Slo CR Hc Q5 Q6 ROOM; lia | do 3 right; left; clear - F Q6 ROOM; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & _ & _ & _ & Y8 & _); exact (Y8 F)|]. split; [clear - F SHB1 S3 S2 Slo CR; lia | do 4 right; exact F].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & Y4 & _); clear - F Y4; lia|]. split; [clear - F T2 Slo CR; lia | right; left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & Y5 & _); clear - F Y5; lia|]. split; [clear - F S2 Slo CR Hc; lia | right; right; left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9); clear - F Y9 Slo CR; lia|]. split; [clear - F; lia | left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & Y2 & _); clear - F Y2; lia|]. split; [clear - F T2 Slo CR Hc; lia | right; left; clear - F Hc; lia].
        - split; [intros HY; destruct (YY HY) as (_ & Y2 & _); clear - F Y2 DF; lia|]. split; [clear - F T2 Slo CR Hc DF; lia | right; left; clear - F Hc DF; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & Y3 & _); clear - F Y3; lia|]. split; [clear - F T2 Slo CR; lia | right; left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & Y5 & _); clear - F Y5; lia|]. split; [clear - F S2 Slo CR Hc; lia | right; right; left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & Y5 & _); clear - F Y5; lia|]. split; [clear - F S2 Slo CR Hc; lia | right; right; left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & Y5 & _); clear - F Y5; lia|]. split; [clear - F S2 Slo CR Hc; lia | right; right; left; clear - F; lia].
        - split; [intros HY; destruct (YY HY) as (_ & _ & _ & _ & _ & _ & Y7 & _); clear - F Y7 I_nf NF0 DF; lia|]. split; [clear - F S2 Slo CR Hc Q5 I_nf NF0 DF; lia | do 3 right; left; clear - F I_nf NF0 DF; lia]. }
      apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold dfull_map_post in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold mx mfa lo. exists Mi, MF, mdlF, rF.
      split; [reflexivity|]. split; [rewrite EhF; exact HH'|]. split; [exact (model_ivs_wf_sbm mdl' mdlF SBMF MW')|]. split; [exact MIF|].
      split; [exact W'|]. split; [exact FAR'|]. split; [exact RXa|].
      split.
      { intros a NE. destruct (decide (MF a = M' a)) as [E | N]; [| left; exact (FOOTF a N)].
        rewrite E in NE. assert (NE' : Mi a <> M' a) by (intros Q; apply NE; symmetry; exact Q).
        destruct (proj1 (PATCH a NE')) as [Hp | [Hk | Hl]]; [right; exact Hp | left; (lazymatch goal with |- ?G => let G' := eval unfold FOOTC in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); right; left; exact Hk | left; (lazymatch goal with |- ?G => let G' := eval unfold FOOTC in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); do 4 right; left; exact Hl]. }
      split; [exact DEFMi|].
      split.
      { intros a NE. split; [exact (dfull_foot_changed st Lc FF qt qg c (U S) (U a) W Hc ROOM (proj2 (proj2 (OFFALL a NE))))|]. intros E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
        assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. apply GRP in D. apply GRF' in D. exact (D E1). }
      split.
      { intros a Ha. destruct (decide (MF a = M a)) as [E | NE]; [exact E|]. exfalso. destruct (OFFALL a NE) as (N1 & N2 & _).
        destruct Ha as [Ha | Ha]; [exact (N1 Ha) | clear - Ha N2; lia]. }
      split.
      { eapply rd_same; [| clear - GT0 GTC CR Hc; wd_ulia_c | exact FCNT].
        intros x Hx. apply VIS'. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT'. clear - Hx GT0 GTC CR Hc. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia. }
      split.
      { eapply rd_same; [| clear - GT0 GTC CR Hc DF; wd_ulia_c | exact FSLOT].
        intros x Hx. apply VIS'. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHT'. clear - Hx GT0 GTC CR Hc DF. revert Hx. unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). intros Hx. lia. }
      split.
      { intros a Ha. transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite ElzF; reflexivity|].
        transitivity (lzb mdl1 a); [exact (LK a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity]. }
      split.
      { exact (same_except_vm_trans _ _ _ (same_but_materialized_except_vm _ _ SBM1) (same_except_vm_trans _ _ _ SEV (same_but_materialized_except_vm _ _ SBMF))). }
      destruct RGC as (Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z3 & Z4 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27).
      rewrite V3, A3 in Z3. rewrite V4, A4 in Z4.
      apply regs_kept_intro; rewrite ?Z2, ?Z3, ?Z4, ?Z8, ?Z9, ?Z18, ?Z19, ?Z20, ?Z21, ?Z22, ?Z23, ?Z24, ?Z25, ?Z26, ?Z27; try reflexivity. symmetry; exact R2.
    - (* [comment removed for export] *)
      intros r0 r' M' mdl' st'' Est W' RX' SEV LK MW' HH' FOOTP AG POST. apply katD_refl.
      destruct POST as (V10 & V2 & _). rewrite USP in FOOTP. fold mfa lo in FOOTP.
      assert (CINIT'' : a_cinit st'' = true) by (destruct Est as [-> | ->]; exact CINIT).
      destruct (dfull_cells bt TSDP BT_segs BT_ia CELLNB RCC RCF CELLSPIN (BoAllocM8La.XL bt Yp c) st'' Lc FF M' mdl' qt qg c W' RX' Hc CINIT'' CSH) as
        (NHs' & _ & _ & _ & _ & _ & _ & _ & _ & _ & KS1' & KS2' & KS3' & _).
      set (Hd'' := HID st'' mdl') in *.
      assert (SOKsp : store_ok BSEGS (mrestrict Hd'' M') (at_ S (-2656)) 16 = true).
      { replace (at_ S (-2656)) with (Z_to_bv 64 (U S - 2656) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
        apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
        - assert (Ez : U (Z_to_bv 64 z : word) = z) by (clear - Hz Slo CR HSr; wd_ulia).
          destruct (decide (M' (Z_to_bv 64 z) = M1 (Z_to_bv 64 z))) as [E | N].
          + rewrite E. apply GR1. apply (SOK (Z_to_bv 64 z)). rewrite Ez. clear - Hz. lia.
          + destruct (FOOTP _ N) as [[_ D] | F]; [exact D | exfalso; rewrite Ez in F; rewrite ELO in F; unfold fa_beg, region_beg, KREGION, KFAOFF, KFAMAP in *; clear - F Hz Slo S2 Q5 Q6 ROOM Hc; lia].
        - apply NHs'; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
      destruct (rta_spin_run (mrestrict Hd'' M') (seg_rom BSEGS) r' S V10 V2 ltac:(clear - Slo Shi CR; lia) SOKsp KS1' KS2' KS3') as (rs & ms & RUNS).
      replace (0x4f344%bv : word) with (Z_to_bv 64 0x4f344 : word) in RUNS by (apply bv_eq; reflexivity).
      pose proof RX' as (M0'' & RP'' & DX'').
      pose proof RP'' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R14'' & _). destruct R14'' as (B1'' & B2'' & _).
      apply (doomed_msteps_acct BSEGS Hd'' (HID_off_segments bt st'' Lc FF M0'' mdl' BT_ia RP'') asanF_segs_wx (a_aa st'')
               (@mkst fx r' (Z_to_bv 64 0x4f344) M' (seg_rom BSEGS)) (@mkst fx rs (0x4f674%bv : word) ms (seg_rom BSEGS)) mdl').
      { apply lazy_cover_HID. } { exact B1''. } { exact B2''. } { exact HH'. } { rewrite restrict_mkstK. exact RUNS. }
      intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst.
      pose proof (same_but_materialized_frame mdl' mdl3 SBM3) as SF3.
      destruct SF3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _).
      apply doomed_to_spin; [apply rta_spin_to_spin | rewrite Eh3; exact HH'].
  Qed.
End K6M.
End BoAllocFRcK6m.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA BoAllocFRc3T4 BoAllocFRc3U4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R.BoAllocFRc4U OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4R BoAllocFRc4V BoAllocFRc4T BoAllocFRc4W.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc43 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRtPriv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFRcG OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcH OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6a BoAllocFRcK6g OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFRcK6h BoAllocFRcK6m.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lcq.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAllocFKeep0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcK1.BoAllocFHypR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma down8_up8K6 : forall n, AsRtRegion.down8 (n + 7) = up8 n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold AsRtRegion.down8, AsAinvOpsPf3d.AsAinvFreeS.up8 in G in change_no_check G' end). lia. Qed.
Lemma rz_16_32_6 : forall r, r mod 16 = 0 -> 16 <= r -> r = 16 \/ 32 <= r.
Proof. intros. lia. Qed.
Lemma mod16_8_6 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros. lia. Qed.
Lemma sh_range_in6 : forall lo len a n8, lo mod 8 = 0 -> len mod 8 = 0 -> a mod 8 = 0 -> n8 mod 8 = 0 -> lo <= a -> a + n8 <= lo + len -> 0 <= n8 ->
  lo / 8 <= a / 8 /\ a / 8 + n8 / 8 <= lo / 8 + len / 8 /\ 8 * (a / 8) = a /\ 8 * (n8 / 8) = n8.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section K6P.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis CELLNB : free_cells_nb bt.
  Hypothesis RCC : rc_cells bt TSDP.
  Hypothesis RCF : rc_cells_full bt.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Variables (TPm TSDPm PGPm FLm MIDENDm : Z).
  Hypothesis CELLSPIN : free_cells_spin bt.
  Hypothesis BOOTG : AsKSys10.AsKSys9.boot_geom bt.
  Hypothesis HTPm : TPm = ia_tp both_addrs.
  Hypothesis CELLSM : malloc_cells bt TPm TSDPm PGPm FLm MIDENDm.
  Hypothesis PCELLS : pop_cells bt.
  Definition qhdr_const_stmt : Prop := forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.      (* [comment removed for export] *)
  Hypothesis QHDR_CONST : qhdr_const_stmt.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  Theorem rc_item_full_map_pf : rc_item_stmt bt FXOK arm_prim_full_map.
  Proof using QHDR_CONST PCELLS CELLSM HTPm BOOTG CELLSPIN MIDENDm FLm PGPm TSDPm TPm HTP RCF RCC CELLNB CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold rc_item_stmt in G in change_no_check G' end).
    intros fx X Xd qt qg st Lc FF M mdl R S ret ba m n its rest HFX HH MW W RX EGQ ((HP & FULL) & NFAR) XSUB XQ XOBJ QDEF
           R1 RET R2 R10 R11 R4 CCB S16 Slo Shi SOK QRK.
    pose proof NFAR as NFAR0. pose proof RCC as RCC0. pose proof RCF as RCF0. pose proof CELLNB as CELLNB0.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    pose proof RX as (M0 & RP & DX).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a Ha. destruct (decide (M a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M) by (intros a Ha; destruct (decide (M a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct RCC as (CELL_rib & CELL_magic & G_tsdp). destruct RCF as (CELL_int & CELL_gpg & CELL_pgv & CELL_470).
    unfold free_cells_nb in CELLNB.
    (* [comment removed for export] *)
    assert (Hq : In (m, n) (quar st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). apply in_flat_map. exists (BATCH ba ((m, n) :: its)). split; [apply in_app_iff; right; rewrite EGQ; left; reflexivity | left; reflexivity]. }
    assert (Hb : In (BATCH ba ((m, n) :: its)) (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite EGQ; left; reflexivity).
    pose proof (cinit_of_batch bt st Lc FF qt qg _ W Hb) as CINIT.
    pose proof (quar_chunk bt st Lc FF W m n Hq HP) as G. cbn zeta in G.
    unfold fa_room in NFAR. remember (blk_class n) as c eqn:Ec. remember (prim_alloc_beg (m + 16) n) as ab eqn:Eab0.
    destruct G as (Hc & CV & INQ & G4 & G5 & G6).
    destruct (carved_range bt st Lc FF W c ab Hc CV) as (C1 & C2 & C3 & C4 & C5).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
    pose proof (csize_pos c Hc) as ((CS1 & CS2) & CS16).
    (* [comment removed for export] *)
    pose proof W as (_ & WC & _). destruct (WC c Hc) as (CLEN & _ & CKS). clear WC.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & MFA18 & _). clear WR1. unfold KFAMAP in MFA18.
    set (mx := cache_max c) in *.
    assert (P_Gmx : 2 <= mx <= 16) by ((lazymatch goal with |- ?G => let G' := eval unfold mx, cache_max, cache_hint in G in change_no_check G' end); clear; lia).
    assert (DF : 1 <= mx / 2 <= 8 /\ 1 <= mx - mx / 2 <= 8) by (clear - P_Gmx; Z.div_mod_to_equations; lia).
    assert (LEN : Z.of_nat (length (a_cache st c)) = mx) by (clear - FULL CLEN; lia).
    set (ks := skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2)) (a_cache st c)).
    assert (LKS : Z.of_nat (length ks) = mx / 2) by ((lazymatch goal with |- ?G => let G' := eval unfold ks in G in change_no_check G' end); rewrite length_skipn; clear - LEN DF; lia).
    assert (FKS : Forall (fun k => 0 <= k < 2 ^ 31) ks).
    { apply Forall_forall. intros k0 Hk. assert (Hin : In k0 (a_cache st c)) by (unfold ks in Hk; rewrite <- (firstn_skipn (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2)) (a_cache st c)); apply in_or_app; right; exact Hk).
      destruct (CKS k0 Hin) as (Kr & CVk). destruct (carved_range bt st Lc FF W c _ Hc CVk) as (D1 & D2 & _).
      pose proof (region_facts bt st Lc FF W c Hc) as RF0. cbn zeta in RF0. destruct RF0 as (_ & E2 & E3 & _).
      unfold chunk_of_compact, fa_beg, region_beg, KREGION, KFAOFF in *. clear - D1 D2 E2 E3 Kr CS1. lia. }
    set (nf := Z.of_nat (length (r_free (a_reg st c)))) in *.
    assert (NF0 : 0 <= nf) by ((lazymatch goal with |- ?G => let G' := eval unfold nf in G in change_no_check G' end); lia).
    destruct (quar_item_range bt st Lc FF W m n Hq) as (QR1 & QR2 & QR3).
    pose proof (rz_mod16 n) as RM. pose proof (rz_range n) as RZ.
    assert (N64 : n <= 64512) by (apply (is_primary_iff n ltac:(lia)); exact HP).
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & INT & _ & _ & INC).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as SPT.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SPC.
    destruct CV as (j & Hj0 & Hj1 & Eab). pose proof Eab as Eab'. unfold chunk_addr, region_beg, KREGION in Eab'.
    assert (CVc : carved bt st c ab) by (exists j; repeat split; assumption).
    destruct (up8_facts n ltac:(lia)) as (U8a & U8b & U8c & U8d).
    assert (T16 : T mod 16 = 0) by (clear - TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    rewrite BT_ia in GTI, GCI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI.
    unfold IB in *. rewrite BT_ia in *. cbn [ia_instance both_addrs] in *.
    unfold fa_beg, reginfo, region_beg, KREGION, KFAOFF, KSPACE, PG, AS_HEAPLO, AS_LO, NMAX, PTRHI in *.
    remember (csize c) as cs eqn:Ecs. set (d := m - SBEG - c * 2 ^ 32).
    assert (Em : m = ab + rz n - 16) by (clear - G4; lia).
    assert (M16 : m mod 16 = 0) by (clear - Em C5 RM; Z.div_mod_to_equations; lia).
    assert (Ed : d = j * cs + (rz n - 16)) by ((lazymatch goal with |- ?G => let G' := eval unfold d in G in change_no_check G' end); clear - Em Eab'; lia).
    assert (Hrz : 0 <= rz n - 16 < cs) by (clear - G5 G4 QR3 RZ; lia).
    assert (Eidx : d / cs = j) by (symmetry; apply (Z.div_unique d cs j (rz n - 16)); [left; exact Hrz | clear - Ed; lia]).
    assert (JJ : (j + 1) * cs = j * cs + cs) by ring.
    assert (JJ0 : 0 <= j * cs) by (clear - Hj0 CS1; nia).
    assert (Hd32 : 0 <= d < 2 ^ 32) by (clear - Ed Hrz JJ JJ0 Hj1 Q3 Q2; lia).
    assert (Eabm : SBEG + c * 2 ^ 32 + d / cs * cs = ab) by (rewrite Eidx; clear - Eab'; lia).
    assert (P8 : (m + 16) mod 8 = 0) by (clear - M16; Z.div_mod_to_equations; lia).
    assert (N8le : m + 16 + up8 n <= ab + cs).
    { apply (up8_le (m + 16) n (ab + cs) P8); [clear - C5 CS16; Z.div_mod_to_equations; lia | exact G5]. }
    destruct (sh_up8 (m + 16) n P8 ltac:(lia)) as [SHhi SHlo]. unfold SB in SHhi, SHlo.
    destruct (sh_range_in6 (SBEG + c * 2 ^ 32) (r_mapped_user (a_reg st c)) (m + 16) (up8 n))
      as (SR1 & SR2 & SR3 & SR4);
      [clear - Q11; Z.div_mod_to_equations; lia | clear - Q13; Z.div_mod_to_equations; lia | exact P8 | exact U8d
      | clear - Em C1 RZ; lia | clear - N8le C2 Q3; lia | clear - U8b; lia |].
    (* [comment removed for export] *)
    pose proof RP as (Rc & Ri & Rt & Rr & _ & _ & _ & Rh & _ & _ & _ & Rs & R13 & R14 & _ & _ & Csb & _ & SHM0).
    first [pose proof (proj1 SHM0) as SHM | pose proof SHM0 as SHM]. clear SHM0.          (* [comment removed for export] *)
    rewrite BT_ia in Csb. cbn [ia_rtc_sb both_addrs] in Csb.
    destruct Rt as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & Tback & _).
    destruct (TPC c Hc) as (PCcnt & PCmax & PCcs & PCks). rewrite CINIT in PCmax.
    destruct (Rr c Hc) as [(RIm0 & _ & RInf & RImfa & _ & _ & RImu & _ & _ & RIW) (_ & FAW & RWR)]. fold nf in RInf.
    destruct Rh as [_ RHQ]. destruct (RHQ m n Hq) as [(Hst & (b1 & Hb1 & H11) & Hnhi & Hnlo & _ & _ & HMAG) _].
    destruct R14 as (B1 & B2 & _ & _ & BSH & _).
    destruct (BSH c Hc) as [BSHu _].
    rewrite BT_segs in *.
    unfold T_PC, PC_SZ in *. unfold fa_beg, reginfo, region_beg, KREGION, KFAOFF, KSPACE, sh_lo, SB in *.
    replace (m + 16 - 16) with m in * by lia. replace (m + 16 - 15) with (m + 1) in * by lia.
    replace (m + 16 - 14) with (m + 2) in * by lia. replace (m + 16 - 12) with (m + 4) in * by lia.
    assert (Hb1r : 0 <= b1 < 256) by (destruct Hb1; subst; lia).
    (* [comment removed for export] *)
    assert (XZ : forall z, X z -> (0x10ab58 + 888 <= z < 0x10ab58 + 920) \/ SBEG <= z < SBEG + 2 ^ 37).
    { intros z Hz. destruct (XB_zone bt st Lc FF W z (XSUB z Hz)) as [Q | Q]; [left; unfold qhdr, IB in Q; rewrite BT_ia in Q; exact Q | right; exact Q]. }
    assert (XCH : forall z, ab <= z < ab + cs -> ~ X z).
    { intros z Hz Hx. rewrite Ecs in Hz. exact (XB_not_owned bt st Lc FF W z c ab (XSUB z Hx) Hc CVc (or_introl INQ) Hz). }
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GT0 GTC CR; lia|]. apply (rep_nolazy_thread bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHC : forall z, CTX <= z < CTX + 65536 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz GC0 GCC CR; lia|]. apply (rep_nolazy_tctx bt st Lc FF M0 mdl W RP). exact Hz. }
    assert (NHR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 CR; lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). exact Hz. }
    assert (NHF : forall z, SBEG + c * 2 ^ 32 + 3758096384 <= z < SBEG + c * 2 ^ 32 + 3758096384 + r_mapped_fa (a_reg st c) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz SB0 SB1 Q5 Q6 CR Hc; lia|]. apply (rep_nolazy_fa bt st Lc FF M0 mdl W RP c z Hc).
      (lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). exact Hz. }
    assert (NHch : forall z, ab <= z < ab + cs -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz C3 C4 SB0 SB1 CR; lia|]. rewrite Ecs in Hz. exact (rep_nolazy_chunk bt st Lc FF M0 mdl W RP c ab z Hc CVc Hz). }
    assert (NHsh : forall z, 0x7fff8000 + (m + 16) / 8 <= z < 0x7fff8000 + (m + 16) / 8 + up8 n / 8 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. apply BSHu. clear - Hz SR1 SR2. lia. }
    (* [comment removed for export] *)
    pose (memD := mrestrict Hd M).
    Ltac cimg XZ SBH NHs := intros z Hz; split; [ intros Hx; destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q; lia | clear - Hz Q SBH; lia]
                                                 | apply NHs; [clear - Hz; lia | right; clear - Hz; lia] ].
    Ltac czl := first [ reflexivity | (vm_compute; discriminate) | (vm_compute; reflexivity) ].
    Ltac konstK Hd M M0 X Rc EQ0 XZ SBH NHs C := apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc C) EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); cimg XZ SBH NHs].
    assert (K_spb : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SBEG))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELLNB.
    assert (K_rib : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 (SBEG + 2 ^ 37)))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_rib.
    assert (K_magc : rdn BSEGS memD (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_magic.
    assert (K_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gsh.
    assert (K_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { apply (cellX Hd M M0 X _ _ _ Csb EQ0); [czl | czl | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); cimg XZ SBH NHs]. }
    assert (K_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gmb.
    assert (K_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_mb.
    assert (K_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gme.
    assert (K_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_me.
    assert (K_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_ghe.
    assert (K_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_he.
    assert (K_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_grm.
    assert (K_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_rm.
    assert (K_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 CPM]).
    { rewrite <- w2b1 by (clear - Gc8; lia). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_cpm. }
    assert (K_kif : rdn BSEGS memD (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]).
    { rewrite <- w2b1 by (clear; lia). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_kif. }
    assert (K_key : rdn BSEGS memD (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (clear - HSr; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; reflexivity). konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_key. }
    subst TP. cbn [ia_tp both_addrs] in CELL_tsdp, Gc9, Gc10.
    assert (Utp : U (getr R 4) = 0x641380) by (rewrite R4; vm_compute; reflexivity).
    assert (K_tsdp : rdn BSEGS memD (at_ (getr R 4) (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ (getr R 4) (-88)) with (Z_to_bv 64 (0x641380 - 88) : word) by (clear - Utp; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Utp; unorm; reflexivity).
      konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_tsdp. }
    assert (K_tctx : rdn BSEGS memD (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))).
    { apply (cellX Hd M M0 X _ _ _ (const_cell bt _ _ _ _ Rc CELL_tctx) EQ0); [clear - Gc1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc2; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q G_tsdp; lia | clear - Hz Q SBH Gc2; lia].
      - apply NHs; [clear - Hz Gc1 Gc2; lia | right; clear - Hz Gc1 Gc2; lia]. }
    assert (K_thr : rdn BSEGS memD (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152) : word) by (clear - GC0 GCC CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (cellX Hd M M0 X _ _ _ Tback EQ0); [clear - GC0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GCI; lia | clear - Hz Q SPC; lia].
      - apply NHC. clear - Hz. lia. }
    assert (K_au : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 48)) 8 = Some (LE8 (Z_to_bv 64 (r_mapped_user (a_reg st c))))).
    { apply (cellX Hd M M0 X _ _ _ RImu EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q SBH Hc; lia | clear - Hz Q Hc; lia].
      - apply NHR. clear - Hz Hc. lia. }
    assert (K_mx : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c + 4)) 4 = Some (LE4 (cache_max c))).
    { apply (cellX Hd M M0 X _ _ _ PCmax EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI Hc; lia | clear - Hz Q SPT Hc; lia].
      - apply NHT. clear - Hz Hc. lia. }
    assert (K_cnt : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c)) 4 = Some (LE4 (Z.of_nat (length (a_cache st c))))).
    { apply (cellX Hd M M0 X _ _ _ PCcnt EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC Hc CR; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI Hc; lia | clear - Hz Q SPT Hc; lia].
      - apply NHT. clear - Hz Hc. lia. }
    assert (K_cntF : rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c)) 4 = Some (LE4 mx)) by (rewrite <- LEN; exact K_cnt).
    assert (K_int : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 40)) 4 = Some (LE4 0xffffffff)) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_int.
    assert (K_gpg : rdn BSEGS memD (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 0x19dc60))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_gpg.
    assert (K_pgv : rdn BSEGS memD (Z_to_bv 64 0x19dc60) 8 = Some (LE8 (Z_to_bv 64 4096))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_pgv.
    assert (K_470 : rdn BSEGS memD (Z_to_bv 64 0x10468) 8 = Some (LE8 (Z_to_bv 64 0xafffff00000fffff))) by konstK Hd M M0 X Rc EQ0 XZ SBH NHs CELL_470.
    assert (OFFT : forall z, T <= z < T + 4096 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHT; exact Hz]. intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q GTI; lia | clear - Hz Q SPT; lia]. }
    assert (OFFR : forall z, SBEG + 2 ^ 37 <= z < SBEG + 2 ^ 37 + 4096 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [| apply NHR; exact Hz]. intros Hx. destruct (XZ z Hx) as [Q|Q]; [clear - Hz Q SBH; lia | clear - Hz Q; lia]. }
    assert (K_src : forall i k0, nth_error ks i = Some k0 -> rdn BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i)) 4 = Some (LE4 k0)).
    { intros i k0 Hik. assert (Hi : Z.of_nat i < mx / 2) by (rewrite <- LKS; apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hik; discriminate).
      unfold ks in Hik. rewrite nth_error_skipn in Hik. specialize (PCks _ _ Hik).
      replace (T + 208 + 80 * c + 16 + 4 * (mx - mx / 2) + 4 * Z.of_nat i) with (T + 208 + 80 * c + 16 + 4 * Z.of_nat (Z.to_nat (Z.of_nat (length (a_cache st c)) - mx / 2) + i))
        by (rewrite Nat2Z.inj_add, Z2Nat.id by (clear - LEN DF; lia); rewrite LEN; clear; lia).
      apply (cellX Hd M M0 X _ _ _ PCks EQ0); [clear - GT0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR LEN Hi Hc DF P_Gmx; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFT. clear - Hz LEN Hi Hc DF P_Gmx. lia. }
    assert (K_mu : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { apply (cellX Hd M M0 X _ _ _ RIm0 EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz Hc. lia. }
    assert (K_nf : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 16)) 8 = Some (LE8 (Z_to_bv 64 nf))).
    { apply (cellX Hd M M0 X _ _ _ RInf EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz Hc. lia. }
    assert (K_mfa : rdn BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 24)) 8 = Some (LE8 (Z_to_bv 64 (r_mapped_fa (a_reg st c))))).
    { apply (cellX Hd M M0 X _ _ _ RImfa EQ0); [clear - SB0 Hc; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - SB1 CR Hc; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFR. clear - Hz Hc. lia. }
    assert (RDEF : forall i, SBEG + 2 ^ 37 + 128 * c <= i < SBEG + 2 ^ 37 + 128 * c + 128 -> memD (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHR; clear - Hi Hc; lia). apply GR0. apply (writableZ_def M0 _ _ _ RIW). exact Hi. }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 80)) 8) as (b80 & C80 & L80);
      [intros i Hi; apply RDEF; clear - Hi SB0 SB1 CR Hc; revert Hi; unorm; intros Hi; lia | clear - SB0 SB1 CR Hc; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c + 88)) 8) as (b88 & C88 & L88);
      [intros i Hi; apply RDEF; clear - Hi SB0 SB1 CR Hc; revert Hi; unorm; intros Hi; lia | clear - SB0 SB1 CR Hc; wd_ulia |].
    assert (K_magic : ab <> m -> rdn BSEGS memD (Z_to_bv 64 ab) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))).
    { intros NE. pose proof (rz_16_32_6 (rz n) RM ltac:(clear - RZ; lia)) as RZC. destruct (HMAG ltac:(clear - NE Em RZC; lia)) as [MG _]. replace (m + 16 - rz n) with ab in MG by (clear - Em; lia).
      apply (cellX Hd M M0 X _ _ _ MG EQ0); [clear - C3 SB0; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR CS1; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split; [apply XCH | apply NHch]; clear - Hz CS1; lia. }
    assert (OFFm : forall z, m <= z < m + 8 -> ~ X z /\ Hd (Z_to_bv 64 z) = false).
    { intros z Hz. split; [apply XCH | apply NHch]; clear - Hz Em RZ G5 QR3; lia. }
    assert (Kh0 : rdn BSEGS memD (Z_to_bv 64 m) 1 = Some [Z_to_bv 8 3]).
    { rewrite <- w2b1 by (clear; lia). apply (cellX Hd M M0 X _ _ _ Hst EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (Kh1 : rdn BSEGS memD (Z_to_bv 64 (m + 1)) 1 = Some [Z_to_bv 8 b1]).
    { rewrite <- w2b1 by (clear - Hb1r; lia). apply (cellX Hd M M0 X _ _ _ H11 EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (Kh2 : rdn BSEGS memD (Z_to_bv 64 (m + 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32)))).
    { apply (cellX Hd M M0 X _ _ _ Hnhi EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (K_nlo : rdn BSEGS memD (Z_to_bv 64 (m + 4)) 4 = Some (LE4 (n mod 2 ^ 32))).
    { apply (cellX Hd M M0 X _ _ _ Hnlo EQ0); [clear - C3 SB0 Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - C4 SB1 CR Em Hrz; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    set (h2 := Z_to_bv 8 (U (Z_to_bv 64 (n / 2 ^ 32)))). set (h3 := Z_to_bv 8 (Z.shiftr (U (Z_to_bv 64 (n / 2 ^ 32))) 8)).
    assert (Mrng : 0 <= m /\ m + 16 < 2 ^ 64) by (clear - C3 SB0 Em RZ C4 SB1 CR Hrz; lia).
    assert (K_hdr : rdn BSEGS memD (Z_to_bv 64 m) 4 = Some [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3]).
    { change 4%nat with (1 + (1 + 2))%nat.
      apply (rdn_cat BSEGS memD _ 1 3 [Z_to_bv 8 3]); [exact Kh0 | | clear - Mrng; wd_ulia].
      replace (at_ (Z_to_bv 64 m) (Z.of_nat 1)) with (Z_to_bv 64 (m + 1)) by (clear - Mrng; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply (rdn_cat BSEGS memD _ 1 2 [Z_to_bv 8 b1]); [exact Kh1 | | clear - Mrng; wd_ulia].
      replace (at_ (Z_to_bv 64 (m + 1)) (Z.of_nat 1)) with (Z_to_bv 64 (m + 2)) by (clear - Mrng; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      exact Kh2. }
    (* [comment removed for export] *)
    assert (TDEF : forall i, T <= i < T + 4096 -> memD (Z_to_bv 64 i) <> None).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite mrestrict_off by (apply NHT; exact Hi). apply GR0. apply (writableZ_def M0 _ _ _ TW). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hi. }
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2840)) 8) as (bf0 & Cf0 & Lf0);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2848)) 8) as (bf1 & Cf1 & Lf1);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 2784)) 8) as (bst & Cst & Lst);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR; wd_ulia |].
    destruct (rdn_defined_ex BSEGS memD (Z_to_bv 64 (T + 208 + 80 * c + 8)) 8) as (bcs & Ccs & Lcs);
      [intros i Hi; apply TDEF; clear - Hi GT0 GTC CR Hc; revert Hi; unorm; intros Hi; lia | clear - GT0 GTC CR Hc; wd_ulia |].
    (* [comment removed for export] *)
    assert (K_cache : rdn BSEGS memD (at_ S (-2392)) 8 = Some (LE8 (Z_to_bv 64 (T + 208)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold memD in G in change_no_check G' end). rewrite rdn_mrestrict; [exact CCB | clear - HSr Slo Shi CR; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      rewrite at_u by (clear - HSr Slo Shi CR; lia). apply hid_off_of. intros z Hz. split; [clear - Hz HSr Slo Shi CR; lia | apply NHs; [clear - Hz HSr Slo Shi CR; lia | left; clear - Hz Slo; lia]]. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS memD (at_ S (-2512)) 112 = true).
    { replace (at_ S (-2512)) with (Z_to_bv 64 (U S - 2512) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (SOKstkF : store_ok BSEGS memD (at_ S (-2720)) 320 = true).
    { replace (at_ S (-2720)) with (Z_to_bv 64 (U S - 2720) : word) by (clear - HSr Slo Shi CR; apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - Slo CR; lia | clear - HSr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. split.
      - apply (SOK (Z_to_bv 64 z)). clear - Hz HSr Slo CR. unorm. lia.
      - apply NHs; [clear - Hz HSr Slo CR; lia | left; clear - Hz Slo; lia]. }
    assert (SOKRI : store_ok BSEGS memD (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 128 = true).
    { apply (sokX Hd M M0 _ _ _ _ RIW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - SB1 CR Hc; lia | clear - SB0 Hc; lia |].
      intros z Hz. apply NHR. clear - Hz Hc. cbn in Hz. lia. }
    assert (RWlo : SBEG + c * 2 ^ 32 <= ab /\ ab + cs <= SBEG + c * 2 ^ 32 + r_mapped_user (a_reg st c) /\ SBEG + c * 2 ^ 32 + r_mapped_user (a_reg st c) < 2 ^ 64).
    { clear - C1 C2 Q3 Q2 SB1 CR Hc. lia. }
    assert (SOKhdr : store_ok BSEGS memD (Z_to_bv 64 m) 4 = true).
    { apply (sokX Hd M M0 _ _ m 4 RWR GR0); [clear - RWlo Em RZ; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - RWlo Em G5 QR3; lia | clear - RWlo; lia | clear - Mrng; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply OFFm. clear - Hz. lia. }
    assert (SOKab : ab <> m -> store_ok BSEGS memD (Z_to_bv 64 ab) 8 = true).
    { intros NE. apply (sokX Hd M M0 _ _ ab 8 RWR GR0); [clear - RWlo; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - RWlo CS1; lia | clear - RWlo; lia | clear - C3 SB0; lia |].
      (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). intros z Hz. apply NHch. clear - Hz CS1. lia. }
    assert (SHB : 0x2008fff7000 <= 0x7fff8000 + (m + 16) / 8 /\ 0x7fff8000 + (m + 16) / 8 + up8 n / 8 <= 0x10007fff8000).
    { clear - SR3 SR4 Em RZ C3 SBH N8le C4 SB1 CR. lia. }
    assert (SOKsh : store_ok BSEGS memD (Z_to_bv 64 (AsRtPoison.shad (Z_to_bv 64 (m + 16)))) (Z.to_nat (up8 n / 8)) = true).
    { replace (AsRtPoison.shad (Z_to_bv 64 (m + 16))) with (0x7fff8000 + (m + 16) / 8) by (clear - Mrng; (lazymatch goal with |- ?G => let G' := eval unfold AsRtPoison.shad in G in change_no_check G' end); wd_ulia).
      apply sokD; [clear - SHB; lia | rewrite Z2Nat.id by (clear - SR4 U8b; lia); clear - SHB; lia |].
      rewrite Z2Nat.id by (clear - SR4 U8b; lia). intros z Hz. split; [| apply NHsh; exact Hz].
      apply GR0. apply SHM. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_GAPLO, AS_LO, AS_HEAPLO in G in change_no_check G' end). right. clear - Hz SHB. lia. }
    unfold PG in TW.
    assert (SOKT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { apply (sokX Hd M M0 _ _ T _ TW GR0); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | clear - GTC CR; lia | clear - GT0; lia |].
      intros z Hz. apply NHT. clear - Hz. cbn in Hz. lia. }
    (* [comment removed for export] *)
    subst cs.
    set (hdr := [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3]).
    pose proof (bytes_le_to_Z_bound hdr) as Bhv. cbn [length hdr] in Bhv. pose proof (bytes_le_to_Z_nonneg hdr) as Bhv0.
    assert (P_hv : bytes_le_to_Z [Z_to_bv 8 3; Z_to_bv 8 b1; h2; h3] = U (Z_to_bv 64 (bytes_le_to_Z hdr))) by (clear - Bhv Bhv0; unorm; reflexivity).
    assert (P_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - Slo Shi CR; lia).
    assert (P_Gspb : 0x10007fff8000 <= SBEG /\ SBEG + 2 ^ 37 < 2 ^ 47) by (clear - SBH SB1 CR; lia).
    assert (P_Gm : m = SBEG + c * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32 /\ 1 <= c <= 30) by (unfold d in *; clear - Hd32 Hc; lia).
    assert (P_Gm2 : m + 16 + up8 n <= U S - 3584 /\ m mod 16 = 0) by (split; [clear - N8le C4 SB1 Slo; lia | exact M16]).
    assert (P_Gab : SBEG + c * 2 ^ 32 + d / csize c * csize c = m \/ SBEG + c * 2 ^ 32 + d / csize c * csize c + 16 <= m).
    { rewrite Eabm. pose proof (rz_16_32_6 (rz n) RM ltac:(clear - RZ; lia)) as RZC. clear - RZC Em. lia. }
    assert (P_Gab8 : (SBEG + c * 2 ^ 32 + d / csize c * csize c) mod 8 = 0) by (rewrite Eabm; apply mod16_8_6; exact C5).
    assert (P_Grib : AIMGHI <= SBEG + 2 ^ 37 /\ SBEG + 2 ^ 37 + 4096 <= U S - 3584) by (clear - SBH SB1 Slo; lia).
    assert (P_Gau : (d / csize c + 1) * csize c <= r_mapped_user (a_reg st c) /\ r_mapped_user (a_reg st c) < 2 ^ 64) by (rewrite Eidx; clear - Hj1 Q3 RWlo SB0 Hc; lia).
    assert (P_Gn : 1 <= n <= 2 ^ 28) by (clear - QR3 N64; lia).
    assert (P_Gn8 : AsRtRegion.down8 (n + 7) = up8 n /\ n <= up8 n <= n + 7 /\ up8 n mod 8 = 0 /\ 8 <= up8 n) by (split; [apply down8_up8K6 | clear - U8a U8b U8c U8d; lia]).
    assert (P_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584) /\ T mod 16 = 0).
    { split; [exact GT4|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; lia | clear - GTC Slo; lia] | exact T16]. }
    assert (P_GabT : m + 16 + up8 n <= T \/ T + 4096 <= SBEG + c * 2 ^ 32 + d / csize c * csize c) by (rewrite Eabm; clear - SPT N8le C3 C4; lia).
    assert (P_Gctx : 1 <= CTX /\ CTX + 4096 <= U S - 3584) by (clear - GC0 GCC Slo; lia).
    assert (P_Gctxm : CTX + 4096 <= SBEG + c * 2 ^ 32 + d / csize c * csize c \/ m + 16 + up8 n <= CTX) by (rewrite Eabm; clear - SPC N8le C3 C4; lia).
    assert (P_Gctxs : CTX + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX) by (clear - GCB; lia).
    assert (P_Gtp : AIMGLO + 88 <= U (getr R 4) /\ U (getr R 4) + 8 <= AIMGHI) by (rewrite Utp; clear; lia).
    assert (P_Gtsdp : AIMGLO <= U (Z_to_bv 64 TSDP) /\ U (Z_to_bv 64 TSDP) + 8 <= AIMGHI) by (clear - Gc1 Gc2; wd_ulia).
    assert (P_Gspb2 : SBEG + 2 ^ 37 + 4096 <= U S - 3584 /\ SBEG mod 8 = 0) by (split; [clear - SB1 Slo; lia | clear - SB16; Z.div_mod_to_equations; lia]).
    assert (P_GTsp : hideW (T + 4096 <= SBEG \/ SBEG + 2 ^ 37 + 4096 <= T)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact SPT).
    assert (P_cpm1 : U (Z_to_bv 8 CPM) <> 0) by (clear - Gc8; rewrite (Z_to_bv_small 8 CPM ltac:(change (bv_modulus 8) with 256; lia)); lia).
    assert (P_magic : SBEG + c * 2 ^ 32 + d / csize c * csize c <> m -> rdn BSEGS memD (Z_to_bv 64 (SBEG + c * 2 ^ 32 + d / csize c * csize c)) 8 = Some (LE8 (Z_to_bv 64 0xcc6e96b9cc6e96b9))) by (rewrite Eabm; exact K_magic).
    assert (P_okab : SBEG + c * 2 ^ 32 + d / csize c * csize c <> m -> store_ok BSEGS memD (Z_to_bv 64 (SBEG + c * 2 ^ 32 + d / csize c * csize c)) 8 = true) by (rewrite Eabm; exact SOKab).
    (* [comment removed for export] *)
    destruct (rc_item34_run memD (seg_rom BSEGS) R S ret (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 4) (Z_to_bv 64 TSDP)
                m SBEG c d (SBEG + 2 ^ 37) (r_mapped_user (a_reg st c)) n (up8 n) T CTX
                (Z_to_bv 8 b1) h2 h3 (Z_to_bv 64 (bytes_le_to_Z hdr)) (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND) bf0 bf1
                R1 R2 R10 R11 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                P_GS P_Gspb P_Gm P_Gm2 P_Gab P_Gab8 P_Grib P_Gau P_Gn P_Gn8 P_GT P_GabT P_Gctx P_Gctxm P_Gctxs P_Gtp P_Gtsdp
                SOKstk SOKhdr P_okab SOKsh SOKT K_spb K_rib K_au K_magc P_magic K_hdr P_hv eq_refl K_nlo
                K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_cpm P_cpm1 K_kif K_key K_tsdp K_tctx K_thr
                Cf0 Lf0 Cf1 Lf1 K_cache)
      as (r5 & RUN34 & F1 & F2 & F10 & F11 & F12 & F13 & F8 & F9 & F18 & F19 & F20 & F21 & F3 & F4 & F22 & F23 & F24 & F25 & F26 & F27).
    (* [comment removed for export] *)
    rewrite Eabm in RUN34, F13.
    match type of RUN34 with msteps _ _ (mkst _ _ ?mf _) => remember mf as M34r eqn:EM34 end.
    assert (I_GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by exact P_GS.
    assert (I_Gm : 0x10007fff8000 <= ab /\ (ab = m \/ ab + 16 <= m) /\ m + 16 + up8 n <= U S - 3584 /\ m mod 16 = 0).
    { rewrite Eabm in P_Gab. split; [clear - C3 SBH; lia|]. split; [exact P_Gab|]. exact P_Gm2. }
    assert (I_Gn8 : 8 <= up8 n /\ up8 n mod 8 = 0 /\ up8 n <= 2 ^ 40) by (clear - U8b U8c U8d N64; lia).
    assert (I_GT : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)) by (destruct P_GT as (X1 & X2 & _); exact (conj X1 X2)).
    assert (I_GabT : m + 16 + up8 n <= T \/ T + 4096 <= ab) by (rewrite Eabm in P_GabT; exact P_GabT).
    assert (FT0 : forall a : word, M34r a <> memD a ->
              (U S - 2512 <= U a < U S - 2400) \/ (m <= U a < m + 4) \/ (ab <> m /\ ab <= U a < ab + 8)
              \/ (0x7fff8000 + (m + 16) / 8 <= U a < 0x7fff8000 + (m + 16) / 8 + up8 n / 8) \/ (T + 2840 <= U a < T + 2856))
      by (rewrite EM34; apply fr_item34_foot; assumption).
    assert (GRF0 : mem_grows memD M34r) by (rewrite EM34; apply fr_item34_grows).
    assert (FSH0 : forall i, 0 <= i < up8 n / 8 -> M34r (Z_to_bv 64 (0x7fff8000 + (m + 16) / 8 + i)) = Some (Z_to_bv 8 0xfa))
      by (rewrite EM34; apply fr_item34_shadow; assumption).
    idtac "PROGRESS K6p: run A0".
    (* [comment removed for export] *)
    replace (0x4e8a4%bv : word) with (Z_to_bv 64 0x4e8a4 : word) in RUN34 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x4e8a4) M (seg_rom BSEGS)) (@mkst fx r5 (0x4eca8%bv : word) M34r (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact B1. } { exact B2. } { exact HH. } { rewrite restrict_mkstK. exact RUN34. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x4e8a4) M (seg_rom BSEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _).
    set (M1 := munrestrict Hd M M34r).
    assert (VIS : forall a : word, Hd a = false -> M1 a = M34r a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM : forall a : word, Hd a = false -> memD a = M a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GR1 : mem_grows M M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GRF0. rewrite (MrM a Eh). exact Ha. }
    set (P0 := fun z : Z => (m <= z < m + 4) \/ (ab <> m /\ ab <= z < ab + 8)
                            \/ (0x7fff8000 + (m + 16) / 8 <= z < 0x7fff8000 + (m + 16) / 8 + up8 n / 8) \/ (T + 2840 <= z < T + 2856)).
    assert (FOOT1 : forall a : word, M1 a <> M a -> (U S - 2512 <= U a < U S - 2400) \/ P0 (U a)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM a Eh) in NE. exact (FT0 a NE). }
    assert (DEF1 : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE E1. apply NE. rewrite E1. destruct (M a) eqn:E0; [|reflexivity]. exfalso.
      assert (D : M a <> None) by (rewrite E0; discriminate). apply GR1 in D. exact (D E1). }
    assert (P0d : Xdec P0).
    { (lazymatch goal with |- ?G => let G' := eval unfold P0 in G in change_no_check G' end). apply Xdec_or; [apply Xdec_iv|]. apply Xdec_or; [| apply Xdec_or; apply Xdec_iv].
      apply Xdec_and; [| apply Xdec_iv]. intros z. destruct (Z.eq_dec ab m) as [E | N]; [right; intros Q; exact (Q E) | left; exact N]. }
    assert (RX0 : AsAinvOpsRc73.AsAinvRepX3.RepX bt (fun z => X z \/ P0 z) st Lc FF M1 mdl1).
    { apply (repx_call bt BT_ia X P0 st Lc FF M M1 mdl mdl1 qt qg W RX SBM1 MI1).
      intros a NE. split; [| exact (DEF1 a NE)]. destruct (FOOT1 a NE) as [F | F]; [left; clear - F Slo; lia | right; exact F]. }
    (* [comment removed for export] *)
    pose proof (dfull_room bt st Lc FF qt qg c W Hc NFAR0) as ROOM. unfold KFAMAP in ROOM.
    pose proof (BoAllocM8Lcq.BoAllocM8Lkq.pk_thread_geom bt BT_ia st Lc FF qt qg W) as (T1g & T2g & C1g & C2g & T4k & TIMG & CIMG).
    pose proof (BoAllocM8Lcq.BoAllocM8Lkq.pk_thread_geom2 bt st Lc FF qt qg W) as (TBAND & CBAND & TSP & CSP & S1g & S2g & S3g).
    unfold KSPACE, PG, AS_HEAPLO, AS_LO in TBAND, CBAND, TSP, CSP, S1g, S2g, S3g.
    set (mfa := r_mapped_fa (a_reg st c)) in *.
    assert (SLOTg : AS_HEAPLO <= SBEG + c * 2 ^ 32 + 3758096384 + mfa /\ SBEG + c * 2 ^ 32 + 3758096384 + mfa + 2 ^ 18 <= CEIL).
    { (lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end). clear - Q1 Q5 Q6 S2g S3g ROOM Hc. lia. }
    destruct (sh_band (SBEG + c * 2 ^ 32 + 3758096384 + mfa) (2 ^ 18) (proj1 SLOTg) ltac:(clear; lia) (proj2 SLOTg) ltac:(reflexivity)) as (SHB0' & SHB1' & SHB2').
    unfold AS_GAPHI, AS_HEAPLO, SB in SHB0', SHB1', SHB2'.
    assert (SHDIV : (m + 16) / 8 + up8 n / 8 <= (SBEG + c * 2 ^ 32 + 3758096384 + mfa) / 8).
    { assert (LE0 : m + 16 + up8 n <= SBEG + c * 2 ^ 32 + 3758096384 + mfa) by (clear - N8le C2 Q3 Q2 Q6; lia).
      clear - LE0 P8 U8c. Z.div_mod_to_equations. lia. }
    assert (PS : forall z, P0 z -> Yshape bt st c z).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold Yshape in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB, fa_beg, region_beg, KREGION, KFAOFF, KFAMAP in G in change_no_check G' end). fold mfa. unfold P0 in Hz.
      assert (ZN : (SBEG <= z < SBEG + 2 ^ 37 /\ z < SBEG + c * 2 ^ 32 + 3758096384 /\ SBEG + c * 2 ^ 32 <= z)
                   \/ (0x2008fff7000 <= z /\ z < 0x7fff8000 + (SBEG + c * 2 ^ 32 + 3758096384 + mfa) / 8 /\ z < 0x10007fff8000)
                   \/ (T + 2840 <= z < T + 2856)).
      { destruct Hz as [Hz | [Hz | [Hz | Hz]]]; [left; clear - Hz C1 C2 C3 C4 Q2 Q3 Em RZ G5 QR3 Hrz; lia | left; clear - Hz C1 C2 C3 C4 Q2 Q3 CS1; lia
                                                 | right; left; clear - Hz SHB SHDIV; lia | right; right; exact Hz]. }
      clear Hz.
      split; [intros HI; exfalso; destruct ZN as [ZN | [ZN | ZN]]; [clear - HI ZN SBH; lia | clear - HI ZN; lia | clear - HI ZN TIMG; lia]|].
      split; [destruct ZN as [ZN | [ZN | ZN]]; [clear - ZN TSP Hc; lia | clear - ZN TBAND Hc; lia | clear - ZN Hc; lia]|].
      split; [destruct ZN as [ZN | [ZN | ZN]]; [clear - ZN TSP; lia | clear - ZN TBAND; lia | clear - ZN; lia]|].
      split; [destruct ZN as [ZN | [ZN | ZN]]; [clear - ZN TSP; lia | clear - ZN TBAND; lia | clear - ZN; lia]|].
      split; [destruct ZN as [ZN | [ZN | ZN]]; [clear - ZN Hc; lia | clear - ZN S3g Hc; lia | clear - ZN TSP Hc; lia]|].
      split; [destruct ZN as [ZN | [ZN | ZN]]; [clear - ZN CSP; lia | clear - ZN CBAND; lia | clear - ZN GCT'; lia]|].
      split; [destruct ZN as [ZN | [ZN | ZN]]; [clear - ZN; lia | clear - ZN S3g Hc; lia | clear - ZN TSP Q5 Hc; lia]|].
      split; [destruct ZN as [ZN | [ZN | ZN]]; [clear - ZN SHB1' S3g; lia | clear - ZN; lia | clear - ZN TBAND SHB0' SHB1'; lia]|].
      destruct ZN as [ZN | [ZN | ZN]]; [clear - ZN S2g; lia | clear - ZN CR; lia | clear - ZN T2g; lia]. }
    (* [comment removed for export] *)
    replace (0x4eca8%bv : word) with (Z_to_bv 64 0x4eca8 : word) by (apply bv_eq; reflexivity).
    set (e := j * csize c).
    assert (He : 0 <= e < 2 ^ 32) by ((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); clear - JJ JJ0 Hj1 Q3 Q2 CS1; lia).
    assert (SOK1 : forall a : word, U S - 3584 <= U a < U S - 2400 -> M1 a <> None /\ store_ok BSEGS M1 a 1%nat = true).
    { intros a Ha. destruct (SOK a Ha) as [D0 K0]. split; [apply GR1; exact D0 | eapply store_ok_mono; [exact GR1 | exact K0]]. }
    eapply katD_conseq.
    { apply (dfull_map_katD bt TSDP TPm TSDPm PGPm FLm MIDENDm BT_segs BT_ia CELLNB0 RCC0 RCF0 CELLSPIN BOOTG HTPm CELLSM PCELLS QHDR_CONST
               fx X P0 Xd P0d qt qg st Lc FF M1 mdl1 r5 S ret c e).
      - rewrite Eh1. exact HH.
      - exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW).
      - exact W.
      - exact QRK.
      - exact RX0.
      - exact Hc.
      - exact FULL.
      - exact NFAR0.
      - exact CINIT.
      - exact He.
      - exact XSUB.
      - exact PS.
      - exact F1.
      - exact RET.
      - exact F2.
      - exact F10.
      - exact F11.
      - exact F12.
      - rewrite F13. f_equal. (lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end). clear - Eab'. lia.
      - rewrite F4. rewrite ?BT_ia. exact R4.
      - exact Slo.
      - (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). exact Shi.
      - exact SOK1. }
    intros c' POST. cbv zeta in POST.
    set (lo := fa_beg (bt_spacebeg bt) c + r_mapped_fa (a_reg st c)) in *.
    set (st' := add_meter (op_famap st c) 0 [(AsVocab.sh_lo lo, AsVocab.sh_lo lo + KFAMAP / 8)] 0) in *.
    fold mx in POST.
    destruct POST as (Mi & MF & mdlF & RF & -> & HHF & MWF & MIF & W' & FAR' & RXa & FOOTMi & DEFMi & CHG & KEEP & PCNT & PSLOT & LZF & SEVF & RKF).
    idtac "PROGRESS K6p: generic".
    assert (CA' : a_cache st' c = a_cache st c) by reflexivity.
    assert (REG' : a_reg st' c = REG (r_mapped_user (a_reg st c)) (r_alloc_user (a_reg st c)) (r_mapped_fa (a_reg st c) + KFAMAP) (r_free (a_reg st c)) (r_uhole (a_reg st c)) false).
    { (lazymatch goal with |- ?G => let G' := eval unfold st', op_famap, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_reg] in G in change_no_check G' end). apply fupdZ_same. }
    assert (NF' : Z.of_nat (length (r_free (a_reg st' c))) = nf) by (rewrite REG'; reflexivity).
    assert (AL' : forall c0, r_alloc_user (a_reg st' c0) = r_alloc_user (a_reg st c0)).
    { intros c0. (lazymatch goal with |- ?G => let G' := eval unfold st', add_meter, op_famap in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_reg set_reg] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold fupdZ in G in change_no_check G' end). destruct (Z.eqb c0 c) eqn:E; [apply Z.eqb_eq in E; subst c0; reflexivity | reflexivity]. }
    set (st1 := op_drain_top st' c (mx / 2)).
    assert (W1 : WFq bt st1 Lc FF qt qg) by (apply (OPS_WFq_drain_top_pf bt st' Lc FF c (mx / 2) qt qg W' Hc); [rewrite CA'; clear - LEN DF; lia | exact FAR']).
    assert (GQ1 : a_gq st1 = a_gq st) by reflexivity.
    assert (CA1 : a_cache st1 c = firstn (Z.to_nat (Z.of_nat (length (a_cache st' c)) - mx / 2)) (a_cache st' c)).
    { (lazymatch goal with |- ?G => let G' := eval unfold st1, op_drain_top in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_cache set_cache set_reg] in G in change_no_check G' end). apply fupdZ_same. }
    assert (LEN1 : Z.of_nat (length (a_cache st1 c)) = mx - mx / 2) by (rewrite CA1, CA', length_firstn; clear - LEN DF; lia).
    set (k := compact_of SBEG c ab).
    assert (Ek : k = j * csize c / 16).
    { (lazymatch goal with |- ?G => let G' := eval unfold k, compact_of, region_beg, KREGION in G in change_no_check G' end). f_equal. clear - Eab'. lia. }
    assert (Ek0 : k = compact_of SBEG c (prim_alloc_beg (m + 16) n)) by (rewrite <- Eab0; reflexivity).
    assert (EGQ1 : a_gq st1 = BATCH ba ((m, n) :: its) :: rest) by (rewrite GQ1; exact EGQ).
    assert (XSUB1 : forall z, X z -> XB bt st1 z) by (intros z Hz; apply XB_drain_top; apply XB_famap_meter; exact (XSUB z Hz)).
    assert (ROOM1 : Z.of_nat (length (a_cache st1 c)) < cache_max c) by (rewrite LEN1; fold mx; clear - DF; lia).
    assert (GRF : mem_grows M1 MF).
    { intros a Ha. destruct (decide (MF a = M1 a)) as [E | N]; [rewrite E; exact Ha | exact (proj2 (CHG a N))]. }
    assert (MDEFT : forall a : word, T <= U a < T + 4096 -> M a <> None).
    { intros a Ha. apply GR0. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (writableZ_def M0 _ _ _ TW). exact Ha. }
    assert (HFA : forall a : word, MF a <> mid_mem bt st' c (mx / 2) Mi MF a -> foot_recycle_prim bt st1 m n c (U a) /\ MF a <> None).
    { intros a NE. (lazymatch goal with |- ?G => let G' := eval unfold foot_recycle_prim in G in change_no_check G' end). rewrite <- Eab0. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). rewrite <- SHhi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end). rewrite LEN1.
      destruct (mid_mem_diff bt st' Lc FF qt qg c (mx / 2) W' Hc ltac:(clear - DF; lia) FAR' Mi MF a NE) as [I | [NE' NFd]].
      - unfold T_PC, PC_SZ in I. split; [right; right; left; exact I | apply GRF; apply GR1; apply MDEFT; clear - I Hc; lia].
      - split; [| exact (DEFMi a NE')].
        destruct (FOOTMi a NE') as [F | F].
        + unfold FOOTC in F. cbv zeta in F. fold mx nf in F. destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]].
          * do 5 right. clear - F Slo. lia.
          * right; right; left. clear - F. lia.
          * right; right; right; left. clear - F. lia.
          * do 4 right. left. clear - F. lia.
          * exfalso. apply NFd. (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end). left. exact F.
          * exfalso. apply NFd. (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end). right; left. exact F.
          * exfalso. apply NFd. (lazymatch goal with |- ?G => let G' := eval unfold Fdr, reginfo, KSPACE in G in change_no_check G' end). right; right; left. clear - F. lia.
          * exfalso. apply NFd. (lazymatch goal with |- ?G => let G' := eval unfold Fdr, fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end). rewrite NF'. do 3 right. clear - F. lia.
        + unfold P0 in F. destruct F as [F|[F|[F|F]]].
          * left. clear - F Em RZ G5 QR3. lia.
          * left. clear - F CS1. lia.
          * right; left. clear - F. lia.
          * do 4 right. left. clear - F. lia. }
    assert (RX1 : AsAinvOpsRc73.AsAinvRepX3.RepX bt X (op_recycle_prim st1 c k) Lc FF MF mdlF).
    { apply (OPS_REPX_recycle_prim_pf bt X Xd st1 Lc FF (mid_mem bt st' c (mx / 2) Mi MF) MF mdlF mdlF ba m n its rest c k qt qg W1 RXa EGQ1 HP Ec Ek0 ROOM1 XSUB1 XQ XOBJ).
      - intros a Ha. apply GRF. apply GR1. exact (QDEF a Ha).
      - intros a NE. destruct (HFA a NE) as [F D]. split; [left; exact F | exact D].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). rewrite LEN1. exact PCNT.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). rewrite LEN1, Ek. exact PSLOT.
      - intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end). rewrite w2b1 by (clear; lia).
        rewrite <- SHhi in Hi. unfold sh_lo, SB in Hi.
        apply heap_rdn1; [clear - Hi SHB; wd_ulia|].
        assert (Ei : U (Z_to_bv 64 i : word) = i) by (clear - Hi SHB; wd_ulia).
        rewrite (KEEP (Z_to_bv 64 i)) by (left; right; (lazymatch goal with |- ?G => let G' := eval unfold P0 in G in change_no_check G' end); rewrite Ei; right; right; left; exact Hi).
        rewrite VIS by (apply NHsh; exact Hi).
        replace i with (0x7fff8000 + (m + 16) / 8 + (i - (0x7fff8000 + (m + 16) / 8))) by (clear; lia). apply FSH0. clear - Hi. lia.
      - apply same_but_materialized_refl.
      - exact MIF. }
    idtac "PROGRESS K6p: RX1".
    assert (NOX0 : forall a : word, M1 a <> M a -> ~ X (U a) /\ U a < U S - 2400).
    { intros a NE. destruct (FOOT1 a NE) as [F | F]; [| unfold P0 in F; destruct F as [F|[F|[F|F]]]].
      - split; [| clear - F; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q Slo CR; lia | clear - F Q SB1 Slo; lia].
      - split; [apply XCH; clear - F Em RZ G5 QR3; lia | clear - F P_Gm2 U8b; lia].
      - split; [apply XCH; clear - F CS1; lia | clear - F I_Gm U8b; lia].
      - split; [| clear - F SHB Slo CR; lia]. intros Hx. destruct (XZ _ Hx) as [Q|Q]; [clear - F Q SHB; lia | clear - F Q SHB SBH; lia].
      - split; [apply (OFFT (U a)); clear - F; lia | clear - F GTC Slo; lia]. }
    assert (TC : touchable bt st c) by exact (touchable_carved bt st c ab Hc CVc).
    assert (TC' : touchable bt st' c) by exact (touchable_alloc bt st st' c AL' TC).
    (lazymatch goal with |- ?G => let G' := eval unfold rc_step_post in G in change_no_check G' end). exists fx, (op_recycle_prim st1 c k), MF, mdlF, RF.
    split; [reflexivity|]. split; [exact HFX|]. split; [exact HHF|]. split; [exact MWF|].
    split; [exact (OPS_WFq_recycle_prim_pf bt st1 Lc FF ba m n its rest c k qt qg W1 EGQ1 HP Ec Ek0 ROOM1)|].
    split; [exact RX1|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ1; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ1; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end); rewrite EGQ1; (lazymatch goal with |- ?G => let G' := eval unfold st1, op_drain_top, st', add_meter in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_kact op_cache_push set_cache set_gq set_reg] in G in change_no_check G' end); apply Z.add_0_r|].
    split.
    { split; [| exact (fk_trans _ _ _ (fk_famap_meter bt st c _ TC)
                          (fk_trans _ _ _ (fk_drain_top bt st' c (mx / 2) TC')
                                          (fk_recycle_prim_at bt st1 c k (touchable_alloc bt st' st1 c (fun c0 => alloc_drain_top st' c (mx / 2) c0) TC'))))].
      intros h HL. unfold holes_le in *. (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_prim, op_qitem in G in change_no_check G' end). rewrite EGQ1. (lazymatch goal with |- ?G => let G' := eval cbn [a_reg op_cache_push set_cache set_gq] in G in change_no_check G' end). intros c' Hc'. apply HL.
      unfold st1, op_drain_top, st', add_meter, op_famap in Hc'. cbn [a_reg set_cache set_reg] in Hc'. unfold fupdZ in Hc'.
      destruct (Z.eqb c' c) eqn:E; [apply Z.eqb_eq in E; subst c'; rewrite ?Z.eqb_refl in Hc'; cbn [r_uhole r_fhole] in Hc'; destruct Hc' as [H | H]; [left; exact H | discriminate H] | exact Hc']. }
    split; [intros z Hz; exact (XB_recycle_prim bt st1 ba (m, n) its rest c k z EGQ1 (XSUB1 z Hz))|].
    split.
    { intros a Ha. transitivity (M1 a).
      - apply KEEP. destruct Ha as [Ha | Ha]; [left; left; exact Ha | right; exact Ha].
      - destruct (decide (M1 a = M a)) as [E|NE]; [exact E|]. exfalso. destruct (NOX0 a NE) as [N1 N2].
        destruct Ha as [Ha|Ha]; [exact (N1 Ha) | clear - Ha N2; lia]. }
    split.
    { intros a NE. destruct (decide (MF a = M1 a)) as [E | N]; [| destruct (CHG a N) as [C D]; exact (conj C (or_introl D))].
      rewrite E in NE |- *. split; [| left; exact (DEF1 a NE)]. (lazymatch goal with |- ?G => let G' := eval unfold rc_changed in G in change_no_check G' end).
      destruct (FOOT1 a NE) as [F | F]; [| unfold P0 in F; destruct F as [F|[F|[F|F]]]].
      - left. clear - F. lia.
      - right; left. apply (quar_prim_private bt st Lc FF W m n (U a) Hq HP). rewrite <- Eab0, <- Ec. clear - F Em RZ G5 QR3. lia.
      - right; left. apply (quar_prim_private bt st Lc FF W m n (U a) Hq HP). rewrite <- Eab0, <- Ec. clear - F CS1. lia.
      - right; left. apply (quar_prim_shadow_private bt st Lc FF W m n (U a) Hq HP). rewrite <- SHhi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end). clear - F. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W (U a)). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia. }
    split.
    { intros a Ha. transitivity (lzb mdl1 a); [exact (LZF a Ha) | (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity]. }
    split; [exact (same_except_vm_trans _ _ _ (same_but_materialized_except_vm _ _ SBM1) SEVF)|].
    assert (KR : forall (r : bv 5), existsb (Z.eqb (bv_unsigned r)) as_callee_saved = true -> getr RF r = getr r5 r) by (intros r Hr; exact (regs_kept_litK r5 RF r RKF Hr)).
    apply regs_kept_intro;
      [ rewrite (KR 2%bv eq_refl), F2; symmetry; exact R2 | rewrite (KR 3%bv eq_refl); exact F3 | rewrite (KR 4%bv eq_refl); exact F4
      | rewrite (KR 8%bv eq_refl); exact F8 | rewrite (KR 9%bv eq_refl); exact F9 | rewrite (KR 18%bv eq_refl); exact F18 | rewrite (KR 19%bv eq_refl); exact F19
      | rewrite (KR 20%bv eq_refl); exact F20 | rewrite (KR 21%bv eq_refl); exact F21 | rewrite (KR 22%bv eq_refl); exact F22 | rewrite (KR 23%bv eq_refl); exact F23
      | rewrite (KR 24%bv eq_refl); exact F24 | rewrite (KR 25%bv eq_refl); exact F25 | rewrite (KR 26%bv eq_refl); exact F26 | rewrite (KR 27%bv eq_refl); exact F27 ].
  Qed.
End K6P.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
(* [comment removed for export] *)
Ltac anc_and F D val := an F D; try match goal with |- context [v_and ?x ?y] => replace (v_and x y) with val by (apply bv_eq; vm_compute; reflexivity) end.
Ltac anc_or F D val := an F D; try match goal with |- context [v_or ?x ?y] => replace (v_or x y) with val by (apply bv_eq; vm_compute; reflexivity) end.
Ltac pc4 := apply bv_eq; reflexivity.

(* [comment removed for export] *)
Lemma lock_cas_4f29c : forall regs mem rom (ri : word) (newv : word),
  getr regs 8 = ri -> getr regs 13 = Z_to_bv 64 0 -> getr regs 15 = newv -> (bv_unsigned ri mod 8 = 0)%Z ->
  rdn BSEGS mem ri 8 = Some (LE8 (Z_to_bv 64 0)) -> store_ok BSEGS mem ri 8 = true ->
  msteps BSEGS (mkst regs (0x4f29c : word) mem rom)
    (mkst (regupd (regupd regs 14 (Z_to_bv 64 0)) 16 (Z_to_bv 64 0)) (0x4f2ac : word) (wbytes mem ri (LE8 newv)) rom).
Proof using.
  intros regs mem rom ri newv H8 H13 H15 Hal Hrd Hok.
  pose proof (cas_d_run BSEGS regs (0x4f29c : word) (0x4f2a0 : word) (0x4f2a4 : word) (0x4f2a8 : word) (0x4f2ac : word) mem rom
                _ _ _ _ _ _ _ _ 14 8 16 15 14 13 _ _ _ (LE8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
                F_4f29c eq_refl D_4f29c F_4f2a0 eq_refl D_4f2a0 F_4f2a4 eq_refl D_4f2a4 F_4f2a8 eq_refl D_4f2a8) as R.
  rewrite H8 in R.
  replace (getr (regupd regs 14 (Z_to_bv 64 0)) 15) with newv in R by (gres; rewrite H15; reflexivity).
  apply R; clear R; first [regneq | pc4 | exact Hal | exact Hrd | apply bytes_le_to_Z_8 | exact Hok | idtac].
  (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end). gres. rewrite H13. rewrite bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fr_rta0 (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (RIz : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2520)) (LE8 ra0))
    (at_ S (-2528)) (LE8 s0v))
    (at_ S (-2536)) (LE8 s1v))
    (at_ S (-2544)) (LE8 s2v))
    (at_ S (-2552)) (LE8 s3v))
    (at_ S (-2560)) (LE8 s4v))
    (at_ S (-2568)) (LE8 s5v))
    (at_ S (-2576)) (LE8 s6v))
    (at_ S (-2584)) (LE8 s7v))
    (at_ S (-2592)) (LE8 s8v))
    (at_ S (-2600)) (LE8 s9v))
    (at_ S (-2608)) (LE8 s10v))
    (at_ S (-2616)) (LE8 s11v))
    (at_ S (-2624)) (LE8 (Z_to_bv 64 (RIz + 8))))
    (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 (2 ^ 60))).
#[local] Hint Unfold fr_rta0 : asfr.

Section RTA1.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v mapv : word).
  Variables (spb rib c chp n nf : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation RIz := (rib + 128 * c)%Z.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2512).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H11 : getr regs 11 = mapv.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 c.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 chp.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 n.
  Hypothesis H8 : getr regs 8 = s0v.    Hypothesis H9 : getr regs 9 = s1v.    Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.  Hypothesis H20 : getr regs 20 = s4v.  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v.  Hypothesis H23 : getr regs 23 = s7v.  Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v.  Hypothesis H26 : getr regs 26 = s10v. Hypothesis H27 : getr regs 27 = s11v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hrib : (AIMGHI <= rib /\ rib + 4096 <= bv_unsigned S - 3584 /\ rib mod 8 = 0)%Z.
  Hypothesis Hn : (0 <= n < 2 ^ 32)%Z.
  Hypothesis Hnf : (0 <= nf < 2 ^ 32)%Z.
  Hypothesis Hchp : (0 <= chp < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2640)) 128 = true.
  Hypothesis Hokri : store_ok BSEGS mem (Z_to_bv 64 RIz) 8 = true.
  Hypothesis Rspb : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis Rrib : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 48)) 8 = Some (LE8 (Z_to_bv 64 rib)).
  Hypothesis Rmu : rdn BSEGS mem (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rnf : rdn BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).

  #[local] Abbreviation M0 := (fr_rta0 mem S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v RIz).

  (* [comment removed for export] *)
  Definition rta_regs (r : bvmap 5 word) : Prop :=
    getr r 2 = at_ S (-2640) /\ getr r 8 = Z_to_bv 64 RIz /\ getr r 18 = Z_to_bv 64 c /\ getr r 19 = mapv /\ getr r 20 = Z_to_bv 64 0x10ab58
    /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = Z_to_bv 64 chp /\ getr r 24 = Z_to_bv 64 (2 ^ 61)
    /\ getr r 25 = Z_to_bv 64 (spb + c * 2 ^ 32 + 0xE0000000)
    /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4.

  Lemma rta_lock :
    exists r, msteps BSEGS (mkst regs (0x4f1e0 : word) mem rom) (mkst r (0x4f508 : word) M0 rom)
      /\ rta_regs r /\ getr r 1 = Z_to_bv 64 0x4f344 /\ getr r 10 = Z_to_bv 64 0x10ab58 /\ getr r 11 = Z_to_bv 64 RIz
      /\ getr r 12 = Z_to_bv 64 (spb + c * 2 ^ 32) /\ getr r 13 = Z_to_bv 64 (nf + n)
      /\ getr r 9 = Z_to_bv 64 nf /\ getr r 23 = Z_to_bv 64 (nf + n).
  Proof using Rnf Rmu Rrib Rspb Hokri Hstk Hnf Hn Hrib Hspb Hc HS H27 H26 H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H15 H14 H13 H11 H10 H2 H1.
    (lazymatch goal with |- ?G => let G' := eval unfold rta_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. destruct Hrib as (Hr1 & Hr2 & Hr8).
    assert (Hal8 : ((rib + 128 * c) mod 8 = 0)%Z) by (clear - Hr8; Z.div_mod_to_equations; lia).
    wd_eexists. split.
    - an F_4f1e0 D_4f1e0.                              (* [comment removed for export] *)
      fsd F_4f1e4 D_4f1e4 (at_ S (-2520)).             (* [comment removed for export] *)
      fsd F_4f1e8 D_4f1e8 (at_ S (-2528)).
      fsd F_4f1ec D_4f1ec (at_ S (-2536)).
      fsd F_4f1f0 D_4f1f0 (at_ S (-2544)).
      fsd F_4f1f4 D_4f1f4 (at_ S (-2552)).
      fsd F_4f1f8 D_4f1f8 (at_ S (-2560)).
      fsd F_4f1fc D_4f1fc (at_ S (-2568)).
      fsd F_4f200 D_4f200 (at_ S (-2576)).
      fsd F_4f204 D_4f204 (at_ S (-2584)).
      fsd F_4f208 D_4f208 (at_ S (-2592)).
      fsd F_4f20c D_4f20c (at_ S (-2600)).
      fsd F_4f210 D_4f210 (at_ S (-2608)).
      fsd F_4f214 D_4f214 (at_ S (-2616)).
      an F_4f218 D_4f218.                              (* [comment removed for export] *)
      an F_4f21c D_4f21c.                              (* [comment removed for export] *)
      an F_4f220 D_4f220.                              (* [comment removed for export] *)
      an F_4f224 D_4f224.                              (* [comment removed for export] *)
      an F_4f228 D_4f228.                              (* [comment removed for export] *)
      an F_4f22c D_4f22c.                              (* [comment removed for export] *)
      an F_4f230 D_4f230.                              (* [comment removed for export] *)
      cld8 F_4f234 D_4f234 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      cld8 F_4f238 D_4f238 (Z_to_bv 64 rib) Rrib.      (* [comment removed for export] *)
      av F_4f23c D_4f23c (Z_to_bv 64 (128 * c)) ltac:(valz).          (* [comment removed for export] *)
      av F_4f240 D_4f240 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia).   (* [comment removed for export] *)
      an F_4f244 D_4f244.                              (* [comment removed for export] *)
      an F_4f248 D_4f248.                              (* [comment removed for export] *)
      av F_4f24c D_4f24c (Z_to_bv 64 (2 ^ 61)) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av F_4f250 D_4f250 (Z_to_bv 64 0xE0000000) ltac:(apply bv_eq; reflexivity). (* [comment removed for export] *)
      av F_4f254 D_4f254 (Z_to_bv 64 (2 ^ 40)) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av F_4f258 D_4f258 (Z_to_bv 64 (2 ^ 40 + 1)) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av F_4f25c D_4f25c (Z_to_bv 64 (2 ^ 60 + 2 ^ 20)) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av F_4f260 D_4f260 (Z_to_bv 64 RIz) ltac:(valz).  (* [comment removed for export] *)
      av F_4f264 D_4f264 (Z_to_bv 64 (spb + c * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      av F_4f268 D_4f268 (Z_to_bv 64 (2 ^ 60 + 2 ^ 20 - 1)) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av F_4f26c D_4f26c (Z_to_bv 64 (spb + c * 2 ^ 32 + 0xE0000000)) ltac:(valz).   (* [comment removed for export] *)
      cld8 F_4f270 D_4f270 (Z_to_bv 64 0) Rmu.         (* [comment removed for export] *)
      av F_4f274 D_4f274 (Z_to_bv 64 (RIz + 8)) ltac:(valz).   (* [comment removed for export] *)
      fsd F_4f278 D_4f278 (at_ S (-2624)).             (* [comment removed for export] *)
      av F_4f27c D_4f27c (Z_to_bv 64 (2 ^ 60)) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      an F_4f280 D_4f280.                              (* [comment removed for export] *)
      an F_4f284 D_4f284.                              (* [comment removed for export] *)
      an F_4f288 D_4f288.                              (* [comment removed for export] *)
      anc_and F_4f28c D_4f28c (Z_to_bv 64 0).          (* [comment removed for export] *)
      ab_ft F_4f290 D_4f290 ltac:(condz).              (* [comment removed for export] *)
      anc_or F_4f294 D_4f294 (Z_to_bv 64 (2 ^ 60)).    (* [comment removed for export] *)
      anc_and F_4f298 D_4f298 (Z_to_bv 64 (2 ^ 60)).   (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (lock_cas_4f29c _ _ rom (Z_to_bv 64 RIz) (Z_to_bv 64 (2 ^ 60)));
          [ gres; rwH; reflexivity | gres; rwH; reflexivity | gres; rwH; reflexivity | unorm; exact Hal8 | rd_addr Rmu | any_ok ]
      | ].
      ab_tk F_4f2ac D_4f2ac ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4f32c D_4f32c (Z_to_bv 64 nf) Rnf.        (* [comment removed for export] *)
      av F_4f330 D_4f330 (Z_to_bv 64 (nf + n)) ltac:(valz).   (* [comment removed for export] *)
      an F_4f334 D_4f334.                              (* [comment removed for export] *)
      an F_4f338 D_4f338.                              (* [comment removed for export] *)
      an F_4f33c D_4f33c.                              (* [comment removed for export] *)
      an F_4f340 D_4f340.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0. wd_refl.
    - post.
  Qed.
End RTA1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint fa_fill (m : word -> option byte) (a : Z) (ks : list Z) : word -> option byte :=
  match ks with [] => m | k :: r => fa_fill (wbytes m (Z_to_bv 64 a) (LE4 k)) (a + 4)%Z r end.

Definition cp_keep (r r' : bvmap 5 word) : Prop :=
  getr r' 1 = getr r 1 /\ getr r' 2 = getr r 2 /\ getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4 /\ getr r' 8 = getr r 8 /\ getr r' 9 = getr r 9
  /\ getr r' 10 = getr r 10 /\ getr r' 18 = getr r 18 /\ getr r' 19 = getr r 19 /\ getr r' 20 = getr r 20 /\ getr r' 21 = getr r 21
  /\ getr r' 23 = getr r 23 /\ getr r' 24 = getr r 24 /\ getr r' 26 = getr r 26 /\ getr r' 27 = getr r 27.

Lemma rta_copy_loop : forall (ks : list Z) (regs : bvmap 5 word) (mem rom : word -> option byte) (src dst : Z),
  ks <> [] -> getr regs 22 = Z_to_bv 64 src -> getr regs 25 = Z_to_bv 64 dst -> getr regs 10 = Z_to_bv 64 (src + 4 * Z.of_nat (length ks)) ->
  (0 <= src /\ src + 4 * Z.of_nat (length ks) < 2 ^ 63)%Z -> (0 <= dst /\ dst + 4 * Z.of_nat (length ks) < 2 ^ 63)%Z ->
  (src + 4 * Z.of_nat (length ks) <= dst \/ dst + 4 * Z.of_nat (length ks) <= src)%Z ->
  Forall (fun k => (0 <= k < 2 ^ 31)%Z) ks ->
  (forall i k, nth_error ks i = Some k -> rdn BSEGS mem (Z_to_bv 64 (src + 4 * Z.of_nat i)) 4 = Some (LE4 k)) ->
  store_ok BSEGS mem (Z_to_bv 64 dst) (4 * length ks) = true ->
  exists r, msteps BSEGS (mkst regs (0x4f35c : word) mem rom) (mkst r (0x4f370 : word) (fa_fill mem dst ks) rom) /\ cp_keep regs r.
Proof using.
  induction ks as [|k ks IH]; intros regs mem rom src dst NE H22 H25 H10 Hsrc Hdst Hdisj Hks Hcells Hok; [exfalso; exact (NE eq_refl)|].
  apply Forall_cons_iff in Hks as [Hk Hks]. cbn [length] in *.
  pose proof (Hcells 0%nat k eq_refl) as C0. replace (src + 4 * Z.of_nat 0)%Z with src in C0 by lia.
  assert (V0 : bytes_le_to_Z (LE4 k) = bv_unsigned (Z_to_bv 64 k)) by (apply bytes4_small; lia).
  assert (Hok4 : store_ok BSEGS mem (Z_to_bv 64 dst) 4 = true).
  { eapply (store_ok_sub BSEGS mem (Z_to_bv 64 dst) _ (4 * Datatypes.S (length ks))); [wd_ulia | exact Hok | lia | wd_ulia]. }
  destruct ks as [|k' ks'].
  - (* [comment removed for export] *)
    cbn [length] in *. replace (src + 4 * Z.of_nat 1)%Z with (src + 4)%Z in H10 by lia.
    wd_eexists. split.
    + clw F_4f35c D_4f35c (LE4 k) (Z_to_bv 64 k) C0 V0.     (* [comment removed for export] *)
      rewrite (v_lw_small k) by lia.
      av F_4f360 D_4f360 (Z_to_bv 64 (src + 4)) ltac:(valz).   (* [comment removed for export] *)
      fsw F_4f364 D_4f364 (Z_to_bv 64 dst).                  (* [comment removed for export] *)
      av F_4f368 D_4f368 (Z_to_bv 64 (dst + 4)) ltac:(valz).   (* [comment removed for export] *)
      ab_ft F_4f36c D_4f36c ltac:(condz).                    (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval cbn [fa_fill] in G in change_no_check G' end). wd_refl.
    + (lazymatch goal with |- ?G => let G' := eval unfold cp_keep in G in change_no_check G' end). post.
  - (* [comment removed for export] *)
    cbn [length] in *.
    assert (HN : (0 <= Z.of_nat (length ks'))%Z) by lia.
    replace (src + 4 * Z.of_nat (Datatypes.S (Datatypes.S (length ks'))))%Z with (src + 4 * (Z.of_nat (length ks') + 2))%Z in H10 by lia.
    assert (STEP : exists r1, msteps BSEGS (mkst regs (0x4f35c : word) mem rom) (mkst r1 (0x4f35c : word) (wbytes mem (Z_to_bv 64 dst) (LE4 k)) rom)
                     /\ cp_keep regs r1 /\ getr r1 22 = Z_to_bv 64 (src + 4) /\ getr r1 25 = Z_to_bv 64 (dst + 4)).
    { wd_eexists. split.
      + clw F_4f35c D_4f35c (LE4 k) (Z_to_bv 64 k) C0 V0.
        rewrite (v_lw_small k) by lia.
        av F_4f360 D_4f360 (Z_to_bv 64 (src + 4)) ltac:(valz).
        fsw F_4f364 D_4f364 (Z_to_bv 64 dst).
        av F_4f368 D_4f368 (Z_to_bv 64 (dst + 4)) ltac:(valz).
        ab_tk F_4f36c D_4f36c ltac:(condz).                  (* [comment removed for export] *)
        wd_refl.
      + (lazymatch goal with |- ?G => let G' := eval unfold cp_keep in G in change_no_check G' end). post. }
    destruct STEP as (r1 & RUN1 & KP1 & E22 & E25).
    pose proof KP1 as (K1 & K2 & K3 & K4 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K23 & K24 & K26 & K27).
    destruct (IH r1 (wbytes mem (Z_to_bv 64 dst) (LE4 k)) rom (src + 4)%Z (dst + 4)%Z ltac:(discriminate) E22 E25) as (r2 & RUN2 & KP2).
    + rewrite K10, H10. f_equal. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    + (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    + (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    + (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    + exact Hks.
    + intros i ki Hi.
      assert (Li : (Z.of_nat i < Z.of_nat (length ks') + 1)%Z).
      { pose proof (nth_error_Some (k' :: ks') i) as NS. rewrite Hi in NS. assert (L0 : (i < length (k' :: ks'))%nat) by (apply NS; discriminate). cbn [length] in L0. lia. }
      rewrite rdn_wbytes_out; [| rewrite length_N_to_le_bytes; wd_ulia | wd_ulia | rewrite length_N_to_le_bytes; wd_ulia].
      replace (src + 4 + 4 * Z.of_nat i)%Z with (src + 4 * Z.of_nat (Datatypes.S i))%Z by lia. exact (Hcells (Datatypes.S i) ki Hi).
    + eapply store_ok_mono; [apply wbytes_grows|].
      eapply (store_ok_sub BSEGS mem (Z_to_bv 64 dst) _ (4 * Datatypes.S (Datatypes.S (length ks')))); [wd_ulia | exact Hok | wd_ulia | wd_ulia].
    + exists r2. split; [eapply msteps_trans; [exact RUN1 | (lazymatch goal with |- ?G => let G' := eval cbn [fa_fill] in G in change_no_check G' end); exact RUN2]|].
      destruct KP2 as (L1 & L2 & L3 & L4 & L8 & L9 & L10 & L18 & L19 & L20 & L21 & L23 & L24 & L26 & L27).
      (lazymatch goal with |- ?G => let G' := eval unfold cp_keep in G in change_no_check G' end). repeat split; etransitivity; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_rtac (mem : word -> option byte) (RIz nfn : Z) (w80 : word) : word -> option byte :=
  wbytes (wbytes mem (Z_to_bv 64 (RIz + 16)) (LE8 (Z_to_bv 64 nfn))) (Z_to_bv 64 (RIz + 80)) (LE8 w80).
#[local] Hint Unfold fr_rtac : asfr.

Section RTA2.
  Variables (mem rom : word -> option byte) (S mapv : word) (RIz c chp n nf fa : Z) (b80 : list byte).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2640).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 RIz.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 nf.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 c.
  Hypothesis H19 : getr regs 19 = mapv.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 0x10ab58.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 n.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 chp.
  Hypothesis H23 : getr regs 23 = Z_to_bv 64 (nf + n).
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 fa.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hn : (1 <= n < 2 ^ 28)%Z.
  Hypothesis Hnf : (0 <= nf < 2 ^ 32)%Z.
  Hypothesis Hchp : (0 <= chp /\ chp + 4 * n < 2 ^ 63)%Z.
  Hypothesis Hfa : (0 <= fa /\ fa + 4 * nf + 4 * n < 2 ^ 63)%Z.

  (* [comment removed for export] *)
  Lemma rta_to_copy : getr regs 10 = Z_to_bv 64 1 ->
    exists r, msteps BSEGS (mkst regs (0x4f344 : word) mem rom) (mkst r (0x4f35c : word) mem rom)
      /\ getr r 22 = Z_to_bv 64 chp /\ getr r 25 = Z_to_bv 64 (fa + 4 * nf) /\ getr r 10 = Z_to_bv 64 (chp + 4 * n)
      /\ getr r 1 = getr regs 1 /\ getr r 2 = getr regs 2 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 8 = getr regs 8
      /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hfa Hchp Hnf Hn H25 H23 H22 H21 H20 H19 H18 H9 H8 H2 c RIz mapv S.
    intros H10. pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - ab_ft F_4f344 D_4f344 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_4f348 D_4f348 ltac:(condz).              (* [comment removed for export] *)
      av F_4f34c D_4f34c (Z_to_bv 64 (4 * nf)) ltac:(valz).      (* [comment removed for export] *)
      av F_4f350 D_4f350 (Z_to_bv 64 (fa + 4 * nf)) ltac:(valz). (* [comment removed for export] *)
      av F_4f354 D_4f354 (Z_to_bv 64 (4 * n)) ltac:(valz).       (* [comment removed for export] *)
      av F_4f358 D_4f358 (Z_to_bv 64 (chp + 4 * n)) ltac:(valz). (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hb80 : length b80 = 8%nat.
  Hypothesis R80 : rdn BSEGS mem (Z_to_bv 64 (RIz + 80)) 8 = Some b80.
  Hypothesis Hok : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  #[local] Abbreviation w80 := (v_add (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 n)).
  Lemma rta_counters :
    exists r, msteps BSEGS (mkst regs (0x4f370 : word) mem rom) (mkst r (0x4f688 : word) (fr_rtac mem RIz (nf + n) w80) rom)
      /\ getr r 1 = Z_to_bv 64 0x4f394 /\ getr r 10 = Z_to_bv 64 0x10ab58 /\ getr r 11 = mapv /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = Z_to_bv 64 0
      /\ getr r 2 = getr regs 2 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 8 = getr regs 8
      /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hok R80 Hb80 HRI HS H23 H21 H20 H19 H18 H8 H2 S.
    pose proof (u64_range S) as HSr.
    pose proof (bytes_le_to_Z_bound b80) as B80. rewrite Hb80 in B80. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B80.
    pose proof (bytes_le_to_Z_nonneg b80) as B80'.
    assert (V80 : bytes_le_to_Z b80 = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z b80))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (OK16 : store_ok BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = true).
    { eapply (store_ok_sub BSEGS mem (Z_to_bv 64 RIz) _ 128); [wd_ulia | exact Hok | wd_ulia | wd_ulia_c]. }
    assert (OK80 : store_ok BSEGS (wbytes mem (Z_to_bv 64 (RIz + 16)) (LE8 (Z_to_bv 64 (nf + n)))) (Z_to_bv 64 (RIz + 80)) 8 = true).
    { eapply store_ok_mono; [apply wbytes_grows|]. eapply (store_ok_sub BSEGS mem (Z_to_bv 64 RIz) _ 128); [wd_ulia | exact Hok | wd_ulia | wd_ulia_c]. }
    wd_eexists. split.
    - cld F_4f370 D_4f370 b80 (Z_to_bv 64 (bytes_le_to_Z b80)) R80 V80.   (* [comment removed for export] *)
      fsd F_4f374 D_4f374 (Z_to_bv 64 (RIz + 16)).     (* [comment removed for export] *)
      an F_4f378 D_4f378.                              (* [comment removed for export] *)
      fsd F_4f37c D_4f37c (Z_to_bv 64 (RIz + 80)).     (* [comment removed for export] *)
      an F_4f380 D_4f380.                              (* [comment removed for export] *)
      an F_4f384 D_4f384.                              (* [comment removed for export] *)
      an F_4f388 D_4f388.                              (* [comment removed for export] *)
      an F_4f38c D_4f38c.                              (* [comment removed for export] *)
      an F_4f390 D_4f390.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End RTA2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unlock_cas_4f3d0 : forall regs mem rom (ri : word),
  getr regs 8 = ri -> getr regs 10 = Z_to_bv 64 (2 ^ 60) -> getr regs 5 = Z_to_bv 64 0 -> (bv_unsigned ri mod 8 = 0)%Z ->
  rdn BSEGS mem ri 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))) -> store_ok BSEGS mem ri 8 = true ->
  msteps BSEGS (mkst regs (0x4f3d0 : word) mem rom)
    (mkst (regupd (regupd regs 6 (Z_to_bv 64 (2 ^ 60))) 7 (Z_to_bv 64 0)) (0x4f3e0 : word) (wbytes mem ri (LE8 (Z_to_bv 64 0))) rom).
Proof using.
  intros regs mem rom ri H8 H10 H5 Hal Hrd Hok.
  pose proof (cas_d_run BSEGS regs (0x4f3d0 : word) (0x4f3d4 : word) (0x4f3d8 : word) (0x4f3dc : word) (0x4f3e0 : word) mem rom
                _ _ _ _ _ _ _ _ 6 8 7 5 6 10 _ _ _ (LE8 (Z_to_bv 64 (2 ^ 60))) (Z_to_bv 64 (2 ^ 60))
                F_4f3d0 eq_refl D_4f3d0 F_4f3d4 eq_refl D_4f3d4 F_4f3d8 eq_refl D_4f3d8 F_4f3dc eq_refl D_4f3dc) as R.
  rewrite H8 in R.
  replace (getr (regupd regs 6 (Z_to_bv 64 (2 ^ 60))) 5) with (Z_to_bv 64 0) in R by (gres; rewrite H5; reflexivity).
  apply R; clear R; first [regneq | pc4 | exact Hal | exact Hrd | apply bytes_le_to_Z_8 | exact Hok | idtac].
  (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end). gres. rewrite H10. rewrite bv_eqb_refl. reflexivity.
Qed.

Section RTA3.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (RIz : Z) (b470 : list byte).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2640).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 RIz.
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 (2 ^ 61).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= bv_unsigned S - 3584 /\ RIz mod 8 = 0)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hb470 : length b470 = 8%nat.
  Hypothesis Hok : store_ok BSEGS mem (Z_to_bv 64 RIz) 8 = true.
  Hypothesis Rmu : rdn BSEGS mem (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60))).
  Hypothesis R470 : rdn BSEGS mem (Z_to_bv 64 0x10468) 8 = Some b470.
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2520)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2528)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2536)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2544)) 8 = Some (LE8 s2v).
  Hypothesis Cs3 : rdn BSEGS mem (at_ S (-2552)) 8 = Some (LE8 s3v).
  Hypothesis Cs4 : rdn BSEGS mem (at_ S (-2560)) 8 = Some (LE8 s4v).
  Hypothesis Cs5 : rdn BSEGS mem (at_ S (-2568)) 8 = Some (LE8 s5v).
  Hypothesis Cs6 : rdn BSEGS mem (at_ S (-2576)) 8 = Some (LE8 s6v).
  Hypothesis Cs7 : rdn BSEGS mem (at_ S (-2584)) 8 = Some (LE8 s7v).
  Hypothesis Cs8 : rdn BSEGS mem (at_ S (-2592)) 8 = Some (LE8 s8v).
  Hypothesis Cs9 : rdn BSEGS mem (at_ S (-2600)) 8 = Some (LE8 s9v).
  Hypothesis Cs10 : rdn BSEGS mem (at_ S (-2608)) 8 = Some (LE8 s10v).
  Hypothesis Cs11 : rdn BSEGS mem (at_ S (-2616)) 8 = Some (LE8 s11v).

  Lemma rta_unlock :
    exists r, msteps BSEGS (mkst regs (0x4f394 : word) mem rom) (mkst r ra0 (wbytes mem (Z_to_bv 64 RIz) (LE8 (Z_to_bv 64 0))) rom)
      /\ getr r 2 = at_ S (-2512) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = s5v /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v /\ getr r 26 = s10v /\ getr r 27 = s11v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4.
  Proof using Cs11 Cs10 Cs9 Cs8 Cs7 Cs6 Cs5 Cs4 Cs3 Cs2 Cs1 Cs0 Cra R470 Rmu Hok Hb470 Hret HRI HS H24 H8 H2 b470.
    pose proof (u64_range S) as HSr. destruct HRI as (HR1 & HR2 & HR8).
    pose proof (bytes_le_to_Z_bound b470) as B4. rewrite Hb470 in B4. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B4.
    pose proof (bytes_le_to_Z_nonneg b470) as B4'.
    assert (V470 : bytes_le_to_Z b470 = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z b470))) by (rewrite u_Z2bv by lia; reflexivity).
    wd_eexists. split.
    - cld8 F_4f394 D_4f394 (Z_to_bv 64 (2 ^ 60)) Rmu.  (* [comment removed for export] *)
      an F_4f398 D_4f398.                              (* [comment removed for export] *)
      an F_4f39c D_4f39c.                              (* [comment removed for export] *)
      an F_4f3a0 D_4f3a0.                              (* [comment removed for export] *)
      an F_4f3a4 D_4f3a4.                              (* [comment removed for export] *)
      an F_4f3a8 D_4f3a8.                              (* [comment removed for export] *)
      an F_4f3ac D_4f3ac.                              (* [comment removed for export] *)
      an F_4f3b0 D_4f3b0.                              (* [comment removed for export] *)
      cld F_4f3b4 D_4f3b4 b470 (Z_to_bv 64 (bytes_le_to_Z b470)) R470 V470.   (* [comment removed for export] *)
      an F_4f3b8 D_4f3b8.                              (* [comment removed for export] *)
      an F_4f3bc D_4f3bc.                              (* [comment removed for export] *)
      an F_4f3c0 D_4f3c0.                              (* [comment removed for export] *)
      an F_4f3c4 D_4f3c4.                              (* [comment removed for export] *)
      an F_4f3c8 D_4f3c8.                              (* [comment removed for export] *)
      an F_4f3cc D_4f3cc.                              (* [comment removed for export] *)
      an F_4f3e8 D_4f3e8.                              (* [comment removed for export] *)
      an F_4f3ec D_4f3ec.                              (* [comment removed for export] *)
      ab_ft F_4f3f0 D_4f3f0 ltac:(condz).              (* [comment removed for export] *)
      an F_4f3f4 D_4f3f4.                              (* [comment removed for export] *)
      ab_tk F_4f3f8 D_4f3f8 ltac:(condz).              (* [comment removed for export] *)
      an F_4f41c D_4f41c.                              (* [comment removed for export] *)
      an F_4f420 D_4f420.                              (* [comment removed for export] *)
      an F_4f424 D_4f424.                              (* [comment removed for export] *)
      an F_4f428 D_4f428.                              (* [comment removed for export] *)
      an F_4f42c D_4f42c.                              (* [comment removed for export] *)
      an F_4f430 D_4f430.                              (* [comment removed for export] *)
      an F_4f434 D_4f434.                              (* [comment removed for export] *)
      ab_tk F_4f438 D_4f438 ltac:(condz).              (* [comment removed for export] *)
      eapply msteps_trans;
      [ eapply (unlock_cas_4f3d0 _ _ rom (Z_to_bv 64 RIz));
          [ gres; rwH; reflexivity | gres; rwH; reflexivity | gres; rwH; reflexivity | unorm; exact HR8 | rd_addr Rmu | any_ok ]
      | ].
      ab_tk F_4f3e0 D_4f3e0 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_4f448 D_4f448 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4f44c D_4f44c ra0 Cra. cld8 F_4f450 D_4f450 s0v Cs0. cld8 F_4f454 D_4f454 s1v Cs1. cld8 F_4f458 D_4f458 s2v Cs2.
      cld8 F_4f45c D_4f45c s3v Cs3. cld8 F_4f460 D_4f460 s4v Cs4. cld8 F_4f464 D_4f464 s5v Cs5. cld8 F_4f468 D_4f468 s6v Cs6.
      cld8 F_4f46c D_4f46c s7v Cs7. cld8 F_4f470 D_4f470 s8v Cs8. cld8 F_4f474 D_4f474 s9v Cs9. cld8 F_4f478 D_4f478 s10v Cs10.
      cld8 F_4f47c D_4f47c s11v Cs11.
      an F_4f480 D_4f480.                              (* [comment removed for export] *)
      aret F_4f484 D_4f484 ra0.                        (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End RTA3.
End FPGen.

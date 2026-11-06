(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8q.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
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

Lemma Z2bv_plus64k : forall a k, Z_to_bv 64 (a + k * 2 ^ 64) = Z_to_bv 64 a.
Proof.
  intros a k. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  apply Z.mod_add. lia.
Qed.

Ltac fsb F D aa bb :=
  chain_step; [reflexivity
    | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [reflexivity | apply bv_eq; unorm; reflexivity]
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Fixpoint pf_cv (M : word -> option byte) (top au csz : Z) (i : nat) : word -> option byte :=
  match i with
  | O => M
  | S i' => wbytes (pf_cv M top au csz i') (Z_to_bv 64 (top - 4 * (Z.of_nat i' + 1))) (LE4 ((au + Z.of_nat i' * csz) / 16))
  end.
(* [comment removed for export] *)
Definition pf_mc (M : word -> option byte) (RIz top au csz nf newn : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (pf_cv M top au csz (Z.to_nat newn))
    (Z_to_bv 64 (RIz + 16)) (LE8 (Z_to_bv 64 (nf + newn))))
    (Z_to_bv 64 (RIz + 32)) (LE8 (Z_to_bv 64 (au + newn * csz))))
    (Z_to_bv 64 (RIz + 68)) [Z_to_bv 8 0].

Lemma pf_cv_grows : forall M top au csz i, mem_grows M (pf_cv M top au csz i).
Proof using. induction i as [|i IH]; [apply mem_grows_refl|]. (lazymatch goal with |- ?G => let G' := eval cbn [pf_cv] in G in change_no_check G' end). eapply mem_grows_trans; [exact IH | apply wbytes_grows]. Qed.
Lemma pf_cv_outside : forall M top au csz i (x : word),
  (0 <= top - 4 * Z.of_nat i)%Z -> (top < 2 ^ 64)%Z ->
  (U x < top - 4 * Z.of_nat i \/ top <= U x)%Z -> pf_cv M top au csz i x = M x.
Proof using.
  induction i as [|i IH]; intros x H0 H1 Hx; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [pf_cv] in G in change_no_check G' end).
  rewrite wbytes_outside; [apply IH; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia].
Qed.

Section CARVE.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v : word) (RIz SPB c au mu nf : Z).
  #[local] Abbreviation csz := (csize c).
  #[local] Abbreviation newn := ((mu - au) / csize c)%Z.
  #[local] Abbreviation FAB := (SPB + c * 2 ^ 32 + 0xE0000000)%Z.
  #[local] Abbreviation top := (SPB + c * 2 ^ 32 + 0xE0000000 + 4 * (nf + (mu - au) / csize c))%Z.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hau : (0 <= au /\ au + csize c <= mu /\ mu <= 0xE0000000)%Z.       (* [comment removed for export] *)
  Hypothesis Hnf : (0 <= nf /\ 4 * (nf + (mu - au) / csize c) <= 2 ^ 29)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis HRI : (SPB + 2 ^ 37 <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis R_au : rdn BSEGS M (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_nf : rdn BSEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis R_mu : rdn BSEGS M (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis R_am : rdn BSEGS M (Z_to_bv 64 (RIz + 40)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_mm : rdn BSEGS M (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOK_RI : store_ok BSEGS M (Z_to_bv 64 RIz) 128 = true.
  Hypothesis SOK_fa : store_ok BSEGS M (Z_to_bv 64 (FAB + 4 * nf)) (Z.to_nat (4 * newn)) = true.

  Lemma newn_facts : (1 <= newn /\ newn * csize c <= mu - au /\ newn <= 0xE0000000 /\ 32 <= csize c <= 65536)%Z.
  Proof using HRI HSPB Hau Hc Hsp SPB RIz sp.
    pose proof (csize_pos c Hc) as [Hcs1 Hcs2]. destruct Hau as (A1 & A2 & A3).
    pose proof (Z.mul_div_le (mu - au) (csize c) ltac:(lia)).
    assert (1 <= newn)%Z by (apply Z.div_le_lower_bound; lia).
    assert (newn <= mu - au)%Z by (apply Z.div_le_upper_bound; nia).
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pf_loop : forall (j i : nat) r,
      (Z.of_nat i + Z.of_nat j = newn)%Z -> (1 <= Z.of_nat j)%Z ->
      getr r 10 = Z_to_bv 64 (Z.of_nat i) -> getr r 11 = Z_to_bv 64 top -> getr r 12 = Z_to_bv 64 (au + Z.of_nat i * csz) ->
      getr r 19 = Z_to_bv 64 newn -> getr r 21 = Z_to_bv 64 csz ->
      exists r',
        msteps BSEGS (mkst r (0x51a00 : word) (pf_cv M top au csz i) rom) (mkst r' (0x51a20 : word) (pf_cv M top au csz (Z.to_nat newn)) rom)
        /\ (forall x : reg, ~ In x [10; 12; 14; 15] -> getr r' x = getr r x).
  Proof using SOK_fa HRI HSPB Hnf Hau Hc Hsp RIz sp.
    pose proof newn_facts as (N1 & N2 & N3 & N4). destruct Hau as (A1 & A2 & A3). destruct Hnf as (F1 & F2).
    induction j as [|j IH]; intros i r Hij Hj R10 R11 R12 R19 R21; [lia|].
    pose proof (u64_range sp) as Hspr.
    assert (SOK : store_ok BSEGS (pf_cv M top au csz i) (Z_to_bv 64 (top - 4 * (Z.of_nat i + 1))) 4 = true).
    { eapply store_ok_mono; [apply pf_cv_grows|].
      eapply (store_ok_sub BSEGS M (Z_to_bv 64 (FAB + 4 * nf)) _ (Z.to_nat (4 * newn))); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact SOK_fa | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | rewrite !u_Z2bv by lia; rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia]. }
    assert (BODY : exists r1, msteps BSEGS (mkst r (0x51a00 : word) (pf_cv M top au csz i) rom) (mkst r1 (0x51a1c : word) (pf_cv M top au csz (S i)) rom)
              /\ getr r1 10 = Z_to_bv 64 (Z.of_nat (S i)) /\ getr r1 11 = Z_to_bv 64 top /\ getr r1 12 = Z_to_bv 64 (au + Z.of_nat (S i) * csz)
              /\ getr r1 19 = Z_to_bv 64 newn /\ getr r1 21 = Z_to_bv 64 csz
              /\ (forall x : reg, ~ In x [10; 12; 14; 15] -> getr r1 x = getr r x)).
    { wd_eexists. split.
      - av F_51a00 D_51a00 (Z_to_bv 64 ((au + Z.of_nat i * csz) / 16))
          ltac:(rewrite ?R12; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite u_Z2bv by nia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).   (* [comment removed for export] *)
        av F_51a04 D_51a04 (Z_to_bv 64 (2 ^ 64 - 1 - Z.of_nat i)) ltac:(rewrite ?R10; apply v_not_lit; lia).   (* [comment removed for export] *)
        av F_51a08 D_51a08 (Z_to_bv 64 (Z.of_nat i + 1)) ltac:(rewrite ?R10; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).   (* [comment removed for export] *)
        av F_51a0c D_51a0c (Z_to_bv 64 (2 ^ 64 - 4 * (Z.of_nat i + 1)))
          ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite u_Z2bv by lia; rewrite Z.shiftl_mul_pow2 by lia;
                rewrite <- (Z2bv_plus64k (2 ^ 64 - 4 * (Z.of_nat i + 1)) 3); f_equal; lia).   (* [comment removed for export] *)
        av F_51a10 D_51a10 (Z_to_bv 64 (top - 4 * (Z.of_nat i + 1)))
          ltac:(rewrite ?R11; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite !u_Z2bv by lia;
                rewrite <- (Z2bv_plus64k (top - 4 * (Z.of_nat i + 1)) 1); f_equal; lia).   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := Z_to_bv 64 (top - 4 * (Z.of_nat i + 1)));
            [exact F_51a14 | reflexivity | exact D_51a14
            | gres; imm_norm; rewrite ?v_addi_0; reflexivity
            | gres; reflexivity
            | exact SOK ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        change (wbytes (pf_cv M top au csz i) _ _) with (pf_cv M top au csz (S i)).
        av F_51a18 D_51a18 (Z_to_bv 64 (au + Z.of_nat (S i) * csz))
          ltac:(rewrite ?R12, ?R21; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite !u_Z2bv by nia; f_equal; lia).   (* [comment removed for export] *)
        wd_refl.
      - split; [gres; f_equal; lia|]. split; [gres; exact R11|]. split; [gres; reflexivity|].
        split; [gres; exact R19|]. split; [gres; exact R21|].
        intros x Hx. gres. rewrite !getr_other; try reflexivity; intros E; apply Hx; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
    destruct BODY as (r1 & RUN1 & Q10 & Q11 & Q12 & Q19 & Q21 & QK).
    destruct (Z.eq_dec (Z.of_nat j) 0) as [Zj|NZj].
    - exists r1. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_ft F_51a1c D_51a1c ltac:(rewrite ?Q10, ?Q19; condz).   (* [comment removed for export] *)
        replace (Z.to_nat newn) with (S i) by lia. wd_refl.
      + exact QK.
    - destruct (IH (S i) r1 ltac:(lia) ltac:(lia) Q10 Q11 Q12 Q19 Q21) as (r' & RUN' & QK').
      exists r'. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_tk F_51a1c D_51a1c ltac:(rewrite ?Q10, ?Q19; condz).   (* [comment removed for export] *)
        exact RUN'.
      + intros x Hx. rewrite (QK' x Hx). exact (QK x Hx).
  Qed.

  #[local] Abbreviation MCV := (pf_cv M top au csz (Z.to_nat newn)).

  (* [comment removed for export] *)
  Lemma cv_rd : forall (a : word) (k : nat) bs,
    (U a + Z.of_nat k <= top - 4 * newn \/ top <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn BSEGS M a k = Some bs -> rdn BSEGS MCV a k = Some bs.
  Proof using HRI HSPB Hnf Hau Hc Hsp RIz sp.
    pose proof newn_facts as (N1 & N2 & N3 & N4). destruct Hnf as (F1 & F2).
    intros a k bs Ha Hk R. rewrite <- R. apply rdn_ext; [exact Hk|].
    intros x Hx. apply pf_cv_outside; [rewrite Z2Nat.id by lia; lia | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Section PRE.
    Variable regs : bvmap 5 word.
    Hypothesis HR : pf_regs sp RIz SPB c regs.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 1.
    Hypothesis H9 : getr regs 9 = Z_to_bv 64 (nf + newn).
    Hypothesis H19 : getr regs 19 = Z_to_bv 64 newn.
    Hypothesis H20 : getr regs 20 = Z_to_bv 64 (mu - au).
    Lemma pf_carve_pre :
      exists r, msteps BSEGS (mkst regs (0x519d8 : word) M rom) (mkst r (0x51a00 : word) M rom)
        /\ pf_regs sp RIz SPB c r /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 top /\ getr r 12 = Z_to_bv 64 au
        /\ getr r 13 = Z_to_bv 64 au /\ getr r 19 = Z_to_bv 64 newn
        /\ regs_agree (fun i : reg => In i [9; 10; 11; 12; 13]) regs r.
    Proof using H20 H19 H9 H10 HR R_au HRI HSPB Hnf Hau Hc Hsp.
      pose proof newn_facts as (N1 & N2 & N3 & N4). destruct Hau as (A1 & A2 & A3). destruct Hnf as (F1 & F2).
      destruct HR as (R2 & R8 & R18 & R21). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
      wd_eexists. split.
      - ab_ft F_519d8 D_519d8 ltac:(condz).            (* [comment removed for export] *)
        cld8 F_519dc D_519dc (Z_to_bv 64 au) R_au.     (* [comment removed for export] *)
        ab_ft F_519e0 D_519e0 ltac:(condz).            (* [comment removed for export] *)
        an F_519e4 D_519e4.                            (* [comment removed for export] *)
        an F_519e8 D_519e8.                            (* [comment removed for export] *)
        av F_519ec D_519ec (Z_to_bv 64 0xE0000000) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
        av F_519f0 D_519f0 (Z_to_bv 64 FAB) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        av F_519f4 D_519f4 (Z_to_bv 64 (4 * (nf + newn))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).   (* [comment removed for export] *)
        av F_519f8 D_519f8 (Z_to_bv 64 top) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        an F_519fc D_519fc.                            (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve.
    Qed.
  End PRE.

  (* [comment removed for export] *)
  Hypothesis S_ra : rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn BSEGS M (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn BSEGS M (at_ sp (-64)) 8 = Some (LE8 s6v).

  Definition pf_post1 (regs r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 1 /\ getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = s6v
    /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20; 21; 22]) regs r.

  Section POST.
    Variable regs : bvmap 5 word.
    Hypothesis HR : pf_regs sp RIz SPB c regs.
    Hypothesis H13 : getr regs 13 = Z_to_bv 64 au.
    Hypothesis H19 : getr regs 19 = Z_to_bv 64 newn.
    Lemma pf_carve_post :
      exists r, msteps BSEGS (mkst regs (0x51a20 : word) MCV rom) (mkst r ra (pf_mc M RIz top au csz nf newn) rom) /\ pf_post1 regs r.
    Proof using H19 H13 HR S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra SOK_RI R_mm R_am R_mu R_nf HRI HSPB Hnf Hau Hc Hret Hsp.
      pose proof newn_facts as (N1 & N2 & N3 & N4). destruct Hau as (A1 & A2 & A3). destruct Hnf as (F1 & F2).
      destruct HR as (R2 & R8 & R18 & R21). (lazymatch goal with |- ?G => let G' := eval unfold pf_post1 in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
      destruct HRI as [RI1 RI2]. destruct HSPB as [SP1 SP2].
      assert (TOP : (top <= RIz)%Z) by lia.
      Ltac cvr H := apply cv_rd; [first [rewrite u_Z2bv by lia | rewrite at_u by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                                 | first [rewrite u_Z2bv by lia | rewrite at_u by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact H].
      assert (Q_nf : rdn BSEGS MCV (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf))) by cvr R_nf.
      assert (Q_mu : rdn BSEGS MCV (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu))) by cvr R_mu.
      assert (Q_am : rdn BSEGS MCV (Z_to_bv 64 (RIz + 40)) 8 = Some (LE8 (Z_to_bv 64 0))) by cvr R_am.
      assert (Q_mm : rdn BSEGS MCV (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0))) by cvr R_mm.
      assert (Q_ra : rdn BSEGS MCV (at_ sp (-8)) 8 = Some (LE8 ra)) by cvr S_ra.
      assert (Q_s0 : rdn BSEGS MCV (at_ sp (-16)) 8 = Some (LE8 s0v)) by cvr S_s0.
      assert (Q_s1 : rdn BSEGS MCV (at_ sp (-24)) 8 = Some (LE8 s1v)) by cvr S_s1.
      assert (Q_s2 : rdn BSEGS MCV (at_ sp (-32)) 8 = Some (LE8 s2v)) by cvr S_s2.
      assert (Q_s3 : rdn BSEGS MCV (at_ sp (-40)) 8 = Some (LE8 s3v)) by cvr S_s3.
      assert (Q_s4 : rdn BSEGS MCV (at_ sp (-48)) 8 = Some (LE8 s4v)) by cvr S_s4.
      assert (Q_s5 : rdn BSEGS MCV (at_ sp (-56)) 8 = Some (LE8 s5v)) by cvr S_s5.
      assert (Q_s6 : rdn BSEGS MCV (at_ sp (-64)) 8 = Some (LE8 s6v)) by cvr S_s6.
      assert (SOK2 : store_ok BSEGS MCV (Z_to_bv 64 RIz) 128 = true) by (eapply store_ok_mono; [apply pf_cv_grows | exact SOK_RI]).
      wd_eexists. split.
      - cld8 F_51a20 D_51a20 (Z_to_bv 64 nf) Q_nf.     (* [comment removed for export] *)
        av F_51a24 D_51a24 (Z_to_bv 64 (newn * csz)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        cld8 F_51a28 D_51a28 (Z_to_bv 64 mu) Q_mu.     (* [comment removed for export] *)
        av F_51a2c D_51a2c (Z_to_bv 64 (au + newn * csz)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        av F_51a30 D_51a30 (Z_to_bv 64 (nf + newn)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        fsd F_51a34 D_51a34 (Z_to_bv 64 (RIz + 16)).   (* [comment removed for export] *)
        fsd F_51a38 D_51a38 (Z_to_bv 64 (RIz + 32)).   (* [comment removed for export] *)
        ab_ft F_51a3c D_51a3c ltac:(condz).            (* [comment removed for export] *)
        cld8 F_51a40 D_51a40 (Z_to_bv 64 0) Q_am.      (* [comment removed for export] *)
        cld8 F_51a44 D_51a44 (Z_to_bv 64 0) Q_mm.      (* [comment removed for export] *)
        ab_ft F_51a48 D_51a48 ltac:(condz).            (* [comment removed for export] *)
        fsb F_51a4c D_51a4c (Z_to_bv 64 (RIz + 68)) (Z_to_bv 8 0).   (* [comment removed for export] *)
        change (wbytes (wbytes (wbytes MCV _ _) _ _) _ _) with (pf_mc M RIz top au csz nf newn).
        an F_51a50 D_51a50.                            (* [comment removed for export] *)
        an F_51a54 D_51a54.                            (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold pf_mc in G in change_no_check G' end).
        cld8 F_51a58 D_51a58 ra Q_ra.                  (* [comment removed for export] *)
        cld8 F_51a5c D_51a5c s0v Q_s0.                 (* [comment removed for export] *)
        cld8 F_51a60 D_51a60 s1v Q_s1.                 (* [comment removed for export] *)
        cld8 F_51a64 D_51a64 s2v Q_s2.                 (* [comment removed for export] *)
        cld8 F_51a68 D_51a68 s3v Q_s3.                 (* [comment removed for export] *)
        cld8 F_51a6c D_51a6c s4v Q_s4.                 (* [comment removed for export] *)
        cld8 F_51a70 D_51a70 s5v Q_s5.                 (* [comment removed for export] *)
        cld8 F_51a74 D_51a74 s6v Q_s6.                 (* [comment removed for export] *)
        an F_51a78 D_51a78.                            (* [comment removed for export] *)
        aret F_51a7c D_51a7c ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve.
    Qed.
  End POST.

  (* [comment removed for export] *)
  Section ALL.
    Variable regs : bvmap 5 word.
    Hypothesis HR : pf_regs sp RIz SPB c regs.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 1.
    Hypothesis H9 : getr regs 9 = Z_to_bv 64 (nf + newn).
    Hypothesis H19 : getr regs 19 = Z_to_bv 64 newn.
    Hypothesis H20 : getr regs 20 = Z_to_bv 64 (mu - au).
    Lemma pf_carve :
      exists r, msteps BSEGS (mkst regs (0x519d8 : word) M rom) (mkst r ra (pf_mc M RIz top au csz nf newn) rom) /\ pf_post1 regs r.
    Proof using H20 H19 H9 H10 HR S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra SOK_fa SOK_RI R_mm R_am R_mu R_nf R_au HRI HSPB Hnf Hau Hc Hret Hsp.
      pose proof newn_facts as (N1 & N2 & N3 & N4).
      destruct (pf_carve_pre regs HR H10 H9 H19 H20) as (r1 & RUN1 & HR1 & A10 & A11 & A12 & A13 & A19 & AG1).
      destruct (pf_loop (Z.to_nat newn) 0%nat r1 ltac:(rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(rewrite Z2Nat.id by lia; lia)
                  A10 A11 ltac:(rewrite A12; f_equal; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) A19 ltac:(destruct HR1 as (_ & _ & _ & X); exact X)) as (r2 & RUN2 & K2).
      assert (HR2 : pf_regs sp RIz SPB c r2).
      { destruct HR1 as (X2 & X8 & X18 & X21). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end).
        rewrite !K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[E|[E|[]]]]]; discriminate E). auto. }
      destruct (pf_carve_post r2 HR2 ltac:(rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[E|[E|[]]]]]; discriminate E); exact A13)
                  ltac:(rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [E|[E|[E|[E|[]]]]]; discriminate E); exact A19)) as (r3 & RUN3 & P3).
      exists r3. split.
      - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
      - destruct P3 as (B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & AG3). (lazymatch goal with |- ?G => let G' := eval unfold pf_post1 in G in change_no_check G' end).
        repeat (split; [assumption|]).
        intros x Hx. rewrite (AG3 x Hx). rewrite K2 by (intros Hin; apply Hx; cbn [In] in *; tauto).
        apply AG1. intros Hin; apply Hx; cbn [In] in *; tauto.
    Qed.
  End ALL.
End CARVE.
End FPGen.
End BoAllocM8q.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM9a.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Lemma land_m8 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 3) = (a - a mod 2 ^ 3)%Z.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 2 ^ 3)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2 ^ 3) ltac:(lia)). lia.
Qed.
Lemma v_andi_m8 : forall x, (0 <= x < 2 ^ 64)%Z -> v_andi (Z_to_bv 64 x) (-8) = Z_to_bv 64 (x - x mod 8).
Proof.
  intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). rewrite u_Z2bv by lia. change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite land_m8 by lia. reflexivity.
Qed.
Lemma v_and_4095_al : forall mb, (0 <= mb < 2 ^ 64)%Z -> (mb mod 4096 = 0)%Z -> v_and (Z_to_bv 64 4095) (Z_to_bv 64 mb) = Z_to_bv 64 0.
Proof.
  intros mb Hmb Hal. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite !u_Z2bv by lia. f_equal. rewrite Z.land_comm.
  change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia. exact Hal.
Qed.
Lemma v_and_7_al : forall x, (0 <= x < 2 ^ 64)%Z -> (x mod 8 = 0)%Z -> v_and (Z_to_bv 64 x) (Z_to_bv 64 7) = Z_to_bv 64 0.
Proof.
  intros x Hx Hal. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite !u_Z2bv by lia. f_equal. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact Hal.
Qed.

(* [comment removed for export] *)
Definition la_msz (size : Z) : Z := ((size + 4095) / 4096 * 4096 + 4096)%Z.

Section FPGen.
Context {fx : FPState}.

Definition la_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
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
    (at_ sp (-88)) (LE8 s9v).
#[local] Hint Unfold la_m0 : asfr.

(* [comment removed for export] *)
Definition la_regs (sp stats : word) (size : Z) (r : bvmap 5 word) : Prop :=
  getr r 2 = at_ sp (-96) /\ getr r 8 = stats /\ getr r 9 = Z_to_bv 64 (0x10ab58 + 64)
  /\ getr r 18 = Z_to_bv 64 (la_msz size) /\ getr r 19 = Z_to_bv 64 size /\ getr r 24 = Z_to_bv 64 7.

Section PRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v stats name : word) (size : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (0x10ab58 + 64).
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 size.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 8.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v. Hypothesis H23 : getr regs 23 = s7v. Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-96)) 96 = true.
  Hypothesis C_pg : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_gnm : rdn BSEGS mem (Z_to_bv 64 0x105f00) 8 = Some (LE8 (Z_to_bv 64 0x107e90)).
  Hypothesis C_nm : rdn BSEGS mem (Z_to_bv 64 0x107e90) 8 = Some (LE8 name).

  #[local] Abbreviation M0 := (la_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v).

  Lemma la_msz_facts : (la_msz size mod 4096 = 0 /\ size + 4096 <= la_msz size <= size + 8191)%Z.
  Proof using name rom. (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end). Z.div_mod_to_equations. lia. Qed.

  Lemma la_pre :
    exists r, msteps BSEGS (mkst regs (0x50fc4 : word) mem rom) (mkst r (0x82a74 : word) M0 rom)
      /\ la_regs sp stats size r /\ getr r 1 = Z_to_bv 64 0x51080 /\ getr r 21 = Z_to_bv 64 8
      /\ getr r 10 = Z_to_bv 64 (la_msz size) /\ getr r 11 = name
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 18; 19; 21; 24]) regs r.
  Proof using C_nm C_gnm C_pg Hstk Hsize Hsp H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    (lazymatch goal with |- ?G => let G' := eval unfold la_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr. pose proof la_msz_facts as [LF1 LF2].
    wd_eexists. split.
    - an F_50fc4 D_50fc4.                              (* [comment removed for export] *)
      fsd F_50fc8 D_50fc8 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_50fcc D_50fcc (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_50fd0 D_50fd0 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_50fd4 D_50fd4 (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_50fd8 D_50fd8 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_50fdc D_50fdc (at_ sp (-48)).              (* [comment removed for export] *)
      fsd F_50fe0 D_50fe0 (at_ sp (-56)).              (* [comment removed for export] *)
      fsd F_50fe4 D_50fe4 (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_50fe8 D_50fe8 (at_ sp (-72)).              (* [comment removed for export] *)
      fsd F_50fec D_50fec (at_ sp (-80)).              (* [comment removed for export] *)
      fsd F_50ff0 D_50ff0 (at_ sp (-88)).              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0.
      an F_50ff4 D_50ff4.                              (* [comment removed for export] *)
      av F_50ff8 D_50ff8 (Z_to_bv 64 7) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_50ffc D_50ffc (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      ab_ft F_51000 D_51000 ltac:(condz).              (* [comment removed for export] *)
      an F_51004 D_51004.                              (* [comment removed for export] *)
      cld8 F_51008 D_51008 (Z_to_bv 64 4096) C_pg.     (* [comment removed for export] *)
      av F_5100c D_5100c (Z_to_bv 64 4095) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_51010 D_51010 (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      ab_ft F_51014 D_51014 ltac:(condz).              (* [comment removed for export] *)
      an F_51018 D_51018.                              (* [comment removed for export] *)
      av F_5101c D_5101c (Z_to_bv 64 (size + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av F_51020 D_51020 (Z_to_bv 64 (2 ^ 64 - 2 ^ 12)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_51024 D_51024 (Z_to_bv 64 (size + 4095)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_51028 D_51028 (Z_to_bv 64 (la_msz size - 4096))
        ltac:(rewrite v_and_m4k; unorm; f_equal; (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      an F_5102c D_5102c. try sltu0.                     (* [comment removed for export] *)
      av F_51030 D_51030 (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_51034 D_51034 (Z_to_bv 64 (la_msz size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_51038 D_51038 (Z_to_bv 64 0) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_5103c D_5103c (Z_to_bv 64 (la_msz size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      ab_tk F_51040 D_51040 ltac:(condz).              (* [comment removed for export] *)
      an F_51068 D_51068.                              (* [comment removed for export] *)
      an F_5106c D_5106c.                              (* [comment removed for export] *)
      cld8 F_51070 D_51070 (Z_to_bv 64 0x107e90) C_gnm.   (* [comment removed for export] *)
      cld8 F_51074 D_51074 name C_nm.                  (* [comment removed for export] *)
      an F_51078 D_51078.                              (* [comment removed for export] *)
      an F_5107c D_5107c.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End PRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MID.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v stats : word) (size mb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.

  Definition la_post0 (r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 0 /\ getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
    /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
    /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]) regs r.

  (* [comment removed for export] *)
  Section FAIL.
    Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
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
    Lemma la_fail : exists r, msteps BSEGS (mkst regs (0x51080 : word) M rom) (mkst r ra M rom) /\ la_post0 r.
    Proof using S_s9 S_s8 S_s7 S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra H10 Hret HR size stats.
      destruct HR as (R2 & R8 & R9 & R18 & R19 & R24). (lazymatch goal with |- ?G => let G' := eval unfold la_post0 in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
      wd_eexists. split.
      - ab_tk F_51080 D_51080 ltac:(condz).            (* [comment removed for export] *)
        cld8 F_512a0 D_512a0 ra S_ra.                  (* [comment removed for export] *)
        cld8 F_512a4 D_512a4 s0v S_s0. cld8 F_512a8 D_512a8 s1v S_s1. cld8 F_512ac D_512ac s2v S_s2. cld8 F_512b0 D_512b0 s3v S_s3.
        cld8 F_512b4 D_512b4 s4v S_s4. cld8 F_512b8 D_512b8 s5v S_s5. cld8 F_512bc D_512bc s6v S_s6. cld8 F_512c0 D_512c0 s7v S_s7.
        cld8 F_512c4 D_512c4 s8v S_s8. cld8 F_512c8 D_512c8 s9v S_s9.
        an F_512cc D_512cc.                            (* [comment removed for export] *)
        aret F_512d0 D_512d0 ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve.
    Qed.
  End FAIL.

  (* [comment removed for export] *)
  Definition la_regs2 (r : bvmap 5 word) : Prop :=
    la_regs sp stats size r /\ getr r 20 = Z_to_bv 64 mb /\ getr r 22 = Z_to_bv 64 (mb + la_msz size)
    /\ getr r 23 = Z_to_bv 64 (mb + 4096 + size - (mb + 4096 + size) mod 8) /\ getr r 25 = Z_to_bv 64 (mb + 4096)
    /\ getr r 21 = Z_to_bv 64 (mb + 4096 + size).

  Hypothesis Hmb : (4096 <= mb /\ mb + la_msz size < 2 ^ 63 /\ mb mod 4096 = 0)%Z.
  Hypothesis C_pg : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).

  Lemma la_mid1 : getr regs 10 = Z_to_bv 64 mb -> getr regs 21 = Z_to_bv 64 8 ->
    exists r, msteps BSEGS (mkst regs (0x51080 : word) M rom) (mkst r (0x70080 : word) M rom)
      /\ la_regs2 r /\ getr r 1 = Z_to_bv 64 0x510d8
      /\ getr r 10 = Z_to_bv 64 mb /\ getr r 11 = Z_to_bv 64 4096 /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12; 20; 21; 22; 23; 25]) regs r.
  Proof using C_pg Hmb Hsize HR.
    intros H10 H21. destruct HR as (R2 & R8 & R9 & R18 & R19 & R24). (lazymatch goal with |- ?G => let G' := eval unfold la_regs2, la_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
    destruct Hmb as (MB1 & MB2 & MB3).
    assert (LF : (la_msz size mod 4096 = 0 /\ size + 4096 <= la_msz size <= size + 8191)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct LF as [LF1 LF2].
    assert (RES8 : ((mb + 4096) mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
    wd_eexists. split.
    - ab_ft F_51080 D_51080 ltac:(condz).              (* [comment removed for export] *)
      an F_51084 D_51084.                              (* [comment removed for export] *)
      cld8 F_51088 D_51088 (Z_to_bv 64 4096) C_pg.     (* [comment removed for export] *)
      av F_5108c D_5108c (Z_to_bv 64 4095) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_51090 D_51090 (Z_to_bv 64 0) ltac:(apply v_and_4095_al; lia).   (* [comment removed for export] *)
      ab_ft F_51094 D_51094 ltac:(condz).              (* [comment removed for export] *)
      av F_51098 D_51098 (Z_to_bv 64 (mb + la_msz size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_5109c D_5109c (Z_to_bv 64 (mb + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av_and F_510a0 D_510a0 (Z_to_bv 64 0) ltac:(apply v_and_7_al; lia).   (* [comment removed for export] *)
      an F_510a4 D_510a4.                              (* [comment removed for export] *)
      av F_510a8 D_510a8 (Z_to_bv 64 8) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_510ac D_510ac.                              (* [comment removed for export] *)
      an F_510b0 D_510b0.                              (* [comment removed for export] *)
      av F_510b4 D_510b4 (Z_to_bv 64 (mb + 4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_510b8 D_510b8 (Z_to_bv 64 (mb + 4096 + size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av F_510bc D_510bc (Z_to_bv 64 (mb + 4096 + 7)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av F_510c0 D_510c0 (Z_to_bv 64 (mb + 4096 + size - (mb + 4096 + size) mod 8)) ltac:(apply v_andi_m8; lia).   (* [comment removed for export] *)
      av F_510c4 D_510c4 (Z_to_bv 64 (mb + 4096)) ltac:(rewrite v_andi_m8 by lia; f_equal; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      av F_510c8 D_510c8 (Z_to_bv 64 4096) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      an F_510cc D_510cc.                              (* [comment removed for export] *)
      an F_510d0 D_510d0.                              (* [comment removed for export] *)
      an F_510d4 D_510d4.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End MID.

(* [comment removed for export] *)
Section MID2.
  Variables (M rom : word -> option byte) (sp stats : word) (size mb : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs2 sp stats size mb regs.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hmb : (4096 <= mb /\ mb + la_msz size < 2 ^ 63 /\ mb mod 4096 = 0)%Z.
  Lemma la_mid2 :
    exists r, msteps BSEGS (mkst regs (0x510d8 : word) M rom) (mkst r (0x70080 : word) M rom)
      /\ la_regs2 sp stats size mb r /\ getr r 1 = Z_to_bv 64 0x510e8
      /\ getr r 10 = Z_to_bv 64 (mb + 4096 + size - (mb + 4096 + size) mod 8)
      /\ getr r 11 = Z_to_bv 64 (mb + la_msz size - (mb + 4096 + size - (mb + 4096 + size) mod 8)) /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12]) regs r.
  Proof using Hmb Hsize HR.
    destruct HR as ((R2 & R8 & R9 & R18 & R19 & R24) & R20 & R22 & R23 & R25 & R21). (lazymatch goal with |- ?G => let G' := eval unfold la_regs2, la_regs in G in change_no_check G' end).
    destruct Hmb as (MB1 & MB2 & MB3).
    assert (LF : (la_msz size mod 4096 = 0 /\ size + 4096 <= la_msz size <= size + 8191)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct LF as [LF1 LF2].
    pose proof (Z.mod_pos_bound (mb + 4096 + size) 8 ltac:(lia)) as MP.
    wd_eexists. split.
    - av F_510d8 D_510d8 (Z_to_bv 64 (mb + la_msz size - (mb + 4096 + size - (mb + 4096 + size) mod 8)))
        ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; reflexivity).       (* [comment removed for export] *)
      an F_510dc D_510dc.                              (* [comment removed for export] *)
      an F_510e0 D_510e0.                              (* [comment removed for export] *)
      an F_510e4 D_510e4.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End MID2.
End FPGen.
End BoAllocM9a.
Require LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM9b.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF7r.BoAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition la_m1 (M : word -> option byte) (thr v72 v80 : word) (size mb : Z) (b1 b2 b3 : byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (at_ thr 2872) (LE8 (v_addi v72 1)))
    (at_ thr 2880) (LE8 (v_add v80 (Z_to_bv 64 (la_msz size)))))
    (Z_to_bv 64 mb) (LE8 (Z_to_bv 64 mb)))
    (Z_to_bv 64 (mb + 8)) (LE8 (Z_to_bv 64 (la_msz size))))
    (Z_to_bv 64 (mb + 16)) (LE8 (Z_to_bv 64 size)))
    (Z_to_bv 64 0x10ae00) [Z_to_bv 8 1; b1; b2; b3].
#[local] Hint Unfold la_m1 : asfr.

Section T1.
  Variables (M rom : word -> option byte) (sp stats thr v72 v80 lkw : word) (size mb T : Z) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs2 sp stats size mb regs.
  Hypothesis H10 : getr regs 10 = at_ thr 2800.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hmb : (AIMGHI <= mb /\ mb + la_msz size < 2 ^ 63 /\ mb mod 4096 = 0)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 96 /\ T mod 8 = 0)%Z.
  Hypothesis HTmb : (T + 4096 <= mb \/ mb + la_msz size <= T)%Z.
  Hypothesis Hmbsp : (mb + la_msz size <= U sp - 96 \/ U sp <= mb)%Z.
  Hypothesis HTimg : (T + 4096 <= AIMGLO \/ AIMGHI <= T)%Z.
  Hypothesis R_72 : rdn BSEGS M (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn BSEGS M (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis C_pg : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis R_lock : rdn BSEGS M (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw.
  Hypothesis SOK_T : store_ok BSEGS M thr 4096 = true.
  Hypothesis SOK_h : store_ok BSEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_lk : store_ok BSEGS M (Z_to_bv 64 0x10ae00) 4 = true.

  Lemma la_t1 :
    exists r, msteps BSEGS (mkst regs (0x510ec : word) M rom) (mkst r (0x51170 : word) (la_m1 M thr v72 v80 size mb b1 b2 b3) rom)
      /\ la_regs sp stats size r /\ getr r 21 = Z_to_bv 64 mb /\ getr r 10 = Z_to_bv 64 (mb + 4096)
      /\ regs_agree (fun i : reg => In i [10; 11; 12; 13; 14; 15; 16; 21]) regs r.
  Proof using SOK_lk SOK_h SOK_T V_lock R_lock C_pg R_80 R_72 HTimg HT Hmb Hsize Hsp H10 HR T lkw. clear - SOK_lk SOK_h SOK_T V_lock R_lock C_pg R_80 R_72 HTimg HT Hmb Hsize Hsp H10 HR T lkw.
    destruct HR as ((R2 & R8 & R9 & R18 & R19 & R24) & R20 & R22 & R23 & R25 & R21). (lazymatch goal with |- ?G => let G' := eval unfold la_regs in G in change_no_check G' end).
    destruct Hmb as (MB1 & MB2 & MB3). destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range sp) as Hspr.
    assert (LF : (la_msz size mod 4096 = 0 /\ size + 4096 <= la_msz size <= size + 8191)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct LF as [LF1 LF2].
    pose proof (Z.mod_pos_bound (mb + 4096 + size) 8 ltac:(lia)) as MP.
    wd_eexists. split.
    - cld8 F_510ec D_510ec v72 R_72.                   (* [comment removed for export] *)
      cld8 F_510f0 D_510f0 v80 R_80.                   (* [comment removed for export] *)
      av_and F_510f4 D_510f4 (Z_to_bv 64 0) ltac:(apply v_and_7_al; [lia | Z.div_mod_to_equations; lia]).   (* [comment removed for export] *)
      an F_510f8 D_510f8.                              (* [comment removed for export] *)
      an F_510fc D_510fc.                              (* [comment removed for export] *)
      fsd F_51100 D_51100 (at_ thr 2872).              (* [comment removed for export] *)
      fsd F_51104 D_51104 (at_ thr 2880).              (* [comment removed for export] *)
      ab_ft F_51108 D_51108 ltac:(condz).              (* [comment removed for export] *)
      an F_5110c D_5110c.                              (* [comment removed for export] *)
      cld8 F_51110 D_51110 (Z_to_bv 64 4096) C_pg.     (* [comment removed for export] *)
      av F_51114 D_51114 (Z_to_bv 64 4095) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av_and F_51118 D_51118 (Z_to_bv 64 0) ltac:(apply v_and_4095_al; [lia | Z.div_mod_to_equations; lia]).   (* [comment removed for export] *)
      ab_ft F_5111c D_5111c ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_51120 D_51120 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_51124 D_51124 ltac:(condz).              (* [comment removed for export] *)
      av F_51128 D_51128 (Z_to_bv 64 mb) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      fsd F_5112c D_5112c (Z_to_bv 64 mb).             (* [comment removed for export] *)
      fsd F_51130 D_51130 (Z_to_bv 64 (mb + 8)).       (* [comment removed for export] *)
      fsd F_51134 D_51134 (Z_to_bv 64 (mb + 16)).      (* [comment removed for export] *)
      ab_ft F_51138 D_51138 ltac:(condz).              (* [comment removed for export] *)
      av F_5113c D_5113c (Z_to_bv 64 0x10ae00) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_51140 D_51140.                              (* [comment removed for export] *)
      av F_51144 D_51144 (Z_to_bv 64 0x10ae00) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_51148 D_51148.                              (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (xchg_byte_run BSEGS _ (0x5114c : word) (0x51150 : word) (0x51154 : word) (0x51158 : word)
                  (0x5115c : word) (0x51160 : word) (0x51164 : word) (0x51168 : word) _ rom
                  _ _ _ _ _ _ _ _ _ _ _ 15 13 16 14 12 _ [Z_to_bv 8 0; b1; b2; b3] lkw 0%nat 1%Z
                  F_5114c eq_refl D_5114c F_51150 eq_refl D_51150 F_51154 eq_refl D_51154 F_51158 eq_refl D_51158
                  F_5115c eq_refl D_5115c F_51160 eq_refl D_51160 F_51164 eq_refl D_51164).
        all: lazymatch goal with
             | |- v_addi _ _ = _ => first [reflexivity | apply bv_eq; vm_compute; reflexivity]
             | |- _ <> _ => first [regneq | intros X; discriminate X]
             | |- (_ mod 4 = 0)%Z => gres; rwH; unorm; reflexivity
             | |- rdn _ _ _ _ = _ => gres; rwH; rd_peel; exact R_lock
             | |- bytes_le_to_Z _ = _ => exact V_lock
             | |- store_ok _ _ _ _ = true => gres; rwH; any_ok
             | |- (_ < _)%nat => lia
             | |- (_ <= _ < _)%Z => lia
             | |- U _ = _ => gres; rwH; unorm; reflexivity
             end. }
      gres. rwH. (lazymatch goal with |- ?G => let G' := eval cbn [firstn skipn app] in G in change_no_check G' end).
      av F_51168 D_51168 (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ V_lock); unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_5116c D_5116c ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End T1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section T2.
  Variables (M rom : word -> option byte) (sp stats : word) (size mb nch nres PA cz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hnch : (0 <= nch < 2 ^ 20 /\ nch <> nres /\ 0 <= nres < 2 ^ 64)%Z.
  Hypothesis Hclz : (U (swar_clz (Z_to_bv 64 (la_msz size))) = cz /\ 0 <= cz <= 63)%Z.
  Hypothesis R_nch : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

End T2.

(* [comment removed for export] *)
Section T2P.
  Variables (M rom : word -> option byte) (smw : word) (nres : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x10ab58 + 64).
  Hypothesis H11 : getr regs 11 = smw.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 0x5555555555555555.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 0x3333333333333333.
  Hypothesis H15 : getr regs 15 = Z_to_bv 64 0x0f0f0f0f0f0f0f0f.
  Hypothesis R_nres : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

End T2P.

Section T2C.
  Variables (M rom : word -> option byte) (sp stats : word) (size mb nch nres PA cz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : la_regs sp stats size regs.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hnch : (0 <= nch < 2 ^ 20 /\ nch <> nres /\ 0 <= nres < 2 ^ 64)%Z.
  Hypothesis Hclz : (U (swar_clz (Z_to_bv 64 (la_msz size))) = cz /\ 0 <= cz <= 63)%Z.
  Hypothesis R_nch : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).


End T2C.
End FPGen.
End BoAllocM9b.
Module BoAllocM9d.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
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

Definition cbs_m0 (mem : word -> option byte) (sp ra s0v s1v s2v s3v s4v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (LE8 ra))
    (at_ sp (-16)) (LE8 s0v))
    (at_ sp (-24)) (LE8 s1v))
    (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v))
    (at_ sp (-48)) (LE8 s4v).
#[local] Hint Unfold cbs_m0 : asfr.

Section PRE.
  Variables (mem rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v : word) (size : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 size.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 8.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsize : (0x10000 < size <= 2 ^ 41)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-48)) 48 = true.

  Lemma cbs_pre :
    exists r, msteps BSEGS (mkst regs (0x50cec : word) mem rom) (mkst r (0x50fc4 : word) (cbs_m0 mem sp ra s0v s1v s2v s3v s4v) rom)
      /\ getr r 1 = Z_to_bv 64 0x50d94 /\ getr r 2 = at_ sp (-48) /\ getr r 8 = Z_to_bv 64 8
      /\ getr r 10 = Z_to_bv 64 (0x10ab58 + 64) /\ getr r 11 = Z_to_bv 64 0x10ae08 /\ getr r 12 = Z_to_bv 64 size /\ getr r 13 = Z_to_bv 64 8
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 10; 11; 12; 14; 15]) regs r.
  Proof using Hstk Hsize Hsp H20 H19 H18 H9 H8 H13 H12 H10 H2 H1.
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - an F_50cec D_50cec.                              (* [comment removed for export] *)
      fsd F_50cf0 D_50cf0 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_50cf4 D_50cf4 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_50cf8 D_50cf8 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_50cfc D_50cfc (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_50d00 D_50d00 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_50d04 D_50d04 (at_ sp (-48)).              (* [comment removed for export] *)
      an F_50d08 D_50d08.                              (* [comment removed for export] *)
      match goal with |- context [v_sltiu ?a ?b] =>
        replace (v_sltiu a b) with (Z_to_bv 64 0)
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_sltiu in G in change_no_check G' end); unorm; change (bv_wrap 64 1) with 1%Z; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity) end.
      av F_50d0c D_50d0c (Z_to_bv 64 size) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av F_50d10 D_50d10 (Z_to_bv 64 (2 ^ 64 - 1 - size)) ltac:(apply v_not_lit; lia).   (* [comment removed for export] *)
      ab_tk F_50d14 D_50d14 ltac:(condz).              (* [comment removed for export] *)
      an F_50d38 D_50d38.                              (* [comment removed for export] *)
      an F_50d3c D_50d3c.                              (* [comment removed for export] *)
      ab_tk F_50d40 D_50d40 ltac:(condz).              (* [comment removed for export] *)
      an F_50d60 D_50d60.                              (* [comment removed for export] *)
      ab_ft F_50d64 D_50d64 ltac:(condz).              (* [comment removed for export] *)
      ab_tk F_50d68 D_50d68 ltac:(condz).              (* [comment removed for export] *)
      av F_50d80 D_50d80 (Z_to_bv 64 (0x10ab58 + 64)) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      av F_50d84 D_50d84 (Z_to_bv 64 0x10ae08) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
      an F_50d88 D_50d88.                              (* [comment removed for export] *)
      an F_50d8c D_50d8c.                              (* [comment removed for export] *)
      an F_50d90 D_50d90.                              (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End PRE.

Section RET.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v res : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 8.
  Hypothesis H10 : getr regs 10 = res.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis S_ra : rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Lemma cbs_ret :
    exists r, msteps BSEGS (mkst regs (0x50d94 : word) M rom) (mkst r ra M rom)
      /\ getr r 10 = res /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 11; 13; 18; 19; 20]) regs r.
  Proof using S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hret H10 H8 H2.
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - an F_50d94 D_50d94.                              (* [comment removed for export] *)
      an F_50d98 D_50d98.                              (* [comment removed for export] *)
      ab_ft F_50d9c D_50d9c ltac:(condz).              (* [comment removed for export] *)
      an F_50da0 D_50da0.                              (* [comment removed for export] *)
      cld8 F_50ef0 D_50ef0 ra S_ra.                    (* [comment removed for export] *)
      cld8 F_50ef4 D_50ef4 s0v S_s0.                   (* [comment removed for export] *)
      cld8 F_50ef8 D_50ef8 s1v S_s1.                   (* [comment removed for export] *)
      cld8 F_50efc D_50efc s2v S_s2.                   (* [comment removed for export] *)
      cld8 F_50f00 D_50f00 s3v S_s3.                   (* [comment removed for export] *)
      cld8 F_50f04 D_50f04 s4v S_s4.                   (* [comment removed for export] *)
      an F_50f08 D_50f08.                              (* [comment removed for export] *)
      aret F_50f0c D_50f0c ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End RET.
End FPGen.
End BoAllocM9d.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p BoAllocM8q BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_50a9c_51a9c.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Lemma xori63 : forall cz, (0 <= cz <= 63)%Z -> v_xori (Z_to_bv 64 cz) 63 = Z_to_bv 64 (63 - cz).
Proof.
  intros cz Hcz.
  assert (E : exists k : nat, cz = Z.of_nat k /\ (k <= 63)%nat) by (exists (Z.to_nat cz); lia).
  destruct E as (k & -> & Hk).
  do 64 (destruct k as [|k]; [apply bv_eq; vm_compute; reflexivity|]). lia.
Qed.

Section FPGen.
Context {fx : FPState}.

Definition la_m2 (M : word -> option byte) (mb nch PA idx msz : Z) (naw sumw mxw' blw w16 w24 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (Z_to_bv 64 (mb + 24)) (LE8 (Z_to_bv 64 nch)))
    (Z_to_bv 64 (PA + 8 * nch)) (LE8 (Z_to_bv 64 mb)))
    (Z_to_bv 64 0x10abd0) (LE8 (Z_to_bv 64 (nch + 1))))
    (Z_to_bv 64 0x10abd8) [Z_to_bv 8 0])
    (Z_to_bv 64 0x10abe0) (LE8 (v_addi naw 1)))
    (Z_to_bv 64 0x10abf0) (LE8 sumw))
    (Z_to_bv 64 0x10abf8) (LE8 mxw'))
    (Z_to_bv 64 (0x10ac00 + 8 * idx)) (LE8 (v_addi blw 1)))
    (Z_to_bv 64 0x10ae18) (LE8 (v_add w16 (Z_to_bv 64 msz))))
    (Z_to_bv 64 0x10ae20) (LE8 (v_add w24 (Z_to_bv 64 msz))))
    (Z_to_bv 64 0x10ae00) [Z_to_bv 8 0].
#[local] Hint Unfold la_m2 : asfr.

Section T2B.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v naw curw mxw blw w16 w24 : word)
            (size mb nch nres PA cz : Z).
  #[local] Abbreviation msz := (la_msz size).
  #[local] Abbreviation idx := (63 - cz)%Z.
  #[local] Abbreviation sumw := (v_add curw (Z_to_bv 64 (la_msz size))).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-96).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0x10ae08.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x10ab58 + 64).
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 msz.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 cz.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 nch.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 nres.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hsize : (1 <= size <= 2 ^ 41)%Z.
  Hypothesis Hnch : (0 <= nch < 2 ^ 20 /\ nch <> nres /\ 0 <= nres < 2 ^ 64)%Z.
  Hypothesis Hcz : (0 <= cz <= 63)%Z.
  Hypothesis Hmb : (AIMGHI <= mb /\ mb + la_msz size < 2 ^ 63)%Z.
  Hypothesis HPA : (AIMGHI <= PA /\ PA + 2 ^ 23 < 2 ^ 63)%Z.
  Hypothesis HPAmb : (PA + 2 ^ 23 <= mb \/ mb + 32 <= PA)%Z.
  Hypothesis Hmbsp : (mb + 32 <= U sp - 96 \/ U sp <= mb)%Z.
  Hypothesis HPAsp : (PA + 2 ^ 23 <= U sp - 96 \/ U sp <= PA)%Z.
  Hypothesis R_pa : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 PA)).
  Hypothesis R_na : rdn BSEGS M (Z_to_bv 64 0x10abe0) 8 = Some (LE8 naw).
  Hypothesis R_cur : rdn BSEGS M (Z_to_bv 64 0x10abf0) 8 = Some (LE8 curw).
  Hypothesis R_mx : rdn BSEGS M (Z_to_bv 64 0x10abf8) 8 = Some (LE8 mxw).
  Hypothesis R_bl : rdn BSEGS M (Z_to_bv 64 (0x10ac00 + 8 * idx)) 8 = Some (LE8 blw).
  Hypothesis R_16 : rdn BSEGS M (Z_to_bv 64 0x10ae18) 8 = Some (LE8 w16).
  Hypothesis R_24 : rdn BSEGS M (Z_to_bv 64 0x10ae20) 8 = Some (LE8 w24).
  Hypothesis SOK_h : store_ok BSEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_pa : store_ok BSEGS M (Z_to_bv 64 (PA + 8 * nch)) 8 = true.
  Hypothesis SOK_inst : store_ok BSEGS M (Z_to_bv 64 0x10ab98) 728 = true.        (* [comment removed for export] *)

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



  Ltac t2b_head :=
      ab_ft F_51224 D_51224 ltac:(condz);              (* [comment removed for export] *)
      cld8 F_51228 D_51228 (Z_to_bv 64 PA) R_pa;       (* [comment removed for export] *)
      av F_5122c D_5122c (Z_to_bv 64 idx) ltac:(apply xori63; lia);   (* [comment removed for export] *)
      fsd F_51230 D_51230 (Z_to_bv 64 (mb + 24));      (* [comment removed for export] *)
      av F_51234 D_51234 (Z_to_bv 64 (8 * nch)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia);   (* [comment removed for export] *)
      av F_51238 D_51238 (Z_to_bv 64 (PA + 8 * nch)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      fsd F_5123c D_5123c (Z_to_bv 64 (PA + 8 * nch)); (* [comment removed for export] *)
      cld8 F_51240 D_51240 naw R_na;                   (* [comment removed for export] *)
      cld8 F_51244 D_51244 curw R_cur;                 (* [comment removed for export] *)
      av F_51248 D_51248 (Z_to_bv 64 (nch + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity);   (* [comment removed for export] *)
      cld8 F_5124c D_5124c mxw R_mx;                   (* [comment removed for export] *)
      an F_51250 D_51250;                              (* [comment removed for export] *)
      an F_51254 D_51254;                              (* [comment removed for export] *)
      fsd F_51258 D_51258 (Z_to_bv 64 0x10abd0);       (* [comment removed for export] *)
      fsb F_5125c D_5125c (Z_to_bv 64 0x10abd8) (Z_to_bv 8 0);   (* [comment removed for export] *)
      fsd F_51260 D_51260 (Z_to_bv 64 0x10abe0);       (* [comment removed for export] *)
      fsd F_51264 D_51264 (Z_to_bv 64 0x10abf0).       (* [comment removed for export] *)
  Ltac t2b_tail :=
      av F_51270 D_51270 (Z_to_bv 64 (8 * idx)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia);   (* [comment removed for export] *)
      av F_51274 D_51274 (Z_to_bv 64 (0x10ab98 + 8 * idx)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia);   (* [comment removed for export] *)
      cld8 F_51278 D_51278 blw R_bl;                   (* [comment removed for export] *)
      an F_5127c D_5127c;                              (* [comment removed for export] *)
      fsd F_51280 D_51280 (Z_to_bv 64 0x10abf8);       (* [comment removed for export] *)
      fsd F_51284 D_51284 (Z_to_bv 64 (0x10ac00 + 8 * idx));   (* [comment removed for export] *)
      av F_51288 D_51288 (Z_to_bv 64 0x10ae18) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 w16) (v := w16);
          [exact F_5128c | reflexivity | exact D_5128c
          | gres; rwH; unorm; reflexivity
          | gres; rwH; rd_peel; exact R_16
          | apply bytes_le_to_Z_8
          | gres; rwH; any_ok ]
        | step_simpl]; vn);                            (* [comment removed for export] *)
      av F_51290 D_51290 (Z_to_bv 64 0x10ae20) ltac:(apply bv_eq; vm_compute; reflexivity);   (* [comment removed for export] *)
      (chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 w24) (v := w24);
          [exact F_51294 | reflexivity | exact D_51294
          | gres; rwH; unorm; reflexivity
          | gres; rwH; rd_peel; exact R_24
          | apply bytes_le_to_Z_8
          | gres; rwH; any_ok ]
        | step_simpl]; vn);                            (* [comment removed for export] *)
      afence F_51298 D_51298;                          (* [comment removed for export] *)
      fsb F_5129c D_5129c (Z_to_bv 64 0x10ae00) (Z_to_bv 8 0);   (* [comment removed for export] *)
      cld8 F_512a0 D_512a0 ra S_ra;                    (* [comment removed for export] *)
      cld8 F_512a4 D_512a4 s0v S_s0; cld8 F_512a8 D_512a8 s1v S_s1; cld8 F_512ac D_512ac s2v S_s2; cld8 F_512b0 D_512b0 s3v S_s3;
      cld8 F_512b4 D_512b4 s4v S_s4; cld8 F_512b8 D_512b8 s5v S_s5; cld8 F_512bc D_512bc s6v S_s6; cld8 F_512c0 D_512c0 s7v S_s7;
      cld8 F_512c4 D_512c4 s8v S_s8; cld8 F_512c8 D_512c8 s9v S_s9;
      an F_512cc D_512cc;                              (* [comment removed for export] *)
      aret F_512d0 D_512d0 ra.

End T2B.
End FPGen.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8q.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z.RefEnframeArith.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
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
  Hypothesis R_au : rdn ASEGS M (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_nf : rdn ASEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis R_mu : rdn ASEGS M (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis R_am : rdn ASEGS M (Z_to_bv 64 (RIz + 40)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_mm : rdn ASEGS M (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOK_RI : store_ok ASEGS M (Z_to_bv 64 RIz) 128 = true.
  Hypothesis SOK_fa : store_ok ASEGS M (Z_to_bv 64 (FAB + 4 * nf)) (Z.to_nat (4 * newn)) = true.

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
        msteps ASEGS (mkst r (0x50f90 : word) (pf_cv M top au csz i) rom) (mkst r' (0x50fb0 : word) (pf_cv M top au csz (Z.to_nat newn)) rom)
        /\ (forall x : reg, ~ In x [10; 12; 14; 15] -> getr r' x = getr r x).
  Proof using SOK_fa HRI HSPB Hnf Hau Hc Hsp RIz sp.
    pose proof newn_facts as (N1 & N2 & N3 & N4). destruct Hau as (A1 & A2 & A3). destruct Hnf as (F1 & F2).
    induction j as [|j IH]; intros i r Hij Hj R10 R11 R12 R19 R21; [lia|].
    pose proof (u64_range sp) as Hspr.
    assert (SOK : store_ok ASEGS (pf_cv M top au csz i) (Z_to_bv 64 (top - 4 * (Z.of_nat i + 1))) 4 = true).
    { eapply store_ok_mono; [apply pf_cv_grows|].
      eapply (store_ok_sub ASEGS M (Z_to_bv 64 (FAB + 4 * nf)) _ (Z.to_nat (4 * newn))); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact SOK_fa | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | rewrite !u_Z2bv by lia; rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia]. }
    assert (BODY : exists r1, msteps ASEGS (mkst r (0x50f90 : word) (pf_cv M top au csz i) rom) (mkst r1 (0x50fac : word) (pf_cv M top au csz (S i)) rom)
              /\ getr r1 10 = Z_to_bv 64 (Z.of_nat (S i)) /\ getr r1 11 = Z_to_bv 64 top /\ getr r1 12 = Z_to_bv 64 (au + Z.of_nat (S i) * csz)
              /\ getr r1 19 = Z_to_bv 64 newn /\ getr r1 21 = Z_to_bv 64 csz
              /\ (forall x : reg, ~ In x [10; 12; 14; 15] -> getr r1 x = getr r x)).
    { wd_eexists. split.
      - av F_50f88 D_50f88 (Z_to_bv 64 ((au + Z.of_nat i * csz) / 16))
          ltac:(rewrite ?R12; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite u_Z2bv by nia; rewrite Z.shiftr_div_pow2 by lia; reflexivity).   (* [comment removed for export] *)
        av F_50f8c D_50f8c (Z_to_bv 64 (2 ^ 64 - 1 - Z.of_nat i)) ltac:(rewrite ?R10; apply v_not_lit; lia).   (* [comment removed for export] *)
        av F_50f90 D_50f90 (Z_to_bv 64 (Z.of_nat i + 1)) ltac:(rewrite ?R10; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).   (* [comment removed for export] *)
        av F_50f94 D_50f94 (Z_to_bv 64 (2 ^ 64 - 4 * (Z.of_nat i + 1)))
          ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite u_Z2bv by lia; rewrite Z.shiftl_mul_pow2 by lia;
                rewrite <- (Z2bv_plus64k (2 ^ 64 - 4 * (Z.of_nat i + 1)) 3); f_equal; lia).   (* [comment removed for export] *)
        av F_50f98 D_50f98 (Z_to_bv 64 (top - 4 * (Z.of_nat i + 1)))
          ltac:(rewrite ?R11; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite !u_Z2bv by lia;
                rewrite <- (Z2bv_plus64k (top - 4 * (Z.of_nat i + 1)) 1); f_equal; lia).   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sw_at with (a := Z_to_bv 64 (top - 4 * (Z.of_nat i + 1)));
            [exact F_50f9c | reflexivity | exact D_50f9c
            | gres; imm_norm; rewrite ?v_addi_0; reflexivity
            | gres; reflexivity
            | exact SOK ]
          | step_simpl]; vn.                               (* [comment removed for export] *)
        change (wbytes (pf_cv M top au csz i) _ _) with (pf_cv M top au csz (S i)).
        av F_50fa0 D_50fa0 (Z_to_bv 64 (au + Z.of_nat (S i) * csz))
          ltac:(rewrite ?R12, ?R21; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite !u_Z2bv by nia; f_equal; lia).   (* [comment removed for export] *)
        wd_refl.
      - split; [gres; f_equal; lia|]. split; [gres; exact R11|]. split; [gres; reflexivity|].
        split; [gres; exact R19|]. split; [gres; exact R21|].
        intros x Hx. gres. rewrite !getr_other; try reflexivity; intros E; apply Hx; rewrite <- E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
    destruct BODY as (r1 & RUN1 & Q10 & Q11 & Q12 & Q19 & Q21 & QK).
    destruct (Z.eq_dec (Z.of_nat j) 0) as [Zj|NZj].
    - exists r1. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_ft F_50fa4 D_50fa4 ltac:(rewrite ?Q10, ?Q19; condz).   (* [comment removed for export] *)
        replace (Z.to_nat newn) with (S i) by lia. wd_refl.
      + exact QK.
    - destruct (IH (S i) r1 ltac:(lia) ltac:(lia) Q10 Q11 Q12 Q19 Q21) as (r' & RUN' & QK').
      exists r'. split.
      + eapply msteps_trans; [exact RUN1|].
        ab_tk F_50fa4 D_50fa4 ltac:(rewrite ?Q10, ?Q19; condz).   (* [comment removed for export] *)
        exact RUN'.
      + intros x Hx. rewrite (QK' x Hx). exact (QK x Hx).
  Qed.

  #[local] Abbreviation MCV := (pf_cv M top au csz (Z.to_nat newn)).

  (* [comment removed for export] *)
  Lemma cv_rd : forall (a : word) (k : nat) bs,
    (U a + Z.of_nat k <= top - 4 * newn \/ top <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn ASEGS M a k = Some bs -> rdn ASEGS MCV a k = Some bs.
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
      exists r, msteps ASEGS (mkst regs (0x50f68 : word) M rom) (mkst r (0x50f90 : word) M rom)
        /\ pf_regs sp RIz SPB c r /\ getr r 10 = Z_to_bv 64 0 /\ getr r 11 = Z_to_bv 64 top /\ getr r 12 = Z_to_bv 64 au
        /\ getr r 13 = Z_to_bv 64 au /\ getr r 19 = Z_to_bv 64 newn
        /\ regs_agree (fun i : reg => In i [9; 10; 11; 12; 13]) regs r.
    Proof using H20 H19 H9 H10 HR R_au HRI HSPB Hnf Hau Hc Hsp.
      pose proof newn_facts as (N1 & N2 & N3 & N4). destruct Hau as (A1 & A2 & A3). destruct Hnf as (F1 & F2).
      destruct HR as (R2 & R8 & R18 & R21). (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
      wd_eexists. split.
      - ab_ft F_50f60 D_50f60 ltac:(condz).            (* [comment removed for export] *)
        cld8 F_50f64 D_50f64 (Z_to_bv 64 au) R_au.     (* [comment removed for export] *)
        ab_ft F_50f68 D_50f68 ltac:(condz).            (* [comment removed for export] *)
        an F_50f6c D_50f6c.                            (* [comment removed for export] *)
        an F_50f70 D_50f70.                            (* [comment removed for export] *)
        av F_50f74 D_50f74 (Z_to_bv 64 0xE0000000) ltac:(apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
        av F_50f78 D_50f78 (Z_to_bv 64 FAB) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        av F_50f7c D_50f7c (Z_to_bv 64 (4 * (nf + newn))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); unorm; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).   (* [comment removed for export] *)
        av F_50f80 D_50f80 (Z_to_bv 64 top) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        an F_50f84 D_50f84.                            (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve.
    Qed.
  End PRE.

  (* [comment removed for export] *)
  Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Hypothesis S_s5 : rdn ASEGS M (at_ sp (-56)) 8 = Some (LE8 s5v).
  Hypothesis S_s6 : rdn ASEGS M (at_ sp (-64)) 8 = Some (LE8 s6v).

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
      exists r, msteps ASEGS (mkst regs (0x50fb0 : word) MCV rom) (mkst r ra (pf_mc M RIz top au csz nf newn) rom) /\ pf_post1 regs r.
    Proof using H19 H13 HR S_s6 S_s5 S_s4 S_s3 S_s2 S_s1 S_s0 S_ra SOK_RI R_mm R_am R_mu R_nf HRI HSPB Hnf Hau Hc Hret Hsp.
      pose proof newn_facts as (N1 & N2 & N3 & N4). destruct Hau as (A1 & A2 & A3). destruct Hnf as (F1 & F2).
      destruct HR as (R2 & R8 & R18 & R21). (lazymatch goal with |- ?G => let G' := eval unfold pf_post1 in G in change_no_check G' end). pose proof (u64_range sp) as Hspr.
      destruct HRI as [RI1 RI2]. destruct HSPB as [SP1 SP2].
      assert (TOP : (top <= RIz)%Z) by lia.
      Ltac cvr H := apply cv_rd; [first [rewrite u_Z2bv by lia | rewrite at_u by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia
                                 | first [rewrite u_Z2bv by lia | rewrite at_u by lia]; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact H].
      assert (Q_nf : rdn ASEGS MCV (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf))) by cvr R_nf.
      assert (Q_mu : rdn ASEGS MCV (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu))) by cvr R_mu.
      assert (Q_am : rdn ASEGS MCV (Z_to_bv 64 (RIz + 40)) 8 = Some (LE8 (Z_to_bv 64 0))) by cvr R_am.
      assert (Q_mm : rdn ASEGS MCV (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0))) by cvr R_mm.
      assert (Q_ra : rdn ASEGS MCV (at_ sp (-8)) 8 = Some (LE8 ra)) by cvr S_ra.
      assert (Q_s0 : rdn ASEGS MCV (at_ sp (-16)) 8 = Some (LE8 s0v)) by cvr S_s0.
      assert (Q_s1 : rdn ASEGS MCV (at_ sp (-24)) 8 = Some (LE8 s1v)) by cvr S_s1.
      assert (Q_s2 : rdn ASEGS MCV (at_ sp (-32)) 8 = Some (LE8 s2v)) by cvr S_s2.
      assert (Q_s3 : rdn ASEGS MCV (at_ sp (-40)) 8 = Some (LE8 s3v)) by cvr S_s3.
      assert (Q_s4 : rdn ASEGS MCV (at_ sp (-48)) 8 = Some (LE8 s4v)) by cvr S_s4.
      assert (Q_s5 : rdn ASEGS MCV (at_ sp (-56)) 8 = Some (LE8 s5v)) by cvr S_s5.
      assert (Q_s6 : rdn ASEGS MCV (at_ sp (-64)) 8 = Some (LE8 s6v)) by cvr S_s6.
      assert (SOK2 : store_ok ASEGS MCV (Z_to_bv 64 RIz) 128 = true) by (eapply store_ok_mono; [apply pf_cv_grows | exact SOK_RI]).
      wd_eexists. split.
      - cld8 F_50fa8 D_50fa8 (Z_to_bv 64 nf) Q_nf.     (* [comment removed for export] *)
        av F_50fac D_50fac (Z_to_bv 64 (newn * csz)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        cld8 F_50fb0 D_50fb0 (Z_to_bv 64 mu) Q_mu.     (* [comment removed for export] *)
        av F_50fb4 D_50fb4 (Z_to_bv 64 (au + newn * csz)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        av F_50fb8 D_50fb8 (Z_to_bv 64 (nf + newn)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
        fsd F_50fbc D_50fbc (Z_to_bv 64 (RIz + 16)).   (* [comment removed for export] *)
        fsd F_50fc0 D_50fc0 (Z_to_bv 64 (RIz + 32)).   (* [comment removed for export] *)
        ab_ft F_50fc4 D_50fc4 ltac:(condz).            (* [comment removed for export] *)
        cld8 F_50fc8 D_50fc8 (Z_to_bv 64 0) Q_am.      (* [comment removed for export] *)
        cld8 F_50fcc D_50fcc (Z_to_bv 64 0) Q_mm.      (* [comment removed for export] *)
        ab_ft F_50fd0 D_50fd0 ltac:(condz).            (* [comment removed for export] *)
        fsb F_50fd4 D_50fd4 (Z_to_bv 64 (RIz + 68)) (Z_to_bv 8 0).   (* [comment removed for export] *)
        change (wbytes (wbytes (wbytes MCV _ _) _ _) _ _) with (pf_mc M RIz top au csz nf newn).
        an F_50fd8 D_50fd8.                            (* [comment removed for export] *)
        an F_50fdc D_50fdc.                            (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold pf_mc in G in change_no_check G' end).
        cld8 F_50fe0 D_50fe0 ra Q_ra.                  (* [comment removed for export] *)
        cld8 F_50fe4 D_50fe4 s0v Q_s0.                 (* [comment removed for export] *)
        cld8 F_50fe8 D_50fe8 s1v Q_s1.                 (* [comment removed for export] *)
        cld8 F_50fec D_50fec s2v Q_s2.                 (* [comment removed for export] *)
        cld8 F_50ff0 D_50ff0 s3v Q_s3.                 (* [comment removed for export] *)
        cld8 F_50ff4 D_50ff4 s4v Q_s4.                 (* [comment removed for export] *)
        cld8 F_50ff8 D_50ff8 s5v Q_s5.                 (* [comment removed for export] *)
        cld8 F_50ffc D_50ffc s6v Q_s6.                 (* [comment removed for export] *)
        an F_51000 D_51000.                            (* [comment removed for export] *)
        aret F_51004 D_51004 ra.                       (* [comment removed for export] *)
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
      exists r, msteps ASEGS (mkst regs (0x50f68 : word) M rom) (mkst r ra (pf_mc M RIz top au csz nf newn) rom) /\ pf_post1 regs r.
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
End AsAllocM8q.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
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
    (Z_to_bv 64 0x103f90) (LE8 (Z_to_bv 64 (nch + 1))))
    (Z_to_bv 64 0x103f98) [Z_to_bv 8 0])
    (Z_to_bv 64 0x103fa0) (LE8 (v_addi naw 1)))
    (Z_to_bv 64 0x103fb0) (LE8 sumw))
    (Z_to_bv 64 0x103fb8) (LE8 mxw'))
    (Z_to_bv 64 (0x103fc0 + 8 * idx)) (LE8 (v_addi blw 1)))
    (Z_to_bv 64 0x1041d8) (LE8 (v_add w16 (Z_to_bv 64 msz))))
    (Z_to_bv 64 0x1041e0) (LE8 (v_add w24 (Z_to_bv 64 msz))))
    (Z_to_bv 64 0x1041c0) [Z_to_bv 8 0].
#[local] Hint Unfold la_m2 : asfr.

Section T2B.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v naw curw mxw blw w16 w24 : word)
            (size mb nch nres PA cz : Z).
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



  Ltac t2b_head :=
      ab_ft F_507ac D_507ac ltac:(condz);              (* [comment removed for export] *)
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
      aret F_50858 D_50858 ra.

End T2B.
End FPGen.

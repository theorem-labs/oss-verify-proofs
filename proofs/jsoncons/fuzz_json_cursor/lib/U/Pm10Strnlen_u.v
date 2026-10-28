(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim Frame
  RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.musl Require Import Pm10MemcpyBase_u Pm10Memchr_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10_code_b6000_b7000_u   .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

Section SNL.
  Variable mem : word -> option byte.
  Variables s sp : word.
  Variable buf : list byte.
  Variables K n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mchrH mem s buf K n.
  Hypothesis HsK : (0 < bv_unsigned s + K)%Z.
  Hypothesis Hstk : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true.
  Hypothesis Hspr : (0x147e8 <= bv_unsigned sp - 32)%Z.
  Hypothesis Hdisj : (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32
                      \/ bv_unsigned sp <= bv_unsigned s)%Z.

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation W8 v := (word_to_le_bytes 8 v).

  Definition mem1 (ra s0 s1 : word) : word -> option byte :=
    wbytes (wbytes (wbytes mem (Z_to_bv 64 (usp - 8)) (W8 ra)) (Z_to_bv 64 (usp - 16)) (W8 s0))
           (Z_to_bv 64 (usp - 24)) (W8 s1).

  Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  Lemma mem1_out : forall ra s0 s1 (a : word),
    (bv_unsigned a < usp - 24 \/ usp <= bv_unsigned a)%Z -> mem1 ra s0 s1 a = mem a.
  Proof.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1 a Ha. pose proof (u64_range sp). unfold mem1.
    rewrite !wbytes_outside; rewrite ?lenW8; unfold in_rng; u_norm; try lia; reflexivity.
  Qed.

  Lemma HOK1 : forall ra s0 s1, mchrH (mem1 ra s0 s1) s buf K n.
  Proof.
    intros ra s0 s1. pose proof (u64_range sp). pose proof (u64_range s). destruct HOK. split; try assumption.
    - rewrite <- Hbuf. apply rdn_ext; [lia|]. intros x Hx. apply mem1_out. lia.
    - intros i Hi. rewrite mem1_out; [apply Hro; exact Hi | u_norm; lia].
  Qed.

  Lemma frame1 : forall ra s0 s1, frame_mod mem (mem1 ra s0 s1) [(Z_to_bv 64 (usp - 32), 32%Z)].
  Proof.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1. pose proof (u64_range sp). split.
    - intros a [Ha _]. unfold in_rng in Ha. revert Ha. u_norm. intros Ha. apply mem1_out. lia.
    - unfold mem1. eapply mem_grows_trans; [| apply wbytes_grows].
      eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
  Qed.

  Lemma rd_ra : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 8)) 8 = Some (W8 ra).
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  Lemma rd_s0 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 16)) 8 = Some (W8 s0).
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  Lemma rd_s1 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 24)) 8 = Some (W8 s1).
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1. apply rdn_wbytes_hit8. u_norm. lia.
  Qed.

  Ltac okstk :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
      [u_norm; lia | exact Hstk | u_norm; lia | u_norm; cbn; lia].

  Ltac kept_cs := cbv [callee_saved In]; tauto.

  Ltac msd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
        | gres; rwH; reflexivity
        | okstk ]
      | step_simpl]; vnorm.

  Ltac mld8 F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
          exact RD
        | apply bytes_le_to_Z_8 ]
      | step_simpl]; vnorm.

  Lemma strnlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0xb8388 : word) mem rom)
                   (mkst regs' ret (mem1 ret (getr regs 8) (getr regs 9)) rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 K.
  Proof.
    intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs.
    pose proof (KL _ _ _ _ _ HOK) as HKL.
    destruct HOK as [Hbuf Hwin Hnw HK0 _ _ HKn Hn64 Hro].
    set (s0 := getr regs 8). set (s1 := getr regs 9).

    eapply (runs_trans RSEGS _ (fun r => mkst r (0xb7798 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 1 = (0xb83ac : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
                       /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = s
                       /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 n
                       /\ (forall x : reg, In x callee_saved -> x <> 1 -> x <> 2 -> x <> 8 -> x <> 9 -> getr r x = getr regs x))).
    { eexists. split.
      - stepiv F_b64f8 D_b64f8 (Z_to_bv 64 (usp - 32))
          ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).
        msd F_b64fc D_b64fc (Z_to_bv 64 (usp - 8)).
        msd F_b6500 D_b6500 (Z_to_bv 64 (usp - 16)).
        msd F_b6504 D_b6504 (Z_to_bv 64 (usp - 24)).
        stepn F_b6508 D_b6508.
        stepn F_b650c D_b650c.
        stepn F_b6510 D_b6510.
        stepn F_b6514 D_b6514.
        stepn F_b6518 D_b6518.
        rwH. fold s0 s1. unfold mem1. apply mst_refl.
      - cbv beta. repeat split; gres; rwH; try reflexivity; try bveq.
        intros x Hx N1 N2 N8 N9. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [first [ exfalso; match goal with N : ?a <> ?a |- _ => apply N; reflexivity end
                 | gres; reflexivity ] |]).
        destruct Hx. }
    cbv beta. intros r1 (R1 & R2 & R8 & R9 & R10 & R11 & R12 & RK).

    eapply (runs_trans RSEGS _ (fun r => mkst r (0xb83ac : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 10 = Z_to_bv 64 (bv_unsigned s + K) /\ keeps_cs r1 r)).
    { destruct (ref_memchr0 (mem1 ret s0 s1) s buf K n rom r1 (0xb83ac : word) (HOK1 ret s0 s1)
                  ltac:(apply ret_ok_even; reflexivity) R1 R10 R11 R12) as (r & RUN & KC & A10).
      exists r. split; [exact RUN | split; [exact A10 | exact KC]]. }
    cbv beta. intros r2 (A10 & KC).
    assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (KC 2) by kept_cs; exact R2).
    assert (S9 : getr r2 9 = s) by (rewrite (KC 9) by kept_cs; exact R9).

    eexists. split.
    - stepb_ft F_b651c D_b651c ltac:(rwH; apply c_eq_neq; unorm; lia).
      stepiv F_b6520 D_b6520 (Z_to_bv 64 K)
        ltac:(gres; rwH; unfold v_sub; unorm; f_equal; lia).
      stepn F_b6524 D_b6524.
      mld8 F_b6528 D_b6528 ret (rd_ra ret s0 s1).
      mld8 F_b652c D_b652c s0 (rd_s0 ret s0 s1).
      mld8 F_b6530 D_b6530 s1 (rd_s1 ret s0 s1).
      stepiv F_b6534 D_b6534 sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).

      stepret F_b6538 D_b6538 ret ltac:(reflexivity).
      apply mst_refl.
    - split.
      + intros x Hx. pose proof Hx as Hx'. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ gres; subst s0 s1; first [ symmetry; assumption | reflexivity
                  | rewrite (KC _ Hx'); apply (RK _ Hx'); intros E; discriminate E ] |]).
        destruct Hx.
      + gres. reflexivity.
  Qed.
End SNL.

Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x147e8 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0xb8388 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
  intros mem s sp buf K n rom regs ret HOK HsK Hstk Hspr Hdisj Hret H1 H2 H10 H11.
  destruct (strnlen_run mem s sp buf K n rom HOK HsK Hstk Hspr Hdisj regs ret Hret H1 H2 H10 H11)
    as (r & RUN & KC & A10).
  exists r, (mem1 mem sp ret (getr regs 8) (getr regs 9)).
  split; [exact RUN | split; [exact KC | split; [exact A10 | apply frame1; exact Hspr]]].
Qed.

End FPX_1.

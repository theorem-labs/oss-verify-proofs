(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMemcpyBase RefMemcpyWBase RefMemcpyWAL RefMemcpyWMIS RefMemcpyWC1 RefMemcpyWC2 RefMemcpyWC3 Ref_code_235f0_2427c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ALL.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcW mem0 dst src n.

  #[local] Notation MK := (MW mem0 dst).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Wn _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Wnws _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Wnwd _ _ _ _ HOK.

  Ltac mlw F D jj := mlwW HOK F D jj.
  Ltac mlbu F D jj := mlbuW HOK F D jj.
  Ltac msw F D kk := mswW HOK mem0 dst F D kk.
  Ltac msb F D kk := msbW HOK mem0 dst F D kk.

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.

  Ltac post := repeat split; try solve_len; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  (* [comment removed for export] *)
  Ltac conda := rwH; unfold at_; cond.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_finish : forall regs (ret : word) acc k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23760 : word) (MK acc) rom) (mkst regs' ret (MK acc') rom)
      /\ LEN acc' (n)
      /\ keeps regs regs'.
  Proof.
    intros regs ret acc k Hret H1 H11 H13 H12 Hk HLN.
    set (m := ((n - k) mod 16)%Z).
    pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)) as Hm16.
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    assert (Hl16 : Z.land m 16 = 0%Z) by (destruct B16 as [E|E]; [exact E|exfalso; lia]).
    eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x2379c : word) (MK a) rom)
             (fun r a => LEN a ((n - m)) /\ getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run _ _ _ _ rom HOK regs ret acc k H1 H11 H13 H12 Hk HLN) as (r & a & R & P). exists r, a.
      subst m. split; [exact R|]. decompose [and] P. repeat split; try assumption. }
    cbv beta. intros r2 a2 (L2 & S1 & S11 & S13 & S12 & K2).
    eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x237bc : word) (MK a) rom)
             (fun r a => LEN a ((n - m + Z.land m 8)) /\ getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run _ _ _ _ rom HOK r2 ret a2 (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia) ltac:(lia) L2) as (r & a & R & P).
      exists r, a. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r3 a3 (L3 & T1 & T11 & T13 & T12 & K3).
    eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23a00 : word) (MK a) rom)
             (fun r a => LEN a ((n - m + Z.land m 8 + Z.land m 4)) /\ getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run _ _ _ _ rom HOK r3 ret a3 (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia) ltac:(lia) ltac:(lia) L3) as (r & a & R & P).
      exists r, a. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r4 a4 (L4 & U1 & U11 & U13 & U12 & K4).
    destruct (t2_run _ _ _ _ rom HOK r4 ret a4 (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1 ltac:(lia) ltac:(lia) L4) as (r & a & R & P).
    decompose [and] P. exists r, a. split; [exact R | split; [solve_len | eapply keeps_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mis_run : forall regs (ret : word) acc k q,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 15 = Z_to_bv 64 q -> (q = 1 \/ q = 2 \/ q = 3)%Z ->
    (0 <= k <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23690 : word) (MK acc) rom) (mkst regs' ret (MK acc') rom)
      /\ LEN acc' (n)
      /\ keeps regs regs'.
  Proof.
    intros regs ret acc k q Hret H1 H11 H13 H12 H15 Hq Hk HLN.
    destruct (Z.lt_ge_cases (n - k) 32) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      destruct (bits_lt32 (n - k) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
      assert (0 <= Z.land (n - k) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 4)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - k) 1)%Z by (apply Z.land_nonneg; lia).
      assert (0 <= Z.land (n - k) 16)%Z by (apply Z.land_nonneg; lia).
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23698 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23690 D_23690.                        (* [comment removed for export] *)
          stepb_ft F_23694 D_23694 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        set (m := (n - k)%Z) in *.
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23a00 : word) (MK a) rom)
                 (fun r a => LEN a ((k + Z.land m 16 + Z.land m 8 + Z.land m 4)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + Z.land m 16 + Z.land m 8 + Z.land m 4)
                           /\ getr r 13 = at_ dst (k + Z.land m 16 + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (t16_run _ _ _ _ rom HOK r1 ret a1 k m R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & P).
          exists r2, a2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 a2 (L2 & S1 & S11 & S13 & S12 & K2).
          destruct (t2_run _ _ _ _ rom HOK r2 ret a2 (k + Z.land m 16 + Z.land m 8 + Z.land m 4)%Z m Hret S1 S11 S13 S12
                      ltac:(lia) B2 B1 ltac:(lia) ltac:(lia) L2) as (r3 & a3 & RUN & L3' & K3).
          exists r3, a3. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x236b4 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23690 D_23690.                        (* [comment removed for export] *)
          stepb_tk F_23694 D_23694 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & R15 & K1).
        assert (CASE : exists regs' acc' m,
          msteps RSEGS (mkst r1 (0x236b4 : word) (MK a1) rom)
                       (mkst regs' (0x23a00 : word) (MK acc') rom)
          /\ LEN acc' (n - (Z.land m 2 + Z.land m 1))
          /\ (0 <= m < 32)%Z
          /\ getr regs' 1 = ret /\ getr regs' 11 = at_ src (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 13 = at_ dst (n - (Z.land m 2 + Z.land m 1))
          /\ getr regs' 12 = Z_to_bv 64 m /\ keeps r1 regs').
        { destruct Hq as [-> | [-> | ->]].
          - apply (c1_run _ _ _ _ rom HOK r1 ret a1 k); try assumption; lia.
          - apply (c2_run _ _ _ _ rom HOK r1 ret a1 k); try assumption; lia.
          - apply (c3_run _ _ _ _ rom HOK r1 ret a1 k); try assumption; lia. }
        destruct CASE as (r2 & a2 & m & RUN & L2 & Hm & S1 & S11 & S13 & S12 & K2).
        destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
        assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
        destruct (t2_run _ _ _ _ rom HOK r2 ret a2 (n - (Z.land m 2 + Z.land m 1))%Z m Hret S1 S11 S13 S12
                    ltac:(lia) B2 B1 ltac:(lia) ltac:(lia) L2) as (r3 & a3 & RUN3 & L3 & K3).
        exists r3, a3. split; [eapply msteps_trans; [exact RUN | exact RUN3] |].
        split; [exact L3|]. eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma j_run : forall regs (ret : word) acc k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    (0 <= k <= n)%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23688 : word) (MK acc) rom) (mkst regs' ret (MK acc') rom)
      /\ LEN acc' (n)
      /\ keeps regs regs'.
  Proof.
    intros regs ret acc k Hret H1 H11 H13 H12 Hk HLN.
    pose proof (u64_range dst).
    set (q := ((bv_unsigned dst + k) mod 4)%Z).
    pose proof (Z.mod_pos_bound (bv_unsigned dst + k) 4 ltac:(lia)) as Hq4.
    destruct (Z.eq_dec q 0) as [Hq0|Hq0].
    - (* [comment removed for export] *)
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23760 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k) /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23688 D_23688.                        (* [comment removed for export] *)
          stepb_tk F_2368c D_2368c ltac:(conda).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
        destruct (al_finish r1 ret a1 k Hret R1 R11 R13 R12 Hk L1) as (r2 & a2 & RUN & L2' & K2).
        exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
    - eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23690 : word) (MK a) rom)
               (fun r a => LEN a (k) /\ getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 (n - k)
                         /\ getr r 15 = Z_to_bv 64 q /\ keeps regs r)).
      + eexists. eexists. split.
        * stepn F_23688 D_23688.
          stepb_ft F_2368c D_2368c ltac:(conda).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post. unfold v_andi, at_. subst q. rewrite <- land_3 by lia. unorm.
          change (bv_wrap 64 3) with 3%Z. reflexivity.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & R15 & K1).
        destruct (mis_run r1 ret a1 k q Hret R1 R11 R13 R12 R15 ltac:(lia) Hk L1) as (r2 & a2 & RUN & L2' & K2).
        exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hl_loop : forall (i : nat) regs (ret : word) acc k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = Z_to_bv 64 (n - k) ->
    getr regs 14 = at_ src (k + 1) -> getr regs 15 = Z_to_bv 64 1 ->
    (0 <= k)%Z -> (k < n)%Z -> ((bv_unsigned src + k) mod 4 <> 0)%Z ->
    (Z.of_nat i + 1 = Z.min (n - k) (4 - (bv_unsigned src + k) mod 4))%Z ->
    LEN acc (k) ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23658 : word) (MK acc) rom) (mkst regs' ret (MK acc') rom)
      /\ LEN acc' (n)
      /\ keeps regs regs'.
  Proof.
    induction i as [|i IH]; intros regs ret acc k Hret H1 H11 H13 H12 H14 H15 Hk Hkn Hal Hi HLN.
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      destruct (Z.eq_dec ((bv_unsigned src + (k + 1)) mod 4) 0) as [Hz|Hz].
      + eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23688 : word) (MK a) rom)
                 (fun r a => LEN a ((k + 1)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * eexists. eexists. split.
          -- mlbu F_23658 D_23658 k.                    (* [comment removed for export] *)
             stepn F_2365c D_2365c.                    (* [comment removed for export] *)
             stepn F_23660 D_23660.                    (* [comment removed for export] *)
             stepn F_23664 D_23664.                    (* [comment removed for export] *)
             msb F_23668 D_23668 k.   (* [comment removed for export] *)
             stepn F_2366c D_2366c.                    (* [comment removed for export] *)
             stepn F_23670 D_23670.                    (* [comment removed for export] *)
             stepb_tk F_23674 D_23674 ltac:(conda).    (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret a1 (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) L1) as (r2 & a2 & RUN & L2' & K2).
          exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
      + eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23688 : word) (MK a) rom)
                 (fun r a => LEN a ((k + 1)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1)) /\ keeps regs r)).
        * eexists. eexists. split.
          -- mlbu F_23658 D_23658 k.
             stepn F_2365c D_2365c.
             stepn F_23660 D_23660.
             stepn F_23664 D_23664.
             msb F_23668 D_23668 k.
             stepn F_2366c D_2366c.
             stepn F_23670 D_23670.
             stepb_ft F_23674 D_23674 ltac:(conda).    (* [comment removed for export] *)
             stepn F_23678 D_23678.                    (* [comment removed for export] *)
             stepb_ft F_2367c D_2367c ltac:(cond).     (* [comment removed for export] *)
             stepn F_23680 D_23680.                    (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. unfold v_addi. unorm. f_equal. lia.
        * cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret a1 (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) L1) as (r2 & a2 & RUN & L2' & K2).
          exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
    - (* [comment removed for export] *)
      pose proof (u64_range src).
      eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23658 : word) (MK a) rom)
               (fun r a => LEN a ((k + 1)) /\ getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1) /\ getr r 12 = Z_to_bv 64 (n - (k + 1))
                         /\ getr r 14 = at_ src (k + 1 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
      + eexists. eexists. split.
        * mlbu F_23658 D_23658 k.
          stepn F_2365c D_2365c.
          stepn F_23660 D_23660.
          stepn F_23664 D_23664.
          msb F_23668 D_23668 k.
          stepn F_2366c D_2366c.
          stepn F_23670 D_23670.
          stepb_ft F_23674 D_23674 ltac:(conda).       (* [comment removed for export] *)
          stepn F_23678 D_23678.                       (* [comment removed for export] *)
          stepb_tk F_2367c D_2367c ltac:(cond).        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret a1 (k + 1)%Z Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & L2' & K2).
        exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem ref_memcpy_weak0 : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' acc',
      msteps RSEGS (mkst regs (0x23640 : word) mem0 rom) (mkst regs' ret (MK acc') rom)
      /\ LEN acc' n /\ keeps regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src). pose proof (u64_range dst).
    change mem0 with (MK []). pose proof LEN_nil as HLN.
    assert (H11' : getr regs 11 = at_ src 0) by (rewrite at_0; exact H11).
    assert (H12' : getr regs 12 = Z_to_bv 64 (n - 0)) by (rewrite Z.sub_0_r; exact H12).
    destruct (Z.eq_dec (bv_unsigned src mod 4) 0) as [Hs4|Hs4].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (bv_unsigned dst mod 4) 0) as [Hd4|Hd4].
      + eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23760 : word) (MK a) rom)
                 (fun r a => LEN a (0) /\ getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. eexists. split.
          -- stepn F_23640 D_23640.                     (* [comment removed for export] *)
             stepb_tk F_23644 D_23644 ltac:(conda).     (* [comment removed for export] *)
             stepn F_23754 D_23754.                     (* [comment removed for export] *)
             stepn F_23758 D_23758.                     (* [comment removed for export] *)
             stepb_ft F_2375c D_2375c ltac:(cond).      (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
          destruct (al_finish r1 ret a1 0 Hret R1 R11 R13 R12 ltac:(lia) L1) as (r2 & a2 & RUN & L2' & K2).
          exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
      + eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23690 : word) (MK a) rom)
                 (fun r a => LEN a (0) /\ getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 15 = Z_to_bv 64 (bv_unsigned dst mod 4) /\ keeps regs r)).
        * eexists. eexists. split.
          -- stepn F_23640 D_23640.
             stepb_tk F_23644 D_23644 ltac:(conda).
             stepn F_23754 D_23754.
             stepn F_23758 D_23758.
             stepb_tk F_2375c D_2375c ltac:(cond).      (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post; try (rewrite at_0; reflexivity).
             unfold v_andi. rewrite <- land_3 by lia. change (bv_wrap 64 3) with 3%Z. reflexivity.
        * cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & R15 & K1).
          pose proof (Z.mod_pos_bound (bv_unsigned dst) 4 ltac:(lia)).
          destruct (mis_run r1 ret a1 0 (bv_unsigned dst mod 4) Hret R1 R11 R13 R12 R15 ltac:(lia) ltac:(lia) L1) as (r2 & a2 & RUN & L2' & K2).
          exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hn0z|Hn0z].
      + eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23688 : word) (MK a) rom)
                 (fun r a => LEN a (0) /\ getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ keeps regs r)).
        * eexists. eexists. split.
          -- stepn F_23640 D_23640.                     (* [comment removed for export] *)
             stepb_ft F_23644 D_23644 ltac:(conda).     (* [comment removed for export] *)
             stepb_tk F_23648 D_23648 ltac:(cond).      (* [comment removed for export] *)
             stepn F_23684 D_23684.                     (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & K1).
          destruct (j_run r1 ret a1 0 Hret R1 R11 R13 R12 ltac:(lia) L1) as (r2 & a2 & RUN & L2' & K2).
          exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
      + set (i := Z.to_nat (Z.min n (4 - bv_unsigned src mod 4) - 1)).
        pose proof (Z.mod_pos_bound (bv_unsigned src) 4 ltac:(lia)).
        eapply (runsW_trans RSEGS _ (fun r a => mkst r (0x23658 : word) (MK a) rom)
                 (fun r a => LEN a (0) /\ getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0 /\ getr r 12 = Z_to_bv 64 (n - 0)
                           /\ getr r 14 = at_ src (0 + 1) /\ getr r 15 = Z_to_bv 64 1 /\ keeps regs r)).
        * eexists. eexists. split.
          -- stepn F_23640 D_23640.                     (* [comment removed for export] *)
             stepb_ft F_23644 D_23644 ltac:(conda).     (* [comment removed for export] *)
             stepb_ft F_23648 D_23648 ltac:(cond).      (* [comment removed for export] *)
             stepn F_2364c D_2364c.                     (* [comment removed for export] *)
             stepn F_23650 D_23650.                     (* [comment removed for export] *)
             stepn F_23654 D_23654.                     (* [comment removed for export] *)
             apply mst_refl.
          -- cbv beta. post. rewrite at_0. reflexivity.
        * cbv beta. intros r1 a1 (L1 & R1 & R11 & R13 & R12 & R14 & R15 & K1).
          destruct (hl_loop i r1 ret a1 0 Hret R1 R11 R13 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hs4) ltac:(subst i; rewrite Z.add_0_r, Z.sub_0_r; rewrite Z2Nat.id; lia) L1) as (r2 & a2 & RUN & L2' & K2).
          exists r2, a2. split; [exact RUN | split; [solve_len | eapply keeps_trans; eassumption]].
  Qed.

End ALL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


(* [comment removed for export] *)
Theorem ref_memcpy_weak :
  forall (mem0 : word -> option byte) (dst src : word) (n : Z) (rom : word -> option byte)
         (regs : bvmap 5 word) (ret : word),
    mcW mem0 dst src n ->
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' (bs' : list byte),
      length bs' = Z.to_nat n
      /\ msteps RSEGS (mkst regs (0x23640 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs') rom)
      /\ keeps regs regs'.
Proof.
  intros mem0 dst src n rom regs ret HOK Hret H1 H10 H11 H12.
  destruct (ref_memcpy_weak0 mem0 dst src n rom HOK regs ret Hret H1 H10 H11 H12) as (r & a & R & L & K).
  exists r, a. split; [apply (LEN_to_nat _ _ L)|]. split; [exact R | exact K].
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec SymStepR StepTac StoreOk AgentLib StartupTac StartupAux RefMemcpyLib RefEnframeArith MemSplit SumsLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import BothRPLib BothPlanImages BothIMemcpy.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Both_code_depot3 Both_code_depot4 BothDepotMem BothDepotWalkL.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.BothRPLib.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma okr_rw : forall m a n, (0xa8000 <= a)%Z -> (a + n <= 0x607000)%Z -> okr m a n.
Proof.
  intros m a n Ha Hn j Hj. cbn [store_ok].
  destruct (wview SEGS m (Z_to_bv 64 (a + j))) eqn:E; [reflexivity|].
  exfalso. refine (both_rw_window m (Z_to_bv 64 (a + j)) _ E). rewrite u64_lit by lia. lia.
Qed.

Lemma mul_pow_div : forall a j k, (0 <= a)%Z -> (0 <= k <= j)%Z -> (a * 2 ^ j / 2 ^ k = a * 2 ^ (j - k))%Z.
Proof.
  intros a j k Ha Hk. replace (2 ^ j)%Z with (2 ^ (j - k) * 2 ^ k)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc. apply Z.div_mul. apply Z.pow_nonzero; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ALLOC.
  Variables (mem rom : word -> option byte) (usp tf P count : Z) (ret : word).
  Hypothesis Husp : (2 ^ 32 <= usp - 16)%Z /\ (usp + 8 < 2 ^ 64)%Z.
  Hypothesis Hstk : okr mem (usp - 16) 24.                (* [comment removed for export] *)
  Hypothesis Htf : cell64 mem SSB tf.
  Hypothesis HP : cell64 mem (SSB + 16) P.
  Hypothesis Hroom : (0 <= tf)%Z /\ (1 <= count <= 256)%Z /\ (tf + count < 2 ^ 20)%Z.
  Hypothesis HPnz : (1 <= P)%Z /\ (P + 8 * 2 ^ 20 < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ret.

  Definition alloc_mem (vra v8 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem
      (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 vra))
      (Z_to_bv 64 (usp - 16)) (word_to_le_bytes 8 v8))
      (Z_to_bv 64 SSB) (word_to_le_bytes 8 (Z_to_bv 64 (tf + count))))
      (Z_to_bv 64 usp) (word_to_le_bytes 8 (Z_to_bv 64 tf)).

  #[using="Husp Hstk Htf HP Hroom HPnz Hret"] Theorem alloc_walk : forall regs,
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 SSB ->
    getr regs 11 = Z_to_bv 64 count -> getr regs 12 = Z_to_bv 64 usp ->
    exists regs',
      msteps SEGS (mkst regs (0x7281c : word) mem rom) (mkst regs' ret (alloc_mem ret (getr regs 8)) rom)
      /\ getr regs' 10 = Z_to_bv 64 (P + 8 * tf) /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ret
      /\ (forall r, r <> 5 -> r <> 6 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
  Proof.
    intros regs H1 H2 H10 H11 H12. destruct Htf as [Htfc Htfr]. destruct HP as [HPc HPr]. cbn in Htfr, HPr.
    eexists. split.
    - ai F_7281c D_7281c.
      ast F_72820 D_72820 (Z_to_bv 64 (usp - 8)) ret ltac:(okw Hstk).
      ast F_72824 D_72824 (Z_to_bv 64 (usp - 16)) (getr regs 8) ltac:(okw Hstk).
      ai F_72828 D_72828.
      ai F_7282c D_7282c.
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply (step_amoadd_d _ _ _ rom _ _ _ 8 10 15 1587848 tf);
          [ exact F_72830 | reflexivity | exact D_72830 | gr; pin; reflexivity | lia | lia | reflexivity
          | split; [peelz; exact Htfc | cbn; lia]
          | apply okr_store_ok; [lia | cbn; lia | repeat apply okr_wbytes; apply okr_rw; lia] ]
        | step_simpl ].
      nz. rewrite (u64_lit count) by lia. rewrite (Z.mod_small (tf + count)) by lia.
      (* [comment removed for export] *)
      ai F_72834 D_72834.
      ai F_72838 D_72838. rewrite v_srli_lit by lia. rewrite (Z.div_small tf) by lia.
      ai F_7283c D_7283c.
      ai F_72840 D_72840. rewrite v_srli_lit by lia. rewrite (Z.div_small (count + -1 + tf)) by lia.
      (* [comment removed for export] *)
      stepb_ft F_72844 D_72844 ltac:(pin; unfold c_eq; rewrite bv_eqb_refl; reflexivity).
      (* [comment removed for export] *)
      ai F_72848 D_72848. rewrite v_srli_lit by lia. rewrite (Z.div_small tf) by lia.
      stepb_tk F_7284c D_7284c ltac:(pin; unfold c_eq; rewrite bv_eqb_refl; reflexivity).
      (* [comment removed for export] *)
      ast F_72864 D_72864 (Z_to_bv 64 usp) (Z_to_bv 64 tf) ltac:(okw Hstk).
      (* [comment removed for export] *)
      ai F_72868 D_72868.
      ai F_7286c D_7286c. try rewrite Z.add_0_r.
      (* [comment removed for export] *)
      ld_step F_72870 D_72870 (word_to_le_bytes 8 (Z_to_bv 64 P)) (Z_to_bv 64 P)
        ltac:(peelz; exact HPc) ltac:(rewrite bytes_le_to_Z_8; reflexivity).
      (* [comment removed for export] *)
      stepb_ft F_72874 D_72874 ltac:(pin; unfold c_eq; rewrite c_eq_zbv by lia; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      ai F_72878 D_72878. rewrite v_slli_lit by (try lia; change (2 ^ 44)%Z with 17592186044416%Z; lia).
      ai F_7287c D_7287c. rewrite v_srli_lit by (change (2 ^ 44)%Z with 17592186044416%Z; lia).
      rewrite mul_pow_div by lia. change (2 ^ (44 - 41))%Z with 8%Z.
      ai F_72880 D_72880.
      (* [comment removed for export] *)
      ald F_72884 D_72884 ret ltac:(idtac).
      ald F_72888 D_72888 (getr regs 8) ltac:(idtac).
      (* [comment removed for export] *)
      ai F_7288c D_7288c. replace (usp + -16 + 16)%Z with usp by lia.
      stepjr F_72890 D_72890 ret ltac:(gr; pin; first [reflexivity | assumption]). imm_norm. rewrite (Hret : v_jalr ret 0 = ret).
      replace (tf * 8)%Z with (8 * tf)%Z by lia.
      unfold alloc_mem. apply mst_refl.
    - split; [gr; f_equal; lia|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
      intros r N5 N6 N10 N11 N12 N14 N15.
      destruct (bv_eq_dec 5 r 1) as [->|N1]; [gr; symmetry; exact H1|].
      destruct (bv_eq_dec 5 r 2) as [->|N2]; [gr; symmetry; exact H2|].
      destruct (bv_eq_dec 5 r 8) as [->|N8]; [gr; reflexivity|].
      repeat (rewrite getr_other by (first [exact N1|exact N2|exact N5|exact N6|exact N8|exact N10|exact N11|exact N12|exact N14|exact N15])).
      reflexivity.
  Qed.
End ALLOC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SSTORE.
  Variables (mem rom : word -> option byte) (usp tf P st T w size tag : Z) (bs : list byte) (ret : word).
  Hypothesis Husp : (2 ^ 32 <= usp - 80)%Z /\ (usp + 56 < 2 ^ 64)%Z.
  Hypothesis Hstk : okr mem (usp - 80) 96.                          (* [comment removed for export] *)
  Hypothesis HA0 : cell64 mem (usp + 40) T.                         (* [comment removed for export] *)
  Hypothesis HA8 : cell64 mem (usp + 48) w.                         (* [comment removed for export] *)
  Hypothesis Hw : w = (size + tag * 2 ^ 32)%Z /\ (1 <= size <= 255)%Z /\ (0 <= tag < 256)%Z.
  Hypothesis Htf : cell64 mem SSB tf.
  Hypothesis HP : cell64 mem (SSB + 16) P.
  Hypothesis Hst : cell32 mem (SSB + 24) st.
  Hypothesis Hroom : (0 <= tf)%Z /\ (tf + 256 < 2 ^ 20)%Z /\ (0 <= st)%Z /\ (st + 256 < 2 ^ 20)%Z.
  Hypothesis HPblk : (0x607000 <= P)%Z /\ (P + 8 * 2 ^ 20 < 2 ^ 64)%Z.
  Hypothesis HPok : okr mem (P + 8 * tf) (8 * (size + 1)).
  Hypothesis HT : (2 ^ 32 <= T)%Z /\ (T + 8 * size < 2 ^ 64)%Z.
  Hypothesis HTrd : rdn SEGS mem (Z_to_bv 64 T) (Z.to_nat (8 * size)) = Some bs.
  Hypothesis HTstk : (T + 8 * size <= usp - 80 \/ usp + 56 <= T)%Z.        (* [comment removed for export] *)
  Hypothesis HTP : (T + 8 * size <= P + 8 * tf \/ P + 8 * tf + 8 * (size + 1) <= T)%Z.
  Hypothesis HPstk : (usp + 56 <= P + 8 * tf \/ P + 8 * tf + 8 * (size + 1) <= usp - 80)%Z.
  Hypothesis Hret : ret_ok ret.

  #[local] Notation count := (size + 1)%Z.
  #[local] Notation hdr := (tag * 256 + size)%Z.

  (* [comment removed for export] *)
  Definition ss_mem1 (vra v8 v9 v18 v19 v20 v21 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
      (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 vra))
      (Z_to_bv 64 (usp - 16)) (word_to_le_bytes 8 v8))
      (Z_to_bv 64 (usp - 24)) (word_to_le_bytes 8 v9))
      (Z_to_bv 64 (usp - 32)) (word_to_le_bytes 8 v18))
      (Z_to_bv 64 (usp - 40)) (word_to_le_bytes 8 v19))
      (Z_to_bv 64 (usp - 48)) (word_to_le_bytes 8 v20))
      (Z_to_bv 64 (usp - 56)) (word_to_le_bytes 8 v21))
      (Z_to_bv 64 (usp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (usp + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  #[using="tf P T w Husp Hstk HA8 Hw HT HTstk HTP HPstk"] Lemma sstore_seg1 : forall regs,
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 SSB ->
    getr regs 11 = Z_to_bv 64 (usp + 40) -> getr regs 12 = Z_to_bv 64 (usp + 8) ->
    exists r1,
      msteps SEGS (mkst regs (0x726f8 : word) mem rom)
                  (mkst r1 (0x7281c : word) (ss_mem1 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)) rom)
      /\ getr r1 1 = (0x72770 : word) /\ getr r1 2 = Z_to_bv 64 (usp - 64) /\ getr r1 10 = Z_to_bv 64 SSB
      /\ getr r1 11 = Z_to_bv 64 count /\ getr r1 12 = Z_to_bv 64 (usp - 64)
      /\ getr r1 8 = Z_to_bv 64 (usp + 8) /\ getr r1 9 = Z_to_bv 64 SSB /\ getr r1 18 = Z_to_bv 64 count
      /\ getr r1 19 = Z_to_bv 64 (usp + 40) /\ getr r1 20 = Z_to_bv 64 size /\ getr r1 21 = Z_to_bv 64 tag
      /\ (forall r, r <> 1 -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 ->
                    r <> 18 -> r <> 19 -> r <> 20 -> r <> 21 -> getr r1 r = getr regs r).
  Proof.
    intros regs H1 H2 H10 H11 H12.
    destruct HA8 as [HA8c _]. destruct Hw as (Ew & Hsz & Htg).
    assert (Hwr : (0 <= w < 2 ^ 64)%Z) by (rewrite Ew; lia).
    assert (Hlo : (w mod 2 ^ 32 = size)%Z) by (rewrite Ew, Z.mod_add by lia; apply Z.mod_small; lia).
    assert (Hhi : (w / 2 ^ 32 = tag)%Z) by (rewrite Ew, Z.div_add by lia; rewrite Z.div_small by lia; lia).
    (* [comment removed for export] *)
    eapply (runs_trans SEGS _ (fun r => mkst r (0x72750 : word)
              (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
                 (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 ret))
                 (Z_to_bv 64 (usp - 16)) (word_to_le_bytes 8 (getr regs 8)))
                 (Z_to_bv 64 (usp - 24)) (word_to_le_bytes 8 (getr regs 9)))
                 (Z_to_bv 64 (usp - 32)) (word_to_le_bytes 8 (getr regs 18)))
                 (Z_to_bv 64 (usp - 40)) (word_to_le_bytes 8 (getr regs 19)))
                 (Z_to_bv 64 (usp - 48)) (word_to_le_bytes 8 (getr regs 20)))
                 (Z_to_bv 64 (usp - 56)) (word_to_le_bytes 8 (getr regs 21))) rom)
              (fun r => getr r 1 = ret /\ getr r 2 = Z_to_bv 64 (usp - 64) /\ getr r 9 = Z_to_bv 64 1587848
                        /\ getr r 8 = Z_to_bv 64 (usp + 8) /\ getr r 19 = Z_to_bv 64 (usp + 40)
                        /\ getr r 20 = Z_to_bv 64 size /\ getr r 21 = Z_to_bv 64 tag
                        /\ (forall x, x <> 2 -> x <> 8 -> x <> 9 -> x <> 10 -> x <> 11 -> x <> 19 -> x <> 20 -> x <> 21 -> getr r x = getr regs x))).
    - assert (PRE : exists r0,
        msteps SEGS (mkst regs (0x726f8 : word) mem rom)
          (mkst r0 (0x72748 : word)
              (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
                 (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 ret))
                 (Z_to_bv 64 (usp - 16)) (word_to_le_bytes 8 (getr regs 8)))
                 (Z_to_bv 64 (usp - 24)) (word_to_le_bytes 8 (getr regs 9)))
                 (Z_to_bv 64 (usp - 32)) (word_to_le_bytes 8 (getr regs 18)))
                 (Z_to_bv 64 (usp - 40)) (word_to_le_bytes 8 (getr regs 19)))
                 (Z_to_bv 64 (usp - 48)) (word_to_le_bytes 8 (getr regs 20)))
                 (Z_to_bv 64 (usp - 56)) (word_to_le_bytes 8 (getr regs 21))) rom)
        /\ getr r0 1 = ret /\ getr r0 2 = Z_to_bv 64 (usp - 64) /\ getr r0 9 = Z_to_bv 64 1587848
        /\ getr r0 8 = Z_to_bv 64 (usp + 8) /\ getr r0 19 = Z_to_bv 64 (usp + 40)
        /\ getr r0 20 = Z_to_bv 64 size /\ getr r0 21 = Z_to_bv 64 tag /\ getr r0 10 = Z_to_bv 64 255
        /\ (forall x, x <> 2 -> x <> 8 -> x <> 9 -> x <> 10 -> x <> 11 -> x <> 19 -> x <> 20 -> x <> 21 -> getr r0 x = getr regs x)).
      { eexists. split.
        - ai F_726f8 D_726f8.
          ast F_726fc D_726fc (Z_to_bv 64 (usp - 8)) ret ltac:(okw Hstk).
          ast F_72700 D_72700 (Z_to_bv 64 (usp - 16)) (getr regs 8) ltac:(okw Hstk).
          ast F_72704 D_72704 (Z_to_bv 64 (usp - 24)) (getr regs 9) ltac:(okw Hstk).
          ast F_72708 D_72708 (Z_to_bv 64 (usp - 32)) (getr regs 18) ltac:(okw Hstk).
          ast F_7270c D_7270c (Z_to_bv 64 (usp - 40)) (getr regs 19) ltac:(okw Hstk).
          ast F_72710 D_72710 (Z_to_bv 64 (usp - 48)) (getr regs 20) ltac:(okw Hstk).
          ast F_72714 D_72714 (Z_to_bv 64 (usp - 56)) (getr regs 21) ltac:(okw Hstk).
          ai F_72718 D_72718.
          (* [comment removed for export] *)
          ld_step F_7271c D_7271c (word_to_le_bytes 4 (Z_to_bv 64 size)) (Z_to_bv 64 size)
            ltac:(peelz; rewrite <- Hlo; apply rdn_lo32; [lia | replace (usp + 40 + 8)%Z with (usp + 48)%Z by lia; exact HA8c])
            ltac:(rewrite bytes_le_cell by (first [cbn; lia | lia]); symmetry; apply u64_lit; lia).
          rewrite v_lw_lit by lia.
          ld_step F_72720 D_72720 (word_to_le_bytes 4 (Z_to_bv 64 tag)) (Z_to_bv 64 tag)
            ltac:(peelz; rewrite <- Hhi; replace (usp + 40 + 12)%Z with (usp + 48 + 4)%Z by lia; apply rdn_hi32; [lia | lia | lia | exact HA8c])
            ltac:(rewrite bytes_le_cell by (first [cbn; lia | lia]); symmetry; apply u64_lit; lia).
          rewrite v_lw_lit by lia.
          (* [comment removed for export] *)
          ai F_72724 D_72724. rewrite v_or_lit by lia.
          stepb_tk F_72728 D_72728 ltac:(pin; rewrite c_eq_zbv; [apply Z.eqb_neq; pose proof (lor_range size tag 64); pose proof (Z.lor_nonneg size tag); intros E; apply Z.lor_eq_0_iff in E; lia | pose proof (lor_range size tag 64); lia | lia]).
          (* [comment removed for export] *)
          ai F_72734 D_72734.
          ai F_72738 D_72738.
          stepb_ft F_7273c D_7273c ltac:(pin; rewrite c_ltu_zbv by lia; apply Z.ltb_lt; lia).
          ai F_72740 D_72740.
          ai F_72744 D_72744.
          apply mst_refl.
        - repeat split; gr; try reflexivity; try assumption.
          intros x N2 N8 N9 N10 N11 N19 N20 N21.
          repeat (rewrite getr_other by (first [exact N2|exact N8|exact N9|exact N10|exact N11|exact N19|exact N20|exact N21])). reflexivity. }
      destruct PRE as (r0 & RUN0 & Q1 & Q2 & Q9 & Q8 & Q19 & Q20 & Q21 & Q10 & QR).
      destruct (Z_lt_le_dec size 255) as [Hlt|Hge].
      + exists r0. split.
        * eapply msteps_trans; [exact RUN0|].
          stepb_tk F_72748 D_72748 ltac:(pin; rewrite c_ltu_zbv by lia; apply Z.ltb_lt; lia).
          apply mst_refl.
        * repeat split; assumption.
      + eexists. split.
        * eapply msteps_trans; [exact RUN0|].
          stepb_ft F_72748 D_72748 ltac:(pin; rewrite c_ltu_zbv by lia; apply Z.ltb_ge; lia).
          ai F_7274c D_7274c.
          apply mst_refl.
        * repeat split; gr; try assumption. { replace size with 255%Z by lia. reflexivity. }
          intros x N2 N8 N9 N10 N11 N19 N20 N21. rewrite getr_other by exact N20. apply QR; assumption.
    - cbv beta. intros r0 (Q1 & Q2 & Q9 & Q8 & Q19 & Q20 & Q21 & QR).
      eexists. split.
      + (* [comment removed for export] *)
        ast F_72750 D_72750 (Z_to_bv 64 (usp - 64)) (Z_to_bv 64 0) ltac:(okw Hstk).
        ast F_72754 D_72754 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 0) ltac:(okw Hstk).
        (* [comment removed for export] *)
        ai F_72758 D_72758.
        ai F_7275c D_7275c.
        ai F_72760 D_72760.
        ai F_72764 D_72764.
        ai F_72768 D_72768.
        stepj F_7276c D_7276c.
        unfold ss_mem1. apply mst_refl.
      + repeat split; gr; try reflexivity; try assumption; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity).
        intros x N1 N2 N8 N9 N10 N11 N12 N13 N18 N19 N20 N21.
        repeat (rewrite getr_other by (first [exact N1|exact N2|exact N8|exact N9|exact N10|exact N11|exact N12|exact N13|exact N18|exact N19|exact N20|exact N21])).
        apply QR; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition ss_mem (vra v8 v9 v18 v19 v20 v21 : word) : word -> option byte :=
    let m1 := ss_mem1 vra v8 v9 v18 v19 v20 v21 in
    let m2 := alloc_mem m1 (usp - 64) tf count (0x72770 : word) (Z_to_bv 64 (usp + 8)) in
    let m3 := wbytes m2 (Z_to_bv 64 (P + 8 * tf)) (word_to_le_bytes 8 (Z_to_bv 64 hdr)) in
    let m4 := wbytes m3 (Z_to_bv 64 (P + 8 * tf + 8)) bs in
    let m5 := wbytes m4 (Z_to_bv 64 (SSB + 24)) (word_to_le_bytes 4 (Z_to_bv 64 (st + count))) in
    wbytes m5 (Z_to_bv 64 (usp + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Let LENBS : length bs = Z.to_nat (8 * size).
  Proof. exact (rdn_length _ _ _ _ _ HTrd). Qed.

  Ltac peelb := repeat (rewrite rdn_wbytes_out by (rewrite ?length_N_to_le_bytes, ?LENBS; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)).
  Ltac aldb F D vv pre := ld_step F D (word_to_le_bytes 8 vv) vv ltac:(pre; peelb; hit8) ltac:(apply bytes_le_to_Z_8).

  (* [comment removed for export] *)
  #[using="st w bs Husp HA0 Hw Hroom HPblk HPok HT HTrd HTstk HTP HPstk LENBS"] Lemma sstore_seg2 : forall r2 (vra v8 v9 v18 v19 v20 v21 : word),
    let m2 := alloc_mem (ss_mem1 vra v8 v9 v18 v19 v20 v21) (usp - 64) tf count (0x72770 : word) (Z_to_bv 64 (usp + 8)) in
    getr r2 10 = Z_to_bv 64 (P + 8 * tf) -> getr r2 2 = Z_to_bv 64 (usp - 64) ->
    getr r2 19 = Z_to_bv 64 (usp + 40) -> getr r2 20 = Z_to_bv 64 size -> getr r2 21 = Z_to_bv 64 tag ->
    exists r3,
      msteps SEGS (mkst r2 (0x72770 : word) m2 rom)
                  (mkst r3 both_imemcpy_entry (wbytes m2 (Z_to_bv 64 (P + 8 * tf)) (word_to_le_bytes 8 (Z_to_bv 64 hdr))) rom)
      /\ getr r3 1 = (0x72790 : word) /\ getr r3 10 = Z_to_bv 64 (P + 8 * tf + 8) /\ getr r3 11 = Z_to_bv 64 T
      /\ getr r3 12 = Z_to_bv 64 (8 * size)
      /\ (forall r, r <> 1 -> r <> 10 -> r <> 11 -> r <> 12 -> getr r3 r = getr r2 r).
  Proof.
    intros r2 vra v8 v9 v18 v19 v20 v21 m2 R10 R2 R19 R20 R21.
    destruct HA0 as [HA0c HTr]. destruct Hw as (Ew & Hsz & Htg). cbn in HTr.
    eexists. split.
    - (* [comment removed for export] *)
      stepb_ft F_72770 D_72770 ltac:(pin; rewrite c_eq_zbv by lia; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      ai F_72774 D_72774. rewrite v_slliw_lit by lia.
      (* [comment removed for export] *)
      ld_step F_72778 D_72778 (word_to_le_bytes 8 (Z_to_bv 64 T)) (Z_to_bv 64 T)
        ltac:(unfold m2, alloc_mem, ss_mem1; peelb; rewrite ?Z.add_0_r; exact HA0c) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      ai F_7277c D_7277c. rewrite v_or_lit by lia. rewrite lor_disjoint_add by lia.
      replace (tag * 2 ^ 8 + size)%Z with hdr by lia.
      (* [comment removed for export] *)
      ast F_72780 D_72780 (Z_to_bv 64 (P + 8 * tf)) (Z_to_bv 64 hdr)
        ltac:(unfold m2, alloc_mem, ss_mem1; apply okr_store_ok; [lia | cbn; lia | repeat apply okr_wbytes; eapply okr_sub; [exact HPok | lia | lia] ]).
      (* [comment removed for export] *)
      ai F_72784 D_72784.
      ai F_72788 D_72788. rewrite v_slli_lit by lia.
      stepj F_7278c D_7278c.
      replace (size * 2 ^ 3)%Z with (8 * size)%Z by lia.
      apply mst_refl.
    - repeat split; gr; try reflexivity; try assumption; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity).
      intros x N1 N10 N11 N12.
      repeat (rewrite getr_other by (first [exact N1|exact N10|exact N11|exact N12])). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="T w Husp Hstk Hw Hst Hroom HPblk HT HTrd HTstk HTP HPstk Hret LENBS"] Lemma sstore_seg3 : forall r4 (v8 v9 v18 v19 v20 v21 : word),
    let m2 := alloc_mem (ss_mem1 ret v8 v9 v18 v19 v20 v21) (usp - 64) tf count (0x72770 : word) (Z_to_bv 64 (usp + 8)) in
    let m4 := wbytes (wbytes m2 (Z_to_bv 64 (P + 8 * tf)) (word_to_le_bytes 8 (Z_to_bv 64 hdr))) (Z_to_bv 64 (P + 8 * tf + 8)) bs in
    getr r4 2 = Z_to_bv 64 (usp - 64) -> getr r4 8 = Z_to_bv 64 (usp + 8) -> getr r4 9 = Z_to_bv 64 SSB -> getr r4 18 = Z_to_bv 64 count ->
    exists r5,
      msteps SEGS (mkst r4 (0x72790 : word) m4 rom) (mkst r5 ret (ss_mem ret v8 v9 v18 v19 v20 v21) rom)
      /\ getr r5 10 = Z_to_bv 64 (tf + 1) /\ getr r5 2 = Z_to_bv 64 usp /\ getr r5 1 = ret
      /\ getr r5 8 = v8 /\ getr r5 9 = v9 /\ getr r5 18 = v18 /\ getr r5 19 = v19 /\ getr r5 20 = v20 /\ getr r5 21 = v21
      /\ (forall r, r <> 1 -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 18 -> r <> 19 -> r <> 20 -> r <> 21 ->
                    getr r5 r = getr r4 r).
  Proof.
    intros r4 v8 v9 v18 v19 v20 v21 m2 m4 R2 R8 R9 R18.
    destruct Hw as (Ew & Hsz & Htg). destruct Hst as [Hstc Hstr]. cbn in Hstr.
    assert (Hx : (1 <= Z.lxor (size + 1 + st) 1048576 < 2 ^ 64)%Z).
    { pose proof (lxor_range64 (size + 1 + st) 1048576 ltac:(lia) ltac:(lia)).
      pose proof (lxor_nz (size + 1 + st) 1048576 ltac:(lia)). lia. }
    eexists. split.
    - (* [comment removed for export] *)
      ld_step F_72790 D_72790 (word_to_le_bytes 8 (Z_to_bv 64 tf)) (Z_to_bv 64 tf)
        ltac:(unfold m4, m2, alloc_mem; peelb; rewrite ?Z.add_0_r; hit8) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      ai F_72794 D_72794. rewrite v_srli_lit by lia.
      ai F_72798 D_72798. rewrite v_andi_m16_small by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      ai F_7279c D_7279c.
      ai F_727a0 D_727a0.
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply (step_amoadd_w _ _ _ rom _ _ _ 10 10 18 (1587848 + 24) st);
          [ exact F_727a4 | reflexivity | exact D_727a4 | gr; pin; f_equal; (ltac2:(LK.k [@LENBS; @Hstr; @Husp; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia) | (ltac2:(LK.k [@LENBS; @Hstr; @Husp; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia) | (ltac2:(LK.k [@LENBS; @Hstr; @Husp; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia) | reflexivity
          | split; [unfold m4, m2, alloc_mem, ss_mem1; peelb; exact Hstc | cbn; (ltac2:(LK.k [@LENBS; @Hstr; @Husp; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia)] | (ltac2:(LK.k [@LENBS; @Hstr; @Husp; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia)
          | apply okr_store_ok; [(ltac2:(LK.k [@LENBS; @Hstr; @Husp; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia) | cbn; (ltac2:(LK.k [@LENBS; @Hstr; @Husp; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia) | repeat apply okr_wbytes; apply okr_rw; (ltac2:(LK.k [@LENBS; @Hstr; @Husp; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia)] ]
        | step_simpl ].
      nz. rewrite (u64_lit (size + 1)) by lia. rewrite (Z.mod_small (st + (size + 1))) by lia.
      (* [comment removed for export] *)
      ai F_727a8 D_727a8.
      ai F_727ac D_727ac. rewrite v_slli_lit by (try lia; change (2 ^ 32)%Z with 4294967296%Z; lia).
      ai F_727b0 D_727b0. rewrite v_srli_lit by (change (2 ^ 32)%Z with 4294967296%Z; lia). rewrite Z.div_mul by lia.
      ai F_727b4 D_727b4.
      (* [comment removed for export] *)
      ld_step F_727b8 D_727b8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(unfold m4, m2, alloc_mem, ss_mem1; peelb; rewrite ?Z.add_0_r; hit8) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      ai F_727bc D_727bc. rewrite v_xor_lit by lia.
      (* [comment removed for export] *)
      ld_step F_727c0 D_727c0 (word_to_le_bytes 4 (Z_to_bv 64 tf)) (Z_to_bv 64 tf)
        ltac:(unfold m4, m2, alloc_mem; peelb; rewrite ?Z.add_0_r; replace (word_to_le_bytes 4 (Z_to_bv 64 tf)) with (word_to_le_bytes 4 (Z_to_bv 64 (tf mod 2 ^ 32))) by (rewrite Z.mod_small by (ltac2:(LK.k [@Husp; @LENBS; @Hstr; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia); reflexivity); apply rdn_lo32; [(ltac2:(LK.k [@Husp; @LENBS; @Hstr; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia) | hit8])
        ltac:(rewrite bytes_le_cell by (first [cbn; (ltac2:(LK.k [@Husp; @LENBS; @Hstr; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia) | (ltac2:(LK.k [@Husp; @LENBS; @Hstr; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia)]); symmetry; apply u64_lit; (ltac2:(LK.k [@Husp; @LENBS; @Hstr; @Hroom; @HPblk; @HT; @Hsz; @HTstk; @HTP; @HPstk]); lia)).
      rewrite v_lw_lit by lia.
      (* [comment removed for export] *)
      ai F_727c4 D_727c4. rewrite v_sltiu1_nz by lia.
      ai F_727c8 D_727c8.
      (* [comment removed for export] *)
      ast F_727cc D_727cc (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 0) ltac:(unfold m4, m2, alloc_mem, ss_mem1; okw Hstk).
      (* [comment removed for export] *)
      ai F_727d0 D_727d0. rewrite v_addiw_lit by lia.
      (* [comment removed for export] *)
      aldb F_727d4 D_727d4 ret ltac:(unfold m4, m2, alloc_mem, ss_mem1).
      aldb F_727d8 D_727d8 v8 ltac:(unfold m4, m2, alloc_mem, ss_mem1).
      aldb F_727dc D_727dc v9 ltac:(unfold m4, m2, alloc_mem, ss_mem1).
      aldb F_727e0 D_727e0 v18 ltac:(unfold m4, m2, alloc_mem, ss_mem1).
      aldb F_727e4 D_727e4 v19 ltac:(unfold m4, m2, alloc_mem, ss_mem1).
      aldb F_727e8 D_727e8 v20 ltac:(unfold m4, m2, alloc_mem, ss_mem1).
      aldb F_727ec D_727ec v21 ltac:(unfold m4, m2, alloc_mem, ss_mem1).
      ai F_727f0 D_727f0. replace (usp - 64 + 64)%Z with usp by lia.
      stepjr F_727f4 D_727f4 ret ltac:(gr; pin; first [reflexivity | assumption]). imm_norm. rewrite (Hret : v_jalr ret 0 = ret).
      replace (0 + 0)%Z with 0%Z by reflexivity.
      unfold ss_mem, m4, m2. apply mst_refl.
    - repeat split; gr; try reflexivity; try assumption; try (f_equal; lia).
      intros x N1 N2 N8 N9 N10 N11 N12 N18 N19 N20 N21.
      repeat (rewrite getr_other by (first [exact N1|exact N2|exact N8|exact N9|exact N10|exact N11|exact N12|exact N18|exact N19|exact N20|exact N21])). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="T w Husp Hstk HA0 HA8 Hw Htf HP Hst Hroom HPblk HPok HT HTrd HTstk HTP HPstk Hret LENBS"] Theorem sstore_walk : forall regs,
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 SSB ->
    getr regs 11 = Z_to_bv 64 (usp + 40) -> getr regs 12 = Z_to_bv 64 (usp + 8) ->
    exists r5,
      msteps SEGS (mkst regs (0x726f8 : word) mem rom)
                  (mkst r5 ret (ss_mem ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)) rom)
      /\ getr r5 10 = Z_to_bv 64 (tf + 1) /\ getr r5 2 = Z_to_bv 64 usp /\ getr r5 1 = ret
      /\ (forall r, r <> 5 -> r <> 6 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> getr r5 r = getr regs r).
  Proof.
    intros regs H1 H2 H10 H11 H12.
    pose proof Hw as (Ew & Hsz & Htg). pose proof Htf as [Htfc Htfr]. pose proof HP as [HPc HPr]. cbn in Htfr, HPr.
    destruct (sstore_seg1 regs H1 H2 H10 H11 H12) as (r1 & RUN1 & Q1 & Q2 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QR).
    set (m1 := ss_mem1 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)) in RUN1.
    destruct (alloc_walk m1 rom (usp - 64) tf P count (0x72770 : word)) with (regs := r1)
      as (r2 & RUN2 & A10 & A2 & A1 & AR); try assumption.
    { lia. }
    { unfold m1, ss_mem1. repeat apply okr_wbytes. eapply okr_sub; [exact Hstk | lia | lia]. }
    { split; [unfold m1, ss_mem1; peelb; exact Htfc | cbn; (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Husp; @Hroom]); lia)]. }
    { split; [unfold m1, ss_mem1; peelb; exact HPc | cbn; (ltac2:(LK.k [@LENBS; @Htfr; @HPr; @Husp; @HPblk]); lia)]. }
    { lia. }
    { lia. }
    { apply ret_ok_even; vm_compute; reflexivity. }
    assert (B19 : getr r2 19 = Z_to_bv 64 (usp + 40)) by (rewrite AR by (intros E; discriminate E); exact Q19).
    assert (B20 : getr r2 20 = Z_to_bv 64 size) by (rewrite AR by (intros E; discriminate E); exact Q20).
    assert (B21 : getr r2 21 = Z_to_bv 64 tag) by (rewrite AR by (intros E; discriminate E); exact Q21).
    rewrite Q8 in RUN2.
    destruct (sstore_seg2 r2 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) A10 A2 B19 B20 B21)
      as (r3 & RUN3 & C1 & C10 & C11 & C12 & CR).
    set (m3 := wbytes _ (Z_to_bv 64 (P + 8 * tf)) _) in RUN3.
    assert (CPY : cpyH SEGS m3 (Z_to_bv 64 (P + 8 * tf + 8)) (Z_to_bv 64 T) (8 * size) bs).
    { constructor.
      - lia.
      - exact LENBS.
      - rewrite LENBS. unfold m3, alloc_mem, ss_mem1. peelb. exact HTrd.
      - rewrite LENBS. unfold m3, alloc_mem, ss_mem1.
        apply okr_store_ok; [lia | lia | repeat apply okr_wbytes; eapply okr_sub; [exact HPok | lia | lia] ].
      - rewrite !u64_lit by lia. lia.
      - rewrite u64_lit by lia. lia.
      - rewrite u64_lit by lia. lia. }
    destruct (both_imemcpy m3 (Z_to_bv 64 (P + 8 * tf + 8)) (Z_to_bv 64 T) (8 * size) bs rom r3 (0x72790 : word) CPY
               ltac:(apply ret_ok_even; vm_compute; reflexivity) C1 C10 C11 C12) as (r4 & RUN4 & AG4).
    assert (D2 : getr r4 2 = Z_to_bv 64 (usp - 64)).
    { rewrite (AG4 2) by (cbn; intuition discriminate). rewrite CR by (intros E; discriminate E). exact A2. }
    assert (D8 : getr r4 8 = Z_to_bv 64 (usp + 8)).
    { rewrite (AG4 8) by (cbn; intuition discriminate). rewrite CR, AR by (intros E; discriminate E). exact Q8. }
    assert (D9 : getr r4 9 = Z_to_bv 64 SSB).
    { rewrite (AG4 9) by (cbn; intuition discriminate). rewrite CR, AR by (intros E; discriminate E). exact Q9. }
    assert (D18 : getr r4 18 = Z_to_bv 64 count).
    { rewrite (AG4 18) by (cbn; intuition discriminate). rewrite CR, AR by (intros E; discriminate E). exact Q18. }
    destruct (sstore_seg3 r4 (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) D2 D8 D9 D18)
      as (r5 & RUN5 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & ER).
    exists r5. split; [|split; [exact E10 | split; [exact E2 | split; [exact E1|]]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. exact RUN5.
    - intros r N5 N6 N10 N11 N12 N13 N14 N15.
      destruct (bv_eq_dec 5 r 1) as [->|N1]; [rewrite E1; symmetry; exact H1|].
      destruct (bv_eq_dec 5 r 2) as [->|N2]; [rewrite E2; symmetry; exact H2|].
      destruct (bv_eq_dec 5 r 8) as [->|N8]; [exact E8|].
      destruct (bv_eq_dec 5 r 9) as [->|N9]; [exact E9|].
      destruct (bv_eq_dec 5 r 18) as [->|N18]; [exact E18|].
      destruct (bv_eq_dec 5 r 19) as [->|N19]; [exact E19|].
      destruct (bv_eq_dec 5 r 20) as [->|N20]; [exact E20|].
      destruct (bv_eq_dec 5 r 21) as [->|N21]; [exact E21|].
      rewrite ER by assumption. rewrite (AG4 r) by (cbn; intuition congruence).
      rewrite CR by assumption. rewrite AR by assumption.
      destruct (bv_eq_dec 5 r 13) as [->|N13']; [congruence|].
      apply QR; assumption.
  Qed.
End SSTORE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NSTORE.
  Variables (mem rom : word -> option byte) (usp N tf P st T w size tag : Z) (h : word) (bs : list byte) (ret : word).
  Hypothesis Husp : (2 ^ 32 <= usp - 112)%Z /\ (usp + 24 < 2 ^ 64)%Z.
  Hypothesis Hstk : okr mem (usp - 112) 112.
  Hypothesis HA0 : cell64 mem (usp + 8) T.
  Hypothesis HA8 : cell64 mem (usp + 16) w.
  Hypothesis Hw : w = (size + tag * 2 ^ 32)%Z /\ (1 <= size <= 255)%Z /\ (0 <= tag < 256)%Z.
  Hypothesis Htf : cell64 mem SSB tf.
  Hypothesis HP : cell64 mem (SSB + 16) P.
  Hypothesis Hst : cell32 mem (SSB + 24) st.
  Hypothesis Hroom : (0 <= tf)%Z /\ (tf + 256 < 2 ^ 20)%Z /\ (0 <= st)%Z /\ (st + 256 < 2 ^ 20)%Z.
  Hypothesis HPblk : (0x607000 <= P)%Z /\ (P + 8 * 2 ^ 20 < 2 ^ 64)%Z.
  Hypothesis HPok : okr mem (P + 8 * tf) (8 * (size + 1)).
  Hypothesis HT : (2 ^ 32 <= T)%Z /\ (T + 8 * size < 2 ^ 64)%Z.
  Hypothesis HTrd : rdn SEGS mem (Z_to_bv 64 T) (Z.to_nat (8 * size)) = Some bs.
  Hypothesis HTstk : (T + 8 * size <= usp - 112 \/ usp + 24 <= T)%Z.
  Hypothesis HTP : (T + 8 * size <= P + 8 * tf \/ P + 8 * tf + 8 * (size + 1) <= T)%Z.
  Hypothesis HPstk : (usp + 24 <= P + 8 * tf \/ P + 8 * tf + 8 * (size + 1) <= usp - 112)%Z.
  (* [comment removed for export] *)
  Hypothesis HN : (0x607000 <= N)%Z /\ (N + 16 < 2 ^ 64)%Z.
  Hypothesis HNok : okr mem N 16.
  Hypothesis HNstk : (usp + 24 <= N \/ N + 16 <= usp - 112)%Z.
  Hypothesis HNT : (T + 8 * size <= N \/ N + 16 <= T)%Z.
  Hypothesis HNP : (P + 8 * tf + 8 * (size + 1) <= N \/ N + 16 <= P + 8 * tf)%Z.
  Hypothesis Hret : ret_ok ret.

  #[local] Notation count := (size + 1)%Z.

  (* [comment removed for export] *)
  Definition ns_mem1 (vra v8 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem
      (Z_to_bv 64 (usp - 8)) (word_to_le_bytes 8 vra))
      (Z_to_bv 64 (usp - 16)) (word_to_le_bytes 8 v8))
      (Z_to_bv 64 N) (word_to_le_bytes 8 h))
      (Z_to_bv 64 (usp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)).
  (* [comment removed for export] *)
  Definition ns_mem (vra v8 v9 v18 v19 v20 v21 : word) : word -> option byte :=
    wbytes (ss_mem (ns_mem1 vra v8) (usp - 32) tf P st size tag bs (0x74a38 : word) (Z_to_bv 64 N) v9 v18 v19 v20 v21)
           (Z_to_bv 64 (N + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (tf + 1))).

  Let LENBS2 : length bs = Z.to_nat (8 * size).
  Proof. exact (rdn_length _ _ _ _ _ HTrd). Qed.
  Ltac peeln := repeat (rewrite rdn_wbytes_out by (rewrite ?length_N_to_le_bytes, ?LENBS2; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)).

  #[using="T w Husp Hstk HA0 HA8 Hw Htf HP Hst Hroom HPblk HPok HT HTrd HTstk HTP HPstk HN HNok HNstk HNT HNP Hret LENBS2"] Theorem nstore_walk : forall regs,
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 N ->
    getr regs 12 = Z_to_bv 64 (usp + 8) -> getr regs 13 = h ->
    exists r',
      msteps SEGS (mkst regs (0x74a0c : word) mem rom)
                  (mkst r' ret (ns_mem ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)) rom)
      /\ getr r' 2 = Z_to_bv 64 usp /\ getr r' 1 = ret
      /\ (forall r, r <> 5 -> r <> 6 -> r <> 10 -> r <> 11 -> r <> 12 -> r <> 13 -> r <> 14 -> r <> 15 -> getr r' r = getr regs r).
  Proof.
    intros regs H1 H2 H10 H12 H13.
    pose proof Hw as (Ew & Hsz & Htg). pose proof Htf as [Htfc Htfr]. pose proof HP as [HPc HPr]. pose proof Hst as [Hstc Hstr].
    pose proof HA0 as [HA0c HA0r]. pose proof HA8 as [HA8c HA8r]. cbn in Htfr, HPr, Hstr, HA0r, HA8r.
    (* [comment removed for export] *)
    assert (SEG1 : exists r1,
      msteps SEGS (mkst regs (0x74a0c : word) mem rom) (mkst r1 (0x726f8 : word) (ns_mem1 ret (getr regs 8)) rom)
      /\ getr r1 1 = (0x74a38 : word) /\ getr r1 2 = Z_to_bv 64 (usp - 32) /\ getr r1 10 = Z_to_bv 64 SSB
      /\ getr r1 11 = Z_to_bv 64 (usp - 32 + 40) /\ getr r1 12 = Z_to_bv 64 (usp - 32 + 8) /\ getr r1 8 = Z_to_bv 64 N
      /\ (forall r, r <> 1 -> r <> 2 -> r <> 8 -> r <> 10 -> r <> 11 -> r <> 12 -> getr r1 r = getr regs r)).
    { eexists. split.
      - ai F_74a0c D_74a0c.
        ast F_74a10 D_74a10 (Z_to_bv 64 (usp - 8)) ret ltac:(okw Hstk).
        ast F_74a14 D_74a14 (Z_to_bv 64 (usp - 16)) (getr regs 8) ltac:(okw Hstk).
        ai F_74a18 D_74a18.
        ai F_74a1c D_74a1c.
        ast F_74a20 D_74a20 (Z_to_bv 64 N) h ltac:(okw HNok).
        ast F_74a24 D_74a24 (Z_to_bv 64 (usp - 24)) (Z_to_bv 64 0) ltac:(okw Hstk).
        match goal with |- context [wbytes (wbytes (wbytes (wbytes mem _ (word_to_le_bytes 8 ?a)) _ (word_to_le_bytes 8 ?b)) _ _) _ _] =>
          change (wbytes (wbytes (wbytes (wbytes mem _ _) _ _) _ _) _ _) with (ns_mem1 a b) end.
        ai F_74a28 D_74a28.
        ai F_74a2c D_74a2c.
        ai F_74a30 D_74a30.
        stepj F_74a34 D_74a34.
        apply mst_refl.
      - repeat split; gr; try reflexivity; try assumption; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity).
        intros x N1 N2 N8 N10 N11 N12.
        repeat (rewrite getr_other by (first [exact N1|exact N2|exact N8|exact N10|exact N11|exact N12])). reflexivity. }
    destruct SEG1 as (r1 & RUN1 & Q1 & Q2 & Q10 & Q11 & Q12 & Q8 & QR).
    destruct (sstore_walk (ns_mem1 ret (getr regs 8)) rom (usp - 32) tf P st T w size tag bs (0x74a38 : word)) with (regs := r1)
      as (r2 & RUN2 & A10 & A2 & A1 & AR); try assumption.
    { lia. }
    { unfold ns_mem1. repeat apply okr_wbytes. eapply okr_sub; [exact Hstk | lia | lia]. }
    { split; [unfold ns_mem1; peeln; replace (usp - 32 + 40)%Z with (usp + 8)%Z by lia; exact HA0c | cbn; lia]. }
    { split; [unfold ns_mem1; peeln; replace (usp - 32 + 48)%Z with (usp + 16)%Z by (ltac2:(LK.k [@Husp; @LENBS2; @Htfr; @HPr; @Hstr; @HA0r; @HA8r; @HN; @HNstk]); lia); exact HA8c | cbn; (ltac2:(LK.k [@Husp; @LENBS2; @Htfr; @HPr; @Hstr; @HA0r; @HA8r; @HN; @HNstk]); lia)]. }
    { split; [unfold ns_mem1; peeln; exact Htfc | cbn; lia]. }
    { split; [unfold ns_mem1; peeln; exact HPc | cbn; lia]. }
    { split; [unfold ns_mem1; peeln; exact Hstc | cbn; lia]. }
    { unfold ns_mem1. repeat apply okr_wbytes. exact HPok. }
    { unfold ns_mem1. peeln. exact HTrd. }
    { lia. }
    { lia. }
    { apply ret_ok_even; vm_compute; reflexivity. }
    (* [comment removed for export] *)
    rewrite Q8 in RUN2.
    set (m2 := ss_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in RUN2.
    assert (B8 : getr r2 8 = Z_to_bv 64 N) by (rewrite AR by (intros E; discriminate E); exact Q8).
    eexists. split; [|split; [|split]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      (* [comment removed for export] *)
      ld_step F_74a38 D_74a38 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(unfold m2, ss_mem; peeln; replace (usp - 32 + 8)%Z with (usp - 32 - 64 + 72)%Z by lia; hit8) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      ast F_74a3c D_74a3c (Z_to_bv 64 (N + 12)) (Z_to_bv 64 (tf + 1))
        ltac:(unfold m2, ss_mem, alloc_mem, ss_mem1, ns_mem1; okw HNok).
      (* [comment removed for export] *)
      stepb_ft F_74a40 D_74a40 ltac:(pin; reflexivity).
      (* [comment removed for export] *)
      ld_step F_74a44 D_74a44 (word_to_le_bytes 8 ret) ret
        ltac:(unfold m2, ss_mem, alloc_mem, ss_mem1, ns_mem1; peeln; hit8) ltac:(apply bytes_le_to_Z_8).
      ld_step F_74a48 D_74a48 (word_to_le_bytes 8 (getr regs 8)) (getr regs 8)
        ltac:(unfold m2, ss_mem, alloc_mem, ss_mem1, ns_mem1; peeln; hit8) ltac:(apply bytes_le_to_Z_8).
      ai F_74a4c D_74a4c. replace (usp - 32 + 32)%Z with usp by lia.
      stepjr F_74a50 D_74a50 ret ltac:(gr; pin; first [reflexivity | assumption]). imm_norm. rewrite (Hret : v_jalr ret 0 = ret).
      unfold ns_mem, m2.
      rewrite (QR 9), (QR 18), (QR 19), (QR 20), (QR 21) by (intros E; discriminate E).
      apply mst_refl.
    - gr. reflexivity.
    - gr. reflexivity.
    - intros r N5 N6 N10 N11 N12 N13 N14 N15.
      destruct (bv_eq_dec 5 r 1) as [->|N1]; [gr; symmetry; exact H1|].
      destruct (bv_eq_dec 5 r 2) as [->|N2]; [gr; symmetry; exact H2|].
      destruct (bv_eq_dec 5 r 8) as [->|N8]; [gr; reflexivity|].
      repeat (rewrite getr_other by (first [exact N1|exact N2|exact N8|exact N11])).
      rewrite AR by assumption. apply QR; assumption.
  Qed.
End NSTORE.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesRP AsanNodesRPSoundG AsanNodesRPAsan AsanNodesPG AsanNodesPGSoundG AsanRegionPoisoned AsanIcptCheck AsanPartialGranule AsanPlanImages.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan AsanNodesFX SumsAsanSpecs AsanPGVal AsanPGValSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma asan_idst_spec : idst_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom p n b1 bs1 bs2 regs Hp Hp8 Hn Hpn C1 C2 Hz Hl Hw1 Hw2 H10 H20.
  destruct (icpt_dst_check mem rom p n b1 bs1 bs2 Hp Hp8 Hn Hpn C1 C2 Hz Hl Hw1 Hw2 regs H10 H20) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  match type of Hms with msteps _ (mkst _ ?pp _ _) (mkst _ ?qq _ _) =>
    replace (Z_to_bv 64 (PGN.IDST_ENTRY RPN.RP_ASAN)) with pp by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 (PGN.IDST_EXIT RPN.RP_ASAN)) with qq by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

(* [comment removed for export] *)
Lemma asan_pg_spec : pg_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom p n regs Hp Hp8 Hn Hrng C1 C2 C3 C4 C5 C6 C7 C8 Cfl Cpp Ccp Hst H9 H22 H20.
  destruct (partial_granule mem rom p n Hp Hp8 Hn Hrng (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 C8)))))))
              Cfl Cpp Ccp Hst regs H9 H22 H20) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  match type of Hms with msteps _ (mkst _ ?pp _ _) (mkst _ ?qq _ _) =>
    replace (Z_to_bv 64 (PGN.PG_ENTRY RPN.RP_ASAN)) with pp by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 (PGN.PG_EXIT RPN.RP_ASAN)) with qq by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma asan_rdn1_mem : forall mem (a : Z) (b : byte),
  img_hi ASAN <= a < 2 ^ 64 -> rdn ASEGS mem (Z_to_bv 64 a) 1 = Some [b] -> mem (Z_to_bv 64 a) = Some b.
Proof.
  intros mem a b Ha H. cbn [rdn] in H. cbn [img_hi ASAN] in Ha.
  destruct (mem (Z_to_bv 64 a)) as [b0|] eqn:Hm.
  - cbn in H. injection H as ->. reflexivity.
  - exfalso. rewrite (seg_rom_off_hull ASEGS ASAN asan_in_hull (Z_to_bv 64 a)) in H; [discriminate|].
    unfold in_hull. rewrite zbv_u by lia. cbn [img_lo img_hi ASAN].
    apply Bool.andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Lemma asan_rpp_spec : rpp_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem beg n usp regs ra b1 Hn Hbeg Hbeg8 Hrng Husp Hdisj Hz Hl Hstk C1 C2 C3 C4 C5 C6 C7 C8 Hret H1 H2 H10 H11.
  pose proof (rpp_arith beg n Hbeg Hbeg8 ltac:(lia)) as (D1 & D2 & D3 & D4 & D5).
  unfold RPN.kHighBeg, RPN.kHighEnd in Hrng.
  assert (HRb : beg + n <= 140737488355327) by (unfold RPN.kLowEnd in Hrng; destruct Hrng as [HR|[HR1 HR2]]; lia).
  assert (HR : (beg + n <= kLowEnd)%Z \/ (kHighBeg <= beg /\ beg + n <= kHighEnd)%Z)
    by (unfold kLowEnd, kHighBeg, kHighEnd; unfold RPN.kLowEnd in Hrng; lia).
  assert (Hq : 0 <= n / 8) by (apply Z.div_pos; lia).
  assert (exists b1', rpH mem beg n usp b1') as [b1' H].
  { destruct (Z.eqb_spec (n mod 8) 0) as [R0|R1].
    - exists (Z_to_bv 8 0). constructor; try assumption; try lia.
      + intros g Hg. replace (SB + g) with (RPN.SB + beg / 8 + (g - beg / 8)) by (unfold RPN.SB, SB; lia). apply Hz. lia.
      + replace (SB + (beg + n - 1) / 8) with (RPN.SB + beg / 8 + (n / 8 - 1)) by (unfold RPN.SB, SB; lia). apply Hz. lia.
      + left. reflexivity.
      + unfold cells, cell. repeat split; assumption.
    - destruct (Hl R1) as [Hrd Hv]. exists b1. constructor; try assumption; try lia.
      + intros g Hg. replace (SB + g) with (RPN.SB + beg / 8 + (g - beg / 8)) by (unfold RPN.SB, SB; lia). apply Hz. lia.
      + replace (SB + (beg + n - 1) / 8) with (RPN.SB + beg / 8 + n / 8) by (unfold RPN.SB, SB; lia).
        apply asan_rdn1_mem; [|exact Hrd]. cbn [img_hi ASAN]. unfold RPN.SB.
        assert (Hb8 : 0 <= beg / 8 <= 140737488355327 / 8) by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
        change (140737488355327 / 8) with 17592186044415 in Hb8.
        assert (Hn8 : n / 8 <= 2 ^ 40 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 40 / 8) with 137438953472 in Hn8. lia.
      + right. rewrite D4. replace (n mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact R1).
        pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
      + unfold cells, cell. repeat split; assumption. }
  destruct (as_region_is_poisoned mem (seg_rom ASEGS) beg n usp b1' H regs ra Hret H1 H2 H10 H11)
    as (regs' & Hms & Ha0 & Hsp & Hra & Hkeep).
  exists regs', (rp_frame mem usp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  split; [|split; [|split; [exact Ha0|split]]].
  - cbn [RPN.rp_entry RPN.RP_ASAN].
    match type of Hms with msteps _ (mkst _ ?pp _ _) _ => replace (Z_to_bv 64 0x569ac) with pp by (apply bv_eq; reflexivity) end.
    exact Hms.
  - intros r Hr0 Hcs. destruct (bv_eq_dec 5 r 2%bv) as [->|Hne2]; [rewrite Hsp, H2; reflexivity|].
    apply Hkeep. destruct (rp_clob r) eqn:E; [|reflexivity]. exfalso. exact (Hcs (rp_clob_sub r E)).
  - intros x Hx. unfold rp_frame.
    rewrite !wbytes_out; try reflexivity; rewrite ?length_N_to_le_bytes, ?zbv_u by lia; lia.
  - unfold rp_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma asan_rpin_spec : rpin_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem beg n usp B N regs ra Hn HB HB8 HN8 Hlo Hhi Hrng Husp Hdisj Hz Hstk C1 C2 C3 C4 C5 C6 C7 C8 Hret H1 H2 H10 H11.
  pose proof (rpin_arith B N beg n HB HB8 HN8 Hlo Hhi ltac:(lia)) as (D1 & D2 & D3).
  unfold RPN.kHighBeg, RPN.kHighEnd in Hrng.
  assert (HR : (beg + n <= kLowEnd)%Z \/ (kHighBeg <= beg /\ beg + n <= kHighEnd)%Z)
    by (unfold kLowEnd, kHighBeg, kHighEnd; unfold RPN.kLowEnd in Hrng; lia).
  assert (H : rpH mem beg n usp (Z_to_bv 8 0)).
  { constructor; try assumption; try lia.
    + assert ((beg + n - 1) / 8 <= (B + N - 1) / 8) by (apply Z.div_le_mono; lia). unfold SB. unfold RPN.SB in Hdisj. lia.
    + intros g Hg. replace (SB + g) with (RPN.SB + B / 8 + (g - B / 8)) by (unfold RPN.SB, SB; lia). apply Hz. lia.
    + replace (SB + (beg + n - 1) / 8) with (RPN.SB + B / 8 + ((beg + n - 1) / 8 - B / 8)) by (unfold RPN.SB, SB; lia). apply Hz. lia.
    + left. reflexivity.
    + unfold cells, cell. repeat split; assumption. }
  destruct (as_region_is_poisoned mem (seg_rom ASEGS) beg n usp (Z_to_bv 8 0) H regs ra Hret H1 H2 H10 H11)
    as (regs' & Hms & Ha0 & Hsp & Hra & Hkeep).
  exists regs', (rp_frame mem usp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  split; [|split; [|split; [exact Ha0|split]]].
  - cbn [RPN.rp_entry RPN.RP_ASAN].
    match type of Hms with msteps _ (mkst _ ?pp _ _) _ => replace (Z_to_bv 64 0x569ac) with pp by (apply bv_eq; reflexivity) end.
    exact Hms.
  - intros r Hr0 Hcs. destruct (bv_eq_dec 5 r 2%bv) as [->|Hne2]; [rewrite Hsp, H2; reflexivity|].
    apply Hkeep. destruct (rp_clob r) eqn:E; [|reflexivity]. exfalso. exact (Hcs (rp_clob_sub r E)).
  - intros x Hx. unfold rp_frame.
    rewrite !wbytes_out; try reflexivity; rewrite ?length_N_to_le_bytes, ?zbv_u by lia; lia.
  - unfold rp_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

Lemma asan_img_gfl : img_cell ASEGS (RPN.rp_gfl RPN.RP_ASAN) (RPN.rp_cfl RPN.RP_ASAN).
Proof. cbn [RPN.rp_gfl RPN.rp_cfl RPN.RP_ASAN]. img_cell_vm. Qed.

Lemma asan_isrc_spec : isrc_spec ASEGS RPN.RP_ASAN.
Proof.
  intros mem rom src s3v regs Hsrc Hs3 C1 C2 Hz1 Hz2 H11 H19.
  destruct (icpt_src_check mem rom src s3v Hsrc Hs3 C1 C2 Hz1 Hz2 regs H11 H19) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 (PGN.ISRC_ENTRY RPN.RP_ASAN)) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 (PGN.ISRC_EXIT RPN.RP_ASAN)) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AsanNode.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.

Theorem asan_pg_ext_sound : ext_stmt ASEGS ASAN nx0 LIMIT (PGN.xn ASEGS nx0 RPN.RP_ASAN) SINV argH FS0.
Proof.
  eapply (pg_xn_sound ASEGS ASAN nx0 LIMIT); try eassumption;
    first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_segs_wr | exact asan_rp_img | exact asan_isrc_spec | exact asan_idst_spec | exact asan_pg_spec | exact asan_rpp_spec | exact asan_rpin_spec | exact asan_img_gfl | idtac ].
Qed.
End AsanNode.

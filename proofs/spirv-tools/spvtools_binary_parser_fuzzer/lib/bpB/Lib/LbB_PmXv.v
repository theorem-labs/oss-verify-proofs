(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Xv.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition xv_ok (w : pmwA H) (LBs : list block) (ftbl : list (Z * SymExec3.SX2.expr)) (iv : Z * Z) : Prop :=
    xp_ok H w ftbl iv
    \/ (fst iv <= snd iv /\ wa_p w + O_M1 <= fst iv /\ snd iv <= wa_p w + PARSER_SIZE)
    \/ (fst iv <= snd iv /\ exists b, In b LBs /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
    \/ (fst iv <= snd iv /\ exists b, In b LBs /\ sh (blk_addr b) <= fst iv /\ snd iv <= sh (blk_addr b) + nsh (blk_size b))
    \/ (fst iv <= snd iv /\ wa_s1 w <= fst iv /\ snd iv <= wa_s1 w + PM_RF_TOP).

  Lemma nodup_app_ids : forall (l1 l2 : list block) b1 b2, List.NoDup (map blk_id (l1 ++ l2)) -> List.In b1 l1 -> List.In b2 l2 ->
    blk_id b1 <> blk_id b2.
  Proof.
    induction l1 as [|a l1 IH]; intros l2 b1 b2 ND H1 H2; [destruct H1|].
    cbn [app map] in ND. inversion ND as [|x l NI ND']; subst.
    destruct H1 as [<-|H1].
    - intros E. apply NI. rewrite E. apply List.in_map. apply List.in_or_app. right. exact H2.
    - exact (IH l2 b1 b2 ND' H1 H2).
  Qed.

  Lemma lbs_blk : forall (w : pmwA H) s LB LBs TB m b, as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) -> In b LBs ->
    In b LB /\ ablock_range H (blk_addr b) (blk_size b).
  Proof.
    intros w s LB LBs TB m b RH P Hb.
    assert (HinLB : In b LB) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; right; apply in_app_iff; left; exact Hb).
    split; [exact HinLB|]. exact (ah_blocks H HH _ _ _ _ RH HinLB).
  Qed.

  Lemma sh_apart : forall A n B k, 0 <= A -> 0 <= n -> 0 <= B -> 0 <= k -> A mod 8 = 0 -> B mod 8 = 0 ->
    (A + n + 8 <= B \/ B + k + 8 <= A) ->
    sh A + nsh n <= sh B \/ sh B + nsh k <= sh A.
  Proof. intros A n B k H0 H1 H2 H3 H4 H5 D. unfold sh, nsh. Z.div_mod_to_equations. lia. Qed.

  Lemma xv_loc : forall w s LB LBs TB m ftbl iv, pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) ->
    xv_ok w LBs ftbl iv -> snd iv <= aceil \/ (wa_s1 w <= fst iv /\ snd iv <= wa_s1 w + PM_RF_TOP).
  Proof.
    intros w s LB LBs TB m ftbl iv OK RH P Hiv. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    destruct Hiv as [[(I0 & I1 & I2 & _)|ETD]|[(I0 & I1 & I2)|[(I0 & b & Hb & I1 & I2)|[(I0 & b & Hb & I1 & I2)|(I0 & I1 & I2)]]]].
    - left. lia.
    - left. subst iv. cbn [snd]. unfold RtB_Td.ATDLOC. pose proof aceil_facts as ((AF1 & _) & _ & _). lia.
    - left. unfold PARSER_SIZE in *. lia.
    - left. destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)). lia.
    - left. destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      pose proof (aapp_bounds _ _ RAPP Rn) as (B1 & B2 & B3 & B4 & B5).
      assert (sh (blk_addr b) + nsh (blk_size b) <= sh aceil).
      { unfold sh, nsh. pose proof aceil_al8. Z.div_mod_to_equations. lia. }
      assert (sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; pose proof aceil_facts as ((? & ?) & _ & _); Z.div_mod_to_equations; lia).
      lia.
    - right. lia.
  Qed.

  Definition xv_ok4 (w : pmwA H) (LBs : list block) (ftbl : list (Z * SymExec3.SX2.expr)) (iv : Z * Z) : Prop :=
    xp_ok H w ftbl iv
    \/ (fst iv <= snd iv /\ wa_p w + O_M1 <= fst iv /\ snd iv <= wa_p w + PARSER_SIZE)
    \/ (fst iv <= snd iv /\ exists b, In b LBs /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
    \/ (fst iv <= snd iv /\ exists b, In b LBs /\ sh (blk_addr b) <= fst iv /\ snd iv <= sh (blk_addr b) + nsh (blk_size b)).
  Lemma xv_ok4_ok : forall w LBs ftbl iv, xv_ok4 w LBs ftbl iv -> xv_ok w LBs ftbl iv.
  Proof. intros w LBs ftbl iv [A|[A|[A|A]]]; [left | right; left | right; right; left | right; right; right; left]; exact A. Qed.
  Lemma xv4_below : forall w s LB LBs TB m ftbl iv, pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) ->
    xv_ok4 w LBs ftbl iv -> snd iv <= aceil.
  Proof.
    intros w s LB LBs TB m ftbl iv OK RH P Hiv. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    destruct Hiv as [[(I0 & I1 & I2 & _)|ETD]|[(I0 & I1 & I2)|[(I0 & b & Hb & I1 & I2)|(I0 & b & Hb & I1 & I2)]]].
    - lia.
    - subst iv. cbn [snd]. unfold RtB_Td.ATDLOC. pose proof aceil_facts as ((AF1 & _) & _ & _). lia.
    - unfold PARSER_SIZE in *. lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)). lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      pose proof (aapp_bounds _ _ RAPP Rn) as (B1 & B2 & B3 & B4 & B5).
      assert (sh (blk_addr b) + nsh (blk_size b) <= sh aceil).
      { unfold sh, nsh. pose proof aceil_al8. Z.div_mod_to_equations. lia. }
      assert (sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; pose proof aceil_facts as ((? & ?) & _ & _); Z.div_mod_to_equations; lia).
      lia.
  Qed.

  Lemma ap_Xv_fso : forall w s LB LBs TB m ftbl X O n, pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) ->
    Forall (xv_ok w LBs ftbl) X -> as_FSB H <= O -> O + n <= as_FSB H + AFS_SIZE -> 0 <= n ->
    (O + n <= wa_ff w \/ wa_ff w + 16384 <= O) -> (O + n <= wa_p w + O_M1 \/ wa_p w + PARSER_SIZE <= O) ->
    Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) X.
  Proof.
    intros w s LB LBs TB m ftbl X O n OK RH P FX HO1 HO2 Hn HF HP. eapply Forall_impl; [| exact FX].
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & _).
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    intros iv Hiv. cbn beta.
    destruct Hiv as [[(I0 & I1 & I2 & _)|ETD]|[(I0 & I1 & I2)|[(I0 & b & Hb & I1 & I2)|[(I0 & b & Hb & I1 & I2)|(I0 & I1 & I2)]]]].
    - destruct HF; lia.
    - subst iv. cbn [fst snd]. right. unfold RtB_Td.ATDLOC, AIMG_TOP in *. lia.
    - destruct HP; lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      destruct RF; lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (blk_addr b) (blk_size b) FS4 ltac:(lia) ltac:(pose proof (aapp_bounds _ _ RAPP Rn); lia) Rn) as D.
      destruct D; lia.
    - left. lia.
  Qed.

  Lemma ap_Xv_ffo : forall w s LB LBs TB m ftbl X O n, pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) ->
    Forall (xv_ok w LBs ftbl) X -> wa_ff w <= O -> O + n <= wa_ff w + 16384 -> 0 <= n ->
    Forall (fun iv : Z * Z => xp_ok H w ftbl iv -> O + n <= fst iv \/ snd iv <= O) X ->
    Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) X.
  Proof.
    intros w s LB LBs TB m ftbl X O n OK RH P FX HO1 HO2 Hn FXP.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF.
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    apply Forall_forall. intros iv Hin. pose proof (proj1 (Forall_forall _ _) FX iv Hin) as Hiv.
    pose proof (proj1 (Forall_forall _ _) FXP iv Hin) as Hxp.
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct Hiv as [Hx|[(I0 & I1 & I2)|[(I0 & b & Hb & I1 & I2)|[(I0 & b & Hb & I1 & I2)|(I0 & I1 & I2)]]]].
    - exact (Hxp Hx).
    - unfold PARSER_SIZE, O_V1, O_M1 in *. destruct PFF; lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      unfold AFS_HDR in *. destruct RF; lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      pose proof (aapp_disjoint_sh (wa_ff w) 16384 (blk_addr b) (blk_size b) FA ltac:(lia) ltac:(pose proof (aapp_bounds _ _ RAPP Rn); lia) Rn) as D.
      destruct D; lia.
    - left. lia.
  Qed.

  Lemma ap_Xv_fssh : forall w s LB LBs TB m ftbl X O n, pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) ->
    Forall (xv_ok w LBs ftbl) X -> as_FSB H <= O -> O + n <= as_FSB H + AFS_SIZE -> 0 <= n ->
    Forall (fun iv : Z * Z => xp_ok H w ftbl iv -> sh O + nsh n <= fst iv \/ snd iv <= sh O) X ->
    Forall (fun iv : Z * Z => sh O + nsh n <= fst iv \/ snd iv <= sh O) X.
  Proof.
    intros w s LB LBs TB m ftbl X O n OK RH P FX HO1 HO2 Hn FXP.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    pose proof (aapp_bounds _ _ FS4 ltac:(unfold AFS_SIZE; lia)) as (B1 & B2 & B3 & B4 & B5).
    apply Forall_forall. intros iv Hin. pose proof (proj1 (Forall_forall _ _) FX iv Hin) as Hiv.
    pose proof (proj1 (Forall_forall _ _) FXP iv Hin) as Hxp.
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct Hiv as [Hx|[(I0 & I1 & I2)|[(I0 & b & Hb & I1 & I2)|[(I0 & b & Hb & I1 & I2)|(I0 & I1 & I2)]]]].
    - exact (Hxp Hx).
    -
      pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
      pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE O n PA ltac:(lia) ltac:(unfold AAPP_HI, AFS_SIZE in *; lia) Hn) as D.
      unfold PARSER_SIZE, O_V1, O_M1 in *. destruct D; lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      pose proof (aapp_disjoint_sh (blk_addr b) (blk_size b) O n RAPP ltac:(lia) ltac:(unfold AAPP_HI, AFS_SIZE in *; lia) Hn) as D.
      destruct D; lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).

      assert (O0 : 0 <= O) by lia.
      assert (Hd : blk_addr b + blk_size b + 8 <= O \/ O + n + 8 <= blk_addr b) by (destruct RF; lia).

      set (O8 := O - O mod 8).
      assert (E8 : O8 mod 8 = 0) by (subst O8; Z.div_mod_to_equations; lia).
      assert (Eq : sh O8 = sh O) by (subst O8; unfold sh; Z.div_mod_to_equations; lia).
      assert (Hn8 : sh O + nsh n <= sh O8 + nsh (n + O mod 8)) by (rewrite Eq; unfold nsh; apply Z.add_le_mono_l; apply Z.div_le_mono; Z.div_mod_to_equations; lia).
      pose proof (sh_apart (blk_addr b) (blk_size b) O8 (n + O mod 8) ltac:(lia) ltac:(lia) ltac:(subst O8; Z.div_mod_to_equations; lia)
                    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) E8
                    ltac:(subst O8; destruct Hd; [left | right]; Z.div_mod_to_equations; lia)) as D.
      rewrite Eq in D. destruct D; lia.
    - left. assert (sh O + nsh n <= sh aceil) by (unfold sh, nsh; pose proof aceil_al8; Z.div_mod_to_equations; lia).
      assert (sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; pose proof aceil_facts as ((? & ?) & _ & _); Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma ap_Xv_blk0 : forall w s LB LBs TB m ftbl X b0, pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) ->
    Forall (xv_ok w LBs ftbl) X -> In b0 (wa_LB0 w) ->
    Forall (fun iv : Z * Z => blk_addr b0 + blk_size b0 <= fst iv \/ snd iv <= blk_addr b0) X.
  Proof.
    intros w s LB LBs TB m ftbl X b0 OK RH P FX Hb0.
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    assert (Hb0L : In b0 LB) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hb0).
    pose proof (ah_blocks H HH _ _ _ _ RH Hb0L) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
    pose proof (blk_apart_ff H HH w s LB m b0 OK RH Hb0L) as BF.
    pose proof (ah_nodup H HH _ _ _ RH) as ND.
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    eapply Forall_impl; [| exact FX]. intros iv Hiv. cbn beta.
    destruct Hiv as [[(I0 & I1 & I2 & _)|ETD]|[(I0 & I1 & I2)|[(I0 & b & Hb & I1 & I2)|[(I0 & b & Hb & I1 & I2)|(I0 & I1 & I2)]]]].
    - destruct BF; lia.
    - subst iv. cbn [fst snd]. right. unfold RtB_Td.ATDLOC, AIMG_TOP in *. lia.
    - unfold PARSER_SIZE, O_V1, O_M1, AFS_HDR in *. destruct QF; lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (HbL & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      assert (Hid : blk_id b0 <> blk_id b).
      { apply (Permutation_NoDup (Permutation_map blk_id P)) in ND.
        exact (nodup_app_ids (wa_LB0 w) (LBs ++ TB) b0 b ND Hb0 ltac:(apply in_or_app; left; exact Hb)). }
      pose proof (ah_disj H HH _ _ _ _ _ RH Hb0L HbL Hid) as D. destruct D; lia.
    - destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (_ & (R0 & R16 & Rn & RI & RC & RF & RAPP)).
      pose proof (aapp_disjoint_sh (blk_addr b0) (blk_size b0) (blk_addr b) (blk_size b) QAPP ltac:(lia) ltac:(pose proof (aapp_bounds _ _ RAPP Rn); lia) Rn) as D.
      destruct D; lia.
    - left. lia.
  Qed.

  Lemma stack_noclient : forall w s LB LBs TB m a, pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) ->
    aceil <= a < wa_sp0 w -> ~ aclient_addr H (wa_LB0 w) (wa_sp0 w) a.
  Proof.
    intros w s LB LBs TB m a OK RH P Ha Hc.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    assert (SHA : sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
    - lia.
    - unfold aimg_client, AIMG_TOP in *. lia.
    - destruct Hc as (b' & Hb' & C1 & C2).
      assert (Hb'L : In b' LB) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hb').
      pose proof (ah_blocks H HH _ _ _ _ RH Hb'L) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP). lia.
    - destruct Hc as (b' & Hb' & C1 & C2).
      assert (Hb'L : In b' LB) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hb').
      pose proof (ah_blocks H HH _ _ _ _ RH Hb'L) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      assert (sh (blk_addr b') + nsh (blk_size b') <= sh aceil) by (unfold sh, nsh; pose proof aceil_al8; Z.div_mod_to_equations; lia). lia.
    - lia.
    - assert (sh (as_FSB H + AFS_SIZE) <= sh aceil) by (apply sh_mono; lia). lia.
    - unfold AHI_LO in *. lia.
  Qed.

  Lemma xv_noclient : forall w s LB LBs TB m a, pmw_okA H w -> as_RHEAP H s LB m -> Permutation LB (wa_LB0 w ++ LBs ++ TB) ->
    ((exists b, In b LBs /\ blk_addr b <= a < blk_addr b + blk_size b)
     \/ (exists b, In b LBs /\ sh (blk_addr b) <= a < sh (blk_addr b) + nsh (blk_size b))) ->
    ~ aclient_addr H (wa_LB0 w) (wa_sp0 w) a.
  Proof.
    intros w s LB LBs TB m a OK RH P Ha Hc.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    assert (FSp : 0 < as_FSB H) by (unfold AIMG_TOP in *; lia).
    pose proof (aapp_bounds _ _ FS4 ltac:(unfold AFS_SIZE; lia)) as (FB1 & FB2 & FB3 & FB4 & FB5).
    pose proof (ah_nodup H HH _ _ _ RH) as ND.
    pose proof (Permutation_NoDup (Permutation_map blk_id P) ND) as ND'.
    assert (SHA : sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (SHL : ALOWSH_LO <= sh aceil) by (unfold sh, ASHADOW_BASE, ALOWSH_LO; Z.div_mod_to_equations; lia).
    destruct Ha as [(b & Hb & A1 & A2)|(b & Hb & A1 & A2)];
      destruct (lbs_blk w s LB LBs TB m b RH P Hb) as (HbL & (R0 & R16 & Rn & RI & RC & RF & RAPP));
      pose proof (aapp_bounds _ _ RAPP Rn) as (B1 & B2 & B3 & B4 & B5).
    -
      destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
      + unfold APM_STACK in *. lia.
      + unfold aimg_client, AIMG_TOP in *. lia.
      + destruct Hc as (b' & Hb' & C1 & C2).
        assert (Hb'L : In b' LB) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hb').
        assert (Hid : blk_id b' <> blk_id b) by exact (nodup_app_ids (wa_LB0 w) (LBs ++ TB) b' b ND' Hb' ltac:(apply in_or_app; left; exact Hb)).
        pose proof (ah_disj H HH _ _ _ _ _ RH Hb'L HbL Hid) as D. lia.
      + destruct Hc as (b' & Hb' & C1 & C2).
        assert (Hb'L : In b' LB) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hb').
        pose proof (ah_blocks H HH _ _ _ _ RH Hb'L) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        pose proof (aapp_disjoint_sh (blk_addr b) (blk_size b) (blk_addr b') (blk_size b') RAPP ltac:(lia) ltac:(pose proof (aapp_bounds _ _ QAPP Qn); lia) Qn) as D.
        lia.
      + destruct RF; lia.
      + pose proof (aapp_disjoint_sh (blk_addr b) (blk_size b) (as_FSB H) AFS_SIZE RAPP ltac:(lia) ltac:(pose proof (aapp_bounds _ _ FS4 ltac:(unfold AFS_SIZE; lia)); lia) ltac:(unfold AFS_SIZE; lia)) as D.
        assert (sh (as_FSB H) + nsh AFS_SIZE = sh (as_FSB H + AFS_SIZE)).
        { unfold sh, nsh, AFS_SIZE. Z.div_mod_to_equations. lia. }
        lia.
      + pose proof (aapp_not_shadowland _ _ RAPP) as D. unfold AHI_LO, ALOWSH_LO in *. lia.
    -
      assert (SH1 : ALOWSH_LO + 0x1000 <= sh (blk_addr b)) by (apply (sh_in_shadowland (blk_addr b)); lia).
      assert (SH2 : sh (blk_addr b) + nsh (blk_size b) <= sh aceil).
      { unfold sh, nsh. pose proof aceil_al8. Z.div_mod_to_equations. lia. }
      destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
      + unfold APM_STACK in *. lia.
      + unfold aimg_client, ALOWSH_LO in *. lia.
      + destruct Hc as (b' & Hb' & C1 & C2).
        assert (Hb'L : In b' LB) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hb').
        pose proof (ah_blocks H HH _ _ _ _ RH Hb'L) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        pose proof (aapp_disjoint_sh (blk_addr b') (blk_size b') (blk_addr b) (blk_size b) QAPP ltac:(lia) ltac:(lia) Rn) as D.
        lia.
      + destruct Hc as (b' & Hb' & C1 & C2).
        assert (Hb'L : In b' LB) by (apply (Permutation_in _ (Permutation_sym P)); apply in_app_iff; left; exact Hb').
        pose proof (ah_blocks H HH _ _ _ _ RH Hb'L) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        assert (Hid : blk_id b' <> blk_id b) by exact (nodup_app_ids (wa_LB0 w) (LBs ++ TB) b' b ND' Hb' ltac:(apply in_or_app; left; exact Hb)).
        pose proof (ah_disj H HH _ _ _ _ _ RH Hb'L HbL Hid) as D.
        pose proof (sh_apart (blk_addr b') (blk_size b') (blk_addr b) (blk_size b) ltac:(lia) Qn ltac:(lia) Rn
                      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as D2.
        lia.
      + assert (ALOWSH_LO <= as_FSB H \/ as_FSB H + AFS_SIZE <= ALOWSH_LO \/ True) by (right; right; exact I).
        pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (blk_addr b) (blk_size b) FS4 ltac:(lia) ltac:(lia) Rn) as D.
        lia.
      + pose proof (sh_apart (blk_addr b) (blk_size b) (as_FSB H) AFS_SIZE ltac:(lia) Rn ltac:(lia) ltac:(unfold AFS_SIZE; lia)
                      ltac:(Z.div_mod_to_equations; lia) ltac:(unfold AFS_SIZE in *; Z.div_mod_to_equations; lia) ltac:(destruct RF; lia)) as D.
        assert (sh (as_FSB H) + nsh AFS_SIZE = sh (as_FSB H + AFS_SIZE)).
        { unfold sh, nsh, AFS_SIZE in *. Z.div_mod_to_equations. lia. }
        lia.
      + lia.
  Qed.
End Xv.

Lemma rin_ivs_In : forall X a, rin_ivs X a -> exists iv, In iv X /\ fst iv <= a /\ a < snd iv.
Proof.
  induction X as [|iv X IH]; intros a Ha; cbn in Ha; [contradiction|].
  destruct Ha as [[H1 H2]|Ha]; [exists iv; split; [left; reflexivity | split; assumption]|].
  destruct (IH a Ha) as (iv' & Hin & H1 & H2). exists iv'. split; [right; exact Hin | split; assumption].
Qed.

Section XvMain.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pmxa_xv : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs' m' mo' c' TB' spal' LBk X XS tbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->

    as_RHEAP H s' LB' m' -> as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_sp0 w) ->
    (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) -> as_rauxv_ok H m' (wa_B w) ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) -> LINV m' ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LBk (wa_s1 w) (X ++ XS) m m' ->
    Forall (xv_ok H w LBs ftbl) X ->
    Forall (fun iv : Z * Z => (snd iv <= wa_ff w + 24 \/ wa_ff w + 16376 <= fst iv) \/ wr_at asegs m' (fst iv) (snd iv - fst iv)) X ->
    mdef m' (wa_p w + O_M1) (PARSER_SIZE - O_M1) ->
    fkeys_ok (map fst ftbl) = true -> slots_ok w m' bvmap_empty tbl' ->

    (forall b, In b LBk -> In b LB) -> (forall b, In b (wa_LB0 w) -> In b LBk) ->
    Permutation LB' (wa_LB0 w ++ LBs' ++ TB') -> Permutation (lbl LBs') (c_blocks c') -> lb_own LBs' m' -> pm_meas_ok (wa_n w) LBs' ->
    lb_own TB' m' -> (length TB' <= 1)%nat ->

    as_AL H s' >= as_AL H (wa_s0 w) - pm_phi c' - spal' -> pm_cap c' + PM_RESERVE <= po_cost (wa_n w) -> 0 <= spal' <= PM_RESERVE ->

    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M1) (t3a (c_m1 c')) (t3b (c_m1 c')) (t3c (c_m1 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB') m' (wa_p w + O_M2) (t3a (c_m2 c')) (t3b (c_m2 c')) (t3c (c_m2 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M3) (t3a (c_m3 c')) (t3b (c_m3 c')) (t3c (c_m3 c')) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V1) (t3a (c_v1 c')) (t3b (c_v1 c')) (t3c (c_v1 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V2) (t3a (c_v2 c')) (t3b (c_v2 c')) (t3c (c_v2 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V3) (t3a (c_v3 c')) (t3b (c_v3 c')) (t3c (c_v3 c')) ->
    pmc_sh m' c' ->
    PMXAT H LINV w s' LB' LBs' m' mo' c' ins tbl' ftbl TB' spal'.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs' m' mo' c' TB' spal' LBk X XS tbl' OK X0
           RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP FX FXW MDh Hfk SL' LBk1 LBk0 OWN1 OWN2 OWN3 MEAS' TBO TBL AL1 AL2 SPAL
           Cw Ci Ce Cr U1 U2 U3 V1 V2 V3 SHc.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (wk_capp H w OK) as (CA & CA0 & CA16).
    destruct (wk_cin H w OK) as (fc0 & Hfc0 & CF1 & CF2).
    pose proof (proj2 (ah_RFS_range H HH _ _ RFS') fc0 (or_intror Hfc0)) as (_ & CR1 & CR2 & _).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as Xrheap0.
    pose proof (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) as Xown0.
    set (XX := X ++ XS).
    assert (XXb : Forall (fun iv : Z * Z => snd iv <= aceil \/ (wa_s1 w <= fst iv /\ snd iv <= wa_s1 w + PM_RF_TOP)) XX).
    { apply Forall_app. split.
      - eapply Forall_impl; [| exact FX]. intros iv Hiv. exact (xv_loc H HH w s LB LBs TB m ftbl iv OK Xrheap0 Xown0 Hiv).
      - eapply Forall_impl; [| exact FXS]. intros iv Hiv. left. exact (scratch_below H HH _ _ _ RFS' Hiv). }

    assert (FOp : fsobj H (PMLF H w) (wa_p w) PARSER_SIZE) by (right; exists fp0; split; [right; exact Hfp0 | lia]).
    assert (FOc : fsobj H (PMLF H w) (wa_cons w) 48) by (right; exists fc0; split; [right; exact Hfc0 | lia]).
    assert (FOf : fsobj H (PMLF H w) (wa_ff w) 16384) by (right; exists (PM_FCLASS, wa_ff w, wa_fp w); split; [left; reflexivity | unfold ff_addr, ff_class; cbn [fst snd]; change (fsz PM_FCLASS) with 16384; lia]).
    pose proof (xp_scr_obj H HH w m' XS (wa_p w) PARSER_SIZE OK RFS' FXS FOp ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(unfold AAPP_HI, PARSER_SIZE in *; lia) PA) as [SXp SXps].
    pose proof (xp_scr_obj H HH w m' XS (wa_cons w) 48 OK RFS' FXS FOc ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) CA) as [SXc SXcs].
    pose proof (xp_scr_obj H HH w m' XS (wa_ff w) 16384 OK RFS' FXS FOf ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) FA) as [SXf SXfs].
    assert (SUBXS : forall O n O' n', Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) XS -> O <= O' -> O' + n' <= O + n ->
              Forall (fun iv : Z * Z => O' + n' <= fst iv \/ snd iv <= O') XS).
    { intros O n O' n' F HO HO'. eapply Forall_impl; [| exact F]. intros iv Hiv. cbn beta in *. lia. }

    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF.
    pose proof (lf0_apart_ff H w fc0 (wa_cons w) 48 OK Hfc0 CF1 CF2) as CFF.

    assert (XRp : forall k n, 0 <= k -> 0 <= n -> k + n <= O_M1 -> xclient_range H LBk (wa_s1 w) XX (wa_p w + k) n).
    { intros k n Hk Hn Hkn. apply (xr_fs H w); [exact OK | unfold PARSER_SIZE, AFS_HDR in *; lia | unfold PARSER_SIZE, O_V1, O_M1 in *; lia |].
      apply Forall_app. split.
      - eapply (ap_Xv_fso H HH w s LB LBs TB m ftbl X); [exact OK | exact Xrheap0 | exact Xown0 | exact FX | unfold AFS_HDR in *; lia
          | unfold PARSER_SIZE, O_V1, O_M1 in *; lia | lia | unfold PARSER_SIZE, O_V1, O_M1 in *; lia | left; lia].
      - eapply SUBXS; [exact SXp | lia | unfold PARSER_SIZE, O_V1, O_M1 in *; lia]. }
    assert (XRc : forall k n, 0 <= k -> 0 <= n -> k + n <= 48 -> xclient_range H LBk (wa_s1 w) XX (wa_cons w + k) n).
    { intros k n Hk Hn Hkn. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |].
      apply Forall_app. split.
      - eapply (ap_Xv_fso H HH w s LB LBs TB m ftbl X); [exact OK | exact Xrheap0 | exact Xown0 | exact FX | unfold AFS_HDR in *; lia
          | lia | lia | lia | pose proof (wk_pcons H w OK) as PC; unfold PARSER_SIZE, O_V1, O_M1 in *; lia].
      - eapply SUBXS; [exact SXc | lia | lia]. }
    assert (XRffh : forall k n, 0 <= k -> 0 <= n -> k + n <= 16384 -> (k + n <= 24 \/ 16376 <= k) ->
              xclient_range H LBk (wa_s1 w) XX (wa_ff w + k) n).
    { intros k n Hk Hn Hkn Hh. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |].
      apply Forall_app. split.
      - eapply (ap_Xv_ffo H HH w s LB LBs TB m ftbl X); [exact OK | exact Xrheap0 | exact Xown0 | exact FX | lia | lia | lia |].
        apply Forall_forall. intros iv _ [(I0 & I1 & I2 & _)| ->]; [lia | cbn [fst snd]; unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR in *; lia].
      - eapply SUBXS; [exact SXf | lia | lia]. }
    assert (XRsl : forall k e, In (k, e) ftbl -> 0 <= k -> k + 8 <= 16384 -> xclient_range H LBk (wa_s1 w) XX (wa_ff w + k) 8).
    { intros k e Hin Hk Hk8. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |].
      apply Forall_app. split.
      - eapply (ap_Xv_ffo H HH w s LB LBs TB m ftbl X); [exact OK | exact Xrheap0 | exact Xown0 | exact FX | lia | lia | lia |].
        apply Forall_forall. intros iv _ [(I0 & I1 & I2 & I3)| ->]; cbn beta; [| cbn [fst snd]; unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR in *; lia].
        pose proof (proj1 (Forall_forall _ _) I3 (k, e) Hin) as D. cbn [fst] in D. lia.
      - eapply SUBXS; [exact SXf | lia | lia]. }
    assert (XRfsh : xclient_range H LBk (wa_s1 w) XX (sh (wa_ff w)) PM_NSH).
    { apply (xr_fssh H w); [exact OK | apply sh_mono; unfold AFS_HDR in *; lia | |].
      - assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
        assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; rewrite (div8_add (wa_ff w) 11584) by (Z.div_mod_to_equations; lia); change (11584 / 8) with 1448; ring).
        unfold PM_NSH. lia.
      - apply Forall_app. split.
        { replace PM_NSH with (nsh 11584) by reflexivity.
          eapply (ap_Xv_fssh H HH w s LB LBs TB m ftbl X); [exact OK | exact Xrheap0 | exact Xown0 | exact FX | unfold AFS_HDR in *; lia | lia | lia |].
          apply Forall_forall. intros iv _ [(I0 & I1 & I2 & _)| ->]; cbn beta;
            [| cbn [fst snd]; right; unfold sh; rewrite ASHADOW_BASE_val; unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR in *; Z.div_mod_to_equations; lia].
          pose proof (pm_geom H w OK) as G'. cbn zeta in G'.
          destruct G' as (_ & _ & _ & _ & _ & G6' & _ & _ & _ & _ & _ & _ & G13'). change (nsh 11584) with 1448. rewrite G13' in *.
          destruct G6' as [G6'|G6']; [right | left]; lia. }
        eapply SUBXS; [exact SXfs | lia | unfold nsh, PM_NSH; change ((16384 + 7) / 8) with 2048; lia]. }
    assert (XRst : forall A n, wa_sp0 w - 104 <= A -> 0 <= n -> xclient_range H LBk (wa_s1 w) XX A n).
    { intros A n HA Hn. split; [left; lia|]. eapply Forall_impl; [| exact XXb]. intros iv Hiv. cbn beta in Hiv. right. unfold PM_RF_TOP in Hiv. lia. }
    assert (XRsh : forall O n, 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> as_FSB H <= O -> O + n <= as_FSB H + AFS_SIZE ->
              Forall (fun iv : Z * Z => sh O + nsh n <= fst iv \/ snd iv <= sh O) XS ->
              (sh (as_FSB H) <= sh O /\ sh O + nsh n <= sh (as_FSB H + AFS_SIZE)) -> xclient_range H LBk (wa_s1 w) XX (sh O) (nsh n)).
    { intros O n H0 Hn Ht Hf1 Hf2 SX [B1 B2]. apply (xr_fssh H w); [exact OK | exact B1 | exact B2 |].
      apply Forall_app. split; [| exact SX].
      eapply (ap_Xv_fssh H HH w s LB LBs TB m ftbl X); [exact OK | exact Xrheap0 | exact Xown0 | exact FX | exact Hf1 | exact Hf2 | exact Hn |].
      apply Forall_forall. intros iv _ [(I0 & I1 & I2 & _)| ->]; cbn beta;
        [| cbn [fst snd]; right; unfold sh; rewrite ASHADOW_BASE_val; unfold RtB_Td.ATDLOC; clear - H0; Z.div_mod_to_equations; lia].
      pose proof (aapp_disjoint_sh (wa_ff w) 16384 O n FA H0 Ht Hn) as D. destruct D; lia. }

    destruct X0 as [Xrheap Xlbown Xtb Xown Xmeas Xmpres Xmeminv Xstk Xerrno Xrauxv Xaconst Xstack0 Xlinv Xrfs Xxpres Xal Xsaved Xfhdr Xfflag Xfwr Xchain Xfsh Xslots Xfslots Xpdef Xcons Xuser Xhdrfn Xinsfn Xhunk Xwords Xn Xdiag Xwidx Xicount Xendian Xflags Xretry Xscal Xconsf Xconsd Xconsw Xwbuf Xm1 Xm2 Xm3 Xv1 Xv2 Xv3 Xsh].
    constructor.
    - exact RH'.
    - exact OWN3.
    - split; [exact TBO | exact TBL].
    - split; [exact OWN1 | exact OWN2].
    - exact MEAS'.
    - eapply (ah_mpres_trans H HH); [exact Xmpres | exact MP'].
    - exact MI'.
    - exact STK'.
    - exact ERR'.
    - exact RA'.
    - exact AC'.
    - exact S0'.
    - exact LI'.
    - exact RFS'.
    - destruct Xxpres as (XS0 & FXS0 & XP0). exists (XS0 ++ XS). split.
      + apply Forall_app. split; [exact FXS0|]. eapply Forall_impl; [| exact FXS]. intros iv Hiv. exact (fs_scratch_tail H _ _ _ Hiv).
      + eapply xpres_trans.
        * eapply (xpres_weaken H); [exact XP0 | lia | intros b Hb; exact Hb |].
          intros a Ha. cbn [rin_ivs] in *. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [left | right; left | right; right; left | right; right; right; left |]; try exact Ha.
          right; right; right; right. apply rin_ivs_app. left. exact Ha.
        * intros a Ha [Hc Hx]. apply XP; [exact Ha|]. split.
          -- eapply aclient_addr_weaken; [exact Hc | lia | intros b Hb; exact (LBk0 b Hb)].
          -- intros Hin. apply rin_ivs_app in Hin as [Hin|Hin].
             ++ destruct (rin_ivs_In X a Hin) as (iv & HivX & Hr1 & Hr2).
                pose proof (proj1 (Forall_forall _ _) FX iv HivX) as Hk.
                destruct Hk as [[(I0 & I1 & I2 & _)|ETD]|[(I0 & I1 & I2)|[(I0 & b & Hb & I1 & I2)|[(I0 & b & Hb & I1 & I2)|(I0 & I1 & I2)]]]].
                ** apply Hx. cbn [rin_ivs fst snd]. right; right; left. change (fsz PM_FCLASS) with 16384. lia.
                ** apply Hx. cbn [rin_ivs fst snd]. left. subst iv. cbn [fst snd] in Hr1, Hr2. lia.
                ** apply Hx. cbn [rin_ivs fst snd]. right; left. unfold PARSER_SIZE, O_V1, O_M1 in *. lia.
                ** assert (Hab : blk_addr b <= a /\ a < blk_addr b + blk_size b) by lia.
                   exact (xv_noclient H HH w s LB LBs TB m a OK Xrheap Xown0 (or_introl (ex_intro _ b (conj Hb Hab))) Hc).
                ** assert (Hab : sh (blk_addr b) <= a /\ a < sh (blk_addr b) + nsh (blk_size b)) by lia.
                   exact (xv_noclient H HH w s LB LBs TB m a OK Xrheap Xown0 (or_intror (ex_intro _ b (conj Hb Hab))) Hc).
                ** exact (stack_noclient H HH w s LB LBs TB m a OK Xrheap Xown0 ltac:(unfold PM_RF_TOP in *; lia) Hc).
             ++ apply Hx. cbn [rin_ivs]. right; right; right; right. apply rin_ivs_app. right. exact Hin.
    - split; [exact AL1|]. split; [exact AL2|]. split; [exact (proj1 (proj2 (proj2 Xal))) | exact SPAL].
    - eapply (xpres_rw_cells H); [exact XP | exact Xsaved |]. rewrite cells_size_mapC8, (wk_saved H w OK). apply XRst; lia.
    - eapply (xpres_rw_cells H); [exact XP | exact Xfhdr |]. cbn [cells_size csize Nat.add].
      replace (wa_ff w) with (wa_ff w + 0) at 1 by lia. apply XRffh; lia.
    - eapply (xpres_rw_cells H); [exact XP | exact Xfflag |]. cbn [cells_size csize Nat.add]. change (fsz PM_FCLASS) with 16384.
      replace (wa_ff w + 16384 - 8) with (wa_ff w + 16376) by lia. apply XRffh; lia.
    - destruct Xfwr as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. change (fsz PM_FCLASS) with 16384 in *.
      destruct (Z_lt_le_dec i 24) as [Li|Li]; [| destruct (Z_le_gt_dec 16376 i) as [Ui|Ui]].
      + pose proof (XP (wa_ff w + i) ltac:(lia)) as K. destruct K as [_ K]; [| exact (K (W3 i Hi))].
        eapply (xclient_range_addr H); [apply (XRffh 0 24); lia | lia].
      + pose proof (XP (wa_ff w + i) ltac:(lia)) as K. destruct K as [_ K]; [| exact (K (W3 i Hi))].
        eapply (xclient_range_addr H); [apply (XRffh 16376 8); lia | lia].
      +
        destruct (outside_dec X (wa_ff w + i)) as [Ho|(lo & hi & Hin & Hr)].
        * assert (XC : xclient H LBk (wa_s1 w) XX (wa_ff w + i)).
          { split; [right; right; right; right; left; unfold AFS_HDR in *; lia|].
            intros R. apply rin_ivs_app in R as [R|R].
            - clear -R Ho. induction X as [|[lo hi] X IH]; cbn in R, Ho; [contradiction|]. destruct Ho as [Ho1 Ho2]. destruct R as [R|R]; [lia | eapply IH; eassumption].
            - pose proof SXf as F. clear -R F Hi. induction XS as [|iv XS IH]; cbn in R; [contradiction|].
              apply Forall_cons_iff in F as [F1 F2]. destruct R as [R|R]; [cbn beta in F1; lia | eapply IH; eassumption]. }
          exact (proj2 (XP (wa_ff w + i) ltac:(lia) XC) (W3 i Hi)).
        * pose proof (proj1 (Forall_forall _ _) FXW (lo, hi) Hin) as [Habs|(_ & _ & WW)]; [cbn [fst snd] in Habs; exfalso; lia|].
          cbn [fst snd] in WW.
          replace (wa_ff w + i) with (lo + (wa_ff w + i - lo)) by lia. apply WW. lia.
    - eapply (chain_via_xpres H HH); [exact Xchain | exact XP | |].
      + intros fp ra Hin. destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia | pose proof (wk_chfr H w OK fp ra Hin); lia].
      + intros fp ra Hin. assert (Hfp : wa_sp0 w <= fp) by (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia | pose proof (wk_chfr H w OK fp ra Hin); lia]).
        eapply Forall_impl; [| exact XXb]. intros iv Hiv. cbn beta in *. right. unfold PM_RF_TOP in Hiv. lia.
    - eapply (xpres_SHAD H); [exact XP | exact Xfsh |]. unfold pm_fsh. rewrite length_map, pm_fsh_len. exact XRfsh.
    - exact SL'.
    - unfold fslots_ok in *. apply Forall_forall. intros [k e] Hin. pose proof (proj1 (Forall_forall _ _) Xfslots (k, e) Hin) as C.
      cbn [fst snd] in *. pose proof (proj1 (forallb_forall _ _) Hfk k (in_map fst _ (k, e) Hin)) as Kk.
      apply andb_true_iff in Kk as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
      eapply (xpres_rw_cells H); [exact XP | exact C |]. cbn [cells_size csize]. apply (XRsl k e Hin); lia.
    - intros i Hi. destruct (Z_lt_le_dec i O_M1) as [Li|Li].
      + assert (MD0 : mdef m' (wa_p w) O_M1).
        { eapply xpres_mdef; [exact XP | intros j Hj; apply Xpdef; unfold PARSER_SIZE, O_M1 in *; lia | | lia | unfold O_M1, PARSER_SIZE in *; lia].
          replace (wa_p w) with (wa_p w + 0) by lia. apply XRp; unfold O_M1; lia. }
        exact (MD0 i ltac:(lia)).
      + replace (wa_p w + i) with (wa_p w + O_M1 + (i - O_M1)) by lia. apply MDh. unfold PARSER_SIZE, O_M1 in *. lia.
    - eapply xpres_fld; [exact XP | exact Xcons | apply XRp; unfold O_M1; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xuser | apply XRp; unfold O_M1; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xhdrfn | apply XRp; unfold O_M1; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xinsfn | apply XRp; unfold O_M1; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xhunk | apply XRp; unfold O_M1; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xwords | apply XRp; unfold O_WORDS, O_M1; cbn; lia | unfold O_WORDS; lia | cbn; unfold O_WORDS, PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xn | apply XRp; unfold O_N, O_M1; cbn; lia | unfold O_N; lia | cbn; unfold O_N, PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xdiag | apply XRp; unfold O_DIAG, O_M1; cbn; lia | unfold O_DIAG; lia | cbn; unfold O_DIAG, PARSER_SIZE in *; lia].
    - rewrite Cw. eapply xpres_fld; [exact XP | exact Xwidx | apply XRp; unfold O_WIDX, O_M1; cbn; lia | unfold O_WIDX; lia | cbn; unfold O_WIDX, PARSER_SIZE in *; lia].
    - rewrite Ci. eapply xpres_fld; [exact XP | exact Xicount | apply XRp; unfold O_ICOUNT, O_M1; cbn; lia | unfold O_ICOUNT; lia | cbn; unfold O_ICOUNT, PARSER_SIZE in *; lia].
    - rewrite Ce. eapply xpres_fld; [exact XP | exact Xendian | apply XRp; unfold O_ENDIAN, O_M1; cbn; lia | unfold O_ENDIAN; lia | cbn; unfold O_ENDIAN, PARSER_SIZE in *; lia].
    - rewrite Cr. eapply xpres_fld; [exact XP | exact Xflags | apply XRp; unfold O_FLAGS, O_M1; cbn; lia | unfold O_FLAGS; lia | cbn; unfold O_FLAGS, PARSER_SIZE in *; lia].
    - rewrite <- Z.add_assoc in *. eapply xpres_fld; [exact XP | exact Xretry | apply XRp; unfold O_FLAGS, O_M1; cbn; lia | unfold O_FLAGS; lia | cbn; unfold O_FLAGS, PARSER_SIZE in *; lia].
    - rewrite Cw, Ci, Ce, Cr. exact Xscal.
    - eapply xpres_fld; [exact XP | exact Xconsf | apply XRc; cbn; lia | lia | cbn; lia].
    - eapply xpres_mdef; [exact XP | exact Xconsd | apply XRc; lia | lia | lia].
    - eapply (xpres_wr_at H); [exact XP | exact Xconsw |]. replace (wa_cons w) with (wa_cons w + 0) at 1 by lia. apply XRc; lia.
    - intros Hwz. destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Hk & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
      assert (HinLB : In (pw, wa_words w, k) LB).
      { apply (Permutation_in _ (Permutation_sym (proj1 Xown))). apply in_app_iff. left. exact Hin. }
      pose proof (ah_blocks H HH _ _ _ _ Xrheap HinLB) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof (blk_apart_ff H HH w s LB m _ OK Xrheap HinLB) as BF. cbn [blk_addr blk_size fst snd] in BF.
      assert (FOw : fsobj H (PMLF H w) (wa_words w) k) by (eapply fsobj_block; [exact HH | exact Xrheap | exact HinLB]).
      pose proof (xp_scr_obj H HH w m' XS (wa_words w) k OK RFS' FXS FOw ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) RAPP) as [SXw _].
      eapply xpres_mdef; [exact XP | exact (Xwbuf Hwz) | | lia | lia].
      apply (xr_blk H w LBk XX (pw, wa_words w, k)); [exact (LBk0 _ Hin) | cbn; lia | cbn; lia |].
      apply Forall_app. split; [| eapply SUBXS; [exact SXw | lia | lia]].
      eapply Forall_impl; [| exact (ap_Xv_blk0 H HH w s LB LBs TB m ftbl X (pw, wa_words w, k) OK Xrheap Xown0 FX Hin)].
      intros iv Hiv. cbn [blk_addr blk_size fst snd] in Hiv |- *. lia.
    - exact U1.
    - exact U2.
    - exact U3.
    - exact V1.
    - exact V2.
    - exact V3.
    - split; [exact SHc|]. destruct Xsh as (_ & SHp & SHk). split.
      + eapply xpres_addressable; [exact XP | exact SHp |].
        apply XRsh; [lia | unfold PARSER_SIZE; lia | unfold AAPP_HI, PARSER_SIZE in *; lia | unfold AFS_HDR in *; lia | unfold PARSER_SIZE in *; lia | exact SXps |].
        split; [apply sh_mono; unfold AFS_HDR in *; lia|].
        assert (sh (wa_p w + PARSER_SIZE) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; unfold PARSER_SIZE in *; lia).
        assert (sh (wa_p w) + nsh PARSER_SIZE = sh (wa_p w + PARSER_SIZE)).
        { unfold sh, nsh, PARSER_SIZE. rewrite (div8_add (wa_p w) 288) by (Z.div_mod_to_equations; lia).
          change (288 / 8) with 36. change ((288 + 7) / 8) with 36. ring. }
        lia.
      + eapply xpres_addressable; [exact XP | exact SHk |].
        apply XRsh; [lia | lia | unfold AAPP_HI in *; lia | unfold AFS_HDR in *; lia | lia | exact SXcs |].
        split; [apply sh_mono; unfold AFS_HDR in *; lia|].
        assert (sh (wa_cons w + 48) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
        assert (sh (wa_cons w) + nsh 48 = sh (wa_cons w + 48)).
        { unfold sh, nsh. rewrite (div8_add (wa_cons w) 48) by (Z.div_mod_to_equations; lia).
          change (48 / 8) with 6. change ((48 + 7) / 8) with 6. ring. }
        lia.
  Qed.

  Lemma slots_xpres : forall (w : pmwA H) m m' tbl LBk XX, pmw_okA H w -> slots_ok w m bvmap_empty tbl ->
    keys_nonneg (map fst tbl) = true -> xpres H LBk (wa_s1 w) XX m m' -> Forall (fun iv : Z * Z => snd iv <= aceil) XX ->
    slots_ok w m' bvmap_empty tbl.
  Proof.
    intros w m m' tbl LBk XX OK SL Hknn XP XXb.
    unfold slots_ok in *. apply Forall_forall. intros [k e] Hin. pose proof (proj1 (Forall_forall _ _) SL (k, e) Hin) as C.
    cbn [fst snd] in *. pose proof (proj1 (forallb_forall _ _) Hknn k (in_map fst _ (k, e) Hin)) as Kk. apply Z.leb_le in Kk.
    eapply (xpres_rw_cells H); [exact XP | exact C |]. cbn [cells_size csize].
    apply (xr_stack H w); [exact OK | lia | lia | exact XXb].
  Qed.

  Lemma stk_xjoin : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' LBk XX,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    stk asegs m' (wa_lo w) (wa_s1 w) -> xpres H LBk (wa_s1 w) XX m m' -> Forall (fun iv : Z * Z => snd iv <= aceil) XX ->
    stk asegs m' (wa_lo w) (wa_sp0 w).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' LBk XX OK X0 STK' XP XXb.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    apply (stk_join m' (wa_lo w) (wa_s1 w) (wa_sp0 w)); [exact STK' | | lia].
    destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) ltac:(lia)) as [_ ST2].
    eapply (xpres_stk H); [exact XP | exact ST2 | lia |]. eapply Forall_impl; [| exact XXb]. intros iv Hiv. cbn beta in *. right. lia.
  Qed.

  Lemma pmxa_xv4 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs' m' mo' c' TB' spal' LBk X XS,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> keys_nonneg (map fst tbl) = true ->

    as_RHEAP H s' LB' m' -> as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) -> as_rauxv_ok H m' (wa_B w) ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) -> LINV m' ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LBk (wa_s1 w) (X ++ XS) m m' ->
    Forall (xv_ok4 H w LBs ftbl) X ->
    Forall (fun iv : Z * Z => (snd iv <= wa_ff w + 24 \/ wa_ff w + 16376 <= fst iv) \/ wr_at asegs m' (fst iv) (snd iv - fst iv)) X ->
    mdef m' (wa_p w + O_M1) (PARSER_SIZE - O_M1) ->
    fkeys_ok (map fst ftbl) = true ->

    (forall b, In b LBk -> In b LB) -> (forall b, In b (wa_LB0 w) -> In b LBk) ->
    Permutation LB' (wa_LB0 w ++ LBs' ++ TB') -> Permutation (lbl LBs') (c_blocks c') -> lb_own LBs' m' -> pm_meas_ok (wa_n w) LBs' ->
    lb_own TB' m' -> (length TB' <= 1)%nat ->

    as_AL H s' >= as_AL H (wa_s0 w) - pm_phi c' - spal' -> pm_cap c' + PM_RESERVE <= po_cost (wa_n w) -> 0 <= spal' <= PM_RESERVE ->

    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M1) (t3a (c_m1 c')) (t3b (c_m1 c')) (t3c (c_m1 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB') m' (wa_p w + O_M2) (t3a (c_m2 c')) (t3b (c_m2 c')) (t3c (c_m2 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M3) (t3a (c_m3 c')) (t3b (c_m3 c')) (t3c (c_m3 c')) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V1) (t3a (c_v1 c')) (t3b (c_v1 c')) (t3c (c_v1 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V2) (t3a (c_v2 c')) (t3b (c_v2 c')) (t3c (c_v2 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V3) (t3a (c_v3 c')) (t3b (c_v3 c')) (t3c (c_v3 c')) ->
    pmc_sh m' c' ->
    PMXAT H LINV w s' LB' LBs' m' mo' c' ins tbl ftbl TB' spal'.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs' m' mo' c' TB' spal' LBk X XS OK X0 Hknn
           RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP FX FXW MDh Hfk LBk1 LBk0 OWN1 OWN2 OWN3 MEAS' TBO TBL AL1 AL2 SPAL
           Cw Ci Ce Cr U1 U2 U3 V1 V2 V3 SHc.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as Xrheap0.
    pose proof (proj1 (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) as Xown0.
    assert (XXb : Forall (fun iv : Z * Z => snd iv <= aceil) (X ++ XS)).
    { apply Forall_app. split.
      - eapply Forall_impl; [| exact FX]. intros iv Hiv. exact (xv4_below H HH w s LB LBs TB m ftbl iv OK Xrheap0 Xown0 Hiv).
      - eapply Forall_impl; [| exact FXS]. intros iv Hiv. exact (scratch_below H HH _ _ _ RFS' Hiv). }
    eapply (pmxa_xv w s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs' m' mo' c' TB' spal' LBk X XS tbl);
      [exact OK | exact X0 | exact RH' | exact MP' | exact MI'
      | exact (stk_xjoin w s LB LBs m mo c ins tbl ftbl TB spal m' LBk (X ++ XS) OK X0 STK' XP XXb)
      | exact ERR' | exact RA' | exact RFS' | exact AC' | exact S0' | exact LI' | exact FXS | exact XP
      | eapply Forall_impl; [| exact FX]; intros iv Hiv; exact (xv_ok4_ok H w LBs ftbl iv Hiv)
      | exact FXW | exact MDh | exact Hfk
      | exact (slots_xpres w m m' tbl LBk (X ++ XS) OK (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) Hknn XP XXb)
      | exact LBk1 | exact LBk0 | exact OWN1 | exact OWN2 | exact OWN3 | exact MEAS' | exact TBO | exact TBL | exact AL1 | exact AL2 | exact SPAL
      | exact Cw | exact Ci | exact Ce | exact Cr | exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact V3 | exact SHc].
  Qed.
End XvMain.

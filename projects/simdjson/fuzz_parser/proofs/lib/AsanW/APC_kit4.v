(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_client_kit AU_fuzz_kit Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Pres.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv CI.

  Local Ltac pick_in := (left; reflexivity) + (right; pick_in).
  Local Ltac in_cr := apply IMG_CI; unfold client_ranges; pick_in.

  Lemma magree_of_pres_x : forall LB SP X n m m', aheap_pres_x CI LB SP X n m m' ->
    magree asegs (fun a => aclient_addr CI LB SP a /\ ~ (X <= a < X + n)) m m'.
  Proof. intros LB SP X n m m' H a Ha [Hc Hx]. exact (H a Ha Hc Hx). Qed.

  (* [comment removed for export] *)
  Lemma client_img_addr : forall LB SP a, (0x103e90 <= a < 0x103ec0) \/ (0x103f50 <= a < 0x103fa0) \/ client_x_addr a ->
    aclient_addr CI LB SP a.
  Proof.
    intros LB SP a [Ha|[Ha|Ha]]; [right; left; exists (0x103e90, 0x103ec0); (split; [in_cr| cbn; lia])
                                 | right; left; exists (0x103f50, 0x103fa0); (split; [in_cr| cbn; lia]) |].
    unfold client_x_addr, AREAL_MC, AFMIN in Ha.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|(lo & hi & Hin & Ha)]]]];
      [ right; left; exists (0x1090e0, 0x1090f0); (split; [in_cr| cbn; lia])
      | right; left; exists (0x10b978, 0x10b97c); (split; [in_cr| cbn; lia])
      | apply (client_sh_addr_of_range AI IMG_CI LB SP 0x22ec0 0x22f00);
          [unfold client_ranges; pick_in| unfold ABOM in Ha; replace ((0x22f00 - 0x22ec0) / 8) with 8 by reflexivity; exact Ha| reflexivity| reflexivity]
      | apply (client_sh_addr_of_range AI IMG_CI LB SP 0x28140 0x28240);
          [unfold client_ranges; pick_in| unfold ACTAB in Ha; replace ((0x28240 - 0x28140) / 8) with 32 by reflexivity; exact Ha| reflexivity| reflexivity]
      | pose proof (img_tabs_bounds lo hi Hin) as (B1 & B2 & B3 & B4 & B5);
        apply (client_sh_addr_of_range AI IMG_CI LB SP lo hi); [unfold client_ranges; apply in_or_app; right; exact Hin| exact Ha| exact B4| exact B5] ].
  Qed.

  Lemma client_img_addr_bounds : forall a, (0x103e90 <= a < 0x103ec0) \/ (0x103f50 <= a < 0x103fa0) \/ client_x_addr a ->
    a < AIMG_HI \/ KLS <= a < 0x800c4a00.
  Proof.
    intros a [Ha|[Ha|Ha]]; [unfold AIMG_HI; lia| unfold AIMG_HI; lia|].
    apply client_x_addr_num in Ha. unfold AREAL_MC, AFMIN, ABOM, ACTAB, shad, ASHOFF, AIMG_HI, KLS in *.
    rewrite !Z.shiftr_div_pow2 in Ha by lia. change (2 ^ 3) with 8 in Ha. cbn in Ha. lia.
  Qed.

  Lemma client_img_pres_x : forall L RNG st LB LB' SP X n mx my, aheap_pres_x CI LB SP X n mx my -> wfar (X, X + n) ->
    client_img mx -> AHEAP AI L RNG st LB' my -> mem_inv asegs my -> client_img my.
  Proof.
    intros L RNG st LB LB' SP X n mx my HPX FW IG AH MI.
    eapply (client_img_magree AI _ L RNG st LB' mx my IG (magree_of_pres_x _ _ _ _ _ _ HPX)); [| exact AH| exact MI].
    intros a Ha. split; [exact (client_img_addr LB SP a Ha)|].
    pose proof (client_img_addr_bounds a Ha) as B. unfold wfar in FW. cbn [fst snd] in FW. unfold AIMG_HI, KLS in *. lia.
  Qed.

  Lemma client_sh_addr : forall LB SP X, In X client_sh_addrs -> aclient_addr CI LB SP (shad X).
  Proof.
    intros LB SP X HX. right; right; right. exists X. split; [|reflexivity]. right; left.
    unfold client_sh_addrs in HX. cbn [In] in HX.
    repeat (destruct HX as [<-|HX];
      [ first [ exists (0x103e90, 0x103ec0); (split; [in_cr| cbn; lia]) | exists (0x103f50, 0x103fa0); (split; [in_cr| cbn; lia])
              | exists (0x642200, 0x642208); (split; [in_cr| cbn; lia]) | exists (0x642220, 0x642222); (split; [in_cr| cbn; lia])
              | exists (0x6422a0, 0x6422d0); (split; [in_cr| cbn; lia]) | exists (0x642300, 0x642302); (split; [in_cr| cbn; lia]) ] |]).
    destruct HX.
  Qed.

  Lemma client_sh_addr_bounds : forall X, In X client_sh_addrs -> KLS <= shad X < 0x800c4a00.
  Proof.
    intros X HX. assert (B : 0x103e00 <= X < 0x665000)
      by (unfold client_sh_addrs in HX; cbn [In] in HX; repeat (destruct HX as [<-|HX]; [lia|]); destruct HX).
    rewrite shad_div. unfold ASHOFF, KLS. Z.div_mod_to_equations. lia.
  Qed.

  Lemma client_sh_pres_x : forall LB SP X n mx my, aheap_pres_x CI LB SP X n mx my -> wfar (X, X + n) -> client_sh mx -> client_sh my.
  Proof.
    intros LB SP X n mx my HPX FW CS.
    eapply (client_sh_magree _ mx my CS (magree_of_pres_x _ _ _ _ _ _ HPX)).
    intros Y HY. split; [exact (client_sh_addr LB SP Y HY)|].
    pose proof (client_sh_addr_bounds Y HY) as B. unfold wfar in FW. cbn [fst snd] in FW. unfold AIMG_HI, KLS in *. lia.
  Qed.

  Lemma client_static_pres_x : forall s LB0 LB SP X n mx my, aheap_pres_x CI LB SP X n mx my -> wfar (X, X + n) ->
    client_static s LB0 mx -> client_static s LB0 my.
  Proof.
    intros s LB0 LB SP X n mx my HPX FW CS. unfold wfar in FW. cbn [fst snd] in FW. unfold AIMG_HI in FW.
    unfold client_static, client_static0, client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard0, guard1 in *.
    destruct CS as [CL [(C1' & C2 & C3 & C4') | (C1' & C2 & C3 & C4')]]; (split; [exact CL|]); [left| right];
      (split; [| split; [| split]]); (eapply aheap_pres_x_rw_cells; [exact HPX| eassumption| | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]);
      left; right; left; eexists; (split; [in_cr| cbn; lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma aclient_range_img_sh : forall LB SP A n iv, In iv CI -> fst iv <= 8 * (A - ASHOFF) -> 8 * (A + n - ASHOFF) <= snd iv ->
    aclient_range CI LB SP A n.
  Proof. intros LB SP A n iv H H1 H2. right; right. right; left. exists iv. split; [exact H| lia]. Qed.

  (* [comment removed for export] *)
  Definition awin (X n : Z) : Prop := (AIMG_HI <= X /\ X + n <= KLS) \/ 0x10007fff8000 <= X.
  Lemma awin_wfar : forall X n, awin X n -> wfar (X, X + n).
  Proof. intros X n H. unfold awin, wfar, AIMG_HI, KLS in *. cbn [fst snd]. lia. Qed.
  Lemma awin_ablk : forall X n, ablk X (X + n) -> awin X n.
  Proof. intros X n H. unfold ablk, awin in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma hull_sh_client : forall LB SP RLO RHI s, ATOP <= RLO -> RLO mod 8 = 0 -> RHI <= 2^47 -> shad RLO <= s < shad RHI ->
    aclient_addr CI LB SP s.
  Proof.
    intros LB SP RLO RHI s H1 H2 H3 Hs. right; right; right. exists (8 * (s - ASHOFF)). split; [| symmetry; apply shad_unshad].
    left. rewrite !shad_div in Hs. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma rclean_pres_x : forall LB SP X n m m' r, aheap_pres_x CI LB SP X n m m' -> awin X n -> ATOP <= r_rlo r -> rclean m r -> rclean m' r.
  Proof.
    intros LB SP X n m m' r HPX AW RA [(U & HL & WR & AB) LT]. pose proof HL as (H1 & H2 & H3 & H4 & H5 & H6).
    unfold KEND in H6. pose proof atop_range as AR.
    assert (SB : forall s, shad (r_rlo r) <= s < shad (r_rhi r) -> 0 <= s < 2^64 /\ aclient_addr CI LB SP s /\ ~ (X <= s < X + n)).
    { intros s Hs. split; [rewrite !shad_div in Hs; unfold ASHOFF in *; Z.div_mod_to_equations; lia|].
      split; [eapply (hull_sh_client LB SP (r_rlo r) (r_rhi r) s); [lia| Z.div_mod_to_equations; lia| lia| exact Hs]|].
      unfold awin, AIMG_HI, KLS in AW. rewrite !shad_div in Hs. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
    split; [| exact LT]. split; [| split; [exact HL| split; [| exact AB]]].
    - eapply unpoisoned_agree; [exact U|]. intros s Hs.
      assert (Hs' : shad (r_rlo r) <= s < shad (r_rhi r)).
      { rewrite !shad_div in Hs |- *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
      destruct (SB s Hs') as (SR & SC & SX). exact (proj1 (HPX s SR SC SX)).
    - eapply wr_at_magree; [exact (magree_of_pres_x _ _ _ _ _ _ HPX)| exact WR|]. intros a Ha.
      assert (Ha' : shad (r_rlo r) <= a < shad (r_rhi r)) by lia.
      destruct (SB a Ha') as (_ & SC & SX). exact (conj SC SX).
  Qed.

  (* [comment removed for export] *)
  Lemma client_static1_pres_x : forall LB SP X n mx my, aheap_pres_x CI LB SP X n mx my -> wfar (X, X + n) ->
    client_static1 mx -> client_static1 my.
  Proof.
    intros LB SP X n mx my HPX FW CS. unfold wfar in FW. cbn [fst snd] in FW. unfold AIMG_HI in FW.
    unfold client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard1 in *.
    destruct CS as (C1' & C2 & C3 & C4').
    (split; [| split; [| split]]); (eapply aheap_pres_x_rw_cells; [exact HPX| eassumption| | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]);
      left; right; left; eexists; (split; [in_cr| cbn; lia]).
  Qed.
  Lemma client_static1_pres : forall LB SP mx my, aheap_pres CI LB SP mx my -> client_static1 mx -> client_static1 my.
  Proof.
    intros LB SP mx my HP CS. unfold client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard1 in *.
    destruct CS as (C1' & C2 & C3 & C4').
    (split; [| split; [| split]]); (eapply aheap_pres_rw_cells; [exact HP| eassumption|]); left; right; left; eexists; (split; [in_cr| cbn; lia]).
  Qed.
End Pres.

Lemma client_static1_munch32 : forall W mx my, client_static1 mx -> munch W mx my -> wmono asegs mx my -> Forall wfar W -> client_static1 my.
Proof.
  intros W mx my CS MU WM FW. unfold client_static1, AACTIVE, AACTIVE_GUARD, AFALLBACK, AFALLBACK_GUARD, fallback_cells, guard1 in *.
  destruct CS as (C1' & C2 & C3 & C4').
  (split; [| split; [| split]]); (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]); apply wfar_disjoint; try exact FW; left; unfold AIMG_HI; cbn; lia.
Qed.
End CANSEC1.

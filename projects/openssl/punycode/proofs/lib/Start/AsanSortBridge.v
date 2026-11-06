(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatSim StoreOk AgentLib AsanAcct RegEqv AxSymExec3 AsanNodesLibSound.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Exec MState Frame Mem Cells Step.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanSortModel AsanSort AsanSortStmt AsanSortSound AsanHookBridge AsanRehashBridge AsanRegBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Module HSB.
Import HSN.

#[local] Notation W := LBNS.W (only parsing).
#[local] Notation C8 := Cells.C8 (only parsing).

Section SB.
Variable segs : list Segment.
Variable entry : Z.
Hypothesis SEG_below : forall a : word, find_segment segs (bv_unsigned a) 1 <> None -> bv_unsigned a < 2 ^ 47.
Hypothesis Hwx : wx_segs_nowrap segs.

#[local] Notation cell := (LBNS.cell segs) (only parsing).
#[local] Notation wr_ok := (LBNS.wr_ok segs) (only parsing).
#[local] Notation HI := RHB.HI (only parsing).

Theorem isort_contract_of_walk : HSS.walk_stmt segs entry -> HSNS.isort_contract segs entry.
Proof.
  intros WALK regs M tab n ra es G10 G11 G1 Hlen Hn Hrng Hrecs Wt Ht0 Ht1 Ht8 Hra Hra2 RO.
  set (m := mrestrict HI M).
  assert (P_recs : forall j, 0 <= j < n -> HSS.rec_at segs m tab es j).
  { intros j Hj. destruct (Hrecs j Hj) as [C0 C1]. unfold HSS.rec_at. split.
    - apply (RHB.cells_at_cons segs); [exact I | refine (RGB.bcell segs M _ _ _ _ _ C0); lia |].
      cbn [Cells.csize]. replace (tab + 16 * j + Z.of_nat 8) with (tab + 16 * j + 8) by lia.
      apply (RHB.cells_at_cons segs); [exact I | refine (RGB.bcell segs M _ _ _ _ _ C1); lia |].
      apply (RHB.cells_at_nil segs). cbn [Cells.csize]. lia.
    - cbn [Cells.cells_size Cells.csize]. change (Z.of_nat (8 + (8 + 0))) with 16.
      exact (RHB.wr_at_of_wr_ok segs M (tab + 16 * j) 16 ltac:(lia) ltac:(lia) (RGB.wr_sub segs M tab (16 * n) (tab + 16 * j) 16 Wt ltac:(lia) ltac:(lia))). }
  pose proof (RGB.mem_inv_restrict segs SEG_below M RO) as P_inv.
  pose proof (WALK tab n es ra
                (getr regs (Z_to_bv 5 2)) (getr regs (Z_to_bv 5 3)) (getr regs (Z_to_bv 5 4)) (getr regs (Z_to_bv 5 5)) (getr regs (Z_to_bv 5 6)) (getr regs (Z_to_bv 5 7))
                (getr regs (Z_to_bv 5 8)) (getr regs (Z_to_bv 5 9))
                (getr regs (Z_to_bv 5 12)) (getr regs (Z_to_bv 5 13)) (getr regs (Z_to_bv 5 14)) (getr regs (Z_to_bv 5 15)) (getr regs (Z_to_bv 5 16)) (getr regs (Z_to_bv 5 17))
                (getr regs (Z_to_bv 5 18)) (getr regs (Z_to_bv 5 19)) (getr regs (Z_to_bv 5 20)) (getr regs (Z_to_bv 5 21)) (getr regs (Z_to_bv 5 22))
                (getr regs (Z_to_bv 5 23)) (getr regs (Z_to_bv 5 24)) (getr regs (Z_to_bv 5 25)) (getr regs (Z_to_bv 5 26)) (getr regs (Z_to_bv 5 27))
                (getr regs (Z_to_bv 5 28)) (getr regs (Z_to_bv 5 29)) (getr regs (Z_to_bv 5 30)) (getr regs (Z_to_bv 5 31))
                bvmap_empty (Z_to_bv 32 0) m Hlen Hn Hrng P_recs Ht0 Ht1 Ht8 Hra Hra2 P_inv) as X.
  assert (Ecan : HBR.canon regs =
            Frame.mkR (Z_to_bv 64 ra) (getr regs (Z_to_bv 5 2)) (getr regs (Z_to_bv 5 3)) (getr regs (Z_to_bv 5 4)) (getr regs (Z_to_bv 5 5))
              (getr regs (Z_to_bv 5 6)) (getr regs (Z_to_bv 5 7)) (getr regs (Z_to_bv 5 8)) (getr regs (Z_to_bv 5 9)) (Z_to_bv 64 tab) (Z_to_bv 64 n)
              (getr regs (Z_to_bv 5 12)) (getr regs (Z_to_bv 5 13)) (getr regs (Z_to_bv 5 14)) (getr regs (Z_to_bv 5 15)) (getr regs (Z_to_bv 5 16)) (getr regs (Z_to_bv 5 17))
              (getr regs (Z_to_bv 5 18)) (getr regs (Z_to_bv 5 19)) (getr regs (Z_to_bv 5 20)) (getr regs (Z_to_bv 5 21)) (getr regs (Z_to_bv 5 22))
              (getr regs (Z_to_bv 5 23)) (getr regs (Z_to_bv 5 24)) (getr regs (Z_to_bv 5 25)) (getr regs (Z_to_bv 5 26)) (getr regs (Z_to_bv 5 27))
              (getr regs (Z_to_bv 5 28)) (getr regs (Z_to_bv 5 29)) (getr regs (Z_to_bv 5 30)) (getr regs (Z_to_bv 5 31))).
  { unfold HBR.canon. unfold LBNS.W in G10, G11, G1.
    change (getr regs (Z_to_bv 5 1)) with (getr regs 1%bv). change (getr regs (Z_to_bv 5 10)) with (getr regs 10%bv).
    change (getr regs (Z_to_bv 5 11)) with (getr regs 11%bv). rewrite G1, G10, G11. reflexivity. }
  rewrite <- Ecan in X.
  destruct (HBR.evt_bridge segs HI (RHB.HI_off segs SEG_below) Hwx _ regs (Z_to_bv 64 entry) M (seg_rom segs) X)
    as (ms1 & ms2 & HQ & Hrun & Ereg & Efr & Epc & Esvc & Erv & Efc & Erom & Emem & HG).
  destruct HQ as (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & m' & -> & Hmunch & Hwm & Hinv' & Hrecs').
  cbn [MState.MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  rewrite (HBR.mkst_eta ms2 Efr Esvc Erv Efc) in Hrun. rewrite Epc, Erom, Emem in Hrun.
  exists (ms_regs ms2), (munrestrict HI M m').
  split; [exact Hrun|].
  assert (Elow : forall x : word, bv_unsigned x < 2 ^ 47 -> munrestrict HI M m' x = m' x).
  { intros x Hx. unfold munrestrict. rewrite (RHB.HI_low x Hx). reflexivity. }
  assert (Cup : forall a (w : nat) v, 0 <= a -> a + Z.of_nat w <= 2 ^ 47 -> cell m' a w v -> cell (munrestrict HI M m') a w v).
  { intros a w v Ha Hw Hc. unfold LBNS.cell in *. rewrite <- Hc. apply rdn_ext; [rewrite LBNS.u_W by lia; lia|].
    intros x Hx. rewrite LBNS.u_W in Hx by lia. apply Elow. lia. }
  split.
  { intros r Hnin. unfold getr. destruct (bv_eqb r 0) eqn:E0; [reflexivity|].
    assert (Hr : r <> 0%bv) by (intros ->; rewrite bv_eqb_refl in E0; discriminate E0).
    rewrite <- (Ereg r Hr). unfold LBNS.W in G10, G1. rewrite <- G1, <- G10.
    destruct (HBR.reg_cases r Hr) as (q & Hq & ->).
    assert (Hq' : q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12
                  \/ q = 13 \/ q = 14 \/ q = 15 \/ q = 16 \/ q = 17 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23
                  \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27 \/ q = 28 \/ q = 29 \/ q = 30 \/ q = 31) by lia.
    clear - Hq' Hnin.
    repeat (destruct Hq' as [-> | Hq']); try (subst q);
      first [ reflexivity | exfalso; apply Hnin; vm_compute; solve [repeat (first [left; reflexivity | right])] ]. }
  split.
  { intros j Hj. destruct (Hrecs' j Hj) as [Hc _]. apply (RHB.cells_at_uncons segs) in Hc as [Hc0 Hc1]. apply (RHB.cells_at_uncons segs) in Hc1 as [Hc1 _].
    cbn [Cells.csize] in Hc1. replace (tab + 16 * j + Z.of_nat 8) with (tab + 16 * j + 8) in Hc1 by lia.
    split; [exact (Cup (tab + 16 * j) 8%nat (W (fst (HSM.get (HSM.hsort es) j))) ltac:(lia) ltac:(lia) (RHB.cell_of_bytes segs m' (tab + 16 * j) 8 _ Hc0))
           | exact (Cup (tab + 16 * j + 8) 8%nat (W (snd (HSM.get (HSM.hsort es) j))) ltac:(lia) ltac:(lia) (RHB.cell_of_bytes segs m' (tab + 16 * j + 8) 8 _ Hc1))]. }
  split.
  { intros x Hx. unfold munrestrict. destruct (HI x) eqn:EH; [reflexivity|].
    rewrite (Hmunch x); [unfold m, mrestrict; rewrite EH; reflexivity|].
    unfold LBNS.inr in Hx. cbn [Frame.outside]. split; [intros Y; apply Hx; lia | exact I]. }
  intros x Hx. unfold munrestrict. destruct (HI x) eqn:EH; [exact Hx|].
  apply HG. unfold mrestrict. rewrite EH. exact Hx.
Qed.

End SB.
End HSB.

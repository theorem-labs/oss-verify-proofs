(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatSim StoreOk AgentLib AsanAcct RegEqv AxSymExec3 AsanNodesLibSound.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Exec MState Frame Mem Cells Step.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanRegModel AsanRegStmt AsanRegContract AsanHookBridge AsanRehashBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Module RGB.
Import RGM.

#[local] Notation W := LBNS.W (only parsing).
#[local] Notation C8 := Cells.C8 (only parsing).
#[local] Notation C4 := Cells.C4 (only parsing).
#[local] Notation C1 := Cells.C1 (only parsing).

(* [comment removed for export] *)
Definition ctab_okb (T : ctab) : bool :=
  forallb (fun a => Z.leb 0 a && Z.ltb a (2 ^ 40))
    [c_entry T; c_tab T; c_inited T; c_flags T; c_shcell T; c_canpoison T; c_msetcell T; c_memset T; c_llaalign T; c_lla T; c_statics T; c_map T;
     l_ilo (c_lay T); l_ihi (c_lay T); l_shb (c_lay T); l_odr_lo (c_lay T); l_odr_hi (c_lay T)]
  && Z.leb (l_ilo (c_lay T)) (l_ihi (c_lay T)).

Section RB.
Variable segs : list Segment.
Variable T : ctab.
Hypothesis SEG_below : forall a : word, find_segment segs (bv_unsigned a) 1 <> None -> bv_unsigned a < 2 ^ 47.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis CT : ctab_okb T = true.

#[local] Notation cell := (LBNS.cell segs) (only parsing).
#[local] Notation wr_ok := (LBNS.wr_ok segs) (only parsing).
#[local] Notation rd_ok := LBNS.rd_ok (only parsing).
#[local] Notation y := (c_lay T) (only parsing).
#[local] Notation HI := RHB.HI (only parsing).

Lemma ct_bounds : forall a, In a [c_entry T; c_tab T; c_inited T; c_flags T; c_shcell T; c_canpoison T; c_msetcell T; c_memset T; c_llaalign T; c_lla T;
                                  c_statics T; c_map T; l_ilo y; l_ihi y; l_shb y; l_odr_lo y; l_odr_hi y] -> 0 <= a < 2 ^ 40.
Proof.
  intros a Ha. unfold ctab_okb in CT. apply andb_prop in CT as [C1 _]. rewrite forallb_forall in C1. specialize (C1 a Ha).
  apply andb_prop in C1 as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.

(* [comment removed for export] *)
Lemma mem_inv_restrict : forall M : word -> option byte,
  (forall s, In s segs -> seg_writable s = false -> forall z, Z.of_N (seg_base s) <= z < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> M (W z) = None) ->
  Mem.mem_inv segs (mrestrict HI M).
Proof.
  intros M RO. apply Mem.mem_inv_intro.
  - intros a Ha. unfold Mem.seg_addr in Ha. unfold Mem.UTOP. change 0x800000000000 with (2 ^ 47). apply SEG_below.
    destruct (find_segment segs (bv_unsigned a) 1); [discriminate | discriminate Ha].
  - intros a b Hab. unfold mrestrict in Hab. destruct (HI a) eqn:EH; [discriminate Hab|].
    unfold RHB.HI in EH. apply Z.leb_gt in EH. split; [| unfold Mem.UTOP; change 0x800000000000 with (2 ^ 47); exact EH].
    unfold Mem.ro_addr. destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:Ef; [|reflexivity].
    destruct (seg_writable sg) eqn:Ew; [reflexivity|]. exfalso.
    destruct (find_segment_some_spec segs _ _ _ Ef) as (Hin & Hlo & Hhi).
    pose proof (RO sg Hin Ew (bv_unsigned a) ltac:(lia)) as X. rewrite LBNS.W_u in X. rewrite X in Hab. discriminate Hab.
Qed.

(* [comment removed for export] *)
Lemma ro8 : forall (M : word -> option byte) a v, 0 <= a -> a + 8 <= 2 ^ 47 -> cell M a 8 (W v) ->
  Step.ro_cells segs (mrestrict HI M) a [C8 (Z_to_bv 64 v)].
Proof.
  intros M a v Ha Hn Hc. apply (RHB.cells_at_cons segs); [exact I | | apply (RHB.cells_at_nil segs); cbn [Cells.csize]; lia].
  exact (RHB.bytes_of_cell segs _ a 8 (W v) ltac:(lia) ltac:(lia) (RHB.cell_restrict segs M a 8 (W v) ltac:(lia) ltac:(lia) Hc)).
Qed.
Lemma ro4 : forall (M : word -> option byte) a v, 0 <= a -> a + 4 <= 2 ^ 47 -> cell M a 4 (W v) ->
  Step.ro_cells segs (mrestrict HI M) a [C4 (Z_to_bv 64 v)].
Proof.
  intros M a v Ha Hn Hc. apply (RHB.cells_at_cons segs); [exact I | | apply (RHB.cells_at_nil segs); cbn [Cells.csize]; lia].
  exact (RHB.bytes_of_cell segs _ a 4 (W v) ltac:(lia) ltac:(lia) (RHB.cell_restrict segs M a 4 (W v) ltac:(lia) ltac:(lia) Hc)).
Qed.
Lemma le1_W : forall b : Z, 0 <= b < 256 -> word_to_le_bytes 1 (W b) = [Z_to_bv 8 b].
Proof.
  intros b Hb. unfold word_to_le_bytes, LBNS.W. rewrite u64_lit by lia. cbn [Z_to_le_bytes]. f_equal.
Qed.
Lemma ro1 : forall (M : word -> option byte) a b, 0 <= a -> a + 1 <= 2 ^ 47 -> 0 <= b < 256 -> cell M a 1 (W b) ->
  Step.ro_cells segs (mrestrict HI M) a [C1 (Z_to_bv 8 b)].
Proof.
  intros M a b Ha Hn Hb Hc. apply (RHB.cells_at_cons segs); [exact I | | apply (RHB.cells_at_nil segs); cbn [Cells.csize]; lia].
  cbn [Cells.cbytes]. rewrite <- (le1_W b Hb).
  exact (RHB.bytes_of_cell segs _ a 1 (W b) ltac:(lia) ltac:(lia) (RHB.cell_restrict segs M a 1 (W b) ltac:(lia) ltac:(lia) Hc)).
Qed.

(* [comment removed for export] *)
Lemma stk_rw : forall (M : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 47 -> RGK.rw segs M a n -> Frame.stk segs (mrestrict HI M) a (a + n).
Proof.
  intros M a n Ha Hn [Hrd _]. apply (RHB.stk_of_rd_ok segs); [lia | lia |]. exact (RHB.rd_ok_restrict M a n Ha Hn Hrd).
Qed.

(* [comment removed for export] *)
Lemma bcell : forall (M : word -> option byte) a (w : nat) v, 0 <= a -> a + Z.of_nat w <= 2 ^ 47 -> cell M a w v ->
  Mem.bytes_at segs (mrestrict HI M) a (word_to_le_bytes w v).
Proof.
  intros M a w v Ha Hn Hc.
  exact (RHB.bytes_of_cell segs _ a w v ltac:(lia) ltac:(lia) (RHB.cell_restrict segs M a w v ltac:(lia) ltac:(lia) Hc)).
Qed.

Lemma wr_sub : forall (M : word -> option byte) a n a' n', wr_ok M a n -> a <= a' -> a' + n' <= a + n -> wr_ok M a' n'.
Proof. intros M a n a' n' Hw H1 H2 x j Hx Hj. apply Hw; lia. Qed.

Lemma inds_window : forall ds, forallb (d_okb y) ds = true -> forall o, In o (inds ds) -> l_odr_lo y <= o < l_odr_hi y.
Proof.
  intros ds Hok o Ho. unfold inds in Ho. apply in_map_iff in Ho as (d & <- & Hd). apply filter_In in Hd as [Hd Hi].
  rewrite forallb_forall in Hok. specialize (Hok d Hd). unfold d_okb in Hok. apply andb_prop in Hok as [_ Hw].
  unfold is_ind in Hi. apply negb_true_iff in Hi. rewrite Hi in Hw. cbn [orb] in Hw. apply andb_prop in Hw as [X1 X2].
  apply Z.leb_le in X1. apply Z.ltb_lt in X2. lia.
Qed.

Lemma outside_app : forall (a b : list Frame.ivl) x, Frame.outside a x -> Frame.outside b x -> Frame.outside (a ++ b) x.
Proof. induction a as [|[lo hi] r IH]; intros b x Ha Hb; cbn [app Frame.outside] in *; [exact Hb|]. destruct Ha as [H1 H2]. split; [exact H1 | exact (IH b x H2 Hb)]. Qed.
Lemma outside_ind_fp : forall os x, ~ In x os -> Frame.outside (map (fun o => (o, o + 1)) os) x.
Proof.
  induction os as [|o r IH]; intros x Hx; cbn [map Frame.outside]; [exact I|]. split; [| apply IH; intros Y; apply Hx; right; exact Y].
  intros Y. apply Hx. left. lia.
Qed.

Theorem regrun_contract_of_walk : RGS.walk_stmt segs T -> RGK.regrun_contract segs T.
Proof.
  intros WALK regs M i n ds N ne ks ks' ne' B cur lend size first fp k na sp
    G27 G8 G2 G9 G20 G21 G24 G25 Hrun Hk Hi Hin Hn Htab0 Htab1 Hdesc Hnd Hind Hodrw
    Cin Win Cf24 Cf85 Cf100 Csh Ccp Cms Cal Cn Cmp Rks Rfr Hfp16 Hsp1 Hsp2 Hfp Rshw
    Clend Ccur Wlla Hcur0 Hroom Hlend Rlla Hlla1 Hlla2 Hlla3 Csize Cfirst Wlist Hsize1 Hsize2 Hmap RO.
  subst k na sp.
  set (m := mrestrict HI M).
  assert (Bin := ct_bounds (c_inited T) ltac:(cbn; tauto)). assert (Bfl := ct_bounds (c_flags T) ltac:(cbn; tauto)).
  assert (Bsh := ct_bounds (c_shcell T) ltac:(cbn; tauto)). assert (Bcp := ct_bounds (c_canpoison T) ltac:(cbn; tauto)).
  assert (Bms := ct_bounds (c_msetcell T) ltac:(cbn; tauto)). assert (Bal := ct_bounds (c_llaalign T) ltac:(cbn; tauto)).
  assert (Bla := ct_bounds (c_lla T) ltac:(cbn; tauto)). assert (Bst := ct_bounds (c_statics T) ltac:(cbn; tauto)).
  assert (Bmp := ct_bounds (c_map T) ltac:(cbn; tauto)). assert (Bil := ct_bounds (l_ilo y) ltac:(cbn; tauto)).
  assert (Bih := ct_bounds (l_ihi y) ltac:(cbn; tauto)). assert (Bsb := ct_bounds (l_shb y) ltac:(cbn; tauto)).
  assert (Bol := ct_bounds (l_odr_lo y) ltac:(cbn; tauto)). assert (Boh := ct_bounds (l_odr_hi y) ltac:(cbn; tauto)).
  assert (Bsw : 0 <= shad y (l_ilo y) /\ shad y (l_ilo y) <= shad y (l_ihi y) /\ shad y (l_ihi y) < 2 ^ 41).
  { unfold shad. unfold ctab_okb in CT. apply andb_prop in CT as [_ CL]. apply Z.leb_le in CL.
    pose proof (Z.div_le_mono _ _ 8 ltac:(lia) CL). pose proof (Z.div_pos (l_ilo y) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (l_ihi y) 8 (2 ^ 40) ltac:(lia) ltac:(lia)). lia. }
  pose proof (run_ok _ _ _ _ _ _ Hrun) as Hok.
  (* [comment removed for export] *)
  assert (P_desc : forall j, 0 <= j < Z.of_nat (length ds) -> RGS.desc_at segs m (c_tab T + 64 * (i + j)) (nth (Z.to_nat j) ds RGS.dflt)).
  { intros j Hj. destruct (Hdesc j Hj) as (D0 & D1 & D2 & D5 & D7). set (g := c_tab T + 64 * (i + j)) in *.
    assert (Bg : 0 <= g /\ g + 64 <= 2 ^ 40) by (unfold g; lia).
    split; [| split; [exact (ro8 M (g + 40) (d_dyn (nth (Z.to_nat j) ds RGS.dflt)) ltac:(lia) ltac:(lia) D5) | exact (ro8 M (g + 56) (d_odr (nth (Z.to_nat j) ds RGS.dflt)) ltac:(lia) ltac:(lia) D7)]].
    apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ D0); lia |].
    cbn [Cells.csize]. replace (g + Z.of_nat 8) with (g + 8) by lia.
    apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ D1); lia |].
    cbn [Cells.csize]. replace (g + 8 + Z.of_nat 8) with (g + 16) by lia.
    apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ D2); lia |].
    apply (RHB.cells_at_nil segs). cbn [Cells.csize]. lia. }
  assert (P_ind : forall o, In o (inds ds) -> Step.rw_cells segs m o [C1 (Z_to_bv 8 0)]).
  { intros o Ho. pose proof (inds_window ds Hok o Ho) as Bo.
    split; [exact (ro1 M o 0 ltac:(lia) ltac:(lia) ltac:(lia) (Hind o Ho))|].
    exact (RHB.wr_at_of_wr_ok segs M o 1 ltac:(lia) ltac:(lia) (wr_sub M _ _ o 1 Hodrw ltac:(lia) ltac:(lia))). }
  assert (P_in : Step.rw_cells segs m (c_inited T) [C1 (Z_to_bv 8 1)]).
  { split; [exact (ro1 M (c_inited T) 1 ltac:(lia) ltac:(lia) ltac:(lia) Cin) | exact (RHB.wr_at_of_wr_ok segs M (c_inited T) 1 ltac:(lia) ltac:(lia) Win)]. }
  pose proof (ro4 M (c_flags T + 24) 1 ltac:(lia) ltac:(lia) Cf24) as P_f24. pose proof (ro1 M (c_flags T + 85) 1 ltac:(lia) ltac:(lia) ltac:(lia) Cf85) as P_f85.
  pose proof (ro4 M (c_flags T + 100) 2 ltac:(lia) ltac:(lia) Cf100) as P_f100. pose proof (ro8 M (c_shcell T) (l_shb y) ltac:(lia) ltac:(lia) Csh) as P_sh.
  pose proof (ro1 M (c_canpoison T) 1 ltac:(lia) ltac:(lia) ltac:(lia) Ccp) as P_cp. pose proof (ro8 M (c_msetcell T) (c_memset T) ltac:(lia) ltac:(lia) Cms) as P_ms.
  pose proof (ro8 M (c_llaalign T) 8 ltac:(lia) ltac:(lia) Cal) as P_al.
  pose proof (ro8 M (fp - 0x10b0) n ltac:(lia) ltac:(lia) Cn) as P_n. pose proof (ro8 M (fp - 0x10d0) (c_msetcell T) ltac:(lia) ltac:(lia) Cmp) as P_mp.
  pose proof (stk_rw M (fp - 0x10a8) 8 ltac:(lia) ltac:(lia) Rks) as P_ks. replace (fp - 0x10a8 + 8) with (fp - 0x10a0) in P_ks by lia.
  pose proof (stk_rw M (fp - 0x10f0 - 32) 32 ltac:(lia) ltac:(lia) Rfr) as P_fr. replace (fp - 0x10f0 - 32 + 32) with (fp - 0x10f0) in P_fr by lia.
  pose proof (stk_rw M (shad y (l_ilo y)) (shad y (l_ihi y) - shad y (l_ilo y)) ltac:(lia) ltac:(lia) Rshw) as P_shw.
  replace (shad y (l_ilo y) + (shad y (l_ihi y) - shad y (l_ilo y))) with (shad y (l_ihi y)) in P_shw by lia.
  set (na := Z.of_nat (length ds) + nind ds) in *.
  assert (Hna : 0 <= nind ds) by (unfold nind; lia).
  assert (P_lla : Step.rw_cells segs m (c_lla T) [C8 (Z_to_bv 64 lend); C8 (Z_to_bv 64 cur)]).
  { split; [| exact (RHB.wr_at_of_wr_ok segs M (c_lla T) 16 ltac:(lia) ltac:(lia) Wlla)].
    apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ Clend); lia |].
    cbn [Cells.csize]. replace (c_lla T + Z.of_nat 8) with (c_lla T + 8) by lia.
    apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ Ccur); lia |].
    apply (RHB.cells_at_nil segs). cbn [Cells.csize]. lia. }
  pose proof (stk_rw M cur (16 * na) ltac:(lia) ltac:(lia) Rlla) as P_llar.
  assert (P_list : Step.rw_cells segs m (c_statics T + 8) [C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 first)]).
  { split; [| exact (RHB.wr_at_of_wr_ok segs M (c_statics T + 8) 16 ltac:(lia) ltac:(lia) Wlist)].
    apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ Csize); lia |].
    cbn [Cells.csize]. replace (c_statics T + 8 + Z.of_nat 8) with (c_statics T + 16) by lia.
    apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ Cfirst); lia |].
    apply (RHB.cells_at_nil segs). cbn [Cells.csize]. lia. }
  assert (P_map : 0 < nind ds -> RGS.map_pre segs T m B N ne ks cur na fp).
  { intros Hpos. destruct (Hmap Hpos) as (M1 & M1w & MB & Mne & Mtb & MN & Mw & HN & Hne & Hlen & Hrng & Mkeys & MR & B0 & BT & BI & B8 & BS & BA & BF).
    unfold RGS.map_pre.
    split; [split; [exact (ro8 M (c_statics T + 56) (c_map T) ltac:(lia) ltac:(lia) M1) | exact (RHB.wr_at_of_wr_ok segs M (c_statics T + 56) 8 ltac:(lia) ltac:(lia) M1w)]|].
    split.
    { split; [| exact (RHB.wr_at_of_wr_ok segs M (c_map T) 20 ltac:(lia) ltac:(lia) Mw)].
      apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ MB); lia |].
      cbn [Cells.csize]. replace (c_map T + Z.of_nat 8) with (c_map T + 8) by lia.
      apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ Mne); lia |].
      cbn [Cells.csize]. replace (c_map T + 8 + Z.of_nat 4) with (c_map T + 12) by lia.
      apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ Mtb); lia |].
      cbn [Cells.csize]. replace (c_map T + 12 + Z.of_nat 4) with (c_map T + 16) by lia.
      apply (RHB.cells_at_cons segs); [exact I | refine (bcell M _ _ _ _ _ MN); lia |].
      apply (RHB.cells_at_nil segs). cbn [Cells.csize]. lia. }
    split; [exact HN|]. split; [exact Hne|]. split; [exact Hlen|]. split; [exact Hrng|].
    split; [intros b Hb; exact (ro8 M (B + 32 * b) (nth (Z.to_nat b) ks 0) ltac:(lia) ltac:(lia) (Mkeys b Hb))|].
    split; [exact (stk_rw M B (32 * N) ltac:(lia) ltac:(lia) MR)|].
    repeat (split; [assumption|]). assumption. }
  pose proof (mem_inv_restrict M RO) as P_inv.
  (* [comment removed for export] *)
  pose proof (WALK i n ds N ne ks ks' ne' B cur lend size first fp
                (getr regs (Z_to_bv 5 1)) (getr regs (Z_to_bv 5 3)) (getr regs (Z_to_bv 5 4)) (getr regs (Z_to_bv 5 5)) (getr regs (Z_to_bv 5 6)) (getr regs (Z_to_bv 5 7))
                (getr regs (Z_to_bv 5 10)) (getr regs (Z_to_bv 5 11)) (getr regs (Z_to_bv 5 12)) (getr regs (Z_to_bv 5 13)) (getr regs (Z_to_bv 5 14))
                (getr regs (Z_to_bv 5 15)) (getr regs (Z_to_bv 5 16)) (getr regs (Z_to_bv 5 17))
                (getr regs (Z_to_bv 5 28)) (getr regs (Z_to_bv 5 29)) (getr regs (Z_to_bv 5 30)) (getr regs (Z_to_bv 5 31))
                (getr regs (Z_to_bv 5 18)) (getr regs (Z_to_bv 5 19)) (getr regs (Z_to_bv 5 22)) (getr regs (Z_to_bv 5 23)) (getr regs (Z_to_bv 5 26))
                bvmap_empty (Z_to_bv 32 0) m) as X.
  cbv zeta in X. fold na in X.
  specialize (X Hrun Hk Hi Hin Hn P_desc Hnd P_ind P_in P_f24 P_f85 P_f100 P_sh P_cp P_ms P_al P_n P_mp P_ks P_fr Hfp16 Hsp1 Hsp2 Hfp P_shw
                P_lla Hcur0 Hroom Hlend P_llar Hlla1 Hlla2 Hlla3 P_list Hsize1 Hsize2 P_map P_inv).
  assert (Ecan : HBR.canon regs =
            Frame.mkR (getr regs (Z_to_bv 5 1)) (Z_to_bv 64 (fp - 0x10f0)) (getr regs (Z_to_bv 5 3)) (getr regs (Z_to_bv 5 4)) (getr regs (Z_to_bv 5 5))
              (getr regs (Z_to_bv 5 6)) (getr regs (Z_to_bv 5 7)) (Z_to_bv 64 fp) (Z_to_bv 64 (c_tab T))
              (getr regs (Z_to_bv 5 10)) (getr regs (Z_to_bv 5 11)) (getr regs (Z_to_bv 5 12)) (getr regs (Z_to_bv 5 13)) (getr regs (Z_to_bv 5 14))
              (getr regs (Z_to_bv 5 15)) (getr regs (Z_to_bv 5 16)) (getr regs (Z_to_bv 5 17))
              (getr regs (Z_to_bv 5 18)) (getr regs (Z_to_bv 5 19)) (Z_to_bv 64 (c_shcell T)) (Z_to_bv 64 1) (getr regs (Z_to_bv 5 22)) (getr regs (Z_to_bv 5 23))
              (Z_to_bv 64 (c_flags T)) (Z_to_bv 64 (c_statics T)) (getr regs (Z_to_bv 5 26)) (Z_to_bv 64 i)
              (getr regs (Z_to_bv 5 28)) (getr regs (Z_to_bv 5 29)) (getr regs (Z_to_bv 5 30)) (getr regs (Z_to_bv 5 31))).
  { unfold HBR.canon. unfold LBNS.W in G27, G8, G2, G9, G20, G21, G24, G25.
    change (getr regs (Z_to_bv 5 2)) with (getr regs 2%bv). change (getr regs (Z_to_bv 5 8)) with (getr regs 8%bv).
    change (getr regs (Z_to_bv 5 9)) with (getr regs 9%bv). change (getr regs (Z_to_bv 5 20)) with (getr regs 20%bv).
    change (getr regs (Z_to_bv 5 21)) with (getr regs 21%bv). change (getr regs (Z_to_bv 5 24)) with (getr regs 24%bv).
    change (getr regs (Z_to_bv 5 25)) with (getr regs 25%bv). change (getr regs (Z_to_bv 5 27)) with (getr regs 27%bv).
    rewrite G27, G8, G2, G9, G20, G21, G24, G25. reflexivity. }
  rewrite <- Ecan in X.
  destruct (HBR.evt_bridge segs HI (RHB.HI_off segs SEG_below) Hwx _ regs (Z_to_bv 64 (c_entry T)) M (seg_rom segs) X)
    as (ms1 & ms2 & HQ & Hrun2 & Ereg & Efr & Epc & Esvc & Erv & Efc & Erom & Emem & HG).
  destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s2' & s6' & s7' & m' & -> &
                  Hmunch & Hwm & Hinv' & Hcur' & Hlist' & Hmap').
  cbn [MState.MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  rewrite (HBR.mkst_eta ms2 Efr Esvc Erv Efc) in Hrun2. rewrite Epc, Erom, Emem in Hrun2.
  exists (ms_regs ms2), (munrestrict HI M m').
  split; [exact Hrun2|].
  assert (Elow : forall x : word, bv_unsigned x < 2 ^ 47 -> munrestrict HI M m' x = m' x).
  { intros x Hx. unfold munrestrict. rewrite (RHB.HI_low x Hx). reflexivity. }
  assert (Cup : forall a (w : nat) v, 0 <= a -> a + Z.of_nat w <= 2 ^ 47 -> cell m' a w v -> cell (munrestrict HI M m') a w v).
  { intros a w v Ha Hw Hc. unfold LBNS.cell in *. rewrite <- Hc. apply rdn_ext; [rewrite LBNS.u_W by lia; lia|].
    intros x Hx. rewrite LBNS.u_W in Hx by lia. apply Elow. lia. }
  unfold LBNS.W in G27, G8, G2, G9, G20, G21, G24, G25.
  split.
  { (* [comment removed for export] *)
    intros r Hnin Hn27. unfold getr. destruct (bv_eqb r 0) eqn:E0; [reflexivity|].
    assert (Hr : r <> 0%bv) by (intros ->; rewrite bv_eqb_refl in E0; discriminate E0).
    rewrite <- (Ereg r Hr). rewrite <- G8, <- G2, <- G9, <- G20, <- G21, <- G24, <- G25.
    destruct (HBR.reg_cases r Hr) as (q & Hq & ->).
    assert (Hq' : q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12
                  \/ q = 13 \/ q = 14 \/ q = 15 \/ q = 16 \/ q = 17 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23
                  \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27 \/ q = 28 \/ q = 29 \/ q = 30 \/ q = 31) by lia.
    clear - Hq' Hnin Hn27.
    repeat (destruct Hq' as [-> | Hq']); try (subst q);
      first [ reflexivity
            | exfalso; apply Hn27; vm_compute; reflexivity
            | exfalso; apply Hnin; vm_compute; solve [repeat (first [left; reflexivity | right])] ]. }
  split.
  { unfold getr. change (bv_eqb 27%bv 0) with false. cbv iota. rewrite <- (Ereg 27%bv ltac:(intros Y; discriminate Y)). reflexivity. }
  destruct Hcur' as [Hcur' _]. apply (RHB.cells_at_uncons segs) in Hcur' as [Hcur' _].
  split; [exact (Cup (c_lla T + 8) 8%nat (W (cur + 16 * na)) ltac:(lia) ltac:(lia) (RHB.cell_of_bytes segs m' (c_lla T + 8) 8 (W (cur + 16 * na)) Hcur'))|].
  destruct Hlist' as [Hlist' _]. apply (RHB.cells_at_uncons segs) in Hlist' as [Hl1 Hl2]. apply (RHB.cells_at_uncons segs) in Hl2 as [Hl2 _].
  cbn [Cells.csize] in Hl2. replace (c_statics T + 8 + Z.of_nat 8) with (c_statics T + 16) in Hl2 by lia.
  split; [exact (Cup (c_statics T + 8) 8%nat (W (size + Z.of_nat (length ds))) ltac:(lia) ltac:(lia) (RHB.cell_of_bytes segs m' (c_statics T + 8) 8 (W (size + Z.of_nat (length ds))) Hl1))|].
  split; [exact (Cup (c_statics T + 16) 8%nat (W (cur + 16 * na - 16)) ltac:(lia) ltac:(lia) (RHB.cell_of_bytes segs m' (c_statics T + 16) 8 (W (cur + 16 * na - 16)) Hl2))|].
  split.
  { intros Hpos. destruct (Hmap' Hpos) as [[Hne' _] Hkeys']. apply (RHB.cells_at_uncons segs) in Hne' as [Hne' _].
    destruct (Hmap Hpos) as (_ & _ & _ & _ & _ & _ & _ & HN & _ & _ & _ & _ & _ & B0 & BT & _).
    split; [exact (Cup (c_map T + 8) 4%nat (W ne') ltac:(lia) ltac:(lia) (RHB.cell_of_bytes segs m' (c_map T + 8) 4 (W ne') Hne'))|].
    intros b Hb. destruct (Hkeys' b Hb) as [Hkb _]. apply (RHB.cells_at_uncons segs) in Hkb as [Hkb _].
    exact (Cup (B + 32 * b) 8%nat (W (nth (Z.to_nat b) ks' 0)) ltac:(lia) ltac:(lia) (RHB.cell_of_bytes segs m' (B + 32 * b) 8 (W (nth (Z.to_nat b) ks' 0)) Hkb)). }
  split.
  { intros x Hx. unfold munrestrict. destruct (HI x) eqn:EH; [reflexivity|].
    rewrite (Hmunch x); [unfold m, mrestrict; rewrite EH; reflexivity|].
    unfold RGK.rg_FP, LBNS.inr in Hx.
    apply outside_app; [| apply outside_app].
    - cbn [Frame.outside]. repeat split; try (intros Y; apply Hx; lia).
    - apply outside_ind_fp. intros Y. apply Hx. do 6 right. left. exact Y.
    - destruct (0 <? nind ds) eqn:Epos; [| exact I]. cbn [Frame.outside]. repeat split; intros Y; apply Hx; do 7 right; (split; [reflexivity | lia]). }
  intros x Hx. unfold munrestrict. destruct (HI x) eqn:EH; [exact Hx|].
  apply HG. unfold mrestrict. rewrite EH. exact Hx.
Qed.

End RB.
End RGB.

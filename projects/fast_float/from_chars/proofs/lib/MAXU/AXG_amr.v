(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM MngNtfS MngMWP MngMW0 MngMW1 MngMW2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_am1 AXG_am3 AXG_am4 AXG_am5 AXG_amr0.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt10z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt100z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am4 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am5 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_amr0.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition open_cw (p : sptr) (s1 : astate) : list mcell :=
  [am_cell (padd (padd p AREA_HDR) META_SIZE); amc_cell (METAS_PER_AREA - 1); ac_cell (st_avail_meta_area_count s1 - 1);
   head_cell (match st_area_head s1 with None => Some p | h => h end); tail_cell (Some p); ama_cell (padd p 4096);
   MCell (LMem p) 8 VSec; MCell (LMem (padd p 16)) 4 (VZ METAS_PER_AREA)]
  ++ match st_areas s1 with [] => [] | _ => [anext_cell (last (st_areas s1) (SP 0%nat 0)) (Some p)] end.

(* [comment removed for export] *)
Definition OEXC : list loc := [LCtx CTX_avail_meta; LCtx CTX_avail_meta_count; LCtx CTX_avail_meta_areas].

Ltac not_oexc := let H := fresh "H" in intros H; unfold OEXC in H; cbn [In] in H;
  repeat (destruct H as [H|H]; [injection H as H; cbv in H; discriminate H|]); exact H.

Lemma pc_rd : forall HTOP L EXC s m sp0 K c, PCUT HTOP L EXC s m sp0 K -> In c (image s) -> ~ In (mc_loc c) EXC -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
  rdn SEGS m (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))).
Proof. intros HTOP L EXC s m sp0 K c P Hc Hn Hv Hw. exact (holds_rdn SEGS L m c (pc_cells _ _ _ _ _ _ _ P c Hc Hn) Hv Hw). Qed.

Lemma pc_wr : forall HTOP L EXC s m sp0 K f, PCUT HTOP L EXC s m sp0 K -> In f (footprint s) ->
  forall a n, loc_addr L (fst f) <= a -> a + n <= loc_addr L (fst f) + snd f -> 0 <= a -> a + n <= 2^64 ->
  forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (a + d)) k = true.
Proof.
  intros HTOP L EXC s m sp0 K f P Hf a n H1 H2 H3 H4. apply (store_ok_of_bytes SEGS m a n).
  intros j Hj. pose proof (proj1 (Forall_forall _ _) (pc_fp _ _ _ _ _ _ _ P) f Hf (a + j) ltac:(lia)) as H.
  unfold bview in H. destruct ((0 <=? a + j) && (a + j <? 2^64)); [|exfalso; exact (H eq_refl)].
  destruct (wview SEGS m (wa (a + j))); [discriminate | exfalso; exact (H eq_refl)].
Qed.

Lemma zp_wr : forall m a, ZP m a -> 0 <= a -> a + PGSZ <= 2^64 -> forall o n, 0 <= o -> o + n <= PGSZ ->
  forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m (wa (a + o + d)) k = true.
Proof.
  intros m a HZ H0 H1 o n Ho Hn. apply (store_ok_of_bytes SEGS m (a + o) n).
  intros j Hj E. unfold wview in E. rewrite (HZ (a + o + j) ltac:(unfold PGSZ in *; lia)) in E. discriminate E.
Qed.

Definition hide (P : Prop) : Prop := P.

Section AMR.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem open_mach : forall HTOP X R U L s1 m1 R0 rom sp0 K can ra s0 s1' s2 s3 s4,
  PCUT HTOP L OEXC s1 m1 sp0 K -> 1152 <= K ->
  Inv X R U (open_st (st_avail_meta_areas s1) s1) -> rgeoA HTOP L s1 -> rdisj L s1 ->
  st_init_done s1 = true -> 0 < st_avail_meta_area_count s1 ->
  st_area_head s1 = hd_error (st_areas s1) ->
  st_area_tail s1 = (match st_areas s1 with [] => None | l => Some (last l (SP 0%nat 0)) end) ->
  ZP m1 (loc_addr L (LMem (st_avail_meta_areas s1))) ->
  am_frame R0 m1 sp0 can ra s0 s1' s2 s3 s4 -> getr R0 9 = wa (loc_addr L (LMem (st_avail_meta_areas s1))) ->
  (ra = 0x542a0 \/ ra = 0x53ec4) ->
  exists R' m2, msteps SEGS (mkst R0 (wa 0x53c78) m1 rom) (mkst R' (wa ra) m2 rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa s0 /\ getr R' 9 = wa s1' /\
    getr R' 10 = wa (loc_addr L (LMem (st_avail_meta_areas s1)) + 24) /\
    getr R' 18 = wa s2 /\ getr R' 19 = wa s3 /\ getr R' 20 = wa s4 /\
    (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))) /\
    Forall (cell_holds L (bview SEGS m2)) (open_cw (st_avail_meta_areas s1) s1) /\
    (forall x, (loc_addr L (LMem (st_avail_meta_areas s1)) + 8 <= x < loc_addr L (LMem (st_avail_meta_areas s1)) + 16 \/
                loc_addr L (LMem (st_avail_meta_areas s1)) + 24 <= x < loc_addr L (LMem (st_avail_meta_areas s1)) + 4096) ->
       m2 (wa x) = Some (Z_to_bv 8 0)) /\
    (forall x, 0 <= x < 2^64 -> m2 (wa x) <> m1 (wa x) -> exists c', In c' (open_cw (st_avail_meta_areas s1) s1) /\ in_rng (cell_range L c') x) /\
    mem_grows m1 m2 /\ 4096 <= loc_addr L (LMem (st_avail_meta_areas s1)) /\ loc_addr L (LMem (st_avail_meta_areas s1)) + 4096 <= HTOP.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L s1 m1 R0 rom sp0 K can ra s0 s1' s2 s3 s4 P HK HIo HG HD Hi Hac Hhd Htl HZ F R9 Hra.
  set (p := st_avail_meta_areas s1) in *. set (pa := loc_addr L (LMem p)) in *.
  set (so := open_st p s1) in *.
  pose proof P as [HCS HFM Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HT HTB].
  change (hide (ra = 0x542a0 \/ ra = 0x53ec4)) in Hra.
  assert (HGo : rgeoA HTOP L so) by (intros k rg Hk Hl; exact (HG k rg Hk Hl)).
  (* [comment removed for export] *)
  assert (GEO : forall a, In a (st_areas so) -> 4096 <= loc_addr L (LMem a) /\ loc_addr L (LMem a) mod 4096 = 0 /\
                  loc_addr L (LMem a) + 4096 <= HTOP /\ hide (loc_addr L (LMem a) + 4096 <= 0x10000 \/ 0x99000 <= loc_addr L (LMem a))).
  { intros a Ha. destruct (area_range HTOP X R U so L a HIo HGo Ha) as (r & rg & Epr & Hr & Hl & _ & B1 & B2 & B3 & B4).
    destruct (HGo r rg Hr Hl) as (G1 & G2 & G3 & G4). unfold ranges_disjoint in G4. cbn [fst snd] in G4.
    clear - Epr B1 B2 B3 B4 G1 G2 G3 G4. unfold hide. rewrite loc_addr_LMem in *. rewrite Epr in *. unfold PGSZ in *. split; [lia|]. split.
    - apply Z.mod_divide in G2; [|lia]. apply Z.mod_divide in B4; [|lia]. destruct G2 as (k1 & E1). destruct B4 as (k2 & E2). rewrite E1, E2.
      replace (k1 * 4096 + k2 * 4096) with ((k1 + k2) * 4096) by ring. apply Z.mod_mul. lia.
    - split; lia. }
  assert (Hpin : In p (st_areas so)) by (unfold so; rewrite st_areas_open; apply in_app_iff; right; left; reflexivity).
  destruct (GEO p Hpin) as (Rpa1 & Rpa2 & Rpa3 & Rpa4). fold pa in Rpa1, Rpa2, Rpa3, Rpa4.
  assert (Rpa5 : pa + 4096 <= 2^47) by (clear - Rpa3 HTB; lia).
  assert (Rpa6 : pa + 4096 <= sp0 - 1024) by (clear - Rpa3 HT HK; lia).
  pose proof (open_page_fresh HTOP X R U s1 L p HTB HIo Hctx HG HD) as FR. fold pa in FR.
  set (ac := st_avail_meta_area_count s1) in *.
  assert (Rac : 1 <= ac <= 2^60).
  { pose proof (inv_areas HIo) as (_ & _ & _ & _ & _ & _ & _ & A8 & _).
    destruct (Z.eq_dec ac 1) as [E|E]; [clear - E; lia|].
    assert (Hac1 : 0 < st_avail_meta_area_count so) by (unfold so; rewrite st_area_count_open; fold ac; clear - E Hac; lia).
    destruct (A8 Hac1) as (r' & o' & rg' & _ & Hr' & _ & Hl' & _ & Ho' & Hlen' & _).
    unfold so in Hlen'. rewrite st_area_count_open in Hlen'. fold ac in Hlen'. destruct (HGo r' rg' Hr' Hl') as (G1' & _ & G3' & _).
    clear - Hac Hlen' Ho' G1' G3' HTB. unfold PGSZ in *. lia. }
  set (sec := ly_sec L mod 2^64).
  assert (Hsec : sec mod 2^64 = ly_sec L mod 2^64) by (unfold sec; apply Z.mod_mod; discriminate).
  assert (Rsec : 0 <= sec <= 2^64-1) by (clear - sec; unfold sec; pose proof (Z.mod_pos_bound (ly_sec L) (2^64) ltac:(reflexivity)); lia).
  assert (Msec : rdn SEGS m1 (wa (0 + 621720)) 8 = Some (word_to_le_bytes 8 (wa sec))).
  { pose proof (pc_rd HTOP L OEXC s1 m1 sp0 K (MCell (LCtx CTX_secret) 8 (if st_init_done s1 then VSec else VZ 0)) P
       ltac:(apply ctx_in_image; in_ctx13) ltac:(not_oexc) ltac:(intros z E; rewrite Hi in E; discriminate) ltac:(apply Nat.leb_le; reflexivity)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, Hi in H. cbn [sval_num] in H.
    change (0 + 621720) with (0x97c98 + CTX_secret). rewrite H. f_equal. f_equal. apply wa_eqm. exact (eq_sym Hsec). }
  assert (Mac : rdn SEGS m1 (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa ac))).
  { pose proof (pc_rd HTOP L OEXC s1 m1 sp0 K (MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s1))) P
       ltac:(apply ctx_in_image; in_ctx13) ltac:(not_oexc) ltac:(intros z E; discriminate) ltac:(apply Nat.leb_le; reflexivity)) as H.
    cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. exact H. }
  assert (Wctx : forall d k, 0 <= d -> d + Z.of_nat k <= 64 -> store_ok SEGS m1 (wa (0 + 621736 + d)) k = true).
  { intros d k Hd Hk. refine (pc_wr HTOP L OEXC s1 m1 sp0 K (LCtx 0, CTX_SIZE) P (or_introl eq_refl) 621736 64 _ _ _ _ d k Hd Hk);
      cbn [fst snd loc_addr]; try rewrite Hctx; unfold CTX_SIZE; clear; lia. }
  assert (Wpg : forall d k, 0 <= d -> d + Z.of_nat k <= 24 -> store_ok SEGS m1 (wa (pa + 0 + d)) k = true).
  { intros d k Hd Hk. refine (zp_wr m1 pa HZ _ _ 0 24 _ _ d k Hd Hk); clear - Rpa1 Rpa5; unfold PGSZ; lia. }
  assert (W16 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m1 (wa (pa + 24 + d)) k = true).
  { intros d k Hd Hk. refine (zp_wr m1 pa HZ _ _ 24 16 _ _ d k Hd Hk); clear - Rpa1 Rpa5; unfold PGSZ; lia. }
  assert (Dpg : 0 + 621736 + 64 <= pa + 0 \/ pa + 0 + 24 <= 0 + 621736) by (clear - Rpa1 Rpa4; unfold hide in Rpa4; lia).
  destruct (st_areas s1) as [|la0 t0] eqn:Ea.
  - (* [comment removed for export] *)
    try rewrite Ea in Htl. try rewrite Ea in Hhd. cbn [hd_error] in Hhd.
    assert (Mtl : rdn SEGS m1 (wa (0 + 621784)) 8 = Some (word_to_le_bytes 8 (wa 0))).
    { pose proof (pc_rd HTOP L OEXC s1 m1 sp0 K (MCell (LCtx CTX_meta_area_tail) 8 (optr (st_area_tail s1))) P
         ltac:(apply ctx_in_image; in_ctx13) ltac:(not_oexc) ltac:(intros z E; destruct (st_area_tail s1); discriminate) ltac:(apply Nat.leb_le; reflexivity)) as H.
      cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, Htl in H. cbn [optr sval_num] in H. exact H. }
    assert (P100 : mt100_pre R0 m1 pa ac sec).
    { constructor; [exact R9 | exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | clear - Rpa1 Rpa5; lia | exact Rac | exact Rsec | exact Rpa2 | exact Mac | exact Mtl | exact Msec
                   | exact Wctx | exact Wpg | exact Dpg]. }
    destruct (seg_amo0 R0 m1 rom sp0 can ra s0 s1' s2 s3 s4 pa ac sec F R9 P100 Rpa6 Rpa4 Hra W16)
      as (R' & Hms & Q1 & Q2 & Q8 & Q9 & Q10 & Q18 & Q19 & Q20 & QK).
    exists R', (amo0_mem m1 pa ac sec). split; [exact Hms|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q10|].
    split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact QK|].
    split.
    { unfold open_cw. rewrite Ea, Hhd, app_nil_r. fold ac.
      exact (amo0_cells m1 pa ac sec Rpa1 Rpa5 Rpa4 L p Hctx eq_refl Hsec). }
    split; [exact (amo0_zero m1 pa ac sec Rpa1 Rpa5 Rpa4 HZ)|].
    split; [|split; [exact (amo0_grows m1 pa ac sec) | split; [exact Rpa1 | exact Rpa3]]].
    intros x Hx Hne. destruct (amo0_wo m1 pa ac sec Rpa1 Rpa5 Rpa4 HZ x Hx Hne) as [A|[B|[C|D]]]; unfold open_cw; rewrite Ea, Hhd.
    + destruct (range_dec x 621744 8) as [A1|A1]; [exists (am_cell (padd (padd p AREA_HDR) META_SIZE)); split; [cbn [In app]; memb|]|].
      { unfold in_rng, cell_range, am_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_avail_meta. clear - A1; lia. }
      destruct (range_dec x 621752 8) as [A2|A2]; [exists (amc_cell (METAS_PER_AREA - 1)); split; [cbn [In app]; memb|]|].
      { unfold in_rng, cell_range, amc_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_avail_meta_count. clear - A2; lia. }
      exists (ac_cell (ac - 1)). split; [cbn [In app]; memb|].
      unfold in_rng, cell_range, ac_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_avail_meta_area_count. clear - A A1 A2; lia.
    + destruct (range_dec x 621776 8) as [A1|A1]; [exists (head_cell (Some p)); split; [cbn [In app]; memb|]|].
      { unfold in_rng, cell_range, head_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_meta_area_head. clear - A1; lia. }
      destruct (range_dec x 621784 8) as [A2|A2]; [exists (tail_cell (Some p)); split; [cbn [In app]; memb|]|].
      { unfold in_rng, cell_range, tail_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_meta_area_tail. clear - A2; lia. }
      exists (ama_cell (padd p 4096)). split; [cbn [In app]; memb|].
      unfold in_rng, cell_range, ama_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_avail_meta_areas. clear - B A1 A2; lia.
    + exists (MCell (LMem p) 8 VSec). split; [cbn [In app]; memb|]. unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. fold pa. clear - C; lia.
    + exists (MCell (LMem (padd p 16)) 4 (VZ METAS_PER_AREA)). split; [cbn [In app]; memb|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. fold pa. clear - D; lia.
  - (* [comment removed for export] *)
    set (la := last (la0 :: t0) (SP 0%nat 0)) in *.
    try rewrite Ea in Htl. try rewrite Ea in Hhd. cbn [hd_error] in Hhd.
    set (tl := loc_addr L (LMem la)).
    assert (Hla : In la (st_areas s1)) by (rewrite Ea; apply MngLt.last_In_l; discriminate).
    assert (Hlao : In la (st_areas so)) by (unfold so; rewrite st_areas_open; apply in_app_iff; left; exact Hla).
    destruct (GEO la Hlao) as (Rtl1 & _ & Rtl2 & Rtl3). fold tl in Rtl1, Rtl2, Rtl3.
    assert (Rtl5 : tl + 4096 <= 2^47) by (clear - Rtl2 HTB; lia).
    assert (Hfl : In (LMem la, PGSZ) (footprint s1)) by (right; apply in_app_iff; left; apply in_map_iff; exists la; auto).
    assert (Dtl : hide (tl + 4096 <= pa \/ pa + 4096 <= tl)).
    { pose proof (FR _ Hfl) as Dp. unfold ranges_disjoint, crange in Dp. cbn [fst snd] in Dp. fold tl in Dp. unfold hide, PGSZ in *. clear - Dp. lia. }
    assert (Mtl : rdn SEGS m1 (wa (0 + 621784)) 8 = Some (word_to_le_bytes 8 (wa tl))).
    { pose proof (pc_rd HTOP L OEXC s1 m1 sp0 K (MCell (LCtx CTX_meta_area_tail) 8 (optr (st_area_tail s1))) P
         ltac:(apply ctx_in_image; in_ctx13) ltac:(not_oexc) ltac:(intros z E; destruct (st_area_tail s1); discriminate) ltac:(apply Nat.leb_le; reflexivity)) as H.
      cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, Htl in H. cbn [optr sval_num] in H. exact H. }
    assert (Wtl : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m1 (wa (tl + 8 + d)) k = true).
    { intros d k Hd Hk. refine (pc_wr HTOP L OEXC s1 m1 sp0 K (LMem la, PGSZ) P Hfl (tl + 8) 8 _ _ _ _ d k Hd Hk); cbn [fst snd]; fold tl;
        clear - Rtl1 Rtl5; unfold PGSZ; lia. }
    assert (P10 : mt10_pre R0 m1 pa ac tl sec).
    { constructor; [exact R9 | exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | clear - Rpa1 Rpa5; lia | exact Rac | clear - Rtl1 Rtl5; lia | exact Rsec
                   | exact Rpa2 | exact Mac | exact Mtl | exact Msec | exact Wctx | exact Wpg | exact Wtl | exact Dpg | | | ];
      clear - Rpa1 Rpa4 Rtl1 Rtl3 Dtl; unfold hide in *; lia. }
    destruct (seg_amo R0 m1 rom sp0 can ra s0 s1' s2 s3 s4 pa ac tl sec F R9 P10 ltac:(clear - Rtl1 HTB; lia) Rpa6 Rpa4
       ltac:(clear - Rtl2 HT HK; lia) ltac:(clear - Rtl3; unfold hide in *; lia) Hra W16)
      as (R' & Hms & Q1 & Q2 & Q8 & Q9 & Q10 & Q18 & Q19 & Q20 & QK).
    exists R', (amo_mem m1 pa ac tl sec). split; [exact Hms|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q10|].
    split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact QK|].
    assert (Hhc : cell_holds L (bview SEGS m1) (head_cell (st_area_head s1))).
    { exact (HCS (head_cell (st_area_head s1)) (ctx_in_image s1 (head_cell (st_area_head s1)) ltac:(unfold head_cell; in_ctx13)) ltac:(unfold head_cell; cbn [mc_loc]; not_oexc)). }
    split.
    { unfold open_cw. rewrite Ea, Hhd. fold ac. rewrite Hhd in Hhc. cbn [app].
      exact (amo_cells m1 pa ac tl sec Rpa1 Rpa5 Rpa4 L p Hctx eq_refl Hsec la (Some la0) eq_refl Rtl1 Rtl5 Rtl3 Dtl Hhc). }
    split; [exact (amo_zero m1 pa ac tl sec Rpa1 Rpa5 Rpa4 Rtl1 Rtl5 Dtl HZ)|].
    split; [|split; [exact (amo_grows m1 pa ac tl sec) | split; [exact Rpa1 | exact Rpa3]]].
    intros x Hx Hne. destruct (amo_wo m1 pa ac tl sec Rpa1 Rpa5 Rpa4 Rtl1 Rtl5 Dtl HZ x Hx Hne) as [A|[B|[C|[D|E]]]];
      unfold open_cw; rewrite Ea, Hhd; fold la.
    + destruct (range_dec x 621744 8) as [A1|A1]; [exists (am_cell (padd (padd p AREA_HDR) META_SIZE)); split; [cbn [In app]; memb|]|].
      { unfold in_rng, cell_range, am_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_avail_meta. clear - A1; lia. }
      destruct (range_dec x 621752 8) as [A2|A2]; [exists (amc_cell (METAS_PER_AREA - 1)); split; [cbn [In app]; memb|]|].
      { unfold in_rng, cell_range, amc_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_avail_meta_count. clear - A2; lia. }
      exists (ac_cell (ac - 1)). split; [cbn [In app]; memb|].
      unfold in_rng, cell_range, ac_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_avail_meta_area_count. clear - A A1 A2; lia.
    + destruct (range_dec x 621784 8) as [A2|A2]; [exists (tail_cell (Some p)); split; [cbn [In app]; memb|]|].
      { unfold in_rng, cell_range, tail_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_meta_area_tail. clear - A2; lia. }
      exists (ama_cell (padd p 4096)). split; [cbn [In app]; memb|].
      unfold in_rng, cell_range, ama_cell. cbn [mc_loc mc_w loc_addr fst snd Z.of_nat Pos.of_succ_nat]. rewrite Hctx. unfold CTX_avail_meta_areas. clear - B A2; lia.
    + exists (anext_cell la (Some p)). split; [cbn [In app]; memb|].
      unfold in_rng, cell_range, anext_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. fold tl. clear - C; lia.
    + exists (MCell (LMem p) 8 VSec). split; [cbn [In app]; memb|]. unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. fold pa. clear - D; lia.
    + exists (MCell (LMem (padd p 16)) 4 (VZ METAS_PER_AREA)). split; [cbn [In app]; memb|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. fold pa. clear - E; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem open_tail : forall HTOP X R U L s1 m1 R0 rom sp0 K can ra s0 s1' s2 s3 s4,
  PCUT HTOP L OEXC s1 m1 sp0 K -> 1152 <= K ->
  Inv X R U (open_st (st_avail_meta_areas s1) s1) -> XNM X s1 -> rgeoA HTOP L s1 -> rdisj L s1 ->
  st_init_done s1 = true -> 0 < st_avail_meta_area_count s1 ->
  st_area_head s1 = hd_error (st_areas s1) ->
  st_area_tail s1 = (match st_areas s1 with [] => None | l => Some (last l (SP 0%nat 0)) end) ->
  ZP m1 (loc_addr L (LMem (st_avail_meta_areas s1))) ->
  am_frame R0 m1 sp0 can ra s0 s1' s2 s3 s4 -> getr R0 9 = wa (loc_addr L (LMem (st_avail_meta_areas s1))) ->
  (ra = 0x542a0 \/ ra = 0x53ec4) ->
  exists R' m2, msteps SEGS (mkst R0 (wa 0x53c78) m1 rom) (mkst R' (wa ra) m2 rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa s0 /\ getr R' 9 = wa s1' /\
    getr R' 10 = wa (loc_addr L (LMem (padd (st_avail_meta_areas s1) AREA_HDR))) /\
    getr R' 18 = wa s2 /\ getr R' 19 = wa s3 /\ getr R' 20 = wa s4 /\
    (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))) /\
    CUT HTOP (padd (st_avail_meta_areas s1) AREA_HDR :: X) R U L (s_opn (st_avail_meta_areas s1) s1) m2 sp0 K /\
    GROW sp0 K L s1 m1 L (s_opn (st_avail_meta_areas s1) s1) m2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L s1 m1 R0 rom sp0 K can ra s0 s1' s2 s3 s4 P HK HIo HX HG HD Hi Hac Hhd Htl HZ F R9 Hra.
  destruct (open_mach HTOP X R U L s1 m1 R0 rom sp0 K can ra s0 s1' s2 s3 s4 P HK HIo HG HD Hi Hac Hhd Htl HZ F R9 Hra)
    as (R' & m2 & Hms & Q1 & Q2 & Q8 & Q9 & Q10 & Q18 & Q19 & Q20 & QK & HNEW & HZ2 & HWO & HG2 & Rpa1 & Rpa3).
  change (hide (ra = 0x542a0 \/ ra = 0x53ec4)) in Hra.
  set (p := st_avail_meta_areas s1) in *. set (pa := loc_addr L (LMem p)) in *. set (so := open_st p s1) in *.
  exists R', m2. split; [exact Hms|].
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|].
  split; [rewrite loc_padd; exact Q10|].
  split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact QK|].
  pose proof P as [HCS HFM Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HT HTB].
  assert (Rpa5 : pa + 4096 <= 2^47) by (clear - Rpa3 HTB; lia).
  (* [comment removed for export] *)
  destruct (take_slot_Inv X R U so HIo ltac:(unfold so; cbn [open_st set_avail_meta set_avail_meta_count st_avail_meta_count]; unfold METAS_PER_AREA; clear; lia))
    as (Hfresh & NX & HI2 & EU2).
  assert (Hk1 : ~ In (padd p AREA_HDR) (keys s1)) by exact Hfresh.
  set (s' := s_opn p s1) in *.
  assert (HX2 : XNM (padd p AREA_HDR :: X) s').
  { intros x [<-|Hx]; [left; unfold s', s_opn, s_take; apply MT_upd_same|].
    assert (Hxk : x <> padd p AREA_HDR) by (intros ->; destruct (HX _ Hx) as [E|E]; apply Hk1; exact (MT_Some_In_keys s1 _ _ E)).
    unfold s', s_opn, s_take. rewrite MT_upd_other by exact Hxk. exact (HX x Hx). }
  set (Cnew := open_cw p s1 ++ area_cells s' p None).
  apply (silent_pc HTOP (padd p AREA_HDR :: X) R U L OEXC s1 s' m1 m2 sp0 K Cnew P).
  { (* [comment removed for export] *)
    intros c Hc HE. unfold OEXC in HE. cbn [In] in HE.
    assert (Kw : forall c', In c' [am_cell (padd (padd p AREA_HDR) META_SIZE); amc_cell (METAS_PER_AREA - 1); ama_cell (padd p 4096)] -> In c' Cnew).
    { intros c' Hc'. apply in_app_iff. left. unfold open_cw. apply in_app_iff. left. cbn [In] in Hc' |- *.
      destruct Hc' as [<-|[<-|[<-|[]]]]; memb. }
    destruct HE as [E|[E|[E|[]]]]; rewrite <- E.
    - exists (am_cell (padd (padd p AREA_HDR) META_SIZE)). split; [apply Kw; cbn [In]; memb|]. unfold in_rng, cell_range, am_cell. cbn [mc_loc mc_w fst snd]. lia.
    - exists (amc_cell (METAS_PER_AREA - 1)). split; [apply Kw; cbn [In]; memb|]. unfold in_rng, cell_range, amc_cell. cbn [mc_loc mc_w fst snd]. lia.
    - exists (ama_cell (padd p 4096)). split; [apply Kw; cbn [In]; memb|]. unfold in_rng, cell_range, ama_cell. cbn [mc_loc mc_w fst snd]. lia. }
  all: try exact HI2. all: try exact HX2. all: try exact HG. all: try exact HD. all: try exact (RMONO_refl s1).
  - (* [comment removed for export] *)
    intros f Hf. destruct (fp_open_inv p s1 f Hf) as [H | ->]; [left; exact H|]. right.
    intros x Hx. cbn [fst snd] in Hx. fold pa in Hx. unfold PGSZ in Hx.
    apply (bview_grow_n m1 m2 x HG2). rewrite (MngWb.bview_some_byte SEGS m1 x (Z_to_bv 8 0) ltac:(clear - Hx Rpa1 Rpa5; lia) (HZ x ltac:(unfold PGSZ; exact Hx))).
    discriminate.
  - (* [comment removed for export] *)
    intros c Hc. destruct (open_cov p s1 c Hk1 Hc) as [H|[(H1 & H2)|[H|(a & Hne & Ea & Ec)]]].
    + left. exact H.
    + right. apply in_app_iff. left. unfold open_cw. apply in_app_iff. left.
      destruct (open_cov_ctx p s1 c H1) as [H3|[E|[E|[E|[E|[E|E]]]]]]; [exfalso; exact (H2 H3)| | | | | |]; subst c; cbn [In]; memb.
    + right. apply in_app_iff. right. exact H.
    + right. apply in_app_iff. left. unfold open_cw. apply in_app_iff. right. subst a c.
      destruct (st_areas s1) as [|a0 t0]; [exfalso; exact (Hne eq_refl)|]. left. reflexivity.
  - (* [comment removed for export] *)
    intros c Hc. apply in_app_iff in Hc as [Hc|Hc].
    + unfold open_cw in Hc. apply in_app_iff in Hc as [Hc|Hc].
      * cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
        1-6: apply ctx_in_image; unfold s', s_opn, s_take, upd_meta, open_st; unfold ctx_cells; apply in_app_iff; left;
             cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
                  st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk set_metas set_avail_meta
                  set_avail_meta_count set_areas set_area_head set_area_tail set_avail_meta_areas set_avail_meta_area_count];
             destruct (st_areas s1) as [|a0 t0]; cbn [app andb In]; memb.
        1-2: apply in_image_front; apply in_app_iff; right; change (st_areas s') with (st_areas s1 ++ [p]); apply In_areas_cells_snoc_new;
             unfold area_cells; apply in_app_iff; left; cbn [In]; memb.
      * destruct (st_areas s1) as [|a0 t0] eqn:Ea; [destruct Hc|]. destruct Hc as [<-|[]].
        apply in_image_front. apply in_app_iff. right. change (st_areas s') with (st_areas s1 ++ [p]). rewrite Ea.
        apply In_areas_cells_snoc_next. discriminate.
    + apply in_image_front. apply in_app_iff. right. change (st_areas s') with (st_areas s1 ++ [p]). apply In_areas_cells_snoc_new. exact Hc.
  - (* [comment removed for export] *)
    intros c Hc. destruct (open_rev p s1 c Hk1 Hc) as [H|[(H1 & H2)|(a & Hne & Ea & Ec)]].
    + left. exact H.
    + right. destruct (open_rev_ctx p s1 c H1) as [H3|(El & Ew)]; [exfalso; exact (H2 H3)|].
      assert (Ecr : forall c', mc_loc c' = mc_loc c -> mc_w c' = 8%nat -> cell_range L c' = cell_range L c).
      { intros c' E1 E2. unfold cell_range. rewrite E1, E2, Ew. reflexivity. }
      assert (Kw : forall c', In c' [am_cell (padd (padd p AREA_HDR) META_SIZE); amc_cell (METAS_PER_AREA - 1); ac_cell (st_avail_meta_area_count s1 - 1);
                   head_cell (match st_area_head s1 with None => Some p | h => h end); tail_cell (Some p); ama_cell (padd p 4096);
                   MCell (LMem p) 8 VSec; MCell (LMem (padd p 16)) 4 (VZ METAS_PER_AREA)] -> In c' Cnew).
      { intros c' Hc'. apply in_app_iff. left. unfold open_cw. apply in_app_iff. left. exact Hc'. }
      destruct El as [E|[E|[E|[E|[E|E]]]]].
      * exists (am_cell (padd (padd p AREA_HDR) META_SIZE)). split; [apply Kw; cbn [In]; memb | apply Ecr; [rewrite E; reflexivity | reflexivity]].
      * exists (amc_cell (METAS_PER_AREA - 1)). split; [apply Kw; cbn [In]; memb | apply Ecr; [rewrite E; reflexivity | reflexivity]].
      * exists (ac_cell (st_avail_meta_area_count s1 - 1)). split; [apply Kw; cbn [In]; memb | apply Ecr; [rewrite E; reflexivity | reflexivity]].
      * exists (head_cell (match st_area_head s1 with None => Some p | h => h end)). split; [apply Kw; cbn [In]; memb | apply Ecr; [rewrite E; reflexivity | reflexivity]].
      * exists (tail_cell (Some p)). split; [apply Kw; cbn [In]; memb | apply Ecr; [rewrite E; reflexivity | reflexivity]].
      * exists (ama_cell (padd p 4096)). split; [apply Kw; cbn [In]; memb | apply Ecr; [rewrite E; reflexivity | reflexivity]].
    + right. subst a c. exists (anext_cell (last (st_areas s1) (SP 0%nat 0)) (Some p)). split; [|reflexivity].
      apply in_app_iff. left. unfold open_cw. apply in_app_iff. right. destruct (st_areas s1) as [|a0 t0]; [exfalso; exact (Hne eq_refl)|]. left. reflexivity.
  - (* [comment removed for export] *)
    apply Forall_app. split; [exact HNEW|].
    apply Forall_forall. intros c Hc. unfold area_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
    + cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[]]]].
      * exact (proj1 (Forall_forall _ _) HNEW (MCell (LMem p) 8 VSec) ltac:(unfold open_cw; apply in_app_iff; left; cbn [In]; memb)).
      * apply (zero_cell_holds_r L m2 _ (pa + 8) 8); [intros x Hx; apply HZ2; left; clear - Hx; lia | clear - Rpa1; lia | clear - Rpa5; lia | | | | intros z E; discriminate | reflexivity];
          cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]; try rewrite loc_padd; fold pa; clear; lia.
      * exact (proj1 (Forall_forall _ _) HNEW (MCell (LMem (padd p 16)) 4 (VZ METAS_PER_AREA)) ltac:(unfold open_cw; apply in_app_iff; left; cbn [In]; memb)).
    + apply in_flat_map in Hc as (k & Hk & Hc). apply in_seq in Hk. unfold METAS_PER_AREA in Hk. change (Z.to_nat 101) with 101%nat in Hk.
      set (q := padd p (AREA_HDR + META_SIZE * Z.of_nat k)) in Hc.
      assert (Zq : meta_slot_cells q (mlookup (st_metas s') q) = meta_slot_cells q None).
      { unfold s', s_opn. rewrite mlookup_open_take. destruct (sptr_eqb q (padd p AREA_HDR)); [reflexivity|].
        destruct (mlookup (st_metas s1) q) as [x|] eqn:E; [|reflexivity]. exfalso.
        exact (open_no_key X R U s1 p HIo q (mlookup_In_keys _ _ _ E) (Z.of_nat k) ltac:(clear - Hk; lia) eq_refl). }
      rewrite Zq in Hc. cbn [meta_slot_cells In] in Hc.
      assert (Lq : forall d, loc_addr L (LMem (padd q d)) = pa + 24 + 40 * Z.of_nat k + d).
      { intros d. unfold q. rewrite !loc_padd. fold pa. unfold AREA_HDR, META_SIZE. ring. }
      destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        (apply (zero_cell_holds_r L m2 _ (pa + 24) 4072); [intros x Hx; apply HZ2; right; clear - Hx; lia | clear - Rpa1; lia | clear - Rpa5; lia | | | | intros z E; discriminate | reflexivity]);
        cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]; try rewrite Lq; unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits; clear - Hk; lia.
  - exact HG2.
  - intros x Hx Hne. right. destruct (HWO x Hx Hne) as (c' & Hc' & Hin). exists c'. split; [apply in_app_iff; left; exact Hc' | exact Hin].
Qed.
End AMR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fp_below : forall HTOP X R U s L LIM, Inv X R U s -> rgeoA HTOP L s -> ly_ctx L = 0x97c98 -> HTOP <= LIM -> 0x98038 <= LIM ->
  forall f, In f (footprint s) -> loc_addr L (fst f) + snd f <= LIM.
Proof.
  intros HTOP X R U s L LIM HI HG Hctx HT HC f Hf. destruct (footprint_inv s f Hf) as [-> | [(a & Ha & ->) | (k & rgk & Hk & Kk & Lk & ->)]].
  - cbn [fst snd loc_addr]. rewrite Hctx. unfold CTX_SIZE. clear - HC; lia.
  - destruct (area_range HTOP X R U s L a HI HG Ha) as (r & rg & _ & Hr & Hl & _ & B1 & B2 & _).
    destruct (HG r rg Hr Hl) as (_ & _ & G3 & _). cbn [fst snd]. clear - B2 G3 HT. lia.
  - destruct (HG k rgk Hk Lk) as (_ & _ & G3 & _). cbn [fst snd loc_addr]. clear - G3 HT. lia.
Qed.

Lemma PCUT_res1 : forall HTOP L EXC s m sp0 K r rg o, PCUT HTOP L EXC s m sp0 K -> region_of s r = Some rg -> rg_kind rg <> RkMap ->
  PCUT HTOP L EXC (s_res1 s r rg o) m sp0 K.
Proof.
  intros HTOP L EXC s m sp0 K r rg o [HCS HFM Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HT HTB] Hr Hk. constructor; try assumption.
  - rewrite image_res1. exact HCS.
  - rewrite footprint_res1 by assumption. exact HFM.
Qed.

Lemma mem_after_zero_grows : forall m a n, 0 <= a < 2^64 -> 0 <= n < 2^64 -> mem_grows m (mem_after m (mkEffect (w64 0) [] [(w64 a, w64 n)])).
Proof.
  intros m a n Ha Hn x Hx. rewrite <- (wa_u x) in Hx |- *. rewrite mem_after_zero by (first [exact Ha | exact Hn | apply u64_range]).
  destruct ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n)); [discriminate | exact Hx].
Qed.

Section AMR2.
Context {fx : FPState}.

#[using="Type"] Theorem wk_open_resv : forall HTOP X R U L0 s0 m0 (regs0 : bvmap 5 word) L s m Rg rom sp0 K FORB can ra r o rg
    (Kt : Z -> itree astate (option sptr * astate)),
  CUT HTOP X R U L s m sp0 K -> GROW sp0 K L0 s0 m0 L s m -> 1152 <= K ->
  am_frame Rg m sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
    (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) ->
  getr regs0 1 = wa ra -> getr regs0 2 = wa sp0 -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rg (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  getr Rg 1 = wa 343320 -> getr Rg 9 = wa (ly_reg L r + o) -> getr Rg 10 = wa (ly_reg L r + o) ->
  getr Rg 11 = wa 4096 -> getr Rg 12 = wa 3 ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> 0 < st_avail_meta_area_count s ->
  st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  Kt 1 = IRet (Some (padd (SP r o) AREA_HDR), s_opn (SP r o) (s_res1 s r rg o)) ->
  wk SEGS FORB HTOP rom L Rg (wa 0x551cc) m (IAsk (KMprotect (SP r o)) s Kt)
     (am_qpost HTOP X R U L0 s0 m0 regs0 sp0 K ra).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L0 s0 m0 regs0 L s m Rg rom sp0 K FORB can ra r o rg Kt C GR0 HK F R1 R2 Hra RK Rg1 Rg9 Rg10 Rg11 Rg12
    Hi Hf Hc Hac Ep Hr Mpg EK1.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK' Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HCe HMP HMD].
  pose proof (inv_areas HI) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  destruct (A8 Hac) as (r' & o' & rg' & Ep' & Hr' & Hk & Hl & Ho & Hlo & Hlen & Hrw).
  rewrite Ep in Ep'. injection Ep' as <- <-. rewrite Hr in Hr'. injection Hr' as <-.
  clear A1 A2 A5 A6 A7 A8 A9 A10 Hrw.
  change (hide (ra = 0x542a0 \/ ra = 0x53ec4)) in Hra.
  set (p := SP r o) in *. set (pa := ly_reg L r + o) in *.
  assert (Epa : loc_addr L (LMem p) = pa) by reflexivity.
  destruct (HG r rg Hr Hl) as (G1 & G2 & G3 & G4). unfold ranges_disjoint in G4. cbn [fst snd] in G4.
  assert (Rpa : 4096 <= pa /\ pa mod 4096 = 0 /\ pa + 4096 <= HTOP /\ hide (pa + 4096 <= 0x10000 \/ 0x99000 <= pa)).
  { clear - G1 G2 G3 G4 Ho Hlo Hlen Hac. unfold pa, hide, PGSZ in *. split; [lia|]. split.
    - apply Z.mod_divide in G2; [|lia]. apply Z.mod_divide in Ho; [|lia]. destruct G2 as (k1 & E1). destruct Ho as (k2 & E2). rewrite E1, E2.
      replace (k1 * 4096 + k2 * 4096) with ((k1 + k2) * 4096) by ring. apply Z.mod_mul. lia.
    - split; lia. }
  destruct Rpa as (Rpa1 & Rpa2 & Rpa3 & Rpa4). clear G4.
  assert (Rpa5 : pa + 4096 <= 2^47) by (clear - Rpa3 HTB; lia).
  (* [comment removed for export] *)
  assert (STK1 : stk_ok SEGS m (wa (sp0 + -64)) 1024).
  { apply (stk_ok_mono' m (wa (sp0 + -64)) (K - 64) 1024); [|clear - HK; lia].
    replace (sp0 + -64) with (sp0 - 64) by ring. apply stk_ok_shift; [exact HSTK | clear - HK; lia | clear - HK Hsp1; lia | clear - Hsp2; lia]. }
  destruct (seg_mpw Rg Rg m rom sp0 can ra _ _ _ _ _ pa F (mf_R2 _ _ _ _ _ _ _ _ _ _ F) Rg1 Rg10 Rg11 Rg12 ltac:(clear - Rpa1 Rpa5; lia) Rpa2 STK1
      ltac:(rewrite Z.add_0_l; exact Mpg) ltac:(clear - Hsp1 HK; lia)) as (R3 & Hms3 & C17 & C10 & C11 & C12 & C2 & K3).
  set (me := mpw_store m sp0) in *.
  exists R3, (wa 0x551fc), me. split; [exact Hms3|]. split.
  { split; [exact ecall_52f24|]. exists SYS_mprotect, [pa; PGSZ; 3]. split; [reflexivity|]. split; [rewrite C17; apply u_wa_small; unfold SYS_mprotect; clear; lia|].
    cbn [args_match]. split; [exact (getr_u R3 _ pa C10 ltac:(clear - Rpa1 Rpa5; lia))|]. split; [exact (getr_u R3 _ 4096 C11 ltac:(clear; lia))|].
    split; [exact (getr_u R3 _ 3 C12 ltac:(clear; lia)) | exact I]. }
  intros eff ans L' Ho'. destruct (kout_mprotect FORB HTOP L s p eff ans L' Ho') as (-> & -> & ->).
  rewrite EK1. cbn [wk]. rewrite add4_52f24. cbn [eff_ret].
  set (m1 := mem_after me (mkEffect (w64 0) [] [(w64 (loc_addr L (LMem p)), w64 PGSZ)])).
  assert (MA : forall x, 0 <= x < 2^64 -> m1 (wa x) = if (pa <=? x) && (x <? pa + PGSZ) then Some (Z_to_bv 8 0) else me (wa x)).
  { intros x Hx. unfold m1. rewrite Epa. apply mem_after_zero; [clear - Rpa1 Rpa5; lia | clear; unfold PGSZ; lia | exact Hx]. }
  assert (ZP1 : ZP m1 pa).
  { intros x Hx. rewrite MA by (clear - Hx Rpa1 Rpa5; unfold PGSZ in *; lia).
    replace ((pa <=? x) && (x <? pa + PGSZ)) with true; [reflexivity|]. symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Hx; lia. }
  assert (OUT1 : forall x, 0 <= x < 2^64 -> ~ (pa <= x < pa + 4096) -> m1 (wa x) = me (wa x)).
  { intros x Hx Hn. rewrite MA by exact Hx. replace ((pa <=? x) && (x <? pa + PGSZ)) with false; [reflexivity|]. symmetry. apply andb_false_iff.
    unfold PGSZ. destruct (Z_le_gt_dec pa x); [right; apply Z.ltb_ge; clear - Hn l; lia | left; apply Z.leb_gt; clear - g; lia]. }
  assert (OUTe : forall x, 0 <= x < 2^64 -> ~ (sp0 - 72 <= x < sp0 - 64) -> me (wa x) = m (wa x)).
  { intros x Hx Hn. unfold me, mpw_store. rewrite MngWb.wbytes_out; [reflexivity | | exact Hx | ];
      cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite u_wa_small by (clear - Hsp1 Hsp2 HK; lia); clear - Hn Hsp1 Hsp2 HK; lia. }
  assert (GM1 : mem_grows m m1).
  { apply (mem_grows_trans m me m1 (wbytes_grows (word_to_le_bytes 8 (wa 343320)) m (wa (sp0 + -64 + -8)))). unfold m1. rewrite Epa. apply mem_after_zero_grows; [clear - Rpa1 Rpa5; lia | clear; unfold PGSZ; lia]. }
  (* [comment removed for export] *)
  assert (F1 : am_frame Rg m1 sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
                 (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20))).
  { apply (am_frame_mem Rg m); [exact F | |].
    - intros x Hx. rewrite OUT1, OUTe by (clear - Hx Rpa3 HT HK Hsp1 Hsp2; lia). reflexivity.
    - intros x Hx. rewrite OUT1, OUTe by (clear - Hx Rpa1 Rpa4 Hsp1 HK; unfold hide in *; lia). reflexivity. }
  assert (Mra : rdn SEGS m1 (wa (sp0 + -64 + -8)) 8 = Some (word_to_le_bytes 8 (wa 343320))).
  { rewrite (rdn_frame_n me m1 (sp0 + -64 + -8) 8) by (first [clear - Hsp1 Hsp2 HK; lia | (intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply OUT1; clear - Hx Rpa3 HT HK Hsp1 Hsp2; lia)]).
    unfold me, mpw_store. apply rdn_wbytes_hit8. rewrite u_wa_small by (clear - Hsp1 Hsp2 HK; lia). clear - Hsp2; lia. }
  set (R3' := regupd R3 10 (w64 0)).
  assert (R3'2 : getr R3' 2 = wa (sp0 + -64 + -16)) by (unfold R3'; rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact C2).
  assert (R3'10 : getr R3' 10 = wa 0) by (unfold R3'; rewrite getr_same by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); reflexivity).
  assert (K3' : forall k, In k [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3' (Z_to_bv 5 (Z.of_nat k)) = getr Rg (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. unfold R3'. rewrite getr_other; [apply K3; clear - Hk'; klist Hk'|]. clear - Hk'. cbn [In] in Hk'.
    repeat (destruct Hk' as [<-|Hk']; [intros E; apply (f_equal bv_unsigned) in E; cbv in E; discriminate E|]). destruct Hk'. }
  assert (R3'18 : getr R3' 18 = wa 621568) by (regk K3' 18%nat; exact (mf_R18 _ _ _ _ _ _ _ _ _ _ F)).
  assert (R3'19 : getr R3' 19 = wa 621712) by (regk K3' 19%nat; exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F)).
  destruct (seg_ams Rg R3' m1 rom sp0 can ra _ _ _ _ _ F1 R3'2 R3'10 R3'18 R3'19 Mra ltac:(clear - Hsp1 HK; lia)) as (R4 & Hms4 & F4 & K4).
  (* [comment removed for export] *)
  set (s1 := s_res1 s r rg o) in *.
  assert (Eap1 : st_avail_meta_areas s1 = p) by exact Ep.
  assert (HG1 : rgeoA HTOP L s1) by exact (rgeoA_res1 HTOP L s r rg o Hr HG).
  assert (HD1 : rdisj L s1) by exact (rdisj_res1 L s r rg o Hr HD).
  assert (Hkm : rg_kind rg <> RkMap) by (rewrite Hk; discriminate).
  assert (HIo : Inv X R U (open_st (st_avail_meta_areas s1) s1)) by (rewrite Eap1; exact (Inv_open_resv X R U s r o rg HI Hac Hc Hi Ep Hr)).
  assert (FR : forall f, In f (footprint s) -> ranges_disjoint (pa, PGSZ) (crange L f)).
  { intros f Hf0. rewrite <- (footprint_res1 s r rg o Hr Hkm) in Hf0. rewrite Eap1 in HIo.
    exact (open_page_fresh HTOP X R U s1 L p HTB HIo Hctx HG1 HD1 f Hf0). }
  assert (FB : forall f, In f (footprint s) -> loc_addr L (fst f) + snd f <= sp0 - K).
  { intros f Hf0. exact (fp_below HTOP X R U s L (sp0 - K) HI HG Hctx HT ltac:(clear - Hsp1; lia) f Hf0). }
  assert (CHGX : forall x, 0 <= x < 2^64 -> m1 (wa x) <> m (wa x) -> (pa <= x < pa + 4096) \/ (sp0 - 72 <= x < sp0 - 64)).
  { intros x Hx Hne. destruct (decide (pa <= x < pa + 4096)) as [Hp|Hp]; [left; exact Hp|]. right.
    destruct (decide (sp0 - 72 <= x < sp0 - 64)) as [Hq|Hq]; [exact Hq|]. exfalso. apply Hne. rewrite OUT1, OUTe by assumption. reflexivity. }
  assert (P1 : PCUT HTOP L OEXC s1 m1 sp0 K).
  { apply (PCUT_mono HTOP L []); [| intros l []].
    apply PCUT_res1; [| exact Hr | exact Hkm].
    apply (PCUT_frame HTOP L [] s m m1 sp0 K (PCUT_of_CUT HTOP X R U L s m sp0 K C) GM1).
    - intros x Hx Hne. destruct (CHGX x Hx Hne) as [Hp|Hq]; split.
      + intros f Hf0 Hin. pose proof (FR f Hf0) as D. unfold ranges_disjoint, crange, in_rng in *. cbn [fst snd] in *. unfold PGSZ in *. clear - D Hin Hp. lia.
      + clear - Hp Rpa1 Rpa4. unfold hide in *. lia.
      + intros f Hf0 Hin. pose proof (FB f Hf0) as D. unfold crange, in_rng in *. cbn [fst snd] in *. clear - D Hin Hq HK. lia.
      + clear - Hq Hsp1 HK. lia.
    - intros c Hc0. exact (image_in_footprint_X X R U s L c HI (XNU_of_XNM X s HX) (layout_of_geo HTOP HTB X R U s L HI Hctx HG HD) Hc0). }
  assert (ZP1' : ZP m1 (loc_addr L (LMem (st_avail_meta_areas s1)))) by (rewrite Eap1, Epa; exact ZP1).
  assert (R49 : getr R4 9 = wa (loc_addr L (LMem (st_avail_meta_areas s1)))).
  { rewrite Eap1, Epa. regk K4 9%nat. regk K3' 9%nat. exact Rg9. }
  destruct (open_tail HTOP X R U L s1 m1 R4 rom sp0 K can ra _ _ _ _ _ P1 HK HIo HX HG1 HD1 Hi Hac A3 A4 ZP1' F4 R49 Hra)
    as (R5 & m2 & Hms5 & Q1 & Q2 & Q8 & Q9 & Q10 & Q18 & Q19 & Q20 & QK & CC & GG).
  rewrite Eap1 in Q10, CC, GG.
  exists R5, (wa ra), m2. split; [exact (msteps_trans SEGS _ _ _ Hms4 Hms5)|].
  exists (padd p AREA_HDR), (s_opn p s1). split; [reflexivity|]. split; [reflexivity|]. split; [exact Q10|].
  split.
  { assert (KK : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R5 (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))).
    { intros k Hk'. rewrite (QK k Hk'), (K4 k ltac:(clear - Hk'; klist Hk')), (K3' k ltac:(clear - Hk'; klist Hk')). exact (RK k Hk'). }
    intros k Hk'. cbn [In] in Hk'.
    destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]].
    - litr2 Q1. exact (eq_sym R1).
    - litr2 Q2. exact (eq_sym R2).
    - apply KK. cbn [In]. memb.
    - apply KK. cbn [In]. memb.
    - litr2 Q8. apply wa_u.
    - litr2 Q9. apply wa_u.
    - litr2 Q18. apply wa_u.
    - litr2 Q19. apply wa_u.
    - litr2 Q20. apply wa_u.
    - apply KK. cbn [In]. memb.
    - apply KK. cbn [In]. memb.
    - apply KK. cbn [In]. memb.
    - apply KK. cbn [In]. memb.
    - apply KK. cbn [In]. memb.
    - apply KK. cbn [In]. memb.
    - apply KK. cbn [In]. memb. }
  split; [exact CC|].
  refine (GROW_trans sp0 K L0 s0 m0 L s m L (s_opn p s1) m2 GR0 (GROW_trans sp0 K L s m L s1 m1 L (s_opn p s1) m2 _ GG)).
  split; [apply lext_refl|]. split; [exact (RMONO_res1 s r rg o Hr)|].
  split; [intros c Hc0; exists c; split; [unfold s1; rewrite image_res1; exact Hc0 | reflexivity]|].
  split.
  { intros x Hx Hnc. destruct (decide (m1 (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
    destruct (CHGX x ltac:(clear - Hx; lia) E) as [Hp|Hq]; [clear - Hp Hx Rpa1 Rpa4; unfold hide in *; lia | clear - Hq Hx Hsp1 HK; lia]. }
  intros x Hx Hne. destruct (CHGX x Hx Hne) as [Hp|Hq].
  - right. right. right. exists r, (rw_page rg o). split; [unfold s1; rewrite (region_of_res1 s r rg o r Hr), Nat.eqb_refl; reflexivity|].
    split; [exact Hl|]. split; [cbn [rw_page rg_kind]; exact Hkm|]. cbn [rw_page rg_len]. clear - Hp Hlen Ho Hlo Hac. unfold pa, PGSZ in *. lia.
  - left. clear - Hq HK. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem am_openres_wk : forall HTOP X R U L s m regs rom sp0 K ra FORB,
  CUT HTOP X R U L s m sp0 K -> 1152 <= K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> 0 < st_avail_meta_area_count s ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  wk SEGS FORB HTOP rom L regs (wa 0x53a60) m (alloc_meta s) (am_qpost HTOP X R U L s m regs sp0 K ra).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L s m regs rom sp0 K ra FORB C HK R2 R1 Hra Hi Hf Hc Hac Mpg.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK' Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HCe HMP HMD].
  pose proof (inv_areas HI) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  destruct (A8 Hac) as (r & o & rg & Ep & Hr & Hk & Hl & Ho & Hlo & Hlen & Hrw).
  clear A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 Hrw.
  destruct (alloc_meta_openres s r o rg Hi Hf Hc Hac Ep Hr) as (Kt & Et & EK1). rewrite Et.
  change (hide (ra = 0x542a0 \/ ra = 0x53ec4)) in Hra.
  set (pa := ly_reg L r + o).
  set (ac := st_avail_meta_area_count s) in *.
  destruct (HG r rg Hr Hl) as (G1 & G2 & G3 & G4). unfold ranges_disjoint in G4. cbn [fst snd] in G4.
  assert (Rpa : 4096 <= pa /\ pa mod 4096 = 0 /\ pa + 4096 <= 2^47 /\ 1 <= ac <= 2^60).
  { clear - G1 G2 G3 Ho Hlo Hlen Hac HTB. unfold pa, PGSZ in *. split; [lia|]. split.
    - apply Z.mod_divide in G2; [|lia]. apply Z.mod_divide in Ho; [|lia]. destruct G2 as (k1 & E1). destruct Ho as (k2 & E2). rewrite E1, E2.
      replace (k1 * 4096 + k2 * 4096) with ((k1 + k2) * 4096) by ring. apply Z.mod_mul. lia.
    - split; lia. }
  destruct Rpa as (Rpa1 & Rpa2 & Rpa5 & Rac). clear G4.
  (* [comment removed for export] *)
  destruct (seg_amp L s m regs rom sp0 K N R2) as (R1' & can & Hms1 & F1 & K1 & MOUT1 & GR1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (C1 : CUT HTOP X R U L s m1 sp0 K) by (apply (CUT_stack HTOP X R U L s m m1 sp0 K C GR1); intros x Hx Hn; apply MOUT1; [exact Hx | clear - Hn HK; lia]).
  assert (Mpg1 : rdn SEGS m1 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m1 621648 8) by (first [clear; lia | (intros x Hx; cbn in Hx; apply MOUT1; clear - Hx Hsp1 HK; lia)]). exact Mpg. }
  destruct (seg_amq HTOP X R U L s m1 R1' rom sp0 K sp0 can _ _ _ _ _ _ F1 C1 Hi Hf Hc Mpg1) as (R2' & Hms2 & B8 & F2 & K2).
  assert (Mac : rdn SEGS m1 (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa ac))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta_area_count) 8 (VZ ac)) (ct_nc _ _ _ _ _ _ _ _ _ C1) ltac:(in_ctx13)
      ltac:(intros z E; discriminate) ltac:(apply Nat.leb_le; reflexivity)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. exact H. }
  assert (Mar : rdn SEGS m1 (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa pa))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta_areas) 8
        (if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0) then VZ 0 else VP (st_avail_meta_areas s)))
        (ct_nc _ _ _ _ _ _ _ _ _ C1) ltac:(in_ctx13) ltac:(intros z E; destruct ((match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0)); discriminate)
        ltac:(apply Nat.leb_le; reflexivity)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. fold ac in H.
    replace ((match st_areas s with [] => true | _ => false end) && (ac =? 0)) with false in H
      by (replace (ac =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Hac; lia); destruct (st_areas s); reflexivity).
    cbn [sval_num] in H. rewrite Ep in H. exact H. }
  destruct (seg_amr0 R2' m1 rom sp0 can _ _ _ _ _ _ ac pa F2 B8 Rac Mac ltac:(clear - Rpa1 Rpa5; lia) Rpa2 Mar)
    as (R3 & Hms3 & D1 & D9 & D10 & D11 & D12 & F3 & K3).
  eapply wk_msteps; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms3))|].
  (* [comment removed for export] *)
  assert (Era : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; clear - Hra; unfold hide in Hra; lia).
  rewrite Era in F3.
  assert (GR1' : GROW sp0 K L s m L s m1).
  { apply GROW_stack; [|clear - Hsp1; lia]. intros x Hx Hne. destruct (decide (sp0 - 56 <= x < sp0)) as [H|H]; [clear - H HK; lia|].
    exfalso. exact (Hne (MOUT1 x Hx H)). }
  assert (RK : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. rewrite (K3 k ltac:(clear - Hk'; klist Hk')), (K2 k ltac:(clear - Hk'; klist Hk')), (K1 k ltac:(clear - Hk'; klist Hk')). reflexivity. }
  exact (wk_open_resv HTOP X R U L s m regs L s m1 R3 rom sp0 K FORB can ra r o rg Kt C1 GR1' HK F3 R1 R2 Hra RK D1 D9 D10 D11 D12
           Hi Hf Hc Hac Ep Hr Mpg1 EK1).
Qed.
End AMR2.

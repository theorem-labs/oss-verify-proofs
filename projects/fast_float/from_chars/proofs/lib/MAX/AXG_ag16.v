(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfArith MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngMW3 MngNtfPre MngNtfC MngCtx MngCtx2 MngShape MngTake MngTakeX MngOwn AXG_as1 AXG_as5 AXG_am1 AXG_amr0 AXG_amr AXG_am8 AXG_ag0 AXG_ag1 AXG_ag7 AXG_ag8 AXG_ag10 AXG_ag11 AXG_ag12 AXG_ag13 AXG_asq AXG_ag14 AXG_ag15.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTake OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngTakeX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngOwn OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am8 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag7 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag8 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag10 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag11 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag12 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag13 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_asq OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag14 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag15.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma GROWX_above : forall UB0 HTOP X R U L s m L' s' m' sp0 K, GROWX UB0 sp0 K L s m L' s' m' -> CUT HTOP X R U L' s' m' sp0 K ->
  forall x, sp0 <= x < 2^64 -> m' (wa x) = m (wa x).
Proof.
  intros UB0 HTOP X R U L s m L' s' m' sp0 K (_ & _ & _ & _ & CH) C x Hx.
  pose proof C as [_ _ N HG _ HT _]. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  destruct (decide (m' (wa x) = m (wa x))) as [E|E]; [exact E|]. exfalso.
  assert (Hx' : 0 <= x < 2^64) by (pose proof (nc_sp1 _ _ _ _ _ _ _ N); lia).
  destruct (CH x Hx' E) as [[A|[(c & Hc & Hin)|[(r & rg & Hr & Hl & _ & Hrx)|(r & rg & Hr & Hl & _ & Hrx)]]] | ((r & rg & Hr & Hl & _ & Hrx) & _)].
  - lia.
  - pose proof (nc_cells _ _ _ _ _ _ _ N c Hc) as (_ & P2 & _). unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia.
  - destruct (HG r rg Hr Hl) as (_ & _ & G3 & _). lia.
  - destruct (HG r rg Hr Hl) as (_ & _ & G3 & _). lia.
  - destruct (HG r rg Hr Hl) as (_ & _ & G3 & _). lia.
Qed.

Section AG16.
Context {fx : FPState}.
Variable FORB : list (Z * Z).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x87000).

#[using="Type"] Theorem ag_nest_wk : forall f UB0 HTOP X U L s2 m2 (R : bvmap 5 word) rom sp0 K sc req mt can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9,
  as_wk_f FORB f ->
  CUT HTOP (mt :: X) None U L s2 m2 sp0 K -> markers_hold L s2 (bview SEGS m2) -> KAS sc <= K ->
  as_frame R m2 sp0 sc req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 ->
  getr R 10 = wa (loc_addr L (LMem mt)) -> getr R 19 = wa (2 * sc) -> getr R 24 = wa (znth sc size_classes) -> getr R 25 = wa 98984 ->
  rdn SEGS m2 (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) -> TABS m2 -> DBT m2 ->
  (forall c, 0 <= c < 48 -> usage_of s2 c < 2^40) ->
  active_hd s2 sc = None -> (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s2 sc) + UNIT) = false ->
  (need sc <= S (S f))%nat ->
  PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 -> ly_brk0 L <= HTOP -> st_init_done s2 = true ->
  (forall x, UB0 x -> in_user_block L s2 x) -> ~ In mt X ->
  wk SEGS FORB HTOP rom L R (wa 0x524e8) m2 (AGC f sc req mt s2)
    (ag_npost UB0 HTOP X U L s2 m2 R sp0 K sc mt ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f UB0 HTOP X U L s2 m2 R rom sp0 K sc req mt can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9
    IH C2 MK2 HKAS F R10 R19 R24 R25 Mpg TB Mdb UB Hhd Hbr Hf B1 B2 B3 Hinit UBI NX.
  pose proof C2 as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (nc_sp3 _ _ _ _ _ _ _ N) as Hsp3. pose proof (nc_stk _ _ _ _ _ _ _ N) as HSTK. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  pose proof (nc_env _ _ _ _ _ _ _ N) as HENV.
  pose proof F as [A2 A8 A18 A20 A21 A22 A23 Hsp Asp Hsc Hreq Hcan Hra Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9
                   Fra Fs0 Fs1 Fs2 Fs3 Fs4 Fs5 Fs6 Fs7 Fs8 Fs9 Fcan Fgd].
  assert (Hsc' : 0 <= sc < 48) by (clear - Hsc; lia).
  pose proof (size_classes_range sc Hsc') as Hun. pose proof (class_units sc) as Ecs.
  assert (Hsize : 16 <= class_size sc <= 131056) by (rewrite Ecs; clear - Hun; lia).
  pose proof (need_ge2 sc) as Hneed2.
  assert (HK144 : 1440 <= K - 144) by (unfold KAS in HKAS; clear - HKAS Hneed2; lia).
  (* [comment removed for export] *)
  pose proof (inv_ctx HI) as (C1 & C2' & C3' & C4' & C5 & C6 & C7 & C8 & C9 & _).
  set (u0 := usage_of s2 sc) in *. set (cnt0 := initial_cnt sc u0) in *.
  assert (Hu0 : 0 <= u0 <= 2^60).
  { pose proof (UB sc Hsc') as H. unfold u0, usage_of, znth in *.
    destruct (nth_in_or_default (Z.to_nat sc) (st_usage s2) 0) as [E|E]; [pose proof (C5 _ E); clear - H H0; lia | rewrite E; lia]. }
  pose proof (initial_cnt_facts sc u0 Hsc') as (Hc0 & Hc0s & Hc026). fold cnt0 in Hc0, Hc0s, Hc026.
  assert (Hbr' : class_size sc * cnt0 + UNIT <= PGSZ / 2) by (apply Z.ltb_ge in Hbr; exact Hbr).
  pose proof (nested_facts sc cnt0 Hsc' ltac:(clear - Hc0; lia) Hc026 Hbr') as NF. cbv zeta in NF.
  destruct NF as (H23 & Hc2 & Htot & Hj & Hj48 & Hjfit & Hjlt).
  set (total := UNIT + cnt0 * class_size sc - IB) in *. set (j := size_to_class total) in *.
  pose proof (need_nested sc j H23 ltac:(clear - Hj; lia)) as Hnn.
  unfold AGC. rewrite (ag_nested_tree f sc req mt s2 Hbr). fold u0 cnt0. change (ag_total s2 sc) with total. change (ag_j s2 sc) with j.
  change (ag_cnt0 s2 sc) with cnt0.
  apply wk_ibind. apply wk_ibind.
  (* [comment removed for export] *)
  set (mta := loc_addr L (LMem mt)).
  assert (Lc : forall o, loc_addr L (LCtx o) = 614104 + o) by (intros o; cbn [loc_addr]; rewrite Hctx; reflexivity).
  assert (Musg : rdn SEGS m2 (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa u0))).
  { pose proof (nc_ctx_rd L s2 m2 sp0 K _ N (usage_in_ctx s2 (Z.to_nat sc) ltac:(clear - Hsc; lia)) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_usage in H. rewrite Z2Nat.id in H by lia.
    replace (614104 + (464 + 8 * sc)) with (8 * sc + 614568) in H by ring. exact H. }
  assert (Hmt0 : MT s2 mt = Some MRaw \/ MT s2 mt = Some (MFree None None)) by exact (HX mt (or_introl eq_refl)).
  assert (Hkey : In mt (keys s2)) by (destruct Hmt0 as [E'|E']; exact (MT_keys s2 mt _ E')).
  pose proof (nc_mplace _ _ _ _ _ _ _ N mt Hkey) as (Pm1 & Pm2 & Pm3 & Pm4). fold mta in Pm1, Pm2, Pm3, Pm4.
  assert (Hmta : 1 <= mta <= 2^63-1) by (clear - Pm1 Pm2 Hsp2 HK1; lia).
  destruct (seg_agc R m2 rom sc mta u0 A8 R10 R19 A23 R24 R25 Hsc Hmta Hu0 Musg Mpg TB)
    as (R1 & Hms1 & B8 & B9 & B10 & B11 & B19 & B24 & B23 & B25 & B12 & B14 & BK).
  fold cnt0 in Hms1, B19, B14. rewrite Hbr in Hms1.
  (* [comment removed for export] *)
  assert (Hsz0 : 16 <= class_size sc * cnt0 <= 2032) by (clear - Hbr' Hsize Hc0; unfold PGSZ, UNIT in *; nia).
  assert (A16 : (class_size sc * cnt0) mod 16 = 0).
  { rewrite Ecs. replace (16 * znth sc size_classes * cnt0) with ((znth sc size_classes * cnt0) * 16) by ring. apply Z_mod_mult. }
  destruct (seg_npre R1 m2 rom (class_size sc * cnt0) B14 B25 Hsz0 A16 (proj1 (proj2 HENV)) Mdb) as (R2 & Hms2 & Q1 & Q10 & Q11 & Q18 & QK).
  assert (Etot : class_size sc * cnt0 + 12 = total) by (unfold total, UNIT, IB; ring).
  rewrite Etot in Q10, Q11, Q18. fold j in Q10, Q18.
  apply (wk_msteps SEGS FORB HTOP rom _ L R2 (wa 0x522f0) m2 R (wa 0x524e8) m2 _ (msteps_trans SEGS _ _ _ Hms1 Hms2)).
  (* [comment removed for export] *)
  assert (C2s : CUT HTOP (mt :: X) None U L s2 m2 (sp0 - 144) (K - 144)) by (apply CUT_shift; [exact C2 | lia | reflexivity | lia]).
  assert (R2sp : getr R2 2 = wa (sp0 - 144)) by (regk QK 2%nat; regk BK 2%nat; litr2 A2; f_equal; ring).
  eapply wk_mono; [| apply (IH UB0 HTOP (mt :: X) U L s2 m2 R2 rom (sp0 - 144) (K - 144) j total C2s MK2
      ltac:(unfold KAS in *; clear - HKAS Hnn; lia) Hj48 ltac:(clear - Htot; lia) Hjfit ltac:(clear - Hnn Hf; lia)
      R2sp Q10 Q11 UB Mdb TB Mpg B1 B2 B3 (or_introl Hinit) UBI)].
  intros L4 r R4 pc4 m4 Q.
  destruct Q as (idx & s4 & g & amg & -> & -> & A10 & AK & C4s & G4 & MK4 & Hhd4 & U4 & Sc4 & Fit4 & Hidx & HB4 & UB4 & UG4).
  (* [comment removed for export] *)
  assert (ABOVE : forall x, sp0 - 144 <= x < 2^64 -> m4 (wa x) = m2 (wa x))
    by exact (GROWX_above UB0 HTOP (mt :: X) (Some (g, idx)) U L s2 m2 L4 s4 m4 (sp0 - 144) (K - 144) G4 C4s).
  assert (STK4 : stk_ok SEGS m4 (wa sp0) K).
  { pose proof C4s as [_ _ N4 _ _ _ _].
    apply (stk_ok_join m2 m4 sp0 K 144); [exact (nc_stk _ _ _ _ _ _ _ N4) | exact HSTK | intros x Hx; apply ABOVE; lia | lia | lia]. }
  assert (C4 : CUT HTOP (mt :: X) (Some (g, idx)) U L4 s4 m4 sp0 K) by exact (CUT_unshift HTOP (mt :: X) (Some (g, idx)) U L4 s4 m4 sp0 K 144 C4s ltac:(lia) STK4 Hsp2 Hsp3).
  assert (G4' : GROWX UB0 sp0 K L s2 m2 L4 s4 m4) by exact (GROWX_unshift UB0 sp0 K 144 L s2 m2 L4 s4 m4 G4 ltac:(lia)).
  pose proof G4' as (HE4 & RM4 & _ & SI4 & _).
  pose proof C4 as [HI4 HX4 N4 HG4 HD4 HT4 HTB4].
  pose proof (inv_groups HI4 g amg U4) as G. pose proof G as (_ & _ & _ & Gcl & _).
  assert (Hstr : stride_of amg = class_size j).
  { destruct Gcl as [(C63 & _) | (_ & _ & C26 & _)]; [clear - C63 Sc4 Hj48; lia|]. specialize (C26 ltac:(clear - Sc4 Hj; lia)).
    unfold stride_of. rewrite Sc4. destruct C26 as [C|C]; [rewrite C|].
    - destruct (am_last amg =? 0); reflexivity.
    - destruct (am_last amg =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
  assert (Hhsc4 : active_hd s4 sc = None) by (rewrite (HB4 sc ltac:(clear - Hsc Hj; lia)); exact Hhd).
  pose proof (usedX_MT _ _ _ _ U4) as [Mg _].
  cbv beta iota. rewrite (AGN_eq sc mt cnt0 j idx s4 g amg ltac:(lia) Hhd4 Mg Hstr ltac:(lia) Hhsc4).
  apply wk_ret. cbv beta iota. unfold ret. cbn [wk].
  (* [comment removed for export] *)
  destruct UG4 as (UA4 & UB4').
  assert (Eus4 : usage_of s4 sc = u0) by exact (UA4 sc ltac:(clear - Hsc Hj; lia)).
  assert (F4 : as_frame R m4 sp0 sc req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9).
  { apply (as_frame_mem R m2); [exact F | |]; intros x Hx; [apply ABOVE; clear - Hx Hsp2; lia|].
    apply SI4; clear - Hx; lia. }
  assert (Emta : loc_addr L4 (LMem mt) = mta) by exact (loc_addr_ext s2 L L4 HE4 (LMem mt) (key_lt (mt :: X) None U s2 HI mt Hkey)).
  destruct (seg_nest HTOP X U L4 s4 m4 rom sp0 K mt g amg idx j sc cnt0 R4 R req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9
              C4 U4 Sc4 Hhd4 Hhsc4 ltac:(clear - H23 Hsc; lia) Hj ltac:(clear - Hc0 Hc2; lia) ltac:(unfold total, UNIT, IB in Hjfit; clear - Hjfit; lia) ltac:(clear - Hsz0; lia)
              ltac:(rewrite Eus4; clear - Hu0; lia) F4
              ltac:(regk AK 1%nat; exact Q1) ltac:(regk AK 2%nat; litr2 R2sp; f_equal; ring)
              ltac:(regk AK 8%nat; regk QK 8%nat; exact B8) ltac:(regk AK 9%nat; regk QK 9%nat; rewrite Emta; exact B9) A10
              ltac:(regk AK 18%nat; exact Q18) ltac:(regk AK 19%nat; regk QK 19%nat; exact B19)
              ltac:(regk AK 20%nat; regk QK 20%nat; regk BK 20%nat; exact A20) ltac:(regk AK 21%nat; regk QK 21%nat; regk BK 21%nat; exact A21)
              ltac:(regk AK 22%nat; regk QK 22%nat; regk BK 22%nat; exact A22) ltac:(regk AK 23%nat; regk QK 23%nat; exact B23)
              ltac:(regk AK 24%nat; regk QK 24%nat; exact B24) ltac:(regk AK 25%nat; regk QK 25%nat; exact B25))
    as (R6 & hb & Hhb & Hms6 & S1 & S2 & S8 & S9 & S10 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & SK).
  rewrite Emta in Hms6.
  eexists R6, (wa 0x52b8c), _. split; [exact Hms6|].
  unfold ag_npost. exists (ag_nest_st mt sc cnt0 g amg idx j s4). split; [reflexivity|]. split; [reflexivity|].
  do 13 (split; [assumption|]).
  split.
  { intros k Hk. rewrite (SK k Hk). rewrite (AK k ltac:(clear - Hk; klist Hk)). rewrite (QK k ltac:(clear - Hk; klist Hk)). exact (BK k ltac:(clear - Hk; klist Hk)). }
  rewrite <- Emta.
  assert (ND4 : List.NoDup (keys s4)) by exact (proj1 (inv_keys HI4)).
  assert (XU2 : XNU (mt :: X) s2) by exact (XNU_of_XNM (mt :: X) s2 HX).
  assert (UBI4 : forall x, UB0 x -> in_user_block L4 s4 x) by (intros x Hx; exact (in_user_block_ext (mt :: X) None U s2 s4 L L4 x HI XU2 HE4 UB4 ND4 (UBI x Hx))).
  assert (Hsz' : class_size sc <= 2032) by (clear - Hsz0 Hc0; nia).
  assert (Hfit16 : 16 + class_size sc * cnt0 <= class_size j) by (unfold total, UNIT, IB in Hjfit; clear - Hjfit; lia).
  split.
  { intros HI6. destruct (cut_nest UB0 HTOP X U L4 s4 m4 sp0 K mt g amg sc cnt0 idx j hb C4 MK4 U4 Hstr ltac:(clear - Hsc; lia)
                            ltac:(clear - Hc0; lia) Hfit16 Hsz' NX Hhb UBI4 HI6) as (CC & GG).
    split; [exact CC | exact (GROWX_trans UB0 sp0 K L s2 m2 L4 s4 m4 L4 _ _ G4' GG)]. }
  split; [exact (markers_nest HTOP X U L4 s4 m4 sp0 K mt g amg sc cnt0 idx j hb C4 MK4 U4 Hstr ltac:(clear - Hsc; lia)
                                ltac:(clear - Hc0; lia) Hfit16 Hsz')|].
  pose proof (inv_ctx HI4) as (L1 & L2 & _).
  split.
  { unfold active_hd, ag_nest_st, ins_st. cbn [st_active set_active set_metas set_usage ef_grp_st]. apply nth_lupd_same. rewrite L1. clear - Hsc; lia. }
  assert (EU6 : forall c, 0 <= c -> usage_of (ag_nest_st mt sc cnt0 g amg idx j s4) c = if c =? sc then usage_of s4 sc + cnt0 else usage_of s4 c).
  { intros c Hc. unfold usage_of at 1, znth, ag_nest_st, ins_st. cbn [st_usage set_active set_metas set_usage ef_grp_st]. unfold zset.
    destruct (c =? sc) eqn:E.
    - apply Z.eqb_eq in E. subst c. rewrite nth_zupd_same by (rewrite L2; clear - Hsc; lia). reflexivity.
    - apply Z.eqb_neq in E. rewrite nth_zupd_other by (clear - E Hc Hsc; lia). reflexivity. }
  split.
  - intros c Hc. rewrite EU6 by lia. replace (c =? sc) with false by (symmetry; apply Z.eqb_neq; lia). apply UA4. clear - Hc Hj; lia.
  - intros c Hc. rewrite EU6 by lia. destruct (c =? sc) eqn:E.
    + apply Z.eqb_eq in E. subst c. rewrite Eus4. clear - Hc0. unfold u0. lia.
    + exact (UB4' c Hc).
Qed.
End AG16.

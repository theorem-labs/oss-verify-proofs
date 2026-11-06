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
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfArith OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfM MngNtfS MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngNtfPre MngNtfC MngCtx MngCtx2 MngShape AXG_as1 AXG_am1 AXG_am3 AXG_am7 AXG_amr AXG_ag0 AXG_ag1 AXG_ag2 AXG_ag3 AXG_ag3p AXG_ag4 AXG_ag5 AXG_ag6.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShape OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am7 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag3p OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag4 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma kout_mmap_rw : forall FORB HTOP L s len eff ans L', koutcome FORB HTOP L s (KMmapRW len) eff ans L' ->
  exists a, fresh_range FORB HTOP L s a (page_round len) /\ eff = mkEffect (w64 a) [] [(w64 a, w64 (page_round len))] /\ ans = 1 /\
    L' = set_reg_addr L (length (st_regions s)) a.
Proof. intros FORB HTOP L s len eff ans L' H. inversion H; subst. exists a. auto. Qed.

(* [comment removed for export] *)
Lemma mm_plan_eq : forall s sc req, 0 <= sc <= 47 ->
  mm_plan sc (ag_cnt0 s sc) (usage_of s sc) (usage_of s (sc + 1)) (znth (sc - 7) (st_bounces s)) req = ag_plan s sc req.
Proof.
  intros s sc req Hsc. unfold mm_plan, ag_plan, mmap_plan, ag_cnt0, ua_u, ab_ns, rd_cnt, iv_plan, is_bouncing, bounce_idx, ab_tr.
  replace (req + IB + UNIT) with (req + 20) by (unfold IB, UNIT; ring).
  destruct ((7 <=? sc) && (sc <? 39)).
  - destruct (znth (sc - 7) (st_bounces s) <? 100) eqn:E.
    + apply Z.ltb_lt in E. replace (100 <=? znth (sc - 7) (st_bounces s)) with false by (symmetry; apply Z.leb_gt; exact E). reflexivity.
    + apply Z.ltb_ge in E. replace (100 <=? znth (sc - 7) (st_bounces s)) with true by (symmetry; apply Z.leb_le; exact E). reflexivity.
  - reflexivity.
Qed.

Lemma mem_after_zero_grows' : forall m r a n, 0 <= a < 2^64 -> 0 <= n < 2^64 -> mem_grows m (mem_after m (mkEffect r [] [(w64 a, w64 n)])).
Proof.
  intros m r a n Ha Hn x Hx. rewrite <- (wa_u x) in Hx |- *. rewrite mem_after_zero by (first [exact Ha | exact Hn | apply u64_range]).
  destruct ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n)); [discriminate | exact Hx].
Qed.

(* [comment removed for export] *)
Definition AGC (f : nat) (sc req : Z) (mt : sptr) (s2 : astate) : itree astate (Z * astate) :=
  ibind (AGK f sc req (Some mt) s2) (fun r => match r with (og, s') => (match og with None => ret (-1) | Some _ => ret 0 end) s' end).

Ltac side7 := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

(* [comment removed for export] *)
Lemma rdn_read : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  (forall k, (k < length bs)%nat -> m (wa (a + Z.of_nat k)) = Some (nth k bs (Z_to_bv 8 0))) -> rdn SEGS m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H0 H1 HB. destruct bs as [|b0 bs']; [reflexivity|].
  rewrite (rdn_frame_n (wbytes m (wa a) (b0 :: bs')) m a (length (b0 :: bs')) H0 H1).
  - apply rdn_wbytes_hit. rewrite u_wa_small by (cbn [length] in *; lia). exact H1.
  - intros x Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite HB by lia.
    rewrite MngWb.wbytes_at_wa by lia. reflexivity.
Qed.

Lemma rdn_read8 : forall m a v, 0 <= a -> a + 8 <= 2^64 ->
  (forall k, (k < 8)%nat -> m (wa (a + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa v)) (Z_to_bv 8 0))) ->
  rdn SEGS m (wa a) 8 = Some (word_to_le_bytes 8 (wa v)).
Proof.
  intros m a v H0 H1 HB. pose proof (rdn_read m a (word_to_le_bytes 8 (wa v)) H0) as H. rewrite length_N_to_le_bytes in H. apply H; [exact H1|].
  intros k Hk. apply HB. exact Hk.
Qed.

Lemma mmw_reads : forall m spm sc mt len s4 s5, 2^20 <= spm <= 2^47 ->
  rdn SEGS (mmw_frame m spm sc mt len s4 s5) (wa (spm + -8)) 8 = Some (word_to_le_bytes 8 (wa 338336)) /\
  rdn SEGS (mmw_frame m spm sc mt len s4 s5) (wa (spm + -16)) 8 = Some (word_to_le_bytes 8 (wa sc)) /\
  rdn SEGS (mmw_frame m spm sc mt len s4 s5) (wa (spm + -24)) 8 = Some (word_to_le_bytes 8 (wa mt)) /\
  rdn SEGS (mmw_frame m spm sc mt len s4 s5) (wa (spm + -32)) 8 = Some (word_to_le_bytes 8 (wa 18446744073709551615)) /\
  rdn SEGS (mmw_frame m spm sc mt len s4 s5) (wa (spm + -40)) 8 = Some (word_to_le_bytes 8 (wa len)) /\
  rdn SEGS (mmw_frame m spm sc mt len s4 s5) (wa (spm + -48)) 8 = Some (word_to_le_bytes 8 (wa s4)) /\
  rdn SEGS (mmw_frame m spm sc mt len s4 s5) (wa (spm + -56)) 8 = Some (word_to_le_bytes 8 (wa s5)).
Proof.
  intros m spm sc mt len s4 s5 Hs. unfold mmw_frame.
  split; [|split; [|split; [|split; [|split; [|split]]]]];
    (apply rdn_read8; [lia | lia |]); intros k Hk; rewrite ?MngWb.wbytes_out by (clear - Hk Hs; side7);
    (apply MngWb.wbytes_at_wa; [lia | side7 | rewrite length_N_to_le_bytes; exact Hk]).
Qed.

Section AG7.
Context {fx : FPState}.
Variable FORB : list (Z * Z).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x87000).

Definition ag_mpost (HTOP : Z) (X : list sptr) (U : Z -> Z) (L : layout) (s2 : astate) (m2 : word -> option byte) (R : bvmap 5 word)
    (sp0 K sc req : Z) (mt : sptr) (ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 : Z) : @wpost (Z * astate) :=
  fun L' r R' pc m' => r = (0, ag_s6 mt s2 sc req) /\ pc = wa 0x52b8c /\ getr R' 10 = wa 0 /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa sv0 /\ getr R' 9 = wa sv1 /\ getr R' 18 = wa sv2 /\
    getr R' 19 = wa sv3 /\ getr R' 20 = wa sv4 /\ getr R' 21 = wa sv5 /\ getr R' 22 = wa sv6 /\ getr R' 23 = wa sv7 /\
    getr R' 24 = wa sv8 /\ getr R' 25 = wa sv9 /\
    (forall k, In k [3; 4; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (Inv X (Some (mt, 0)) U (ag_s6 mt s2 sc req) ->
       CUT HTOP X (Some (mt, 0)) U L' (ag_s6 mt s2 sc req) m' sp0 K /\ GROW sp0 K L s2 m2 L' (ag_s6 mt s2 sc req) m' /\
       (forall am, MT (ag_s6 mt s2 sc req) mt = Some (MUsed am) -> cell_holds L' (bview SEGS m') (gend_cell am))).

#[using="HFORB"] Theorem ag_mmap_wk : forall HTOP X U L s2 m2 (R : bvmap 5 word) rom sp0 K sc req mt f can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9,
  CUT HTOP (mt :: X) None U L s2 m2 sp0 K -> 1232 <= K ->
  as_frame R m2 sp0 sc req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 ->
  getr R 10 = wa (loc_addr L (LMem mt)) -> getr R 19 = wa (2 * sc) -> getr R 24 = wa (znth sc size_classes) -> getr R 25 = wa 98984 ->
  rdn SEGS m2 (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) -> TABS m2 ->
  (forall c, 0 <= c < 48 -> usage_of s2 c < 2^40) ->
  active_hd s2 sc = None -> (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s2 sc) + UNIT) = true ->
  req + IB <= class_size sc -> ~ In mt X ->
  wk SEGS FORB HTOP rom L R (wa 0x524e8) m2 (AGC f sc req mt s2)
    (ag_mpost HTOP X U L s2 m2 R sp0 K sc req mt ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9).
Proof. LiaFast.lf_pins (fun (HFORB : LiaFast.U) => LiaFast.u0).
  intros HTOP X U L s2 m2 R rom sp0 K sc req mt f can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 C2 HK F R10 R19 R24 R25 Mpg TB UB Hhd Hbr Hfit NX.
  pose proof C2 as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (nc_sp3 _ _ _ _ _ _ _ N) as Hsp3. pose proof (nc_stk _ _ _ _ _ _ _ N) as HSTK. pose proof (nc_K _ _ _ _ _ _ _ N) as HK1.
  pose proof F as [A2 A8 A18 A20 A21 A22 A23 Hsp Asp Hsc Hreq Hcan Hra Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9
                   Fra Fs0 Fs1 Fs2 Fs3 Fs4 Fs5 Fs6 Fs7 Fs8 Fs9 Fcan Fgd].
  assert (Hsc' : 0 <= sc < 48) by (clear - Hsc; lia).
  pose proof (size_classes_range sc Hsc') as Hun. pose proof (class_units sc) as Ecs.
  assert (Hsize : 16 <= class_size sc <= 131056) by (rewrite Ecs; clear - Hun; lia).
  (* [comment removed for export] *)
  destruct (ag_mmap_tree f sc req mt s2 Hbr Hhd) as (Kt & Et & EK1).
  unfold AGC. rewrite Et. cbn [ibind].
  (* [comment removed for export] *)
  pose proof (inv_ctx HI) as (C1 & C2' & C3' & C4 & C5 & C6 & C7 & C8 & C9 & _).
  set (u0 := usage_of s2 sc). set (u1 := usage_of s2 (sc + 1)). set (cnt0 := initial_cnt sc u0).
  set (b := znth (sc - 7) (st_bounces s2)). set (useq := znth (sc - 7) (st_unmap_seq s2)). set (seq := st_seq s2).
  set (mta := loc_addr L (LMem mt)).
  assert (ZN : forall (l : list Z) i lo hi, (forall u, In u l -> lo <= u <= hi) -> lo <= 0 <= hi -> lo <= znth i l <= hi).
  { intros l i lo hi Hl H0. unfold znth. destruct (nth_in_or_default (Z.to_nat i) l 0) as [H|H]; [exact (Hl _ H) | rewrite H; exact H0]. }
  assert (Hu0 : 0 <= u0 <= 2^60).
  { pose proof (UB sc Hsc') as H. pose proof (ZN (st_usage s2) sc 0 (2^60)) as H'. unfold u0, usage_of.
    assert (0 <= znth sc (st_usage s2)) by (unfold znth; destruct (nth_in_or_default (Z.to_nat sc) (st_usage s2) 0) as [E|E]; [exact (C5 _ E) | rewrite E; lia]).
    unfold usage_of in H. clear - H H0. lia. }
  assert (Hu1 : 0 <= u1 <= 2^60).
  { unfold u1, usage_of, znth. destruct (nth_in_or_default (Z.to_nat (sc + 1)) (st_usage s2) 0) as [E|E]; [|rewrite E; lia].
    pose proof (C5 _ E) as Hn. destruct (Z_lt_le_dec (sc + 1) 48) as [Lt|Ge].
    - pose proof (UB (sc + 1) ltac:(clear - Lt Hsc; lia)) as H. unfold usage_of, znth in H. clear - H Hn. lia.
    - assert (E2 : nth (Z.to_nat (sc + 1)) (st_usage s2) 0 = 0) by (apply nth_overflow; rewrite C2'; lia). rewrite E2. lia. }
  assert (Hseq : 0 <= seq <= 255) by exact C8.
  assert (Hb : 0 <= b <= 255) by (apply ZN; [exact C7 | lia]).
  assert (Hus : 0 <= useq <= 255) by (apply ZN; [exact C6 | lia]).
  pose proof (initial_cnt_facts sc u0 Hsc') as (Hc0 & Hc0s & Hc026). fold cnt0 in Hc0, Hc0s, Hc026.
  (* [comment removed for export] *)
  assert (RDC : forall c, In c (ctx_cells s2) -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
             rdn SEGS m2 (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))))
    by (intros c Hc Hv Hw; exact (nc_ctx_rd L s2 m2 sp0 K c N Hc Hv Hw)).
  assert (Lc : forall o, loc_addr L (LCtx o) = 614104 + o) by (intros o; cbn [loc_addr]; rewrite Hctx; reflexivity).
  assert (Musg : rdn SEGS m2 (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa u0))).
  { pose proof (RDC _ (usage_in_ctx s2 (Z.to_nat sc) ltac:(clear - Hsc; lia)) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_usage in H. rewrite Z2Nat.id in H by lia.
    replace (614104 + (464 + 8 * sc)) with (8 * sc + 614568) in H by ring. exact H. }
  assert (Mu1 : sc <= 31 -> rdn SEGS m2 (wa (8 * sc + 614576)) 8 = Some (word_to_le_bytes 8 (wa u1))).
  { intros S. pose proof (RDC _ (usage_in_ctx s2 (Z.to_nat (sc + 1)) ltac:(clear - S Hsc; lia)) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_usage in H. rewrite Z2Nat.id in H by lia.
    replace (614104 + (464 + 8 * (sc + 1))) with (8 * sc + 614576) in H by ring. exact H. }
  assert (Mseq : rdn SEGS m2 (wa (0 + 615016)) 1 = Some (word_to_le_bytes 1 (wa seq))).
  { pose proof (RDC _ (seq_in_ctx s2) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_seq in H. exact H. }
  assert (PC : PCUT HTOP L [] s2 m2 sp0 K) by exact (PCUT_of_CUT HTOP (mt :: X) None U L s2 m2 sp0 K C2).
  assert (WC : forall o n, 0 <= o -> o + n <= 928 -> forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m2 (wa (614104 + o + d)) k = true).
  { intros o n Ho Hn d k Hd Hk. refine (pc_wr HTOP L [] s2 m2 sp0 K (LCtx 0, CTX_SIZE) PC (or_introl eq_refl) (614104 + o) n _ _ _ _ d k Hd Hk);
      cbn [fst snd]; rewrite ?Lc; unfold CTX_SIZE; clear - Ho Hn; lia. }
  assert (Mtr : ab_tr sc = true -> rdn SEGS m2 (wa (sc + 614977)) 1 = Some (word_to_le_bytes 1 (wa b)) /\
             rdn SEGS m2 (wa (sc + 614945)) 1 = Some (word_to_le_bytes 1 (wa useq)) /\
             (forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m2 (wa (sc + 614977 + d)) k = true)).
  { intros Tr. assert (H7 : 7 <= sc < 39) by (unfold ab_tr in Tr; apply andb_true_iff in Tr as [T1 T2]; apply Z.leb_le in T1; apply Z.ltb_lt in T2; lia).
    split; [|split].
    - pose proof (RDC _ (bounce_in_ctx s2 (Z.to_nat (sc - 7)) ltac:(clear - H7; lia)) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
      cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_bounces in H. rewrite Z2Nat.id in H by lia.
      replace (614104 + (880 + (sc - 7))) with (sc + 614977) in H by ring. exact H.
    - pose proof (RDC _ (unmap_in_ctx s2 (Z.to_nat (sc - 7)) ltac:(clear - H7; lia)) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
      cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_unmap_seq in H. rewrite Z2Nat.id in H by lia.
      replace (614104 + (848 + (sc - 7))) with (sc + 614945) in H by ring. exact H.
    - intros d k Hd Hk. replace (sc + 614977 + d) with (614104 + (sc + 873) + d) by ring. apply (WC (sc + 873) 1); clear - H7 Hd Hk; lia. }
  assert (Wun : forall d k, 0 <= d -> d + Z.of_nat k <= 32 -> store_ok SEGS m2 (wa (0 + 614952 + d)) k = true).
  { intros d k Hd Hk. replace (0 + 614952 + d) with (614104 + 848 + d) by ring. apply (WC 848 32); clear - Hd Hk; lia. }
  assert (Wseq : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m2 (wa (0 + 615016 + d)) k = true).
  { intros d k Hd Hk. replace (0 + 615016 + d) with (614104 + 912 + d) by ring. apply (WC 912 1); clear - Hd Hk; lia. }
  (* [comment removed for export] *)
  assert (Hmt0 : MT s2 mt = Some MRaw \/ MT s2 mt = Some (MFree None None)) by exact (HX mt (or_introl eq_refl)).
  assert (Hkey : In mt (keys s2)) by (destruct Hmt0 as [E'|E']; exact (MT_keys s2 mt _ E')).
  pose proof (nc_mplace _ _ _ _ _ _ _ N mt Hkey) as (Pm1 & Pm2 & Pm3 & Pm4). fold mta in Pm1, Pm2, Pm3, Pm4.
  assert (Hmta : 1 <= mta <= 2^63-1) by (clear - Pm1 Pm2 Hsp2 HK1; lia).
  (* [comment removed for export] *)
  destruct (seg_agc R m2 rom sc mta u0 A8 R10 R19 A23 R24 R25 Hsc Hmta Hu0 Musg Mpg TB)
    as (R1 & Hms1 & B8 & B9 & B10 & B11 & B19 & B24 & B23 & B25 & B12 & B14 & BK).
  fold cnt0 in Hms1, B19, B14. fold u0 cnt0 in Hbr. rewrite Hbr in Hms1.
  (* [comment removed for export] *)
  assert (STK : stk_ok SEGS m2 (wa (sp0 + -144)) 1088).
  { replace (sp0 + -144) with (sp0 - 144) by ring. apply (stk_ok_mono' m2 _ (K - 144) 1088); [|clear - HK; lia].
    apply stk_ok_shift; [exact HSTK | lia | clear - Hsp1 HK; lia | clear - Hsp2; lia]. }
  assert (Hsp0 : 2^20 + 1024 <= sp0 <= 2^47) by (clear - Hsp1 Hsp2 HK; lia).
  destruct (seg_mpre R1 m2 rom sp0 sc mta u0 cnt0 req seq b useq u1 ltac:(regk BK 2%nat; exact A2) B8 B9 B10 B11 B12 B14
              ltac:(regk BK 18%nat; exact A18) B19 ltac:(regk BK 20%nat; exact A20) ltac:(regk BK 21%nat; exact A21)
              ltac:(regk BK 22%nat; exact A22) B23 B24 Hsp0 Asp STK Hsc Hmta Hu0 ltac:(clear - Hc0; lia) Hreq Hseq Hb Hus Hu1
              ltac:(clear - Hc0s; lia) Mseq Mtr Wun Wseq Mu1)
    as (R2' & Hms2 & T17 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T2 & T22 & T23 & T24 & T25 & TK).
  replace (mm_plan sc cnt0 u0 u1 b req) with (ag_plan s2 sc req) in Hms2, T11, T25 by (symmetry; exact (mm_plan_eq s2 sc req Hsc)).
  assert (E6 : ag_s6 mt s2 sc req = ins_st mt sc (fst (ag_plan s2 sc req)) (ag_aidx sc (fst (ag_plan s2 sc req))) (snd (ag_plan s2 sc req) / 4096)
                 (SP (length (st_regions (ag_s3 s2 sc))) 0) slot_zero (ag_s5 (ag_s3 s2 sc) (snd (ag_plan s2 sc req)))) by reflexivity.
  rewrite E6 in EK1. unfold ag_mpost. rewrite E6. clear E6.
  destruct (ag_plan s2 sc req) as [cnt len] eqn:Ep. cbn [fst snd] in *.
  pose proof (mmap_plan_facts s2 sc req cnt0 u0 cnt len Hsc' Hc0 Hc0s ltac:(clear - Hreq; lia) Hfit Hc026 Ep)
    as (Hcnt & Hcs & Hc26 & Nmod & N4096 & Nmax & Nfit & Nreq & Npr).
  set (m3 := mmw_frame (sq_mem (ab_mem m2 sc b useq seq) seq) (sp0 + -144) sc mta len 613952 (8 * sc + 614184)) in *.
  destruct (cut_s3 HTOP (mt :: X) None U L s2 m2 sp0 K sc mta len 613952 (8 * sc + 614184) C2 Hsc ltac:(clear - HK; lia)) as (C3 & G3).
  fold m3 in C3, G3.
  (* [comment removed for export] *)
  cbn [wk]. exists R2', (wa 0x533ec), m3. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|]. split.
  { split; [exact ecall_52ecc|]. exists SYS_mmap, [0; len; 3; 34; 2 ^ 64 - 1; 0]. split; [reflexivity|].
    split; [rewrite T17; reflexivity|].
    Ltac argk2 T := match type of T with getr _ ?r0 = _ => match goal with |- bv_unsigned (getr _ ?r1) = _ =>
      replace r1 with r0 by (apply bv_eq; reflexivity) end end; rewrite T, u_wa; reflexivity.
    split; [argk2 T10|]. split; [argk2 T11|]. split; [argk2 T12|]. split; [argk2 T13|]. split; [argk2 T14|]. split; [argk2 T15|]. exact I. }
  intros eff ans L' Ho. destruct (kout_mmap_rw FORB HTOP L (ag_s3 s2 sc) len eff ans L' Ho) as (a & FR & -> & -> & ->).
  rewrite add4_52ecc. cbn [eff_ret]. rewrite EK1. cbn [ibind]. unfold ret. cbn [wk].
  (* [comment removed for export] *)
  pose proof (page_round_fixed len Nmod) as PRL.
  set (m1' := mem_after m3 (mkEffect (w64 a) [] [(w64 a, w64 (page_round len))])).
  pose proof FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7). rewrite PRL in F4, F5.
  assert (HIMG : ranges_disjoint (a, page_round len) (0x10000, 0x87000)) by (rewrite PRL; apply HFORB; [clear - N4096; unfold PGSZ in *; lia | exact F5]).
  assert (Dimg : a + len <= 0x10000 \/ 0x97000 <= a) by (rewrite PRL in HIMG; unfold ranges_disjoint in HIMG; cbn [fst snd] in HIMG; clear - HIMG; lia).
  assert (Ha : 4096 <= a) by (unfold PGSZ in F1; exact F1).
  assert (Ha47 : a + len <= 2^47) by (clear - F4 HTB; lia).
  assert (OUT1 : forall x, 0 <= x < 2^64 -> ~ (a <= x < a + len) -> m1' (wa x) = m3 (wa x)).
  { intros x Hx Hn. unfold m1'. rewrite mem_after_zero by (clear - Hx Ha Ha47 PRL Nmax N4096; rewrite ?PRL; unfold PGSZ in *; lia). rewrite PRL.
    replace ((a <=? x) && (x <? a + len)) with false by (symmetry; apply andb_false_iff; destruct (Z_le_dec a x); [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]).
    reflexivity. }
  assert (IN1 : forall x, a <= x < a + len -> m1' (wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. unfold m1'. rewrite mem_after_zero by (clear - Hx Ha Ha47 PRL Nmax N4096; rewrite ?PRL; unfold PGSZ in *; lia). rewrite PRL.
    replace ((a <=? x) && (x <? a + len)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  assert (OUT3 : forall x, 0 <= x < 2^64 -> ~ (sp0 - 200 <= x < sp0 - 144) -> ~ (614104 <= x < 615032) -> m3 (wa x) = m2 (wa x)).
  { intros x Hx N1 N2. unfold m3. rewrite mmw_frame_out by (clear - Hx N1 Hsp0; lia). rewrite sq_mem_out by (clear - N2 Hx; lia).
    apply ab_mem_out; [exact Hx | exact Hsc | clear - N2 Hsc; lia]. }
  assert (F1' : as_frame R m1' sp0 sc req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9).
  { apply (as_frame_mem R m2); [exact F | |].
    - intros x Hx. rewrite OUT1 by (clear - Hx Hsp0 F4 HT HK; lia). apply OUT3; clear - Hx Hsp0; lia.
    - intros x Hx. rewrite OUT1 by (clear - Hx Dimg; lia). apply OUT3; clear - Hx Hsp0; lia. }
  (* [comment removed for export] *)
  set (s3 := ag_s3 s2 sc) in *.
  pose proof (s3_same s2 sc) as SAME. fold s3 in SAME.
  pose proof SAME as (_ & E2 & _ & Ea3 & _ & _ & _ & _ & _ & _ & _ & _ & Eac3 & Eus3 & Em3 & Er3).
  pose proof C3 as [HI3 HX3 N3 HG3 HD3 HT3 HTB3].
  assert (P3 : PCUT HTOP L [] s3 m3 sp0 K) by exact (PCUT_of_CUT HTOP (mt :: X) None U L s3 m3 sp0 K C3).
  assert (TR1 : forall x n, 0 <= x -> x + Z.of_nat n <= 2^64 -> (x + Z.of_nat n <= a \/ a + len <= x) -> rdn SEGS m1' (wa x) n = rdn SEGS m3 (wa x) n).
  { intros x n H1 H2 H3. apply rdn_frame_n; [exact H1 | exact H2 |]. intros y Hy. apply OUT1; clear - Hy H1 H2 H3; lia. }
  assert (G31 : mem_grows m3 m1') by (apply mem_after_zero_grows'; clear - Ha Ha47 PRL N4096 Nmax; rewrite ?PRL; unfold PGSZ in *; lia).
  assert (Hkey3 : In mt (keys s3)) by (unfold keys; rewrite Em3; exact Hkey).
  destruct (key_slot_range HTOP (mt :: X) None U s3 L mt HI3 HG3 Hkey3) as (ar & j & rr & rga & Har & Hj & Ear & Epr & Hrr & Hlv & Hkd & A1' & A2' & A3' & A4').
  fold mta in A4'.
  assert (Dma : mta + 40 <= a \/ a + len <= mta).
  { pose proof (F7 rr rga Hrr Hlv) as D. rewrite PRL in D. unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite A4'.
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - D A2' A3' Hj. lia. }
  assert (Lc3 : forall o, loc_addr L (LCtx o) = 614104 + o) by exact Lc.
  assert (RD3 : forall c, In c (ctx_cells s3) -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
             rdn SEGS m3 (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))))
    by (intros c Hc Hv Hw; exact (nc_ctx_rd L s3 m3 sp0 K c N3 Hc Hv Hw)).
  assert (WC3 : forall o n, 0 <= o -> o + n <= 928 -> forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok SEGS m1' (wa (614104 + o + d)) k = true).
  { intros o n Ho' Hn d k Hd Hk. apply (store_ok_mono SEGS k m3 m1' _ G31).
    refine (pc_wr HTOP L [] s3 m3 sp0 K (LCtx 0, CTX_SIZE) P3 (or_introl eq_refl) (614104 + o) n _ _ _ _ d k Hd Hk);
      cbn [fst snd]; rewrite ?Lc; unfold CTX_SIZE; clear - Ho' Hn; lia. }
  (* [comment removed for export] *)
  assert (KS3 : KS s3) by exact (KS_of_Inv (mt :: X) None U s3 HI3).
  assert (Hmt3 : MT s3 mt = Some MRaw \/ MT s3 mt = Some (MFree None None)) by (unfold MT; rewrite Em3; exact Hmt0).
  assert (RAW : forall d, d = 0 \/ d = 8 \/ d = 32 -> rdn SEGS m1' (wa (mta + d)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { intros d Hd. rewrite TR1 by (clear - Hd Hmta Dma Pm2 Hsp2 HK1 N4096; unfold PGSZ in *; lia).
    assert (Hc : In (MCell (LMem (padd mt d)) 8 (VZ 0)) (image s3)).
    { destruct Hmt3 as [E0|E0]; apply (msc_key_in_image s3 mt _ _ KS3 E0); cbn [meta_slot_cells optr];
        destruct Hd as [->|[->| ->]]; cbn [In]; unfold META_prev, META_next, META_bits; repeat first [ (left; reflexivity) | right ]. }
    pose proof (pc_rd HTOP L [] s3 m3 sp0 K _ P3 Hc (fun H => H) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite loc_padd in H. exact H. }
  assert (Mctr : rdn SEGS m1' (wa (0 + 614116)) 4 = Some (word_to_le_bytes 4 (wa (st_mmap_counter s3)))).
  { rewrite TR1 by (clear - Dimg; cbn; lia).
    pose proof (RD3 (MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter s3))) ltac:(unfold ctx_cells; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ])
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_mmap_counter in H. exact H. }
  assert (Musg3 : rdn SEGS m1' (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa (usage_of s3 sc)))).
  { rewrite TR1 by (clear - Dimg Hsc; cbn; lia).
    pose proof (RD3 _ (usage_in_ctx s3 (Z.to_nat sc) ltac:(clear - Hsc; lia)) ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val sval_num] in H. rewrite Lc in H. unfold CTX_usage in H. rewrite Z2Nat.id in H by lia.
    replace (614104 + (464 + 8 * sc)) with (8 * sc + 614568) in H by ring. exact H. }
  assert (Mact3 : rdn SEGS m1' (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { rewrite TR1 by (clear - Dimg Hsc; cbn; lia).
    pose proof (RD3 _ (act_in_ctx s3 (Z.to_nat sc) ltac:(clear - Hsc; lia))
                  ltac:(intros z E; cbn [act_cell mc_val] in E; destruct (nth (Z.to_nat sc) (st_active s3) None); discriminate E) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val act_cell] in H. rewrite Lc in H. unfold CTX_active in H. rewrite Z2Nat.id in H by lia.
    replace (614104 + (80 + 8 * sc)) with (8 * sc + 614184) in H by ring.
    assert (EH : nth (Z.to_nat sc) (st_active s3) None = None) by (rewrite Eac3; exact Hhd). rewrite EH in H. exact H. }
  assert (Mhb : rdn SEGS m1' (wa (a + 8)) 1 = Some (word_to_le_bytes 1 (wa 0))).
  { pose proof (rdn_read m1' (a + 8) (word_to_le_bytes 1 (wa 0))) as H. rewrite length_N_to_le_bytes in H. apply H; [clear - Ha; lia | clear - Ha47 N4096 Ha; unfold PGSZ in *; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
    intros k Hk. assert (k = 0%nat) as -> by (clear - Hk; lia). rewrite IN1 by (clear - Ha Ha47 N4096; unfold PGSZ in *; cbn; lia). reflexivity. }
  assert (Wmt : forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m1' (wa (mta + 0 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m3 m1' _ G31).
    refine (pc_wr HTOP L [] s3 m3 sp0 K (LMem ar, PGSZ) P3 _ (mta + 0) 40 _ _ _ _ d k Hd Hk).
    - right. apply in_app_iff. left. apply (in_map (fun a0 => (LMem a0, PGSZ))). exact Har.
    - cbn [fst snd]. rewrite A4'. unfold AREA_HDR, META_SIZE. clear - Hj; lia.
    - cbn [fst snd]. rewrite A4'. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - Hj; lia.
    - clear - Hmta; lia.
    - clear - Hmta; lia. }
  assert (ZPa : ZP m1' a) by (intros x Hx; apply IN1; clear - Hx N4096; unfold PGSZ in *; lia).
  assert (Wa : forall d k, 0 <= d -> d + Z.of_nat k <= 9 -> store_ok SEGS m1' (wa (a + 0 + d)) k = true).
  { intros d k Hd Hk. exact (zp_wr m1' a ZPa ltac:(clear - Ha; lia) ltac:(clear - Ha47 N4096; unfold PGSZ in *; lia) 0 9 ltac:(lia) ltac:(unfold PGSZ; lia) d k Hd Hk). }
  assert (Us3 : usage_of s3 sc = u0) by (unfold usage_of, znth; rewrite Eus3; reflexivity).
  assert (Ct3 : st_mmap_counter s3 = st_mmap_counter s2) by exact E2.
  (* [comment removed for export] *)
  destruct (mmw_reads (sq_mem (ab_mem m2 sc b useq seq) seq) (sp0 + -144) sc mta len 613952 (8 * sc + 614184) ltac:(clear - Hsp0; lia))
    as (W1 & W2 & W3 & W4 & W5 & W6 & W7). fold m3 in W1, W2, W3, W4, W5, W6, W7.
  rewrite <- TR1 in W1, W2, W3, W4, W5, W6, W7 by (clear - Hsp0 F4 HT HK; lia).
  (* [comment removed for export] *)
  destruct (seg_mpost (regupd R2' 10 (w64 a)) m1' rom sp0 sc req can ra sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 R mta a len cnt
              (usage_of s3 sc) (st_mmap_counter s3) F1'
              ltac:(rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact T2)
              ltac:(rewrite getr_same by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); reflexivity)
              ltac:(rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact T16)
              ltac:(rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact T22)
              ltac:(rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact T23)
              ltac:(rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact T24)
              ltac:(rewrite getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate E); exact T25)
              W1 W2 W3 W4 W5 W6 W7 Ha ltac:(unfold PGSZ in F2; exact F2) ltac:(clear - N4096 Nmax; unfold PGSZ in *; lia) Nmod Ha47
              Hmta Pm4 Hcnt ltac:(rewrite Us3; exact Hu0) ltac:(rewrite Ct3; clear - C9; lia)
              (RAW 32 ltac:(lia)) (RAW 0 ltac:(lia)) (RAW 8 ltac:(lia)) Mctr Musg3 Mact3 Mhb Wmt
              ltac:(intros d k Hd Hk; replace (0 + 614116 + d) with (614104 + 12 + d) by ring; apply (WC3 12 4); clear - Hd Hk; lia)
              ltac:(intros d k Hd Hk; replace (8 * sc + 614568 + d) with (614104 + (464 + 8 * sc) + d) by ring; apply (WC3 (464 + 8 * sc) 8); clear - Hd Hk Hsc; lia)
              ltac:(intros d k Hd Hk; replace (8 * sc + 614184 + d) with (614104 + (80 + 8 * sc) + d) by ring; apply (WC3 (80 + 8 * sc) 8); clear - Hd Hk Hsc; lia)
              Wa Pm3 Dimg Dma ltac:(clear - Pm2 HK1; lia) ltac:(clear - F4 HT HK1; lia) ltac:(clear - Hsp0; lia))
    as (R3 & Hms3 & Q1 & Q2 & Q8 & Q9 & Q10 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & QK).
  exists R3, (wa 0x52b8c), (mp_mem m1' mta a len sc cnt (ag_aidx sc cnt) (usage_of s3 sc) (st_mmap_counter s3)). split; [exact Hms3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Q10|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|].
  split; [exact Q9|]. split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|].
  split; [exact Q23|]. split; [exact Q24|]. split; [exact Q25|]. split.
  { intros k Hk. rewrite (QK k Hk). rewrite getr_other.
    - rewrite (TK k Hk). exact (BK k ltac:(clear - Hk; klist Hk)).
    - intros E. apply (f_equal bv_unsigned) in E. clear - Hk E. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [discriminate E|]). destruct Hk. }
  (* [comment removed for export] *)
  intros HI6.
  destruct (cut_s6 HTOP FORB X U L s3 m3 sp0 K mt sc cnt len a C3 Hsc Hcnt ltac:(clear - N4096 Nmax; unfold PGSZ in *; lia) Nmod Nfit FR HIMG NX HI6)
    as (CC6 & GG6).
  split; [exact CC6|]. split; [exact (GROW_trans sp0 K L s2 m2 L s3 m3 _ _ _ G3 GG6)|].
  (* [comment removed for export] *)
  intros am Mam.
  set (s6 := ins_st mt sc cnt (ag_aidx sc cnt) (len / 4096) (SP (length (st_regions s3)) 0) slot_zero (ag_s5 s3 len)) in *.
  assert (Eam : am = am_set_links (Some mt) (Some mt) (new_am (SP (length (st_regions s3)) 0) sc cnt (ag_aidx sc cnt) (len / 4096) slot_zero)).
  { unfold MT, s6, ins_st in Mam. cbn [st_metas set_active set_metas set_usage] in Mam. rewrite mlookup_mupdate_same in Mam. injection Mam as <-. reflexivity. }
  assert (Um : usedX X s6 mt am) by (apply usedX_intro; [apply (proj2 (memb_false_notIn mt X)); exact NX | exact Mam]).
  pose proof (inv_groups HI6 mt am Um) as (_ & _ & _ & _ & Gmp & _).
  assert (Hml : 0 < am_maplen am) by (rewrite Eam; cbn [am_maplen am_set_links new_am]; apply Z.div_str_pos; unfold PGSZ in N4096; lia).
  destruct (Gmp Hml) as (r0 & rg0 & Em0 & _ & _ & _ & Len0 & Fit0 & _).
  assert (Ems : len / 4096 * PGSZ = len) by (unfold PGSZ; pose proof (Z_div_mod_eq_full len 4096); unfold PGSZ in Nmod; lia).
  assert (EML : am_maplen am = len / 4096) by (rewrite Eam; reflexivity). rewrite EML, Ems in Fit0.
  assert (Sp6 : 16 <= stride_of am) by exact (stride_pos _ _ _ _ _ (inv_groups HI6 mt am Um)).
  assert (LK : loc_addr (set_reg_addr L (length (st_regions s3)) a) (mc_loc (gend_cell am)) = a + 12 + stride_of am * (am_last am + 1)).
  { cbn [gend_cell mc_loc]. unfold slot_end. rewrite loc_padd. unfold slot_start at 1. rewrite loc_padd.
    assert (Emm : am_mem am = SP (length (st_regions s3)) 0) by (rewrite Eam; reflexivity). rewrite Emm.
    cbn [loc_addr prid poff]. unfold set_reg_addr. cbn [ly_reg]. rewrite Nat.eqb_refl. unfold UNIT, IB. ring. }
  assert (Hlast : 0 <= am_last am) by (rewrite Eam; cbn [am_last am_set_links new_am]; clear - Hcnt; lia).
  assert (Hgb : a + 28 <= a + 12 + stride_of am * (am_last am + 1) < a + len) by (clear - Fit0 Sp6 Hlast; unfold UNIT in *; nia).
  unfold gend_cell in LK |- *. cbn [mc_loc] in LK.
  apply (holds_read (set_reg_addr L (length (st_regions s3)) a) _ _ 1 _ 0); [intros z E; discriminate E | lia | rewrite LK; clear - Hgb Ha; lia | rewrite LK; clear - Hgb Ha47; cbn [Z.of_nat Pos.of_succ_nat]; lia | reflexivity |].
  intros k Hk. assert (k = 0%nat) as -> by lia. rewrite LK, Z.add_0_r.
  rewrite mp_mem_out; [| clear - Hgb Ha Ha47; lia | exact Hsc | clear - Hmta; lia | clear - Hmta; lia | clear - Ha; lia | clear - Ha47 Hgb; lia
                       | clear - Dma Hgb; lia | clear - Dimg Hgb; lia | clear - Dimg Hgb Hsc; lia | clear - Dimg Hgb Hsc; lia | clear - Hgb; lia].
  rewrite IN1 by (clear - Hgb; lia). reflexivity.
Qed.



End AG7.

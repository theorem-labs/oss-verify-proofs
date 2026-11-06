(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez AXG_ntfm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_decz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ntfm.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.
Ltac wgrow := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MB.
Variable am : ameta.
Hypothesis Hl : 0 <= am_last am <= 31.
Hypothesis Hs : 0 <= am_sc am < 64.
Hypothesis Hm : 0 <= am_maplen am.

#[using="Hl Hs Hm"] Lemma mb_land31 : Z.land (meta_bits am) 31 = am_last am.
Proof. LiaFast.lf_pins (fun (Hl Hs Hm : LiaFast.U) => LiaFast.u0).
  unfold meta_bits. replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with (am_last am + 32 * (1 + 2 * am_sc am + 128 * am_maplen am)) by ring.
  apply land31; lia.
Qed.

#[using="Hl Hs"] Lemma mb_shr12 : Z.shiftr (meta_bits am) 12 = am_maplen am.
Proof. LiaFast.lf_pins (fun (Hl Hs : LiaFast.U) => LiaFast.u0).
  unfold meta_bits. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
  replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((am_last am + 32 + 64 * am_sc am) + am_maplen am * 4096) by ring.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring.
Qed.

#[using="Hl Hs"] Lemma mb_scw : SCW (meta_bits am) = am_sc am.
Proof. LiaFast.lf_pins (fun (Hl Hs : LiaFast.U) => LiaFast.u0).
  unfold meta_bits, SCW. set (l := am_last am) in *. set (sc := am_sc am) in *. set (ml := am_maplen am) in *.
  replace (4503599627370496 * (l + 32 + 64 * sc + 4096 * ml)) with (4503599627370496 * (l + 32 + 64 * sc) + ml * 2^64) by ring.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2^58) with (4503599627370496 * 64). rewrite <- Z.div_div by lia. rewrite Z.mul_comm, Z.div_mul by lia.
  replace (l + 32 + 64 * sc) with ((l + 32) + sc * 64) by ring. rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring.
Qed.

#[using="Hl Hs"] Lemma mb_land32 : Z.land (meta_bits am) 32 <> 0.
Proof. LiaFast.lf_pins (fun (Hl Hs : LiaFast.U) => LiaFast.u0).
  intros E. assert (T : Z.testbit (meta_bits am) 5 = true).
  { assert (Q : Z.shiftr (meta_bits am) 5 = 1 + 2 * (am_sc am + 64 * am_maplen am)).
    { unfold meta_bits. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
      replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with (am_last am + (1 + 2 * (am_sc am + 64 * am_maplen am)) * 32) by ring.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
    replace 5 with (0 + 5) by reflexivity. rewrite <- Z.shiftr_spec by lia. rewrite Q. rewrite Z.bit0_odd.
    rewrite Z.odd_add_mul_2. reflexivity. }
  assert (T2 : Z.testbit (Z.land (meta_bits am) 32) 5 = true) by (rewrite Z.land_spec, T; reflexivity).
  rewrite E in T2. discriminate.
Qed.
End MB.

Lemma dec_ok_model : forall s g am i G csz nxt bnc usg,
  0 <= am_last am <= 31 -> 0 <= am_sc am < 48 -> 0 <= am_maplen am ->
  csz = znth (am_sc am) size_classes ->
  (nxt = G <-> am_next am = Some g) ->
  (7 <= am_sc am < 39 -> bnc = znth (am_sc am - 7) (st_bounces s)) ->
  usg = usage_of s (am_sc am) ->
  dec_ok G i (meta_bits am) (am_avail am) (am_freed am) csz nxt bnc usg =
    (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am.
Proof.
  intros s g am i G csz nxt bnc usg Hl Hs Hm Ecsz Enx Ebn Eus. unfold dec_ok.
  rewrite (mb_land31 am), (mb_shr12 am), (mb_scw am) by lia.
  replace (Z.lor (am_avail am) (am_freed am) + 2 ^ i =? 2 ^ (am_last am + 1) - 1) with (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am))
    by (unfold bit, ones; rewrite Z.lor_comm; reflexivity).
  destruct (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)); [|reflexivity]. cbn [andb].
  unfold okay_to_free. replace (48 <=? am_sc am) with false by (symmetry; apply Z.leb_gt; lia). cbn [orb].
  unfold stride_of, class_size, UNIT. rewrite <- Ecsz.
  destruct (am_maplen am =? 0) eqn:Eml.
  - replace ((am_last am =? 0) && negb true) with false by (destruct (am_last am =? 0); reflexivity).
    rewrite Z.ltb_irrefl. reflexivity.
  - cbn [negb orb]. apply Z.eqb_neq in Eml.
    assert (EA : (if am_last am =? 0 then 4096 * am_maplen am + -16 <? 16 * csz else false) =
                 ((if (am_last am =? 0) && true then am_maplen am * 4096 - 16 else 16 * csz) <? 16 * csz)).
    { destruct (am_last am =? 0); cbn [andb]; [f_equal; ring | symmetry; apply Z.ltb_irrefl]. }
    rewrite EA. destruct ((if (am_last am =? 0) && true then am_maplen am * 4096 - 16 else 16 * csz) <? 16 * csz); [reflexivity|]. cbn [orb].
    assert (EN : negb (nxt =? G) = negb (osptr_eqb (am_next am) (Some g))).
    { f_equal. destruct (nxt =? G) eqn:E1.
      - apply Z.eqb_eq in E1. apply Enx in E1. rewrite E1. cbn [osptr_eqb]. symmetry. apply sptr_eqb_refl.
      - apply Z.eqb_neq in E1. destruct (am_next am) as [q|] eqn:Eq; cbn [osptr_eqb]; [|reflexivity].
        symmetry. apply sptr_eqb_neq. intros ->. apply E1. apply Enx. reflexivity. }
    rewrite EN. destruct (negb (osptr_eqb (am_next am) (Some g))); [reflexivity|]. cbn [orb].
    assert (EB : (31 <? (am_sc am + -7) mod 2^64) || (bnc <? 100) = negb (is_bouncing s (am_sc am))).
    { unfold is_bouncing, bounce_idx. destruct (Z_lt_le_dec (am_sc am) 7) as [A|A].
      - replace ((7 <=? am_sc am) && (am_sc am <? 39)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
        replace ((am_sc am + -7) mod 2^64) with (am_sc am + -7 + 2^64) by (rewrite <- (Z.mod_small (am_sc am + -7 + 2^64) (2^64)) by lia;
          replace (am_sc am + -7 + 2^64) with (am_sc am + -7 + 1 * 2^64) by ring; rewrite Z_mod_plus_full; reflexivity).
        replace (31 <? am_sc am + -7 + 2^64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      - rewrite (Z.mod_small (am_sc am + -7) (2^64)) by lia.
        destruct (Z_lt_le_dec (am_sc am) 39) as [B|B].
        + replace ((7 <=? am_sc am) && (am_sc am <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
          replace (31 <? am_sc am + -7) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
          rewrite (Ebn (conj A B)). replace (am_sc am + -7) with (am_sc am - 7) by ring.
          destruct (znth (am_sc am - 7) (st_bounces s) <? 100) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1].
          * replace (100 <=? znth (am_sc am - 7) (st_bounces s)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
          * replace (100 <=? znth (am_sc am - 7) (st_bounces s)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        + replace ((7 <=? am_sc am) && (am_sc am <? 39)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
          replace (31 <? am_sc am + -7) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    rewrite EB. destruct (negb (is_bouncing s (am_sc am))); [reflexivity|]. cbn [orb]. rewrite Eus.
    destruct (usage_of s (am_sc am) <? 9 * am_last am + 9) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1].
    + replace (9 * (am_last am + 1) <=? usage_of s (am_sc am)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + replace (9 * (am_last am + 1) <=? usage_of s (am_sc am)) with true by (symmetry; apply Z.leb_le; lia). cbn [negb andb].
      destruct (18 <? am_last am) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2].
      * replace (am_last am + 1 <? 20) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * replace (am_last am + 1 <? 20) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DF.
Variables (m : word -> option byte) (regs R : bvmap 5 word) (sp0 canary : Z).
Hypothesis Hsp : 2^20 <= sp0 <= 2^47.

Ltac rdisj := rewrite rdn_wbytes_disjoint; [| cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite !u_wa_small by lia; lia | rewrite !u_wa_small by lia; lia].
Ltac rhit := apply (rdn_wbytes_hit SEGS); cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite u_wa_small by lia; lia.

#[using="Hsp"] Lemma dec_mem_slot : forall k, In k [8; 16; 24; 32; 40; 48] ->
  rdn SEGS (dec_mem m regs sp0 canary) (wa (sp0 + - k)) 8 =
    Some (word_to_le_bytes 8 (match k with 8 => getr regs 1 | 16 => getr regs 8 | 24 => getr regs 9 | 32 => getr regs 18 | 40 => getr regs 19 | _ => wa canary end)).
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0).
  intros k Hk. cbn [In] in Hk. unfold dec_mem.
  destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn beta iota.
  - do 5 rdisj. replace (sp0 + - 8) with (sp0 - 8) by ring. rhit.
  - do 4 rdisj. replace (sp0 + - 16) with (sp0 - 16) by ring. rhit.
  - do 3 rdisj. replace (sp0 + - 24) with (sp0 - 24) by ring. rhit.
  - do 2 rdisj. replace (sp0 + - 32) with (sp0 - 32) by ring. rhit.
  - do 1 rdisj. replace (sp0 + - 40) with (sp0 - 40) by ring. rhit.
  - replace (sp0 + - 48) with (sp0 - 48) by ring. rhit.
Qed.

#[using="Hsp"] Lemma dec_mem_out : forall x, 0 <= x < 2^64 -> ~ (sp0 - 48 <= x < sp0) -> dec_mem m regs sp0 canary (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0). intros x Hx H1. unfold dec_mem. do 6 peel. reflexivity. Qed.

#[using="Type"] Lemma dec_mem_grows : mem_grows m (dec_mem m regs sp0 canary).
Proof. LiaFast.lf_pins LiaFast.u0. unfold dec_mem. wgrow. Qed.

#[using="Hsp"] Lemma dec_frame : stk_ok SEGS m (wa sp0) 1024 -> getr R 2 = wa (sp0 - 96) -> getr R 9 = wa 0x95e40 -> sp0 mod 16 = 0 ->
  0 <= canary <= 2^64 - 1 -> rdn SEGS m (wa 613952) 8 = Some (word_to_le_bytes 8 (wa canary)) ->
  ntf_frame R (dec_mem m regs sp0 canary) sp0 canary (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
    (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)).
Proof. LiaFast.lf_pins (fun (Hsp : LiaFast.U) => LiaFast.u0).
  intros HSTK R2 R9 Asp Rc Mc. constructor; try assumption.
  - exact (stk_ok_grows SEGS m _ (wa sp0) 1024 HSTK dec_mem_grows).
  - pose proof (u64_range (getr regs 1)). lia.
  - pose proof (u64_range (getr regs 8)). lia.
  - pose proof (u64_range (getr regs 9)). lia.
  - pose proof (u64_range (getr regs 18)). lia.
  - pose proof (u64_range (getr regs 19)). lia.
  - rewrite wa_u. exact (dec_mem_slot 8 ltac:(clear; cbn; tauto)).
  - rewrite wa_u. exact (dec_mem_slot 16 ltac:(clear; cbn; tauto)).
  - rewrite wa_u. exact (dec_mem_slot 24 ltac:(clear; cbn; tauto)).
  - rewrite wa_u. exact (dec_mem_slot 32 ltac:(clear; cbn; tauto)).
  - rewrite wa_u. exact (dec_mem_slot 40 ltac:(clear; cbn; tauto)).
  - exact (dec_mem_slot 48 ltac:(clear; cbn; tauto)).
  - rewrite (rdn_frame_n m (dec_mem m regs sp0 canary) (0 + 0x95e40) 8) by (try lia; intros x Hx; apply dec_mem_out; lia). exact Mc.
Qed.
End DF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma meta_bits_nonneg : forall am, 0 <= am_last am -> 0 <= am_sc am -> 0 <= am_maplen am -> 0 <= meta_bits am.
Proof. intros am H1 H2 H3. unfold meta_bits. lia. Qed.

(* [comment removed for export] *)
Lemma NC_stack : forall L X EXC s m m1 sp0 K, NC L X EXC s m sp0 K -> mem_grows m m1 ->
  (forall x, 0 <= x < 2^64 -> ~ (sp0 - 48 <= x < sp0) -> m1 (wa x) = m (wa x)) ->
  NC L X EXC s m1 sp0 K /\ FRM L s sp0 K m m1.
Proof.
  intros L X EXC s m m1 sp0 K N Hg Hout.
  assert (FR : FRM L s sp0 K m m1).
  { intros x Hx Hne. left. destruct (decide (sp0 - 48 <= x < sp0)) as [A|A]; [pose proof (nc_K _ _ _ _ _ _ _ N); lia|].
    exfalso. apply Hne. apply Hout; assumption. }
  split; [|exact FR].
  apply (NC_next L X EXC s s m m1 sp0 K N); [| apply RS_refl | exact (nc_ks _ _ _ _ _ _ _ N) | intros; reflexivity | exact Hg | exact FR | reflexivity].
  apply (repr_x_same L s (bview SEGS m) (bview SEGS m1) EXC (nc_repr _ _ _ _ _ _ _ N) (fun a E => bview_grow_n m m1 a Hg E)).
  intros a Ha c Hc _ Hin. pose proof (bview_ne_range m m1 a Ha) as Ra.
  assert (Hs : sp0 - 48 <= a < sp0).
  { destruct (decide (sp0 - 48 <= a < sp0)) as [A|A]; [exact A|]. exfalso. apply Ha. apply bview_ext. apply Hout; assumption. }
  pose proof (nc_cells _ _ _ _ _ _ _ N c Hc) as (P1 & P2 & _). pose proof (nc_K _ _ _ _ _ _ _ N).
  unfold in_rng, cell_range in Hin. cbn [fst snd] in Hin. lia.
Qed.

Section SEGD.
Context {fx : FPState}.

#[using="Type"] Theorem seg_dec : forall L X EXC s m regs rom sp0 K g am i,
  NC L X EXC s m sp0 K -> getr regs 2 = wa sp0 -> getr regs 10 = wa (loc_addr L (LMem g)) -> getr regs 11 = wa i ->
  MT s g = Some (MUsed am) -> 0 <= i <= 31 -> 0 <= am_last am <= 31 -> 0 <= am_sc am < 48 -> 0 <= am_maplen am -> meta_bits am <= 2^64-1 ->
  0 <= am_avail am <= 2^32-1 -> 0 <= am_freed am <= 2^32-1 -> Z.testbit (am_avail am) i = false -> Z.testbit (am_freed am) i = false ->
  (forall q, am_next am = Some q -> In q (keys s)) -> 0 <= usage_of s (am_sc am) <= 2^64-1 ->
  (7 <= am_sc am < 39 -> 0 <= znth (am_sc am - 7) (st_bounces s) <= 255) ->
  exists R m1 canary, msteps SEGS (mkst regs (wa 0x518d0) m rom)
      (mkst R (wa (if (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am then 0x519e4 else 0x51a2c)) m1 rom) /\
    NC L X EXC s m1 sp0 K /\
    ntf_frame R m1 sp0 canary (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) /\
    FRM L s sp0 K m m1 /\ mem_grows m m1 /\
    getr R 10 = wa (loc_addr L (LMem g)) /\ getr R 12 = wa (am_sc am) /\ getr R 11 = wa (bv_swrap 32 (2^i)) /\
    getr R 13 = wa (bv_swrap 32 (Z.lor (am_avail am) (am_freed am))) /\
    (forall n, In n [3;4;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n))) /\
    ((Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am = true -> getr R 18 = wa 0x95ed8).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m regs rom sp0 K g am i N R2 R10 R11 Mg Ri Rl Rsc Rml RW Rav Rfr A2 A3 Hnx Rus Rbn.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  destruct Henv as (Egot & Etab & can & Rcan & Ecan).
  set (sc := am_sc am) in *.
  set (W := meta_bits am).
  assert (RW0 : 0 <= W) by (apply meta_bits_nonneg; lia).
  assert (ESC : SCW W = sc) by (unfold W; apply mb_scw; lia).
  set (csz := znth sc size_classes).
  assert (Rcsz : 0 <= csz <= 65535) by (pose proof (size_classes_range sc Rsc); unfold csz; lia).
  set (nxt := onum L (am_next am) mod 2^64).
  assert (Rnxt : 0 <= nxt <= 2^64-1) by (pose proof (Z.mod_pos_bound (onum L (am_next am)) (2^64) ltac:(lia)); unfold nxt; lia).
  assert (Mnx : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa nxt))).
  { pose proof (rx_next L s m EXC HR HEO HK g am Mg) as E. fold G in E. rewrite E. f_equal. f_equal. apply wa_eqm. unfold nxt. rewrite Z.mod_mod by lia. reflexivity. }
  destruct (rx_ctx_byte L s m EXC (873 + sc) HR Hctx ltac:(lia)) as (zb & Rzb & Mzb).
  set (bnc := if (7 <=? sc) && (sc <? 39) then znth (sc - 7) (st_bounces s) else zb).
  assert (Rbnc : 0 <= bnc <= 255).
  { unfold bnc. destruct ((7 <=? sc) && (sc <? 39)) eqn:E; [|exact Rzb]. apply andb_prop in E as [E1 E2]. apply Rbn. split; [apply Z.leb_le in E1 | apply Z.ltb_lt in E2]; lia. }
  assert (Mbnc : rdn SEGS m (wa (614977 + SCW W)) 1 = Some (word_to_le_bytes 1 (wa bnc))).
  { rewrite ESC. unfold bnc. destruct ((7 <=? sc) && (sc <? 39)) eqn:E.
    - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      pose proof (rx_bounce L s m EXC HR HEO Hctx (Z.to_nat (sc - 7)) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia.
      replace (614977 + sc) with (614984 + (sc - 7)) by ring. exact H.
    - replace (614977 + sc) with (614104 + (873 + sc)) by ring. exact Mzb. }
  set (usg := usage_of s sc).
  assert (Musg : rdn SEGS m (wa (614568 + 8 * SCW W)) 8 = Some (word_to_le_bytes 8 (wa usg))).
  { rewrite ESC. pose proof (rx_usage L s m EXC HR HEO Hctx (Z.to_nat sc) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. exact H. }
  assert (DP : dec_pre regs m G i W (am_avail am) (am_freed am) sp0 can csz nxt bnc usg).
  { constructor; try assumption; try lia.
    - apply (stk_ok_mono' m (wa sp0) K 1024 HSTK HK1).
    - exact (rx_avail L s m EXC HR HEO HK g am Mg).
    - exact (rx_freed L s m EXC HR HEO HK g am Mg).
    - exact (rx_bits L s m EXC HR HEO HK g am Mg).
    - rewrite ESC. exact (Etab sc Rsc).
    - unfold W. apply mb_land32; lia. }
  destruct (dec_arm regs m rom G i W (am_avail am) (am_freed am) sp0 can csz nxt bnc usg DP) as (R & Hms & POST & R18).
  assert (EDEC : dec_ok G i W (am_avail am) (am_freed am) csz nxt bnc usg = (Z.lor (am_freed am) (am_avail am) + bit i =? ones (am_last am)) && okay_to_free s g am).
  { apply dec_ok_model; try lia; try reflexivity.
    - split.
      + intros E. destruct (am_next am) as [q|] eqn:Eq.
        * destruct (sptr_eq_dec q g) as [->|Hne]; [reflexivity|]. exfalso.
          pose proof (Hnx q eq_refl) as Kq. destruct (HMP q Kq) as (Q1 & Q2 & _). pose proof (HMD g q Kg Kq (fun E' => Hne (eq_sym E'))) as D.
          unfold nxt in E. cbn [onum] in E. rewrite Z.mod_small in E by lia. fold G in D. lia.
        * exfalso. unfold nxt in E. cbn [onum] in E. rewrite Z.mod_0_l in E by lia. lia.
      + intros E. unfold nxt. rewrite E. cbn [onum]. fold G. apply Z.mod_small. lia.
    - intros B. unfold bnc. replace ((7 <=? sc) && (sc <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity. }
  rewrite EDEC in Hms, R18.
  set (m1 := dec_mem m regs sp0 can).
  destruct POST as (P10 & P11 & P12 & P13 & P9 & P2 & Poth).
  destruct (NC_stack L X EXC s m m1 sp0 K N (dec_mem_grows m regs sp0 can) (dec_mem_out m regs sp0 can ltac:(lia))) as (N1 & FR).
  exists R, m1, can. split; [exact Hms|]. split; [exact N1|]. split.
  { apply dec_frame; try assumption; first [ (clear - Hsp1 Hsp2 HK1; lia) | apply (stk_ok_mono' m (wa sp0) K 1024 HSTK HK1) | exact Ecan ]. }
  split; [exact FR|]. split; [exact (dec_mem_grows m regs sp0 can)|].
  split; [exact P10|]. split; [rewrite P12, ESC; reflexivity|]. split; [exact P11|]. split; [exact P13|]. split; [|exact R18].
  intros n Hn. apply Poth. clear - Hn. cbn [In] in Hn |- *. tauto.
Qed.
End SEGD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.

Lemma dec63_mem_eq : forall m regs G idx W avail freed sp0 canary, AXF_dec63z.dec63_mem_pd63 m regs G idx W avail freed sp0 canary = dec_mem m regs sp0 canary.
Proof. intros. unfold AXF_dec63z.dec63_mem_pd63, dec_mem. rewrite !wa_u. reflexivity. Qed.

Section SEGD63.
Context {fx : FPState}.

#[using="Type"] Theorem seg_dec63 : forall L X EXC s m regs rom sp0 K g am,
  NC L X EXC s m sp0 K -> getr regs 2 = wa sp0 -> getr regs 10 = wa (loc_addr L (LMem g)) -> getr regs 11 = wa 0 ->
  MT s g = Some (MUsed am) -> am_sc am = 63 -> am_last am = 0 -> 1 <= am_maplen am -> meta_bits am <= 2^64-1 ->
  am_avail am = 0 -> am_freed am = 0 ->
  exists R m1 canary, msteps SEGS (mkst regs (wa 0x518d0) m rom) (mkst R (wa 0x519e4) m1 rom) /\
    NC L X EXC s m1 sp0 K /\
    ntf_frame R m1 sp0 canary (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) /\
    FRM L s sp0 K m m1 /\ mem_grows m m1 /\
    getr R 10 = wa (loc_addr L (LMem g)) /\ getr R 12 = wa 63 /\ getr R 18 = wa 0x95ed8 /\
    (forall n, In n [3;4;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s m regs rom sp0 K g am N R2 R10 R11 Mg Hsc Hl Hml RW Hav Hfr.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z X s EXC (proj1 HK) HEX) as HEO.
  assert (Kg : In g (keys s)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  destruct Henv as (Egot & Etab & can & Rcan & Ecan).
  set (W := meta_bits am).
  assert (RW0 : 0 <= W) by (apply meta_bits_nonneg; lia).
  assert (ESC : SCW W = 63) by (unfold W; rewrite mb_scw by lia; exact Hsc).
  assert (EL : Z.land W 31 = 0) by (unfold W; rewrite mb_land31 by lia; exact Hl).
  assert (EL32 : Z.land W 32 <> 0) by (unfold W; apply mb_land32; lia).
  assert (DP : AXF_dec63z.dec63_pre regs m G 0 W 0 0 sp0 can).
  { constructor; try assumption; try lia.
    - apply (stk_ok_mono' m (wa sp0) K 1024 HSTK HK1).
    - rewrite <- Hav. exact (rx_avail L s m EXC HR HEO HK g am Mg).
    - rewrite <- Hfr. exact (rx_freed L s m EXC HR HEO HK g am Mg).
    - exact (rx_bits L s m EXC HR HEO HK g am Mg). }
  destruct (AXF_dec63z.dec63_pd63 regs m rom G 0 W 0 0 sp0 can DP) as (R & Hms & P2 & P9 & P10 & P12 & P14 & P15 & P16 & P18 & Poth).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_dec63.RES_pd63 fst snd]. set (E := Ez regs (AXF_dec63z.VALS_dec63 G 0 W 0 0 sp0 can)).
    assert (Z33 : bv_unsigned (ev E 33) = 0) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Z35 : bv_unsigned (ev E 35) = 0) by (apply zatom; [reflexivity | reflexivity | lia]).
    assert (Z36 : bv_unsigned (ev E 36) = 0) by (apply zatom; [reflexivity | reflexivity | lia]).
    repeat (first [apply Forall_nil | apply Forall_cons]); apply sc_br_z; cbn [zeval edenot]; rewrite ?Z33, ?Z34, ?Z35, ?Z36;
      rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    - litmods. change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W). rewrite ESC. reflexivity.
    - assert (E32 : W mod 32 = 0) by (change 32 with (2^5); rewrite <- Z.land_ones by lia; exact EL). rewrite E32. reflexivity.
    - rewrite (Z.mod_small W) by lia. litmods.
      assert (R32 : 0 <= Z.land W 32 < 2^64).
      { assert (N0 : 0 <= Z.land W 32) by (apply Z.land_nonneg; lia). split; [exact N0|].
        destruct (Z.eq_dec (Z.land W 32) 0) as [E0|E0]; [rewrite E0; lia|].
        pose proof (Z.log2_land W 32 ltac:(lia) ltac:(lia)) as L1. change (Z.log2 32) with 5 in L1.
        pose proof (Z.log2_spec (Z.land W 32) ltac:(lia)) as (_ & L2).
        assert (2^(Z.log2 (Z.land W 32) + 1) <= 2^6) by (apply Z.pow_le_mono_r; lia). lia. }
      rewrite (Z.mod_small (Z.land W 32)) by lia. apply Z.eqb_neq. exact EL32. }
  set (m1 := dec_mem m regs sp0 can).
  rewrite dec63_mem_eq in Hms. fold m1 in Hms.
  destruct (NC_stack L X EXC s m m1 sp0 K N (dec_mem_grows m regs sp0 can) (dec_mem_out m regs sp0 can ltac:(lia))) as (N1 & FR).
  exists R, m1, can. split; [exact Hms|]. split; [exact N1|]. split.
  { apply dec_frame; try assumption; first [ (clear - Hsp1 Hsp2 HK1; lia) | apply (stk_ok_mono' m (wa sp0) K 1024 HSTK HK1) | exact Ecan
                                           | (rewrite P2; f_equal; ring) ]. }
  split; [exact FR|]. split; [exact (dec_mem_grows m regs sp0 can)|].
  split; [exact P10|]. split; [rewrite P12; change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W); rewrite ESC; reflexivity|].
  split; [exact P18|].
  intros n Hn. apply Poth. clear - Hn. cbn [In] in Hn |- *. tauto.
Qed.
End SEGD63.

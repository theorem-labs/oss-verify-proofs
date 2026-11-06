(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "bind"; "UNIT"; "class_size"; "kreq"; "itree"; "IB"; "IRet"; "alloc_group"; "mslot"; "PGSZ"; "KMmapRW"; "ret"; "MUsed"; "get"; "halve_while_big"; "halve_while_even"; "initial_cnt"; "FGroup"; "RkMap"; "account_bounce"; "alloc_meta"; "alloc_slot"; "ameta"; "ask"; "free_meta"; "install_group"; "mmap_plan"; "region"; "st_mmap_counter"; "stride_of"; "usage_of"; "znth"; "M"; "SP"; "enframe"; "new_region"; "ones"; "page_round"; "set_mmap_counter"; "slot_junk"; "slot_zero"; "small_cnt"; "step_seq"; "zset"; "FModel"; "HActive"; "IAsk"; "MFree"; "am_last"; "am_set_links"; "bounce_idx"; "fail"; "frame"; "get_head"; "getm"; "links_of"; "mcheck"; "med_cnt_tab"; "mkAMeta"; "mkFrame"; "mkRegion"; "mkSlot"; "put"; "set_bounces"; "set_regions"; "set_usage"; "size_to_class"; "slotst"; "small_cnt_tab"; "st_bounces"; "st_free_meta_head"; "st_regions"; "st_seq"; "st_unmap_seq"; "st_usage"; "upd_slot"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "unit"; "pair"; "option"; "None"; "Some"; "S"; "nil"; "snd"; "cons"; "app"; "negb"; "nat"; "andb"; "fst"; "tt"; "false"; "true"; "list"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "mul"; "add"; "div"; "le"; "ltb"; "lt"; "eqb"; "land"; "even"; "leb"; "pow"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "yields"; "active_hd"; "MT"; "Inv"; "answer_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost"; "fm_post"; "free_ring_ok"; "ig_post"; "ab_post"; "nr_id"; "nr_post"; "ctr_post"; "ig_am"; "mm_aidx"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.AllocGroup.Nested"; "ne_p"; "ne_s3"; "ne_am"; "ne_hdr"; "ne_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfArith"; "need"; "@Corelib.Lists.ListDef"; "nth"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocGroupPost.AllocGroup.Mmap"; "mm_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FreeNtPost"; "fq_post"; "seq_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ImageDelta"; "set_hd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfGroup"; "group_post"; "slot_post"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfArith MallocWfInv MallocWfFrame MallocWfSlot MallocWfGroup
  ImageUpd ImageDelta TryAvailPost FreeNtPost MallocFastPost.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Definition ab_post (sc : Z) (s : astate) : astate := ltac2:(tb__ "0|2|
S53S0A1S1Lx;S35Vsc;A1S0S22R1S4cVs;A1A2S0S22R2S48Vs;A1M0A2S0S4fS1L_;S5dS5bS6fR2Z0A2A1S6dS68S4bVs;A1R2A2ZaA2A2S42S2eR3S4fS0L_;S6dS6aR1Z1A2M1Z64A2G1Z96X4fx2G0A3Vs;A2Vs;X4fx2Tb;Tuseq;Lk;Vs;X53x2").

Lemma account_bounce_eq sc s : ltac2:(tb__ "0|1|
S63S7S1S50S51S1A2M0A2S16Vsc;Vs;A2S9S1G0S52S51S1S5fS7eVsc;Vs;A2A4A3A3").
Proof. unfold account_bounce, ab_post, modify. destruct (bounce_idx sc); reflexivity. Qed.

Definition mm_pre (sc : Z) (s1 : astate) : astate := ltac2:(tb__ "0|0|
S8fS7eVsc;Vs1;A2A1").

Definition fm_post (m : sptr) (t : astate) : astate := ltac2:(tb__ "0|1|
S8eS7aVm;S32S54S2A1M0G0A2Vt;A3Vm;A2").

Definition free_ring_ok (m : sptr) (t : astate) : Prop := ltac2:(tb__ "0|3|
S2S63S53S2A1M0S49Vt;A1S55S2R1A2M1A3S64S65S63S2R2Vm;A3A1S66SbSbS66S2S2S64S63S53SbA1M2S77Vt;R4A2S55SbR2A2A3S64S63G0S5eG0G0S3aR2A1A3G1A3S64S65S63S2R1Vm;A3A1S65S63G2S77Vt;R1A2S54SbA1A3A1A2A2A2Lhp;A2Lxf;A2A2F_;Ffm;").

Lemma free_meta_eq m t : ltac2:(tb__ "0|1|
S7cVm;Vt;A2S63S7S1S50S51S1A2M0A2S1bVm;Vt;A2S9S1G0S52S51S1S5fS7bVm;Vt;A2A4A3A3F_;").
Proof.
  intros Hr. unfold free_meta, fm_post. rewrite (bind_eq _ _ t tt _ (setslot_eq t m (MFree None None))).
  apply queue_free_eq; [apply MT_upd_same|].
  intros fm Hfm. cbn [upd_meta set_metas st_free_meta_head] in Hfm.
  change (st_free_meta_head (upd_meta m (MFree None None) t)) with (st_free_meta_head t) in Hfm.
  destruct (Hr fm Hfm) as (Hne & xf & hp & Mf & Hhp & Hpm & Mhp).
  split; [exact Hne|]. exists xf, hp. rewrite (MT_upd_other m _ t fm Hne), (MT_upd_other m _ t hp Hpm). auto.
Qed.

Definition ig_am (mem : sptr) (sc cnt aidx maplen : Z) (sl : slotst) : ameta := ltac2:(tb__ "0|3|
S27Vaidx;A1S0S68S27S68Vcnt;Z1M0A2M1A1R1A2S0S3dS54S2A1M2G2Vmem;S68R2G0A2R1G1Vsc;Vmaplen;Vaidx;S8cS46Vsl;S74Vcnt;A1A3AaTfreed;Tavail;").

Definition ig_post (m : sptr) (sc cnt aidx maplen : Z) (mem : sptr) (sl : slotst) (t : astate) : astate := ltac2:(tb__ "0|1|
S44S2eVsc;S6aS21Vt;Vsc;A2Vcnt;A2S4dVt;A1A3Vt;A2S1S82Vmem;Vsc;Vcnt;Vaidx;Vmaplen;Vsl;A6S19S7aVm;SfR1A1R2A3S1S90Vsc;S55S2Vm;A2M0S7aVm;SfS34G0G0R2A3A1R1A3A3Tt2;Tam1;Tt1;").

Lemma install_group_eq m sc cnt aidx maplen mem sl t : ltac2:(tb__ "0|1|
S63S53S2A1S76Vt;Vsc;A2S54S2A1A3S63S7S1S50S51S1A2M0A2S1cVm;Vsc;Vcnt;Vaidx;Vmaplen;Vmem;Vsl;Vt;A8S9S1G0S52S51S1S5fS7dVm;Vsc;Vcnt;Vaidx;Vmaplen;Vmem;Vsl;Vt;A8A4A3A3F_;").
Proof.
  intros Hhd. unfold install_group, ig_post.
  rewrite (bind_eq _ _ t t t (get_eq t)).
  set (t1 := set_usage _ t).
  rewrite (bind_eq _ _ t tt t1) by reflexivity.
  set (am1 := ig_am mem sc cnt aidx maplen sl).
  change (mkAMeta None None mem (ones aidx - 1) (ones (cnt - 1) - ones aidx) (cnt - 1) sc maplen aidx (repeat sl (Z.to_nat cnt))) with am1.
  rewrite (bind_eq _ _ t1 tt _ (setm_eq t1 m am1)).
  set (t2 := upd_meta m (MUsed am1) t1).
  unfold queue. rewrite (bind_eq _ _ t2 _ t2 (get_links_eq t2 m (MUsed am1) (MT_upd_same m _ t1))).
  cbn [links_of am_prev am_next fst snd osptr_eqb andb am1 ig_am].
  rewrite (bind_eq _ _ t2 tt t2) by (apply massert_true_eq; reflexivity).
  rewrite (bind_eq _ _ t2 _ t2 (get_head_eq t2 sc)).
  assert (Hhd2 : active_hd t2 sc = None).
  { unfold t2, t1. rewrite active_hd_upd_meta. unfold active_hd in *. cbn. exact Hhd. }
  rewrite Hhd2.
  rewrite (bind_eq _ _ t2 tt _ (set_links_eq t2 m (MUsed am1) (Some m) (Some m) (MT_upd_same m _ t1))).
  cbn [with_links]. apply set_head_eq.
Qed.

Definition nr_post (len : Z) (t : astate) : astate := ltac2:(tb__ "0|0|
S43S5aS1eS4aVt;A1S59S1eS3fS15Vlen;S57S0A1S61A4S57S1eA1A3A3Vt;A2").
Definition nr_id (t : astate) : nat := length (st_regions t).
Lemma new_region_eq len t : ltac2:(tb__ "0|1|
S63S7S1S50S5cS1A2M0A2S26S15Vlen;Vt;A3S9S1G0S52S5cS1S7fVt;A1S80Vlen;Vt;A2A4A3A3").
Proof. reflexivity. Qed.

Definition ctr_post (t : astate) : astate := ltac2:(tb__ "0|1|
S29S70S6aS1fVt;A1Z1M0A2S68S73Z2Z20A2G0A2A2Vt;A2").

Definition mm_aidx (size cnt : Z) : Z := ltac2:(tb__ "0|4|
S68S6bS68Z1000S4A2Vsize;A2Z1M0A2S0S4fS0L_;M1S6dS68Vcnt;G0A2M2R1A2G2R1X4fx2S0G1S6dR1Z0M3A2G3R1X4fx2Ta1;Ta0;").

Lemma yields_of_eq {A} (m : M A) s a s1 : ltac2:(tb__ "0|3|
S63S7S1S50VA;S1A2M0A2Vm;Vs;A1M1S9S1G0S52VA;S1Va;Vs1;A4M2A3A3S75G0G1S57S50S6S0A2A1G2A4F_;").
Proof. intros ->. reflexivity. Qed.
Lemma yields_ask1 q s z : ltac2:(tb__ "0|1|
S79Vq;Vz;A2S75S50S4fS1A2S1aVq;Vs;A2S59S50S6S0A2M0S52S6S0Vq;Vz;A4S57G0A1A3S52S4fS1S5bS6fVz;Z0A2A1Vs;A4A4F_;").
Proof. intros Hz. cbn. auto. Qed.
Lemma yields_bind_one {A B} (m : M A) (k : A -> M B) s e a s1 b : ltac2:(tb__ "0|4|
S75S50VA;S1A2Vm;Vs;A1S59S50S6S0A2M0Ve;S57G0A1M1A3M2S52VA;S1Va;Vs1;A4A4S75S50VB;S1A2M3Vk;Va;Vs1;A2G1Vb;A4S75G3S3VA;VB;Vm;Vk;Vs;A5G2Vb;A4F_;F_;").
Proof. intros H1 H2. exact (yields_bind m k s [e] [] a s1 b H1 H2). Qed.

Lemma hwe_t f c u : ltac2:(tb__ "0|0|
S63S4fS71Vc;A1S61A3S6eVu;S69Z4Vc;A2A2S63S0S12S56Vf;A1Vc;Vu;A3S12Vf;S6bVc;Z2A2Vu;A3A3F_;F_;").
Proof. intros E H. cbn [halve_while_even]. rewrite E. replace (u <? 4 * c) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma hwe_f f c u : ltac2:(tb__ "0|0|
S67S63S4fS71Vc;A1S60A3S6cS69Z4Vc;A2Vu;A2A2S63S0S12S56Vf;A1Vc;Vu;A3Vc;A3F_;").
Proof.
  intros H. cbn [halve_while_even]. destruct H as [E|H]; [rewrite E; reflexivity|].
  replace (u <? 4 * c) with false by (symmetry; apply Z.ltb_ge; lia). destruct (Z.even c); reflexivity.
Qed.
Lemma hwb_t f c size : ltac2:(tb__ "0|0|
S6cS69Z10000S4A2S69Vsize;Vc;A2A2S63S0S11S56Vf;A1Vc;Vsize;A3S11Vf;S6bVc;Z2A2Vsize;A3A3F_;").
Proof. intros H. cbn [halve_while_big]. replace (65536 * UNIT <=? size * c) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
Lemma hwb_f f c size : ltac2:(tb__ "0|0|
S6eS69Vsize;Vc;A2S69Z10000S4A2A2S63S0S11S56Vf;A1Vc;Vsize;A3Vc;A3F_;").
Proof. intros H. cbn [halve_while_big]. replace (65536 * UNIT <=? size * c) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.
Lemma icnt_med sc u : ltac2:(tb__ "0|2|
S6cZ9Vsc;A2S63S0S13Vsc;Vu;A2S5Vsc;A1S0S11U8M0S12G0S22S70Vsc;Z3A2S3cA2Vu;A3R1A3S0S4fS0L_;S5dS6fR1Z1A2S72S6aS69R2R1A2S4A2S6bScZ2M1A2A2A2G1R1X4fx2Tcnt;Tsize;A3F_;").
Proof. intros H. unfold initial_cnt. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.
Lemma icnt_small sc u : ltac2:(tb__ "0|1|
S6eVsc;Z9A2S63S0S13Vsc;Vu;A2S5Vsc;A1S0S2cVsc;Vu;A2S0S4fS0L_;S5dS6fR1Z1A2S72S6aS69R2R1A2S4A2S6bScZ2M0A2A2A2G0R1X4fx2Tcnt;Tsize;A3F_;").
Proof. intros H. unfold initial_cnt. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma small_cnt_eq sc u (r0 r1 r2 : Z) : ltac2:(tb__ "0|4|
S63S62S0A1M0S8bG0S74Vsc;A1S47S57S0A1M1A4S59S0Vr0;S59S0Vr1;S59S0Vr2;G1A3A3A3A3S63S0S2cVsc;Vu;A2S4fS0L_;M2S5bS6dVu;S69Z4M3Vr0;A2A2A1Vr0;G2S5bS6dVu;S69G3Vr1;A2A2A1Vr1;Vr2;X4fx2X4fx2A3F_;").
Proof. intros E. unfold small_cnt. rewrite E. reflexivity. Qed.

Section AllocGroup.
  Variables (sc req : Z) (fuel : nat) (s : astate).

  Lemma alloc_group_unfold : ltac2:(tb__ "0|d|
S63S7S1S50S53S2A1M0S1A2A2SaS56Vfuel;A1Vsc;Vreq;Vs;A4S3G0G0S17G0G0S23G0A1M1Lom;R1S2S3S1G0S10S1S5Vsc;A1S0S21R2Vsc;A2S0S13Vsc;R1A2S0S4fG1L_;M2S6dS6bScZ2M3A2S6aS69R3R1A2S4A2A2S1dR4Vsc;Vreq;R1R2A5S50S0S0A2S3S51G0S16Vsc;A1S51S3S51G0S2dS51S3S4fG0S1aSdS58S0S0R3A3A1A1S4fG2S5bR1A1S3S51G0S1bR9A1S51SeG0S54S2A1A2M4L_;M5A4S3S5cG0S26S15S28S58S0S0R4A3A1A2S5cS3S1G0S10S1S3S51G0S41S29S70S6aS1fR1A1M6Z1M7A2S68S73G3Z20A2G7A2A2R1A2A1S51S5eS0S0R7A3S0S68S6bS68Z1000M8S4A2RbA2G7A2S0S4fS0L_;M9S6dS68R2G7A2MaR1A2GaR1X4fx2S0G9S6dR1Z0MbA2McGbR1X4fx2S0S3S51G0S1cR10Vsc;R4R1S6bS58S0S0RbA3G8A2S24R7GbA2S2bA7S51SeG0S55S2R11A2A2L_;A4Taidx;Ta1;Ta0;Tcnt;L_;A4Ls2;A4Lr;A4X4fx2Lok;A4L_;A4L_;A4Tplan;S68S6aS4S69R1R3A2A2S8A2S0S45R1A1S0S3S0G0S18Vfuel;R1R2A3S0G2GcS3S51G0S1bR8A1G5A4S3G0G0S38S30R2A1A1G0G0G1Lhj;R1S2S3S19G0S39R1A1S19S3S51G0S3bS6fS20R1A1S5R5A1A2ZbA2S51S3S1G0S10S1S3S2G0S25R4R6S68S5R7A1S8A2G6S14A5S2S3S51G0S1cReVsc;RaS68RaG7A2GbR1S2aA7S51SeG0S55S2RfA2A2L_;A4Lp;A4Ls3;A4L_;A4Lamg;A4Lg;S36G0S2fZ8A1A2X53x2Lhj;A4X4fx2Lidx;A4Tj;Ttotal;X4fx2Tcnt0;Tusage;Tsize;Ls0;A4Lm;G4X53x2Lom;Vs;A5A3").
  Proof using . reflexivity. Qed.

  Theorem ag_nometa tr s1 : ltac2:(tb__ "0|3|
S75S50S53S2A1M0S1A2M1S17Vs;A1Vtr;S52G0S1S54S2A1Vs1;A4M2A4S75G1SaS56Vfuel;A1Vsc;Vreq;Vs;A4Vtr;G2A4F_;").
  Proof using .
    intros Hm. rewrite alloc_group_unfold. rewrite <- (app_nil_r tr).
    eapply yields_bind; [exact Hm|]. apply yields_ret.
  Qed.

  Variables (m : sptr) (tr0 : list (kreq * Z)) (s1 : astate).
  Hypothesis Hm : ltac2:(tb__ "0|1|
S75S50S53S2A1M0S1A2S17Vs;A1Vtr0;S52G0S1S55S2Vm;A2Vs1;A4A4").
  Let size : Z := class_size sc.
  Let usage : Z := usage_of s1 sc.
  Let cnt0 : Z := initial_cnt sc usage.

  Section Mmap.
    Hypothesis Harm : ltac2:(tb__ "0|0|
S6eS6bScZ2A2S6aS69Vsize;Vcnt0;A2S4A2A2").
    Let plan : ltac2:(tb__ "0|0|
S50S0S0A2") := ltac2:(tb__ "0|0|
S1dVs1;Vsc;Vreq;Vcnt0;Vusage;A5").
    Let s2 : astate := mm_pre sc s1.

    Lemma mmap_prefix_eq : ltac2:(tb__ "0|1|
S63S7S1S50S4fS1A2M0A2S3S1S4fS10S1S5Vsc;A1S0S21R2Vsc;A2S0S13Vsc;R1A2S0S4fS23S4fA1L_;S6dS6bScZ2A2S6aS69R3R1A2S4A2A2S1dR4Vsc;Vreq;R1R2A5S50S0S0A2S3S51S4fS16Vsc;A1S51S3S51S4fS2dS51S3S4fS4fS1aSdS58S0S0R3A3A1A1S4fS4fSeS4fR1A2Lok;R1A1Lok;A4L_;A4L_;A4Tplan;SeS4fS60A2X4fx2Tcnt0;Tusage;Tsize;Ls0;Vs1;A5S31S1G0SdS58S0S0Vplan;A3A1Vs2;S0S9S1G0S52S4fS1S5bS6fR1Z0A2A1Vs2;A4A3Lz;A5A3").
    Proof using Harm.
      rewrite (bind_eq _ _ s1 s1 s1 (get_eq s1)). cbn zeta.
      replace (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT) with true by (symmetry; apply Z.ltb_lt; exact Harm).
      rewrite (bind_eq _ _ s1 tt _ (account_bounce_eq sc s1)).
      rewrite (bind_eq _ _ _ tt _ (step_seq_eq _)). reflexivity.
    Qed.

    Theorem ag_mmap_refused : ltac2:(tb__ "0|2|
S7cVm;Vs2;A2S75S50S53S2A1M0S1A2SaS56Vfuel;A1Vsc;Vreq;Vs;A4S5aS50S6S0A2M1Vtr0;S59G1S52S6S0SdS58S0S0Vplan;A3A1Z0A4S57G1A1A3A3S52G0S1S54S2A1S7bVm;Vs2;A2A4A4F_;").
    Proof using Harm Hm.
      intros Hr. rewrite alloc_group_unfold. eapply yields_bind; [exact Hm|]. cbn beta iota.
      eapply yields_bind0; [apply yields_of_eq; apply get_eq|]. cbn beta zeta.
      replace (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT) with true by (symmetry; apply Z.ltb_lt; exact Harm).
      eapply yields_bind0; [apply yields_of_eq; apply account_bounce_eq|].
      eapply yields_bind0; [apply yields_of_eq; apply step_seq_eq|].
      eapply yields_bind_one; [apply yields_ask1; exact I|]. cbn [Z.eqb negb].
      eapply yields_bind0; [apply yields_of_eq; apply (free_meta_eq m s2 Hr)|]. apply yields_ret.
    Qed.

    Let s3 : astate := ltac2:(tb__ "0|0|
S81S80S28S58S0S0Vplan;A3A1Vs2;A2A1").
    Definition mm_post : astate := ltac2:(tb__ "0|1|
S7dVm;Vsc;S5eS0S0Vplan;A3M0S83Vsize;G0A2S6bS58S0S0Vplan;A3Z1000A2S24S7fVs2;A1Z0A2S2bVs3;A8").

    Theorem ag_mmap_granted z : ltac2:(tb__ "0|2|
S65S63S0Vz;Z0A3A1S63S53S2A1M0S76Vs1;Vsc;A2S54S2A1A3S75S50G0S1A2SaS56Vfuel;A1Vsc;Vreq;Vs;A4S5aS50S6S0A2M1Vtr0;S59G1S52S6S0SdS58S0S0Vplan;A3A1Vz;A4S57G1A1A3A3S52G0S1S55S2Vm;A2S8dA4A4F_;F_;").
    Proof using Harm Hm.
      intros Hz Hhd. rewrite alloc_group_unfold. eapply yields_bind; [exact Hm|]. cbn beta iota.
      eapply yields_bind0; [apply yields_of_eq; apply get_eq|]. cbn beta zeta.
      replace (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT) with true by (symmetry; apply Z.ltb_lt; exact Harm).
      eapply yields_bind0; [apply yields_of_eq; apply account_bounce_eq|].
      eapply yields_bind0; [apply yields_of_eq; apply step_seq_eq|].
      eapply yields_bind_one; [apply yields_ask1; exact I|].
      replace (z =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). cbn [negb].
      eapply yields_bind0; [apply yields_of_eq; apply new_region_eq|].
      eapply yields_bind0; [apply yields_of_eq; apply get_eq|].
      eapply yields_bind0; [apply yields_of_eq; apply put_eq|].
      assert (Hhd3 : active_hd s3 sc = None).
      { unfold s3, ctr_post, nr_post, s2, mm_pre, seq_post, ab_post. unfold active_hd in *.
        destruct (bounce_idx sc); [destruct (negb _ && _)|]; destruct (st_seq _ =? 255); cbn; exact Hhd. }
      eapply yields_bind0; [apply yields_of_eq; exact (install_group_eq m sc (fst plan) _ (snd plan / 4096) (SP (nr_id s2) 0) slot_zero s3 Hhd3)|].
      apply yields_ret.
    Qed.
  End Mmap.

  Section Nested.
    Hypothesis Harm : ltac2:(tb__ "0|0|
S6cS6aS69Vsize;Vcnt0;A2S4A2S6bScZ2A2A2").
    Let total : Z := ltac2:(tb__ "0|0|
S68S6aS4S69Vcnt0;Vsize;A2A2S8A2").
    Let j : Z := size_to_class total.
    Variables (trR : list (kreq * Z)) (idx : Z) (s2 : astate).
    Hypothesis HR : ltac2:(tb__ "0|0|
S75S50S0S1A2S18Vfuel;Vj;Vtotal;Vs1;A4VtrR;S52S0S1Vidx;Vs2;A4A4").

    Theorem ag_nest_refused : ltac2:(tb__ "0|2|
S6eVidx;Z0A2S7cVm;Vs2;A2S75S50S53S2A1M0S1A2SaS56Vfuel;A1Vsc;Vreq;Vs;A4S5aS50S6S0A2M1Vtr0;S5aG1VtrR;S57G1A1A3A3S52G0S1S54S2A1S7bVm;Vs2;A2A4A4F_;F_;").
    Proof using HR Harm Hm.
      intros Hneg Hr. rewrite alloc_group_unfold. eapply yields_bind; [exact Hm|]. cbn beta iota.
      eapply yields_bind0; [apply yields_of_eq; apply get_eq|]. cbn beta zeta.
      replace (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT) with false by (symmetry; apply Z.ltb_ge; exact Harm).
      eapply yields_bind; [exact HR|].
      replace (idx <? 0) with true by (symmetry; apply Z.ltb_lt; exact Hneg).
      eapply yields_bind0; [apply yields_of_eq; apply (free_meta_eq m s2 Hr)|]. apply yields_ret.
    Qed.

    Variables (g : sptr) (amg : ameta).
    Hypothesis Hg : ltac2:(tb__ "0|0|
S63S53S2A1S76Vs2;Vj;A2S55S2Vg;A2A3").
    Hypothesis Mg : ltac2:(tb__ "0|0|
S63S53SbA1S77Vs2;Vg;A2S55SbSfVamg;A1A2A3").
    Hypothesis Hstride : ltac2:(tb__ "0|0|
S63S0S20Vamg;A1S5Vj;A1A3").
    Hypothesis Hidx : ltac2:(tb__ "0|0|
S64S6cZ0Vidx;A2S6cVidx;S33Vamg;A1A2A2").

    Definition ne_hdr : Z * Z := ltac2:(tb__ "0|0|
S52S0S0S6aVidx;Zc0A2S6bS69S20Vamg;A1Vidx;A2S4A2A4").
    Definition ne_am : ameta := ltac2:(tb__ "0|0|
S4eVamg;Vidx;S40S55S50S0S0A2S88A2S55S37S3eZ0S68S5Vj;A1S8A2S14A3A2A2A3").
    Definition ne_s3 : astate := ltac2:(tb__ "0|0|
S7aVg;SfS87A1Vs2;A3").
    Definition ne_p : sptr := slot_start amg idx.

    Lemma enframe_nested_eq : ltac2:(tb__ "0|1|
S63S7S1S50S2S1A2M0A2S25Vg;Vidx;S68S5Vj;A1S8A2S1fVs2;A1S14Vs2;A6S9S1G0S52S2S1S85S86A4A3A3").
    Proof using Hidx Hstride Mg.
      unfold enframe. rewrite (bind_eq _ _ s2 amg s2 (getm_eq s2 g amg Mg)).
      rewrite (bind_eq _ _ s2 tt s2).
      2:{ unfold mcheck. replace ((0 <=? idx) && (idx <=? am_last amg)) with true; [reflexivity|].
          symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le]; lia. }
      cbn zeta. rewrite Hstride.
      replace ((class_size j - IB - (class_size j - IB)) / UNIT) with 0 by (rewrite Z.sub_diag; reflexivity).
      cbn [Z.eqb]. rewrite (bind_eq _ _ s2 0 s2 (ret_eq 0 s2)). cbn [Z.ltb].
      rewrite (bind_eq _ _ s2 tt s2) by (apply massert_true_eq; reflexivity).
      replace (class_size j - IB - UNIT * 0 - (class_size j - IB)) with 0 by lia. cbn [Z.leb Z.eqb].
      rewrite (bind_eq _ _ s2 tt _ (setm_eq s2 g _)).
      unfold ne_s3, ne_am, ne_hdr, ne_p. rewrite Hstride. rewrite Z.mul_0_r. rewrite padd_0. reflexivity.
    Qed.

    Definition ne_post : astate := ltac2:(tb__ "0|0|
S7dVm;Vsc;Vcnt0;S68Vcnt0;Z1A2Z0S85S2aS86A8").

    Theorem ag_nest_granted : ltac2:(tb__ "0|2|
S6cZ0Vidx;A2S63S53S2A1M0S76Vs2;Vsc;A2S54S2A1A3S75S50G0S1A2SaS56Vfuel;A1Vsc;Vreq;Vs;A4S5aS50S6S0A2M1Vtr0;S5aG1VtrR;S57G1A1A3A3S52G0S1S55S2Vm;A2S89A4A4F_;F_;").
    Proof using HR Harm Hg Hidx Hm Hstride Mg.
      intros Hpos Hhd. rewrite alloc_group_unfold. eapply yields_bind; [exact Hm|]. cbn beta iota.
      eapply yields_bind0; [apply yields_of_eq; apply get_eq|]. cbn beta zeta.
      replace (PGSZ / 2 <? class_size sc * initial_cnt sc (usage_of s1 sc) + UNIT) with false by (symmetry; apply Z.ltb_ge; exact Harm).
      eapply yields_bind; [exact HR|].
      replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; exact Hpos).
      eapply yields_bind0; [apply yields_of_eq; apply get_head_eq|].
      change (size_to_class (UNIT + initial_cnt sc (usage_of s1 sc) * class_size sc - IB)) with j. rewrite Hg.
      eapply yields_bind0; [apply yields_of_eq; apply (getm_eq s2 g amg Mg)|].
      eapply yields_bind0. { apply yields_of_eq. unfold mcheck. rewrite Hstride, Z.eqb_refl. reflexivity. }
      eapply yields_bind0; [apply yields_of_eq; apply get_eq|].
      change (UNIT + initial_cnt sc (usage_of s1 sc) * class_size sc - IB) with total.
      eapply yields_bind0; [apply yields_of_eq; apply enframe_nested_eq|].
      assert (Hhd3 : active_hd ne_s3 sc = None) by (unfold ne_s3; rewrite active_hd_upd_meta; exact Hhd).
      eapply yields_bind0; [apply yields_of_eq; exact (install_group_eq m sc _ _ 0 ne_p slot_junk ne_s3 Hhd3)|].
      apply yields_ret.
    Qed.
  End Nested.
End AllocGroup.

Theorem alloc_group_post X U s sc req fuel tr r : ltac2:(tb__ "0|2|
S78VX;S54S50S2S0A2A1VU;Vs;A4S64S6cZ0M0Vsc;A2S6eVsc;Z30A2A2S6cG0Vreq;A2S6cS6aVreq;S8A2S5Vsc;A1A2S84S8aVsc;A1S56Vfuel;A1A2S63S53S2A1M1S76Vs;Vsc;A2S54S2A1A3S75S50G1S1A2SaVfuel;Vsc;Vreq;Vs;A4Vtr;Vr;A4S91VX;VU;Vs;Vsc;Vreq;Vr;A6F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hreq Hfit Hf Hhd Hy.
  eapply itok_yields; [|exact Hy].
  apply (proj2 (alloc_mutual fuel) X U s sc req); auto.
Qed.

Theorem alloc_slot_post X U s sc req fuel tr r : ltac2:(tb__ "0|1|
S78VX;S54S50S2S0A2A1VU;Vs;A4S64S6cZ0M0Vsc;A2S6eVsc;Z30A2A2S6cG0Vreq;A2S6cS6aVreq;S8A2S5Vsc;A1A2S84S8aVsc;A1Vfuel;A2S75S50S0S1A2S18Vfuel;Vsc;Vreq;Vs;A4Vtr;Vr;A4S92VX;VU;Vs;Vsc;Vreq;Vr;A6F_;F_;F_;F_;F_;F_;").
Proof.
  intros HI Hsc Hreq Hfit Hf Hy.
  eapply itok_yields; [|exact Hy].
  apply (proj1 (alloc_mutual fuel) X U s sc req); auto.
Qed.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "astate"; "mslot"; "kreq"; "itree"; "IRet"; "PGSZ"; "region"; "bind"; "alloc_meta"; "MFree"; "links_of"; "mkRegion"; "padd"; "st_regions"; "with_links"; "ret"; "SP"; "set_regions"; "AREA_HDR"; "MRaw"; "set_free_meta_head"; "st_avail_meta_count"; "BrkCur"; "HFreeMeta"; "META_SIZE"; "brkst"; "get"; "lupd"; "set_avail_meta"; "set_avail_meta_area_count"; "set_avail_meta_areas"; "set_avail_meta_count"; "st_brk"; "st_free_meta_head"; "IAsk"; "KBrkGrow"; "KMprotect"; "M"; "RkBrk"; "RkMap"; "RkMetaRes"; "ameta"; "prid"; "put"; "rg_len"; "set_brk"; "st_avail_meta"; "BrkDead"; "BrkNever"; "KBrkQuery"; "KGuard"; "KMmapNone"; "area_from_brk"; "area_from_mmap"; "ask"; "dequeue_head"; "get_head"; "get_links"; "modify"; "open_area"; "poff"; "rg_kind"; "rg_live"; "rg_rw"; "set_head"; "set_init_done"; "set_links"; "set_meta_alloc_shift"; "set_next"; "set_prev"; "setslot"; "st_meta_alloc_shift"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "iff"; "@Corelib.Init.Datatypes"; "option"; "Some"; "prod"; "bool"; "pair"; "nil"; "unit"; "cons"; "None"; "tt"; "false"; "true"; "list"; "snd"; "app"; "fst"; "negb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "yields"; "Inv"; "usedX"; "memb"; "answer_ok"; "chain"; "flinks"; "keys"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.Arms"; "s0"; "res_r"; "s_dead"; "take"; "r_RES"; "res_n"; "tr_RES"; "t_RES1"; "am_spec_post"; "s_RESok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "ub_same"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "mul"; "sub"; "add"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.Arms.Kernel.AR"; "ar_p"; "ar_rg"; "s_ARok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "open_st"; "am_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.Arms.Avail"; "am_q"; "s_AV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.Arms.Kernel.NoArea.BK"; "bk_p"; "bk_rg"; "r_BK"; "s_BKok"; "tr_BK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.Arms.Kernel.NoArea.IN"; "in_p"; "in_r"; "r_IN"; "s_INok"; "tr_IN"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.Arms.Head.H23"; "s_H23a"; "s_H23"; "s_H23b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost.Arms.Head.H1"; "s_H1"; "@Stdlib.Lists.List"; "In"; "last"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfMeta.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Section Stepping.
  Lemma bind_eq {A B} (m : M A) (k : A -> M B) s a s1 : ltac2:(tb__ "0|1|
S49S4S1S51VA;S1A2M0A2Vm;Vs;A1S5S1G0S53VA;S1Va;Vs1;A4A3A3S49S4S1S51VB;S1A2A2S8VA;VB;Vm;Vk;Vs;A5Vk;Va;Vs1;A2A3F_;").
  Proof. intros H. unfold bind. rewrite H. reflexivity. Qed.

  Lemma bind_ask {B} (q : kreq) (k : bool -> M B) s : ltac2:(tb__ "0|1|
S49S4S1S51VB;S1A2M0A2S8S52VB;S37Vq;A1Vk;Vs;A5S23S1G0Vq;Vs;S60Vk;S5fS76R1Z0A2A1Vs;A2Lz;A5A3").
  Proof. reflexivity. Qed.

  Lemma ret_eq {A} (a : A) s : ltac2:(tb__ "0|1|
S49S4S1S51VA;S1A2M0A2S10VA;Va;Vs;A3S5S1G0S53VA;S1Va;Vs;A4A3A3"). Proof. reflexivity. Qed.
  Lemma get_eq s : ltac2:(tb__ "0|1|
S49S4S1S51S1S1A2M0A2S1bVs;A1S5S1G0S53S1S1Vs;Vs;A4A3A3"). Proof. reflexivity. Qed.
  Lemma modify_eq f s : ltac2:(tb__ "0|1|
S49S4S1S51S55S1A2M0A2S3bVf;Vs;A2S5S1G0S53S55S1S58Vf;Vs;A1A4A3A3"). Proof. reflexivity. Qed.
  Lemma put_eq s s0 : ltac2:(tb__ "0|1|
S49S4S1S51S55S1A2M0A2S2cVs;Vs0;A2S5S1G0S53S55S1S58Vs;A4A3A3"). Proof. reflexivity. Qed.

  Lemma get_links_eq s p x : ltac2:(tb__ "0|3|
S49S4fS2A1S61Vs;Vp;A2S50S2Vx;A2A3S49S4S1S51S51S4fS0A1M0G0A2M1S1A2M2A2S3aVp;Vs;A2S5S1G2S53G1S1SbVx;A1Vs;A4A3A3F_;").
  Proof. intros H. unfold get_links. rewrite (bind_eq _ _ s s s (get_eq s)). unfold MT in H. rewrite H. reflexivity. Qed.
  Lemma set_links_eq s p x pr nx : ltac2:(tb__ "0|1|
S49S4fS2A1S61Vs;Vp;A2S50S2Vx;A2A3S49S4S1S51S55S1A2M0A2S43Vp;Vpr;Vnx;Vs;A4S5S1G0S53S55S1S58S74Vp;SfVx;Vpr;Vnx;A3Vs;A3A4A3A3F_;").
  Proof. intros H. unfold set_links. rewrite (bind_eq _ _ s s s (get_eq s)). unfold MT in H. rewrite H. reflexivity. Qed.
  Lemma set_prev_eq s p x pr : ltac2:(tb__ "0|2|
S49S4fS2A1S61Vs;Vp;A2S50S2Vx;A2A3S49S4S1S51S55S1A2M0A2S46Vp;Vpr;Vs;A3S5S1G0S53S55S1S58S74Vp;SfVx;Vpr;S5cS4fS0A1M1G1SbVx;A1A3A3Vs;A3A4A3A3F_;").
  Proof. intros H. unfold set_prev. rewrite (bind_eq _ _ s _ s (get_links_eq s p x H)). apply set_links_eq. exact H. Qed.
  Lemma set_next_eq s p x nx : ltac2:(tb__ "0|2|
S49S4fS2A1S61Vs;Vp;A2S50S2Vx;A2A3S49S4S1S51S55S1A2M0A2S45Vp;Vnx;Vs;A3S5S1G0S53S55S1S58S74Vp;SfVx;S5eS4fS0A1M1G1SbVx;A1A3Vnx;A3Vs;A3A4A3A3F_;").
  Proof. intros H. unfold set_next. rewrite (bind_eq _ _ s _ s (get_links_eq s p x H)). apply set_links_eq. exact H. Qed.

  Lemma get_head_free_eq s : ltac2:(tb__ "0|2|
S49S4S1S51S4fS0A1M0S1A2M1A2S39S18Vs;A2S5S1G1S53G0S1S22Vs;A1Vs;A4A3A3").
  Proof. reflexivity. Qed.
  Lemma set_head_free_eq s v : ltac2:(tb__ "0|1|
S49S4S1S51S55S1A2M0A2S41S18Vv;Vs;A3S5S1G0S53S55S1S58S15Vv;Vs;A2A4A3A3").
  Proof. reflexivity. Qed.

  Lemma yields_ask {A} q snap (k : Z -> itree astate A) z tr a : ltac2:(tb__ "0|0|
S66Vq;Vz;A2S62VA;Vk;Vz;A1Vtr;Va;A4S62VA;S23S1VA;Vq;Vsnap;Vk;A5S56S51S3S60A2S53S3S60Vq;Vz;A4Vtr;A3Va;A4F_;F_;").
  Proof. intros Hz Hy. cbn. auto. Qed.
  Lemma yields_ret {A} (a : A) : ltac2:(tb__ "0|0|
S62VA;S5S1VA;Va;A3S54S51S3S60A2A1Va;A4").
  Proof. reflexivity. Qed.
End Stepping.

Lemma MT_set_free_meta_head v s q : ltac2:(tb__ "0|0|
S49S4fS2A1S61S15Vv;Vs;A2Vq;A2S61Vs;Vq;A2A3").
Proof. reflexivity. Qed.
Lemma MT_set_init_done v s q : ltac2:(tb__ "0|0|
S49S4fS2A1S61S42Vv;Vs;A2Vq;A2S61Vs;Vq;A2A3").
Proof. reflexivity. Qed.

Section Arms.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S63VX;VR;VU;Vs;A4").

  Definition s0 : astate := set_init_done true s.

  Lemma alloc_meta_unfold : ltac2:(tb__ "0|3|
S49S4S1S51S4fS0A1M0S1A2A2S9Vs;A1S8G0G0S38S18A1G0G0S26G0A1M1Lfm;R1S0S10G0S50S0R1A2A2Lm;S8S1G0S1bS1S8S52G0S52S26S52A1M2L_;S7aZ0S16R1A1A2S10S52S5aA2S8S52S52S35S52S8S52S52S36S52S52G2Lrs;R1S3cR2A1S10S52S59A2X52x2Lrs;A4Lnu;A4X52x2S52S52G1L_;S5fR1A1S10G0S57S0A1A2S8S1G0S1bS1S2fR1A1S0S8S55G0S2cS1dSdR1S19A2S20S78S16R2A1Z1A2R2A2A2A1S55S8S55G0S47R2S14A2S55S10G0S50S0R3A2A2L_;A4L_;A4Tm;Ls2;A4X52x2Lok;A4Ls1;A4X4fx2Lfm;S6aA5A3").
  Proof using . unfold alloc_meta. rewrite (bind_eq _ _ s tt s0 (modify_eq _ _)). reflexivity. Qed.

  Definition am_spec_post (r : option sptr * astate) : Prop := ltac2:(tb__ "0|5|
S5cS4fS0A1M0S1Vr;A3S1G0OLx;S5eG0S1Vr;A3S0S4aS63S56S0R1VX;A3VR;VU;R2A4S4aS49S52S65R1VX;A2S59A3S4aS91S0R1S69R2A1A3S4aS4dS49S4fS2A1M1S61R2R1A2M2S50S2S14A2A3S49G1G2S50S2SaS57S0A1M3G3A2A2A3A2S4aS7fVs;R2A2S4aS0S2aS4eS64S56S0R3VX;A3R4R2R1A4S64VX;Vs;R2R1A4M4A2Fam;Fg;S75Vs;R2A2A2A2A2A2A2A2Lm;S4aS63VX;VR;VU;R1A4S4aS7fVs;R1A2S4aS0S2aS4eS64VX;R3R2R1A4G4A2Fam;Fg;S75Vs;R1A2A2A2A2X4fx2Ts';").

  Lemma am_spec_of_yields tr r : ltac2:(tb__ "0|0|
S62S51S4fS0A1S1A2S9Vs;A1Vtr;Vr;A4S72Vr;A1F_;").
  Proof using HI.
    intros Hy. apply (itok_yields (alloc_meta s) am_spec_post tr r); [|exact Hy].
    apply (alloc_meta_spec X R U); [exact HI | |].
    - intros s' H1 H2 H3 H4. cbn. auto.
    - intros m s' H1 H2 H3 H4 H5 H6 H7. cbn. repeat (split; [assumption|]). assumption.
  Qed.

  Section Head.
    Variable m : sptr.
    Hypothesis Hhd : ltac2:(tb__ "0|0|
S49S4fS0A1S22Vs;A1S50S0Vm;A2A3").
    Variable xm : mslot.
    Hypothesis Hm : ltac2:(tb__ "0|0|
S49S4fS2A1S61Vs;Vm;A2S50S2Vxm;A2A3").

    Let Hm0 : MT s0 m = Some xm. Proof. unfold s0. rewrite MT_set_init_done. exact Hm. Qed.

    Section H1.
      Hypothesis Hnx : ltac2:(tb__ "0|1|
S49S4fS0A1M0S5cG0G0SbVxm;A1A3S50S0Vm;A2A3").
      Definition s_H1 : astate := ltac2:(tb__ "0|1|
S74Vm;SfVxm;S57S0A1M0G0A3S15G0S6aA2A3").

      Lemma yields_H1 : ltac2:(tb__ "0|1|
S62S51S4fS0A1M0S1A2S9Vs;A1S54S51S3S60A2A1S53G0S1S50S0Vm;A2S90A4A4").
      Proof using Hhd Hm0 Hnx.
        rewrite alloc_meta_unfold. unfold dequeue_head.
        unfold bind at 1. unfold bind at 1. rewrite get_head_free_eq. cbn [ibind st_free_meta_head s0 set_init_done]. rewrite Hhd.
        unfold dequeue. unfold bind at 1. unfold bind at 1.
        rewrite (get_links_eq s0 m xm Hm0). cbn [ibind].
        rewrite Hnx. cbn [osptr_eqb]. rewrite sptr_eqb_refl. unfold bind at 1.
        rewrite set_head_free_eq. cbn [ibind].
        rewrite (set_links_eq (set_free_meta_head None s0) m xm) by (rewrite MT_set_free_meta_head; exact Hm0).
        cbn [ibind]. reflexivity.
      Qed.
    End H1.

    Section H23.
      Variables p n : sptr.
      Hypothesis Hlk : ltac2:(tb__ "0|1|
S49S51S4fS0A1M0G0A2SbVxm;A1S53G0G0S50S0Vp;A2S50S0Vn;A2A4A3").
      Hypothesis Hnm : n <> m.
      Hypothesis Hpm : p <> m.
      Variable xp : mslot.
      Hypothesis Hp : ltac2:(tb__ "0|0|
S49S4fS2A1S61Vs;Vp;A2S50S2Vxp;A2A3").

      Definition s_H23a : astate := ltac2:(tb__ "0|1|
S74Vp;SfVxp;S5eS4fS0A1M0G0SbVxp;A1A3S50S0Vn;A2A3S6aA3").

      Variable xn1 : mslot.
      Hypothesis Hn1 : ltac2:(tb__ "0|0|
S49S4fS2A1S61S8dVn;A2S50S2Vxn1;A2A3").
      Definition s_H23b : astate := ltac2:(tb__ "0|1|
S74Vn;SfVxn1;S50S0Vp;A2S5cS4fS0A1M0G0SbVxn1;A1A3A3S8dA3").
      Definition s_H23 : astate := ltac2:(tb__ "0|1|
S74Vm;SfVxm;S57S0A1M0G0A3S15S50S0Vn;A2S8fA2A3").

      Lemma yields_H23 : ltac2:(tb__ "0|1|
S62S51S4fS0A1M0S1A2S9Vs;A1S54S51S3S60A2A1S53G0S1S50S0Vm;A2S8eA4A4").
      Proof using Hhd Hlk Hm0 Hn1 Hnm Hp Hpm.
        rewrite alloc_meta_unfold. unfold dequeue_head.
        unfold bind at 1. unfold bind at 1. rewrite get_head_free_eq. cbn [ibind st_free_meta_head s0 set_init_done]. rewrite Hhd.
        unfold dequeue. unfold bind at 1. unfold bind at 1.
        rewrite (get_links_eq s0 m xm Hm0). cbn [ibind].
        rewrite Hlk. cbn [fst snd osptr_eqb].
        replace (sptr_eqb n m) with false by (symmetry; apply sptr_eqb_neq; exact Hnm).
        unfold bind at 1. unfold bind at 1.
        rewrite (set_next_eq s0 p xp (Some n)) by (unfold s0; rewrite MT_set_init_done; exact Hp). cbn [ibind]. fold s_H23a.
        unfold bind at 1. rewrite (set_prev_eq s_H23a n xn1 (Some p) Hn1). cbn [ibind]. fold s_H23b.
        unfold bind at 1. rewrite get_head_free_eq. cbn [ibind].
        replace (st_free_meta_head s_H23b) with (Some m) by (unfold s_H23b, s_H23a, s0; cbn; rewrite Hhd; reflexivity).
        cbn [osptr_eqb]. rewrite sptr_eqb_refl. rewrite set_head_free_eq. cbn [ibind].
        rewrite (set_links_eq (set_free_meta_head (Some n) s_H23b) m xm).
        2:{ rewrite MT_set_free_meta_head. unfold s_H23b. rewrite MT_upd_other by (intros E; exact (Hnm (eq_sym E)) || exact (Hnm E) || congruence).
            unfold s_H23a. rewrite MT_upd_other by congruence. exact Hm0. }
        cbn [ibind]. reflexivity.
      Qed.
    End H23.
  End Head.

  Section Avail.
    Hypothesis Hhd : st_free_meta_head s = None.
    Hypothesis Hcnt : 0 < st_avail_meta_count s.
    Definition am_q : sptr := st_avail_meta s.
    Definition s_AV : astate := ltac2:(tb__ "0|0|
S74S80S14S1dSdS80S19A2S20S78S16Vs;A1Z1A2S6aA2A2A3").

    Lemma yields_AV : ltac2:(tb__ "0|1|
S62S51S4fS0A1M0S1A2S9Vs;A1S54S51S3S60A2A1S53G0S1S50S0S80A2S81A4A4").
    Proof using Hcnt Hhd.
      rewrite alloc_meta_unfold. unfold dequeue_head.
      unfold bind at 1. unfold bind at 1. rewrite get_head_free_eq. cbn [ibind st_free_meta_head s0 set_init_done]. rewrite Hhd.
      unfold bind at 1. rewrite ret_eq. cbn [ibind].
      unfold bind at 1. rewrite get_eq. cbn [ibind].
      replace (0 <? st_avail_meta_count s0) with true by (symmetry; apply Z.ltb_lt; exact Hcnt).
      unfold bind at 1. rewrite ret_eq. cbn [ibind negb].
      unfold bind at 1. rewrite get_eq. cbn [ibind].
      unfold bind at 1. rewrite put_eq. cbn [ibind].
      unfold setslot. rewrite modify_eq. cbn [ibind]. reflexivity.
    Qed.
  End Avail.

  Ltac am_compute :=
    unfold alloc_meta, dequeue_head, dequeue, area_from_brk, area_from_mmap, open_area, new_region, upd_region,
           setslot, get_head, set_head, get_links, set_links, set_next, set_prev;
    unfold bind, ret, get, put, modify, ask;
    cbn -[padd Z.mul Z.add Z.sub Z.shiftl].

  Definition take (t : astate) : astate := ltac2:(tb__ "0|1|
S74S2fVt;A1M0S14S1dSdG0S19A2S20S78S16Vt;A1Z1A2Vt;A2A2A3").

  Definition s_dead : astate := set_brk BrkDead s0.

  Definition res_n (t : astate) : Z := Z.shiftl 2 (st_meta_alloc_shift t).
  Definition res_r (t : astate) : nat := length (st_regions t).
  Definition t_RES1 (t : astate) : astate := ltac2:(tb__ "0|2|
S44S79S48Vt;A1Z1M0A2S1eS78S6fVt;A1M1G0A2S1fS11S6bVt;A1S6A2S12S5dS7SeVt;A1S56S7ScS29S77G1S6A2S54S60A1S5aA4S54S7A1A3A3Vt;A2A2A2A2").
  Definition s_RESok (t : astate) : astate := ltac2:(tb__ "0|2|
S6dS7eS11S6bVt;A1M0S6A2S12S1cS7SeS71Vt;A1M1A1G0ScS29S77S6fVt;A1S6A2S56S60S6S54S60A1A3S5aA4A4G1A2A2A1").
  Definition tr_RES (t : astate) (zm zp : Z) : list (kreq * Z) := ltac2:(tb__ "0|2|
S56S51S3S60A2M0S53S3S60S34S77S6fVt;A1S6A2A1Vzm;A4S52S5bG0A1L_;S76Vzm;Z0A2S54G0A1M1S56G0S53S3S60S25S11S6bVt;A1S6A2A1Vzp;A4G1A3X52x2A3").
  Definition r_RES (t : astate) (zm zp : Z) : option sptr * astate := ltac2:(tb__ "0|4|
S52S51S4fS0A1M0S1A2L_;M1S76Vzm;Z0M2A2S53G0S1S57S0A1M3Vt;A4G1S76Vzp;G2A2S53G0S1G3S71Vt;A1A4S53G0S1S50S0SdS11S6bVt;A1S6A2S13A2A2S73Vt;A1A4X52x2X52x2").

  Section Kernel.
    Hypothesis Hhd : st_free_meta_head s = None.
    Hypothesis Hcnt : st_avail_meta_count s = 0.

    Section AR.
      Hypothesis Hac : 0 < st_avail_meta_area_count s.
      Hypothesis Hinit : st_init_done s = true.
      Definition ar_p : sptr := st_avail_meta_areas s.
      Definition ar_rg : region := ltac2:(tb__ "0|0|
S8cS7S2bS7bA1SeVs;A1ScS28Z0S54S60A1S59A4A4").
      Definition s_ARok : astate := ltac2:(tb__ "0|0|
S6dS7eS7bS12S1cS7SeS6aA1S2bS7bA1ScS3eS7cA1S2dS7cA1S5dS60S40S7cA1S56S60S3dS7bA1S54S60A1A3A3S3fS7cA1A4A4S6aA2A2A1").

      Lemma yields_AR z : ltac2:(tb__ "0|3|
S62S51S4fS0A1M0S1A2M1S9Vs;A1S56S51S3S60A2M2S53S3S60S25S7bA1Vz;A4S54G2A1A3S52G1L_;S76Vz;Z0A2S53G0S1S57S0A1S6aA4S53G0S1S50S0SdS7bS13A2A2S7dA4X52x2A4").
      Proof using Hac Hcnt Hhd.
        assert (E : (st_avail_meta_area_count s =? 0) = false) by (apply Z.eqb_neq; lia).
        am_compute. repeat (progress (rewrite ?Hhd, ?Hcnt, ?E; am_compute)).
        split; [reflexivity|]. split; [exact I|].
        unfold ar_p. destruct (st_avail_meta_areas s) as [r o] eqn:Ep. cbn -[padd Z.mul Z.add Z.sub Z.shiftl].
        destruct (z =? 0); cbn -[Z.mul Z.add Z.sub Z.shiftl]; [reflexivity|].
        unfold s_ARok, take, open_st, ar_rg, ar_p, s0. rewrite Ep. cbn -[Z.mul Z.add Z.sub Z.shiftl]. reflexivity.
      Qed.
    End AR.

    Section NoArea.
      Hypothesis Hac : st_avail_meta_area_count s = 0.

      Section NB.
        Hypothesis Hbrk : ltac2:(tb__ "0|0|
S49S1aS21Vs;A1S30A3").
        Lemma yields_NB zm zp : ltac2:(tb__ "0|0|
S62S51S4fS0A1S1A2S9Vs;A1S70S6aVzm;Vzp;A3S6eS6aVzm;Vzp;A3A4").
        Proof using Hac Hbrk Hcnt Hhd.
          am_compute. repeat (progress (rewrite ?Hhd, ?Hcnt, ?Hac, ?Hbrk; am_compute)).
          unfold tr_RES, r_RES. split; [reflexivity|]. split; [exact I|].
          destruct (zm =? 0); cbn -[padd Z.mul Z.add Z.sub Z.shiftl]; [reflexivity|].
          split; [reflexivity|]. split; [exact I|].
          destruct (zp =? 0); cbn -[padd Z.mul Z.add Z.sub Z.shiftl]; [reflexivity|].
          unfold s_RESok, take, open_st, t_RES1, res_r, res_n, s0. cbn -[Z.mul Z.add Z.sub Z.shiftl].
          rewrite !nth_middle. cbn -[Z.mul Z.add Z.sub Z.shiftl]. reflexivity.
        Qed.
      End NB.

      Section BK.
        Variables (rb : nat) (pb : Z).
        Hypothesis Hbrk : ltac2:(tb__ "0|0|
S49S1aS21Vs;A1S17Vrb;Vpb;A2A3").
        Definition bk_rg : region := ltac2:(tb__ "0|0|
S8cS7Vrb;SeVs;A1ScS28Z0S54S60A1S59A4A4").
        Definition bk_p : sptr := ltac2:(tb__ "0|0|
S11Vrb;S77S6Vpb;A2A2").
        Definition s_BKok : astate := ltac2:(tb__ "0|1|
S6dS7eS82S2eS17Vrb;S79Vpb;Z1M0A2A2S1fS82S1eG0S12S1cS7SeS6aA1Vrb;ScS27S79S2dS83A1S6A2S54S60A1S5aA4A4S6aA2A2A2A2A2A1").
        Definition tr_BK (zg zm zp : Z) : list (kreq * Z) := ltac2:(tb__ "0|1|
S56S51S3S60A2M0S53S3S60S24Z1A1Vzg;A4S52S5bG0A1L_;S76Vzg;Z0A2S70S6cVzm;Vzp;A3S54G0A1X52x2A3").
        Definition r_BK (zg zm zp : Z) : option sptr * astate := ltac2:(tb__ "0|1|
S52S51S4fS0A1M0S1A2L_;S76Vzg;Z0A2S6eS6cVzm;Vzp;A3S53G0S1S50S0SdS82S13A2A2S85A4X52x2").

        Lemma yields_BK zg zm zp : ltac2:(tb__ "0|0|
S62S51S4fS0A1S1A2S9Vs;A1S86Vzg;Vzm;Vzp;A3S84Vzg;Vzm;Vzp;A3A4").
        Proof using Hac Hbrk Hcnt Hhd.
          am_compute. repeat (progress (rewrite ?Hhd, ?Hcnt, ?Hac, ?Hbrk; am_compute)).
          unfold tr_BK, r_BK. split; [reflexivity|]. split; [exact I|].
          destruct (zg =? 0); am_compute; repeat (progress (rewrite ?Hhd, ?Hcnt, ?Hac, ?Hbrk; am_compute)).
          -
            unfold tr_RES, r_RES. split; [reflexivity|]. split; [exact I|].
            destruct (zm =? 0); am_compute; [reflexivity|].
            split; [reflexivity|]. split; [exact I|].
            destruct (zp =? 0); am_compute; [reflexivity|].
            unfold s_RESok, take, open_st, t_RES1, res_r, res_n, s_dead, s0. cbn -[Z.mul Z.add Z.sub Z.shiftl].
            rewrite !nth_middle. cbn -[Z.mul Z.add Z.sub Z.shiftl]. reflexivity.
          - unfold s_BKok, take, open_st, bk_p, bk_rg, s0. cbn -[Z.mul Z.add Z.sub Z.shiftl]. reflexivity.
        Qed.
      End BK.

      Section IN.
        Hypothesis Hbrk : ltac2:(tb__ "0|0|
S49S1aS21Vs;A1S31A3").
        Definition in_r : nat := length (st_regions s).
        Definition in_p : sptr := SP in_r PGSZ.
        Definition s_INok : astate := ltac2:(tb__ "0|1|
S6dS7eS87S2eS17S88Z2M0A2S1fS87S1eZ1S12S5dS7SeS6aA1S56S7ScS27S77G0S6A2S54S60A1S5aA4S54S7A1A3A3S6aA2A2A2A2A2A1").
        Definition tr_IN (zq zg zu zm zp : Z) : list (kreq * Z) := ltac2:(tb__ "0|1|
S56S51S3S60A2M0S53S3S60S32Vzq;A4S56G0S53S3S60S24Z2A1Vzg;A4S52S5bG0A1L_;S76Vzg;Z0A2S70S6cVzm;Vzp;A3S56G0S53S3S60S33Vzu;A4S54G0A1A3X52x2A3A3").
        Definition r_IN (zg zm zp : Z) : option sptr * astate := ltac2:(tb__ "0|1|
S52S51S4fS0A1M0S1A2L_;S76Vzg;Z0A2S6eS6cVzm;Vzp;A3S53G0S1S50S0SdS87S13A2A2S8aA4X52x2").

        Lemma yields_IN zq zg zu zm zp : ltac2:(tb__ "0|0|
S62S51S4fS0A1S1A2S9Vs;A1S8bVzq;Vzg;Vzu;Vzm;Vzp;A5S89Vzg;Vzm;Vzp;A3A4").
        Proof using Hac Hbrk Hcnt Hhd.
          am_compute. repeat (progress (rewrite ?Hhd, ?Hcnt, ?Hac, ?Hbrk; am_compute)).
          unfold tr_IN, r_IN. split; [reflexivity|]. split; [exact I|]. split; [reflexivity|]. split; [exact I|].
          destruct (zg =? 0); am_compute; repeat (progress (rewrite ?Hhd, ?Hcnt, ?Hac, ?Hbrk; am_compute)).
          - unfold tr_RES, r_RES. split; [reflexivity|]. split; [exact I|].
            destruct (zm =? 0); am_compute; [reflexivity|].
            split; [reflexivity|]. split; [exact I|].
            destruct (zp =? 0); am_compute; [reflexivity|].
            unfold s_RESok, take, open_st, t_RES1, res_r, res_n, s_dead, s0. cbn -[Z.mul Z.add Z.sub Z.shiftl].
            rewrite !nth_middle. cbn -[Z.mul Z.add Z.sub Z.shiftl]. reflexivity.
          - split; [reflexivity|]. split; [exact I|].
            unfold s_INok, take, open_st, in_p, in_r, s0. cbn -[Z.mul Z.add Z.sub Z.shiftl]. reflexivity.
        Qed.
      End IN.
    End NoArea.
  End Kernel.
End Arms.

Section FreeRing.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S63VX;VR;VU;Vs;A4").

  Lemma chain_last lk : ltac2:(tb__ "0|3|
S5bS0A1M0S0S0S0S67Vlk;R3R4R2A4S4cS49G0R5S54S0A1A3A1S4bS0S0S49S4fS51S4fS0A1M1G1A2M2A1Vlk;S92S0R7R4A3A1S50G2S53G1G1S50S0R1A2S50S0R5A2A4A2A3Lpp;A2F_;F_;Fd;Ffirst;Fprev;Fl;").
  Proof using .
    induction l as [|x rest IH]; intros prev first d Hc Hne; [congruence|].
    cbn in Hc. destruct Hc as [Hx Hr]. destruct rest as [|y rest'].
    - cbn. exists prev. exact Hx.
    - rewrite last_cons. apply (IH x first x Hr). discriminate.
  Qed.

  Lemma flinks_MT g pr nx : ltac2:(tb__ "0|2|
S49S4fS51S4fS0A1M0G0A2M1A1S68VX;Vs;Vg;A3S50G1S53G0G0Vpr;Vnx;A4A2A3S4aS49S4fS2A1S61Vs;Vg;A2S50S2SaVpr;Vnx;A2A2A3S49S52S65Vg;VX;A2S59A3A2F_;").
  Proof using .
    unfold flinks, MTX. destruct (memb g X); [discriminate|].
    destruct (MT s g) as [[p' n'| |am]|]; try discriminate. intros E. injection E as -> ->. split; reflexivity.
  Qed.

  Lemma free_head_cases m : ltac2:(tb__ "0|5|
S49S4fS0A1S22Vs;A1S50S0Vm;A2M0A3S4dS49S4fS2A1M1S61Vs;Vm;A2M2S50S2SaG0G0A2A2M3A3S4dS4bS0S0S4aS4cS49S0R1Vm;A3A1S4aS49G1G2S50S2SaS50S0R1A2M4G4A2A2A3S49G1S61Vs;R1A2G3A3A2A2Ln;A2S4bS0S0S4bS0S0S4bS0S0S4bS0S0S4aS4cS49S0R3Vm;A3A1S4aS4cS49S0R4Vm;A3A1S4aS4cS49S0R4R3A3A1S4aS49G1G2S50S2SaS50S0R4A2S50S0R3A2A2A2A3S4aS49G1S61Vs;R3A2S50S2SaG0G4A2A2A3S49G1S61Vs;R4A2S50S2SaS50S0R2A2G0A2A2A3A2A2A2A2A2Ln2;A2Lpp;A2Ln;A2Lp;A2A2A2F_;").
  Proof using HI.
    intros Hhd. destruct (inv_rings HI) as ((ms & Hring & _) & _ & _). rewrite Hhd in Hring.
    destruct (ring_head_In _ _ _ Hring) as [_ [rest ->]].
    destruct Hring as [[Hnd Hch] _]. rewrite last_cons in Hch.
    cbn [chain] in Hch. destruct Hch as [Hm Hrest].
    destruct rest as [|n rest2].
    - left. cbn [last hd] in Hm. exact (proj1 (flinks_MT _ _ _ Hm)).
    - cbn [hd] in Hm. cbn [chain] in Hrest. destruct Hrest as [Hn Hrest2].
      assert (Hnm : n <> m) by (intros ->; inversion Hnd as [|a l Hni Hnd']; subst; apply Hni; left; reflexivity).
      destruct rest2 as [|n2 rest3].
      + right; left. exists n. cbn [last hd] in Hm, Hn.
        split; [exact Hnm|]. split; [exact (proj1 (flinks_MT _ _ _ Hm)) | exact (proj1 (flinks_MT _ _ _ Hn))].
      + right; right. cbn [hd] in Hn.
        set (p := last (n :: n2 :: rest3) m) in *.
        assert (Ep : last (n2 :: rest3) n = p) by (subst p; rewrite (last_cons n); reflexivity).
        assert (Hp_in : In p (n2 :: rest3)) by (rewrite <- Ep; apply In_last; discriminate).
        destruct (chain_last (flinks X s) (n2 :: rest3) n m n Hrest2 ltac:(discriminate)) as [pp Hp].
        rewrite Ep in Hp.
        exists p, n, pp, n2.
        inversion Hnd as [|a l Hni Hnd']; subst a l. inversion Hnd' as [|a l Hni2 Hnd'']; subst a l.
        split; [exact Hnm|].
        split; [intros E; apply Hni; right; rewrite <- E; exact Hp_in|].
        split; [intros E; apply Hni2; rewrite <- E; exact Hp_in|].
        split; [exact (proj1 (flinks_MT _ _ _ Hm))|]. split; [exact (proj1 (flinks_MT _ _ _ Hn)) | exact (proj1 (flinks_MT _ _ _ Hp))].
  Qed.
End FreeRing.

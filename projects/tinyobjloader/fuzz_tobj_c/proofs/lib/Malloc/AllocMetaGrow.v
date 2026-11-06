(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "iff"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "PGSZ"; "st_areas"; "mslot"; "st_regions"; "rg_kind"; "rkind"; "prid"; "rg_len"; "st_meta_alloc_shift"; "RkMetaRes"; "padd"; "rg_live"; "st_active"; "st_metas"; "ameta"; "astate"; "lupd"; "set_regions"; "st_area_head"; "st_bounces"; "st_unmap_seq"; "st_usage"; "RkMap"; "st_mmap_counter"; "st_seq"; "BrkDead"; "METAS_PER_AREA"; "META_SIZE"; "MRaw"; "brkst"; "st_area_tail"; "st_avail_meta"; "st_avail_meta_area_count"; "st_brk"; "st_free_meta_head"; "MFree"; "mkRegion"; "st_avail_meta_areas"; "st_avail_meta_count"; "st_init_done"; "AREA_HDR"; "SP"; "am_mem"; "am_next"; "am_prev"; "mupdate"; "rg_rw"; "set_avail_meta"; "set_avail_meta_count"; "usage_of"; "@Stdlib.Lists.List"; "In"; "flat_map"; "last"; "NoDup"; "incl"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "of_nat"; "mul"; "max"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "loc"; "LCtx"; "loc_addr"; "footprint"; "MCell"; "mc_loc"; "LMem"; "image"; "keys"; "region_of"; "ctx_cells"; "ly_reg"; "VZ"; "CTX_avail_meta_areas"; "mc_val"; "pairwise"; "sval"; "usedX"; "user_blocks"; "Inv"; "area_cells"; "ly_ctx"; "MT"; "VP"; "sval_num"; "mc_w"; "optr"; "CTX_SIZE"; "CTX_active"; "CTX_avail_meta"; "CTX_avail_meta_area_count"; "CTX_meta_alloc_shift"; "areas_cells"; "crange"; "CTX_avail_meta_count"; "CTX_bounces"; "CTX_meta_area_head"; "CTX_meta_area_tail"; "CTX_unmap_seq"; "CTX_usage"; "Layout"; "group_cells"; "layout_ok"; "ly_brk0"; "ly_sec"; "ly_top"; "memb"; "meta_slot_cells"; "slot_cells"; "used_metas"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.RES"; "t2"; "t1"; "pnew"; "lenZ"; "L'"; "mnew"; "rr"; "bounded34"; "rg2"; "t2pre"; "vm1"; "vm2"; "CHG1"; "CHG2"; "C_ac"; "C_ars"; "C_sh"; "C_tn"; "old_ctx1"; "old_ctx2"; "rg1"; "wa"; "wn"; "C_avm2"; "C_cnt2"; "C_hd2"; "C_tl2"; "@Corelib.Init.Datatypes"; "prod"; "list"; "cons"; "app"; "option"; "nat"; "Some"; "fst"; "snd"; "bool"; "nil"; "None"; "pair"; "true"; "length"; "false"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "footer_cells"; "group_footer_cells"; "@Corelib.Init.Peano"; "lt"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaImage"; "map_fp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "layout_extends"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "vm_reserved"; "vm_maps"; "maps_subtract"; "iv_subtract"; "mkVmMapsFull"; "vm_brk"; "vm_init_sp"; "vm_limit"; "vm_mmap_base"; "vm_noaccess"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"; "range_in_maps"; "vm_ok"; "addr_of"; "ledger_ok"; "blocks"; "img_reserved"; "mc_img_hi"; "mc_img_lo"; "mc_ctx"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow"; "Lext"; "val_below"; "loc_below"; "vm_okX";
"vm_ok_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaPost"; "res_n"; "am_spec_post"; "s0"; "take"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.CellsBelow"; "areas_cell_ok"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow.Pigeonhole"; "list_min"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "upd_meta"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta"; "am_frame"; "open_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLemmasRing MallocWfInv MallocWfFrame MallocWfRings MallocWfRepr MallocWfMeta MallocWfGeom
  MallocWfSurgery MallocFooter MallocFooterLemmas MallocLayout MallocIface MallocIfaceI MallocLaws FpLaws WalkArith RingFacts Zones2 AllocMetaPost AllocMetaImage MapsWf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition Lext (L : layout) (r : nat) (a : Z) : layout := ltac2:(tb__ "0|0|
S73S60VL;A1S9dSa1S7L_;Sd2R1Vr;A2Va;S56VL;R1A2Xa1x2Lk;S76VL;A1S77VL;A1S78VL;A1A5").

Lemma Lext_reg L r a : ltac2:(tb__ "0|0|
S0S7S56Sc8VL;Vr;Va;A3Vr;A2Va;A3").
Proof. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma Lext_old L r a k : ltac2:(tb__ "0|0|
S3S0S9dVk;Vr;A3A1S0S7S56Sc8VL;Vr;Va;A3Vk;A2S56VL;Vk;A2A3F_;").
Proof. intros Hk. cbn. destruct (Nat.eqb k r) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity]. Qed.

Lemma Lext_extends L r a : ltac2:(tb__ "0|0|
SafVL;Sc8VL;Vr;Va;A3Vr;A3").
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
  intros k Hk. apply Lext_old. lia.
Qed.

Lemma Lext_top L r a : ltac2:(tb__ "0|0|
S0S7SbbSc8VL;Vr;Va;A3A1SbbVL;A1A3").
Proof. reflexivity. Qed.

Definition loc_below (n : nat) (l : loc) : Prop := ltac2:(tb__ "0|0|
S4bOLl;Vl;S7S6Loff;S8SacS10R1A1Vn;A2Lp;X4bx2").
Definition val_below (n : nat) (v : sval) : Prop := ltac2:(tb__ "0|1|
S5bOLv;Vv;S7S6Lz;M0S8SacS10R1A1Vn;A2Lp;G0S6X5bx4").

Lemma loc_addr_ext L L' n l : ltac2:(tb__ "0|0|
SafVL;VL';Vn;A3ScaVn;Vl;A2S0S7S4dVL';Vl;A2S4dVL;Vl;A2A3F_;F_;").
Proof.
  intros (EC & _ & _ & ER & _) Hl. destruct l as [o|[r o]]; cbn in *; [rewrite EC; reflexivity|].
  rewrite (ER r Hl). reflexivity.
Qed.

Lemma sval_num_ext L L' n v : ltac2:(tb__ "0|0|
SafVL;VL';Vn;A3Sc9Vn;Vv;A2S0S7S63VL';Vv;A2S63VL;Vv;A2A3F_;F_;").
Proof.
  intros (EC & _ & ES & ER & _) Hv. destruct v as [z|[r o]|z|]; cbn in *; try reflexivity; [|rewrite ES; reflexivity].
  rewrite (ER r Hv). reflexivity.
Qed.

Lemma layout_extends_trans L1 L2 L3 n1 n2 : ltac2:(tb__ "0|0|
SadVn1;Vn2;A2SafVL1;VL2;Vn1;A3SafVL2;VL3;Vn2;A3SafVL1;VL3;Vn1;A3F_;F_;F_;").
Proof.
  intros Hn (A1 & B1 & C1 & D1 & E1) (A2 & B2 & C2 & D2 & E2). split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [|congruence]. intros r Hr. rewrite (D2 r) by lia. apply D1. exact Hr.
Qed.

Section CellsBelow.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
  Hypothesis HI : ltac2:(tb__ "0|0|
S5eVX;VR;VU;Vs;A4").
  Hypothesis HX : xraw X s.
  Let n : nat := length (st_regions s).

  Lemma area_below a : ltac2:(tb__ "0|0|
S3cS8Va;SbVs;A1A3SacS10Va;A1Vn;A2F_;").
  Proof using HI.
    intros Ha. pose proof (inv_areas HI) as (_ & AOK & _). destruct (AOK a Ha) as (r & o & rg & -> & _ & _ & Hr & _).
    cbn. exact (region_of_lt _ _ _ Hr).
  Qed.

  Lemma key_below q : ltac2:(tb__ "0|0|
S3cS8Vq;S53Vs;A1A3SacS10Vq;A1Vn;A2F_;").
  Proof using HI.
    intros Hq. destruct (key_area X R U s HI q Hq) as (a & k & Ha & _ & ->).
    destruct a as [r o]. cbn. exact (area_below _ Ha).
  Qed.

  Lemma optr_below (o : option sptr) : ltac2:(tb__ "0|0|
S8S0S9cS8A1Vo;S9eS8R1A2A3S3cS8R2S53Vs;A1A3F_;Fq;Sc9Vn;S65Vo;A1A2F_;").
  Proof using HI. intros H. destruct o as [q|]; cbn; [apply key_below; apply H; reflexivity | exact I]. Qed.

  Lemma used_mem_below g am : ltac2:(tb__ "0|0|
S5cVX;Vs;Vg;Vam;A4SacS10S34Vam;A1A1Vn;A2F_;").
  Proof using HI. intros Hu. exact (used_group_prid_lt X R U s g am HI Hu). Qed.

  Lemma In_last_cons (l : list sptr) (d : sptr) : ltac2:(tb__ "0|0|
S3cS8S3eS8Vl;Vd;A3S9aS8Vd;Vl;A3A3").
  Proof using .
    revert d. induction l as [|z t IH]; intros d; [left; reflexivity|]. destruct t as [|w t']; [right; left; reflexivity|].
    change (last (z :: w :: t') d) with (last (w :: t') d).
    destruct (IH d) as [E|Hin]; [left; exact E | right; right; exact Hin].
  Qed.

  Lemma free_links_keys q pr nx : ltac2:(tb__ "0|3|
S0S9cScA1S61Vs;Vq;A2S9eScS2dVpr;Vnx;A2A2A3S1S8S0S9cS8A1M0Vpr;S9eS8R1A2M1A3S3cS8R2S53Vs;A1A3M2F_;Fp;S8S0G0Vnx;G1A3G2F_;Fp;A2F_;").
  Proof using HI HX.
    intros Hq.
    destruct (memb q X) eqn:EX.
    - assert (Hin : In q X).
      { unfold memb in EX. apply existsb_exists in EX as (y & Hy & Ey). apply sptr_eqb_eq in Ey. subst y. exact Hy. }
      destruct (HX q Hin) as [M|M]; rewrite M in Hq; [discriminate|]. injection Hq as <- <-.
      split; intros p Hp; discriminate.
    - destruct (inv_rings HI) as ((ms & Rg & Hall) & _ & _).
      assert (Hfl : flinks X s q = Some (pr, nx)) by (unfold flinks, MTX; rewrite EX, Hq; reflexivity).
      assert (Hqm : In q ms) by (apply (Hall q pr nx); unfold MTX; rewrite EX; exact Hq).
      pose proof Rg as [[Hnd Hch] Hhd].
      assert (MEM : forall x, In x ms -> In x (keys s)).
      { intros x Hx. destruct (ring_links _ _ _ _ Rg Hx) as (pr' & nx' & L').
        destruct (flinks_free _ _ _ _ L') as (pr'' & nx'' & _ & M & _). exact (MT_Some_In_keys _ _ _ M). }
      destruct ms as [|m0 rest]; [destruct Hqm|].
      destruct (chain_next _ _ _ _ _ _ _ Hch Hqm Hfl) as (l1 & l2 & El & Enx & Epr).
      split; intros p Hp.
      + rewrite Hp in Epr. injection Epr as Ep. subst p. apply MEM.
        destruct l1 as [|y l1'] using rev_ind.
        * cbn [last app]. destruct rest as [|r1 rt]; [left; reflexivity | exact (In_last_cons (r1 :: rt) m0)].
        * rewrite last_last. rewrite El. apply in_app_iff. left. apply in_app_iff. right. left. reflexivity.
      + rewrite Hp in Enx. injection Enx as Ep. subst p. apply MEM.
        destruct l2 as [|y l2']; cbn [hd]; [left; reflexivity|]. rewrite El. apply in_app_iff. right. right. left. reflexivity.
  Qed.

  Lemma used_links_keys g am : ltac2:(tb__ "0|3|
S5cVX;Vs;Vg;Vam;A4S1S8S0S9cS8A1M0S36Vam;A1S9eS8R1A2M1A3S3cS8R2S53Vs;A1A3M2F_;Fp;S8S0G0S35Vam;A1G1A3G2F_;Fp;A2F_;").
  Proof using HI.
    intros Hu. pose proof (inv_groups HI g am Hu) as (_ & _ & _ & CL & _).
    destruct CL as [(E63 & _) | (Hsc & _)].
    - destruct (inv_rings HI) as (_ & _ & DU). destruct (DU g am Hu E63) as [P N]. rewrite P, N. split; intros p Hp; discriminate.
    - destruct (inv_rings HI) as (_ & AR & _). destruct (AR (am_sc am) Hsc) as (ms & Rg & MEMB & _).
      assert (CASE : (am_prev am, am_next am) = (None, None) \/ (am_prev am, am_next am) <> (None, None)).
      { destruct (am_prev am), (am_next am); [right|right|right|left]; congruence. }
      destruct CASE as [E|NE].
      + injection E as EP EN. rewrite EP, EN. split; intros p Hp; discriminate.
      + assert (Hgm : In g ms) by (apply (proj2 (MEMB g am Hu eq_refl)); exact NE).
        destruct ms as [|m0 rest]; [destruct Hgm|].
        pose proof Rg as [_ Hhd]. cbn [hd_error] in Hhd. rewrite Hhd in Rg.
        destruct (ring_step X s (am_sc am) m0 rest g Rg Hgm) as ((am' & Hu' & _ & M' & Er) & N1 & P1).
        pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
        assert (MEM : forall x, In x (m0 :: rest) -> In x (keys s)).
        { intros x Hx. destruct (ring_members_used _ _ _ _ _ _ Rg Hx) as (amx & Hux & _). pose proof (usedX_MT _ _ _ _ Hux) as [Mx _]. exact (MT_Some_In_keys _ _ _ Mx). }
        unfold mnext, mprev in N1, P1. rewrite Er in N1, P1.
        split; intros p Hp; [rewrite Hp in P1 | rewrite Hp in N1]; apply MEM; assumption.
  Qed.

  Lemma active_hd_key k g : ltac2:(tb__ "0|1|
SacVk;U30A2S0S9cS8A1M0Sc6G0Vk;S16Vs;A1Sa3S8A1A4S9eS8Vg;A2A3S3cS8Vg;S53Vs;A1A3F_;F_;").
  Proof using HI.
    intros Hk Hg. destruct (inv_rings HI) as (_ & AR & _).
    destruct (AR (Z.of_nat k) ltac:(lia)) as (ms & Rg & _).
    assert (Hhd : active_hd s (Z.of_nat k) = Some g) by (unfold active_hd; rewrite Nat2Z.id; exact Hg).
    rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _].
    destruct (ring_members_used _ _ _ _ _ _ Rg Hin) as (am & Hu & _). pose proof (usedX_MT _ _ _ _ Hu) as [M _]. exact (MT_Some_In_keys _ _ _ M).
  Qed.

  Lemma head_key q : ltac2:(tb__ "0|0|
S0S9cS8A1S2cVs;A1S9eS8Vq;A2A3S3cS8Vq;S53Vs;A1A3F_;").
  Proof using HI.
    intros Hh. destruct (inv_rings HI) as ((ms & Rg & Hall) & _).
    rewrite Hh in Rg. destruct (ring_head_In _ _ _ Rg) as [Hin _].
    destruct (ring_links _ _ _ q Rg Hin) as (pr & nx & Hl).
    destruct (flinks_free _ _ _ _ Hl) as (pr' & nx' & _ & M & _). exact (MT_Some_In_keys _ _ _ M).
  Qed.

  Lemma last_In {A} (l : list A) (d : A) : ltac2:(tb__ "0|0|
S3S0S99VA;A1Vl;Sa2VA;A1A3A1S3cVA;S3eVA;Vl;Vd;A3Vl;A3F_;").
  Proof using .
    induction l as [|x t IH]; intros Hne; [congruence|]. destruct t as [|y t']; [left; reflexivity|].
    right. apply IH. discriminate.
  Qed.

  Definition areas_cell_ok : Prop := ltac2:(tb__ "0|0|
S0S7S2aVs;A1Z0A3S0S99S8A1SbVs;A1Sa2S8A1A3F_;").

  Lemma ctx_cell_below c : ltac2:(tb__ "0|1|
S3cS4aVc;S55Vs;A1A3S0S4bS50Vc;A1M0S4cS58A1A3Sd1F_;S1ScaVn;G0A2Sc9Vn;S59Vc;A1A2A2F_;F_;").
  Proof using HI.
    intros Hin Hac. pose proof (inv_areas HI) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof (inv_keys HI) as (K1 & K2 & K3 & K4 & K5).
    unfold ctx_cells in Hin. apply in_app_iff in Hin as [Hin|Hin].
    - cbn [In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; cbn [mc_loc mc_val]; (split; [exact I|]).
      + destruct (st_init_done s); exact I.
      + exact I.
      + exact I.
      + apply optr_below. intros q Hq. exact (head_key q Hq).
      + destruct (st_areas s) as [|a t] eqn:Ea; [exact I|]. cbn.
        rewrite (K4 ltac:(discriminate)).
        assert (Hl : In (last (a :: t) (SP 0%nat 0)) (st_areas s)) by (rewrite Ea; apply last_In; discriminate).
        pose proof (area_below _ Hl) as B. destruct (last (a :: t) (SP 0%nat 0)); cbn in *. exact B.
      + exact I.
      + exact I.
      + exact I.
      + rewrite A3. destruct (st_areas s) as [|a t] eqn:Ea; cbn; [exact I|]. apply (area_below a). rewrite Ea. left. reflexivity.
      + rewrite A4. destruct (st_areas s) as [|a t] eqn:Ea; cbn; [exact I|].
        assert (Hl : In (last (a :: t) (SP 0%nat 0)) (st_areas s)) by (rewrite Ea; apply last_In; discriminate).
        exact (area_below _ Hl).
      + cbn [mc_loc] in Hac. specialize (Hac eq_refl). unfold areas_cell_ok in Hac.
        destruct (Z.eq_dec (st_avail_meta_area_count s) 0) as [E0|NE].
        * rewrite (Hac E0), E0. cbn. exact I.
        * destruct (A8 ltac:(pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&_&_&_&C11&_); lia)) as (r & o & rg & Ep & Hr & _).
          destruct (match st_areas s with [] => true | _ => false end && (st_avail_meta_area_count s =? 0)); cbn; [exact I|].
          rewrite Ep. cbn. exact (region_of_lt _ _ _ Hr).
      + exact I.
      + destruct (st_brk s) as [| |r p]; cbn; try exact I.
        destruct A7 as (_ & rg & Hr & _). exact (region_of_lt _ _ _ Hr).
    - split.
      + apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]];
          apply in_map_iff in Hin as (k & <- & _); exact I.
      + apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]];
          apply in_map_iff in Hin as (k & <- & Hk); cbn [mc_val]; try exact I.
        apply in_seq in Hk. apply optr_below. intros q Hq. exact (active_hd_key k q ltac:(lia) Hq).
  Qed.

  Lemma slot_cells_val am i c : ltac2:(tb__ "0|0|
S3cS4aVc;S7bVam;Vi;A2A3S4S7S7S0S5bS59Vc;A1S57R1A1A3Lz;A2F_;").
  Proof using .
    intros Hin. unfold slot_cells in Hin.
    apply in_app_iff in Hin as [Hin|Hin]; [destruct Hin as [<-|[]]; eexists; reflexivity|].
    apply in_app_iff in Hin as [Hin|Hin].
    - destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hin]. destruct Hin as [<-|[<-|[]]]; eexists; reflexivity.
    - destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hin]. destruct (fr_off fr =? 0); [destruct Hin|].
      destruct Hin as [<-|[<-|[<-|[]]]]; eexists; reflexivity.
  Qed.

  Lemma footer_cells_val am c : ltac2:(tb__ "0|0|
S3cS4aVc;SabVam;A1A3S4S7S7S0S5bS59Vc;A1S57R1A1A3Lz;A2F_;").
  Proof using .
    intros Hin. unfold group_footer_cells in Hin. destruct Hin as [<-|Hin]; [eexists; reflexivity|].
    apply in_flat_map in Hin as (i & _ & Hin). destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hin].
    unfold frame_footer_cells in Hin. destruct (fr_kind fr); [|destruct Hin].
    apply in_app_iff in Hin as [Hin|Hin]; [destruct (0 <? reserved_of am fr); [destruct Hin as [<-|[]]; eexists; reflexivity | destruct Hin]|].
    apply in_app_iff in Hin as [Hin|Hin]; [destruct (5 <=? reserved_of am fr); [destruct Hin as [<-|[]]; eexists; reflexivity | destruct Hin]|].
    destruct (5 <? reserved_of am fr); [destruct Hin as [<-|[]]; eexists; reflexivity | destruct Hin].
  Qed.

  Lemma In_areas_cells_next l c : ltac2:(tb__ "0|2|
S3cS4aVc;S6bVs;Vl;A2A3S4S8S8S4S9cS8A1M0G0S1S3cS8R2Vl;A3M1S1S8S0G0R2S9eS8R1A2A3G1F_;Fp;S3cS4aVc;S5fVs;R2R1A3A3A2A2Lnext;A2La;A2F_;").
  Proof using .
    induction l as [|a t IH]; cbn [areas_cells]; intros Hin; [destruct Hin|].
    apply in_app_iff in Hin as [Hin|Hin].
    - exists a, (hd_error t). split; [left; reflexivity|]. split; [|exact Hin].
      intros p Hp. destruct t as [|b t']; [discriminate|]. cbn in Hp. injection Hp as ->. right. left. reflexivity.
    - destruct (IH Hin) as (a' & next & Ha' & Hn & Hc). exists a', next. split; [right; exact Ha'|]. split; [|exact Hc].
      intros p Hp. right. exact (Hn p Hp).
  Qed.

  Lemma slot_cell_below q x c : ltac2:(tb__ "0|0|
S0S9cScA1S61Vs;Vq;A2Vx;A3S3cS4aVc;S7aVq;Vx;A2A3Sc9Vn;S59Vc;A1A2F_;F_;").
  Proof using HI HX.
    intros Hq Hin.
    destruct x as [[pr nx| |am]|].
    - destruct (free_links_keys q pr nx Hq) as [P N].
      cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_val]; try exact I; apply optr_below; assumption.
    - cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; exact I.
    - assert (Hu : usedX X s q am).
      { unfold usedX, MTX. destruct (memb q X) eqn:EX; [|exact Hq]. exfalso.
        assert (Hin' : In q X).
        { unfold memb in EX. apply existsb_exists in EX as (y & Hy & Ey). apply sptr_eqb_eq in Ey. subst y. exact Hy. }
        destruct (HX q Hin') as [M|M]; rewrite M in Hq; discriminate. }
      destruct (used_links_keys q am Hu) as [P N].
      cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_val]; try exact I;
        [apply optr_below; exact P | apply optr_below; exact N | exact (used_mem_below q am Hu)].
    - cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; exact I.
  Qed.

  Theorem cell_below c : ltac2:(tb__ "0|1|
S3cS4aVc;S9bS4aS52Vs;A1SaaVs;A1A3A3S0S4bS50Vc;A1M0S4cS58A1A3Sd1F_;S1ScaVn;G0A2Sc9Vn;S59Vc;A1A2A2F_;F_;").
  Proof using HI HX.
    intros Hin Hac. apply in_app_iff in Hin as [Hin|Hin].
    - unfold image in Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (ctx_cell_below c Hin Hac)|].
      apply in_app_iff in Hin as [Hin|Hin].
      + destruct (In_areas_cells_next _ c Hin) as (a & next & Ha & Hnext & Hc).
        split.
        * destruct (In_area_cells s a next c Hc) as (d & E & _). rewrite E. destruct a as [r o]; cbn. exact (area_below _ Ha).
        * unfold area_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
          -- destruct Hc as [<-|[<-|[<-|[]]]]; cbn [mc_val]; [exact I | | exact I].
             destruct next as [p|]; cbn; [|exact I]. exact (area_below p (Hnext p eq_refl)).
          -- apply in_flat_map in Hc as (k & _ & Hc). exact (slot_cell_below _ _ c eq_refl Hc).
      + apply in_flat_map in Hin as ([g am] & Hg & Hc). cbn [fst snd] in Hc.
        pose proof (proj1 (used_iff X R U s HI HX g am) Hg) as Hu.
        split.
        * destruct (In_group_cells X R U s g am c HI Hu Hc) as (d & E & _). rewrite E. destruct (am_mem am) as [r o] eqn:Em; cbn.
          pose proof (used_mem_below g am Hu) as B. rewrite Em in B. exact B.
        * unfold group_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
          -- destruct Hc as [<-|[<-|[]]]; cbn [mc_val].
             ++ cbn. pose proof (usedX_MT _ _ _ _ Hu) as [M _]. exact (key_below g (MT_Some_In_keys _ _ _ M)).
             ++ destruct (am_maplen am =? 0); exact I.
          -- apply in_flat_map in Hc as (i & _ & Hc). destruct (slot_cells_val am i c Hc) as [z ->]. exact I.
    - unfold footer_cells in Hin. apply in_flat_map in Hin as ([g am] & Hg & Hc). cbn [fst snd] in Hc.
      pose proof (proj1 (used_iff X R U s HI HX g am) Hg) as Hu.
      split.
      + destruct (In_group_footer_cells X R U s g am c HI Hu Hc) as (d & E & _). rewrite E. destruct (am_mem am) as [r o] eqn:Em; cbn.
        pose proof (used_mem_below g am Hu) as B. rewrite Em in B. exact B.
      + destruct (footer_cells_val am c Hc) as [z ->]. exact I.
  Qed.

  Theorem cell_stable L L' c : ltac2:(tb__ "0|2|
SafVL;VL';Vn;A3S3cS4aVc;S9bS4aS52Vs;A1SaaVs;A1A3A3S0S4bS50Vc;A1M0S4cS58A1A3Sd1F_;S1S0S7S4dVL';G0A2S4dVL;G0A2A3S0S7S63VL';S59Vc;A1M1A2S63VL;G1A2A3A2F_;F_;F_;").
  Proof using HI HX.
    intros HE Hin Hac. destruct (cell_below c Hin Hac) as [B1 B2].
    split; [exact (loc_addr_ext L L' n _ HE B1) | exact (sval_num_ext L L' n _ HE B2)].
  Qed.

  Lemma footprint_below e : ltac2:(tb__ "0|0|
S3cS98S4bS7A2Ve;S4eVs;A1A3ScaVn;S9fS4bS7Ve;A3A2F_;").
  Proof using HI.
    intros Hin. unfold footprint in Hin. destruct Hin as [<-|Hin]; [exact I|].
    apply in_app_iff in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as (a & <- & Ha). cbn. destruct a as [r o]; cbn. exact (area_below _ Ha).
    - apply in_flat_map in Hin as (k & Hk & Hin). apply in_seq in Hk.
      destruct (region_of s k) as [rg|]; [|destruct Hin]. destruct (rg_kind rg); try destruct Hin.
      destruct (rg_live rg); [|destruct Hin]. destruct Hin as [<-|[]]. cbn. lia.
  Qed.

  Lemma user_block_below b : ltac2:(tb__ "0|0|
S3cS98S8S7A2Vb;S5dVs;A1A3SacS10S9fS8S7Vb;A3A1Vn;A2F_;").
  Proof using HI HX.
    intros Hin. unfold user_blocks in Hin. apply in_flat_map in Hin as ([g am] & Hg & Hin). cbn [snd] in Hin.
    apply in_flat_map in Hin as (i & _ & Hin).
    destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hin]. destruct (fr_kind fr); [|destruct Hin].
    destruct Hin as [<-|[]]. cbn [fst]. unfold slot_start.
    pose proof (used_mem_below g am (proj1 (used_iff X R U s HI HX g am) Hg)) as B.
    destruct (am_mem am) as [r o]; cbn in *. exact B.
  Qed.
End CellsBelow.

Lemma flat_map_seq_ext {A} (f g : nat -> list A) n : ltac2:(tb__ "0|2|
S9dSacR1Vn;A2S0S99VA;A1M0Vf;R2A1Vg;R2A1A3F_;Fk;S0G0S3dS9dVA;Vf;Sc7U0Vn;A2M1A4S3dS9dVA;Vg;G1A4A3F_;").
Proof.
  intros H. apply flat_map_ext_in || idtac.
  induction n as [|n IH]; [reflexivity|]. rewrite seq_S, !flat_map_app. cbn [flat_map Nat.add]. rewrite app_nil_r, app_nil_r.
  rewrite (IH ltac:(intros k Hk; apply H; lia)). rewrite (H n ltac:(lia)). reflexivity.
Qed.

Lemma lupd_app_last {A} (l : list A) (x y : A) : ltac2:(tb__ "0|1|
S0S99VA;A1S1aVA;S9bVA;Vl;S9aVA;Vx;Sa2VA;A1M0A3A3Sa6VA;Vl;A2Vy;A4S9bVA;Vl;S9aVA;Vy;G0A3A3A3").
Proof. induction l as [|h l' IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma map_fp_app_nonmap s rg : ltac2:(tb__ "0|0|
S2S3S0SfSeVrg;A1S20A3A1S0Sa1S15Vrg;A1Sa7A3A2S0S99S98S4bS7A2A1SaeS1bS9bS9SdVs;A1S9aS9Vrg;Sa2S9A1A3A3Vs;A2A1SaeVs;A1A3F_;").
Proof.
  intros Hk. unfold map_fp. cbn [st_regions set_regions]. rewrite length_app. cbn [length]. rewrite Nat.add_1_r, seq_S, flat_map_app.
  cbn [flat_map Nat.add]. rewrite app_nil_r.
  rewrite (region_of_app_new s rg).
  assert (E : match rg_kind rg with RkMap => if rg_live rg then [(LMem (SP (length (st_regions s)) 0), rg_len rg)] else [] | _ => [] end = (@nil (loc * Z))).
  { destruct Hk as [Hk|Hl]; [destruct (rg_kind rg); congruence | rewrite Hl; destruct (rg_kind rg); reflexivity]. }
  rewrite E, app_nil_r. apply flat_map_seq_ext. intros k Hkk. rewrite (region_of_app_old s [rg] k Hkk). reflexivity.
Qed.

Lemma map_fp_upd_same s r rg rg' : ltac2:(tb__ "0|0|
S0S9cS9A1S54Vs;Vr;A2S9eS9Vrg;A2A3S0SfSeVrg';A1SeVrg;A1A3S0S7S11Vrg';A1S11Vrg;A1A3S0Sa1S15Vrg';A1S15Vrg;A1A3S0S99S98S4bS7A2A1SaeS1bS1aS9SdVs;A1Vr;Vrg';A4Vs;A2A1SaeVs;A1A3F_;F_;F_;F_;").
Proof.
  intros Hr Ek El Ev. unfold map_fp. cbn [st_regions set_regions]. rewrite length_lupd.
  apply flat_map_seq_ext. intros k Hk. rewrite (region_of_upd s r rg' k).
  destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 _]. apply Nat.eqb_eq in E1. subst k. rewrite Hr, Ek, El, Ev. reflexivity.
Qed.

Lemma map_fp_upd_nonmap s r rg rg' : ltac2:(tb__ "0|0|
S0S9cS9A1S54Vs;Vr;A2S9eS9Vrg;A2A3S3S0SfSeVrg;A1S20A3A1S3S0SfSeVrg';A1S20A3A1S0S99S98S4bS7A2A1SaeS1bS1aS9SdVs;A1Vr;Vrg';A4Vs;A2A1SaeVs;A1A3F_;F_;F_;").
Proof.
  intros Hr Hk1 Hk2. unfold map_fp. cbn [st_regions set_regions]. rewrite length_lupd.
  apply flat_map_seq_ext. intros k Hkk. rewrite (region_of_upd s r rg' k).
  destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 _]. apply Nat.eqb_eq in E1. subst k. rewrite Hr.
  destruct (rg_kind rg') eqn:E1; try congruence; destruct (rg_kind rg) eqn:E2; try congruence; reflexivity.
Qed.

Lemma map_fp_regions_only s s' : ltac2:(tb__ "0|0|
S0S99S9A1SdVs';A1SdVs;A1A3S0S99S98S4bS7A2A1SaeVs';A1SaeVs;A1A3F_;").
Proof. intros E. unfold map_fp, region_of. rewrite E. reflexivity. Qed.

Lemma In_footprint s e : ltac2:(tb__ "0|1|
S5S3cS98S4bS7A2M0Ve;S4eVs;A1A3S2S0G0Ve;Sa4S4bS7S4cZ0A1S66A4A3S2S3cG0Ve;Sc5S8G0S8Sa4S4bS7S51R1A1SaA4La;SbVs;A1A4A3S3cG0Ve;SaeVs;A1A3A2A2A2").
Proof. rewrite footprint_eq. cbn [In]. rewrite in_app_iff. split; intros H; (destruct H as [H|[H|H]]; [left; symmetry + idtac; exact H | right; left; exact H | right; right; exact H]). Qed.

Definition vm_okX (L : layout) (s : astate) : Prop := ltac2:(tb__ "0|9|
S1S9dS9S7S0S9cS9A1M0S54Vs;R3A2S9eS9R2A2A3S0SfSeR3A1S13A3S3cS7R3S38R4A1A3S1S41SaR4A2S41S42R4SaA2S11R5A1A2A2F_;F_;F_;Foff;Frg;Fr;S1S9dS9dS9S9S3S0S9dR4R3A3A1S0G0S54Vs;R5A2S9eS9R3A2A3M1G1S0SfSeR5A1S13A3M2G2S2S41S42S56VL;R9A2M3S11R7A1A2S56VL;R8A2M4A2S41S42G4S11R6A1A2G3A2A2F_;F_;F_;F_;F_;Frg2;Frg1;Fr2;Fr1;S1S9dS9S0G0S54Vs;R2A2S9eS9R1A2A3M5S0Sa1S15R2A1Sa5A3M6S41SaS11R3A1M7A2F_;F_;Frg;Fr;S9dS9G5G6S1S41SaS56VL;R4A2M8A2S41S42G8G7A2SbbVL;A1A2A2F_;F_;Frg;Fr;A2A2A2").

Lemma vm_ok_X L s vm : ltac2:(tb__ "0|0|
SbdVL;Vs;Vvm;A3ScbVL;Vs;A2F_;").
Proof. intros (_ & _ & _ & _ & X1 & X2 & X3 & X4 & _). exact (conj X1 (conj X2 (conj X3 X4))). Qed.

Lemma urange (w : word) : ltac2:(tb__ "0|1|
S1S41Z0Sa8Q40Vw;A2M0A2S43G0S44Z2Z40A2A2A2").
Proof. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma range_in_maps_cons e l x n : ltac2:(tb__ "0|1|
SbcVl;Vx;Vn;A3SbcS9aS98Sa9Q40A1M0G0A2Ve;Vl;A3Vx;Vn;A3F_;").
Proof. intros (e' & He' & H). exists e'. split; [right; exact He' | exact H]. Qed.
Lemma range_in_maps_head e l x n : ltac2:(tb__ "0|3|
S41Sa8Q40M0S9fSa9G0A1M1G1Ve;A3A2M2Vx;A2S41S42Vx;Vn;A2S42G2Sa8G0Sa0G1G1Ve;A3A2A2A2SbcS9aS98G1G1A2Ve;Vl;A3Vx;Vn;A3F_;F_;").
Proof. intros H1 H2. exists e. split; [left; reflexivity | split; assumption]. Qed.

Lemma iv_subtract_keeps (e : word * word) lo hi x n : ltac2:(tb__ "0|7|
S43Z0M0Vn;A2S41G0Vlo;A2S43Vhi;S44Z2Z40A2A2S41Sa8Q40M1S9fSa9G1A1M2G2Ve;A3M3A2M4Vx;A2S41S42Vx;Vn;A2M5S42G4Sa8G1Sa0G2G2Ve;A3M6A2A2A2S2S41G5Vlo;A2S41Vhi;Vx;A2A2SbcSb3G3G6Vlo;Vhi;A4Vx;Vn;A3F_;F_;F_;F_;F_;F_;").
Proof.
  intros Hn Hlo Hhi H1 H2 Hd. destruct e as [ea esz]. cbn [fst snd] in *.
  pose proof (urange ea) as Ra. pose proof (urange esz) as Rs. unfold iv_subtract.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned ea <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    exists (ea, Z_to_bv 64 (Z.min (bv_unsigned esz) (lo - bv_unsigned ea))). split; [apply in_app_iff; left; left; reflexivity|].
    cbn [fst snd]. rewrite u64 by lia. lia.
  - replace (hi <? bv_unsigned ea + bv_unsigned esz) with true by (symmetry; apply Z.ltb_lt; lia).
    exists (Z_to_bv 64 (Z.max (bv_unsigned ea) hi), Z_to_bv 64 (bv_unsigned ea + bv_unsigned esz - Z.max (bv_unsigned ea) hi)).
    split; [apply in_app_iff; right; left; reflexivity|]. cbn [fst snd]. rewrite !u64 by lia. lia.
Qed.

Lemma maps_subtract_keeps l lo hi x n : ltac2:(tb__ "0|1|
S43Z0M0Vn;A2S41G0Vlo;A2S43Vhi;S44Z2Z40A2A2S2S41S42Vx;Vn;A2Vlo;A2S41Vhi;Vx;A2A2SbcVl;Vx;Vn;A3SbcSb2Vl;Vlo;Vhi;A3Vx;Vn;A3F_;F_;F_;F_;F_;").
Proof.
  intros Hn Hlo Hhi Hd. induction l as [|[ea esz] l IH]; intros (e & He & R1 & R2); [destruct He|].
  cbn [maps_subtract]. destruct He as [<-|He].
  - destruct (iv_subtract_keeps (ea, esz) lo hi x n Hn Hlo Hhi R1 R2 Hd) as (e' & He' & R'). exists e'. split; [apply in_app_iff; left; exact He' | exact R'].
  - destruct (IH ltac:(exists e; auto)) as (e' & He' & R'). exists e'. split; [apply in_app_iff; right; exact He' | exact R'].
Qed.

Lemma iv_subtract_piece (e e' : word * word) lo hi : ltac2:(tb__ "0|7|
S41Z0Vlo;A2S41Vlo;Vhi;A2S43Vhi;S44Z2Z40A2A2S3cS98Sa9Q40M0A1M1G1A2Ve';Sb3S9fG1G1Ve;A3M2Sa0G1G1Ve;A3M3Vlo;Vhi;A4A3S1S41Sa8G0G2A2M4Sa8G0S9fG1G1Ve';A3A2M5A2S1S41S42G5Sa8G0Sa0G1G1Ve';A3A2A2M6S42G4Sa8G0G3A2A2A2S2S41G6Vlo;A2S41Vhi;G5A2A2A2A2F_;F_;F_;F_;").
Proof.
  intros Hlo Hlh Hhi Hin. destruct e as [ea esz]. cbn [fst snd] in *. pose proof (urange ea) as Ra. pose proof (urange esz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned ea <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite u64 by lia. lia.
  - destruct (hi <? bv_unsigned ea + bv_unsigned esz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite !u64 by lia. lia.
Qed.

Lemma maps_subtract_piece l lo hi e' : ltac2:(tb__ "0|6|
S41Z0Vlo;A2S41Vlo;Vhi;A2S43Vhi;S44Z2Z40A2A2S3cS98Sa9Q40M0A1M1G1A2M2Ve';Sb2Vl;Vlo;Vhi;A3A3S4G2G2S1S3cG2R1Vl;A3S1S41Sa8G0S9fG1G1R1A3A2M3Sa8G0S9fG1G1Ve';A3A2M4A2S1S41S42G4Sa8G0Sa0G1G1Ve';A3A2A2M5S42G3Sa8G0Sa0G1G1R1A3A2A2A2S2S41G5Vlo;A2S41Vhi;G4A2A2A2A2A2Le;A2F_;F_;F_;F_;").
Proof.
  intros Hlo Hlh Hhi. induction l as [|[ea esz] l IH]; intros Hin; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (ea, esz). split; [left; reflexivity|]. exact (iv_subtract_piece (ea, esz) e' lo hi Hlo Hlh Hhi Hin).
  - destruct (IH Hin) as (e & He & R). exists e. split; [right; exact He | exact R].
Qed.

Lemma pairwise_insert {A} (Rr : A -> A -> Prop) (u v : list A) (x : A) : ltac2:(tb__ "0|1|
S5aVA;VRr;S9bVA;Vu;Vv;A3M0A3VA;S3cVA;R1G0A3S1VRr;Vx;R2A2VRr;R2Vx;A2A2F_;Fy;S5aVA;VRr;S9bVA;Vu;S9aVA;Vx;Vv;A3A3A3F_;F_;").
Proof.
  revert v. induction u as [|h u IH]; intros v Hp Hx; cbn in *.
  - split; [intros y Hy; apply (proj1 (Hx y Hy)) | exact Hp].
  - destruct Hp as [H1 H2]. split.
    + intros y Hy. apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply H1; apply in_app_iff; left; exact Hy | apply (proj2 (Hx h ltac:(left; reflexivity))) | apply H1; apply in_app_iff; right; exact Hy].
    + apply IH; [exact H2|]. intros y Hy. apply Hx. right. exact Hy.
Qed.

Section Pigeonhole.
  Variable w : Z.
  Hypothesis Hw : 0 < w.
  Let Rd (x y : Z) : Prop := ltac2:(tb__ "0|0|
S2S41S42Vx;Vw;A2Vy;A2S41S42Vy;Vw;A2Vx;A2A2").

  Lemma pairwise_app_split {A} (Rr : A -> A -> Prop) (u v : list A) (x : A) : ltac2:(tb__ "0|0|
S5aVA;VRr;S9bVA;Vu;S9aVA;Vx;Vv;A3A3A3S1S5aVA;VRr;S9bVA;Vu;Vv;A3A3S1VA;S3cVA;R1Vu;A3VRr;R2Vx;A2F_;Fy;VA;S3cVA;R1Vv;A3VRr;Vx;R2A2F_;Fy;A2A2F_;").
  Proof using .
    revert v. induction u as [|h u IH]; intros v Hp; cbn in *.
    - destruct Hp as [H1 H2]. split; [exact H2|]. split; [intros y []|exact H1].
    - destruct Hp as [H1 H2]. destruct (IH v H2) as (P1 & P2 & P3). split; [split; [|exact P1]|split; [|exact P3]].
      + intros y Hy. apply H1. apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy].
      + intros y [<-|Hy]; [apply H1; apply in_app_iff; right; left; reflexivity | exact (P2 y Hy)].
  Qed.

  Fixpoint list_min (d : Z) (l : list Z) : Z := match l with [] => d | x :: t => Z.min x (list_min d t) end.
  Lemma list_min_In d l : ltac2:(tb__ "0|0|
S3cS7Sd3Vd;Vl;A2S9aS7Vd;Vl;A3A3").
  Proof using .
    induction l as [|x t IH]; cbn; [left; reflexivity|].
    destruct (Z.min_spec x (list_min d t)) as [[_ E]|[_ E]]; rewrite E; [right; left; reflexivity|].
    destruct IH as [H|H]; [left; exact H | right; right; exact H].
  Qed.
  Lemma list_min_le d l y : ltac2:(tb__ "0|0|
S3cS7Vy;S9aS7Vd;Vl;A3A3S41Sd3Vd;Vl;A2Vy;A2F_;").
  Proof using Rd. induction l as [|x t IH]; cbn; intros Hy; [destruct Hy as [<-|[]]; lia|]. destruct Hy as [<-|[<-|Hy]]; [specialize (IH (or_introl eq_refl)); lia | lia | specialize (IH (or_intror Hy)); lia]. Qed.

  Theorem disjoint_count : ltac2:(tb__ "0|0|
S9dS99S7A1S7S7S0S9dSa6S7R3A2R4A3S7S3cS7R1R5A3S1S41R5R2A2S41S42R2Vw;A2R4A2A2F_;Fx;S5aS7VRd;R5A3S41S47S46R7A1Vw;A2S48Z0S45R4R5A2A2A2F_;F_;F_;Fhi;Flo;Fl;Fn;").
  Proof using Hw.
    induction n as [|n IH]; intros l lo hi Hlen Hb Hp; [lia|].
    destruct l as [|d t]; [discriminate|]. cbn in Hlen.
    set (m := list_min d t).
    pose proof (list_min_In d t) as Hm. fold m in Hm.
    destruct (in_split m (d :: t) Hm) as (u & v & E).
    rewrite E in Hb, Hp. destruct (pairwise_app_split Rd u v m Hp) as (P1 & P2 & P3).
    assert (ABOVE : forall y, In y (u ++ v) -> m + w <= y).
    { intros y Hy. pose proof (list_min_le d t y ltac:(rewrite E; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy])) as LE. fold m in LE.
      apply in_app_iff in Hy as [Hy|Hy]; [pose proof (P2 y Hy) as Q | pose proof (P3 y Hy) as Q]; unfold Rd in Q; lia. }
    pose proof (Hb m ltac:(apply in_app_iff; right; left; reflexivity)) as [Bm1 Bm2].
    assert (LEN : length (u ++ v) = n).
    { apply (f_equal (@length Z)) in E. rewrite length_app in E. cbn in E. rewrite length_app. lia. }
    pose proof (IH (u ++ v) (m + w) hi LEN ltac:(intros y Hy; split; [exact (ABOVE y Hy) | apply Hb; apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy]]) P1) as R0.
    rewrite Nat2Z.inj_succ. lia.
  Qed.
End Pigeonhole.

Lemma pairwise_of_NoDup {A B} (Rr : B -> B -> Prop) (f : A -> B) (l : list A) : ltac2:(tb__ "0|1|
S3fVA;Vl;A2VA;VA;S3cVA;R2Vl;A3M0G0S3S0VA;R4R3A3A1VRr;Vf;R5A1Vf;R4A1A2F_;F_;F_;Fb;Fa;S5aVB;VRr;Sc5VA;VB;Vf;Vl;A4A3F_;F_;").
Proof.
  induction l as [|a t IH]; intros ND H; cbn; [exact I|].
  inversion ND as [|a' t' Hna Hnd]; subst.
  assert (Hna' : ~ In a t) by (intros Q; apply Hna; first [exact Q | apply (proj2 (list_elem_of_In t a)); exact Q]).
  split.
  - intros y Hy. apply in_map_iff in Hy as (b & <- & Hb). apply H; [left; reflexivity | right; exact Hb | intros ->; exact (Hna' Hb)].
  - apply IH; [exact Hnd|]. intros x y Hx Hy Hne. apply H; [right; exact Hx | right; exact Hy | exact Hne].
Qed.

Theorem areas_bound X R U s L C vm : ltac2:(tb__ "0|0|
S5eVX;VR;VU;Vs;A4S75VL;Vs;A2SbdVL;Vs;Vvm;A3SbfVC;Vvm;A2S43S46Sa6S8SbVs;A1A2A1S44Z2Z23A2A2F_;F_;F_;F_;").
Proof.
  intros HI HL HV HLG. pose proof HL as (_ & _ & PW & _). pose proof HV as (_ & _ & _ & V5 & _). pose proof (inv_areas HI) as (ND & _).
  set (l := map (fun a => addr_of L a) (st_areas s)).
  assert (LEN : length l = length (st_areas s)) by (unfold l; apply length_map).
  assert (B : forall x, In x l -> PGSZ <= x /\ x + PGSZ <= topL L).
  { intros x Hx. unfold l in Hx. apply in_map_iff in Hx as (a & <- & Ha).
    destruct (V5 a PGSZ ltac:(right; apply in_app_iff; left; apply in_map_iff; exists a; auto)) as (e & He & R1 & R2).
    destruct (HLG e He) as (G1 & G2 & _). rewrite <- (vm_ok_top L s vm HV) in G2. lia. }
  assert (PWl : pairwise (fun x y => x + PGSZ <= y \/ y + PGSZ <= x) l).
  { unfold l. apply pairwise_of_NoDup; [exact ND|]. intros a b Ha Hb Hab.
    assert (Ia : In (LMem a, PGSZ) (footprint s)) by (right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
    assert (Ib : In (LMem b, PGSZ) (footprint s)) by (right; apply in_app_iff; left; apply in_map_iff; exists b; auto).
    destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW Ia Ib ltac:(intros E; injection E as E'; exact (Hab E'))) as [D|D];
      unfold ranges_disjoint, crange, addr_of in *; cbn [fst snd] in D; lia. }
  pose proof (disjoint_count PGSZ ltac:(unfold PGSZ; lia) (length l) l PGSZ (topL L) eq_refl B PWl) as CNT.
  rewrite LEN in CNT. top_ranges. unfold PGSZ in CNT. lia.
Qed.

Ltac in_list := solve [ cbn; repeat first [ left; reflexivity | right ] ].

Section RES.
  Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (t : astate) (L : layout).
  Hypothesis HI : ltac2:(tb__ "0|0|
S5eVX;VR;VU;Vt;A4").
  Hypothesis HX : xraw X t.
  Hypothesis Hhd : st_free_meta_head t = None.
  Hypothesis Hcnt : st_avail_meta_count t = 0.
  Hypothesis Hac : st_avail_meta_area_count t = 0.
  Hypothesis Hbrk : ltac2:(tb__ "0|0|
S0S27S2bVt;A1S23A3").
  Hypothesis Hinit : st_init_done t = true.
  Hypothesis HL : layout_ok L t.

  Definition rr : nat := length (st_regions t).
  Definition lenZ : Z := res_n t * PGSZ.
  Definition pnew : sptr := SP rr PGSZ.
  Definition mnew : sptr := padd pnew AREA_HDR.
  Definition t1 : astate := t_RES1 t.
  Definition t2 : astate := s_RESok t.

  Definition rg1 : region := ltac2:(tb__ "0|0|
S2eS13S80Sa2S7A1Sa5A4").
  Definition rg2 : region := ltac2:(tb__ "0|0|
S2eS13S80S9aS7SaSa2S7A1A3Sa5A4").

  Lemma s0_t : ltac2:(tb__ "0|0|
S0S19ScfVt;A1Vt;A3").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. unfold s0. destruct t; cbn in *. rewrite Hinit. reflexivity. Qed.

  Lemma SPEC1 : ltac2:(tb__ "0|0|
SceVX;VR;VU;Vt;Sa4S9cS8A1S19Sa3S8A1S7eA4A5").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof (yields_NB t Hhd Hcnt Hac Hbrk 1 0) as Y. rewrite s0_t in Y. unfold r_RES in Y. cbn [Z.eqb] in Y.
    exact (am_spec_of_yields X R U t HI _ _ Y).
  Qed.
  Lemma SPEC2 : ltac2:(tb__ "0|0|
SceVX;VR;VU;Vt;Sa4S9cS8A1S19S9eS8S82A2S7dA4A5").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof (yields_NB t Hhd Hcnt Hac Hbrk 1 1) as Y. rewrite s0_t in Y. unfold r_RES in Y. cbn [Z.eqb] in Y.
    exact (am_spec_of_yields X R U t HI _ _ Y).
  Qed.
  Lemma HI1 : ltac2:(tb__ "0|0|
S5eVX;VR;VU;S7eA4"). Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. exact (proj1 SPEC1). Qed.
  Lemma HI2 : ltac2:(tb__ "0|0|
S5eS9aS8S82VX;A3VR;VU;S7dA4"). Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. exact (proj1 SPEC2). Qed.

  Lemma t1_fields : ltac2:(tb__ "0|3|
S1S0S99S9A1SdS7eA1S9bS9SdVt;A1S9aS9S91Sa2S9A1A3A3A3S1S0S99S8A1SbS7eA1SbVt;A1A3S1S0S99S98S8ScA2A1S17S7eA1S17Vt;A1A3S1S0S27S2bS7eA1S23A3S1S0Sa1S31S7eA1Sa5A3S1S0S9cS8A1M0S2cS7eA1Sa3S8A1A3S1S0S8S29S7eA1S29Vt;A1A3S1S0S7S30S7eA1Z0A3S1S0S7S2aS7eA1S45ScdVt;A1Z1M1A2A3S1S0S7S12S7eA1S42S12Vt;A1G1A2A3S1S0G0S1cS7eA1S1cVt;A1A3S1S0G0S28S7eA1S28Vt;A1A3S1S0S8S2fS7eA1S7fA3S1S0S99G0A1S16S7eA1S16Vt;A1A3S1S0S99S7A1M2S1fS7eA1S1fVt;A1A3S1S0G2S1eS7eA1S1eVt;A1A3S1S0G2S1dS7eA1S1dVt;A1A3S1S0S7S22S7eA1S22Vt;A1A3S0S7S21S7eA1S21Vt;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using Hbrk Hcnt Hhd Hinit. unfold t1, t_RES1, rg1, lenZ, pnew, rr, res_r. repeat split; try reflexivity; assumption. Qed.

  Lemma t2_eq : ltac2:(tb__ "0|0|
S0S19S7dSd0Sd7S7fS1bS1aS9SdS7eA1S83S85A4S7eA2A2A1A3").
  Proof using . reflexivity. Qed.

  Lemma t2_fields : ltac2:(tb__ "0|4|
S1S0S99S9A1SdS7dA1S9bS9SdVt;A1S9aS9S85Sa2S9A1A3A3A3S1S0S99S8A1SbS7dA1S9bS8SbVt;A1S9aS8S7fSa2S8A1A3A3A3S1S0S99S98S8ScA2A1S17S7dA1S37S17Vt;A1S82S26A3A3S1S0S27S2bS7dA1S23A3S1S0Sa1S31S7dA1Sa5A3S1S0S9cS8A1M0S2cS7dA1Sa3S8A1A3S1S0S8S29S7dA1S14S82S25A2A3S1S0S7S30S7dA1S45S24Z1M1A2A3S1S0S7S2aS7dA1S45S45ScdVt;A1G1A2G1A2A3S1S0S7S12S7dA1S42S12Vt;A1G1A2A3S1S0G0S1cS7dA1G0G0Lx;S1cVt;A1S8S9eS8R1A2Ls;S9eS8S7fA2M2X9cx2A3S1S0G0S28S7dA1G2A3S1S0S8S2fS7dA1S14S7fZ1000A2A3S1S0S99G0A1S16S7dA1S16Vt;A1A3S1S0S99S7A1M3S1fS7dA1S1fVt;A1A3S1S0G3S1eS7dA1S1eVt;A1A3S1S0G3S1dS7dA1S1dVt;A1A3S1S0S7S22S7dA1S22Vt;A1A3S0S7S21S7dA1S21Vt;A1A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
  Proof using Hbrk Hhd Hinit.
    unfold t2, s_RESok, take, open_st, t_RES1, rg2, lenZ, mnew, pnew, rr, res_r. cbn -[Z.mul Z.add Z.sub Z.shiftl padd METAS_PER_AREA].
    rewrite lupd_app_last. repeat split; try reflexivity; try assumption.
  Qed.

  Definition C_ac (z : Z) : mcell := ltac2:(tb__ "0|0|
S4fS4cS69A1U8S57Vz;A1A3").
  Definition C_sh : mcell := ltac2:(tb__ "0|0|
S4fS4cS6aA1U8S57S42S12Vt;A1Z1A2A1A3").
  Definition C_ars (p : sptr) : mcell := ltac2:(tb__ "0|0|
S4fS4cS58A1U8S62Vp;A1A3").
  Definition CHG1 : list mcell := ltac2:(tb__ "0|0|
S9aS4aS8bS45ScdVt;A1Z1A2A1S9aS4aS8dS9aS4aS8cS7fA1Sa2S4aA1A3A3A3").

  Definition old_ctx1 (c : mcell) : Prop := ltac2:(tb__ "0|1|
S1S3cS4aVc;S55Vt;A1A3S1S3S0S4bS50Vc;A1M0S4cS69A1A3A1S1S3S0S4bG0S4cS6aA1A3A1S3S0S4bG0S4cS58A1A3A1A2A2A2").

  Lemma res_n_ge2 : 2 <= res_n t.
  Proof using HI.
    unfold res_n. pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&_&_&C10&_). rewrite Z.shiftl_mul_pow2 by lia.
    assert (1 <= 2 ^ st_meta_alloc_shift t) by (apply (Z.pow_le_mono_r 2 0); lia). lia.
  Qed.

  Lemma ctx_maps_loc u c : ltac2:(tb__ "0|8|
S3cS4aVc;S9bS4aSc5S9dS4aS9dS4fS4cS42S67S47Z8S46R1A1M0A2M1A2A1U8M2S65Sc6S9cS8A1R1S16Vu;A1Sa3S8A1A4A1A3Lk;Sc7U0M3U30A2M4A4S9bS4aSc5S9dS4aS9dS4fS4cS42S72G1A2A1G2S57Sc6S7R1S1fVu;A1Z0M5A4A1A3Lk;G4A4S9bS4aSc5S9dS4aS9dS4fS4cS42S71G0A2A1U1M6S57Sc6S7R1S1eVu;A1G5A4A1A3Lk;Sc7G3U20A2M7A4Sc5S9dS4aS9dS4fS4cS42S6eG0A2A1G6S57Sc6S7R1S1dVu;A1G5A4A1A3Lk;G7A4A3A3A3A3S4S7S7S1S0S4bS50Vc;A1S4cR1A1A3S41S67R1A2A2Lo;A2F_;").
  Proof using .
    intros Hin. unfold CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in *.
    apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]];
      apply in_map_iff in Hin as (k & <- & _); cbn [mc_loc]; eexists; (split; [reflexivity | lia]).
  Qed.

  Lemma ctx_cells_t1 c : ltac2:(tb__ "0|0|
S3cS4aVc;S55S7eA1A3S2S3cS4aVc;S89A3S8fVc;A1A2F_;").
  Proof using HI Hac Hbrk Hcnt Hhd Hinit.
    pose proof res_n_ge2 as R2. intros Hin. unfold old_ctx1.
    unfold t1, t_RES1, ctx_cells in Hin. cbn -[Z.add Z.mul Z.sub Z.of_nat seq map padd Z.shiftl Z.eqb In app] in Hin.
    rewrite Hbrk, Hinit, Hhd, Hcnt in Hin.
    replace (res_n t - 1 =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; lia). rewrite Bool.andb_false_r in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - cbn [In] in Hin.
      unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
        CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
      unfold CHG1, C_ac, C_sh, C_ars, ctx_cells. rewrite Hbrk, Hinit, Hhd, Hcnt, Hac.
      unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
        CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        first [ left; in_list
              | right; (split; [apply in_app_iff; left; in_list | cbn [mc_loc]; repeat split; intros E; injection E as E'; lia]) ].
    - right. split; [unfold ctx_cells; apply in_app_iff; right; exact Hin|].
      destruct (ctx_maps_loc _ c Hin) as (o & -> & Ho). unfold CTX_active, CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_avail_meta_areas in *.
      repeat split; intros E; injection E as E'; lia.
  Qed.

  Lemma old_noctx_loc c : ltac2:(tb__ "0|2|
S2S3cS4aVc;S9bS4aS6bVt;SbVt;A1A2S3dS98S8S18A2M0S4aG0S74S9fS8S18R1A3Sa0S8S18R1A3A2Lgm;S7cVt;A1A4A3A3S3cS4aVc;SaaVt;A1M1A3A2S1S3cS4aVc;S9bS4aS52Vt;A1G1A3A3S4S8S8S0S4bS50Vc;A1S51R1A1A3Lq;A2A2F_;").
  Proof using HI HX.
    intros H. split.
    - apply in_app_iff. destruct H as [H|H]; [left; unfold image; apply in_app_iff; right; exact H | right; exact H].
    - destruct H as [H|H].
      + apply in_app_iff in H as [H|H].
        * destruct (In_areas_cells t _ c H) as (a & next & _ & Hc). destruct (In_area_cells t a next c Hc) as (d & E & _). rewrite E. eexists; reflexivity.
        * apply in_flat_map in H as ([g am] & Hg & Hc). cbn [fst snd] in Hc.
          destruct (In_group_cells X R U t g am c HI (proj1 (used_iff X R U t HI HX g am) Hg) Hc) as (d & E & _). rewrite E. eexists; reflexivity.
      + unfold footer_cells in H. apply in_flat_map in H as ([g am] & Hg & Hc). cbn [fst snd] in Hc.
        destruct (In_group_footer_cells X R U t g am c HI (proj1 (used_iff X R U t HI HX g am) Hg) Hc) as (d & E & _). rewrite E. eexists; reflexivity.
  Qed.

  Theorem image_t1 c : ltac2:(tb__ "0|0|
S3cS4aVc;S9bS4aS52S7eA1SaaS7eA1A3A3S2S3cS4aVc;S89A3S2S8fVc;A1S1S3cS4aVc;S9bS4aS52Vt;A1SaaVt;A1A3A3S4S8S8S0S4bS50Vc;A1S51R1A1A3Lq;A2A2A2A2F_;").
  Proof using HI HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof t1_fields as (F1 & F2 & F3 & _).
    intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - unfold image in Hin. apply in_app_iff in Hin as [Hin|Hin]; [destruct (ctx_cells_t1 c Hin); tauto|].
      right; right. apply old_noctx_loc. left. rewrite F2, (co_areas_cells t t1 F3), (co_used_metas t t1 F3) in Hin. exact Hin.
    - right; right. apply old_noctx_loc. right. rewrite (co_footers t t1 F3) in Hin. exact Hin.
  Qed.

  Definition C_avm2 : mcell := ltac2:(tb__ "0|0|
S4fS4cS68A1U8S62S14S82S25A2A1A3").
  Definition C_cnt2 : mcell := ltac2:(tb__ "0|0|
S4fS4cS6dA1U8S57S45S24Z1A2A1A3").
  Definition C_hd2 : mcell := ltac2:(tb__ "0|1|
S4fS4cS6fA1U8S65S9cS8A1M0G0Lx;S1cVt;A1S8S9eS8R1A2Ls;S9eS8S7fA2X9cx2A1A3").
  Definition C_tl2 : mcell := ltac2:(tb__ "0|0|
S4fS4cS70A1U8S62S7fA1A3").
  Definition CHG2 : list mcell := ltac2:(tb__ "0|1|
S9aS4aS94S9aS4aS95S9aS4aS8bS45S45ScdVt;A1Z1M0A2G0A2A1S9aS4aS8dS9aS4aS96S9aS4aS97S9aS4aS8cS14S7fZ1000A2A1Sa2S4aA1A3A3A3A3A3A3A3").
  Definition old_ctx2 (c : mcell) : Prop := ltac2:(tb__ "0|0|
S1S3cS4aVc;S55Vt;A1A3S4S7S7S1S0S4bS50Vc;A1S4cR1A1A3S2S41S42R1S46S64Vc;A1A1A2S68A2S41S42S58Z8A2R1A2A2A2Lo;A2A2").

  Definition C_tn : mcell := ltac2:(tb__ "0|0|
S4fS51S14S3eS8SbVt;A1S33U0Z0A2A3Z8A2A1U8S62S7fA1A3").

  Lemma fresh_slot q : ltac2:(tb__ "0|0|
S0S9dS10Vq;A1S83A3S0S9cScA1S61Vt;Vq;A2Sa3ScA1A3F_;").
  Proof using HI.
    intros Hq. destruct (MT t q) as [x|] eqn:E; [|reflexivity]. exfalso.
    pose proof (key_below X R U t HI q (MT_Some_In_keys _ _ _ E)) as B. unfold rr in Hq. lia.
  Qed.
  Lemma pnew_fresh : ltac2:(tb__ "0|0|
S3S3cS8S7fSbVt;A1A3A1").
  Proof using HI. intros Hin. pose proof (area_below X R U t HI pnew Hin) as B. unfold pnew, rr in B. cbn in B. lia. Qed.

  Lemma ctx_cells_t2 c : ltac2:(tb__ "0|0|
S3cS4aVc;S55S7dA1A3S2S3cS4aVc;S8aA3S90Vc;A1A2F_;").
  Proof using HI Hac Hbrk Hcnt Hhd Hinit.
    pose proof res_n_ge2 as R2. intros Hin. unfold old_ctx2.
    pose proof t2_fields as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19).
    unfold ctx_cells in Hin. rewrite F2, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19 in Hin.
    apply in_app_iff in Hin as [Hin|Hin].
    - cbn [In] in Hin.
      unfold CHG2, C_avm2, C_cnt2, C_ac, C_sh, C_hd2, C_tl2, C_ars, ctx_cells. rewrite Hbrk, Hinit, Hhd, Hcnt, Hac.
      unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
        CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk in *.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
        first [ left; in_list
              | right; (split; [apply in_app_iff; left; in_list | cbn [mc_loc mc_w]; eexists; (split; [reflexivity | cbn; lia])])
              | idtac ].
        all: left; destruct (st_areas t); in_list.
    - right. split; [unfold ctx_cells; apply in_app_iff; right; exact Hin|].
      destruct (ctx_maps_loc _ c Hin) as (o & -> & Ho). exists o. split; [reflexivity|]. right. unfold CTX_active, CTX_avail_meta_areas in *. lia.
  Qed.

  Definition t2pre : astate := ltac2:(tb__ "0|0|
S39S14S82S25A2S3aS45S24Z1A2Sd7S7fS1bS1aS9SdS7eA1S83S85A4S7eA2A2A2A2").
  Lemma t2_upd : ltac2:(tb__ "0|0|
S0S19S7dSd5S82S26S86A3A3").
  Proof using . reflexivity. Qed.
  Lemma t2pre_fields : ltac2:(tb__ "0|0|
S1S0S99S98S8ScA2A1S17S86A1S17Vt;A1A3S1S0S99S8A1SbS86A1S9bS8SbVt;A1S9aS8S7fSa2S8A1A3A3A3S0S99S4aA1S55S86A1S55S7dA1A3A2A2").
  Proof using . repeat split; reflexivity. Qed.

  Lemma mnew_prid : prid mnew = rr. Proof using . reflexivity. Qed.

  Lemma area_cells_t2 : ltac2:(tb__ "0|1|
S0S99S4aA1S5fS7dS7fSa3S8A1M0A3S5fVt;S7fG0A3A3").
  Proof using HI Hbrk Hhd Hinit.
    pose proof t2_fields as (_ & _ & F3 & _).
    assert (E : forall k, meta_slot_cells (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)) (mlookup (st_metas t2) (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)))
                        = meta_slot_cells (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)) (mlookup (st_metas t) (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)))).
    { intros k. rewrite F3. rewrite mlookup_mupdate.
      assert (FR : mlookup (st_metas t) (padd pnew (AREA_HDR + META_SIZE * Z.of_nat k)) = None) by (apply fresh_slot; reflexivity).
      rewrite FR. destruct (sptr_eqb _ _); [apply meta_slot_cells_raw | reflexivity]. }
    unfold area_cells. f_equal.
    induction (seq 0 (Z.to_nat METAS_PER_AREA)) as [|k l IH]; [reflexivity|]. cbn [flat_map]. rewrite (E k), IH. reflexivity.
  Qed.

  Theorem image_t2 c : ltac2:(tb__ "0|0|
S3cS4aVc;S9bS4aS52S7dA1SaaS7dA1A3A3S2S3cS4aVc;S8aA3S2S90Vc;A1S2S1S3S0S99S8A1SbVt;A1Sa2S8A1A3A1S0S4aVc;S8eA3A2S2S3cS4aVc;S5fS7dS7fSa3S8A1A3A3S1S3cS4aVc;S9bS4aS52Vt;A1SaaVt;A1A3A3S4S8S8S0S4bS50Vc;A1S51R1A1A3Lq;A2A2A2A2A2A2F_;").
  Proof using HI HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof t2pre_fields as (P1 & P2 & P3).
    assert (NU : nonused (MT t2pre mnew)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) mnew) with (MT t mnew); rewrite (fresh_slot mnew mnew_prid); exact I).
    intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite t2_upd in Hin. destruct (uf_image_In t2pre mnew MRaw NU I c Hin) as [H|H].
      + unfold image in H. apply in_app_iff in H as [H|H]; [rewrite P3 in H; destruct (ctx_cells_t2 c H); tauto|].
        rewrite P2, (co_areas_cells t t2pre P1), (co_used_metas t t2pre P1) in H.
        apply in_app_iff in H as [H|H].
        * destruct (ap_areas_cells_In t t pnew eq_refl (st_areas t) c H) as [Ho|[Htn|Hnew]].
          -- right; right; right; right. apply old_noctx_loc. left. apply in_app_iff. left. exact Ho.
          -- right; right; left. exact Htn.
          -- right; right; right; left. rewrite area_cells_t2. exact Hnew.
        * right; right; right; right. apply old_noctx_loc. left. apply in_app_iff. right. exact H.
      + right; right; right; left. rewrite area_cells_t2. unfold area_cells. apply in_app_iff. right.
        apply in_flat_map. exists 0%nat. split; [apply in_seq; unfold METAS_PER_AREA; lia|].
        replace (padd pnew (AREA_HDR + META_SIZE * Z.of_nat 0)) with mnew by (unfold mnew; f_equal).
        change (mlookup (st_metas t) mnew) with (MT t mnew). rewrite (fresh_slot mnew mnew_prid). rewrite meta_slot_cells_raw in H. exact H.
    - right; right; right; right. apply old_noctx_loc. right.
      rewrite t2_upd, (uf_footers t2pre mnew MRaw NU I), (co_footers t t2pre P1) in Hin. exact Hin.
  Qed.

  Theorem image_t2C c : ltac2:(tb__ "0|0|
S3cS4aVc;S9bS4aS52S7dA1SaaS7dA1A3A3S2S3cS4aVc;S55S7dA1A3S2S1S3S0S99S8A1SbVt;A1Sa2S8A1A3A1S0S4aVc;S8eA3A2S2S3cS4aVc;S5fS7dS7fSa3S8A1A3A3S1S3cS4aVc;S9bS4aS52Vt;A1SaaVt;A1A3A3S4S8S8S0S4bS50Vc;A1S51R1A1A3Lq;A2A2A2A2A2F_;").
  Proof using HI HX Hbrk Hhd Hinit.
    pose proof t2pre_fields as (P1 & P2 & P3).
    assert (NU : nonused (MT t2pre mnew)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) mnew) with (MT t mnew); rewrite (fresh_slot mnew mnew_prid); exact I).
    intros Hin. apply in_app_iff in Hin as [Hin|Hin].
    - rewrite t2_upd in Hin. destruct (uf_image_In t2pre mnew MRaw NU I c Hin) as [H|H].
      + unfold image in H. apply in_app_iff in H as [H|H]; [left; rewrite <- P3; exact H|].
        rewrite P2, (co_areas_cells t t2pre P1), (co_used_metas t t2pre P1) in H.
        apply in_app_iff in H as [H|H].
        * destruct (ap_areas_cells_In t t pnew eq_refl (st_areas t) c H) as [Ho|[Htn|Hnew]].
          -- right; right; right. apply old_noctx_loc. left. apply in_app_iff. left. exact Ho.
          -- right; left. exact Htn.
          -- right; right; left. rewrite area_cells_t2. exact Hnew.
        * right; right; right. apply old_noctx_loc. left. apply in_app_iff. right. exact H.
      + right; right; left. rewrite area_cells_t2. unfold area_cells. apply in_app_iff. right.
        apply in_flat_map. exists 0%nat. split; [apply in_seq; unfold METAS_PER_AREA; lia|].
        replace (padd pnew (AREA_HDR + META_SIZE * Z.of_nat 0)) with mnew by (unfold mnew; f_equal).
        change (mlookup (st_metas t) mnew) with (MT t mnew). rewrite (fresh_slot mnew mnew_prid). rewrite meta_slot_cells_raw in H. exact H.
    - right; right; right. apply old_noctx_loc. right.
      rewrite t2_upd, (uf_footers t2pre mnew MRaw NU I), (co_footers t t2pre P1) in Hin. exact Hin.
  Qed.

  Lemma ctx_cells_t2C c : ltac2:(tb__ "0|1|
S3cS4aVc;S55S7dA1A3S2S4S7S7S4S9dS9dS4S5bS5bS1S0S4aVc;S4fS4cR3A1R2R1A3A3S1SacU0R2A2S2S1S41Z0R3A2S41S42R3S46R2A1A2M0ZcA2A2S2S1S41Z10R3A2S41G0Z50A2A2S1S41Z398R3A2S41G0Z3a0A2A2A2A2A2A2Lval;A2Lw;A2Lo;A2S1S3cS4aVc;S55Vt;A1A3S3S0S4bS50Vc;A1S4cS58A1A3A1A2A2F_;").
  Proof using HI Hac Hbrk Hcnt Hhd Hinit.
    intros Hc. destruct (ctx_cells_t2 c Hc) as [H|(Hin & o & Eo & Ho)].
    - left. unfold CHG2, C_avm2, C_cnt2, C_ac, C_sh, C_hd2, C_tl2, C_ars in H. cbn [In] in H.
      unfold CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas in H.
      destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; eexists _, _, _; (split; [reflexivity|]); (split; [cbn; lia | cbn; lia]).
    - right. split; [exact Hin|]. intros E. rewrite Eo in E. injection E as E'. pose proof (cell_w_posI t c ltac:(apply in_app_iff; left; unfold image; apply in_app_iff; left; exact Hin)) as WP.
      unfold CTX_avail_meta, CTX_avail_meta_areas in *. lia.
  Qed.

  Lemma fp_t1 : ltac2:(tb__ "0|0|
S0S99S98S4bS7A2A1S4eS7eA1S4eVt;A1A3").
  Proof using Hbrk Hcnt Hhd Hinit.
    pose proof t1_fields as (F1 & F2 & _). rewrite !footprint_eq, F2.
    rewrite (map_fp_regions_only (set_regions (st_regions t ++ [rg1]) t) t1) by (rewrite F1; reflexivity).
    rewrite (map_fp_app_nonmap t rg1) by (left; discriminate). reflexivity.
  Qed.
  Lemma fp_t2 e : ltac2:(tb__ "0|1|
S5S3cS98S4bS7A2M0Ve;S4eS7dA1A3S2S3cG0Ve;S4eVt;A1A3S0G0Ve;Sa4S4bS7S51S7fA1SaA4A3A2A2").
  Proof using Hbrk Hhd Hinit.
    pose proof t2_fields as (F1 & F2 & _). rewrite !In_footprint, F2.
    rewrite (map_fp_regions_only (set_regions (st_regions t ++ [rg2]) t) t2) by (rewrite F1; reflexivity).
    rewrite (map_fp_app_nonmap t rg2) by (left; discriminate).
    rewrite map_app, in_app_iff. cbn [map In]. intuition congruence.
  Qed.
  Lemma ub_t1 : ltac2:(tb__ "0|0|
S0S99S98S8S7A2A1S5dS7eA1S5dVt;A1A3").
  Proof using Hbrk Hcnt Hhd Hinit. pose proof t1_fields as (_ & _ & F3 & _). exact (co_user_blocks t t1 F3). Qed.
  Lemma ub_t2 : ltac2:(tb__ "0|0|
S0S99S98S8S7A2A1S5dS7dA1S5dVt;A1A3").
  Proof using HI.
    pose proof t2pre_fields as (P1 & _).
    assert (NU : nonused (MT t2pre mnew)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) mnew) with (MT t mnew); rewrite (fresh_slot mnew mnew_prid); exact I).
    rewrite t2_upd, (uf_user_blocks t2pre mnew MRaw NU I). exact (co_user_blocks t t2pre P1).
  Qed.
  Lemma footers_t1 : ltac2:(tb__ "0|0|
S0S99S4aA1SaaS7eA1SaaVt;A1A3").
  Proof using Hbrk Hcnt Hhd Hinit. pose proof t1_fields as (_ & _ & F3 & _). exact (co_footers t t1 F3). Qed.
  Lemma footers_t2 : ltac2:(tb__ "0|0|
S0S99S4aA1SaaS7dA1SaaVt;A1A3").
  Proof using HI.
    pose proof t2pre_fields as (P1 & _).
    assert (NU : nonused (MT t2pre mnew)) by (unfold MT; rewrite P1; change (mlookup (st_metas t) mnew) with (MT t mnew); rewrite (fresh_slot mnew mnew_prid); exact I).
    rewrite t2_upd, (uf_footers t2pre mnew MRaw NU I). exact (co_footers t t2pre P1).
  Qed.

  Variables (C : mconsts) (vm : VmMaps) (a : Z).
  Hypothesis Hctx : ltac2:(tb__ "0|0|
S0S7S60VL;A1Sc4VC;A1A3").
  Hypothesis HSI : statics_in_image C.
  Hypothesis HV : ltac2:(tb__ "0|0|
SbdVL;Vt;Vvm;A3").
  Let HVX : vm_okX L t := ltac2:(tb__ "0|0|
SccVL;Vt;Vvm;VHV;A4").
  Hypothesis HLG : ledger_ok C vm.
  Hypothesis HIR : img_reserved C vm.
  Hypothesis HB : bounded t.
  Hypothesis HMW : maps_wf vm.
  Hypothesis Ha_al : a mod PGSZ = 0.
  Hypothesis Ha_pos : 0 < a.
  Hypothesis Ha_ceil : ltac2:(tb__ "0|0|
S41S42Va;S80A2SbbVL;A1A2").
  Hypothesis Hfree : ltac2:(tb__ "0|4|
S98Sa9Q40M0A1M1G1A2M2S3cG2R1S9bG2Sb0Vvm;A1Sb1Vvm;A1A3A3S2S41S42Sa8G0S9fG1G1R2A3A2M3Sa8G0Sa0G1G1R2A3A2A2Va;A2S41S42Va;S80A2G3A2A2F_;Fe;").

  Definition L' : layout := ltac2:(tb__ "0|0|
Sc8VL;S83Va;A3").
  Definition wa : word := wz a.
  Definition wn : word := wz lenZ.
  Definition vm1 : VmMaps := ltac2:(tb__ "0|3|
Sb4Sb0Vvm;A1S9aS98Sa9Q40A1M0G0A2M1Sa4G0G0S92S93A4M2Sb1Vvm;A1A3S9aG1G2Sb9Vvm;A1A3SbaVvm;A1Sb5Vvm;A1Sb7Vvm;A1Sb8Vvm;A1Sb6Vvm;A1A8").
  Definition vm2 : VmMaps := ltac2:(tb__ "0|4|
Sb4Sb0Vvm;A1S9aS98Sa9Q40A1M0G0A2M1Sa4G0G0S92S93A4M2Sb1Vvm;A1A3Sb2S9aG1G2Sb9Vvm;A1A3S42Va;SaA2M3S42G3SaA2A3SbaVvm;A1Sb5Vvm;A1Sb7Vvm;A1Sb8Vvm;A1Sb6Vvm;A1A8").

  Lemma lenZ_facts : ltac2:(tb__ "0|1|
S1S41S47Z2M0SaA2S80A2S1S0S7S49S80SaA2Z0A3S0S7S80S47S44G0S42S12Vt;A1Z1A2A2SaA2A3A2A2").
  Proof using HB Ha_al Ha_pos.
    pose proof HB as (_ & SH & _). unfold lenZ, res_n. rewrite Z.shiftl_mul_pow2 by lia.
    assert (1 <= 2 ^ st_meta_alloc_shift t) by (apply (Z.pow_le_mono_r 2 0); lia).
    split; [unfold PGSZ; lia|]. split; [apply Z_mod_mult|]. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
  Qed.
  Lemma a_facts : ltac2:(tb__ "0|3|
S1S41SaVa;A2S1S43S42Va;S80A2S44Z2M0Z2fA2A2S1S1S41Z0M1Va;A2S43Va;S44G0Z40A2M2A2A2S1S41G1S80A2S43S80G2A2A2A2A2A2").
  Proof using HB Ha_al Ha_ceil Ha_pos.
    pose proof lenZ_facts as (L1 & L2 & _). top_ranges. unfold PGSZ in *.
    split; [Z.to_euclidean_division_equations; lia|]. lia.
  Qed.
  Lemma ua : bv_unsigned wa = a. Proof using HB Ha_al Ha_ceil Ha_pos. pose proof a_facts. unfold wa, wz. apply u64. lia. Qed.
  Lemma un : bv_unsigned wn = lenZ. Proof using HB Ha_al Ha_ceil Ha_pos. pose proof a_facts. unfold wn, wz. apply u64. lia. Qed.

  Lemma grant_vs_image x : ltac2:(tb__ "0|0|
S1S41Sc3VC;A1Vx;A2S43Vx;Sc2VC;A1A2A2S3S1S41Va;Vx;A2S43Vx;S42Va;S80A2A2A2A1F_;").
  Proof using HIR Ha_al Ha_pos Hfree.
    intros Hx Hin. destruct (HIR x Hx) as (e & He & Hex).
    pose proof (Hfree e ltac:(apply in_app_iff; left; exact He)). lia.
  Qed.
  Lemma grant_vs_maps e x : ltac2:(tb__ "0|3|
S3cS98Sa9Q40M0A1M1G1A2Ve;Sb1Vvm;A1A3S1S41Sa8G0S9fG1G1Ve;A3A2M2Vx;A2S43Vx;S42G2Sa8G0Sa0G1G1Ve;A3A2A2A2A2S3S1S41Va;Vx;A2S43Vx;S42Va;S80A2A2A2A1F_;F_;").
  Proof using Ha_al Ha_pos Hfree. intros He Hx Hin. pose proof (Hfree e ltac:(apply in_app_iff; right; exact He)). lia. Qed.
  Lemma grant_vs_footprint e x : ltac2:(tb__ "0|1|
S3cS98S4bS7A2Ve;S4eVt;A1A3S1S41S4dVL;S9fS4bS7Ve;A3A2M0Vx;A2S43Vx;S42G0Sa0S4bS7Ve;A3A2A2A2S3S1S41Va;Vx;A2S43Vx;S42Va;S80A2A2A2A1F_;F_;").
  Proof using HIR HSI HV Ha_al Ha_pos Hctx Hfree.
    intros He Hx. pose proof HV as (_ & _ & _ & V5 & _). destruct e as [[o|p] n].
    -   pose proof HSI as (_&_&_&_&_&_&_&_&_& [C1 C2] &_). cbn [fst snd loc_addr] in Hx.
      unfold footprint in He. destruct He as [E|He].
      + injection E as <- <-. apply grant_vs_image. rewrite Hctx in Hx. lia.
      + exfalso. apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & E & _); discriminate|].
        apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|]; [|destruct He]. destruct (rg_kind rg); try destruct He.
        destruct (rg_live rg); [destruct He as [E|[]]; discriminate | destruct He].
    - destruct (V5 p n He) as (e' & He' & R1 & R2). cbn [fst snd loc_addr] in Hx. unfold addr_of in R1, R2. cbn [loc_addr] in R1, R2.
      apply (grant_vs_maps e' x He'). destruct p; cbn in *. lia.
  Qed.

  Lemma fp_size e : ltac2:(tb__ "0|0|
S3cS98S4bS7A2Ve;S4eVt;A1A3S43Z0Sa0S4bS7Ve;A3A2F_;").
  Proof using HVX a.
    intros He. pose proof HVX as (_ & _ & SZ & _). unfold footprint in He. destruct He as [<-|He]; [cbn; unfold CTX_SIZE; lia|].
    apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & <- & _); cbn; unfold PGSZ; lia|].
    apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|] eqn:Ek; [|destruct He]. destruct (rg_kind rg); try destruct He.
    destruct (rg_live rg) eqn:El; [|destruct He]. destruct He as [<-|[]]. cbn. pose proof (SZ k rg Ek El). unfold PGSZ in *. lia.
  Qed.

  Lemma L'_ext : ltac2:(tb__ "0|0|
SafVL;S81S83A3"). Proof using . apply Lext_extends. Qed.
  Lemma L'_ctx : ltac2:(tb__ "0|0|
S0S7S60S81A1S60VL;A1A3"). Proof using . reflexivity. Qed.
  Lemma L'_reg_new : ltac2:(tb__ "0|0|
S0S7S56S81S83A2Va;A3"). Proof using . apply Lext_reg. Qed.
  Lemma L'_top : ltac2:(tb__ "0|0|
S0S7SbbS81A1SbbVL;A1A3"). Proof using . reflexivity. Qed.
  Lemma L'_fp e : ltac2:(tb__ "0|1|
S3cS98S4bS7A2Ve;S4eVt;A1A3S0S7S4dS81S9fS4bS7Ve;A3M0A2S4dVL;G0A2A3F_;").
  Proof using HI. intros He. exact (loc_addr_ext L L' rr _ L'_ext (footprint_below X R U t HI e He)). Qed.
  Lemma L'_crange e : ltac2:(tb__ "0|0|
S3cS98S4bS7A2Ve;S4eVt;A1A3S0S98S7S7A2S6cS81Ve;A2S6cVL;Ve;A2A3F_;").
  Proof using HI. intros He. unfold crange. rewrite (L'_fp e He). reflexivity. Qed.
  Lemma L'_ub b : ltac2:(tb__ "0|1|
S3cS98S8S7A2Vb;S5dVt;A1A3S0S7S4dS81S51S9fS8S7Vb;A3A1M0A2S4dVL;G0A2A3F_;").
  Proof using HI HX. intros Hb. apply (loc_addr_ext L L' rr _ L'_ext). cbn. exact (user_block_below X R U t HI HX b Hb). Qed.
  Lemma L'_addr_of q : ltac2:(tb__ "0|0|
SacS10Vq;A1S83A2S0S7SbeS81Vq;A2SbeVL;Vq;A2A3F_;").
  Proof using . intros Hq. unfold addr_of. apply (loc_addr_ext L L' rr _ L'_ext). exact Hq. Qed.
  Lemma L'_pnew : ltac2:(tb__ "0|0|
S0S7S4dS81S51S7fA1A2S42Va;SaA2A3").
  Proof using . cbn [loc_addr pnew]. unfold pnew. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.
  Lemma L'_mnew : ltac2:(tb__ "0|0|
S0S7SbeS81S82A2S42S42Va;SaA2S32A2A3").
  Proof using . unfold addr_of, mnew, pnew. cbn. rewrite Nat.eqb_refl. lia. Qed.

  Lemma region_of_t1 k : ltac2:(tb__ "0|1|
S0S9cS9A1M0S54S7eVk;A2Sa1G0L_;Sd2Vk;S83A2S9eS9S91A2S54Vt;Vk;A2Xa1x2A3").
  Proof using Ha_al Ha_pos Hbrk Hcnt Hhd Hinit.
    pose proof t1_fields as (F1 & _). unfold region_of. rewrite F1. unfold rr.
    destruct (Nat.eqb k (length (st_regions t))) eqn:E.
    - apply Nat.eqb_eq in E. subst k. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - apply Nat.eqb_neq in E. destruct (Nat.lt_ge_cases k (length (st_regions t))) as [Hlt|Hge].
      + rewrite nth_error_app1 by exact Hlt. reflexivity.
      + rewrite nth_error_app2 by lia. replace (nth_error (st_regions t) k) with (@None region) by (symmetry; apply nth_error_None; lia).
        destruct (k - length (st_regions t))%nat as [|k'] eqn:Ek; [lia|]. cbn. destruct k'; reflexivity.
  Qed.
  Lemma region_of_t2 k : ltac2:(tb__ "0|1|
S0S9cS9A1M0S54S7dVk;A2Sa1G0L_;Sd2Vk;S83A2S9eS9S85A2S54Vt;Vk;A2Xa1x2A3").
  Proof using Ha_al Ha_pos Hbrk Hhd Hinit.
    pose proof t2_fields as (F1 & _). unfold region_of. rewrite F1. unfold rr.
    destruct (Nat.eqb k (length (st_regions t))) eqn:E.
    - apply Nat.eqb_eq in E. subst k. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - apply Nat.eqb_neq in E. destruct (Nat.lt_ge_cases k (length (st_regions t))) as [Hlt|Hge].
      + rewrite nth_error_app1 by exact Hlt. reflexivity.
      + rewrite nth_error_app2 by lia. replace (nth_error (st_regions t) k) with (@None region) by (symmetry; apply nth_error_None; lia).
        destruct (k - length (st_regions t))%nat as [|k'] eqn:Ek; [lia|]. cbn. destruct k'; reflexivity.
  Qed.

  Theorem layout_ok_t1 : layout_ok L' t1.
  Proof using HB HI HL Ha_al Ha_ceil Ha_pos Hbrk Hcnt Hhd Hinit.
    pose proof HL as (A & B & Cc & D). pose proof a_facts as (A1 & _). rewrite fp_t1 || idtac.
    split; [rewrite L'_ctx; exact A|]. split.
    { intros k rg Hk Hl. rewrite region_of_t1 in Hk. destruct (Nat.eqb k rr) eqn:E.
      - apply Nat.eqb_eq in E. subst k. rewrite L'_reg_new. exact Ha_al.
      - apply Nat.eqb_neq in E. unfold L'. rewrite Lext_old by exact E. exact (B k rg Hk Hl). }
    rewrite fp_t1.
    assert (EM : map (crange L') (footprint t) = map (crange L) (footprint t)).
    { apply map_ext_in. intros e He. exact (L'_crange e He). }
    rewrite EM. split; [exact Cc|]. intros rg Hrg. rewrite (L'_crange rg Hrg). exact (D rg Hrg).
  Qed.

  Theorem layout_ok_t2 : layout_ok L' t2.
  Proof using HB HI HIR HL HSI HVX Ha_al Ha_ceil Ha_pos Hbrk Hctx Hfree Hhd Hinit.
    pose proof HL as (A & B & Cc & D). pose proof a_facts as (A1 & A2 & _). pose proof lenZ_facts as (L1 & _).
    split; [rewrite L'_ctx; exact A|]. split.
    { intros k rg Hk Hl. rewrite region_of_t2 in Hk. destruct (Nat.eqb k rr) eqn:E.
      - apply Nat.eqb_eq in E. subst k. rewrite L'_reg_new. exact Ha_al.
      - apply Nat.eqb_neq in E. unfold L'. rewrite Lext_old by exact E. exact (B k rg Hk Hl). }
    pose proof t2_fields as (F1 & F2 & _).
    assert (NEWR : crange L' (LMem pnew, PGSZ) = (a + PGSZ, PGSZ)) by (unfold crange; cbn [fst snd]; rewrite L'_pnew; reflexivity).
    assert (DISJ : forall e, In e (footprint t) -> ranges_disjoint (crange L' e) (crange L' (LMem pnew, PGSZ)) /\ ranges_disjoint (crange L' (LMem pnew, PGSZ)) (crange L' e)).
    { intros e He. rewrite (L'_crange e He), NEWR. unfold ranges_disjoint, crange. cbn [fst snd].
      pose proof (D e He) as [P1 P2]. unfold crange in P1, P2. cbn [fst snd] in P1, P2. pose proof (fp_size e He) as SZ.
      destruct (Z_le_dec (loc_addr L (fst e) + snd e) (a + PGSZ)); [lia|].
      destruct (Z_le_dec (a + PGSZ + PGSZ) (loc_addr L (fst e))); [lia|]. exfalso.
      destruct (Z_le_dec (loc_addr L (fst e)) (a + PGSZ)).
      - apply (grant_vs_footprint e (a + PGSZ) He); unfold PGSZ in *; lia.
      - apply (grant_vs_footprint e (loc_addr L (fst e)) He); unfold PGSZ in *; lia. }
    assert (FP2 : footprint t2 = ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ (LMem pnew, PGSZ) :: map_fp t).
    { rewrite footprint_eq, F2, map_app. rewrite (map_fp_regions_only (set_regions (st_regions t ++ [rg2]) t) t2) by (rewrite F1; reflexivity).
      rewrite (map_fp_app_nonmap t rg2) by (left; discriminate). cbn [map]. rewrite <- app_assoc. reflexivity. }
    assert (FP0 : footprint t = ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ map_fp t) by (rewrite footprint_eq; reflexivity).
    split.
    - rewrite FP2, map_app.
      change (map (crange L') ((LMem pnew, PGSZ) :: map_fp t)) with (crange L' (LMem pnew, PGSZ) :: map (crange L') (map_fp t)).
      assert (EQ0 : map (crange L') ((LCtx 0, CTX_SIZE) :: map (fun a0 : sptr => (LMem a0, PGSZ)) (st_areas t)) ++ map (crange L') (map_fp t) = map (crange L') (footprint t)).
      { rewrite FP0, map_app. reflexivity. }
      apply pairwise_insert.
      + rewrite EQ0. rewrite (map_ext_in (crange L') (crange L) (footprint t) L'_crange). exact Cc.
      + intros y Hy. rewrite EQ0 in Hy. apply in_map_iff in Hy as (e & <- & He). split; [apply (proj2 (DISJ e He)) | apply (proj1 (DISJ e He))].
    - intros rg Hrg. apply fp_t2 in Hrg as [Hrg| ->].
      + rewrite (L'_crange rg Hrg). exact (D rg Hrg).
      + rewrite NEWR. cbn [fst snd]. unfold PGSZ in *. lia.
  Qed.

  Lemma region_live_t k rg : ltac2:(tb__ "0|0|
S0S9cS9A1S54Vt;Vk;A2S9eS9Vrg;A2A3S0SfSeVrg;A1S13A3S0Sa1S15Vrg;A1Sa5A3F_;F_;").
  Proof using HI. intros Hk Hkd. pose proof (inv_areas HI) as (_&_&_&_&A5&_). exact (proj1 (A5 k rg Hk Hkd)). Qed.

  Lemma old_region_vs_grant k rg x : ltac2:(tb__ "0|2|
S0S9cS9A1S54Vt;Vk;A2S9eS9Vrg;A2A3S0Sa1S15Vrg;A1Sa5A3S2S0SfSeVrg;A1M0S20A3S0SfG0S13A3A2S1S41S56VL;Vk;A2M1Vx;A2S43Vx;S42G1S11Vrg;A1A2A2A2S3S1S41Va;Vx;A2S43Vx;S42Va;S80A2A2A2A1F_;F_;F_;F_;").
  Proof using HV Ha_al Ha_pos Hfree.
    intros Hk Hl Hkd Hx. pose proof HV as (V1 & V2 & _ & _ & _ & _ & X3 & X4 & _).
    destruct (X4 k rg Hk Hl) as [B1 B2]. pose proof (X3 k rg Hk Hl) as B3. top_ranges.
    assert (IN : In (wz (ly_reg L k), wz (rg_len rg)) (vm_maps vm)).
    { destruct Hkd as [Hkd|Hkd]; [exact (V1 k rg Hk Hl Hkd) | exact (proj1 (V2 k rg Hk Hkd))]. }
    apply (grant_vs_maps _ x IN). cbn [fst snd]. unfold wz. rewrite !u64 by (unfold PGSZ in *; lia). exact Hx.
  Qed.

  Theorem vm_okX_t1 : vm_okX L' t1.
  Proof using HB HI HV Ha_al Ha_ceil Ha_pos Hbrk Hcnt Hfree Hhd Hinit.
    pose proof HV as (_ & _ & _ & _ & X1 & X2 & X3 & X4 & _). pose proof a_facts as (A1 & A2 & A3 & A4). pose proof lenZ_facts as (LL1 & LL2 & _).
    assert (OLDREG : forall k rg, region_of t k = Some rg -> ly_reg L' k = ly_reg L k).
    { intros k rg Hk. unfold L'. apply Lext_old. pose proof (region_of_lt _ _ _ Hk). unfold rr. lia. }
    split; [|split; [|split]].
    - intros r rg off Hr Hk Hoff. rewrite region_of_t1 in Hr. destruct (Nat.eqb r rr); [injection Hr as <-; destruct Hoff | exact (X1 r rg off Hr Hk Hoff)].
    - intros r1 r2 q1 q2 Hne H1 H2 K1 K2. rewrite region_of_t1 in H1, H2.
      destruct (Nat.eqb r1 rr) eqn:E1; destruct (Nat.eqb r2 rr) eqn:E2.
      + apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. exfalso. apply Hne. lia.
      + apply Nat.eqb_eq in E1. subst r1. injection H1 as <-. cbn [rg1 rg_len]. rewrite L'_reg_new, (OLDREG r2 q2 H2).
        pose proof (region_live_t r2 q2 H2 K2) as Hl. pose proof (X3 r2 q2 H2 Hl) as SZ.
        destruct (Z_le_dec (a + lenZ) (ly_reg L r2)); [left; lia|]. destruct (Z_le_dec (ly_reg L r2 + rg_len q2) a); [right; lia|]. exfalso.
        destruct (Z_le_dec a (ly_reg L r2)).
        * apply (old_region_vs_grant r2 q2 (ly_reg L r2) H2 Hl (or_intror K2)); unfold PGSZ in *; lia.
        * apply (old_region_vs_grant r2 q2 a H2 Hl (or_intror K2)); unfold PGSZ in *; lia.
      + apply Nat.eqb_eq in E2. subst r2. injection H2 as <-. cbn [rg1 rg_len]. rewrite L'_reg_new, (OLDREG r1 q1 H1).
        pose proof (region_live_t r1 q1 H1 K1) as Hl. pose proof (X3 r1 q1 H1 Hl) as SZ.
        destruct (Z_le_dec (ly_reg L r1 + rg_len q1) a); [left; lia|]. destruct (Z_le_dec (a + lenZ) (ly_reg L r1)); [right; lia|]. exfalso.
        destruct (Z_le_dec a (ly_reg L r1)).
        * apply (old_region_vs_grant r1 q1 (ly_reg L r1) H1 Hl (or_intror K1)); unfold PGSZ in *; lia.
        * apply (old_region_vs_grant r1 q1 a H1 Hl (or_intror K1)); unfold PGSZ in *; lia.
      + rewrite (OLDREG r1 q1 H1), (OLDREG r2 q2 H2). exact (X2 r1 r2 q1 q2 Hne H1 H2 K1 K2).
    - intros r rg Hr Hl. rewrite region_of_t1 in Hr. destruct (Nat.eqb r rr); [injection Hr as <-; cbn [rg1 rg_len]; unfold PGSZ in *; lia | exact (X3 r rg Hr Hl)].
    - intros r rg Hr Hl. rewrite region_of_t1 in Hr. destruct (Nat.eqb r rr) eqn:E.
      + apply Nat.eqb_eq in E. subst r. injection Hr as <-. cbn [rg1 rg_len]. rewrite L'_reg_new, L'_top. lia.
      + rewrite (OLDREG r rg Hr), L'_top. exact (X4 r rg Hr Hl).
  Qed.

  Theorem vm_ok_t1 : ltac2:(tb__ "0|0|
SbdS81S7eS87A3").
  Proof using HB HI HIR HSI HVX Ha_al Ha_ceil Ha_pos Hbrk Hcnt Hctx Hfree Hhd Hinit.
    pose proof HV as (V1 & V2 & V3 & V5 & X1 & X2 & X3 & X4 & V9 & V10 & V11). pose proof a_facts as (A1 & A2 & A3 & A4). pose proof lenZ_facts as (LL1 & LL2 & _).
    pose proof t1_fields as (F1 & F2 & F3 & F4 & _).
    assert (OLDREG : forall k rg, region_of t k = Some rg -> ly_reg L' k = ly_reg L k).
    { intros k rg Hk. unfold L'. apply Lext_old. pose proof (region_of_lt _ _ _ Hk). unfold rr. lia. }
    pose proof vm_okX_t1 as (Y1 & Y2 & Y3 & Y4). unfold vm_ok. rewrite F4.
    split; [|split; [|split; [exact I|split; [|split; [exact Y1|split; [exact Y2|split; [exact Y3|split; [exact Y4|split; [|split; [intros r p k rgk Hb; discriminate Hb|   rewrite L'_top; exact V11]]]]]]]]]].
    - intros r rg Hr Hl Hk. rewrite region_of_t1 in Hr. destruct (Nat.eqb r rr) eqn:E; [injection Hr as <-; discriminate|].
      rewrite (OLDREG r rg Hr). cbn [vm1 vm_maps]. right. exact (V1 r rg Hr Hl Hk).
    - intros r rg Hr Hk. rewrite region_of_t1 in Hr. destruct (Nat.eqb r rr) eqn:E.
      + apply Nat.eqb_eq in E. subst r. injection Hr as <-. cbn [rg1 rg_len rg_rw vm1 vm_maps vm_noaccess]. rewrite L'_reg_new.
        split; [left; reflexivity|]. split.
        * intros k Hk1 Hk2 _. apply range_in_maps_head; cbn [fst snd]; rewrite ?ua, ?un; unfold PGSZ in *; nia.
        * intros off [].
      + rewrite (OLDREG r rg Hr). destruct (V2 r rg Hr Hk) as (W1 & W2 & W3). cbn [vm1 vm_maps vm_noaccess]. split; [right; exact W1|]. split.
        * intros k Hk1 Hk2 Hk3. apply range_in_maps_cons. exact (W2 k Hk1 Hk2 Hk3).
        * intros off Hoff e [<-|He]; [|exact (W3 off Hoff e He)]. cbn [fst snd]. rewrite ua, un.
          destruct (X1 r rg off Hr Hk Hoff) as [O1 O2]. pose proof (region_live_t r rg Hr Hk) as Hl.
          destruct (Z_le_dec (ly_reg L r + off + PGSZ) a) as [|N1]; [left; lia|].
          destruct (Z_le_dec (a + lenZ) (ly_reg L r + off)) as [|N2]; [right; lia|]. exfalso.
          destruct (Z_le_dec a (ly_reg L r + off)).
          -- apply (old_region_vs_grant r rg (ly_reg L r + off) Hr Hl (or_intror Hk)); unfold PGSZ in *; lia.
          -- apply (old_region_vs_grant r rg a Hr Hl (or_intror Hk)); unfold PGSZ in *; lia.
    - intros p n Hin. rewrite fp_t1 in Hin. rewrite (L'_addr_of p) by exact (footprint_below X R U t HI _ Hin).
      apply range_in_maps_cons. exact (V5 p n Hin).
    -   intros r rg q n Hr Hk Hl Hin Hne. rewrite fp_t1 in Hin.
      pose proof (L'_fp (LMem q, n) Hin) as EQ. cbn [fst] in EQ. rewrite EQ.
      rewrite region_of_t1 in Hr. destruct (Nat.eqb r rr) eqn:E.
      + apply Nat.eqb_eq in E. subst r. injection Hr as <-. cbn [rg1 rg_len]. rewrite L'_reg_new.
        pose proof (fp_size (LMem q, n) Hin) as SZ. cbn [snd] in SZ.
        destruct (Z_le_dec (loc_addr L (LMem q) + n) a) as [Y|N1]; [left; exact Y|].
        destruct (Z_le_dec (a + lenZ) (loc_addr L (LMem q))) as [Y|N2]; [right; exact Y|]. exfalso.
        destruct (Z_le_dec a (loc_addr L (LMem q))).
        * apply (grant_vs_footprint (LMem q, n) (loc_addr L (LMem q)) Hin); cbn [fst snd]; unfold PGSZ in *; lia.
        * apply (grant_vs_footprint (LMem q, n) a Hin); cbn [fst snd]; unfold PGSZ in *; lia.
      + rewrite (OLDREG r rg Hr). exact (V9 r rg q n Hr Hk Hl Hin Hne).
  Qed.

  Theorem ledger_t1 : ltac2:(tb__ "0|1|
S1SbfVC;S87A2S1Sc1VC;S87A2S0S99S98Sa9Q40A1M0G0A2A1Sb0S87A1Sb0Vvm;A1A3A2A2").
  Proof using HB HIR HLG HSI HV Ha_al Ha_ceil Ha_pos Hfree.
    pose proof a_facts as (A1 & A2 & A3 & A4). pose proof lenZ_facts as (LL1 & _).
    split; [|split; [exact HIR | reflexivity]].
    intros e [<-|He]; [|exact (HLG e He)]. cbn [fst snd]. rewrite ua, un. split; [exact A1|].
    split; [change (alloc_top vm1) with (alloc_top vm); rewrite <- (vm_ok_top L t vm HV); exact Ha_ceil|].
    pose proof HSI as (_&_&_&_&_&_&_&_&_& [CX1 CX2] &_& IMG1 & IMG2).
    destruct (Z_le_dec (a + lenZ) (mc_img_lo C)); [left; lia|]. destruct (Z_le_dec (mc_img_hi C) a); [right; lia|]. exfalso.
    destruct (Z_le_dec a (mc_img_lo C)).
    - apply (grant_vs_image (mc_img_lo C)); unfold CTX_SIZE, PGSZ in *; lia.
    - apply (grant_vs_image a); unfold PGSZ in *; lia.
  Qed.

  Theorem vm_okX_t2 : vm_okX L' t2.
  Proof using HB HI HV Ha_al Ha_ceil Ha_pos Hbrk Hcnt Hfree Hhd Hinit.
    pose proof vm_okX_t1 as (Y1 & Y2 & Y3 & Y4). pose proof lenZ_facts as (LL1 & _).
    assert (RG : forall r, region_of t2 r = match region_of t1 r with Some rg => Some (if Nat.eqb r rr then rg2 else rg) | None => None end).
    { intros r. rewrite region_of_t1, region_of_t2. destruct (Nat.eqb r rr); [reflexivity|]. destruct (region_of t r); reflexivity. }
    split; [|split; [|split]].
    - intros r rg off Hr Hk Hoff. rewrite region_of_t2 in Hr. destruct (Nat.eqb r rr) eqn:E.
      + injection Hr as <-. destruct Hoff as [<-|[]]. cbn [rg2 rg_len]. unfold PGSZ in *. lia.
      + apply (Y1 r rg off); [rewrite region_of_t1, E; exact Hr | exact Hk | exact Hoff].
    - intros r1 r2 q1 q2 Hne H1 H2 K1 K2. rewrite region_of_t2 in H1, H2.
      assert (G : forall r q, (if Nat.eqb r rr then Some rg2 else region_of t r) = Some q -> rg_kind q = RkMetaRes ->
                 exists q', region_of t1 r = Some q' /\ rg_kind q' = RkMetaRes /\ rg_len q' = rg_len q).
      { intros r q Hq Kq. rewrite region_of_t1. destruct (Nat.eqb r rr); [injection Hq as <-; exists rg1; repeat split; reflexivity | exists q; auto]. }
      destruct (G r1 q1 H1 K1) as (q1' & H1' & K1' & L1). destruct (G r2 q2 H2 K2) as (q2' & H2' & K2' & L2).
      rewrite <- L1, <- L2. exact (Y2 r1 r2 q1' q2' Hne H1' H2' K1' K2').
    - intros r rg Hr Hl. rewrite region_of_t2 in Hr. destruct (Nat.eqb r rr) eqn:E; [injection Hr as <-; cbn [rg2 rg_len]; unfold PGSZ in *; lia|].
      apply (Y3 r rg); [rewrite region_of_t1, E; exact Hr | exact Hl].
    - intros r rg Hr Hl. rewrite region_of_t2 in Hr. destruct (Nat.eqb r rr) eqn:E.
      + apply Nat.eqb_eq in E. subst r. injection Hr as <-. destruct (Y4 rr rg1 ltac:(rewrite region_of_t1, Nat.eqb_refl; reflexivity) eq_refl) as [B1 B2]. cbn [rg2 rg1 rg_len] in *. lia.
      + apply (Y4 r rg); [rewrite region_of_t1, E; exact Hr | exact Hl].
  Qed.

  Theorem vm_ok_t2 : ltac2:(tb__ "0|0|
SbdS81S7dS88A3").
  Proof using HB HI HIR HSI HVX Ha_al Ha_ceil Ha_pos Hbrk Hcnt Hctx Hfree Hhd Hinit.
    pose proof HV as (V1 & V2 & V3 & V5 & X1 & X2 & X3 & X4 & V9 & V10 & V11). pose proof a_facts as (A1 & A2 & A3 & A4). pose proof lenZ_facts as (LL1 & LL2 & _).
    pose proof t2_fields as (F1 & F2 & F3 & F4 & _).
    assert (OLDREG : forall k rg, region_of t k = Some rg -> ly_reg L' k = ly_reg L k).
    { intros k rg Hk. unfold L'. apply Lext_old. pose proof (region_of_lt _ _ _ Hk). unfold rr. lia. }
    assert (HI64 : a + PGSZ + PGSZ < 2 ^ 64) by (unfold PGSZ in *; lia).
    assert (Hlo : 0 <= a + PGSZ) by (unfold PGSZ in *; lia).
    assert (Hlh : a + PGSZ <= a + PGSZ + PGSZ) by (unfold PGSZ in *; lia).
    pose proof vm_okX_t2 as (Y1 & Y2 & Y3 & Y4). unfold vm_ok. rewrite F4.
    split; [|split; [|split; [exact I|split; [|split; [exact Y1|split; [exact Y2|split; [exact Y3|split; [exact Y4|split; [|split; [intros r p k rgk Hb; discriminate Hb|   rewrite L'_top; exact V11]]]]]]]]]].
    - intros r rg Hr Hl Hk. rewrite region_of_t2 in Hr. destruct (Nat.eqb r rr) eqn:E; [injection Hr as <-; discriminate|].
      rewrite (OLDREG r rg Hr). cbn [vm2 vm_maps]. right. exact (V1 r rg Hr Hl Hk).
    - intros r rg Hr Hk. rewrite region_of_t2 in Hr. destruct (Nat.eqb r rr) eqn:E.
      + apply Nat.eqb_eq in E. subst r. injection Hr as <-. cbn [rg2 rg_len rg_rw vm2 vm_maps vm_noaccess]. rewrite L'_reg_new.
        split; [left; reflexivity|]. split.
        * intros k Hk1 Hk2 Hk3.
          assert (Hk0 : 2 <= k) by (destruct (Z.eq_dec k 1) as [->|]; [exfalso; apply Hk3; left; reflexivity | lia]).
          apply (maps_subtract_keeps ((wa, wn) :: vm_noaccess vm) (a + PGSZ) (a + PGSZ + PGSZ) (a + PGSZ * k) PGSZ);
            [unfold PGSZ; lia | exact Hlo | exact HI64 | right; clear - Hk0; unfold PGSZ; lia |].
          apply range_in_maps_head; cbn [fst snd]; rewrite ?ua, ?un; clear - Hk0 Hk2 LL1; unfold PGSZ in *; lia.
        * intros off [<-|[]] e He.
          destruct (maps_subtract_piece _ (a + PGSZ) (a + PGSZ + PGSZ) e Hlo Hlh HI64 He) as (e0 & _ & _ & _ & D). clear - D. lia.
      + rewrite (OLDREG r rg Hr). destruct (V2 r rg Hr Hk) as (W1 & W2 & W3). pose proof (region_live_t r rg Hr Hk) as Hl.
        cbn [vm2 vm_maps vm_noaccess]. split; [right; exact W1|]. split.
        * intros k Hk1 Hk2 Hk3.
          apply (maps_subtract_keeps ((wa, wn) :: vm_noaccess vm) (a + PGSZ) (a + PGSZ + PGSZ)); [unfold PGSZ; lia | exact Hlo | exact HI64 | |].
          --
             destruct (Z_le_dec (ly_reg L r + PGSZ * k + PGSZ) (a + PGSZ)) as [Y|N1]; [left; exact Y|].
             destruct (Z_le_dec (a + PGSZ + PGSZ) (ly_reg L r + PGSZ * k)) as [Y|N2]; [right; exact Y|]. exfalso.
             destruct (Z_le_dec a (ly_reg L r + PGSZ * k)).
             ++ apply (old_region_vs_grant r rg (ly_reg L r + PGSZ * k) Hr Hl (or_intror Hk)); clear - Hk1 Hk2 N1 N2 l LL1; unfold PGSZ in *; lia.
             ++ apply (old_region_vs_grant r rg a Hr Hl (or_intror Hk)); clear - Hk1 Hk2 N1 N2 n LL1; unfold PGSZ in *; lia.
          -- apply range_in_maps_cons. exact (W2 k Hk1 Hk2 Hk3).
        * intros off Hoff e He.
          destruct (maps_subtract_piece _ (a + PGSZ) (a + PGSZ + PGSZ) e Hlo Hlh HI64 He) as (e0 & He0 & S1 & S2 & D).
          destruct He0 as [<-|He0].
          -- cbn [fst snd] in S1, S2. rewrite ua in S1. rewrite ua, un in S2.
             destruct (X1 r rg off Hr Hk Hoff) as [O1 O2].
             destruct (Z_le_dec (ly_reg L r + off + PGSZ) (bv_unsigned (fst e))) as [Y|N1]; [left; exact Y|].
             destruct (Z_le_dec (bv_unsigned (fst e) + bv_unsigned (snd e)) (ly_reg L r + off)) as [Y|N2]; [right; exact Y|]. exfalso.
             pose proof (urange (snd e)) as US.
             destruct (Z_le_dec a (ly_reg L r + off)).
             ++ apply (old_region_vs_grant r rg (ly_reg L r + off) Hr Hl (or_intror Hk)); clear - O1 O2 S1 S2 N1 N2 l US LL1; unfold PGSZ in *; lia.
             ++ apply (old_region_vs_grant r rg a Hr Hl (or_intror Hk)); clear - O1 O2 S1 S2 N1 N2 n US LL1; unfold PGSZ in *; lia.
          -- exact (W3 off Hoff e0 He0) || (pose proof (W3 off Hoff e0 He0) as Z0; clear - Z0 S1 S2; lia).
    - intros p n Hin. apply fp_t2 in Hin as [Hin|E].
      + rewrite (L'_addr_of p) by exact (footprint_below X R U t HI _ Hin). apply range_in_maps_cons. exact (V5 p n Hin).
      + injection E as -> ->. unfold addr_of. rewrite L'_pnew. apply range_in_maps_head; cbn [fst snd]; rewrite ?ua, ?un; clear - LL1 A1; unfold PGSZ in *; lia.
    -   intros r rg q n Hr Hk Hl Hin Hne. apply fp_t2 in Hin as [Hin|E].
      + pose proof (L'_fp (LMem q, n) Hin) as EQ. cbn [fst] in EQ. rewrite EQ.
        rewrite region_of_t2 in Hr. destruct (Nat.eqb r rr) eqn:E.
        * apply Nat.eqb_eq in E. subst r. injection Hr as <-. cbn [rg2 rg_len]. rewrite L'_reg_new.
          pose proof (fp_size (LMem q, n) Hin) as SZ. cbn [snd] in SZ.
          destruct (Z_le_dec (loc_addr L (LMem q) + n) a) as [Y|N1]; [left; exact Y|].
          destruct (Z_le_dec (a + lenZ) (loc_addr L (LMem q))) as [Y|N2]; [right; exact Y|]. exfalso.
          destruct (Z_le_dec a (loc_addr L (LMem q))).
          -- apply (grant_vs_footprint (LMem q, n) (loc_addr L (LMem q)) Hin); cbn [fst snd]; unfold PGSZ in *; lia.
          -- apply (grant_vs_footprint (LMem q, n) a Hin); cbn [fst snd]; unfold PGSZ in *; lia.
        * rewrite (OLDREG r rg Hr). exact (V9 r rg q n Hr Hk Hl Hin Hne).
      +
        injection E as -> ->. rewrite region_of_t2 in Hr. destruct (Nat.eqb r rr) eqn:E; [apply Nat.eqb_eq in E; exfalso; exact (Hne (eq_sym E))|].
        pose proof L'_pnew as EP. rewrite EP. rewrite (OLDREG r rg Hr).
        pose proof (region_live_t r rg Hr Hk) as Hlv. pose proof (X3 r rg Hr Hlv) as SZr.
        destruct (Z_le_dec (a + PGSZ + PGSZ) (ly_reg L r)) as [Y|N1]; [left; exact Y|].
        destruct (Z_le_dec (ly_reg L r + rg_len rg) (a + PGSZ)) as [Y|N2]; [right; exact Y|]. exfalso.
        destruct (Z_le_dec a (ly_reg L r)).
        -- apply (old_region_vs_grant r rg (ly_reg L r) Hr Hlv (or_intror Hk)); unfold PGSZ in *; lia.
        -- apply (old_region_vs_grant r rg a Hr Hlv (or_intror Hk)); unfold PGSZ in *; lia.
  Qed.

  Theorem ledger_t2 : ltac2:(tb__ "0|1|
S1SbfVC;S88A2S1Sc1VC;S88A2S0S99S98Sa9Q40A1M0G0A2A1Sb0S88A1Sb0Vvm;A1A3A2A2").
  Proof using HB HIR HLG HSI HV HVX Ha_al Ha_ceil Ha_pos Hfree. exact ledger_t1. Qed.

  Lemma fp_where e x : ltac2:(tb__ "0|3|
S3cS98S4bS7A2Ve;S4eVt;A1A3S1S41S4dVL;S9fS4bS7Ve;A3M0A2M1Vx;A2S43Vx;S42G1Sa0S4bS7Ve;A3A2A2A2S2S1S0S4bG0S4cZ0A1A3S1S41S60VL;A1M2Vx;A2S43Vx;S42G2S66A2A2A2A2S4S8S8S1S0S4bG0S51R1A1A3S1S1S41SaVx;A2S43Vx;SbbVL;A1A2A2S3S1S41Sc3VC;A1Vx;A2S43Vx;Sc2VC;A1A2A2A1A2A2Lp;A2A2F_;F_;").
  Proof using HLG HV Ha_al Ha_pos.
    intros He Hx. pose proof HV as (_ & _ & _ & V5 & _). destruct e as [[o|p] n]; cbn [fst snd] in *.
    - left. unfold footprint in He. destruct He as [E|He].
      + injection E as <- <-. cbn [loc_addr] in Hx. split; [reflexivity | lia].
      + exfalso. apply in_app_iff in He as [He|He]; [apply in_map_iff in He as (? & E & _); discriminate|].
        apply in_flat_map in He as (k & _ & He). destruct (region_of t k) as [rg|]; [|destruct He]. destruct (rg_kind rg); try destruct He.
        destruct (rg_live rg); [destruct He as [E|[]]; discriminate | destruct He].
    - right. exists p. split; [reflexivity|]. destruct (V5 p n He) as (e' & He' & R1 & R2). destruct (HLG e' He') as (G1 & G2 & G3). rewrite <- (vm_ok_top _ _ _ HV) in G2.
      unfold addr_of in R1, R2. cbn [loc_addr] in Hx. destruct p as [r o]. cbn [loc_addr] in *. lia.
  Qed.

  Lemma maps_wf_t1 : maps_wf vm1.
  Proof using HB HMW Ha_al Ha_ceil Ha_pos Hfree.
    pose proof a_facts as (A1 & A2 & A3 & A4). pose proof lenZ_facts as (LL1 & _). unfold maps_wf, vm1. cbn [vm_maps].
    apply mwf_cons; [exact HMW | cbn [snd]; rewrite un; unfold PGSZ in LL1; lia |].
    intros e' He'. unfold wdisj. cbn [fst snd]. rewrite ua, un.
    destruct (Hfree e' ltac:(apply in_app_iff; right; exact He')) as [H|H]; [right; exact H | left; exact H].
  Qed.
  Lemma maps_wf_t2 : maps_wf vm2.
  Proof using HB HMW Ha_al Ha_ceil Ha_pos Hfree. exact maps_wf_t1. Qed.

  Lemma block_where b n x : ltac2:(tb__ "0|3|
S3cS98S7S7A2Sa4S7S7Vb;Vn;A4Sc0VL;Vt;A2A3S1S41Vb;Vx;A2S43Vx;S42Vb;Vn;A2A2A2S4S98S4bS7A2M0G0S4S8S8S1S3cG0R2S4eVt;A1A3S1S0S4bS9fS4bS7R2A3M1S51R1A1A3S1S41S4dVL;G1A2M2Vx;A2S43Vx;S42G2Sa0S4bS7R2A3A2A2A2A2A2Lp;A2Le;A2F_;F_;").
  Proof using HI HX Ha_pos.
    intros Hin Hx. unfold blocks in Hin. apply in_map_iff in Hin as [[p n'] [E Hin]]. cbn [fst snd] in E. injection E as Eb En. subst b n'.
    destruct (user_block_in_group X R U t L HI HX (p, n) Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & Eb & B1 & B2 & B3 & B4). cbn [fst snd] in *.
    destruct (used_group_region X R U t g am HI Hu) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
    exists (LMem (SP (prid (am_mem am)) 0), rg_len rg), (SP (prid (am_mem am)) 0). split; [exact (footprint_region_In t _ _ Hr Hkd Hl)|]. split; [reflexivity|].
    cbn [fst snd loc_addr]. pose proof (stride_pos _ _ _ _ _ (inv_groups HI g am Hu)) as Sp. assert (0 <= stride_of am * i) by nia.
    unfold addr_of, loc_addr in *. destruct (am_mem am) as [r o]. cbn [prid poff] in *. unfold UNIT, IB in *. lia.
  Qed.

  Lemma grant_vs_block b n x : ltac2:(tb__ "0|0|
S3cS98S7S7A2Sa4S7S7Vb;Vn;A4Sc0VL;Vt;A2A3S1S41Vb;Vx;A2S43Vx;S42Vb;Vn;A2A2A2S3S1S41Va;Vx;A2S43Vx;S42Va;S80A2A2A2A1F_;F_;").
  Proof using HI HIR HSI HV HX Ha_al Ha_pos Hctx Hfree. intros Hin Hx. destruct (block_where b n x Hin Hx) as (e & p & He & _ & Rx). exact (grant_vs_footprint e x He Rx). Qed.

  Lemma xraw_t1 : xraw X t1.
  Proof using HX Hbrk Hcnt Hhd Hinit. intros q Hq. pose proof t1_fields as (_ & _ & F3 & _). unfold MT. rewrite F3. exact (HX q Hq). Qed.
  Lemma xraw_t2 : ltac2:(tb__ "0|0|
Sd8S9aS8S82VX;A3S7dA2").
  Proof using HI HX a.
    intros q [<-|Hq].
    - left. rewrite t2_upd. apply MT_upd_same.
    - rewrite t2_upd. rewrite MT_upd_other.
      + unfold MT. rewrite (proj1 t2pre_fields). exact (HX q Hq).
      + intros ->. pose proof (key_below X R U t HI mnew (proj1 (inv_X HI mnew Hq))) as K. rewrite mnew_prid in K. unfold rr in K. lia.
  Qed.
  Lemma mnew_notX : ltac2:(tb__ "0|3|
S1S0Sa1S79S82VX;A2Sa7A3S1S3cS8S82S53S7dA1A3S2S0S9cScA1M0S61S7dS82A2M1S9eScS26A2A3S0G0G1S9eScS2dSa3S8A1M2G2A2A2A3A2A2A2").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. pose proof SPEC2 as (_ & M & K & R2 & _). cbn [fst snd] in *. auto. Qed.
  Lemma keys_t1 : ltac2:(tb__ "0|0|
S0S99S8A1S53S7eA1S53Vt;A1A3").
  Proof using Hbrk Hcnt Hhd Hinit. pose proof t1_fields as (_ & _ & F3 & _). unfold keys. rewrite F3. reflexivity. Qed.
  Lemma keys_t2 : ltac2:(tb__ "0|0|
S40S8S53Vt;A1S53S7dA1A3").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit.
    pose proof SPEC2 as (_ & _ & _ & _ & _ & _ & (ext & E & _)). cbn [fst snd] in E. intros q Hq. rewrite E. apply in_app_iff. left. exact Hq.
  Qed.
  Lemma am_frame_t1 : ltac2:(tb__ "0|0|
S1Sd6Vt;S7eA2S1S8S18S5S5cVX;S7eR2R1A4S5cVX;Vt;R2R1A4A2Fam;Fg;Sd4Vt;S7eA2A2A2").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. pose proof SPEC1 as (_ & F & U1 & UB). cbn [fst snd] in *. auto. Qed.
  Lemma am_frame_t2 : ltac2:(tb__ "0|0|
S1Sd6Vt;S7dA2S1S8S18S5S5cS9aS8S82VX;A3S7dR2R1A4S5cVX;Vt;R2R1A4A2Fam;Fg;Sd4Vt;S7dA2A2A2").
  Proof using HI HL HX Hac Hbrk Hcnt Hhd Hinit. pose proof SPEC2 as (_ & _ & _ & _ & F & U1 & UB). cbn [fst snd] in *. auto. Qed.

  Definition bounded34 (s : astate) : Prop := ltac2:(tb__ "0|4|
S1S7S1S41Z0M0S3bVs;R1A2M1A2S43G1S44Z2M2Z30A2A2A2Fsc;S1S1S41G0S12Vs;A1M3A2S41G3Z22A2A2S43S46Sa6S8SbVs;A1A2A1S44G2Z23A2A2A2A2").
  Lemma bounded34_t1 : ltac2:(tb__ "0|0|
S84Vt;A1S84S7eA1F_;").
  Proof using HB Ha_al Ha_ceil Ha_pos Hbrk Hcnt Hhd Hinit.
    intros (B1 & B2 & B3). pose proof t1_fields as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & F10 & _ & _ & _ & _ & F15 & _).
    pose proof lenZ_facts as (_ & _ & LL3). pose proof a_facts as (A1 & A2 & _).
    split; [intros sc; unfold usage_of; rewrite F15; apply B1|]. split; [|rewrite F2; exact B3]. rewrite F10.
    split; [lia|]. destruct (Z_le_dec (st_meta_alloc_shift t + 1) 34) as [|Hgt]; [lia|]. exfalso.
    assert (2 ^ 35 <= 2 ^ (st_meta_alloc_shift t + 1)) by (apply Z.pow_le_mono_r; lia). unfold PGSZ in LL3. lia.
  Qed.
  Lemma bounded34_t2 : ltac2:(tb__ "0|0|
S84Vt;A1S84S7dA1F_;").
  Proof using HB HI HIR HL HLG HSI HVX HX Ha_al Ha_ceil Ha_pos Hac Hbrk Hcnt Hctx Hfree Hhd Hinit.
    intros B. pose proof (bounded34_t1 B) as (B1 & B2 & B3).
    pose proof t1_fields as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F10 & _ & _ & _ & _ & F15 & _).
    pose proof t2_fields as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _ & _ & _ & _ & G15 & _).
    split; [intros sc; unfold usage_of in *; rewrite G15; rewrite F15 in B1; apply B1|]. split; [rewrite G10; rewrite F10 in B2; exact B2|].
    exact (areas_bound (mnew :: X) R U t2 L' C vm2 HI2 layout_ok_t2 vm_ok_t2 (proj1 ledger_t2)).
  Qed.

  Lemma bounded_t1 : bounded t1.
  Proof using HB Ha_al Ha_ceil Ha_pos Hbrk Hcnt Hhd Hinit.
    pose proof HB as (B1 & B2 & B3 & _). pose proof (bounded34_t1 (conj B1 (conj B2 B3))) as (C1 & C2 & C3).
    pose proof t1_fields as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F13 & _).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. right. rewrite F13, F1. cbn [prid pnew]. rewrite length_app. cbn. unfold rr. lia.
  Qed.
  Lemma bounded_t2 : bounded t2.
  Proof using HB HI HIR HL HLG HSI HVX HX Ha_al Ha_ceil Ha_pos Hac Hbrk Hcnt Hctx Hfree Hhd Hinit.
    pose proof HB as (B1 & B2 & B3 & _). pose proof (bounded34_t2 (conj B1 (conj B2 B3))) as (C1 & C2 & C3).
    pose proof t2_fields as (F1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F13 & _).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. right. rewrite F13, F1. cbn [prid pnew padd]. rewrite length_app. cbn. unfold rr. lia.
  Qed.

  Lemma cell_where1 c x : ltac2:(tb__ "0|3|
S3cS4aVc;S9bS4aS52S7eA1SaaS7eA1A3A3S1S41S4dS81S50Vc;A1A2M0Vx;A2S43Vx;S42G0S46S64Vc;A1A1A2A2A2S4S98S4bS7A2M1G1S1S3cG1R1S4eVt;A1A3S1S41S4dVL;S9fS4bS7R1A3A2M2Vx;A2S43Vx;S42G2Sa0S4bS7R1A3A2A2A2A2Le;A2F_;F_;").
  Proof using HI HL HX Ha_al Ha_pos Hac Hbrk Hcnt Hhd Hinit.
    intros Hc Hx. destruct (cell_in_footprintI X R U t1 L' HI1 xraw_t1 c Hc) as (e & He & [I1 I2]). rewrite fp_t1 in He.
    exists e. split; [exact He|]. unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2. rewrite (L'_fp e He) in I1, I2. lia.
  Qed.
  Lemma cell_where2 c x : ltac2:(tb__ "0|4|
S3cS4aVc;S9bS4aS52S7dA1SaaS7dA1A3A3S1S41S4dS81S50Vc;A1A2M0Vx;A2S43Vx;S42G0S46S64Vc;A1A1A2A2A2S2S4S98S4bS7A2M1G1S1S3cG1R1S4eVt;A1A3S1S41S4dVL;S9fS4bS7R1A3A2M2Vx;A2S43Vx;S42G2Sa0S4bS7R1A3A2A2A2A2Le;A2S1S41S42Va;SaA2M3Vx;A2S43Vx;S42G3SaA2A2A2A2F_;F_;").
  Proof using HI HL HX Ha_al Ha_pos Hac Hbrk Hcnt Hhd Hinit.
    intros Hc Hx. destruct (cell_in_footprintI (mnew :: X) R U t2 L' HI2 xraw_t2 c Hc) as (e & He & [I1 I2]).
    unfold cell_range, crange in I1, I2. cbn [fst snd] in I1, I2. apply fp_t2 in He as [He| ->].
    - left. exists e. split; [exact He|]. rewrite (L'_fp e He) in I1, I2. lia.
    - right. cbn [fst snd] in I1, I2. rewrite L'_pnew in I1, I2. lia.
  Qed.

End RES.


(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngNtfM MngNtfS MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1 MngMW2 MngShift AXG_am1 AXG_am2 AXG_am3 AXG_am4 AXG_am5 AXG_am6 AXG_am7 AXG_am6b AXG_amr0 AXG_amr AXG_am6c AXG_am6d AXG_am6e AXG_am8.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngShift OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am4 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am7 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6b OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_amr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6c OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6d OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am6e OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma free_head_cases : forall X R U s fm, Inv X R U s -> st_free_meta_head s = Some fm ->
  (exists pr, MT s fm = Some (MFree pr (Some fm))) \/
  (exists x px nxx, MT s fm = Some (MFree (Some x) (Some x)) /\ x <> fm /\ MT s x = Some (MFree px nxx)) \/
  (exists p n pp np pn nn, MT s fm = Some (MFree (Some p) (Some n)) /\ n <> fm /\ p <> fm /\ p <> n /\
     MT s p = Some (MFree pp np) /\ MT s n = Some (MFree pn nn)).
Proof.
  intros X R U s fm HI Hf. destruct (inv_rings HI) as ((ms & FR & _) & _ & _). rewrite Hf in FR.
  destruct (ring_head_In _ _ _ FR) as (_ & rest & ->). destruct FR as ((ND & CH) & _).
  destruct CH as (Lfm & _).
  assert (Mfm : MT s fm = Some (MFree (Some (last (fm :: rest) fm)) (Some (hd fm rest)))).
  { unfold flinks, MTX in Lfm. destruct (memb fm X); [discriminate|]. destruct (MT s fm) as [[a b| |am]|]; try discriminate. injection Lfm as -> ->. reflexivity. }
  destruct (free_ring_nbrs X R U s fm _ _ HI Hf Mfm) as (_ & NB).
  destruct rest as [|x rest].
  - left. exists (Some fm). exact Mfm.
  - destruct (NB x ltac:(right; reflexivity)) as (_ & px & nxx & Hx).
    assert (Hxf : x <> fm) by (intros ->; inversion ND; apply H1; left; reflexivity).
    destruct rest as [|y rest].
    + right; left. exists x, px, nxx. cbn [last hd] in Mfm. split; [exact Mfm|]. split; [exact Hxf | exact Hx].
    + right; right. set (lp := last (fm :: x :: y :: rest) fm) in *.
      assert (Hlp : In lp (y :: rest)).
      { unfold lp. rewrite last_cons, last_cons. apply In_last. discriminate. }
      destruct (NB lp ltac:(left; reflexivity)) as (_ & pp & np & Hp).
      exists lp, x, pp, np, px, nxx. split; [exact Mfm|]. split; [exact Hxf|].
      inversion ND as [|? ? Hnf ND2]. inversion ND2 as [|? ? Hnx _].
      split; [intros E; apply Hnf; rewrite <- E; right; exact Hlp|].
      split; [intros E; apply Hnx; rewrite <- E; exact Hlp|].
      split; [exact Hp | exact Hx].
Qed.

Section AMW.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma wk_silent : forall FORB HTOP X R U L s m (regs : bvmap 5 word) rom sp0 K ra mt s' t,
  t = IRet (Some mt, s') ->
  (exists R' m', msteps SEGS (mkst regs (wa 0x51ca8) m rom) (mkst R' (wa ra) m' rom) /\
     getr R' 10 = wa (loc_addr L (LMem mt)) /\
     (forall k, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
     CUT HTOP (mt :: X) R U L s' m' sp0 K /\ GROW sp0 K L s m L s' m' /\ mem_grows m m') ->
  wk SEGS FORB HTOP rom L regs (wa 0x51ca8) m t (am_qpost HTOP X R U L s m regs sp0 K ra).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros FORB HTOP X R U L s m regs rom sp0 K ra mt s' t -> (R' & m' & Hms & H10 & HKk & C' & G' & _).
  cbn [wk]. exists R', (wa ra), m'. split; [exact Hms|].
  exists mt, s'. split; [reflexivity|]. split; [reflexivity|]. split; [exact H10|]. split; [exact HKk|]. split; [exact C' | exact G'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem am_wk : forall FORB, (forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x87000)) ->
  forall HTOP X R U L s m (regs : bvmap 5 word) rom sp0 K ra,
  CUT HTOP X R U L s m sp0 K -> 1152 <= K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x524e8 \/ ra = 0x5210c) ->
  rdn SEGS m (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 -> ly_brk0 L <= HTOP ->
  (st_init_done s = true \/ AMI L m sp0) ->
  wk SEGS FORB HTOP rom L regs (wa 0x51ca8) m (alloc_meta s) (am_qpost HTOP X R U L s m regs sp0 K ra).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros FORB HFORB HTOP X R U L s m regs rom sp0 K ra C HK R2 R1 Hra Mpg B1 B2 B3 Hin.
  pose proof C as [HI HX N HG HD HT HTB].
  assert (WOR : forall HTOP X R U L0 s0 m0 (regs0 : bvmap 5 word) L s m Rg rom sp0 K can ra r o rg
      (Kt : Z -> itree astate (option sptr * astate)),
    CUT HTOP X R U L s m sp0 K -> GROW sp0 K L0 s0 m0 L s m -> 1152 <= K ->
    am_frame Rg m sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
      (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) ->
    getr regs0 1 = wa ra -> getr regs0 2 = wa sp0 -> (ra = 0x524e8 \/ ra = 0x5210c) ->
    (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rg (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
    getr Rg 1 = wa 335712 -> getr Rg 9 = wa (ly_reg L r + o) -> getr Rg 10 = wa (ly_reg L r + o) ->
    getr Rg 11 = wa 4096 -> getr Rg 12 = wa 3 ->
    st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> 0 < st_avail_meta_area_count s ->
    st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
    rdn SEGS m (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
    Kt 1 = IRet (Some (padd (SP r o) AREA_HDR), s_opn (SP r o) (s_res1 s r rg o)) ->
    wk SEGS FORB HTOP rom L Rg (wa 0x53414) m (IAsk (KMprotect (SP r o)) s Kt)
       (am_qpost HTOP X R U L0 s0 m0 regs0 sp0 K ra)).
  { intros HTOP' X' R' U' L0 s0 m0 regs0 L' s' m' Rg rom' sp0' K' can ra' r o rg Kt.
    exact (wk_open_resv HTOP' X' R' U' L0 s0 m0 regs0 L' s' m' Rg rom' sp0' K' FORB can ra' r o rg Kt). }
  destruct (st_init_done s) eqn:Hi.
  2: { destruct Hin as [E|HAMI]; [discriminate E|].
       exact (wk_init FORB HFORB WOR HTOP X R U L s m regs rom sp0 K ra C HK R2 R1 Hra Mpg B1 B2 B3 Hi HAMI). }
  clear Hin.
  destruct (st_free_meta_head s) as [fm|] eqn:Hf.
  - destruct (free_head_cases X R U s fm HI Hf)
      as [(pr & Hm) | [(x & px & nxx & Hm & Hne & Hx) | (p & n & pp & np & pn & nn & Hm & Hnf & Hpf & Hpn & Hp & Hn)]].
    + apply (wk_silent FORB HTOP X R U L s m regs rom sp0 K ra fm _ _ (alloc_meta_pop1 s fm pr Hi Hf Hm)).
      exact (am_pop1 HTOP X R U L s m regs rom sp0 K ra fm pr C R2 R1 Hra Hi Hf Hm Mpg).
    + apply (wk_silent FORB HTOP X R U L s m regs rom sp0 K ra fm _ _ (alloc_meta_pop2 s fm x px nxx Hi Hf Hm Hne Hx)).
      exact (am_pop2 HTOP X R U L s m regs rom sp0 K ra fm x px nxx C R2 R1 Hra Hi Hf Hm Hne Hx Mpg).
    + apply (wk_silent FORB HTOP X R U L s m regs rom sp0 K ra fm _ _ (alloc_meta_popn s fm p n pp np pn nn Hi Hf Hm Hnf Hpf Hpn Hp Hn)).
      exact (am_popn HTOP X R U L s m regs rom sp0 K ra fm p n pp np pn nn C R2 R1 Hra Hi Hf Hm Hnf Hpf Hpn Hp Hn Mpg).
  - destruct (Z_lt_le_dec 0 (st_avail_meta_count s)) as [Hc|Hc].
    + apply (wk_silent FORB HTOP X R U L s m regs rom sp0 K ra _ _ _ (alloc_meta_take s Hi Hf Hc)).
      exact (am_take HTOP X R U L s m regs rom sp0 K ra C R2 R1 Hra Hi Hf Hc Mpg).
    + assert (Hc0 : st_avail_meta_count s = 0) by (pose proof (inv_keys HI) as (_ & _ & _ & _ & K5); clear - K5 Hc; lia).
      destruct (Z_lt_le_dec 0 (st_avail_meta_area_count s)) as [Hac|Hac].
      * exact (am_openres_wk HTOP X R U L s m regs rom sp0 K ra FORB C HK R2 R1 Hra Hi Hf Hc0 Hac Mpg).
      * assert (Hac0 : st_avail_meta_area_count s = 0).
        { pose proof (inv_ctx HI) as CT. unfold ctx_ok in CT. destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C11 & _). clear - C11 Hac. lia. }
        destruct (st_brk s) as [| |r p] eqn:Hb.
        -- exact (wk_bn FORB HFORB WOR HTOP X R U L s m regs rom sp0 K ra C HK R2 R1 Hra Mpg B1 B2 B3 Hi Hf Hc0 Hac0 Hb).
        -- exact (wk_dead FORB HFORB WOR HTOP X R U L s m regs rom sp0 K ra C HK R2 R1 Hra Mpg Hi Hf Hc0 Hac0 Hb).
        -- exact (wk_bc FORB HFORB WOR HTOP X R U L s m regs rom sp0 K ra r p C HK R2 R1 Hra Mpg Hi Hf Hc0 Hac0 Hb).
Qed.
End AMW.

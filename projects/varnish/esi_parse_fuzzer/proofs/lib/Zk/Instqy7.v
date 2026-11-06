(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module HW := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv MI_Kit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Arith MI_Geom MI_Pres2 MI_Cnt MI_WFree Mallkgx Mall1es Mall79j KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import W_ge3a6 RF_free Instfes Inst8ld InstDefs InstFree Instjhg Instffk Instrcx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Record rbf (st : mstate) (m : mem) (c : cptr) (off n : Z) (g bm : aptr) (i : Z) (r : region) (ar : area) (q res : Z) : Prop := mkRBF {
  rb_slot : (s_slots st) !! c = Some (g, i);
  rb_hosts : exists ai, (s_groups st) !! bm = Some (mkGhdr (Some g) ai);
  rb_mem : m_mem (get_meta_rec st g) = Some bm;
  rb_reg : (s_regions st) !! (fst c) = Some r;
  rb_kind : r_kind r = RKGroup;
  rb_fst : fst c = fst bm;
  rb_c : snd c = snd bm + UNIT + get_stride (get_meta_rec st g) * i;
  rb_b0 : 0 <= snd bm;
  rb_i : 0 <= i <= m_last_idx (get_meta_rec st g);
  rb_off : 0 <= off <= 255;
  rb_n : 0 <= n;
  rb_fit : UNIT * off + n <= get_stride (get_meta_rec st g) - IB;
  rb_stride : UNIT <= get_stride (get_meta_rec st g) /\ get_stride (get_meta_rec st g) mod UNIT = 0;
  rb_si0 : 0 <= get_stride (get_meta_rec st g) * i;
  rb_span : snd bm + UNIT + get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1) <= round_up_pg (r_len r);
  rb_rbase : 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
             /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x63000 <= r_base r);
  rb_q : 16 * q = get_stride (get_meta_rec st g) * i + 16 * off /\ 0 <= q < 2^16;
  rb_res : res = (snd c + get_stride (get_meta_rec st g) - IB) - (snd c + UNIT * off) - n /\ 0 <= res;
  (* [comment removed for export] *)
  rb_k4 : cell_read (get_shadow st (fst c)) (snd c + UNIT * off - 4) = Known 0;
  rb_k3 : cell_read (get_shadow st (fst c)) (snd c + UNIT * off - 3) = Known (i + 32 * Z.min res 5);
  rb_k2 : cell_read (get_shadow st (fst c)) (snd c + UNIT * off - 2) = Known (byte_of q 0);
  rb_k1 : cell_read (get_shadow st (fst c)) (snd c + UNIT * off - 1) = Known (byte_of q 1);
  (* [comment removed for export] *)
  rb_mslot : meta_slot st g;
  rb_g0 : 0 <= snd g;
  rb_area : (s_areas st) !! (area_of g) = Some ar /\ a_check ar = c_secret (ctx st);
  rb_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  rb_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  rb_sec : 0 <= c_secret (ctx st) < 2^64;
  rb_li : 0 <= m_last_idx (get_meta_rec st g) <= 31;
  rb_freeable : m_freeable (get_meta_rec st g) = 1;
  rb_sc : (0 <= m_sizeclass (get_meta_rec st g) < 48
           /\ (get_stride (get_meta_rec st g) <= UNIT * size_class (m_sizeclass (get_meta_rec st g)) \/ 28 <= m_sizeclass (get_meta_rec st g))
           /\ (get_stride (get_meta_rec st g) = UNIT * size_class (m_sizeclass (get_meta_rec st g))
               \/ (m_last_idx (get_meta_rec st g) = 0 /\ m_maplen (get_meta_rec st g) <> 0)))
          \/ (m_sizeclass (get_meta_rec st g) = 63 /\ m_last_idx (get_meta_rec st g) = 0 /\ 0 < m_maplen (get_meta_rec st g));
  rb_maplen : 0 <= m_maplen (get_meta_rec st g) < 2^35;
  rb_stride20 : m_sizeclass (get_meta_rec st g) < 48 -> get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1) < 2^20;
  rb_notA : Z.testbit (m_avail (get_meta_rec st g)) i = false;
  rb_notF : Z.testbit (m_freed (get_meta_rec st g)) i = false;
  rb_g16 : m_sizeclass (get_meta_rec st g) < 48 ->
           size_class (m_sizeclass (get_meta_rec st g)) * i <= q < size_class (m_sizeclass (get_meta_rec st g)) * (i + 1);
  rb_g17 : m_maplen (get_meta_rec st g) <> 0 -> q <= m_maplen (get_meta_rec st g) * 256 - 1;
  rb_top : m_maplen (get_meta_rec st g) <> 0 -> snd bm = 0 /\ m_maplen (get_meta_rec st g) * 4096 = round_up_pg (r_len r);
  (* [comment removed for export] *)
  rb_rd3 : bytes_at rsegs m (r_base r + snd c + UNIT * off - 3) [b8 (i + 32 * Z.min res 5)];
  rb_rd5 : 5 <= res -> bytes_at rsegs m (r_base r + snd c + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz res))
                     /\ bytes_at rsegs m (r_base r + snd c + get_stride (get_meta_rec st g) - IB - 5) [b8 0] /\ res < 2^32;
  rb_rdc : bytes_at rsegs m (r_base r + snd c + get_stride (get_meta_rec st g) - IB - res) [b8 0];
  rb_rde : bytes_at rsegs m (r_base r + snd c + get_stride (get_meta_rec st g) - IB) [b8 0];
  rb_wr : wr_at rsegs m (r_base r) (round_up_pg (r_len r));
  (* [comment removed for export] *)
  rb_active : fact_active (strip st)
}.

Lemma le4_of_byte_of v : 0 <= v < 2^32 -> le4 (wz v) = [b8 (byte_of v 0); b8 (byte_of v 1); b8 (byte_of v 2); b8 (byte_of v 3)].
Proof.
  intros Hv.
  pose proof (byte_of_range v 0 ltac:(lia) ltac:(lia)) as B0. pose proof (byte_of_range v 1 ltac:(lia) ltac:(lia)) as B1.
  pose proof (byte_of_range v 2 ltac:(lia) ltac:(lia)) as B2. pose proof (byte_of_range v 3 ltac:(lia) ltac:(lia)) as B3.
  rewrite <- (RF_free.le4_of_bytes (b8 (byte_of v 0)) (b8 (byte_of v 1)) (b8 (byte_of v 2)) (b8 (byte_of v 3))).
  unfold b8. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
  change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. rewrite (u32_bytes v Hv). reflexivity.
Qed.

(* [comment removed for export] *)
Definition heap_wit (s : PState) (LB : list block) (m : mem) (st : mstate) : Prop :=
  exists LB0, Permutation LB0 LB /\ strip st = ps_m s /\ mrep st m /\ HINV_from p0_reserved st (ps_brk s) LB0.
Lemma heap_wit_HEAP s LB m st : heap_wit s LB m st -> HEAP s LB m.
Proof. intros (LB0 & H). exists st, LB0. exact H. Qed.
(* [comment removed for export] *)

Lemma live_block_rbf : forall s LB m b,
  HEAP s LB m -> In b LB ->
  exists st off g bm i r ar q res,
    heap_wit s LB m st /\ ps_m s = strip st /\ mrep st m /\ ticks_ok st
    /\ blk_addr b = r_base r + snd (blk_slot b) + UNIT * off
    /\ rbf st m (blk_slot b) off (blk_size b) g bm i r ar q res.
Proof.
  intros s LB m b HP Hb.
  (first [ dex1 HP as st; dand5 HP as LB0 PERM Hst MR [BLK AR] | dand6 HP as st LB0 PERM Hst MR [BLK AR] | destruct HP as (st & LB0 & PERM & Hst & MR & [BLK AR]) ]).
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  pose proof (Mallx0l.areach_cinv_proof _ _ AR) as C.
  (first [ pose proof (AR) as dR_2; dand8 dR_2 as L LS BL INV LIVE RESV SEC CR | pose proof AR as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]).
  (first [ pose proof ((Forall2_In_l _ _ _ _ CR IN0)) as dR_3; dex1 dR_3 as k; destruct dR_3 as [Hk (KS & KZ & KA)] | pose proof ((Forall2_In_l _ _ _ _ CR IN0)) as dR_3; dand3 dR_3 as k Hk (KS & KZ & KA) | destruct (Forall2_In_l _ _ _ _ CR IN0) as (k & Hk & (KS & KZ & KA)) ]).
  destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in KS, KZ, KA.
  (first [ pose proof ((block_facts x0 st L BL LS INV c off n Hk)) as dR_4; dex7 dR_4 as g bm i ai a ar ka; rename dR_4 into BF | pose proof ((block_facts x0 st L BL LS INV c off n Hk)) as dR_4; dand8 dR_4 as g bm i ai a ar ka BF | destruct (block_facts x0 st L BL LS INV c off n Hk) as (g & bm & i & ai & a & ar & ka & BF) ]).
  (first [ pose proof (INV) as dR_5; dand7 dR_5 as IR IA IM IL IG IS ISH | pose proof INV as (IR & IA & IM & IL & IG & IS & ISH) ]).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as SL.
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HO.
  pose proof (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) as MEM.
  pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as EC.
  pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as HI.
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as HOFF.
  pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF) as HN.
  pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF) as FIT.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 SM].
  pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [B0 B16].
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA.
  pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF.
  pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as BSC.
  pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP.
  pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF) as ML0.
  (first [ pose proof ((bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) as dR_6; dand5 dR_6 as Ha Hck Hal Hka Eg | pose proof (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Eg) ]).
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH.
  pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0.
  pose proof (q16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Q16 QR].
  pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as HLI.
  unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  unfold gbase in SH. rewrite MEM in SH.
  (first [ dand8 SH as K4 K3 K2 K1 Q K5 Kr KU | destruct SH as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU) ]).
  assert (HOST : hosts st bm g) by (exists ai; exact HO).
  pose proof (ci_gmetas _ _ C bm g HOST) as GO.
  (first [ pose proof ((go_region _ _ _ GO)) as dR_8; dex1 dR_8 as r; dand6 dR_8 as Hr Kr' _ _ SPAN GTOP | pose proof ((go_region _ _ _ GO)) as dR_8; dand7 dR_8 as r Hr Kr' _ _ SPAN GTOP | destruct (go_region _ _ _ GO) as (r & Hr & Kr' & _ & _ & SPAN & GTOP) ]).
  (first [ pose proof (MR) as dR_9; dand6 dR_9 as WF CX GL ARS GR SHR | pose proof MR as (WF & CX & GL & ARS & GR & SHR) ]). (first [ pose proof (WF) as dR_10; dand5 dR_10 as Hres WR DJ WA WG | pose proof WF as (Hres & WR & DJ & WA & WG) ]).
  (first [ pose proof ((WR _ _ Hr)) as dR_11; dand5 dR_11 as R0 RAL _ RC RF | destruct (WR _ _ Hr) as (R0 & RAL & _ & RC & RF) ]).
  destruct (SHR _ r Hr Kr') as [WRr RDr].
  change (MI_Inv.MR st g) with (get_meta_rec st g) in *.
  set (stride := get_stride (get_meta_rec st g)) in *.
  set (q := (snd (aadd c (UNIT * off)) - snd bm - UNIT) / UNIT) in *.
  cbn [aadd snd] in q.
  set (res := snd c + stride - IB - (snd c + UNIT * off) - n).
  assert (Fc : fst c = fst bm) by (rewrite EC; reflexivity).
  assert (Ec2 : snd c = snd bm + UNIT + stride * i).
  { rewrite EC. cbn [snd]. unfold sstart, gbase. rewrite MEM. reflexivity. }
  change ((snd c + UNIT * off - snd (default (0%N, 0) (Some bm)) - UNIT) / UNIT) with q in K2, K1, Q.
  assert (RES0 : 0 <= res) by (subst res; try (generalize alloc_ceiling_val); clear - FIT HN; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia).
  assert (Eres : snd c + stride - IB - (snd c + UNIT * off) - n = res) by reflexivity.
  rewrite Eres in K3, K5, Kr.
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; [try (generalize alloc_ceiling_val); clear - S16; try pose proof alloc_ceiling_val; unfold UNIT in S16; lia| try (generalize alloc_ceiling_val); clear - HI; try pose proof alloc_ceiling_val; lia]).
  assert (OFS : 16 * off + 16 <= stride).
  { clear - FIT HN SM S16 HOFF; try pose proof alloc_ceiling_val. unfold UNIT, IB in *. Z.div_mod_to_equations. nia. }
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; [try (generalize alloc_ceiling_val); clear - S16; try pose proof alloc_ceiling_val; unfold UNIT in S16; lia| try (generalize alloc_ceiling_val); clear - HI; try pose proof alloc_ceiling_val; lia]. }
  assert (EHI : snd c + stride <= round_up_pg (r_len r)).
  { rewrite Ec2. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. try (generalize alloc_ceiling_val); clear - SPAN SIL; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
  (* [comment removed for export] *)
  unfold sstart, gbase in H0. rewrite MEM in H0. cbn [fst snd] in H0. fold stride in H0.
  assert (EE : snd bm + UNIT + stride * (i + 1) - IB = snd c + stride - IB) by (rewrite Ec2; clear; unfold UNIT, IB; lia).
  rewrite EE in H0. rewrite <- Fc in H0.
  (* [comment removed for export] *)
  assert (RDB : forall o v, 0 <= o < round_up_pg (r_len r) -> known st (fst c, o) v -> bytes_at rsegs m (r_base r + o) [b8 v] /\ 0 <= v < 256).
  { intros o v Ho Kn. apply (RDr o v Ho). rewrite <- Fc. exact Kn. }
  assert (LO3 : 0 <= snd c + UNIT * off - 3) by (try (generalize alloc_ceiling_val); clear - SI0 B0 Ec2 HOFF; try pose proof alloc_ceiling_val; unfold UNIT in *; lia).
  assert (HI3 : snd c + stride <= round_up_pg (r_len r) /\ 16 * off + 16 <= stride /\ 16 <= stride) by (try (generalize alloc_ceiling_val); clear - EHI OFS S16; try pose proof alloc_ceiling_val; unfold UNIT in *; lia).
  exists st, off, g, bm, i, r, ar, q, res.
  split; [exists LB0; split; [exact PERM| split; [exact Hst| split; [exact MR| split; [exact BLK| exact AR]]]]|].
  split; [symmetry; exact Hst|]. split; [exact MR|]. split; [exact (ci_ticks _ _ C)|].
  split. { rewrite KA, KS, (conc_region' st c r ltac:(rewrite Fc; exact Hr)). clear. lia. }
  rewrite KS, KZ.
  constructor.
  - exact SL.
  - exists ai. exact HO.
  - exact MEM.
  - rewrite Fc. exact Hr.
  - exact Kr'.
  - exact Fc.
  - exact Ec2.
  - exact B0.
  - exact HI.
  - exact HOFF.
  - exact HN.
  - exact FIT.
  - split; [exact S16| exact SM].
  - exact SI0.
  - exact SPAN.
  - split; [exact R0|]. split; [exact RAL|]. split; [exact RC|]. apply (reserved_disjoint1 _ _ RF). pose proof (round_up_pg_ge (r_len r)). try (generalize alloc_ceiling_val); clear - H EHI S16 Ec2 B0 SI0; try pose proof alloc_ceiling_val. unfold UNIT in *. lia.
  - split; [| exact QR]. try (generalize alloc_ceiling_val); clear - Q16; try pose proof alloc_ceiling_val. unfold UNIT in Q16. lia.
  - split; [reflexivity| exact RES0].
  - exact K4.
  - exact K3.
  - exact K2.
  - exact K1.
  - exact (go_slot _ _ _ GO).
  - (first [ pose proof ((go_slot _ _ _ GO)) as dR_12; dex3 dR_12 as a' ara k'; dand3 dR_12 as Ha' Hk' Eg' | pose proof ((go_slot _ _ _ GO)) as dR_12; dand6 dR_12 as a' ara k' Ha' Hk' Eg' | destruct (go_slot _ _ _ GO) as (a' & ara & k' & Ha' & Hk' & Eg') ]). rewrite Eg'. (first [ pose proof ((WA a' ara Ha')) as dR_13; dex1 dR_13 as rg0; dand3 dR_13 as _ A00 _ | pose proof ((WA a' ara Ha')) as dR_13; dand4 dR_13 as rg0 _ A00 _ | destruct (WA a' ara Ha') as (rg0 & _ & A00 & _) ]).
    cbn [aadd snd]. try (generalize alloc_ceiling_val); clear - A00 Hk'; try pose proof alloc_ceiling_val. unfold AREA_HDR, META_SIZE. lia.
  - replace (area_of g) with a; [split; [exact Ha| exact Hck]|]. rewrite Eg. symmetry. apply area_of_mslot; [exact Hal| exact Hka].
  - exact (go_avail _ _ _ GO).
  - exact (go_freed _ _ _ GO).
  - (first [ pose proof ((ci_cx _ _ C)) as dR_14; dand5 dR_14 as _ _ _ _ SE' | destruct (ci_cx _ _ C) as (_ & _ & _ & _ & SE') ]). exact SE'.
  - exact (go_li _ _ _ GO).
  - exact (go_freeable _ _ _ GO).
  - destruct BSC as [X|E63]; [left; exact X| right]. destruct (go_sc _ _ _ GO) as [Y|Y]; [exfalso; try (generalize alloc_ceiling_val); clear - Y E63; try pose proof alloc_ceiling_val; lia| exact Y].
  - exact (go_maplen _ _ _ GO).
  - intros SC48. (first [ pose proof ((g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ HO) SC48)) as dR_15; dand3 dR_15 as _ _ LT | pose proof (g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ HO) SC48) as (_ & _ & LT) ]). unfold cnt_of in LT. exact LT.
  - exact NA.
  - exact NF.
  - intros SC48. destruct BSC as [(A1 & A2 & A3)|E63]; [| exfalso; try (generalize alloc_ceiling_val); clear - SC48 E63; try pose proof alloc_ceiling_val; lia].
    pose proof (size_class_bound _ A1) as SB.
    apply (guard16_arith (size_class (m_sizeclass (get_meta_rec st g))) stride i off n q (m_last_idx (get_meta_rec st g)));
      [try (generalize alloc_ceiling_val); clear - SB; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Q16; try pose proof alloc_ceiling_val; unfold UNIT in Q16; lia| try (generalize alloc_ceiling_val); clear - FIT; try pose proof alloc_ceiling_val; unfold UNIT, IB in FIT; lia| exact HN| exact HOFF| exact HI
      | try (generalize alloc_ceiling_val); clear - A3; try pose proof alloc_ceiling_val; unfold UNIT in A3; lia
      | destruct A2 as [A2|A2]; [left; try (generalize alloc_ceiling_val); clear - A2; try pose proof alloc_ceiling_val; unfold UNIT in A2; lia| right; apply size_class_28; try (generalize alloc_ceiling_val); clear - A1 A2; try pose proof alloc_ceiling_val; lia]].
  - intros NM. destruct (TOP NM) as [BM0 GE]. unfold gend, cnt_of, sstart, gbase in GE.
    rewrite MEM in GE. cbn [default from_option id snd] in GE. fold stride in GE.
    pose proof (guard17_arith stride i off n q (m_last_idx (get_meta_rec st g)) (m_maplen (get_meta_rec st g))
                  ltac:(try (generalize alloc_ceiling_val); clear - S16; try pose proof alloc_ceiling_val; unfold UNIT in S16; lia) ltac:(try (generalize alloc_ceiling_val); clear - Q16; try pose proof alloc_ceiling_val; unfold UNIT in Q16; lia) ltac:(try (generalize alloc_ceiling_val); clear - FIT; try pose proof alloc_ceiling_val; unfold UNIT, IB in FIT; lia)
                  HN ltac:(try (generalize alloc_ceiling_val); clear - HOFF; try pose proof alloc_ceiling_val; lia) HI ltac:(try (generalize alloc_ceiling_val); clear - GE BM0; try pose proof alloc_ceiling_val; unfold UNIT in GE; lia)) as G17.
    rewrite <- (Z.div_mul (m_maplen (get_meta_rec st g) * 256) 16) by (clear; lia).
    replace (m_maplen (get_meta_rec st g) * 256 * 16) with (m_maplen (get_meta_rec st g) * 4096) by (clear; lia). exact G17.
  - exact GTOP.
  - replace (r_base r + snd c + UNIT * off - 3) with (r_base r + (snd c + UNIT * off - 3)) by (clear; lia).
    apply (proj1 (RDB (snd c + UNIT * off - 3) _ ltac:(try (generalize alloc_ceiling_val); clear - LO3 HI3; try pose proof alloc_ceiling_val; unfold UNIT in *; lia) K3)).
  - intros R5. (first [ pose proof ((K5 R5)) as dR_16; dand6 dR_16 as E4 E3 E2 E1 E5 R32 | destruct (K5 R5) as (E4 & E3 & E2 & E1 & E5 & R32) ]).
    split; [| split; [| exact R32]].
    + rewrite (le4_of_byte_of res) by (try (generalize alloc_ceiling_val); clear - RES0 R32; try pose proof alloc_ceiling_val; lia).
      change [b8 (byte_of res 0); b8 (byte_of res 1); b8 (byte_of res 2); b8 (byte_of res 3)]
        with ([b8 (byte_of res 0)] ++ ([b8 (byte_of res 1)] ++ ([b8 (byte_of res 2)] ++ [b8 (byte_of res 3)]))).
      assert (RG : 0 <= snd c + stride - IB - 5 /\ snd c + stride - IB <= round_up_pg (r_len r)) by (try (generalize alloc_ceiling_val); clear - LO3 HI3; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia).
      apply bytes_at_app. split; [replace (r_base r + snd c + stride - IB - 4) with (r_base r + (snd c + stride - IB - 4)) by (clear; lia); apply (proj1 (RDB (snd c + stride - IB - 4) _ ltac:(try (generalize alloc_ceiling_val); clear - RG; try pose proof alloc_ceiling_val; lia) E4))|].
      apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; replace (r_base r + snd c + stride - IB - 4 + 1) with (r_base r + (snd c + stride - IB - 3)) by (clear; lia); apply (proj1 (RDB (snd c + stride - IB - 3) _ ltac:(try (generalize alloc_ceiling_val); clear - RG; try pose proof alloc_ceiling_val; lia) E3))|].
      apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
      * replace (r_base r + snd c + stride - IB - 4 + 1 + 1) with (r_base r + (snd c + stride - IB - 2)) by (clear; lia). apply (proj1 (RDB (snd c + stride - IB - 2) _ ltac:(try (generalize alloc_ceiling_val); clear - RG; try pose proof alloc_ceiling_val; lia) E2)).
      * replace (r_base r + snd c + stride - IB - 4 + 1 + 1 + 1) with (r_base r + (snd c + stride - IB - 1)) by (clear; lia). apply (proj1 (RDB (snd c + stride - IB - 1) _ ltac:(try (generalize alloc_ceiling_val); clear - RG; try pose proof alloc_ceiling_val; lia) E1)).
    + replace (r_base r + snd c + stride - IB - 5) with (r_base r + (snd c + stride - IB - 5)) by (clear; lia).
      apply (proj1 (RDB (snd c + stride - IB - 5) _ ltac:(try (generalize alloc_ceiling_val); clear - LO3 HI3; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia) E5)).
  - destruct (Z.eq_dec res 0) as [R00|R00].
    + rewrite R00, Z.sub_0_r. replace (r_base r + snd c + stride - IB) with (r_base r + (snd c + stride - IB)) by (clear; lia).
      apply (proj1 (RDB (snd c + stride - IB) _ ltac:(try (generalize alloc_ceiling_val); clear - LO3 HI3; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia) H0)).
    + replace (r_base r + snd c + stride - IB - res) with (r_base r + (snd c + stride - IB - res)) by (clear; lia).
      assert (RR : res <= stride - IB - UNIT * off) by (rewrite <- Eres; try (generalize alloc_ceiling_val); clear - HN; try pose proof alloc_ceiling_val; lia).
      apply (proj1 (RDB (snd c + stride - IB - res) _ ltac:(try (generalize alloc_ceiling_val); clear - LO3 HI3 RES0 RR; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia) (Kr ltac:(try (generalize alloc_ceiling_val); clear - RES0 R00; try pose proof alloc_ceiling_val; lia)))).
  - replace (r_base r + snd c + stride - IB) with (r_base r + (snd c + stride - IB)) by (clear; lia).
    apply (proj1 (RDB (snd c + stride - IB) _ ltac:(try (generalize alloc_ceiling_val); clear - LO3 HI3; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia) H0)).
  - exact WRr.
  - apply (mf_active _ _ (Malls6g.areach_facts_proof _ _ AR)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lb_resize (b : block) (n' : Z) (LB : list block) : list block :=
  map (fun x => if aptr_eqb (blk_slot x) (blk_slot b) then (blk_id x, blk_addr x, n') else x) LB.

Lemma lb_resize_ids b n' LB : map blk_id (lb_resize b n' LB) = map blk_id LB.
Proof.
  unfold lb_resize. rewrite map_map. apply map_ext. intros x. destruct (aptr_eqb (blk_slot x) (blk_slot b)); reflexivity.
Qed.

(* [comment removed for export] *)

Lemma lb_resize_in b n' LB x : In x (lb_resize b n' LB) <->
  exists y, In y LB /\ x = (if aptr_eqb (blk_slot y) (blk_slot b) then (blk_id y, blk_addr y, n') else y).
Proof.
  unfold lb_resize. rewrite in_map_iff. split; [((first [ intro dR_19; dex1 dR_19 as y; destruct dR_19 as [E Hy] | intro dR_19; dand3 dR_19 as y E Hy | intros (y & E & Hy) ])); exists y; auto| ((first [ intro dR_20; dex1 dR_20 as y; destruct dR_20 as [Hy E] | intro dR_20; dand3 dR_20 as y Hy E | intros (y & Hy & E) ])); exists y; auto].
Qed.

(* [comment removed for export] *)
Lemma NoDup_map_in_inj {A B} (f : A -> B) (l : list A) x y :
  List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros ND Hx Hy E; [destruct Hx|]. cbn in ND. inversion ND; subst.
  destruct Hx as [->|Hx], Hy as [->|Hy]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply H1. rewrite E. apply in_map_iff. exists y; auto.
  - exfalso. apply H1. rewrite <- E. apply in_map_iff. exists x; auto.
Qed.

Lemma heap_slot_inj s LB m x y : HEAP s LB m -> In x LB -> In y LB -> blk_slot x = blk_slot y -> x = y.
Proof.
  ((first [ intro dR_21; dex1 dR_21 as st; dand5 dR_21 as LB0 PERM _ _ [_ AR] | intro dR_21; dand6 dR_21 as st LB0 PERM _ _ [_ AR] | intros (st & LB0 & PERM & _ & _ & [_ AR]) ]); intros Hx Hy E).
  pose proof (mf_nodup _ _ (Malls6g.areach_facts_proof _ _ AR)) as ND.
  assert (ND' : List.NoDup (map blk_slot LB)).
  { eapply Permutation_NoDup; [apply Permutation_map; exact PERM| exact ND]. }
  exact (NoDup_map_in_inj blk_slot LB x y ND' Hx Hy E).
Qed.

Lemma find_blk_resize b n' LB q :
  find_blk (lb_resize b n' LB) q =
  match find_blk LB q with
  | Some y => Some (if aptr_eqb (blk_slot y) (blk_slot b) then (blk_id y, blk_addr y, n') else y)
  | None => None
  end.
Proof.
  unfold find_blk, lb_resize. induction LB as [|x LB IH]; cbn; [reflexivity|].
  assert (EA : blk_addr (if aptr_eqb (blk_slot x) (blk_slot b) then (blk_id x, blk_addr x, n') else x) = blk_addr x).
  { destruct (aptr_eqb (blk_slot x) (blk_slot b)); reflexivity. }
  rewrite EA. destruct (Z.eqb (blk_addr x) q); [reflexivity| exact IH].
Qed.

Lemma p0_live_resize_self s s' LB m b n' : HEAP s LB m -> In b LB ->
  p0_live (mkIAS s' (lb_resize b n' LB) Rr) (blk_addr b) = Some n'.
Proof.
  intros HP Hb. unfold p0_live. cbn [ia_LB]. rewrite find_blk_resize.
  destruct (find_blk LB (blk_addr b)) as [y|] eqn:E.
  - apply find_blk_some in E. destruct E as [Hy EA].
    assert (y = b).
    { destruct (decide (blk_id y = blk_id b)) as [EI|NI].
      - eapply (NoDup_map_in_inj blk_id LB y b (heap_ids_nodup s LB m HP) Hy Hb EI).
      - exfalso. destruct (heap_blocks_apart s LB m HP y b Hy Hb NI); pose proof (heap_block_zone s LB m HP y Hy); pose proof (heap_block_zone s LB m HP b Hb); lia. }
    subst y. rewrite (proj2 (aptr_eqb_eq _ _) eq_refl). reflexivity.
  - exfalso. pose proof (p0_live_in s LB m b HP Hb) as L. unfold p0_live in L. cbn [ia_LB] in L. rewrite E in L. discriminate.
Qed.

Lemma p0_live_resize_other s s' LB m b n' q : HEAP s LB m -> In b LB -> q <> blk_addr b ->
  p0_live (mkIAS s' (lb_resize b n' LB) Rr) q = p0_live (mkIAS s LB Rr) q.
Proof.
  intros HP Hb NQ. unfold p0_live. cbn [ia_LB]. rewrite find_blk_resize.
  destruct (find_blk LB q) as [y|] eqn:E; [| reflexivity].
  apply find_blk_some in E. destruct E as [Hy EA].
  destruct (aptr_eqb_spec (blk_slot y) (blk_slot b)) as [ES|NS]; [| reflexivity].
  exfalso. apply NQ. rewrite <- EA. f_equal. exact (heap_slot_inj s LB m y b HP Hy Hb ES).
Qed.

Lemma in_block_resize s LB m b n' a : HEAP s LB m -> In b LB ->
  in_block (lb_resize b n' LB) a <->
  (blk_addr b <= a < blk_addr b + n') \/ (exists y, In y LB /\ y <> b /\ blk_addr y <= a < blk_addr y + blk_size y).
Proof.
  intros HP Hb. unfold in_block. split.
  - ((first [ intro dR_22; dex1 dR_22 as x; destruct dR_22 as [Hx Ha] | intro dR_22; dand3 dR_22 as x Hx Ha | intros (x & Hx & Ha) ])). apply lb_resize_in in Hx. (first [ dex1 Hx as y; destruct Hx as [Hy ->] | dand3 Hx as y Hy -> | destruct Hx as (y & Hy & ->) ]).
    destruct (aptr_eqb_spec (blk_slot y) (blk_slot b)) as [ES|NS].
    + left. rewrite <- (heap_slot_inj s LB m y b HP Hy Hb ES). cbn [blk_addr blk_size fst snd] in Ha. exact Ha.
    + right. exists y. split; [exact Hy|]. split; [intros ->; apply NS; reflexivity| exact Ha].
  - intros [Ha|(y & Hy & NY & Ha)].
    + exists (blk_id b, blk_addr b, n'). split; [| cbn [blk_addr blk_size fst snd]; exact Ha].
      apply lb_resize_in. exists b. split; [exact Hb|]. rewrite (proj2 (aptr_eqb_eq _ _) eq_refl). reflexivity.
    + exists y. split; [| exact Ha]. apply lb_resize_in. exists y. split; [exact Hy|].
      destruct (aptr_eqb_spec (blk_slot y) (blk_slot b)) as [ES|NS]; [exfalso; apply NY; exact (heap_slot_inj s LB m y b HP Hy Hb ES)| reflexivity].
Qed.

End CEIL.

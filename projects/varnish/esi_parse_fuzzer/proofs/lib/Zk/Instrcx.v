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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0 R_memset.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Arith MI_Geom MI_Pres2 MI_Cnt MI_WFree Mallkgx Mall1es Mall79j KNodes RzImpl KLink KLinkC MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import W_ge3a6 W_al5bs W_calloc Instfes Inst8ld InstDefs InstFree Instjhg Instffk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Lemma live_block_allzerop : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    m s LB b,
  HEAP s LB m -> mem_inv rsegs m -> In b LB -> a0 = Z_to_bv 64 (blk_addr b) ->
  exists st g i,
    ps_m s = strip st /\ (s_slots st) !! (blk_slot b) = Some (g, i) /\ fact_active (strip st) /\
    let mr := get_meta_rec st g in
    (m_sizeclass mr < 48 ->
       (get_stride mr <= UNIT * size_class (m_sizeclass mr) \/ 28 <= m_sizeclass mr)
       /\ (get_stride mr = UNIT * size_class (m_sizeclass mr) \/ (m_last_idx mr = 0 /\ m_maplen mr <> 0))) /\
    0 <= m_maplen mr /\
    evt rsegs (allzerop_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7
                 (allzerop_res (m_sizeclass mr) (m_last_idx mr) (m_maplen mr)) F fc m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 allzerop_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until b. intros HP MI Hb A0.
  (first [ dex1 HP as st; dand5 HP as LB0 PERM Hst MR [_ AR] | dand6 HP as st LB0 PERM Hst MR [_ AR] | destruct HP as (st & LB0 & PERM & Hst & MR & [_ AR]) ]).
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  pose proof (Mallx0l.areach_cinv_proof _ _ AR) as C.
  (first [ pose proof (AR) as dR_2; dand8 dR_2 as L LS BL INV LIVE RESV SEC CR | pose proof AR as (L & LS & BL & INV & LIVE & RESV & SEC & CR) ]).
  (first [ pose proof ((Forall2_In_l _ _ _ _ CR IN0)) as dR_3; dex1 dR_3 as k; destruct dR_3 as [Hk (KS & KZ & KA)] | pose proof ((Forall2_In_l _ _ _ _ CR IN0)) as dR_3; dand3 dR_3 as k Hk (KS & KZ & KA) | destruct (Forall2_In_l _ _ _ _ CR IN0) as (k & Hk & (KS & KZ & KA)) ]).
  destruct k as [[c off] n]. cbn [bslot boff bsize fst snd] in KS, KZ, KA.
  (first [ pose proof ((block_facts x0 st L BL LS INV c off n Hk)) as dR_4; dex7 dR_4 as g bm i ai a ar ka; rename dR_4 into BF | pose proof ((block_facts x0 st L BL LS INV c off n Hk)) as dR_4; dand8 dR_4 as g bm i ai a ar ka BF | destruct (block_facts x0 st L BL LS INV c off n Hk) as (g & bm & i & ai & a & ar & ka & BF) ]).
  exists st, g, i.
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
  pose proof (q16 _ _ _ _ _ _ _ _ _ _ _ BF) as [Q16 QR].
  pose proof (p_mod16 _ _ _ _ _ _ _ _ _ _ _ BF) as PM16.
  unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  unfold gbase in SH. rewrite MEM in SH.
  (first [ dand8 SH as K4 K3 K2 K1 Q K5 Kr KU | destruct SH as (K4 & K3 & K2 & K1 & Q & K5 & Kr & KU) ]).
  assert (HOST : hosts st bm g) by (exists ai; exact HO).
  pose proof (ci_gmetas _ _ C bm g HOST) as GO.
  (first [ pose proof ((go_region _ _ _ GO)) as dR_8; dex1 dR_8 as r; dand6 dR_8 as Hr Kr' _ _ SPAN _ | pose proof ((go_region _ _ _ GO)) as dR_8; dand7 dR_8 as r Hr Kr' _ _ SPAN _ | destruct (go_region _ _ _ GO) as (r & Hr & Kr' & _ & _ & SPAN & _) ]).
  (first [ pose proof (MR) as dR_9; dand6 dR_9 as WF CX GL ARS GR SHR | pose proof MR as (WF & CX & GL & ARS & GR & SHR) ]). (first [ pose proof (WF) as dR_10; dand5 dR_10 as Hres WR DJ WA WG | pose proof WF as (Hres & WR & DJ & WA & WG) ]).
  set (p := aadd c (UNIT * off)) in *.
  set (stride := get_stride (MI_Inv.MR st g)) in *.
  set (q := (snd p - snd bm - UNIT) / UNIT) in *.
  set (res := snd c + stride - IB - snd p - n).
  assert (Fp : fst p = fst bm) by (subst p; rewrite EC; reflexivity).
  assert (Ec2 : snd c = snd bm + UNIT + stride * i).
  { rewrite EC. cbn [snd]. unfold sstart, gbase. rewrite MEM. reflexivity. }
  assert (Sp : snd p = snd bm + UNIT + stride * i + UNIT * off) by (subst p; cbn [aadd snd]; rewrite Ec2; reflexivity).
  assert (Hrp : s_regions st !! fst p = Some r) by (rewrite Fp; exact Hr).
  assert (Cp : conc st p = r_base r + snd p) by (apply conc_region'; exact Hrp).
  assert (Cc : conc st c = r_base r + snd c) by (apply conc_region'; rewrite EC; cbn [fst]; exact Hr).
  assert (HA : blk_addr b = r_base r + snd p) by (rewrite KA, Cc; subst p; cbn [aadd snd]; clear; lia).
  change ((snd c + UNIT * off - snd (default (0%N, 0) (Some bm)) - UNIT) / UNIT) with q in K2, K1, Q.
  assert (Ebase : aadd p (- (UNIT * (byte_of q 0 + 256 * byte_of q 1)) - UNIT) = bm).
  { rewrite (u16_bytes q Q). unfold aadd. apply injective_projections; cbn [fst snd]; [exact Fp|]. try (generalize alloc_ceiling_val); clear - Q16 Sp; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
  assert (RES0 : 0 <= res) by (subst res; rewrite Sp, Ec2; try (generalize alloc_ceiling_val); clear - FIT HN; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia).
  pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF) as HLI.
  assert (IDX : Z.land (i + 32 * Z.min res 5) 31 = i) by (apply land31_idx; [try (generalize alloc_ceiling_val); clear - HI HLI; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - RES0; try pose proof alloc_ceiling_val; lia]).
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  split. { symmetry. exact Hst. }
  split. { rewrite KS. exact SL. }
  split. { apply (mf_active _ _ (Malls6g.areach_facts_proof _ _ AR)). }
  cbv zeta. split.
  { intros SC48. destruct BSC as [(A1 & A2 & A3)|E63]; [| exfalso; try (generalize alloc_ceiling_val); clear - SC48 E63; try pose proof alloc_ceiling_val; change (MI_Inv.MR st g) with (get_meta_rec st g) in E63; lia].
    split; [exact A2| exact A3]. }
  split. { exact ML0. }
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; [try (generalize alloc_ceiling_val); clear - S16; try pose proof alloc_ceiling_val; unfold UNIT in S16; lia| try (generalize alloc_ceiling_val); clear - HI; try pose proof alloc_ceiling_val; lia]).
  assert (OFS : 16 * off + 16 <= stride).
  { clear - FIT HN SM S16 HOFF; try pose proof alloc_ceiling_val. unfold UNIT, IB in *. Z.div_mod_to_equations. nia. }
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; [try (generalize alloc_ceiling_val); clear - S16; try pose proof alloc_ceiling_val; unfold UNIT in S16; lia| try (generalize alloc_ceiling_val); clear - HI; try pose proof alloc_ceiling_val; change (MI_Inv.MR st g) with (get_meta_rec st g) in HI; lia]. }
  assert (PHI : snd p + 16 <= round_up_pg (r_len r)).
  { rewrite Sp. change (get_stride (get_meta_rec st g)) with stride in SPAN. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
    try (generalize alloc_ceiling_val); clear - SPAN OFS SIL SI0 B0; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
  assert (A0u : bv_unsigned a0 = r_base r + snd p).
  { rewrite A0, HA. (first [ pose proof ((WR _ _ Hr)) as dR_11; dand5 dR_11 as R0 _ _ RC _ | destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _) ]).
    apply unsigned_lit. rewrite Sp in PHI |- *. clear - R0 RC PHI B0 SI0 HOFF; try pose proof alloc_ceiling_val. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold UNIT in *. lia. }
  pose proof (u16_bytes q QR) as U16.
  eapply (allzerop_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
            st p r g (mkGhdr (Some g) ai) ar (i + 32 * Z.min res 5) (byte_of q 0) (byte_of q 1)).
  all: rewrite ?IDX, ?Ebase, ?U16.
  - exact MR.
  - exact MI.
  - exact Hrp.
  - exact Kr'.
  - exact A0u.
  - exact PM16.
  - rewrite Sp. try (generalize alloc_ceiling_val); clear - B0 SI0 HOFF; try pose proof alloc_ceiling_val. unfold UNIT. lia.
  - rewrite Sp. try (generalize alloc_ceiling_val); clear - Q16 B0; try pose proof alloc_ceiling_val. unfold UNIT in *. lia.
  - exact PHI.
  - eapply (known_at _ _ _ _ _ _ K4); subst p; cbn [aadd fst snd]; [clear; lia| reflexivity].
  - eapply (known_at _ _ _ _ _ _ K3); subst p res; cbn [aadd fst snd]; [clear; lia| reflexivity].
  - eapply (known_at _ _ _ _ _ _ K2); subst p; cbn [aadd fst snd]; [clear; lia| reflexivity].
  - eapply (known_at _ _ _ _ _ _ K1); subst p; cbn [aadd fst snd]; [clear; lia| reflexivity].
  - exact HO.
  - reflexivity.
  - exact (go_slot _ _ _ GO).
  - (first [ pose proof ((go_slot _ _ _ GO)) as dR_12; dex3 dR_12 as a' ara k'; dand3 dR_12 as Ha' Hk' Eg' | pose proof ((go_slot _ _ _ GO)) as dR_12; dand6 dR_12 as a' ara k' Ha' Hk' Eg' | destruct (go_slot _ _ _ GO) as (a' & ara & k' & Ha' & Hk' & Eg') ]). rewrite Eg'. (first [ pose proof ((WA a' ara Ha')) as dR_13; dex1 dR_13 as rg0; dand3 dR_13 as _ A00 _ | pose proof ((WA a' ara Ha')) as dR_13; dand4 dR_13 as rg0 _ A00 _ | destruct (WA a' ara Ha') as (rg0 & _ & A00 & _) ]).
    cbn [aadd snd]. try (generalize alloc_ceiling_val); clear - A00 Hk'; try pose proof alloc_ceiling_val. unfold AREA_HDR, META_SIZE. lia.
  - exact MEM.
  - rewrite Eg, (area_of_mslot a ka Hal Hka). exact Ha.
  - exact Hck.
  - exact (go_avail _ _ _ GO).
  - exact (go_freed _ _ _ GO).
  - (first [ pose proof ((ci_cx _ _ C)) as dR_14; dand5 dR_14 as _ _ _ _ SE' | destruct (ci_cx _ _ C) as (_ & _ & _ & _ & SE') ]). exact SE'.
  - pose proof (go_li _ _ _ GO) as X. try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val. lia.
  - rewrite (go_freeable _ _ _ GO). clear. lia.
  - pose proof (go_sc _ _ _ GO) as X. try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val. lia.
  - pose proof (go_maplen _ _ _ GO) as X. try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val. lia.
  - clear - HI; try pose proof alloc_ceiling_val. exact (proj2 HI).
  - exact NA.
  - exact NF.
  - intros SC48. destruct BSC as [(A1 & A2 & A3)|E63]; [| exfalso; try (generalize alloc_ceiling_val); clear - SC48 E63; try pose proof alloc_ceiling_val; change (MI_Inv.MR st g) with (get_meta_rec st g) in E63; lia].
    change (MI_Inv.MR st g) with (get_meta_rec st g) in *.
    pose proof (size_class_bound _ A1) as SB.
    apply (guard16_arith (size_class (m_sizeclass (get_meta_rec st g))) stride i off n q (m_last_idx (get_meta_rec st g)));
      [try (generalize alloc_ceiling_val); clear - SB; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Q16; try pose proof alloc_ceiling_val; unfold UNIT in Q16; lia| try (generalize alloc_ceiling_val); clear - FIT; try pose proof alloc_ceiling_val; unfold UNIT, IB in FIT; lia| exact HN| exact HOFF| exact HI
      | try (generalize alloc_ceiling_val); clear - A3; try pose proof alloc_ceiling_val; unfold UNIT in A3; lia
      | destruct A2 as [A2|A2]; [left; try (generalize alloc_ceiling_val); clear - A2; try pose proof alloc_ceiling_val; unfold UNIT in A2; lia| right; apply size_class_28; try (generalize alloc_ceiling_val); clear - A1 A2; try pose proof alloc_ceiling_val; lia]].
  - intros SC48. destruct (go_sc _ _ _ GO) as [X|X]; try (generalize alloc_ceiling_val); clear - X SC48; try pose proof alloc_ceiling_val; lia.
  - intros NM. destruct (TOP NM) as [BM0 GE]. unfold gend, cnt_of, sstart, gbase in GE. change (MI_Inv.MR st g) with (get_meta_rec st g) in *.
    rewrite MEM in GE. cbn [default from_option id snd] in GE. fold stride in GE.
    pose proof (guard17_arith stride i off n q (m_last_idx (get_meta_rec st g)) (m_maplen (get_meta_rec st g))
                  ltac:(try (generalize alloc_ceiling_val); clear - S16; try pose proof alloc_ceiling_val; unfold UNIT in S16; lia) ltac:(try (generalize alloc_ceiling_val); clear - Q16; try pose proof alloc_ceiling_val; unfold UNIT in Q16; lia) ltac:(try (generalize alloc_ceiling_val); clear - FIT; try pose proof alloc_ceiling_val; unfold UNIT, IB in FIT; lia)
                  HN ltac:(try (generalize alloc_ceiling_val); clear - HOFF; try pose proof alloc_ceiling_val; lia) HI ltac:(try (generalize alloc_ceiling_val); clear - GE BM0; try pose proof alloc_ceiling_val; unfold UNIT in GE; lia)) as G17.
    rewrite <- (Z.div_mul (m_maplen (get_meta_rec st g) * 256) 16) by (clear; lia).
    replace (m_maplen (get_meta_rec st g) * 256 * 16) with (m_maplen (get_meta_rec st g) * 4096) by (clear; lia). exact G17.
Qed.

End CEIL.

(* [comment removed for export] *)
Definition stc_f27 (k : Z) : bool := stc_k k <=? 27.
Lemma stc_f27_true : forallb stc_f27 (zrange 0 255) = true. Proof. vm_compute. reflexivity. Qed.
Lemma size_to_class_27 n : 0 <= n <= 4076 -> size_to_class n <= 27.
Proof.
  intros Hn. rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB.
  set (k := (n + 4 - 1) / 2 ^ 4).
  assert (Hk : 0 <= k < 255) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (forallb_zrange stc_f27 0 255 k stc_f27_true ltac:(lia) ltac:(lia)) as H. unfold stc_f27 in H. apply Z.leb_le in H. exact H.
Qed.
Definition lor1_le27_check : bool := forallb (fun sc => Z.lor sc 1 <=? 27) (zrange 0 28).
Lemma lor1_le27_check_true : lor1_le27_check = true. Proof. vm_compute. reflexivity. Qed.
Lemma lor1_le27 x : 0 <= x <= 27 -> Z.lor x 1 <= 27.
Proof.
  intros Hx. pose proof (forallb_zrange _ 0 28 x lor1_le27_check_true ltac:(lia) ltac:(lia)) as X. cbv beta in X.
  apply Z.leb_le in X. exact X.
Qed.
Lemma size_class_255 sc : 0 <= sc <= 27 -> size_class sc <= 255.
Proof. intros H. pose proof (size_class_le sc 27 ltac:(lia) ltac:(lia) ltac:(lia)). change (size_class 27) with 255 in H0. lia. Qed.

Lemma allzerop_res0 mr n sc' :
  0 <= n <= 4076 -> m_sizeclass mr = sc' -> 0 <= sc' <= Z.lor (size_to_class n) 1 ->
  (m_sizeclass mr < 48 ->
     (get_stride mr <= UNIT * size_class (m_sizeclass mr) \/ 28 <= m_sizeclass mr)
     /\ (get_stride mr = UNIT * size_class (m_sizeclass mr) \/ (m_last_idx mr = 0 /\ m_maplen mr <> 0))) ->
  0 <= m_maplen mr ->
  allzerop_res (m_sizeclass mr) (m_last_idx mr) (m_maplen mr) = 0.
Proof.
  intros Hn Esc Hsc GS ML.
  pose proof (size_to_class_27 n Hn) as S27.
  pose proof (proj1 (size_to_class_ok n ltac:(unfold MMAP_THRESHOLD; lia))) as S0.
  pose proof (lor1_le27 (size_to_class n) ltac:(lia)) as L27.
  assert (SC27 : 0 <= m_sizeclass mr <= 27) by lia.
  pose proof (size_class_255 _ SC27) as C255.
  destruct (GS ltac:(lia)) as [G1 _].
  unfold allzerop_res. destruct (Z.leb_spec 48 (m_sizeclass mr)); [lia|].
  destruct (Z.eqb_spec (m_maplen mr) 0) as [M0|M0]; [reflexivity|].
  destruct (Z.eqb_spec (m_last_idx mr) 0) as [L0|L0]; cbn [negb orb]; [| reflexivity].
  unfold get_stride in G1. rewrite (proj2 (Z.eqb_eq _ _) L0) in G1. rewrite (proj2 (Z.eqb_neq _ _) M0) in G1. cbn [andb negb] in G1.
  unfold UNIT in G1. destruct G1 as [G1|G1]; [|lia].
  destruct (Z.ltb_spec (m_maplen mr * 4096 - 16) (16 * size_class (m_sizeclass mr))); [exfalso; lia| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_le_bytes_to_Z (bs : list byte) : Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  assert (R : 0 <= bytes_le_to_Z bs).
  { clear IH. induction bs as [|c cs IH2]; cbn [bytes_le_to_Z]; [lia|]. apply Z.lor_nonneg. split; [pose proof (bv_unsigned_in_range 8 c); lia| apply Z.shiftl_nonneg; exact IH2]. }
  rewrite (lor_shiftl8_add (bv_unsigned b) (bytes_le_to_Z bs)) by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap8_mod. change (2 ^ 8) with 256.
    Z.div_mod_to_equations. lia.
  - replace (Z.shiftr (bv_unsigned b + 256 * bytes_le_to_Z bs) 8) with (bytes_le_to_Z bs); [exact IH|].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. Z.div_mod_to_equations. lia.
Qed.

Lemma le8_surj (bs : list byte) : length bs = 8%nat -> exists w : word, le8 w = bs.
Proof.
  intros L. exists (le_bytes_to_word bs). unfold le8, word_to_le_bytes, le_bytes_to_word.
  rewrite Z_to_bv_unsigned.
  assert (R : 0 <= bytes_le_to_Z bs < 2^64).
  { rewrite bytes_le_to_Z_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as H. rewrite length_map, L in H. exact H. }
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
  rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Lemma rw_cells_C8x4 m A junk :
  rw_cells rsegs m A [CB 32 junk] -> exists j0 j1 j2 j3 : word, rw_cells rsegs m A [C8 j0; C8 j1; C8 j2; C8 j3].
Proof.
  intros H. pose proof H as [[WF _] _]. cbn in WF. destruct WF as [L _].
  destruct (le8_surj (firstn 8 junk) ltac:(rewrite length_firstn; lia)) as [j0 E0].
  destruct (le8_surj (firstn 8 (skipn 8 junk)) ltac:(rewrite length_firstn, length_skipn; lia)) as [j1 E1].
  destruct (le8_surj (firstn 8 (skipn 16 junk)) ltac:(rewrite length_firstn, length_skipn; lia)) as [j2 E2].
  destruct (le8_surj (skipn 24 junk) ltac:(rewrite length_skipn; lia)) as [j3 E3].
  exists j0, j1, j2, j3.
  assert (EJ : junk = take 8 junk ++ (take 8 (drop 8 junk) ++ (take 8 (drop 16 junk) ++ drop 24 junk))).
  { replace (drop 24 junk) with (drop 8 (drop 16 junk)) by (rewrite drop_drop; reflexivity). rewrite take_drop.
    replace (drop 16 junk) with (drop 8 (drop 8 junk)) by (rewrite drop_drop; reflexivity). rewrite !take_drop. reflexivity. }
  eapply rw_cells_congr; [| | | exact H].
  - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, E0, E1, E2, E3. exact EJ.
  - reflexivity.
  - cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I.
Qed.

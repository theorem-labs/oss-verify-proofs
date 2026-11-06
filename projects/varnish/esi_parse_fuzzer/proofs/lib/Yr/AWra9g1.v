(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic ALogic16 ARtStmts ACor4x6 ACoresk ACorg10.

Module AMalgej.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d ARt_3ti ARt_fpo ARt_png.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_a0k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMTac
     AMallocA AMallocH AMalmys AMal9l1 AMalgue AMaly5g AMal93m ASecZ ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.   (* [comment removed for export] *)
Local Ltac natz_kl :=
  repeat match goal with
  | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
      let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit za; natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz; clear H
  | H : (@length ?A ?l <= ?b)%nat |- _ =>
      let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz; clear H
  end.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Zifyk6b.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= natz_kl; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Zifyk6b.zon_hook.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Section BridgeC.
Context {Clg : Ceiling}.
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt depot_repL.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis BLK2 : classid_blk2_stmt.

  #[using="BLK2 BLK DPS PS TSS GT RZL"] Theorem alloc_hit_c :
    forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T : TSet),
      alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
      (* [comment removed for export] *)
      n <= kMaxPrimaryUser -> pk_chunks (a_cache A (class_of n)) <> [] ->
      alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T.
  Proof.
    intros until T. intros PRE NP NE K1.
    (first [ dand25 PRE as AI MI NRQ NCAP LIM NLV TINY SCRED PCRED CF TPE CLO LOSA SAHI HI47 SPA RAC2 ST SM SOLO SOHI TRC TRB KEYU KR | destruct PRE as (AI & MI & NRQ & NCAP & LIM & NLV & TINY & SCRED & PCRED & CF & TPE & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SM & SOLO & SOHI & TRC & TRB & KEYU & KR) ]).   (* [comment removed for export] *)
    subst tp. unfold alloc_entry_ms. cbn [cl_segs cl_malloc_pc LPA] in MI, K1 |- *.
    assert (NR : 1 <= n <= kMaxPrimaryUser) by (clear - NRQ NP; lia).
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spa) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    (first [ pose proof ((hit_kidx A m md n AI NR NE)) as dR_2; dand4 dR_2 as KWE KIN KB CNT | pose proof (hit_kidx A m md n AI NR NE) as (KWE & KIN & KB & CNT) ]).
    set (ks' := pk_chunks (a_cache A (class_of n))) in *.
    set (kidx := nth (length ks' - 1) ks' 0) in *.
    assert (KID : kidx = nth (length ks' - 1) ks' 0) by reflexivity.
    (first [ pose proof ((hit_class n NR)) as dR_3; dand5 dR_3 as CR HC FIT CSR CM32 | pose proof (hit_class n NR) as (CR & HC & FIT & CSR & CM32) ]).
    (first [ pose proof ((hit_geom A m md n kidx AI NR KIN)) as dR_4; dand15 dR_4 as ABE ABA ABQ ABR1 ABR2 RZ8 SB1 SB2 RB1 RB2 FIT2 _ _ _ KWR | pose proof (hit_geom A m md n kidx AI NR KIN) as (ABE & ABA & ABQ & ABR1 & ABR2 & RZ8 & SB1 & SB2 & RB1 & RB2 & FIT2 & _ & _ & _ & KWR) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_5; dand7 dR_5 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_6; dand13 dR_6 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]).
    (first [ pose proof ((hit_PC A m md n AI NR NE)) as dR_7; dex1 dR_7 as ks; dand5 dR_7 as LKS KW KSM KSF PC | pose proof ((hit_PC A m md n AI NR NE)) as dR_7; dand6 dR_7 as ks LKS KW KSM KSF PC | destruct (hit_PC A m md n AI NR NE) as (ks & LKS & KW & KSM & KSF & PC) ]). fold ks' in KW, KSF, PC. fold kidx in KW.
    (first [ pose proof ((hit_stats A m md n AI NR)) as dR_8; dex5 dR_8 as statv v0 v1 v2 vs; dand4 dR_8 as STA STS STA2 LVS | pose proof ((hit_stats A m md n AI NR)) as dR_8; dand9 dR_8 as statv v0 v1 v2 vs STA STS STA2 LVS | destruct (hit_stats A m md n AI NR) as (statv & v0 & v1 & v2 & vs & STA & STS & STA2 & LVS) ]).
    (first [ pose proof ((hit_HDR A m md n kidx AI NR KIN)) as dR_9; dex5 dR_9 as b0w b1w h2 w4 d8; rename dR_9 into HDR | pose proof ((hit_HDR A m md n kidx AI NR KIN)) as dR_9; dand6 dR_9 as b0w b1w h2 w4 d8 HDR | destruct (hit_HDR A m md n kidx AI NR KIN) as (b0w & b1w & h2 & w4 & d8 & HDR) ]).
    (first [ pose proof ((hit_ABH A m md n kidx AI NR KIN)) as dR_10; dex2 dR_10 as j0 j1; rename dR_10 into ABH | pose proof ((hit_ABH A m md n kidx AI NR KIN)) as dR_10; dand3 dR_10 as j0 j1 ABH | destruct (hit_ABH A m md n kidx AI NR KIN) as (j0 & j1 & ABH) ]).
    destruct (hit_USR A m md n kidx AI NR KIN) as (uj & USR).
    pose proof (Z_div_mod_eq_full n 8) as NDE. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as ER.
    (first [ pose proof ((hit_SH A m md n kidx AI NR KIN (n / 8) (n mod 8) NDE ER)) as dR_11; dex2 dR_11 as olds oldp; dand4 dR_11 as SHA SHU OL SHP | pose proof ((hit_SH A m md n kidx AI NR KIN (n / 8) (n mod 8) NDE ER)) as dR_11; dand6 dR_11 as olds oldp SHA SHU OL SHP | destruct (hit_SH A m md n kidx AI NR KIN (n / 8) (n mod 8) NDE ER) as (olds & oldp & SHA & SHU & OL & SHP) ]).
    (first [ pose proof ((hit_depot_wf A m md AI)) as dR_12; dand5 dR_12 as DND DLEN DTOT3 DKEY _ | pose proof (hit_depot_wf A m md AI) as (DND & DLEN & DTOT3 & DKEY & _) ]).
    pose proof (hit_DR A m md AI) as DR0.
    pose proof (hit_TC A m md AI) as TC. pose proof (hit_tsd A m md AI) as [TSD1 TSD2].
    (* [comment removed for export] *)
    (first [ pose proof ((sec_dkeys A WF0)) as dR_13; dand3 dR_13 as DK1 _ DK3 | pose proof (sec_dkeys A WF0) as (DK1 & _ & DK3) ]).
    assert (KL : (1 <= length key <= 255)%nat) by exact (proj1 (Forall_forall _ _) DK1 key KEYU).
    assert (DTOT : depot_total (a_depot A) + 1 + Z.of_nat (length key) < kStackStoreBlockFrames).
    { (first [ pose proof ((wfD A WF0)) as dR_14; dand3 dR_14 as INC NDd _ | destruct (wfD A WF0) as (INC & NDd & _) ]).
      assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros k Hk; exact (proj1 (Forall_forall _ _) INC k Hk)).
      (first [ pose proof ((depot_universe_bounds _ _ DK1 DK3 NDd INC')) as dR_15; dand3 dR_15 as L1 _ L3 | pose proof (depot_universe_bounds _ _ DK1 DK3 NDd INC') as (L1 & _ & L3) ]). unfold kStackStoreBlockFrames. clear - L1 L3 KL. lia. }
    (* [comment removed for export] *)
    assert (LO : alloc_ceiling <= lo /\ lo <= bv_unsigned spa - 1024) by (clear - CLO LOSA; lia).
    assert (CEIL : alloc_ceiling <= bv_unsigned spa - 1024) by (clear - CLO LOSA; lia).
    assert (SPR' : bv_unsigned spa + 65536 < 2^64) by (clear - SAHI HI47; lia).
    assert (NR64 : 1 <= n <= 64512) by (clear - NR; unfold kMaxPrimaryUser in NR; lia).
    assert (NDE' : n = 8 * (n / 8) + n mod 8) by (clear - NDE; lia).
    assert (SOA : bv_unsigned spa <= stkobj /\ stkobj + 2064 <= 2^47) by (clear - SOLO SOHI HI47; lia).
    assert (TSDL : 0x5e8328 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e83d8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    assert (KWR' : bv_unsigned (wz (kidx * class_size (class_of n) / kCompactPtrScale)) < 2^32) by (rewrite unsigned_lit by lia; lia).
    assert (ABE' : chunk_addr (a_sb A) (class_of n) kidx = a_sb A + class_of n * 2^32 + 16 * bv_unsigned (wz (kidx * class_size (class_of n) / kCompactPtrScale))) by (rewrite unsigned_lit by lia; exact ABE).
    assert (DRF : forall D' (m1 m2 : mem), depot_repL AL_pasan rsegs D' (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) m1 ->
              (forall a, ACells.depot_foot AL_pasan (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) ->
              depot_repL AL_pasan rsegs D' (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) m2).
    { intros D' m1 m2 H1 H2. exact (depot_repL_agree AL_pasan rsegs D' _ _ m1 m2 H1 H2). }
    (* [comment removed for export] *)
    pose proof (alloc_hit rac spa gp (cl_tp LPA) t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                  (aview_of (pa_hull A) m) lo n stkobj canfill pa_tsd (p_ctx (a_pl A)) (p_thr (a_pl A))
                  (class_of n) (Z.of_nat (length ks')) (max_count (class_of n)) (a_sb A) (chunk_addr (a_sb A) (class_of n) kidx)
                  (chunk_addr (a_sb A) (class_of n) kidx / 8) (rz_size n / 8) (n / 8) (n mod 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A))
                  ks b0w b1w (wz (kidx * class_size (class_of n) / kCompactPtrScale)) statv h2 w4 d8 j0 j1 v0 v1 v2 vs (a_depot A) key olds uj oldp depot_repL
                  MI ST LO SPA SPR' NR64 NDE' ER CF SOA RZL GT TSS PS DPS BLK BLK2
                  (hit_INI A m md AI) (hit_RSS A m md AI) (hit_RZm A m md AI) (hit_MUM A m md AI) (hit_PCo A m md AI)
                  (hit_AF1 A m md AI) (hit_AF2 A m md AI) (hit_AF44 A m md AI) (hit_AF52 A m md AI) (hit_LS1 A m md AI) (hit_LS2 A m md AI)
                  (hit_HK A m md AI) (hit_SBc A m md AI)
                  TC (hit_TH0 A m md AI) (hit_CT8 A m md AI) (conj TH1 TH2) THRA (conj CT1 CT2) TSDL TPL
                  (conj SB1 SB2) SEP_thr SEP_ctx SEP_tc
                  HC PC LKS CNT KW KWR' STA STS STA2 LVS
                  ABE' ABA ABQ (conj ABR1 ABR2) RZ8 HDR (fun _ => ABH) SHA SHU OL SHP USR
                  DR0 DND DLEN DTOT (conj DN01 DN02) (conj DF01 DF02) SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DRF
                  KL KR TRC TRB) as EV.
    (* [comment removed for export] *)
    destruct (asI_minv A m md AI) as [HMI HH].
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) _ _ md T HMI HH).
    { rewrite restrict_MS. exact EV. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex21 HQ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' v' md0; dand18 HQ as -> MU WM' MI' ST' Ppc Psta Psts Psta2 Phdr Plch Pshz Pshw Pshe Pusr Pdr Pmu2 WM2 | dand36 HQ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' v' md0 -> MU WM' MI' ST' Ppc Psta Psts Psta2 Phdr Plch Pshz Pshw Pshe dR_HQ_t0; dand4 dR_HQ_t0 as Pusr Pdr Pmu2 WM2 | destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & vc' & v0' & v1' & v2' & v' & md0
                    & -> & MU & WM' & MI' & ST' & Ppc & Psta & Psts & Psta2 & Phdr & Plch & Pshz & Pshw & Pshe & Pusr & Pdr & Pmu2 & WM2) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v') = v').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> aview_of (pa_hull A) m (wz a) <> None -> v' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NN _ _ a WM'); clear - H0 H1 H2; lia. }
    pose proof (b1_final_ok (bv_unsigned b1w) ltac:(pose proof (bv_unsigned_in_range _ b1w); lia)) as [B1R B1M].
    pose proof (hit_u_fresh A m md n kidx AI NR NE KID) as FR. (first [ pose proof ((hit_u_range A n kidx NR)) as dR_17; dand3 dR_17 as UR1 UR2 UE | pose proof (hit_u_range A n kidx NR) as (UR1 & UR2 & UE) ]).
    assert (IDR : 0 <= snd (depot_putC (a_depot A) key) < 2^32) by (pose proof (depot_putC_id_range (a_depot A) key) as X; clear - X DLEN; lia).
    assert (SMW : mapped (aview_of (pa_hull A) m) lo (hi - lo)).
    { intros i Hi. destruct (Z_lt_le_dec (lo + i) (bv_unsigned spa)) as [L|GE].
      - (first [ dand3 ST as _ _ ST3 | destruct ST as (_ & _ & ST3) ]). destruct (ST3 (lo + i) ltac:(clear - Hi L; lia)) as [X _]. unfold wview, wa in X.
        intros E. apply X. rewrite E. cbn [cl_segs LPA]. rewrite unsigned_lit by (clear - Hi L CLO CE SPR; lia).
        rewrite (pa_find_segment_none (lo + i) 1); [reflexivity| clear - Hi L CLO CE SPR; lia| right; clear - Hi L CLO CE SPR; lia].
      - replace (lo + i) with (bv_unsigned spa + (lo + i - bv_unsigned spa)) by lia. apply SM. clear - Hi GE; lia. }
    rewrite <- UE.
    pose proof (GEO A m md n kidx spa AI NR NE KID CEIL) as G. fold kidx in G.
    eapply (K1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (hit_user A n kidx) (hitA A n kidx key) (munrestrict (hidc (pa_hull A)) m v') md').
    - (* [comment removed for export] *)
      constructor.
      + exact (hit_WF A m md n kidx key AI NR NE KID KEYU LIM NLV TINY PCRED).   (* [comment removed for export] *)
      + change (ahull_of pa_image_ivs AL_pasan (hitA A n kidx key)) with (pa_hull A). rewrite VIEW.
        exact (hit_arepr A m md n kidx key spa v' AI NR NE KID CEIL MU NN md0 ks _ _ LKS KSF Ppc B1R B1M IDR Phdr Plch Pshz Pshe Pdr Pmu2).
      + cbn [hitA a_pl a_reg a_sec]. apply (hit_hidden A m md n kidx spa v' lo AI NR NE KID CLO (proj2 LO) MU WM'). exact (ai_hidden _ _ _ _ _ _ _ AI).
      + cbn [hitA a_pl]. exact (ai_extra _ _ _ _ _ _ _ AI).
      + cbn [hitA a_pl a_sec]. exact (aledger_sbm _ _ _ _ md md' Hsame (ai_ledger _ _ _ _ _ _ _ AI)).
      + exact HI'.
      + (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _) ]). rewrite HLT. exact HH.
      + (* [comment removed for export] *) cbn [hitA a_pl a_sec]. rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_cover _ _ _ _ _ _ _ AI).
      + (* [comment removed for export] *) rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_ceil _ _ _ _ _ _ _ AI).
    - (* [comment removed for export] *)
      change (pa_hull (hitA A n kidx key)) with (pa_hull A). rewrite VIEW. exact MI'.
    - (* [comment removed for export] *)
      unfold amd_frame. (first [ dand18 FRM as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | destruct FRM as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
      rewrite X2, X17, HH. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption| reflexivity].
    - apply hull_le_refl.
    - intros ff. reflexivity.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      intros c0 [VR VC] [X|X]; [exfalso; clear - X NR; lia|]. split; [exact VR|].
      cbn [hitA a_cache]. unfold hit_cache. rewrite (proj2 (Z.eqb_neq c0 (class_of n)) X). exact VC.
    - rewrite UE. clear - G. kung_all. lia.
    - unfold as_live, as_live_. rewrite FR. reflexivity.
    - unfold as_live, as_live_. cbn [hitA a_livemap]. rewrite lookup_insert_eq. reflexivity.
    - intros q Hq. unfold as_live, as_live_. cbn [hitA a_livemap]. rewrite lookup_insert_ne by congruence. reflexivity.
    - unfold as_livebytes. cbn [hitA a_livemap]. rewrite (as_livebytes_insert _ _ _ FR). cbn [li_n]. lia.
    - unfold as_tinycred. cbn [hitA a_tiny]. unfold is_tiny. reflexivity.
    - unfold as_nlive. cbn [hitA a_livemap]. rewrite (as_nlive_insert _ _ _ FR). reflexivity.
    - unfold as_seccred. cbn [hitA a_scred]. destruct (Z.ltb_spec kMaxPrimaryUser n); lia.
    - (* [comment removed for export] *)
      unfold as_primcred. cbn [hitA a_pcred]. rewrite (prim_cost_primary n NP). reflexivity.
    - (* [comment removed for export] *) intros _ X. exfalso. clear - X NR. lia.
    - (* [comment removed for export] *) split; [intros _| intros _; exact NP]. rewrite UE. change (p_sb (a_pl A)) with (a_sb A). clear - ABR1 ABR2 G NR. kung_all. lia.
    - (* [comment removed for export] *)
      change (pa_hull (hitA A n kidx key)) with (pa_hull A). rewrite VIEW.
      exact (hit_frame_ok A m md n kidx key spa v' lo hi AI NR NE KID CLO (proj2 LO) SAHI HI47 MU WM' SMW).
    - (* [comment removed for export] *)
      change (pa_hull (hitA A n kidx key)) with (pa_hull A). rewrite VIEW. intros i Hi. cbn [cl_errno LPA]. unfold mrd.
      rewrite (AGimg A m md n kidx spa v' AI NR NE KID CEIL MU (6193972 + i)); [reflexivity| clear - Hi; lia| clear - Hi; lia].
    - (* [comment removed for export] *)
      change (pa_hull (hitA A n kidx key)) with (pa_hull A). rewrite VIEW. intros a Ha.
      (first [ pose proof ((USH A m md n kidx spa AI NR NE KID CEIL)) as dR_21; dand4 dR_21 as U1 U2 U3 _ | pose proof (USH A m md n kidx spa AI NR NE KID CEIL) as (U1 & U2 & U3 & _) ]). pose proof (div8_ceil n ltac:(lia)) as DC.
      apply (AGW A m n kidx spa v' MU); [clear - Ha HI47 SPR; lia|].
      apply (W_shape A m md n kidx spa AI NR NE KID CEIL); clear - Ha HI47 SPR G U3 DC CE; kung_all; lia.
    - change (pa_hull (hitA A n kidx key)) with (pa_hull A). rewrite VIEW. exact ST'.
  Qed.
End BridgeC.

(* [comment removed for export] *)
Section Closed.
Context {Clg : Ceiling}.
  Theorem alloc_hit_c_closed :
    forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T : TSet),
      alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
      n <= kMaxPrimaryUser -> pk_chunks (a_cache A (class_of n)) <> [] ->
      alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T.
  Proof. exact (alloc_hit_c rzlog_ok get_thread_ok thread_stats_ok poison_ok depot_put_ok classid_blk_ok classid_blk2_ok). Qed.
End Closed.
End AMalgej.

Module ACoreTop.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic ACor4x6 ACorg10.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMal92l ASecTop.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACorg10 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWra9g1.AMalgej OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMal92l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecTop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section CoreTop.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Hypothesis POP : pop_core_stmt.
  Hypothesis A8 : a8_core_cps1_stmt.

  (* [comment removed for export] *)
  Theorem alloc_core_cps1_ok : alloc_core_cps1.
  Proof.
    unfold alloc_core_cps1. intros until T1. intros PRE K1.
    pose proof PRE as PRE'. (first [ dand4 PRE' as _ _ NRQ _ | destruct PRE' as (_ & _ & NRQ & _) ]).
    destruct (Z_lt_le_dec kMaxPrimaryUser n) as [SEC|PRI].
    - (* [comment removed for export] *)
      destruct (Z_lt_le_dec n 524288) as [SMALL|BIG].
      + eapply sec_core_cps1_ok; [exact PRE| lia | exact K1].
      + eapply A8; [exact PRE| lia | exact K1].
    - destruct (pk_chunks (a_cache A (class_of n))) as [|ch chs] eqn:CH.
      + (* [comment removed for export] *)
        destruct (Z_lt_le_dec (Z.of_nat (length (rg_free (a_reg A (class_of n))))) (refill_count (class_of n))) as [SHORT|ENOUGH].
        * (* [comment removed for export] *)
          exact (POP rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A n canfill stkobj lo hi key T1
                   PRE PRI CH SHORT K1).
        * (* [comment removed for export] *)
          exact (alloc_refill_cE_closed rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A n canfill stkobj lo hi key T1
                   PRE PRI CH ENOUGH K1).
      + (* [comment removed for export] *)
        exact (alloc_hit_c_closed rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A n canfill stkobj lo hi key T1
                 PRE PRI ltac:(rewrite CH; discriminate) K1).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

End CoreTop.
End ACoreTop.

Module AWrapTop.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d ARt_6n0 ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic ALogic16 ARtStmts ACor4x6 ACoresk ACorg10.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AWrapC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AWrapC AWrapR AWrapF.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACorg10 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWra9g1.ACoreTop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapC.AWrapM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapF.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WrapTop.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Hypothesis POP : pop_core_stmt.
  Hypothesis A8 : a8_core_cps1_stmt.
  Hypothesis DCORE : dealloc_core_cps.

  Let ACORE1 : alloc_core_cps1 := alloc_core_cps1_ok POP A8.

  (* [comment removed for export] *)
  Theorem pa_malloc16_top : @pa_malloc_obligation16 _ DepotRepL.
  Proof. exact (pa_malloc16_of_core unwind_ok ACORE1). Qed.

  Theorem pa_calloc16_top : @pa_calloc_obligation16 _ DepotRepL.
  Proof. exact (pa_calloc16_of_core unwind_ok ACORE1). Qed.

  Theorem pa_realloc16_top : @pa_realloc_obligation16 _ DepotRepL.
  Proof. exact (pa_realloc16_of_core unwind_ok thread_stats_ok ACORE1 DCORE). Qed.

  (* [comment removed for export] *)
  Theorem pa_malloc_top : @pa_malloc_obligation _ DepotRepL.
  Proof. exact (pa_malloc_15_of_16 pa_malloc16_top). Qed.

  Theorem pa_calloc_top : @pa_calloc_obligation _ DepotRepL.
  Proof. exact (pa_calloc_15_of_16 pa_calloc16_top). Qed.

  Theorem pa_realloc_top : @pa_realloc_obligation _ DepotRepL.
  Proof. exact (pa_realloc_15_of_16 pa_realloc16_top). Qed.

  Theorem pa_free_top : @pa_free_obligation _ DepotRepL.
  Proof. exact (pa_free_of_core DCORE). Qed.

End WrapTop.
End AWrapTop.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACorg10 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWra9g1.AWrapTop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WrapTop16.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Theorem pasan_AsanAlloc16_of :
    forall (Hm : @pa_malloc_obligation _ DepotRepL) (Hf : @pa_free_obligation _ DepotRepL) (Hc : @pa_calloc_obligation _ DepotRepL)
           (Hr : @pa_realloc_obligation _ DepotRepL) (Hs : @pa_smalloc_obligation _ DepotRepL) (Hsf : @pa_sfree_obligation _ DepotRepL),
      @pa_malloc_obligation16 _ DepotRepL -> @pa_calloc_obligation16 _ DepotRepL -> @pa_realloc_obligation16 _ DepotRepL ->
      @AsanAlloc16 Clg (pasan_AsanAlloc Hm Hf Hc Hr Hs Hsf).
  Proof.
    intros Hm Hf Hc Hr Hs Hsf M16 C16 R16. constructor.
    - exact M16.
    - exact C16.
    - exact R16.
  Qed.

  Hypothesis POP : pop_core_stmt.
  Hypothesis A8 : a8_core_cps1_stmt.
  Hypothesis DCORE : dealloc_core_cps.

  Theorem pasan_AsanAlloc16_top :
    forall (Hm : @pa_malloc_obligation _ DepotRepL) (Hf : @pa_free_obligation _ DepotRepL) (Hc : @pa_calloc_obligation _ DepotRepL)
           (Hr : @pa_realloc_obligation _ DepotRepL) (Hs : @pa_smalloc_obligation _ DepotRepL) (Hsf : @pa_sfree_obligation _ DepotRepL),
      @AsanAlloc16 Clg (pasan_AsanAlloc Hm Hf Hc Hr Hs Hsf).
  Proof.
    intros. apply pasan_AsanAlloc16_of;
      [exact (pa_malloc16_top POP A8) | exact (pa_calloc16_top POP A8) | exact (pa_realloc16_top POP A8 DCORE)].
  Qed.
End WrapTop16.

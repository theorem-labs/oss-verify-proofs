(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSnjd ARtSrgm AMalmys ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQWf2 AQPart ACover AFreeR AFreeR2 AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2 AFreeRP AFreeRQ AFreeRU AFreeRC.

Module AFreeRI1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSnjd ARtSrgm AMalmys ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQWf2 AQPart ACover AFreeR AFreeR2 AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2 AFreeRP AFreeRQ AFreeRU AFreeRC AWrapKit ACoresk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRQ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve,
                        kQuarantineBatchBytes, kQuarantineBatchCount in *.

Section RIter.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Variables (rac spd gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet).
  (* [comment removed for export] *)
  Variables (xs2 xs5 : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HI47 : hi <= 2^47.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis VB : forall a, newblk p n0 a -> a < alloc_ceiling.
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation T := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation v0 := (aview_of (pa_hull A0) m0).

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation put_frame := (put_frameG rac spd s0 s1 s2 s3 s4 s5 s6 stkobj).
  #[warnings="-notation-for-abbreviation"] Local Notation rec_frame := (rec_frameG spd stkobj xs2).
  #[warnings="-notation-for-abbreviation"] Local Notation dorec_fr := (dorec_frG s7 s8 s9 stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation CUR := (CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p n0 stkobj lo hi xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation it_cfg := (it_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation head_cfg := (head_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation blk_cfg := (blk_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation exit_cfg := (exit_cfgG spd gp s7 s8 s9 s10 s11 F fc stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation XCUR := (XCURG rac spd s0 s1 s2 s3 s4 s5 s6 A0 m0 md0 p n0 stkobj lo hi xs2).

  (* [comment removed for export] *)
  #[using="VB SPA HI47 SPHI LOW CEIL"] Lemma step_prim_push : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (c k n : Z),
    CUR A m md (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChP (CP c k)) n) ->
    Z.of_nat (length (pk_chunks (a_cache A c))) < max_count c ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        (S i < length (ba_entries b0))%nat -> CUR A' m' md' (Some (b0, S i)) more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (it_cfg A' m' md' b0 (Z.of_nat (S i)) dorec_callblk (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'') TS) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        (S i = length (ba_entries b0))%nat -> CUR A' m' md' (Some (b0, S i)) more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (it_cfg A' m' md' b0 (Z.of_nat (S i)) dorec_batchblk (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'') TS) ->
    srealizes rsegs (it_cfg A m md b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Proof.
    intros A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CU NTH ROOM KM KD.
    destruct CU as [RI HIST MI ST PF RF DF [LEN ILE] QB]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC) : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    assert (L' : a_qlimbo A = BA (ba_idx b0) (QE (ChP (CP c k)) n :: skipn (S i) (ba_entries b0)) :: more).
    { rewrite L. unfold limbo_of. rewrite (skipn_cons_nth (ba_entries b0) i _ NTH). reflexivity. }
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (* [comment removed for export] *)
    (first [ pose proof ((rk_ri A v [] AR)) as dR_1; dand10 dR_1 as RI0 RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v [] AR) as (RI0 & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    (first [ pose proof ((rk_sep A v [] AR)) as dR_2; dand6 dR_2 as SP1 SP2 SP3 SP4 SP5 SP6 | pose proof (rk_sep A v [] AR) as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6) ]).
    (first [ pose proof ((rk_place A v [] AR)) as dR_3; dand6 dR_3 as PT PTC PTM PC PCC _ | pose proof (rk_place A v [] AR) as (PT & PTC & PTM & PC & PCC & _) ]).
    pose proof (rk_TC A v [] AR) as TC. pose proof (rk_PCo A v [] AR) as PCo. pose proof (rk_SBc A v [] AR) as CSB. pose proof (rk_CRI A v [] AR) as CRI.
    pose proof (wrI A W) as CI.
    (first [ pose proof ((rk_stats A v [] AR)) as dR_4; dex3 dR_4 as statv rf rfd; dand4 dR_4 as RFR RFDR STA TRF | pose proof ((rk_stats A v [] AR)) as dR_4; dand7 dR_4 as statv rf rfd RFR RFDR STA TRF | destruct (rk_stats A v [] AR) as (statv & rf & rfd & RFR & RFDR & STA & TRF) ]).
    pose proof (ev_wf A v [] c k n _ _ _ AR W L') as WE. pose proof (ev_carved A v [] c k n _ _ _ AR W L') as CVe.
    (first [ pose proof ((rk_line A v [] AR CI c ltac:(exact (proj1 CVe)))) as dR_5; dex1 dR_5 as ks; dand7 dR_5 as LKS KSM KSF KLE KRG KND LINE | pose proof ((rk_line A v [] AR CI c ltac:(exact (proj1 CVe)))) as dR_5; dand8 dR_5 as ks LKS KSM KSF KLE KRG KND LINE | destruct (rk_line A v [] AR CI c ltac:(exact (proj1 CVe))) as (ks & LKS & KSM & KSF & KLE & KRG & KND & LINE) ]).
    pose proof (ek_geo A v [] c k n AR WE) as G.
    destruct RC as [RAR RTMP RCH RME RMO RCUR]. cbn [rc_cur] in RCUR. (first [ dand3 RCUR as RENT RBAT RBSH | destruct RCUR as (RENT & RBAT & RBSH) ]).
    pose proof (RENT i _ (Nat.le_refl i) NTH) as LE.
    (first [ pose proof ((ek_cells A v [] c k n AR WE LE)) as dR_7; dex2 dR_7 as b1 ctxw; dand10 dR_7 as B1R HDR CTXW MAG SHC SHQ QL SHA R88 MP | pose proof ((ek_cells A v [] c k n AR WE LE)) as dR_7; dand12 dR_7 as b1 ctxw B1R HDR CTXW MAG SHC SHQ QL SHA R88 MP | destruct (ek_cells A v [] c k n AR WE LE) as (b1 & ctxw & B1R & HDR & CTXW & MAG & SHC & SHQ & QL & SHA & R88 & MP) ]).
    pose proof (ek_slot v (a_sb A) (batch_addr (a_sb A) b0) (ba_entries b0) i (batch_bytes b0) i _ RBAT (Nat.le_refl i) NTH LEN) as SLOT. cbn [qe_chunk qe_n] in SLOT.
    pose proof (batch_known A v [] AR (BA (ba_idx b0) (QE (ChP (CP c k)) n :: skipn (S i) (ba_entries b0))) (head_in A _ _ more W L')) as [KBR _]. cbn [ba_idx] in KBR.
    pose proof (rk_batch A v [] AR (ba_idx b0) KBR) as BG. cbv zeta in BG. (first [ dand9 BG as BFORM BLO BHI BAL KB0 KBH SEP_bt SEP_bc SEP_br | destruct BG as (BFORM & BLO & BHI & BAL & KB0 & KBH & SEP_bt & SEP_bc & SEP_br) ]).
    (first [ pose proof ((rk_region_facts A v [] AR c (proj1 CVe))) as dR_9; dand7 dR_9 as RGF1 RGF2 RGF3 RGF4 RGF5 RGF6 RGF7 | destruct (rk_region_facts A v [] AR c (proj1 CVe)) as (RGF1 & RGF2 & RGF3 & RGF4 & RGF5 & RGF6 & RGF7) ]).
    (first [ pose proof ((rk_region A v [] AR c 0%nat (proj1 CVe) ltac:(lia))) as dR_10; dex4 dR_10 as na nfs v88 junk; dand8 dR_10 as RMX RNF RMFA RMU RNA RNFS LJ RARR | pose proof ((rk_region A v [] AR c 0%nat (proj1 CVe) ltac:(lia))) as dR_10; dand12 dR_10 as na nfs v88 junk RMX RNF RMFA RMU RNA RNFS LJ RARR | destruct (rk_region A v [] AR c 0%nat (proj1 CVe) ltac:(lia)) as (na & nfs & v88 & junk & RMX & RNF & RMFA & RMU & RNA & RNFS & LJ & RARR) ]).
    (* [comment removed for export] *)
    pose proof (head_in A _ _ more W L') as HIN.
    assert (NEhb : ChP (CP kQuarantineBatchClass (ba_idx b0)) <> ChP (CP c k)).
    { intros E. exact (quar_not_batch A v [] AR _ _ (ev_in A c k n _ _ _ W L') HIN (eq_sym E)). }
    pose proof (carved_disjoint A v [] AR _ _ (batch_carved A v [] AR _ HIN) CVe NEhb) as Dbp. cbn [chunk_lo chunk_hi alloc_beg ba_idx] in Dbp.
    (first [ dand25 G as Gcr Gcc Gnr Gk Grz Grzm Gu1 Gu2 Gu3 Gfit Gcsr Gcm Gpe Gka Gam Gmk Gplo Gphi Gpm Gsbm Guo Gho Gab Gclo Gchi | destruct G as (Gcr & Gcc & Gnr & Gk & Grz & Grzm & Gu1 & Gu2 & Gu3 & Gfit & Gcsr & Gcm & Gpe & Gka & Gam & Gmk & Gplo & Gphi & Gpm & Gsbm & Guo & Gho & Gab & Gclo & Gchi) ]).
    pose proof TC as TC'. (first [ dand13 TC' as _ _ _ _ _ Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct TC' as (_ & _ & _ & _ & _ & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    pose proof (max_count_range c Gcr) as (MCR & _). pose proof (class_size_mod32 c Gcr) as CS32.
    set (thr := p_thr (a_pl A)) in *. set (sb := a_sb A) in *. set (ri := a_ri A) in *.
    set (b := batch_addr sb b0) in *. set (cnt := Z.of_nat (length (ba_entries b0))) in *.
    set (pp := chunk_addr sb c k) in *. set (mh := pp + rz_size n - 16) in *. set (fac_ := free_array_of sb c) in *.
    set (cntc := Z.of_nat (length (pk_chunks (a_cache A c)))) in *.
    set (kk := k * class_size c / kCompactPtrScale).
    set (Q := fun ms' : machine_state => exists (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 statv' : word) (m' : mem) (pc : Z),
           ms' = MS (it_regs (wz dsp) gp (cl_tp LPA) T b cnt s10 s11 (wz dorec_retpc) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 (Z.of_nat i + 1)) F (wz pc) fc None m' (seg_rom rsegs) /\
           ((Z.of_nat i + 1 < cnt /\ pc = dorec_callblk) \/ (Z.of_nat i + 1 = cnt /\ pc = dorec_batchblk)) /\
           rw_cells rsegs m' dsp (dorec_fr thr scr) /\
           (rz_size n - 16 = 0 \/ rw_cells rsegs m' pp [C8 (wz 0)]) /\
           rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi (user_size n))); C4 (wz (user_size n))] /\
           bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (round_up (user_size n) 8 / 8))) /\
           rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + user_size n))] /\
           rw_cells rsegs m' (thr + 208 + 80 * c) [C4 (wz (cntc + 1)); C4 (wz (max_count c)); C8 (wz (class_size c)); CB 64 (u32s (upd ks (Z.to_nat cntc) (wz kk)))] /\
           rw_cells rsegs m' (thr + 208 + 2576) [C8 statv'] /\
           munch [(dsp - 112, dsp); (pp, pp + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + round_up (user_size n) 8 / 8);
                  (thr + 2840, thr + 2856); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584)] v m' /\
           wmono rsegs v m' /\ mem_inv rsegs m' /\ stk rsegs m' lo dsp).
    unfold it_cfgG. fold sb. fold b cnt.
    eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR A) pa_wxR _ (pa_eager A) Q _ md TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (iter_prim_push gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b cnt (Z.of_nat i) scr
                (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                pa_tsd (p_ctx (a_pl A)) thr sb ri)
        with (kb := 512 * ba_idx b0) (c := c) (idx := k) (d := rz_size n - 16) (mu := rg_mapped_user (a_reg A c)) (n := user_size n) (b1 := b1)
             (rf := rf) (rfd := rfd) (cntc := cntc) (maxc := max_count c) (k := kk) (old := fd8 ((user_size n + 7) / 8)) (ks := ks) (statv := statv)
             (pw := wz (hdr_of sb (ChP (CP c k)) n)) (mh := mh).
      all: try assumption.
      all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
      all: try assumption.
      all: cycle -2. 3: cycle 0.
      1: { intros LT a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' DF' SL' MU' MG' HD' SH' TF' LN' ST' MUN WM' MI' STK'.
           apply evt_done. subst Q. first [ hotw_ex18 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' dorec_callblk | exists a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', statv', m', dorec_callblk ].
           split; [reflexivity|]. split; [left; split; [exact LT| reflexivity]|].
           repeat (split; [assumption|]). exact STK'. }
      1: { intros EQ a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' DF' SL' MU' MG' HD' SH' TF' LN' ST' MUN WM' MI' STK'.
           apply evt_done. subst Q. first [ hotw_ex18 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' dorec_batchblk | exists a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', statv', m', dorec_batchblk ].
           split; [reflexivity|]. split; [right; split; [exact EQ| reflexivity]|].
           repeat (split; [assumption|]). exact STK'. }
      all: first [ assumption | reflexivity
                 | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                 | unfold pa_tsd; clear; lia
                 | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                 | unfold cnt; clear -LEN; unfold kQuarantineBatchCount in LEN; lia
                 | clear -SBRI RHI; lia
                 | clear -KB0 KBH; lia
                 | pose proof (nth_error_Some_lt _ _ _ NTH) as IL; unfold cnt; clear -IL; lia
                 | unfold mh, pp in *; rewrite Gho; rewrite unsigned_lit; [reflexivity| clear -Gplo Gphi Grz Gfit Gu1 CE; kung_all; pose proof (round_up_ge (user_size n) 8 ltac:(lia)); lia]
                 | unfold mh, pp in *; clear -Gpe; lia
                 | pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU; clear -RU Grz Gfit Gu1; lia
                 | clear -Grzm; lia
                 | clear -Gk; lia
                 | clear -Gka Gam; lia
                 | clear -Gmk Gam Gka Gk Gcsr; kung_all; nia
                 | unfold kk; unfold kCompactPtrScale; clear -Gcm Gk; nia
                 | clear -Gu1 Gu3 Gnr; unfold kMaxPrimaryUser in *; lia
                 | unfold mh, pp in *; clear -Gfit Gphi CE; lia
                 | unfold cntc; clear -ROOM; lia
                 | clear -MCR; lia
                 | match goal with |- ?g => idtac "UNSOLVED:" g end ]. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex18 HQ as a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' pc; dand13 HQ as -> CASE DF' MG' HD' SH' TF' LN' ST' MUN WM' MI' STK' | dand31 HQ as a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' pc -> CASE DF' MG' HD' SH' TF' LN' ST' MUN WM' MI' STK' | destruct HQ as (a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t0'' & t1'' & t2'' & t3'' & t4'' & t5'' & t6'' & statv' & m' & pc & -> & CASE & DF' & MG' & HD' & SH' & TF' & LN' & ST' & MUN & WM' & MI' & STK') ]).
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m m') = m').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NNR _ _ a WM'); [exact H1| lia]. }
    (* [comment removed for export] *)
    set (fa' := rg_mapped_fa (a_reg A c)).
    set (es' := skipn (S i) (ba_entries b0)) in *.
    set (cache' := recp_cache (a_cache A) c k).
    set (A' := recA' A (a_reg A) cache' (BA (ba_idx b0) es' :: more)).
    assert (RGE : recp_reg (a_reg A) (a_cache A) c k fa' = a_reg A).
    { unfold recp_reg. fold cntc. destruct (Z.eqb_spec cntc (max_count c)); [exfalso; clear -e ROOM; lia| reflexivity]. }
    assert (CAE : pk_chunks (cache' c) = pk_chunks (a_cache A c) ++ [k]).
    { unfold cache', recp_cache, cache_set, cache_push_list. rewrite Z.eqb_refl. fold cntc. destruct (Z.eqb_spec cntc (max_count c)); [exfalso; clear -e ROOM; lia| reflexivity]. }
    assert (CAO : forall c', c' <> c -> cache' c' = a_cache A c').
    { intros c' NE. unfold cache', recp_cache, cache_set. destruct (Z.eqb_spec c' c); [exfalso; exact (NE e)| reflexivity]. }
    assert (EXT : same_ext (a_reg A) (a_reg A)) by (intros c0; split; reflexivity).
    pose proof (su_hull A (a_reg A) cache' (BA (ba_idx b0) es' :: more) EXT) as HULL. pose proof (su_lhull A (a_reg A) cache' (BA (ba_idx b0) es' :: more) EXT) as LHULL.   (* [comment removed for export] *)
    pose proof (su_eager A (a_reg A) cache' (BA (ba_idx b0) es' :: more) EXT) as EAGER.
    change (mkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with A' in HULL, LHULL, EAGER.
    (* [comment removed for export] *)
    set (Wn := fun a => dsp - 112 <= a < dsp).
    set (SHP := fun a => sh (pp + rz_size n) <= a < sh (pp + rz_size n) + (user_size n + 7) / 8).
    pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU.
    assert (MU : forall a, 0 <= a < 2^64 -> ~ rp_foot A c k (a_reg A) Wn SHP a -> m' (wz a) = v (wz a)).
    { intros a Ha NF. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha; lia). unfold rp_foot in NF. subst Wn SHP. cbv beta in NF.
      cbn [outside]. unfold pp, mh, sb, thr, cntc in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NF.
      - left. exact X.
      - right; left. clear -X Gcsr. lia.
      - right; left. clear -X Grz Gfit RU Gu1. lia.
      - right; right; left. unfold pp in X. replace (chunk_addr (a_sb A) c k + rz_size n - 16 + 16) with (chunk_addr (a_sb A) c k + rz_size n) in X by lia. rewrite ?R88 in X. exact X.
      - do 4 right; left. clear -X. lia.
      - do 3 right; left. exact X.
      - do 4 right; left. clear -X. lia. }
    (* [comment removed for export] *)
    assert (W' : WFR A').
    { pose proof (WFR_prim A _ c k n fa' _ more W L' ltac:(intros E; exfalso; unfold cntc in ROOM; clear -E ROOM; lia)) as X.
      unfold recpA in X. rewrite RGE in X. exact X. }
    assert (WNH : forall a, Wn a -> alloc_ceiling <= a) by (subst Wn; cbv beta; intros a Ha; clear -Ha CEIL LOW; lia).
    pose proof (round_up_mod (user_size n) 8 ltac:(lia)) as RUM.
    assert (SHPW : forall a, SHP a -> sh pp <= a < sh pp + class_size c / 8).
    { subst SHP; cbv beta; intros a Ha. rewrite SHA in Ha. clear -Ha Gfit Grz Grzm CS32 RUM RU Gu1 R88. lia. }
    (* [comment removed for export] *)
    assert (DISJ : forall a l, 0 < l -> (ri <= a /\ a + l <= ri + 4096) \/ (fac_ <= a /\ a + l <= fac_ + rg_mapped_fa (a_reg A c)) \/ (T <= a /\ a + l <= uspd) ->
             disjoint_from [(dsp - 112, dsp); (pp, pp + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + round_up (user_size n) 8 / 8);
                            (thr + 2840, thr + 2856); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584)] a l).
    { intros a l Hl Ha. unfold pp, mh, thr, ri, sb, fac_ in *. cbn [disjoint_from].
      (first [ pose proof ((rk_region_facts A v [] AR c (proj1 CVe))) as dR_14; dand4 dR_14 as _ _ RG3 _ | pose proof (rk_region_facts A v [] AR c (proj1 CVe)) as (_ & _ & RG3 & _) ]).
      destruct Ha as [Ha|[Ha|Ha]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
      all: first [ clear -Ha Hl Gcr SBRI RLO RHI CEIL LOW CE SPR; kung_all; lia
                 | clear -Ha Hl SP1 Gcr; unfold apart in SP1; lia
                 | clear -Ha Hl SP4 Gcr RG3 SBRI; unfold apart, free_array_of in *; kung_all; lia
                 | clear -Ha Hl Gpe Gka Gam Gmk Gcr SBRI Gcsr Gk Grz Gfit RU Gu1 RG3; unfold free_array_of in *; kung_all; lia
                 | clear -Ha Hl Gplo Gphi Grz Gfit RU Gu1 CE SBRI SBLO Gpe Gcr Gk Gcsr RG3 CEIL LOW; unfold sh, free_array_of in *; kung_all; lia
                 | clear -Ha Hl PTC CEIL LOW Gcr; lia
                 | clear -Ha Hl Gcr SBRI RHI RG3 CEIL LOW; unfold free_array_of in *; kung_all; lia ]. }
    assert (OUT : forall a, (ri <= a < ri + 4096 \/ fac_ <= a < fac_ + rg_mapped_fa (a_reg A c) \/ T <= a < uspd) ->
             outside [(dsp - 112, dsp); (pp, pp + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + round_up (user_size n) 8 / 8);
                      (thr + 2840, thr + 2856); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584)] a).
    { intros a Ha. apply (disjoint_outside _ a 1); [| clear; lia]. apply DISJ; [clear; lia|]. clear -Ha. lia. }
    assert (P_mx : u64_at rsegs m' (ri + 128 * c) 0).
    { assert (X : rw_cells rsegs m' (ri + 128 * c) [C8 (wz 0)]).
      { eapply rw_cells_transport; [exact RMX| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. left. cbn [cells_size csize Nat.add]. clear -Gcr. lia. }
      destruct X as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    assert (P_regc : region_repr_ LPA sb (a_reg A c) m' c).
    { apply (region_P A v m' [] AR NN c Gcr). intros a Ha. unfold rfoot in Ha. rewrite RIA, FAE in Ha. unfold kRegionInfoSize in Ha. fold fac_ in Ha.
      apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RLO RHI CE SBLO SBRI RGF3; unfold fac_, free_array_of in *; kung_all; lia).
      apply OUT. clear -Ha Gcr. lia. }
    (* [comment removed for export] *)
    assert (ENC : forall k', In k' (pk_chunks (a_cache A c)) \/ k' = k -> 0 <= k' * class_size c / kCompactPtrScale < 2^32).
    { intros k' Hk'. assert (KR' : 0 <= k' < carved_count A c) by (destruct Hk' as [Hk'| ->]; [exact (KRG k' Hk')| exact Gk]).
      unfold kCompactPtrScale. clear -KR' RGF6 Gam Gmk Gcsr. split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. kung_all. nia. }
    assert (ENT : forall i0 k', nth_error (pk_chunks (a_cache A c) ++ [k]) i0 = Some k' ->
              nth_error (upd ks (Z.to_nat cntc) (wz kk)) i0 = Some (wz (k' * class_size c / kCompactPtrScale)) /\ 0 <= k' * class_size c / kCompactPtrScale < 2^32).
    { intros i0 k' Hk'. destruct (Nat.lt_ge_cases i0 (length (pk_chunks (a_cache A c)))) as [LT|GE].
      - rewrite nth_error_app1 in Hk' by exact LT. split; [| apply ENC; left; eapply nth_error_In; exact Hk'].
        rewrite nth_error_upd_other by (unfold cntc; clear -LT; lia).
        pose proof (f_equal (fun l => nth_error l i0) KSF) as E. cbv beta in E. rewrite nth_error_firstn in E.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A c)))); [| exfalso; clear -LT H; lia]. rewrite E, nth_error_map, Hk'. reflexivity.
      - rewrite nth_error_app2 in Hk' by exact GE. destruct (i0 - length (pk_chunks (a_cache A c)))%nat as [|x] eqn:EQ; cbn in Hk'; [injection Hk' as <-| destruct x; discriminate].
        assert (i0 = length (pk_chunks (a_cache A c))) by (clear -GE EQ; lia). subst i0. split; [| apply ENC; right; reflexivity].
        unfold cntc. rewrite Nat2Z.id. rewrite nth_error_upd_same by (rewrite LKS; unfold cntc in ROOM; clear -ROOM MCR; lia). reflexivity. }
    pose proof LN' as LNx. unfold cntc in LNx at 1.
    replace (Z.of_nat (length (pk_chunks (a_cache A c))) + 1) with (Z.of_nat (length (pk_chunks (a_cache A c) ++ [k]))) in LNx by (rewrite length_app; cbn; lia).
    pose proof (line_of_cells m' (thr + 208 + 80 * c) c (upd ks (Z.to_nat cntc) (wz kk)) (pk_chunks (a_cache A c) ++ [k]) (a_cache_inited A) Gcr CI
                  ltac:(rewrite upd_length; exact LKS) ltac:(rewrite length_app; cbn [length]; unfold cntc in ROOM; clear -ROOM MCR; lia) ENT
                  LNx) as P_linec.
    rewrite <- CAE in P_linec.
    replace (thr + 208 + 80 * c) with (thr + off_th_per_class c) in P_linec by (unfold off_th_per_class, off_th_alloc_cache, kPerClassSize; clear; lia).
    assert (MFA8 : rg_mapped_fa (a_reg A c) mod 8 = 0) by (apply (mod0_down _ kFreeArrayMapSize 8); [exists (2^15); reflexivity| exact RGF4]).
    assert (R'E : rg_mapped_user (a_reg A c) = rg_mapped_user (a_reg A c) /\ rg_allocated_user (a_reg A c) = rg_allocated_user (a_reg A c) /\
                  rg_mapped_fa (a_reg A c) <= rg_mapped_fa (a_reg A c) /\ rg_mapped_fa (a_reg A c) <= kFreeArraySize /\ rg_mapped_fa (a_reg A c) mod 8 = 0).
    { clear -RGF3 MFA8. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; try lia. }
    assert (VSH : bytes_at rsegs m' (sh pp) (pshadow_free c)).
    { apply (vsh_entry A v m' [] c k (a_reg A) AR Wn WNH SHP CVe R'E MU n WE LE).
      - intros a. subst SHP. cbv beta. unfold pp, sb. split; intros X; exact X.
      - replace (chunk_addr (a_sb A) c k + rz_size n) with (mh + 16) by (unfold mh, pp, sb; clear; lia). exact SH'. }
    assert (P_fash : bytes_at rsegs m' (sh (fac_ + rg_mapped_fa (a_reg A c))) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_fa (a_reg A c) - rg_mapped_fa (a_reg A c)) / 8)))).
    { rewrite Z.sub_diag. cbn. apply bytes_at_nil. unfold sh, fac_, free_array_of. clear -Gcr SBLO SBRI RHI RGF3 CE. kung_all. lia. }
    pose proof (recp_arepr A v m' [] c k more (a_reg A) cache' AR W Wn WNH SHP SHPW CVe
                  (ev_ne_live A v [] c k n _ _ _ AR W L') (ev_ne_batch A v [] c k n _ _ _ AR W L') (ev_ne_rest A c k n _ _ _ W L')
                  CAO ltac:(intros k' Hk'; rewrite CAE in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|[<-|[]]]; [left; exact Hk'| right; reflexivity])
                  ltac:(intros; reflexivity) R'E ltac:(intros k' Hk'; left; exact Hk')
                  MU NN P_mx P_regc P_linec VSH P_fash (BA (ba_idx b0) es' :: more)) as AR'.
    change (recA' _ _ _ _) with A' in AR'.
    (* [comment removed for export] *)
    pose proof (ev_ne_batch A v [] c k n _ _ _ AR W L') as NEB. pose proof (ev_ne_limbo A c k n _ _ _ W L') as NEL.
    assert (INmore : forall b' e', In b' more -> In e' (ba_entries b') -> In e' (es' ++ q_entries more)).
    { intros b' e' Hb' He'. apply in_or_app. right. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He'). }
    assert (INhead : forall j e', (S i <= j)%nat -> nth_error (ba_entries b0) j = Some e' -> In e' (es' ++ q_entries more)).
    { intros j e' Hj He'. apply in_or_app. left. subst es'. apply (nth_error_In _ (j - S i)). rewrite nth_error_skipn. replace (S i + (j - S i))%nat with j by (clear -Hj; lia). exact He'. }
    assert (RC' : rcells A' m' T (Some (b0, S i)) more).
    { constructor.
      - exact AR'.
      - unfold tmp_hdr. eapply rw_cells_transport; [exact RTMP| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia.
      - apply (tmp_chain_xfer A v m' [] c k (ba_idx b0) _ more (a_reg A) cache' AR W L' Wn WNH SHP SHPW CVe NEB R'E MU more); [intros b' Hb'; exact Hb'| exact RCH].
      - intros b' e' Hb' He'. apply (lentry_xfer A v m' [] c k (a_reg A) AR Wn WNH SHP SHPW CVe R'E MU NN e').
        + apply (limbo_in A (ba_idx b0) _ more W L'). cbn [app]. right. exact (INmore b' e' Hb' He').
        + apply NEL. exact (INmore b' e' Hb' He').
        + exact (RME b' e' Hb' He').
      - intros b' Hb'. destruct (RMO b' Hb') as [LB SHB]. pose proof (more_in A (ba_idx b0) _ more W L' b' Hb') as Hb2.
        destruct (lbatch_xfer A v m' [] c k (a_reg A) cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b') (ba_entries b') 0%nat (batch_bytes b')
                    (batch_carved A v [] AR b' Hb2) (NEB b' (or_intror Hb')) (proj2 (batch_known A v [] AR b' Hb2)) LB) as [LB' SHB'].
        split; [exact LB'| exact (SHB' SHB)].
      - split; [|split].
        + intros j e' Hj He'. apply (lentry_xfer A v m' [] c k (a_reg A) AR Wn WNH SHP SHPW CVe R'E MU NN e').
          * apply (limbo_in A (ba_idx b0) _ more W L'). cbn [app]. right. exact (INhead j e' Hj He').
          * apply NEL. exact (INhead j e' Hj He').
          * exact (RENT j e' ltac:(clear -Hj; lia) He').
        + assert (LBi : lbatch_cells sb v (chunk_addr sb kQuarantineBatchClass (ba_idx b0)) (ba_entries b0) (S i) (batch_bytes b0)).
          { (first [ dand3 RBAT as X1 X2 X3 | destruct RBAT as (X1 & X2 & X3) ]). split; [| exact (conj X2 X3)]. intros i0 e' Hi0 He'. apply (X1 i0 e'); [clear -Hi0; lia| exact He']. }
          exact (proj1 (lbatch_xfer A v m' [] c k (a_reg A) cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b0) (ba_entries b0) (S i) (batch_bytes b0)
                           (batch_carved A v [] AR _ HIN) NEhb LEN LBi)).
        + exact (proj2 (lbatch_xfer A v m' [] c k (a_reg A) cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b0) (ba_entries b0) i (batch_bytes b0)
                           (batch_carved A v [] AR _ HIN) NEhb LEN RBAT) RBSH). }
    (* [comment removed for export] *)
    assert (RI' : RINV A' (munrestrict (hidc (pa_hull A)) m m') md' T (Some (b0, S i)) more).
    { constructor.
      - exact W'.
      - reflexivity.
      - rewrite HULL, VIEW. exact RC'.
      - apply (su_hidden A (a_reg A) cache' (BA (ba_idx b0) es' :: more) EXT m m' HID).
        + intros z Gz Hz Vz. destruct Gz as [SMz _]. unfold in_shadow_maps in SMz. apply NN; [clear -SMz; kung_all; lia| right; clear -SMz; kung_all; lia| clear -SMz; kung_all; lia| exact Vz].
        + intros z Gz Hz NHS. destruct Gz as [SMz _]. apply (AG_shadow_maps A v m' [] c k (a_reg A) AR Wn WNH SHP SHPW CVe R'E MU z SMz).
          * intros SP. apply NHS. (first [ pose proof ((chunk_shadow A v [] AR c k Gcr Gk)) as dR_16; dand3 dR_16 as _ S2 _ | pose proof (chunk_shadow A v [] AR c k Gcr Gk) as (_ & S2 & _) ]). apply S2. exact (SHPW z SP).
          * rewrite Z.sub_diag. clear. intros X. cbn in X. lia.
        + intros z Hz Hc Vz. apply NN; [clear -Hz; kung_all; lia| right; clear -Hz; kung_all; lia| clear -Hz; kung_all; lia| exact Vz].
      - exact EXTRA.
      - first [ exact (aledger_sbm _ _ _ _ md md' Hsame LED)
              | (* [comment removed for export] *)
                refine (aledger_reg _ _ _ _ _ _ (fun c0 _ => EXT c0) (aledger_sbm _ _ _ _ md md' Hsame LED)) ].
      - rewrite HULL, LHULL, EAGER. exact HI'.   (* [comment removed for export] *)
      - (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT' _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT' & _) ]). rewrite HLT'. exact HLT.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact COV.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact CEI. }
    (* [comment removed for export] *)
    assert (PF' : put_frame (p_thr (a_pl A)) m').
    { unfold put_frameG in *. eapply rw_cells_transport; [exact PF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
    assert (RF' : rec_frame (p_thr (a_pl A)) m').
    { unfold rec_frameG in *. eapply rw_cells_transport; [exact RF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
    assert (SM' : mapped m' lo (uspd - lo)).
    { intros q Hq. pose proof (rc_tmp _ _ _ _ _ RC') as TM'. unfold tmp_hdr in TM'.
      destruct (Z.lt_ge_cases (lo + q) dsp) as [C1|C1].
      { exact (stk_mapped_pa m' lo dsp lo (dsp - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
      destruct (Z.lt_ge_cases (lo + q) T) as [C2|C2].
      { pose proof (rw_mapped_hi m' _ _ DF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
        specialize (M (lo + q - dsp) ltac:(clear -C1 C2; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M. }
      destruct (Z.lt_ge_cases (lo + q) (T + 32)) as [C3|C3].
      { pose proof (rw_mapped_hi m' _ _ TM' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - T) ltac:(clear -C2 C3; lia)). replace (T + (lo + q - T)) with (lo + q) in M by (clear; lia). exact M. }
      destruct (Z.lt_ge_cases (lo + q) (T + 80)) as [C4|C4].
      { pose proof (rw_mapped_hi m' _ _ RF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (lo + q - (T + 32))) with (lo + q) in M by (clear; lia). exact M. }
      pose proof (rw_mapped_hi m' _ _ PF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
      specialize (M (lo + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (lo + q - (uspd + -80))) with (lo + q) in M by (clear; lia). exact M. }
    (* [comment removed for export] *)
    assert (RS : rstep (pa_owned A) (pa_owned A') lo uspd v m').
    { unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      - intros a Ha NO NO' NW. apply MU; [exact Ha|]. intros Fa.
        destruct (foot_owned A v [] c k (a_reg A) AR Wn SHP SHPW CVe (ev_ne_live A v [] c k n _ _ _ AR W L') R'E a Fa) as [X|[X|[X|X]]].
        + apply NW. subst Wn. cbv beta in X. clear -X LOW CEIL. lia.
        + exact (NO X).
        + clear -X. lia.
        + rewrite Z.sub_diag in X. clear -X. cbn in X. lia.
      - intros a Ha NI Hv. right. apply NN; [clear -Ha; lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| clear -Ha; lia| exact Hv].
      - exact SM'.
      - intros a Ha O'. left. exact (proj1 (su_owned A (a_reg A) cache' (BA (ba_idx b0) es' :: more) EXT a) O').
      - intros a Ha O NO'. exfalso. apply NO'. exact (proj2 (su_owned A (a_reg A) cache' (BA (ba_idx b0) es' :: more) EXT a) O). }
    assert (NZ : a_reg A c <> region_zero).
    { intros E. pose proof Gk as X. unfold carved_count, carved_count_ in X. rewrite E in X. cbn in X. clear -X. 
      pose proof (Z.div_0_l (class_size c)). rewrite Zdiv_0_l in X. lia. }
    pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A v md A' m' md' HIST (WFT_of_WFR A W) (WFT_of_WFR A' W') CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                  (fun c0 NE V0 => su_virgin A (a_reg A) cache' (BA (ba_idx b0) es' :: more) c c0 NZ (fun c' _ => eq_refl) CAO V0)
                  (wamd_sbm md md' Hsame HLT) RS) as HIST'.
    (* [comment removed for export] *)
    assert (CU' : CUR A' (munrestrict (hidc (pa_hull A)) m m') md' (Some (b0, S i)) more scr).
    { constructor; rewrite ?HULL, ?VIEW.
      - exact RI'.
      - exact HIST'.
      - exact MI'.
      - exact STK'.
      - exact PF'.
      - exact RF'.
      - exact DF'.
      - split; [exact LEN| pose proof (nth_error_Some_lt _ _ _ NTH) as IL; clear -IL; lia].
      - unfold A', recA'. cbn [a_qlimbo]. rewrite L' in QB. rewrite !q_bytes_cons, !batch_bytes_ebytes in QB |- *. cbn [ba_entries] in QB |- *. rewrite ebytes_cons in QB.
        pose proof (user_size_pos n ltac:(clear -Gnr; lia)) as (U1 & _). unfold qe_bytes in QB at 1. cbn [qe_n] in QB. clear -QB U1. lia. }
    destruct CASE as [[LT ->]|[EQ ->]].
    - specialize (KM A' (munrestrict (hidc (pa_hull A)) m m') md' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6''
                     ltac:(unfold cnt in LT; clear -LT; lia) CU' eq_refl).
      unfold it_cfgG in KM. rewrite Nat2Z.inj_succ in KM. exact KM.
    - specialize (KD A' (munrestrict (hidc (pa_hull A)) m m') md' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6''
                     ltac:(unfold cnt in EQ; clear -EQ; lia) CU' eq_refl).
      unfold it_cfgG in KD. rewrite Nat2Z.inj_succ in KD. exact KD.
  Qed.

  (* [comment removed for export] *)
  #[using="VB SPA HI47 SPHI LOW CEIL"] Lemma step_prim_drainfast : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (c k n : Z),
    CUR A m md (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChP (CP c k)) n) ->
    Z.of_nat (length (pk_chunks (a_cache A c))) = max_count c ->
    4 * (Z.of_nat (length (rg_free (a_reg A c))) + max_count c / 2) <= rg_mapped_fa (a_reg A c) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        (S i < length (ba_entries b0))%nat -> CUR A' m' md' (Some (b0, S i)) more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (it_cfg A' m' md' b0 (Z.of_nat (S i)) dorec_callblk (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'') TS) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        (S i = length (ba_entries b0))%nat -> CUR A' m' md' (Some (b0, S i)) more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (it_cfg A' m' md' b0 (Z.of_nat (S i)) dorec_batchblk (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'') TS) ->
    srealizes rsegs (it_cfg A m md b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Proof.
    intros A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CU NTH FULL ROOMF KM KD.
    destruct CU as [RI HIST MI ST PF RF DF [LEN ILE] QB]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC) : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    assert (L' : a_qlimbo A = BA (ba_idx b0) (QE (ChP (CP c k)) n :: skipn (S i) (ba_entries b0)) :: more).
    { rewrite L. unfold limbo_of. rewrite (skipn_cons_nth (ba_entries b0) i _ NTH). reflexivity. }
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (* [comment removed for export] *)
    (first [ pose proof ((rk_ri A v [] AR)) as dR_18; dand10 dR_18 as RI0 RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v [] AR) as (RI0 & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    (first [ pose proof ((rk_sep A v [] AR)) as dR_19; dand6 dR_19 as SP1 SP2 SP3 SP4 SP5 SP6 | pose proof (rk_sep A v [] AR) as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6) ]).
    (first [ pose proof ((rk_place A v [] AR)) as dR_20; dand6 dR_20 as PT PTC PTM PC PCC _ | pose proof (rk_place A v [] AR) as (PT & PTC & PTM & PC & PCC & _) ]).
    pose proof (rk_TC A v [] AR) as TC. pose proof (rk_PCo A v [] AR) as PCo. pose proof (rk_SBc A v [] AR) as CSB. pose proof (rk_CRI A v [] AR) as CRI.
    pose proof (wrI A W) as CI.
    (first [ pose proof ((rk_stats A v [] AR)) as dR_21; dex3 dR_21 as statv rf rfd; dand4 dR_21 as RFR RFDR STA TRF | pose proof ((rk_stats A v [] AR)) as dR_21; dand7 dR_21 as statv rf rfd RFR RFDR STA TRF | destruct (rk_stats A v [] AR) as (statv & rf & rfd & RFR & RFDR & STA & TRF) ]).
    pose proof (ev_wf A v [] c k n _ _ _ AR W L') as WE. pose proof (ev_carved A v [] c k n _ _ _ AR W L') as CVe.
    (first [ pose proof ((rk_line A v [] AR CI c ltac:(exact (proj1 CVe)))) as dR_22; dex1 dR_22 as ks; dand7 dR_22 as LKS KSM KSF KLE KRG KND LINE | pose proof ((rk_line A v [] AR CI c ltac:(exact (proj1 CVe)))) as dR_22; dand8 dR_22 as ks LKS KSM KSF KLE KRG KND LINE | destruct (rk_line A v [] AR CI c ltac:(exact (proj1 CVe))) as (ks & LKS & KSM & KSF & KLE & KRG & KND & LINE) ]).
    pose proof (ek_geo A v [] c k n AR WE) as G.
    destruct RC as [RAR RTMP RCH RME RMO RCUR]. cbn [rc_cur] in RCUR. (first [ dand3 RCUR as RENT RBAT RBSH | destruct RCUR as (RENT & RBAT & RBSH) ]).
    pose proof (RENT i _ (Nat.le_refl i) NTH) as LE.
    (first [ pose proof ((ek_cells A v [] c k n AR WE LE)) as dR_24; dex2 dR_24 as b1 ctxw; dand10 dR_24 as B1R HDR CTXW MAG SHC SHQ QL SHA R88 MP | pose proof ((ek_cells A v [] c k n AR WE LE)) as dR_24; dand12 dR_24 as b1 ctxw B1R HDR CTXW MAG SHC SHQ QL SHA R88 MP | destruct (ek_cells A v [] c k n AR WE LE) as (b1 & ctxw & B1R & HDR & CTXW & MAG & SHC & SHQ & QL & SHA & R88 & MP) ]).
    pose proof (ek_slot v (a_sb A) (batch_addr (a_sb A) b0) (ba_entries b0) i (batch_bytes b0) i _ RBAT (Nat.le_refl i) NTH LEN) as SLOT. cbn [qe_chunk qe_n] in SLOT.
    pose proof (batch_known A v [] AR (BA (ba_idx b0) (QE (ChP (CP c k)) n :: skipn (S i) (ba_entries b0))) (head_in A _ _ more W L')) as [KBR _]. cbn [ba_idx] in KBR.
    pose proof (rk_batch A v [] AR (ba_idx b0) KBR) as BG. cbv zeta in BG. (first [ dand9 BG as BFORM BLO BHI BAL KB0 KBH SEP_bt SEP_bc SEP_br | destruct BG as (BFORM & BLO & BHI & BAL & KB0 & KBH & SEP_bt & SEP_bc & SEP_br) ]).
    (first [ pose proof ((rk_region_facts A v [] AR c (proj1 CVe))) as dR_26; dand7 dR_26 as RGF1 RGF2 RGF3 RGF4 RGF5 RGF6 RGF7 | destruct (rk_region_facts A v [] AR c (proj1 CVe)) as (RGF1 & RGF2 & RGF3 & RGF4 & RGF5 & RGF6 & RGF7) ]).
    (first [ pose proof ((max_count_range c (proj1 CVe))) as dR_27; dand3 dR_27 as MCR0 MCE RFR0 | pose proof (max_count_range c (proj1 CVe)) as (MCR0 & MCE & RFR0) ]). set (h := refill_count c) in *.
    assert (HSH : Z.shiftr (max_count c) 1 = h) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; clear -MCE; rewrite MCE; rewrite Z.mul_comm, Z_div_mult by lia; reflexivity).
    (first [ pose proof ((rk_region A v [] AR c (Z.to_nat h) (proj1 CVe) ltac:(rewrite Z2Nat.id by lia; clear -ROOMF MCE; rewrite MCE in ROOMF; replace (2 * h / 2) with h in ROOMF by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity); exact ROOMF))) as dR_28; dex4 dR_28 as na nfs v88 junk; dand8 dR_28 as RMX RNF RMFA RMU RNA RNFS LJ RARR | pose proof ((rk_region A v [] AR c (Z.to_nat h) (proj1 CVe) ltac:(rewrite Z2Nat.id by lia; clear -ROOMF MCE; rewrite MCE in ROOMF; replace (2 * h / 2) with h in ROOMF by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity); exact ROOMF))) as dR_28; dand12 dR_28 as na nfs v88 junk RMX RNF RMFA RMU RNA RNFS LJ RARR | destruct (rk_region A v [] AR c (Z.to_nat h) (proj1 CVe) ltac:(rewrite Z2Nat.id by lia; clear -ROOMF MCE; rewrite MCE in ROOMF; replace (2 * h / 2) with h in ROOMF by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity); exact ROOMF)) as (na & nfs & v88 & junk & RMX & RNF & RMFA & RMU & RNA & RNFS & LJ & RARR) ]).
    pose proof (rk_CITV A v [] AR) as CITV.
    (first [ pose proof ((wtR A (proj1 AR))) as dR_29; dand3 dR_29 as WR1 _ _ | destruct (wtR A (proj1 AR)) as (WR1 & _ & _) ]). (first [ pose proof ((WR1 c (proj1 CVe))) as dR_30; dand12 dR_30 as _ _ _ _ _ _ _ _ _ _ _ CAP | destruct (WR1 c (proj1 CVe)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CAP) ]). cbv zeta in CAP. pose proof (wfr_fa_cap A W c (proj1 CVe)) as [CAPN _].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (head_in A _ _ more W L') as HIN.
    assert (NEhb : ChP (CP kQuarantineBatchClass (ba_idx b0)) <> ChP (CP c k)).
    { intros E. exact (quar_not_batch A v [] AR _ _ (ev_in A c k n _ _ _ W L') HIN (eq_sym E)). }
    pose proof (carved_disjoint A v [] AR _ _ (batch_carved A v [] AR _ HIN) CVe NEhb) as Dbp. cbn [chunk_lo chunk_hi alloc_beg ba_idx] in Dbp.
    (first [ dand25 G as Gcr Gcc Gnr Gk Grz Grzm Gu1 Gu2 Gu3 Gfit Gcsr Gcm Gpe Gka Gam Gmk Gplo Gphi Gpm Gsbm Guo Gho Gab Gclo Gchi | destruct G as (Gcr & Gcc & Gnr & Gk & Grz & Grzm & Gu1 & Gu2 & Gu3 & Gfit & Gcsr & Gcm & Gpe & Gka & Gam & Gmk & Gplo & Gphi & Gpm & Gsbm & Guo & Gho & Gab & Gclo & Gchi) ]).
    pose proof TC as TC'. (first [ dand13 TC' as _ _ _ _ _ Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct TC' as (_ & _ & _ & _ & _ & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    pose proof MCR0 as MCR. pose proof (class_size_mod32 c Gcr) as CS32.
    set (thr := p_thr (a_pl A)) in *. set (sb := a_sb A) in *. set (ri := a_ri A) in *.
    set (b := batch_addr sb b0) in *. set (cnt := Z.of_nat (length (ba_entries b0))) in *.
    set (pp := chunk_addr sb c k) in *. set (mh := pp + rz_size n - 16) in *. set (fac_ := free_array_of sb c) in *.
    set (cntc := Z.of_nat (length (pk_chunks (a_cache A c)))) in *.
    set (kk := k * class_size c / kCompactPtrScale).
    set (nf := Z.of_nat (length (rg_free (a_reg A c)))) in *. set (mfa := rg_mapped_fa (a_reg A c)) in *. set (Ra := ri + 128 * c) in *.
    set (Q := fun ms' : machine_state => exists (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 statv' : word) (m' : mem) (pc : Z),
           ms' = MS (it_regs (wz dsp) gp (cl_tp LPA) T b cnt s10 s11 (wz dorec_retpc) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 (Z.of_nat i + 1)) F (wz pc) fc None m' (seg_rom rsegs) /\
           ((Z.of_nat i + 1 < cnt /\ pc = dorec_callblk) \/ (Z.of_nat i + 1 = cnt /\ pc = dorec_batchblk)) /\
           rw_cells rsegs m' dsp (dorec_fr thr scr) /\
           (rz_size n - 16 = 0 \/ rw_cells rsegs m' pp [C8 (wz 0)]) /\
           rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi (user_size n))); C4 (wz (user_size n))] /\
           bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (round_up (user_size n) 8 / 8))) /\
           rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + user_size n))] /\
           rw_cells rsegs m' (thr + 208 + 80 * c) [C4 (wz (max_count c - h + 1)); C4 (wz (max_count c)); C8 (wz (class_size c)); CB 64 (u32s (upd ks (Z.to_nat (max_count c - h)) (wz kk)))] /\
           rw_cells rsegs m' (thr + 208 + 2576) [C8 statv'] /\
           rw_cells rsegs m' Ra [C8 (wz 0)] /\ rw_cells rsegs m' (Ra + 16) [C8 (wz (nf + h))] /\ rw_cells rsegs m' (Ra + 24) [C8 (wz mfa)] /\
           rw_cells rsegs m' (Ra + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] /\
           u32arr rsegs m' (fac_ + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (max_count c - h)) ks)) /\
           munch [(dsp - 320, dsp); (pp, pp + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + round_up (user_size n) 8 / 8);
                  (thr + 2840, thr + 2856); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584);
                  (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 80, Ra + 88); (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h)] v m' /\
           wmono rsegs v m' /\ mem_inv rsegs m' /\ stk rsegs m' lo dsp).
    unfold it_cfgG. fold sb. fold b cnt.
    eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR A) pa_wxR _ (pa_eager A) Q _ md TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (iter_prim_drainfast gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b cnt (Z.of_nat i) scr
                (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                pa_tsd (p_ctx (a_pl A)) thr sb ri)
        with (kb := 512 * ba_idx b0) (c := c) (idx := k) (d := rz_size n - 16) (mu := rg_mapped_user (a_reg A c)) (n := user_size n) (b1 := b1)
             (rf := rf) (rfd := rfd) (maxc := max_count c) (k := kk) (old := fd8 ((user_size n + 7) / 8)) (ks := ks) (statv := statv)
             (pw := wz (hdr_of sb (ChP (CP c k)) n)) (mh := mh) (nf := nf) (mfa := mfa) (junk := junk) (nfs := nfs) (v88 := v88).
      all: rewrite ?HSH.
      all: try assumption.
      all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
      all: try assumption.
      all: cycle -2. 3: cycle 0.
      1: { intros LT a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' DF' SL' MU' MG' HD' SH' TF' LN' ST' RX' RNF' RMFA' RNFS' ARR' MUN WM' MI' STK'.
           apply evt_done. subst Q. first [ hotw_ex18 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' dorec_callblk | exists a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', statv', m', dorec_callblk ].
           split; [reflexivity|]. split; [left; split; [exact LT| reflexivity]|].
           repeat (split; [assumption|]). exact STK'. }
      1: { intros EQ a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' DF' SL' MU' MG' HD' SH' TF' LN' ST' RX' RNF' RMFA' RNFS' ARR' MUN WM' MI' STK'.
           apply evt_done. subst Q. first [ hotw_ex18 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' dorec_batchblk | exists a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', statv', m', dorec_batchblk ].
           split; [reflexivity|]. split; [right; split; [exact EQ| reflexivity]|].
           repeat (split; [assumption|]). exact STK'. }
      all: first [ assumption | reflexivity
                 | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                 | unfold pa_tsd; clear; lia
                 | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                 | unfold cnt; clear -LEN; unfold kQuarantineBatchCount in LEN; lia
                 | clear -SBRI RHI; lia
                 | clear -KB0 KBH; lia
                 | pose proof (nth_error_Some_lt _ _ _ NTH) as IL; unfold cnt; clear -IL; lia
                 | unfold mh, pp in *; rewrite Gho; rewrite unsigned_lit; [reflexivity| clear -Gplo Gphi Grz Gfit Gu1 CE; kung_all; pose proof (round_up_ge (user_size n) 8 ltac:(lia)); lia]
                 | unfold mh, pp in *; clear -Gpe; lia
                 | pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU; clear -RU Grz Gfit Gu1; lia
                 | clear -Grzm; lia
                 | clear -Gk; lia
                 | clear -Gka Gam; lia
                 | clear -Gmk Gam Gka Gk Gcsr; kung_all; nia
                 | unfold kk; unfold kCompactPtrScale; clear -Gcm Gk; nia
                 | clear -Gu1 Gu3 Gnr; unfold kMaxPrimaryUser in *; lia
                 | unfold mh, pp in *; clear -Gfit Gphi CE; lia
                 | unfold cntc; clear -ROOM; lia
                 | clear -MCR; lia
                 | clear -MCE RFR0; unfold h; lia
                 | rewrite LJ; clear; rewrite Z2Nat.id by lia || idtac; lia
                 | unfold nf; clear; lia
                 | clear -RGF5 CAPN RFR0; unfold nf, mfa, h in *; kung_all; lia
                 | clear -ROOMF MCE RFR0; unfold nf, mfa, h in *; lia
                 | rewrite <- FULL at 1; exact LINE
                 | clear -RGF3; unfold mfa; kung_all; lia
                 | clear -Gmk; kung_all; lia
                 | match goal with |- ?g => idtac "UNSOLVED:" g end ]. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex18 HQ as a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' pc; dand18 HQ as -> CASE DF' MG' HD' SH' TF' LN' ST' RX' RNF' RMFA' RNFS' ARR' MUN WM' MI' STK' | dand36 HQ as a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' pc -> CASE DF' MG' HD' SH' TF' LN' ST' RX' RNF' RMFA' RNFS' ARR' MUN WM' MI' STK' | destruct HQ as (a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t0'' & t1'' & t2'' & t3'' & t4'' & t5'' & t6'' & statv' & m' & pc & -> & CASE & DF' & MG' & HD' & SH' & TF' & LN' & ST' & RX' & RNF' & RMFA' & RNFS' & ARR' & MUN & WM' & MI' & STK') ]).
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m m') = m').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NNR _ _ a WM'); [exact H1| lia]. }
    (* [comment removed for export] *)
    set (es' := skipn (S i) (ba_entries b0)) in *.
    set (hN := Z.to_nat h) in *.
    set (out := drain_out (pk_chunks (a_cache A c)) hN).
    set (cache' := recp_cache (a_cache A) c k).
    set (reg' := recp_reg (a_reg A) (a_cache A) c k mfa).
    set (A' := recA' A reg' cache' (BA (ba_idx b0) es' :: more)).
    assert (RGC : reg' c = reg_return (a_reg A c) out mfa).
    { unfold reg', recp_reg, reg_set, cache_push_list. fold cntc. rewrite FULL, Z.eqb_refl, Z.eqb_refl. cbn [snd].
      replace (max_count c / 2) with h by (clear -MCE RFR0; unfold h in *; lia). reflexivity. }
    assert (RGO : forall c', c' <> c -> reg' c' = a_reg A c').
    { intros c' NE. unfold reg', recp_reg, reg_set. fold cntc. rewrite FULL, Z.eqb_refl. destruct (Z.eqb_spec c' c); [exfalso; exact (NE e)| reflexivity]. }
    assert (CAE : pk_chunks (cache' c) = drain_keep (pk_chunks (a_cache A c)) hN ++ [k]).
    { unfold cache', recp_cache, cache_set, cache_push_list. rewrite Z.eqb_refl. fold cntc. rewrite FULL, Z.eqb_refl. cbn [fst pk_chunks].
      replace (max_count c / 2) with h by (clear -MCE RFR0; unfold h in *; lia). reflexivity. }
    assert (CAO : forall c', c' <> c -> cache' c' = a_cache A c').
    { intros c' NE. unfold cache', recp_cache, cache_set. destruct (Z.eqb_spec c' c); [exfalso; exact (NE e)| reflexivity]. }
    assert (EXT : same_ext (a_reg A) reg').
    { intros c0. destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite RGC, reg_return_mapped_user, reg_return_mapped_fa; split; reflexivity| rewrite (RGO c0 NE); split; reflexivity]. }
    pose proof (su_hull A reg' cache' (BA (ba_idx b0) es' :: more) EXT) as HULL. pose proof (su_lhull A reg' cache' (BA (ba_idx b0) es' :: more) EXT) as LHULL.   (* [comment removed for export] *)
    pose proof (su_eager A reg' cache' (BA (ba_idx b0) es' :: more) EXT) as EAGER.
    change (mkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with A' in HULL, LHULL, EAGER.
    assert (HLEN : (hN <= length (pk_chunks (a_cache A c)))%nat) by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
    assert (OUTL : length out = hN) by (unfold out; apply drain_out_length; exact HLEN).
    (* [comment removed for export] *)
    set (Wn := fun a => dsp - 320 <= a < dsp).
    set (SHP := fun a => sh (pp + rz_size n) <= a < sh (pp + rz_size n) + (user_size n + 7) / 8).
    pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU.
    assert (MU : forall a, 0 <= a < 2^64 -> ~ rp_foot A c k reg' Wn SHP a -> m' (wz a) = v (wz a)).
    { intros a Ha NF. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha; lia). unfold rp_foot in NF. rewrite RGC, reg_return_mapped_fa in NF. subst Wn SHP. cbv beta in NF.
      cbn [outside]. unfold pp, mh, sb, thr, cntc, Ra, ri, fac_, nf, mfa in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NF.
      - left. exact X.
      - right; left. clear -X Gcsr. lia.
      - right; left. clear -X Grz Gfit RU Gu1. lia.
      - right; right; left. unfold pp in X. replace (chunk_addr (a_sb A) c k + rz_size n - 16 + 16) with (chunk_addr (a_sb A) c k + rz_size n) in X by lia. rewrite ?R88 in X. exact X.
      - do 4 right; left. clear -X. lia.
      - do 3 right; left. exact X.
      - do 4 right; left. clear -X. lia.
      - do 5 right; left. unfold Ra, ri in X. exact X.
      - do 6 right; left. unfold Ra, ri in X. clear -X. lia.
      - do 6 right; left. unfold Ra, ri in X. clear -X. lia.
      - do 7 right; left. unfold fac_, nf, sb, mfa, h in *. clear -X ROOMF MCE RFR0. lia. }
    (* [comment removed for export] *)
    assert (W' : WFR A').
    { pose proof (WFR_prim A _ c k n mfa _ more W L') as X. apply X. intros _. unfold nf, mfa, h in *. clear -ROOMF RGF3 RGF4 CAP Gam Gka Gk Gcsr.
      split; [exact ROOMF|]. split; [lia|]. split; [lia|]. split; [exact RGF4|]. split; [exact CAP|]. intros MU0. nia. }
    assert (WNH : forall a, Wn a -> alloc_ceiling <= a) by (subst Wn; cbv beta; intros a Ha; clear -Ha CEIL LOW; lia).
    pose proof (round_up_mod (user_size n) 8 ltac:(lia)) as RUM.
    assert (SHPW : forall a, SHP a -> sh pp <= a < sh pp + class_size c / 8).
    { subst SHP; cbv beta; intros a Ha. rewrite SHA in Ha. clear -Ha Gfit Grz Grzm CS32 RUM RU Gu1 R88. lia. }
    (* [comment removed for export] *)
    assert (DISJ : forall a l, 0 < l ->
             (Ra + 32 <= a /\ a + l <= Ra + 80) \/ (Ra + 96 <= a /\ a + l <= Ra + 128) \/ (fac_ <= a /\ a + l <= fac_ + 4 * nf) \/ (T <= a /\ a + l <= uspd) ->
             disjoint_from [(dsp - 320, dsp); (pp, pp + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + round_up (user_size n) 8 / 8);
                            (thr + 2840, thr + 2856); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584);
                            (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 80, Ra + 88); (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h)] a l).
    { intros a l Hl Ha. unfold pp, mh, thr, ri, sb, fac_, Ra, nf, mfa in *. cbn [disjoint_from].
      (first [ pose proof ((rk_region_facts A v [] AR c (proj1 CVe))) as dR_34; dand6 dR_34 as _ _ RG3 _ RG5 _ | pose proof (rk_region_facts A v [] AR c (proj1 CVe)) as (_ & _ & RG3 & _ & RG5 & _) ]).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
      all: first [ clear -Ha Hl Gcr SBRI RLO RHI CEIL LOW CE SPR; kung_all; lia
                 | clear -Ha Hl SP1 Gcr; unfold apart in SP1; lia
                 | clear -Ha Hl SP4 Gcr RG3 SBRI; unfold apart, free_array_of in *; kung_all; lia
                 | clear -Ha Hl Gpe Gka Gam Gmk Gcr SBRI Gcsr Gk Grz Gfit RU Gu1 RG3; unfold free_array_of in *; kung_all; lia
                 | clear -Ha Hl Gplo Gphi Grz Gfit RU Gu1 CE SBRI SBLO Gpe Gcr Gk Gcsr RG3 CEIL LOW; unfold sh, free_array_of in *; kung_all; lia
                 | clear -Ha Hl PTC CEIL LOW Gcr; lia
                 | clear -Ha Hl Gcr SBRI RHI RG3 CEIL LOW; unfold free_array_of in *; kung_all; lia
                 | clear -Ha Hl RFR0; unfold h; lia
                 | clear -Ha Hl Gcr SBRI RHI RG3 RG5 ROOMF MCE RFR0 CEIL LOW SBLO; unfold h, free_array_of in *; kung_all; lia
                 | clear -Ha Hl SP1 SP4 Gcr RG3 RG5 ROOMF MCE RFR0 SBRI; unfold apart, h, free_array_of in *; kung_all; lia ]. }
    assert (OUT : forall a, (Ra + 32 <= a < Ra + 80 \/ Ra + 96 <= a < Ra + 128 \/ fac_ <= a < fac_ + 4 * nf \/ T <= a < uspd) ->
             outside [(dsp - 320, dsp); (pp, pp + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + round_up (user_size n) 8 / 8);
                      (thr + 2840, thr + 2856); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584);
                      (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 80, Ra + 88); (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h)] a).
    { intros a Ha. apply (disjoint_outside _ a 1); [| clear; lia]. apply DISJ; [clear; lia|]. clear -Ha. lia. }
    assert (P_mx : u64_at rsegs m' (ri + 128 * c) 0) by (apply u64_of_rw; [clear; lia| exact RX']).
    (* [comment removed for export] *)
    assert (KSE : firstn (length (pk_chunks (a_cache A c))) ks = map (fun k0 => wz (k0 * class_size c / kCompactPtrScale)) (pk_chunks (a_cache A c))) by exact KSF.
    assert (OUTW : firstn (Z.to_nat h) (skipn (Z.to_nat (max_count c - h)) ks) = map (fun k0 => wz (k0 * class_size c / kCompactPtrScale)) out).
    { unfold out, drain_out. fold hN. replace (Z.to_nat (max_count c - h)) with (length (pk_chunks (a_cache A c)) - hN)%nat by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
      rewrite firstn_skipn_comm. replace (length (pk_chunks (a_cache A c)) - hN + hN)%nat with (length (pk_chunks (a_cache A c))) by (clear -HLEN; lia).
      rewrite KSE, skipn_map. reflexivity. }
    assert (P_regc : region_repr_ LPA sb (reg' c) m' c).
    { rewrite RGC. pose proof (ar_regions _ _ _ _ _ (proj2 AR) c Gcr) as RR0. change (a_sb A) with sb in RR0.
      (first [ pose proof ((rk_region_facts A v [] AR c Gcr)) as dR_35; dand6 dR_35 as _ _ RG3 _ RG5 _ | pose proof (rk_region_facts A v [] AR c Gcr) as (_ & _ & RG3 & _ & RG5 & _) ]).
      apply (region_return_of_cells v m' sb (a_reg A c) c out (wz (bv_unsigned nfs + h)) v88 Gcr RR0).
      - rewrite OUTL. unfold hN, nf in *. clear -RG3 RG5 CAPN RFR0. kung_all. lia.
      - clear -RG3. kung_all. lia.
      - intros a Ha. rewrite RIA in Ha. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RLO RHI CE; kung_all; lia). apply OUT. left. unfold Ra. clear -Ha. lia.
      - intros a Ha. rewrite RIA in Ha. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RLO RHI CE; kung_all; lia). apply OUT. right; left. unfold Ra. clear -Ha. lia.
      - intros a Ha. rewrite FAE in Ha. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RG3 RG5 SBLO SBRI RHI CE; unfold free_array_of in *; kung_all; lia). apply OUT. right; right; left. unfold fac_, nf. clear -Ha. lia.
      - intros a Ha Hv. rewrite FAE in Ha. apply NN; [| right| | exact Hv]; clear -Ha Gcr RG3 SBLO SBRI RHI CE; unfold free_array_of in *; kung_all; lia.
      - intros a Ha Hv. rewrite RBE in Ha. apply NN; [| right| | exact Hv]; clear -Ha Gcr Gmk SBLO SBRI RHI CE; kung_all; lia.
      - rewrite RIA, OUTL. unfold hN. rewrite Z2Nat.id by (clear -RFR0; unfold h; lia). fold nf. unfold Ra, ri in RNF'. exact RNF'.
      - rewrite RIA. unfold Ra, ri, mfa in RMFA'. exact RMFA'.
      - rewrite RIA. unfold Ra, ri in RNFS'. exact RNFS'.
      - rewrite FAE, <- OUTW. fold nf. unfold fac_, sb in ARR'. exact ARR'. }
    (* [comment removed for export] *)
    assert (ENC : forall k', In k' (pk_chunks (a_cache A c)) \/ k' = k -> 0 <= k' * class_size c / kCompactPtrScale < 2^32).
    { intros k' Hk'. assert (KR' : 0 <= k' < carved_count A c) by (destruct Hk' as [Hk'| ->]; [exact (KRG k' Hk')| exact Gk]).
      unfold kCompactPtrScale. clear -KR' RGF6 Gam Gmk Gcsr. split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. kung_all. nia. }
    assert (ENT : forall i0 k', nth_error (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]) i0 = Some k' ->
              nth_error (upd ks (Z.to_nat (max_count c - h)) (wz kk)) i0 = Some (wz (k' * class_size c / kCompactPtrScale)) /\ 0 <= k' * class_size c / kCompactPtrScale < 2^32).
    { assert (KL : length (drain_keep (pk_chunks (a_cache A c)) hN) = (length (pk_chunks (a_cache A c)) - hN)%nat) by (apply drain_keep_length; exact HLEN).
      assert (MH : Z.to_nat (max_count c - h) = (length (pk_chunks (a_cache A c)) - hN)%nat) by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
      intros i0 k' Hk'. destruct (Nat.lt_ge_cases i0 (length (pk_chunks (a_cache A c)) - hN)) as [LT|GE].
      - rewrite nth_error_app1 in Hk' by (rewrite KL; exact LT). unfold drain_keep in Hk'. rewrite nth_error_firstn in Hk'.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A c)) - hN)); [| exfalso; clear -LT H; lia].
        split; [| apply ENC; left; eapply nth_error_In; exact Hk'].
        rewrite nth_error_upd_other by (rewrite MH; clear -LT; lia).
        pose proof (f_equal (fun l => nth_error l i0) KSF) as E. cbv beta in E. rewrite nth_error_firstn in E.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A c)))); [| exfalso; clear -LT H0; lia]. rewrite E, nth_error_map, Hk'. reflexivity.
      - rewrite nth_error_app2 in Hk' by (rewrite KL; exact GE). rewrite KL in Hk'. destruct (i0 - (length (pk_chunks (a_cache A c)) - hN))%nat as [|x] eqn:EQ; cbn in Hk'; [injection Hk' as <-| destruct x; discriminate].
        assert (i0 = (length (pk_chunks (a_cache A c)) - hN)%nat) by (clear -GE EQ; lia). subst i0. split; [| apply ENC; right; reflexivity].
        rewrite MH. rewrite nth_error_upd_same by (rewrite LKS; unfold hN, cntc in *; clear -FULL MCR RFR0; lia). reflexivity. }
    pose proof LN' as LNx.
    replace (max_count c - h + 1) with (Z.of_nat (length (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]))) in LNx
      by (rewrite length_app, (drain_keep_length _ _ HLEN); cbn [length]; unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
    pose proof (line_of_cells m' (thr + 208 + 80 * c) c (upd ks (Z.to_nat (max_count c - h)) (wz kk)) (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]) (a_cache_inited A) Gcr CI
                  ltac:(rewrite upd_length; exact LKS) ltac:(rewrite length_app, (drain_keep_length _ _ HLEN); cbn [length]; unfold hN, cntc in *; clear -FULL MCE RFR0 MCR; lia) ENT
                  LNx) as P_linec.
    rewrite <- CAE in P_linec.
    replace (thr + 208 + 80 * c) with (thr + off_th_per_class c) in P_linec by (unfold off_th_per_class, off_th_alloc_cache, kPerClassSize; clear; lia).
    assert (MFA8 : rg_mapped_fa (a_reg A c) mod 8 = 0) by (apply (mod0_down _ kFreeArrayMapSize 8); [exists (2^15); reflexivity| exact RGF4]).
    assert (R'E : rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_allocated_user (reg' c) = rg_allocated_user (a_reg A c) /\
                  rg_mapped_fa (a_reg A c) <= rg_mapped_fa (reg' c) /\ rg_mapped_fa (reg' c) <= kFreeArraySize /\ rg_mapped_fa (reg' c) mod 8 = 0).
    { rewrite RGC, reg_return_mapped_user, reg_return_allocated, reg_return_mapped_fa. unfold mfa. clear -RGF3 MFA8. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; try lia. }
    assert (VSH : bytes_at rsegs m' (sh pp) (pshadow_free c)).
    { apply (vsh_entry A v m' [] c k reg' AR Wn WNH SHP CVe R'E MU n WE LE).
      - intros a. subst SHP. cbv beta. unfold pp, sb. split; intros X; exact X.
      - replace (chunk_addr (a_sb A) c k + rz_size n) with (mh + 16) by (unfold mh, pp, sb; clear; lia). exact SH'. }
    assert (P_fash : bytes_at rsegs m' (sh (fac_ + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_fa (reg' c) - mfa) / 8)))).
    { rewrite RGC, reg_return_mapped_fa. rewrite Z.sub_diag. cbn. apply bytes_at_nil. unfold sh, fac_, mfa, free_array_of. clear -Gcr SBLO SBRI RHI RGF3 CE. kung_all. lia. }
    pose proof (recp_arepr A v m' [] c k more reg' cache' AR W Wn WNH SHP SHPW CVe
                  (ev_ne_live A v [] c k n _ _ _ AR W L') (ev_ne_batch A v [] c k n _ _ _ AR W L') (ev_ne_rest A c k n _ _ _ W L')
                  CAO ltac:(intros k' Hk'; rewrite CAE in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|[<-|[]]]; [left; exact (proj2 (drain_in_iff _ hN k') (or_introl Hk'))| right; reflexivity])
                  RGO R'E ltac:(intros k' Hk'; rewrite RGC, reg_return_free in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|Hk']; [left; exact Hk'| right; exact (proj2 (drain_in_iff _ hN k') (or_intror Hk'))])
                  MU NN P_mx P_regc P_linec VSH P_fash (BA (ba_idx b0) es' :: more)) as AR'.
    change (recA' _ _ _ _) with A' in AR'.
    (* [comment removed for export] *)
    pose proof (ev_ne_batch A v [] c k n _ _ _ AR W L') as NEB. pose proof (ev_ne_limbo A c k n _ _ _ W L') as NEL.
    assert (INmore : forall b' e', In b' more -> In e' (ba_entries b') -> In e' (es' ++ q_entries more)).
    { intros b' e' Hb' He'. apply in_or_app. right. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He'). }
    assert (INhead : forall j e', (S i <= j)%nat -> nth_error (ba_entries b0) j = Some e' -> In e' (es' ++ q_entries more)).
    { intros j e' Hj He'. apply in_or_app. left. subst es'. apply (nth_error_In _ (j - S i)). rewrite nth_error_skipn. replace (S i + (j - S i))%nat with j by (clear -Hj; lia). exact He'. }
    assert (RC' : rcells A' m' T (Some (b0, S i)) more).
    { constructor.
      - exact AR'.
      - unfold tmp_hdr. eapply rw_cells_transport; [exact RTMP| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia.
      - apply (tmp_chain_xfer A v m' [] c k (ba_idx b0) _ more reg' cache' AR W L' Wn WNH SHP SHPW CVe NEB R'E MU more); [intros b' Hb'; exact Hb'| exact RCH].
      - intros b' e' Hb' He'. apply (lentry_xfer A v m' [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU NN e').
        + apply (limbo_in A (ba_idx b0) _ more W L'). cbn [app]. right. exact (INmore b' e' Hb' He').
        + apply NEL. exact (INmore b' e' Hb' He').
        + exact (RME b' e' Hb' He').
      - intros b' Hb'. destruct (RMO b' Hb') as [LB SHB]. pose proof (more_in A (ba_idx b0) _ more W L' b' Hb') as Hb2.
        destruct (lbatch_xfer A v m' [] c k reg' cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b') (ba_entries b') 0%nat (batch_bytes b')
                    (batch_carved A v [] AR b' Hb2) (NEB b' (or_intror Hb')) (proj2 (batch_known A v [] AR b' Hb2)) LB) as [LB' SHB'].
        split; [exact LB'| exact (SHB' SHB)].
      - split; [|split].
        + intros j e' Hj He'. apply (lentry_xfer A v m' [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU NN e').
          * apply (limbo_in A (ba_idx b0) _ more W L'). cbn [app]. right. exact (INhead j e' Hj He').
          * apply NEL. exact (INhead j e' Hj He').
          * exact (RENT j e' ltac:(clear -Hj; lia) He').
        + assert (LBi : lbatch_cells sb v (chunk_addr sb kQuarantineBatchClass (ba_idx b0)) (ba_entries b0) (S i) (batch_bytes b0)).
          { (first [ dand3 RBAT as X1 X2 X3 | destruct RBAT as (X1 & X2 & X3) ]). split; [| exact (conj X2 X3)]. intros i0 e' Hi0 He'. apply (X1 i0 e'); [clear -Hi0; lia| exact He']. }
          exact (proj1 (lbatch_xfer A v m' [] c k reg' cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b0) (ba_entries b0) (S i) (batch_bytes b0)
                           (batch_carved A v [] AR _ HIN) NEhb LEN LBi)).
        + exact (proj2 (lbatch_xfer A v m' [] c k reg' cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b0) (ba_entries b0) i (batch_bytes b0)
                           (batch_carved A v [] AR _ HIN) NEhb LEN RBAT) RBSH). }
    (* [comment removed for export] *)
    assert (RI' : RINV A' (munrestrict (hidc (pa_hull A)) m m') md' T (Some (b0, S i)) more).
    { constructor.
      - exact W'.
      - reflexivity.
      - rewrite HULL, VIEW. exact RC'.
      - apply (su_hidden A reg' cache' (BA (ba_idx b0) es' :: more) EXT m m' HID).
        + intros z Gz Hz Vz. destruct Gz as [SMz _]. unfold in_shadow_maps in SMz. apply NN; [clear -SMz; kung_all; lia| right; clear -SMz; kung_all; lia| clear -SMz; kung_all; lia| exact Vz].
        + intros z Gz Hz NHS. destruct Gz as [SMz _]. apply (AG_shadow_maps A v m' [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU z SMz).
          * intros SP. apply NHS. (first [ pose proof ((chunk_shadow A v [] AR c k Gcr Gk)) as dR_37; dand3 dR_37 as _ S2 _ | pose proof (chunk_shadow A v [] AR c k Gcr Gk) as (_ & S2 & _) ]). apply S2. exact (SHPW z SP).
          * rewrite RGC, reg_return_mapped_fa. unfold mfa. rewrite Z.sub_diag. clear. intros X. cbn in X. lia.
        + intros z Hz Hc Vz. apply NN; [clear -Hz; kung_all; lia| right; clear -Hz; kung_all; lia| clear -Hz; kung_all; lia| exact Vz].
      - exact EXTRA.
      - first [ exact (aledger_sbm _ _ _ _ md md' Hsame LED)
              | (* [comment removed for export] *)
                refine (aledger_reg _ _ _ _ _ _ (fun c0 _ => EXT c0) (aledger_sbm _ _ _ _ md md' Hsame LED)) ].
      - rewrite HULL, LHULL, EAGER. exact HI'.   (* [comment removed for export] *)
      - (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT' _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT' & _) ]). rewrite HLT'. exact HLT.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact COV.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact CEI. }
    (* [comment removed for export] *)
    assert (PF' : put_frame (p_thr (a_pl A)) m').
    { unfold put_frameG in *. eapply rw_cells_transport; [exact PF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
    assert (RF' : rec_frame (p_thr (a_pl A)) m').
    { unfold rec_frameG in *. eapply rw_cells_transport; [exact RF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
    assert (SM' : mapped m' lo (uspd - lo)).
    { intros q Hq. pose proof (rc_tmp _ _ _ _ _ RC') as TM'. unfold tmp_hdr in TM'.
      destruct (Z.lt_ge_cases (lo + q) dsp) as [C1|C1].
      { exact (stk_mapped_pa m' lo dsp lo (dsp - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
      destruct (Z.lt_ge_cases (lo + q) T) as [C2|C2].
      { pose proof (rw_mapped_hi m' _ _ DF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
        specialize (M (lo + q - dsp) ltac:(clear -C1 C2; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M. }
      destruct (Z.lt_ge_cases (lo + q) (T + 32)) as [C3|C3].
      { pose proof (rw_mapped_hi m' _ _ TM' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - T) ltac:(clear -C2 C3; lia)). replace (T + (lo + q - T)) with (lo + q) in M by (clear; lia). exact M. }
      destruct (Z.lt_ge_cases (lo + q) (T + 80)) as [C4|C4].
      { pose proof (rw_mapped_hi m' _ _ RF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (lo + q - (T + 32))) with (lo + q) in M by (clear; lia). exact M. }
      pose proof (rw_mapped_hi m' _ _ PF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
      specialize (M (lo + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (lo + q - (uspd + -80))) with (lo + q) in M by (clear; lia). exact M. }
    (* [comment removed for export] *)
    assert (RS : rstep (pa_owned A) (pa_owned A') lo uspd v m').
    { unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      - intros a Ha NO NO' NW. apply MU; [exact Ha|]. intros Fa.
        destruct (foot_owned A v [] c k reg' AR Wn SHP SHPW CVe (ev_ne_live A v [] c k n _ _ _ AR W L') R'E a Fa) as [X|[X|[X|X]]].
        + apply NW. subst Wn. cbv beta in X. clear -X LOW CEIL. lia.
        + exact (NO X).
        + rewrite RGC, reg_return_mapped_fa in X. unfold mfa in X. clear -X. lia.
        + rewrite RGC, reg_return_mapped_fa in X. unfold mfa in X. rewrite Z.sub_diag in X. clear -X. cbn in X. lia.
      - intros a Ha NI Hv. right. apply NN; [clear -Ha; lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| clear -Ha; lia| exact Hv].
      - exact SM'.
      - intros a Ha O'. left. exact (proj1 (su_owned A reg' cache' (BA (ba_idx b0) es' :: more) EXT a) O').
      - intros a Ha O NO'. exfalso. apply NO'. exact (proj2 (su_owned A reg' cache' (BA (ba_idx b0) es' :: more) EXT a) O). }
    assert (NZ : a_reg A c <> region_zero).
    { intros E. pose proof Gk as X. unfold carved_count, carved_count_ in X. rewrite E in X. cbn in X. clear -X. 
      pose proof (Z.div_0_l (class_size c)). rewrite Zdiv_0_l in X. lia. }
    pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A v md A' m' md' HIST (WFT_of_WFR A W) (WFT_of_WFR A' W') CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                  (fun c0 NE V0 => su_virgin A reg' cache' (BA (ba_idx b0) es' :: more) c c0 NZ RGO CAO V0)
                  (wamd_sbm md md' Hsame HLT) RS) as HIST'.
    (* [comment removed for export] *)
    assert (CU' : CUR A' (munrestrict (hidc (pa_hull A)) m m') md' (Some (b0, S i)) more scr).
    { constructor; rewrite ?HULL, ?VIEW.
      - exact RI'.
      - exact HIST'.
      - exact MI'.
      - exact STK'.
      - exact PF'.
      - exact RF'.
      - exact DF'.
      - split; [exact LEN| pose proof (nth_error_Some_lt _ _ _ NTH) as IL; clear -IL; lia].
      - unfold A', recA'. cbn [a_qlimbo]. rewrite L' in QB. rewrite !q_bytes_cons, !batch_bytes_ebytes in QB |- *. cbn [ba_entries] in QB |- *. rewrite ebytes_cons in QB.
        pose proof (user_size_pos n ltac:(clear -Gnr; lia)) as (U1 & _). unfold qe_bytes in QB at 1. cbn [qe_n] in QB. clear -QB U1. lia. }
    destruct CASE as [[LT ->]|[EQ ->]].
    - specialize (KM A' (munrestrict (hidc (pa_hull A)) m m') md' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6''
                     ltac:(unfold cnt in LT; clear -LT; lia) CU' eq_refl).
      unfold it_cfgG in KM. rewrite Nat2Z.inj_succ in KM. exact KM.
    - specialize (KD A' (munrestrict (hidc (pa_hull A)) m m') md' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6''
                     ltac:(unfold cnt in EQ; clear -EQ; lia) CU' eq_refl).
      unfold it_cfgG in KD. rewrite Nat2Z.inj_succ in KD. exact KD.
  Qed.
  (* [comment removed for export] *)
  #[using="VB SPA HI47 SPHI LOW CEIL"] Lemma step_pop : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (more : list batch) (scr : list byte)
      (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' : word),
    CUR A m md None (b0 :: more) scr ->
    (forall (m' : mem) (md' : Model) (a0'' a1'' : word), ba_entries b0 <> [] -> CUR A m' md' (Some (b0, 0%nat)) more scr ->
        srealizes rsegs (it_cfg A m' md' b0 0 dorec_callblk ra' a0'' a1'' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS) ->
    (forall (m' : mem) (md' : Model) (a0'' a1'' : word), ba_entries b0 = [] -> CUR A m' md' (Some (b0, 0%nat)) more scr ->
        srealizes rsegs (blk_cfg A m' md' b0 ra' a0'' a1'' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' (wz 0) s7' s8' s9') TS) ->
    srealizes rsegs (head_cfg A m md (b0 :: more) ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9') TS.
  Proof.
    intros A m md b0 more scr ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' CU K1 K0.
    destruct b0 as [kb es0].
    destruct CU as [RI HIST MI ST PF RF DF _ QB]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC) : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    cbn [limbo_of] in L.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (* [comment removed for export] *)
    (first [ pose proof ((rk_ri A v [] AR)) as dR_39; dand10 dR_39 as RI0 RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v [] AR) as (RI0 & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    pose proof (rk_TC A v [] AR) as TC. pose proof (wrI A W) as CI.
    destruct RC as [RAR RTMP RCH RME RMO _].
    pose proof (head_in A _ _ more W L) as HIN.
    pose proof (batch_known A v [] AR (BA kb es0) HIN) as [KBR LEN]. cbn [ba_entries] in LEN.
    pose proof (rk_batch A v [] AR kb KBR) as BG. cbv zeta in BG. (first [ dand9 BG as BFORM BLO BHI BAL KB0 KBH SEP_bt SEP_bc SEP_br | destruct BG as (BFORM & BLO & BHI & BAL & KB0 & KBH & SEP_bt & SEP_bc & SEP_br) ]).
    pose proof TC as TC'. (first [ dand13 TC' as _ _ _ _ _ Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct TC' as (_ & _ & _ & _ & _ & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    set (thr := p_thr (a_pl A)) in *. set (sb := a_sb A) in *. set (ri := a_ri A) in *.
    set (b := batch_addr sb (BA kb es0)) in *. set (cnt := Z.of_nat (length es0)) in *.
    (* [comment removed for export] *)
    pose proof RTMP as TH. unfold tmp_hdr in TH. cbn [length] in TH. fold b in TH.
    pose proof RCH as CH. cbn [tmp_chain] in CH. destruct CH as [BC CHm]. fold sb b cnt in BC.
    set (tn := Z.of_nat (S (length more))) in *.
    set (nx := match more with [] => 0 | b' :: _ => batch_addr sb b' end) in *.
    set (tl := batch_addr sb (last (BA kb es0 :: more) (BA 0 []))) in *.
    set (ts := q_bytes (BA kb es0 :: more)) in *.
    assert (TNR : 1 <= tn < 2^64).
    { pose proof (limbo_count_bound A W) as X. rewrite L in X. cbn [length] in X.
      (first [ pose proof ((rk_region_facts A v [] AR kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia))) as dR_42; dand7 dR_42 as RG1 RG2 _ _ _ RG6 _ | pose proof (rk_region_facts A v [] AR kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (RG1 & RG2 & _ & _ & _ & RG6 & _) ]).
      change (class_size kQuarantineBatchClass) with 8192 in RG6. unfold tn. clear -X RG1 RG2 RG6. kung_all. lia. }
    assert (NXR : 0 <= nx < 2^64 /\ (more <> [] -> nx <> 0)).
    { unfold nx. destruct more as [|b' more']; [clear; split; [lia| intros X; exfalso; exact (X eq_refl)]|].
      (first [ pose proof ((batch_range A v [] AR b' (more_in A _ _ (b' :: more') W L b' ltac:(left; reflexivity)))) as dR_43; dand3 dR_43 as R1 R2 _ | pose proof (batch_range A v [] AR b' (more_in A _ _ (b' :: more') W L b' ltac:(left; reflexivity))) as (R1 & R2 & _) ]). unfold sb. clear -R1 R2 CE. kung_all. split; [lia| intros _; lia]. }
    destruct NXR as [NXR NXNZ].
    assert (INlast : In (last (BA kb es0 :: more) (BA 0 [])) (a_qthread A ++ a_qglobal A ++ a_qlimbo A)).
    { rewrite (wrT A W), L. cbn [app]. apply in_or_app. right.
      assert (X : forall (l : list batch) d, l <> [] -> In (last l d) l).
      { clear. induction l as [|x l IH]; intros d NE; [congruence|]. destruct l as [|y l']; [left; reflexivity| right; apply IH; discriminate]. }
      apply X. discriminate. }
    assert (TLR : 0 <= tl < 2^64).
    { unfold tl. (first [ pose proof ((batch_range A v [] AR _ INlast)) as dR_44; dand3 dR_44 as R1 R2 _ | pose proof (batch_range A v [] AR _ INlast) as (R1 & R2 & _) ]). unfold sb. clear -R1 R2 CE. kung_all. lia. }
    assert (QNN : forall l, (forall e, In e (q_entries l) -> 0 <= qe_n e) -> 0 <= q_bytes l).
    { clear. intros l QW. induction l as [|bb r IH]; [cbn; lia|]. rewrite q_bytes_cons, batch_bytes_ebytes.
      assert (IHr : 0 <= q_bytes r) by (apply IH; intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; right; exact He).
      assert (EW : forall e, In e (ba_entries bb) -> 0 <= qe_n e) by (intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; left; exact He).
      assert (0 <= ebytes (ba_entries bb)); [| unfold kQuarantineBatchBytes; lia].
      clear -EW. induction (ba_entries bb) as [|e es IHe]; [cbn; lia|].
      rewrite ebytes_cons. unfold qe_bytes. pose proof (user_size_pos (qe_n e) ltac:(apply EW; left; reflexivity)).
      assert (0 <= ebytes es) by (apply IHe; intros e' He'; apply EW; right; exact He'). lia. }
    assert (QWF : forall e, In e (q_entries (a_qlimbo A)) -> 0 <= qe_n e).
    { intros e He. destruct (qentry_wf A v [] AR e ltac:(rewrite (wrT A W); cbn [app]; unfold q_entries in *; rewrite flat_map_app; apply in_or_app; right; exact He)) as [N _]. clear -N. lia. }
    assert (TSR : batch_bytes (BA kb es0) <= ts < 2^64 /\ 0 <= batch_bytes (BA kb es0)).
    { unfold ts. rewrite q_bytes_cons. rewrite L in QB, QWF. rewrite q_bytes_cons in QB.
      pose proof (QNN more ltac:(intros e He; apply QWF; rewrite q_entries_cons; apply in_or_app; right; exact He)) as M0.
      pose proof (QNN [BA kb es0] ltac:(intros e He; apply QWF; rewrite q_entries_cons; apply in_or_app; left; cbn in He; rewrite app_nil_r in He; exact He)) as B0.
      rewrite q_bytes_cons, q_bytes_nil in B0. clear -QB M0 B0. lia. }
    destruct TSR as [TSR BS0].
    (* [comment removed for export] *)
    set (Q := fun ms' : machine_state => exists (m' : mem),
           ((cnt <> 0 /\ ms' = MS (it_regs (wz dsp) gp (cl_tp LPA) T b cnt s10 s11 ra' (wz (batch_bytes (BA kb es0))) (wz (ts - batch_bytes (BA kb es0))) a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' 0) F (wz dorec_callblk) fc None m' (seg_rom rsegs))
            \/ (cnt = 0 /\ ms' = MS (mkR ra' (wz dsp) gp (cl_tp LPA) t0' t1' t2' (wz T) (wz 0xb1d58) (wz (batch_bytes (BA kb es0))) (wz (ts - batch_bytes (BA kb es0))) a2' a3' a4' a5' a6' a7'
                                        (wz LMA_L) (wz LMA_STAT) (wz b) (wz (2^37)) (wz 0) s7' s8' s9' s10 s11 t3' t4' t5' t6') F (wz dorec_batchblk) fc None m' (seg_rom rsegs))) /\
           rw_cells rsegs m' T [C8 (wz (tn - 1)); C8 (wz nx); C8 (wz (if nx =? 0 then 0 else tl)); C8 (wz (ts - batch_bytes (BA kb es0)))] /\
           rw_cells rsegs m' b [C8 (wz nx); C8 (wz (batch_bytes (BA kb es0))); C8 (wz cnt)] /\
           munch [(T, T + 32)] v m' /\ wmono rsegs v m' /\ mem_inv rsegs m').
    unfold head_cfgG. cbn [length]. fold tn.
    eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR A) pa_wxR _ (pa_eager A) Q _ md TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      unshelve (eapply (batch_pop gp (cl_tp LPA) s10 s11 (wz dsp) F fc v T b cnt thr sb ri _ _ _ _ _ _ Q
                ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' tn tl ts nx (batch_bytes (BA kb es0))
                TNR NXR TLR BS0 TSR)).
      all: try assumption.
      all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
      all: try assumption.
      all: first [ assumption | reflexivity
                 | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                 | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                 | unfold cnt; clear -LEN; unfold kQuarantineBatchCount in LEN; lia
                 | clear -BLO; kung_all; lia
                 | clear -BHI; lia
                 | exact TH | exact BC
                 | intros CZ m' TC' BC' MU' WM' MI'; apply evt_done; subst Q; exists m'; split; [left; split; [exact CZ| reflexivity]|]; exact (conj TC' (conj BC' (conj MU' (conj WM' MI'))))
                 | intros CZ m' TC' BC' MU' WM' MI'; apply evt_done; subst Q; exists m'; split; [right; split; [exact CZ| reflexivity]|]; exact (conj TC' (conj BC' (conj MU' (conj WM' MI'))))
                 | match goal with |- ?g => idtac "UNSOLVED:" g end ]. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex1 HQ as m'; dand6 HQ as CASE TC' BC' MUN WM' MI' | dand7 HQ as m' CASE TC' BC' MUN WM' MI' | destruct HQ as (m' & CASE & TC' & BC' & MUN & WM' & MI') ]).
    assert (MSE : exists regs pcw, msr' = MS regs F pcw fc None m' (seg_rom rsegs)) by (destruct CASE as [[_ ->]|[_ ->]]; eexists _, _; reflexivity).
    (first [ dex2 MSE as regs pcw | dand3 MSE as regs pcw MSE | destruct MSE as (regs & pcw & MSE) ]). rewrite MSE in Hcl |- *. rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m m') = m').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NNR _ _ a WM'); [exact H1| lia]. }
    assert (AGC : forall a, 0 <= a < alloc_ceiling -> m' (wz a) = v (wz a)).
    { intros a Ha. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha CE; lia). cbn [outside]. clear -Ha CEIL LOW. split; [|exact I]. intros X. lia. }
    assert (AGW : forall a, 0 <= a < 2^64 -> ~ (lo <= a < uspd) -> m' (wz a) = v (wz a)).
    { intros a Ha NW. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha; lia). cbn [outside]. clear -Ha NW CEIL LOW. split; [|exact I]. intros X. lia. }
    pose proof (arepr_keep A v m' [] AR AGC NN) as AR'.
    (* [comment removed for export] *)
    assert (DISJ : forall a l, 0 < l -> (a + l <= T \/ T + 32 <= a) -> disjoint_from [(T, T + 32)] a l).
    { intros a l Hl Ha. cbn [disjoint_from]. clear -Hl Ha. split; [lia| exact I]. }
    (* [comment removed for export] *)
    assert (TLQ : (if nx =? 0 then 0 else tl) = match more with [] => 0 | _ :: _ => batch_addr sb (last more (BA 0 [])) end).
    { clear -NXNZ. subst nx tl. destruct more as [|b' more']; [reflexivity|].
      change (last (BA kb es0 :: b' :: more') (BA 0 [])) with (last (b' :: more') (BA 0 [])).
      destruct (Z.eqb_spec (batch_addr sb b') 0) as [E|NE]; [exfalso; exact (NXNZ ltac:(discriminate) E)| reflexivity]. }
    assert (RTMP' : tmp_hdr sb m' T more).
    { unfold tmp_hdr. replace (Z.of_nat (length more)) with (tn - 1) by (unfold tn; clear; lia).
      replace (q_bytes more) with (ts - batch_bytes (BA kb es0)) by (unfold ts; rewrite q_bytes_cons; clear; lia).
      rewrite <- TLQ. exact TC'. }
    (* [comment removed for export] *)
    assert (INb : forall b', In b' (BA kb es0 :: more) -> In b' (a_qthread A ++ (a_qglobal A ++ a_qlimbo A))).
    { intros b' Hb'. rewrite (wrT A W), L. cbn [app]. apply in_or_app. right. exact Hb'. }
    assert (INe : forall b' e, In b' (BA kb es0 :: more) -> In e (ba_entries b') -> In e (q_entries (a_qthread A ++ (a_qglobal A ++ a_qlimbo A)))).
    { intros b' e Hb' He. unfold q_entries. apply in_flat_map. exists b'. exact (conj (INb b' Hb') He). }
    assert (RC' : rcells A m' T (Some (BA kb es0, 0%nat)) more).
    { constructor.
      - exact AR'.
      - exact RTMP'.
      - apply (tmp_chain_keep A v m' [] AR AGC more); [intros b' Hb'; apply INb; right; exact Hb'| exact CHm].
      - intros b' e Hb' He. apply (lentry_keep A v m' [] AR AGC NN e (INe b' e (or_intror Hb') He)). exact (RME b' e (or_intror Hb') He).
      - intros b' Hb'. destruct (RMO b' (or_intror Hb')) as [LB SHB].
        destruct (lbatch_keep A v m' [] AR AGC NN b' (ba_entries b') 0%nat (batch_bytes b') (INb b' (or_intror Hb')) (proj2 (batch_known A v [] AR b' (INb b' (or_intror Hb')))) LB) as [LB' SHB'].
        exact (conj LB' (SHB' SHB)).
      - cbn [ba_entries ba_idx]. destruct (RMO (BA kb es0) (or_introl eq_refl)) as [LB SHB]. cbn [ba_entries batch_bytes] in LB, SHB.
        destruct (lbatch_keep A v m' [] AR AGC NN (BA kb es0) es0 0%nat (batch_bytes (BA kb es0)) (INb _ (or_introl eq_refl)) LEN LB) as [LB' SHB'].
        split; [| exact (conj LB' (SHB' SHB))].
        intros j e _ He. apply (lentry_keep A v m' [] AR AGC NN e (INe (BA kb es0) e (or_introl eq_refl) (nth_error_In _ _ He))).
        exact (RME (BA kb es0) e (or_introl eq_refl) (nth_error_In _ _ He)). }
    (* [comment removed for export] *)
    assert (RI' : RINV A (munrestrict (hidc (pa_hull A)) m m') md' T (Some (BA kb es0, 0%nat)) more).
    { constructor.
      - exact W.
      - exact L.
      - rewrite VIEW. exact RC'.
      - apply (hidden_keep A m m' HID). exact AGC.
      - exact EXTRA.
      - first [ exact (aledger_sbm _ _ _ _ md md' Hsame LED)
              | (* [comment removed for export] *)
                refine (aledger_reg _ _ _ _ _ _ (fun c0 _ => EXT c0) (aledger_sbm _ _ _ _ md md' Hsame LED)) ].
      - exact HI'.
      - (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT' _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT' & _) ]). rewrite HLT'. exact HLT.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact COV.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact CEI. }
    (* [comment removed for export] *)
    assert (PF' : put_frame thr m').
    { unfold put_frameG in *. eapply rw_cells_transport; [exact PF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right. clear. lia. }
    assert (RF' : rec_frame thr m').
    { unfold rec_frameG in *. eapply rw_cells_transport; [exact RF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right. clear. lia. }
    assert (DF' : rw_cells rsegs m' dsp (dorec_fr thr scr)).
    { eapply rw_cells_transport; [exact DF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. left. cbn [cells_size csize Nat.add dorec_frG dorec_frame length]. clear. lia. }
    assert (STK' : stk rsegs m' lo dsp).
    { apply (stk_transport_disjoint rsegs [(T, T + 32)] v m' lo dsp ST MUN WM'). apply DISJ; [clear -LOW CEIL; lia|]. left. clear. lia. }
    assert (SM' : mapped m' lo (uspd - lo)).
    { intros q Hq.
      destruct (Z.lt_ge_cases (lo + q) dsp) as [C1|C1].
      { exact (stk_mapped_pa m' lo dsp lo (dsp - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
      destruct (Z.lt_ge_cases (lo + q) T) as [C2|C2].
      { pose proof (rw_mapped_hi m' _ _ DF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
        specialize (M (lo + q - dsp) ltac:(clear -C1 C2; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M. }
      destruct (Z.lt_ge_cases (lo + q) (T + 32)) as [C3|C3].
      { pose proof (rw_mapped_hi m' _ _ RTMP' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - T) ltac:(clear -C2 C3; lia)). replace (T + (lo + q - T)) with (lo + q) in M by (clear; lia). exact M. }
      destruct (Z.lt_ge_cases (lo + q) (T + 80)) as [C4|C4].
      { pose proof (rw_mapped_hi m' _ _ RF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (lo + q - (T + 32))) with (lo + q) in M by (clear; lia). exact M. }
      pose proof (rw_mapped_hi m' _ _ PF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
      specialize (M (lo + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (lo + q - (uspd + -80))) with (lo + q) in M by (clear; lia). exact M. }
    (* [comment removed for export] *)
    assert (RS : rstep (pa_owned A) (pa_owned A) lo uspd v m').
    { apply rstep_window; [exact AGW| exact SM'|]. intros a Oa. pose proof (owned_below_ceilingT A a (WFT_of_WFR A W) Oa). clear -H CEIL. lia. }
    pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A v md A m' md' HIST (WFT_of_WFR A W) (WFT_of_WFR A W) CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (fun c _ V => V) (wamd_sbm md md' Hsame HLT) RS) as HIST'.
    (* [comment removed for export] *)
    assert (CU' : CUR A (munrestrict (hidc (pa_hull A)) m m') md' (Some (BA kb es0, 0%nat)) more scr).
    { constructor; rewrite ?VIEW.
      - exact RI'.
      - exact HIST'.
      - exact MI'.
      - exact STK'.
      - exact PF'.
      - exact RF'.
      - exact DF'.
      - cbn [ba_entries]. split; [exact LEN| clear; lia].
      - exact QB. }
    cbn [ms_mem].
    destruct CASE as [[CZ E]|[CZ E]]; rewrite MSE in E; injection E as Er Ep; subst regs pcw.
    - specialize (K1 (munrestrict (hidc (pa_hull A)) m m') md' (wz (batch_bytes (BA kb es0))) (wz (ts - batch_bytes (BA kb es0)))
                     ltac:(cbn [ba_entries]; intros E0; apply CZ; unfold cnt; rewrite E0; reflexivity) CU').
      unfold it_cfgG in K1. cbn [ba_entries] in K1. fold sb in K1. fold b cnt in K1. exact K1.
    - specialize (K0 (munrestrict (hidc (pa_hull A)) m m') md' (wz (batch_bytes (BA kb es0))) (wz (ts - batch_bytes (BA kb es0)))
                     ltac:(cbn [ba_entries]; unfold cnt in CZ; clear -CZ; destruct es0; [reflexivity| cbn in CZ; lia]) CU').
      unfold blk_cfgG in K0. fold sb in K0. fold b in K0. exact K0.
  Qed.
  (* [comment removed for export] *)
  #[using="VB SPA HI47 SPHI LOW CEIL"] Lemma step_batch_push : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word),
    CUR A m md (Some (b0, length (ba_entries b0))) more scr ->
    Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass))) < max_count kQuarantineBatchClass ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        more <> [] -> CUR A' m' md' None more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (head_cfg A' m' md' more (wz dorec_nextpc) a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (wz (batch_addr (a_sb A) b0)) s6' s7' s8' s9') TS) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        more = [] -> XCUR A' m' md' -> a_pl A' = a_pl A ->
        srealizes rsegs (exit_cfg A' m' md' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'') TS) ->
    srealizes rsegs (blk_cfg A m md b0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9') TS.
  Proof.
    intros A m md b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CU ROOM KM K0.
    destruct CU as [RI HIST MI ST PF RF DF [LEN _] QB]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC) : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    assert (L' : a_qlimbo A = BA (ba_idx b0) [] :: more).
    { rewrite L. unfold limbo_of. rewrite skipn_all. reflexivity. }
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (* [comment removed for export] *)
    (first [ pose proof ((rk_ri A v [] AR)) as dR_48; dand10 dR_48 as RI0 RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v [] AR) as (RI0 & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    (first [ pose proof ((rk_sep A v [] AR)) as dR_49; dand6 dR_49 as SP1 SP2 SP3 SP4 SP5 SP6 | pose proof (rk_sep A v [] AR) as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6) ]).
    (first [ pose proof ((rk_place A v [] AR)) as dR_50; dand6 dR_50 as PT PTC PTM PC PCC _ | pose proof (rk_place A v [] AR) as (PT & PTC & PTM & PC & PCC & _) ]).
    pose proof (rk_TC A v [] AR) as TC. pose proof (rk_PCo A v [] AR) as PCo. pose proof (rk_SBc A v [] AR) as CSB. pose proof (rk_CRI A v [] AR) as CRI.
    pose proof (wrI A W) as CI.
    (first [ pose proof ((rk_stats A v [] AR)) as dR_51; dex3 dR_51 as statv rf rfd; dand4 dR_51 as RFR RFDR STA TRF | pose proof ((rk_stats A v [] AR)) as dR_51; dand7 dR_51 as statv rf rfd RFR RFDR STA TRF | destruct (rk_stats A v [] AR) as (statv & rf & rfd & RFR & RFDR & STA & TRF) ]).
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; clear; lia).
    (first [ pose proof ((rk_line A v [] AR CI kQuarantineBatchClass C24)) as dR_52; dex1 dR_52 as ks; dand7 dR_52 as LKS KSM KSF KLE KRG KND LINE | pose proof ((rk_line A v [] AR CI kQuarantineBatchClass C24)) as dR_52; dand8 dR_52 as ks LKS KSM KSF KLE KRG KND LINE | destruct (rk_line A v [] AR CI kQuarantineBatchClass C24) as (ks & LKS & KSM & KSF & KLE & KRG & KND & LINE) ]).
    destruct RC as [RAR RTMP RCH RME RMO RCUR]. cbn [rc_cur] in RCUR. (first [ dand3 RCUR as RENT RBAT RBSH | destruct RCUR as (RENT & RBAT & RBSH) ]).
    pose proof (head_in A _ _ more W L') as HIN.
    pose proof (batch_known A v [] AR (BA (ba_idx b0) []) HIN) as [KBR _]. cbn [ba_idx] in KBR.
    pose proof (rk_batch A v [] AR (ba_idx b0) KBR) as BG. cbv zeta in BG. (first [ dand9 BG as BFORM BLO BHI BAL KB0 KBH SEP_bt SEP_bc SEP_br | destruct BG as (BFORM & BLO & BHI & BAL & KB0 & KBH & SEP_bt & SEP_bc & SEP_br) ]).
    (first [ pose proof ((rk_region_facts A v [] AR kQuarantineBatchClass C24)) as dR_55; dand7 dR_55 as RGF1 RGF2 RGF3 RGF4 RGF5 RGF6 RGF7 | destruct (rk_region_facts A v [] AR kQuarantineBatchClass C24) as (RGF1 & RGF2 & RGF3 & RGF4 & RGF5 & RGF6 & RGF7) ]).
    (first [ pose proof ((rk_region A v [] AR kQuarantineBatchClass 0%nat C24 ltac:(lia))) as dR_56; dex4 dR_56 as na nfs v88 junk; dand8 dR_56 as RMX RNF RMFA RMU RNA RNFS LJ RARR | pose proof ((rk_region A v [] AR kQuarantineBatchClass 0%nat C24 ltac:(lia))) as dR_56; dand12 dR_56 as na nfs v88 junk RMX RNF RMFA RMU RNA RNFS LJ RARR | destruct (rk_region A v [] AR kQuarantineBatchClass 0%nat C24 ltac:(lia)) as (na & nfs & v88 & junk & RMX & RNF & RMFA & RMU & RNA & RNFS & LJ & RARR) ]).
    pose proof (bv_carved A v [] (ba_idx b0) more AR W L') as CVe.
    pose proof TC as TC'. (first [ dand13 TC' as _ _ _ _ _ Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct TC' as (_ & _ & _ & _ & _ & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    pose proof (max_count_range kQuarantineBatchClass C24) as (MCR & _).
    set (thr := p_thr (a_pl A)) in *. set (sb := a_sb A) in *. set (ri := a_ri A) in *.
    set (b := batch_addr sb b0) in *.
    set (fac_ := free_array_of sb kQuarantineBatchClass) in *.
    set (cntc := Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass)))) in *.
    set (kk := 512 * ba_idx b0).
    set (tn := Z.of_nat (length more)).
    assert (TNR : 0 <= tn < 2^64).
    { pose proof (limbo_count_bound A W) as X. rewrite L' in X. cbn [length] in X.
      change (class_size kQuarantineBatchClass) with 8192 in RGF6. unfold tn. clear -X RGF1 RGF2 RGF6. kung_all. lia. }
    pose proof RTMP as TH. unfold tmp_hdr in TH. fold tn in TH.
    assert (RRE : bv_unsigned (wz recycle_ret : word) mod 2 = 0) by (rewrite unsigned_lit; [reflexivity| unfold recycle_ret; clear; lia]).
    set (Q := fun ms' : machine_state => exists (a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 statv' : word) (m' : mem),
           ((more <> [] /\ ms' = MS (head_regs (wz dsp) gp (cl_tp LPA) T s10 s11 (wz dorec_nextpc) tn a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 (wz b) s6' s7' s8' s9') F (wz dorec_head) fc None m' (seg_rom rsegs)
             /\ rw_cells rsegs m' dsp (dorec_fr thr scr) /\ stk rsegs m' lo dsp)
            \/ (more = [] /\ ms' = MS (mkR (wz recycle_ret) (wz (dsp + 112)) gp (cl_tp LPA) t0 t1 t2 (wz QINST) (wz (thr + 80)) (wz 0) a1 a2 a3 a4 a5 a6 a7
                                        xs2 (wz stkobj) (wz (thr + 208)) xs5 (wz (2^20)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (wz recycle_ret)) fc None m' (seg_rom rsegs)
             /\ stk rsegs m' lo (dsp + 112))) /\
           tmp_hdr sb m' T more /\
           rw_cells rsegs m' (thr + 208 + 80 * kQuarantineBatchClass) [C4 (wz (cntc + 1)); C4 (wz (max_count kQuarantineBatchClass)); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat cntc) (wz kk)))] /\
           rw_cells rsegs m' (thr + 208 + 2576) [C8 statv'] /\
           munch [(dsp - 48, dsp); (thr + 208 + 80 * kQuarantineBatchClass, thr + 208 + 80 * kQuarantineBatchClass + 80); (thr + 208 + 2576, thr + 208 + 2584)] v m' /\
           wmono rsegs v m' /\ mem_inv rsegs m').
    unfold blk_cfgG. fold sb. fold b.
    eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR A) pa_wxR _ (pa_eager A) Q _ md TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (batch_free_push gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b scr
                (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                pa_tsd (p_ctx (a_pl A)) thr sb ri)
        with (kb := kk) (tn := tn) (cntc := cntc) (maxc := max_count kQuarantineBatchClass) (ks := ks) (statv := statv)
             (tf := match more with [] => 0 | b' :: _ => batch_addr sb b' end)
             (tl := match more with [] => 0 | _ :: _ => batch_addr sb (last more (BA 0 [])) end)
             (ts := q_bytes more).
      all: try assumption.
      all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
      all: try assumption.
            all: first [ assumption | reflexivity
                 | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                 | unfold pa_tsd; clear; lia
                 | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                 | clear -SBRI RHI; lia
                 | unfold kk; clear -KB0 KBH; lia
                 | unfold cntc; clear -ROOM; lia
                 | clear -MCR; lia
                 | exact TH
                 | intros NE a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' DF' TC' LN' ST' MUN WM' MI' STK';
                   apply evt_done; subst Q; first [ hotw_ex16 a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' | exists a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', statv', m' ];
                   split; [left; split; [unfold tn in NE; clear -NE; intros E; apply NE; rewrite E; reflexivity| split; [reflexivity| exact (conj DF' STK')]]|];
                   exact (conj TC' (conj LN' (conj ST' (conj MUN (conj WM' MI')))))
                 | intros EQ a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' DF' TC' LN' ST' MUN WM' MI' STK';
                   apply evt_done; subst Q; first [ hotw_ex16 a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' | exists a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', statv', m' ];
                   split; [right; split; [unfold tn in EQ; clear -EQ; destruct more; [reflexivity| cbn in EQ; lia]| split; [reflexivity| exact STK']]|];
                   exact (conj TC' (conj LN' (conj ST' (conj MUN (conj WM' MI')))))
                 | match goal with |- ?g => idtac "UNSOLVED:" g end ]. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex16 HQ as a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m'; dand7 HQ as CASE TC' LN' ST' MUN WM' MI' | dand23 HQ as a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' CASE TC' LN' ST' MUN WM' MI' | destruct HQ as (a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t0'' & t1'' & t2'' & t3'' & t4'' & t5'' & t6'' & statv' & m' & CASE & TC' & LN' & ST' & MUN & WM' & MI') ]).
    assert (MSE : exists regs pcw, msr' = MS regs F pcw fc None m' (seg_rom rsegs)) by (destruct CASE as [(_ & -> & _)|(_ & -> & _)]; eexists _, _; reflexivity).
    (first [ dex2 MSE as regs pcw | dand3 MSE as regs pcw MSE | destruct MSE as (regs & pcw & MSE) ]). rewrite MSE in Hcl |- *. rewrite unrestrict_MS. cbn [ms_mem] in Hcl. cbn [ms_mem].
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m m') = m').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NNR _ _ a WM'); [exact H1| lia]. }
    (* [comment removed for export] *)
    set (fa' := rg_mapped_fa (a_reg A kQuarantineBatchClass)).
    set (cache' := recp_cache (a_cache A) kQuarantineBatchClass (ba_idx b0)).
    set (A' := recA' A (a_reg A) cache' more).
    assert (RGE : recp_reg (a_reg A) (a_cache A) kQuarantineBatchClass (ba_idx b0) fa' = a_reg A).
    { unfold recp_reg. fold cntc. destruct (Z.eqb_spec cntc (max_count kQuarantineBatchClass)); [exfalso; clear -e ROOM; lia| reflexivity]. }
    assert (CAE : pk_chunks (cache' kQuarantineBatchClass) = pk_chunks (a_cache A kQuarantineBatchClass) ++ [ba_idx b0]).
    { unfold cache', recp_cache, cache_set, cache_push_list. rewrite Z.eqb_refl. fold cntc. destruct (Z.eqb_spec cntc (max_count kQuarantineBatchClass)); [exfalso; clear -e ROOM; lia| reflexivity]. }
    assert (CAO : forall c', c' <> kQuarantineBatchClass -> cache' c' = a_cache A c').
    { intros c' NE. unfold cache', recp_cache, cache_set. destruct (Z.eqb_spec c' kQuarantineBatchClass); [exfalso; exact (NE e)| reflexivity]. }
    assert (EXT : same_ext (a_reg A) (a_reg A)) by (intros c0; split; reflexivity).
    pose proof (su_hull A (a_reg A) cache' more EXT) as HULL. pose proof (su_lhull A (a_reg A) cache' more EXT) as LHULL.   (* [comment removed for export] *)
    pose proof (su_eager A (a_reg A) cache' more EXT) as EAGER.
    change (mkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with A' in HULL, LHULL, EAGER.
    (* [comment removed for export] *)
    set (Wn := fun a => dsp - 48 <= a < dsp).
    set (SHP := fun a : Z => False).
    assert (MU : forall a, 0 <= a < 2^64 -> ~ rp_foot A kQuarantineBatchClass (ba_idx b0) (a_reg A) Wn SHP a -> m' (wz a) = v (wz a)).
    { intros a Ha NF. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha; lia). unfold rp_foot in NF. subst Wn SHP. cbv beta in NF.
      cbn [outside]. unfold thr, cntc in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NF.
      - left. exact X.
      - do 3 right; left. exact X.
      - do 4 right; left. clear -X. lia. }
    (* [comment removed for export] *)
    assert (W' : WFR A').
    { pose proof (WFR_batch A (ba_idx b0) fa' more W L' ltac:(intros E; exfalso; unfold cntc in ROOM; clear -E ROOM; lia)) as X.
      unfold recpbA in X. rewrite RGE in X. exact X. }
    assert (WNH : forall a, Wn a -> alloc_ceiling <= a) by (subst Wn; cbv beta; intros a Ha; clear -Ha CEIL LOW; lia).
    assert (SHPW : forall a, SHP a -> sh b <= a < sh b + class_size kQuarantineBatchClass / 8) by (subst SHP; cbv beta; intros a []).
    pose proof (bv_ne_live A v [] (ba_idx b0) more AR W L') as NE_live.
    pose proof (bv_ne_batch A (ba_idx b0) more W L') as NEB.
    pose proof (bv_ne_rest A v [] (ba_idx b0) more AR W L') as NE_rest.
    pose proof (bv_ne_limbo A v [] (ba_idx b0) more AR W L') as NEL.
    (* [comment removed for export] *)
    assert (DISJ : forall a l, 0 < l -> (ri <= a /\ a + l <= ri + 4096) \/ (fac_ <= a /\ a + l <= fac_ + rg_mapped_fa (a_reg A kQuarantineBatchClass)) \/ (T <= a /\ a + l <= uspd) ->
             disjoint_from [(dsp - 48, dsp); (thr + 208 + 80 * kQuarantineBatchClass, thr + 208 + 80 * kQuarantineBatchClass + 80); (thr + 208 + 2576, thr + 208 + 2584)] a l).
    { intros a l Hl Ha. unfold thr, ri, sb, fac_ in *. cbn [disjoint_from].
      destruct Ha as [Ha|[Ha|Ha]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
      all: first [ clear -Ha Hl C24 SBRI RLO RHI CEIL LOW CE SPR; kung_all; lia
                 | clear -Ha Hl SP1 C24; unfold apart in SP1; lia
                 | clear -Ha Hl SP4 C24 RGF3 SBRI; unfold apart, free_array_of in *; kung_all; lia
                 | clear -Ha Hl PTC CEIL LOW C24; lia
                 | clear -Ha Hl C24 SBRI RHI RGF3 CEIL LOW; unfold free_array_of in *; kung_all; lia ]. }
    assert (OUT : forall a, (ri <= a < ri + 4096 \/ fac_ <= a < fac_ + rg_mapped_fa (a_reg A kQuarantineBatchClass) \/ T <= a < uspd) ->
             outside [(dsp - 48, dsp); (thr + 208 + 80 * kQuarantineBatchClass, thr + 208 + 80 * kQuarantineBatchClass + 80); (thr + 208 + 2576, thr + 208 + 2584)] a).
    { intros a Ha. apply (disjoint_outside _ a 1); [| clear; lia]. apply DISJ; [clear; lia|]. clear -Ha. lia. }
    assert (P_mx : u64_at rsegs m' (ri + 128 * kQuarantineBatchClass) 0).
    { assert (X : rw_cells rsegs m' (ri + 128 * kQuarantineBatchClass) [C8 (wz 0)]).
      { eapply rw_cells_transport; [exact RMX| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. left. cbn [cells_size csize Nat.add]. clear -C24. lia. }
      destruct X as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    assert (P_regc : region_repr_ LPA sb (a_reg A kQuarantineBatchClass) m' kQuarantineBatchClass).
    { apply (region_P A v m' [] AR NN kQuarantineBatchClass C24). intros a Ha. unfold rfoot in Ha. rewrite RIA, FAE in Ha. unfold kRegionInfoSize in Ha. fold fac_ in Ha.
      apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha C24 RLO RHI CE SBLO SBRI RGF3; unfold fac_, free_array_of in *; kung_all; lia).
      apply OUT. clear -Ha C24. lia. }
    (* [comment removed for export] *)
    assert (KKE : forall k', k' * class_size kQuarantineBatchClass / kCompactPtrScale = 512 * k').
    { intros k'. change (class_size kQuarantineBatchClass) with 8192. unfold kCompactPtrScale. replace (k' * 8192) with (512 * k' * 16) by (clear; lia). rewrite Z.div_mul by (clear; lia). reflexivity. }
    assert (ENC : forall k', In k' (pk_chunks (a_cache A kQuarantineBatchClass)) \/ k' = ba_idx b0 -> 0 <= k' * class_size kQuarantineBatchClass / kCompactPtrScale < 2^32).
    { intros k' Hk'. assert (KR' : 0 <= k' < carved_count A kQuarantineBatchClass) by (destruct Hk' as [Hk'| ->]; [exact (KRG k' Hk')| exact KBR]).
      rewrite KKE. change (class_size kQuarantineBatchClass) with 8192 in RGF6. clear -KR' RGF6 RGF1 RGF2. kung_all. lia. }
    assert (ENT : forall i0 k', nth_error (pk_chunks (a_cache A kQuarantineBatchClass) ++ [ba_idx b0]) i0 = Some k' ->
              nth_error (upd ks (Z.to_nat cntc) (wz kk)) i0 = Some (wz (k' * class_size kQuarantineBatchClass / kCompactPtrScale)) /\ 0 <= k' * class_size kQuarantineBatchClass / kCompactPtrScale < 2^32).
    { intros i0 k' Hk'. destruct (Nat.lt_ge_cases i0 (length (pk_chunks (a_cache A kQuarantineBatchClass)))) as [LT|GE].
      - rewrite nth_error_app1 in Hk' by exact LT. split; [| apply ENC; left; eapply nth_error_In; exact Hk'].
        rewrite nth_error_upd_other by (unfold cntc; clear -LT; lia).
        pose proof (f_equal (fun l => nth_error l i0) KSF) as E. cbv beta in E. rewrite nth_error_firstn in E.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A kQuarantineBatchClass)))); [| exfalso; clear -LT H; lia]. rewrite E, nth_error_map, Hk'. reflexivity.
      - rewrite nth_error_app2 in Hk' by exact GE. destruct (i0 - length (pk_chunks (a_cache A kQuarantineBatchClass)))%nat as [|x] eqn:EQ; cbn in Hk'; [injection Hk' as <-| destruct x; discriminate].
        assert (i0 = length (pk_chunks (a_cache A kQuarantineBatchClass))) by (clear -GE EQ; lia). subst i0. split; [| apply ENC; right; reflexivity].
        unfold cntc. rewrite Nat2Z.id. rewrite nth_error_upd_same by (rewrite LKS; unfold cntc in ROOM; clear -ROOM MCR; lia). rewrite KKE. reflexivity. }
    pose proof LN' as LNx. unfold cntc in LNx at 1.
    replace (Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass))) + 1) with (Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass) ++ [ba_idx b0]))) in LNx by (rewrite length_app; cbn; lia).
    pose proof (line_of_cells m' (thr + 208 + 80 * kQuarantineBatchClass) kQuarantineBatchClass (upd ks (Z.to_nat cntc) (wz kk)) (pk_chunks (a_cache A kQuarantineBatchClass) ++ [ba_idx b0]) (a_cache_inited A) C24 CI
                  ltac:(rewrite upd_length; exact LKS) ltac:(rewrite length_app; cbn [length]; unfold cntc in ROOM; clear -ROOM MCR; lia) ENT
                  LNx) as P_linec.
    rewrite <- CAE in P_linec.
    replace (thr + 208 + 80 * kQuarantineBatchClass) with (thr + off_th_per_class kQuarantineBatchClass) in P_linec by (unfold off_th_per_class, off_th_alloc_cache, kPerClassSize; clear; lia).
    assert (MFA8 : rg_mapped_fa (a_reg A kQuarantineBatchClass) mod 8 = 0) by (apply (mod0_down _ kFreeArrayMapSize 8); [exists (2^15); reflexivity| exact RGF4]).
    assert (R'E : rg_mapped_user (a_reg A kQuarantineBatchClass) = rg_mapped_user (a_reg A kQuarantineBatchClass) /\ rg_allocated_user (a_reg A kQuarantineBatchClass) = rg_allocated_user (a_reg A kQuarantineBatchClass) /\
                  rg_mapped_fa (a_reg A kQuarantineBatchClass) <= rg_mapped_fa (a_reg A kQuarantineBatchClass) /\ rg_mapped_fa (a_reg A kQuarantineBatchClass) <= kFreeArraySize /\ rg_mapped_fa (a_reg A kQuarantineBatchClass) mod 8 = 0).
    { clear -RGF3 MFA8. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; try lia. }
    (first [ pose proof ((chunk_shadow A v [] AR kQuarantineBatchClass (ba_idx b0) C24 KBR)) as dR_60; dand4 dR_60 as CS1 CS2 CS3 CS4 | pose proof (chunk_shadow A v [] AR kQuarantineBatchClass (ba_idx b0) C24 KBR) as (CS1 & CS2 & CS3 & CS4) ]). fold sb in CS1, CS2, CS3, CS4.
    change (chunk_addr sb kQuarantineBatchClass (ba_idx b0)) with b in CS1, CS2, CS3, CS4.
    assert (AGSH : forall z, sh b <= z < sh b + class_size kQuarantineBatchClass / 8 -> m' (wz z) = v (wz z)).
    { intros z Hz. apply (AG_shadow_maps A v m' [] kQuarantineBatchClass (ba_idx b0) (a_reg A) AR Wn WNH SHP SHPW CVe R'E MU z).
      - exact (heap_shadow_rangeT A z (WFT_of_WFR A W) (CS2 z Hz)).
      - intros [].
      - rewrite Z.sub_diag. clear. intros X. cbn in X. lia. }
    assert (VSH : bytes_at rsegs m' (sh b) (pshadow_free kQuarantineBatchClass)).
    { eapply bytes_at_xfer; [exact RBSH|]. intros z Hz. apply AGSH. unfold pshadow_free, fa8 in Hz. rewrite repeat_length, Z2Nat.id in Hz by (change (class_size kQuarantineBatchClass) with 8192; clear; lia). exact Hz. }
    assert (P_fash : bytes_at rsegs m' (sh (fac_ + rg_mapped_fa (a_reg A kQuarantineBatchClass))) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_fa (a_reg A kQuarantineBatchClass) - rg_mapped_fa (a_reg A kQuarantineBatchClass)) / 8)))).
    { rewrite Z.sub_diag. cbn. apply bytes_at_nil. unfold sh, fac_, free_array_of. clear -C24 SBLO SBRI RHI RGF3 CE. kung_all. lia. }
    pose proof (recp_arepr A v m' [] kQuarantineBatchClass (ba_idx b0) more (a_reg A) cache' AR W Wn WNH SHP SHPW CVe NE_live NEB NE_rest
                  CAO ltac:(intros k' Hk'; rewrite CAE in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|[<-|[]]]; [left; exact Hk'| right; reflexivity])
                  ltac:(intros; reflexivity) R'E ltac:(intros k' Hk'; left; exact Hk')
                  MU NN P_mx P_regc P_linec VSH P_fash more) as AR'.
    change (recA' _ _ _ _) with A' in AR'.
    (* [comment removed for export] *)
    assert (INmore : forall b' e', In b' more -> In e' (ba_entries b') -> In e' ([] ++ q_entries more)).
    { intros b' e' Hb' He'. cbn [app]. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He'). }
    assert (RCM : forall cur, match cur with None => True | _ => False end -> rcells A' m' T cur more).
    { intros cur Hcur. constructor.
      - exact AR'.
      - exact TC'.
      - apply (tmp_chain_xfer A v m' [] kQuarantineBatchClass (ba_idx b0) (ba_idx b0) _ more (a_reg A) cache' AR W L' Wn WNH SHP SHPW CVe NEB R'E MU more); [intros b' Hb'; exact Hb'| exact RCH].
      - intros b' e' Hb' He'. apply (lentry_xfer A v m' [] kQuarantineBatchClass (ba_idx b0) (a_reg A) AR Wn WNH SHP SHPW CVe R'E MU NN e').
        + apply (limbo_in A (ba_idx b0) _ more W L'). exact (INmore b' e' Hb' He').
        + apply NEL. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He').
        + exact (RME b' e' Hb' He').
      - intros b' Hb'. destruct (RMO b' Hb') as [LB SHB]. pose proof (more_in A (ba_idx b0) _ more W L' b' Hb') as Hb2.
        destruct (lbatch_xfer A v m' [] kQuarantineBatchClass (ba_idx b0) (a_reg A) cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b') (ba_entries b') 0%nat (batch_bytes b')
                    (batch_carved A v [] AR b' Hb2) (NEB b' (or_intror Hb')) (proj2 (batch_known A v [] AR b' Hb2)) LB) as [LB' SHB'].
        split; [exact LB'| exact (SHB' SHB)].
      - destruct cur; [destruct Hcur| exact I]. }
    (* [comment removed for export] *)
    assert (RIM : forall cur, match cur with None => True | _ => False end -> a_qlimbo A' = limbo_of cur more -> RINV A' (munrestrict (hidc (pa_hull A)) m m') md' T cur more).
    { intros cur Hcur Hl. constructor.
      - exact W'.
      - exact Hl.
      - rewrite HULL, VIEW. exact (RCM cur Hcur).
      - apply (su_hidden A (a_reg A) cache' more EXT m m' HID).
        + intros z Gz Hz Vz. destruct Gz as [SMz _]. unfold in_shadow_maps in SMz. apply NN; [clear -SMz; kung_all; lia| right; clear -SMz; kung_all; lia| clear -SMz; kung_all; lia| exact Vz].
        + intros z Gz Hz NHS. destruct Gz as [SMz _]. apply (AG_shadow_maps A v m' [] kQuarantineBatchClass (ba_idx b0) (a_reg A) AR Wn WNH SHP SHPW CVe R'E MU z SMz).
          * intros [].
          * rewrite Z.sub_diag. clear. intros X. cbn in X. lia.
        + intros z Hz Hc Vz. apply NN; [clear -Hz; kung_all; lia| right; clear -Hz; kung_all; lia| clear -Hz; kung_all; lia| exact Vz].
      - exact EXTRA.
      - first [ exact (aledger_sbm _ _ _ _ md md' Hsame LED)
              | (* [comment removed for export] *)
                refine (aledger_reg _ _ _ _ _ _ (fun c0 _ => EXT c0) (aledger_sbm _ _ _ _ md md' Hsame LED)) ].
      - rewrite HULL, LHULL, EAGER. exact HI'.   (* [comment removed for export] *)
      - (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT' _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT' & _) ]). rewrite HLT'. exact HLT.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact COV.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact CEI. }
    (* [comment removed for export] *)
    assert (PF' : put_frame (p_thr (a_pl A)) m').
    { unfold put_frameG in *. eapply rw_cells_transport; [exact PF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
    assert (RF' : rec_frame (p_thr (a_pl A)) m').
    { unfold rec_frameG in *. eapply rw_cells_transport; [exact RF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
    assert (SMT : mapped m' T (uspd - T)).
    { intros q Hq. pose proof TC' as TM'. unfold tmp_hdr in TM'.
      destruct (Z.lt_ge_cases (T + q) (T + 32)) as [C3|C3].
      { pose proof (rw_mapped_hi m' _ _ TM' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        exact (M q ltac:(clear -Hq C3; lia)). }
      destruct (Z.lt_ge_cases (T + q) (T + 80)) as [C4|C4].
      { pose proof (rw_mapped_hi m' _ _ RF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (T + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (T + q - (T + 32))) with (T + q) in M by (clear; lia). exact M. }
      pose proof (rw_mapped_hi m' _ _ PF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
      specialize (M (T + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (T + q - (uspd + -80))) with (T + q) in M by (clear; lia). exact M. }
    assert (SM' : mapped m' lo (uspd - lo)).
    { intros q Hq. destruct (Z.lt_ge_cases (lo + q) T) as [C1|C1]; [| specialize (SMT (lo + q - T) ltac:(clear -C1 Hq; lia)); replace (T + (lo + q - T)) with (lo + q) in SMT by (clear; lia); exact SMT].
      destruct CASE as [(_ & _ & DF' & STK')|(_ & _ & STK')].
      - destruct (Z.lt_ge_cases (lo + q) dsp) as [C0|C0].
        { exact (stk_mapped_pa m' lo dsp lo (dsp - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C0; lia)). }
        pose proof (rw_mapped_hi m' _ _ DF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
        specialize (M (lo + q - dsp) ltac:(clear -C0 C1; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M.
      - exact (stk_mapped_pa m' lo (dsp + 112) lo (dsp + 112 - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
    (* [comment removed for export] *)
    assert (RS : rstep (pa_owned A) (pa_owned A') lo uspd v m').
    { unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      - intros a Ha NO NO' NW. apply MU; [exact Ha|]. intros Fa.
        destruct (foot_owned A v [] kQuarantineBatchClass (ba_idx b0) (a_reg A) AR Wn SHP SHPW CVe NE_live R'E a Fa) as [X|[X|[X|X]]].
        + apply NW. subst Wn. cbv beta in X. clear -X LOW CEIL. lia.
        + exact (NO X).
        + clear -X. lia.
        + rewrite Z.sub_diag in X. clear -X. cbn in X. lia.
      - intros a Ha NI Hv. right. apply NN; [clear -Ha; lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| clear -Ha; lia| exact Hv].
      - exact SM'.
      - intros a Ha O'. left. exact (proj1 (su_owned A (a_reg A) cache' more EXT a) O').
      - intros a Ha O NO'. exfalso. apply NO'. exact (proj2 (su_owned A (a_reg A) cache' more EXT a) O). }
    assert (NZ : a_reg A kQuarantineBatchClass <> region_zero).
    { intros E. pose proof KBR as X. unfold carved_count, carved_count_ in X. rewrite E in X. cbn in X. clear -X.
      pose proof (Z.div_0_l (class_size kQuarantineBatchClass)). rewrite Zdiv_0_l in X. lia. }
    pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A v md A' m' md' HIST (WFT_of_WFR A W) (WFT_of_WFR A' W') CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                  (fun c0 NE V0 => su_virgin A (a_reg A) cache' more kQuarantineBatchClass c0 NZ (fun c' _ => eq_refl) CAO V0)
                  (wamd_sbm md md' Hsame HLT) RS) as HIST'.
    (* [comment removed for export] *)
    destruct CASE as [(NE & E & DF' & STK')|(EQ & E & STK')]; rewrite MSE in E; injection E as Er Ep; subst regs pcw.
    - assert (CU' : CUR A' (munrestrict (hidc (pa_hull A)) m m') md' None more scr).
      { constructor; rewrite ?HULL, ?VIEW.
        - apply RIM; [exact I| reflexivity].
        - exact HIST'.
        - exact MI'.
        - exact STK'.
        - exact PF'.
        - exact RF'.
        - exact DF'.
        - exact I.
        - unfold A', recA'. cbn [a_qlimbo]. rewrite L' in QB. rewrite q_bytes_cons, batch_bytes_ebytes in QB. cbn [ba_entries] in QB. change (ebytes []) with 0 in QB. unfold kQuarantineBatchBytes in QB. clear -QB. lia. }
      specialize (KM A' (munrestrict (hidc (pa_hull A)) m m') md' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' NE CU' eq_refl).
      unfold head_cfgG in KM. fold tn in KM. exact KM.
    - subst more.
      assert (XCU' : XCUR A' (munrestrict (hidc (pa_hull A)) m m') md').
      { constructor; rewrite ?HULL, ?VIEW.
        - apply RIM; [exact I| reflexivity].
        - exact HIST'.
        - exact MI'.
        - replace T with (dsp + 112) by (clear; lia). exact STK'.
        - exact PF'.
        - exact RF'. }
      specialize (K0 A' (munrestrict (hidc (pa_hull A)) m m') md' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' eq_refl XCU' eq_refl).
      unfold exit_cfgG in K0. cbn [a_pl] in K0. fold thr in K0. replace (dsp + 112) with T by (clear; lia). exact K0.
  Qed.

  (* [comment removed for export] *)
  #[using="VB SPA HI47 SPHI LOW CEIL"] Lemma step_batch_drainfast : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word),
    CUR A m md (Some (b0, length (ba_entries b0))) more scr ->
    Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass))) = max_count kQuarantineBatchClass ->
    4 * (Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) + max_count kQuarantineBatchClass / 2) <= rg_mapped_fa (a_reg A kQuarantineBatchClass) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        more <> [] -> CUR A' m' md' None more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (head_cfg A' m' md' more (wz dorec_nextpc) a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (wz (batch_addr (a_sb A) b0)) s6' s7' s8' s9') TS) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        more = [] -> XCUR A' m' md' -> a_pl A' = a_pl A ->
        srealizes rsegs (exit_cfg A' m' md' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'') TS) ->
    srealizes rsegs (blk_cfg A m md b0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9') TS.
  Proof.
    intros A m md b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CU FULL ROOMF KM K0.
    destruct CU as [RI HIST MI ST PF RF DF [LEN _] QB]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC) : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    assert (L' : a_qlimbo A = BA (ba_idx b0) [] :: more).
    { rewrite L. unfold limbo_of. rewrite skipn_all. reflexivity. }
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (* [comment removed for export] *)
    (first [ pose proof ((rk_ri A v [] AR)) as dR_62; dand10 dR_62 as RI0 RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v [] AR) as (RI0 & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    (first [ pose proof ((rk_sep A v [] AR)) as dR_63; dand6 dR_63 as SP1 SP2 SP3 SP4 SP5 SP6 | pose proof (rk_sep A v [] AR) as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6) ]).
    (first [ pose proof ((rk_place A v [] AR)) as dR_64; dand6 dR_64 as PT PTC PTM PC PCC _ | pose proof (rk_place A v [] AR) as (PT & PTC & PTM & PC & PCC & _) ]).
    pose proof (rk_TC A v [] AR) as TC. pose proof (rk_PCo A v [] AR) as PCo. pose proof (rk_SBc A v [] AR) as CSB. pose proof (rk_CRI A v [] AR) as CRI.
    pose proof (wrI A W) as CI.
    (first [ pose proof ((rk_stats A v [] AR)) as dR_65; dex3 dR_65 as statv rf rfd; dand4 dR_65 as RFR RFDR STA TRF | pose proof ((rk_stats A v [] AR)) as dR_65; dand7 dR_65 as statv rf rfd RFR RFDR STA TRF | destruct (rk_stats A v [] AR) as (statv & rf & rfd & RFR & RFDR & STA & TRF) ]).
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; clear; lia).
    (first [ pose proof ((rk_line A v [] AR CI kQuarantineBatchClass C24)) as dR_66; dex1 dR_66 as ks; dand7 dR_66 as LKS KSM KSF KLE KRG KND LINE | pose proof ((rk_line A v [] AR CI kQuarantineBatchClass C24)) as dR_66; dand8 dR_66 as ks LKS KSM KSF KLE KRG KND LINE | destruct (rk_line A v [] AR CI kQuarantineBatchClass C24) as (ks & LKS & KSM & KSF & KLE & KRG & KND & LINE) ]).
    destruct RC as [RAR RTMP RCH RME RMO RCUR]. cbn [rc_cur] in RCUR. (first [ dand3 RCUR as RENT RBAT RBSH | destruct RCUR as (RENT & RBAT & RBSH) ]).
    pose proof (head_in A _ _ more W L') as HIN.
    pose proof (batch_known A v [] AR (BA (ba_idx b0) []) HIN) as [KBR _]. cbn [ba_idx] in KBR.
    pose proof (rk_batch A v [] AR (ba_idx b0) KBR) as BG. cbv zeta in BG. (first [ dand9 BG as BFORM BLO BHI BAL KB0 KBH SEP_bt SEP_bc SEP_br | destruct BG as (BFORM & BLO & BHI & BAL & KB0 & KBH & SEP_bt & SEP_bc & SEP_br) ]).
    (first [ pose proof ((rk_region_facts A v [] AR kQuarantineBatchClass C24)) as dR_69; dand7 dR_69 as RGF1 RGF2 RGF3 RGF4 RGF5 RGF6 RGF7 | destruct (rk_region_facts A v [] AR kQuarantineBatchClass C24) as (RGF1 & RGF2 & RGF3 & RGF4 & RGF5 & RGF6 & RGF7) ]).
    (first [ pose proof ((max_count_range kQuarantineBatchClass C24)) as dR_70; dand3 dR_70 as MCR0 MCE RFR0 | pose proof (max_count_range kQuarantineBatchClass C24) as (MCR0 & MCE & RFR0) ]). set (h := refill_count kQuarantineBatchClass) in *.
    assert (HSH : Z.shiftr (max_count kQuarantineBatchClass) 1 = h) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; clear -MCE; rewrite MCE; rewrite Z.mul_comm, Z_div_mult by lia; reflexivity).
    (first [ pose proof ((rk_region A v [] AR kQuarantineBatchClass (Z.to_nat h) C24 ltac:(rewrite Z2Nat.id by lia; clear -ROOMF MCE; rewrite MCE in ROOMF; replace (2 * h / 2) with h in ROOMF by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity); exact ROOMF))) as dR_71; dex4 dR_71 as na nfs v88 junk; dand8 dR_71 as RMX RNF RMFA RMU RNA RNFS LJ RARR | pose proof ((rk_region A v [] AR kQuarantineBatchClass (Z.to_nat h) C24 ltac:(rewrite Z2Nat.id by lia; clear -ROOMF MCE; rewrite MCE in ROOMF; replace (2 * h / 2) with h in ROOMF by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity); exact ROOMF))) as dR_71; dand12 dR_71 as na nfs v88 junk RMX RNF RMFA RMU RNA RNFS LJ RARR | destruct (rk_region A v [] AR kQuarantineBatchClass (Z.to_nat h) C24 ltac:(rewrite Z2Nat.id by lia; clear -ROOMF MCE; rewrite MCE in ROOMF; replace (2 * h / 2) with h in ROOMF by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity); exact ROOMF)) as (na & nfs & v88 & junk & RMX & RNF & RMFA & RMU & RNA & RNFS & LJ & RARR) ]).
    pose proof (rk_CITV A v [] AR) as CITV.
    (first [ pose proof ((wtR A (proj1 AR))) as dR_72; dand3 dR_72 as WR1 _ _ | destruct (wtR A (proj1 AR)) as (WR1 & _ & _) ]). (first [ pose proof ((WR1 kQuarantineBatchClass C24)) as dR_73; dand12 dR_73 as _ _ _ _ _ _ _ _ _ _ _ CAP | destruct (WR1 kQuarantineBatchClass C24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CAP) ]). cbv zeta in CAP. pose proof (wfr_fa_cap A W kQuarantineBatchClass C24) as [CAPN _].
    pose proof (bv_carved A v [] (ba_idx b0) more AR W L') as CVe.
    pose proof TC as TC'. (first [ dand13 TC' as _ _ _ _ _ Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct TC' as (_ & _ & _ & _ & _ & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    pose proof MCR0 as MCR.
    set (thr := p_thr (a_pl A)) in *. set (sb := a_sb A) in *. set (ri := a_ri A) in *.
    set (b := batch_addr sb b0) in *.
    set (fac_ := free_array_of sb kQuarantineBatchClass) in *.
    set (cntc := Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass)))) in *.
    set (kk := 512 * ba_idx b0).
    set (tn := Z.of_nat (length more)).
    set (nf := Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass)))) in *. set (mfa := rg_mapped_fa (a_reg A kQuarantineBatchClass)) in *.
    set (Ra := ri + 128 * kQuarantineBatchClass) in *.
    assert (TNR : 0 <= tn < 2^64).
    { pose proof (limbo_count_bound A W) as X. rewrite L' in X. cbn [length] in X.
      change (class_size kQuarantineBatchClass) with 8192 in RGF6. unfold tn. clear -X RGF1 RGF2 RGF6. kung_all. lia. }
    pose proof RTMP as TH. unfold tmp_hdr in TH. fold tn in TH.
    assert (RRE : bv_unsigned (wz recycle_ret : word) mod 2 = 0) by (rewrite unsigned_lit; [reflexivity| unfold recycle_ret; clear; lia]).
    set (Q := fun ms' : machine_state => exists (a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 statv' : word) (m' : mem),
           ((more <> [] /\ ms' = MS (head_regs (wz dsp) gp (cl_tp LPA) T s10 s11 (wz dorec_nextpc) tn a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 (wz b) s6' s7' s8' s9') F (wz dorec_head) fc None m' (seg_rom rsegs)
             /\ rw_cells rsegs m' dsp (dorec_fr thr scr) /\ stk rsegs m' lo dsp)
            \/ (more = [] /\ ms' = MS (mkR (wz recycle_ret) (wz (dsp + 112)) gp (cl_tp LPA) t0 t1 t2 (wz QINST) (wz (thr + 80)) (wz 0) a1 a2 a3 a4 a5 a6 a7
                                        xs2 (wz stkobj) (wz (thr + 208)) xs5 (wz (2^20)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (wz recycle_ret)) fc None m' (seg_rom rsegs)
             /\ stk rsegs m' lo (dsp + 112))) /\
           tmp_hdr sb m' T more /\
           rw_cells rsegs m' (thr + 208 + 80 * kQuarantineBatchClass) [C4 (wz (max_count kQuarantineBatchClass - h + 1)); C4 (wz (max_count kQuarantineBatchClass)); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat (max_count kQuarantineBatchClass - h)) (wz kk)))] /\
           rw_cells rsegs m' (thr + 208 + 2576) [C8 statv'] /\
           rw_cells rsegs m' Ra [C8 (wz 0)] /\ rw_cells rsegs m' (Ra + 16) [C8 (wz (nf + h))] /\ rw_cells rsegs m' (Ra + 24) [C8 (wz mfa)] /\
           rw_cells rsegs m' (Ra + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] /\
           u32arr rsegs m' (fac_ + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (max_count kQuarantineBatchClass - h)) ks)) /\
           munch [(dsp - 320, dsp); (thr + 208 + 80 * kQuarantineBatchClass, thr + 208 + 80 * kQuarantineBatchClass + 80); (thr + 208 + 2576, thr + 208 + 2584);
                  (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 80, Ra + 88); (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h)] v m' /\
           wmono rsegs v m' /\ mem_inv rsegs m').
    unfold blk_cfgG. fold sb. fold b.
    eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR A) pa_wxR _ (pa_eager A) Q _ md TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (batch_free_drainfast gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b scr
                (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                pa_tsd (p_ctx (a_pl A)) thr sb ri)
        with (kb := kk) (tn := tn) (maxc := max_count kQuarantineBatchClass) (ks := ks) (statv := statv)
             (tf := match more with [] => 0 | b' :: _ => batch_addr sb b' end)
             (tl := match more with [] => 0 | _ :: _ => batch_addr sb (last more (BA 0 [])) end)
             (ts := q_bytes more) (nf := nf) (mfa := mfa) (junk := junk) (nfs := nfs) (v88 := v88).
      all: rewrite ?HSH.
      all: try assumption.
      all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
      all: try assumption.
      all: first [ assumption | reflexivity
                 | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                 | unfold pa_tsd; clear; lia
                 | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                 | clear -SBRI RHI; lia
                 | unfold kk; clear -KB0 KBH; lia
                 | clear -MCR; lia
                 | clear -MCE RFR0; unfold h; lia
                 | rewrite LJ; clear; rewrite Z2Nat.id by lia || idtac; lia
                 | unfold nf; clear; lia
                 | clear -RGF5 CAPN RFR0; unfold nf, mfa, h in *; kung_all; lia
                 | clear -ROOMF MCE RFR0; unfold nf, mfa, h in *; lia
                 | rewrite <- FULL at 1; exact LINE
                 | clear -RGF3; unfold mfa; kung_all; lia
                 | exact TH
                 | intros NE a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' DF' TC' LN' ST' RX' RNF' RMFA' RNFS' ARR' MUN WM' MI' STK';
                   apply evt_done; subst Q; first [ hotw_ex16 a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' | exists a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', statv', m' ];
                   split; [left; split; [unfold tn in NE; clear -NE; intros E; apply NE; rewrite E; reflexivity| split; [reflexivity| exact (conj DF' STK')]]|];
                   exact (conj TC' (conj LN' (conj ST' (conj RX' (conj RNF' (conj RMFA' (conj RNFS' (conj ARR' (conj MUN (conj WM' MI'))))))))))
                 | intros EQ a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' DF' TC' LN' ST' RX' RNF' RMFA' RNFS' ARR' MUN WM' MI' STK';
                   apply evt_done; subst Q; first [ hotw_ex16 a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' | exists a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', statv', m' ];
                   split; [right; split; [unfold tn in EQ; clear -EQ; destruct more; [reflexivity| cbn in EQ; lia]| split; [reflexivity| exact STK']]|];
                   exact (conj TC' (conj LN' (conj ST' (conj RX' (conj RNF' (conj RMFA' (conj RNFS' (conj ARR' (conj MUN (conj WM' MI'))))))))))
                 | match goal with |- ?g => idtac "UNSOLVED:" g end ]. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex16 HQ as a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m'; dand12 HQ as CASE TC' LN' ST' RX' RNF' RMFA' RNFS' ARR' MUN WM' MI' | dand28 HQ as a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' m' CASE TC' LN' ST' RX' RNF' RMFA' RNFS' ARR' MUN WM' MI' | destruct HQ as (a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t0'' & t1'' & t2'' & t3'' & t4'' & t5'' & t6'' & statv' & m' & CASE & TC' & LN' & ST' & RX' & RNF' & RMFA' & RNFS' & ARR' & MUN & WM' & MI') ]).
    assert (MSE : exists regs pcw, msr' = MS regs F pcw fc None m' (seg_rom rsegs)) by (destruct CASE as [(_ & -> & _)|(_ & -> & _)]; eexists _, _; reflexivity).
    (first [ dex2 MSE as regs pcw | dand3 MSE as regs pcw MSE | destruct MSE as (regs & pcw & MSE) ]). rewrite MSE in Hcl |- *. rewrite unrestrict_MS. cbn [ms_mem] in Hcl. cbn [ms_mem].
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m m') = m').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NNR _ _ a WM'); [exact H1| lia]. }
    (* [comment removed for export] *)
    set (hN := Z.to_nat h) in *.
    set (out := drain_out (pk_chunks (a_cache A kQuarantineBatchClass)) hN).
    set (cache' := recp_cache (a_cache A) kQuarantineBatchClass (ba_idx b0)).
    set (reg' := recp_reg (a_reg A) (a_cache A) kQuarantineBatchClass (ba_idx b0) mfa).
    set (A' := recA' A reg' cache' more).
    assert (RGC : reg' kQuarantineBatchClass = reg_return (a_reg A kQuarantineBatchClass) out mfa).
    { unfold reg', recp_reg, reg_set, cache_push_list. fold cntc. rewrite FULL, Z.eqb_refl, Z.eqb_refl. cbn [snd].
      replace (max_count kQuarantineBatchClass / 2) with h by (clear -MCE RFR0; unfold h in *; lia). reflexivity. }
    assert (RGO : forall c', c' <> kQuarantineBatchClass -> reg' c' = a_reg A c').
    { intros c' NE. unfold reg', recp_reg, reg_set. fold cntc. rewrite FULL, Z.eqb_refl. destruct (Z.eqb_spec c' kQuarantineBatchClass); [exfalso; exact (NE e)| reflexivity]. }
    assert (CAE : pk_chunks (cache' kQuarantineBatchClass) = drain_keep (pk_chunks (a_cache A kQuarantineBatchClass)) hN ++ [ba_idx b0]).
    { unfold cache', recp_cache, cache_set, cache_push_list. rewrite Z.eqb_refl. fold cntc. rewrite FULL, Z.eqb_refl. cbn [fst pk_chunks].
      replace (max_count kQuarantineBatchClass / 2) with h by (clear -MCE RFR0; unfold h in *; lia). reflexivity. }
    assert (CAO : forall c', c' <> kQuarantineBatchClass -> cache' c' = a_cache A c').
    { intros c' NE. unfold cache', recp_cache, cache_set. destruct (Z.eqb_spec c' kQuarantineBatchClass); [exfalso; exact (NE e)| reflexivity]. }
    assert (EXT : same_ext (a_reg A) reg').
    { intros c0. destruct (Z.eq_dec c0 kQuarantineBatchClass) as [->|NE]; [rewrite RGC, reg_return_mapped_user, reg_return_mapped_fa; split; reflexivity| rewrite (RGO c0 NE); split; reflexivity]. }
    pose proof (su_hull A reg' cache' more EXT) as HULL. pose proof (su_lhull A reg' cache' more EXT) as LHULL.   (* [comment removed for export] *)
    pose proof (su_eager A reg' cache' more EXT) as EAGER.
    change (mkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with A' in HULL, LHULL, EAGER.
    assert (HLEN : (hN <= length (pk_chunks (a_cache A kQuarantineBatchClass)))%nat) by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
    assert (OUTL : length out = hN) by (unfold out; apply drain_out_length; exact HLEN).
    (* [comment removed for export] *)
    set (Wn := fun a => dsp - 320 <= a < dsp).
    set (SHP := fun a : Z => False).
    assert (MU : forall a, 0 <= a < 2^64 -> ~ rp_foot A kQuarantineBatchClass (ba_idx b0) reg' Wn SHP a -> m' (wz a) = v (wz a)).
    { intros a Ha NF. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha; lia). unfold rp_foot in NF. rewrite RGC, reg_return_mapped_fa in NF. subst Wn SHP. cbv beta in NF.
      cbn [outside]. unfold thr, cntc, Ra, ri, fac_, nf, mfa, sb in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NF.
      - left. exact X.
      - do 3 right; left. exact X.
      - do 4 right; left. clear -X. lia.
      - do 5 right; left. exact X.
      - do 6 right; left. clear -X. lia.
      - do 6 right; left. clear -X. lia.
      - do 7 right; left. unfold h in *. clear -X ROOMF MCE RFR0. lia. }
    (* [comment removed for export] *)
    assert (W' : WFR A').
    { pose proof (WFR_batch A (ba_idx b0) mfa more W L') as X. apply X. intros _. unfold nf, mfa, h in *. clear -ROOMF RGF3 RGF4 CAP KBR RGF6 RGF1.
      split; [exact ROOMF|]. split; [lia|]. split; [lia|]. split; [exact RGF4|]. split; [exact CAP|]. intros MU0. change (class_size kQuarantineBatchClass) with 8192 in RGF6. nia. }
    assert (WNH : forall a, Wn a -> alloc_ceiling <= a) by (subst Wn; cbv beta; intros a Ha; clear -Ha CEIL LOW; lia).
    assert (SHPW : forall a, SHP a -> sh b <= a < sh b + class_size kQuarantineBatchClass / 8) by (subst SHP; cbv beta; intros a []).
    pose proof (bv_ne_live A v [] (ba_idx b0) more AR W L') as NE_live.
    pose proof (bv_ne_batch A (ba_idx b0) more W L') as NEB.
    pose proof (bv_ne_rest A v [] (ba_idx b0) more AR W L') as NE_rest.
    pose proof (bv_ne_limbo A v [] (ba_idx b0) more AR W L') as NEL.
    (* [comment removed for export] *)
    assert (DISJ : forall a l, 0 < l ->
             (Ra + 32 <= a /\ a + l <= Ra + 80) \/ (Ra + 96 <= a /\ a + l <= Ra + 128) \/ (fac_ <= a /\ a + l <= fac_ + 4 * nf) \/ (T <= a /\ a + l <= uspd) ->
             disjoint_from [(dsp - 320, dsp); (thr + 208 + 80 * kQuarantineBatchClass, thr + 208 + 80 * kQuarantineBatchClass + 80); (thr + 208 + 2576, thr + 208 + 2584);
                            (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 80, Ra + 88); (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h)] a l).
    { intros a l Hl Ha. unfold thr, ri, sb, fac_, Ra, nf, mfa in *. cbn [disjoint_from].
      (first [ pose proof ((rk_region_facts A v [] AR kQuarantineBatchClass C24)) as dR_77; dand6 dR_77 as _ _ RG3 _ RG5 _ | pose proof (rk_region_facts A v [] AR kQuarantineBatchClass C24) as (_ & _ & RG3 & _ & RG5 & _) ]).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
      all: first [ clear -Ha Hl C24 SBRI RLO RHI CEIL LOW CE SPR; kung_all; lia
                 | clear -Ha Hl SP1 C24; unfold apart in SP1; lia
                 | clear -Ha Hl SP4 C24 RG3 SBRI; unfold apart, free_array_of in *; kung_all; lia
                 | clear -Ha Hl PTC CEIL LOW C24; lia
                 | clear -Ha Hl C24 SBRI RHI RG3 CEIL LOW; unfold free_array_of in *; kung_all; lia
                 | clear -Ha Hl RFR0; unfold h; lia
                 | clear -Ha Hl C24 SBRI RHI RG3 RG5 ROOMF MCE RFR0 CEIL LOW SBLO; unfold h, free_array_of in *; kung_all; lia
                 | clear -Ha Hl SP1 SP4 C24 RG3 RG5 ROOMF MCE RFR0 SBRI; unfold apart, h, free_array_of in *; kung_all; lia ]. }
    assert (OUT : forall a, (Ra + 32 <= a < Ra + 80 \/ Ra + 96 <= a < Ra + 128 \/ fac_ <= a < fac_ + 4 * nf \/ T <= a < uspd) ->
             outside [(dsp - 320, dsp); (thr + 208 + 80 * kQuarantineBatchClass, thr + 208 + 80 * kQuarantineBatchClass + 80); (thr + 208 + 2576, thr + 208 + 2584);
                      (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 80, Ra + 88); (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h)] a).
    { intros a Ha. apply (disjoint_outside _ a 1); [| clear; lia]. apply DISJ; [clear; lia|]. clear -Ha. lia. }
    assert (P_mx : u64_at rsegs m' (ri + 128 * kQuarantineBatchClass) 0) by (apply u64_of_rw; [clear; lia| exact RX']).
    (* [comment removed for export] *)
    assert (KSE : firstn (length (pk_chunks (a_cache A kQuarantineBatchClass))) ks = map (fun k0 => wz (k0 * class_size kQuarantineBatchClass / kCompactPtrScale)) (pk_chunks (a_cache A kQuarantineBatchClass))) by exact KSF.
    assert (OUTW : firstn (Z.to_nat h) (skipn (Z.to_nat (max_count kQuarantineBatchClass - h)) ks) = map (fun k0 => wz (k0 * class_size kQuarantineBatchClass / kCompactPtrScale)) out).
    { unfold out, drain_out. fold hN. replace (Z.to_nat (max_count kQuarantineBatchClass - h)) with (length (pk_chunks (a_cache A kQuarantineBatchClass)) - hN)%nat by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
      rewrite firstn_skipn_comm. replace (length (pk_chunks (a_cache A kQuarantineBatchClass)) - hN + hN)%nat with (length (pk_chunks (a_cache A kQuarantineBatchClass))) by (clear -HLEN; lia).
      rewrite KSE, skipn_map. reflexivity. }
    assert (P_regc : region_repr_ LPA sb (reg' kQuarantineBatchClass) m' kQuarantineBatchClass).
    { rewrite RGC. pose proof (ar_regions _ _ _ _ _ (proj2 AR) kQuarantineBatchClass C24) as RR0. change (a_sb A) with sb in RR0.
      (first [ pose proof ((rk_region_facts A v [] AR kQuarantineBatchClass C24)) as dR_78; dand6 dR_78 as _ _ RG3 _ RG5 _ | pose proof (rk_region_facts A v [] AR kQuarantineBatchClass C24) as (_ & _ & RG3 & _ & RG5 & _) ]).
      apply (region_return_of_cells v m' sb (a_reg A kQuarantineBatchClass) kQuarantineBatchClass out (wz (bv_unsigned nfs + h)) v88 C24 RR0).
      - rewrite OUTL. unfold hN, nf in *. clear -RG3 RG5 CAPN RFR0. kung_all. lia.
      - clear -RG3. kung_all. lia.
      - intros a Ha. rewrite RIA in Ha. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha C24 RLO RHI CE; kung_all; lia). apply OUT. left. unfold Ra. clear -Ha. lia.
      - intros a Ha. rewrite RIA in Ha. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha C24 RLO RHI CE; kung_all; lia). apply OUT. right; left. unfold Ra. clear -Ha. lia.
      - intros a Ha. rewrite FAE in Ha. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha C24 RG3 RG5 SBLO SBRI RHI CE; unfold free_array_of in *; kung_all; lia). apply OUT. right; right; left. unfold fac_, nf. clear -Ha. lia.
      - intros a Ha Hv. rewrite FAE in Ha. apply NN; [| right| | exact Hv]; clear -Ha C24 RG3 SBLO SBRI RHI CE; unfold free_array_of in *; kung_all; lia.
      - intros a Ha Hv. rewrite RBE in Ha. apply NN; [| right| | exact Hv]; clear -Ha C24 RGF2 SBLO SBRI RHI CE; kung_all; lia.
      - rewrite RIA, OUTL. unfold hN. rewrite Z2Nat.id by (clear -RFR0; unfold h; lia). fold nf. unfold Ra, ri in RNF'. exact RNF'.
      - rewrite RIA. unfold Ra, ri, mfa in RMFA'. exact RMFA'.
      - rewrite RIA. unfold Ra, ri in RNFS'. exact RNFS'.
      - rewrite FAE, <- OUTW. fold nf. unfold fac_, sb in ARR'. exact ARR'. }
    (* [comment removed for export] *)
    assert (KKE : forall k', k' * class_size kQuarantineBatchClass / kCompactPtrScale = 512 * k').
    { intros k'. change (class_size kQuarantineBatchClass) with 8192. unfold kCompactPtrScale. replace (k' * 8192) with (512 * k' * 16) by (clear; lia). rewrite Z.div_mul by (clear; lia). reflexivity. }
    assert (ENC : forall k', In k' (pk_chunks (a_cache A kQuarantineBatchClass)) \/ k' = ba_idx b0 -> 0 <= k' * class_size kQuarantineBatchClass / kCompactPtrScale < 2^32).
    { intros k' Hk'. assert (KR' : 0 <= k' < carved_count A kQuarantineBatchClass) by (destruct Hk' as [Hk'| ->]; [exact (KRG k' Hk')| exact KBR]).
      rewrite KKE. change (class_size kQuarantineBatchClass) with 8192 in RGF6. clear -KR' RGF6 RGF1 RGF2. kung_all. lia. }
    assert (ENT : forall i0 k', nth_error (drain_keep (pk_chunks (a_cache A kQuarantineBatchClass)) hN ++ [ba_idx b0]) i0 = Some k' ->
              nth_error (upd ks (Z.to_nat (max_count kQuarantineBatchClass - h)) (wz kk)) i0 = Some (wz (k' * class_size kQuarantineBatchClass / kCompactPtrScale)) /\ 0 <= k' * class_size kQuarantineBatchClass / kCompactPtrScale < 2^32).
    { assert (KL : length (drain_keep (pk_chunks (a_cache A kQuarantineBatchClass)) hN) = (length (pk_chunks (a_cache A kQuarantineBatchClass)) - hN)%nat) by (apply drain_keep_length; exact HLEN).
      assert (MH : Z.to_nat (max_count kQuarantineBatchClass - h) = (length (pk_chunks (a_cache A kQuarantineBatchClass)) - hN)%nat) by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
      intros i0 k' Hk'. destruct (Nat.lt_ge_cases i0 (length (pk_chunks (a_cache A kQuarantineBatchClass)) - hN)) as [LT|GE].
      - rewrite nth_error_app1 in Hk' by (rewrite KL; exact LT). unfold drain_keep in Hk'. rewrite nth_error_firstn in Hk'.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A kQuarantineBatchClass)) - hN)); [| exfalso; clear -LT H; lia].
        split; [| apply ENC; left; eapply nth_error_In; exact Hk'].
        rewrite nth_error_upd_other by (rewrite MH; clear -LT; lia).
        pose proof (f_equal (fun l => nth_error l i0) KSF) as E. cbv beta in E. rewrite nth_error_firstn in E.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A kQuarantineBatchClass)))); [| exfalso; clear -LT H0; lia]. rewrite E, nth_error_map, Hk'. reflexivity.
      - rewrite nth_error_app2 in Hk' by (rewrite KL; exact GE). rewrite KL in Hk'. destruct (i0 - (length (pk_chunks (a_cache A kQuarantineBatchClass)) - hN))%nat as [|x] eqn:EQ; cbn in Hk'; [injection Hk' as <-| destruct x; discriminate].
        assert (i0 = (length (pk_chunks (a_cache A kQuarantineBatchClass)) - hN)%nat) by (clear -GE EQ; lia). subst i0. split; [| apply ENC; right; reflexivity].
        rewrite MH. rewrite nth_error_upd_same by (rewrite LKS; unfold hN, cntc in *; clear -FULL MCR RFR0; lia). rewrite KKE. reflexivity. }
    pose proof LN' as LNx.
    replace (max_count kQuarantineBatchClass - h + 1) with (Z.of_nat (length (drain_keep (pk_chunks (a_cache A kQuarantineBatchClass)) hN ++ [ba_idx b0]))) in LNx
      by (rewrite length_app, (drain_keep_length _ _ HLEN); cbn [length]; unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
    pose proof (line_of_cells m' (thr + 208 + 80 * kQuarantineBatchClass) kQuarantineBatchClass (upd ks (Z.to_nat (max_count kQuarantineBatchClass - h)) (wz kk)) (drain_keep (pk_chunks (a_cache A kQuarantineBatchClass)) hN ++ [ba_idx b0]) (a_cache_inited A) C24 CI
                  ltac:(rewrite upd_length; exact LKS) ltac:(rewrite length_app, (drain_keep_length _ _ HLEN); cbn [length]; unfold hN, cntc in *; clear -FULL MCE RFR0 MCR; lia) ENT
                  LNx) as P_linec.
    rewrite <- CAE in P_linec.
    replace (thr + 208 + 80 * kQuarantineBatchClass) with (thr + off_th_per_class kQuarantineBatchClass) in P_linec by (unfold off_th_per_class, off_th_alloc_cache, kPerClassSize; clear; lia).
    assert (MFA8 : rg_mapped_fa (a_reg A kQuarantineBatchClass) mod 8 = 0) by (apply (mod0_down _ kFreeArrayMapSize 8); [exists (2^15); reflexivity| exact RGF4]).
    assert (R'E : rg_mapped_user (reg' kQuarantineBatchClass) = rg_mapped_user (a_reg A kQuarantineBatchClass) /\ rg_allocated_user (reg' kQuarantineBatchClass) = rg_allocated_user (a_reg A kQuarantineBatchClass) /\
                  rg_mapped_fa (a_reg A kQuarantineBatchClass) <= rg_mapped_fa (reg' kQuarantineBatchClass) /\ rg_mapped_fa (reg' kQuarantineBatchClass) <= kFreeArraySize /\ rg_mapped_fa (reg' kQuarantineBatchClass) mod 8 = 0).
    { rewrite RGC, reg_return_mapped_user, reg_return_allocated, reg_return_mapped_fa. unfold mfa. clear -RGF3 MFA8. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; try lia. }
    (first [ pose proof ((chunk_shadow A v [] AR kQuarantineBatchClass (ba_idx b0) C24 KBR)) as dR_79; dand4 dR_79 as CS1 CS2 CS3 CS4 | pose proof (chunk_shadow A v [] AR kQuarantineBatchClass (ba_idx b0) C24 KBR) as (CS1 & CS2 & CS3 & CS4) ]). fold sb in CS1, CS2, CS3, CS4.
    change (chunk_addr sb kQuarantineBatchClass (ba_idx b0)) with b in CS1, CS2, CS3, CS4.
    assert (AGSH : forall z, sh b <= z < sh b + class_size kQuarantineBatchClass / 8 -> m' (wz z) = v (wz z)).
    { intros z Hz. apply (AG_shadow_maps A v m' [] kQuarantineBatchClass (ba_idx b0) reg' AR Wn WNH SHP SHPW CVe R'E MU z).
      - exact (heap_shadow_rangeT A z (WFT_of_WFR A W) (CS2 z Hz)).
      - intros [].
      - rewrite RGC, reg_return_mapped_fa. unfold mfa. rewrite Z.sub_diag. clear. intros X. cbn in X. lia. }
    assert (VSH : bytes_at rsegs m' (sh b) (pshadow_free kQuarantineBatchClass)).
    { eapply bytes_at_xfer; [exact RBSH|]. intros z Hz. apply AGSH. unfold pshadow_free, fa8 in Hz. rewrite repeat_length, Z2Nat.id in Hz by (change (class_size kQuarantineBatchClass) with 8192; clear; lia). exact Hz. }
    assert (P_fash : bytes_at rsegs m' (sh (fac_ + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_fa (reg' kQuarantineBatchClass) - mfa) / 8)))).
    { rewrite RGC, reg_return_mapped_fa. rewrite Z.sub_diag. cbn. apply bytes_at_nil. unfold sh, fac_, mfa, free_array_of. clear -C24 SBLO SBRI RHI RGF3 CE. kung_all. lia. }
    pose proof (recp_arepr A v m' [] kQuarantineBatchClass (ba_idx b0) more reg' cache' AR W Wn WNH SHP SHPW CVe NE_live NEB NE_rest
                  CAO ltac:(intros k' Hk'; rewrite CAE in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|[<-|[]]]; [left; exact (proj2 (drain_in_iff _ hN k') (or_introl Hk'))| right; reflexivity])
                  RGO R'E ltac:(intros k' Hk'; rewrite RGC, reg_return_free in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|Hk']; [left; exact Hk'| right; exact (proj2 (drain_in_iff _ hN k') (or_intror Hk'))])
                  MU NN P_mx P_regc P_linec VSH P_fash more) as AR'.
    change (recA' _ _ _ _) with A' in AR'.
    (* [comment removed for export] *)
    assert (INmore : forall b' e', In b' more -> In e' (ba_entries b') -> In e' ([] ++ q_entries more)).
    { intros b' e' Hb' He'. cbn [app]. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He'). }
    assert (RCM : forall cur, match cur with None => True | _ => False end -> rcells A' m' T cur more).
    { intros cur Hcur. constructor.
      - exact AR'.
      - exact TC'.
      - apply (tmp_chain_xfer A v m' [] kQuarantineBatchClass (ba_idx b0) (ba_idx b0) _ more reg' cache' AR W L' Wn WNH SHP SHPW CVe NEB R'E MU more); [intros b' Hb'; exact Hb'| exact RCH].
      - intros b' e' Hb' He'. apply (lentry_xfer A v m' [] kQuarantineBatchClass (ba_idx b0) reg' AR Wn WNH SHP SHPW CVe R'E MU NN e').
        + apply (limbo_in A (ba_idx b0) _ more W L'). exact (INmore b' e' Hb' He').
        + apply NEL. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He').
        + exact (RME b' e' Hb' He').
      - intros b' Hb'. destruct (RMO b' Hb') as [LB SHB]. pose proof (more_in A (ba_idx b0) _ more W L' b' Hb') as Hb2.
        destruct (lbatch_xfer A v m' [] kQuarantineBatchClass (ba_idx b0) reg' cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b') (ba_entries b') 0%nat (batch_bytes b')
                    (batch_carved A v [] AR b' Hb2) (NEB b' (or_intror Hb')) (proj2 (batch_known A v [] AR b' Hb2)) LB) as [LB' SHB'].
        split; [exact LB'| exact (SHB' SHB)].
      - destruct cur; [destruct Hcur| exact I]. }
    (* [comment removed for export] *)
    assert (RIM : forall cur, match cur with None => True | _ => False end -> a_qlimbo A' = limbo_of cur more -> RINV A' (munrestrict (hidc (pa_hull A)) m m') md' T cur more).
    { intros cur Hcur Hl. constructor.
      - exact W'.
      - exact Hl.
      - rewrite HULL, VIEW. exact (RCM cur Hcur).
      - apply (su_hidden A reg' cache' more EXT m m' HID).
        + intros z Gz Hz Vz. destruct Gz as [SMz _]. unfold in_shadow_maps in SMz. apply NN; [clear -SMz; kung_all; lia| right; clear -SMz; kung_all; lia| clear -SMz; kung_all; lia| exact Vz].
        + intros z Gz Hz NHS. destruct Gz as [SMz _]. apply (AG_shadow_maps A v m' [] kQuarantineBatchClass (ba_idx b0) reg' AR Wn WNH SHP SHPW CVe R'E MU z SMz).
          * intros [].
          * rewrite RGC, reg_return_mapped_fa. unfold mfa. rewrite Z.sub_diag. clear. intros X. cbn in X. lia.
        + intros z Hz Hc Vz. apply NN; [clear -Hz; kung_all; lia| right; clear -Hz; kung_all; lia| clear -Hz; kung_all; lia| exact Vz].
      - exact EXTRA.
      - first [ exact (aledger_sbm _ _ _ _ md md' Hsame LED)
              | (* [comment removed for export] *)
                refine (aledger_reg _ _ _ _ _ _ (fun c0 _ => EXT c0) (aledger_sbm _ _ _ _ md md' Hsame LED)) ].
      - rewrite HULL, LHULL, EAGER. exact HI'.   (* [comment removed for export] *)
      - (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT' _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT' & _) ]). rewrite HLT'. exact HLT.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact COV.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact CEI. }
    (* [comment removed for export] *)
    assert (PF' : put_frame (p_thr (a_pl A)) m').
    { unfold put_frameG in *. eapply rw_cells_transport; [exact PF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
    assert (RF' : rec_frame (p_thr (a_pl A)) m').
    { unfold rec_frameG in *. eapply rw_cells_transport; [exact RF| exact MUN| exact WM'|]. apply DISJ; [cbn; clear; lia|]. right; right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
    assert (SMT : mapped m' T (uspd - T)).
    { intros q Hq. pose proof TC' as TM'. unfold tmp_hdr in TM'.
      destruct (Z.lt_ge_cases (T + q) (T + 32)) as [C3|C3].
      { pose proof (rw_mapped_hi m' _ _ TM' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        exact (M q ltac:(clear -Hq C3; lia)). }
      destruct (Z.lt_ge_cases (T + q) (T + 80)) as [C4|C4].
      { pose proof (rw_mapped_hi m' _ _ RF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (T + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (T + q - (T + 32))) with (T + q) in M by (clear; lia). exact M. }
      pose proof (rw_mapped_hi m' _ _ PF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
      specialize (M (T + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (T + q - (uspd + -80))) with (T + q) in M by (clear; lia). exact M. }
    assert (SM' : mapped m' lo (uspd - lo)).
    { intros q Hq. destruct (Z.lt_ge_cases (lo + q) T) as [C1|C1]; [| specialize (SMT (lo + q - T) ltac:(clear -C1 Hq; lia)); replace (T + (lo + q - T)) with (lo + q) in SMT by (clear; lia); exact SMT].
      destruct CASE as [(_ & _ & DF' & STK')|(_ & _ & STK')].
      - destruct (Z.lt_ge_cases (lo + q) dsp) as [C0|C0].
        { exact (stk_mapped_pa m' lo dsp lo (dsp - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C0; lia)). }
        pose proof (rw_mapped_hi m' _ _ DF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
        specialize (M (lo + q - dsp) ltac:(clear -C0 C1; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M.
      - exact (stk_mapped_pa m' lo (dsp + 112) lo (dsp + 112 - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
    (* [comment removed for export] *)
    assert (RS : rstep (pa_owned A) (pa_owned A') lo uspd v m').
    { unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      - intros a Ha NO NO' NW. apply MU; [exact Ha|]. intros Fa.
        destruct (foot_owned A v [] kQuarantineBatchClass (ba_idx b0) reg' AR Wn SHP SHPW CVe NE_live R'E a Fa) as [X|[X|[X|X]]].
        + apply NW. subst Wn. cbv beta in X. clear -X LOW CEIL. lia.
        + exact (NO X).
        + rewrite RGC, reg_return_mapped_fa in X. unfold mfa in X. clear -X. lia.
        + rewrite RGC, reg_return_mapped_fa in X. unfold mfa in X. rewrite Z.sub_diag in X. clear -X. cbn in X. lia.
      - intros a Ha NI Hv. right. apply NN; [clear -Ha; lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| clear -Ha; lia| exact Hv].
      - exact SM'.
      - intros a Ha O'. left. exact (proj1 (su_owned A reg' cache' more EXT a) O').
      - intros a Ha O NO'. exfalso. apply NO'. exact (proj2 (su_owned A reg' cache' more EXT a) O). }
    assert (NZ : a_reg A kQuarantineBatchClass <> region_zero).
    { intros E. pose proof KBR as X. unfold carved_count, carved_count_ in X. rewrite E in X. cbn in X. clear -X.
      pose proof (Z.div_0_l (class_size kQuarantineBatchClass)). rewrite Zdiv_0_l in X. lia. }
    pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A v md A' m' md' HIST (WFT_of_WFR A W) (WFT_of_WFR A' W') CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                  (fun c0 NE V0 => su_virgin A reg' cache' more kQuarantineBatchClass c0 NZ RGO CAO V0)
                  (wamd_sbm md md' Hsame HLT) RS) as HIST'.
    (* [comment removed for export] *)
    destruct CASE as [(NE & E & DF' & STK')|(EQ & E & STK')]; rewrite MSE in E; injection E as Er Ep; subst regs pcw.
    - assert (CU' : CUR A' (munrestrict (hidc (pa_hull A)) m m') md' None more scr).
      { constructor; rewrite ?HULL, ?VIEW.
        - apply RIM; [exact I| reflexivity].
        - exact HIST'.
        - exact MI'.
        - exact STK'.
        - exact PF'.
        - exact RF'.
        - exact DF'.
        - exact I.
        - unfold A', recA'. cbn [a_qlimbo]. rewrite L' in QB. rewrite q_bytes_cons, batch_bytes_ebytes in QB. cbn [ba_entries] in QB. change (ebytes []) with 0 in QB. unfold kQuarantineBatchBytes in QB. clear -QB. lia. }
      specialize (KM A' (munrestrict (hidc (pa_hull A)) m m') md' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' NE CU' eq_refl).
      unfold head_cfgG in KM. fold tn in KM. exact KM.
    - subst more.
      assert (XCU' : XCUR A' (munrestrict (hidc (pa_hull A)) m m') md').
      { constructor; rewrite ?HULL, ?VIEW.
        - apply RIM; [exact I| reflexivity].
        - exact HIST'.
        - exact MI'.
        - replace T with (dsp + 112) by (clear; lia). exact STK'.
        - exact PF'.
        - exact RF'. }
      specialize (K0 A' (munrestrict (hidc (pa_hull A)) m m') md' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' eq_refl XCU' eq_refl).
      unfold exit_cfgG in K0. cbn [a_pl] in K0. fold thr in K0. replace (dsp + 112) with T by (clear; lia). exact K0.
  Qed.

End RIter.
End AFreeRI1.


Module AFreeRL.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSnjd ARtSrgm AMalmys ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQWf2 AQPart ACover AFreeR AFreeR2 AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2 AFreeRP AFreeRQ AFreeRU AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AWrapKit ACoresk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRQ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE.AFreeRI1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve,
                        kQuarantineBatchBytes, kQuarantineBatchCount in *.

Section RL.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Variables (rac spd gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet).
  (* [comment removed for export] *)
  Variables (xs2 xs5 : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HI47 : hi <= 2^47.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis VB : forall a, newblk p n0 a -> a < alloc_ceiling.
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation T := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation v0 := (aview_of (pa_hull A0) m0).

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation put_frame := (put_frameG rac spd s0 s1 s2 s3 s4 s5 s6 stkobj).
  #[warnings="-notation-for-abbreviation"] Local Notation rec_frame := (rec_frameG spd stkobj xs2).
  #[warnings="-notation-for-abbreviation"] Local Notation dorec_fr := (dorec_frG s7 s8 s9 stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation CUR := (CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p n0 stkobj lo hi xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation it_cfg := (it_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation head_cfg := (head_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation blk_cfg := (blk_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation exit_cfg := (exit_cfgG spd gp s7 s8 s9 s10 s11 F fc stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation XCUR := (XCURG rac spd s0 s1 s2 s3 s4 s5 s6 A0 m0 md0 p n0 stkobj lo hi xs2).


  (* [comment removed for export] *)
  Definition KBLK (A : AState) (b0 : batch) (more : list batch) (scr : list byte) : Prop :=
    forall (A' : AState) (m' : mem) (md' : Model) (ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s6' s7' s8' s9' : word),
      CUR A' m' md' (Some (b0, length (ba_entries b0))) more scr -> a_pl A' = a_pl A ->
      srealizes rsegs (blk_cfg A' m' md' b0 ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s6' s7' s8' s9') TS.
  Definition KEXIT (A : AState) : Prop :=
    forall (A' : AState) (m' : mem) (md' : Model) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      XCUR A' m' md' -> a_pl A' = a_pl A ->
      srealizes rsegs (exit_cfg A' m' md' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) TS.
  Definition KHEAD (A : AState) (more : list batch) (scr : list byte) : Prop :=
    forall (A' : AState) (m' : mem) (md' : Model) (ra a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s4' s6' s7' s8' s9' : word),
      more <> [] -> CUR A' m' md' None more scr -> a_pl A' = a_pl A ->
      srealizes rsegs (head_cfg A' m' md' more ra a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s4' s6' s7' s8' s9') TS.
  (* [comment removed for export] *)
  Definition KMORE (A : AState) (b0 : batch) (i : nat) (more : list batch) (scr : list byte) : Prop :=
    forall (A' : AState) (m' : mem) (md' : Model) (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word),
      (S i < length (ba_entries b0))%nat -> CUR A' m' md' (Some (b0, S i)) more scr -> a_pl A' = a_pl A ->
      srealizes rsegs (it_cfg A' m' md' b0 (Z.of_nat (S i)) dorec_callblk (wz dorec_retpc) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6) TS.
  Definition KDONE (A : AState) (b0 : batch) (i : nat) (more : list batch) (scr : list byte) : Prop :=
    forall (A' : AState) (m' : mem) (md' : Model) (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word),
      (S i = length (ba_entries b0))%nat -> CUR A' m' md' (Some (b0, S i)) more scr -> a_pl A' = a_pl A ->
      srealizes rsegs (it_cfg A' m' md' b0 (Z.of_nat (S i)) dorec_batchblk (wz dorec_retpc) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6) TS.

  (* [comment removed for export] *)
  Hypothesis STEP_PDM : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (c k n : Z),
    CUR A m md (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChP (CP c k)) n) ->
    Z.of_nat (length (pk_chunks (a_cache A c))) = max_count c ->
    rg_mapped_fa (a_reg A c) < 4 * (Z.of_nat (length (rg_free (a_reg A c))) + max_count c / 2) ->
    KMORE A b0 i more scr -> KDONE A b0 i more scr ->
    srealizes rsegs (it_cfg A m md b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Hypothesis STEP_SEC : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (s : chunkS) (n : Z),
    CUR A m md (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChS s) n) ->
    KMORE A b0 i more scr -> KDONE A b0 i more scr ->
    srealizes rsegs (it_cfg A m md b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Hypothesis STEP_BDM : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word),
    CUR A m md (Some (b0, length (ba_entries b0))) more scr ->
    Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass))) = max_count kQuarantineBatchClass ->
    rg_mapped_fa (a_reg A kQuarantineBatchClass) < 4 * (Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) + max_count kQuarantineBatchClass / 2) ->
    KHEAD A more scr -> KEXIT A ->
    srealizes rsegs (blk_cfg A m md b0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9') TS.

  (* [comment removed for export] *)
  Lemma cur_line_facts : forall A m md b0 i more scr c k n,
    CUR A m md (Some (b0, i)) more scr -> nth_error (ba_entries b0) i = Some (QE (ChP (CP c k)) n) ->
    1 <= c <= 30 /\ Z.of_nat (length (pk_chunks (a_cache A c))) <= max_count c.
  Proof.
    intros A m md b0 i more scr c k n CU NTH. destruct CU as [RI _ _ _ _ _ _ _ _]. destruct RI as [W L RC _ _ _ _ _ _ _].
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC)) as AR.
    assert (L' : a_qlimbo A = BA (ba_idx b0) (QE (ChP (CP c k)) n :: skipn (S i) (ba_entries b0)) :: more).
    { rewrite L. unfold limbo_of. rewrite (skipn_cons_nth (ba_entries b0) i _ NTH). reflexivity. }
    pose proof (ev_carved A v0 [] c k n _ _ _ ltac:(exact AR) W L') as [CR _] || pose proof (ev_carved A _ [] c k n _ _ _ AR W L') as [CR _].
    split; [exact CR|]. destruct (wrC A W) as (C1 & _ & _). exact (proj1 (C1 c ltac:(clear -CR; lia))).
  Qed.
  Lemma cur_batch_line : forall A m md cur more scr, CUR A m md cur more scr ->
    Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass))) <= max_count kQuarantineBatchClass.
  Proof.
    intros A m md cur more scr CU. destruct CU as [RI _ _ _ _ _ _ _ _]. destruct RI as [W _ _ _ _ _ _ _ _ _].
    destruct (wrC A W) as (C1 & _ & _). exact (proj1 (C1 kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia))).
  Qed.

  (* [comment removed for export] *)
  Lemma rblk : forall A m md b0 more scr (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word),
    CUR A m md (Some (b0, length (ba_entries b0))) more scr -> KHEAD A more scr -> KEXIT A ->
    srealizes rsegs (blk_cfg A m md b0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9') TS.
  Proof.
    intros A m md b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CU KH KX.
    pose proof (cur_batch_line A m md _ more scr CU) as LE.
    destruct (Z.lt_ge_cases (Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass)))) (max_count kQuarantineBatchClass)) as [ROOM|GE].
    - exact (step_batch_push rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 CEIL LOW SPHI HI47 SPA VB
               A m md b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CU ROOM (fun A' m' md' a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 => KH A' m' md' _ a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 _ _ _ _ _) (fun A' m' md' a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 _ X PL => KX A' m' md' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 X PL)).
    - assert (FULL : Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass))) = max_count kQuarantineBatchClass) by (clear -LE GE; lia).
      destruct (Z.le_gt_cases (4 * (Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) + max_count kQuarantineBatchClass / 2)) (rg_mapped_fa (a_reg A kQuarantineBatchClass))) as [RF|NRF].
      + exact (step_batch_drainfast rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 CEIL LOW SPHI HI47 SPA VB
                 A m md b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CU FULL RF (fun A' m' md' a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 => KH A' m' md' _ a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 _ _ _ _ _) (fun A' m' md' a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 _ X PL => KX A' m' md' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 X PL)).
      + exact (STEP_BDM A m md b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CU FULL NRF KH KX).
  Qed.

  (* [comment removed for export] *)
  Lemma rbatch : forall (n : nat) A m md b0 (i : nat) more scr (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word),
    (length (ba_entries b0) - i <= n)%nat -> (i < length (ba_entries b0))%nat ->
    CUR A m md (Some (b0, i)) more scr -> KBLK A b0 more scr ->
    srealizes rsegs (it_cfg A m md b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Proof.
    induction n as [|n IH]; intros A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' LEFT LT CU KB; [exfalso; clear -LEFT LT; lia|].
    destruct (nth_error (ba_entries b0) i) as [[ch n1]|] eqn:NTH; [| exfalso; apply nth_error_None in NTH; clear -NTH LT; lia].
    assert (KM : KMORE A b0 i more scr).
    { intros A' m' md' a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 LT' CU' PL. apply (IH A' m' md' b0 (S i) more scr); [clear -LEFT LT'; lia| exact LT'| exact CU'|].
      intros A'' m'' md'' ra b0' b1' b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 s6' s7' s8' s9' CU'' PL'. apply (KB A'' m'' md''); [exact CU''| exact (eq_trans PL' PL)]. }
    assert (KD : KDONE A b0 i more scr).
    { intros A' m' md' a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 EQ CU' PL. rewrite EQ in CU' |- *. apply (KB A' m' md'); [exact CU'| exact PL]. }
    destruct ch as [[c k]|s].
    - pose proof (cur_line_facts A m md b0 i more scr c k n1 CU NTH) as [CR LE].
      destruct (Z.lt_ge_cases (Z.of_nat (length (pk_chunks (a_cache A c)))) (max_count c)) as [ROOM|GE].
      + exact (step_prim_push rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 CEIL LOW SPHI HI47 SPA VB
                 A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n1 CU NTH ROOM KM KD).
      + assert (FULL : Z.of_nat (length (pk_chunks (a_cache A c))) = max_count c) by (clear -LE GE; lia).
        destruct (Z.le_gt_cases (4 * (Z.of_nat (length (rg_free (a_reg A c))) + max_count c / 2)) (rg_mapped_fa (a_reg A c))) as [RF|NRF].
        * exact (step_prim_drainfast rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 CEIL LOW SPHI HI47 SPA VB
                   A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n1 CU NTH FULL RF KM KD).
        * exact (STEP_PDM A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n1 CU NTH FULL NRF KM KD).
    - exact (STEP_SEC A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n1 CU NTH KM KD).
  Qed.

  (* [comment removed for export] *)
  Theorem rloop : forall (n : nat) A m md more scr (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' : word),
    (length more <= n)%nat -> more <> [] ->
    CUR A m md None more scr -> KEXIT A ->
    srealizes rsegs (head_cfg A m md more ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9') TS.
  Proof.
    induction n as [|n IH]; intros A m md more scr ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' LEFT NE CU KX.
    { exfalso. destruct more; [exact (NE eq_refl)| cbn in LEFT; clear -LEFT; lia]. }
    destruct more as [|b0 more]; [exfalso; exact (NE eq_refl)|]. cbn [length] in LEFT.
    (* [comment removed for export] *)
    assert (KHX : forall A', a_pl A' = a_pl A -> KHEAD A' more scr /\ KEXIT A').
    { intros A' PL. split.
      - intros A'' m'' md'' ra a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 u4 u6 u7 u8 u9 NE' CU'' PL'.
        apply (IH A'' m'' md'' more scr); [clear -LEFT; lia| exact NE'| exact CU''|].
        intros A3 m3 md3 t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c X3 PL3. apply (KX A3 m3 md3); [exact X3| exact (eq_trans PL3 (eq_trans PL' PL))].
      - intros A3 m3 md3 t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c X3 PL3. apply (KX A3 m3 md3); [exact X3| exact (eq_trans PL3 PL)]. }
    apply (step_pop rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 CEIL LOW SPHI HI47 SPA VB
             A m md b0 more scr ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' CU).
    - (* [comment removed for export] *)
      intros m' md' a0'' a1'' NEB CU'. apply (rbatch (length (ba_entries b0)) A m' md' b0 0 more scr); [clear; lia| destruct (ba_entries b0); [exfalso; exact (NEB eq_refl)| cbn; clear; lia]| exact CU'|].
      intros A'' m'' md'' ra b0' b1' b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 u6' u7' u8' u9' CU'' PL''.
      destruct (KHX A'' PL'') as [KH' KX']. exact (rblk A'' m'' md'' b0 more scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CU'' KH' KX').
    - (* [comment removed for export] *)
      intros m' md' a0'' a1'' EB CU'. destruct (KHX A eq_refl) as [KH' KX'].
      assert (CUb : CUR A m' md' (Some (b0, length (ba_entries b0))) more scr) by (rewrite EB; exact CU').
      exact (rblk A m' md' b0 more scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CUb KH' KX').
  Qed.
End RL.
End AFreeRL.


Module AFreeRN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSnjd AMalmys AFreeB1 AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AQPart ATransp ATranspR AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve,
                        kQuarantineBatchBytes, kQuarantineBatchCount in *.

(* [comment removed for export] *)
Lemma batches_repr_suffix : forall (m : mem) sb (l1 l2 : list batch), batches_repr LPA m sb (l1 ++ l2) -> batches_repr LPA m sb l2.
Proof. induction l1 as [|b l1 IH]; intros l2 H; [exact H|]. cbn [batches_repr app] in H. (first [ dand6 H as _ _ _ _ _ H | destruct H as (_ & _ & _ & _ & _ & H) ]). exact (IH l2 H). Qed.

(* [comment removed for export] *)
Lemma batches_repr_cells : forall (m : mem) sb (l : list batch) i b, batches_repr LPA m sb l -> nth_error l i = Some b ->
  let a := batch_addr sb b in
  u64_at rsegs m (a + off_qb_next) (match nth_error l (S i) with None => 0 | Some b' => batch_addr sb b' end) /\
  u64_at rsegs m (a + off_qb_size) (batch_bytes b) /\
  u64_at rsegs m (a + off_qb_count) (Z.of_nat (length (ba_entries b))) /\
  (forall j e, nth_error (ba_entries b) j = Some e -> u64_at rsegs m (a + off_qb_batch (Z.of_nat j)) (hdr_of sb (qe_chunk e) (qe_n e))) /\
  mapped m a kQuarantineBatchBytes.
Proof.
  intros m sb l. induction l as [|b0 l IH]; intros i b BR Hn; [destruct i; discriminate|].
  cbn [batches_repr] in BR. (first [ dand6 BR as X1 X2 X3 X4 M BR | destruct BR as (X1 & X2 & X3 & X4 & M & BR) ]).
  destruct i as [|i].
  - cbn in Hn. injection Hn as ->. cbv zeta. cbn [nth_error]. split; [destruct l; exact X1|]. exact (conj X2 (conj X3 (conj X4 M))).
  - cbn in Hn. exact (IH i b BR Hn).
Qed.


(* [comment removed for export] *)
Lemma rw_cells_of_u64x3 : forall (m : mem) a x y z, 0 <= a -> a + 24 <= 2^64 -> mapped m a 24 ->
  u64_at rsegs m a x -> u64_at rsegs m (a + 8) y -> u64_at rsegs m (a + 16) z -> rw_cells rsegs m a [C8 (wz x); C8 (wz y); C8 (wz z)].
Proof.
  intros m a x y z H0 H1 M Bx By Bz. apply ro_rw; [| cbn; exact M].
  unfold ro_cells, cells_at. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply length_le8|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_app. split; [exact Bx|]. rewrite length_le8. apply bytes_at_app. split; [exact By|]. rewrite length_le8.
  replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) by lia. exact Bz.
Qed.

Section Enter.
Context {Clg : Ceiling}.
  Variables (A : AState) (v v' : mem) (R rest : list batch).
  #[local] Notation rm := (al_instance AL_pasan + off_q_recycle_mutex).
  (* [comment removed for export] *)
  Hypothesis ART : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [rm] A v.
  Hypothesis QT : a_qthread A = [].
  Hypothesis SPL : a_qglobal A = R ++ rest.
  Let WT : WFT A. Proof. exact (proj1 ART). Qed.
  Let RR : @arepr _ DepotRepL LPA AL_pasan [rm] A v. Proof. exact (proj2 ART). Qed.
  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation ri := (a_ri A).
  #[local] Notation Iq := 728408.

  (* [comment removed for export] *)
  Variable Wn : Z -> Prop.
  Hypothesis WNH : forall a, Wn a -> alloc_ceiling <= a.
  Definition en_foot (a : Z) : Prop :=
       Wn a
    \/ (Iq + off_q_cache_mutex <= a < Iq + off_q_cache_mutex + 4)
    \/ (Iq + off_q_cache_list_size <= a < Iq + off_q_cache_list_size + 32)
    \/ (exists b, In b R /\ batch_addr sb b <= a < batch_addr sb b + 8).
  Hypothesis MU : forall a, 0 <= a < 2^64 -> ~ en_foot a -> v' (wz a) = v (wz a).
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.
  (* [comment removed for export] *)
  Hypothesis LCK' : rw_cells rsegs v' (Iq + off_q_cache_mutex) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)].
  Hypothesis HDR' : rw_cells rsegs v' (Iq + off_q_cache_list_size)
                      [C8 (wz (Z.of_nat (length rest))); C8 (wz (match rest with [] => 0 | b :: _ => batch_addr sb b end));
                       C8 (wz (match rest with [] => 0 | _ :: _ => batch_addr sb (last rest (BA 0 [])) end)); C8 (wz (q_bytes rest))].
  Hypothesis CUT : forall j b, nth_error R j = Some b ->
    u64_at rsegs v' (batch_addr sb b) (match nth_error R (S j) with None => 0 | Some b' => batch_addr sb b' end).

  (* [comment removed for export] *)
  Definition enA : AState := recA2 A R rest.

  (* [comment removed for export] *)
  Lemma R_in : forall b, In b R -> In b (a_qthread A ++ (a_qglobal A ++ a_qlimbo A)).
  Proof. intros b Hb. apply in_or_app. right. apply in_or_app. left. rewrite SPL. apply in_or_app. left. exact Hb. Qed.
  Lemma rest_in : forall b, In b rest -> In b (a_qthread A ++ (a_qglobal A ++ a_qlimbo A)).
  Proof. intros b Hb. apply in_or_app. right. apply in_or_app. left. rewrite SPL. apply in_or_app. right. exact Hb. Qed.
  (* [comment removed for export] *)
  Lemma R_in2 : forall b, In b R -> In b (a_qthread A ++ a_qglobal A).
  Proof. intros b Hb. apply in_or_app. right. rewrite SPL. apply in_or_app. left. exact Hb. Qed.

  (* [comment removed for export] *)
  Lemma AGx : forall a, 0 <= a < alloc_ceiling ->
    ~ (Iq + off_q_cache_mutex <= a < Iq + off_q_cache_mutex + 4) -> ~ (Iq + off_q_cache_list_size <= a < Iq + off_q_cache_list_size + 32) ->
    ~ (exists b, In b R /\ batch_addr sb b <= a < batch_addr sb b + 8) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha N1 N2 N3. pose proof alloc_ceiling_val as CE. apply MU; [clear -Ha CE; lia|]. intros [F|[F|[F|F]]].
    - pose proof (WNH a F). clear -H Ha. lia.
    - exact (N1 F).
    - exact (N2 F).
    - exact (N3 F).
  Qed.
  (* [comment removed for export] *)
  Lemma R_range : forall b, In b R -> kHighMemBeg <= batch_addr sb b /\ batch_addr sb b + kQuarantineBatchBytes <= alloc_ceiling /\
    a_b6 A <= batch_addr sb b /\ batch_addr sb b + kQuarantineBatchBytes <= a_b6 A + kSpaceReserve /\
    region_beg sb kQuarantineBatchClass <= batch_addr sb b /\ batch_addr sb b + kQuarantineBatchBytes <= region_beg sb kQuarantineBatchClass + rg_allocated_user (a_reg A kQuarantineBatchClass).
  Proof.
    intros b Hb. (first [ pose proof ((batch_range A v [rm] ART b (R_in b Hb))) as dR_3; dand3 dR_3 as B1 B2 _ | pose proof (batch_range A v [rm] ART b (R_in b Hb)) as (B1 & B2 & _) ]).
    (first [ pose proof ((carved_prim_where A v [rm] ART kQuarantineBatchClass (ba_idx b) (batch_carved A v [rm] ART b (R_in b Hb)))) as dR_4; dand9 dR_4 as W1 W2 W3 W4 W5 W6 W7 W8 _ | pose proof (carved_prim_where A v [rm] ART kQuarantineBatchClass (ba_idx b) (batch_carved A v [rm] ART b (R_in b Hb))) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & _) ]).
    unfold batch_addr in *. change (class_size kQuarantineBatchClass) with 8192 in W2. unfold kQuarantineBatchBytes in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; clear -W1 W2 W3 W4 W5 W6 W7 W8; kung_all; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma AGz : forall a, 0 <= a < alloc_ceiling ->
    ~ (0x10000 <= a < 0x60a000) \/ (~ (Iq + off_q_cache_mutex <= a < Iq + off_q_cache_mutex + 4) /\ ~ (Iq + off_q_cache_list_size <= a < Iq + off_q_cache_list_size + 32)) ->
    ~ (region_beg sb kQuarantineBatchClass <= a < region_beg sb kQuarantineBatchClass + rg_allocated_user (a_reg A kQuarantineBatchClass)) ->
    v' (wz a) = v (wz a).
  Proof.
    intros a Ha NI NZ. apply AGx; [exact Ha| | |].
    - destruct NI as [NI|[N1 N2]]; [| exact N1]. intros X. apply NI. unfold off_q_cache_mutex in X. clear -X. lia.
    - destruct NI as [NI|[N1 N2]]; [| exact N2]. intros X. apply NI. unfold off_q_cache_list_size in X. clear -X. lia.
    - ((first [ intro dR_53; dex1 dR_53 as b; destruct dR_53 as [Hb X] | intro dR_53; dand3 dR_53 as b Hb X | intros (b & Hb & X) ])). apply NZ. (first [ pose proof ((R_range b Hb)) as dR_5; dand6 dR_5 as _ _ _ _ R5 R6 | pose proof (R_range b Hb) as (_ & _ & _ & _ & R5 & R6) ]). unfold kQuarantineBatchBytes in R6. clear -X R5 R6. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> ~ (Iq + off_q_cache_mutex <= a < Iq + off_q_cache_mutex + 4) ->
    ~ (Iq + off_q_cache_list_size <= a < Iq + off_q_cache_list_size + 32) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha N1 N2. pose proof alloc_ceiling_val as CE. pose proof (R_range) as RR0. apply AGx; [clear -Ha CE; lia| exact N1| exact N2|].
    ((first [ intro dR_54; dex1 dR_54 as b; destruct dR_54 as [Hb X] | intro dR_54; dand3 dR_54 as b Hb X | intros (b & Hb & X) ])). pose proof (R_range b Hb) as (R1 & _). clear -X R1 Ha. kung_all. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma AG_app : forall i b s a, nth_error (big_maps A) i = Some (b, s) -> (i <> 0)%nat -> app_rangeA AL_pasan b s ->
    b <= a < b + s -> v' (wz a) = v (wz a).
  Proof.
    intros i b s a Hn H0 AP Ha. (first [ pose proof ((app_facts _ _ AP)) as dR_6; dand5 dR_6 as F1 F2 F3 F4 F5 | pose proof (app_facts _ _ AP) as (F1 & F2 & F3 & F4 & F5) ]).
    pose proof (bm_nth_fixed A) as (E0 & _). pose proof (bm_sepT A i 0 _ _ _ _ WT Hn E0 H0) as D.
    apply AGx; [clear -Ha F1 F3; lia| | |].
    - intros X. unfold off_q_cache_mutex in X. clear -X Ha F4. lia.
    - intros X. unfold off_q_cache_list_size in X. clear -X Ha F4. lia.
    - ((first [ intro dR_55; dex1 dR_55 as b'; destruct dR_55 as [Hb' X] | intro dR_55; dand3 dR_55 as b' Hb' X | intros (b' & Hb' & X) ])). (first [ pose proof ((R_range b' Hb')) as dR_7; dand5 dR_7 as _ _ R3 R4 _ | pose proof (R_range b' Hb') as (_ & _ & R3 & R4 & _) ]). unfold a_b6 in *. clear -X R3 R4 D Ha. kung_all. lia.
  Qed.
  Let PF := place_factsT A WT.
  Lemma AGthr : forall a, thr <= a < thr + 4096 -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_8; dand6 dR_8 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]). pose proof PF as ((X & _) & _). exact (AG_app 4 _ _ a E4 ltac:(lia) X Ha). Qed.
  Lemma AGctx : forall a, p_ctx P <= a < p_ctx P + 0x10000 -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_9; dand7 dR_9 as _ _ _ _ _ E5 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & E5 & _) ]). pose proof PF as (_ & (X & _) & _). exact (AG_app 5 _ _ a E5 ltac:(lia) X Ha). Qed.
  Lemma AGdtls : forall a, p_dtls P <= a < p_dtls P + 4096 -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_10; dand15 dR_10 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ E14 | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E14) ]). pose proof PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (X & _) & _). exact (AG_app 14 _ _ a E14 ltac:(lia) X Ha). Qed.
  Lemma AGfs : forall a, a_fs A <= a < a_fs A + kFakeStackBytes -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_11; dand8 dR_11 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]). pose proof (place_fsT A WT) as (X & _). exact (AG_app 6 _ _ a E6 ltac:(lia) X Ha). Qed.
  Lemma AGn0 : forall a, p_nodes0 P <= a < p_nodes0 P + kDepotNodesBlock -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_12; dand9 dR_12 as _ _ _ _ _ _ _ E7 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & E7 & _) ]). pose proof PF as (_ & _ & (X & _) & _). exact (AG_app 7 _ _ a E7 ltac:(lia) X Ha). Qed.
  Lemma AGf0 : forall a, p_frames0 P <= a < p_frames0 P + kStackStoreBlockBytes -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_13; dand10 dR_13 as _ _ _ _ _ _ _ _ E8 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & E8 & _) ]). pose proof PF as (_ & _ & _ & (X & _) & _). exact (AG_app 8 _ _ a E8 ltac:(lia) X Ha). Qed.
  Lemma AGpa : forall a, p_pa P <= a < p_pa P + kPtrArrayReserve -> v' (wz a) = v (wz a).
  Proof. intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_14; dand3 dR_14 as _ E1 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _) ]). pose proof PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (X & _) & _). exact (AG_app 1 _ _ a E1 ltac:(lia) X Ha). Qed.
  Lemma AGhs : forall a, in_shadow_maps a -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha. pose proof alloc_ceiling_val as CE. pose proof (region_piece_boundsT A kQuarantineBatchClass WT ltac:(unfold kQuarantineBatchClass; lia)) as (Q1 & _). cbv zeta in Q1.
    unfold in_shadow_maps in Ha. apply AGz; [clear -Ha CE; kung_all; lia| left; clear -Ha; kung_all; lia| clear -Ha Q1; kung_all; lia].
  Qed.
  Lemma AGsec : forall sc a, In sc (sr_chunks (a_sec A)) -> cs_map sc <= a < cs_map sc + map_size (cs_n sc) -> v' (wz a) = v (wz a).
  Proof.
    intros sc a Hin Ha. destruct (In_nth_error' _ _ Hin) as [j Hj]. pose proof (bm_nth_sec A _ _ Hj) as E.
    (first [ pose proof ((sec_chunk_boundsT A sc WT Hin)) as dR_15; dand4 dR_15 as _ _ AP _ | pose proof (sec_chunk_boundsT A sc WT Hin) as (_ & _ & AP & _) ]). exact (AG_app (15 + j) _ _ a E ltac:(lia) AP Ha).
  Qed.
  (* [comment removed for export] *)
  Lemma AGchunk : forall ch, carved A ch -> (forall b, In b R -> ch <> ChP (CP kQuarantineBatchClass (ba_idx b))) ->
    forall a, chunk_lo sb ch <= a < chunk_hi sb ch -> v' (wz a) = v (wz a).
  Proof.
    intros ch CV NE a Ha. (first [ pose proof ((carved_range A v [rm] ART ch CV)) as dR_16; dand3 dR_16 as C1 C2 _ | pose proof (carved_range A v [rm] ART ch CV) as (C1 & C2 & _) ]). pose proof alloc_ceiling_val as CE.
    apply AGx; [clear -Ha C1 C2; lia| | |].
    - intros X. unfold off_q_cache_mutex in X. clear -X Ha C1. lia.
    - intros X. unfold off_q_cache_list_size in X. clear -X Ha C1. lia.
    - ((first [ intro dR_56; dex1 dR_56 as b; destruct dR_56 as [Hb X] | intro dR_56; dand3 dR_56 as b Hb X | intros (b & Hb & X) ])). pose proof (carved_disjoint A v [rm] ART ch _ CV (batch_carved A v [rm] ART b (R_in b Hb)) (NE b Hb)) as D.
      cbn [chunk_lo chunk_hi alloc_beg] in D. unfold batch_addr in X. change (class_size kQuarantineBatchClass) with 8192 in D. clear -X D Ha. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma AGbatchR : forall b a, In b R -> batch_addr sb b + 8 <= a < batch_addr sb b + kQuarantineBatchBytes -> v' (wz a) = v (wz a).
  Proof.
    intros b a Hb Ha. (first [ pose proof ((R_range b Hb)) as dR_17; dand3 dR_17 as R1 R2 _ | pose proof (R_range b Hb) as (R1 & R2 & _) ]). pose proof alloc_ceiling_val as CE.
    apply AGx; [clear -Ha R1 R2; kung_all; lia| | |].
    - intros X. unfold off_q_cache_mutex in X. clear -X Ha R1. kung_all. lia.
    - intros X. unfold off_q_cache_list_size in X. clear -X Ha R1. kung_all. lia.
    - ((first [ intro dR_57; dex1 dR_57 as b'; destruct dR_57 as [Hb' X] | intro dR_57; dand3 dR_57 as b' Hb' X | intros (b' & Hb' & X) ])). destruct (classic (ba_idx b' = ba_idx b)) as [E|NE].
      + unfold batch_addr in X, Ha. rewrite E in X. clear -X Ha. lia.
      + pose proof (carved_disjoint A v [rm] ART _ _ (batch_carved A v [rm] ART b' (R_in b' Hb')) (batch_carved A v [rm] ART b (R_in b Hb))
                      ltac:(intros EE; injection EE as EE; exact (NE EE))) as D.
        cbn [chunk_lo chunk_hi alloc_beg] in D. unfold batch_addr in X, Ha. change (class_size kQuarantineBatchClass) with 8192 in D. unfold kQuarantineBatchBytes in Ha.
        clear -X D Ha. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma LCKb : u8_at rsegs v' (Iq + off_q_cache_mutex) 0 /\ u8_at rsegs v' (Iq + off_q_recycle_mutex) 0 /\ bytes_at rsegs v' 0xb20ca [Z_to_bv 8 0; Z_to_bv 8 0].
  Proof.
    destruct LCK' as [[_ B] _]. cbn [cells_bytes cbytes app] in B. change (le2 (wz 0)) with [Z_to_bv 8 0; Z_to_bv 8 0] in B. unfold off_q_cache_mutex, off_q_recycle_mutex in *.
    apply (bytes_at_app _ v' _ [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) in B as [U1 B].
    apply (bytes_at_app _ v' _ [Z_to_bv 8 0] [Z_to_bv 8 0; Z_to_bv 8 0]) in B as [U2 PD]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in U2, PD.
    exact (conj U1 (conj U2 PD)).
  Qed.
  Lemma QPD' : bytes_at rsegs v' 0xb20ca [Z_to_bv 8 0; Z_to_bv 8 0].
  Proof. exact (proj2 (proj2 LCKb)). Qed.

  Lemma consts_P' : consts_repr_ LPA AL_pasan P v'.
  Proof.
    pose proof alloc_ceiling_val as CE. pose proof (place_factsT A WT) as PF0. cbv zeta in PF0.
    apply (consts_P2 A v v' [rm] ART).
    - intros cst Hin. destruct (decide (cst = q_pad)) as [->|NQ]; [right; exact QPD'|]. left. intros a Ha.
      cbn [cl_consts LPA] in Hin.
      pose proof (proj1 (forallb_forall _ _) pa_consts_noia cst Hin) as NI. cbv beta in NI.
      apply Bool.orb_true_iff in NI. destruct NI as [NI|NI]; [| apply bool_decide_eq_true in NI; exfalso; exact (NQ NI)].
      apply Bool.orb_true_iff in NI. destruct NI as [NI|NI].
      2: { apply bool_decide_eq_true in NI. subst cst. cbn in Ha. apply AGimg; unfold off_q_cache_mutex, off_q_cache_list_size; clear -Ha; lia. }
      unfold const_noia in NI. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in NI. destruct NI as (((_ & _) & N3) & N4).
      destruct (pa_consts_where cst a Hin Ha) as [Sh|[IS|St]].
      + pose proof (asI_shared_where a Sh) as X. cbn [cl_rw_lo cl_image_hi LPA] in X.
        apply AGimg; [clear -X; lia| unfold off_q_cache_mutex; clear -Ha N3; lia| unfold off_q_cache_list_size; clear -Ha N4; lia].
      + apply AGhs. unfold pa_image_shadow in IS. unfold in_shadow_maps, sh in *. left. clear -IS. kung_all. lia.
      + cbn [cl_static LPA] in St. unfold pa_static in St.
        apply AGimg; [clear -St; lia| unfold off_q_cache_mutex; clear -Ha N3; lia| unfold off_q_cache_list_size; clear -Ha N4; lia].
    - intros a Sh. cbn [cl_shared LPA] in Sh. unfold pa_shared in Sh. apply AGimg; unfold off_q_cache_mutex, off_q_cache_list_size; clear -Sh; lia.
    - intros a H. apply AGimg; unfold cfoot_stat in H; cbn [al_instance al_kHighMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache al_may_return_null
          al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan] in H;
        unfold off_primary_reserved_base, off_primary_reserved_size, off_SpaceBeg, off_release_interval, off_RegionInfo_ptr, off_PremappedHeap, off_sec_page_size,
          off_sec_chunks, off_sec_ptr_array_base, off_sec_ptr_array_size, off_q_max_size, off_q_min_size, off_q_max_cache_size, off_max_user_malloc,
          off_min_redzone, off_max_redzone, off_alloc_dealloc_mismatch, off_q_cache_mutex, off_q_cache_list_size in *; clear -H; lia.
    - intros a H. unfold cfoot_thr, off_th_context, off_th_stack_top, off_th_stack_bottom, off_th_stack_switching, off_th_unwinding in H. apply AGthr. clear -H. lia.
    - intros a H. unfold cfoot_misc in H. cbn [cl_tp LPA] in H. rewrite unsigned_lit in H by (clear; lia).
      (first [ dand12 PF0 as _ Pctx _ _ _ _ _ _ _ _ Pdt _ | destruct PF0 as (_ & Pctx & _ & _ & _ & _ & _ & _ & _ & _ & Pdt & _) ]).
      destruct H as [H|[H|[H|[H|[H|H]]]]]; first [apply AGctx; clear -H; lia | apply AGimg; unfold off_q_cache_mutex, off_q_cache_list_size; clear -H; lia | apply AGdtls; clear -H; lia].
  Qed.

  Lemma locks_P' : locks_repr_ LPA AL_pasan P [] v'.
  Proof.
    pose proof (ar_locks _ _ _ _ _ RR) as C. unfold locks_repr_ in *. cbv zeta in *. (first [ dand6 C as C0 L1 L2 L3 L4 L5 | destruct C as (C0 & L1 & L2 & L3 & L4 & L5) ]).
    change (al_internal_alloc_inited AL_pasan) with 0x144e48 in *. change (al_instance AL_pasan) with Iq in *.
    (first [ pose proof ((rk_ri A v [rm] ART)) as dR_20; dand4 dR_20 as RIE RLO RHI _ | pose proof (rk_ri A v [rm] ART) as (RIE & RLO & RHI & _) ]). change (a_ri A) with (p_ri P) in RIE, RLO, RHI. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((sb_factsT A WT)) as dR_21; dand5 dR_21 as _ _ _ _ SCE | pose proof (sb_factsT A WT) as (_ & _ & _ & _ & SCE) ]). (first [ pose proof ((region_piece_boundsT A kQuarantineBatchClass WT ltac:(unfold kQuarantineBatchClass; lia))) as dR_22; dand8 dR_22 as _ _ Q3 Q4 _ _ Q7 _ | pose proof (region_piece_boundsT A kQuarantineBatchClass WT ltac:(unfold kQuarantineBatchClass; lia)) as (_ & _ & Q3 & Q4 & _ & _ & Q7 & _) ]). cbv zeta in Q3, Q4, Q7.
    unfold kRegionInfoSize in *.
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y].
      split; (eapply u64_at_agree; [eassumption|]; intros i Hi; apply AGz;
        [ clear -Hi Hc SCE RLO RIE; kung_all; lia | left; clear -Hi Hc RLO RIE; kung_all; lia | clear -Hi Hc Q3 Q4 Q7 RIE; kung_all; lia ]).
    - unfold off_sec_mutex, off_fallback_mutex in *. rewrite !lockb_nil. cbn [lockb existsb Z.eqb orb off_q_cache_mutex off_q_recycle_mutex] in L1, L4, L5.
      (first [ pose proof (LCKb) as dR_23; dand3 dR_23 as B1 B2 _ | pose proof LCKb as (B1 & B2 & _) ]). unfold off_q_cache_mutex, off_q_recycle_mutex in *.
      split; [| split; [exact B1| split; [exact B2| split]]].
      + eapply u8_at_agree; [exact L1|]. apply AGimg; unfold off_q_cache_mutex, off_q_cache_list_size; clear; lia.
      + eapply u8_at_agree; [exact L4|]. apply AGimg; unfold off_q_cache_mutex, off_q_cache_list_size; clear; lia.
      + eapply u8_at_agree; [exact L5|]. apply AGimg; unfold off_q_cache_mutex, off_q_cache_list_size; clear; lia.
  Qed.

  Lemma regions_P' : forall c, 1 <= c <= 30 -> region_repr_ LPA sb (a_reg A c) v' c.
  Proof.
    intros c Hc. apply (region_P A v v' [rm] ART NN c Hc). intros a H. unfold rfoot in H.
    (first [ pose proof ((region_piece_boundsT A c WT Hc)) as dR_24; dand9 dR_24 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 _ | pose proof (region_piece_boundsT A c WT Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & _) ]). cbv zeta in *.
    (first [ pose proof ((region_piece_boundsT A kQuarantineBatchClass WT ltac:(unfold kQuarantineBatchClass; lia))) as dR_25; dand5 dR_25 as _ _ B3 B4 _ | pose proof (region_piece_boundsT A kQuarantineBatchClass WT ltac:(unfold kQuarantineBatchClass; lia)) as (_ & _ & B3 & B4 & _) ]). cbv zeta in B3, B4.
    (first [ pose proof ((rk_ri A v [rm] ART)) as dR_26; dand10 dR_26 as RIE RLO RHI _ _ SBLO _ _ _ RBE | pose proof (rk_ri A v [rm] ART) as (RIE & RLO & RHI & _ & _ & SBLO & _ & _ & _ & RBE) ]).
    unfold region_info_addr, free_array_beg, kRegionInfoSize in H. pose proof alloc_ceiling_val as CE.
    apply AGz.
    - clear -H Hc Q1 Q5 Q6 Q7 Q8. kung_all. lia.
    - left. clear -H Hc Q1 Q5 Q7. kung_all. lia.
    - rewrite (RBE kQuarantineBatchClass). rewrite (RBE c) in H. destruct H as [H|H].
      + clear -H Hc B3 B4 RBE. rewrite (RBE kQuarantineBatchClass) in B4. unfold kQuarantineBatchClass in *. kung_all. lia.
      + destruct (Z.eq_dec c kQuarantineBatchClass) as [->|NE].
        * clear -H B3 B4 RBE. rewrite (RBE kQuarantineBatchClass) in B4. unfold kQuarantineBatchClass in *. kung_all. lia.
        * rewrite (RBE c) in Q6. clear -H Hc NE B3 B4 Q5 Q6 RBE. rewrite (RBE kQuarantineBatchClass) in B4. unfold kQuarantineBatchClass in *. kung_all.
          assert (c + 1 <= 24 \/ 24 + 1 <= c) as [X|X] by lia; nia.
  Qed.

  Lemma cache_P' : cache_repr_ LPA P (a_cache A) (a_cache_inited A) v'.
  Proof.
    apply (cache_P A v v' [rm] ART NN (a_cache A)). intros c' Hc'. apply (cache_line_P A v v' [rm] ART NN (a_cache A) c' Hc' eq_refl).
    intros a Ha. unfold off_th_per_class, off_th_alloc_cache, kPerClassSize in Ha. apply AGthr. clear -Ha Hc'. lia.
  Qed.

  Lemma live_P' : live_repr_ LPA sb (a_livemap A) v'.
  Proof.
    apply (live_sub_P A v v' [rm] ART NN (a_livemap A)); [intros u li Hl; exact Hl|].
    intros u li a Hl Ha. apply (AGchunk (li_chunk li) (known_carved A v [rm] ART _ _ (known_live A v [rm] ART u li Hl))); [| exact Ha].
    intros b Hb. exact (live_not_batch A v [rm] ART u li b Hl (R_in b Hb)).
  Qed.

  Lemma quar_P' : quarantine_repr_ LPA AL_pasan P [] rest v'.
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ RR)) as dR_27; dand3 dR_27 as QTr QG QR | pose proof (ar_quar _ _ _ _ _ RR) as (QTr & QG & QR) ]). rewrite QT in QTr, QR. rewrite SPL in QG, QR. unfold quarantine_repr_. change (p_sb P) with sb in *.
    change (al_instance AL_pasan) with Iq in *. cbn [app] in QR.
    split; [|split].
    - (first [ dand5 QTr as X1 X2 X3 X4 _ | destruct QTr as (X1 & X2 & X3 & X4 & _) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P A v v' (thr + off_th_qcache) [] ltac:(intros a Ha; apply AGthr; unfold off_th_qcache in Ha; clear -Ha; lia) (conj X1 (conj X2 (conj X3 X4))))) as dR_29; dand4 dR_29 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P A v v' (thr + off_th_qcache) [] ltac:(intros a Ha; apply AGthr; unfold off_th_qcache in Ha; clear -Ha; lia) (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      exact (conj Y1 (conj Y2 (conj Y3 (conj Y4 I)))).
    - unfold qcache_repr. destruct HDR' as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      apply bytes_at_app in B as [B0 B]. apply bytes_at_app in B as [B1 B]. apply bytes_at_app in B as [B2 B3]. rewrite !length_le8 in *.
      unfold u64_at. rewrite Z.add_0_r.
      split; [exact B0|]. split; [replace (Iq + off_q_cache_list_size + 8) with (Iq + off_q_cache_list_size + Z.of_nat 8) by (clear; lia); exact B1|].
      split; [replace (Iq + off_q_cache_list_size + 16) with (Iq + off_q_cache_list_size + Z.of_nat 8 + Z.of_nat 8) by (clear; lia); exact B2|].
      split; [replace (Iq + off_q_cache_list_size + 24) with (Iq + off_q_cache_list_size + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by (clear; lia); exact B3|].
      (first [ dand5 QG as _ _ _ _ BR | destruct QG as (_ & _ & _ & _ & BR) ]). apply (batches_P A v v' [rm] ART NN rest); [intros b Hb; exact (rest_in b Hb)| | exact (batches_repr_suffix v sb R rest BR)].
      intros b a Hb Ha. apply (AGchunk (ChP (CP kQuarantineBatchClass (ba_idx b))) (batch_carved A v [rm] ART b (rest_in b Hb))).
      + intros b' Hb' E. injection E as E. pose proof (batches_nodup A v [rm] ART) as ND. rewrite QT, SPL in ND. cbn [app] in ND. rewrite map_app in ND.
        apply (proj1 (list.NoDup_app _ _)) in ND as (ND & _ & _). rewrite map_app in ND.
        apply (NoDup_app_In _ _ (ba_idx b) ND); [apply in_map_iff; exists b'; split; [exact (eq_sym E)| exact Hb']|].
        apply in_map. exact Hb.
      + cbn [chunk_lo chunk_hi alloc_beg]. unfold batch_addr, kQuarantineBatchBytes in Ha. change (class_size kQuarantineBatchClass) with 8192. exact Ha.
    - intros e He. cbn [app] in He. apply (quar_entry_P A v v' [rm] ART NN e); [rewrite QT, SPL; cbn [app]; unfold q_entries in *; rewrite flat_map_app; apply in_or_app; right; exact He|].
      intros a Ha. assert (HeA : In e (q_entries (a_qthread A ++ (a_qglobal A ++ a_qlimbo A)))).
      { rewrite QT, SPL. cbn [app]. unfold q_entries in *. rewrite !flat_map_app. apply in_or_app. left. apply in_or_app. right. exact He. }
      apply (AGchunk (qe_chunk e) (known_carved A v [rm] ART _ _ (known_quar A v [rm] ART e HeA))); [| exact Ha].
      intros b Hb. exact (quar_not_batch A v [rm] ART e b HeA (R_in b Hb)).
  Qed.

  Lemma sec_P' : sec_repr_ LPA AL_pasan P (a_sec A) v'.
  Proof.
    (first [ pose proof ((wtS A WT)) as dR_31; dand4 dR_31 as _ LEN RES _ | destruct (wtS A WT) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. pose proof (place_factsT A WT) as PF0. cbv zeta in PF0.
    (first [ dand13 PF0 as _ _ _ _ _ _ _ _ _ _ _ (Ppa & PpaC & _) _ | destruct PF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Ppa & PpaC & _) & _) ]).
    apply (sec_P A v v' [rm] ART NN).
    - intros a H. apply AGimg; unfold sfoot_stat in H; change (al_instance AL_pasan) with Iq in H;
        unfold off_sec_n_reserved, off_sec_n_chunks, off_sec_chunks_sorted, off_sec_stat_n_allocs, off_global_stats, off_q_cache_mutex, off_q_cache_list_size in *; clear -H; lia.
    - intros a Ha. apply AGpa. clear -Ha LEN RES. kung_all. lia.
    - intros sc a Hin Ha. (first [ pose proof ((sec_chunk_boundsT A sc WT Hin)) as dR_33; dand5 dR_33 as _ _ SB3 SB4 SB5 | pose proof (sec_chunk_boundsT A sc WT Hin) as (_ & _ & SB3 & SB4 & SB5) ]).
      pose proof (needed_size_ge (cs_n sc)) as N1. pose proof (rz_size_range (cs_n sc)) as N2. unfold needed_size2 in SB5.
      apply (AGsec sc a Hin). clear -Ha SB4 SB5 N1 N2. destruct (from_primary (cs_n sc)); unfold kSecondaryHeaderSize, kPageSize in *; lia.
  Qed.

  Lemma depot_P' : depot_repr_ LPA AL_pasan P (a_depot A) v'.
  Proof.
    apply (depot_P A v' (a_depot A) v); [exact (ar_depot _ _ _ _ _ RR)|].
    intros a H. unfold depot_foot in H. cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in H. unfold kDepotNodesL1 in H.
    destruct H as [H|[H|H]]; [apply AGimg; unfold off_q_cache_mutex, off_q_cache_list_size; clear -H; lia| apply AGn0; exact H| apply AGf0; exact H].
  Qed.

  Lemma ia_P' : ia_repr_ LPA AL_pasan (a_ia_inited A) v'.
  Proof.
    apply (ia_P A v v' [rm] ART). intros a H. apply AGimg; unfold iafoot in H; cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pasan] in H;
      unfold off_q_cache_mutex, off_q_cache_list_size; clear -H; lia.
  Qed.

  Lemma shadow_P' : shadow_repr_ LPA sb (a_reg A) (a_cache A) (a_livemap A) [] rest v'.
  Proof.
    pose proof (shadow_P0 A v v' [rm] ART ltac:(intros z Hz; apply AGhs; exact (heap_shadow_rangeT A z WT Hz))) as S. rewrite QT, SPL in S.
    (first [ dand6 S as S1 S2 S3 S4 S5 S6 | destruct S as (S1 & S2 & S3 & S4 & S5 & S6) ]). unfold shadow_repr_.
    split; [| split; [exact S2| split; [| split; [exact S4| split; [exact S5|]]]]].
    - intros c k Hc ST. apply (S1 c k Hc). destruct ST as [ST|[ST|ST]]; [left; exact ST| right; left; exact ST| right; right].
      unfold p_batch_ in *. destruct ST as [E I]. split; [exact E|]. unfold batch_indices_ in *. cbn [app] in *. rewrite map_app. apply in_or_app. right. exact I.
    - intros c k n He. apply S3. cbn [app] in *. unfold q_entries in *. rewrite flat_map_app. apply in_or_app. right. exact He.
    - intros mb n0 n He. apply (S6 mb n0 n). cbn [app] in *. unfold q_entries in *. rewrite flat_map_app. apply in_or_app. right. exact He.
  Qed.

  (* [comment removed for export] *)
  Theorem en_arepr : @arepr _ DepotRepL LPA AL_pasan [] enA v'.
  Proof.
    pose proof (place_factsT A WT) as PF0. cbv zeta in PF0. (first [ dand6 PF0 as _ _ _ _ (Pfs & PfsC & _) _ | destruct PF0 as (_ & _ & _ & _ & (Pfs & PfsC & _) & _) ]).
    unfold enA, recA2. constructor; cbn [a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes a_qlimbo a_scred a_deadsh].
    - exact consts_P'. - exact locks_P'. - exact regions_P'. - exact cache_P'. - exact live_P'. - exact quar_P'. - exact sec_P'. - exact depot_P'. - exact ia_P'.
    - apply (fsbase_P A v v' [rm] ART NN). intros a Ha. apply AGfs. unfold a_fs, kFakeFlagsOffset, kFakeStackBytes in *. clear -Ha. lia.
    - apply (fsptrs_P A v v' [rm] ART). intros a Ha. apply AGfs. unfold a_fs, kFakeFramesOffset, kFakeStackBytes in *. clear -Ha. lia.
    - apply (fsflags_P A v v' [rm] ART). intros a Ha. apply AGfs. unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. clear -Ha. lia.
    - exact (maps_P A v v' [rm] ART NN).
    - exact shadow_P'.
  Qed.

  (* [comment removed for export] *)
  Theorem en_entries : forall b e, In b R -> In e (ba_entries b) -> lentry_cells (a_sb A) v' e.
  Proof.
    intros b e Hb He. (first [ pose proof ((ar_quar _ _ _ _ _ RR)) as dR_36; dand3 dR_36 as _ _ QR | pose proof (ar_quar _ _ _ _ _ RR) as (_ & _ & QR) ]). (first [ pose proof ((ar_shadow _ _ _ _ _ RR)) as dR_37; dand6 dR_37 as _ _ S3 _ _ S6 | pose proof (ar_shadow _ _ _ _ _ RR) as (_ & _ & S3 & _ & _ & S6) ]).
    assert (He2 : In e (q_entries (a_qthread A ++ a_qglobal A))).
    { rewrite QT, SPL. cbn [app]. unfold q_entries. rewrite flat_map_app. apply in_or_app. left. apply in_flat_map. exists b. exact (conj Hb He). }
    assert (HeA : In e (q_entries (a_qthread A ++ (a_qglobal A ++ a_qlimbo A)))) by (apply q_in_big; exact He2).
    pose proof (known_quar A v [rm] ART e HeA) as CL. pose proof (known_carved A v [rm] ART _ _ CL) as CV.
    assert (AG : forall a, chunk_lo sb (qe_chunk e) <= a < chunk_hi sb (qe_chunk e) -> v' (wz a) = v (wz a)).
    { apply (AGchunk (qe_chunk e) CV). intros b' Hb'. exact (quar_not_batch A v [rm] ART e b' HeA (R_in b' Hb')). }
    (first [ pose proof ((quar_entry_P A v v' [rm] ART NN e He2 AG)) as dR_38; dand3 dR_38 as HR J MC | destruct (quar_entry_P A v v' [rm] ART NN e He2 AG) as (HR & J & MC) ]).
    split; [exact HR|]. split; [exact J|]. split; [exact MC|].
    destruct (qe_chunk e) as [[c'' k'']|[mb n1]] eqn:EC.
    - eapply bytes_at_xfer; [apply (S3 c'' k'' (qe_n e)); rewrite <- EC; destruct e; exact He2|]. intros z Hz. apply AGhs.
      unfold known in CL. (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((chunk_shadow A v [rm] ART c'' k'' Hc Hk)) as dR_40; dand3 dR_40 as _ CS2 _ | pose proof (chunk_shadow A v [rm] ART c'' k'' Hc Hk) as (_ & CS2 & _) ]).
      rewrite (pshadow_quar_length c'' (qe_n e)) in Hz by (clear -Hn Hcl; lia). exact (heap_shadow_rangeT A z WT (CS2 z Hz)).
    - unfold known in CL. (first [ dand3 CL as Hin Hn En | destruct CL as (Hin & Hn & En) ]). subst n1.
      eapply bytes_at_xfer; [apply (S6 mb (qe_n e) (qe_n e)); rewrite <- EC; destruct e; exact He2|]. intros z Hz. apply AGhs.
      rewrite (sshadow_quar_length (qe_n e)) in Hz by (clear -Hn; lia).
      (first [ pose proof ((sec_shadow A v [rm] ART (CS mb (qe_n e)) Hin)) as dR_42; dand3 dR_42 as _ SS2 _ | pose proof (sec_shadow A v [rm] ART (CS mb (qe_n e)) Hin) as (_ & SS2 & _) ]). cbn [cs_map cs_n] in SS2. exact (heap_shadow_rangeT A z WT (SS2 z Hz)).
  Qed.

  Theorem en_objs : forall b, In b R ->
    lbatch_cells (a_sb A) v' (batch_addr sb b) (ba_entries b) 0 (batch_bytes b) /\ bytes_at rsegs v' (sh (batch_addr sb b)) (pshadow_free kQuarantineBatchClass).
  Proof.
    intros b Hb. (first [ pose proof ((ar_quar _ _ _ _ _ RR)) as dR_43; dand3 dR_43 as _ QG _ | pose proof (ar_quar _ _ _ _ _ RR) as (_ & QG & _) ]). rewrite SPL in QG. (first [ dand5 QG as _ _ _ _ BR | destruct QG as (_ & _ & _ & _ & BR) ]).
    destruct (In_nth_error' _ _ Hb) as [j Hj].
    (first [ pose proof ((batches_repr_cells v sb (R ++ rest) j b BR ltac:(rewrite nth_error_app1 by (apply nth_error_Some_lt in Hj; exact Hj); exact Hj))) as dR_45; dand5 dR_45 as _ X2 X3 X4 M | pose proof (batches_repr_cells v sb (R ++ rest) j b BR ltac:(rewrite nth_error_app1 by (apply nth_error_Some_lt in Hj; exact Hj); exact Hj)) as (_ & X2 & X3 & X4 & M) ]).
    pose proof (batch_known A v [rm] ART b (R_in b Hb)) as [KB LEN].
    split; [split; [|split]|].
    - intros i e _ He. eapply u64_at_agree; [exact (X4 i e He)|]. intros q Hq. apply (AGbatchR b _ Hb).
      pose proof (nth_error_Some_lt _ _ _ He) as IL. unfold off_qb_batch, kQuarantineBatchBytes, kQuarantineBatchCount in *. clear -Hq IL LEN. lia.
    - eapply u64_at_agree; [exact X2|]. intros q Hq. apply (AGbatchR b _ Hb). unfold off_qb_size, kQuarantineBatchBytes in *. clear -Hq. lia.
    - (first [ pose proof ((R_range b Hb)) as dR_46; dand3 dR_46 as R1 R2 _ | pose proof (R_range b Hb) as (R1 & R2 & _) ]). pose proof alloc_ceiling_val as CE. unfold kQuarantineBatchBytes in *.
      apply (mapped_N v v' NN); [clear -R1; kung_all; lia| right; clear -R1; kung_all; lia| clear -R2 CE; lia| exact M].
    - pose proof (ar_shadow _ _ _ _ _ RR) as (S1 & _). eapply bytes_at_xfer.
      + apply (S1 kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia)). right; right. split; [reflexivity|].
        unfold batch_indices_. apply in_map. exact (R_in2 b Hb).
      + intros z Hz. apply AGhs. (first [ pose proof ((chunk_shadow A v [rm] ART kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia) KB)) as dR_47; dand3 dR_47 as _ CS2 _ | pose proof (chunk_shadow A v [rm] ART kQuarantineBatchClass (ba_idx b) ltac:(unfold kQuarantineBatchClass; lia) KB) as (_ & CS2 & _) ]).
        unfold pshadow_free, fa8 in Hz. rewrite repeat_length, Z2Nat.id in Hz by (change (class_size kQuarantineBatchClass) with 8192; clear; lia).
        exact (heap_shadow_rangeT A z WT (CS2 z Hz)).
  Qed.

  Theorem en_chain : tmp_chain (a_sb A) v' R.
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ RR)) as dR_48; dand3 dR_48 as _ QG _ | pose proof (ar_quar _ _ _ _ _ RR) as (_ & QG & _) ]). rewrite SPL in QG. (first [ dand5 QG as _ _ _ _ BR | destruct QG as (_ & _ & _ & _ & BR) ]).
    assert (G : forall l1 l2, R = l1 ++ l2 -> tmp_chain (a_sb A) v' l2).
    { intros l1 l2. revert l1. induction l2 as [|b l2 IH]; intros l1 E; [exact I|]. cbn [tmp_chain]. split.
      - assert (Hj : nth_error R (length l1) = Some b) by (rewrite E, nth_error_app2, Nat.sub_diag by lia; reflexivity).
        assert (Hb : In b R) by (eapply nth_error_In; exact Hj).
        (first [ pose proof ((batches_repr_cells v sb (R ++ rest) (length l1) b BR ltac:(rewrite nth_error_app1 by (apply nth_error_Some_lt in Hj; exact Hj); exact Hj))) as dR_50; dand5 dR_50 as _ X2 X3 _ M | pose proof (batches_repr_cells v sb (R ++ rest) (length l1) b BR ltac:(rewrite nth_error_app1 by (apply nth_error_Some_lt in Hj; exact Hj); exact Hj)) as (_ & X2 & X3 & _ & M) ]).
        pose proof (CUT (length l1) b Hj) as X1.
        replace (match l2 with [] => 0 | b' :: _ => batch_addr sb b' end) with (match nth_error R (S (length l1)) with None => 0 | Some b' => batch_addr sb b' end)
          by (rewrite E, nth_error_app2 by lia; replace (S (length l1) - length l1)%nat with 1%nat by lia; destruct l2; reflexivity).
        (first [ pose proof ((R_range b Hb)) as dR_51; dand3 dR_51 as R1 R2 _ | pose proof (R_range b Hb) as (R1 & R2 & _) ]). (first [ pose proof ((batch_range A v [rm] ART b (R_in b Hb))) as dR_52; dand3 dR_52 as _ _ BAL | pose proof (batch_range A v [rm] ART b (R_in b Hb)) as (_ & _ & BAL) ]). pose proof alloc_ceiling_val as CE.
        assert (X2' : u64_at rsegs v' (batch_addr sb b + off_qb_size) (batch_bytes b)).
        { eapply u64_at_agree; [exact X2|]. intros q Hq. apply (AGbatchR b _ Hb). unfold off_qb_size, kQuarantineBatchBytes in *. clear -Hq. lia. }
        assert (X3' : u64_at rsegs v' (batch_addr sb b + off_qb_count) (Z.of_nat (length (ba_entries b)))).
        { eapply u64_at_agree; [exact X3|]. intros q Hq. apply (AGbatchR b _ Hb). unfold off_qb_count, kQuarantineBatchBytes in *. clear -Hq. lia. }
        unfold off_qb_size, off_qb_count in *.
        apply rw_cells_of_u64x3; [clear -R1; kung_all; lia| clear -R2 CE; kung_all; lia| | exact X1| exact X2'| exact X3'].
        apply (mapped_N v v' NN); [clear -R1; kung_all; lia| right; clear -R1; kung_all; lia| clear -R2 CE; kung_all; lia|]. intros q Hq. apply M. unfold kQuarantineBatchBytes. clear -Hq. lia.
      - apply (IH (l1 ++ [b])). rewrite <- app_assoc. exact E. }
    exact (G [] R eq_refl).
  Qed.
End Enter.
End AFreeRN.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeDc AFreeB4c AFreeB2 AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQPart.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AWrapKit ACoresk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRQ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE.AFreeRI1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE.AFreeRL OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE.AFreeRN OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeDc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQPart.AQWfJ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR.ARt4ak4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve,
                        kQuarantineBatchBytes, kQuarantineBatchCount in *.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section WFTs.
Context {Clg : Ceiling}.
  Variables (A : AState) (B : Z).
  Hypothesis W : WFB B A.
  Let B0 : forall l, Forall (wf_batch_ (a_reg A) (a_sec A)) l -> Forall (wf_batch0T_ (a_reg A) (a_sec A)) l.
  Proof. intros l F. eapply Forall_impl; [| exact F]. (intros b; (first [ intro dR_16; dand3 dR_16 as H1 H2 H3 | intros (H1 & H2 & H3) ])). split; [lia|]. split; [exact H2| exact H3]. Qed.

  Lemma WFT_of_WFB : WFT A.
  Proof.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN]. (first [ dand8 wQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct wQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
    constructor; rewrite ?wI, ?app_nil_r; try assumption.
    split; [apply B0; exact Q1|]. split; [apply B0; exact Q2|]. repeat (split; [exact I|]). exact (conj Q6 (conj Q7 Q8)).
  Qed.

  Lemma WFT_xfer : WFT (xferA A).
  Proof.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ wN]. (first [ dand8 wQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct wQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
    constructor; cbn [xferA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid a_sb a_fs];
      rewrite ?wI, ?app_nil_r.
    - exact wP.
    - exact wM.
    - exact wR.
    - exact wC.
    - apply (proj2 (wf_partition_pfun (PT (a_reg A) (a_cache A) (a_livemap A) [] (qtransfer (a_qthread A) (a_qglobal A))))).
      apply (partition_same (PT (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A))).
      + apply (proj1 (wf_partition_pfun (PT _ _ _ _ _))). exact wX.
      + intros c. reflexivity.
      + intros c k s0 Hc Hk. destruct s0; cbn [pholds pt_reg pt_cache pt_lm pt_qt pt_qg]; try tauto.
        * apply p_quar_transfer.
        * apply p_batch_transfer.
    - exact wV.
    - split; [constructor|]. split; [unfold qtransfer; apply Forall_app; split; apply B0; assumption|]. repeat (split; [exact I|]).
      split; [| split].
      + unfold batch_indices_, qtransfer in *. cbn [app]. rewrite map_app. apply NoDup_app_comm. rewrite <- map_app. exact Q6.
      + rewrite quarantined_chunks_def in *. unfold qtransfer. cbn [q_entries flat_map app]. rewrite q_entries_app, map_app. apply NoDup_app_comm. rewrite <- map_app. exact Q7.
      + intros u li Hu Hin. apply (Q8 u li Hu). apply (quarantined_chunks_transfer (a_qthread A) (a_qglobal A)). exact Hin.
    - (first [ dand5 wS as S1 S2 S3 S4 S5 | destruct wS as (S1 & S2 & S3 & S4 & S5) ]). split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      intros sc Hin. destruct (S5 sc Hin) as [L|Q]; [left; exact L| right]. apply (quarantined_chunks_transfer (a_qthread A) (a_qglobal A)). exact Q.
    - exact wD.
    - exact wF.
    - (first [ dand5 wB as B1 B2 B3 B4 B5 | destruct wB as (B1 & B2 & B3 & B4 & B5) ]). split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
      rewrite (tiny_quar_transfer (a_qthread A) (a_qglobal A)). exact B5.
  Qed.
End WFTs.

(* [comment removed for export] *)
Lemma hidden_keepS {Clg : Ceiling} : forall (A : AState) (m v' : mem),
  hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
  (forall a, in_shadow_maps a -> v' (wz a) = aview_of (pa_hull A) m (wz a)) ->
  hidden_repr (a_pl A) (a_reg A) (a_sec A) (munrestrict (hidc (pa_hull A)) m v').
Proof.
  intros A m v' [H1 H2] AG.
  assert (E : forall z, in_shadow_maps z -> munrestrict (hidc (pa_hull A)) m v' (wz z) = m (wz z)).
  { intros z Hz. unfold munrestrict. destruct (hidc (pa_hull A) (wz z)) eqn:Hc; [reflexivity|].
    rewrite (AG z Hz). unfold aview_of, mrestrict. rewrite Hc. reflexivity. }
  split.
  - intros z Gz. rewrite (E z (proj1 Gz)). exact (H1 z Gz).
  - intros z Hz NV. rewrite (E z ltac:(unfold in_shadow_maps; left; exact Hz)). exact (H2 z Hz NV).
Qed.

(* [comment removed for export] *)
Section ChainT.
Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem) (held : list Z).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v.
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).

  Lemma bwf_ofT : forall l, (forall b, In b l -> In b (a_qthread A ++ a_qglobal A)) -> NoDup (map ba_idx l) -> bwf (bsl sb l).
  Proof.
    intros l SUB ND. pose proof alloc_ceiling_val as CE. split.
    - intros i Hi. rewrite bsl_length in Hi. rewrite (baddr_bsl sb l i (BA 0 []) Hi), (bsz_bsl sb l i (BA 0 []) Hi).
      pose proof (nth_In l (BA 0 []) Hi) as IN. (first [ pose proof ((batch_range A v held AR _ (b_in_big A _ (SUB _ IN)))) as dR_5; dand3 dR_5 as R1 R2 R3 | pose proof (batch_range A v held AR _ (b_in_big A _ (SUB _ IN))) as (R1 & R2 & R3) ]).
      split; [exact R1|]. split; [unfold kQuarantineBatchBytes in R2; lia|]. split; [clear -R3; Z.div_mod_to_equations; lia|].
      rewrite batch_bytes_ebytes. pose proof (qentry_wf A v held AR) as QW.
      assert (E0 : 0 <= ebytes (ba_entries (nth i l (BA 0 []))) <= kQuarantineBatchCount * (REQ_MAX + 16384)).
      { pose proof (batch_known A v held AR _ (b_in_big A _ (SUB _ IN))) as [_ LEN].
        assert (EW : forall e, In e (ba_entries (nth i l (BA 0 []))) -> 0 <= qe_bytes e <= REQ_MAX + 16384).
        { intros e He. assert (INe : In e (q_entries (a_qthread A ++ (a_qglobal A ++ a_qlimbo A)))).
          { apply q_in_big. unfold q_entries. apply in_flat_map. exists (nth i l (BA 0 [])). split; [exact (SUB _ IN)| exact He]. }
          destruct (QW e INe) as [N _]. unfold qe_bytes, user_size. destruct (Z.eqb_spec (qe_n e) 0); unfold REQ_MAX in *; lia. }
        pose proof (ebytes_bound _ _ EW) as EB. clear -EB LEN. unfold kQuarantineBatchCount, REQ_MAX in *. nia. }
      unfold kQuarantineBatchBytes, kQuarantineBatchCount, REQ_MAX in *. lia.
    - intros i j Hi Hj NE. rewrite bsl_length in Hi, Hj. rewrite (baddr_bsl sb l i (BA 0 []) Hi), (baddr_bsl sb l j (BA 0 []) Hj).
      pose proof (nth_In l (BA 0 []) Hi) as INi. pose proof (nth_In l (BA 0 []) Hj) as INj.
      assert (NIX : ba_idx (nth i l (BA 0 [])) <> ba_idx (nth j l (BA 0 []))).
      { intros E. apply NE. apply (proj1 (NoDup_nth (map ba_idx l) 0) ltac:(apply NoDup_ListNoDup; exact ND) i j); [rewrite length_map; exact Hi| rewrite length_map; exact Hj|].
        assert (Ei : nth i (map ba_idx l) 0 = ba_idx (nth i l (BA 0 []))) by (rewrite (nth_indep _ 0 (ba_idx (BA 0 []))) by (rewrite length_map; exact Hi); apply map_nth).
        assert (Ej : nth j (map ba_idx l) 0 = ba_idx (nth j l (BA 0 []))) by (rewrite (nth_indep _ 0 (ba_idx (BA 0 []))) by (rewrite length_map; exact Hj); apply map_nth).
        rewrite Ei, Ej. exact E. }
      pose proof (carved_disjoint A v held AR _ _ (batch_carved A v held AR _ (b_in_big A _ (SUB _ INi))) (batch_carved A v held AR _ (b_in_big A _ (SUB _ INj))) ltac:(intros E; injection E as E; exact (NIX E))) as D.
      rewrite !(proj1 (c24_range A _)), !(proj2 (c24_range A _)) in D. unfold batch_addr, kQuarantineBatchBytes in *. clear -D. lia.
  Qed.
End ChainT.


(* [comment removed for export] *)
Lemma outside_bivls : forall sb l x, outside (bivls (bsl sb l)) x <-> (forall b, In b l -> ~ (batch_addr sb b <= x < batch_addr sb b + 8)).
Proof.
  intros sb l x. induction l as [|b l IH]; cbn [bivls bsl map outside fst]; [split; [intros _ b []| intros _; exact I]|].
  unfold bivls, bsl in IH. rewrite map_map in IH |- *. cbn [fst] in *. rewrite IH. split.
  - intros [N R] b' [<-|Hb']; [exact N| exact (R b' Hb')].
  - intros H. split; [apply H; left; reflexivity| intros b' Hb'; apply H; right; exact Hb'].
Qed.


Lemma last_skipn : forall {X} (l : list X) k d, (k < length l)%nat -> last (skipn k l) d = last l d.
Proof.
  induction l as [|x l IH]; intros k d LT; [cbn in LT; lia|]. destruct k as [|k]; [reflexivity|]. cbn [skipn].
  rewrite (IH k d) by (cbn in LT; lia). destruct l as [|y l']; [cbn in LT; lia| reflexivity].
Qed.


Lemma last_firstn_nth : forall {X} (l : list X) k d, (1 <= k <= length l)%nat -> last (firstn k l) d = nth (k - 1) l d.
Proof.
  induction l as [|x l IH]; intros k d H; [cbn in H; lia|]. destruct k as [|k]; [lia|]. cbn [firstn].
  destruct k as [|k']; [reflexivity|]. destruct l as [|y t]; [cbn in H; lia|].
  specialize (IH (S k') d ltac:(cbn in H |- *; lia)). cbn [firstn] in IH |- *.
  replace (S (S k') - 1)%nat with (S k') by lia. replace (S k' - 1)%nat with k' in IH by lia.
  change (nth (S k') (x :: y :: t) d) with (nth k' (y :: t) d). rewrite <- IH. reflexivity.
Qed.


Lemma q_bytes_nonneg : forall l, (forall e, In e (q_entries l) -> 0 <= qe_n e) -> 0 <= q_bytes l.
Proof.
  intros l QW. induction l as [|bb r IH]; [cbn; lia|]. rewrite q_bytes_cons, batch_bytes_ebytes.
  assert (IHr : 0 <= q_bytes r) by (apply IH; intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; right; exact He).
  assert (EW : forall e, In e (ba_entries bb) -> 0 <= qe_n e) by (intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; left; exact He).
  assert (0 <= ebytes (ba_entries bb)); [| unfold kQuarantineBatchBytes; lia].
  clear -EW. induction (ba_entries bb) as [|e es IHe]; [cbn; lia|].
  rewrite ebytes_cons. unfold qe_bytes. pose proof (user_size_pos (qe_n e) ltac:(apply EW; left; reflexivity)).
  assert (0 <= ebytes es) by (apply IHe; intros e' He'; apply EW; right; exact He'). lia.
Qed.

Section RE.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Variables (rac spd gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet).
  (* [comment removed for export] *)
  Variables (xs2 xs5 : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HI47 : hi <= 2^47.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis VB : forall a, newblk p n0 a -> a < alloc_ceiling.
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation T := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation v0 := (aview_of (pa_hull A0) m0).

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation put_frame := (put_frameG rac spd s0 s1 s2 s3 s4 s5 s6 stkobj).
  #[warnings="-notation-for-abbreviation"] Local Notation rec_frame := (rec_frameG spd stkobj xs2).
  #[warnings="-notation-for-abbreviation"] Local Notation dorec_fr := (dorec_frG s7 s8 s9 stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation CUR := (CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p n0 stkobj lo hi xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation it_cfg := (it_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation head_cfg := (head_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation blk_cfg := (blk_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation exit_cfg := (exit_cfgG spd gp s7 s8 s9 s10 s11 F fc stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation XCUR := (XCURG rac spd s0 s1 s2 s3 s4 s5 s6 A0 m0 md0 p n0 stkobj lo hi xs2).


  (* [comment removed for export] *)
  Variable key : list Z.
  Hypothesis KL : (1 <= length key <= 255)%nat.
  Hypothesis RA2 : bv_unsigned rac mod 2 = 0.
  Hypothesis PNB : 0x60a000 <= p + -16.
  Hypothesis SMH : mapped v0 uspd (hi - uspd).
  Variable li : liveinfo.
  Hypothesis LU : a_livemap A0 !! p = Some li.
  Hypothesis LN : li_n li = n0.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem loop_exit : forall (A' : AState) (m' : mem) (md' : Model) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    XCUR A' m' md' -> a_pl A' = a_pl A0 ->
    dealloc_core_K rac spd gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 p n0 lo hi TS ->
    srealizes rsegs (exit_cfg A' m' md' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) TS.
  Proof.
    intros A' m' md' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 XC PL KK.
    destruct XC as [RI HIST MI ST PF RF]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A') m') in *.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof (WFR_exit A' W L) as WF'.
    pose proof (conj (WFT_of_WFR A' W) (rc_arepr _ _ _ _ _ RC) : WFT A' /\ @arepr _ DepotRepL LPA AL_pasan [] A' v) as AR.
    destruct RC as [RAR RTMP _ _ _ _]. unfold tmp_hdr in RTMP. cbn [length q_bytes foldr last] in RTMP.
    set (thr := p_thr (a_pl A')) in *.
    (* [comment removed for export] *)
    assert (FRM : rw_cells rsegs v (uspd + -80 + -80) (recycle_frame 0 0 0 0 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz 0x3b664))).
    { unfold recycle_frame. replace (uspd + -80 + -80) with T by (clear; lia).
      apply (rw_cells_app_join v T [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] [C8 (wz (thr + 208)); C8 (wz stkobj); C8 xs2; C8 (wz (thr + 80)); C8 (wz QINST); C8 (wz 0x3b664)]).
      - change (Z.of_nat 0) with 0 in RTMP. exact RTMP.
      - cbn [cells_size csize Nat.add]. unfold rec_frameG in RF. exact RF. }
    set (Q := fun ms' : machine_state => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m'' : mem),
           ms' = MS (mkR rac spd gp (cl_tp LPA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m'' (seg_rom rsegs) /\
           munch [(lo, uspd)] v m'' /\ wmono rsegs v m'' /\ mem_inv rsegs m'' /\ stk rsegs m'' lo uspd).
    unfold exit_cfgG.
    eapply (srz_evt_restrict rsegs (pa_hull A') (hull_segsR A') pa_wxR _ (pa_eager A') Q _ md' TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A')) m') with v. rewrite PL. fold thr. rewrite <- PL.
      replace (wz T : word) with (wz (uspd + -80 + -80) : word) by (f_equal; clear; lia).
      replace (ret_pc (wz recycle_ret)) with (wz recycle_ret : word) by (symmetry; apply ret_pc_even; [unfold recycle_ret; clear; lia| reflexivity]).
      eapply evt_cut.
      { eapply (recycle_post_ok (wz 0) gp (cl_tp LPA) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc v (uspd + -80) lo 0 0 0 0);
          [exact MI| replace (uspd + -80 - 80) with T by (clear; lia); exact ST| clear -LOW; lia| exact CEIL| clear -LOW SPHI HI47; lia| clear -SPA SPR; lia| exact FRM
          | rewrite unsigned_lit; [reflexivity| clear; lia]]. }
      cbv beta. (intros ms1; (first [ intro dR_17; dex1 dR_17 as m9; dand5 dR_17 as -> MU9 WM9 MI9 ST9 | intro dR_17; dand6 dR_17 as m9 -> MU9 WM9 MI9 ST9 | intros (m9 & -> & MU9 & WM9 & MI9 & ST9) ])).
      replace (ret_pc (wz 0x3b664)) with (wz 0x3b664 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (PF9 : rw_cells rsegs m9 (uspd + -80) [C8 (wz (thr + 208)); C8 (wz stkobj); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]).
      { unfold put_frameG in PF. eapply rw_cells_transport; [exact PF| exact MU9| exact WM9|]. cbn [disjoint_from cells_size csize Nat.add]. clear -LOW. lia. }
      assert (LO' : alloc_ceiling <= lo /\ lo <= uspd - 704) by (clear -CEIL LOW; split; lia).
      assert (SPH' : uspd <= 2^47) by (clear -SPHI HI47; lia).
      eapply (free_crtail rac spd gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p thr stkobj [] key LO' SPH' PNB KL Q m9); [exact MI9| exact ST9| exact PF9|].
      intros ST10. apply evt_done. subst Q. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m9. split; [reflexivity|].
      split; [| exact (conj WM9 (conj MI9 ST10))].
      intros y Hy. apply MU9. cbn [outside] in Hy |- *. clear -Hy LOW. lia. }
    intros msr' md'' HQ HI' Hsame Hcl.
    (first [ dex16 HQ as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m''; dand5 HQ as -> MUN WM' MI' STK' | dand21 HQ as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'' -> MUN WM' MI' STK' | destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & -> & MUN & WM' & MI' & STK') ]).
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM2.
    assert (VIEW : aview_of (pa_hull A') (munrestrict (hidc (pa_hull A')) m' m'') = m'').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m'' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NNR _ _ a WM'); [exact H1| lia]. }
    assert (AGC : forall a, 0 <= a < alloc_ceiling -> m'' (wz a) = v (wz a)).
    { intros a Ha. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha CE; lia). cbn [outside]. clear -Ha CEIL. split; [|exact I]. intros X. lia. }
    assert (AGW : forall a, 0 <= a < 2^64 -> ~ (lo <= a < uspd) -> m'' (wz a) = v (wz a)).
    { intros a Ha NW. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha; lia). cbn [outside]. clear -Ha NW. split; [|exact I]. intros X. lia. }
    pose proof (arepr_keep A' v m'' [] AR AGC NN) as AR'.
    (* [comment removed for export] *)
    assert (AI' : @pa_ainv _ DepotRepL A' (munrestrict (hidc (pa_hull A')) m' m'') md'').
    { constructor.
      - exact WF'.
      - change (ahull_of pa_image_ivs AL_pasan A') with (pa_hull A'). rewrite VIEW. exact AR'.
      - apply (hidden_keep A' m' m'' HID). exact AGC.
      - exact EXTRA.
      - exact (aledger_sbm _ _ _ _ md' md'' Hsame LED).
      - exact HI'.
      - (first [ dand18 FRM2 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT' _ | destruct FRM2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT' & _) ]). rewrite HLT'. exact HLT.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact COV.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact CEI. }
    (* [comment removed for export] *)
    assert (SM' : mapped m'' lo (uspd - lo)).
    { intros q Hq. exact (stk_mapped_pa m'' lo uspd lo (uspd - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q Hq). }
    assert (RS : rstep (pa_owned A') (pa_owned A') lo uspd v m'').
    { apply rstep_window; [exact AGW| exact SM'|]. intros a Oa. pose proof (owned_below_ceilingT A' a (WFT_of_WFR A' W) Oa). clear -H CEIL. lia. }
    pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A' v md' A' m'' md'' HIST (WFT_of_WFR A' W) (WFT_of_WFR A' W) CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (fun c _ V => V) (wamd_sbm md' md'' Hsame HLT) RS) as HIST'.
    destruct HIST' as [hP hF hH hL hT hS hPC hV hA hE hFR hAB].
    (* [comment removed for export] *)
    unfold dealloc_core_K in KK. cbv zeta in KK.
    specialize (KK t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' (munrestrict (hidc (pa_hull A')) m' m'') md'').
    rewrite VIEW in KK. apply KK.
    - exact AI'.
    - exact MI'.
    - exact hA.
    - intros ff. unfold as_fframe. rewrite hF. reflexivity.
    - exact hP.
    - unfold as_live, as_live_. rewrite hL, lookup_delete_eq. reflexivity.
    - intros q NE. unfold as_live, as_live_. rewrite hL, lookup_delete_ne by congruence. reflexivity.
    - unfold as_livebytes. rewrite hL, (as_livebytes_delete' _ _ _ LU), LN. reflexivity.
    - unfold as_tinycred. rewrite hT. reflexivity.
    - unfold as_seccred. rewrite hS. reflexivity.
    - unfold as_primcred. rewrite hPC. reflexivity.   (* [comment removed for export] *)
    - unfold as_nlive. rewrite hL, (as_nlive_delete _ _ _ LU). destruct (Z.eqb_spec p 0) as [E0|_]; [exfalso; clear -E0 PNB; lia| reflexivity].
    - exact hV.
    - intros i Hi. unfold mrd. rewrite (hE i Hi). reflexivity.
    - exact (frame_ok_widen _ _ _ _ _ _ uspd lo hi SPHI hFR hAB SMH).
    - exact hAB.
    - exact STK'.
  Qed.
  (* [comment removed for export] *)
  #[local] Notation rm := (al_instance AL_pasan + off_q_recycle_mutex).
  #[local] Notation Iq := 728408.
  (* [comment removed for export] *)
  Definition rec_cfg (A : AState) (m : mem) (md : Model) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) : config :=
    mkCfg (MS (mkR (wz 0x3b664) (wz (uspd + -80)) gp (cl_tp LPA) t0 t1 t2 (wz QINST) (wz (p_thr (a_pl A) + 80))
                   (wz QINST) (wz kQuarantineMinSize) (wz (p_thr (a_pl A) + 208)) (wz stkobj) a4 a5 a6 a7
                   xs2 (wz stkobj) (wz (p_thr (a_pl A) + 208)) xs5 (wz (2^20)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz recycle_entry) fc None m (seg_rom rsegs)) md.
  (* [comment removed for export] *)
  Record RECX (A : AState) (m : mem) (md : Model) : Prop := {
    rx_wfb : WFB (q_bytes (a_qthread A)) A;
    rx_ci : a_cache_inited A = true;
    rx_dr : kQuarantineCacheSize < q_bytes (a_qthread A);
    rx_big : kQuarantineMaxSize < q_bytes (a_qglobal A) + q_bytes (a_qthread A);
    rx_qb : q_bytes (a_qglobal A) + q_bytes (a_qthread A) <= 2^29 + 2^21;
    rx_ar : @arepr _ DepotRepL LPA AL_pasan [rm] (xferA A) (aview_of (pa_hull A) m);
    rx_hidden : hidden_repr (a_pl A) (a_reg A) (a_sec A) m;
    rx_extra : wf_extra LPA pa_site_pcs (a_pl A);
    rx_ledger : aledger_ AL_pasan (a_pl A) (a_reg A) (a_sec A) md;
    rx_minv : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md;
    rx_halted : m_halted md = None;
    rx_cover : acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md);
    rx_ceil : alloc_top (m_vmmaps md) = alloc_ceiling;
    rx_hist : RHIST A0 v0 md0 p n0 uspd lo hi A (aview_of (pa_hull A) m) md;
    rx_mi : mem_inv rsegs (aview_of (pa_hull A) m);
    rx_stk : stk rsegs (aview_of (pa_hull A) m) lo (uspd + -80);
    rx_put : put_frame (p_thr (a_pl A)) (aview_of (pa_hull A) m);
    rx_lck : rw_cells rsegs (aview_of (pa_hull A) m) (Iq + off_q_cache_mutex) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz 0)];
    rx_hdr : rw_cells rsegs (aview_of (pa_hull A) m) (Iq + off_q_cache_list_size)
               [C8 (wz (Z.of_nat (length (qtransfer (a_qthread A) (a_qglobal A)))));
                C8 (wz (match qtransfer (a_qthread A) (a_qglobal A) with [] => 0 | b :: _ => batch_addr (a_sb A) b end));
                C8 (wz (match qtransfer (a_qthread A) (a_qglobal A) with [] => 0 | _ :: _ => batch_addr (a_sb A) (last (qtransfer (a_qthread A) (a_qglobal A)) (BA 0 [])) end));
                C8 (wz (q_bytes (qtransfer (a_qthread A) (a_qglobal A))))];
    rx_qmin : ro_cells rsegs (aview_of (pa_hull A) m) (QINST + 64) [C8 (wz (2^28)); C8 (wz kQuarantineMinSize)] }.

  (* [comment removed for export] *)
  Lemma qall_count_bound : forall A held (v : mem), WFT A /\ @arepr _ DepotRepL LPA AL_pasan held A v ->
    Z.of_nat (length (a_qthread A ++ a_qglobal A ++ a_qlimbo A)) <= carved_count A kQuarantineBatchClass /\
    carved_count A kQuarantineBatchClass * 8192 <= 3758096384.
  Proof.
    intros A held v AR. pose proof (batches_nodup A v held AR) as ND. apply NoDup_ListNoDup in ND.
    assert (RG : forall x, In x (map ba_idx (a_qthread A ++ a_qglobal A ++ a_qlimbo A)) -> 0 <= x < carved_count A kQuarantineBatchClass).
    { intros x Hx. apply in_map_iff in Hx as (b & <- & Hb). exact (proj1 (batch_known A v held AR b Hb)). }
    (first [ pose proof ((rk_region_facts A v held AR kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia))) as dR_8; dand7 dR_8 as RG1 RG2 _ _ _ RG6 RG7 | pose proof (rk_region_facts A v held AR kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (RG1 & RG2 & _ & _ & _ & RG6 & RG7) ]).
    change (class_size kQuarantineBatchClass) with 8192 in RG6.
    split; [| clear -RG1 RG2 RG6; kung_all; lia].
    pose proof (NoDup_incl_length ND (l' := map Z.of_nat (seq 0 (Z.to_nat (carved_count A kQuarantineBatchClass))))) as X.
    rewrite !length_map, length_seq in X. rewrite <- (Z2Nat.id (carved_count A kQuarantineBatchClass)) by lia.
    apply inj_le. apply X. intros x Hx. apply in_map_iff. exists (Z.to_nat x). pose proof (RG x Hx). split; [lia|]. apply in_seq. lia.
  Qed.

  Theorem rec_to_loop : forall (A : AState) (m : mem) (md : Model) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    RECX A m md ->
    (forall (A' : AState) (m' : mem) (md' : Model) (scr : list byte) (ra a1 a2 a3 a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' : word) (more : list batch),
        more <> [] -> CUR A' m' md' None more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (head_cfg A' m' md' more ra a1 a2 a3 a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9') TS) ->
    srealizes rsegs (rec_cfg A m md t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6) TS.
  Proof.
    intros A m md t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 RX KH.
    destruct RX as [WB CI DR BIG QBB AR0 HID EXTRA LED HMI HLT COV CEI HIST MI ST PF LCK HDR QMN].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    set (Ax := xferA A) in *.
    pose proof (WFT_xfer A _ WB) as WTx. change (xferA A) with Ax in WTx.
    pose proof (conj WTx AR0 : WFT Ax /\ @arepr _ DepotRepL LPA AL_pasan [rm] Ax v) as AR.
    set (qg0 := qtransfer (a_qthread A) (a_qglobal A)) in *.
    assert (QG0 : a_qglobal Ax = qg0) by reflexivity. assert (QT0 : a_qthread Ax = []) by reflexivity.
    assert (LIM0 : a_qlimbo Ax = []) by (destruct WB as [_ _ _ _ _ _ _ _ _ _ _ wI _ _]; exact wI).
    set (sb := a_sb A) in *. set (thr := p_thr (a_pl A)) in *.
    set (bs := bsl sb qg0). set (gqb := q_bytes qg0). set (gn := Z.of_nat (length qg0)).
    set (k := npop kQuarantineMinSize gqb bs). set (kz := Z.of_nat k).
    set (R := fst (rsplit qg0 kQuarantineMinSize)). set (rest := snd (rsplit qg0 kQuarantineMinSize)).
    pose proof (npop_rsplit sb qg0 kQuarantineMinSize) as NR. cbv zeta in NR. fold bs gqb k in NR. destruct NR as [RE1 RE2]. fold R in RE1. fold rest in RE2.
    assert (APP : qg0 = R ++ rest) by (rewrite RE1, RE2; symmetry; apply firstn_skipn).
    assert (GQE : gqb = q_bytes (a_qglobal A) + q_bytes (a_qthread A)) by (unfold gqb, qg0, qtransfer; rewrite q_bytes_app; reflexivity).
    (* [comment removed for export] *)
    assert (INqg : forall b, In b qg0 -> In b (a_qthread Ax ++ a_qglobal Ax)) by (intros b Hb; rewrite QT0, QG0; exact Hb).
    pose proof (batches_nodup Ax v [rm] AR) as NDA. rewrite QT0, QG0, LIM0, app_nil_r in NDA. cbn [app] in NDA.
    pose proof (bwf_ofT Ax v [rm] AR qg0 INqg NDA) as BWF. change (a_sb Ax) with sb in BWF. fold bs in BWF.
    (first [ pose proof ((ar_quar _ _ _ _ _ AR0)) as dR_9; dand3 dR_9 as _ QG _ | pose proof (ar_quar _ _ _ _ _ AR0) as (_ & QG & _) ]). change (a_qglobal (xferA A)) with qg0 in QG. change (p_sb (a_pl (xferA A))) with sb in QG.
    (first [ dand5 QG as _ _ _ _ BR | destruct QG as (_ & _ & _ & _ & BR) ]).
    pose proof (bchain_of Ax v qg0 BR) as BC. change (a_sb Ax) with sb in BC. fold bs in BC.
    (* [comment removed for export] *)
    pose proof (qall_count_bound Ax [rm] v AR) as [CNT CAPB]. rewrite QT0, QG0, LIM0, app_nil_r in CNT. cbn [app] in CNT. fold gn in CNT.
    assert (GQMIN : kQuarantineMinSize < gqb) by (rewrite GQE; unfold kQuarantineMinSize, kQuarantineMaxSize in *; clear -BIG; lia).
    assert (GN16 : 16384 * gn <= gqb).
    { destruct WB as [_ _ _ _ _ _ wQ _ _ _ wBu _ _ wJ].
      pose proof (wf_qcredit_transfer (a_reg A) (a_livemap A) (a_qthread A) (a_qglobal A) (a_sec A) (a_tiny A) _ wQ wBu wJ DR) as J'.
      exact (wf_qcredit_nomerge _ J' GQMIN). }
    assert (K1 : (1 <= k)%nat).
    { unfold k. destruct qg0 as [|b0 r] eqn:E0; [exfalso; unfold gqb in GQMIN; cbn in GQMIN; unfold kQuarantineMinSize in GQMIN; clear -GQMIN; lia|].
      unfold bs, bsl. cbn [map npop]. destruct (Z.leb_spec gqb kQuarantineMinSize); [exfalso; clear -GQMIN H; lia| clear; lia]. }
    pose proof (npop_length sb qg0 kQuarantineMinSize) as KLE. fold bs gqb k in KLE.
    set (gl := match qg0 with [] => 0 | _ :: _ => batch_addr sb (last qg0 (BA 0 [])) end) in *.
    assert (NE0 : qg0 <> []) by (intros E0; unfold gqb in GQMIN; rewrite E0 in GQMIN; cbn in GQMIN; unfold kQuarantineMinSize in GQMIN; clear -GQMIN; lia).
    assert (HDR2 : rw_cells rsegs v (QINST + 160) [C8 (wz gn); C8 (wz (baddr bs 0)); C8 (wz gl); C8 (wz gqb)]).
    { unfold QINST. replace (Iq + 728 + 160) with (Iq + off_q_cache_list_size) by reflexivity.
      replace (baddr bs 0) with (match qg0 with [] => 0 | b :: _ => batch_addr sb b end); [exact HDR|].
      unfold bs. destruct qg0 as [|b0 r]; [exfalso; exact (NE0 eq_refl)| symmetry; apply baddr_bsl_cons]. }
    assert (LCK2 : rw_cells rsegs v (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz 0)]) by exact LCK.
    assert (LASTIN : forall (l : list batch) d, l <> [] -> In (last l d) l).
    { clear. induction l as [|x l IH]; intros d NE; [congruence|]. destruct l as [|y l']; [left; reflexivity| right; apply IH; discriminate]. }
    assert (GLR : 0 <= gl < 2^64).
    { unfold gl. destruct qg0 as [|b0 r] eqn:E0; [clear; lia|].
      (first [ pose proof ((batch_range Ax v [rm] AR _ (b_in_big Ax _ (INqg _ (LASTIN (b0 :: r) (BA 0 []) ltac:(discriminate)))))) as dR_11; dand3 dR_11 as R1 R2 _ | pose proof (batch_range Ax v [rm] AR _ (b_in_big Ax _ (INqg _ (LASTIN (b0 :: r) (BA 0 []) ltac:(discriminate))))) as (R1 & R2 & _) ]).
      unfold sb. change (a_sb A) with (a_sb Ax). clear -R1 R2 CE. kung_all. lia. }
    assert (GQB8 : gn * 8192 <= gqb) by (clear -GN16 CNT; lia).
    assert (LSUM : lsum bs = gqb) by (unfold bs, gqb; apply lsum_bsl).
    set (psum := lsum (firstn k bs)).
    set (Q := fun ms' : machine_state => exists (t0' t1' t2' a4' a5' a6' a7' : word) (scr : list byte) (m' : mem),
           ms' = MS (head_regs (wz dsp) gp (cl_tp LPA) T s10 s11 (wz recycle_ret) kz (wz 0xb23e0) (wz (thr + 208)) (wz stkobj) a4' a5' a6' a7' t0' t1' t2' t3 t4 t5 t6
                               (wz (thr + 208)) (wz (2^20)) s7 s8 s9) F (wz dorec_head) fc None m' (seg_rom rsegs) /\
           rw_cells rsegs m' T [C8 (wz kz); C8 (wz (baddr bs 0)); C8 (wz (baddr bs (k - 1))); C8 (wz psum)] /\
           rec_frame thr m' /\
           rw_cells rsegs m' dsp (dorec_fr thr scr) /\
           rw_cells rsegs m' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)] /\
           rw_cells rsegs m' (QINST + 160) [C8 (wz (gn - kz)); C8 (wz (baddr bs k)); C8 (wz (if ((k =? length qg0)%nat && (0 <? k)%nat)%bool then 0 else gl)); C8 (wz (gqb - psum))] /\
           bchain_cut m' bs k /\
           munch ((uspd + -80 - 192, uspd + -80) :: (QINST + 152, QINST + 156) :: (QINST + 160, QINST + 192) :: bivls (firstn k bs)) v m' /\
           wmono rsegs v m' /\ mem_inv rsegs m' /\ stk rsegs m' lo dsp).
    unfold rec_cfg. fold thr.
    eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR A) pa_wxR _ (pa_eager A) Q _ md TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (recycle_enter (wz 0x3b664) (wz (uspd + -80)) gp (cl_tp LPA) t0 t1 t2 (wz QINST) (wz (thr + 80)) (wz (thr + 208)) (wz stkobj) a4 a5 a6 a7
                xs2 (wz stkobj) (wz (thr + 208)) xs5 (wz (2^20)) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v QINST kQuarantineMinSize 0 gl gqb lo bs Q).
      all: cbv zeta; unfold bs; rewrite ?bsl_length; fold bs; fold gn; fold k; fold kz; fold psum.
      all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
      all: lazymatch goal with
           | |- forall (x : word), _ =>
               intros t0' t1' t2' a4' a5' a6' a7' scr m' TC' RR' DF' LK' GL' BCC' MU' WM' MI' ST';
               apply evt_done; subst Q; exists t0', t1', t2', a4', a5', a6', a7', scr, m';
               replace (uspd + -80 - 80 - 112) with dsp in * by (clear; lia); replace (uspd + -80 - 80 + 32) with (T + 32) in RR' by (clear; lia);
               replace (uspd + -80 - 80) with T in * by (clear; lia);
               split; [reflexivity|];
               split; [exact TC'|]; split; [exact RR'|]; split; [exact DF'|]; split; [exact LK'|]; split; [exact GL'|]; split; [exact BCC'|];
               split; [exact MU'|]; exact (conj WM' (conj MI' ST'))
           | _ => idtac
           end.
      all: first [ assumption | reflexivity
                 | exact MI | exact ST | exact BWF | exact BC | exact K1 | exact LCK2 | exact HDR2
                 | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                 | unfold QINST; clear; lia
                 | unfold kQuarantineMinSize; clear; lia
                 | clear -GLR; lia
                 | rewrite GQE; clear -QBB BIG; unfold kQuarantineMaxSize in *; lia
                 | clear -CNT CAPB; unfold gn in *; lia
                 | clear -GQB8; unfold gn in *; lia
                 | left; clear -GN16; unfold gn in *; lia
                 | rewrite LSUM; clear; lia
                 | rewrite LSUM; unfold kQuarantineMinSize; clear; lia
                 | match goal with |- ?g => idtac "UNSOLVED:" g end ]. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex9 HQ as t0' t1' t2' a4' a5' a6' a7' scr m'; dand11 HQ as -> TC' RR' DF' LK' GL' BCC' MUN WM' MI' STK' | dand20 HQ as t0' t1' t2' a4' a5' a6' a7' scr m' -> TC' RR' DF' LK' GL' BCC' MUN WM' MI' STK' | destruct HQ as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & scr & m' & -> & TC' & RR' & DF' & LK' & GL' & BCC' & MUN & WM' & MI' & STK') ]).
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m m') = m').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NNR _ _ a WM'); [exact H1| lia]. }
    set (A2 := recA2 A R rest).
    assert (W2 : WFR A2) by exact (WFR_enter A _ WB CI DR).
    assert (SPL : a_qglobal Ax = R ++ rest) by (rewrite QG0; exact APP).
    assert (RF : R = firstn k qg0) by exact RE1. assert (LR : length R = k) by (rewrite RF, firstn_length; clear -KLE; lia).
    assert (BSR : firstn k bs = bsl sb R) by (rewrite RF; unfold bs; apply firstn_bsl).
    (* [comment removed for export] *)
    set (Wn := fun a => uspd + -80 - 192 <= a < uspd + -80).
    assert (WNH : forall a, Wn a -> alloc_ceiling <= a) by (subst Wn; cbv beta; intros a Ha; clear -Ha CEIL LOW; lia).
    assert (MU2 : forall a, 0 <= a < 2^64 -> ~ en_foot Ax R Wn a -> m' (wz a) = v (wz a)).
    { intros a Ha NF. apply (MUN (wz a)). rewrite unsigned_lit by (clear -Ha; lia). unfold en_foot in NF. subst Wn. cbv beta in NF.
      cbn [outside]. unfold QINST, off_q_cache_mutex, off_q_cache_list_size in *.
      split; [intros X; apply NF; left; exact X|]. split; [intros X; apply NF; right; left; clear -X; lia|]. split; [intros X; apply NF; right; right; left; clear -X; lia|].
      rewrite BSR. apply (proj2 (outside_bivls sb R a)). intros b Hb X. apply NF. right; right; right. exists b. exact (conj Hb X). }
    (* [comment removed for export] *)
    assert (HLEN : gn - kz = Z.of_nat (length rest)) by (rewrite RE2, length_skipn; unfold gn, kz; clear -KLE; lia).
    assert (HFST : baddr bs k = match rest with [] => 0 | b :: _ => batch_addr sb b end).
    { rewrite RE2. destruct (Nat.lt_ge_cases k (length qg0)) as [LT|GE].
      - unfold bs. rewrite (baddr_bsl sb qg0 k (BA 0 []) LT). destruct (skipn k qg0) as [|b r] eqn:E; [exfalso; apply (f_equal (@length batch)) in E; rewrite length_skipn in E; cbn in E; clear -E LT; lia|].
        pose proof (f_equal (fun l => nth_error l 0) E) as E1. cbv beta in E1. rewrite nth_error_skipn, Nat.add_0_r in E1. cbn in E1.
        rewrite (nth_error_nth' qg0 (BA 0 []) LT) in E1. injection E1 as ->. reflexivity.
      - rewrite baddr_over by (unfold bs; rewrite bsl_length; exact GE). rewrite skipn_all2 by exact GE. reflexivity. }
    assert (HLST : (if ((k =? length qg0)%nat && (0 <? k)%nat)%bool then 0 else gl) = match rest with [] => 0 | _ :: _ => batch_addr sb (last rest (BA 0 [])) end).
    { rewrite RE2. destruct (Nat.eqb_spec k (length qg0)) as [E|NE].
      - rewrite E, skipn_all. cbn [andb]. destruct (Nat.ltb_spec 0 (length qg0)); [reflexivity| exfalso; clear -K1 E H; lia].
      - cbn [andb]. assert (LT : (k < length qg0)%nat) by (clear -NE KLE; lia).
        destruct (skipn k qg0) as [|b r] eqn:E; [exfalso; apply (f_equal (@length batch)) in E; rewrite length_skipn in E; cbn in E; clear -E LT; lia|].
        rewrite <- E, (last_skipn qg0 k (BA 0 []) LT). unfold gl. clear -NE0. destruct qg0; [exfalso; exact (NE0 eq_refl)| reflexivity]. }
    assert (HBYT : gqb - psum = q_bytes rest).
    { unfold psum, gqb. rewrite BSR, lsum_bsl. rewrite APP at 1. rewrite q_bytes_app. clear. lia. }
    assert (HDR3 : rw_cells rsegs m' (Iq + off_q_cache_list_size)
                     [C8 (wz (Z.of_nat (length rest))); C8 (wz (match rest with [] => 0 | b :: _ => batch_addr sb b end));
                      C8 (wz (match rest with [] => 0 | _ :: _ => batch_addr sb (last rest (BA 0 [])) end)); C8 (wz (q_bytes rest))]).
    { rewrite <- HLEN, <- HFST, <- HLST, <- HBYT. exact GL'. }
    assert (CUT : forall j b, nth_error R j = Some b -> u64_at rsegs m' (batch_addr sb b) (match nth_error R (S j) with None => 0 | Some b' => batch_addr sb b' end)).
    { intros j b Hj. pose proof (nth_error_Some_lt _ _ _ Hj) as JL. rewrite LR in JL.
      assert (JL2 : (j < length bs)%nat) by (unfold bs; rewrite bsl_length; clear -JL KLE; lia).
      pose proof (BCC' j JL2) as X.
      assert (E1 : baddr bs j = batch_addr sb b).
      { unfold bs. rewrite (baddr_bsl sb qg0 j (BA 0 []) ltac:(clear -JL KLE; lia)). f_equal. rewrite RF in Hj. rewrite nth_error_firstn in Hj.
        destruct (Nat.ltb_spec j k); [| discriminate]. apply nth_error_nth. exact Hj. }
      rewrite E1 in X. apply u64_of_rw with (v := m').
      - destruct (nth_error R (S j)) as [b'|] eqn:E2; [| clear; lia]. (first [ pose proof ((batch_range Ax v [rm] AR b' (b_in_big Ax _ (INqg _ ltac:(rewrite APP; apply in_or_app; left; eapply nth_error_In; exact E2))))) as dR_13; dand3 dR_13 as R1 R2 _ | pose proof (batch_range Ax v [rm] AR b' (b_in_big Ax _ (INqg _ ltac:(rewrite APP; apply in_or_app; left; eapply nth_error_In; exact E2)))) as (R1 & R2 & _) ]).
        change (a_sb Ax) with sb in R1, R2. clear -R1 R2 CE. kung_all. lia.
      - apply (rw_cells_app_split m' _ [C8 _] [C8 _]) in X as [X _].
        replace (match nth_error R (S j) with Some b' => batch_addr sb b' | None => 0 end) with (if (S j =? k)%nat then 0 else baddr bs (S j)); [exact X|].
        rewrite RF, nth_error_firstn. destruct (Nat.eqb_spec (S j) k) as [E|NE].
        + destruct (Nat.ltb_spec (S j) k); [exfalso; clear -E H; lia| reflexivity].
        + destruct (Nat.ltb_spec (S j) k); [| exfalso; clear -NE H JL; lia].
          destruct (nth_error qg0 (S j)) as [b'|] eqn:E2.
          * unfold bs. rewrite (baddr_bsl sb qg0 (S j) (BA 0 []) (nth_error_Some_lt _ _ _ E2)). f_equal. apply nth_error_nth. exact E2.
          * apply nth_error_None in E2. clear -E2 H KLE. exfalso. lia. }
    pose proof (en_arepr Ax v m' R rest AR QT0 SPL Wn WNH MU2 NN LK' HDR3) as AR2. change (enA Ax R rest) with A2 in AR2.
    (* [comment removed for export] *)
    assert (TMP : tmp_hdr sb m' T R).
    { unfold tmp_hdr. rewrite LR. fold kz.
      replace (match R with [] => 0 | b :: _ => batch_addr sb b end) with (baddr bs 0).
      2: { rewrite RF. destruct k as [|k']; [exfalso; clear -K1; lia|]. unfold bs. destruct qg0 as [|b0 r0]; [exfalso; exact (NE0 eq_refl)|]. cbn [firstn]. apply baddr_bsl_cons. }
      replace (match R with [] => 0 | _ :: _ => batch_addr sb (last R (BA 0 [])) end) with (baddr bs (k - 1)).
      2: { assert (LT : (k - 1 < length qg0)%nat) by (clear -K1 KLE; lia).
           unfold bs. rewrite (baddr_bsl sb qg0 (k - 1) (BA 0 []) LT). rewrite RF.
           destruct (firstn k qg0) as [|b0 r0] eqn:E; [exfalso; apply (f_equal (@length batch)) in E; rewrite firstn_length in E; cbn in E; clear -E K1 KLE; lia|].
           rewrite <- E. f_equal. symmetry. apply last_firstn_nth. clear -K1 KLE. lia. }
      replace (q_bytes R) with psum by (unfold psum; rewrite BSR, lsum_bsl; reflexivity). exact TC'. }
    assert (RC2 : rcells A2 m' T None R).
    { constructor.
      - exact AR2.
      - exact TMP.
      - exact (en_chain Ax v m' R rest AR SPL Wn WNH MU2 NN CUT).
      - intros b e Hb He. exact (en_entries Ax v m' R rest AR QT0 SPL Wn WNH MU2 NN b e Hb He).
      - intros b Hb. exact (en_objs Ax v m' R rest AR SPL Wn WNH MU2 NN b Hb).
      - exact I. }
    (* [comment removed for export] *)
    assert (AGS : forall a, in_shadow_maps a -> m' (wz a) = v (wz a)).
    { intros a Ha. unfold in_shadow_maps in Ha. apply MU2; [clear -Ha; kung_all; lia|]. unfold en_foot. subst Wn. cbv beta.
      unfold off_q_cache_mutex, off_q_cache_list_size. intros [Fo|[Fo|[Fo|(b & Hb & Fo)]]].
      - clear -Fo Ha CEIL LOW CE. kung_all. lia.
      - clear -Fo Ha. kung_all. lia.
      - clear -Fo Ha. kung_all. lia.
      - pose proof (batch_range Ax v [rm] AR b (b_in_big Ax _ (INqg _ ltac:(rewrite APP; apply in_or_app; left; exact Hb)))) as (R1 & _). change (a_sb Ax) with sb in R1.
        change (a_sb Ax) with sb in Fo. clear -Fo Ha R1. kung_all. lia. }
    assert (RI2 : RINV A2 (munrestrict (hidc (pa_hull A)) m m') md' T None R).
    { constructor.
      - exact W2.
      - reflexivity.
      - change (pa_hull A2) with (pa_hull A). rewrite VIEW. exact RC2.
      - exact (hidden_keepS A m m' HID AGS).
      - exact EXTRA.
      - exact (aledger_sbm _ _ _ _ md md' Hsame LED).
      - exact HI'.
      - (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT' _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT' & _) ]). rewrite HLT'. exact HLT.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact COV.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact CEI. }
    (* [comment removed for export] *)
    assert (PF' : put_frame thr m').
    { unfold put_frameG in *. eapply rw_cells_agree; [exact PF|]. cbn [cells_size csize Nat.add]. intros i Hi. apply MU2; [clear -Hi SPR SPHI HI47 LOW CEIL CE; lia|].
      unfold en_foot. subst Wn. cbv beta. unfold off_q_cache_mutex, off_q_cache_list_size. intros [Fo|[Fo|[Fo|(b & Hb & Fo)]]].
      - clear -Fo Hi. lia.
      - clear -Fo Hi CEIL LOW CE. lia.
      - clear -Fo Hi CEIL LOW CE. lia.
      - (first [ pose proof ((batch_range Ax v [rm] AR b (b_in_big Ax _ (INqg _ ltac:(rewrite APP; apply in_or_app; left; exact Hb))))) as dR_15; dand3 dR_15 as _ R2 _ | pose proof (batch_range Ax v [rm] AR b (b_in_big Ax _ (INqg _ ltac:(rewrite APP; apply in_or_app; left; exact Hb)))) as (_ & R2 & _) ]).
        change (a_sb Ax) with sb in Fo, R2. clear -Fo Hi R2 CEIL LOW. kung_all. lia. }
    assert (SM' : mapped m' lo (uspd - lo)).
    { intros q Hq. pose proof TMP as TM'. unfold tmp_hdr in TM'. unfold rec_frameG in RR'.
      destruct (Z.lt_ge_cases (lo + q) dsp) as [C1|C1].
      { exact (stk_mapped_pa m' lo dsp lo (dsp - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
      destruct (Z.lt_ge_cases (lo + q) T) as [C2|C2].
      { pose proof (rw_mapped_hi m' _ _ DF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
        specialize (M (lo + q - dsp) ltac:(clear -C1 C2; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M. }
      destruct (Z.lt_ge_cases (lo + q) (T + 32)) as [C3|C3].
      { pose proof (rw_mapped_hi m' _ _ TM' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - T) ltac:(clear -C2 C3; lia)). replace (T + (lo + q - T)) with (lo + q) in M by (clear; lia). exact M. }
      destruct (Z.lt_ge_cases (lo + q) (T + 80)) as [C4|C4].
      { pose proof (rw_mapped_hi m' _ _ RR' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (lo + q - (T + 32))) with (lo + q) in M by (clear; lia). exact M. }
      pose proof (rw_mapped_hi m' _ _ PF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
      specialize (M (lo + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (lo + q - (uspd + -80))) with (lo + q) in M by (clear; lia). exact M. }
    (* [comment removed for export] *)
    assert (OWN2 : forall a, pa_owned A2 a <-> pa_owned A a) by (intros a; split; intros X; exact X).
    assert (RS : rstep (pa_owned A) (pa_owned A2) lo uspd v m').
    { unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      - intros a Ha NO NO' NW. apply MU2; [exact Ha|]. unfold en_foot. subst Wn. cbv beta. unfold off_q_cache_mutex, off_q_cache_list_size.
        intros [Fo|[Fo|[Fo|(b & Hb & Fo)]]].
        + apply NW. clear -Fo LOW CEIL. lia.
        + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -Fo. lia.
        + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -Fo. lia.
        + apply NO. assert (INb : In b (a_qthread Ax ++ (a_qglobal Ax ++ a_qlimbo Ax))) by (apply b_in_big; apply INqg; rewrite APP; apply in_or_app; left; exact Hb).
          apply (carved_owned Ax v [rm] AR _ a (batch_carved Ax v [rm] AR b INb)).
          * cbn [chunk_lo chunk_hi alloc_beg]. change (class_size kQuarantineBatchClass) with 8192. unfold batch_addr in Fo |- *. change (a_sb Ax) with sb in Fo |- *. clear -Fo. lia.
          * intros u li' Hl E _. exact (live_not_batch Ax v [rm] AR u li' b Hl INb E).
      - intros a Ha NI Hv. right. apply NN; [clear -Ha; lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| clear -Ha; lia| exact Hv].
      - exact SM'.
      - intros a Ha O'. left. exact (proj1 (OWN2 a) O').
      - intros a Ha O NO'. exfalso. apply NO'. exact (proj2 (OWN2 a) O). }
    pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A v md A2 m' md' HIST (WFT_of_WFB A _ WB) (WFT_of_WFR A2 W2) CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (fun c _ V => V) (wamd_sbm md md' Hsame HLT) RS) as HIST2.
    (* [comment removed for export] *)
    assert (CU2 : CUR A2 (munrestrict (hidc (pa_hull A)) m m') md' None R scr).
    { constructor; change (pa_hull A2) with (pa_hull A); rewrite ?VIEW.
      - exact RI2.
      - exact HIST2.
      - exact MI'.
      - exact STK'.
      - exact PF'.
      - exact RR'.
      - exact DF'.
      - exact I.
      - unfold A2, recA2. cbn [a_qlimbo]. replace (q_bytes R) with psum by (unfold psum; rewrite BSR, lsum_bsl; reflexivity).
        unfold psum. pose proof HBYT as X. unfold psum in X.
        assert (RNG : 0 <= q_bytes rest).
        { apply q_bytes_nonneg. intros e He.
          destruct (qentry_wf Ax v [rm] AR e ltac:(apply q_in_big; rewrite QT0, QG0, APP; cbn [app]; unfold q_entries in *; rewrite flat_map_app; apply in_or_app; right; exact He)) as [N _].
          clear -N. lia. }
        clear -X RNG QBB GQE. unfold gqb in *. lia. }
    assert (NER : R <> []) by (intros E; rewrite E in LR; cbn in LR; clear -LR K1; lia).
    specialize (KH A2 (munrestrict (hidc (pa_hull A)) m m') md' scr (wz recycle_ret) (wz 0xb23e0) (wz (thr + 208)) (wz stkobj) a4' a5' a6' a7' t0' t1' t2' t3 t4 t5 t6
                  (wz (thr + 208)) (wz (2^20)) s7 s8 s9 R NER CU2 eq_refl).
    unfold head_cfgG in KH. rewrite LR in KH. fold kz in KH. exact KH.
  Qed.
End RE.

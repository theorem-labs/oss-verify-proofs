(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.openssl.bignum.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocKit_A2.
From OSSVerify.Proofs.openssl.bignum.lib.BgU Require Import F_memcpy.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres MallocModel_B F_ntf_B MallocKit_B MallocKit_B2 MallocKit_B3.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require KStepLite.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P F_alloc_meta.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A2 RF_ntf_A.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocU Require Import RF_am_A RF_am_K RF_am_K2 RF_am_C RF_am_D RF_am_E RF_am_F RF_am_G RF_am_H RF_am_P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.

From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (rwview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.

Lemma rrw_cells_magree C m m' A cs :
  rw_cells bgusegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells bgusegs m' A cs.
Proof.
  intros cells agree away.
  exact (rpres_except_rw_cells C m m' A cs (rpres_of_magree C m m' agree) cells away).
Qed.
Lemma rbytes_at_magree C m m' A bs :
  bytes_at bgusegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at bgusegs m' A bs.
Proof.
  intros bytes agree away.
  exact (rpres_except_bytes_at C m m' A bs (rpres_of_magree C m m' agree) bytes away).
Qed.

Lemma rauxv_ok_magree C m m' B :
  rauxv_ok m B -> magree C m m' -> (forall a, C a -> a < B /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8)) -> rauxv_ok m' B.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AC & AL & RN & H) AG HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rrw_cells_magree; [exact AC| exact AG|]. cbn. intros a Ha X. destruct (HC a X) as [_ Y]. apply Y. exact Ha.
  - eapply rbytes_at_magree; [exact AL| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _].
    unfold auxv_list in Ha. rewrite u64s_length, map_length in Ha. cbn in Ha. lia.
  - eapply rbytes_at_magree; [exact RN| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _]. rewrite length_le8 in Ha. lia.
Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk bgusegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells bgusegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv bgusegs m.
Hypothesis TP : tp = Z_to_bv 64 0x330f98.
Hypothesis KH : forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     rimplT o (k st1 mo) s' Q ms'.

Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. left. apply ram_fp_alloc_fp. exact H. Qed.

Lemma rETP : errno_addr tp = 0x330f98 - 164.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). rewrite TP, unsigned_lit by lia. reflexivity. Qed.

Lemma rfinish_K : forall (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
  am_rel st st1 mo -> rmrep st1 m' -> mem_inv bgusegs m' -> stk bgusegs m' lo (bv_unsigned sp) ->
  rw_cells bgusegs m' (errno_addr tp) [C4 e] -> rauxv_ok m' (bv_unsigned sp) -> magree (rFP st1) m m' ->
  brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rv = pw st1 mo ->
  rimplT o (k st1 mo) sX Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bgusegs)).
Proof using TK KH.
  intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv.
  intros rel1 rep1 inv1 stk1 errno1 auxv1 agree1 link1 sameM sameFa sameSo retv.
  assert (ticks1 : ticks_ok st1).
  { unfold ticks_ok. rewrite (amr_shadow _ _ _ rel1), (amr_tick _ _ _ rel1). exact TK. }
  pose proof (rpres_of_magree (rFP st1) m m' agree1) as pres1.
  subst rv.
  apply KH; [|exact link1].
  unfold ram_post.
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', e.
  exact (conj eq_refl (conj inv1 (conj stk1 (conj errno1 (conj auxv1 (conj pres1
          (conj rep1 (conj ticks1 (conj sameM (conj sameFa (conj sameSo rel1))))))))))).
Qed.

Lemma rFP_mono stX stY a :
  (forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rFP stX a -> rFP stY a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
  destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
  assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
  { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
  unfold lr_lo in *. rewrite K', B'. lia.
Qed.

Lemma rFP_same stX stY a : s_regions stY = s_regions stX -> rFP stX a -> rFP stY a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros E. apply rFP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.

Lemma rFP_below stX a : rregions_wf stX -> rFP stX a -> a < bv_unsigned sp /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold RAUXV_CELL, RLIBC, RCTX, RAM_STACK, OSSVerify.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *;
    rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
  - destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). pose proof (lr_lo_ge r). unfold OSSVerify.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - pose proof (rfresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. unfold OSSVerify.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in C; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
Qed.

Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros WF X. rewrite TP. eapply ram_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.

Lemma ram_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
  am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
  = kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). reflexivity. Qed.
Lemma rconc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. reflexivity. Qed.
Lemma rbrk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
Lemma rconc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

Lemma rcarve_K : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
    (x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  AMI st stY -> c_init_done (ctx stY) <> 0 ->
  (s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
  (forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
  rmrep stY mX -> mem_inv bgusegs mX -> bytes_at bgusegs mX (conc stY p) (zeros 4096) -> wr_at bgusegs mX (conc stY p) 4096 ->
  rw_cells bgusegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk bgusegs mX lo (bv_unsigned sp + -64) ->
  rw_cells bgusegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (k (am_took (carve_st stY p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR))) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b18f8) fc None mX (seg_rom bgusegs)).
Proof using AMP TK LO LOLE TP KH.
  intros stY p r mX sX junk e x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros amiY initY regY kindY offLo offHi alignY lrloY freeY slotsY tailY countY repY invY zeroY wrY
    frameY stkY errY auxY agrY linkY sameM sameFa sameSo.
  pose proof (proj1 repY) as wfY.
  assert (regsC : s_regions (carve_st stY p) = s_regions stY) by apply carve_st_regions.
  assert (fpC : forall a, ram_fp (carve_st stY p) lo (bv_unsigned sp) a -> ram_fp stY lo (bv_unsigned sp) a)
    by (intros a; apply (ram_fp_same stY (carve_st stY p) lo (bv_unsigned sp) a regsC)).
  assert (regsT : s_regions (am_took (carve_st stY p) (aadd p AREA_HDR) 100) = s_regions stY) by exact regsC.
  assert (stackRoom : lo <= bv_unsigned sp - 64) by (unfold RAM_STACK in LOLE; lia).
  eapply rimplT_evt.
  { eapply ram_carve_walk with (raw := ra) (s0o := s0) (s1o := s1) (s2o := s2) (s3o := s3) (s4o := s4)
              (junk := junk) (lo := lo) (st := stY) (p := p) (r := r); try eassumption.
    exact (ami_secretr _ _ amiY). }
  intros ms' (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & mY & -> & presY & _ & invY' & stkY' & repY').
  apply (rfinish_K _ _ sX mY e); try assumption.
  - exact (ram_rel_carve st stY p r amiY regY kindY freeY slotsY tailY).
  - apply (rpres_except_rw_cells _ _ _ _ _ presY errY).
    intros a errnoCell inFP. change (Z.of_nat (cells_size [C4 e])) with 4 in errnoCell.
    exact (rerrno_not_amfp stY a wfY (fpC a inFP) errnoCell).
  - apply (rauxv_ok_magree _ mX mY _ auxY (rmagree_of_pres _ _ _ presY)).
    intros a inFP. exact (rFP_below stY a wfY (rFP_am stY a (fpC a inFP))).
  - apply (magree_trans _ _ _ m mX mY agrY (rmagree_of_pres _ _ _ presY)); intros a inA.
    + exact (rFP_same stY _ a regsT inA).
    + exact (rFP_same stY _ a regsT (rFP_am stY a (fpC a inA))).
  - revert linkY. unfold brk_link_ps. rewrite rbrk_am_took, rbrk_carve.
    destruct (c_brk (ctx stY)); try rewrite rconc_am_took, rconc_carve; tauto.
  - unfold pw, oconc, wz. rewrite rconc_am_took, rconc_carve.
    unfold conc, get_region, aadd. cbn [fst snd]. rewrite regY. unfold AREA_HDR. f_equal. lia.
Qed.

Lemma rrepfoot_low stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros WF H. rewrite rETP. pose proof WF as (_ & WR & _ & WA & WG). unfold OSSVerify.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  destruct H as [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *; try lia.
  - destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold OSSVerify.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold OSSVerify.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold OSSVerify.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
Qed.

Lemma rfinish_path : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  AMI st stY -> c_init_done (ctx stY) <> 0 -> c_avail_meta_areas (ctx stY) = Some p ->
  (s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
  (forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
  rmrep stY mX -> mem_inv bgusegs mX ->
  rw_cells bgusegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk bgusegs mX lo (bv_unsigned sp + -64) ->
  rw_cells bgusegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (am_finish stY true k bail) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b1988) fc None mX (seg_rom bgusegs)).
Proof using AMP TK LO LOLE TP KH.
  intros stY p r mX sX junk e x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros amiY initY availY regY kindY offLo offHi alignY lrloY freeY slotsY tailY countY repY invY
    frameY stkY errY auxY agrY linkY sameM sameFa sameSo.
  pose proof (proj1 repY) as wfY.
  pose proof repY as (_ & _ & (_ & _ & pgszY & _) & _).
  destruct (proj1 (proj2 wfY) _ _ regY) as (baseLo & baseAl & _ & topHi & resvFree).
  assert (concY : conc stY p = r_base r + p.2) by (unfold conc, get_region; rewrite regY; reflexivity).
  pose proof (rreserved_disjoint1 _ _ resvFree ltac:(lia)) as sideY.
  pose proof (u64_range sp) as spRange.
  assert (spDown : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64)
    by (apply unsigned_lit; unfold RAM_STACK in LOLE; lia).
  assert (tpVal : bv_unsigned tp = 3346328) by (rewrite TP; apply unsigned_lit; lia).
  assert (aligned : (p.2 mod PGSZ =? 0) = true) by (apply Z.eqb_eq; exact alignY).
  unfold am_finish. rewrite availY, am_carve_took. cbv beta iota zeta. rewrite aligned. cbv beta iota delta [negb].
  eapply rimplT_evt; [apply ram_to_mprotect|].
  intros ms0 ->.
  eapply rimplT_mprotect.
  { apply rimpl_enode_dec_weaken with (dec := dec_mprotect (conc stY p) PGSZ);
      [|exact (dec_mprotect_rw_weaken (conc stY p) PGSZ)].
    apply rmprotect_spec with (lo := lo) (errv := e).
    - rewrite spDown. exact stkY.
    - exact errY.
    - exact pgszY.
    - exact invY.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite concY, Z.add_mod, baseAl by lia. unfold pgal in alignY. rewrite alignY. reflexivity.
    - reflexivity.
    - lia.
    - unfold PGSZ. lia.
    - unfold PGSZ. lia.
    - unfold PROT_RW. lia.
    - rewrite spDown. unfold RAM_STACK in LOLE. lia.
    - rewrite spDown, tpVal. unfold RAM_STACK in LOLE. lia.
    - left. unfold PGSZ. lia.
    - rewrite tpVal, concY. unfold PGSZ. lia.
    - rewrite concY. unfold PGSZ. lia.
    - lia.
    - rewrite tpVal. unfold RPAGE_SIZE. lia.
    - rewrite tpVal. lia.
    - unfold PGSZ. lia. }
  intros ans ms1 (post1 & strict).
  destruct post1 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & -> & munch1 & mono1 & inv1 & stk1 & errno1 & _ & shape1).
  rewrite spDown in munch1, stk1.
  assert (avoidFoot : ivs_avoid [(bv_unsigned sp + -64 - 32, bv_unsigned sp + -64); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4); (conc stY p, conc stY p + PGSZ)] (rrepfoot stY)).
  { intros l h a inW range foot. destruct (rrepfoot_low stY a wfY foot) as [below notErrno].
    destruct inW as [hit|[hit|[hit|[]]]]; injection hit as <- <-.
    - unfold RAM_STACK in LOLE. lia.
    - exact (notErrno range).
    - unfold PGSZ in range.
      exact (rfresh_page_avoids stY mX p r a repY regY kindY offLo offHi alignY lrloY freeY range foot). }
  assert (coverFP : ivs_covered (rFP stY) [(bv_unsigned sp + -64 - 32, bv_unsigned sp + -64); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4); (conc stY p, conc stY p + PGSZ)]).
  { cbn [ivs_covered]. refine (conj _ (conj _ (conj _ I))); intros a range.
    - left. left. unfold RAM_STACK in LOLE. lia.
    - left. right. left. rewrite TP in range. exact range.
    - left. right. right. right. exists p.1, r. split; [exact regY|]. split; [exact kindY|].
      rewrite concY in range. unfold PGSZ in range. lia. }
  pose proof (rmrep_transport_unowned stY mX m1 _ repY munch1 mono1 avoidFoot) as rep1.
  pose proof (magree_of_munch _ _ mX m1 munch1 coverFP) as agree1.
  pose proof (rauxv_ok_magree _ mX m1 _ auxY agree1 (fun a inFP => rFP_below stY a wfY inFP)) as aux1.
  pose proof (magree_trans _ _ _ m mX m1 agrY agree1 (fun a h => h) (fun a h => h)) as agreeM1.
  assert (frame1 : rw_cells bgusegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
  { apply (rrw_cells_magree (fun a => ~ outside [(bv_unsigned sp + -64 - 32, bv_unsigned sp + -64); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4); (conc stY p, conc stY p + PGSZ)] a) mX m1 _ _ frameY).
    - apply (magree_of_munch _ _ mX m1 munch1). cbn [ivs_covered outside].
      repeat split; intros x range away; tauto.
    - intros a range inW. apply inW. cbn [outside].
      change (Z.of_nat (cells_size (ram_frame junk s4 s3 s2 s1 s0 ra))) with 64 in range.
      rewrite tpVal, concY. unfold PGSZ, RAM_STACK in *. lia. }
  destruct ans as [err | changed]; cbn [mp_strict] in strict; cbn [F_mm_syscalls.rg_errno] in errno1; cbv beta.
  - assert (okErr : mprotect_answer_ok (range_val (RgErr err)) = true).
    { unfold mprotect_answer_ok, is_errno_form, range_val, neg_errno, TWO64.
      apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    assert (notCarve : ((range_val (RgErr err) =? 0) || (range_val (RgErr err) =? TWO64 - ENOSYS)) = false).
    { unfold range_val, neg_errno, TWO64, ENOSYS. apply orb_false_iff. split; apply Z.eqb_neq; lia. }
    rewrite okErr, notCarve. cbv beta iota delta [negb].
    cbn [F_mm_syscalls.munmap_ret]. rewrite ret_pc_even by first [lia | reflexivity].
    eapply rimplT_evt.
    { apply ram_mp_fail with (m0 := m1) (junk := junk) (lo := lo) (e := err) (st := stY)
        (raw := ra) (s0o := s0) (s1o := s1) (s2o := s2) (s3o := s3) (s4o := s4); try assumption.
      - apply rpres_except_refl.
      - intros x keep. exact keep.
      - unfold RAM_STACK in LOLE. lia. }
    intros ms2 ((w0 & w1 & w2 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & w3 & w4 & w5 & w6 & m2 & -> & pres2 & _ & inv2 & stk2 & rep2) & errno2).
    cbn [ms_mem] in errno2.
    apply (rfinish_K stY None sX m2 (Z_to_bv 64 err)); try assumption.
    + exact (ram_rel_none st stY amiY).
    + exact (rauxv_ok_magree _ m1 m2 _ aux1 (rmagree_of_pres _ _ _ pres2) (fun a inFP => rFP_below stY a wfY (rFP_am stY a inFP))).
    + exact (magree_trans _ _ _ m m1 m2 agreeM1 (rmagree_of_pres _ _ _ pres2) (fun a h => h) (fun a h => rFP_am stY a h)).
    + reflexivity.
  - subst changed.
    cbn [range_val mprotect_answer_ok negb orb Z.eqb F_mm_syscalls.munmap_ret].
    rewrite ret_pc_even by first [lia | reflexivity].
    eapply rimplT_evt; [apply ram_mp_ok0|].
    intros ms2 ->.
    apply (rcarve_K stY p r m1 sX junk e); try assumption.
    + pose proof (rw_cells_bytes_at _ _ _ _ shape1) as zeros1. exact zeros1.
    + exact (proj2 shape1).
Qed.

Lemma rlive_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

Lemma rfresh_of_ranges_free stY x L a :
  s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
  ranges_free (live_ranges stY) x L = true -> x + L <= alloc_ceiling -> x <= a < x + L -> fresh_addr st a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros E1 E2 RF XC Ha. split; [lia|]. rewrite (rlive_ranges_same st stY E1 E2) in RF.
  eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.

Lemma rrepfoot_clear stY mY x L a :
  rmrep stY mY -> ranges_free (live_ranges stY) x L = true -> rrepfoot stY a \/ rgrp_region_addr stY a -> ~ (x <= a < x + L).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MRY RF H. pose proof MRY as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  pose proof (clear_range_of_ranges_free stY x L RF) as CR.
  assert (IMG : forall y, 0x10000 <= y < 0x353000 -> ~ (x <= y < x + L)) by (intros y Hy; apply (rimage_clear_of_ranges_free stY x L y RS RF Hy)).
  destruct H as [[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]|C]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *.
  - apply IMG. lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - destruct C as (ak & ar & Hak & Hin). destruct (WA ak ar Hak) as (rra & Hra & _).
    eapply (CR (fst ak) rra a Hra). eapply rarea_in_live; eauto.
  - destruct C as (b & gh & Hb & Hin). destruct (WG b gh Hb) as (rb & Hrb & _).
    eapply (CR (fst b) rb a Hrb). eapply rgroup_in_live; eauto.
  - destruct C as (rid & rg & v & Hrg & Krg & Hin & _). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - destruct C as (rid & rg & Hrg & Krg & Hin). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
Qed.

Lemma rmmap_path : forall (stY : mstate) (mX : mem) (sX : PState) (junk : list byte) (e : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  AMI st stY -> c_init_done (ctx stY) <> 0 -> s_regions stY = s_regions st -> c_avail_meta_area_count (ctx stY) = 0 ->
  0 <= c_meta_alloc_shift (ctx stY) <= 38 ->
  (forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
  (forall q mr, (s_metas stY) !! q = Some mr -> meta_slot stY q) ->
  ptrs_in (fun rid => (rid < s_next_rid stY)%N) stY ->
  rmrep stY mX -> mem_inv bgusegs mX ->
  rw_cells bgusegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk bgusegs mX lo (bv_unsigned sp + -64) ->
  rw_cells bgusegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (am_after_brk stY true k bail) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b1898) fc None mX (seg_rom bgusegs)).
Proof using AMP TK LO LOLE TP KH.
  intros stY mX sX junk e x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros amiY initY regsY countY shiftY tailY keysY ptrsY repY invY frameY stkY errY auxY agrY linkY sameM sameFa sameSo.
  pose proof (proj1 repY) as wfY.
  pose proof (u64_range sp) as spRange.
  assert (spDown : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64)
    by (apply unsigned_lit; unfold RAM_STACK in LOLE; lia).
  assert (tpVal : bv_unsigned tp = 3346328) by (rewrite TP; apply unsigned_lit; lia).
  assert (resvY : s_reserved stY = s_reserved st) by exact (ami_reserved _ _ amiY).
  pose (n := 2 ≪ c_meta_alloc_shift (ctx stY)).
  pose (len := n * PGSZ).
  assert (nVal : n = 2 * 2 ^ c_meta_alloc_shift (ctx stY)) by (apply Z.shiftl_mul_pow2; lia).
  assert (powLo : 0 < 2 ^ c_meta_alloc_shift (ctx stY)) by (apply Z.pow_pos_nonneg; lia).
  assert (powHi : 2 ^ c_meta_alloc_shift (ctx stY) <= 2 ^ 38) by (apply Z.pow_le_mono_r; lia).
  assert (lenRange : 8192 <= len <= 2 ^ 51) by (unfold len, PGSZ; rewrite nVal; lia).
  unfold am_after_brk. rewrite countY. change (0 =? 0) with true. cbv beta iota zeta.
  eapply rimplT_evt; [apply ram_to_mmap; [exact repY | lia]|].
  intros ms0 ->.
  eapply rimplT_mmap_none.
  { apply (rmmap_anon_spec true) with (lo := lo) (errv := e) (avoid := []).
    - rewrite spDown. exact stkY.
    - exact errY.
    - exact invY.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - change (2 ≪ c_meta_alloc_shift (ctx stY) * PGSZ) with len. lia.
    - rewrite spDown. unfold RAM_STACK in LOLE. lia.
    - exact LO.
    - rewrite spDown, tpVal. unfold RAM_STACK in LOLE. lia.
    - rewrite tpVal. lia. }
  intros ans ms1 post1.
  destruct ans as [err | x]; cbv beta.
  - destruct post1 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & -> & munch1 & mono1 & inv1 & stk1 & errno1 & errRange).
    rewrite spDown in munch1, stk1.
    assert (answerOk : mmap_answer_ok (live_ranges stY) (2 ≪ c_meta_alloc_shift (ctx stY) * PGSZ) (mmap_val (MmErr err)) = true).
    { unfold mmap_answer_ok, is_errno_form, mmap_val, neg_errno, TWO64.
      apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    assert (answerErr : is_err (mmap_val (MmErr err)) = true).
    { unfold is_err, mmap_val, neg_errno, TWO64. apply Z.ltb_lt. lia. }
    rewrite answerOk, answerErr. cbv beta iota delta [negb].
    rewrite ret_pc_even by first [lia | reflexivity].
    assert (avoid1 : ivs_avoid [(bv_unsigned sp + -64 - 80, bv_unsigned sp + -64); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] (rrepfoot stY)).
    { intros l h a inW range foot. destruct (rrepfoot_low stY a wfY foot) as [below notErrno].
      destruct inW as [hit|[hit|[]]]; injection hit as <- <-.
      - unfold RAM_STACK in LOLE. lia.
      - exact (notErrno range). }
    assert (cover1 : ivs_covered (rFP stY) [(bv_unsigned sp + -64 - 80, bv_unsigned sp + -64); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)]).
    { cbn [ivs_covered]. refine (conj _ (conj _ I)); intros a range.
      - left. left. unfold RAM_STACK in LOLE. lia.
      - left. right. left. rewrite TP in range. exact range. }
    pose proof (rmrep_transport_unowned stY mX m1 _ repY munch1 mono1 avoid1) as rep1.
    pose proof (magree_of_munch _ _ mX m1 munch1 cover1) as agree1.
    pose proof (rauxv_ok_magree _ mX m1 _ auxY agree1 (fun a inFP => rFP_below stY a wfY inFP)) as aux1.
    pose proof (magree_trans _ _ _ m mX m1 agrY agree1 (fun a keep => keep) (fun a keep => keep)) as agreeM1.
    assert (frame1 : rw_cells bgusegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { apply (rrw_cells_magree (fun a => ~ outside [(bv_unsigned sp + -64 - 80, bv_unsigned sp + -64); (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] a) mX m1 _ _ frameY).
      - apply (magree_of_munch _ _ mX m1 munch1). cbn [ivs_covered outside].
        repeat split; intros y range away; tauto.
      - intros a range inW. apply inW. cbn [outside].
        change (Z.of_nat (cells_size (ram_frame junk s4 s3 s2 s1 s0 ra))) with 64 in range.
        rewrite tpVal. unfold RAM_STACK in LOLE. lia. }
    eapply rimplT_evt.
    { apply ram_mm_fail with (m0 := m1) (junk := junk) (lo := lo) (st := stY)
        (raw := ra) (s0o := s0) (s1o := s1) (s2o := s2) (s3o := s3) (s4o := s4); try assumption.
      - apply rpres_except_refl.
      - intros y keep. exact keep.
      - unfold RAM_STACK in LOLE. lia. }
    intros ms2 (w0 & w1 & w2 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & w3 & w4 & w5 & w6 & m2 & -> & pres2 & _ & inv2 & stk2 & rep2).
    apply (rfinish_K stY None sX m2 (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno err))); try assumption.
    + exact (ram_rel_none st stY amiY).
    + apply (rpres_except_rw_cells _ _ _ _ _ pres2 errno1).
      intros a errnoCell inFP. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno err))])) with 4 in errnoCell.
      exact (rerrno_not_amfp stY a wfY inFP errnoCell).
    + exact (rauxv_ok_magree _ m1 m2 _ aux1 (rmagree_of_pres _ _ _ pres2) (fun a inFP => rFP_below stY a wfY (rFP_am stY a inFP))).
    + exact (magree_trans _ _ _ m m1 m2 agreeM1 (rmagree_of_pres _ _ _ pres2) (fun a keep => keep) (fun a inFP => rFP_am stY a inFP)).
    + reflexivity.
  - destruct post1 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & munch2 & mono2 & inv2 & stkRaw & errno2 & addrOk).
    rewrite spDown in munch2, stkRaw.
    unfold mmap_addr_ok in addrOk. rewrite !andb_true_iff in addrOk.
    destruct addrOk as (((alignX & posX) & topX) & _).
    apply Z.eqb_eq in alignX. apply Z.ltb_lt in posX. apply Z.leb_le in topX.
    rewrite KStepLite.page_size_eq in alignX. rewrite mmap_len_round_up in topX.
    assert (roundLen : round_up_pg len = len).
    { apply round_up_pg_aligned. unfold len, PGSZ. apply Z.mod_mul. lia. }
    change (2 ≪ c_meta_alloc_shift (ctx stY) * PGSZ) with len in *.
    rewrite roundLen in topX.
    cbn [mmap_val].
    destruct (mmap_answer_ok (live_ranges stY) len x) eqn:answerOk; cbv beta iota delta [negb].
    2: { unfold bad_answer. apply rimplT_undef. }
    assert (freeX : ranges_free (live_ranges stY) x len = true).
    { unfold mmap_answer_ok in answerOk. rewrite roundLen in answerOk.
      apply orb_true_iff in answerOk. destruct answerOk as [errForm | fine].
      - exfalso. unfold is_errno_form, TWO64 in errForm. apply andb_true_iff in errForm. destruct errForm as [tooBig _].
        apply Z.leb_le in tooBig. lia.
      - apply andb_true_iff in fine. exact (proj2 fine). }
    assert (answerErr : is_err x = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia).
    rewrite answerErr. cbv beta iota.
    destruct (new_region RKMeta x len stY) as [st1 rid] eqn:newEq. cbv beta iota.
    assert (st1Eq : (new_region RKMeta x len stY).1 = st1) by (rewrite newEq; reflexivity).
    assert (ridEq : rid = s_next_rid stY) by (unfold new_region in newEq; injection newEq as _ <-; reflexivity).
    subst rid.
    pose (rN := {| r_kind := RKMeta; r_base := x; r_len := len |}).
    pose proof (rAMI_new_region st stY RKMeta x len amiY ltac:(discriminate) ltac:(lia)) as (ami1 & lookupNew & concOld & concNew).
    rewrite st1Eq in ami1, lookupNew, concOld, concNew.
    assert (lookupOld : forall q rq, s_regions stY !! q = Some rq -> s_regions st1 !! q = Some rq).
    { intros q rq found. rewrite <- st1Eq. rewrite rnr_lookup_old; [exact found|].
      intros same. subst q. destruct (ami_fresh _ _ amiY (s_next_rid stY) (N.le_refl _)) as [noReg _].
      rewrite noReg in found. discriminate. }
    pose proof (u64_range tp) as tpRange.
    assert (clearX : forall a, 65536 <= a < 3485696 -> ~ (x <= a < x + len))
      by (intros a imageA; exact (rimage_clear_of_ranges_free stY x len a (proj1 wfY) freeX imageA)).
    assert (avoid2 : ivs_avoid [(bv_unsigned sp + -64 - 80, bv_unsigned sp + -64)] (rrepfoot stY)).
    { intros l h a inW range foot. destruct (rrepfoot_low stY a wfY foot) as [below _].
      destruct inW as [hit|[]]; injection hit as <- <-. unfold RAM_STACK in LOLE. lia. }
    pose proof (rmrep_transport_unowned stY mX m2 _ repY munch2 mono2 avoid2) as rep2.
    assert (cover2 : ivs_covered (rFP stY) [(bv_unsigned sp + -64 - 80, bv_unsigned sp + -64)]).
    { cbn [ivs_covered]. refine (conj _ I). intros a range. left. left. unfold RAM_STACK in LOLE. lia. }
    pose proof (magree_of_munch _ _ mX m2 munch2 cover2) as agree2.
    assert (frame2 : rw_cells bgusegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { apply (rrw_cells_magree (fun a => ~ outside [(bv_unsigned sp + -64 - 80, bv_unsigned sp + -64)] a) mX m2 _ _ frameY).
      - apply (magree_of_munch _ _ mX m2 munch2). cbn [ivs_covered outside].
        repeat split; intros y range away; tauto.
      - intros a range inW. apply inW. cbn [outside].
        change (Z.of_nat (cells_size (ram_frame junk s4 s3 s2 s1 s0 ra))) with 64 in range. lia. }
    assert (rawSpec : forall a, 0 <= a < 2 ^ 64 -> a < x \/ x + len <= a -> F_mm_syscalls.mmap_raw true x len m2 (wa a) = m2 (wa a)).
    { intros a aRange away. unfold F_mm_syscalls.mmap_raw. rewrite mmap_len_round_up, roundLen.
      apply unmaps_outside; [lia | lia | lia |]. unfold wa. rewrite unsigned_lit by lia. exact away. }
    assert (repRaw : rmrep st1 (F_mm_syscalls.mmap_raw true x len m2)).
    { rewrite <- st1Eq. apply (rmrep_new_region stY m2); try assumption.
      - apply (ptrs_in_mono (fun q => (q < s_next_rid stY)%N) _ stY); [|exact ptrsY]. intros q below same. subst q. lia.
      - exact (proj2 (ami_fresh _ _ amiY (s_next_rid stY) (N.le_refl _))).
      - lia.
      - rewrite roundLen. lia.
      - rewrite roundLen. exact freeX.
      - intros a aRange away. rewrite roundLen in away. exact (rawSpec a aRange away).
      - discriminate. }
    assert (agreeRaw : magree (rFP stY) m2 (F_mm_syscalls.mmap_raw true x len m2)).
    { intros a aRange notFP. apply rawSpec; [exact aRange|].
      destruct (Z.lt_ge_cases a x) as [lowA | highA]; [left; exact lowA|].
      destruct (Z.lt_ge_cases a (x + len)) as [inA | pastA]; [|right; exact pastA].
      exfalso. apply notFP. right. exact (rfresh_of_ranges_free stY x len a regsY resvY freeX ltac:(lia) ltac:(lia)). }
    assert (frameRaw : rw_cells bgusegs (F_mm_syscalls.mmap_raw true x len m2) (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { unfold F_mm_syscalls.mmap_raw. rewrite mmap_len_round_up, roundLen.
      apply rw_cells_unmaps_other; [lia | lia | lia | exact frame2 |].
      change (Z.of_nat (cells_size (ram_frame junk s4 s3 s2 s1 s0 ra))) with 64. right. unfold RAM_STACK in LOLE. lia. }
    assert (errnoRaw : rw_cells bgusegs (F_mm_syscalls.mmap_raw true x len m2) (bv_unsigned tp + -164) [C4 e]).
    { unfold F_mm_syscalls.mmap_raw. rewrite mmap_len_round_up, roundLen.
      apply rw_cells_unmaps_other; [lia | lia | lia | exact errno2 |].
      change (Z.of_nat (cells_size [C4 e])) with 4. rewrite tpVal.
      destruct (Z.lt_ge_cases x 3346164) as [lowX | highX].
      - right. destruct (Z.le_gt_cases (x + len) 3346164) as [fits | crosses]; [lia|].
        exfalso. apply (clearX 3346164); lia.
      - left. destruct (Z.le_gt_cases 3346168 x) as [above | inside]; [lia|].
        exfalso. apply (clearX x); lia. }
    rewrite ret_pc_even by first [lia | reflexivity].
    eapply rimplT_evt.
    { apply ram_mm_ok with (m0 := F_mm_syscalls.mmap_raw true x len m2) (st0 := stY) (st := st1) (rid := s_next_rid stY)
        (r := rN) (junk := junk) (lo := lo) (raw := ra) (s0o := s0) (s1o := s1) (s2o := s2) (s3o := s3) (s4o := s4); try assumption.
      - unfold F_mm_syscalls.mmap_raw. rewrite mmap_len_round_up, roundLen. apply mem_inv_unmaps; [lia | lia | lia | exact inv2].
      - intros a [stackA | [ctxA | (q & rq & foundQ & kindQ & liveQ)]].
        + left. exact stackA.
        + right. left. exact ctxA.
        + right. right. exists q, rq. exact (conj (lookupOld q rq foundQ) (conj kindQ liveQ)).
      - reflexivity.
      - lia.
      - fold n. rewrite nVal. lia.
      - replace (ctx st1) with (ctx stY) by (rewrite <- st1Eq; reflexivity). lia.
      - apply rpres_except_refl.
      - intros y keep. exact keep.
      - unfold RAM_STACK in LOLE. lia. }
    intros ms2 (m3 & -> & pres3 & _ & inv3 & frame3 & stk3 & rep3).
    pose (st2 := mm_ok_st st1 (s_next_rid stY) n).
    assert (regs2 : s_regions st2 = s_regions st1) by reflexivity.
    assert (conc2 : conc st2 (s_next_rid stY, 4096) = x + 4096) by exact (concNew 4096).
    assert (grow2 : forall q rq, s_regions stY !! q = Some rq ->
                    exists rq', s_regions st2 !! q = Some rq' /\ r_kind rq' = r_kind rq /\ r_base rq' = r_base rq /\ r_len rq <= r_len rq').
    { intros q rq found. exists rq. rewrite regs2. split; [exact (lookupOld q rq found)|].
      split; [reflexivity|]. split; [reflexivity|]. lia. }
    pose proof (proj1 rep3) as wf2.
    assert (fp1to2 : forall a, ram_fp st1 lo (bv_unsigned sp) a -> rFP st2 a)
      by (intros a inFP; exact (rFP_same st1 st2 a regs2 (rFP_am st1 a inFP))).
    assert (agreeM3 : magree (rFP st2) m m3).
    { intros a aRange notFP.
      assert (notFPY : ~ rFP stY a) by (intros inY; apply notFP; exact (rFP_mono stY st2 a grow2 inY)).
      rewrite (rmagree_of_pres _ _ _ pres3 a aRange (fun inFP => notFP (fp1to2 a inFP))).
      rewrite (agreeRaw a aRange notFPY), (agree2 a aRange notFPY).
      exact (agrY a aRange notFPY). }
    assert (agreeX3 : magree (rFP st2) mX m3).
    { intros a aRange notFP.
      assert (notFPY : ~ rFP stY a) by (intros inY; apply notFP; exact (rFP_mono stY st2 a grow2 inY)).
      rewrite (rmagree_of_pres _ _ _ pres3 a aRange (fun inFP => notFP (fp1to2 a inFP))).
      rewrite (agreeRaw a aRange notFPY), (agree2 a aRange notFPY). reflexivity. }
    assert (ami2 : AMI st st2).
    { apply rAMI_ctx; [exact ami1 | | | |].
      - repeat split; reflexivity.
      - exact (ami_secretr _ _ ami1).
      - right. exists (s_next_rid stY, 4096), rN. split; [reflexivity|]. split; [exact lookupNew|]. discriminate.
      - left. reflexivity. }
    assert (areas2 : s_areas st2 = s_areas stY) by (unfold st2; rewrite <- st1Eq; reflexivity).
    assert (areaFresh : forall a ar, s_areas stY !! a = Some ar -> (a.1 < s_next_rid stY)%N).
    { intros a ar found. pose proof ptrsY as (_ & _ & _ & _ & _ & _ & _ & _ & areaP & _). exact (proj1 (areaP a ar found)). }
    replace (Z_to_bv 64 (x + 4096)) with (Z_to_bv 64 (conc st2 (s_next_rid stY, 4096))) by (rewrite conc2; reflexivity).
    apply (rfinish_path st2 (s_next_rid stY, 4096) rN m3 sX junk e); try assumption.
    + change (c_init_done (ctx st1) <> 0). replace (ctx st1) with (ctx stY) by (rewrite <- st1Eq; reflexivity). exact initY.
    + reflexivity.
    + discriminate.
    + cbn [snd]. lia.
    + unfold rN. cbn [snd r_len]. rewrite roundLen. lia.
    + reflexivity.
    + unfold rN. cbn [lr_lo r_kind r_base snd]. lia.
    + rewrite areas2. match goal with |- ?found = None => destruct found as [ar|] eqn:foundA; [|reflexivity] end.
      pose proof (areaFresh _ _ foundA) as below. cbn [fst] in below. lia.
    + intros j slotJ. replace (s_metas st2) with (s_metas stY) by (unfold st2; rewrite <- st1Eq; reflexivity).
      match goal with |- ?found = None => destruct found as [mr|] eqn:foundM; [|reflexivity] end.
      destruct (keysY _ _ foundM) as (a & ar & kk & foundA & _ & sameSlot).
      pose proof (areaFresh _ _ foundA) as below. apply (f_equal fst) in sameSlot. cbn [fst aadd] in sameSlot. rewrite <- sameSlot in below. lia.
    + intros tl tailIs. rewrite areas2. apply tailY. rewrite <- tailIs. unfold st2. rewrite <- st1Eq. reflexivity.
    + change (1 <= n - 1 < 2 ^ 64). rewrite nVal. lia.
    + apply (rpres_except_rw_cells _ _ _ _ _ pres3 errnoRaw).
      intros a errnoCell inFP. change (Z.of_nat (cells_size [C4 e])) with 4 in errnoCell.
      exact (rerrno_not_amfp st1 a (proj1 repRaw) inFP errnoCell).
    + exact (rauxv_ok_magree _ mX m3 _ auxY agreeX3 (fun a inFP => rFP_below st2 a wf2 inFP)).
    + revert linkY. unfold brk_link_ps. replace (c_brk (ctx st2)) with (c_brk (ctx stY)) by (unfold st2; rewrite <- st1Eq; reflexivity).
      pose proof ptrsY as (_ & _ & _ & _ & _ & _ & brkP & _).
      destruct (c_brk (ctx stY)) as [| | bid boff]; try tauto.
      intros linkOld. rewrite linkOld. unfold st2, conc, get_region. rewrite <- st1Eq.
      cbn [fst]. rewrite rnr_lookup_old; [reflexivity|]. intros same. rewrite same in brkP. lia.
Qed.

Lemma rimage_range_clear stY x L : s_reserved stY = ref_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
  x + L <= 0x10000 \/ 0x353000 <= x.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

Lemma rbrk_live_path : forall (stI : mstate) (brid : N) (boff : Z) (m1 : mem) (junk : list byte) (e1 : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  RAMpre stI -> AMI st stI -> c_init_done (ctx stI) <> 0 -> s_regions stI = s_regions st -> brk_link_ps stI s ->
  c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkLive brid boff ->
  ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
  rmrep stI m1 -> mem_inv bgusegs m1 ->
  rw_cells bgusegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk bgusegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells bgusegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  rimplT o (let old := conc stI (brid, boff) in
           let new := old + PGSZ in
           SVis (EBrk new) (fun r =>
             if negb (brk_answer_ok old new r) then bad_answer bail else
             if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
             else if negb (brk_pages_ok stI old PGSZ) then bad_answer bail
             else
               let st1 := upd_region brid (fun rg => mkRegion (r_kind rg) (r_base rg) (boff + PGSZ)) stI in
               let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (brid, boff)) (set_brk (BrkLive brid (boff + PGSZ)) c))) st1 in
               am_after_brk st2 false k bail)) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b17e8) fc None m1 (seg_rom bgusegs)).
Proof using AMP TK LO LOLE ERR TP KH.
  intros stI brid boff m1 junk e1 x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros preI amiI initI regsI linkI countI brkI ptrsI repI invI frameI stkI errI auxI agreeI.
  pose proof (proj1 repI) as wfI.
  pose proof (amp_brk stI preI) as liveI. rewrite brkI in liveI.
  destruct liveI as (r & regI & kindI & lenI & alignI & lowI & freshI & onlyI).
  unfold PGSZ in alignI, lowI.
  assert (kindNG : r_kind r <> RKGroup) by (rewrite kindI; discriminate).
  destruct (proj1 (proj2 wfI) _ _ regI) as (baseLo & baseAl & _ & topHi & _).
  rewrite lenI, (round_up_pg_aligned boff alignI) in topHi.
  assert (concAt : forall d, conc stI (brid, d) = r_base r + d)
    by (intros d; unfold conc, get_region; cbn [fst snd]; rewrite regI; reflexivity).
  pose proof (concAt boff) as oldEq.
  assert (linkOld : ps_brk s = conc stI (brid, boff))
    by (unfold brk_link_ps in linkI; rewrite brkI in linkI; exact linkI).
  pose proof (u64_range sp) as spRange.
  assert (tpVal : bv_unsigned tp = 3346328) by (rewrite TP; apply unsigned_lit; lia).
  unfold RAM_STACK in LOLE.
  cbv zeta. unfold PGSZ.
  eapply rimplT_evt.
  { apply ram_disp_live with (st := stI) (rid := brid) (off := boff); [exact repI | exact countI | exact brkI | lia | lia]. }
  intros ms0 ->.
  eapply rimplT_brk; [lia | apply ram_brk_node_at; [left; reflexivity | lia] |].
  intros [|] ms1 (-> & capOk); cbv beta iota in capOk |- *; rewrite linkOld.
  - unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
    destruct (brk_pages_ok stI (conc stI (brid, boff)) 4096) eqn:pagesOk; cbn [negb];
      [| unfold bad_answer; apply rimplT_undef].
    unfold brk_pages_ok in pagesOk. apply andb_true_iff in pagesOk as (_ & freeOld).
    pose proof (rimage_range_clear stI _ 4096 (proj1 wfI) freeOld ltac:(lia)) as pageClear.
    assert (pageRange : 0 <= conc stI (brid, boff) < 2 ^ 64) by lia.
    assert (pageEnd : conc stI (brid, boff) + 4096 <= 2 ^ 64) by lia.
    assert (oldAl : conc stI (brid, boff) mod 4096 = 0)
      by (rewrite oldEq, Z.add_mod, baseAl, alignI by lia; reflexivity).
    set (mB := apply_zeros m1 [(wa (conc stI (brid, boff)), Z_to_bv 64 4096)]).
    assert (memB : brk_mem m1 (conc stI (brid, boff)) (conc stI (brid, boff) + 4096) BrkGrown = mB).
    { unfold brk_mem. rewrite brk_new_pages_aligned by first [exact oldAl | reflexivity | lia]. reflexivity. }
    rewrite memB. cbn [brk_res].
    assert (munchB : munch [(conc stI (brid, boff), conc stI (brid, boff) + 4096)] m1 mB).
    { intros x outPage. cbn [outside] in outPage. pose proof (u64_range x) as xRange.
      apply zeros_outside; lia. }
    assert (monoB : wmono bgusegs m1 mB)
      by exact (wview_zeros_mono bgusegs m1 _ 4096 pageRange ltac:(lia) pageEnd).
    assert (invB : mem_inv bgusegs mB).
    { apply mem_inv_zeros; [exact pageRange | lia | exact pageEnd | exact invI | | unfold UTOP; lia].
      intros x inPage. apply ref_ro_addr_false. lia. }
    assert (avoidB : ivs_avoid [(conc stI (brid, boff), conc stI (brid, boff) + 4096)] (rrepfoot stI)).
    { intros l h a inW range foot. destruct inW as [hit|[]]. injection hit as <- <-.
      exact (rrepfoot_clear stI m1 _ 4096 a repI freeOld (or_introl foot) range). }
    pose proof (rmrep_transport_unowned stI m1 mB _ repI munchB monoB avoidB) as repB.
    pose proof repB as (_ & (headB & _ & _ & _ & _ & tailB) & _).
    assert (presB : rpres_except (fun a => conc stI (brid, boff) <= a < conc stI (brid, boff) + 4096) m1 mB).
    { apply (rpres_except_of_munch_cov _ _ m1 mB munchB monoB). cbn [ivs_covered].
      split; [intros x inPage; exact inPage | exact I]. }
    rewrite (am_after_brk_false_eq _ _ (brid, boff) k bail) by first [reflexivity | exact alignI | cbn; lia].
    rewrite am_carve_took, carve_st_brk_irrel, (rgr_eq stI brid r boff regI).
    set (grown := {| r_kind := r_kind r; r_base := r_base r; r_len := boff + 4096 |}).
    set (stW := set_regions (<[brid:=grown]> (s_regions stI)) stI).
    set (stC := upd_ctx (fun c : mctx => set_avail_meta_area_count 1 (set_brk (BrkLive brid (boff + 4096)) c)) stW).
    eapply rimplT_evt.
    { eapply ram_bl_ok; [lia | exact headB | exact tailB | exact invB]. }
    intros ms2 (mX & -> & munchX & monoX & invX & headX & tailX).
    set (stJ := upd_ctx (fun c : mctx => set_avail_meta_area_count 1 (set_brk (BrkLive brid (boff + 4096)) c)) stI).
    assert (tailJ : rw_cells bgusegs mX (RCTX + 912) (ctx_tail_cells stJ)).
    { assert (brkJ : brk_word stJ = conc stI (brid, boff) + 4096)
        by (change (conc stI (brid, boff + 4096) = conc stI (brid, boff) + 4096); rewrite !concAt; lia).
      unfold ctx_tail_cells. rewrite brkJ. exact tailX. }
    assert (repJ : rmrep stJ mX).
    { apply (rmrep_ctx_frameW stI stJ mB mX _ repB munchX monoX);
        [reflexivity .. | | left; exact headX | | | | | left; exact tailJ].
      all: try (right; split; [reflexivity |]).
      all: intros wLo wHi inW; destruct inW as [hit|[hit|[]]]; injection hit as <- <-; unfold RCTX; lia. }
    assert (repC : rmrep stC mX).
    { assert (freeBase : ranges_free (live_ranges stI) (r_base r + boff) 4096 = true) by (rewrite <- oldEq; exact freeOld).
      exact (rmrep_grow_region stJ mX brid r boff repJ regI kindNG lenI ltac:(lia) alignI freeBase ltac:(lia)
               (amp_rpos stI preI) (fun q rq lookQ otherQ brkQ => otherQ (onlyI q rq lookQ brkQ))). }
    assert (presX : rpres_except (fun a => RCTX <= a < RCTX + 928) mB mX).
    { apply (rpres_except_of_munch_cov _ _ mB mX munchX monoX). cbn [ivs_covered].
      refine (conj _ (conj _ I)); intros x inW; cbv beta; unfold RCTX in *; lia. }
    assert (pres1X : rpres_except (fun a => (conc stI (brid, boff) <= a < conc stI (brid, boff) + 4096) \/ (RCTX <= a < RCTX + 928)) m1 mX).
    { apply (rpres_except_trans _ m1 mB mX).
      - exact (rpres_except_mono _ _ m1 mB presB (fun a inPage => or_introl inPage)).
      - exact (rpres_except_mono _ _ mB mX presX (fun a inCtx => or_intror inCtx)). }
    assert (concC : forall q, conc stC q = conc stI q) by exact (rgr_conc stI brid r boff regI).
    replace (conc stI (brid, boff) + 4096 - 4096) with (conc stC (brid, boff)) by (rewrite concC; lia).
    apply (rcarve_K stC (brid, boff) grown mX (set_brk_ps (conc stI (brid, boff) + 4096) s) junk e1).
    + destruct (rAMI_grow st stI brid r boff amiI regI kindNG lenI) as (amiW & _ & _).
      apply rAMI_ctx; [exact amiW | unfold ctx_core_eq; repeat split | exact (ami_secretr _ _ amiI) | left; reflexivity |].
      right. right. exists brid, (boff + 4096), grown.
      exact (conj eq_refl (conj (rgr_lookup_new stI brid r boff) kindNG)).
    + exact initI.
    + exact (rgr_lookup_new stI brid r boff).
    + exact kindNG.
    + cbn [snd]. lia.
    + change (boff + 4096 <= round_up_pg (boff + 4096)).
      rewrite rgr_ru, (round_up_pg_aligned boff alignI) by first [exact alignI | lia]. lia.
    + exact alignI.
    + assert (lrGrown : lr_lo grown = r_base r + 4096)
        by (unfold lr_lo; change (r_kind grown) with (r_kind r); rewrite kindI; reflexivity).
      rewrite lrGrown. change (r_base r + 4096 <= r_base r + boff). lia.
    + exact (proj1 (freshI (brid, boff) eq_refl (Z.le_refl boff))).
    + intros j slotJ.
      exact (proj2 (freshI (aadd (brid, boff) (AREA_HDR + META_SIZE * j)) eq_refl
                      ltac:(cbn [aadd snd]; unfold AREA_HDR, META_SIZE, NSLOTS in *; lia))).
    + exact (amp_tail stI preI).
    + change (1 <= 1 < 2 ^ 64). lia.
    + exact repC.
    + exact invX.
    + rewrite concC.
      pose proof (bytes_at_zeros_new bgusegs m1 _ 4096 pageRange ltac:(lia) pageEnd) as zerosB.
      apply (rpres_except_bytes_at _ mB mX _ _ presX zerosB).
      intros a range [ctxLo ctxHi].
      change (Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 4096)))) with 4096 in range.
      unfold RCTX in *. lia.
    + rewrite concC.
      apply (rpres_except_wr_at _ mB mX _ _ presX (wr_at_zeros_new bgusegs m1 _ 4096 pageRange ltac:(lia) pageEnd)).
      intros a range [ctxLo ctxHi]. unfold RCTX in *. lia.
    + apply (rpres_except_rw_cells _ m1 mX _ _ pres1X frameI).
      intros a range [inPage|[ctxLo ctxHi]];
        change (Z.of_nat (cells_size (ram_frame junk s4 s3 s2 s1 s0 ra))) with 64 in range; unfold RCTX in *; lia.
    + apply (rpres_except_stk _ m1 mX _ _ pres1X stkI).
      intros a range [inPage|[ctxLo ctxHi]]; unfold RCTX in *; lia.
    + apply (rpres_except_rw_cells _ m1 mX _ _ pres1X errI).
      intros a range [inPage|[ctxLo ctxHi]]; change (Z.of_nat (cells_size [C4 e1])) with 4 in range;
        rewrite tpVal in range; unfold RCTX in *; lia.
    + apply (rauxv_ok_magree _ m1 mX _ auxI (rmagree_of_pres _ _ _ pres1X)).
      intros a [inPage|[ctxLo ctxHi]]; unfold RAUXV_CELL, RCTX in *; split; lia.
    + apply (magree_trans _ _ _ m m1 mX agreeI (rmagree_of_pres _ _ _ pres1X)).
      * intros a inFP. refine (rFP_mono stI stC a _ inFP).
        intros q rq lookQ. destruct (N.eq_dec q brid) as [->|otherQ].
        -- rewrite regI in lookQ. injection lookQ as <-.
           exists grown. refine (conj (rgr_lookup_new stI brid r boff) (conj eq_refl (conj eq_refl _))).
           change (r_len r <= boff + 4096). lia.
        -- exists rq.
           exact (conj (eq_trans (rgr_lookup_old stI brid r boff q otherQ) lookQ) (conj eq_refl (conj eq_refl (Z.le_refl _)))).
      * intros a [inPage|inCtx].
        -- right. exact (rfresh_of_ranges_free stI _ 4096 a regsI (ami_reserved _ _ amiI) freeOld capOk inPage).
        -- left. right. right. left. exact inCtx.
    + change (conc stI (brid, boff) + 4096 = conc stC (brid, boff + 4096)). rewrite concC, !concAt. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - assert (sameNe : (conc stI (brid, boff) =? conc stI (brid, boff) + 4096) = false) by (apply Z.eqb_neq; lia).
    unfold brk_answer_ok. rewrite sameNe, Z.eqb_refl. cbn [orb negb brk_res brk_mem].
    eapply rimplT_evt.
    { apply ram_bl_fail with (st := stI); [exact repI | exact countI | lia | lia | exact invI]. }
    intros ms2 (m2 & -> & munch2 & mono2 & inv2 & rep2).
    assert (pres2 : rpres_except (fun a => RCTX <= a < RCTX + 928) m1 m2).
    { apply (rpres_except_of_munch_cov _ _ m1 m2 munch2 mono2). cbn [ivs_covered].
      split; [intros x inW; cbv beta; unfold RCTX in *; lia | exact I]. }
    apply (rmmap_path _ m2 s junk e1).
    + apply rAMI_ctx; [exact amiI | unfold ctx_core_eq; repeat split | exact (ami_secretr _ _ amiI) | left; reflexivity | right; left; reflexivity].
    + exact initI.
    + exact regsI.
    + exact countI.
    + exact (amp_shift stI preI).
    + exact (amp_tail stI preI).
    + exact (amp_mkeys stI preI).
    + pose proof ptrsI as (fmhP & amP & mahP & matP & amaP & _).
      apply rptrs_in_upd_ctx; [exact fmhP | exact amP | exact mahP | exact matP | exact amaP | reflexivity | exact I | exact ptrsI].
    + exact rep2.
    + exact inv2.
    + apply (rpres_except_rw_cells _ m1 m2 _ _ pres2 frameI).
      intros a range [ctxLo ctxHi].
      change (Z.of_nat (cells_size (ram_frame junk s4 s3 s2 s1 s0 ra))) with 64 in range. unfold RCTX in *. lia.
    + apply (rpres_except_stk _ m1 m2 _ _ pres2 stkI).
      intros a range [ctxLo ctxHi]. unfold RCTX in *. lia.
    + apply (rpres_except_rw_cells _ m1 m2 _ _ pres2 errI).
      intros a range [ctxLo ctxHi]. change (Z.of_nat (cells_size [C4 e1])) with 4 in range.
      rewrite tpVal in range. unfold RCTX in *. lia.
    + apply (rauxv_ok_magree _ m1 m2 _ auxI (rmagree_of_pres _ _ _ pres2)).
      intros a [ctxLo ctxHi]. unfold RAUXV_CELL, RCTX in *. split; lia.
    + apply (magree_trans _ _ _ m m1 m2 agreeI (rmagree_of_pres _ _ _ pres2)).
      * intros a inFP. exact (rFP_same stI _ a eq_refl inFP).
      * intros a inCtx. left. right. right. left. exact inCtx.
    + exact I.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  RAMpre stI -> AMI st stI -> c_init_done (ctx stI) <> 0 -> s_regions stI = s_regions st ->
  c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
  ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
  rmrep stI m1 -> mem_inv bgusegs m1 ->
  rw_cells bgusegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk bgusegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells bgusegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  ps_m s = ps_m s ->
  rimplT o (SVis (EBrk 0) (fun cur =>
          if negb (brk0_answer_ok cur) then bad_answer bail else
          let base := round_up_pg cur in
          let new := base + 2 * PGSZ in
          SVis (EBrk new) (fun r =>
            if negb (brk_answer_ok cur new r) then bad_answer bail else
            if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
            else if negb (brk_pages_ok stI base (2 * PGSZ)) then bad_answer bail
            else
              SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
                if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
                let '(st1, rid) := new_region RKBrk base (2 * PGSZ) stI in
                let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                              (set_avail_meta_areas (Some (rid, PGSZ))
                                              (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
                am_after_brk st2 false k bail)))) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b17e8) fc None m1 (seg_rom bgusegs)).
Proof using AMP TK LO LOLE ERR TP KH.
  intros stI m1 junk e1 x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros preI amiI initI regsI noAreasI untriedI ptrsI repI invI frameI stkI errI auxI agreeI _.
  pose proof repI as (wfI & (headI & _ & _ & _ & _ & tailI) & _).
  pose proof wfI as (resvI & regWfI & _ & areaWfI & groupWfI).
  pose proof ptrsI as (pFree & pAvail & pHead & pTail & pAreas & _).
  unfold ctx_tail_cells in tailI.
  assert (spHigh : lo + 160 <= bv_unsigned sp) by (unfold RAM_STACK in LOLE; lia).
  assert (spDown : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64)
    by (pose proof (u64_range sp); apply unsigned_lit; lia).
  assert (tpVal : bv_unsigned tp = 3346328) by (rewrite TP; apply unsigned_lit; lia).
  eapply rimplT_evt; [eapply ram_disp_untried; [exact repI | exact noAreasI | exact untriedI]|].
  intros ms0 ->.
  eapply rimplT_brk0; [apply ram_brk0_node|].
  intros cur ms1 (-> & curRange).
  unfold rbrk_regs. cbv beta.
  destruct (brk0_answer_ok cur) eqn:curOk; cbn [negb]; [|apply rimplT_undef].
  unfold brk0_answer_ok, TWO64 in curOk.
  rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq in curOk.
  destruct curOk as [[curPos curAligned] _].
  unfold PGSZ in curAligned.
  rewrite (round_up_pg_aligned cur curAligned).
  change (cur + 2 * PGSZ) with (cur + 8192).
  eapply rimplT_evt; [eapply ram_bu_mid; [lia | exact curAligned | exact tailI | exact invI]|].
  intros ms2 (a2x & mA & -> & munchA & monoA & invA & tailA).
  eapply rimplT_brk; [lia | apply ram_brk_node_at with (cur := cur); [right; reflexivity | lia]|].
  intros ans ms3 (-> & ansFact).
  destruct ans; cbv beta iota in ansFact |- *.
  - rename ansFact into ceilReq.
    assert (pagesNew : brk_new_pages cur (cur + 8192) = Some (cur, 8192)) by (apply brk_new_pages_aligned; lia).
    unfold brk_res, brk_mem, rbrk_regs. rewrite pagesNew. cbv beta iota.
    assert (grownOk : brk_answer_ok cur (cur + 8192) (cur + 8192) = true)
      by (unfold brk_answer_ok; rewrite Z.eqb_refl; reflexivity).
    rewrite grownOk, Z.eqb_refl. cbn [negb].
    destruct (brk_pages_ok stI cur (2 * PGSZ)) eqn:pagesOk; cbn [negb]; [|apply rimplT_undef].
    unfold brk_pages_ok in pagesOk. rewrite !andb_true_iff in pagesOk.
    destruct pagesOk as [_ freeI]. change (2 * PGSZ) with 8192 in freeI.
    pose proof (rimage_range_clear stI cur 8192 resvI freeI ltac:(lia)) as imageClear.
    set (mB := apply_zeros mA [(wa cur, Z_to_bv 64 8192)]).
    pose (E1 := fun a : Z => RCTX + 920 <= a < RCTX + 928 \/ cur <= a < cur + 8192).
    pose proof (magree_of_munch E1 _ m1 mA munchA (conj (fun x range => or_introl range) I)) as agree1A.
    assert (agreeAB : magree E1 mA mB).
    { intros a range away. apply zeros_outside; [lia | lia | lia |].
      unfold wa. rewrite unsigned_lit by lia. unfold E1 in away. lia. }
    pose proof (magree_trans E1 E1 E1 m1 mA mB agree1A agreeAB (fun _ inE => inE) (fun _ inE => inE)) as agree1B.
    assert (stkB : stk bgusegs mB lo (bv_unsigned sp + -64)).
    { apply (rpres_except_stk E1 m1 mB lo _ (rpres_of_magree _ _ _ agree1B) stkI).
      intros a range inE. unfold E1, RCTX in inE. lia. }
    assert (errB : rw_cells bgusegs mB (bv_unsigned tp + -164) [C4 e1]).
    { apply (rrw_cells_magree E1 m1 mB _ _ errI agree1B).
      intros a range inE. simpl in range. unfold E1, RCTX in inE. lia. }
    assert (vmB : rw_cells bgusegs mB RVMLOCK [C4 (Z_to_bv 64 0)]).
    { apply (rrw_cells_magree E1 m1 mB _ _ (rmrep_vmlock stI m1 repI) agree1B).
      intros a range inE. simpl in range. unfold E1, RCTX, RVMLOCK in *. lia. }
    assert (headB : rw_cells bgusegs mB RCTX (rctx_head_cells stI)).
    { apply (rrw_cells_magree E1 m1 mB _ _ headI agree1B).
      intros a range inE. simpl in range. unfold E1, RCTX in *. lia. }
    assert (invB : mem_inv bgusegs mB).
    { apply mem_inv_zeros; [lia | lia | lia | exact invA | | unfold UTOP; lia].
      intros x range. apply ref_ro_addr_false. lia. }
    assert (tailB : rw_cells bgusegs mB (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
    { apply rw_cells_zeros_other; [lia | lia | lia | exact tailA |]. simpl. unfold RCTX. lia. }
    assert (zeroB : rw_cells bgusegs mB (cur + 4096) [CB 4096 (zeros 4096)]).
    { apply (rrw_cells_of_zeros mB cur (Z.to_nat 8192) 4096).
      - exact (bytes_at_zeros_new bgusegs mA cur 8192 ltac:(lia) ltac:(lia) ltac:(lia)).
      - exact (wr_at_zeros_new bgusegs mA cur 8192 ltac:(lia) ltac:(lia) ltac:(lia)).
      - split; [reflexivity | exact I].
      - reflexivity.
      - lia.
      - change (4096 + 4096 <= 8192). lia. }
    eapply rimplT_evt; [eapply ram_bu_ok; [lia | lia | exact tailB]|].
    intros ms4 ->.
    eapply rimplT_mmap_fixed.
    { apply rmmap_fixed_spec with (R := fx_rel cur) (lo := lo) (errv := e1).
      - exact (dec_mmap_fixed_shape cur PGSZ).
      - rewrite spDown. exact stkB.
      - exact errB.
      - exact vmB.
      - lia.
      - exact invB.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - unfold PGSZ. lia.
      - change (mmap_len PGSZ) with 4096. lia.
      - lia.
      - rewrite spDown. lia.
      - rewrite spDown. lia.
      - change (mmap_len PGSZ) with 4096. lia.
      - change (mmap_len PGSZ) with 4096. lia.
      - lia. }
    intros fx ms5 (rr & uu & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & mC & _ & -> & munchC & _ & invC & stkC & errC).
    rewrite spDown in stkC. change (mmap_len PGSZ) with 4096 in munchC.
    rewrite ret_pc_even by first [lia | reflexivity].
    cbv beta.
    destruct (mmap_fixed_answer_ok cur (fixed_val cur fx)); cbn [negb]; [|apply rimplT_undef].
    rewrite (surjective_pairing (new_region RKBrk cur (2 * PGSZ) stI)).
    cbv beta iota zeta.
    change (snd (new_region RKBrk cur (2 * PGSZ) stI)) with (s_next_rid stI).
    destruct (rAMI_new_region st stI RKBrk cur (2 * PGSZ) amiI ltac:(discriminate) ltac:(reflexivity)) as (ami1 & newLookup & oldConc & newConc).
    set (st1 := fst (new_region RKBrk cur (2 * PGSZ) stI)) in *.
    rewrite (am_after_brk_false_eq st1 _ (s_next_rid stI, PGSZ)); [|intros zero1; discriminate zero1 | reflexivity | reflexivity].
    rewrite am_carve_took, carve_st_brk_irrel.
    set (st2 := upd_ctx (fun c : mctx => set_avail_meta_area_count 1 (set_brk (BrkLive (s_next_rid stI) (2 * PGSZ)) c)) st1).
    pose (E2 := fun a : Z => bv_unsigned sp - 160 <= a < bv_unsigned sp - 64
                             \/ bv_unsigned tp + -164 <= a < bv_unsigned tp + -164 + 4 \/ cur <= a < cur + 4096).
    assert (agreeBC : magree E2 mB mC).
    { apply (magree_of_munch E2 _ mB mC munchC). cbn [ivs_covered].
      repeat split; intros x range; unfold E2; lia. }
    assert (headC : rw_cells bgusegs mC RCTX
      [C8 (wz (rsec (c_init_done (ctx stI)) (c_secret (ctx stI)))); C4 (wz (c_init_done (ctx stI))); C4 (wz (c_mmap_counter (ctx stI)));
       C8 (pw stI (c_free_meta_head (ctx stI))); C8 (pw stI (c_avail_meta (ctx stI))); C8 (wz (c_avail_meta_count (ctx stI)));
       C8 (wz (c_avail_meta_area_count (ctx stI))); C8 (wz (c_meta_alloc_shift (ctx stI))); C8 (pw stI (c_meta_area_head (ctx stI)));
       C8 (pw stI (c_meta_area_tail (ctx stI))); C8 (pw stI (c_avail_meta_areas (ctx stI)))]).
    { apply (rrw_cells_magree E2 mB mC _ _ headB agreeBC).
      intros a range inE. simpl in range. unfold E2, RCTX in *. lia. }
    assert (tailC : rw_cells bgusegs mC (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
    { apply (rrw_cells_magree E2 mB mC _ _ tailB agreeBC).
      intros a range inE. simpl in range. unfold E2, RCTX in *. lia. }
    eapply rimplT_evt; [eapply ram_b_store with (nw := cur + 8192); [lia | exact headC | exact tailC | exact invC]|].
    intros ms6 (mD & -> & munchD & _ & invD & headD & tailD).
    pose (E3 := fun a : Z => RCTX + 40 <= a < RCTX + 48 \/ RCTX + 920 <= a < RCTX + 928).
    pose (E23 := fun a : Z => E2 a \/ E3 a).
    pose (D := fun a : Z => E1 a \/ E23 a).
    pose proof (magree_of_munch E3 _ mC mD munchD (conj (fun x range => or_introl range) (conj (fun x range => or_intror range) I))) as agreeCD.
    pose proof (magree_trans E2 E3 E23 mB mC mD agreeBC agreeCD (fun _ inE => or_introl inE) (fun _ inE => or_intror inE)) as agreeBD.
    pose proof (magree_trans E1 E23 D m1 mB mD agree1B agreeBD (fun _ inE => or_introl inE) (fun _ inE => or_intror inE)) as agree1D.
    assert (frameD : rw_cells bgusegs mD (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { apply (rrw_cells_magree D m1 mD _ _ frameI agree1D).
      intros a range inD. simpl in range. unfold D, E1, E23, E2, E3, RCTX in inD. lia. }
    assert (stkD : stk bgusegs mD lo (bv_unsigned sp + -64)).
    { apply (rpres_except_stk E3 mC mD lo _ (rpres_of_magree _ _ _ agreeCD) stkC).
      intros a range inE. unfold E3, RCTX in inE. lia. }
    assert (errD : rw_cells bgusegs mD (bv_unsigned tp + -164) [C4 (sysret_errno rr e1)]).
    { apply (rrw_cells_magree E3 mC mD _ _ errC agreeCD).
      intros a range inE. simpl in range. unfold E3, RCTX in inE. lia. }
    assert (auxD : rauxv_ok mD (bv_unsigned sp)).
    { apply (rauxv_ok_magree D m1 mD _ auxI agree1D).
      intros a inD. unfold D, E1, E23, E2, E3, RCTX, RAUXV_CELL in *. lia. }
    assert (zeroD : rw_cells bgusegs mD (cur + 4096) [CB 4096 (zeros 4096)]).
    { apply (rrw_cells_magree E23 mB mD _ _ zeroB agreeBD).
      intros a range inE. simpl in range. unfold E23, E2, E3, RCTX in inE. lia. }
    pose proof (proj2 (amp_ptrs stI preI) (s_next_rid stI) (N.le_refl _)) as freshNext.
    assert (ridOld : forall q r, s_regions stI !! q = Some r -> q <> s_next_rid stI).
    { intros q r regHit sameRid. rewrite sameRid, (proj1 freshNext) in regHit. discriminate regHit. }
    assert (noAreaNext : forall q ar, s_areas stI !! q = Some ar -> q.1 <> s_next_rid stI).
    { intros q ar areaHit. destruct (areaWfI q ar areaHit) as (r & regHit & _). exact (ridOld _ _ regHit). }
    assert (areaFree : s_areas stI !! (s_next_rid stI, PGSZ) = None).
    { destruct (s_areas stI !! (s_next_rid stI, PGSZ)) as [ar|] eqn:areaHit; [|reflexivity].
      exfalso. exact (noAreaNext _ _ areaHit eq_refl). }
    assert (metaFree : forall q, q.1 = s_next_rid stI -> s_metas stI !! q = None).
    { intros q onNext. destruct (s_metas stI !! q) as [mr|] eqn:metaHit; [|reflexivity].
      destruct (amp_mkeys stI preI q mr metaHit) as (ak & ar & j & akHit & _ & ->).
      exfalso. exact (noAreaNext ak ar akHit onNext). }
    assert (rep1 : rmrep st1 m1).
    { apply (rmrep_new_region stI m1 m1 cur (2 * PGSZ) RKBrk repI
               (ptrs_in_mono (fun rid => (rid < s_next_rid stI)%N) _ stI (fun r below => N.lt_neq _ _ below) ptrsI) (proj2 freshNext));
        [lia | exact curAligned | unfold PGSZ; lia | exact ceilReq | exact freeI | intros; reflexivity | intros kindEq; discriminate kindEq]. }
    assert (regionAway : forall rid r a, s_regions stI !! rid = Some r -> lr_lo r <= a < r_base r + round_up_pg (r_len r) ->
                                         0 <= a < 2 ^ 64 /\ ~ D a).
    { intros rid r a regHit range.
      destruct (regWfI rid r regHit) as (basePos & _ & _ & baseTop & resvFree).
      destruct (rreserved_disjoint _ _ resvFree) as (_ & _ & _ & imageSide).
      pose proof (lr_lo_ge r) as loGe.
      pose proof (clear_range_of_ranges_free stI cur 8192 freeI rid r a regHit range) as notBrk.
      split; [lia|]. unfold D, E1, E23, E2, E3, RCTX. lia. }
    assert (pwSame : forall p, optr_in (fun rid => (rid < s_next_rid stI)%N) p -> pw st2 p = pw stI p).
    { intros p inP.
      exact (rpw_extP stI st2 (fun rid => (rid < s_next_rid stI)%N) (fun q below => oldConc q (N.lt_neq _ _ below)) p inP). }
    assert (headD2 : rw_cells bgusegs mD RCTX (rctx_head_cells st2)).
    { rewrite <- (pwSame _ pFree), <- (pwSame _ pAvail), <- (pwSame _ pHead), <- (pwSame _ pTail), <- (pwSame _ pAreas) in headD.
      exact headD. }
    assert (brkWord : brk_word st2 = cur + 8192) by exact (newConc (2 * PGSZ)).
    assert (tailD2 : rw_cells bgusegs mD (RCTX + 912) (ctx_tail_cells st2)).
    { unfold ctx_tail_cells. rewrite brkWord. exact tailD. }
    assert (midAgree : A2.agree_on m1 mD (RCTX + 80) 832).
    { intros a range. refine (agree1D a _ _); unfold D, E1, E23, E2, E3, RCTX in *; lia. }
    pose proof (rmrep_ctx_mid_agree st1 st2 m1 mD rep1
                  (or_intror (conj (fun _ => eq_refl) (conj (fun _ => eq_refl) (conj (fun _ => eq_refl) (fun _ => eq_refl)))))
                  eq_refl midAgree) as (actD & useD & unmapD & bounceD).
    assert (repD : rmrep st2 mD).
    { apply (rmrep_agree_but_ctx st1 st2 m1 mD rep1); try reflexivity.
      1-5: intros a range; unfold RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK in range;
           refine (agree1D a _ _); [lia | unfold D, E1, E23, E2, E3, RCTX; lia].
      - intros ak ar akHit a range.
        rewrite (oldConc ak (noAreaNext ak ar akHit)) in range.
        destruct (areaWfI ak ar akHit) as (r & regHit & _).
        destruct (regionAway _ _ a regHit (rarea_in_live stI ak ar r a wfI akHit regHit range)) as [bounds away].
        exact (agree1D a bounds away).
      - intros b gh groupHit a range.
        destruct (groupWfI b gh groupHit) as (r & regHit & _).
        rewrite (oldConc b (ridOld _ _ regHit)) in range.
        destruct (regionAway _ _ a regHit (rgroup_in_live stI b gh r a wfI groupHit regHit range)) as [bounds away].
        exact (agree1D a bounds away).
      - intros rid r regHit kindG a range.
        destruct (rnr_lookup_inv stI cur (2 * PGSZ) RKBrk rid r regHit) as [[_ ->] | [_ oldHit]]; [discriminate kindG|].
        destruct (regionAway rid r a oldHit ltac:(rewrite (lr_lo_group r kindG); lia)) as [bounds away].
        exact (agree1D a bounds away).
      - exact (conj headD2 (conj actD (conj useD (conj unmapD (conj bounceD tailD2))))). }
    assert (growI : forall rid r, s_regions stI !! rid = Some r ->
                      exists r', s_regions st2 !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r').
    { intros rid r regHit. exists r.
      exact (conj (eq_trans (rnr_lookup_old stI cur (2 * PGSZ) RKBrk rid (ridOld _ _ regHit)) regHit)
                  (conj eq_refl (conj eq_refl (Z.le_refl _)))). }
    assert (DinFP : forall a, D a -> rFP st2 a).
    { intros a inD. unfold D, E1, E23, E2, E3 in inD.
      destruct inD as [[ctxHit | brkHit] | [[stackHit | [errHit | guardHit]] | [ctxHit | ctxHit]]].
      - left. right. right. left. lia.
      - right. exact (rfresh_of_ranges_free stI cur 8192 a regsI (ami_reserved _ _ amiI) freeI ceilReq brkHit).
      - left. left. lia.
      - left. right. left. rewrite TP in errHit. exact errHit.
      - right. apply (rfresh_of_ranges_free stI cur 8192 a regsI (ami_reserved _ _ amiI) freeI ceilReq). lia.
      - left. right. right. left. lia.
      - left. right. right. left. lia. }
    assert (ami2 : AMI st st2).
    { apply rAMI_ctx.
      - exact ami1.
      - unfold ctx_core_eq. repeat split.
      - exact (ami_secretr _ _ ami1).
      - left. reflexivity.
      - right. right. exists (s_next_rid stI), (2 * PGSZ), {| r_kind := RKBrk; r_base := cur; r_len := 2 * PGSZ |}.
        split; [reflexivity|]. split; [exact newLookup | discriminate]. }
    assert (concP : conc st2 (s_next_rid stI, PGSZ) = cur + 4096) by exact (newConc PGSZ).
    replace (cur + 8192 - 4096) with (conc st2 (s_next_rid stI, PGSZ)) by (rewrite concP; lia).
    apply (rcarve_K st2 (s_next_rid stI, PGSZ) {| r_kind := RKBrk; r_base := cur; r_len := 2 * PGSZ |} mD _ junk (sysret_errno rr e1)).
    + exact ami2.
    + exact initI.
    + exact newLookup.
    + discriminate.
    + change (0 <= 4096). lia.
    + change (4096 + 4096 <= 8192). lia.
    + exact eq_refl.
    + change (cur + 4096 <= cur + 4096). lia.
    + exact areaFree.
    + intros j _. exact (metaFree (aadd (s_next_rid stI, PGSZ) (AREA_HDR + META_SIZE * j)) eq_refl).
    + exact (amp_tail stI preI).
    + change (1 <= 1 < 2 ^ 64). lia.
    + exact repD.
    + exact invD.
    + rewrite concP. exact (rw_cells_bytes_at _ _ _ _ zeroD).
    + rewrite concP. exact (proj2 zeroD).
    + exact frameD.
    + exact stkD.
    + exact errD.
    + exact auxD.
    + exact (magree_trans (rFP stI) D (rFP st2) m m1 mD agreeI agree1D (fun a inP => rFP_mono stI st2 a growI inP) DinFP).
    + exact (eq_sym (newConc (2 * PGSZ))).
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - change (ps_brk (set_brk_ps cur s)) with cur.
    assert (sameOk : brk_answer_ok cur (cur + 8192) cur = true)
      by (unfold brk_answer_ok; rewrite Z.eqb_refl, orb_true_r; reflexivity).
    assert (sameNe : (cur =? cur + 8192) = false) by (apply Z.eqb_neq; lia).
    rewrite sameOk, sameNe. cbn [negb].
    unfold brk_res, brk_mem, rbrk_regs.
    eapply rimplT_evt.
    { eapply ram_bu_fail with (m0 := m1) (st := stI);
        [exact repI | exact munchA | exact monoA | exact noAreasI | lia | lia | exact tailA | reflexivity | reflexivity | exact invA]. }
    intros ms4 (mB & -> & munchB & _ & invB & repB).
    pose (W920 := fun a : Z => RCTX + 920 <= a < RCTX + 928).
    pose proof (magree_trans W920 W920 W920 m1 mA mB
                  (magree_of_munch W920 _ m1 mA munchA (conj (fun x range => range) I))
                  (magree_of_munch W920 _ mA mB munchB (conj (fun x range => range) I))
                  (fun _ inW => inW) (fun _ inW => inW)) as agreeW.
    apply (rmmap_path (upd_ctx (set_brk BrkDead) stI) mB (set_brk_ps cur s) junk e1).
    + apply rAMI_ctx; [exact amiI | unfold ctx_core_eq; repeat split | exact (ami_secretr _ _ amiI) | left; reflexivity | right; left; reflexivity].
    + exact initI.
    + exact regsI.
    + exact noAreasI.
    + exact (amp_shift stI preI).
    + exact (amp_tail stI preI).
    + exact (amp_mkeys stI preI).
    + apply rptrs_in_upd_ctx; [exact pFree | exact pAvail | exact pHead | exact pTail | exact pAreas | reflexivity | exact I | exact ptrsI].
    + exact repB.
    + exact invB.
    + apply (rrw_cells_magree W920 m1 mB _ _ frameI agreeW).
      intros a range inW. simpl in range. unfold W920, RCTX in inW. lia.
    + apply (rpres_except_stk W920 m1 mB lo _ (rpres_of_magree _ _ _ agreeW) stkI).
      intros a range inW. unfold W920, RCTX in inW. lia.
    + apply (rrw_cells_magree W920 m1 mB _ _ errI agreeW).
      intros a range inW. simpl in range. unfold W920, RCTX in inW. lia.
    + apply (rauxv_ok_magree W920 m1 mB _ auxI agreeW).
      intros a inW. unfold W920, RCTX, RAUXV_CELL in *. lia.
    + apply (magree_trans (rFP stI) W920 (rFP (upd_ctx (set_brk BrkDead) stI)) m m1 mB agreeI agreeW (fun _ inP => inP)).
      intros a inW. left. right. right. left. unfold W920 in inW. lia.
    + exact I.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Lemma rbody_spec : forall (stI : mstate) (x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (junk : list byte) (e1 : word),
  RAMpre stI -> AMI st stI -> c_init_done (ctx stI) <> 0 -> s_regions stI = s_regions st -> brk_link_ps stI s ->
  rmrep stI m1 -> mem_inv bgusegs m1 ->
  rw_cells bgusegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk bgusegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells bgusegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  rimplT o (am_body stI k bail) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2b1794) fc None m1 (seg_rom bgusegs)).
Proof using AMP TK LO LOLE ERR TP KH.
  intros stI x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 junk e1.
  intros preI amiI initI regsI linkI repI invI frameI stkI errI auxI agrI.
  pose proof (proj1 repI) as wfI.
  assert (stackRoom : lo <= bv_unsigned sp - 64) by (unfold RAM_STACK in LOLE; lia).
  assert (metaSame : forall g, get_meta_rec stI g = get_meta_rec st g)
    by (intros g; unfold get_meta_rec; rewrite (ami_metas _ _ amiI); reflexivity).
  assert (slotSame : forall g, meta_slot stI g -> meta_slot st g)
    by (intros g; unfold meta_slot; rewrite (ami_areas _ _ amiI); exact (fun inSlot => inSlot)).
  pose proof (ami_ctx _ _ amiI) as (_ & freeSame & availSame & _).
  pose proof (amp_ptrs _ preI) as (ptrsI & _).
  assert (linkKeep : forall X, s_regions X = s_regions stI -> c_brk (ctx X) = c_brk (ctx stI) -> brk_link_ps X s).
  { intros X regsX brkX. revert linkI. unfold brk_link_ps. rewrite brkX.
    destruct (c_brk (ctx stI)) as [| | bid boff]; try tauto.
    intros linkOld. rewrite linkOld. unfold conc, get_region. rewrite regsX. reflexivity. }
  assert (errnoKeep : forall mY, rpres_except (ram_fp stI lo (bv_unsigned sp)) m1 mY -> rw_cells bgusegs mY (bv_unsigned tp + -164) [C4 e1]).
  { intros mY presY. apply (rpres_except_rw_cells _ _ _ _ _ presY errI).
    intros a errnoCell inFP. change (Z.of_nat (cells_size [C4 e1])) with 4 in errnoCell.
    exact (rerrno_not_amfp stI a wfI inFP errnoCell). }
  unfold am_body.
  destruct (c_free_meta_head (ctx stI)) as [h|] eqn:freeI.
  - destruct (amp_fmh _ preI h freeI) as [nextSome memNone].
    pose proof (amp_links _ preI) as linksI.
    pose proof (cl_self _ linksI h nextSome) as slotH.
    pose proof (amp_fml _ preI h memNone nextSome) as (clearH & nextFree & prevFree).
    destruct (m_next (get_meta_rec stI h)) as [nx|] eqn:nextH; [|contradiction].
    destruct (m_prev (get_meta_rec stI h)) as [pv|] eqn:prevH.
    2: { apply (cl_none _ linksI h) in prevH. rewrite nextH in prevH. discriminate. }
    destruct (cl_next _ linksI h nx nextH) as (nxBack & slotNx).
    destruct (cl_prev _ linksI h pv prevH) as (pvBack & slotPv).
    assert (loopIff : nx = h <-> pv = h).
    { split; intros same.
      - rewrite same in nxBack. rewrite nxBack in prevH. injection prevH as <-. reflexivity.
      - rewrite same in pvBack. rewrite pvBack in nextH. injection nextH as <-. reflexivity. }
    eapply rimplT_evt.
    { apply ram_deq with (junk := junk) (lo := lo) (st := stI) (h := h) (nx := nx) (pv := pv)
        (raw := ra) (s0o := s0) (s1o := s1) (s2o := s2) (s3o := s3) (s4o := s4); assumption. }
    intros ms' (w0 & w1 & w2 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & w3 & w4 & w5 & w6 & mD & -> & presD & _ & invD & stkD & repD).
    assert (regsD : s_regions (dequeue LFree h stI) = s_regions stI /\ c_brk (ctx (dequeue LFree h stI)) = c_brk (ctx stI)).
    { unfold dequeue, set_head. cbv zeta. rewrite nextH, prevH.
      destruct (negb (optr_eqb (Some nx) (Some h))); [|split; reflexivity].
      destruct (optr_eqb _ _); split; reflexivity. }
    destruct regsD as [regsD brkD].
    apply (rfinish_K (dequeue LFree h stI) (Some h) s mD e1); try assumption.
    + apply (ram_rel_deq st stI h nx pv amiI); try assumption.
      * rewrite <- freeSame. reflexivity.
      * rewrite <- metaSame. exact nextH.
      * rewrite <- metaSame. exact prevH.
      * exact (slotSame h slotH).
      * rewrite <- metaSame. exact clearH.
      * rewrite <- metaSame. exact (nextFree nx eq_refl).
      * rewrite <- metaSame. intros noNext. apply (cl_none _ linksI nx) in noNext. rewrite nxBack in noNext. discriminate.
      * rewrite <- metaSame. exact (prevFree pv eq_refl).
      * rewrite <- metaSame. rewrite pvBack. discriminate.
    + exact (errnoKeep mD presD).
    + exact (rauxv_ok_magree _ m1 mD _ auxI (rmagree_of_pres _ _ _ presD) (fun a inFP => rFP_below stI a wfI (rFP_am stI a inFP))).
    + exact (magree_trans _ _ _ m m1 mD agrI (rmagree_of_pres _ _ _ presD)
               (fun a inA => rFP_same stI _ a regsD inA) (fun a inFP => rFP_same stI _ a regsD (rFP_am stI a inFP))).
    + exact (linkKeep _ regsD brkD).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold pw, oconc, wz, conc, get_region. rewrite regsD. reflexivity.
  - destruct (Z.eqb_spec (c_avail_meta_count (ctx stI)) 0) as [countZ | countNZ]; cbn [negb].
    2: { destruct (amp_avail _ preI countNZ) as (a & ar & kk & foundA & availQ & kkLo & kkHi & metaNone).
         pose proof (amp_count _ preI) as countRange.
         rewrite (am_take_eq stI k bail _ availQ).
         assert (slotQ : meta_slot stI (aadd a (AREA_HDR + META_SIZE * kk))).
         { exists a, ar, kk. split; [exact foundA|]. split; [unfold NSLOTS in *; lia | reflexivity]. }
         eapply rimplT_evt.
         { apply ram_take_walk with (junk := junk) (lo := lo) (st := stI) (q := aadd a (AREA_HDR + META_SIZE * kk))
             (raw := ra) (s0o := s0) (s1o := s1) (s2o := s2) (s3o := s3) (s4o := s4); try assumption.
           unfold NSLOTS in countRange. lia. }
         intros ms' (w0 & w1 & w2 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & w3 & w4 & w5 & w6 & mT & -> & presT & _ & invT & stkT & repT).
         assert (regsT : s_regions (am_took stI (aadd a (AREA_HDR + META_SIZE * kk)) (c_avail_meta_count (ctx stI) - 1)) = s_regions stI)
           by reflexivity.
         apply (rfinish_K _ _ s mT e1); try assumption.
         - apply ram_rel_take; [exact amiI | | | exact (slotSame _ slotQ)].
           + rewrite <- availSame. exact availQ.
           + rewrite <- (ami_metas _ _ amiI). exact metaNone.
         - exact (errnoKeep mT presT).
         - exact (rauxv_ok_magree _ m1 mT _ auxI (rmagree_of_pres _ _ _ presT) (fun b inFP => rFP_below stI b wfI (rFP_am stI b inFP))).
         - exact (magree_trans _ _ _ m m1 mT agrI (rmagree_of_pres _ _ _ presT)
                    (fun b inA => rFP_same stI _ b regsT inA) (fun b inFP => rFP_same stI _ b regsT (rFP_am stI b inFP))).
         - reflexivity.
         - reflexivity.
         - reflexivity.
         - unfold pw, oconc, wz. rewrite rconc_am_took. reflexivity. }
    eapply rimplT_evt; [apply ram_disp0 with (st := stI); assumption|].
    intros ms0 ->.
    destruct (Z.eqb_spec (c_avail_meta_area_count (ctx stI)) 0) as [areasZ | areasNZ]; cbn [andb].
    2: { unfold am_after_brk. rewrite (proj2 (Z.eqb_neq _ _) areasNZ). cbv beta iota.
         destruct (amp_avail_areas _ preI areasNZ) as (p & r & availP & regP & kindP & alignP & offLo & lrloP & roomP & freshP).
         pose proof (amp_acount _ preI) as areaCount.
         assert (alignedP : pgal p.2) by exact alignP.
         assert (roomOne : p.2 + 4096 <= round_up_pg (r_len r)) by (unfold PGSZ in roomP; lia).
         assert (countWord : 0 <= c_avail_meta_area_count (ctx stI) < 2 ^ 64) by lia.
         eapply rimplT_evt.
         { apply ram_disp_fin with (st := stI) (p := p) (r := r); assumption. }
         intros ms1 ->.
         apply (rfinish_path stI p r m1 s junk e1); try assumption.
         - exact (proj1 (freshP p eq_refl (Z.le_refl _))).
         - intros j slotJ. apply (freshP (aadd p (AREA_HDR + META_SIZE * j))); [reflexivity|].
           cbn [aadd snd]. unfold AREA_HDR, META_SIZE. lia.
         - exact (amp_tail _ preI).
         - lia.
         - reflexivity.
         - reflexivity.
         - reflexivity. }
    destruct (c_brk (ctx stI)) as [| | bid boff] eqn:brkI; cbn [andb negb].
    + apply rbrk_untried_path with (junk := junk) (e1 := e1); try assumption. reflexivity.
    + eapply rimplT_evt; [apply ram_disp_dead with (st := stI); assumption|].
      intros ms1 ->.
      apply (rmmap_path stI m1 s junk e1); try assumption.
      * exact (amp_shift _ preI).
      * exact (amp_tail _ preI).
      * exact (amp_mkeys _ preI).
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + apply rbrk_live_path with (junk := junk) (e1 := e1); assumption.
Qed.

Lemma ralloc_meta_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom bgusegs)).
Proof using AMP MR TK BL AUX ST LO LOLE ERR MI TP KH.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  rewrite alloc_meta_eq.
  pose proof (u64_range sp) as spRange.
  assert (stackRoom : lo <= bv_unsigned sp - 64) by (unfold RAM_STACK in LOLE; lia).
  eapply rimplT_evt.
  { apply ram_entry with (lo := lo) (st := st); try assumption.
    - exact (amp_init _ AMP).
    - exact (amp_s_secret _ AMP).
    - exact (amp_secret _ AMP). }
  intros ms' (x1 & u0 & u1 & u2 & s1x & s4x & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & junk
              & -> & munch1 & mono1 & inv1 & frame1 & stk1 & rep1).
  assert (cover1 : ivs_covered (rFP (am_init_st st)) [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]).
  { cbn [ivs_covered]. refine (conj _ (conj _ I)); intros a range.
    - left. left. unfold RAM_STACK in LOLE. lia.
    - left. right. right. left. lia. }
  apply (rbody_spec (am_init_st st) x1 u0 u1 u2 s1x s4x b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 junk errv).
  - exact (rAMpre_init st AMP).
  - exact (rAMI_init st AMP).
  - exact (ram_init_done st).
  - exact (ram_init_regions st).
  - revert BL. unfold brk_link_ps. rewrite ram_init_brk.
    destruct (c_brk (ctx st)) as [| | bid boff]; try tauto.
    intros linkOld. rewrite linkOld, ram_init_conc. reflexivity.
  - exact rep1.
  - exact inv1.
  - exact frame1.
  - exact stk1.
  - apply (rrw_cells_magree (fun a => ~ outside [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)] a) m m1 _ _ ERR).
    + apply (magree_of_munch _ _ m m1 munch1). cbn [ivs_covered outside].
      repeat split; intros y range away; tauto.
    + intros a range inW. apply inW. cbn [outside].
      change (Z.of_nat (cells_size [C4 errv])) with 4 in range.
      rewrite TP, unsigned_lit in range by lia. unfold RCTX, RAM_STACK in *. lia.
  - apply (rauxv_ok_frame m m1 _ _ AUX munch1 mono1).
    repeat constructor; cbn [fst snd]; unfold RCTX, RAUXV_CELL, RAM_STACK in *; lia.
  - exact (magree_of_munch _ _ m m1 munch1 cover1).
Qed.
End ASM.

Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold ralloc_meta_stmt. intros.
  eapply ralloc_meta_main; eassumption.
Qed.
End WithCeiling0.

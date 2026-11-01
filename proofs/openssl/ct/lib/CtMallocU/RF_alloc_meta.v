(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_A2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres MallocModel_B F_ntf_B MallocKit_B MallocKit_B2 MallocKit_B3. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require KStepLite.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P F_alloc_meta.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A2 RF_ntf_A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RF_am_A RF_am_K RF_am_K2 RF_am_C RF_am_D RF_am_E RF_am_F RF_am_G RF_am_H RF_am_P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (rwview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.

(* [comment removed for export] *)
Lemma rrw_cells_magree C m m' A cs :
  rw_cells ctusegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells ctusegs m' A cs.
Proof.
  intros cellsM agreeM awayC.
  eapply rpres_except_rw_cells; [exact (rpres_of_magree _ _ _ agreeM) | exact cellsM | exact awayC].
Qed.
Lemma rbytes_at_magree C m m' A bs :
  bytes_at ctusegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at ctusegs m' A bs.
Proof.
  intros bytesM agreeM awayC.
  apply (rpres_except_bytes_at C m m' A bs); [apply rpres_of_magree | |]; assumption.
Qed.
Lemma rwr_at_magree C m m' A n :
  wr_at ctusegs m A n -> magree C m m' -> (forall a, A <= a < A + n -> ~ C a) -> 0 <= A -> A + n <= 2^64 -> wr_at ctusegs m' A n.
Proof.
  intros wrM agreeM awayC _ _.
  pose proof (rpres_of_magree C m m' agreeM) as presM.
  exact (rpres_except_wr_at C m m' A n presM wrM awayC).
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

(* [comment removed for export] *)
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk ctusegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells ctusegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv ctusegs m.
Hypothesis TP : tp = Z_to_bv 64 0x333228.
Hypothesis KH : forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     rimplT o (k st1 mo) s' Q ms'.

Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. left. apply ram_fp_alloc_fp. exact H. Qed.

Lemma rETP : errno_addr tp = 0x333228 - 164.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). rewrite TP, unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rfinish_K : forall (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
  am_rel st st1 mo -> rmrep st1 m' -> mem_inv ctusegs m' -> stk ctusegs m' lo (bv_unsigned sp) ->
  rw_cells ctusegs m' (errno_addr tp) [C4 e] -> rauxv_ok m' (bv_unsigned sp) -> magree (rFP st1) m m' ->
  brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rv = pw st1 mo ->
  rimplT o (k st1 mo) sX Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom ctusegs)).
Proof using TK KH.
  intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv.
  intros rel repF invF stkF errF auxF agrF linkF psM psFa psSo rvIs. subst rv.
  apply KH; [|exact linkF].
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', e.
  split; [reflexivity|].
  split; [exact invF|]. split; [exact stkF|]. split; [exact errF|]. split; [exact auxF|].
  split; [exact (rpres_of_magree _ _ _ agrF)|].
  split; [exact repF|].
  split.
  { unfold ticks_ok. rewrite (amr_shadow _ _ _ rel), (amr_tick _ _ _ rel). exact TK. }
  split; [exact psM|]. split; [exact psFa|]. split; [exact psSo|]. exact rel.
Qed.

(* [comment removed for export] *)
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
  intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold RAUXV_CELL, RLIBC, RCTX, RAM_STACK, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *;
    rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
  - destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). pose proof (lr_lo_ge r). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - pose proof (rfresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in C; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
Qed.

Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros WF X. rewrite TP. eapply ram_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

(* [comment removed for export] *)
Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rcarve_K : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
    (x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  AMI st stY -> c_init_done (ctx stY) <> 0 ->
  (s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
  (forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
  rmrep stY mX -> mem_inv ctusegs mX -> bytes_at ctusegs mX (conc stY p) (zeros 4096) -> wr_at ctusegs mX (conc stY p) 4096 ->
  rw_cells ctusegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk ctusegs mX lo (bv_unsigned sp + -64) ->
  rw_cells ctusegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (k (am_took (carve_st stY p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR))) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b3c78) fc None mX (seg_rom ctusegs)).
Proof using AMP TK LO LOLE TP KH.
  intros stY p r mX sX junk e x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros amiY initY regY kindY offLo offHi alignY lrY areaNone metasNone tailOk countY repY invY zeroY wrY frameY stkY errY auxY agrY linkY psM psFa psSo.
  pose proof (ami_secretr _ _ amiY) as secretY.
  assert (roomLo : lo <= bv_unsigned sp - 64) by (pose proof LOLE; unfold RAM_STACK in *; lia).
  eapply rimplT_evt.
  { eapply ram_carve_walk; eassumption. }
  intros msR (t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mR & msIs & presR & monoR & invR & stkR & repR).
  subst msR.
  pose proof (proj1 repY) as wfY.
  assert (regsZ : s_regions (am_took (carve_st stY p) (aadd p AREA_HDR) 100) = s_regions stY).
  { transitivity (s_regions (carve_st stY p)); [reflexivity | apply carve_st_regions]. }
  assert (fpBack : forall a, ram_fp (carve_st stY p) lo (bv_unsigned sp) a -> ram_fp stY lo (bv_unsigned sp) a).
  { intros a. exact (proj1 (ram_fp_same stY (carve_st stY p) lo (bv_unsigned sp) a (carve_st_regions stY p))). }
  eapply rfinish_K.
  - eapply ram_rel_carve; eassumption.
  - exact repR.
  - exact invR.
  - exact stkR.
  - eapply rpres_except_rw_cells; [exact presR | exact errY |].
    intros a inErr fpA. simpl in inErr.
    exact (rerrno_not_amfp stY a wfY (fpBack a fpA) ltac:(lia)).
  - eapply rauxv_ok_magree; [exact auxY | apply rmagree_of_pres; exact presR |].
    intros a fpA. exact (rFP_below stY a wfY (rFP_am stY a (fpBack a fpA))).
  - eapply magree_trans; [exact agrY | apply rmagree_of_pres; exact presR | |].
    + intros a. apply rFP_same. exact regsZ.
    + intros a fpA. apply rFP_am. exact (proj2 (ram_fp_same _ _ _ _ _ regsZ) (fpBack a fpA)).
  - unfold brk_link_ps in *. rewrite rbrk_am_took, rbrk_carve.
    destruct (c_brk (ctx stY)); try exact I.
    rewrite rconc_am_took, rconc_carve. exact linkY.
  - exact psM.
  - exact psFa.
  - exact psSo.
  - unfold pw, oconc. rewrite rconc_am_took, rconc_carve.
    unfold conc, get_region, aadd. cbn [fst snd]. rewrite regY.
    cbv beta iota. unfold wz. f_equal. rewrite <- Z.add_assoc. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rrepfoot_low stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros WF H. rewrite rETP. pose proof WF as (_ & WR & _ & WA & WG). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  destruct H as [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RVMLOCK in *; try lia.
  - destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
  - destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
Qed.

Lemma rfinish_path : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  AMI st stY -> c_init_done (ctx stY) <> 0 -> c_avail_meta_areas (ctx stY) = Some p ->
  (s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
  (forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
  rmrep stY mX -> mem_inv ctusegs mX ->
  rw_cells ctusegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk ctusegs mX lo (bv_unsigned sp + -64) ->
  rw_cells ctusegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (am_finish stY true k bail) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b3d08) fc None mX (seg_rom ctusegs)).
Proof using AMP TK LO LOLE TP KH.
  intros stY p r mX sX junk e x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros amiY initY availY regY kindY offLo offHi alignY lrY areaNone metasNone tailOk countY repY invY frameY stkY errY auxY agrY linkY psM psFa psSo.
  pose proof (proj1 repY) as wfY.
  pose proof repY as (_ & _ & (_ & _ & pageY & _) & _).
  destruct (proj1 (proj2 wfY) p.1 r regY) as (basePos & baseAl & lenPos & baseTop & baseFree).
  destruct (rreserved_disjoint _ _ baseFree) as (img1 & img2 & img3 & img4).
  assert (concY : conc stY p = r_base r + p.2) by (unfold conc, get_region; rewrite regY; reflexivity).
  pose proof (u64_range sp) as spRange.
  assert (spLow : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64).
  { apply unsigned_lit. pose proof LOLE; pose proof LO; unfold RAM_STACK in *; lia. }
  assert (errAt : bv_unsigned tp + -164 = 3355012) by (rewrite rETP; reflexivity).
  assert (loRoom : lo <= bv_unsigned sp - 160) by (pose proof LOLE; unfold RAM_STACK in *; lia).
  pose proof errY as errLit. rewrite errAt in errLit.
  unfold am_finish. rewrite availY. cbv beta iota zeta.
  assert (alignB : (p.2 mod PGSZ =? 0) = true) by (apply Z.eqb_eq; exact alignY).
  rewrite alignB. cbn [negb].
  eapply rimplT_evt; [apply ram_to_mprotect|].
  intros msA ->.
  eapply rimplT_mprotect.
  { eapply (rimpl_enode_dec_weaken _ _ _ mp_strict); [| apply dec_mprotect_rw_weaken].
    eapply rmprotect_spec with (errv := e) (lo := lo); rewrite ?spLow, ?errAt.
    all: try reflexivity.
    all: try assumption.
    all: unfold PGSZ, PROT_RW, RPAGE_SIZE in *; try rewrite concY.
    all: lia. }
  intros ans msB [postB strictB].
  destruct postB as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & mB & msIs & munchB & monoB & invB & stkB & errB & pageB & extraB).
  subst msB. rewrite spLow in munchB, stkB. rewrite errAt in munchB.
  assert (repB : rmrep stY mB).
  { eapply rmrep_transport_unowned; [exact repY | exact munchB | exact monoB |].
    intros lo' hi' a inW inA footA. pose proof (rrepfoot_low stY a wfY footA) as [lowA notErr].
    rewrite errAt in notErr. cbn in inW.
    destruct inW as [hitW|[hitW|[hitW|[]]]]; injection hitW as <- <-.
    - lia.
    - lia.
    - unfold PGSZ in inA.
      exact (rfresh_page_avoids stY mX p r a repY regY kindY offLo offHi alignY lrY areaNone inA footA). }
  assert (frameB : rw_cells ctusegs mB (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
  { eapply rw_cells_transport; [exact frameY | exact munchB | exact monoB |].
    cbn. unfold PGSZ. rewrite concY. lia. }
  assert (auxB : rauxv_ok mB (bv_unsigned sp)).
  { eapply rauxv_ok_frame; [exact auxY | exact munchB | exact monoB |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      cbn [fst snd]; unfold RAUXV_CELL, PGSZ; rewrite ?concY; lia. }
  assert (agrB : magree (rFP stY) m mB).
  { eapply magree_trans; [exact agrY | eapply magree_of_munch; [exact munchB|] | intros a fpA; exact fpA | intros a fpA; exact fpA].
    cbn [ivs_covered]. unfold rFP, ralloc_fp.
    split; [intros a inA; left; left; lia|].
    split; [intros a inA; left; right; left; rewrite unsigned_lit by lia; lia|].
    split; [|exact I].
    intros a inA. left. right. right. right. exists p.1, r.
    unfold PGSZ in inA. rewrite concY in inA. repeat split; [exact regY | exact kindY | lia | lia]. }
  destruct ans as [code|[|]]; cbn [mp_strict] in strictB.
  - cbn [F_mm_syscalls.rg_errno] in errB.
    assert (okB : mprotect_answer_ok (range_val (RgErr code)) = true).
    { cbn [range_val]. unfold mprotect_answer_ok, is_errno_form, neg_errno, TWO64.
      apply orb_true_iff. right. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    assert (notZero : (range_val (RgErr code) =? 0) = false) by (cbn [range_val]; apply Z.eqb_neq; unfold neg_errno; lia).
    assert (notNosys : (range_val (RgErr code) =? TWO64 - ENOSYS) = false) by (cbn [range_val]; apply Z.eqb_neq; unfold neg_errno, TWO64, ENOSYS; lia).
    rewrite okB, notZero, notNosys. cbn [negb orb F_mm_syscalls.munmap_ret].
    rewrite ret_pc_even by lia.
    eapply rimplT_evt.
    { eapply ram_mp_fail with (m0 := mB) (m := mB) (junk := junk) (lo := lo) (e := code) (st := stY);
        [exact repB | exact invB | exact TP | exact errB | exact extraB | exact strictB | apply rpres_except_refl | apply wmono_refl
        | exact frameB | exact stkB | exact LO | lia]. }
    intros msD [postD errD].
    destruct postD as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & mD & msIs & presD & monoD & invD & stkD & repD).
    subst msD. cbn [ms_mem] in errD.
    eapply rfinish_K.
    + exact (ram_rel_none _ _ amiY).
    + exact repD.
    + exact invD.
    + exact stkD.
    + exact errD.
    + eapply rauxv_ok_magree; [exact auxB | apply rmagree_of_pres; exact presD |].
      intros a fpA. exact (rFP_below stY a wfY (rFP_am stY a fpA)).
    + eapply magree_trans; [exact agrB | apply rmagree_of_pres; exact presD | intros a fpA; exact fpA | intros a fpA; exact (rFP_am stY a fpA)].
    + exact linkY.
    + exact psM.
    + exact psFa.
    + exact psSo.
    + reflexivity.
  - cbn [range_val mprotect_answer_ok negb orb Z.eqb F_mm_syscalls.munmap_ret F_mm_syscalls.rg_errno] in *.
    rewrite am_carve_took, ret_pc_even by lia.
    eapply rimplT_evt; [apply ram_mp_ok0|]. intros msC ->.
    destruct extraB as [[_ zeroB] wrB].
    cbn [cells_bytes cbytes cells_size csize] in zeroB, wrB. rewrite app_nil_r in zeroB.
    change (Z.of_nat (Z.to_nat PGSZ + 0)) with 4096 in wrB.
    eapply rcarve_K; eassumption.
  - discriminate strictB.
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
  assert (IMG : forall y, 0x10000 <= y < 0x355000 -> ~ (x <= y < x + L)) by (intros y Hy; apply (rimage_clear_of_ranges_free stY x L y RS RF Hy)).
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
  rmrep stY mX -> mem_inv ctusegs mX ->
  rw_cells ctusegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk ctusegs mX lo (bv_unsigned sp + -64) ->
  rw_cells ctusegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (am_after_brk stY true k bail) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b3c18) fc None mX (seg_rom ctusegs)).
Proof using AMP TK LO LOLE TP KH.
  intros stY mX sX junk e x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros amiY initY regsY countY shiftY tailOk metaSlots ptrsY repY invY frameY stkY errY auxY agrY linkY psM psFa psSo.
  pose proof (proj1 repY) as wfY.
  pose proof (u64_range sp) as spRange.
  assert (loRoom : lo <= bv_unsigned sp - 160) by (pose proof LOLE; unfold RAM_STACK in *; lia).
  assert (spLow : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64).
  { apply unsigned_lit. pose proof LO; lia. }
  assert (errAt : bv_unsigned tp + -164 = 3355012) by (rewrite rETP; reflexivity).
  pose proof errY as errLit. rewrite errAt in errLit.
  set (sh := c_meta_alloc_shift (ctx stY)) in *.
  assert (powPos : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  assert (powTop : 2 ^ sh <= 2 ^ 38) by (apply Z.pow_le_mono_r; lia).
  assert (nIs : 2 ≪ sh = 2 * 2 ^ sh) by (apply Z.shiftl_mul_pow2; lia).
  unfold am_after_brk. rewrite countY. cbn [Z.eqb]. cbv zeta.
  eapply rimplT_evt; [apply ram_to_mmap; [exact repY | lia]|].
  intros msA ->.
  eapply rimplT_mmap_none.
  { eapply rmmap_anon_spec with (isnone := true) (errv := e) (lo := lo); rewrite ?spLow, ?errAt.
    all: try reflexivity.
    all: try assumption.
    all: fold sh; rewrite ?nIs; unfold PGSZ.
    all: try (rewrite TP, unsigned_lit by lia); lia. }
  intros ans msB postB. fold sh.
  set (len := 2 ≪ sh * PGSZ) in *.
  assert (lenIs : len = 2 * 2 ^ sh * 4096) by (unfold len, PGSZ; rewrite nIs; reflexivity).
  assert (lenRound : round_up_pg len = len) by (apply round_up_pg_aligned; rewrite lenIs; apply Z.mod_mul; lia).
  destruct ans as [code|x]; cbn [mmap_val] in *.
  - destruct postB as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & mB & msIs & munchB & monoB & invB & stkB & errB & codeB).
    subst msB. rewrite spLow in munchB, stkB. rewrite errAt in munchB.
    assert (okB : mmap_answer_ok (live_ranges stY) len (neg_errno code) = true).
    { unfold mmap_answer_ok, is_errno_form, neg_errno, TWO64. apply orb_true_iff. left.
      apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    assert (errForm : is_err (neg_errno code) = true) by (unfold is_err, neg_errno, TWO64; apply Z.ltb_lt; lia).
    rewrite okB, errForm. cbn [negb].
    rewrite ret_pc_even by lia.
    assert (repB : rmrep stY mB).
    { eapply rmrep_transport_unowned; [exact repY | exact munchB | exact monoB |].
      intros lo' hi' a inW inA footA. pose proof (rrepfoot_low stY a wfY footA) as [lowA notErr].
      rewrite errAt in notErr. cbn in inW.
      destruct inW as [hitW|[hitW|[]]]; injection hitW as <- <-; lia. }
    assert (frameB : rw_cells ctusegs mB (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact frameY | exact munchB | exact monoB |]. cbn. lia. }
    assert (auxB : rauxv_ok mB (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact auxY | exact munchB | exact monoB |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold RAUXV_CELL; lia. }
    assert (agrB : magree (rFP stY) m mB).
    { eapply magree_trans; [exact agrY | eapply magree_of_munch; [exact munchB|] | intros a fpA; exact fpA | intros a fpA; exact fpA].
      cbn [ivs_covered]. unfold rFP, ralloc_fp.
      split; [intros a inA; left; left; lia|].
      split; [intros a inA; left; right; left; rewrite unsigned_lit by lia; lia | exact I]. }
    eapply rimplT_evt.
    { eapply ram_mm_fail with (m0 := mB) (m := mB) (junk := junk) (lo := lo) (st := stY);
        [exact repB | exact invB | apply rpres_except_refl | apply wmono_refl | exact frameB | exact stkB | exact LO | lia]. }
    intros msD (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & mD & msIs & presD & monoD & invD & stkD & repD).
    subst msD.
    eapply rfinish_K.
    + exact (ram_rel_none _ _ amiY).
    + exact repD.
    + exact invD.
    + exact stkD.
    + eapply rpres_except_rw_cells; [exact presD | exact errB |].
      intros a inErr fpA. simpl in inErr. exact (rerrno_not_amfp stY a wfY fpA ltac:(lia)).
    + eapply rauxv_ok_magree; [exact auxB | apply rmagree_of_pres; exact presD |].
      intros a fpA. exact (rFP_below stY a wfY (rFP_am stY a fpA)).
    + eapply magree_trans; [exact agrB | apply rmagree_of_pres; exact presD | intros a fpA; exact fpA | intros a fpA; exact (rFP_am stY a fpA)].
    + exact linkY.
    + exact psM.
    + exact psFa.
    + exact psSo.
    + reflexivity.
  - destruct postB as (t0b & t1b & t2b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & msIs & munchB & monoB & invB & stkB & errB & addrOk).
    subst msB. rewrite spLow in munchB, stkB.
    unfold mmap_addr_ok, page_size in addrOk. rewrite A2.mmap_len_round_up, lenRound in addrOk.
    apply andb_true_iff in addrOk as [addrOk _]. apply andb_true_iff in addrOk as [addrOk xTop].
    apply andb_true_iff in addrOk as [xAl xPos].
    apply Z.eqb_eq in xAl. apply Z.ltb_lt in xPos. apply Z.leb_le in xTop.
    destruct (mmap_answer_ok (live_ranges stY) len x) eqn:answerOk; cbn [negb]; [|unfold bad_answer; apply rimplT_undef].
    assert (freeX : ranges_free (live_ranges stY) x (round_up_pg len) = true).
    { unfold mmap_answer_ok, is_errno_form, TWO64 in answerOk.
      apply orb_true_iff in answerOk as [errFormX|answerOk].
      - apply andb_true_iff in errFormX as [errFormX _]. apply Z.leb_le in errFormX. lia.
      - apply andb_true_iff in answerOk as [_ freeX]. exact freeX. }
    rewrite lenRound in freeX.
    assert (imageX : forall y, 65536 <= y < 3493888 -> ~ (x <= y < x + len)).
    { intros y yImg. exact (rimage_clear_of_ranges_free stY x len y (proj1 wfY) freeX yImg). }
    pose proof (imageX 3355012 ltac:(lia)) as errOff1. pose proof (imageX 3355015 ltac:(lia)) as errOff2.
    assert (notErr : is_err x = false) by (unfold is_err, TWO64; apply Z.ltb_ge; lia).
    rewrite notErr.
    destruct (new_region RKMeta x len stY) as [st1 rid] eqn:newIs.
    assert (st1Is : st1 = (new_region RKMeta x len stY).1) by (rewrite newIs; reflexivity).
    assert (ridIs : rid = s_next_rid stY) by (unfold new_region in newIs; injection newIs as _ <-; reflexivity).
    rewrite ret_pc_even by lia.
    set (rN := {| r_kind := RKMeta; r_base := x; r_len := len |}).
    pose proof (ami_fresh _ _ amiY (s_next_rid stY) (N.le_refl _)) as [nextNone shadowNone].
    assert (lookNew : s_regions st1 !! rid = Some rN) by (rewrite st1Is, ridIs; apply rnr_lookup_new).
    assert (lookOld : forall q, q <> rid -> s_regions st1 !! q = s_regions stY !! q).
    { intros q qNe. rewrite st1Is. apply rnr_lookup_old. rewrite <- ridIs. exact qNe. }
    assert (oldNe : forall q rq, s_regions stY !! q = Some rq -> q <> rid).
    { intros q rq lookQ ->. rewrite ridIs, nextNone in lookQ. discriminate. }
    assert (unmapRange : 0 <= x < 2 ^ 64 /\ 0 <= mmap_len len < 2 ^ 64 /\ x + mmap_len len <= 2 ^ 64).
    { rewrite A2.mmap_len_round_up, lenRound. lia. }
    destruct unmapRange as (uA & uN & uAN).
    set (mm := F_mm_syscalls.mmap_raw true x len m2).
    assert (mmIs : mm = apply_unmaps m2 [(wa x, Z_to_bv 64 (mmap_len len))]) by reflexivity.
    assert (mmOut : forall a, 0 <= a < 2 ^ 64 -> a < x \/ x + len <= a -> mm (wa a) = m2 (wa a)).
    { intros a aR aOut. rewrite mmIs. apply unmaps_outside; [exact uA | exact uN | exact uAN |].
      unfold wa. rewrite unsigned_lit by exact aR. rewrite A2.mmap_len_round_up, lenRound. exact aOut. }
    assert (rep2 : rmrep stY m2).
    { eapply rmrep_transport_high; [exact repY | exact munchB | exact monoB |].
      intros lo' hi' inW. cbn in inW. destruct inW as [hitW|[]]. injection hitW as <- <-. lia. }
    assert (frame2 : rw_cells ctusegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact frameY | exact munchB | exact monoB |]. cbn. lia. }
    assert (repM : rmrep st1 mm).
    { rewrite st1Is. eapply rmrep_new_region; [exact rep2 | | exact shadowNone | exact xPos | exact xAl | lia | rewrite lenRound; exact xTop | rewrite lenRound; exact freeX | | discriminate].
      - eapply ptrs_in_mono; [|exact ptrsY]. intros q qLt qEq. subst q. exact (N.lt_irrefl _ qLt).
      - intros a aR aOut. rewrite lenRound in aOut. exact (mmOut a aR aOut). }
    assert (frameM : rw_cells ctusegs mm (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { rewrite mmIs. apply rw_cells_unmaps_other; [exact uA | exact uN | exact uAN | exact frame2 |].
      rewrite A2.mmap_len_round_up, lenRound. lia. }
    assert (errM : rw_cells ctusegs mm (bv_unsigned tp + -164) [C4 e]).
    { rewrite mmIs. apply rw_cells_unmaps_other; [exact uA | exact uN | exact uAN | exact errB |].
      rewrite A2.mmap_len_round_up, lenRound, errAt. cbn. lia. }
    assert (auxM : rauxv_ok mm (bv_unsigned sp)).
    { apply (rauxv_ok_magree (fun a => x <= a < x + len)) with (m := m2).
      - eapply rauxv_ok_frame; [exact auxY | exact munchB | exact monoB |].
        apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; unfold RAUXV_CELL; lia.
      - intros a aR aIn. apply mmOut; [exact aR | lia].
      - intros a aIn. split; [lia|]. intros auxIn. apply (imageX a); [unfold RAUXV_CELL in auxIn; lia | exact aIn]. }
    assert (agrM : magree (fun a => rFP stY a \/ (lo <= a < bv_unsigned sp) \/ (x <= a < x + len)) m mm).
    { eapply magree_trans; [exact agrY | | intros a fpA; left; exact fpA | intros a fpA; right; exact fpA].
      eapply magree_trans; [eapply magree_of_munch; [exact munchB|] | | intros a fpA; left; exact fpA | intros a fpA; right; exact fpA].
      - cbn [ivs_covered]. split; [intros a inA; lia | exact I].
      - intros a aR aIn. apply mmOut; [exact aR | lia]. }
    eapply rimplT_evt.
    { eapply ram_mm_ok with (m0 := mm) (m := mm) (st0 := stY) (st := st1) (rid := rid) (r := rN) (junk := junk) (lo := lo) (n := 2 ≪ sh) (x := x);
        [exact repM | rewrite mmIs; apply mem_inv_unmaps; assumption | | exact lookNew | reflexivity | exact xAl | exact xPos | | lia | | apply rpres_except_refl | apply wmono_refl
        | exact frameM | | exact LO | lia].
      - intros a [inA|[inA|(q & rq & lookQ & kindQ & inQ)]]; [left; exact inA | right; left; exact inA |].
        right. right. exists q, rq. rewrite lookOld by exact (oldNe q rq lookQ). auto.
      - lia.
      - rewrite st1Is. change (0 <= sh < 2 ^ 62). lia.
      - exact stkB. }
    intros msC (mF & msIs & presC & monoC & invC & frameC & stkC & repC).
    subst msC.
    set (stZ := mm_ok_st st1 rid (2 ≪ sh)).
    change (upd_ctx _ st1) with stZ.
    assert (concNew : conc stZ (rid, 4096) = x + 4096).
    { change (conc st1 (rid, 4096) = x + 4096). rewrite st1Is, ridIs. apply rnr_conc_new. }
    rewrite <- concNew.
    pose proof (proj1 repM) as wfM.
    clear newIs. subst st1.
    eapply rfinish_path with (r := rN).
    + unfold stZ, mm_ok_st. apply rAMI_ctx.
      * exact (proj1 (rAMI_new_region st stY RKMeta x len amiY ltac:(discriminate) ltac:(lia))).
      * unfold ctx_core_eq. cbn. repeat split.
      * exact (ami_secretr _ _ amiY).
      * right. exists (rid, 4096), rN. split; [reflexivity|]. split; [exact lookNew | discriminate].
      * left. reflexivity.
    + exact initY.
    + reflexivity.
    + exact lookNew.
    + discriminate.
    + cbn. lia.
    + cbn [snd r_len rN]. rewrite lenRound. lia.
    + reflexivity.
    + cbn. lia.
    + change (s_areas stY !! (rid, 4096) = None).
      destruct (s_areas stY !! (rid, 4096)) as [arR|] eqn:areaR; [exfalso|reflexivity].
      destruct (proj1 (proj2 (proj2 (proj2 wfY))) _ _ areaR) as (rR & lookR & _).
      exact (oldNe _ _ lookR eq_refl).
    + intros j jR. change (s_metas stY !! aadd (rid, 4096) (AREA_HDR + META_SIZE * j) = None).
      destruct (s_metas stY !! aadd (rid, 4096) (AREA_HDR + META_SIZE * j)) as [mR|] eqn:metaR; [exfalso|reflexivity].
      destruct (metaSlots _ _ metaR) as (aS & arS & kS & areaS & _ & slotIs).
      destruct (proj1 (proj2 (proj2 (proj2 wfY))) _ _ areaS) as (rS & lookS & _).
      apply (oldNe _ _ lookS). unfold aadd in slotIs. injection slotIs as ridEq _. exact (eq_sym ridEq).
    + exact tailOk.
    + cbn. lia.
    + exact repC.
    + exact invC.
    + exact frameC.
    + exact stkC.
    + eapply rpres_except_rw_cells; [exact presC | exact errM |].
      intros a inErr fpA. simpl in inErr. exact (rerrno_not_amfp _ a wfM fpA ltac:(lia)).
    + eapply rauxv_ok_magree; [exact auxM | apply rmagree_of_pres; exact presC |].
      intros a fpA. exact (rFP_below _ a wfM (rFP_am _ a fpA)).
    + eapply magree_trans; [exact agrM | apply rmagree_of_pres; exact presC | |].
      * intros a [fpA|[inA|inA]].
        -- revert fpA. apply rFP_mono. intros q rq lookQ. exists rq.
           change (s_regions (new_region RKMeta x len stY).1 !! q = Some rq /\ r_kind rq = r_kind rq /\ r_base rq = r_base rq /\ r_len rq <= r_len rq).
           rewrite lookOld by exact (oldNe q rq lookQ). repeat split; [exact lookQ | lia].
        -- left. left. lia.
        -- left. right. right. right. exists rid, rN. split; [exact lookNew|]. split; [discriminate|]. cbn. rewrite lenRound. lia.
      * intros a fpA. apply rFP_am. exact fpA.
    + unfold brk_link_ps in *. change (c_brk (ctx stZ)) with (c_brk (ctx stY)).
      destruct ptrsY as (_ & _ & _ & _ & _ & _ & brkPtr & _).
      destruct (c_brk (ctx stY)) as [| |bq boff]; try exact I.
      change (ps_brk sX = conc (new_region RKMeta x len stY).1 (bq, boff)). rewrite rnr_conc; [exact linkY|]. cbn. intros bqEq. rewrite bqEq in brkPtr. exact (N.lt_irrefl _ brkPtr).
    + exact psM.
    + exact psFa.
    + exact psSo.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rimage_range_clear stY x L : s_reserved stY = ref_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
  x + L <= 0x10000 \/ 0x355000 <= x.
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
  rmrep stI m1 -> mem_inv ctusegs m1 ->
  rw_cells ctusegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk ctusegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells ctusegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
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
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b3b68) fc None m1 (seg_rom ctusegs)).
Proof using AMP TK LO LOLE ERR TP KH.
  intros stI brid boff m1 junk e1 x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros preI amiI initI regsI linkI countI brkI ptrsI repI invI frameI stkI errI auxI agrI.
  pose proof (amp_brk _ preI) as brkRegI. rewrite brkI in brkRegI.
  destruct brkRegI as (rb & regB & kindB & lenB & alignB & pageB & freshB & onlyB).
  unfold PGSZ in alignB, pageB.
  pose proof (proj1 repI) as wfI.
  destruct (proj1 (proj2 wfI) brid rb regB) as (basePos & baseAl & _ & baseTop & _).
  assert (concAt : forall off, conc stI (brid, off) = r_base rb + off) by (intros off; unfold conc, get_region; cbn [fst]; rewrite regB; reflexivity).
  pose proof (concAt boff) as oldIs.
  rewrite lenB, (round_up_pg_aligned boff alignB) in baseTop.
  pose proof linkI as psBrk. unfold brk_link_ps in psBrk. rewrite brkI in psBrk.
  pose proof (u64_range sp) as spRange.
  assert (stackHigh : alloc_ceiling + 160 <= bv_unsigned sp) by (pose proof LOLE; unfold RAM_STACK in *; lia).
  assert (errAt : bv_unsigned tp + -164 = 3355012) by (rewrite rETP; reflexivity).
  cbv zeta.
  eapply rimplT_evt.
  { apply ram_disp_live; [exact repI | exact countI | exact brkI | lia | lia]. }
  intros msD ->.
  eapply rimplT_brk.
  { unfold PGSZ. lia. }
  { apply ram_brk_node_at with (pc := 2833292); [left; reflexivity | unfold PGSZ; lia]. }
  intros ans msB [msIs ansFact]. cbv beta.
  destruct ans; cbn [brk_res brk_mem] in msIs; change (2833292 + 4) with 2833296 in msIs; subst msB.
  2:{ (* the kernel kept the old break: the brk is marked dead and the area comes from mmap *)
    rewrite psBrk.
    assert (stepNe : (conc stI (brid, boff) =? conc stI (brid, boff) + PGSZ) = false) by (apply Z.eqb_neq; unfold PGSZ; lia).
    unfold brk_answer_ok. rewrite stepNe, Z.eqb_refl. cbn [orb negb].
    eapply rimplT_evt.
    { eapply ram_bl_fail; [exact repI | exact countI | lia | lia | exact invI]. }
    intros msE (mE & msIs & munchE & monoE & invE & repE). subst msE.
    assert (deadAmi : AMI st (upd_ctx (set_brk BrkDead) stI)).
    { apply rAMI_ctx; [exact amiI | cbn; repeat split | exact (ami_secretr _ _ amiI) | left; reflexivity | right; left; reflexivity]. }
    pose proof ptrsI as (fmhP & avP & mahP & matP & amaP & _).
    eapply rmmap_path.
    - exact deadAmi.
    - exact initI.
    - exact regsI.
    - exact countI.
    - exact (amp_shift _ preI).
    - exact (amp_tail _ preI).
    - exact (amp_mkeys _ preI).
    - apply rptrs_in_upd_ctx; [exact fmhP | exact avP | exact mahP | exact matP | exact amaP | reflexivity | exact I | exact ptrsI].
    - exact repE.
    - exact invE.
    - eapply rw_cells_transport; [exact frameI | exact munchE | exact monoE |]. cbn. unfold RCTX. lia.
    - eapply stk_transport_disjoint; [exact stkI | exact munchE | exact monoE |]. cbn. unfold RCTX. lia.
    - eapply rw_cells_transport; [exact errI | exact munchE | exact monoE |]. cbn. rewrite errAt. unfold RCTX. lia.
    - eapply rauxv_ok_frame; [exact auxI | exact munchE | exact monoE |].
      apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold RAUXV_CELL, RCTX. lia.
    - eapply (magree_trans (rFP stI) (fun a => RCTX <= a < RCTX + 928)); [exact agrI | | |].
      + eapply magree_of_munch; [exact munchE |]. cbn [ivs_covered]. split; [intros a inA; cbv beta; lia | exact I].
      + intros a fpA. exact (rFP_same stI _ a eq_refl fpA).
      + intros a inCtx. left. right. right. left. exact inCtx.
    - exact I.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  (* the break grew by one page: that page becomes the new meta area *)
  rewrite psBrk.
  assert (oldAl : conc stI (brid, boff) mod 4096 = 0).
  { rewrite oldIs, Z.add_mod, baseAl, alignB by lia. reflexivity. }
  rewrite (brk_new_pages_aligned (conc stI (brid, boff)) 4096) by first [exact oldAl | lia | reflexivity].
  unfold brk_answer_ok. rewrite !Z.eqb_refl. cbn [orb negb].
  destruct (brk_pages_ok stI (conc stI (brid, boff)) PGSZ) eqn:pagesOk; cbn [negb].
  2:{ unfold bad_answer. apply rimplT_undef. }
  apply andb_prop in pagesOk as [_ pagesFree].
  pose proof (rimage_range_clear stI (conc stI (brid, boff)) PGSZ (proj1 wfI) pagesFree ltac:(unfold PGSZ; lia)) as imageClear.
  unfold PGSZ in imageClear.
  assert (notGroup : r_kind rb <> RKGroup) by (rewrite kindB; discriminate).
  rewrite (rgr_eq stI brid rb boff regB).
  destruct (rAMI_grow st stI brid rb boff amiI regB notGroup lenB) as (amiG & concG & lookG).
  set (old := conc stI (brid, boff)) in *.
  set (grown := {| r_kind := r_kind rb; r_base := r_base rb; r_len := boff + 4096 |}) in *.
  set (stG := set_regions (<[brid:=grown]> (s_regions stI)) stI) in *.
  set (mZ := apply_zeros m1 [(wa old, Z_to_bv 64 4096)]) in *.
  assert (oldRange : 0 <= old < 2 ^ 64) by lia.
  assert (sizeRange : 0 <= 4096 < 2 ^ 64) by lia.
  assert (endRange : old + 4096 <= 2 ^ 64) by lia.
  assert (munchZ : munch [(old, old + 4096)] m1 mZ).
  { intros x outX. cbn [outside] in outX. apply zeros_outside; lia. }
  pose proof (wmono_zeros ctusegs m1 old 4096 oldRange sizeRange endRange m1 (wmono_refl _ _)) as monoZ.
  assert (invZ : mem_inv ctusegs mZ).
  { apply mem_inv_zeros; [lia | lia | lia | exact invI | | unfold UTOP; lia].
    intros x inX. apply ref_ro_addr_false. lia. }
  assert (repZ : rmrep stI mZ).
  { apply (rmrep_transport_unowned stI m1 mZ [(old, old + 4096)] repI munchZ monoZ).
    intros lo' hi' a inW inA footA. destruct inW as [hitW | []]. injection hitW as <- <-.
    exact (rrepfoot_clear stI m1 old PGSZ a repI pagesFree (or_introl footA) ltac:(unfold PGSZ; lia)). }
  assert (repG : rmrep stG mZ).
  { apply rmrep_grow_region; [exact repZ | exact regB | exact notGroup | exact lenB | lia | exact alignB | | lia | exact (amp_rpos _ preI) |].
    - rewrite <- oldIs. exact pagesFree.
    - intros q rq regQ otherQ kindQ. exact (otherQ (onlyB q rq regQ kindQ)). }
  pose proof repG as (_ & (headG & _ & _ & _ & _ & tailG) & _).
  eapply rimplT_evt.
  { eapply ram_bl_ok; [lia | exact headG | exact tailG | exact invZ]. }
  intros msF (mF & msIs & munchF & monoF & invF & headF & tailF). subst msF.
  rewrite (am_after_brk_false_eq stG _ (brid, boff)) by first [discriminate | reflexivity | exact alignB].
  rewrite am_carve_took, carve_st_brk_irrel.
  set (stY := upd_ctx (fun c : mctx => set_avail_meta_area_count 1 (set_brk (BrkLive brid (boff + PGSZ)) c)) stG) in *.
  assert (concY : conc stY (brid, boff) = old) by exact (concG (brid, boff)).
  assert (newConc : conc stY (brid, boff + PGSZ) = old + 4096).
  { transitivity (conc stI (brid, boff + PGSZ)); [exact (concG _)|]. rewrite concAt, oldIs. unfold PGSZ. lia. }
  assert (tailY : rw_cells ctusegs mF (RCTX + 912) (ctx_tail_cells stY)).
  { unfold ctx_tail_cells. change (brk_word stY) with (conc stY (brid, boff + PGSZ)). rewrite newConc. exact tailF. }
  assert (repY : rmrep stY mF).
  { apply (rmrep_ctx_frameW stG stY mZ mF [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)] repG munchF monoF); try reflexivity.
    - intros lo' hi' inW. destruct inW as [hitW | [hitW | []]]; injection hitW as <- <-; lia.
    - left. exact headF.
    - right. split; [reflexivity|]. intros lo' hi' inW. destruct inW as [hitW | [hitW | []]]; injection hitW as <- <-; lia.
    - right. split; [reflexivity|]. intros lo' hi' inW. destruct inW as [hitW | [hitW | []]]; injection hitW as <- <-; lia.
    - right. split; [reflexivity|]. intros lo' hi' inW. destruct inW as [hitW | [hitW | []]]; injection hitW as <- <-; lia.
    - right. split; [reflexivity|]. intros lo' hi' inW. destruct inW as [hitW | [hitW | []]]; injection hitW as <- <-; lia.
    - left. exact tailY. }
  assert (lrGrown : lr_lo grown = r_base rb + 4096) by (unfold lr_lo, grown; cbn [r_kind r_base]; rewrite kindB; reflexivity).
  assert (topGrown : r_base grown + round_up_pg (r_len grown) = old + 4096).
  { change (r_base rb + round_up_pg (boff + 4096) = old + 4096).
    rewrite round_up_pg_aligned by (rewrite Z.add_mod, alignB by lia; reflexivity). lia. }
  assert (growMono : forall a, rFP stI a -> rFP stY a).
  { intros a. apply rFP_mono. intros rid r regR.
    destruct (N.eq_dec rid brid) as [-> | otherRid].
    - rewrite regB in regR. injection regR as <-. exists grown.
      split; [exact lookG|]. split; [reflexivity|]. split; [reflexivity|]. change (r_len rb <= boff + 4096). lia.
    - exists r. split; [etransitivity; [exact (rgr_lookup_old stI brid rb boff rid otherRid) | exact regR]|].
      split; [reflexivity|]. split; [reflexivity|]. lia. }
  assert (pageInY : forall a, old <= a < old + 4096 -> rFP stY a).
  { intros a inPage. left. right. right. right. exists brid, grown.
    split; [exact lookG|]. split; [exact notGroup|]. rewrite lrGrown, topGrown. lia. }
  replace (old + 4096 - 4096) with (conc stY (brid, boff)) by (rewrite concY; lia).
  eapply rcarve_K with (r := grown).
  - apply rAMI_ctx; [exact amiG | cbn; repeat split | exact (ami_secretr _ _ amiG) | left; reflexivity |].
    right. right. exists brid, (boff + PGSZ), grown. split; [reflexivity|]. split; [exact lookG | exact notGroup].
  - exact initI.
  - exact lookG.
  - exact notGroup.
  - cbn [snd]. lia.
  - cbn [snd]. change (boff + 4096 <= round_up_pg (boff + 4096)).
    rewrite round_up_pg_aligned by (rewrite Z.add_mod, alignB by lia; reflexivity). lia.
  - exact alignB.
  - rewrite lrGrown. cbn [snd]. change (r_base rb + 4096 <= r_base rb + boff). lia.
  - exact (proj1 (freshB (brid, boff) eq_refl (Z.le_refl boff))).
  - intros j rangeJ. refine (proj2 (freshB (aadd (brid, boff) (AREA_HDR + META_SIZE * j)) eq_refl _)).
    unfold aadd, AREA_HDR, META_SIZE. cbn [snd]. lia.
  - exact (amp_tail _ preI).
  - change (1 <= 1 < 2 ^ 64). lia.
  - exact repY.
  - exact invF.
  - rewrite concY. eapply bytes_at_transport; [exact (bytes_at_zeros_new ctusegs m1 old 4096 oldRange sizeRange endRange) | exact munchF |].
    change (Z.of_nat (length (zeros 4096))) with 4096. cbn [disjoint_from]. unfold RCTX. lia.
  - rewrite concY. apply (wr_at_transport ctusegs mZ mF old 4096); [exact (wr_at_zeros_new ctusegs m1 old 4096 oldRange sizeRange endRange) | exact monoF].
  - eapply rw_cells_transport; [eapply rw_cells_transport; [exact frameI | exact munchZ | exact monoZ |] | exact munchF | exact monoF |].
    + cbn. lia.
    + cbn. unfold RCTX. lia.
  - eapply stk_transport_disjoint; [eapply stk_transport_disjoint; [exact stkI | exact munchZ | exact monoZ |] | exact munchF | exact monoF |].
    + cbn. lia.
    + cbn. unfold RCTX. lia.
  - eapply rw_cells_transport; [eapply rw_cells_transport; [exact errI | exact munchZ | exact monoZ |] | exact munchF | exact monoF |].
    + cbn. rewrite errAt. lia.
    + cbn. rewrite errAt. unfold RCTX. lia.
  - eapply rauxv_ok_frame; [eapply rauxv_ok_frame; [exact auxI | exact munchZ | exact monoZ |] | exact munchF | exact monoF |].
    + apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. unfold RAUXV_CELL. lia.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold RAUXV_CELL, RCTX; lia.
  - eapply (magree_trans (rFP stI) (fun a => (old <= a < old + 4096) \/ (RCTX <= a < RCTX + 928))); [exact agrI | | exact growMono |].
    + eapply (magree_trans (fun a => old <= a < old + 4096) (fun a => RCTX <= a < RCTX + 928)).
      * eapply magree_of_munch; [exact munchZ|]. cbn [ivs_covered]. split; [intros a inA; exact inA | exact I].
      * eapply magree_of_munch; [exact munchF|]. cbn [ivs_covered].
        split; [intros a inA; cbv beta; lia | split; [intros a inA; cbv beta; lia | exact I]].
      * intros a inA. left. exact inA.
      * intros a inA. right. exact inA.
    + intros a [inPage | inCtx]; [exact (pageInY a inPage) | left; right; right; left; exact inCtx].
  - change (old + PGSZ = conc stY (brid, boff + PGSZ)). rewrite newConc. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  RAMpre stI -> AMI st stI -> c_init_done (ctx stI) <> 0 -> s_regions stI = s_regions st ->
  c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
  ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
  rmrep stI m1 -> mem_inv ctusegs m1 ->
  rw_cells ctusegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk ctusegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells ctusegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
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
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b3b68) fc None m1 (seg_rom ctusegs)).
Proof using AMP TK LO LOLE ERR TP KH.
  intros stI m1 junk e1 x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6.
  intros ampI amiI initI regsI countI brkI ptrsI repI invI frameI stkI errI auxI agrI _.
  pose proof repI as (wfI & (headI & _ & _ & _ & _ & tailI) & _).
  unfold ctx_tail_cells, brk_word in tailI. rewrite brkI in tailI.
  pose proof ceil_window_holds as ceilW. unfold ceil_window in ceilW.
  assert (roomLo : lo <= bv_unsigned sp - 160) by (pose proof LOLE as roomL; unfold RAM_STACK in roomL; lia).
  assert (spLow : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64).
  { apply unsigned_lit. pose proof (u64_range sp). lia. }
  assert (errAt : bv_unsigned tp + -164 = 3355012) by (rewrite rETP; reflexivity).
  eapply rimplT_evt; [eapply ram_disp_untried; [exact repI | exact countI | exact brkI] |].
  intros msU ->.
  eapply rimplT_brk0; [eapply ram_brk0_node |].
  intros cur msZ (msIs & curRange). subst msZ. cbv beta.
  destruct (brk0_answer_ok cur) eqn:okCur; cbn [negb]; [| apply rimplT_undef].
  pose proof okCur as curOk. unfold brk0_answer_ok, PGSZ, TWO64 in curOk.
  rewrite !andb_true_iff, Z.ltb_lt, Z.eqb_eq, Z.ltb_lt in curOk.
  destruct curOk as [[curPos curAl] curTop].
  rewrite (round_up_pg_aligned cur curAl). change (2 * PGSZ) with 8192.
  eapply rimplT_evt; [eapply ram_bu_mid; [lia | exact curAl | exact tailI | exact invI] |].
  intros msM (a2m & mA & msIs & munchA & monoA & invA & tailA). subst msM.
  eapply rimplT_brk; [lia | eapply ram_brk_node_at; [right; reflexivity | lia] |].
  intros ans msN [msIs grownCeil]. subst msN.
  change (ps_brk (set_brk_ps cur s)) with cur.
  unfold brk_answer_ok.
  destruct ans; cbn [brk_res].
  2: {
    assert (sameNe : (cur =? cur + 8192) = false) by (apply Z.eqb_neq; lia).
    rewrite sameNe, Z.eqb_refl. cbn [negb orb brk_mem].
    eapply rimplT_evt.
    { eapply ram_bu_fail with (m0 := m1) (st := stI);
        [exact repI | exact munchA | exact monoA | exact countI | exact curPos | exact curTop | exact tailA
        | reflexivity | reflexivity | exact invA]. }
    intros msF (mF & msIs & munchF & monoF & invF & repF). subst msF.
    pose proof (munch_trans _ _ _ _ munchA munchF) as munchAF.
    assert (agreeF : magree (fun a => RCTX + 920 <= a < RCTX + 928) m1 mF).
    { apply (magree_of_munch _ _ _ _ munchAF). split; [intros a inA; exact inA | exact I]. }
    assert (ctxHigh : RCTX + 928 <= lo) by (unfold RCTX; lia).
    eapply rmmap_path.
    - eapply rAMI_ctx; [exact amiI | | exact (ami_secretr _ _ amiI) | left; reflexivity | right; left; reflexivity].
      unfold ctx_core_eq. repeat split.
    - exact initI.
    - exact regsI.
    - exact countI.
    - exact (amp_shift _ ampI).
    - exact (amp_tail _ ampI).
    - exact (amp_mkeys _ ampI).
    - pose proof ptrsI as (fmhP & amP & mahP & matP & amaP & _).
      apply rptrs_in_upd_ctx. all: first [assumption | reflexivity | exact I].
    - exact repF.
    - exact invF.
    - eapply rrw_cells_magree; [exact frameI | exact agreeF |].
      intros a inFrame atW. cbn in inFrame. lia.
    - eapply stk_transport_disjoint; [| exact munchF | exact monoF |].
      + eapply stk_transport_disjoint; [exact stkI | exact munchA | exact monoA |].
        split; [lia | exact I].
      + split; [lia | exact I].
    - eapply rrw_cells_magree; [exact errI | exact agreeF |].
      intros a inErr atW. rewrite errAt in inErr. cbn in inErr. unfold RCTX in atW. lia.
    - eapply rauxv_ok_magree; [exact auxI | exact agreeF |].
      intros a atW. unfold RAUXV_CELL, RCTX in *. lia.
    - eapply magree_trans; [exact agrI | exact agreeF | |].
      + intros a. apply rFP_same. reflexivity.
      + intros a atW. cbv beta in atW. left. right. right. left. lia.
    - exact I.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  }
  cbn in grownCeil.
  rewrite Z.eqb_refl. cbn [negb orb].
  destruct (brk_pages_ok stI cur 8192) eqn:pagesOk; cbn [negb]; [| apply rimplT_undef].
  unfold brk_pages_ok in pagesOk. rewrite !andb_true_iff in pagesOk. destruct pagesOk as [_ freeI].
  pose proof (rimage_range_clear stI cur 8192 (proj1 wfI) freeI ltac:(lia)) as imgCur.
  assert (ru8192 : round_up_pg 8192 = 8192) by (apply round_up_pg_aligned; reflexivity).
  assert (memB : brk_mem mA cur (cur + 8192) BrkGrown = apply_zeros mA [(wa cur, Z_to_bv 64 8192)]).
  { cbn [brk_mem]. rewrite (brk_new_pages_aligned cur 8192) by lia. reflexivity. }
  rewrite memB. set (mB := apply_zeros mA [(wa cur, Z_to_bv 64 8192)]).
  assert (curFits : 0 <= cur < 2 ^ 64) by lia.
  assert (lenFits : 0 <= 8192 < 2 ^ 64) by lia.
  assert (endFits : cur + 8192 <= 2 ^ 64) by lia.
  pose proof (bytes_at_zeros_new ctusegs mA cur 8192 curFits lenFits endFits) as zeroB.
  pose proof (wr_at_zeros_new ctusegs mA cur 8192 curFits lenFits endFits) as wrB.
  assert (stkB : stk ctusegs mB lo (bv_unsigned sp + -64)).
  { apply (stk_zeros ctusegs mA cur 8192 curFits lenFits endFits).
    eapply stk_transport_disjoint; [exact stkI | exact munchA | exact monoA |].
    split; [unfold RCTX; lia | exact I]. }
  assert (errB : rw_cells ctusegs mB (bv_unsigned tp + -164) [C4 e1]).
  { apply (rw_cells_zeros_other ctusegs mA cur 8192 curFits lenFits endFits); [| cbn; rewrite errAt; lia].
    eapply rw_cells_transport; [exact errI | exact munchA | exact monoA |].
    split; [cbn; rewrite errAt; unfold RCTX; lia | exact I]. }
  assert (vmB : rw_cells ctusegs mB RVMLOCK [C4 (Z_to_bv 64 0)]).
  { apply (rw_cells_zeros_other ctusegs mA cur 8192 curFits lenFits endFits); [| cbn; unfold RVMLOCK; lia].
    eapply rw_cells_transport; [exact (rmrep_vmlock _ _ repI) | exact munchA | exact monoA |].
    split; [cbn; unfold RVMLOCK, RCTX; lia | exact I]. }
  assert (invB : mem_inv ctusegs mB).
  { apply (mem_inv_zeros ctusegs mA cur 8192 curFits lenFits endFits invA); [| unfold UTOP; lia].
    intros x inX. apply ref_ro_addr_false. lia. }
  assert (tailB : rw_cells ctusegs mB (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
  { apply (rw_cells_zeros_other ctusegs mA cur 8192 curFits lenFits endFits); [exact tailA | cbn; unfold RCTX; lia]. }
  eapply rimplT_evt; [eapply ram_bu_ok; [exact curPos | lia | exact tailB] |].
  intros msK ->.
  assert (mmapLen : mmap_len PGSZ = 4096) by (rewrite A2.mmap_len_round_up; apply round_up_pg_aligned; reflexivity).
  eapply rimplT_mmap_fixed.
  { eapply (rmmap_fixed_spec (dec_mmap_fixed cur PGSZ) (fx_rel cur)) with (lo := lo) (errv := e1);
      [exact (dec_mmap_fixed_shape cur PGSZ) | ..].
    all: rewrite ?spLow; try assumption; try reflexivity.
    all: rewrite ?errAt, ?mmapLen; unfold PGSZ; lia. }
  intros fa msP postP.
  destruct postP as (rv & _ & t0p & t1p & t2p & a1p & a2p & a3p & a4p & a5p & a6p & a7p & t3p & t4p & t5p & t6p & mC & _ & msIs & munchC & _ & invC & stkC & errC).
  subst msP. rewrite ?spLow, ?errAt, ?mmapLen in munchC. rewrite spLow in stkC.
  rewrite ret_pc_even by lia. cbv beta.
  destruct (mmap_fixed_answer_ok cur (fixed_val cur fa)); cbn [negb]; [| apply rimplT_undef].
  rewrite (surjective_pairing (new_region RKBrk cur 8192 stI)). cbv beta iota.
  change ((new_region RKBrk cur 8192 stI).2) with (s_next_rid stI).
  rewrite (am_after_brk_false_eq _ _ (s_next_rid stI, PGSZ)); [| cbn; lia | reflexivity | reflexivity].
  rewrite am_carve_took, carve_st_brk_irrel.
  set (stY := upd_ctx (fun c => set_avail_meta_area_count 1 (set_brk (BrkLive (s_next_rid stI) 8192) c)) (new_region RKBrk cur 8192 stI).1).
  destruct (rAMI_new_region st stI RKBrk cur 8192 amiI ltac:(discriminate) ltac:(lia)) as (amiN & regNew & concOld & concNew).
  pose proof ptrsI as (_ & _ & _ & _ & _ & _ & _ & _ & areaP & grpP).
  pose proof (proj2 (amp_ptrs _ ampI) (s_next_rid stI) (N.le_refl _)) as [_ shadowNone].
  assert (ptrsNe : ptrs_in (fun r => r <> s_next_rid stI) stI).
  { apply (ptrs_in_mono (fun rid => (rid < s_next_rid stI)%N)); [| exact ptrsI].
    intros r ltR ->. exact (N.lt_irrefl _ ltR). }
  assert (repN : rmrep (new_region RKBrk cur 8192 stI).1 m1).
  { apply (rmrep_new_region stI m1 m1 cur 8192 RKBrk repI ptrsNe shadowNone curPos curAl); rewrite ?ru8192; try lia.
    - exact freeI.
    - intros a _ _. reflexivity.
    - intros kindEq. discriminate kindEq. }
  pose proof repN as (_ & (headN & _) & _).
  pose (inW1C := fun a : Z => RCTX + 920 <= a < RCTX + 928 \/ bv_unsigned sp - 160 <= a < bv_unsigned sp - 64
                              \/ 3355012 <= a < 3355016 \/ cur <= a < cur + 8192).
  pose (inBC := fun a : Z => bv_unsigned sp + -64 - 96 <= a < bv_unsigned sp + -64 \/ 3355012 <= a < 3355012 + 4
                             \/ cur <= a < cur + 4096).
  pose (inCD := fun a : Z => RCTX + 40 <= a < RCTX + 48 \/ RCTX + 920 <= a < RCTX + 928).
  pose (inW := fun a : Z => inCD a \/ inW1C a).
  assert (agreeA : magree inW1C m1 mA).
  { apply (magree_of_munch _ _ _ _ munchA). split; [intros x inX; left; exact inX | exact I]. }
  assert (agreeB : magree inW1C mA mB).
  { intros a aFits notW. unfold mB. apply zeros_outside; [exact curFits | exact lenFits | exact endFits |].
    unfold wa. rewrite unsigned_lit by exact aFits. unfold inW1C in notW. lia. }
  assert (agreeBC : magree inBC mB mC).
  { apply (magree_of_munch _ _ _ _ munchC). cbn [ivs_covered]. unfold inBC.
    repeat split; intros x inX; cbv beta; lia. }
  assert (agree1C : magree inW1C m1 mC).
  { eapply magree_trans; [| exact agreeBC | intros a inWin; exact inWin |].
    - eapply magree_trans; [exact agreeA | exact agreeB | intros a inWin; exact inWin | intros a inWin; exact inWin].
    - intros a inWin. unfold inBC, inW1C in *. lia. }
  assert (headC : rw_cells ctusegs mC RCTX (rctx_head_cells (new_region RKBrk cur 8192 stI).1)).
  { eapply rrw_cells_magree; [exact headN | exact agree1C |].
    intros a inA atW.
    change (Z.of_nat (cells_size (rctx_head_cells (new_region RKBrk cur 8192 stI).1))) with 80 in inA.
    unfold inW1C, RCTX in *. lia. }
  assert (tailC : rw_cells ctusegs mC (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
  { eapply rrw_cells_magree; [exact tailB | exact agreeBC |].
    intros a inA atW.
    change (Z.of_nat (cells_size [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)])) with 16 in inA.
    unfold inBC, RCTX in *. lia. }
  eapply rimplT_evt.
  { eapply ram_b_store with (nw := cur + 8192); [lia | exact headC | exact tailC | exact invC]. }
  intros msS (mD & msIs & munchD & monoD & invD & headD & tailD). subst msS.
  assert (agreeCD : magree inCD mC mD).
  { apply (magree_of_munch _ _ _ _ munchD). cbn [ivs_covered]. unfold inCD.
    repeat split; intros x inX; cbv beta; lia. }
  assert (agreeAll : magree inW m1 mD).
  { eapply magree_trans; [exact agree1C | exact agreeCD | intros a inWin; right; exact inWin | intros a inWin; left; exact inWin]. }
  assert (liveAway : forall rid r x, s_regions stI !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) ->
                     mD (wa x) = m1 (wa x)).
  { intros rid r x regR inX.
    destruct (proj1 (proj2 wfI) rid r regR) as (basePos & _ & _ & baseTop & baseFree).
    destruct (rreserved_disjoint _ _ baseFree) as (_ & _ & _ & imgSide).
    pose proof (clear_range_of_ranges_free stI cur 8192 freeI rid r x regR inX) as notCur.
    assert (baseLo : r_base r <= lr_lo r) by (unfold lr_lo; destruct (r_kind r); lia).
    apply agreeAll; [lia |]. unfold inW, inCD, inW1C, RCTX. lia. }
  assert (concY : forall off, conc stY (s_next_rid stI, off) = cur + off) by (intros off; exact (concNew off)).
  assert (repY : rmrep stY mD).
  { apply (rmrep_agree_but_ctx (new_region RKBrk cur 8192 stI).1 stY m1 mD repN); try reflexivity.
    1-6: intros a inA; apply agreeAll;
      [unfold RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK, RCTX in inA; lia
      | unfold inW, inCD, inW1C, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD, RVMLOCK, RCTX in *; lia].
    - intros ak ar areaK x inX.
      destruct (areaP _ _ areaK) as [ltK _].
      rewrite concOld in inX by (intros sameK; rewrite sameK in ltK; exact (N.lt_irrefl _ ltK)).
      destruct (rarea_conc stI ak ar wfI areaK) as (r & regK & _).
      exact (liveAway _ _ _ regK (rarea_in_live stI ak ar r x wfI areaK regK inX)).
    - intros b gh grpK x inX.
      destruct (grpP _ _ grpK) as [ltB _].
      rewrite concOld in inX by (intros sameB; rewrite sameB in ltB; exact (N.lt_irrefl _ ltB)).
      destruct (rgroup_conc stI b gh wfI grpK) as (r & regB & _).
      exact (liveAway _ _ _ regB (rgroup_in_live stI b gh r x wfI grpK regB inX)).
    - intros rid r regR kindR x inX.
      destruct (rnr_lookup_inv stI cur 8192 RKBrk rid r regR) as [[_ ->] | [_ regOld]].
      + cbn in kindR. discriminate kindR.
      + apply (liveAway rid r x regOld). rewrite (lr_lo_group r kindR). exact inX.
    - assert (agreeArr : MallocKit_B.agree_on m1 mD (RCTX + 80) 832).
      { intros a inA. apply agreeAll; [unfold RCTX in inA; lia | unfold inW, inCD, inW1C, RCTX in *; lia]. }
      destruct (rmrep_ctx_mid_agree (new_region RKBrk cur 8192 stI).1 stY m1 mD repN
        (or_intror (conj (fun _ => eq_refl) (conj (fun _ => eq_refl) (conj (fun _ => eq_refl) (fun _ => eq_refl)))))
        eq_refl agreeArr) as (actD & useD & unmD & bncD).
      split; [exact headD |]. split; [exact actD |]. split; [exact useD |]. split; [exact unmD |]. split; [exact bncD |].
      change (rw_cells ctusegs mD (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (wz (conc stY (s_next_rid stI, 8192)))]).
      rewrite concY. exact tailD. }
  assert (amiY : AMI st stY).
  { apply rAMI_ctx; [exact amiN | unfold ctx_core_eq; repeat split | exact (ami_secretr _ _ amiN) | left; reflexivity |].
    right. right. exists (s_next_rid stI), 8192, {| r_kind := RKBrk; r_base := cur; r_len := 8192 |}.
    split; [reflexivity | split; [exact regNew | cbn; discriminate]]. }
  replace (cur + 8192 - 4096) with (conc stY (s_next_rid stI, PGSZ)) by (rewrite concY; unfold PGSZ; lia).
  eapply rcarve_K.
  - exact amiY.
  - exact initI.
  - exact regNew.
  - cbn. discriminate.
  - unfold PGSZ. cbn. lia.
  - cbn [snd r_len]. rewrite ru8192. unfold PGSZ. lia.
  - reflexivity.
  - unfold lr_lo, PGSZ. cbn. lia.
  - change (s_areas stI !! (s_next_rid stI, PGSZ) = None).
    destruct (s_areas stI !! (s_next_rid stI, PGSZ)) as [ar|] eqn:areaHit; [exfalso | reflexivity].
    destruct (areaP _ _ areaHit) as [ltSelf _]. exact (N.lt_irrefl _ ltSelf).
  - intros j jRange. change (s_metas stI !! aadd (s_next_rid stI, PGSZ) (AREA_HDR + META_SIZE * j) = None).
    destruct (s_metas stI !! aadd (s_next_rid stI, PGSZ) (AREA_HDR + META_SIZE * j)) as [mr|] eqn:metaHit;
      [exfalso | reflexivity].
    destruct (amp_mkeys _ ampI _ _ metaHit) as (ak & ar & kk & areaK & _ & keyEq).
    apply (f_equal fst) in keyEq. cbn in keyEq.
    destruct (areaP _ _ areaK) as [ltK _]. rewrite <- keyEq in ltK. exact (N.lt_irrefl _ ltK).
  - exact (amp_tail _ ampI).
  - change (1 <= 1 < 2 ^ 64). lia.
  - exact repY.
  - exact invD.
  - rewrite concY. unfold PGSZ.
    eapply rbytes_at_magree; [| exact agreeCD |].
    + eapply rbytes_at_magree; [| exact agreeBC |].
      * exact (rbytes_at_zeros_sub mB cur (Z.to_nat 8192) 4096 4096 zeroB ltac:(lia) ltac:(cbn; lia)).
      * intros a inA. unfold zeros in inA. rewrite repeat_length in inA. change (Z.of_nat 4096) with 4096 in inA.
        unfold inBC. lia.
    + intros a inA. unfold zeros in inA. rewrite repeat_length in inA. change (Z.of_nat 4096) with 4096 in inA.
      unfold inCD, RCTX. lia.
  - rewrite concY. unfold PGSZ.
    eapply rwr_at_magree; [| exact agreeCD | | lia | lia].
    + eapply rwr_at_magree; [| exact agreeBC | | lia | lia].
      * exact (wr_at_sub ctusegs mB cur 8192 (cur + 4096) 4096 wrB ltac:(lia) ltac:(lia)).
      * intros a inA. unfold inBC. lia.
    + intros a inA. unfold inCD, RCTX. lia.
  - eapply rrw_cells_magree; [exact frameI | exact agreeAll |].
    intros a inFrame atW. cbn in inFrame. unfold inW, inCD, inW1C, RCTX in atW. lia.
  - eapply stk_transport_disjoint; [exact stkC | exact munchD | exact monoD |].
    repeat split; unfold RCTX; lia.
  - eapply rw_cells_transport; [exact errC | exact munchD | exact monoD |].
    repeat split; rewrite errAt; cbn; unfold RCTX; lia.
  - eapply rauxv_ok_magree; [exact auxI | exact agreeAll |].
    intros a atW. unfold inW, inCD, inW1C, RAUXV_CELL, RCTX in *. lia.
  - eapply magree_trans; [exact agrI | exact agreeAll | |].
    + intros a. apply rFP_mono. intros rid r regR. rewrite regsI in regR.
      destruct (ami_regions _ _ amiY rid r regR) as (r' & regR' & kindE & baseE & lenLe & _).
      exists r'. repeat split; assumption.
    + intros a atW. unfold inW, inCD, inW1C in atW.
      destruct atW as [ctxA | [ctxA | [stkA | [errA | curA]]]].
      * left. right. right. left. unfold RCTX in *. lia.
      * left. right. right. left. unfold RCTX in *. lia.
      * left. left. lia.
      * left. right. left. rewrite unsigned_lit by lia. lia.
      * right. exact (rfresh_of_ranges_free stI cur 8192 a regsI (ami_reserved _ _ amiI) freeI grownCeil curA).
  - change (cur + 8192 = conc stY (s_next_rid stI, 8192)). rewrite concY. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rbody_spec : forall (stI : mstate) (x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (junk : list byte) (e1 : word),
  RAMpre stI -> AMI st stI -> c_init_done (ctx stI) <> 0 -> s_regions stI = s_regions st -> brk_link_ps stI s ->
  rmrep stI m1 -> mem_inv ctusegs m1 ->
  rw_cells ctusegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk ctusegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells ctusegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  rimplT o (am_body stI k bail) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2b3b14) fc None m1 (seg_rom ctusegs)).
Proof using AMP TK LO LOLE ERR TP KH.
  intros stI x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 junk e1.
  intros preI amiI initI regsI linkI repI invI frameI stkI errI auxI agrI.
  pose proof (proj1 repI) as wfI.
  assert (loRoom : lo <= bv_unsigned sp - 160) by (pose proof LOLE; unfold RAM_STACK in *; lia).
  pose proof (ami_ctx _ _ amiI) as (_ & fmhEq & availEq & _).
  pose proof (ami_metas _ _ amiI) as metasEq.
  pose proof (ami_areas _ _ amiI) as areasEq.
  assert (slotBack : forall q, meta_slot stI q -> meta_slot st q) by (intros q; unfold meta_slot; rewrite areasEq; exact id).
  assert (recBack : forall q, get_meta_rec stI q = get_meta_rec st q) by (intros q; apply rget_meta_rec_extP; exact metasEq).
  (* the post-call bookkeeping shared by the dequeue and take paths *)
  assert (finishWith : forall stF (q : aptr) mR t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r t3r t4r t5r t6r,
             am_rel st stF (Some q) -> s_regions stF = s_regions stI -> c_brk (ctx stF) = c_brk (ctx stI) ->
             conc stF q = conc stI q ->
             rpres_except (ram_fp stI lo (bv_unsigned sp)) m1 mR -> mem_inv ctusegs mR -> stk ctusegs mR lo (bv_unsigned sp) -> rmrep stF mR ->
             rimplT o (k stF (Some q)) s Q
               (MS (mkR ra sp gp tp t0r t1r t2r s0 s1 (Z_to_bv 64 (conc stI q)) a1r a2r a3r a4r a5r a6r a7r s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r) F (ret_pc ra) fc None mR (seg_rom ctusegs))).
  { intros stF q mR t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r t3r t4r t5r t6r relF regsF brkF concF presR invR stkR repR.
    eapply rfinish_K.
    - exact relF.
    - exact repR.
    - exact invR.
    - exact stkR.
    - eapply rpres_except_rw_cells; [exact presR | exact errI |].
      intros a inErr fpA. simpl in inErr. exact (rerrno_not_amfp stI a wfI fpA ltac:(lia)).
    - eapply rauxv_ok_magree; [exact auxI | apply rmagree_of_pres; exact presR |].
      intros a fpA. exact (rFP_below stI a wfI (rFP_am stI a fpA)).
    - eapply magree_trans; [exact agrI | apply rmagree_of_pres; exact presR | |].
      + intros a. apply rFP_same. exact regsF.
      + intros a fpA. apply rFP_am. exact (proj2 (ram_fp_same _ _ _ _ _ regsF) fpA).
    - unfold brk_link_ps in *. rewrite brkF. destruct (c_brk (ctx stI)) as [| |bq boff]; try exact I.
      rewrite linkI. unfold conc, get_region. rewrite regsF. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold pw, oconc. rewrite concF. reflexivity. }
  unfold am_body.
  destruct (c_free_meta_head (ctx stI)) as [h|] eqn:fmhI.
  - destruct (amp_fmh _ preI h fmhI) as [nextSome memNone].
    pose proof (amp_links _ preI) as linksI.
    destruct (m_next (get_meta_rec stI h)) as [nx|] eqn:nextH; [clear nextSome|contradiction].
    destruct (m_prev (get_meta_rec stI h)) as [pv|] eqn:prevH.
    2:{ exfalso. apply (proj2 (cl_none _ linksI h)) in prevH. rewrite nextH in prevH. discriminate. }
    destruct (cl_next _ linksI h nx nextH) as [nxPrev nxSlot].
    destruct (cl_prev _ linksI h pv prevH) as [pvNext pvSlot].
    assert (hSlot : meta_slot stI h) by (apply (cl_self _ linksI h); rewrite nextH; discriminate).
    assert (selfIff : nx = h <-> pv = h).
    { split; intros ->; congruence. }
    destruct (amp_fml _ preI h memNone ltac:(rewrite nextH; discriminate)) as (clrH & nxMem & pvMem).
    eapply rimplT_evt.
    { eapply ram_deq; try eassumption. lia. }
    intros msR (t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mR & msIs & presR & monoR & invR & stkR & repR).
    subst msR.
    assert (regsD : s_regions (dequeue LFree h stI) = s_regions stI).
    { unfold dequeue. cbv zeta. repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; reflexivity. }
    assert (brkD : c_brk (ctx (dequeue LFree h stI)) = c_brk (ctx stI)).
    { unfold dequeue. cbv zeta. repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; reflexivity. }
    apply finishWith; try assumption.
    + eapply ram_rel_deq; rewrite <- ?recBack; try eassumption.
      * exact (eq_sym fmhEq).
      * apply slotBack. exact hSlot.
      * exact (nxMem nx nextH).
      * intros nxNone. apply (cl_none _ linksI nx) in nxNone. rewrite nxPrev in nxNone. discriminate.
      * exact (pvMem pv prevH).
      * rewrite pvNext. discriminate.
    + unfold conc, get_region. rewrite regsD. reflexivity.
  - destruct (c_avail_meta_count (ctx stI) =? 0) eqn:cntZ; cbn [negb].
    + apply Z.eqb_eq in cntZ.
      eapply rimplT_evt; [eapply ram_disp0; [exact repI | exact fmhI | exact cntZ] |]. intros ms0 ->.
      pose proof (proj1 (amp_ptrs _ preI)) as ptrsI.
      destruct (c_avail_meta_area_count (ctx stI) =? 0) eqn:areasZ.
      * apply Z.eqb_eq in areasZ.
        destruct (c_brk (ctx stI)) as [| |bid boff] eqn:brkI; cbn [andb negb].
        -- eapply rbrk_untried_path; try eassumption. reflexivity.
        -- eapply rimplT_evt; [eapply ram_disp_dead; [exact repI | exact areasZ | exact brkI] |]. intros ms1 ->.
           eapply rmmap_path; try eassumption.
           all: first [exact (amp_shift _ preI) | exact (amp_tail _ preI) | exact (amp_mkeys _ preI) | reflexivity].
        -- eapply rbrk_live_path; eassumption.
      * cbn [andb]. unfold am_after_brk. rewrite areasZ.
        apply Z.eqb_neq in areasZ.
        destruct (amp_avail_areas _ preI areasZ) as (p & r & availP & regP & kindP & alP & offP & lrP & topP & freshP).
        pose proof (amp_acount _ preI) as acountR.
        assert (pageFits : p.2 + 4096 <= round_up_pg (r_len r)) by (unfold PGSZ in topP; lia).
        eapply rimplT_evt; [eapply ram_disp_fin; try eassumption; lia |]. intros ms1 ->.
        eapply rfinish_path with (r := r); try eassumption.
        all: try first [exact (amp_tail _ preI) | reflexivity | lia].
        -- destruct (freshP p eq_refl (Z.le_refl _)) as [areaNone _]. exact areaNone.
        -- intros j jR. destruct (freshP (aadd p (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia)) as [_ metaNone]. exact metaNone.
    + apply Z.eqb_neq in cntZ.
      destruct (amp_avail _ preI cntZ) as (aA & arA & jA & areaA & availI & jLo & jHi & metaA).
      rewrite (am_take_eq stI k bail _ availI).
      pose proof (amp_count _ preI) as cntR.
      assert (qSlot : meta_slot stI (aadd aA (AREA_HDR + META_SIZE * jA))).
      { exists aA, arA, jA. split; [exact areaA|]. split; [|reflexivity]. lia. }
      eapply rimplT_evt.
      { eapply ram_take_walk; try eassumption; unfold NSLOTS in *; lia. }
      intros msR (t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mR & msIs & presR & monoR & invR & stkR & repR).
      subst msR.
      apply finishWith; try assumption.
      * eapply ram_rel_take; [exact amiI | rewrite <- availEq; exact availI | rewrite <- metasEq; exact metaA | apply slotBack; exact qSlot].
      * reflexivity.
      * apply rbrk_am_took.
      * apply rconc_am_took.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ralloc_meta_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom ctusegs)).
Proof using AMP MR TK BL AUX ST LO LOLE ERR MI TP KH.
  intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  pose proof LOLE as roomSp. unfold RAM_STACK in roomSp.
  assert (errAt : bv_unsigned tp + -164 = 3355012) by (rewrite rETP; reflexivity).
  rewrite alloc_meta_eq.
  eapply rimplT_evt.
  { eapply ram_entry; try eassumption.
    - lia.
    - exact (amp_init _ AMP).
    - exact (amp_s_secret _ AMP).
    - exact (amp_secret _ AMP). }
  intros msE (x1 & t0e & t1e & t2e & s1x & s4x & a0e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & mE & junk & msIs & munchE & monoE & invE & frameE & stkE & repE).
  subst msE.
  eapply rbody_spec with (e1 := errv).
  - exact (rAMpre_init _ AMP).
  - exact (rAMI_init _ AMP).
  - apply ram_init_done.
  - apply ram_init_regions.
  - unfold brk_link_ps in *. rewrite ram_init_brk.
    destruct (c_brk (ctx st)); try exact I. rewrite ram_init_conc. exact BL.
  - exact repE.
  - exact invE.
  - exact frameE.
  - exact stkE.
  - eapply rw_cells_transport; [exact ERR | exact munchE | exact monoE |].
    rewrite errAt. cbn. unfold RCTX. lia.
  - eapply rauxv_ok_frame; [exact AUX | exact munchE | exact monoE |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold RAUXV_CELL, RCTX; lia.
  - eapply magree_of_munch; [exact munchE|].
    cbn [ivs_covered]. unfold rFP, ralloc_fp.
    split; [intros a inA; left; left; lia|].
    split; [intros a inA; left; right; right; left; lia | exact I].
Qed.
End ASM.

Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold ralloc_meta_stmt. intros.
  eapply ralloc_meta_main; eassumption.
Qed.
End WithCeiling0.

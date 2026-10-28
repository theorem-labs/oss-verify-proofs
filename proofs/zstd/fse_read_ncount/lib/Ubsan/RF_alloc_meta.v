(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocKit_A2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_memcpy.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres MallocModel_B F_ntf_B MallocKit_B MallocKit_B2 MallocKit_B3.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require KStep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P F_alloc_meta.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A2 RF_ntf_A.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RF_am_A RF_am_K RF_am_K2 RF_am_C RF_am_D RF_am_E RF_am_F RF_am_G RF_am_H RF_am_P.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof. intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
#[using="Type"] Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof. intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (rwview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.
#[using="Type"] Lemma rrw_cells_magree C m m' A cs :
rw_cells usegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells usegs m' A cs.
Proof.
intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply RA2.rrw_cells_agree; [exact H|]. intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56765667309.12000007S2H02Ha".
apply AG; [lia| apply HC; exact Ha].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rbytes_at_magree C m m' A bs :
bytes_at usegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at usegs m' A bs.
Proof.
intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply RA2.rbytes_at_agree; [exact H|]. intros a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56765667309.12000007S2H02Ha".
apply AG; [lia| apply HC; exact Ha].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rauxv_ok_magree C m m' B :
rauxv_ok m B -> magree C m m' -> (forall a, C a -> a < B /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8)) -> rauxv_ok m' B.
Proof.
intros (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AC & AL & RN & H) AG HC.
exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
- eapply rrw_cells_magree; [exact AC| exact AG|]. cbn. intros a Ha X. destruct (HC a X) as [_ Y]. apply Y. exact Ha.
- eapply rbytes_at_magree; [exact AL| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _].
unfold rauxv_list in Ha. rewrite u64s_length, map_length in Ha. cbn in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59323410545.26000008S1H2Ha1Y".
lia.
- eapply rbytes_at_magree; [exact RN| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _]. rewrite length_le8 in Ha. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis LO : ATOP <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 0x2ef30.
Hypothesis KH : forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
rimplT o (k st1 mo) s' Q ms'.
Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.
#[using="Type"] Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof. intros H. left. apply ram_fp_alloc_fp. exact H. Qed.
#[using="rc TP"] Lemma rETP : errno_addr tp = 0x2ef30 - 164.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010=8841017104.42000001S".
rewrite TP, unsigned_lit by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="TK KH"] Lemma rfinish_K : forall (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
am_rel st st1 mo -> rmrep st1 m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
rw_cells usegs m' (errno_addr tp) [C4 e] -> rauxv_ok m' (bv_unsigned sp) -> magree (rFP st1) m m' ->
brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rv = pw st1 mo ->
rimplT o (k st1 mo) sX Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)).
Proof.
intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv REL MR1 MI1 ST1 ERR1 AUX1 AG BL1 P1 P2 P3 ->.
apply KH; [| exact BL1]. unfold ram_post. do 16 eexists. split; [reflexivity|].
split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact AUX1|]. split.
{ apply rpres_of_magree. exact AG. }
split; [exact MR1|]. split.
{ destruct TK as [T1 T2]. split; intros; rewrite (amr_shadow _ _ _ REL) in *; rewrite (amr_tick _ _ _ REL); eauto. }
auto.
Qed.
#[using="Type"] Lemma rFP_mono stX stY a :
(forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rFP stX a -> rFP stY a.
Proof.
intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
{ unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). Local Ltac2 Set LiaHints.tbl := fun () => "0030>17199868364.5630139505620.5750812193970.7000000100700FSS1X2RUS2L'1H2H02H42H5".
rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
unfold lr_lo in *. rewrite K', B'. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rFP_same stX stY a : s_regions stY = s_regions stX -> rFP stX a -> rFP stY a.
Proof. intros E. apply rFP_mono. intros rid r Hr. exists r. rewrite E. Local Ltac2 Set LiaHints.tbl := fun () => "0010=2599663278.49000001S".
repeat split; auto; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="AMP LO LOLE"] Lemma rFP_below stX a : rregions_wf stX -> rFP stX a -> a < bv_unsigned sp /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8).
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>52216868299.4652216868299.4752216868299.568841017104.46 00000A00T00n00oS2LO1X5ATOPR4LOLES2LO4LOLE1C1H5ATOPRS2LO4LOLE1X3RBC2D21H5ATOPRS".
intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold RAUXV_CELL, RLIBC, RCTX, RAM_STACK in *;
rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
- destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). pose proof (lr_lo_ge r). atop_facts. lia.
- pose proof (rfresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. atop_facts. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="LO TP"] Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. intros WF X. rewrite TP. eapply ram_fp_not_errno; [exact X| exact WF| exact LO]. Qed.
#[using="Type"] Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.
#[using="Type"] Lemma ram_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
= kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rconc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbrk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof.
unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
#[using="Type"] Lemma rconc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.
#[using="AMP TK LO LOLE TP KH"] Lemma rcarve_K : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> c_init_done (ctx stY) = 1 ->
(s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
rmrep stY mX -> mem_inv usegs mX -> bytes_at usegs mX (conc stY p) (zeros 4096) -> wr_at usegs mX (conc stY p) 4096 ->
rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (k (am_took (carve_st stY p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR))) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15bc4) fc None mX (seg_rom usegs)).
Proof.
intros until t6. intros AI HIDY Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX ZB ZW FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof MRX as (WFX & _).
eapply rimplT_evt.
{ Local Ltac2 Set LiaHints.tbl := fun () => "0020>38038706128.946722869515.11800000600:S4LOLES2Ha".
eapply (ram_carve_walk sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc mX junk lo stY p r);
first [exact MRX | exact MIX | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
| exact (ami_secretr _ _ AI) | exact HIDY | exact ZB | exact ZW | exact FRX | exact STX | exact LO | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
pose proof (carve_st_regions stY p) as RC.
eapply rfinish_K.
- eapply (ram_rel_carve st stY p r AI); assumption.
- exact MR2.
- exact MI2.
- exact ST2.
- eapply rrw_cells_magree; [exact ERRX| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X.
apply (rerrno_not_amfp stY a WFX); [exact (proj1 (ram_fp_same stY _ lo _ a RC) X) | lia].
- eapply rauxv_ok_magree; [exact AUXX| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stY _ WFX). apply rFP_am. exact (proj1 (ram_fp_same stY _ lo _ a RC) X).
- assert (RA : s_regions (am_took (carve_st stY p) (aadd p AREA_HDR) 100) = s_regions stY) by (cbn; exact RC).
eapply magree_trans; [exact AGX| apply rmagree_of_pres; exact PE2| intros a X; exact (rFP_same stY _ a RA X) | intros a X; apply rFP_am; refine (proj2 (ram_fp_same (carve_st stY p) _ lo _ a _) X); reflexivity].
- unfold brk_link_ps in *. rewrite rbrk_am_took, rbrk_carve. destruct (c_brk (ctx stY)) as [| |rid off]; auto.
rewrite rconc_am_took, rconc_carve. exact BLX.
- exact P1.
- exact P2.
- exact P3.
- unfold pw, oconc, wz. rewrite rconc_am_took, rconc_carve. rewrite (conc_aadd stY p AREA_HDR) by (rewrite Hr; eauto). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="TP"] Lemma rrepfoot_low stY a : rregions_wf stY -> rrepfoot stY a -> a < ATOP /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof.
intros WF H. rewrite rETP. pose proof WF as (_ & WR & _ & WA & WG). atop_facts.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>49647359182.4949657931118.5949657931118.6549657931118.6600000900K00h01ES1C5ATOPRS3Hin5ATOPR3RBC2D2S3Hin5ATOPR2Cb3Sb03Sb13RBC2D2S3Hin5ATOPR2Ca3Sa03Sa13RBC2D2".
destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; try lia.
- destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). atop_facts. lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). atop_facts. lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). atop_facts. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rfinish_path : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> c_init_done (ctx stY) = 1 -> c_avail_meta_areas (ctx stY) = Some p ->
(s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
pgal (snd p) -> lr_lo r <= r_base r + snd p ->
(s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
rmrep stY mX -> mem_inv usegs mX ->
rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (am_finish stY true k bail) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15c54) fc None mX (seg_rom usegs)).
Proof using AMP KH LO LOLE TK TP.
intros until t6. intros AI HIDY AMA Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. atop_facts.
pose proof MRX as (WFX & _ & (_ & _ & PGX & _) & _). pose proof WFX as (RS & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). atop_facts.
pose proof (conc_region' stY p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU. pose proof (lr_lo_ge r) as LRG.
Local Ltac2 Set LiaHints.tbl := fun () => "00M0?17260316077.25 18926302184.11422089672348.11422811622155.13826496810409.1382740296790.111 29800690184.14130983301007.13830987217776.1143159755484.114 32224975529.11438040802167.14139646542907.11442150904833.11446505993046.14151882385243.11453010370357.14154323714468.11455713317748.11456756879236.14257264412314.11458577821655.14159308579027.14564148442380.11464601901568.11464606291582.11264624998266.1418828123124.114 8832910886.142 00000E00F00U00V01001701=01Q01e02802I02O02_02j03003603<03L03M03[03\03b04404504:04K04N04O04XS3SAL4RBAL1H2H02H42H9SS2S13LO'3RBC2CpSS4LOLE2S13LO'5ATOPR3RBC2CpS2S02S1S4CASES4LOLE3SPR3LO'5ATOPRS4LOLE3SPR3LO'5ATOPRS2S13SLR3DR22Cp3LRGS2S15ATOPR3RBC2CpS4LOLES4LOLE3LO'5ATOPRS3LO'5ATOPRS4CASES4LOLES4CASES3SLR3RB02Cp3LRGSS2S13SLR2Cp2HxSS4CASES4LOLE3LO'2Hy1H2H0SS3IMGS2S13SLR2Cp3LRG1HS1GSS4LOLE2Hx".
assert (PAL : conc stY p mod 4096 = 0) by (rewrite Cp; unfold pgal in SAL; clear - RBAL SAL; Z.div_mod_to_equations; lia).
assert (IMG : conc stY p + 4096 <= 0x10000 \/ 0x50000 <= conc stY p) by (pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)); lia).
pose proof rETP as rETP'. pose proof TP as TPv. unfold wz in PGX.
unfold am_finish. rewrite AMA. unfold pgal in SAL. unfold PGSZ at 1. rewrite (proj2 (Z.eqb_eq _ _) SAL). cbn [negb].
eapply rimplT_evt.
{ apply (ram_to_mprotect (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX (conc stY p)). }
intros ms2 ->.
eapply (rimplT_mprotect o (conc stY p) PGSZ PROT_RW _ sX).
{ eapply rimpl_enode_dec_weaken; [| intros rsp a Hd; exact (dec_mprotect_rw_weaken _ _ rsp a Hd)].
unfold PGSZ, PROT_RW.
eapply rmprotect_spec with (lo := lo) (errv := e);
[ rewrite unsigned_lit by lia; exact STX | exact ERRX | exact PGX | exact MIX | reflexivity | reflexivity | reflexivity
| exact PAL | reflexivity | lia | lia | lia | lia | ..]; rewrite ?rETP', ?TPv, ?unsigned_lit by lia; unfold RPAGE_SIZE; try lia. }
intros ans ms3 [MP G]. unfold rmprotect_post in MP.
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & PG3 & CASE).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0x15c64)) with (Z_to_bv 64 0x15c64 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply rw_cells_transport; [exact FRX| exact MU3| exact WM3|]. rewrite rETP'. cbn. atop_facts. lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_unowned; [exact MRX| exact MU3| exact WM3|].
intros lo' hi' y [E|[E|[E|[]]]] Hy; inversion E; subst lo' hi'.
- intros RFt. destruct (rrepfoot_low stY y WFX RFt). atop_facts. lia.
- intros RFt. destruct (rrepfoot_low stY y WFX RFt). lia.
- eapply (rfresh_page_avoids stY mX p r y MRX); try assumption; lia. }
assert (M23 : magree (rFP stY) mX m3).
{ eapply magree_of_munch; [exact MU3|].
cbn. split; [| split; [| split; [| exact I]]]; intros x Hx.
- left. left. lia.
- left. right. left. rewrite TPv in Hx. exact Hx.
- left. right. right. right. exists (fst p), r. split; [exact Hr|]. split; [exact NK|]. lia. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AGX| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUXX| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
clear MU3 WM3.
destruct ans as [e'|b]; cbn in G.
-
cbn [range_val MM_syscalls.munmap_ret MM_syscalls.rg_errno] in *.
unfold mprotect_answer_ok, is_errno_form, neg_errno, TWO64, ENOSYS.
replace ((2 ^ 64 - e' =? 0) || ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64))) with true by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
replace ((2 ^ 64 - e' =? 0) || (2 ^ 64 - e' =? 2 ^ 64 - 38)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
cbn [negb].
eapply rimplT_evt.
{ eapply (ram_mp_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo e' stY);
first [exact MR3 | exact MI3 | exact TPv | exact ERR3 | exact G | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
intros ms4 [RP ERR4]. unfold ram_ret_post in RP. cbn [ms_mem] in ERR4.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & EQ & PE4 & WM4 & MI4 & ST4 & MR4).
rewrite EQ in ERR4 |- *. cbn [ms_mem] in ERR4.
eapply rfinish_K.
+ apply (ram_rel_none st stY AI).
+ exact MR4.
+ exact MI4.
+ exact ST4.
+ exact ERR4.
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
+ exact BLX.
+ exact P1.
+ exact P2.
+ exact P3.
+ reflexivity.
-
subst b. cbn [range_val] in *.
unfold mprotect_answer_ok. cbn [Z.eqb orb negb].
rewrite (am_carve_eq stY p k bail), (ram_take_took (carve_st stY p) p k bail).
destruct CASE as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
eapply rimplT_evt.
{ apply (ram_mp_ok0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 (Z_to_bv 64 0x15c64) F fc m3). }
intros ms4 ->.
eapply (rcarve_K stY p r m3 sX junk); first [exact AI | exact HIDY | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
| exact MR3 | exact MI3 | exact ZB | exact ZW | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | exact BLX | exact P1 | exact P2 | exact P3 | idtac].
unfold pgal. exact SAL.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rlive_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.
#[using="Type"] Lemma rfresh_of_ranges_free stY x L a :
s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
ranges_free (live_ranges stY) x L = true -> x + L <= ATOP -> x <= a < x + L -> fresh_addr st a.
Proof.
intros E1 E2 RF XC Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0040>22035104588.5144254599231.5164832337071.516749508636.51 00000700;00?00@S2XC2HaS2HaS2HaS".
split; [lia|]. rewrite (rlive_ranges_same st stY E1 E2) in RF.
eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rrepfoot_clear stY mY x L a :
rmrep stY mY -> ranges_free (live_ranges stY) x L = true -> rrepfoot stY a \/ rgrp_region_addr stY a -> ~ (x <= a < x + L).
Proof.
intros MRY RF H. pose proof MRY as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
pose proof (clear_range_of_ranges_free stY x L RF) as CR.
assert (IMG : forall y, 0x10000 <= y < 0x50000 -> ~ (x <= y < x + L)) by (intros y Hy; apply (rimage_clear_of_ranges_free stY x L y (rstatics_reserved _ RS) RF Hy)).
destruct H as [[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]|C]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *. atop_facts.
- apply IMG. Local Ltac2 Set LiaHints.tbl := fun () => "0030>16075364609.5857385639285.6257385639285.6300000300800=S1CS3HinS3Hin".
lia.
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
- destruct C as (rid & rg & Hrg & Krg & Hin). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="AMP TK LO LOLE TP KH"] Lemma rmmap_path : forall (stY : mstate) (mX : mem) (sX : PState) (junk : list byte) (e : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
AMI st stY -> c_init_done (ctx stY) = 1 -> s_regions stY = s_regions st -> c_avail_meta_area_count (ctx stY) = 0 ->
0 <= c_meta_alloc_shift (ctx stY) <= 38 ->
(forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
(forall q mr, (s_metas stY) !! q = Some mr -> meta_slot stY q) ->
ptrs_in (fun rid => (rid < s_next_rid stY)%N) stY ->
rmrep stY mX -> mem_inv usegs mX ->
rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
rimplT o (am_after_brk stY true k bail) sX Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15b64) fc None mX (seg_rom usegs)).
Proof.
intros until t6. intros AI HIDY RGY ACNT SHR TL MK PTR MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. atop_facts. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MRX as (WFX & _). pose proof WFX as (RS & WR & DJ & WA & WG).
set (n := Z.shiftl 2 (c_meta_alloc_shift (ctx stY))).
assert (NR : 2 <= n <= 2^39).
{ unfold n. Local Ltac2 Set LiaHints.tbl := fun () => "00l0?10706941820.14111803556607.13611825081397.13412366485855.119170082587.138  17997477514.97 18926596843.15018928426569.12219245667879.15619265643551.97 2179098206.152 23014285634.14823014534341.14123598322735.13925071664653.11929804951343.11930056767660.14430056767660.14630063058068.14730723765111.12530723846054.14130972718900.97 30985366036.11930987398027.11931332189928.14331332194059.14534127904326.13734969366989.95 35057702175.15037308221042.14637310060433.12338040802167.12438040802167.13941422703888.95 41910285729.96 46591911764.97 48055533212.13650594129072.12453006240274.11956091525403.14156391998866.1475744645808.133 59308579027.12659308579027.14559308587280.14259310612847.12359738815927.15062889468287.97 636407792.150  64146557256.97 65197122447.11965199153680.11965324126411.13966975430554.13567002792210.1396714072449.147 6714072449.153 67376300219.95 67798083931.1398838919088.97  00000400500E00I00J00N00O00P00Q00W00[00\00]00b01201601901<01@01D01I01]02102E02I02M02N02S02W02_02h02n03403503:03>03K03X03\03`03f04604H04W04[04j04n05>05?05@05A05B05F05P05Y05]05a05f05m05nS2XASS5ATOPR2NR2X02XCS2ERSS2LOSSSS4LOLES2PBSSS3SHRS4LOLE3LO'5ATOPRS2ERS1HS1HS2H0S2NRS3Hn1S4LOLE3SPR3LO'5ATOPRS4LOLE3SPR3LO'5ATOPRS4LOLE3SPR3LO'5ATOPRS2HyS2HySS3SHRS2NRS4LOLE1XS4LOLE2HyS4LOLES4LOLESS3SHRS2NRS4LOLE3LO'2XCS5ATOPR2NR2XCS2ERS2X0S1H2H0S5ATOPR2NR2X02XCS4LOLE3LO'2Hy1H2H0S4LOLE3LO'2Hy1HS2HqS5ATOPR2NR2XC1VS2NRS4LOLE3LO'5ATOPRSSSSS2NRS5ATOPR2XCS2NR1H2H0S2HaS2HaS3SHRS2NR2XCS".
rewrite Z.shiftl_mul_pow2 by lia. split.
- rewrite <- (Z.mul_1_r 2) at 1. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r with (b := 0); lia || (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
- change (2^39) with (2 * 2^38). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
unfold am_after_brk. rewrite ACNT. cbn [Z.eqb]. fold n.
eapply rimplT_evt.
{ apply (ram_to_mmap (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX stY MRX ltac:(lia)). }
intros ms2 ->. fold n.
pose proof MRX as MR2. pose proof MIX as MI2. pose proof FRX as FR2. pose proof STX as ST2. pose proof ERRX as ERR2. pose proof AGX as AG2. pose proof AUXX as AUX2.
set (m2 := mX) in MR2, MI2, FR2, ST2, ERR2, AG2, AUX2 |- *.
clear MRX MIX FRX STX ERRX AUXX AGX.
eapply (rimplT_mmap_none o (n * PGSZ) _ sX).
{ unfold PGSZ. replace (Z_to_bv 64 (n * 4096)) with (Z_to_bv 64 (n * 4096)%Z) by reflexivity.
eapply (rmmap_anon_spec true) with (lo := lo) (errv := e) (avoid := []);
[ rewrite unsigned_lit by lia; exact ST2 | exact ERR2 | exact MI2 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
rewrite ?rETP', ?TPv, ?unsigned_lit by lia; try lia. }
intros ans ms3 MP. unfold rmmap_anon_post in MP.
destruct ans as [e'|x].
-
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & ER).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0x15b90)) with (Z_to_bv 64 0x15b90 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
cbn [mmap_val]. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64.
replace ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [orb negb]. replace (2 ^ 64 - 4096 <? 2 ^ 64 - e') with true by (symmetry; apply Z.ltb_lt; lia).
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. rewrite rETP'. cbn. lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
intros lo' hi' y [E|[E|[]]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); atop_facts; lia. }
assert (M23 : magree (rFP stY) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| split; [| exact I]]; intros y Hy; [left; left; lia|]. left. right. left. rewrite TPv in Hy. exact Hy. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
eapply rimplT_evt.
{ eapply (ram_mm_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 n) u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo stY);
first [exact MR3 | exact MI3 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
intros ms4 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & -> & PE4 & WM4 & MI4 & ST4 & MR4).
eapply rfinish_K.
+ apply (ram_rel_none st stY AI).
+ exact MR4.
+ exact MI4.
+ exact ST4.
+ eapply rrw_cells_magree; [exact ERR3| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp stY a WFX); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
+ exact BLX.
+ exact P1.
+ exact P2.
+ exact P3.
+ reflexivity.
-
destruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2' & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & AOK).
rewrite unsigned_lit in MU3, ST3 by lia.
replace (ret_pc (Z_to_bv 64 0x15b90)) with (Z_to_bv 64 0x15b90 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
cbn [mmap_val]. rewrite (rregions_wf_atop stY WFX).
destruct (mmap_answer_ok ATOP (live_ranges stY) (n * PGSZ) x) eqn:VOK; cbn [negb]; [| apply rimplT_undef].
unfold mmap_addr_ok in AOK. apply andb_prop in AOK. destruct AOK as [AOK _]. apply andb_prop in AOK. destruct AOK as [AOK XC].
apply andb_prop in AOK. destruct AOK as [XA X0]. apply Z.eqb_eq in XA. apply Z.ltb_lt in X0. apply Z.leb_le in XC.
rewrite A2.mmap_len_round_up in XC. atop_facts. change page_size with 4096 in XA.
assert (LAL : round_up_pg (n * PGSZ) = n * PGSZ) by (apply round_up_pg_aligned; unfold PGSZ; apply Z.mod_mul; lia).
rewrite LAL in XC.
unfold mmap_answer_ok in VOK. rewrite LAL in VOK. apply orb_prop in VOK.
assert (RF : ranges_free (live_ranges stY) x (n * PGSZ) = true).
{ destruct VOK as [V|V]; [| apply andb_prop in V; destruct V as [_ V]; exact V].
unfold is_errno_form, TWO64 in V. apply andb_prop in V. destruct V as [V _]. apply Z.leb_le in V. unfold PGSZ in XC. exfalso. lia. }
unfold is_err, TWO64. replace (2 ^ 64 - 4096 <? x) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ in XC; lia).
unfold new_region. cbv beta iota zeta delta [fst snd].
set (rid := s_next_rid stY).
pose proof (rAMI_new_region st stY RKMeta x (n * PGSZ) AI ltac:(discriminate) ltac:(unfold PGSZ; lia)) as (AI1 & RG1 & CQ1 & CN1).
unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
set (st2 := upd_ctx _ st1).
assert (E2 : st2 = mm_ok_st st1 rid n) by reflexivity.
unfold MM_syscalls.mmap_raw in ST3 |- *. rewrite A2.mmap_len_round_up, LAL in ST3 |- *.
set (m3 := apply_unmaps m2' [(wa x, Z_to_bv 64 (n * PGSZ))]) in *.
assert (Hx1 : 0 <= x < 2^64) by (unfold PGSZ in XC; lia). assert (Hn1 : 0 <= n * PGSZ < 2^64) by (unfold PGSZ in *; lia). assert (Hxn : x + n * PGSZ <= 2^64) by (unfold PGSZ in *; lia).
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ apply (rw_cells_unmaps_other usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn).
- eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. lia.
- cbn. unfold PGSZ in *. lia. }
assert (ERR4 : rw_cells usegs m3 (errno_addr tp) [C4 e]).
{ apply (rw_cells_unmaps_other usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); [exact ERR3|]. cbn. rewrite rETP'.
pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x2ef30 - 164) (rstatics_reserved _ RS) RF ltac:(lia)).
pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x2ef30 - 161) (rstatics_reserved _ RS) RF ltac:(lia)). unfold PGSZ in *. lia. }
assert (MI4 : mem_inv usegs m3) by (apply (mem_inv_unmaps usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); exact MI3).
assert (MR2' : rmrep stY m2').
{ eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); atop_facts; lia. }
assert (MR3 : rmrep stY m3).
{ eapply rmrep_transport_agree'; [exact MR2'|]. intros y Hy HF. unfold m3. apply (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
rewrite wa_unsigned by lia. pose proof (rrepfoot_clear stY m2' x (n * PGSZ) y MR2' RF HF). lia. }
assert (MRn : rmrep st1 m3).
{ unfold st1. apply (RA2.rmrep_new_region stY m3 m3 x (n * PGSZ) RKMeta);
first [ exact MR3
| eapply ptrs_in_mono; [| exact PTR]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
| apply (ami_fresh _ _ AI); unfold rid; lia
| atop_facts; rewrite LAL; exact XC
| rewrite LAL; exact RF
| intros; reflexivity
| intros; discriminate
| unfold PGSZ in *; lia ]. }
assert (M23 : magree (rFP stY) m2 m3).
{ intros y Hy Hc. unfold m3. rewrite (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
- apply MU3. rewrite wa_unsigned by lia. cbn. split; [| exact I]. intros X. apply Hc. left. left. lia.
- rewrite wa_unsigned by lia. destruct (Z.lt_ge_cases y x); [lia|]. destruct (Z.lt_ge_cases y (x + n * PGSZ)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stY x (n * PGSZ)); [exact RGY| exact (ami_reserved _ _ AI)| exact RF| atop_facts; exact XC| lia]. }
assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
clearbody m3. clear MU3 WM3 MR2 MR2' MI3 ERR3.
eapply rimplT_evt.
{ eapply (ram_mm_ok sp gp tp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo x n st1 st1 rid (mkRegion RKMeta x (n * PGSZ)));
first [exact MRn | exact MI4 | intros a X; exact X | exact RG1 | reflexivity | exact XA | exact X0 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | idtac];
try (unfold PGSZ in *; lia).
change (ctx st1) with (ctx stY). lia. }
intros ms4 (m4 & -> & PE4 & WM4 & MI5 & FR4 & ST4 & MR4).
pose proof MRn as (WFn & _).
assert (RG2 : forall q, (s_regions st2) !! q = if decide (q = rid) then Some (mkRegion RKMeta x (n * PGSZ)) else (s_regions stY) !! q).
{ intros q. change (s_regions st2) with (<[rid := mkRegion RKMeta x (n * PGSZ)]> (s_regions stY)).
destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
replace (Z_to_bv 64 (x + 4096)) with (Z_to_bv 64 (conc st2 (rid, 4096))) by (change (conc st2 (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
eapply (rfinish_path st2 (rid, 4096) (mkRegion RKMeta x (n * PGSZ)) m4 sX junk e).
+ unfold st2. apply (rAMI_ctx st st1 _ AI1).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AI1).
* right. exists (rid, PGSZ), (mkRegion RKMeta x (n * PGSZ)). cbn [fst]. split; [reflexivity|]. split; [exact RG1| cbn; discriminate].
* left. reflexivity.
+ exact HIDY.
+ reflexivity.
+ cbn [fst]. rewrite RG2. destruct (decide (rid = rid)); [reflexivity| congruence].
+ cbn. discriminate.
+ cbn. lia.
+ cbn [snd r_len]. rewrite LAL. unfold PGSZ. lia.
+ unfold pgal. reflexivity.
+ cbn. lia.
+ change (s_areas st2) with (s_areas stY). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
exfalso. destruct (WA _ _ EA) as (rr & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
+ intros j Hj. change (s_metas st2) with (s_metas stY). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
exfalso. destruct (MK _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr & Hrr & _).
assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
+ intros tl Htl. change (s_areas st2) with (s_areas stY). apply TL. exact Htl.
+ cbn. lia.
+ exact MR4.
+ exact MI5.
+ exact FR4.
+ exact ST4.
+ eapply rrw_cells_magree; [exact ERR4| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp st1 a WFn); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below st1 a WFn (rFP_am st1 a X))].
+ eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| |].
* intros a X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq. rewrite RG2.
destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate|]. repeat split; auto; lia.
* intros a X. eapply rFP_same; [| exact (rFP_am st1 a X)]. reflexivity.
+ unfold brk_link_ps in *. change (c_brk (ctx st2)) with (c_brk (ctx stY)).
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _).
destruct (c_brk (ctx stY)) as [| |rb ob]; auto. change (conc st2 (rb, ob)) with (conc st1 (rb, ob)). rewrite CQ1; [exact BLX|]. cbn [fst]. unfold rid. lia.
+ exact P1.
+ exact P2.
+ exact P3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc"] Lemma rimage_range_clear stY x L : s_reserved stY = ref_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
x + L <= 0x10000 \/ 0x50000 <= x.
Proof.
intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>55003855020.5200000?S2HL1H2H02H12H2".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbrk_live_path : forall (stI : mstate) (brid : N) (boff : Z) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> c_init_done (ctx stI) = 1 -> s_regions stI = s_regions st -> brk_link_ps stI s ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkLive brid boff ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv usegs m1 ->
rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
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
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15ab4) fc None m1 (seg_rom usegs)).
Proof.
intros until t6. intros AMPI AI HIDI RGI BLI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. atop_facts. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6) & _). pose proof WF1 as (RS & WR & DJ & WA & WG).
pose proof (amp_brk stI AMPI) as HB. rewrite BRK in HB. destruct HB as (r & Hr & Kr & Lr & OAL & O4 & FRA & UNQ).
pose proof (conc_region' stI (brid, boff) r Hr) as OLD. cbn [snd] in OLD.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr). atop_facts. rewrite Lr in RBC.
assert (RUB : round_up_pg boff = boff) by (apply round_up_pg_aligned; unfold PGSZ in OAL; exact OAL). rewrite RUB in RBC.
set (old := conc stI (brid, boff)) in *.
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
unfold brk_link_ps in BLI. rewrite BRK in BLI. fold old in BLI.
cbv zeta.
eapply rimplT_evt.
{ Local Ltac2 Set LiaHints.tbl := fun () => "00n0?10157438998.11810159569049.11510517620025.1571123187672.146 11803467556.12112417435289.15414021459664.12614261229597.13214801318322.14016671995537.12216671995537.15218889376915.15918926392770.11718926756720.12318939190001.15918941394330.11819245667879.16420519352896.1282063004445.146 22093328857.11822178757405.14625069796650.15525071778694.15326308011740.14527259221976.14629979368849.1593083493640.119 31194372668.13631332194059.13833421808466.14033424336918.13834244755217.14534254993293.15934752135640.14635001855670.15139220075992.14639570392592.13039638388940.14039640493300.13940195148532.12941293112974.15941299370787.14944483050603.12144611174109.11944644643966.11544708267278.16149253317592.14650319705501.11850906287447.12250906340591.11551864552859.12255123685831.15955243536250.12055661371392.11557088489432.14657222941531.15959579068465.12159942308312.14663578776024.1466383655373.142 65917611529.125839959391.119  00000@00P00Q00R00b00m01201301701;01?01C01D01E01F01G01H01U01V01\01]01^01n02602702802=02K02O02U02Y02]02e02f03O03P03U03Y03\04H04M04R04]04^04_04c04d05E05O05^05a05b06;06K06L06M06N06O06P06Q06V06WS2Lr3OLD3RB03RL0S2Lr3OLD3RB03RL0SSS4LOLE3LO'5ATOPRS3LO'5ATOPRS3IMGSS2OCS2HyS2HyS2O4SSSSSS4LOLE3LO'2OCSS4OALDSSS4LOLE3LO'5ATOPRS3OLD2OCSSS3OALS5ATOPR2OC3Ho1S2HyS1H2H0S2HyS2O4S2Lr3RL0SS2Lr3OAL2O43OLD3RB04RBAL3RL04OALD3Ho13IMGSS3IMGS2H0S1HS2Lr3OAL2O43OLD3RB04RBAL3RL04OALD3Ho13IMG2HyS3OLDS3OLDS3LO'5ATOPRSSS2HjSS2Lr3OAL2O43OLD3RB04RBAL3RL04OALDS5ATOPR2OCS5ATOPR3OLD3RBCS1HSS5ATOPR2Lr3OLD3RB03RL02OCS2Lr3OLD3RB03RL0SSSSSSS3IMGF".
eapply (ram_disp_live _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI brid boff); [exact MR1| exact ACNT| exact BRK| fold old; lia| fold old; unfold PGSZ; lia]. }
intros ms2 ->. fold old.
eapply (rimplT_brk o (old + PGSZ) _ s).
{ unfold PGSZ; lia. }
{ rewrite BLI. unfold PGSZ.
exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 0x15ad8 (or_introl eq_refl) old (old + 4096) ltac:(lia)). }
intros a ms3 ->. rewrite BLI. unfold brk_res, brk_mem, rbrk_regs.
destruct a.
-
unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
destruct (brk_pages_ok stI old PGSZ) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC. rewrite (rregions_wf_atop stI (proj1 MR1)) in OC.
unfold PGSZ in OC. atop_facts. unfold PGSZ in RF.
assert (OALD : old mod 4096 = 0) by (rewrite OLD; rewrite Z.add_mod, RBAL by lia; unfold PGSZ in OAL; rewrite OAL; reflexivity).
rewrite (brk_new_pages_aligned old 4096) by (first [lia | exact OALD | reflexivity]).
rewrite (rgr_eq stI brid r boff Hr).
set (stG := set_regions _ stI).
unfold PGSZ. rewrite (am_after_brk_false_eq stG _ (brid, boff) k bail) by (cbn; first [lia | reflexivity | unfold PGSZ in OAL; exact OAL]).
rewrite am_carve_took, carve_st_brk_irrel.
set (stX := upd_ctx _ stG).
assert (Ho1 : 0 <= old < 2^64) by lia. assert (Hn1 : 0 <= 4096 < 2^64) by lia. assert (Hon : old + 4096 <= 2^64) by lia.
pose proof (rimage_range_clear stI old 4096 (rstatics_reserved _ RS) RF ltac:(lia)) as IMG.
set (m2 := apply_zeros m1 [(wa old, Z_to_bv 64 4096)]).
unfold rctx_head_cells, rsecw in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6. fold old in HX6.
assert (HC2 : rw_cells usegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact HX1| cbn; unfold RCTX; lia]).
assert (TC2 : rw_cells usegs m2 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (wz old)])
by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact HX6| cbn; unfold RCTX; lia]).
assert (MI2 : mem_inv usegs m2).
{ apply (mem_inv_zeros usegs m1 old 4096 Ho1 Hn1 Hon MI1). intros y Hy. apply ref_ro_addr_false. lia. }
assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra))
by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact FR1| cbn; lia]).
assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)) by (apply (stk_zeros usegs m1 old 4096 Ho1 Hn1 Hon); exact ST1).
assert (ERR2 : rw_cells usegs m2 (errno_addr tp) [C4 e1])
by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact ERR1| cbn; rewrite rETP'; lia]).
pose proof (rw_cells_zeros_new usegs m1 old 4096 Ho1 Hn1 Hon) as ZN. fold m2 in ZN.
assert (MU12 : munch [(old, old + 4096)]%Z m1 m2) by (apply (munch_zeros m1 old 4096 Ho1 Hn1 Hon); [apply munch_refl| cbn; lia]).
assert (WM12 : wmono usegs m1 m2) by (apply (wmono_zeros usegs m1 old 4096 Ho1 Hn1 Hon); apply wmono_refl).
assert (MR2 : rmrep stI m2).
{ eapply rmrep_transport_unowned; [exact MR1| exact MU12| exact WM12|].
intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'. intros RFt. apply (rrepfoot_clear stI m1 old 4096 y MR1 RF (or_introl RFt)). lia. }
assert (M12 : magree (rFP stI) m1 m2).
{ intros y Hy Hc. unfold m2. apply (zeros_outside m1 old 4096 Ho1 Hn1 Hon). rewrite wa_unsigned by lia.
destruct (Z.lt_ge_cases y old); [lia|]. destruct (Z.lt_ge_cases y (old + 4096)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI old 4096); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| atop_facts; lia| lia]. }
clearbody m2.
eapply rimplT_evt.
{ eapply (ram_bl_ok _ gp tp t0 t1 t2 (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 _ s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (old + 4096)); [lia | | | exact MI2].
- unfold pw in HC2. cbn [oconc] in HC2. exact HC2.
- unfold wz in TC2. exact TC2. }
intros ms4 (m3 & -> & MU3 & WM3 & MI3 & HC3 & TC3). replace (old + 4096 - 4096) with old by lia.
pose proof (rAMI_grow st stI brid r boff AI Hr ltac:(rewrite Kr; discriminate) Lr) as (AIG & CQG & RG'). fold stG in AIG, CQG, RG'.
assert (MRG : rmrep stG m2).
{ unfold stG. apply (rmrep_grow_region stI m2 brid r boff MR2 Hr);
first [ rewrite Kr; discriminate
| exact Lr
| unfold PGSZ in OAL; exact OAL
| rewrite <- OLD; exact RF
| exact (amp_rpos stI AMPI)
| intros q rq Hq NE KB; apply NE; exact (UNQ q rq Hq KB)
| unfold PGSZ in *; lia ]. }
assert (PWX : forall q, pw stX q = pw stI q) by (intros [q|]; unfold pw, oconc; [change (conc stX q) with (conc stG q); rewrite CQG|]; reflexivity).
assert (PWG : forall q, pw stG q = pw stI q) by (intros [q|]; unfold pw, oconc; [rewrite CQG|]; reflexivity).
assert (CQX : forall q, conc stX q = conc stI q) by (intros q; change (conc stX q) with (conc stG q); apply CQG).
assert (MRX : rmrep stX m3).
{ eapply (rmrep_ctx_frameW stG stX m2 m3 _ MRG MU3 WM3); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
- left. unfold rctx_head_cells, rsecw. rewrite !PWX.
cbn [ctx stX stG upd_ctx s_ctx set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (s_ctx stI) with (ctx stI). unfold wz at 5. exact HC3.
- right. split; [| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
unfold actives. apply map_ext. intros i. rewrite PWX, PWG. reflexivity.
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
- left. unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
change (conc stX (brid, boff + 4096)) with (conc stG (brid, boff + 4096)).
rewrite CQG. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold wz.
replace (r_base r + (boff + 4096)) with (old + 4096) by lia. change (s_ctx stI) with (ctx stI). exact TC3. }
assert (M23 : magree (rFP stX) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. unfold RCTX. split; [| split; [| exact I]]; intros y Hy; left; right; right; left; unfold RCTX; lia. }
assert (ZN3 : rw_cells usegs m3 old [CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]).
{ eapply rw_cells_transport; [exact ZN| exact MU3| exact WM3|]. cbn. unfold RCTX. lia. }
destruct ZN3 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (AGX1 : forall y, rFP stI y -> rFP stX y).
{ intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. destruct (ami_regions _ _ AI q rq) as (r0 & H0 & _); [rewrite <- RGI; exact Hq|].
destruct (decide (q = brid)) as [->|NE].
- eexists. split; [exact RG'|]. rewrite Hr in Hq. inversion Hq; subst. cbn. repeat split; lia.
- exists rq. change (s_regions stX) with (<[brid := mkRegion (r_kind r) (r_base r) (boff + 4096)]> (s_regions stI)). rewrite lookup_insert_ne by congruence. repeat split; auto; lia. }
assert (AG3 : magree (rFP stX) m m3).
{ eapply magree_trans; [| exact M23| exact AGX1| intros y X; exact X]. eapply magree_trans; [exact AG1| exact M12| intros y X; exact X| intros y X; exact X]. }
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
{ eapply rauxv_ok_magree; [exact AUX1| |intros y X; exact (rFP_below stX y (proj1 MRX) X)].
eapply magree_trans; [exact M12| exact M23| exact AGX1| intros y X; exact X]. }
replace (Z_to_bv 64 old) with (Z_to_bv 64 (conc stX (brid, boff))) by (change (conc stX (brid, boff)) with (conc stG (brid, boff)); rewrite CQG; reflexivity).
eapply (rcarve_K stX (brid, boff) (mkRegion (r_kind r) (r_base r) (boff + 4096)) m3 _ junk e1);
first [exact RG' | exact HIDI | exact MRX | exact MI3 | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | reflexivity | idtac].
+ unfold stX. apply (rAMI_ctx st stG _ AIG).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AIG).
* left. reflexivity.
* right. right. exists brid, (boff + 4096), (mkRegion (r_kind r) (r_base r) (boff + 4096)). split; [reflexivity|]. split; [exact RG'|]. cbn. rewrite Kr. discriminate.
+ cbn. rewrite Kr. discriminate.
+ cbn. lia.
+ cbn [snd r_len]. rewrite round_up_pg_aligned; [lia|]. rewrite Z.add_mod, OAL by lia. reflexivity.
+ unfold pgal. unfold PGSZ in OAL. exact OAL.
+ cbn [snd r_base]. unfold lr_lo. cbn [r_kind r_base]. rewrite Kr. unfold PGSZ in O4. lia.
+ change (s_areas stX) with (s_areas stI). apply (proj1 (FRA (brid, boff) eq_refl ltac:(cbn; lia))).
+ intros j Hj. change (s_metas stX) with (s_metas stI). apply (proj2 (FRA (aadd (brid, boff) (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
+ intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
+ cbn. lia.
+ change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZB.
+ change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZW.
+ unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
rewrite CQX. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold PGSZ. lia.
-
unfold brk_answer_ok. rewrite Z.eqb_refl.
replace (old =? old + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [orb negb].
eapply rimplT_evt.
{ unfold PGSZ. eapply (ram_bl_fail _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI old); [exact MR1| exact ACNT| lia| lia| exact MI1]. }
intros ms4 (m3 & -> & MU3 & WM3 & MI3 & MRD).
assert (M13 : magree (rFP stI) m1 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. atop_facts. lia. }
eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 s junk e1); first [exact MRD | exact MI3 | exact HIDI | reflexivity | idtac].
+ apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
+ exact RGI.
+ exact ACNT.
+ change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
+ exact TLI.
+ exact MKI.
+ pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
+ eapply rw_cells_transport; [exact FR1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply rw_cells_transport; [exact ERR1| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
+ eapply rauxv_ok_magree; [exact AUX1| exact M13| intros y X; exact (rFP_below stI y WF1 X)].
+ eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1 M13); intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> c_init_done (ctx stI) = 1 -> s_regions stI = s_regions st ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv usegs m1 ->
rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
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
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15ab4) fc None m1 (seg_rom usegs)).
Proof using AMP ERR KH LO LOLE TK TP.
intros until t6. intros AMPI AI HIDI RGI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1 _.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. atop_facts. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6) & _). pose proof WF1 as (RS & WR & DJ & WA & WG).
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
unfold rctx_head_cells, rsecw in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6.
eapply rimplT_evt.
{ eapply (ram_disp_untried _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
intros ms2 ->.
eapply (rimplT_brk0 o _ s).
{ exact (ram_brk0_node x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1). }
intros cur ms3 [-> CR]. unfold rbrk_regs.
destruct (brk0_answer_ok cur) eqn:B0; cbn [negb]; [| apply rimplT_undef].
unfold brk0_answer_ok, TWO64, PGSZ in B0. apply andb_prop in B0. destruct B0 as [B0 _]. apply andb_prop in B0. destruct B0 as [C0 CAL].
apply Z.ltb_lt in C0. apply Z.eqb_eq in CAL.
rewrite (round_up_pg_aligned cur CAL). cbv zeta. unfold PGSZ.
replace (2 * 4096) with 8192 by reflexivity.
eapply rimplT_evt.
{ Local Ltac2 Set LiaHints.tbl := fun () => "01k0?10947458327.10611673973531.12311803467684.11711803634851.10911807078258.10712415402805.1951655170994.118 16671995537.11316671995537.11816674350962.20216674350962.20318197161723.12118925874810.15818926535208.17818926678662.19318928498840.11319245567059.20219265708313.13322706596293.18422923820699.11422923917470.10024347241947.11025069682474.19325069796649.19625069843881.17426037337389.15826678373646.21026680472829.19326682372276.20426682374324.21026901956799.17427780153549.19928002138295.11129784180006.13330972783153.15730972783154.13331121290587.11931332171611.16931332171738.18431332192896.12931332194059.12831332194325.16731332194325.16831332194325.16931332194325.19331332194325.19531334093916.21031334095964.20431338480102.2103228147421.178 32532659937.17833311269285.17833313544981.11334210629134.13034212002357.15734278262948.16337097343144.19937311030038.13339210363599.13339532249910.19939621423194.19939631659935.21040195148532.12244031104390.17544483050731.11744483185900.10844610905063.16345623613246.13345625714495.12745625788729.11648839323451.18448839323578.16948839346420.16748839346420.16848839346420.16948839346420.19348839346420.19548841508029.21048841510077.20448845639943.21050324209823.11350459855632.19950602379985.1685115421043.199 51435258009.19951489998255.21051490000303.20451491899878.16751491899878.16851491899878.16951491899878.19351491899878.19551492007465.18451492007592.16951493998613.21051864552859.11854655238256.15857212665560.1995756892644.199 57628789700.18458258292945.16359308587280.17959579071025.11560492756848.12960494842696.13060494849046.12961132225997.11161429770410.21062831717169.19962889403513.13364146623566.1336630996118.133 7170411736.133 7172389982.111 7172521050.178 7172521177.127 7174751978.113 828472123.192  8838854326.133 8876763758.178 8879074280.130 8881430464.206 9164483184.199 00000400900I00J00Z00e00j00n01201501801E01F01G01H01I01J01P01T01X01_01`01e01f02602:02N02\02h03<03=03>03?03G03[03o04404804<04@04D04H04L04c04g05705U05g06E06F06G06L06Q06W06X06Y06Z06_06`06a06b06f07107207=07H07I07N07X07b07f07j08508@08P08[08_08`08a08b08f08g09409509609I09Q09d0:70:J0:N0:e0;10;80;K0;N0;R0;S0;T0;[0;\0;`0;a0;d0;h0;l0<00<40<50<E0<F0<G0<K0<O0<S0<W0<[0<_0<`0<d0<h0<l0<mS2CRS3IMGS4LOLE3LO'5ATOPRSS4LOLE3LO'5ATOPRS3LO'5ATOPRS3IMGS2HyS2HyS1XS1XS4LOLE3LO'2OCSSSSSS4LOLES2N1S2CRS2CR2C0SS3IMGSS4LOLE3LO'5ATOPRS2HES3LO'2Hy2Cb3Sb14RBCbS3LO'5ATOPR2HyS3LO'2Hy3RBCS3LO'2Hy2Ca3Sa14RBCaSFSS3LO'2OCS4LOLE3SPR3LO'5ATOPRS4LOLE3SPR3LO'5ATOPRS3IMGS2HyS2HyS2HyS2HyS2HyS2HyS4LOLE3SPR3LO'5ATOPR2HyS2HyS5ATOPR2C02OC2HyS5ATOPR2Hy2Ca3Sa03Sa13RBa4RBCaS5ATOPR2Hy3RB03RBCS5ATOPR2Hy2Cb3Sb03Sb13RBb4RBCbFFS3CALS3CALS1H2H0SFFS3IMGSFFS2HyS2CR3IMG2HySS3LO'5ATOPRS3LO'5ATOPRSS3HcnS5ATOPR2OCS5ATOPR2OCS2N4S2N3S2CR3IMG2HyS2CR3IMG2HyS4LOLE3LO'2OC2HyS2CR3IMG2HyS2HyFFFS2CRFS5ATOPR2CR2OCFFS2Hy2Ca3Sa03Sa13Da2S2Hy3Dq2S4LOLE3LO'5ATOPR2HyS4LOLE3LO'5ATOPR2HyS2Hy4LOLE3LO'5ATOPRS2HyS4LOLE3LO'2OC2Hy2CR3IMGS4LOLE2N22N3S2N12N2S2Hy2Cb3Sb03Sb13Db2S1HS2HESFS2N02N1FS2HqSS1HS2H0S2HnS2CRS2HyFS4LOLE3LO'5ATOPRSSS2C0S2C0S2C0S2C0S2CRS2HqSS2OCS2OCS2OCF".
eapply (ram_bu_mid _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m1 cur); [lia| exact CAL| unfold wz in HX6; exact HX6| exact MI1]. }
intros ms4 (a2' & m2 & -> & MU2 & WM2 & MI2 & TC2).
eapply (rimplT_brk o (cur + 8192) _ (set_brk_ps cur s)).
{ lia. }
{ exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 0x15b14 (or_intror eq_refl) cur (cur + 8192) ltac:(lia)). }
intros a ms5 ->. cbn [ps_brk set_brk_ps]. unfold brk_res, brk_mem, rbrk_regs.
assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (ERR2 : rw_cells usegs m2 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (HC2 : rw_cells usegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (eapply rw_cells_transport; [exact HX1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
assert (M12 : magree (rFP stI) m1 m2).
{ eapply magree_of_munch; [exact MU2|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. atop_facts. lia. }
destruct a.
-
unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
destruct (brk_pages_ok stI cur 8192) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC. rewrite (rregions_wf_atop stI (proj1 MR1)) in OC.
atop_facts.
rewrite (brk_new_pages_aligned cur 8192) by (first [lia | exact CAL | reflexivity]).
pose proof (rimage_range_clear stI cur 8192 (rstatics_reserved _ RS) RF ltac:(lia)) as IMG.
assert (Hc1 : 0 <= cur < 2^64) by lia. assert (Hn1 : 0 <= 8192 < 2^64) by lia. assert (Hcn : cur + 8192 <= 2^64) by lia.
set (m3 := apply_zeros m2 [(wa cur, Z_to_bv 64 8192)]).
assert (HC3 : rw_cells usegs m3 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact HC2| cbn; unfold RCTX; lia]).
assert (TC3 : rw_cells usegs m3 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)])
by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [unfold RCTX in TC2 |- *; exact TC2| cbn; unfold RCTX; lia]).
assert (MI3 : mem_inv usegs m3) by (apply (mem_inv_zeros usegs m2 cur 8192 Hc1 Hn1 Hcn MI2); intros y Hy; apply ref_ro_addr_false; lia).
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact FR2| cbn; lia]).
assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -64)) by (apply (stk_zeros usegs m2 cur 8192 Hc1 Hn1 Hcn); exact ST2).
assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 e1]) by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact ERR2| cbn; rewrite rETP'; lia]).
pose proof (rw_cells_zeros_new usegs m2 cur 8192 Hc1 Hn1 Hcn) as ZN. fold m3 in ZN.
assert (M23 : magree (rFP stI) m2 m3).
{ intros y Hy Hc. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia.
destruct (Z.lt_ge_cases y cur); [lia|]. destruct (Z.lt_ge_cases y (cur + 8192)); [| lia].
exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| atop_facts; lia| lia]. }
assert (E23 : forall y, 0 <= y < 2^64 -> ~ (cur <= y < cur + 8192) -> m3 (wa y) = m2 (wa y)).
{ intros y Hy Hn. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia. lia. }
clearbody m3.
eapply rimplT_evt.
{ eapply (ram_bu_ok _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m3 cur);
first [exact TC3 | lia]. }
intros ms6 ->.
pose proof MI3 as MI4. pose proof FR3 as FR4. pose proof ST3 as ST4. pose proof TC3 as TC4. pose proof HC3 as HC4. pose proof ERR3 as ERR4.
eapply (rimplT_mmap_fixed o cur PGSZ _ (set_brk_ps (cur + 8192) (set_brk_ps cur s))).
{ unfold PGSZ. eapply (rmmap_fixed_spec (dec_mmap_fixed cur 4096) (fx_rel cur)) with (lo := lo) (errv := e1);
[ intros rsp fa Hd; exact (dec_mmap_fixed_shape cur 4096 rsp fa Hd)
| rewrite unsigned_lit by lia; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
rewrite ?A2.mmap_len_round_up, ?rETP', ?TPv, ?unsigned_lit by lia; try (change (round_up_pg 4096) with 4096); try lia. }
intros fa ms7 MP. unfold rmmap_fixed_post in MP.
destruct MP as (rr & u & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5 & REL & -> & MU5 & WM5 & MI5 & ST5 & ERR5).
rewrite A2.mmap_len_round_up in MU5. change (round_up_pg 4096) with 4096 in MU5. rewrite unsigned_lit in MU5, ST5 by lia.
replace (ret_pc (Z_to_bv 64 0x15b38)) with (Z_to_bv 64 0x15b38 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
replace (mmap_fixed_answer_ok cur (fixed_val cur fa)) with true.
2:{ symmetry. unfold mmap_fixed_answer_ok, is_errno_form, fixed_val, neg_errno, TWO64.
destruct fa as [e| |e]; cbn in REL.
- destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
- apply orb_true_iff. right. apply Z.eqb_refl.
- destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
cbn [negb].
unfold new_region. cbv beta iota zeta delta [fst snd].
set (rid := s_next_rid stI).
pose proof (rAMI_new_region st stI RKBrk cur 8192 AI ltac:(discriminate) ltac:(lia)) as (AI1 & RG1 & CQ1 & CN1).
unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
rewrite (am_after_brk_false_eq st1 _ (rid, 4096) k bail) by (cbn; first [lia | reflexivity]).
rewrite am_carve_took, carve_st_brk_irrel.
set (stX := upd_ctx _ st1).
assert (E45 : forall y, 0 <= y < 2^64 -> ~ (bv_unsigned sp - 64 - 80 <= y < bv_unsigned sp - 64) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 4096) -> m5 (wa y) = m3 (wa y)).
{ intros y Hy N1 N2 N3. apply MU5. rewrite wa_unsigned by lia. cbn. rewrite ?rETP' in *. repeat split; lia. }
assert (HC5 : rw_cells usegs m5 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end)).
{ eapply RA2.rrw_cells_agree; [exact HC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
assert (TC5 : rw_cells usegs m5 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
{ eapply RA2.rrw_cells_agree; [exact TC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
{ eapply RA2.rrw_cells_agree; [exact FR4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
eapply rimplT_evt.
{ eapply (ram_b_store _ gp tp u0 u1 u2 _ u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (cur + 8192));
first [exact HC5 | exact TC5 | exact MI5 | lia]. }
intros ms8 (m6 & -> & MU6 & WM6 & MI6 & HC6 & TC6). replace (cur + 8192 - 4096) with (cur + 4096) by lia.
assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
assert (E16 : forall y, 0 <= y < 2^64 ->
~ (RCTX + 40 <= y < RCTX + 48) -> ~ (RCTX + 920 <= y < RCTX + 928) -> ~ (lo <= y < bv_unsigned sp) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 8192) ->
m6 (wa y) = m1 (wa y)).
{ intros y Hy N0 N1 N2 N3 N4.
rewrite (MU6 (wa y)) by (rewrite wa_unsigned by lia; cbn; unfold RCTX in *; lia).
rewrite (E45 y Hy) by (rewrite ?rETP' in *; lia).
rewrite (E23 y Hy) by lia.
apply MU2. rewrite wa_unsigned by lia. cbn. unfold RCTX in *. atop_facts. lia. }
assert (MRn1 : rmrep st1 m1).
{ unfold st1. apply (RA2.rmrep_new_region stI m1 m1 cur 8192 RKBrk);
first [ exact MR1
| eapply ptrs_in_mono; [| exact PTRI]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
| exact FRr | exact FRs
| atop_facts; change (round_up_pg 8192) with 8192; lia
| change (round_up_pg 8192) with 8192; exact RF
| intros; reflexivity
| intros; discriminate
| lia ]. }
assert (CQX : forall q, fst q <> rid -> conc stX q = conc stI q) by (intros q Hq; change (conc stX q) with (conc st1 q); apply CQ1; exact Hq).
pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
assert (PWX : forall q, optr_in (fun r => (r < s_next_rid stI)%N) q -> pw stX q = pw stI q).
{ intros [q|] Hq; unfold pw, oconc; [rewrite CQX; [reflexivity|]|reflexivity]. cbn in Hq. unfold rid. lia. }
assert (MRX : rmrep stX m6).
{ apply (rmrep_agree_but_ctx st1 stX m1 m6 MRn1); try reflexivity.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RMLOCK, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RLIBC, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RGOT_SSP, RCTX in *; lia.
- intros y Hy. apply E16; rewrite ?rETP'; unfold RSSP_GUARD, RCTX in *; lia.
- intros a ar Ha y Hy. change (s_areas st1) with (s_areas stI) in Ha.
destruct (rarea_conc stI a ar WF1 Ha) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RBa & RBAa & RBCa).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as (Da1 & _ & Da23 & Da2). atop_facts.
rewrite (CQ1 a) in Hy by (intros E; rewrite E, FRr in Hra; discriminate).
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. eapply rrepfoot_area; [exact Ha| lia].
- intros b gh Hb y Hy. change (s_groups st1) with (s_groups stI) in Hb.
destruct (rgroup_conc stI b gh WF1 Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Alb & RBb & RBCb).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). destruct (rreserved_disjoint _ _ RFb) as (Db1 & _ & Db23 & Db2). atop_facts.
pose proof (round_up_pg_ge (r_len rb)).
rewrite (CQ1 b) in Hy by (intros E; rewrite E, FRr in Hrb; discriminate).
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. do 5 right. left. exists b, gh. split; [exact Hb| lia].
- intros q rq Hq Kq y Hy.
assert (Hq' : (s_regions stI) !! q = Some rq).
{ change (s_regions st1) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)) in Hq.
destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; discriminate| rewrite lookup_insert_ne in Hq by congruence; exact Hq]. }
destruct (WR _ _ Hq') as (RB0 & _ & _ & RBC & RFq). destruct (rreserved_disjoint _ _ RFq) as (Dq1 & _ & Dq23 & Dq2). atop_facts.
apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). right. exists q, rq. auto.
-
destruct (rmrep_ctx_mid_agree st1 stX m1 m6 MRn1 ltac:(right; repeat split; reflexivity) eq_refl) as (X2 & X3 & X4 & X5).
{ intros y Hy. apply E16; rewrite ?rETP'; unfold RCTX in *; lia. }
split; [| split; [exact X2| split; [exact X3| split; [exact X4| split; [exact X5|]]]]].
+ unfold rctx_head_cells, rsecw. rewrite !PWX by assumption.
cbn [ctx stX st1 upd_ctx s_ctx set_next_rid set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (s_ctx stI) with (ctx stI). unfold pw in HC6 |- *. cbn [oconc] in HC6 |- *. unfold wz. exact HC6.
+ unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. change (s_ctx st1) with (ctx stI). unfold wz. exact TC6. }
assert (ZP3 : rw_cells usegs m3 (cur + 4096) [CB 4096 (zeros 4096)]).
{ destruct ZN as [[_ ZB0] ZW0]. cbn [cells_bytes cbytes cells_size csize app] in ZB0, ZW0. rewrite app_nil_r in ZB0. rewrite Nat.add_0_r in ZW0.
eapply (rrw_cells_of_zeros m3 cur 8192 4096); [exact ZB0| exact ZW0| split; [exact (zeros_length 4096)| exact I]| cbn [cells_bytes cbytes cells_size csize]; rewrite app_nil_r, Nat.add_0_r; reflexivity| lia| cbv; discriminate]. }
assert (ZP6 : rw_cells usegs m6 (cur + 4096) [CB 4096 (zeros 4096)]).
{ eapply rw_cells_transport; [| exact MU6| exact WM6| cbn [cells_size csize]; rewrite ?Nat.add_0_r; cbn; unfold RCTX; lia].
eapply RA2.rrw_cells_agree; [exact ZP3|].
cbn [cells_size csize]. rewrite ?Nat.add_0_r. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
destruct ZP6 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize app] in ZB, ZW. rewrite app_nil_r in ZB. rewrite Nat.add_0_r in ZW.
assert (ST6 : stk usegs m6 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
assert (ERR6 : rw_cells usegs m6 (errno_addr tp) [C4 (sysret_errno rr e1)]) by (eapply rw_cells_transport; [exact ERR5| exact MU6| exact WM6|]; cbn; rewrite rETP'; unfold RCTX; lia).
assert (FPX : forall y, rFP stI y -> rFP stX y).
{ intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq.
change (s_regions stX) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)).
rewrite lookup_insert_ne by (intros ->; rewrite FRr in Hq; discriminate). repeat split; auto; lia. }
assert (M16 : magree (rFP stX) m1 m6).
{ intros y Hy Hc.
assert (~ (RCTX + 40 <= y < RCTX + 48)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
assert (~ (RCTX + 920 <= y < RCTX + 928)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
assert (~ (lo <= y < bv_unsigned sp)) by (intros X; apply Hc; left; left; exact X).
assert (~ (errno_addr tp <= y < errno_addr tp + 4)) by (intros X; apply Hc; left; right; left; rewrite <- TPv; exact X).
assert (~ (cur <= y < cur + 8192)).
{ intros X. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| atop_facts; lia| exact X]. }
apply E16; assumption. }
replace (Z_to_bv 64 (cur + 4096)) with (Z_to_bv 64 (conc stX (rid, 4096))) by (change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
eapply (rcarve_K stX (rid, 4096) (mkRegion RKBrk cur 8192) m6 _ _ (sysret_errno rr e1));
first [exact RG1 | exact HIDI | exact MRX | exact MI6 | exact FR6 | exact ST6 | exact ERR6 | reflexivity | idtac].
all: try (cbn [snd fst r_len r_base r_kind]; unfold pgal, lr_lo; cbn [r_kind r_base]; change (round_up_pg 8192) with 8192; first [discriminate | lia]).
+ unfold stX. apply (rAMI_ctx st st1 _ AI1).
* cbn. repeat split; reflexivity.
* cbn. exact (ami_secretr _ _ AI1).
* left. reflexivity.
* right. right. exists rid, 8192, (mkRegion RKBrk cur 8192). split; [reflexivity|]. split; [exact RG1|]. cbn. discriminate.
+ change (s_areas stX) with (s_areas stI). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
exfalso. destruct (WA _ _ EA) as (rr0 & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
+ intros j Hj. change (s_metas stX) with (s_metas stI). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
exfalso. destruct (MKI _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr0 & Hrr & _).
assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
+ intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
+ cbn. lia.
+ change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZB.
+ change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZW.
+ eapply rauxv_ok_magree; [exact AUX1| exact M16| intros y X; exact (rFP_below stX y (proj1 MRX) X)].
+ eapply magree_trans; [exact AG1| exact M16| exact FPX| intros y X; exact X].
+ unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. reflexivity.
-
unfold brk_answer_ok. rewrite Z.eqb_refl.
replace (cur =? cur + 8192) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb negb].
eapply rimplT_evt.
{ eapply (ram_bu_fail _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m1 m2 stI cur);
first [exact MR1 | exact MU2 | exact WM2 | exact ACNT | exact MI2 | reflexivity | exact TC2 | lia]. }
intros ms6 (m3 & -> & MU3 & WM3 & MI3 & MRD).
assert (M23 : magree (rFP stI) m2 m3).
{ eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. atop_facts. lia. }
eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 (set_brk_ps cur s) junk e1); first [exact MRD | exact MI3 | exact HIDI | reflexivity | idtac].
+ apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
+ exact RGI.
+ exact ACNT.
+ change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
+ exact TLI.
+ exact MKI.
+ pose proof PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
+ eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
+ eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
+ eapply rauxv_ok_magree; [exact AUX1| | intros y X; exact (rFP_below stI y WF1 X)].
eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X].
+ eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1); [eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X] | |];
intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbody_spec : forall (stI : mstate) (x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (junk : list byte) (e1 : word),
RAMpre stI -> AMI st stI -> c_init_done (ctx stI) = 1 -> s_regions stI = s_regions st -> brk_link_ps stI s ->
rmrep stI m1 -> mem_inv usegs m1 ->
rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
rimplT o (am_body stI k bail) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15a60) fc None m1 (seg_rom usegs)).
Proof.
intros until e1. intros AMPI AI HIDI RGI BLI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof MR1 as (WF1 & _).
unfold am_body.
destruct (c_free_meta_head (ctx stI)) as [h|] eqn:FMH.
-
pose proof (amp_fmh stI AMPI h FMH) as [HN0 HM0].
pose proof (amp_links stI AMPI) as [CLn CLp CLno CLs].
pose proof (CLs h HN0) as MSh.
pose proof (amp_fml stI AMPI h HM0 HN0) as (CL0 & FMn & FMp).
destruct (m_next (get_meta_rec stI h)) as [nx|] eqn:HN; [| exfalso; apply HN0; reflexivity].
destruct (m_prev (get_meta_rec stI h)) as [pv|] eqn:HP.
2:{ exfalso. pose proof (proj2 (CLno h) HP) as X. rewrite HN in X. discriminate. }
destruct (CLn h nx HN) as [PVn MSn]. destruct (CLp h pv HP) as [NXp MSp].
assert (SELF : nx = h <-> pv = h).
{ split; intros ->; [rewrite HP in PVn| rewrite HN in NXp]; congruence. }
eapply rimplT_evt.
{ Local Ltac2 Set LiaHints.tbl := fun () => "00>0>16086156136.9016086156136.9518242491790.9522771665647.8923351237782.9526339957187.9538038706128.9038038706128.9950455870004.9551872794881.8661369617066.856722869515.1136722869515.12267850223294.9700000400900=00H00I00W00]00c00m01001601:01>01BS2CRS3ACRS2P0S3CNT2K12CRSS4ACNT3PHI3ACRS4LOLES4LOLES4ACNT3ACRS1HS2Hq1HS2HaS2HaS2Hj".
eapply (ram_deq sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI h nx pv);
first [exact MR1 | exact MI1 | exact FMH | exact MSh | exact HN | exact HP | exact MSn | exact MSp | exact SELF | exact FR1 | exact ST1 | exact LO | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
eapply rfinish_K.
+ eapply (ram_rel_deq st stI h nx pv AI); try assumption.
* rewrite <- FMH. symmetry. exact (proj1 (proj2 (ami_ctx _ _ AI))).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HN.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HP.
* eapply meta_slot_same_areas; [| exact MSh]. symmetry. exact (ami_areas _ _ AI).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact CL0.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMn nx eq_refl).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). intros X. apply (proj1 (CLno nx)) in X. rewrite PVn in X. discriminate.
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMp pv eq_refl).
* unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). rewrite NXp. discriminate.
+ exact MR2.
+ exact MI2.
+ exact ST2.
+ eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
+ eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
+ pose proof (sbl_regions _ _ (sbl_dequeue stI LFree h)) as RD.
eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [exact RD| exact X] | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a RD)); exact X].
+ unfold brk_link_ps in *. rewrite (sbl_brk _ _ (sbl_dequeue stI LFree h)). destruct (c_brk (ctx stI)) as [| |rid off]; auto.
unfold conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). exact BLI.
+ reflexivity.
+ reflexivity.
+ reflexivity.
+ unfold pw, oconc, wz, conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). reflexivity.
-
destruct (Z.eqb_spec (c_avail_meta_count (ctx stI)) 0) as [CNT|CNT]; cbn [negb].
+
eapply rimplT_evt.
{ eapply (ram_disp0 _ gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact FMH| exact CNT]. }
intros ms2 ->.
assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
assert (PTRI : ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI).
{ apply (ami_ptrs _ _ AI); [| eapply ptrs_in_mono; [| exact (proj1 (amp_ptrs st AMP))]; intros q Hq; cbn in Hq; pose proof (ami_next _ _ AI); lia]. intros rid r Hr _.
destruct (N.lt_ge_cases rid (s_next_rid stI)) as [L|G]; [exact L|]. destruct (ami_fresh _ _ AI rid G) as [X _]. rewrite X in Hr. discriminate. }
destruct (Z.eqb_spec (c_avail_meta_area_count (ctx stI)) 0) as [ACNT|ACNT]; cbn [andb].
*
destruct (c_brk (ctx stI)) as [| |brid boff] eqn:BRK; cbn [negb].
--
eapply (rbrk_untried_path stI m1 junk e1); first [exact AMPI | exact AI | exact HIDI | exact RGI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | reflexivity].
--
eapply rimplT_evt.
{ eapply (ram_disp_dead _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
intros ms3 ->.
eapply (rmmap_path stI m1 s junk e1); first [exact AI | exact HIDI | exact RGI | exact ACNT | exact TLI | exact MKI | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
pose proof (amp_shift stI AMPI). lia.
--
eapply (rbrk_live_path stI brid boff m1 junk e1); first [exact AMPI | exact AI | exact HIDI | exact RGI | exact BLI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1].
*
destruct (amp_avail_areas stI AMPI ACNT) as (p & r & AMA & Hr & NK & PAL & P0 & PLR & PHI & FRA).
pose proof (amp_acount stI AMPI) as ACR.
unfold am_after_brk. rewrite (proj2 (Z.eqb_neq _ _) ACNT).
eapply rimplT_evt.
{ eapply (ram_disp_fin _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI p r);
first [exact MR1 | exact ACNT | exact AMA | exact Hr | unfold pgal, PGSZ in *; exact PAL | lia | idtac]. unfold PGSZ in *. lia. }
intros ms3 ->.
eapply (rfinish_path stI p r m1 s junk e1); first [exact AI | exact HIDI | exact AMA | exact Hr | exact NK | exact P0 | exact PLR | exact TLI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
-- unfold PGSZ in PHI. lia.
-- unfold pgal. unfold PGSZ in PAL. exact PAL.
-- apply (proj1 (FRA p eq_refl ltac:(lia))).
-- intros j Hj. apply (proj2 (FRA (aadd p (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
-- lia.
+
destruct (amp_avail stI AMPI CNT) as (aa & ar & kk & Haa & AVM & K0 & K1 & MQ).
pose proof (amp_count stI AMPI) as CR.
assert (MSq : meta_slot stI (aadd aa (AREA_HDR + META_SIZE * kk))) by (exists aa, ar, kk; repeat split; auto; unfold NSLOTS in *; lia).
rewrite (am_take_eq stI k bail _ AVM).
eapply rimplT_evt.
{ eapply (ram_take_walk sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI _);
first [exact MR1 | exact MI1 | exact FMH | exact CNT | exact AVM | exact MSq | exact FR1 | exact ST1 | exact LO | unfold NSLOTS in CR; lia | lia]. }
intros ms2 RP. unfold ram_ret_post in RP.
destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
eapply rfinish_K.
* eapply (ram_rel_take st stI _ AI).
-- rewrite <- AVM. symmetry. exact (proj1 (proj2 (proj2 (ami_ctx _ _ AI)))).
-- rewrite <- (ami_metas _ _ AI). exact MQ.
-- eapply meta_slot_same_areas; [| exact MSq]. symmetry. exact (ami_areas _ _ AI).
* exact MR2.
* exact MI2.
* exact ST2.
* eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
* eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
* eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [| exact X]; reflexivity | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a ltac:(reflexivity))); exact X].
* unfold brk_link_ps in *. unfold ctx in BLI. cbn. destruct (c_brk (s_ctx stI)) as [| |rid off]; auto.
* reflexivity.
* reflexivity.
* reflexivity.
* unfold pw, oconc, wz. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH"] Lemma ralloc_meta_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs)).
Proof.
intros. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
pose proof LO as LO'. atop_facts. pose proof rETP as rETP'. pose proof TP as TPv.
pose proof MR as (WF0 & _).
rewrite alloc_meta_eq. unfold ralloc_meta_entry.
eapply rimplT_evt.
{ Local Ltac2 Set LiaHints.tbl := fun () => "0040>16671995537.9025069424428.8937310060433.9038043196530.6200000400D00M00SS2HyS4LOLE3LO'5ATOPRS4LOLE2HyS4LOLE".
eapply (ram_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st);
first [exact MR | exact MI | exact AUX | exact ST | exact LO | exact (amp_init st AMP) | exact (amp_s_secret st AMP) | exact (amp_secret st AMP) | lia]. }
intros ms1 (x1 & u0 & u1 & u2 & s1x & s4x & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u9' & u10 & u11 & u12 & u13 & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & MR1).
assert (M01 : magree (rFP (am_init_st st)) m m1).
{ eapply magree_of_munch; [exact MU1|]. cbn. split; [| split; [| exact I]]; intros y Hy.
- left. left. lia.
- left. right. right. left. unfold RCTX in *. atop_facts. lia. }
eapply (rbody_spec (am_init_st st) x1 u0 u1 u2 s1x s4x u3 u4 u5 u6 u7 u8 u9 u9' u10 u11 u12 u13 m1 junk errv).
- exact (rAMpre_init st AMP).
- exact (rAMI_init st AMP).
- exact (ram_init_done st AMP).
- exact (ram_init_regions st).
- unfold brk_link_ps in *. rewrite ram_init_brk. destruct (c_brk (ctx st)) as [| |rid off]; auto. rewrite ram_init_conc. exact BL.
- exact MR1.
- exact MI1.
- exact FR1.
- exact ST1.
- eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite rETP'. cbn. unfold RCTX. lia.
- eapply rauxv_ok_magree; [exact AUX| exact M01| intros a X; exact (rFP_below (am_init_st st) a (proj1 MR1) X)].
- exact M01.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ASM.
#[using="Type"] Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof.
unfold ralloc_meta_stmt. intros.
eapply ralloc_meta_main; eassumption.
Qed.
End CANSEC1.

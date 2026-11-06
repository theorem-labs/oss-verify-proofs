(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk Zp8.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpt Zps Zpo Zwn Zsl Z4a Z73 Z5g Z6m Z71 Z5h Z5i Z5j
  Z6q Z6y Z6p Z45 Z5k Z4e Z4l Z4m Z4n Z4o Z52 Z57 Z5b Z4q
  Z59.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma junk4 : forall (m : mem) (sp' : Z) (jq je jo jn : list byte),
  rw_cells bsegs m (sp' + 56) [CB 24 jq] -> rw_cells bsegs m (sp' + 80) [CB 16 je] -> rw_cells bsegs m (sp' + 96) [CB 24 jo] -> rw_cells bsegs m (sp' + 120) [CB 16 jn] ->
  rw_cells bsegs m (sp' + 56) [CB 24 jq; CB 16 je; CB 24 jo; CB 16 jn].
Proof.
  intros m sp' jq je jo jn H1 H2 H3 H4.
  change [CB 24 jq; CB 16 je; CB 24 jo; CB 16 jn] with ([CB 24 jq] ++ [CB 16 je] ++ [CB 24 jo] ++ [CB 16 jn]).
  apply Zvw.rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. replace (sp' + 56 + Z.of_nat 24) with (sp' + 80) by lia.
  apply Zvw.rw_cells_app. split; [exact H2|]. cbn [cells_size csize Nat.add]. replace (sp' + 80 + Z.of_nat 16) with (sp' + 96) by lia.
  apply Zvw.rw_cells_app. split; [exact H3|]. cbn [cells_size csize Nat.add]. replace (sp' + 96 + Z.of_nat 24) with (sp' + 120) by lia.
  exact H4.
Qed.

Section Top3b.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Hypothesis RC0 : rt_contracts RT.
Hypothesis PDT : pdtor_cps RT (pdone RT).
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis HELEM : forall E, aenvA_ok E -> atp_elem_cpsA RT E TAPE_MAX_DEPTH.

Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, ATPA_DESTROY_STACK, PID_STACK, GSTR_STACK_A in *;
                 unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem lftoi_par3 : forall (Σ Σg : rts RT) PMc (m mg : mem) (usp sp' f A lo d : Z) (bs : list byte)
    (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s6x s7x s8x t3 t4 t5 t6 : word) F fc (h3 t j20 : list byte)
    (impl idx oc ia tape sbuf : Z) (r : word),
  fdfs_only PMc -> mat_stable PMc ->
  0 < d -> Z.of_nat (length bs) < 2^26 ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ -> 8 + vcost_pushes (atp_P (chars bs)) 0 0 <= 2^31 + 2^26 ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  lp_inv RT LIB Σ Σg m mg usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  rw_cells bsegs mg (sp' + 136) (res_cellsA (f + 120) r j20) -> bv_unsigned r < 64 ->
  s2a_okres tape sbuf (roundup64 (doc_cap bs + 3)) (al_sbuf (doc_cap bs)) r mg ->
  pdone RT Σg mg (f + 96) (vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ) ->
  pidA_st RT Σg mg (f + 96) impl idx oc ia tape sbuf (doc_cap bs) ->
  usp - 304 <= sp' <= usp - 288 -> sp' mod 32 = 0 -> 0 < f -> f mod 64 = 0 -> f + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN ->
  rt_live RT Σg = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx (doc_cap bs)) :: (impl, 96) :: (tape, al_tape (doc_cap bs)) :: (sbuf, al_sbuf (doc_cap bs))
                    :: vblockA A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) ++ rt_live RT Σ ->
  (impl mod 16 = 0 /\ idx mod 16 = 0 /\ oc mod 16 = 0 /\ ia mod 16 = 0 /\ tape mod 16 = 0 /\ sbuf mod 16 = 0) ->
  rt_credit RT Σ - 2 - vcost_pushes (atp_P (chars bs)) 0 0 - mcost (doc_len bs + 64) - pid_costA (doc_len bs) <= rt_credit RT Σg ->
  frm0 fc ->
  cps_f (ASTA RT Σg PMc (eq (sa_regs 0x96dcc x1 sp' gp (Z_to_bv 64 0x653c30) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2x s6x s7x s8x t3 t4 t5 t6 F fc mg)))
    (fin_postA RT LIB Σ PMc usp lo ra gp (Z_to_bv 64 0x653c30) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using LIB_loc AF RC0 PDT VDES HELEM.
  intros Σ Σg PMc m mg usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s6x s7x s8x t3 t4 t5 t6 F fc h3 t j20
    impl idx oc ia tape sbuf r FDO MST D0 BSL INLV FRS0 LVPOS LVB CR0 VCB LOW LOR SPT SPA INV RC R64 OKR PD PST SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT LVg MODS CRg FRM.
  intros T c (Hc & FC0) Hk.
  pose proof INV as (ARTg & MIg & STg & (j0 & j1 & j2 & j4 & jq & je & jo & jn & jr & j13 & FRlg) & STpg & FRsg & FHg & FSg & VRg & BSg & LIBg & PRESg & FRSg & SPg).
  pose proof (af_sp0_range RT AF Σg mg ARTg) as SP0R. rewrite SPg in SP0R. pose proof (af_sp0_win RT AF Σg mg ARTg) as SP0W. rewrite SPg in SP0W.
  set (n := Z.of_nat (length bs)) in *. set (P := atp_P (chars bs)) in *. set (S := f / 8 + 2147450880) in *. set (capv := vcap_iter P 0 0) in *.
  set (cap := doc_cap bs) in *.
  assert (CAPR : 32 <= cap <= 1048512) by (subst cap; unfold doc_cap, doc_len; pose proof (atp_doc_len (chars bs)) as [_ DL]; unfold SJ_PADMAX in DL; pose proof (zlength_nonneg (atp_doc (chars bs))); lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (EUSP : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).
  assert (P2 : (2 <= P)%nat) by (subst P; unfold atp_P; lia).
  pose proof (vcap_iter_inv P 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI. fold capv in CAPI.
  assert (DLR : 0 <= doc_len bs <= 1048512) by (unfold doc_len; pose proof (atp_doc_len (chars bs)) as [_ DL]; unfold SJ_PADMAX in DL; pose proof (zlength_nonneg (atp_doc (chars bs))); lia).
  pose proof (pid_costA_nonneg (doc_len bs) ltac:(lia)) as PC0. pose proof (pid_costA_bound (doc_len bs) DLR) as PCB.
  pose proof (mcost_nonneg (doc_len bs + 64) ltac:(lia)) as MC0. pose proof (mcost_le (doc_len bs + 64) ltac:(lia)) as MCB.
  assert (VC0 : 0 <= vcost_pushes P 0 0) by (apply vcost_pushes_nonneg; lia).
  assert (CRT : rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σg) by (clear - CRg CR0 VCB PC0 MC0 VC0 PCB MCB DLR; subst P; unfold FUZZ_COST, DCOST in *; lia).
  destruct (Z.eq_dec (bv_unsigned r) 0) as [R0|RNZ].
  2: {
    pose proof (fa_walk11 usp sp' f x1 gp (Z_to_bv 64 0x653c30) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s6x s7x s8x t3 t4 t5 t6 r j20 F fc mg
                  FPOS ltac:(ul) ltac:(ul) ltac:(ul) ltac:(pose proof (bv_unsigned_in_range 64 r) as XR; clear - XR RNZ R64; lia) RC MIg) as W11.
    unfold sa_regs in W11. fold S in W11.
    lazymatch type of W11 with evt bsegs _ ?X =>
      assert (W11' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W11) end.
    clear W11.
    apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σg PMc _ _ MST W11') ltac:(unfold sa_regs in Hc; subst S; exact Hc)). clear W11'. intros c6 Hc6.
    destruct (ASTA_unpack RT Σg _ _ c6 Hc6) as (ms6 & <- & Hc6'). clear Hc6.
    exact (lftoi_tail RT LIB LIB_loc AF PDT VDES Σ Σg PMc m mg usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7
             s2x s6x s7x s8x t3 t4 t5 t6 F fc h3 t
             FDO MST INLV FRS0 LVPOS LOW LOR SPT SPA INV PD CRT SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM T c6
             (conj ltac:(unfold sa_regs; subst S; exact Hc6') (cfrm0_of_asta RT Σg PMc (eq _) c6 Hc6' ltac:(intros ms0 <-; exact FRM))) Hk). }

  assert (ER : r = Z_to_bv 64 0) by (apply bv_eq; rewrite R0; reflexivity). subst r.
  unfold res_cellsA in RC. rewrite bv_eqb_refl in RC.
  destruct OKR as [K|(_ & tws & sbs & TAPEB & SBUFB & WF & SBSR & LT & LS)]; [rewrite unsigned_lit in K by lia; lia|].
  pose proof (tape_wf_root _ _ _ _ _ WF) as [EL NR]. pose proof WF as (_ & SNR & TW0 & TWN & _).
  set (tn := Z.of_nat (length tws)) in *. set (sn := Z.of_nat (length sbs)) in *.

  pose proof VRg as (EELS0 & SZR & CAPB & A0 & AH & SVg & BLKg).
  destruct BLKg as [(C0 & _)|(CP1 & A16 & APOS & ELg)]; [exfalso; lia|].
  destruct (atp_elsA_shape d (chars bs)) as (P0 & [P1 L1] & rest & EELS & P0Z & ES0).
  destruct (atp_ptr_bytes d bs _ P1 L1 rest mg EELS BSg) as (bsp & EPTR & EL1 & PTRC).
  rewrite EELS in ELg. cbn [velts fst snd] in ELg.
  assert (INCLg : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σg)) by (intros e He; rewrite LVg; do 6 right; apply in_or_app; right; exact He).
  assert (INAg : In (A, 16 * Z.of_nat P) (rt_live RT Σg)).
  { rewrite LVg. do 6 right. apply in_or_app. left. unfold vblockA. destruct (Z.eqb_spec capv 0); [lia|]. apply ann_block_vis. }
  assert (INTg : In (tape, al_tape cap) (rt_live RT Σg)) by (rewrite LVg; do 4 right; left; reflexivity).
  assert (INSg : In (sbuf, al_sbuf cap) (rt_live RT Σg)) by (rewrite LVg; do 5 right; left; reflexivity).
  pose proof (af_live_range RT AF Σg mg A _ ARTg INAg) as (AR0 & AR1 & AR2). rewrite SPg in AR1.
  pose proof (af_live_range RT AF Σg mg tape _ ARTg INTg) as (TR0 & TR1 & TR2). rewrite SPg in TR1.
  pose proof (af_live_range RT AF Σg mg sbuf _ ARTg INSg) as (SR0 & SR1 & SR2). rewrite SPg in SR1.
  pose proof (al_tape_bounds cap ltac:(lia)) as TPB. pose proof (al_sbuf_bounds cap ltac:(lia)) as SBB.
  assert (SHZA : shz mg A 32).
  { pose proof (shz_live RT AF Σg mg A _ ARTg INAg ltac:(clear - A16; Z.div_mod_to_equations; lia)) as X.
    eapply shz_sub; [exact X| lia|]. clear - P2. Z.div_mod_to_equations. nia. }
  pose proof PST as (FOBJP & (q1 & q17 & q57 & PCg) & _).
  assert (DOCC : rw_cells bsegs mg (f + 120) [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 q57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { unfold pid_cells in PCg.
    lazymatch type of PCg with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ rest) in PCg end.
    apply Zvw.rw_cells_app in PCg. destruct PCg as [_ X]. cbn [cells_size csize Nat.add] in X. replace (f + 96 + Z.of_nat 24) with (f + 120) in X by lia. exact X. }

  pose proof FRlg as LOC. unfold fa_locals2 in LOC.
  lazymatch type of LOC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ [c6] ++ [c7] ++ [c8] ++ [c9] ++ (c10 :: rest)) in LOC end.
  apply Zvw.rw_cells_app in LOC. destruct LOC as [_ LOC]. apply Zvw.rw_cells_app in LOC. destruct LOC as [JQg LOC].
  apply Zvw.rw_cells_app in LOC. destruct LOC as [JEg LOC]. apply Zvw.rw_cells_app in LOC. destruct LOC as [JOg LOC].
  apply Zvw.rw_cells_app in LOC. destruct LOC as [JNg _].
  cbn [cells_size csize Nat.add] in JQg, JEg, JOg, JNg.
  replace (sp' + Z.of_nat 56) with (sp' + 56) in JQg by lia.
  replace (sp' + Z.of_nat 56 + Z.of_nat 24) with (sp' + 80) in JEg by lia.
  replace (sp' + Z.of_nat 56 + Z.of_nat 24 + Z.of_nat 16) with (sp' + 96) in JOg by lia.
  replace (sp' + Z.of_nat 56 + Z.of_nat 24 + Z.of_nat 16 + Z.of_nat 24) with (sp' + 120) in JNg by lia.

  assert (P0R : 0 <= P0 < 2^64).
  { destruct P0Z as [(-> & _)| ->]; [lia|]. destruct INLV as [(p & k & Hin & Q1 & Q2)|(_ & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σg mg p k ARTg (INCLg _ Hin)) as (_ & R1 & _). rewrite SPg in R1. clear - D0 Q1 Q2 R1 SP0R. ul. }
  assert (L0R : 0 <= zlength (atp_s0 (chars bs)) < 2^64).
  { pose proof (zlength_nonneg (atp_s0 (chars bs))). pose proof (atp_s0_len (chars bs)) as X. rewrite chars_length in X. subst n. lia. }
  assert (P1R : 0 <= P1 /\ P1 + Z.of_nat (length bsp) < 2^47).
  { destruct PTRC as [(-> & ->)|(Q1 & Q2 & _)]; [cbn; lia|]. destruct INLV as [(p & k & Hin & Q3 & Q4)|(E0 & DL)].
    - pose proof (af_live_range RT AF Σg mg p k ARTg (INCLg _ Hin)) as (_ & R1 & _). rewrite SPg in R1. clear - D0 Q1 Q2 Q3 Q4 R1 SP0R. subst n. ul.
    - subst bs n. cbn [length] in Q2. clear - D0 DL Q1 Q2. ul. }
  assert (L1R : 0 <= L1 < 2^64) by (rewrite EL1; clear - P1R; ul).
  assert (INFg : In (f, 2%nat) (rt_frames RT Σg)) by (rewrite FRSg; left; reflexivity).
  pose proof (af_frames_align RT AF Σg mg f 2%nat ARTg INFg) as [_ FSEGg].

  assert (PBX : exists PB NPB, bsp = [] \/ (In (PB, NPB) (rt_live RT Σ) /\ PB <= P1 /\ P1 + Z.of_nat (length bsp) <= PB + NPB)).
  { destruct PTRC as [(_ & ->)|(Q1 & Q2 & _)]; [exists 0, 0; left; reflexivity|].
    destruct INLV as [(p & k & Hin & Q3 & Q4)|(E0 & _)].
    - exists p, k. right. split; [exact Hin| subst n; lia].
    - exists 0, 0. left. subst bs n. cbn [length] in Q2. destruct bsp; [reflexivity| cbn [length] in Q2; lia]. }
  destruct PBX as (PB & NPB & PBF).
  assert (LBSP : Z.of_nat (length bsp) <= n) by (destruct PTRC as [(_ & ->)|(Q1 & Q2 & _)]; [cbn; lia| lia]).
  assert (ECL : zlength (chars bsp) = Z.of_nat (length bsp)) by apply chars_length.
  set (E := mkAEA lo usp (f + 120) f 2%nat tape (al_tape cap) sbuf (al_sbuf cap) tws sbs P1 (chars bsp) PB NPB).
  assert (OKE : aenvA_ok E).
  { apply mkAEAok; subst E; cbn [ae_lo ae_hi ae_DOC ae_fD ae_kD ae_TAPE ae_NT ae_SBUF ae_NS ae_tws ae_sbs ae_PTR ae_p1 ae_PB ae_NPB].
    - exact WF.
    - exact SBSR.
    - apply chars_range.
    - rewrite ECL. lia.
    - split; [clear - MODS; lia|]. split; [unfold al_tape; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity|].
      split; [unfold al_tape; subst tn cap; clear - LT; lia|]. split; [exact TR0| clear - TR1 LOW; lia].
    - split; [clear - MODS; lia|]. split; [unfold al_sbuf, roundup64; clear; Z.div_mod_to_equations; lia|].
      split; [subst sn cap; clear - LS; lia|]. split; [exact SR0| clear - SR1 LOW; lia].
    - intros NE. destruct PBF as [E0|(INPB & Q1 & Q2)]; [exfalso; apply NE; rewrite E0; reflexivity|].
      pose proof (af_live_range RT AF Σg mg PB NPB ARTg (INCLg _ INPB)) as (RB0 & RB1 & _). rewrite SPg in RB1.
      split; [exact RB0|]. rewrite ECL. clear - Q1 Q2 RB1 LOW. lia.
    - lia.
    - change (fs_size 2) with 256. split; [clear - F64; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [exact FSEGg| clear - FR1' LOW; lia].
    - clear - SP0W LOW. unfold STACK_WIN in *. lia.
    - clear - LOR SPT. ul. }
  assert (LVE : a_live RT Σg E).
  { unfold a_live; subst E; cbn [ae_lo ae_fD ae_kD ae_TAPE ae_NT ae_SBUF ae_NS ae_p1 ae_PB ae_NPB].
    split; [exact INTg|]. split; [exact INSg|]. split; [destruct PBF as [->|(INPB & _)]; [left; reflexivity| right; exact (INCLg _ INPB)]|].
    split; [exact INFg| rewrite SPg; exact LOW]. }
  assert (PAT : ptr_atA E P1 (chars bsp)) by (exists []; subst E; cbn [ae_p1 ae_PTR app]; split; [reflexivity| unfold zlength; cbn [length]; lia]).

  assert (CLIg : forall x, lp_dom RT Σ usp sp' f A d bs x -> aclient (rt_live RT Σg) (rt_frames RT Σg) sp' x)
    by (exact (lp_client RT AF Σ Σg mg usp sp' f lo d A bs ARTg FRSg FRS0 INCLg INAg INLV FPOS F64 ltac:(lia) SPT)).
  pose proof (af_frames_range RT AF Σg mg f 2%nat ARTg INFg) as (_ & FR1g & _ & FLVg). change (fs_size 2) with 256 in FR1g, FLVg. rewrite SPg in FR1g.
  pose proof (fframe_ranges RT AF Σg mg f 2 ARTg INFg) as (_ & _ & _ & _ & SHTg). change (fs_size 2) with 256 in SHTg.
  assert (SHF : shad (f + 256) = S + 32) by (subst S; unfold shad, SHB; Z.div_mod_to_equations; lia). rewrite SHF, SPg in SHTg.

  assert (TAILK : forall (Σy : rts RT) (my : mem) (u0 u1 u2 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 : word) (Fy : bvmap 5 word) (fcy : bv 32) (jq' je' jo' jn' : list byte) (cy : config),
    rt_live RT Σy = rt_live RT Σg -> rt_frames RT Σy = rt_frames RT Σg -> rt_sp0 RT Σy = rt_sp0 RT Σg ->
    rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σy ->
    ART RT Σy my -> mem_inv bsegs my -> stk bsegs my lo sp' ->
    (forall a : word, aclient (rt_live RT Σg) (rt_frames RT Σg) sp' (bv_unsigned a) -> ~ (sp' + 56 <= bv_unsigned a < sp' + 136) -> my a = mg a) ->
    rw_cells bsegs my (sp' + 56) [CB 24 jq'; CB 16 je'; CB 24 jo'; CB 16 jn'] ->
    frm0 fcy ->
    ASTA RT Σy PMc (eq (sa_regs e_pdtor (Z_to_bv 64 0x96e80) sp' gp (Z_to_bv 64 0x653c30) u0 u1 u2 usp (Z_to_bv 64 (f + 96)) (Z_to_bv 64 64) v2 v3 v4 v5 v6 v7
                                 f s2x s6x s7x s8x u3 u4 u5 u6 Fy fcy my)) cy ->
    realizes bsegs cy T).
  { intros Σy my u0 u1 u2 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 Fy fcy jq' je' jo' jn' cy LVy FRSy SPy CRy ARTy MIy STy EQA RJ FRMy Hcy.
    assert (EQy : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> ~ (sp' + 56 <= bv_unsigned a < sp' + 136) -> my a = mg a)
      by (intros a Ha Hn; exact (EQA a (CLIg _ Ha) Hn)).
    pose proof (lp_inv_xfer_junk RT LIB LIB_loc AF Σ Σg Σy m mg my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A jq' je' jo' jn'
                  INV FRS0 INCLg INAg INLV LOW LOR SPR FRSy SPy ARTy MIy STy EQy RJ) as INVy.
    assert (PDy : pdone RT Σy my (f + 96) (vblockA A capv (Z.of_nat P) ++ rt_live RT Σ)).
    { apply (pdone_xfer RT AF Σg Σy mg my (f + 96) _ PD ARTg FRSy LVy). intros a Ha.
      assert (LOWa : bv_unsigned a < lo).
      { destruct Ha as [(f9 & k9 & Hin & Hr)|[(f9 & k9 & Hin & Hr)|(p & k & Hin & Hr)]].
        - rewrite FRSg in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. change (fs_size 2) with 256 in Hr. clear - Hr FR1g LOW. lia.
        - rewrite FRSg in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. change (fs_size 2) with 256 in Hr. unfold shad, SHB in Hr. clear - Hr SHTg LOW. subst S. lia.
        - pose proof (af_live_range RT AF Σg mg p k ARTg Hin) as (_ & R1 & _). rewrite SPg in R1. clear - Hr R1 LOW. lia. }
      apply EQA; [| clear - LOWa LOR SPR; ul].
      destruct Ha as [H|[H|H]]; [right; right; right; left; exact H| right; right; right; right; exact H| right; right; left; exact H]. }
    exact (lftoi_tail RT LIB LIB_loc AF PDT VDES Σ Σy PMc m my usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u0 u1 u2 (Z_to_bv 64 64) v2 v3 v4 v5 v6 v7
             s2x s6x s7x s8x u3 u4 u5 u6 Fy fcy h3 t
             FDO MST INLV FRS0 LVPOS LOW LOR SPT SPA INVy PDy CRy SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRMy T cy
             (conj Hcy (cfrm0_of_asta RT Σy PMc (eq _) cy Hcy ltac:(intros ms0 <-; exact FRMy))) Hk). }

  pose proof (fa_walkR1 usp sp' f x1 gp (Z_to_bv 64 0x653c30) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s6x s7x s8x t3 t4 t5 t6 j20 F fc mg
                FPOS ltac:(ul) ltac:(clear - SP0R LOW LOR SPR; ul) ltac:(clear - SPT SPR; ul) RC MIg) as WR1.
  unfold sa_regs in WR1. fold S in WR1.
  lazymatch type of WR1 with evt bsegs _ ?X =>
    assert (WR1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact WR1) end.
  clear WR1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σg PMc _ _ MST WR1') ltac:(unfold sa_regs in Hc; subst S; exact Hc)). clear WR1'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σg _ _ c6 Hc6) as (ms6 & <- & Hc6'). clear Hc6.

  set (nbs := le8 (Z_to_bv 64 (f + 120)) ++ le8 (Z_to_bv 64 1)).
  assert (LNB : length nbs = 16%nat) by (subst nbs; rewrite length_app, !length_le8; reflexivity).
  assert (NBS : bytes_at bsegs mg (sp' + 136) nbs).
  { pose proof RC as X. lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in X end.
    apply Zvw.rw_cells_app in X. destruct X as [X _].
    pose proof (rw_cells_bytes_at bsegs mg _ _ X) as Y. cbn [cells_bytes cbytes] in Y. rewrite app_nil_r in Y. exact Y. }
  assert (CSRC1 : checked_src RT Σg mg (Z_to_bv 64 sp') lo (sp' + 136) (Z.of_nat (length nbs))).
  { rewrite LNB. apply (checked_src_stack RT AF Σg mg _ lo (sp' + 136) 16 ARTg); [rewrite SPg; clear - LOW LOR SPR; ul| clear - SPT SPR; ul| rewrite EU1; lia]. }
  assert (CDST1 : checked_dst RT Σg mg (Z_to_bv 64 sp') (sp' + 120) (Z.of_nat (length nbs))).
  { rewrite LNB. apply (checked_dst_stack RT AF Σg mg _ (sp' + 120) 16 ARTg); [rewrite SPg; clear - LOW LOR SPR; ul| clear - SPT SPR; ul| rewrite EU1; lia| exact (proj2 JNg)]. }
  assert (COKg : call_ok RT Σg mg (Z_to_bv 64 sp') lo).
  { unfold call_ok. rewrite EU1, SPg. split; [exact STg|]. split; [exact LOW|]. split; [clear - LOR SPR; ul|]. split; [clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia]. }
  apply (rc_asan_memcpy RT RC0 Σg PMc (Z_to_bv 64 0x96dec) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
           (Z_to_bv 64 (sp' + 120)) (Z_to_bv 64 (sp' + 136)) (Z_to_bv 64 16) a3 a4 a5 a6 a7 s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120))
           s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc mg (sp' + 120) (sp' + 136) nbs lo
           FDO MST eq_refl eq_refl ltac:(rewrite LNB; reflexivity) ltac:(clear - SPT SPR LOR LOW SP0R; ul) ltac:(clear - SPT SPR LOR LOW SP0R; ul) ltac:(rewrite LNB; cbn; lia)
           NBS CSRC1 CDST1 ltac:(rewrite LNB; cbn; lia) ARTg MIg COKg T c6 ltac:(subst S; exact Hc6')).
  intros c7 Hc7. unfold icpt_postF in Hc7.
  destruct (ASTA_unpack RT Σg _ _ c7 Hc7) as (ms7 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & BY1) & Hc7'). clear Hc7.
  destruct RS1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & ->).
  rewrite EU1 in ST1, PRES1. rewrite LNB in PRES1. change (Z.of_nat 16%nat) with 16 in PRES1.
  rewrite (ret_pc_even 0x96dec) in Hc7' by lia.

  assert (AGC : forall (Q : Z -> Prop), (forall x, Q x -> aclient (rt_live RT Σg) (rt_frames RT Σg) sp' x /\ ~ (sp' + 120 <= x < sp' + 136)) -> agree_on Q mg m1).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as [H1 H2]. apply PRES1; [exact H1| clear - H2; lia]. }
  assert (AGL : forall (Q : Z -> Prop), (forall x, Q x -> lp_dom RT Σ usp sp' f A d bs x /\ ~ (sp' + 120 <= x < sp' + 136)) -> agree_on Q mg m1).
  { intros Q HQ. apply AGC. intros x Hx. destruct (HQ _ Hx) as [H1 H2]. split; [exact (CLIg _ H1)| exact H2]. }
  assert (EQ1 : forall a : word, aclient (rt_live RT Σg) (rt_frames RT Σg) sp' (bv_unsigned a) -> ~ (sp' + 120 <= bv_unsigned a < sp' + 136) -> m1 a = mg a).
  { intros a Ha Hn. apply PRES1; [exact Ha| clear - Hn; lia]. }
  assert (WRN : wr_at bsegs m1 (sp' + 120) (Z.of_nat (length nbs))) by (rewrite LNB; exact (wr_at_transport bsegs mg m1 (sp' + 120) _ (proj2 JNg) WM1)).
  pose proof (rw_cells_CB_intro m1 (sp' + 120) nbs BY1 WRN) as NODE1. rewrite LNB in NODE1. subst nbs. apply rec_node16 in NODE1.
  assert (SV1 : rw_cells bsegs m1 (f + 32) [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * Z.of_nat P)); C8 (Z_to_bv 64 (A + 16 * capv))]).
  { apply (rw_cells_agree_nw bsegs mg m1 _ _ SVg). apply AGL. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; right; left; lia| clear - Hx FR1g LOW LOR SPR; ul]. }
  assert (EL1' : rw_cells bsegs mg A (velts (atp_elsA d (chars bs)))) by (rewrite EELS; cbn [velts fst snd]; exact ELg).
  assert (ELm1 : rw_cells bsegs m1 A (velts (atp_elsA d (chars bs)))).
  { apply (rw_cells_agree_nw bsegs mg m1 _ _ EL1'). apply AGL. intros x Hx. rewrite velts_size, atp_elsA_length in Hx. fold P in Hx.
    split; [left; do 3 right; left; lia| clear - Hx AR1 LOW LOR SPR; ul]. }
  rewrite EELS in ELm1. cbn [velts fst snd] in ELm1. clear EL1'.
  assert (SHZA1 : shz m1 A 32).
  { pose proof (shz_live RT AF Σg m1 A _ ART1 INAg ltac:(clear - A16; Z.div_mod_to_equations; lia)) as X.
    eapply shz_sub; [exact X| lia|]. clear - P2. Z.div_mod_to_equations. nia. }
  assert (JQ1 : rw_cells bsegs m1 (sp' + 56) [CB 24 jq]).
  { apply (rw_cells_agree_nw bsegs mg m1 _ _ JQg). apply AGL. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; left; clear - Hx SPR; lia| lia]. }
  assert (JE1 : rw_cells bsegs m1 (sp' + 80) [CB 16 je]).
  { apply (rw_cells_agree_nw bsegs mg m1 _ _ JEg). apply AGL. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; left; clear - Hx SPR; lia| lia]. }
  assert (OUT1 : rw_cells bsegs m1 (sp' + 96) [CB 24 jo]).
  { apply (rw_cells_agree_nw bsegs mg m1 _ _ JOg). apply AGL. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; left; clear - Hx SPR; lia| lia]. }
  assert (AI1 : AINV_A E m1).
  { unfold AINV_A; subst E; cbn [ae_DOC ae_TAPE ae_SBUF ae_tws ae_sbs ae_PTR ae_p1].
    split. { apply (bytes_at_agree bsegs mg m1 _ _ TAPEB). apply AGC. intros x Hx. cbv beta in Hx. rewrite u64s_length, length_map in Hx.
             split; [right; right; left; exists tape, (al_tape cap); split; [exact INTg| clear - Hx LT TPB; subst tn cap; unfold al_tape in *; lia]
                   | clear - Hx TR1 TPB LT LOW LOR SPR; subst tn cap; unfold al_tape in *; ul]. }
    split. { apply (bytes_at_agree bsegs mg m1 _ _ SBUFB). apply AGC. intros x Hx. cbv beta in Hx. rewrite length_map in Hx.
             split; [right; right; left; exists sbuf, (al_sbuf cap); split; [exact INSg| clear - Hx LS SBB; subst sn cap; lia]
                   | clear - Hx SR1 LS LOW LOR SPR; subst sn cap; ul]. }
    split. { change (map (Z_to_bv 8) (chars bsp)) with (to_bytes (chars bsp)). rewrite to_bytes_chars.
             destruct PTRC as [(-> & ->)|(Q1 & Q2 & BSP)]; [apply bytes_at_nil; lia|].
             apply (bytes_at_agree bsegs mg m1 _ _ BSP). apply AGL. intros x Hx. cbv beta in Hx.
             destruct INLV as [(p & k & Hin & Q3 & Q4)|(E0 & _)]; [| subst bs n; cbn [length] in Q2; lia].
             pose proof (af_live_range RT AF Σg mg p k ARTg (INCLg _ Hin)) as (_ & R1 & _). rewrite SPg in R1.
             split; [left; do 4 right; left; clear - Hx Q1 Q2; lia| clear - Hx Q1 Q2 Q3 Q4 R1 LOW LOR SPR; subst n; ul]. }
    split. { lazymatch type of DOCC with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in DOCC end.
             apply Zvw.rw_cells_app in DOCC. destruct DOCC as [DC _].
             apply (rw_cells_agree_nw bsegs mg m1 _ _ DC). apply AGC. intros x Hx. cbn [cells_size csize Nat.add] in Hx.
             split; [right; right; right; left; exists f, 2%nat; change (fs_size 2) with 256; split; [exact INFg| lia]| clear - Hx FR1g LOW LOR SPR; ul]. }
    replace (shad (f + 120)) with (S + Z.of_nat 15) by (subst S; unfold shad, SHB; Z.div_mod_to_equations; lia).
    pose proof FSg as X. unfold fa_shadow2 in X. cbn [map app repeat] in X.
    lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?d0 :: ?d1 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: c14 :: d0 :: d1 :: rest)
        with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] ++ [d0; d1] ++ rest) in X end.
    apply Zvw.rw_cells_app in X. destruct X as [_ X]. apply Zvw.rw_cells_app in X. destruct X as [X _].
    cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB.
    apply (bytes_at_agree bsegs mg m1 _ _ HB). apply AGL. intros x Hx. cbv beta in Hx. cbn [length] in Hx.
    split; [left; right; right; left; subst S; lia| clear - Hx SHTg LOW LOR SPR; subst S; ul]. }
  assert (CRL : elem_costA TAPE_MAX_DEPTH (zlength (chars bsp)) <= rt_credit RT Σg).
  { rewrite ECL. change TAPE_MAX_DEPTH with 1024%nat. unfold elem_costA, LVL_C1, DCOST. clear - CRg CR0 VCB PC0 MC0 VC0 PCB MCB DLR LBSP BSL. subst P n. unfold FUZZ_COST, DCOST in *. lia. }
  assert (CST0 : 0 <= elem_costA TAPE_MAX_DEPTH (zlength (chars bsp))) by (rewrite ECL; unfold elem_costA, LVL_C1, DCOST; lia).
  assert (PRE : lvl_pre RT E Σg m1 sp' (sp' + 96) (sp' + 120) 1 jo (elem_needA TAPE_MAX_DEPTH) (elem_costA TAPE_MAX_DEPTH (zlength (chars bsp))) TAPE_MAX_DEPTH).
  { unfold lvl_pre. subst E. cbn [ae_DOC ae_hi ae_lo].
    split; [exact NODE1|]. split; [lia|]. split; [lia|]. split; [clear - SPA'; Z.div_mod_to_equations; lia|].
    split; [exact OUT1|]. split; [lia|]. split; [lia|]. split; [clear - SPA'; Z.div_mod_to_equations; lia|]. split; [right; lia|].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact ST1|].
    split; [change TAPE_MAX_DEPTH with 1024%nat; unfold elem_needA, ATP_LEAFB; clear - LOR SPR; ul|].
    split; [clear - SPA'; Z.div_mod_to_equations; lia|].
    split; [rewrite FRSg; cbn [length]; change TAPE_MAX_DEPTH with 1024%nat; unfold FRAMES_MAX2; lia|]. split; [exact CRL|].
    split; [rewrite LVg; cbn [length]; rewrite length_app; pose proof (vblockA_length A capv (Z.of_nat P)); clear - H LVB; unfold FUZZ_LIVE, LIVE_MAX in *; lia|].

    change (lposx (rt_live RT Σg)). rewrite LVg.
    pose proof (roundup64_ge cap) as RG1. pose proof (roundup64_ge (cap + 3)) as RG2. pose proof (roundup64_ge (5 * (cap / 3) + 64)) as RG3.
    do 6 (apply lposx_cons; [first [lia| unfold sc_idx, al_tape, al_sbuf; clear - CAPR RG1 RG2 RG3; Z.div_mod_to_equations; lia]|]).
    apply lposx_app; [| exact (lposx_of_pos _ LVPOS)].
    unfold vblockA. destruct (capv =? 0); [intros p' k' []| apply lposx_ann_block; lia]. }

  pose proof (fa_walkR2 usp sp' f A P0 (zlength (atp_s0 (chars bs))) P1 L1 (velts rest) _ _
                (Z_to_bv 64 0x96dec) gp u0 u1 u2 (Z_to_bv 64 (sp' + 120)) b1 b2 b3 b4 b5 b6 b7 s2x s6x s7x s8x u3 u4 u5 u6 F1 fc m1
                FPOS ltac:(ul) ltac:(clear - SP0R LOW LOR SPR; ul) ltac:(clear - SPT SPR; ul) APOS ltac:(clear - A16; Z.div_mod_to_equations; lia) ltac:(clear - AH CAPI P2; lia)
                ltac:(clear - P1R; ul) L1R P0R L0R SV1 ELm1 SHZA1 MI1) as WR2.
  unfold sa_regs in WR2. fold S in WR2.
  lazymatch type of WR2 with evt bsegs ?K ?X =>
    assert (WR2' : forall ms, eq X ms -> evt bsegs K ms) by (intros ms <-; exact WR2) end.
  clear WR2.
  apply (cps_realizes bsegs _ _ _ c7 (asta_evt_c RT AF Σg PMc _ _ MST WR2') ltac:(unfold TPV; subst S; exact Hc7')). clear WR2'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σg _ _ c8 Hc8) as (ms8 & (a4' & a5' & ->) & Hc8'). clear Hc8.
  rewrite EL1, <- ECL in Hc8'. fold S in Hc8'.
  pose proof (cfrm0_of_asta RT Σg PMc (eq _) c8 Hc8' ltac:(intros ms0 <-; exact FRM)) as FC8.
  apply (HELEM E OKE Σg PMc (chars bsp) 1 (tn - 1) sp' (sp' + 96) (sp' + 120) P1 (Z_to_bv 64 0x96e40) gp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a4' a5' b6 b7
           s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) u3 u4 u5 u6
           F1 fc m1 jo FDO MST LVE AI1 PAT EL ltac:(lia) ltac:(subst E tn; cbn [ae_tws]; lia) PRE FRM T c8 (conj ltac:(subst E S; exact Hc8') FC8)).
  intros cr (Hcr & FCr).
  destruct Hcr as (Σr & Hcr & LVr & FRSr & SPr & CRr).
  destruct (ASTA_unpack_f RT Σr _ _ cr Hcr FCr) as (msr & (vr & m8 & RS8 & (ART8 & MI8 & ST8) & PRES8 & OREC & AI8) & FRM8 & Hcr'). clear Hcr.
  destruct RS8 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F8 & fc8 & ->).
  cbn [ms_fcsr] in FRM8. change (ae_lo E) with lo in ST8. unfold TPV in Hcr'. rewrite (ret_pc_even 0x96e40) in Hcr' by lia.
  destruct OREC as (r0 & j & code & jn' & OUT8 & CR8 & OK8).
  assert (FRSr' : rt_frames RT Σr = [(f, 2%nat)]) by (rewrite FRSr; exact FRSg).
  assert (LVEr : a_live RT Σr E) by (exact (a_live_eq RT Σg Σr E LVE LVr FRSr SPr)).
  assert (CRr' : rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σr).
  { rewrite ECL in CRr. change TAPE_MAX_DEPTH with 1024%nat in CRr. unfold elem_costA, LVL_C1, DCOST in CRr.
    clear - CRr CRg CR0 VCB PC0 MC0 VC0 PCB MCB DLR LBSP BSL. subst P n. unfold FUZZ_COST, DCOST in *. lia. }

  assert (EQ8 : forall a : word, aclient (rt_live RT Σg) (rt_frames RT Σg) sp' (bv_unsigned a) -> ~ (sp' + 96 <= bv_unsigned a < sp' + 136) -> m8 a = mg a).
  { intros a Ha Hn. rewrite <- (EQ1 a Ha ltac:(clear - Hn; lia)). apply PRES8; [exact Ha| cbn [outside]; split; [clear - Hn; lia| exact I]]. }
  assert (AG8 : forall (Q : Z -> Prop), (forall x, Q x -> sp' <= x < usp /\ ~ (sp' + 96 <= x < sp' + 120)) -> agree_on Q m1 m8).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as [H1 H2]. apply PRES8; [left; clear - H1 SPT; ul| cbn [outside]; split; [clear - H2; lia| exact I]]. }
  assert (NODE8 : rw_cells bsegs m8 (sp' + 120) [C8 (Z_to_bv 64 (f + 120)); C8 (Z_to_bv 64 1)]).
  { apply (rw_cells_agree_nw bsegs m1 m8 _ _ NODE1). apply AG8. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }
  assert (JQ8 : rw_cells bsegs m8 (sp' + 56) [CB 24 jq]).
  { apply (rw_cells_agree_nw bsegs m1 m8 _ _ JQ1). apply AG8. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }
  assert (JE8 : rw_cells bsegs m8 (sp' + 80) [CB 16 je]).
  { apply (rw_cells_agree_nw bsegs m1 m8 _ _ JE1). apply AG8. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }
  destruct (rw_cells_forget bsegs m8 (sp' + 120) _ NODE8) as (jn8 & NODE8'). cbn [cells_size csize Nat.add] in NODE8'.
  destruct (Z.eq_dec code 0) as [C0|CNZ].
  2: {
    pose proof (fa_walk11c usp sp' f (Z_to_bv 64 0x96e40) gp (Z_to_bv 64 0x653c30) w0 w1 w2 vr g1 g2 g3 g4 g5 g6 g7 s2x s6x s7x s8x w3 w4 w5 w6 r0 j code jn' F8 fc8 m8
                  FPOS ltac:(ul) ltac:(clear - SP0R LOW LOR SPR; ul) ltac:(clear - SPT SPR; ul) ltac:(clear - CR8 CNZ; lia) OUT8 MI8) as W11.
    unfold sa_regs in W11. fold S in W11.
    lazymatch type of W11 with evt bsegs _ ?X =>
      assert (W11' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W11) end.
    clear W11.
    apply (cps_realizes bsegs _ _ _ cr (asta_evt_c RT AF Σr PMc _ _ MST W11') ltac:(subst S; exact Hcr')). clear W11'. intros c9 Hc9.
    destruct (ASTA_unpack RT Σr _ _ c9 Hc9) as (ms9 & <- & Hc9'). clear Hc9.
    destruct (rw_cells_forget bsegs m8 (sp' + 96) _ OUT8) as (jo8 & OUT8'). cbn [cells_size csize Nat.add] in OUT8'.
    apply (TAILK Σr m8 w0 w1 w2 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F8 fc8 jq je jo8 jn8 c9 LVr FRSr SPr CRr' ART8 MI8 ST8
             ltac:(intros a Ha Hn; apply EQ8; [exact Ha| clear - Hn; lia]) (junk4 m8 sp' jq je jo8 jn8 JQ8 JE8 OUT8' NODE8') FRM8).
    unfold sa_regs. subst S. exact Hc9'. }

  subst code. destruct (OK8 eq_refl) as (-> & J0 & dd & jj & ELJ & JJ).
  pose proof (fa_walkR3 usp sp' f (Z_to_bv 64 0x96e40) gp (Z_to_bv 64 0x653c30) w0 w1 w2 vr g1 g2 g3 g4 g5 g6 g7 s2x s6x s7x s8x w3 w4 w5 w6 (Z_to_bv 64 (ae_DOC E)) j jn' F8 fc8 m8
                FPOS ltac:(ul) ltac:(clear - SP0R LOW LOR SPR; ul) ltac:(clear - SPT SPR; ul) OUT8 MI8) as WR3.
  unfold sa_regs in WR3. fold S in WR3.
  lazymatch type of WR3 with evt bsegs _ ?X =>
    assert (WR3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact WR3) end.
  clear WR3.
  apply (cps_realizes bsegs _ _ _ cr (asta_evt_c RT AF Σr PMc _ _ MST WR3') ltac:(subst S; exact Hcr')). clear WR3'. intros c9 Hc9.
  destruct (ASTA_unpack RT Σr _ _ c9 Hc9) as (ms9 & <- & Hc9'). clear Hc9.

  set (ebs := le8 (Z_to_bv 64 (ae_DOC E)) ++ le8 (Z_to_bv 64 j)).
  assert (LEB : length ebs = 16%nat) by (subst ebs; rewrite length_app, !length_le8; reflexivity).
  assert (EBS : bytes_at bsegs m8 (sp' + 96) ebs).
  { pose proof OUT8 as X. lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in X end.
    apply Zvw.rw_cells_app in X. destruct X as [X _].
    pose proof (rw_cells_bytes_at bsegs m8 _ _ X) as Y. cbn [cells_bytes cbytes] in Y. rewrite app_nil_r in Y. exact Y. }
  pose proof SPr as SPr'. rewrite SPg in SPr'.
  assert (CSRC2 : checked_src RT Σr m8 (Z_to_bv 64 sp') lo (sp' + 96) (Z.of_nat (length ebs))).
  { rewrite LEB. apply (checked_src_stack RT AF Σr m8 _ lo (sp' + 96) 16 ART8); [rewrite SPr'; clear - LOW LOR SPR; ul| clear - SPT SPR; ul| rewrite EU1; lia]. }
  assert (CDST2 : checked_dst RT Σr m8 (Z_to_bv 64 sp') (sp' + 80) (Z.of_nat (length ebs))).
  { rewrite LEB. apply (checked_dst_stack RT AF Σr m8 _ (sp' + 80) 16 ART8); [rewrite SPr'; clear - LOW LOR SPR; ul| clear - SPT SPR; ul| rewrite EU1; lia| exact (proj2 JE8)]. }
  assert (COK8 : call_ok RT Σr m8 (Z_to_bv 64 sp') lo).
  { unfold call_ok. rewrite EU1, SPr'. split; [exact ST8|]. split; [exact LOW|]. split; [clear - LOR SPR; ul|]. split; [clear - SPT SPR; ul| clear - SPA'; Z.div_mod_to_equations; lia]. }
  apply (rc_asan_memcpy RT RC0 Σr PMc (Z_to_bv 64 0x96e60) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) w0 w1 w2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
           (Z_to_bv 64 (sp' + 80)) (Z_to_bv 64 (sp' + 96)) (Z_to_bv 64 16) g3 g4 g5 g6 g7 s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120))
           s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) w3 w4 w5 w6 F8 fc8 m8 (sp' + 80) (sp' + 96) ebs lo
           FDO MST eq_refl eq_refl ltac:(rewrite LEB; reflexivity) ltac:(clear - SPT SPR LOR LOW SP0R; ul) ltac:(clear - SPT SPR LOR LOW SP0R; ul) ltac:(rewrite LEB; cbn; lia)
           EBS CSRC2 CDST2 ltac:(rewrite LEB; cbn; lia) ART8 MI8 COK8 T c9 ltac:(subst S; exact Hc9')).
  intros c10 Hc10. unfold icpt_postF in Hc10.
  destruct (ASTA_unpack RT Σr _ _ c10 Hc10) as (ms10 & (m9 & RS9 & (ART9 & MI9 & WM9 & ST9) & PRES9 & BY9) & Hc10'). clear Hc10.
  destruct RS9 as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F9 & ->).
  rewrite EU1 in ST9, PRES9. rewrite LEB in PRES9. change (Z.of_nat 16%nat) with 16 in PRES9.
  rewrite (ret_pc_even 0x96e60) in Hc10' by lia.
  pose proof PRES9 as PRES9g. rewrite LVr, FRSr in PRES9g.
  assert (AI9 : AINV_A E m9) by (exact (AINV_A_pres_ex RT Σr E sp' (sp' + 80) 16 m8 m9 LVEr OKE AI8 PRES9 ltac:(change (ae_lo E) with lo; clear - LOR SPR; ul))).
  assert (EQ9 : forall a : word, aclient (rt_live RT Σg) (rt_frames RT Σg) sp' (bv_unsigned a) -> ~ (sp' + 80 <= bv_unsigned a < sp' + 136) -> m9 a = mg a).
  { intros a Ha Hn. rewrite <- (EQ8 a Ha ltac:(clear - Hn; lia)). apply PRES9g; [exact Ha| clear - Hn; lia]. }
  assert (AG9 : forall (Q : Z -> Prop), (forall x, Q x -> sp' <= x < usp /\ ~ (sp' + 80 <= x < sp' + 96)) -> agree_on Q m8 m9).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as [H1 H2]. apply PRES9g; [left; clear - H1 SPT; ul| clear - H2; lia]. }
  assert (WRE : wr_at bsegs m9 (sp' + 80) (Z.of_nat (length ebs))) by (rewrite LEB; exact (wr_at_transport bsegs m8 m9 (sp' + 80) _ (proj2 JE8) WM9)).
  pose proof (rw_cells_CB_intro m9 (sp' + 80) ebs BY9 WRE) as ELC9. rewrite LEB in ELC9. subst ebs. apply rec_node16 in ELC9.
  assert (OUT9 : rw_cells bsegs m9 (sp' + 96) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 j); C4 (Z_to_bv 64 0); CB 4 jn']).
  { apply (rw_cells_agree_nw bsegs m8 m9 _ _ OUT8). apply AG9. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }
  assert (NODE9 : rw_cells bsegs m9 (sp' + 120) [CB 16 jn8]).
  { apply (rw_cells_agree_nw bsegs m8 m9 _ _ NODE8'). apply AG9. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }
  assert (JQ9 : rw_cells bsegs m9 (sp' + 56) [CB 24 jq]).
  { apply (rw_cells_agree_nw bsegs m8 m9 _ _ JQ8). apply AG9. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }

  pose proof (fa_walkR4 usp sp' f (Z_to_bv 64 0x96e60) gp (Z_to_bv 64 0x653c30) y0 y1 y2 (Z_to_bv 64 (sp' + 80)) e1 e2 e3 e4 e5 e6 e7 s2x s6x s7x s8x y3 y4 y5 y6 F9 fc8 m9
                FPOS ltac:(ul) ltac:(clear - SP0R LOW LOR SPR; ul) ltac:(clear - SPT SPR; ul)) as WR4.
  unfold sa_regs in WR4. fold S in WR4.
  lazymatch type of WR4 with evt bsegs _ ?X =>
    assert (WR4' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact WR4) end.
  clear WR4.
  apply (cps_realizes bsegs _ _ _ c10 (asta_evt_c RT AF Σr PMc _ _ MST WR4') ltac:(subst S; exact Hc10')). clear WR4'. intros c11 Hc11.
  destruct (ASTA_unpack RT Σr _ _ c11 Hc11) as (ms11 & <- & Hc11'). clear Hc11.
  pose proof (cfrm0_of_asta RT Σr PMc (eq _) c11 Hc11' ltac:(intros ms0 <-; exact FRM8)) as FC11.

  apply (gstr_cpsA RT AF E OKE RC0 Σr PMc sp' (sp' + 56) (sp' + 80) j jj dd (Z_to_bv 64 0x96e6c) gp y0 y1 y2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') e2 e3 e4 e5 e6 e7
           s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6x s7x s8x (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) y3 y4 y5 y6 F9 fc8 m9 jq
           FDO MST LVEr AI9 ELJ J0 ELC9 ltac:(lia) ltac:(subst E; cbn [ae_hi]; clear - SPR; lia) ltac:(clear - SPA'; Z.div_mod_to_equations; lia)
           JQ9 ltac:(lia) ltac:(subst E; cbn [ae_hi]; clear - SPR; lia) ltac:(clear - SPA'; Z.div_mod_to_equations; lia) ltac:(right; lia)
           ART9 MI9 ltac:(change (ae_lo E) with lo; exact ST9) ltac:(change (ae_lo E) with lo; clear - LOR SPR; ul) ltac:(clear - SPA'; Z.div_mod_to_equations; lia)
           FRM8 T c11 (conj ltac:(unfold ATPA_GETSTR, ATP_GETSTR_A, TPV in *; subst E S; exact Hc11') FC11)).
  intros c12 (Hc12 & FC12).
  destruct (ASTA_unpack_f RT Σr _ _ c12 Hc12 FC12) as (ms12 & (vq & m10 & b16 & g20 & code2 & RS10 & (ART10 & MI10 & ST10) & PRES10 & GREC & C2) & FRM10 & Hc12'). clear Hc12.
  destruct RS10 as (z0 & z1 & z2 & h1 & h2 & h3' & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & F10 & fc10 & ->).
  cbn [ms_fcsr] in FRM10. change (ae_lo E) with lo in ST10. unfold TPV in Hc12'. rewrite (ret_pc_even 0x96e6c) in Hc12' by lia.
  pose proof PRES10 as PRES10g. rewrite LVr, FRSr in PRES10g.

  pose proof (fa_walk11g usp sp' f (Z_to_bv 64 0x96e6c) gp (Z_to_bv 64 0x653c30) z0 z1 z2 vq h1 h2 h3' h4 h5 h6 h7 s2x s6x s7x s8x z3 z4 z5 z6 b16 code2 g20 F10 fc10 m10
                FPOS ltac:(ul) ltac:(clear - SP0R LOW LOR SPR; ul) ltac:(clear - SPT SPR; ul) ltac:(clear - C2; lia) GREC MI10) as W11.
  unfold sa_regs in W11. fold S in W11.
  lazymatch type of W11 with evt bsegs _ ?X =>
    assert (W11' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W11) end.
  clear W11.
  apply (cps_realizes bsegs _ _ _ c12 (asta_evt_c RT AF Σr PMc _ _ MST W11') ltac:(subst S; exact Hc12')). clear W11'. intros c13 Hc13.
  destruct (ASTA_unpack RT Σr _ _ c13 Hc13) as (ms13 & <- & Hc13'). clear Hc13.

  assert (EQ10 : forall a : word, aclient (rt_live RT Σg) (rt_frames RT Σg) sp' (bv_unsigned a) -> ~ (sp' + 56 <= bv_unsigned a < sp' + 136) -> m10 a = mg a).
  { intros a Ha Hn. rewrite <- (EQ9 a Ha ltac:(clear - Hn; lia)). apply PRES10g; [exact Ha| cbn [outside]; split; [clear - Hn; lia| exact I]]. }
  assert (AG10 : forall (Q : Z -> Prop), (forall x, Q x -> sp' <= x < usp /\ ~ (sp' + 56 <= x < sp' + 80)) -> agree_on Q m9 m10).
  { intros Q HQ a Ha. destruct (HQ _ Ha) as [H1 H2]. apply PRES10g; [left; clear - H1 SPT; ul| cbn [outside]; split; [clear - H2; lia| exact I]]. }
  destruct (rw_cells_forget bsegs m10 (sp' + 56) _ GREC) as (jq10 & JQ10). cbn [cells_size csize Nat.add] in JQ10.
  destruct (rw_cells_forget bsegs m9 (sp' + 80) _ ELC9) as (je9 & JE9). cbn [cells_size csize Nat.add] in JE9.
  destruct (rw_cells_forget bsegs m9 (sp' + 96) _ OUT9) as (jo9 & JO9). cbn [cells_size csize Nat.add] in JO9.
  assert (JE10 : rw_cells bsegs m10 (sp' + 80) [CB 16 je9]).
  { apply (rw_cells_agree_nw bsegs m9 m10 _ _ JE9). apply AG10. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }
  assert (JO10 : rw_cells bsegs m10 (sp' + 96) [CB 24 jo9]).
  { apply (rw_cells_agree_nw bsegs m9 m10 _ _ JO9). apply AG10. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }
  assert (JN10 : rw_cells bsegs m10 (sp' + 120) [CB 16 jn8]).
  { apply (rw_cells_agree_nw bsegs m9 m10 _ _ NODE9). apply AG10. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx SPR. lia. }
  apply (TAILK Σr m10 z0 z1 z2 h2 h3' h4 h5 h6 h7 z3 z4 z5 z6 F10 fc10 jq10 je9 jo9 jn8 c13 LVr FRSr SPr CRr' ART10 MI10 ST10 EQ10
           (junk4 m10 sp' jq10 je9 jo9 jn8 JQ10 JE10 JO10 JN10) FRM10).
  unfold sa_regs. subst S. exact Hc13'.
Qed.
End Top3b.

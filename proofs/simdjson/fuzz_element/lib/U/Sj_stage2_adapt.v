(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjAlloc SjStage2 SjLeaves SjNumber SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_num_iface Sj_stage2_defs Sj_stage2_exit Sj_stage2_entry Sj_stage2_main Sj_stage2_main2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Sj_iface Sj_kit Sj_stage2_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition stage2t_rootnum_stmt : Prop :=
  forall (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (lo B : Z) (errv : word)
         (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (bs idxs : list Z) (iws : list word) (cap tcap scap : Z)
         (nxt docv dcap : word) (p12 p28 p50 : list byte),
  forall c : Z, SjAlloc.root_copy bs 0 (hd 0 idxs) = Some c ->

  S1OUT bs idxs -> bytes_ok bs -> blen bs <= 1048512 ->
  firstn (length idxs + 3) iws = map wz (idxs ++ [blen bs; blen bs; 0]) ->

  blen bs + 3 <= tcap -> tcap <= 2^40 -> 5 * blen bs + 5 <= 3 * scap -> scap <= 2^40 ->
  blen bs + 3 <= Z.of_nat (length iws) ->

  RHEAP s LB m -> rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SJ_S2_STACK ->
  bv_unsigned sp mod 16 = 0 ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m -> frm0 fc ->
  rw_cells usegs m SJ_GOT_NOTHROW [C8 (wz SJ_NOTHROW_TAG)] ->

  region_in LB THIS 96 -> region_in LB IDX (4 * Z.of_nat (length iws)) -> region_in LB BUF (blen bs + 64) ->
  region_in LB TAPE (8 * tcap) -> region_in LB SBUF scap -> region_in LB OC 8192 -> region_in LB IA 1024 ->
  pairwise_disj [(THIS, 96); (IDX, 4 * Z.of_nat (length iws)); (BUF, blen bs + 64); (TAPE, 8 * tcap); (SBUF, scap); (OC, 8192); (IA, 1024)] ->
  bv_unsigned sp <= DOC -> DOC + 24 <= B ->
  THIS mod 8 = 0 -> DOC mod 8 = 0 -> IDX mod 4 = 0 -> TAPE mod 8 = 0 -> OC mod 8 = 0 ->
  rw_cells usegs m THIS (s2_impl_cells (Z.of_nat (length idxs)) IDX cap OC IA BUF (blen bs) nxt docv p12 p28 p50) ->
  rw_cells usegs m DOC [C8 (wz TAPE); C8 (wz SBUF); C8 dcap] ->
  u32arr usegs m IDX iws ->
  bytes_at usegs m BUF (padded_bytes bs) ->
  wr_at usegs m TAPE (8 * tcap) -> wr_at usegs m SBUF scap ->
  (exists ocs, u32arr usegs m OC ocs /\ length ocs = 2048%nat) ->
  (exists ias, u8arr usegs m IA ias /\ length ias = 1024%nat) ->
  implM usegs (mbind (newnt lops c) (fun r => del lops r)) s
        (stage2t_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B m
                     THIS DOC IDX BUF TAPE SBUF OC IA (Z.of_nat (length idxs)) cap (blen bs) tcap scap p12 p28 p50)
        (MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz THIS) (wz DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz SJ_STAGE2) fc None m (seg_rom usegs)).

Lemma stk_of_wr_at : forall (m : mem) a n, wr_at usegs m a n -> (a + n <= 0x10000 \/ 0x111000 <= a) -> stk usegs m a (a + n).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros m a n (A0 & An & HW) Himg. split; [lia|]. split; [lia|]. intros x Hx.
  specialize (HW (x - a) ltac:(lia)). replace (a + (x - a)) with x in HW by lia.
  rewrite ref_wview_overlay in HW by (rewrite wa_unsigned by lia; lia).
  split.
  - rewrite ref_wview_overlay by (rewrite wa_unsigned by lia; lia). exact HW.
  - rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia). destruct (m (wa x)) as [b|]; [exists b; reflexivity | exfalso; apply HW; reflexivity].
Qed.

Lemma tape_img_init : forall (E : s2env) (m : mem),
  wr_at usegs m (e_TAPE E) (8 * e_tcap E) -> wr_at usegs m (e_SBUF E) (e_scap E) ->
  (e_TAPE E + 8 * e_tcap E <= 0x10000 \/ 0x111000 <= e_TAPE E) -> (e_SBUF E + e_scap E <= 0x10000 \/ 0x111000 <= e_SBUF E) ->
  1 <= e_tcap E -> 0 <= e_scap E ->
  exists h0, tape_img E [h0] [] m.
Proof.
  intros E m WT WS IT IS HT HS.
  pose proof (stk_of_wr_at m _ _ WT IT) as S1. pose proof (stk_of_wr_at m _ _ WS IS) as S2.
  destruct WT as (T0 & T1 & _). destruct WS as (U0 & U1 & _).
  destruct (stk_split usegs m _ (e_TAPE E + 8) _ S1 ltac:(lia)) as [S3 _].
  destruct (stk_bytes usegs m _ _ S3 ltac:(lia)) as (bs8 & HL & HB).
  destruct (le8_surj bs8 ltac:(lia)) as (v & <-).
  exists (bv_unsigned v). unfold tape_img, twords, zbytes. cbn [map u64s length Z.of_nat Pos.of_succ_nat].
  rewrite Z_to_bv_bv_unsigned.
  split; [|split; [|split; [lia|split; [lia|split; [exact S1 | split; [exact S2 | constructor]]]]]].
  - apply bytes_at_app. split; [exact HB|]. rewrite length_le8. apply timg_bytes_at_nil. lia.
  - apply timg_bytes_at_nil. lia.
Qed.

Lemma s2_lx_pres_of_munch : forall LB' SP X W m m',
  munch W m m' -> wmono usegs m m' -> (forall a, lx_client LB' SP X a -> outside W a) -> lx_pres LB' SP X m m'.
Proof. intros LB' SP X W m m' MU WM HW. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)| exact HW]. Qed.

Lemma region_below : forall s LB m X n lo, RHEAP s LB m -> region_in LB X n -> alloc_ceiling <= lo -> 0 <= n ->
  0 < X /\ X + n <= lo /\ (X + n <= 0x10000 \/ 0x111000 <= X).
Proof.
  intros s LB m X n lo HH (b & Hb & H1 & H2) HC Hn.
  pose proof (LH_block_range s LB m b HH Hb) as (R0 & _ & R2 & R3 & R4). lia.
Qed.

Lemma pd7 : forall x1 x2 x3 x4 x5 x6 x7, pairwise_disj [x1; x2; x3; x4; x5; x6; x7] ->
  (ivl_disj x1 x2 /\ ivl_disj x1 x3 /\ ivl_disj x1 x4 /\ ivl_disj x1 x5 /\ ivl_disj x1 x6 /\ ivl_disj x1 x7) /\
  (ivl_disj x2 x3 /\ ivl_disj x2 x4 /\ ivl_disj x2 x5 /\ ivl_disj x2 x6 /\ ivl_disj x2 x7) /\
  (ivl_disj x3 x4 /\ ivl_disj x3 x5 /\ ivl_disj x3 x6 /\ ivl_disj x3 x7) /\
  (ivl_disj x4 x5 /\ ivl_disj x4 x6 /\ ivl_disj x4 x7) /\ (ivl_disj x5 x6 /\ ivl_disj x5 x7) /\ ivl_disj x6 x7.
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 H. cbn [pairwise_disj] in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H end.
  tauto.
Qed.

Theorem stage2t_of_walk :
  slowfu_stmt_g usegs 0x5edf4 0x111000 -> pffu_stmt_g usegs 0x5eea4 0x111000 -> stage2t_rootnum_stmt -> stage2t_stmt.
Proof.
  intros HSLOWF HPFF HROOT. unfold stage2t_stmt.
  intros ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv
         THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws cap tcap scap nxt docv dcap p12 p28 p50
         HS1 HBOK HLEN HIWS HTC1 HTC2 HSC1 HSC2 HIWL HHEAP HAUX HSPB HB63 HST HCEIL HGT HLO HSP16 HERR HMI HFRM HGOT
         RTHIS RIDX RBUF RTAPE RSBUF ROC RIA HPD HDOC1 HDOC2 HALT HALD HALI HALTP HALO HIMPL HDOCC HIDXA HBUFRO HTAPEW HSBUFW HOCA HIAA.
  unfold s2_root_phase. destruct (SjAlloc.root_copy bs 0 (hd 0 idxs)) as [c|] eqn:RC.
  { eapply (HROOT ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB lo B errv
              THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws cap tcap scap nxt docv dcap p12 p28 p50 c RC); eassumption. }
  apply implM_ret.
  assert (HROOMZ : lo + 368 + 2608 <= bv_unsigned sp) by (unfold SJ_S2_STACK, SJ_S2_FRAMES, RMALLOC_STACK in HLO; lia).
  destruct (stk_carve usegs m lo (bv_unsigned sp) 368 HST ltac:(lia)) as [ST' [junk FRJ]].
  apply (rw_cells_split_CB usegs m _ [] 368 junk [] [80; 184; 104]%nat) in FRJ; [|reflexivity].
  cbn [mk_CB_cells app] in FRJ.
  lazymatch type of FRJ with rw_cells _ _ _ [CB 80 ?jlo; CB 184 ?j80; CB 104 ?jhi] =>
    set (E := mkS2Env ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws tcap scap
                      (wz SJ_DPI_VPTR) p12 nxt p28 (wz cap) p50 dcap j80 m [] [])
  end.
  pose proof (region_below s LB m THIS 96 lo HHEAP RTHIS HCEIL ltac:(lia)) as BTHIS.
  pose proof (region_below s LB m IDX _ lo HHEAP RIDX HCEIL ltac:(lia)) as BIDX.
  pose proof (region_below s LB m BUF _ lo HHEAP RBUF HCEIL ltac:(pose proof (blen_nonneg bs); lia)) as BBUF.
  pose proof (region_below s LB m TAPE _ lo HHEAP RTAPE HCEIL ltac:(pose proof (blen_nonneg bs); lia)) as BTAPE.
  pose proof (region_below s LB m SBUF _ lo HHEAP RSBUF HCEIL ltac:(pose proof (blen_nonneg bs); lia)) as BSBUF.
  pose proof (region_below s LB m OC 8192 lo HHEAP ROC HCEIL ltac:(lia)) as BOC.
  pose proof (region_below s LB m IA 1024 lo HHEAP RIA HCEIL ltac:(lia)) as BIA.
  assert (OK : Sj_stage2_defs.env_ok E).
  { destruct (pd7 _ _ _ _ _ _ _ HPD) as ((D12 & D13 & D14 & D15 & D16 & D17) & (D23 & D24 & D25 & D26 & D27) & (D34 & D35 & D36 & D37) & (D45 & D46 & D47) & (D56 & D57) & D67).
    unfold GLOBALS_TOP in HGT.
    subst E. constructor; cbn [Sj_stage2_defs.e_bs Sj_stage2_defs.e_idxs Sj_stage2_defs.e_iws Sj_stage2_defs.e_tcap Sj_stage2_defs.e_scap Sj_stage2_defs.e_lo Sj_stage2_defs.e_sp Sj_stage2_defs.e_THIS Sj_stage2_defs.e_DOC Sj_stage2_defs.e_IDX Sj_stage2_defs.e_BUF Sj_stage2_defs.e_TAPE Sj_stage2_defs.e_SBUF Sj_stage2_defs.e_OC Sj_stage2_defs.e_IA]; unfold S2_LEN_MAX, S2_STACK.
    - exact HS1.
    - exact HBOK.
    - exact HLEN.
    - clear - HTC1 HTC2. lia.
    - clear - HSC1 HSC2. lia.
    - exact HIWS.
    - exact HGT.
    - clear - HROOMZ. lia.
    - clear - BTHIS. lia.
    - clear - HDOC1 HDOC2 HB63. lia.
    - clear - BIDX. lia.
    - clear - BBUF. lia.
    - clear - BTAPE. lia.
    - clear - BSBUF. lia.
    - clear - BOC. lia.
    - clear - BIA. lia.
    - exact HALT.
    - exact HALD.
    - exact HALI.
    - exact HALTP.
    - exact HALO.
    - exact HSP16.
    - clear - D12. unfold ivl_disj in D12. cbn [fst snd] in D12. lia.
    - clear - D13. unfold ivl_disj in D13. cbn [fst snd] in D13. lia.
    - clear - D14. unfold ivl_disj in D14. cbn [fst snd] in D14. lia.
    - clear - D15. unfold ivl_disj in D15. cbn [fst snd] in D15. lia.
    - clear - D16. unfold ivl_disj in D16. cbn [fst snd] in D16. lia.
    - clear - D17. unfold ivl_disj in D17. cbn [fst snd] in D17. lia.
    - clear - D24. unfold ivl_disj in D24. cbn [fst snd] in D24. lia.
    - clear - D34. unfold ivl_disj in D34. cbn [fst snd] in D34. lia.
    - clear - D45. unfold ivl_disj in D45. cbn [fst snd] in D45. lia.
    - clear - D46. unfold ivl_disj in D46. cbn [fst snd] in D46. lia.
    - clear - D47. unfold ivl_disj in D47. cbn [fst snd] in D47. lia.
    - clear - D25. unfold ivl_disj in D25. cbn [fst snd] in D25. lia.
    - clear - D35. unfold ivl_disj in D35. cbn [fst snd] in D35. lia.
    - clear - D56. unfold ivl_disj in D56. cbn [fst snd] in D56. lia.
    - clear - D57. unfold ivl_disj in D57. cbn [fst snd] in D57. lia.
    - clear - D26. unfold ivl_disj in D26. cbn [fst snd] in D26. lia.
    - clear - D36. unfold ivl_disj in D36. cbn [fst snd] in D36. lia.
    - clear - D67. unfold ivl_disj in D67. cbn [fst snd] in D67. lia.
    - clear - D27. unfold ivl_disj in D27. cbn [fst snd] in D27. lia.
    - clear - D37. unfold ivl_disj in D37. cbn [fst snd] in D37. lia. }
  destruct (tape_img_init E m HTAPEW HSBUFW ltac:(clear - BTAPE; subst E; cbn; lia) ltac:(clear - BSBUF; subst E; cbn; lia)
              ltac:(clear - HTC1; subst E; cbn; pose proof (blen_nonneg bs); lia) ltac:(clear - HSC1 HSC2; subst E; cbn; pose proof (blen_nonneg bs); lia)) as [h0 TIMG].
  assert (HM0 : Sj_stage2_entry.MEM0 (s2_ghost E [h0] []) docv fc m).
  { unfold Sj_stage2_entry.MEM0. revert TIMG. subst E. intros TIMG. cbn [Sj_stage2_defs.e_m0 Sj_stage2_defs.e_THIS Sj_stage2_defs.e_DOC Sj_stage2_defs.e_IDX Sj_stage2_defs.e_BUF
      Sj_stage2_defs.e_TAPE Sj_stage2_defs.e_SBUF Sj_stage2_defs.e_OC Sj_stage2_defs.e_IA Sj_stage2_defs.e_bs Sj_stage2_defs.e_iws Sj_stage2_defs.e_tcap
      Sj_stage2_defs.e_scap Sj_stage2_defs.e_lo Sj_stage2_defs.e_sp Sj_stage2_defs.e_j80 Sj_stage2_defs.e_tws Sj_stage2_defs.e_sbs s2_ghost].
    split; [exact HFRM|]. split; [reflexivity|]. split; [exact HIMPL|]. split; [exact HDOCC|]. split; [exact HIDXA|]. split; [exact HBUFRO|].
    split; [exact HTAPEW|]. split; [exact HSBUFW|]. split; [exact HOCA|]. split; [exact HIAA|]. split; [exact HMI|].
    split; [exact ST'|]. split; [eexists _, _; exact FRJ | exact TIMG]. }
  assert (KX : forall tws sbs, Sj_stage2_defs.exit_k (s2_ghost E tws sbs) (s2_post E)).
  { intros tws sbs. unfold Sj_stage2_defs.exit_k. intros.
    eapply (s2_exit (s2_ghost E tws sbs)); [apply env_ok_ghost; exact OK | eassumption | eassumption]. }
  assert (HROOM : Sj_stage2_defs.e_lo E + 368 + NUMU_STACK <= bv_unsigned (Sj_stage2_defs.e_sp E)) by (subst E; cbn; unfold NUMU_STACK; lia).
  assert (RN : is_numstart (tok bs idxs 0) = true -> rootprim_k (s2_ghost E [h0] []) (s2_post E) 0x43a30).
  { intros HN. exfalso. unfold SjAlloc.root_copy in RC. cbn [Z.eqb andb] in RC.
    destruct idxs as [|i0 rest]; [pose proof (n_pos _ _ HS1) as NP; unfold n in NP; cbn in NP; lia|].
    cbn [hd] in RC. unfold tok, off, ext in HN. cbn [app nth Z.to_nat] in HN.
    unfold is_numstart, is_digit, c_minus in HN. unfold SjAlloc.is_numstart_b in RC. rewrite HN in RC. discriminate RC. }
  eapply evt_mono.
  { exact (s2_main2 E OK HSLOWF HPFF HROOM (s2_post E) KX h0 RN docv t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m HM0). }
  intros ms' HP.
  unfold s2_post in HP.
  destruct HP as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & F' & fc' & m'
                  & -> & A064 & MU & WM & MI' & FRM' & (nxt' & IMPL') & _ & _ & _ & _ & _ & _ & _ & ST2 & RES).
  clear TIMG HM0 KX RN. subst E. unfold s2_W in MU.
  cbn [Sj_stage2_defs.e_m0 Sj_stage2_defs.e_THIS Sj_stage2_defs.e_TAPE Sj_stage2_defs.e_SBUF Sj_stage2_defs.e_OC Sj_stage2_defs.e_IA
       Sj_stage2_defs.e_tcap Sj_stage2_defs.e_scap Sj_stage2_defs.e_lo Sj_stage2_defs.e_sp] in MU, WM, ST2, RES.
  destruct RTHIS as (b1 & Hb1 & R11 & R12). destruct RTAPE as (b4 & Hb4 & R41 & R42). destruct RSBUF as (b5 & Hb5 & R51 & R52).
  destruct ROC as (b6 & Hb6 & R61 & R62). destruct RIA as (b7 & Hb7 & R71 & R72).
  pose proof (LH_block_range s LB m b1 HHEAP Hb1) as (Q10 & _ & Q12 & Q13 & Q14).
  pose proof (LH_block_range s LB m b4 HHEAP Hb4) as (Q40 & _ & Q42 & Q43 & Q44).
  pose proof (LH_block_range s LB m b5 HHEAP Hb5) as (Q50 & _ & Q52 & Q53 & Q54).
  pose proof (LH_block_range s LB m b6 HHEAP Hb6) as (Q60 & _ & Q62 & Q63 & Q64).
  pose proof (LH_block_range s LB m b7 HHEAP Hb7) as (Q70 & _ & Q72 & Q73 & Q74).
  unfold stage2t_post.
  exists q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, F', fc', m', errv, nxt'.
  split; [reflexivity|]. split; [exact FRM'|].
  split.
  { eapply LH_frame; [exact HHEAP | exact MU | exact WM |].
    constructor; [apply W_ok_stack; exact HCEIL|].
    constructor; [eapply W_ok_block; [exact Hb1 | exact R11 | exact R12]|].
    constructor; [eapply W_ok_block; [exact Hb4 | exact R41 | exact R42]|].
    constructor; [eapply W_ok_block; [exact Hb5 | exact R51 | exact R52]|].
    constructor; [eapply W_ok_block; [exact Hb6 | exact R61 | exact R62]|].
    constructor; [eapply W_ok_block; [exact Hb7 | exact R71 | exact R72]| constructor]. }
  unfold GLOBALS_TOP in HGT.
  split.
  { eapply rauxv_ok_frame; [exact HAUX | exact MU | exact WM |]. unfold RAUXV_CELL.
    constructor; [cbn [fst snd]; clear - HSPB HGT; lia|].
    constructor; [cbn [fst snd]; clear - BTHIS HROOMZ HSPB; lia|].
    constructor; [cbn [fst snd]; clear - BTAPE HROOMZ HSPB; lia|].
    constructor; [cbn [fst snd]; clear - BSBUF HROOMZ HSPB; lia|].
    constructor; [cbn [fst snd]; clear - BOC HROOMZ HSPB; lia|].
    constructor; [cbn [fst snd]; clear - BIA HROOMZ HSPB; lia| constructor]. }
  split; [exact ST2|].
  split.
  { eapply rw_cells_transport; [exact HERR | exact MU | exact WM |].
    unfold LX_ERRNO, RATP. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    split; [clear - HGT; lia|]. split; [clear - BTHIS; lia|]. split; [clear - BTAPE; lia|]. split; [clear - BSBUF; lia|].
    split; [clear - BOC; lia|]. split; [clear - BIA; lia| exact I]. }
  split; [exact MI'|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { eapply s2_lx_pres_of_munch; [exact MU | exact WM |].
    intros a (HX & HC). unfold s2_X in HX. cbn [rin_ivs fst snd] in HX. cbn [outside].
    assert (HA : ~ (lo <= a < bv_unsigned sp)).
    { destruct HC as [HC | [(b & Hb & Hr) | (HC & _)]]; [clear - HC; lia | | clear - HC HGT; lia].
      pose proof (LH_block_range s LB m b HHEAP Hb) as (_ & _ & _ & P3 & _). clear - P3 Hr HCEIL. lia. }
    split; [exact HA|].
    split; [intros HI; apply HX; left; exact HI|].
    split; [intros HI; apply HX; right; left; exact HI|].
    split; [intros HI; apply HX; right; right; left; exact HI|].
    split; [intros HI; apply HX; right; right; right; left; exact HI|].
    split; [intros HI; apply HX; right; right; right; right; left; exact HI| exact I]. }
  split; [exact IMPL'|].
  unfold s2_result, s2_fail, tape_ok, twords, zbytes in RES. exact RES.
Qed.

End WithCeiling0.

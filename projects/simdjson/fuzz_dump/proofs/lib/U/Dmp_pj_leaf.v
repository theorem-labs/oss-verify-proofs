(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjDmp.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_h_arith Atp_objl.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_kitu Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_defs Dmp_defs Dmp_pj_iface Dmp_pj_kit.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac retlit := try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).

Lemma land7_of_mod8 : forall A, 0 <= A -> A mod 8 = 0 -> Z.land A 7 = 0.
Proof. intros A H0 H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma sbuf_slice : forall m (SBUF : Z) (sbs : list Z) (o l : Z),
  bytes_at usegs m SBUF (map (Z_to_bv 8) sbs) -> 0 <= o -> 0 <= l -> o + 4 + l < Z.of_nat (length sbs) ->
  bytes_at usegs m (SBUF + o + 4) (firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) sbs)))
  /\ Z.of_nat (length (firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) sbs)))) = l.
Proof.
  intros m SBUF sbs o l HB Ho Hl Hol. split.
  - replace (SBUF + o + 4) with (SBUF + Z.of_nat (Z.to_nat (o + 4))) by lia.
    apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
  - rewrite firstn_length_le; [lia|]. rewrite length_skipn, length_map. lia.
Qed.

Section Body.
  Variable D : pjenv.
  Hypothesis DOK : pjenv_ok D.
  Hypothesis PUT : os_putX_stmt.
  Hypothesis INSB : ins_b_stmt.
  Hypothesis INSL : ins_l_stmt.
  Hypothesis INSUL : ins_ul_stmt.
  Hypothesis INSD : ins_d_stmt.

  Notation n := (pe_n D).
  Notation T := (Tf (pe_tws D)).
  Notation S := (Tf (pe_sbs D)).
  Notation sn := (pe_sn D).

  Lemma PINV_below : forall lc m m' k, cells_size lc = 32%nat -> PINV lc D m -> 0 <= k <= DMP_PJ_LEAF ->
    munch [(dsp D - k, dsp D)] m m' -> wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' (pe_lo D) (dsp D) -> PINV lc D m'.
  Proof.
    intros lc m m' k LCS DI HK MU WM MI' ST'.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & DCB & TPC & SSP & MI & ST & (j0 & out & j56 & j80 & FR) & TB & SB & DOCC & MU0 & WM0 & (errv & ERR)).
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    Ltac trb AG C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; cbn [outside]; lia].
    split. { exists pb, pp, ep, fill, dum, j148, j284. split; [| split; [exact PUTI| exact FOK]].
             eapply rw_cells_agree; [exact AG| exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia. }
    split; [eapply LOCB_transport; [exact LB| exact MU| exact WM|]; cbv [disjoint_from fst snd]; lia|].
    split. { destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
             split; [trb AG C1|]. split; [trb AG C2|]. split; [trb AG C3|]. split; [trb AG C4|]. split; [trb AG C5| trb AG C6]. }
    split; [unfold dmp_dcc, DMP_NPB_SLOT in *; trb AG DCB|].
    split; [trb AG TPC|].
    split; [eapply ssp_cells_agree; [exact AG| | exact SSP]; intros a Ha; unfold ssp_addr, got_ssp, ssp_guard in Ha; cbn [outside]; lia|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { exists j0, out, j56, j80. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. rewrite (uframe_size D j0 lc out j56 j80 LCS) in Ha. cbn [outside]. lia. }
    split. { eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. cbn [outside]. clear - Ha T0 TH TI GLO LO HK. lia. }
    split. { eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. cbn [outside]. clear - Ha S0 SH SI GLO LO HK. lia. }
    split; [trb AG DOCC|].
    split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, pj_W. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Definition KEXIT (lc : list cell) (K : machine_state -> Prop) (gp : word) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      PINV lc D m' -> frm0 fc' ->
      evt usegs K (MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                      F' (Z_to_bv 64 DMP_PJ_EXIT) fc' None m' (seg_rom usegs)).

  Definition DST (i ty : Z) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 (pe_DOC D))
            (Z_to_bv 64 ty) x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 i) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D) x28 x29 x30 x31)
       F (Z_to_bv 64 DMP_PJ_DISPATCH) fc None m (seg_rom usegs).

  Lemma pj_exit : forall (lc : list cell) (x1 gp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    cells_size lc = 32%nat -> PINV lc D m -> frm0 fc ->
    evt usegs (pj_post (pe_ra D) (pe_q D) gp (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)
                       (pe_lo D) (pe_OS D) (pe_canary D) (pe_m0 D))
      (MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DMP_PJ_EXIT) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros LCS DI FRM.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, DMP_PJ_EXIT in *.
    pose proof DI as (OSXm & LB & DCC & DCB & TPC & SSP & MI & ST & (j0 & out & j56 & j80 & FR) & TB & SB & DOCC & MU0 & WM0 & (errv & ERR)).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    unfold uframe in FR. rewrite !app_assoc in FR.
    apply (proj1 (rw_cells_app _ _ _ _)) in FR. destruct FR as [F12 F3].
    destruct (rw_cells_forget _ _ _ _ F12) as [j88 F12']. rewrite !cells_size_app, LCS in F12', F3. cbn [cells_size csize Nat.add] in F12', F3.
    pose proof (proj2 (rw_cells_app m (dsp D) [CB 88 j88] _) (conj F12' F3)) as FRJ. cbn [app cells_size csize] in FRJ. unfold pjsaves in FRJ. clear F12 F3 F12'.

    do 13 step. step. release_frame FRJ ST (pe_q D). step.
    replace (Z_to_bv 64 (dsp D + 192)) with (Z_to_bv 64 (pe_q D)) by (f_equal; lia).
    apply evt_done. unfold pj_post. do 15 eexists. exists F, fc. eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FRM|].
    split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, pj_W. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|].
    split; [assumption|].
    split; [assumption|].
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    split. { destruct OSXm as (pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK). exists pb, pp, ep, fill, dum, j148, j284.
             split; [| split; [exact PUTI| exact FOK]]. eapply rw_cells_agree; [exact AG| exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia. }
    split. { eapply rw_cells_agree; [exact AG| exact TPC|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
    split. { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia. }
    split. { eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn [outside]. lia. }
    eapply LOCB_transport; [exact LB| exact MU| exact WM|]. cbv [disjoint_from fst snd]. lia.
  Qed.

  Lemma pj_enter : forall (K : machine_state -> Prop) (gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (errv : word),
    let m := pe_m0 D in let i := pe_i D in
    0 <= T i < 2^64 ->
    rw_cells usegs m (pe_DOC D) [C8 (Z_to_bv 64 (pe_TAPE D)); C8 (Z_to_bv 64 (pe_SBUF D))] ->
    bytes_at usegs m (pe_TAPE D) (u64s (map (Z_to_bv 64) (pe_tws D))) -> bytes_at usegs m (pe_SBUF D) (map (Z_to_bv 8) (pe_sbs D)) ->
    OSX m (pe_OS D) -> LOCB m -> el_dcc m -> dmp_dcc m -> ssp_cells m (pe_canary D) ->
    rw_cells usegs m EL_TPLOC [C8 (MallocRep.wz EL_GLOC)] -> rw_cells usegs m LX_ERRNO [C4 errv] ->
    stk usegs m (pe_lo D) (pe_q D) -> mem_inv usegs m -> frm0 fc ->
    (forall (m1 : mem) (ty : Z) (j32 : list byte) (x1 x11 x12 x13 x14 : word), PINV [CB 32 j32] D m1 ->
       (ttype (T i) = t_false /\ ty = t_true \/ ttype (T i) <> t_false /\ ty = ttype (T i)) ->
       evt usegs K (DST i ty x1 gp t0 t1 t2 x11 x12 x13 x14 a5 a6 a7 t3 t4 t5 t6 F fc m1)) ->
    evt usegs K
      (MS (mkR (pe_ra D) (Z_to_bv 64 (pe_q D)) gp (Z_to_bv 64 RATP) t0 t1 t2 (pe_s0 D) (pe_s1 D) (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 (pe_DOC D)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
               (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D) t3 t4 t5 t6)
          F (Z_to_bv 64 DMP_PJ) fc None m (seg_rom usegs)).
  Proof.
    intros until errv. intros m i TIR DOCC TB SB OSXm LB DCC DCB SSP TPC ERR ST MI FRM HK. subst m i.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, DMP_PJ in *.
    assert (TTR : 0 <= ttype (T (pe_i D)) < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (munch_refl [(dsp D, pe_q D)] (pe_m0 D)) as MU. pose proof (wmono_refl usegs (pe_m0 D)) as WM.
    destruct OSXm as (pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK).
    destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold dmp_dcc, DMP_NPB_SLOT, DMP_NP_BOOL in DCB.
    hide OSC. hide TB. hide SB. hide C1. hide C2. hide C3. hide C4. hide C5. hide C6. hide DCB. hide LB. hide SSP. hide TPC. hide ERR. hide DOCC.

    step. carve_frame 192%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 192 junk [] [8; 32; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 15 hstep.
    unhide TB. unhide OSC. unhide SB. unhide C1. unhide C2. unhide C3. unhide C4. unhide C5. unhide C6. unhide DCB. unhide LB. unhide SSP. unhide TPC. unhide ERR. unhide DOCC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    Ltac tr AG H := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    tr AG DOCC.
    apply (bytes_at_agree _ _ _ _ _ AG) in TB; [| rewrite u64s_length, length_map; intros a Ha; cbn [outside]; clear - Ha T0 TH TI GLO LO; lia].
    pose proof (tape_read m1 (pe_TAPE D) (pe_tws D) (pe_i D) TB ltac:(lia)) as RDT.

    step. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia|]. clear KN.
    step. step. zstep. rewrite (land7_of_mod8 (pe_DOC D) ltac:(lia) D8). step. if_false.
    step. step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3a86c [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    step. astep. step.
    assert (DI1 : PINV [CB 32 (take 32 (drop 8 junk))] D m1).
    { lazymatch goal with MIx : mem_inv usegs m1, STx : stk usegs m1 _ _ |- _ =>
      split; [| split; [| split; [| split; [| split; [| split; [| split; [exact MIx| split; [exact STx| split; [do 4 eexists; unfold uframe, pjsaves; cbn [app]; exact FR|]]]]]]]]] end.
      - exists pb, pp, ep, fill, dum, j148, j284. split; [| split; [exact PUTI| exact FOK]].
        eapply rw_cells_agree; [exact AG| exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia.
      - eapply LOCB_transport; [exact LB| exact MU| exact WM|]. cbv [disjoint_from fst snd]. lia.
      - unfold el_dcc. split; [tr AG C1; exact C1|]. split; [tr AG C2; exact C2|]. split; [tr AG C3; exact C3|]. split; [tr AG C4; exact C4|].
        split; [tr AG C5; exact C5| tr AG C6; exact C6].
      - unfold dmp_dcc, DMP_NPB_SLOT, DMP_NP_BOOL. tr AG DCB. exact DCB.
      - tr AG TPC. exact TPC.
      - eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn [outside]. lia.
      - split; [exact TB|]. split.
        { apply (bytes_at_agree _ _ _ _ _ AG) in SB; [exact SB| rewrite length_map; intros a Ha; cbn [outside]; clear - Ha S0 SH SI GLO LO; lia]. }
        split; [exact DOCC|].
        split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, pj_W. cbn [outside]. intros x Hx. lia. }
        split; [exact WM|].
        exists errv. rewrite ELX in ERR |- *. tr AG ERR. exact ERR. }

    step. if_cases KF; zify_cond KF.
    - eapply evt_eq; [| eapply (HK m1 (ttype (T (pe_i D))) (take 32 (drop 8 junk))); [exact DI1| right; split; [unfold t_false; lia| reflexivity]]].
      unfold DST, DMP_PJ_DISPATCH. cbn. atp_st_eq.
    - step.
      eapply evt_eq; [| eapply (HK m1 t_true (take 32 (drop 8 junk))); [exact DI1| left; split; [unfold t_false; lia| reflexivity]]].
      unfold DST, DMP_PJ_DISPATCH, t_true. cbn. atp_st_eq.
  Qed.

  Section Leaves.
    Variable j32 : list byte.
    Notation lc := [CB 32 j32].
    Notation LCS := (junk32 j32).

  Lemma pj_putc40 : forall (K : machine_state -> Prop) (RA : Z) (gp t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (j0 r15 j56 j80 : list byte),
    PINV lc D m0 -> munch [(dsp D, dsp D + 88)] m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
    rw_cells usegs m (dsp D) ([CB 8 j0] ++ lc ++ [C1 (Z_to_bv 8 10); CB 15 r15; CB 8 j56; C8 (Z_to_bv 64 (pe_DOC D)); C8 (Z_to_bv 64 (pe_i D)); CB 8 j80]
                                ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)) ->
    0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), PINV lc D m' ->
       evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F (Z_to_bv 64 RA) fc None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (pe_OS D + 128))
                         (Z_to_bv 64 (dsp D + 40)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom usegs)).
  Proof.
    intros until j80. intros DI0 MU WM MI FR RAH RAE HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.

    pose proof FR as FRb. cbn [app] in FRb.
    apply (proj1 (rw_cells_app _ _ [_; _] _)) in FRb. destruct FRb as [_ FRb]. cbn [cells_size csize Nat.add] in FRb.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FRb. destruct FRb as [FRb _].
    destruct FRb as [[_ B1] _]. cbn [cells_bytes cbytes app] in B1.
    replace (dsp D + Z.of_nat 40) with (dsp D + 40) in B1 by lia.

    cbn [app] in FR. apply (rw_cells_merge usegs m _ [CB 8 j0; CB 32 j32] [C1 (Z_to_bv 8 10); CB 15 r15]) in FR. cbn [cells_size csize cells_bytes cbytes app Nat.add] in FR.
    pose proof (PINV_reframe lc LCS lc D m0 m j0 _ j56 j80 DOK DI0 MU WM MI FR) as DI.
    eapply (put_call lc LCS D DOK PUT) with (bs := [Z_to_bv 8 10]) (CAP := 1); [exact DI| exact B1| reflexivity| lia| lia| lia| right; right; lia|].
    intros m5 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI5.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RAH| exact RAE]).
    apply HK. exact DI5.
  Qed.

  Ltac open_frame DI FR := let X := fresh in pose proof DI as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & (? & ? & ? & ? & FR) & _); unfold uframe, pjsaves in FR; cbn [app] in FR.

  Lemma pj_null : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> frm0 fc -> T (pe_i D) = tword t_null 0 ->
    KEXIT lc K gp ->
    evt usegs K (DST (pe_i D) t_null x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM TY HK. unfold DST, DMP_PJ_DISPATCH, t_null.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. if_false. step. step. if_true. step. step. if_false. step. step. if_false.

    step. step. step. step. step.
    lit_at 0x10e1a 4%nat m MI LIT LITL.
    eapply (put_call lc LCS D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear MU WM LIT LITL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pose proof (munch_refl [(dsp D, dsp D + 88)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _). open_frame DI2 FR.
    apply (rw_cells_split_CB usegs _ _ [_; _] 16 _ _ [1; 15]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.

    step. hstep. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv usegs mx, MUx : munch _ m2 mx, WMx : wmono usegs m2 mx |- _ =>
      eapply (pj_putc40 K 0x3a9e4) with (m0 := m2); [exact DI2| exact MUx| exact WMx| exact MIx| cbn [app]; exact FR| lia| reflexivity|] end end.
    clear MU WM FR. intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 DI3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.

    step. unfold KEXIT, DMP_PJ_EXIT in HK. eapply HK; [exact DI3| exact FRM].
  Qed.

  Ltac pj_endl40 K DI m RA HK :=
    let MU := fresh "MU" in let WM := fresh "WM" in let FR := fresh "FR" in let MI := fresh "MI" in let X := fresh in
    pose proof (munch_refl [(dsp D, dsp D + 88)]%Z m) as MU; pose proof (wmono_refl usegs m) as WM;
    pose proof DI as X; destruct X as (_ & _ & _ & _ & _ & _ & MI & _);
    open_frame DI FR;
    apply (rw_cells_split_CB usegs _ _ [_; _] 16 _ _ [1; 15]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
    step; hstep; step; step; step;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv usegs mx, MUx : munch _ m mx, WMx : wmono usegs m mx |- _ =>
      eapply (pj_putc40 K RA) with (m0 := m); [exact DI| exact MUx| exact WMx| exact MIx| cbn [app]; exact FR| lia| reflexivity|] end end;
    clear MU WM FR;
    let m' := fresh "m" in let DI' := fresh "DI" in
    intros m' ? ? ? ? ? ? ? ? ? ? ? ? ? ? DI';
    pose proof (munch_refl ([] : list (Z * Z)) m') as MU; pose proof (wmono_refl usegs m') as WM;
    step; unfold KEXIT, DMP_PJ_EXIT in HK; eapply HK; [exact DI'| assumption].

  Lemma pj_bool : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> frm0 fc -> (T (pe_i D) = tword t_true 0 \/ T (pe_i D) = tword t_false 0) ->
    KEXIT lc K gp ->
    evt usegs K (DST (pe_i D) t_true x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM TY HK. unfold DST, DMP_PJ_DISPATCH, t_true.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) (pe_i D) TB ltac:(lia)) as RDT.

    step. step. if_false. step. step. if_false. step. step. if_true. step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3aaa8 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.
    destruct TY as [TY|TY]; rewrite TY in RDT; unfold tword, t_true, t_false in RDT.
    -
      step. step. astep. step. if_true. astep. astep. step. step.
      lazymatch goal with |- context [Z.b2z (?x <? 1)] => replace (Z.b2z (x <? 1)) with 1 by reflexivity end.
      eapply (insb_call lc LCS D DOK INSB); [exact DI| exact FRM| right; reflexivity|].
      clear MU WM RDT. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2. retlit.
      pj_endl40 K DI2 m2 0x3aae8 HK.
    -
      step. step. astep. step. if_false. step. step. step.
      eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3aac4 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
      intros ya1 ya2 ya3 ya4.
      astep. astep. step. step.
      lazymatch goal with |- context [Z.b2z (?x <? 1)] => replace (Z.b2z (x <? 1)) with 0 by reflexivity end.
      eapply (insb_call lc LCS D DOK INSB); [exact DI| exact FRM| left; reflexivity|].
      clear MU WM RDT. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2. retlit.
      pj_endl40 K DI2 m2 0x3aae8 HK.
  Qed.

  Lemma pj_i64 : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> frm0 fc -> pe_i D + 2 <= n -> T (pe_i D) = tword t_i64 0 ->
    KEXIT lc K gp ->
    evt usegs K (DST (pe_i D) t_i64 x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM IN TY HK. unfold DST, DMP_PJ_DISPATCH, t_i64.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) (pe_i D) TB ltac:(lia)) as RDT. rewrite TY in RDT. unfold tword, t_i64 in RDT.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) (pe_i D + 1) TB ltac:(lia)) as RDT1.

    step. step. if_false. step. step. if_true. step. step. if_true. step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3aaf8 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    step. step. astep. step. if_false. astep. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (pe_DOC D) (pe_TAPE D) (pe_i D + 1) 0x3ab14 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.

    step. step. step.
    replace (Z_to_bv 64 (T (pe_i D + 1))) with (Z_to_bv 64 ((T (pe_i D + 1) + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63))
      by (apply Z_to_bv64_eqm; rewrite Zminus_mod_idemp_l; f_equal; lia).
    eapply (ins_call lc LCS D DOK EL_INS_L _ INSL); [exact DI| exact FRM| cbv beta; pose proof (Z.mod_pos_bound (T (pe_i D + 1) + 2 ^ 63) (2 ^ 64) ltac:(lia)); lia|].
    clear MU WM RDT RDT1. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2. retlit.
    pj_endl40 K DI2 m2 0x3ab34 HK.
  Qed.

  Lemma pj_u64 : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> frm0 fc -> pe_i D + 2 <= n -> T (pe_i D) = tword t_u64 0 ->
    KEXIT lc K gp ->
    evt usegs K (DST (pe_i D) t_u64 x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM IN TY HK. unfold DST, DMP_PJ_DISPATCH, t_u64.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) (pe_i D) TB ltac:(lia)) as RDT. rewrite TY in RDT. unfold tword, t_u64 in RDT.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) (pe_i D + 1) TB ltac:(lia)) as RDT1.

    step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_true. step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3ab44 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    step. astep. step. if_false. astep. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (pe_DOC D) (pe_TAPE D) (pe_i D + 1) 0x3ab5c [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.

    step. step. step.
    replace (Z_to_bv 64 (T (pe_i D + 1))) with (Z_to_bv 64 ((T (pe_i D + 1)) mod 2 ^ 64)) by (apply Z_to_bv64_eqm; rewrite Z.mod_mod by lia; reflexivity).
    eapply (ins_call lc LCS D DOK EL_INS_UL _ INSUL); [exact DI| exact FRM| cbv beta; apply Z.mod_pos_bound; lia|].
    clear MU WM RDT RDT1. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2. retlit.
    pj_endl40 K DI2 m2 0x3ab7c HK.
  Qed.

  Lemma getd_cps : forall (K : machine_state -> Prop) (RA : Z) (gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> pe_i D + 2 <= n -> T (pe_i D) = tword t_dbl 0 -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (F' : bvmap 5 word) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), PINV lc D m' ->
       evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (Z_to_bv 64 RA) fc None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (dsp D + 64)) a1 a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x3b2e8) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros DI IN TY RAH RAE HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & ST & _ & TB & _ & DOCC & _). open_frame DI FR.
    pose proof (munch_refl [(dsp D - 16, dsp D)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide TB.

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    replace (pe_q D + -192 + -16) with (pe_q D + -208) in * by lia.
    hstep. hstep. step. step.
    unhide TB. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in TB; [| rewrite u64s_length, length_map; intros a Ha; cbn [outside]; clear - Ha T0 TH TI GLO LO; lia].
    pose proof (tape_read m1 (pe_TAPE D) (pe_tws D) (pe_i D) TB ltac:(lia)) as RDT. rewrite TY in RDT. unfold tword, t_dbl in RDT.
    pose proof (tape_read m1 (pe_TAPE D) (pe_tws D) (pe_i D + 1) TB ltac:(lia)) as RDT1.
    step. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia|]. clear KN.
    zstep. rewrite (land7_of_mod8 (pe_DOC D) ltac:(lia) D8). step. if_false.
    step. step.
    lazymatch goal with H : rw_cells usegs m1 (pe_DOC D) _ |- _ => rename H into DOCC1 end.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3b310 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC1| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    step. step. step. step. astep. zstep. rewrite (land7_of_mod8 (pe_DOC D) ltac:(lia) D8). astep. astep. astep.
    replace (0 <? pe_DOC D) with true by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z (0 <? 1))) with 1.
    step. if_false. step. if_false.

    step. astep. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (pe_DOC D) (pe_TAPE D) (pe_i D + 1) 0x3b348 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC1| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.

    step. step. step. step. step.
    lazymatch goal with H : stk usegs _ (pe_lo D) (pe_q D + -208) |- _ => release_frame FR0 H (dsp D) end.
    step.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RAH| exact RAE]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv usegs mx, MUx : munch _ m mx, WMx : wmono usegs m mx, STx : stk usegs mx _ _ |- _ =>
      eapply HK; eapply (PINV_below lc m mx 16 LCS DI ltac:(unfold DMP_PJ_LEAF; lia)); [| exact WMx| exact MIx| exact STx];
      eapply munch_weaken; [| exact MUx]; unfold sub_fp; cbn [outside]; intros xx Hxx; lia end end.
  Qed.

  Lemma pj_dbl : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> frm0 fc -> pe_i D + 2 <= n -> T (pe_i D) = tword t_dbl 0 ->
    KEXIT lc K gp ->
    evt usegs K (DST (pe_i D) t_dbl x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM IN TY HK. unfold DST, DMP_PJ_DISPATCH, t_dbl.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. if_true. step. step. if_true. step. step. if_false. step. step. if_false. astep. step.
    replace (dsp D + 64) with (dsp D + 64) by reflexivity.
    eapply (getd_cps K 0x3a98c); [exact DI| exact IN| exact TY| lia| reflexivity|].
    clear MU WM. intros m1 F1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 DI1.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.

    step. step.
    eapply (insd_call lc LCS D DOK INSD); [exact DI1| exact FRM|].
    clear MU WM. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2. retlit.
    pj_endl40 K DI2 m2 0x3a9a8 HK.
  Qed.

  Lemma PINV_reframe' : forall m m' k j0 out j56 j80, PINV lc D m -> 0 <= k <= DMP_PJ_LEAF ->
    munch [(dsp D - k, dsp D + 88)] m m' -> wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' (pe_lo D) (dsp D) ->
    rw_cells usegs m' (dsp D) (uframe D j0 lc out j56 j80) -> PINV lc D m'.
  Proof.
    intros m m' k j0' out' j56' j80' DI HK MU WM MI' ST' FR'.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & DCB & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU0 & WM0 & (errv & ERR)).
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    Ltac trc AG C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; cbn [outside]; lia].
    split. { exists pb, pp, ep, fill, dum, j148, j284. split; [| split; [exact PUTI| exact FOK]].
             eapply rw_cells_agree; [exact AG| exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia. }
    split; [eapply LOCB_transport; [exact LB| exact MU| exact WM|]; cbv [disjoint_from fst snd]; lia|].
    split. { destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
             split; [trc AG C1|]. split; [trc AG C2|]. split; [trc AG C3|]. split; [trc AG C4|]. split; [trc AG C5| trc AG C6]. }
    split; [unfold dmp_dcc, DMP_NPB_SLOT in *; trc AG DCB|].
    split; [trc AG TPC|].
    split; [eapply ssp_cells_agree; [exact AG| | exact SSP]; intros a Ha; unfold ssp_addr, got_ssp, ssp_guard in Ha; cbn [outside]; lia|].
    split; [exact MI'|]. split; [exact ST'|].
    split; [exists j0', out', j56', j80'; exact FR'|].
    split. { eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. cbn [outside]. clear - Ha T0 TH TI GLO LO HK. lia. }
    split. { eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. cbn [outside]. clear - Ha S0 SH SI GLO LO HK. lia. }
    split; [trc AG DOCC|].
    split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, pj_W. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Lemma tval_str : forall o, 0 <= o < 2^56 -> Z.land (tword t_str o) 72057594037927935 = o.
  Proof. intros o Ho. change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword, t_str; lia). unfold tword, t_str. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia. Qed.

  Lemma svh_cps : forall (K : machine_state -> Prop) (RA : Z) (gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (o l : Z),
    PINV lc D m -> Tf (pe_tws D) (pe_i D) = tword t_str o -> str_at (Tf (pe_sbs D)) (pe_sn D) o l -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (j0 j80 : list byte) (e4 : list byte) (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), PINV lc D m' ->
       rw_cells usegs m' (dsp D) ([CB 8 j0] ++ lc ++ [C8 (Z_to_bv 64 (pe_SBUF D + o + 4)); C8 (Z_to_bv 64 l); C4 (Z_to_bv 64 0); CB 4 e4;
                                     C8 (Z_to_bv 64 (pe_DOC D)); C8 (Z_to_bv 64 (pe_i D)); CB 8 j80]
                                  ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)) ->
       evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 b0 b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F (Z_to_bv 64 RA) fc None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (dsp D + 40)) (Z_to_bv 64 (dsp D + 64)) a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 0x3b19c) fc None m (seg_rom usegs)).
  Proof.
    intros until l. intros DI TY SA RAH RAE HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & ST & _ & TB & SB & DOCC & _). open_frame DI FR.
    pose proof (str_at_bounds _ _ SNR _ _ SA) as (O0 & L0 & OL & LE & O56).
    assert (TIR : 0 <= T (pe_i D) < 2^64) by (rewrite TY; unfold tword, t_str; lia).
    pose proof (munch_refl [(dsp D - 48, dsp D + 88)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    hide TB. hide SB.

    step. carve_frame 48%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [8; 8; 8; 8; 8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    replace (pe_q D + -192 + -48) with (pe_q D + -240) in * by lia.
    do 5 hstep.
    unhide TB. unhide SB. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in TB; [| rewrite u64s_length, length_map; intros a Ha; cbn [outside]; clear - Ha T0 TH TI GLO LO; lia].
    apply (bytes_at_agree _ _ _ _ _ (agree_on_of_munch _ _ _ MU WM)) in SB; [| rewrite length_map; intros a Ha; cbn [outside]; clear - Ha S0 SH SI GLO LO; lia].
    pose proof (tape_read_type m1 (pe_TAPE D) (pe_tws D) (pe_i D) TB ltac:(lia) TIR) as RTY. rewrite TY, ttype_tword in RTY by lia. unfold t_str in RTY.
    pose proof (tape_read m1 (pe_TAPE D) (pe_tws D) (pe_i D) TB ltac:(lia)) as RDT. rewrite TY in RDT.
    lazymatch goal with H : rw_cells usegs m1 (pe_DOC D) _ |- _ => rename H into DOCC1 end.

    step. step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
    step. zstep. rewrite (land7_of_mod8 (pe_DOC D) ltac:(lia) D8). step. if_false. step. step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3b1d8 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC1| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros xa1 xa2 xa3 xa4.

    step. step. step. if_false.
    step. step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|]. clear K2.
    zstep. rewrite (land7_of_mod8 (pe_DOC D) ltac:(lia) D8). step. if_false. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3b1fc [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC1| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros ya1 ya2 ya3 ya4.

    step. step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. clear K3.
    zstep. rewrite (land7_of_mod8 (pe_DOC D) ltac:(lia) D8). step. if_false.
    step. step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. clear K4.
    step. step. astep. astep. rewrite tval_str by lia. astep. astep.
    pose proof (sbuf_read1 m1 (pe_SBUF D) (pe_sbs D) o SB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m1 (pe_SBUF D) (pe_sbs D) (o + 1) SB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m1 (pe_SBUF D) (pe_sbs D) (o + 2) SB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m1 (pe_SBUF D) (pe_sbs D) (o + 3) SB ltac:(lia)) as RB3.
    assert (B0 : 0 <= S o < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B1 : 0 <= S (o + 1) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B2 : 0 <= S (o + 2) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B3 : 0 <= S (o + 3) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).

    step. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|]. clear K5.
    step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. clear K6.
    step. step. step.
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (pe_DOC D) (pe_TAPE D) (pe_i D) 0x3b240 [C8 (Z_to_bv 64 (pe_SBUF D))]);
      [exact DOCC1| exact T0| lia| lia| lia| exact T8| lia| lia| reflexivity| lia| reflexivity|].
    intros za1 za2 za3 za4.

    step. step. if_cases K7; zify_cond K7; [exfalso; rewrite ?unsigned_lit in K7 by lia; lia|]. clear K7.
    zstep. rewrite (land7_of_mod8 (pe_DOC D) ltac:(lia) D8). step. if_false.
    step. step. astep. rewrite tval_str by lia. astep.
    step. if_cases K8; zify_cond K8; [exfalso; rewrite ?unsigned_lit in K8 by lia; lia|]. clear K8.

    astep. astep. astep.
    replace (0 <? pe_SBUF D) with true by (symmetry; apply Z.ltb_lt; lia). replace (pe_SBUF D + o <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    change (Z.lxor (Z.b2z true) (Z.b2z false)) with 1.
    step. if_false. step. if_cases K9; zify_cond K9; [exfalso; rewrite ?unsigned_lit in K9 by lia; lia|]. clear K9.
    step. if_cases K10; zify_cond K10; [exfalso; rewrite ?unsigned_lit in K10 by lia; lia|]. clear K10.
    step.

    step. step. step. step. astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
    change (S o + 2 ^ 8 * S (o + 1) + 2 ^ 16 * S (o + 2) + 2 ^ 24 * S (o + 3)) with (le32 S o). rewrite LE.

    apply (rw_cells_split_CB usegs _ _ [_; _] 16 _ _ [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (rw_cells_split_CB usegs _ _ [_; _; _; _] 8 _ _ [4; 4]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    hstep. hstep. step. hstep.

    step. step. step. step. step. step.
    lazymatch goal with H : stk usegs _ (pe_lo D) (pe_q D + -240) |- _ => release_frame FR0 H (dsp D) end.
    step.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RAH| exact RAE]).
    replace (o + pe_SBUF D + 4) with (pe_SBUF D + o + 4) in FR by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv usegs mx, MUx : munch _ m mx, WMx : wmono usegs m mx, STx : stk usegs mx _ _ |- _ =>
      pose proof FR as FRm;
      apply (rw_cells_merge usegs mx _ [CB 8 _; CB 32 j32] [C8 _; C8 _]) in FRm; cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRm;
      apply (rw_cells_merge usegs mx _ [CB 8 _; CB 32 j32; CB 16 _] [C4 _; CB 4 _]) in FRm; cbn [cells_size csize cells_bytes cbytes app Nat.add] in FRm;
      eapply HK; [| exact FR];
      eapply (PINV_reframe' m mx 48); [exact DI| unfold DMP_PJ_LEAF; lia| | exact WMx| exact MIx| exact STx| exact FRm];
      eapply munch_weaken; [| exact MUx]; unfold sub_fp; cbn [outside]; intros xx Hxx; lia end end.
  Qed.

  Lemma pj_putc87 : forall (K : machine_state -> Prop) (RA : Z) (gp t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (j0 out j56 r7 : list byte),
    PINV lc D m0 -> munch [(dsp D, dsp D + 88)] m0 m -> wmono usegs m0 m -> mem_inv usegs m ->
    rw_cells usegs m (dsp D) ([CB 8 j0] ++ lc ++ [CB 16 out; CB 8 j56; C8 (Z_to_bv 64 (pe_DOC D)); C8 (Z_to_bv 64 (pe_i D)); CB 7 r7; C1 (Z_to_bv 8 10)]
                                ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)) ->
    0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), PINV lc D m' ->
       evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F (Z_to_bv 64 RA) fc None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (pe_OS D + 128))
                         (Z_to_bv 64 (dsp D + 87)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom usegs)).
  Proof.
    intros until r7. intros DI0 MU WM MI FR RAH RAE HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof FR as FRb. cbn [app] in FRb.
    apply (proj1 (rw_cells_app _ _ [_; _; _; _; _; _; _] _)) in FRb. destruct FRb as [_ FRb]. cbn [cells_size csize Nat.add] in FRb.
    apply (proj1 (rw_cells_app _ _ [_] _)) in FRb. destruct FRb as [FRb _].
    destruct FRb as [[_ B1] _]. cbn [cells_bytes cbytes app] in B1.
    replace (dsp D + Z.of_nat 87) with (dsp D + 87) in B1 by lia.
    cbn [app] in FR. apply (rw_cells_merge usegs m _ [CB 8 j0; CB 32 j32; CB 16 out; CB 8 j56; C8 (Z_to_bv 64 (pe_DOC D)); C8 (Z_to_bv 64 (pe_i D))] [CB 7 r7; C1 (Z_to_bv 8 10)]) in FR.
    cbn [cells_size csize cells_bytes cbytes app Nat.add] in FR.
    pose proof (PINV_reframe lc LCS lc D m0 m j0 out j56 _ DOK DI0 MU WM MI FR) as DI.
    eapply (put_call lc LCS D DOK PUT) with (bs := [Z_to_bv 8 10]) (CAP := 1); [exact DI| exact B1| reflexivity| lia| lia| lia| right; right; lia|].
    intros m5 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI5.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RAH| exact RAE]).
    apply HK. exact DI5.
  Qed.

  Lemma pj_str : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> frm0 fc -> is_str T S sn (pe_i D) ->
    KEXIT lc K gp ->
    evt usegs K (DST (pe_i D) t_str x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros DI FRM STRI HK. unfold DST, DMP_PJ_DISPATCH, t_str.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & O8 & D8 & IR & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _).
    destruct STRI as (o & l & TY & SA). pose proof (str_at_bounds _ _ SNR _ _ SA) as (O0 & L0 & OL & LE & O56).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. if_true. step. step. if_false. step. step. if_true. astep. astep. step.
    eapply (svh_cps K 0x3a9f4); [exact DI| exact TY| exact SA| lia| reflexivity|].
    clear MU WM. intros m1 j0 j80 e4 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 DI1 FR1. cbn [app] in FR1.
    pose proof DI1 as (_ & _ & _ & _ & _ & _ & MI1 & _ & _ & _ & SB1 & _).
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.

    step. step. step. step.
    destruct (sbuf_slice m1 (pe_SBUF D) (pe_sbs D) o l SB1 ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
    eapply (put_call lc LCS D DOK PUT); [exact DI1| exact QB| exact QL| lia| lia| lia| left; lia|].
    clear MU WM QB QL FR1. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pose proof (munch_refl [(dsp D, dsp D + 88)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    pose proof DI2 as (_ & _ & _ & _ & _ & _ & MI2 & _). open_frame DI2 FR.
    apply (rw_cells_split_CB usegs _ _ [_; _; _; _; _; _] 8 _ _ [7; 1]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.

    step. hstep. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv usegs mx, MUx : munch _ m2 mx, WMx : wmono usegs m2 mx |- _ =>
      eapply (pj_putc87 K 0x3aa18) with (m0 := m2); [exact DI2| exact MUx| exact WMx| exact MIx| cbn [app]; exact FR| lia| reflexivity|] end end.
    clear MU WM FR. intros m3 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 DI3.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    step. unfold KEXIT, DMP_PJ_EXIT in HK. eapply HK; [exact DI3| exact FRM].
  Qed.
  End Leaves.
End Body.
End WithCeiling0.

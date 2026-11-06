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
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjDmp.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_objl Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_defs Dmp_defs Dmp_pj_iface Dmp_pj_kit.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
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

  Definition KEXIT (lc : list cell) (K : machine_state -> Prop) (gp : word) : Prop :=
    forall (m' : mem) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      PINV lc D m' -> frm0 fc' ->
      evt psegs K (MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                      F' (Z_to_bv 64 DMP_PJ_EXIT) fc' None m' (seg_rom psegs)).

  Definition DST (i ty : Z) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 (pe_DOC D))
            (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 (T i)) (Z_to_bv 64 (pe_TAPE D + 8 * i)) (Z_to_bv 64 ty) (Z_to_bv 64 102) x15 x16 x17
            (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D) x28 x29 x30 x31)
       F (Z_to_bv 64 DMP_PJ_DISPATCH) fc None m (seg_rom psegs).

  Ltac open_frame DI FR scr := let X := fresh in pose proof DI as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & (scr & FR) & _); unfold pjsaves in FR; cbn [app] in FR.

  Lemma pj_exit : forall (lc : list cell) (x1 gp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    cells_size lc = 32%nat -> PINV lc D m -> frm0 fc ->
    evt psegs (pj_post (pe_ra D) (pe_q D) gp (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)
                       (pe_lo D) (pe_OS D) (pe_canary D) (pe_m0 D))
      (MS (mkR x1 (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DMP_PJ_EXIT) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros LCS DI FRM.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, DMP_PJ_EXIT in *.
    pose proof DI as (OSXm & LB & DCC & DCB & TPC & SSP & MI & ST & (scr & FR) & TB & SB & DOCC & MU0 & WM0 & (errv & ERR)).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.

    destruct (proj1 (rw_cells_app m (dsp D) (lc ++ [CB 8 scr]) _) ltac:(rewrite <- app_assoc; exact FR)) as [F12 F3].
    destruct (rw_cells_forget _ _ _ _ F12) as [j40 F12']. rewrite cells_size_app, LCS in F12', F3. cbn [cells_size csize Nat.add] in F12', F3.
    pose proof (proj2 (rw_cells_app m (dsp D) [CB 40 j40] _) (conj F12' F3)) as FRJ. cbn [app cells_size csize] in FRJ. unfold pjsaves in FRJ. clear F12 F3 F12' FR.

    do 13 step. step. release_frame FRJ ST (pe_q D). step.
    replace (Z_to_bv 64 (dsp D + 144)) with (Z_to_bv 64 (pe_q D)) by (f_equal; lia).
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

  Lemma pj_enter : forall (K : machine_state -> Prop) (gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (i : Z) (errv : word),
    let m := pe_m0 D in
    0 <= i < n -> 0 <= T i < 2^64 ->
    rw_cells psegs m (pe_DOC D) [C8 (Z_to_bv 64 (pe_TAPE D)); C8 (Z_to_bv 64 (pe_SBUF D))] ->
    bytes_at psegs m (pe_TAPE D) (u64s (map (Z_to_bv 64) (pe_tws D))) -> bytes_at psegs m (pe_SBUF D) (map (Z_to_bv 8) (pe_sbs D)) ->
    OSX m (pe_OS D) -> LOCB m -> el_dcc m -> dmp_dcc m -> ssp_cells m (pe_canary D) ->
    rw_cells psegs m EL_TPLOC [C8 (MallocRep.wz EL_GLOC)] -> rw_cells psegs m LX_ERRNO [C4 errv] ->
    stk psegs m (pe_lo D) (pe_q D) -> mem_inv psegs m -> frm0 fc ->
    (forall (m1 : mem) (ty : Z) (j32 : list byte), PINV [CB 32 j32] D m1 ->
       (ttype (T i) = t_false /\ ty = t_true \/ ttype (T i) <> t_false /\ ty = ttype (T i)) ->
       evt psegs K (DST i ty (pe_ra D) gp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc m1)) ->
    evt psegs K
      (MS (mkR (pe_ra D) (Z_to_bv 64 (pe_q D)) gp (Z_to_bv 64 RATP) t0 t1 t2 (pe_s0 D) (pe_s1 D) (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 (pe_DOC D)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
               (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D) t3 t4 t5 t6)
          F (Z_to_bv 64 DMP_PJ) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros m Hi TIR DOCC TB SB OSXm LB DCC DCB SSP TPC ERR ST MI FRM HK. subst m.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF, DMP_PJ in *.
    assert (TTR : 0 <= ttype (T i) < 256) by (unfold ttype; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (munch_refl [(dsp D, pe_q D)] (pe_m0 D)) as MU. pose proof (wmono_refl psegs (pe_m0 D)) as WM.
    destruct OSXm as (pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK).
    destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold dmp_dcc, DMP_NPB_SLOT, DMP_NP_BOOL in DCB.
    hide OSC. hide TB. hide SB. hide C1. hide C2. hide C3. hide C4. hide C5. hide C6. hide DCB. hide LB. hide SSP. hide TPC. hide ERR. hide DOCC.

    step. carve_frame 144%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 144 junk [] [32; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 13 hstep.
    unhide TB. unhide OSC. unhide SB. unhide C1. unhide C2. unhide C3. unhide C4. unhide C5. unhide C6. unhide DCB. unhide LB. unhide SSP. unhide TPC. unhide ERR. unhide DOCC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    Ltac tr AG H := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
    tr AG DOCC.
    apply (bytes_at_agree _ _ _ _ _ AG) in TB; [| rewrite u64s_length, length_map; intros a Ha; cbn [outside]; clear - Ha T0 TH TI GLO LO; lia].
    pose proof (tape_read m1 (pe_TAPE D) (pe_tws D) i TB ltac:(lia)) as RDT.

    step. step. step. astep. astep. step. astep. step. step.
    assert (DI1 : PINV [CB 32 (take 32 junk)] D m1).
    { lazymatch goal with MIx : mem_inv psegs m1, STx : stk psegs m1 _ _ |- _ =>
      split; [| split; [| split; [| split; [| split; [| split; [| split; [exact MIx| split; [exact STx| split; [eexists; unfold pjsaves; cbn [app]; exact FR|]]]]]]]]] end.
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
    -
      eapply evt_eq; [| eapply (HK m1 (ttype (T i)) (take 32 junk)); [exact DI1| right; split; [unfold t_false; lia| reflexivity]]].
      unfold DST, DMP_PJ_DISPATCH. cbn. atp_st_eq.
    -
      step.
      eapply evt_eq; [| eapply (HK m1 t_true (take 32 junk)); [exact DI1| left; split; [unfold t_false; lia| reflexivity]]].
      unfold DST, DMP_PJ_DISPATCH, t_true. cbn. atp_st_eq.
  Qed.

  Section Leaves.

    Variable j32 : list byte.
    Notation lc := [CB 32 j32].
    Notation LCS := (junk32 j32).

  Lemma pj_putc : forall (K : machine_state -> Prop) (RA k : Z) (gp t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (csA csB : list cell),
    PINV lc D m0 -> munch [(dsp D + 32, dsp D + 40)] m0 m -> wmono psegs m0 m -> mem_inv psegs m ->
    rw_cells psegs m (dsp D) (lc ++ (csA ++ C1 (Z_to_bv 8 10) :: csB) ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)) ->
    cells_size (csA ++ C1 (Z_to_bv 8 10) :: csB) = 8%nat -> k = 32 + Z.of_nat (cells_size csA) -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), PINV lc D m' ->
       evt psegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F (Z_to_bv 64 RA) fc None m' (seg_rom psegs))) ->
    evt psegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (pe_OS D + 128))
                         (Z_to_bv 64 (dsp D + k)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                         x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom psegs)).
  Proof.
    intros until csB. intros DI0 MU WM MI FR SZ HK8 RAH RAE HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof (PINV_rescratch lc LCS D m0 m _ DOK DI0 MU WM MI SZ FR) as DI.
    pose proof (frame_scratch lc LCS D m _ SZ FR) as SCR.
    destruct (proj1 (rw_cells_app _ _ csA _) SCR) as [_ SC2].
    destruct (proj1 (rw_cells_app _ _ [_] csB) SC2) as [[[_ B1] _] _]. cbn [cells_bytes cbytes app] in B1.
    rewrite cells_size_app in SZ. cbn [cells_size csize] in SZ.
    replace (dsp D + 32 + Z.of_nat (cells_size csA)) with (dsp D + k) in B1 by lia.
    eapply (put_call lc LCS D DOK PUT) with (bs := [Z_to_bv 8 10]) (CAP := 1); [exact DI| exact B1| reflexivity| lia| lia| lia| right; right; lia|].
    intros m5 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 DI5.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RAH| exact RAE]).
    apply HK. exact DI5.
  Qed.

  Ltac pj_endl_tac DI m A B HK :=
    let MU := fresh "MU" in let WM := fresh "WM" in let FR := fresh "FR" in let scr := fresh "scr" in
    pose proof (munch_refl [(dsp D + 32, dsp D + 40)]%Z m) as MU; pose proof (wmono_refl psegs m) as WM;
    let MI := fresh "MI" in let X := fresh in pose proof DI as X; destruct X as (_ & _ & _ & _ & _ & _ & MI & _);
    open_frame DI FR scr;
    apply (rw_cells_split_CB psegs _ _ [_] 8 scr _ [A; 1; B]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;

    step; hstep; step; step; step;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MIx : mem_inv psegs mx, MUx : munch _ m mx, WMx : wmono psegs m mx |- _ =>
      eapply (pj_putc _ _ _) with (m0 := m) (csA := [CB A (take A scr)]) (csB := [CB B (take B (drop 1 (drop A scr)))]);
        [exact DI| exact MUx| exact WMx| exact MIx| exact FR| reflexivity| reflexivity| lia| reflexivity|] end end;
    clear MU WM FR;
    let m' := fresh "m" in let DI' := fresh "DI" in
    intros m' ? ? ? ? ? ? ? ? ? ? ? ? ? ? DI';

    pose proof (munch_refl ([] : list (Z * Z)) m') as MU; pose proof (wmono_refl psegs m') as WM;
    step; eapply HK; [exact DI'| assumption].

  Lemma pj_null : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (i : Z),
    PINV lc D m -> frm0 fc -> 0 <= i < n -> T i = tword t_null 0 ->
    KEXIT lc K gp ->
    evt psegs K (DST i t_null x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until i. intros DI FRM Hi TY HK. unfold DST, DMP_PJ_DISPATCH, t_null.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.

    step. step. if_false. step. step. if_true. step. step. if_false. step. step. if_false.

    step. step. step. step. step.
    lit_at 0x10e1a 4%nat m MI LIT LITL.
    eapply (put_call lc LCS D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit. clear MU WM LIT LITL.
    pj_endl_tac DI2 m2 6%nat 1%nat HK.
  Qed.

  Lemma pj_bool : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (i : Z),
    PINV lc D m -> frm0 fc -> 0 <= i < n -> (T i = tword t_true 0 \/ T i = tword t_false 0) ->
    KEXIT lc K gp ->
    evt psegs K (DST i t_true x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until i. intros DI FRM Hi TY HK. unfold DST, DMP_PJ_DISPATCH, t_true.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    destruct TY as [TY|TY]; rewrite TY; unfold tword, t_true, t_false.
    all:
         step; step; if_false; step; step; if_false; step; step; if_true.
    all:
         step; astep; astep; astep; step; step.
    1: replace (Z.b2z (0 <? 1)) with 1 by reflexivity.
    2: lazymatch goal with |- context [Z.b2z (?x <? 1)] => replace (Z.b2z (x <? 1)) with 0 by reflexivity end.
    1: eapply (insb_call lc LCS D DOK INSB); [exact DI| exact FRM| right; reflexivity|].
    2: eapply (insb_call lc LCS D DOK INSB); [exact DI| exact FRM| left; reflexivity|].
    all: clear MU WM; intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2; retlit.
    all: pj_endl_tac DI2 m2 5%nat 2%nat HK.
  Qed.

  Lemma pj_i64 : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (i : Z),
    PINV lc D m -> frm0 fc -> 0 <= i -> i + 2 <= n -> T i = tword t_i64 0 ->
    KEXIT lc K gp ->
    evt psegs K (DST i t_i64 x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until i. intros DI FRM I0 IN TY HK. unfold DST, DMP_PJ_DISPATCH, t_i64.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) (i + 1) TB ltac:(lia)) as RDT.
    rewrite TY. unfold tword, t_i64.

    step. step. if_false. step. step. if_true. step. step. if_true.

    step. astep. step. if_false. step. step. step.
    replace (Z_to_bv 64 (T (i + 1))) with (Z_to_bv 64 ((T (i + 1) + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63))
      by (apply Z_to_bv64_eqm; rewrite Zminus_mod_idemp_l; f_equal; lia).
    eapply (ins_call lc LCS D DOK EL_INS_L _ INSL); [exact DI| exact FRM| cbv beta; pose proof (Z.mod_pos_bound (T (i + 1) + 2 ^ 63) (2 ^ 64) ltac:(lia)); lia|].
    clear MU WM RDT. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2. retlit.
    pj_endl_tac DI2 m2 1%nat 6%nat HK.
  Qed.

  Lemma pj_u64 : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (i : Z),
    PINV lc D m -> frm0 fc -> 0 <= i -> i + 2 <= n -> T i = tword t_u64 0 ->
    KEXIT lc K gp ->
    evt psegs K (DST i t_u64 x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until i. intros DI FRM I0 IN TY HK. unfold DST, DMP_PJ_DISPATCH, t_u64.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) (i + 1) TB ltac:(lia)) as RDT.
    rewrite TY. unfold tword, t_u64.

    step. step. if_false. step. step. if_false. step. step. if_false. step. step. if_true.

    astep. step. if_false. step. step. step.
    replace (Z_to_bv 64 (T (i + 1))) with (Z_to_bv 64 ((T (i + 1)) mod 2 ^ 64)) by (apply Z_to_bv64_eqm; rewrite Z.mod_mod by lia; reflexivity).
    eapply (ins_call lc LCS D DOK EL_INS_UL _ INSUL); [exact DI| exact FRM| cbv beta; apply Z.mod_pos_bound; lia|].
    clear MU WM RDT. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2. retlit.
    pj_endl_tac DI2 m2 2%nat 5%nat HK.
  Qed.

  Lemma pj_dbl : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (i : Z),
    PINV lc D m -> frm0 fc -> 0 <= i -> i + 2 <= n -> T i = tword t_dbl 0 ->
    KEXIT lc K gp ->
    evt psegs K (DST i t_dbl x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until i. intros DI FRM I0 IN TY HK. unfold DST, DMP_PJ_DISPATCH, t_dbl.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (tape_read m (pe_TAPE D) (pe_tws D) (i + 1) TB ltac:(lia)) as RDT.
    rewrite TY. unfold tword, t_dbl.

    step. step. if_true. step. step. if_true. step. step. if_false. step. step. if_false.

    step. astep. step. if_false. step. step. step.
    eapply (insd_call lc LCS D DOK INSD); [exact DI| exact FRM|].
    clear MU WM RDT. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F2 fc2 DI2 FRM2. retlit.
    pj_endl_tac DI2 m2 3%nat 4%nat HK.
  Qed.

  Lemma sbuf_slice : forall m (SBUF : Z) (sbs : list Z) (o l : Z),
    bytes_at psegs m SBUF (map (Z_to_bv 8) sbs) -> 0 <= o -> 0 <= l -> o + 4 + l < Z.of_nat (length sbs) ->
    bytes_at psegs m (SBUF + o + 4) (firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) sbs)))
    /\ Z.of_nat (length (firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) sbs)))) = l.
  Proof.
    intros m SBUF sbs o l HB Ho Hl Hol. split.
    - replace (SBUF + o + 4) with (SBUF + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
    - rewrite firstn_length_le; [lia|]. rewrite length_skipn, length_map. lia.
  Qed.

  Lemma pj_str : forall (K : machine_state -> Prop) (x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (i : Z),
    PINV lc D m -> frm0 fc -> 0 <= i -> i + 1 <= n -> is_str T S sn i ->
    KEXIT lc K gp ->
    evt psegs K (DST i t_str x1 gp x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until i. intros DI FRM I0 IN STR HK. unfold DST, DMP_PJ_DISPATCH, t_str.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & MI & _ & _ & TB & SB & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (key_word_range _ _ _ _ STR SNR) as (KWR & KM & KT).
    destruct (is_str_read _ _ _ SNR _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ SNR _ _ SA) as (O0 & L0 & OL & LE & O56).
    set (o := tval (T i)) in *.

    step. step. if_true. step. step. if_false. step. step. if_true.

    astep. rewrite KT. step. if_false.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) o SB ltac:(lia)) as RB0.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 1) SB ltac:(lia)) as RB1.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 2) SB ltac:(lia)) as RB2.
    pose proof (sbuf_read1 m (pe_SBUF D) (pe_sbs D) (o + 3) SB ltac:(lia)) as RB3.
    assert (B0 : 0 <= S o < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B1 : 0 <= S (o + 1) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B2 : 0 <= S (o + 2) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
    assert (B3 : 0 <= S (o + 3) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).

    step. astep. astep. rewrite KM. astep.

    step. step. step. step. astep. astep. astep. astep. astep. astep. astep.
    rewrite !land64_shl_small by lia. rewrite le32_of_lbu4 by lia.
    change (S o + 2 ^ 8 * S (o + 1) + 2 ^ 16 * S (o + 2) + 2 ^ 24 * S (o + 3)) with (le32 S o). rewrite LE.

    step. step. step.
    destruct (sbuf_slice m (pe_SBUF D) (pe_sbs D) o l SB ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
    eapply (put_call lc LCS D DOK PUT); [exact DI| exact QB| exact QL| lia| lia| lia| left; lia|].
    clear MU WM RB0 RB1 RB2 RB3 QB QL. intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 DI2. retlit.
    pj_endl_tac DI2 m2 4%nat 3%nat HK.
  Qed.
  End Leaves.
End Body.
End WithCeiling0.

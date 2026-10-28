(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Atp_objl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_h_defs Pj_loc_defs Pj_loc_get Pj_os_defs Pj_relro El_os_defs El_ins_iface El_esc_iface El_defs El_dump_iface El_dump_kit El_dump_body1 El_dump_body2 El_dump_loop.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac open_framel DI FR scr := let X := fresh in pose proof DI as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & (scr & FR) & _); unfold dlits, dsaves in FR; cbn [app] in FR.

Lemma tape_land7 : forall x : Z, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact H. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Top.
  Variable D : denv.
  Variable j0 : list byte.
  Hypothesis DOK : denv_ok D.
  Hypothesis PUT : os_putX_stmt.
  Hypothesis IUL : ins_ul_stmt.
  Hypothesis IU : ins_u_stmt.
  Hypothesis IL : ins_l_stmt.
  Hypothesis INSD : ins_d_stmt.
  Hypothesis ESC : esc_stmt.

  Notation n := (Z.of_nat (length (de_tws D))).
  Notation T := (Tf (de_tws D)).

  Lemma dump_exit : forall gp : word,
    KLOOP D j0 (dump_post (de_ra D) (de_q D) gp (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D) (de_s7 D) (de_s8 D)
                       (de_s9 D) (de_s10 D) (de_s11 D) (de_lo D) (de_OS D) (de_m0 D)) gp (n - 1).
  Proof.
    intros gp. unfold KLOOP. intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 F fc DI FRM.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof WF as (NR & SNR & _ & TR0 & _).
    assert (TR : 0 <= T (n - 1) < 2^64) by (rewrite TR0; apply tword_range; unfold t_root; lia).
    eapply (dump_head D j0 DOK PUT IUL); [exact DI| exact FRM| lia| exact TR|].
    clear m x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x24 x28 x29 x30 x31 F fc DI FRM.
    intros m x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x21' x28 x29 x30 x31 F fc DI FRM.
    rewrite TR0, ttype_tword by lia. unfold t_root.
    pose proof DI as (OSX1 & LB & DCC & TPC & SSP & MI & ST & _ & TB & SB & DOCC & MU0 & WM0 & ERR). open_framel DI FR scr.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_true. step. if_false. step. step. if_false. step. step. step. if_false. step. if_true.

    do 13 step. step. release_frame FR ST (de_q D). step.
    apply evt_done. unfold dump_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m.
    split; [symmetry; atp_st_eq|]. split; [exact FRM|]. split; [exact MU0|]. split; [exact WM0|]. split; [exact MI|]. split; [exact ST|].
    split. { destruct OSX1 as (pb & pp & ep & fill & dum & j148 & j284 & OSC & _). exists pb, (Z_to_bv 64 pp), (Z_to_bv 64 ep), fill, dum, j148, j284.
             rewrite os_cells_X. exact OSC. }
    split; [exact TPC|]. split; [exact ERR| exact LB].
  Qed.

  Lemma land56_tword : forall t v, 0 <= t -> 0 <= v < 2^56 -> Z.land (tword t v) 72057594037927935 = v.
  Proof.
    intros t v Ht Hv. change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword; lia).
    unfold tword. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
  Qed.

  Lemma dump_hdr : forall (K : machine_state -> Prop) (j72 : list byte) (gp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV [CB 72 j72] D m -> frm0 fc -> KLOOP D (take 8 j72) K gp 1 ->
    evt usegs K (MS (mkR (de_ra D) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 (de_s0 D) (de_s1 D) (Z_to_bv 64 (de_DOC D)) (Z_to_bv 64 (de_OS D + 128))
                         a2 a3 a4 a5 a6 a7 (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D) (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D) t3 t4 t5 t6)
                    F (Z_to_bv 64 0x3ffb0) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros DI FRM HK.
    assert (LC72 : cells_size [CB 72 j72] = 72%nat) by reflexivity.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof WF as (NR & SNR & TR0 & _).
    assert (TR : 0 <= T 0 < 2^64) by (rewrite TR0; apply tword_range; unfold t_root; lia).
    pose proof DI as (_ & _ & _ & _ & _ & MI & _ & _ & TB & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (tape_read m (de_TAPE D) (de_tws D) 0 TB ltac:(lia)) as RDT.
    pose proof RDT as RDT'. rewrite Z.mul_0_r, Z.add_0_r in RDT'.

    step. step. step. if_lia. step. astep.
    rewrite (tape_land7 (de_TAPE D) TAL).
    step. if_false. step. step. step.
    eapply (ins_call [CB 72 j72] LC72 D DOK EL_INS_UL _ IUL); [exact DI| exact FRM| cbv beta; lia|].
    clear m MI TB DOCC MU WM RDT RDT' DI FRM. intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 DI FRM. retlit.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    astep. astep. step. step.
    lit_at 0x10c45 3%nat m MI LIT LITL.
    eapply (put_call [CB 72 j72] LC72 D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear m MI MU WM LIT LITL DI u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6. intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 DI. retlit.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). pose proof (munch_refl [(dsp D + 72, dsp D + 88)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    open_framel DI FR scr.
    apply (rw_cells_split_CB usegs _ _ [_] 16 scr _ [1; 15]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.

    astep.
    change (T 0 / 2 ^ 56) with (ttype (T 0)). rewrite TR0, ttype_tword by lia. unfold t_root in *.
    hstep. astep. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv usegs mx |- _ =>
        pose proof (DINV_rescratch [CB 72 j72] LC72 D m mx [C1 (Z_to_bv 8 114); CB 15 (take 15 (drop 1 scr))] DOK DI MU WM MIx eq_refl FR) as DI4;
        pose proof (frame_scratch [CB 72 j72] LC72 D mx [C1 (Z_to_bv 8 114); CB 15 (take 15 (drop 1 scr))] eq_refl FR) as SCR end end.
    destruct (proj1 (rw_cells_app _ _ [_] _) SCR) as [[[_ B1] _] _]. cbn [cells_bytes cbytes app] in B1.
    eapply (put_call [CB 72 j72] LC72 D DOK PUT) with (bs := [Z_to_bv 8 114]) (CAP := 1); [exact DI4| exact B1| reflexivity| lia| lia| lia| right; right; lia|].
    clear m MI MU WM DI FR SCR B1 DI4 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6. intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 DI. retlit.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. if_false. astep. astep. step. step. step.
    lit_at 0x10845 16%nat m MI LIT LITL.
    eapply (put_call [CB 72 j72] LC72 D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear m MI MU WM LIT LITL DI u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6. intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 DI. retlit.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. astep. astep.
    rewrite (land56_tword 114 n) by lia.
    step. step.
    eapply (ins_call [CB 72 j72] LC72 D DOK EL_INS_UL _ IUL); [exact DI| exact FRM| cbv beta; lia|].
    clear m MI MU WM DI FRM F1 fc1 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6. intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 DI FRM. retlit.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    astep. astep. step. step.
    lit_at 0x10aac 25%nat m MI LIT LITL.
    eapply (put_call [CB 72 j72] LC72 D DOK PUT); [exact DI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear m MI MU WM LIT LITL DI u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6. intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 DI. retlit.
    pose proof DI as (_ & _ & _ & _ & _ & MI & _). pose proof (munch_refl [(dsp D, dsp D + 88)] m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. step. if_cases KB; zify_cond KB; [exfalso; rewrite ?unsigned_lit in KB by lia; lia|].

    astep. astep. astep. astep. step. step. astep. astep. astep. astep. astep. astep. step.

    clear scr. open_framel DI FR scr.
    apply (rw_cells_split_CB usegs _ _ [] 72 j72 _ [8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    astep. astep. hstep. astep. do 7 (astep; hstep).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv usegs mx |- _ =>
        pose proof (DINV_reframe (dlits (take 8 j72)) (dlits72 (take 8 j72)) [CB 72 j72] D m mx [CB 16 scr] DOK DI MU WM MIx eq_refl FR) as DI9 end end.
    eapply evt_eq; [| eapply HK; [exact DI9| exact FRM]]. unfold LST. atp_st_eq.
  Qed.
End Top.

Lemma el_dcc_of_consts : forall m, pj_consts m -> el_dcc m.
Proof.
  intros m (_ & _ & _ & _ & _ & RN).
  relro_chunk RN m constr:(0xd68d8%Z) [C8 (Z_to_bv 64 0x82530); C8 (Z_to_bv 64 0x3fdcc); C8 (Z_to_bv 64 8)] H1.
  relro_chunk RN m constr:(0xda1c0%Z) [C8 (Z_to_bv 64 0xa9050); C8 (Z_to_bv 64 0xa9058)] H2.
  relro_chunk RN m constr:(0xdad70%Z) [C8 (Z_to_bv 64 0x8da74); C8 (Z_to_bv 64 0x8dd20); C8 (Z_to_bv 64 0x8dfcc); C8 (Z_to_bv 64 0x8e254); C8 (Z_to_bv 64 0x8e4dc)] H3.
  relro_chunk RN m constr:(0xda358%Z) [C8 (Z_to_bv 64 0xac23c); C8 (Z_to_bv 64 0xac24c); C8 (Z_to_bv 64 0xac25c)] H4.
  relro_chunk RN m constr:(0xdc418%Z) [C8 (Z_to_bv 64 0xede08)] H5.
  relro_chunk RN m constr:(0xdc370%Z) [C8 (Z_to_bv 64 0xee080)] H6.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
Qed.

Theorem dump_of_parts : os_putX_stmt -> ins_ul_stmt -> ins_u_stmt -> ins_l_stmt -> ins_d_stmt -> esc_stmt -> dump_stmt.
Proof.
  intros PUT IUL IU IL INSD ESC. unfold dump_stmt.
  intros ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q lo OS DOC TAPE SBUF tws sbs canary errv.
  intros WF SBS DOCC QD OSD DH TB T0 T8 TH TI SB S0 SH SI OSF QOS OSH OAL LB PJC SSP TPC ERR ST LO GLO AL MI FRM.
  unfold GLOBALS_TOP, EL_DUMP_STACK, EL_DUMP in *.
  set (D := mkDE q lo OS DOC TAPE SBUF tws sbs canary m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  assert (DOK : denv_ok D). { unfold denv_ok; cbn; unfold GLOBALS_TOP, EL_DUMP_STACK. split; [exact WF|]. repeat split; first [assumption| lia]. }
  pose proof (el_dcc_of_consts m PJC) as DCC. rewrite ELX in ERR.
  pose proof (munch_refl [(q - 192, q)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  hide TB. hide SB. hide DCC. hide LB. hide SSP.

  step. carve_frame 192%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 192 junk [] [72; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 hstep.
  unhide TB. unhide SB. unhide DCC. unhide LB. unhide SSP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MIx : mem_inv usegs mx |- _ =>
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG;
  assert (DI : DINV [CB 72 (take 72 junk)] D mx);
  [ split; [| split; [| split; [| split; [| split; [| split; [exact MIx| split; [exact ST| split; [eexists; exact FR|]]]]]]]]
  | eapply evt_eq; [| eapply (dump_hdr D DOK PUT IUL _ (take 72 junk) gp); [exact DI| exact FRM| apply (dump_root D _ DOK PUT IUL IU IL INSD ESC); apply (dump_exit D _ DOK PUT IUL)]];
    cbn; atp_st_eq ] end end.
  - destruct OSF as (dum & j148 & j284 & OSC). exists (Z_to_bv 64 0), 0, 0, (0xffffffff), dum, j148, j284. unfold D; cbn [de_q de_lo de_OS de_DOC de_TAPE de_SBUF de_tws de_sbs de_canary de_m0 de_ra de_s0 de_s1 de_s2 de_s3 de_s4 de_s5 de_s6 de_s7 de_s8 de_s9 de_s10 de_s11].
    split; [| split; [left; lia| left; reflexivity]].
    eapply rw_cells_agree; [exact AG| rewrite <- os_cells_X; exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia.
  - eapply LOCB_transport; [exact LB| exact MU| exact WM|]. cbv [disjoint_from fst snd]. lia.
  - destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    Ltac trd3 AG C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; cbn [outside]; lia].
    split; [trd3 AG C1|]. split; [trd3 AG C2|]. split; [trd3 AG C3|]. split; [trd3 AG C4|]. split; [trd3 AG C5| trd3 AG C6].
  - exact TPC.
  - unfold D; cbn [de_q de_lo de_OS de_DOC de_TAPE de_SBUF de_tws de_sbs de_canary de_m0 de_ra de_s0 de_s1 de_s2 de_s3 de_s4 de_s5 de_s6 de_s7 de_s8 de_s9 de_s10 de_s11]. eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn [outside]. lia.
  - unfold D; cbn [de_q de_lo de_OS de_DOC de_TAPE de_SBUF de_tws de_sbs de_canary de_m0 de_ra de_s0 de_s1 de_s2 de_s3 de_s4 de_s5 de_s6 de_s7 de_s8 de_s9 de_s10 de_s11]. split; [| split; [| split; [| split; [| split; [exact WM|]]]]].
    + eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. cbn [outside]. lia.
    + eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. cbn [outside]. lia.
    + exact DOCC.
    + eapply munch_weaken; [| exact MU]. unfold sub_fp, dump_W. cbn [outside]. intros x Hx. lia.
    + exists errv. exact ERR.
Qed.
End WithCeiling0.

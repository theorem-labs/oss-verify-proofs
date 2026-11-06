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
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_defs Dmp_defs Dmp_pj_iface.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Record pjenv : Type := mkPE {
  pe_q : Z;
  pe_lo : Z;
  pe_OS : Z;
  pe_DOC : Z;
  pe_TAPE : Z; pe_SBUF : Z; pe_tws : list Z; pe_sbs : list Z;
  pe_canary : word;
  pe_m0 : mem;
  pe_ra : word; pe_s0 : word; pe_s1 : word; pe_s2 : word; pe_s3 : word; pe_s4 : word; pe_s5 : word; pe_s6 : word;
  pe_s7 : word; pe_s8 : word; pe_s9 : word; pe_s10 : word; pe_s11 : word }.

Notation pe_n D := (Z.of_nat (length (pe_tws D))).
Notation pe_sn D := (Z.of_nat (length (pe_sbs D))).
Notation dsp D := (pe_q D - 144).

Definition pjenv_ok (D : pjenv) : Prop :=
  pe_n D < 2^32 /\ Forall (fun c => 0 <= c < 256) (pe_sbs D) /\ pe_sn D < 2^56
  /\ pe_lo D + DMP_PJ_LEAF <= dsp D /\ GLOBALS_TOP <= pe_lo D /\ pe_q D mod 16 = 0
  /\ pe_q D <= pe_OS D /\ (pe_DOC D + 16 <= pe_OS D \/ pe_OS D + 288 <= pe_DOC D) /\ pe_OS D + 288 < 2^62 /\ pe_q D <= pe_DOC D /\ pe_DOC D + 16 < 2^62
  /\ 0 < pe_TAPE D /\ pe_TAPE D mod 8 = 0 /\ pe_TAPE D + 8 * pe_n D <= pe_lo D /\ (pe_TAPE D + 8 * pe_n D <= 0x10000 \/ GLOBALS_TOP <= pe_TAPE D)
  /\ 0 < pe_SBUF D /\ pe_SBUF D + pe_sn D <= pe_lo D /\ (pe_SBUF D + pe_sn D <= 0x10000 \/ GLOBALS_TOP <= pe_SBUF D).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition PINV (lc : list cell) (D : pjenv) (m : mem) : Prop :=
  OSX m (pe_OS D)
  /\ LOCB m /\ el_dcc m /\ dmp_dcc m /\ rw_cells psegs m 0xdfa38 [C8 (Z_to_bv 64 0xffd30)] /\ ssp_cells m (pe_canary D) /\ mem_inv psegs m
  /\ stk psegs m (pe_lo D) (dsp D)
  /\ (exists scr : list byte, rw_cells psegs m (dsp D) (lc ++ [CB 8 scr] ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D)
                                                                                (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)))
  /\ bytes_at psegs m (pe_TAPE D) (u64s (map (Z_to_bv 64) (pe_tws D))) /\ bytes_at psegs m (pe_SBUF D) (map (Z_to_bv 8) (pe_sbs D))
  /\ rw_cells psegs m (pe_DOC D) [C8 (Z_to_bv 64 (pe_TAPE D)); C8 (Z_to_bv 64 (pe_SBUF D))]
  /\ munch (pj_W (pe_lo D) (pe_q D) (pe_OS D)) (pe_m0 D) m /\ wmono psegs (pe_m0 D) m
  /\ (exists errv : word, rw_cells psegs m LX_ERRNO [C4 errv]).

Section Frame.
  Variable lc : list cell.
  Hypothesis LCS : cells_size lc = 32%nat.

Lemma PINV_frame_facts : forall D m m' W,
  pjenv_ok D -> PINV lc D m -> munch W m m' -> wmono psegs m m' ->
  (forall a, (dsp D <= a < pe_q D \/ (0 <= a < pe_lo D /\ ~ (0xdfa38 <= a < 0xdfa40) /\ ~ (915908 <= a < 915912)) \/ pe_DOC D <= a < pe_DOC D + 16) -> outside W a) ->
  el_dcc m' /\ dmp_dcc m' /\ ssp_cells m' (pe_canary D)
  /\ (exists scr : list byte, rw_cells psegs m' (dsp D) (lc ++ [CB 8 scr] ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D)
                                                                                   (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)))
  /\ bytes_at psegs m' (pe_TAPE D) (u64s (map (Z_to_bv 64) (pe_tws D))) /\ bytes_at psegs m' (pe_SBUF D) (map (Z_to_bv 8) (pe_sbs D))
  /\ rw_cells psegs m' (pe_DOC D) [C8 (Z_to_bv 64 (pe_TAPE D)); C8 (Z_to_bv 64 (pe_SBUF D))].
Proof.
  intros D m m' W (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI) DI MU WM HW.
  destruct DI as (_ & _ & DCC & DCB & _ & SSP & _ & _ & (scr & FR) & TB & SB & DOCC & _).
  unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    Ltac trd AG HW C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; apply HW; right; left; lia].
    split; [trd AG HW C1|]. split; [trd AG HW C2|]. split; [trd AG HW C3|]. split; [trd AG HW C4|]. split; [trd AG HW C5| trd AG HW C6].
  - unfold dmp_dcc, DMP_NPB_SLOT in *. eapply rw_cells_agree; [exact AG| exact DCB| intros a Ha; cbn in Ha; apply HW; right; left; lia].
  - eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. apply HW. right; left. lia.
  - exists scr. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. rewrite !cells_size_app, LCS, pjsaves_size in Ha. cbn in Ha. apply HW. left. lia.
  - eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. apply HW. right; left. clear - Ha T0 TH TI GLO. lia.
  - eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. apply HW. right; left. clear - Ha S0 SH SI GLO. lia.
  - eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn in Ha. apply HW. right; right. lia.
Qed.

Lemma frame_rescr : forall D m cs, cells_size cs = 8%nat ->
  rw_cells psegs m (dsp D) (lc ++ cs ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)) ->
  exists scr, rw_cells psegs m (dsp D) (lc ++ [CB 8 scr] ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)).
Proof.
  intros D m cs SZ FR.
  destruct (proj1 (rw_cells_app m (dsp D) lc _) FR) as [F1 F23].
  destruct (proj1 (rw_cells_app m _ cs _) F23) as [F2 F3]. rewrite SZ in F3.
  destruct (rw_cells_forget _ _ _ _ F2) as [scr F2']. rewrite SZ in F2'. exists scr.
  apply (proj2 (rw_cells_app m (dsp D) lc _)). split; [exact F1|].
  apply (proj2 (rw_cells_app m _ [CB 8 scr] _)). split; [exact F2'| exact F3].
Qed.

Lemma frame_scratch : forall D m cs, cells_size cs = 8%nat ->
  rw_cells psegs m (dsp D) (lc ++ cs ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)) ->
  rw_cells psegs m (dsp D + 32) cs.
Proof.
  intros D m cs SZ FR.
  destruct (proj1 (rw_cells_app m (dsp D) lc _) FR) as [_ F23]. rewrite LCS in F23.
  destruct (proj1 (rw_cells_app m _ cs _) F23) as [F2 _]. replace (dsp D + 32) with (dsp D + Z.of_nat 32) by lia. exact F2.
Qed.

Lemma PINV_reframe : forall lc0 D m m' cs, pjenv_ok D -> PINV lc0 D m ->
  munch [(dsp D, dsp D + 40)] m m' -> wmono psegs m m' -> mem_inv psegs m' -> cells_size cs = 8%nat ->
  rw_cells psegs m' (dsp D) (lc ++ cs ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)) ->
  PINV lc D m'.
Proof.
  intros lc0 D m m' cs DOK DI MU WM MI' SZ FR'.
  pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
  pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & DCB & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU0 & WM0 & (errv & ERR)).
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  assert (DCC' : el_dcc m').
  { destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    Ltac trd2 AG C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; cbn [outside]; lia].
    split; [trd2 AG C1|]. split; [trd2 AG C2|]. split; [trd2 AG C3|]. split; [trd2 AG C4|]. split; [trd2 AG C5| trd2 AG C6]. }
  assert (DCB' : dmp_dcc m').
  { unfold dmp_dcc, DMP_NPB_SLOT in *. eapply rw_cells_agree; [exact AG| exact DCB| intros a Ha; cbn in Ha; cbn [outside]; lia]. }
  assert (SSP' : ssp_cells m' (pe_canary D)).
  { eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn [outside]. lia. }
  assert (TB' : bytes_at psegs m' (pe_TAPE D) (u64s (map (Z_to_bv 64) (pe_tws D)))).
  { eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. cbn [outside]. lia. }
  assert (SB' : bytes_at psegs m' (pe_SBUF D) (map (Z_to_bv 8) (pe_sbs D))).
  { eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. cbn [outside]. lia. }
  assert (DOCC' : rw_cells psegs m' (pe_DOC D) [C8 (Z_to_bv 64 (pe_TAPE D)); C8 (Z_to_bv 64 (pe_SBUF D))]).
  { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
  destruct (frame_rescr D m' cs SZ FR') as [scr' FR''].
  split. { exists pb, pp, ep, fill, dum, j148, j284. split; [| split; [exact PUTI| exact FOK]].
           eapply rw_cells_agree; [exact AG| exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia. }
  split; [eapply LOCB_transport; [exact LB| exact MU| exact WM|]; cbv [disjoint_from fst snd]; lia|].
  split; [exact DCC'|]. split; [exact DCB'|]. split; [eapply rw_cells_agree; [exact AG| exact TPC|]; intros a Ha; cbn in Ha; cbn [outside]; lia|].
  split; [exact SSP'|]. split; [exact MI'|].
  split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn [disjoint_from]; lia]|].
  split; [exists scr'; exact FR''|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
  split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, pj_W. cbn [outside]. intros x Hx. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|].
  exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
Qed.

Lemma PINV_rescratch : forall D m m' cs, pjenv_ok D -> PINV lc D m ->
  munch [(dsp D + 32, dsp D + 40)] m m' -> wmono psegs m m' -> mem_inv psegs m' -> cells_size cs = 8%nat ->
  rw_cells psegs m' (dsp D) (lc ++ cs ++ pjsaves (pe_ra D) (pe_s0 D) (pe_s1 D) (pe_s2 D) (pe_s3 D) (pe_s4 D) (pe_s5 D) (pe_s6 D) (pe_s7 D) (pe_s8 D) (pe_s9 D) (pe_s10 D) (pe_s11 D)) ->
  PINV lc D m'.
Proof.
  intros D m m' cs DOK DI MU WM MI' SZ FR'. eapply (PINV_reframe lc); [exact DOK| exact DI| | exact WM| exact MI'| exact SZ| exact FR'].
  eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
Qed.

Section Calls.
  Variable D : pjenv.
  Hypothesis DOK : pjenv_ok D.
  Hypothesis PUT : os_putX_stmt.

  Let usp_eq : bv_unsigned (Z_to_bv 64 (dsp D)) = dsp D.
  Proof. pose proof DOK as (_ & _ & _ & LO & GLO & AL & QOS & OSD & OSH & QD & DH & _). unfold GLOBALS_TOP, DMP_PJ_LEAF in *. apply unsigned_lit. lia. Qed.

  Lemma put_call : forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (BUF N CAP : Z) (bs : list byte),
    PINV lc D m ->
    bytes_at psegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> 0 <= BUF -> BUF + CAP < 2 ^ 62 ->
    (BUF + CAP <= pe_lo D \/ pe_OS D + 288 <= BUF \/ (dsp D <= BUF /\ BUF + CAP <= pe_OS D)) ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), PINV lc D m' ->
       evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 BUF) (Z_to_bv 64 N) a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom psegs)).
  Proof.
    intros until bs. intros DI BB BL NRG B0 BH LOC HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & DCB & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    eapply evt_cut.
    { eapply (PUT ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (pe_lo D) (pe_OS D) BUF N CAP fill pp ep pb dum bs j148 j284); rewrite ?usp_eq;
        [exact ST| lia| lia| exact OSC| exact PUTI| exact FOK| exact LB| lia| lia| exact BB| exact BL| lia| lia| lia| lia| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold os_putX_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & ST' & OSC' & PUTI' & LB').
    apply HK.
    destruct (PINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & DCB' & SSP' & FR' & TB' & SB' & DOCC').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', (fill_after fill), dum', j148, j284; split; [exact OSC'| split; [exact PUTI'| apply FILLOK_after'; exact FOK]]|].
    split; [exact LB'|]. split; [exact DCC'|]. split; [exact DCB'|]. split.
    { eapply rw_cells_agree; [exact AG| exact TPC|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, pj_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Lemma ins_call : forall (ENTRY : Z) (VOKP : Z -> Prop), ins_pre ENTRY VOKP 0x1002 0 FILLOK ->
    forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (v : Z),
    PINV lc D m -> frm0 fc -> VOKP v ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F' : bvmap 5 word) (fc' : bv 32), PINV lc D m' -> frm0 fc' ->
       evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (ret_pc ra) fc' None m' (seg_rom psegs))) ->
    evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 ENTRY) fc None m (seg_rom psegs)).
  Proof.
    intros ENTRY VOKP INS. intros until v. intros DI FRM HV HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & DCB & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    eapply evt_cut.
    { eapply (INS ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (pe_lo D) (pe_OS D) fill v pp ep pb dum j148 j284 (pe_canary D)); rewrite ?usp_eq;
        [exact ST| lia| lia| lia| reflexivity| exact OSC| exact PUTI| exact FOK| lia| lia| exact HV| exact TPC| exact SSP| exact FRM| exact LB| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold ins_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & FRM' & FEQ & ST' & SSP' & OSC' & PUTI' & TPC' & LB').
    apply HK; [| exact FRM'].
    destruct (PINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & DCB' & _ & FR' & TB' & SB' & DOCC').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', (fill_after fill), dum', j148, j284; split; [exact OSC'| split; [exact PUTI'| apply FILLOK_after'; exact FOK]]|].
    split; [exact LB'|]. split; [exact DCC'|]. split; [exact DCB'|]. split; [exact TPC'|].
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, pj_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Hypothesis INSB : ins_b_stmt.

  Lemma insb_call : forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (v : Z),
    PINV lc D m -> frm0 fc -> (v = 0 \/ v = 1) ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F' : bvmap 5 word) (fc' : bv 32), PINV lc D m' -> frm0 fc' ->
       evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (ret_pc ra) fc' None m' (seg_rom psegs))) ->
    evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 DMP_INS_B) fc None m (seg_rom psegs)).
  Proof.
    intros until v. intros DI FRM HV HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & DCB & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    eapply evt_cut.
    { eapply (INSB ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (pe_lo D) (pe_OS D) fill v pp ep pb dum j148 j284 (pe_canary D)); rewrite ?usp_eq;
        [exact ST| lia| lia| lia| reflexivity| exact OSC| exact PUTI| exact FOK| lia| lia| exact HV| exact TPC| exact SSP| exact FRM| exact LB| exact DCC| exact DCB| exact MI]. }
    cbv beta. intros ms' PO. unfold ins_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & FRM' & FEQ & ST' & SSP' & OSC' & PUTI' & TPC' & LB').
    apply HK; [| exact FRM'].
    destruct (PINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & DCB' & _ & FR' & TB' & SB' & DOCC').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', (fill_after fill), dum', j148, j284; split; [exact OSC'| split; [exact PUTI'| apply FILLOK_after'; exact FOK]]|].
    split; [exact LB'|]. split; [exact DCC'|]. split; [exact DCB'|]. split; [exact TPC'|].
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, pj_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Hypothesis INSD : ins_d_stmt.

  Lemma insd_call : forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINV lc D m -> frm0 fc ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F' : bvmap 5 word) (fc' : bv 32), PINV lc D m' -> frm0 fc' ->
       evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (ret_pc ra) fc' None m' (seg_rom psegs))) ->
    evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) a1 a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 EL_INS_D) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros DI FRM HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & DCB & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    eapply evt_cut.
    { eapply (INSD ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (pe_lo D) (pe_OS D) fill pp ep (reg_get F (Z_to_bv 5 10)) pb dum j148 j284 (pe_canary D)); rewrite ?usp_eq;
        [exact ST| lia| lia| lia| reflexivity| exact OSC| exact PUTI| exact FOK| lia| lia| reflexivity| exact TPC| exact SSP| exact FRM| exact LB| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold ins_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & FRM' & FEQ & ST' & SSP' & OSC' & PUTI' & TPC' & LB').
    apply HK; [| exact FRM'].
    destruct (PINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & DCB' & _ & FR' & TB' & SB' & DOCC').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', (fill_after fill), dum', j148, j284; split; [exact OSC'| split; [exact PUTI'| apply FILLOK_after'; exact FOK]]|].
    split; [exact LB'|]. split; [exact DCC'|]. split; [exact DCB'|]. split; [exact TPC'|].
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, pj_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Lemma pj_call : forall (d : nat), pj_stmt d ->
    forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (i j : Z),
    PINV lc D m -> frm0 fc ->
    elem (Tf (pe_tws D)) (Tf (pe_sbs D)) (pe_sn D) ck_any d i j -> 0 <= i -> j <= pe_n D ->
    pe_lo D + pj_need d <= dsp D ->
    (forall (m' : mem) (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F' : bvmap 5 word) (fc' : bv 32), PINV lc D m' -> frm0 fc' ->
       evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 b0 b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (ret_pc ra) fc' None m' (seg_rom psegs))) ->
    evt psegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (pe_OS D + 128)) (Z_to_bv 64 (pe_DOC D)) (Z_to_bv 64 i) a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ) fc None m (seg_rom psegs)).
  Proof.
    intros d PJ. intros until j. intros DI FRM EL I0 JN NEED HK.
    pose proof DOK as (NR & SBS & SNR & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & T8 & TH & TI & S0 & SH & SI). unfold GLOBALS_TOP, DMP_PJ_LEAF in *.
    pose proof DI as (OSXm & LB & DCC & DCB & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    assert (ALD : (dsp D) mod 16 = 0) by (clear - AL; replace (dsp D) with (pe_q D + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact AL).
    eapply evt_cut.
    { eapply (PJ ra gp t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (dsp D) (pe_lo D) (pe_OS D) (pe_DOC D) (pe_TAPE D) (pe_SBUF D) i j (pe_tws D) (pe_sbs D) (pe_canary D) errv);
        [exact EL| exact I0| exact JN| exact NR| exact SBS| exact SNR
        | exact DOCC| lia| exact OSD| exact DH
        | exact TB| exact T0| exact T8| exact TH| unfold GLOBALS_TOP; exact TI
        | exact SB| exact S0| exact SH| unfold GLOBALS_TOP; exact SI
        | exact OSXm| lia| exact OSH| exact LB| exact DCC| exact DCB| exact SSP| exact TPC| rewrite ELX; exact ERR
        | exact ST| exact NEED| unfold GLOBALS_TOP; lia| exact ALD| exact MI| exact FRM]. }
    cbv beta. intros ms' PO. unfold pj_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & -> & FRM' & MU' & WM' & MI' & ST' & OSX' & TPC' & (errv' & ERR') & SSP' & LB').
    apply HK; [| exact FRM'].
    destruct (PINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & DCB' & _ & FR' & TB' & SB' & DOCC').
    { intros a Ha. unfold pj_W. rewrite ELX. cbn [outside]. lia. }
    split; [exact OSX'|]. split; [exact LB'|]. split; [exact DCC'|]. split; [exact DCB'|]. split; [exact TPC'|].
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, pj_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv'. rewrite ELX. exact ERR'.
  Qed.
End Calls.
End Frame.

Lemma pjolits32 : cells_size pjolits = 32%nat. Proof. reflexivity. Qed.
Lemma junk32 : forall j, cells_size [CB 32 j] = 32%nat. Proof. intros. reflexivity. Qed.
End WithCeiling0.

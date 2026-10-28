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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_h_defs Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_esc_iface El_defs El_dump_kit.
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

Record eenv : Type := mkEE {
  ee_q : Z;
  ee_lo : Z; ee_OS : Z; ee_SV : Z; ee_P : Z; ee_bs : list byte;
  ee_j148 : list byte; ee_j284 : list byte; ee_canary : word;
  ee_m0 : word -> option byte;
  ee_j0 : list byte; ee_j32 : list byte;
  ee_ra : word; ee_s0 : word; ee_s1 : word; ee_s2 : word; ee_s3 : word; ee_s4 : word; ee_s5 : word; ee_s6 : word;
  ee_s7 : word; ee_s8 : word; ee_s9 : word; ee_s10 : word; ee_s11 : word }.

Notation esp E := (ee_q E - 144).
Notation eL E := (Z.of_nat (length (ee_bs E))).

Definition eenv_ok (E : eenv) : Prop :=
  ee_lo E <= ee_q E - ESC_DEPTH /\ 0x111000 <= ee_lo E /\ ee_q E mod 16 = 0
  /\ ee_q E <= ee_OS E /\ ee_OS E + 288 < 2^62
  /\ ee_q E <= ee_SV E /\ ee_SV E + 16 < 2^62 /\ (ee_SV E + 16 <= ee_OS E \/ ee_OS E + 288 <= ee_SV E)
  /\ 0 < ee_P E /\ ee_P E + eL E <= ee_lo E /\ (ee_P E + eL E <= 0x10000 \/ 0x111000 <= ee_P E)
  /\ ee_OS E mod 8 = 0.

Definition elits (E : eenv) : list cell :=
  [CB 8 (ee_j0 E); C8 (Z_to_bv 64 0x11c58); C8 (Z_to_bv 64 0x11268); C8 (Z_to_bv 64 0x11eaa); CB 6 (ee_j32 E)].
Definition esaves (E : eenv) : list cell :=
  [C8 (ee_s11 E); C8 (ee_s10 E); C8 (ee_s9 E); C8 (ee_s8 E); C8 (ee_s7 E); C8 (ee_s6 E); C8 (ee_s5 E); C8 (ee_s4 E); C8 (ee_s3 E); C8 (ee_s2 E);
   C8 (ee_s1 E); C8 (ee_s0 E); C8 (ee_ra E)].
Definition EW (E : eenv) : list (Z * Z) := [(ee_lo E, ee_q E); (ee_OS E, ee_OS E + 288); (0xef558, 0xef558 + 8)].

Definition F2030 (f : Z) : Prop := f = 0x20 \/ f = 0x30.
Definition F30 (f : Z) : Prop := f = 0x30.

Lemma elits_size : forall E, cells_size (elits E) = 38%nat.
Proof. intros E. reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition EINV (FL W : Z) (FP : Z -> Prop) (E : eenv) (m : word -> option byte) : Prop :=
  (exists (pb : word) (pp ep fill : Z) (dum : list byte),
     rw_cells usegs m (ee_OS E) (os_cellsX (ee_OS E) pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) FL W fill dum (ee_j148 E) (ee_j284 E)) /\ PUTINV (ee_OS E) pp ep /\ FP fill)
  /\ LOCB m /\ el_dcc m /\ rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] /\ ssp_cells m (ee_canary E) /\ mem_inv usegs m
  /\ stk usegs m (ee_lo E) (esp E)
  /\ (exists sc : list byte, rw_cells usegs m (esp E) (elits E ++ [CB 2 sc] ++ esaves E))
  /\ rw_cells usegs m (ee_SV E) [C8 (Z_to_bv 64 (ee_P E)); C8 (Z_to_bv 64 (eL E))]
  /\ bytes_at usegs m (ee_P E) (ee_bs E)
  /\ munch (EW E) (ee_m0 E) m /\ wmono usegs (ee_m0 E) m.

Lemma EINV_frame_facts : forall FL Wd FP E m m' W,
  eenv_ok E -> EINV FL Wd FP E m -> munch W m m' -> wmono usegs m m' ->
  (forall a, (esp E <= a < ee_q E \/ (0 <= a < ee_lo E /\ ~ (0xef558 <= a < 0xef560)) \/ ee_SV E <= a < ee_SV E + 16) -> outside W a) ->
  el_dcc m' /\ ssp_cells m' (ee_canary E)
  /\ (exists sc : list byte, rw_cells usegs m' (esp E) (elits E ++ [CB 2 sc] ++ esaves E))
  /\ rw_cells usegs m' (ee_SV E) [C8 (Z_to_bv 64 (ee_P E)); C8 (Z_to_bv 64 (eL E))]
  /\ bytes_at usegs m' (ee_P E) (ee_bs E).
Proof.
  intros FL Wd FP E m m' W (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL) EI MU WM HW.
  destruct EI as (_ & _ & DCC & _ & SSP & _ & _ & (sc & FR) & SVC & PB & _).
  unfold ESC_DEPTH in *.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  split; [| split; [| split; [| split]]].
  - destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    Ltac trd AG HW C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; apply HW; right; left; lia].
    split; [trd AG HW C1|]. split; [trd AG HW C2|]. split; [trd AG HW C3|]. split; [trd AG HW C4|]. split; [trd AG HW C5| trd AG HW C6].
  - eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. apply HW. right; left. lia.
  - exists sc. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha.
    rewrite !cells_size_app, elits_size in Ha. cbn [cells_size csize esaves Nat.add] in Ha.
    apply HW. left. lia.
  - eapply rw_cells_agree; [exact AG| exact SVC|]. intros a Ha. cbn in Ha. apply HW. right; right. lia.
  - eapply bytes_at_agree; [exact AG| exact PB|]. intros a Ha. apply HW. right; left. clear - Ha P0 PH PI GLO. lia.
Qed.

Lemma eframe_rescr : forall E m cs, cells_size cs = 2%nat ->
  rw_cells usegs m (esp E) (elits E ++ cs ++ esaves E) -> exists sc, rw_cells usegs m (esp E) (elits E ++ [CB 2 sc] ++ esaves E).
Proof.
  intros E m cs SZ FR.
  destruct (proj1 (rw_cells_app m (esp E) (elits E) _) FR) as [F1 F23].
  destruct (proj1 (rw_cells_app m _ cs _) F23) as [F2 F3]. rewrite SZ in F3.
  destruct (rw_cells_forget _ _ _ _ F2) as [sc F2']. rewrite SZ in F2'. exists sc.
  apply (proj2 (rw_cells_app m (esp E) (elits E) _)). split; [exact F1|].
  apply (proj2 (rw_cells_app m _ [CB 2 sc] _)). split; [exact F2'| exact F3].
Qed.

Lemma eframe_scratch : forall E m cs, rw_cells usegs m (esp E) (elits E ++ cs ++ esaves E) -> rw_cells usegs m (esp E + 38) cs.
Proof.
  intros E m cs FR. pose proof (elits_size E) as SZ.
  destruct (proj1 (rw_cells_app m (esp E) (elits E) _) FR) as [_ F23]. rewrite SZ in F23.
  destruct (proj1 (rw_cells_app m _ cs _) F23) as [F2 _]. replace (esp E + 38) with (esp E + Z.of_nat 38) by lia. exact F2.
Qed.

Lemma EINV_rescratch : forall FL Wd FP E m m' cs, eenv_ok E -> EINV FL Wd FP E m ->
  munch [(esp E + 38, esp E + 40)] m m' -> wmono usegs m m' -> mem_inv usegs m' -> cells_size cs = 2%nat ->
  rw_cells usegs m' (esp E) (elits E ++ cs ++ esaves E) -> EINV FL Wd FP E m'.
Proof.
  intros FL Wd FP E m m' cs EOK EI MU WM MI' SZ FR'.
  pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
  pose proof EI as ((pb & pp & ep & fill & dum & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & SVC & PB & MU0 & WM0).
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  destruct (eframe_rescr E m' cs SZ FR') as [sc' FR''].
  split. { exists pb, pp, ep, fill, dum. split; [| split; [exact PUTI| exact FOK]].
           eapply rw_cells_agree; [exact AG| exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia. }
  split; [eapply LOCB_transport; [exact LB| exact MU| exact WM|]; cbv [disjoint_from fst snd]; lia|].
  split. { destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    Ltac trd2 AG C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; cbn [outside]; lia].
    split; [trd2 AG C1|]. split; [trd2 AG C2|]. split; [trd2 AG C3|]. split; [trd2 AG C4|]. split; [trd2 AG C5| trd2 AG C6]. }
  split; [eapply rw_cells_agree; [exact AG| exact TPC|]; intros a Ha; cbn in Ha; cbn [outside]; lia|].
  split. { eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn [outside]. lia. }
  split; [exact MI'|].
  split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn [disjoint_from]; lia]|].
  split; [exists sc'; exact FR''|].
  split; [eapply rw_cells_agree; [exact AG| exact SVC|]; intros a Ha; cbn in Ha; cbn [outside]; lia|].
  split. { eapply bytes_at_agree; [exact AG| exact PB|]. intros a Ha. cbn [outside]. lia. }
  split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, EW. cbn [outside]. intros x Hx. lia. }
  eapply wmono_trans; [exact WM0| exact WM].
Qed.

Lemma EINV_restream : forall FL Wd FP FL' Wd' (FP' : Z -> Prop) E m m' pb pp ep fill dum, eenv_ok E -> EINV FL Wd FP E m ->
  munch [(ee_OS E + 136, ee_OS E + 168)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
  rw_cells usegs m' (ee_OS E) (os_cellsX (ee_OS E) pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) FL' Wd' fill dum (ee_j148 E) (ee_j284 E)) ->
  PUTINV (ee_OS E) pp ep -> FP' fill -> EINV FL' Wd' FP' E m'.
Proof.
  intros FL Wd FP FL' Wd' FP' E m m' pb pp ep fill dum EOK EI MU WM MI' OSC' PUTI' FOK'.
  pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
  pose proof EI as (_ & LB & DCC & TPC & SSP & MI & ST & (sc & FR) & SVC & PB & MU0 & WM0).
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  split; [exists pb, pp, ep, fill, dum; split; [exact OSC'| split; [exact PUTI'| exact FOK']]|].
  split; [eapply LOCB_transport; [exact LB| exact MU| exact WM|]; cbv [disjoint_from fst snd]; lia|].
  split. { destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    split; [trd2 AG C1|]. split; [trd2 AG C2|]. split; [trd2 AG C3|]. split; [trd2 AG C4|]. split; [trd2 AG C5| trd2 AG C6]. }
  split; [eapply rw_cells_agree; [exact AG| exact TPC|]; intros a Ha; cbn in Ha; cbn [outside]; lia|].
  split. { eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn [outside]. lia. }
  split; [exact MI'|].
  split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn [disjoint_from]; lia]|].
  split. { exists sc. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha.
           rewrite !cells_size_app, elits_size in Ha. cbn [cells_size csize esaves Nat.add] in Ha. cbn [outside]. lia. }
  split; [eapply rw_cells_agree; [exact AG| exact SVC|]; intros a Ha; cbn in Ha; cbn [outside]; lia|].
  split. { eapply bytes_at_agree; [exact AG| exact PB|]. intros a Ha. cbn [outside]. lia. }
  split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, EW. cbn [outside]. intros x Hx. lia. }
  eapply wmono_trans; [exact WM0| exact WM].
Qed.

Lemma EINV_fills : forall FL Wd (FP FP' : Z -> Prop) E m, (forall f, FP f -> FP' f) -> EINV FL Wd FP E m -> EINV FL Wd FP' E m.
Proof.
  intros FL Wd FP FP' E m H ((pb & pp & ep & fill & dum & OSC & PUTI & FOK) & REST).
  split; [exists pb, pp, ep, fill, dum; split; [exact OSC| split; [exact PUTI| apply H; exact FOK]]| exact REST].
Qed.

Lemma F2030_after : forall f, FILLOK f -> F2030 (fill_after f).
Proof. intros f H. unfold fill_after, FILLOK, F2030 in *. destruct (f =? 4294967295) eqn:E; [left; reflexivity|]. apply Z.eqb_neq in E. lia. Qed.
Lemma F2030_FILLOK : forall f, F2030 f -> FILLOK f.
Proof. intros f H. unfold FILLOK, F2030 in *. lia. Qed.

Section Calls.
  Variable E : eenv.
  Hypothesis EOK : eenv_ok E.
  Hypothesis PUT : os_putX_stmt.
  Hypothesis SETF : setfill_stmt.
  Hypothesis INSI : ins_i_stmt.

  Let usp_eq : bv_unsigned (Z_to_bv 64 (esp E)) = esp E.
  Proof. pose proof EOK as (LO & GLO & AL & QOS & OSH & _). unfold ESC_DEPTH in *. apply unsigned_lit. lia. Qed.

  Lemma e_put_call : forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (BUF N CAP : Z) (bs : list byte),
    EINV 0x1002 0 FILLOK E m ->
    bytes_at usegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> 0 < BUF -> BUF + CAP < 2 ^ 62 ->
    (BUF + CAP <= ee_lo E \/ ee_OS E + 288 <= BUF \/ (esp E <= BUF /\ BUF + CAP <= ee_OS E)) ->
    (forall (m' : word -> option byte) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), EINV 0x1002 0 F2030 E m' ->
       evt usegs K (MS (mkR ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (ee_OS E + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F (ret_pc ra) fc None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (ee_OS E + 128)) (Z_to_bv 64 BUF) (Z_to_bv 64 N) a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom usegs)).
  Proof.
    intros until bs. intros EI BB BL NR B0 BH LOC HK.
    pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
    pose proof EI as ((pb & pp & ep & fill & dum & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & SVC & PB & MU & WM).
    eapply evt_cut.
    { eapply (PUT ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (ee_lo E) (ee_OS E) BUF N CAP fill pp ep pb dum bs (ee_j148 E) (ee_j284 E)); rewrite ?usp_eq;
        [exact ST| lia| lia| exact OSC| exact PUTI| exact FOK| exact LB| lia| lia| exact OAL| exact BB| exact BL| lia| lia| lia| lia| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold os_putX_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & ST' & OSC' & PUTI' & LB').
    apply HK.
    destruct (EINV_frame_facts _ _ _ E m m' _ EOK EI MU' WM') as (DCC' & SSP' & FR' & SVC' & PB').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', (fill_after fill), dum'; split; [exact OSC'| split; [exact PUTI'| apply F2030_after; exact FOK]]|].
    split; [exact LB'|]. split; [exact DCC'|]. split.
    { eapply rw_cells_agree; [exact AG| exact TPC|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact SVC'|]. split; [exact PB'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, EW. cbn [outside]. intros x Hx. lia. }
    eapply wmono_trans; [exact WM| exact WM'].
  Qed.

  Lemma e_setfill_call : forall (FL Wd : Z) (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z) (cs1 : list cell),
    EINV FL Wd F2030 E m -> rw_cells usegs m (esp E + 38) (C1 (Z_to_bv 8 c) :: cs1) -> 0 <= c < 256 ->
    (forall (m' : word -> option byte) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), EINV FL Wd (fun f => f = c) E m' ->
       evt usegs K (MS (mkR ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (ee_OS E + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F (ret_pc ra) fc None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (ee_OS E + 128)) (Z_to_bv 64 (esp E + 38)) a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 EL_SETFILL) fc None m (seg_rom usegs)).
  Proof.
    intros until cs1. intros EI CPC CR HK.
    pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
    pose proof EI as ((pb & pp & ep & fill & dum & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & SVC & PB & MU & WM).
    destruct (proj1 (rw_cells_app _ _ [_] _) CPC) as [CP1 _].
    eapply evt_cut.
    { eapply (SETF ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (ee_lo E) (ee_OS E) (esp E + 38) FL Wd fill c pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum (ee_j148 E) (ee_j284 E)); rewrite ?usp_eq;
        [exact ST| lia| lia| exact OSC| exact FOK| lia| lia| exact OAL| exact CP1| exact CR| lia| lia| left; lia| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold setfill_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & ST' & OSC').
    apply HK.
    destruct (EINV_frame_facts _ _ _ E m m' _ EOK EI MU' WM') as (DCC' & SSP' & FR' & SVC' & PB').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb, pp, ep, c, dum; split; [exact OSC'| split; [exact PUTI| reflexivity]]|].
    split; [eapply LOCB_transport; [exact LB| exact MU'| exact WM'|]; cbv [disjoint_from fst snd]; lia|].
    split; [exact DCC'|]. split.
    { eapply rw_cells_agree; [exact AG| exact TPC|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact SVC'|]. split; [exact PB'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, EW. cbn [outside]. intros x Hx. lia. }
    eapply wmono_trans; [exact WM| exact WM'].
  Qed.

  Lemma e_insi_call : forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z),
    EINV 0x1008 4 F30 E m -> frm0 fc -> 0 <= v < 2^32 ->
    (forall (m' : word -> option byte) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F' : bvmap 5 word) (fc' : bv 32), EINV 0x1008 0 F30 E m' -> frm0 fc' ->
       evt usegs K (MS (mkR ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (ee_OS E + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (ret_pc ra) fc' None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (ee_OS E + 128)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 EL_INS_I) fc None m (seg_rom usegs)).
  Proof.
    intros until v. intros EI FRM HV HK.
    pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
    pose proof EI as ((pb & pp & ep & fill & dum & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & SVC & PB & MU & WM).
    eapply evt_cut.
    { eapply (INSI ra (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (ee_lo E) (ee_OS E) fill v pp ep pb dum (ee_j148 E) (ee_j284 E) (ee_canary E)); rewrite ?usp_eq;
        [exact ST| lia| lia| lia| reflexivity| exact OSC| exact PUTI| exact FOK| lia| lia| exact OAL| exact HV| exact TPC| exact SSP| exact FRM| exact LB| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold ins_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & FRM' & FEQ & ST' & SSP' & OSC' & PUTI' & TPC' & LB').
    apply HK; [| exact FRM'].
    destruct (EINV_frame_facts _ _ _ E m m' _ EOK EI MU' WM') as (DCC' & _ & FR' & SVC' & PB').
    { intros a Ha. cbn [outside]. lia. }
    split. { exists pb', pp', ep', (fill_after fill), dum'. split; [exact OSC'| split; [exact PUTI'|]].
             unfold F30 in FOK. rewrite FOK. reflexivity. }
    split; [exact LB'|]. split; [exact DCC'|]. split; [exact TPC'|].
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact SVC'|]. split; [exact PB'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, EW. cbn [outside]. intros x Hx. lia. }
    eapply wmono_trans; [exact WM| exact WM'].
  Qed.
End Calls.

Ltac retlit := try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).
Ltac open_eframe EI FR sc := let X := fresh in pose proof EI as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & (sc & FR) & _); unfold elits, esaves in FR; cbn [app] in FR.

Section Body.
  Variable E : eenv.
  Hypothesis EOK : eenv_ok E.
  Hypothesis PUT : os_putX_stmt.
  Hypothesis SETF : setfill_stmt.
  Hypothesis INSI : ins_i_stmt.

  Definition ELST (pc i : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (ee_SV E)) (Z_to_bv 64 (ee_OS E + 128)) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 0x141c8) (Z_to_bv 64 92) (Z_to_bv 64 34) (Z_to_bv 64 0x131df) (Z_to_bv 64 0x134a5) (Z_to_bv 64 0x13a2d) (Z_to_bv 64 0x12dd1) (Z_to_bv 64 0x11855)
            (Z_to_bv 64 i) (Z_to_bv 64 5) x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m (seg_rom usegs).

  Definition EKLOOP (K : machine_state -> Prop) (gp : word) (j : Z) : Prop :=
    forall (m' : word -> option byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      EINV 0x1002 0 FILLOK E m' -> frm0 fc' -> evt usegs K (ELST 0x405a0 j x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F' fc' m').

  Definition EEXIT (K : machine_state -> Prop) (gp : word) : Prop :=
    forall (m' : word -> option byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F' : bvmap 5 word) (fc' : bv 32),
      EINV 0x1002 0 FILLOK E m' -> frm0 fc' ->
      evt usegs K (MS (mkR x1 (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (ee_SV E)) (Z_to_bv 64 (ee_OS E + 128)) x10 x11 x12 x13 x14 x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F' (Z_to_bv 64 0x40740) fc' None m' (seg_rom usegs)).

  Lemma esc_exit : forall gp : word,
    EEXIT (esc_post (ee_ra E) (ee_q E) gp (ee_s0 E) (ee_s1 E) (ee_s2 E) (ee_s3 E) (ee_s4 E) (ee_s5 E) (ee_s6 E) (ee_s7 E) (ee_s8 E) (ee_s9 E) (ee_s10 E) (ee_s11 E)
                    (ee_lo E) (ee_OS E) (ee_j148 E) (ee_j284 E) (ee_canary E) (ee_m0 E)) gp.
  Proof.
    intros gp. unfold EEXIT. intros until fc'. intros EI FRM.
    pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
    pose proof EI as ((pb & pp & ep & fill & dum & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & _ & SVC & PB & MU0 & WM0). open_eframe EI FR scj.
    pose proof (munch_refl ([] : list (Z * Z)) m') as MU. pose proof (wmono_refl usegs m') as WM.
    step. do 13 step. step. release_frame FR ST (ee_q E). step.
    apply evt_done. unfold esc_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F', fc', pb, pp, ep, fill, dum, m'.
    split; [symmetry; atp_st_eq|]. split; [exact FRM|]. split; [exact MU0|]. split; [exact WM0|]. split; [exact MI|]. split; [exact ST|].
    split; [exact OSC|]. split; [exact PUTI|]. split; [exact FOK|]. split; [exact TPC|]. split; [exact SSP| exact LB].
  Qed.

  Lemma esc_join : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    EINV 0x1002 0 FILLOK E m -> frm0 fc -> 0 <= i < eL E -> (i + 1 < eL E -> EKLOOP K gp (i + 1)) -> EEXIT K gp ->
    evt usegs K (ELST 0x40734 i x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros EI FRM Hi HK HX. unfold ELST.
    pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
    pose proof EI as (_ & _ & _ & _ & _ & MI & _ & _ & SVC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. astep. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
    - eapply HK; [lia| exact EI| exact FRM].
    - eapply HX; [exact EI| exact FRM].
  Qed.

  Lemma esc_putjoin : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (BUF N CAP : Z) (bs : list byte),
    EINV 0x1002 0 FILLOK E m -> frm0 fc -> 0 <= i < eL E ->
    bytes_at usegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> 0 < BUF -> BUF + CAP < 2 ^ 62 ->
    (BUF + CAP <= ee_lo E \/ ee_OS E + 288 <= BUF \/ (esp E <= BUF /\ BUF + CAP <= ee_OS E)) ->
    (i + 1 < eL E -> EKLOOP K gp (i + 1)) -> EEXIT K gp ->
    evt usegs K (ELST 0x40730 i x1 gp x5 x6 x7 (Z_to_bv 64 (ee_OS E + 128)) (Z_to_bv 64 BUF) (Z_to_bv 64 N) a3 a4 a5 a6 a7 x28 x29 x30 x31 F fc m).
  Proof.
    intros until bs. intros EI FRM Hi BB BL NR B0 BH LOC HK HX. unfold ELST.
    pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    step.
    eapply (e_put_call E EOK PUT); [exact EI| exact BB| exact BL| exact NR| exact B0| exact BH| exact LOC|].
    intros m2 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 EI2. retlit.
    eapply esc_join; [eapply EINV_fills; [apply F2030_FILLOK| exact EI2]| exact FRM| exact Hi| exact HK| exact HX].
  Qed.

  Ltac open_os EI OSC PUTI FOK pb pp ep fill dum :=
    let X := fresh in pose proof EI as X; destruct X as ((pb & pp & ep & fill & dum & OSC & PUTI & FOK) & _);
    unfold os_cellsX, sb_cells, ios_cellsX in OSC; cbn [app] in OSC.
  Ltac open_dcc EI V1 V2 V3 V4 V5 V6 := let X := fresh in pose proof EI as X; destruct X as (_ & _ & (V1 & V2 & V3 & V4 & V5 & V6) & _).

  Lemma esc_hex : forall (K : machine_state -> Prop) (i c : Z) (x1 gp x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    EINV 0x1002 0 FILLOK E m -> frm0 fc -> 0 <= i < eL E -> 0 <= c <= 31 ->
    firstn 1 (skipn (Z.to_nat i) (ee_bs E)) = [Z_to_bv 8 c] ->
    (i + 1 < eL E -> EKLOOP K gp (i + 1)) -> EEXIT K gp ->
    evt usegs K (MS (mkR x1 (Z_to_bv 64 (esp E)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (ee_SV E)) (Z_to_bv 64 (ee_OS E + 128)) (Z_to_bv 64 (ee_P E + i)) (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 0x141c8) (Z_to_bv 64 92) (Z_to_bv 64 34) (Z_to_bv 64 0x131df) (Z_to_bv 64 0x134a5) (Z_to_bv 64 0x13a2d) (Z_to_bv 64 0x12dd1) (Z_to_bv 64 0x11855)
                         (Z_to_bv 64 i) (Z_to_bv 64 5) x28 x29 x30 x31) F (Z_to_bv 64 0x40608) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros EI FRM Hi Hc BI HK HX.
    pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
    pose proof EI as (_ & _ & _ & _ & _ & MI & _). open_os EI OSC PUTI FOK pb pp ep fill dum. open_dcc EI V1 V2 V3 V4 V5 V6. open_eframe EI FR scj.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. if_lia.
    step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [exfalso; lia|].

    step. step. astep. astep.
    assert (L7 : forall x d : Z, x mod 8 = 0 -> d mod 8 = 0 -> Z.land (x + d) 7 = 0).
    { intros x d Hx Hd. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. rewrite Z.add_mod, Hx, Hd by lia. reflexivity. }
    rewrite (L7 (ee_OS E) 136 OAL eq_refl).
    step. if_false. step.

    step. step. step. step.
    lit_at 0x11c58 2%nat m MI LIT LITL.
    eapply (e_put_call E EOK PUT); [exact EI| exact LIT| exact LITL| lia| lia| lia| left; lia|].
    clear m MI OSC PUTI FOK pb pp ep fill dum V1 V2 V3 V4 V5 V6 FR scj MU WM LIT LITL EI.
    intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 EI. retlit.
    pose proof EI as (_ & _ & _ & _ & _ & MI & _). open_os EI OSC PUTI FOK pb pp ep fill dum. open_dcc EI V1 V2 V3 V4 V5 V6.
    pose proof (munch_refl [(ee_OS E + 136, ee_OS E + 168)] m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. astep. astep. rewrite (L7 (ee_OS E) 136 OAL eq_refl). step. if_false.

    step. astep. astep. hstep. step. astep. astep. rewrite (L7 (ee_OS E) 136 OAL eq_refl). step. if_false. step. hstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv usegs mx |- _ =>
        pose proof (EINV_restream _ _ _ 0x1008 4 F2030 E m mx pb pp ep fill dum EOK EI MU WM MIx OSC PUTI FOK) as EIB end end.
    clear MU WM OSC EI. rename EIB into EI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(esp E + 38, esp E + 40)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
    open_eframe EI FR scj.
    apply (rw_cells_split_CB usegs _ _ [_; _; _; _; _] 2 scj _ [1; 1]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.

    step. hstep. astep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv usegs mx, MUx : munch _ ?mb mx, WMx : wmono _ ?mb mx |- _ =>
        pose proof (EINV_rescratch _ _ _ E mb mx [C1 (Z_to_bv 8 48); CB 1 (take 1 (drop 1 scj))] EOK EI MUx WMx MIx eq_refl FR) as EIC;
        pose proof (eframe_scratch E mx [C1 (Z_to_bv 8 48); CB 1 (take 1 (drop 1 scj))] FR) as CPC end end.
    eapply (e_setfill_call E EOK SETF 0x1008 4); [exact EIC| exact CPC| lia|].
    clear m MI PUTI FOK pb pp ep fill dum V1 V2 V3 V4 V5 V6 EI u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 FR EIC CPC MU WM.
    intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 EI. retlit.
    pose proof EI as (_ & _ & _ & _ & _ & MI & _ & _ & SVC & PB & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bytes_at_ov_read usegs m (ee_P E) (ee_bs E) (Z.to_nat i) 1 PB ltac:(lia)) as RD. rewrite BI, Z2Nat.id in RD by lia.

    step. astep. step. if_lia. astep. astep. astep.
    replace (0 <? ee_P E) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (ee_P E + i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
    step. if_false. step. if_lia.

    step. step.
    rewrite (a_zxb_small c) by lia.
    eapply (e_insi_call E EOK INSI); [exact EI| exact FRM| lia|].
    clear m MI SVC PB MU WM RD EI u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6.
    intros m u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F3 fc3 EI FRM3. retlit.
    pose proof EI as (_ & _ & _ & _ & _ & MI & _). open_os EI OSC PUTI FOK pb pp ep fill dum. open_dcc EI V1 V2 V3 V4 V5 V6.
    pose proof (munch_refl [(ee_OS E + 136, ee_OS E + 168)] m) as MU. pose proof (wmono_refl usegs m) as WM.

    step. step. astep. astep. rewrite (L7 (ee_OS E) 136 OAL eq_refl). step. if_false. hstep. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with MIx : mem_inv usegs mx |- _ =>
        pose proof (EINV_restream _ _ _ 0x1002 0 FILLOK E m mx pb pp ep fill dum EOK EI MU WM MIx OSC PUTI ltac:(unfold F30 in FOK; unfold FILLOK; lia)) as EID end end.
    eapply esc_join; [exact EID| exact FRM3| exact Hi| exact HK| exact HX].
  Qed.

  Lemma jt_read : forall (m : word -> option byte) (k : nat), mem_inv usegs m -> (k < 6)%nat ->
    ov_read_bytes usegs m (wa (0x141c8 + Z.of_nat (4 * k))) 4 = Some (firstn 4 (skipn (4 * k) (lit 0x141c8 24))).
  Proof.
    intros m k MI Hk. apply (bytes_at_ov_read usegs m 0x141c8 (lit 0x141c8 24) (4 * k) 4).
    - apply lit_bytes; [vm_compute; reflexivity| vm_compute; reflexivity| lia| lia| exact MI].
    - rewrite (ltac:(vm_compute; reflexivity) : length (lit 0x141c8 24) = 24%nat). lia.
  Qed.
  Ltac jt_at m MI k JR := pose proof (jt_read m k MI ltac:(lia)) as JR;
    lazymatch type of JR with ov_read_bytes _ _ (wa ?a) _ = Some ?r =>
      let r' := eval vm_compute in r in change r with r' in JR;
      let a' := eval vm_compute in a in change a with a' in JR end.

  Lemma esc_char : forall (K : machine_state -> Prop) (i : Z) (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    EINV 0x1002 0 FILLOK E m -> frm0 fc -> 0 <= i < eL E -> (i + 1 < eL E -> EKLOOP K gp (i + 1)) -> EEXIT K gp ->
    evt usegs K (ELST 0x405a0 i x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
  Proof.
    intros until m. intros EI FRM Hi HK HX. unfold ELST.
    pose proof EOK as (LO & GLO & AL & QOS & OSH & QSV & SVH & SVD & P0 & PH & PI & OAL). unfold ESC_DEPTH in *.
    pose proof EI as (_ & _ & _ & _ & _ & MI & _ & _ & SVC & PB & _). open_eframe EI FR scj.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

    assert (CH : exists c, 0 <= c < 256 /\ firstn 1 (skipn (Z.to_nat i) (ee_bs E)) = [Z_to_bv 8 c]).
    { destruct (skipn (Z.to_nat i) (ee_bs E)) as [|b rest] eqn:SK.
      - exfalso. pose proof (length_skipn (Z.to_nat i) (ee_bs E)) as LS. rewrite SK in LS. cbn in LS. lia.
      - exists (bv_unsigned b). split; [pose proof (bv_unsigned_in_range _ b) as R; unfold bv_modulus in R; cbn in R; lia|].
        cbn. f_equal. symmetry. apply bitvector.definitions.Z_to_bv_bv_unsigned. }
    destruct CH as (c & Hc & BI).
    pose proof (bytes_at_ov_read usegs m (ee_P E) (ee_bs E) (Z.to_nat i) 1 PB ltac:(lia)) as RD. rewrite BI, Z2Nat.id in RD by lia.

    step. astep. step. if_lia. astep. astep. astep.
    replace (0 <? ee_P E) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (ee_P E + i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
    step. if_false. step. if_lia.

    step. rewrite (a_zxb_small c) by lia. astep.
    assert (CASES : 8 <= c <= 13 \/ ~ (8 <= c <= 13)) by lia. destruct CASES as [CJ|CN].
    -
      assert (CC : c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13) by lia. clear CJ Hc.
      destruct CC as [->|[->|[->|[->|[->| ->]]]]]; (step; if_false; astep; astep).
      + jt_at m MI 0%nat JR. step. astep. step.

        step. step. step. step. lit_at 0x131df 2%nat m MI LIT LITL.
        eapply esc_putjoin; [exact EI| exact FRM| exact Hi| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK| exact HX].
      + jt_at m MI 1%nat JR. step. astep. step.
        step. step. step. step. lit_at 0x134a5 2%nat m MI LIT LITL.
        eapply esc_putjoin; [exact EI| exact FRM| exact Hi| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK| exact HX].
      + jt_at m MI 2%nat JR. step. astep. step.
        step. step. step. step. lit_at 0x13a2d 2%nat m MI LIT LITL.
        eapply esc_putjoin; [exact EI| exact FRM| exact Hi| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK| exact HX].
      + jt_at m MI 3%nat JR. step. astep. step.

        eapply esc_hex; [exact EI| exact FRM| exact Hi| lia| exact BI| exact HK| exact HX].
      + jt_at m MI 4%nat JR. step. astep. step.
        step. step. step. step. lit_at 0x12dd1 2%nat m MI LIT LITL.
        eapply esc_putjoin; [exact EI| exact FRM| exact Hi| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK| exact HX].
      + jt_at m MI 5%nat JR. step. astep. step.
        step. step. step. step. lit_at 0x11855 2%nat m MI LIT LITL.
        eapply esc_putjoin; [exact EI| exact FRM| exact Hi| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK| exact HX].
    -
      replace (Z_to_bv 64 (c + -8)) with (Z_to_bv 64 (if c <? 8 then c + -8 + 2^64 else c + -8)).
      2:{ destruct (c <? 8) eqn:E8; [| reflexivity]. apply Z_to_bv64_eqm.
          replace (c + -8 + 2^64) with ((c + -8) + 1 * 2^64) by lia. rewrite Z_mod_plus_full. reflexivity. }
      assert (D5 : 5 < (if c <? 8 then c + -8 + 2^64 else c + -8) < 2^64) by (destruct (c <? 8) eqn:E8; [apply Z.ltb_lt in E8| apply Z.ltb_ge in E8]; lia).
      set (d := if c <? 8 then c + -8 + 2^64 else c + -8) in *.
      step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].

      step. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by lia.
      {
        step. step. step. step. lit_at 0x11eaa 2%nat m MI LIT LITL.
        eapply esc_putjoin; [exact EI| exact FRM| exact Hi| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK| exact HX]. }

      step. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
      2:{
        step. step. step. step. lit_at 0x11268 2%nat m MI LIT LITL.
        eapply esc_putjoin; [exact EI| exact FRM| exact Hi| exact LIT| exact LITL| lia| lia| lia| left; lia| exact HK| exact HX]. }
      destruct (Z.le_decidable c 31) as [C31|C32].
      { eapply esc_hex; [exact EI| exact FRM| exact Hi| lia| exact BI| exact HK| exact HX]. }

      step. if_lia. step. step. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia; [| exfalso; lia].
      clear MU WM. pose proof (munch_refl [(esp E + 38, esp E + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      apply (rw_cells_split_CB usegs _ _ [_; _; _; _; _] 2 scj _ [1; 1]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      step. rewrite <- (a_zxb_small c) by lia. rewrite le1_zxb. mem_after_store.
      astep. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with MIx : mem_inv usegs mx |- _ =>
          pose proof (EINV_rescratch _ _ _ E m mx [CB 1 (take 1 scj); C1 (Z_to_bv 8 c)] EOK EI MU WM MIx eq_refl FR) as EIC;
          pose proof (eframe_scratch E mx [CB 1 (take 1 scj); C1 (Z_to_bv 8 c)] FR) as SCR end end.
      destruct (proj1 (rw_cells_app _ _ [_] _) SCR) as [_ [[_ B1] _]]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in B1.
      replace (esp E + 38 + Z.of_nat 1) with (esp E + 39) in B1 by lia.
      eapply esc_putjoin with (bs := [Z_to_bv 8 c]) (CAP := 1); [exact EIC| exact FRM| exact Hi| exact B1| reflexivity| lia| lia| lia| right; right; lia| exact HK| exact HX].
  Qed.

  Lemma esc_loop : forall (k : nat) (i : Z) (K : machine_state -> Prop) (gp : word),
    0 <= i -> i + Z.of_nat k + 1 = eL E -> EEXIT K gp -> EKLOOP K gp i.
  Proof.
    induction k as [|k IH]; intros i K gp I0 IK HX; unfold EKLOOP; intros until fc'; intros EI FRM.
    - eapply esc_char; [exact EI| exact FRM| lia| intros C; exfalso; lia| exact HX].
    - eapply esc_char; [exact EI| exact FRM| lia| intros _; apply IH; [lia| lia| exact HX]| exact HX].
  Qed.
End Body.

Theorem esc_of_parts : os_putX_stmt -> setfill_stmt -> ins_i_stmt -> esc_stmt.
Proof.
  intros PUT SETF INSI. unfold esc_stmt.
  intros ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sp lo OS SV P L fill pp ep pb dum j148 j284 bs canary.
  intros ST LO GLO AL OSC PUTI FOK QOS OSH OAL SVC QSV SVH SVD PB BL P0 PH PI TPC SSP FRM LB DCC MI.
  unfold ESC_DEPTH, EL_ESC in *.
  pose proof (munch_refl [(sp - 144, sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  hide PB. hide OSC. hide DCC. hide LB. hide SSP.

  step. carve_frame 144%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 144 junk [] [8; 8; 8; 8; 6; 2; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 13 hstep.

  step. step. step. step. if_cases KZ; zify_cond KZ; rewrite ?unsigned_lit in KZ by lia.
  {
    unhide OSC. unhide LB. unhide SSP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (agree_on_of_munch _ _ _ MU WM) as AG end.
    step. do 13 step. step. release_frame FR ST sp. step.
    apply evt_done. unfold esc_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, pb, pp, ep, fill, dum, mx end.
    split; [symmetry; atp_st_eq|]. split; [exact FRM|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros x Hx; lia|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [eapply rw_cells_agree; [exact AG| exact OSC|]; intros a Ha; rewrite os_cellsX_size in Ha; cbn [outside]; lia|].
    split; [exact PUTI|]. split; [exact FOK|]. split; [exact TPC|].
    split; [eapply ssp_cells_agree; [exact AG| | exact SSP]; intros a Ha; unfold ssp_addr, got_ssp, ssp_guard in Ha; cbn [outside]; lia|].
    eapply LOCB_transport; [exact LB| exact MU| exact WM|]. cbv [disjoint_from fst snd]. lia. }

  step. step. step. astep. step. do 8 astep. do 3 (astep; hstep). do 6 astep.
  unhide PB. unhide OSC. unhide DCC. unhide LB. unhide SSP.
  set (E := mkEE sp lo OS SV P bs j148 j284 canary m (take 8 junk) (take 6 (drop 8 (drop 8 (drop 8 (drop 8 junk))))) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  assert (EOK : eenv_ok E). { unfold eenv_ok; cbn; unfold ESC_DEPTH. rewrite BL. repeat split; first [assumption| lia]. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MIx : mem_inv usegs mx |- _ =>
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG;
  assert (EI : EINV 0x1002 0 FILLOK E mx);
  [ split; [| split; [| split; [| split; [| split; [| split; [exact MIx| split; [exact ST| split; [eexists; exact FR|]]]]]]]]
  | eapply evt_eq; [| eapply (esc_loop E EOK PUT SETF INSI (Z.to_nat (L - 1)) 0 _ gp); [lia| cbn; rewrite BL, Z2Nat.id by lia; lia| apply (esc_exit E EOK)| exact EI| exact FRM]];
    unfold ELST; cbn; atp_st_eq ] end end.
  - exists pb, pp, ep, fill, dum. cbn. split; [| split; [exact PUTI| exact FOK]].
    eapply rw_cells_agree; [exact AG| exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia.
  - eapply LOCB_transport; [exact LB| exact MU| exact WM|]. cbv [disjoint_from fst snd]. lia.
  - destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    Ltac trd3 AG C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; cbn [outside]; lia].
    split; [trd3 AG C1|]. split; [trd3 AG C2|]. split; [trd3 AG C3|]. split; [trd3 AG C4|]. split; [trd3 AG C5| trd3 AG C6].
  - exact TPC.
  - cbn. eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn [outside]. lia.
  - cbn. split; [rewrite BL; exact SVC|]. split.
    + eapply bytes_at_agree; [exact AG| exact PB|]. intros a Ha. cbn [outside]. lia.
    + split; [| exact WM]. eapply munch_weaken; [| exact MU]. unfold sub_fp, EW. cbn. intros x Hx. lia.
Qed.
End WithCeiling0.

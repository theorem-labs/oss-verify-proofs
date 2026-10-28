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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_h_defs Atp_kitu Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_esc_iface El_defs El_dump_iface.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition lit (A : Z) (n : nat) : list byte := match image_bytes usegs A n with Some bs => bs | None => [] end.

Lemma lit_bytes : forall A n, ro_bytes_b usegs A (lit A n) = true -> length (lit A n) = n -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  forall m, mem_inv usegs m -> bytes_at usegs m A (lit A n).
Proof.
  intros A n RB L A0 AH m MI. apply ro_bytes_at; [exact MI| lia| rewrite L; lia| apply ro_bytes_b_sound; exact RB].
Qed.

Ltac lit_at A n m MI H HL :=
  pose proof (lit_bytes A n ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) m MI) as H;
  assert (HL : Z.of_nat (length (lit A n)) = Z.of_nat n) by (vm_compute; reflexivity).

Definition dlits (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 0x1126b); C8 (Z_to_bv 64 0x10ac6); C8 (Z_to_bv 64 0x104d1); C8 (Z_to_bv 64 0x131ba); C8 (Z_to_bv 64 0x124eb);
   C8 (Z_to_bv 64 0x12dc8); C8 (Z_to_bv 64 0x12f42); C8 (Z_to_bv 64 0x11272)].
Definition dsaves (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Record denv : Type := mkDE {
  de_q : Z;
  de_lo : Z;
  de_OS : Z;
  de_DOC : Z;
  de_TAPE : Z; de_SBUF : Z; de_tws : list Z; de_sbs : list Z;
  de_canary : word;
  de_m0 : mem;
  de_ra : word; de_s0 : word; de_s1 : word; de_s2 : word; de_s3 : word; de_s4 : word; de_s5 : word; de_s6 : word;
  de_s7 : word; de_s8 : word; de_s9 : word; de_s10 : word; de_s11 : word }.

Definition denv_ok (D : denv) : Prop :=
  tape_wf (Tf (de_tws D)) (Tf (de_sbs D)) (Z.of_nat (length (de_sbs D))) ck_any (Z.of_nat (length (de_tws D)))
  /\ Forall (fun c => 0 <= c < 256) (de_sbs D)
  /\ de_lo D <= de_q D - EL_DUMP_STACK /\ GLOBALS_TOP <= de_lo D /\ de_q D mod 16 = 0
  /\ de_q D <= de_OS D /\ (de_DOC D + 16 <= de_OS D \/ de_OS D + 288 <= de_DOC D) /\ de_OS D + 288 < 2^62 /\ de_q D <= de_DOC D /\ de_DOC D + 16 < 2^62
  /\ 0 < de_TAPE D /\ de_TAPE D + 8 * Z.of_nat (length (de_tws D)) <= de_lo D
  /\ (de_TAPE D + 8 * Z.of_nat (length (de_tws D)) <= 0x10000 \/ 0x111000 <= de_TAPE D)
  /\ 0 < de_SBUF D /\ de_SBUF D + Z.of_nat (length (de_sbs D)) <= de_lo D
  /\ (de_SBUF D + Z.of_nat (length (de_sbs D)) <= 0x10000 \/ 0x111000 <= de_SBUF D)
  /\ de_OS D mod 8 = 0 /\ de_TAPE D mod 8 = 0.

Notation dsp D := (de_q D - 192).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition DINV (lc : list cell) (D : denv) (m : mem) : Prop :=
  (exists (pb : word) (pp ep fill : Z) (dum j148 j284 : list byte),
     rw_cells usegs m (de_OS D) (os_cellsX (de_OS D) pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) /\ PUTINV (de_OS D) pp ep /\ FILLOK fill)
  /\ LOCB m /\ el_dcc m /\ rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] /\ ssp_cells m (de_canary D) /\ mem_inv usegs m
  /\ stk usegs m (de_lo D) (dsp D)
  /\ (exists scr : list byte, rw_cells usegs m (dsp D) (lc ++ [CB 16 scr] ++ dsaves (de_ra D) (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D)
                                                                                  (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D)))
  /\ bytes_at usegs m (de_TAPE D) (u64s (map (Z_to_bv 64) (de_tws D))) /\ bytes_at usegs m (de_SBUF D) (map (Z_to_bv 8) (de_sbs D))
  /\ rw_cells usegs m (de_DOC D) [C8 (Z_to_bv 64 (de_TAPE D)); C8 (Z_to_bv 64 (de_SBUF D))]
  /\ munch (dump_W (de_lo D) (de_q D) (de_OS D)) (de_m0 D) m /\ wmono usegs (de_m0 D) m
  /\ (exists errv : word, rw_cells usegs m LX_ERRNO [C4 errv]).

Section Frame.
  Variable lc : list cell.
  Hypothesis LCS : cells_size lc = 72%nat.

Lemma DINV_frame_facts : forall D m m' W,
  denv_ok D -> DINV lc D m -> munch W m m' -> wmono usegs m m' ->
  (forall a, (dsp D <= a < de_q D \/ (0 <= a < de_lo D /\ ~ (0xef558 <= a < 0xef560) /\ ~ (980196 <= a < 980200)) \/ de_DOC D <= a < de_DOC D + 16) -> outside W a) ->
  el_dcc m' /\ ssp_cells m' (de_canary D)
  /\ (exists scr : list byte, rw_cells usegs m' (dsp D) (lc ++ [CB 16 scr] ++ dsaves (de_ra D) (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D)
                                                                                   (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D)))
  /\ bytes_at usegs m' (de_TAPE D) (u64s (map (Z_to_bv 64) (de_tws D))) /\ bytes_at usegs m' (de_SBUF D) (map (Z_to_bv 8) (de_sbs D))
  /\ rw_cells usegs m' (de_DOC D) [C8 (Z_to_bv 64 (de_TAPE D)); C8 (Z_to_bv 64 (de_SBUF D))].
Proof.
  intros D m m' W (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL) DI MU WM HW.
  destruct DI as (_ & _ & DCC & _ & SSP & _ & _ & (scr & FR) & TB & SB & DOCC & _).
  unfold GLOBALS_TOP, EL_DUMP_STACK in *.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  split; [| split; [| split; [| split; [| split]]]].
  - destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    Ltac trd AG HW C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; apply HW; right; left; lia].
    split; [trd AG HW C1|]. split; [trd AG HW C2|]. split; [trd AG HW C3|]. split; [trd AG HW C4|]. split; [trd AG HW C5| trd AG HW C6].
  - eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. apply HW. right; left. lia.
  - exists scr. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. rewrite cells_size_app, LCS in Ha. cbn in Ha. apply HW. left. lia.
  - eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. apply HW. right; left. clear - Ha T0 TH TI GLO. lia.
  - eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. apply HW. right; left. clear - Ha S0 SH SI GLO. lia.
  - eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn in Ha. apply HW. right; right. lia.
Qed.

Lemma ELX : LX_ERRNO = 980196. Proof. reflexivity. Qed.

Lemma frame_rescr : forall D m cs, cells_size cs = 16%nat ->
  rw_cells usegs m (dsp D) (lc ++ cs ++ dsaves (de_ra D) (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D) (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D)) ->
  exists scr, rw_cells usegs m (dsp D) (lc ++ [CB 16 scr] ++ dsaves (de_ra D) (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D) (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D)).
Proof.
  intros D m cs SZ FR.
  destruct (proj1 (rw_cells_app m (dsp D) lc _) FR) as [F1 F23].
  destruct (proj1 (rw_cells_app m _ cs _) F23) as [F2 F3]. rewrite SZ in F3.
  destruct (rw_cells_forget _ _ _ _ F2) as [scr F2']. rewrite SZ in F2'. exists scr.
  apply (proj2 (rw_cells_app m (dsp D) lc _)). split; [exact F1|].
  apply (proj2 (rw_cells_app m _ [CB 16 scr] _)). split; [exact F2'| exact F3].
Qed.

Lemma frame_scratch : forall D m cs, cells_size cs = 16%nat ->
  rw_cells usegs m (dsp D) (lc ++ cs ++ dsaves (de_ra D) (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D) (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D)) ->
  rw_cells usegs m (dsp D + 72) cs.
Proof.
  intros D m cs SZ FR.
  destruct (proj1 (rw_cells_app m (dsp D) lc _) FR) as [_ F23]. rewrite LCS in F23.
  destruct (proj1 (rw_cells_app m _ cs _) F23) as [F2 _]. replace (dsp D + 72) with (dsp D + Z.of_nat 72) by lia. exact F2.
Qed.

Lemma DINV_reframe : forall lc0 D m m' cs, denv_ok D -> DINV lc0 D m ->
  munch [(dsp D, dsp D + 88)] m m' -> wmono usegs m m' -> mem_inv usegs m' -> cells_size cs = 16%nat ->
  rw_cells usegs m' (dsp D) (lc ++ cs ++ dsaves (de_ra D) (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D) (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D)) ->
  DINV lc D m'.
Proof.
  intros lc0 D m m' cs DOK DI MU WM MI' SZ FR'.
  pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
  pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU0 & WM0 & (errv & ERR)).
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  assert (DCC' : el_dcc m').
  { destruct DCC as (C1 & C2 & C3 & C4 & C5 & C6). unfold el_dcc.
    Ltac trd2 AG C := eapply rw_cells_agree; [exact AG| exact C| intros a Ha; cbn in Ha; cbn [outside]; lia].
    split; [trd2 AG C1|]. split; [trd2 AG C2|]. split; [trd2 AG C3|]. split; [trd2 AG C4|]. split; [trd2 AG C5| trd2 AG C6]. }
  assert (SSP' : ssp_cells m' (de_canary D)).
  { eapply ssp_cells_agree; [exact AG| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn [outside]. lia. }
  assert (TB' : bytes_at usegs m' (de_TAPE D) (u64s (map (Z_to_bv 64) (de_tws D)))).
  { eapply bytes_at_agree; [exact AG| exact TB|]. rewrite u64s_length, length_map. intros a Ha. cbn [outside]. lia. }
  assert (SB' : bytes_at usegs m' (de_SBUF D) (map (Z_to_bv 8) (de_sbs D))).
  { eapply bytes_at_agree; [exact AG| exact SB|]. rewrite length_map. intros a Ha. cbn [outside]. lia. }
  assert (DOCC' : rw_cells usegs m' (de_DOC D) [C8 (Z_to_bv 64 (de_TAPE D)); C8 (Z_to_bv 64 (de_SBUF D))]).
  { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
  destruct (frame_rescr D m' cs SZ FR') as [scr' FR''].
  split. { exists pb, pp, ep, fill, dum, j148, j284. split; [| split; [exact PUTI| exact FOK]].
           eapply rw_cells_agree; [exact AG| exact OSC|]. intros a Ha. rewrite os_cellsX_size in Ha. cbn [outside]. lia. }
  split; [eapply LOCB_transport; [exact LB| exact MU| exact WM|]; cbv [disjoint_from fst snd]; lia|].
  split; [exact DCC'|]. split; [eapply rw_cells_agree; [exact AG| exact TPC|]; intros a Ha; cbn in Ha; cbn [outside]; lia|].
  split; [exact SSP'|]. split; [exact MI'|].
  split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn [disjoint_from]; lia]|].
  split; [exists scr'; exact FR''|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
  split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp, dump_W. cbn [outside]. intros x Hx. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|].
  exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
Qed.

Lemma DINV_rescratch : forall D m m' cs, denv_ok D -> DINV lc D m ->
  munch [(dsp D + 72, dsp D + 88)] m m' -> wmono usegs m m' -> mem_inv usegs m' -> cells_size cs = 16%nat ->
  rw_cells usegs m' (dsp D) (lc ++ cs ++ dsaves (de_ra D) (de_s0 D) (de_s1 D) (de_s2 D) (de_s3 D) (de_s4 D) (de_s5 D) (de_s6 D) (de_s7 D) (de_s8 D) (de_s9 D) (de_s10 D) (de_s11 D)) ->
  DINV lc D m'.
Proof.
  intros D m m' cs DOK DI MU WM MI' SZ FR'. eapply (DINV_reframe lc); [exact DOK| exact DI| | exact WM| exact MI'| exact SZ| exact FR'].
  eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
Qed.

Lemma FILLOK_after : forall f, FILLOK f -> FILLOK (fill_after f).
Proof. intros f H. unfold fill_after, FILLOK in *. destruct (f =? 4294967295) eqn:E; [right; left; reflexivity| exact H]. Qed.

Section Calls.
  Variable D : denv.
  Hypothesis DOK : denv_ok D.
  Hypothesis PUT : os_putX_stmt.

  Let usp_eq : bv_unsigned (Z_to_bv 64 (dsp D)) = dsp D.
  Proof. pose proof DOK as (_ & _ & LO & GLO & AL & QOS & OSD & OSH & QD & DH & _). unfold GLOBALS_TOP, EL_DUMP_STACK in *. apply unsigned_lit. lia. Qed.

  Lemma put_call : forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (BUF N CAP : Z) (bs : list byte),
    DINV lc D m ->
    bytes_at usegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> 0 < BUF -> BUF + CAP < 2 ^ 62 ->
    (BUF + CAP <= de_lo D \/ de_OS D + 288 <= BUF \/ (dsp D <= BUF /\ BUF + CAP <= de_OS D)) ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word), DINV lc D m' ->
       evt usegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (de_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F (ret_pc ra) fc None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 BUF) (Z_to_bv 64 N) a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 PJ_OS_PUT) fc None m (seg_rom usegs)).
  Proof.
    intros until bs. intros DI BB BL NR B0 BH LOC HK.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    eapply evt_cut.
    { eapply (PUT ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (de_lo D) (de_OS D) BUF N CAP fill pp ep pb dum bs j148 j284); rewrite ?usp_eq;
        [exact ST| lia| lia| exact OSC| exact PUTI| exact FOK| exact LB| lia| lia| exact OAL| exact BB| exact BL| lia| lia| lia| lia| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold os_putX_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & ST' & OSC' & PUTI' & LB').
    apply HK.
    destruct (DINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & SSP' & FR' & TB' & SB' & DOCC').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', (fill_after fill), dum', j148, j284; split; [exact OSC'| split; [exact PUTI'| apply FILLOK_after; exact FOK]]|].
    split; [exact LB'|]. split; [exact DCC'|]. split.
    { eapply rw_cells_agree; [exact AG| exact TPC|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, dump_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Lemma ins_call : forall (ENTRY : Z) (VOKP : Z -> Prop), ins_pre ENTRY VOKP 0x1002 0 FILLOK ->
    forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (v : Z),
    DINV lc D m -> frm0 fc -> VOKP v ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F' : bvmap 5 word) (fc' : bv 32), DINV lc D m' -> frm0 fc' ->
       evt usegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (de_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (ret_pc ra) fc' None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).
  Proof.
    intros ENTRY VOKP INS. intros until v. intros DI FRM HV HK.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    eapply evt_cut.
    { eapply (INS ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (de_lo D) (de_OS D) fill v pp ep pb dum j148 j284 (de_canary D)); rewrite ?usp_eq;
        [exact ST| lia| lia| lia| reflexivity| exact OSC| exact PUTI| exact FOK| lia| lia| exact OAL| exact HV| exact TPC| exact SSP| exact FRM| exact LB| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold ins_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & FRM' & FEQ & ST' & SSP' & OSC' & PUTI' & TPC' & LB').
    apply HK; [| exact FRM'].
    destruct (DINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & _ & FR' & TB' & SB' & DOCC').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', (fill_after fill), dum', j148, j284; split; [exact OSC'| split; [exact PUTI'| apply FILLOK_after; exact FOK]]|].
    split; [exact LB'|]. split; [exact DCC'|]. split; [exact TPC'|].
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, dump_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Hypothesis INSD : ins_d_stmt.

  Lemma insd_call : forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DINV lc D m -> frm0 fc ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F' : bvmap 5 word) (fc' : bv 32), DINV lc D m' -> frm0 fc' ->
       evt usegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (de_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (ret_pc ra) fc' None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (de_OS D + 128)) a1 a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 EL_INS_D) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros DI FRM HK.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    eapply evt_cut.
    { eapply (INSD ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (de_lo D) (de_OS D) fill pp ep (reg_get F (Z_to_bv 5 10)) pb dum j148 j284 (de_canary D)); rewrite ?usp_eq;
        [exact ST| lia| lia| lia| reflexivity| exact OSC| exact PUTI| exact FOK| lia| lia| exact OAL| reflexivity| exact TPC| exact SSP| exact FRM| exact LB| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold ins_post in PO. rewrite usp_eq in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & pb' & pp' & ep' & dum' & m' & -> & MU' & WM' & MI' & FRM' & FEQ & ST' & SSP' & OSC' & PUTI' & TPC' & LB').
    apply HK; [| exact FRM'].
    destruct (DINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & _ & FR' & TB' & SB' & DOCC').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', (fill_after fill), dum', j148, j284; split; [exact OSC'| split; [exact PUTI'| apply FILLOK_after; exact FOK]]|].
    split; [exact LB'|]. split; [exact DCC'|]. split; [exact TPC'|].
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, dump_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Hypothesis ESC : esc_stmt.

  Lemma esc_call : forall (K : machine_state -> Prop) (ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (P L : Z) (bs : list byte),
    DINV lc D m -> frm0 fc -> rw_cells usegs m (dsp D + 72) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 L)] ->
    bytes_at usegs m P bs -> Z.of_nat (length bs) = L -> 0 < P -> P + L <= de_lo D -> (P + L <= 0x10000 \/ 0x111000 <= P) ->
    (forall (m' : mem) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F' : bvmap 5 word) (fc' : bv 32), DINV lc D m' -> frm0 fc' ->
       evt usegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) u0 u1 u2 x8 x9 (Z_to_bv 64 (de_OS D + 128)) b1 b2 b3 b4 b5 b6 b7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6) F' (ret_pc ra) fc' None m' (seg_rom usegs))) ->
    evt usegs K (MS (mkR ra (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 (de_OS D + 128)) (Z_to_bv 64 (dsp D + 72)) a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 EL_ESC) fc None m (seg_rom usegs)).
  Proof.
    intros until bs. intros DI FRM SV BB BL P0 PH PI HK.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as ((pb & pp & ep & fill & dum & j148 & j284 & OSC & PUTI & FOK) & LB & DCC & TPC & SSP & MI & ST & FRX & TB & SB & DOCC & MU & WM & (errv & ERR)).
    eapply evt_cut.
    { unfold RATP.
      eapply (ESC ra gp t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc m
                (dsp D) (de_lo D) (de_OS D) (dsp D + 72) P L fill pp ep pb dum j148 j284 bs (de_canary D));
        [exact ST| unfold ESC_DEPTH; lia| lia| clear - AL LO GLO; replace (dsp D) with (de_q D + (-12) * 16) by lia; rewrite Z.mod_add by lia; exact AL
        | exact OSC| exact PUTI| exact FOK| lia| lia| exact OAL| exact SV| lia| lia| left; lia| exact BB| exact BL| exact P0| exact PH| exact PI
        | exact TPC| exact SSP| exact FRM| exact LB| exact DCC| exact MI]. }
    cbv beta. intros ms' PO. unfold esc_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & pb' & pp' & ep' & fill' & dum' & m' & -> & FRM' & MU' & WM' & MI' & ST' & OSC' & PUTI' & FOK' & TPC' & SSP' & LB').
    unfold RATP in HK. apply HK; [| exact FRM'].
    destruct (DINV_frame_facts D m m' _ DOK DI MU' WM') as (DCC' & _ & FR' & TB' & SB' & DOCC').
    { intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    split; [exists pb', pp', ep', fill', dum', j148, j284; split; [exact OSC'| split; [exact PUTI'| exact FOK']]|].
    split; [exact LB'|]. split; [exact DCC'|]. split; [exact TPC'|].
    split; [exact SSP'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact FR'|]. split; [exact TB'|]. split; [exact SB'|]. split; [exact DOCC'|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, dump_W. rewrite ELX. cbn [outside]. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|].
    exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. rewrite ELX in Ha. cbn [outside]. lia.
  Qed.

  Lemma tix_call : forall (K : machine_state -> Prop) (gp t0 t1 t2 x8 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (i RA : Z),
    DINV lc D m -> 0 <= i < Z.of_nat (length (de_tws D)) -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
    (forall (xa1 xa2 xa3 xa4 : word),
       evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 (Z_to_bv 64 (de_DOC D)) (Z_to_bv 64 (de_TAPE D + 8 * i)) xa1 xa2 xa3 xa4 a5 a6 a7
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 RA) fc None m (seg_rom usegs))) ->
    evt usegs K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (dsp D)) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 (Z_to_bv 64 (de_DOC D)) (Z_to_bv 64 (de_DOC D)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) F (Z_to_bv 64 ATP_TIX) fc None m (seg_rom usegs)).
  Proof.
    intros until RA. intros DI HI RA0 RA2 HK.
    pose proof DOK as (WF & SBS & LO & GLO & AL & QOS & OSD & OSH & QD & DH & T0 & TH & TI & S0 & SH & SI & OAL & TAL). unfold GLOBALS_TOP, EL_DUMP_STACK in *.
    pose proof DI as (_ & _ & _ & _ & _ & _ & ST & _ & _ & _ & DOCC & _).
    assert (LO0 : 0 <= de_lo D) by (destruct ST as [? _]; assumption).
    eapply (Atp_kitu.tix_cps K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (de_DOC D) (de_TAPE D) i RA _ DOCC);
      [lia| lia| lia| lia| exact TAL| lia| lia| reflexivity| exact RA0| exact RA2| exact HK].
  Qed.
End Calls.
End Frame.

Lemma dlits72 : forall j0, cells_size (dlits j0) = 72%nat. Proof. reflexivity. Qed.
End WithCeiling0.

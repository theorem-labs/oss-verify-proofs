(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_M_realloc Fz_kit_ra Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_sk F_strlen F_memcpy Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_insert Fz_K_pstr1 Fz_K_pstr2 Fz_K_pstr3 Fz_K_skstmt Fz_K_pstr.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.
Ltac unhide H := unfold hideP in H.

Theorem pstr_first_true : crypto_malloc_stmt -> crypto_calloc_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (C S LK lh1 lh2 ni vi Q1 Q2 Ls : Z) (str slack : list byte) (ps pk pq pl pb : bptr) (B items : Z) (bks : list (list pnode))
         (qpad qnal qcmpt qfreet qcopyt : word),
  (3 <= f)%nat -> croom L (wA (Z.of_nat (length str) + 16) + wA 32 + wA 24) (wB (Z.of_nat (length str) + 16) + wB 32 + wB 24) (wBig (Z.of_nat (length str) + 16) + wBig 32 + wBig 24) ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - PSTR_STACK ->
  a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 (nmz true) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 Ls ->
  0x10000 <= C -> C + 176 <= 0x353000 -> rw_cells usegs m (C + 168) [C8 (Z_to_bv 64 S)] -> C mod 8 = 0 -> bv_unsigned sp mod 16 = 0 ->
  In (ps, S, 48) LBall -> rw_cells usegs m S (psd_cells LK lh1 lh2 ni vi Q1 Q2) -> 0 <= ni -> ni + 1 < 2 ^ 31 -> 0 <= vi -> vi + 1 < 2 ^ 31 ->
  In (pk, LK, 40) LBall -> rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  plh_rep m LBall L (t_of true lh1 lh2) pl pb B items bks -> items < 16 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  In (pq, q_of true Q1 Q2, 56) LBall ->
  rw_cells usegs m (q_of true Q1 Q2) (sk_cells (Z_to_bv 64 0) qpad (Z_to_bv 64 0) (Z_to_bv 64 1) qnal (Z_to_bv 64 0) qcmpt qfreet qcopyt) ->
  ro_bytes usegs Ls (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> (- (Ls + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0x10000 <= Ls -> Ls + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x2c0000 -> Z.of_nat (length str) < 2 ^ 20 ->
  ~ plh_T pl pb bks ps -> ~ plh_T pl pb bks pk -> ~ plh_T pl pb bks pq ->
  ps <> pk -> ps <> pq -> pk <> pq ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (pstr_T1 ps pk pq pl pb bks) [] 3
           (wA (Z.of_nat (length str) + 16) + wA 32 + wA 24) (wB (Z.of_nat (length str) + 16) + wB 32 + wB 24) (wBig (Z.of_nat (length str) + 16) + wBig 32 + wBig 24)
           (pstr_first_res true S LK lh1 lh2 ni vi Q1 Q2 str pl pb B items bks qpad qcmpt qfreet qcopyt LBall L)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM CC0. intros until qcopyt.
  intros Hf ROOM CST SLO EA0 EA1 EA2 EA3 CI1 CI2 CC CAL SP16 INS SCS NI0 NI1 VI0 VI1 INK LKC REP IT16 HASHES INQ QC ROB NONUL NE PAD SLOW SHIGH LEN
         NTS NTK NTQ NSK NSQ NKQ.
  cbn [nmz t_of pidx_off q_of sl_off cnt_of ni_after vi_after] in *.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, PLHI_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia). assert (SP96 : 8512 <= bv_unsigned sp) by (clear - SLO GLO; lia).
  set (len := Z.of_nat (length str)) in *.
  pose proof REP as (OL & RL & _). destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (INL & INB & INNS).
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INS) as RS. pose proof (RHEAP_block_range_proof _ _ _ _ HP INK) as RK.
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INQ) as RQ. pose proof (RHEAP_block_range_proof _ _ _ _ HP INL) as RLH.
  unfold blk_addr, blk_size in RS, RK, RQ, RLH. cbn [fst snd] in RS, RK, RQ, RLH.
  destruct RS as (S0 & _ & _ & SC48 & SIMG). destruct RK as (LK0 & LKAL & _ & LKC40 & LKIMG). destruct RQ as (Q0 & _ & _ & QC56 & QIMG).
  destruct RLH as (_ & _ & _ & _ & LHIMG).
  assert (APSK : S + 48 <= LK \/ LK + 40 <= S) by (eapply (own_apart _ _ _ ps S 48 pk LK 40 HP INS INK); exact NSK).
  assert (APSQ : S + 48 <= Q1 \/ Q1 + 56 <= S) by (eapply (own_apart _ _ _ ps S 48 pq Q1 56 HP INS INQ); exact NSQ).
  assert (APSL : S + 48 <= lh1 \/ lh1 + 104 <= S) by (eapply (own_apart _ _ _ ps S 48 pl lh1 104 HP INS INL); intros E; apply NTS; left; exact E).
  assert (APKL : LK + 40 <= lh1 \/ lh1 + 104 <= LK) by (eapply (own_apart _ _ _ pk LK 40 pl lh1 104 HP INK INL); intros E; apply NTK; left; exact E).
  assert (APKQ : LK + 40 <= Q1 \/ Q1 + 56 <= LK) by (eapply (own_apart _ _ _ pk LK 40 pq Q1 56 HP INK INQ); exact NKQ).
  assert (APQL : Q1 + 56 <= lh1 \/ lh1 + 104 <= Q1) by (eapply (own_apart _ _ _ pq Q1 56 pl lh1 104 HP INQ INL); intros E; apply NTQ; left; exact E).
  assert (STRm : bytes_at usegs m Ls (str ++ [Z_to_bv 8 0])).
  { apply ro_bytes_at; [exact MI| lia| rewrite length_app; cbn [length]; lia|].
    clear - ROB. revert ROB. generalize Ls. induction str as [|b str IH]; intros S0 H; cbn [app ro_bytes] in H |- *; [exact (conj (proj1 H) I)| exact (conj (proj1 H) (IH _ (proj2 H)))]. }
  hide SIMG. hide LKIMG. hide QIMG. hide LHIMG. hide APSK. hide APSQ. hide APSL. hide APKL. hide APKQ. hide APQL.
  destruct (wA_small 24 ltac:(unfold TIER_A_MAX; lia)) as (W24a & W24b & W24c). destruct (wA_small 32 ltac:(unfold TIER_A_MAX; lia)) as (W32a & W32b & W32c).
  (* [comment removed for export] *)
  eapply climpl_evt.
  { eapply (pstr_seg1_true _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m s LBall L C S LK lh1 lh2 ni vi Q1 Q2 Ls lo str ps pk pl pb B items bks);
      first [eassumption | cbn [nmz t_of]; eassumption | lia | idtac]. }
  cbv beta. intros ms1 POST1. destruct POST1 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & j8 & m1 & -> & MU01 & WM01 & MI1 & ST1 & FR1 & LKC1 & REP1).
  cbn [nmz t_of pidx_off] in *.
  (* [comment removed for export] *)
  assert (CST1 : cstate s LBall LB L m1 (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m m1 _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU01| exact WM01| exact MI1| | clear - SPR SLO LO GLO; lia| exact SPB| | rewrite unsigned_lit by (clear - SPR SP96; lia); exact ST1| rewrite unsigned_lit by (clear - SPR SP96; lia); clear - SPB SPR; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor; [| constructor; [| constructor]]].
      + apply (cwin_block _ _ _ (pk, LK, 40)); [exact INK| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia.
      + apply (cwin_block _ _ _ (pl, lh1, 104)); [exact INL| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unhide LKIMG. unhide LHIMG. clear - SPR GLO SLO LKIMG LK0 LHIMG RL. lia. }
  assert (FRM1 : cframe (pstr_T1 ps pk pq pl pb bks) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU01| exact WM01| exact HP| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor; [| constructor; [| constructor]]].
    - apply (cseg_ok_block _ _ _ _ _ (pk, LK, 40)); [exact INK| | unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| unfold blk_addr, blk_size; cbn [fst snd]; clear; lia].
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. right; left. reflexivity.
    - apply (cseg_ok_block _ _ _ _ _ (pl, lh1, 104)); [exact INL| | unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| unfold blk_addr, blk_size; cbn [fst snd]; clear; lia].
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. do 3 right. left. reflexivity. }
  assert (SCS1 : rw_cells usegs m1 S (psd_cells LK lh1 lh2 ni vi Q1 Q2)).
  { eapply rw_cells_transport; [exact SCS| exact MU01| exact WM01|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unhide APSK. unhide APSL. clear - SPR SLO SC48 LO APSK APSL. lia. }
  assert (QC1 : rw_cells usegs m1 Q1 (sk_cells (Z_to_bv 64 0) qpad (Z_to_bv 64 0) (Z_to_bv 64 1) qnal (Z_to_bv 64 0) qcmpt qfreet qcopyt)).
  { eapply rw_cells_transport; [exact QC| exact MU01| exact WM01|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unhide APKQ. unhide APQL. clear - SPR SLO QC56 LO APKQ APQL. lia. }
  clear SCS QC CC LKC STRm.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (pstr_seg2_true CM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s LBall LB L f lo Bd S LK lh1 lh2 ni vi Q1 Q2 Ls str slack ps);
      [clear - Hf; lia| | exact CST1| clear - SP96; lia| unfold CM_STACK, RMALLOC_STACK; clear - SLO; lia| exact FR1| exact INS| exact SCS1| exact NI0| exact NI1| exact VI0| exact VI1| exact ROB| exact NONUL| exact PAD| exact SLOW| exact SHIGH| exact LEN].
    eapply croom_weaken; [exact ROOM| | |]; rewrite ?W24a, ?W24b, ?W24c, ?W32a, ?W32b, ?W32c; subst len; clear; lia. }
  cbv beta. intros f2 L2 st2 ms2 POST2.
  destruct POST2 as (pn & An & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & m2 & -> & FU2 & -> & GR2 & CST2 & FRM2 & RNGA & FR2 & SCS2 & NC2).
  cbn [nmz t_of pidx_off q_of sl_off cnt_of ni_after vi_after] in *.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by (clear - SPR SP96; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _]. cbn [map blk_id fst] in ND2. inversion ND2 as [|xx ll PNF _]; subst xx ll.
  assert (PNEW : forall q Aq nq, In (q, Aq, nq) LBall -> pn <> q).
  { intros q Aq nq Hin E. apply PNF. subst q. apply in_map_iff. exists (pn, Aq, nq). auto. }
  pose proof RNGA as (An0 & _ & _ & AnC & AnIMG). hide AnIMG.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk, LK, 40) CFR2 LKC1 INK (fun E => NSK E) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, mutex_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)) as LKC2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pq, Q1, 56) CFR2 QC1 INQ (fun E => NSQ E) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, sk_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)) as QC2.
  pose proof (plh_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 FRM2 ltac:(intros q Hq E; apply NTS; rewrite E; exact Hq)) as REP2.
  clear LKC1 QC1 REP1 FR1 SCS1.
  assert (APAQ : An + (len + 16) <= Q1 \/ Q1 + 56 <= An) by (eapply (own_apart _ _ _ pn An (len + 16) pq Q1 56 HP2); [left; reflexivity| right; exact INQ| exact (PNEW _ _ _ INQ)]).
  hide APAQ.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { unfold FZ_SK_PUSH_. eapply (T_sk_push_first_spec CC0) with (psk := pq) (A := Q1) (lo := lo) (B := Bd);
      [clear - Hf FU2; lia| | exact CST2| unfold SK_PUSH_STACK, SK_INSERT_STACK, SK_RESERVE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; rewrite unsigned_lit by (clear - SPR SP96; lia); clear - SLO; lia| reflexivity| right; exact INQ| exact QC2].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GR2]| | |]; rewrite ?W24a, ?W24b, ?W24c, ?W32a, ?W32b, ?W32c; subst len; clear; lia. }
  cbv beta. intros f3 L3 st3 ms3 POST3.
  destruct POST3 as (vq & m3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (pd & D & -> & -> & -> & RNGD & QC3 & DC3)).
  destruct RET3 as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
  cret_lit. rewrite (unsigned_lit (bv_unsigned sp + -96)) in FRM3 by (clear - SPR SP96; lia). 
  pose proof FRM3 as (CFR3 & KP3 & _).
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  pose proof RNGD as (D0 & _ & _ & DC8 & DIMG). hide DIMG.
  set (LB2 := (pn, An, Z.of_nat (length str) + 16) :: LBall) in *. set (L2 := (pn, Z.of_nat (length str) + 16) :: L) in *.
  assert (INQ2 : In (pq, Q1, 56) LB2) by (right; exact INQ).
  assert (INS2 : In (ps, S, 48) LB2) by (right; exact INS). assert (INK2 : In (pk, LK, 40) LB2) by (right; exact INK). assert (INA2 : In (pn, An, len + 16) LB2) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _]. cbn [map blk_id fst] in ND3. inversion ND3 as [|xx ll PDF _]; subst xx ll.
  assert (PDNEW : forall q Aq nq, In (q, Aq, nq) LB2 -> pd <> q).
  { intros q Aq nq Hin E. apply PDF. subst q. change (In pd (map blk_id LB2)). apply in_map_iff. exists (pd, Aq, nq). auto. }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(clear; lia)) as FR3.
  assert (SCS3 : rw_cells usegs m3 S (psd_cells LK lh1 lh2 (ni_after true ni) (vi_after true vi) Q1 Q2)).
  { cbn [ni_after vi_after]. exact (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR3 SCS2 INS2 (fun E => NSQ (eq_sym E)) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, psd_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)). }
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk, LK, 40) CFR3 LKC2 INK2 (fun E => NKQ (eq_sym E)) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, mutex_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)) as LKC3.
  assert (NC3 : rw_cells usegs m3 An [C8 (Z_to_bv 64 (An + 12)); C4 (Z_to_bv 64 (cnt_of true ni vi + 1)); CB (Datatypes.S (length str)) (str ++ [Z_to_bv 8 0])]).
  { cbn [cnt_of]. exact (cfr_cells_block _ _ _ _ _ _ _ _ (pn, An, len + 16) CFR3 NC2 INA2 (fun E => PNEW _ _ _ INQ (eq_sym E)) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; subst len; clear; lia)). }
  assert (REP3 : plh_rep m3 ((pd, D, 32) :: LB2) ((pd, 32) :: L2) lh1 pl pb B items bks).
  { eapply plh_rep_cframe; [exact REP2| exact FRM3|]. intros q Hq E. apply NTQ. rewrite E. exact Hq. }
  assert (NTN : ~ plh_T pl pb bks pn).
  { destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (IL0 & IB0 & IN0). intros [E|[E|E]].
    - exact (PNEW _ _ _ IL0 E). - exact (PNEW _ _ _ IB0 E).
    - apply in_map_iff in E. destruct E as (pa & E1 & E). apply in_map_iff in E. destruct E as (n & E2 & E). pose proof (IN0 n E) as X. rewrite E2, E1 in X. exact (PNEW _ _ _ X eq_refl). }
  clear FR2 SCS2 LKC2 NC2 REP2 QC2.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (pstr_seg3 CM) with (r := 1) (m := m3) (s := st3) (LBall := (pd, D, 32) :: LB2) (LB := LB) (L := (pd, 32) :: L2) (f := f3) (lo := lo) (Bd := Bd) (S := S) (LK := LK) (lh1 := lh1) (lh2 := lh2)
        (ni := ni_after true ni) (vi := vi_after true vi) (Q1 := Q1) (Q2 := Q2) (lh := lh1) (Ls := Ls) (An := An) (idx := cnt_of true ni vi + 1) (str := str)
        (ps := ps) (pk := pk) (pn := pn) (pl := pl) (pb := pb) (B := B) (items := items) (bks := bks) (j8 := j8);
      [clear - Hf FU2 FU3; lia| | exact CST3| clear - SP96; lia| exact SPB| unfold PLHI_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| exact SP16| exact FR3| right; exact INS2| exact SCS3| right; exact INK2| exact LKC3| exact REP3| exact IT16
      | right; subst len; exact INA2| exact NC3| exact NONUL| exact NE| exact LEN| cbn [cnt_of]; clear - NI0 NI1 VI0 VI1; lia| clear; lia| exact HASHES
      | exact NTS| exact NTK| exact NTN| exact NSK| exact (PNEW _ _ _ INS)| exact (PNEW _ _ _ INK)].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR2 GR3)]| | |]; rewrite ?W24a, ?W24b, ?W24c, ?W32a, ?W32b, ?W32c; subst len; clear; lia. }
  cbv beta. intros f4 L4 st4 ms4 POST4.
  destruct POST4 as (pnn & N & z0 & z1 & z2 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m4 & -> & FU4 & -> & GR4 & CST4 & FRM4 & RNGN & REP4 & LKC4).
  pose proof FRM4 as (CFR4 & _).
  apply climpl_done. exists (Z_to_bv 64 (cnt_of true ni vi + 1)), m4, ((pnn, N, 24) :: (pd, D, 32) :: LB2).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear - Hf FU2 FU3 FU4; lia|].
  split. { pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR2 GR3) GR4) as GR. subst L2 len. exact GR. }
  split; [exact CST4|].
  split. { unfold pstr_T1. eapply cframe_call; [eapply cframe_call; [eapply cframe_call; [exact FRM1| exact FRM2| clear - SP96; lia| intros a X; exact X|]| exact FRM3| clear - SP96; lia| intros a X; exact X|]| exact FRM4| clear - SP96; lia| intros a X; exact X|].
    - intros q _ NT E. apply NT. left. symmetry. exact E.
    - intros q _ NT E. apply NT. subst q. do 2 right; left; reflexivity.
    - intros q _ NT [E|E]; apply NT; [subst q; right; left; reflexivity| do 3 right; exact E]. }
  exists pn, An, pd, D, pnn, N. cbv zeta.
  split; [reflexivity|]. split; [subst LB2 len; reflexivity|]. split; [subst L2 len; reflexivity|]. split; [subst len; exact RNGA|]. split; [exact RNGD|]. split; [exact RNGN|].
  assert (INS3 : In (ps, S, 48) ((pd, D, 32) :: LB2)) by (right; exact INS2). assert (INQ3 : In (pq, Q1, 56) ((pd, D, 32) :: LB2)) by (right; exact INQ2).
  assert (IND3 : In (pd, D, 32) ((pd, D, 32) :: LB2)) by (left; reflexivity). assert (INA3 : In (pn, An, len + 16) ((pd, D, 32) :: LB2)) by (right; exact INA2).
  split. { exact (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR4 SCS3 INS3 ltac:(intros [E|E]; [exact (NSK E)| exact (NTS E)]) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, psd_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)). }
  split; [exact LKC4|]. split; [subst LB2 L2 len; exact REP4|].
  assert (NTPD : ~ plh_T pl pb bks pd).
  { destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (IL0 & IB0 & IN0). intros [E|[E|E]].
    - exact (PDNEW _ _ _ (or_intror IL0) E). - exact (PDNEW _ _ _ (or_intror IB0) E).
    - apply in_map_iff in E. destruct E as (pa & E1 & E). apply in_map_iff in E. destruct E as (n & E2 & E). pose proof (IN0 n E) as X. rewrite E2, E1 in X. exact (PDNEW _ _ _ (or_intror X) eq_refl). }
  split. { exact (cfr_cells_block _ _ _ _ _ _ _ _ (pq, Q1, 56) CFR4 QC3 INQ3 ltac:(intros [E|E]; [exact (NKQ (eq_sym E))| exact (NTQ E)]) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, sk_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)). }
  split. { exact (cfr_cells_block _ _ _ _ _ _ _ _ (pd, D, 32) CFR4 DC3 IND3 ltac:(intros [E|E]; [exact (PDNEW _ _ _ (or_intror INK) E)| exact (NTPD E)]) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; clear; lia)). }
  exact (cfr_cells_block _ _ _ _ _ _ _ _ (pn, An, len + 16) CFR4 NC3 INA3 ltac:(intros [E|E]; [exact (PNEW _ _ _ INK E)| exact (NTN E)]) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; subst len; clear; lia)).
Qed.

Theorem pstr_first_false : crypto_malloc_stmt -> crypto_calloc_stmt ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (C S LK lh1 lh2 ni vi Q1 Q2 Ls : Z) (str slack : list byte) (ps pk pq pl pb : bptr) (B items : Z) (bks : list (list pnode))
         (qpad qnal qcmpt qfreet qcopyt : word),
  (3 <= f)%nat -> croom L (wA (Z.of_nat (length str) + 16) + wA 32 + wA 24) (wB (Z.of_nat (length str) + 16) + wB 32 + wB 24) (wBig (Z.of_nat (length str) + 16) + wBig 32 + wBig 24) ->
  cstate s LBall LB L m sp tp lo Bd -> lo <= bv_unsigned sp - PSTR_STACK ->
  a0 = Z_to_bv 64 C -> a1 = Z_to_bv 64 (nmz false) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 Ls ->
  0x10000 <= C -> C + 176 <= 0x353000 -> rw_cells usegs m (C + 168) [C8 (Z_to_bv 64 S)] -> C mod 8 = 0 -> bv_unsigned sp mod 16 = 0 ->
  In (ps, S, 48) LBall -> rw_cells usegs m S (psd_cells LK lh1 lh2 ni vi Q1 Q2) -> 0 <= ni -> ni + 1 < 2 ^ 31 -> 0 <= vi -> vi + 1 < 2 ^ 31 ->
  In (pk, LK, 40) LBall -> rw_cells usegs m LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  plh_rep m LBall L (t_of false lh1 lh2) pl pb B items bks -> items < 16 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  In (pq, q_of false Q1 Q2, 56) LBall ->
  rw_cells usegs m (q_of false Q1 Q2) (sk_cells (Z_to_bv 64 0) qpad (Z_to_bv 64 0) (Z_to_bv 64 1) qnal (Z_to_bv 64 0) qcmpt qfreet qcopyt) ->
  ro_bytes usegs Ls (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> (- (Ls + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0x10000 <= Ls -> Ls + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x2c0000 -> Z.of_nat (length str) < 2 ^ 20 ->
  ~ plh_T pl pb bks ps -> ~ plh_T pl pb bks pk -> ~ plh_T pl pb bks pq ->
  ps <> pk -> ps <> pq -> pk <> pq ->
  climpl f L s
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo Bd (pstr_T1 ps pk pq pl pb bks) [] 3
           (wA (Z.of_nat (length str) + 16) + wA 32 + wA 24) (wB (Z.of_nat (length str) + 16) + wB 32 + wB 24) (wBig (Z.of_nat (length str) + 16) + wBig 32 + wBig 24)
           (pstr_first_res false S LK lh1 lh2 ni vi Q1 Q2 str pl pb B items bks qpad qcmpt qfreet qcopyt LBall L)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM CC0. intros until qcopyt.
  intros Hf ROOM CST SLO EA0 EA1 EA2 EA3 CI1 CI2 CC CAL SP16 INS SCS NI0 NI1 VI0 VI1 INK LKC REP IT16 HASHES INQ QC ROB NONUL NE PAD SLOW SHIGH LEN
         NTS NTK NTQ NSK NSQ NKQ.
  cbn [nmz t_of pidx_off q_of sl_off cnt_of ni_after vi_after] in *.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold PSTR_STACK, SK_PUSH_GROW_STACK, CRE_STACK, RREALLOC_STACK, PLHI_STACK, CM_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia). assert (SP96 : 8512 <= bv_unsigned sp) by (clear - SLO GLO; lia).
  set (len := Z.of_nat (length str)) in *.
  pose proof REP as (OL & RL & _). destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (INL & INB & INNS).
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INS) as RS. pose proof (RHEAP_block_range_proof _ _ _ _ HP INK) as RK.
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INQ) as RQ. pose proof (RHEAP_block_range_proof _ _ _ _ HP INL) as RLH.
  unfold blk_addr, blk_size in RS, RK, RQ, RLH. cbn [fst snd] in RS, RK, RQ, RLH.
  destruct RS as (S0 & _ & _ & SC48 & SIMG). destruct RK as (LK0 & LKAL & _ & LKC40 & LKIMG). destruct RQ as (Q0 & _ & _ & QC56 & QIMG).
  destruct RLH as (_ & _ & _ & _ & LHIMG).
  assert (APSK : S + 48 <= LK \/ LK + 40 <= S) by (eapply (own_apart _ _ _ ps S 48 pk LK 40 HP INS INK); exact NSK).
  assert (APSQ : S + 48 <= Q2 \/ Q2 + 56 <= S) by (eapply (own_apart _ _ _ ps S 48 pq Q2 56 HP INS INQ); exact NSQ).
  assert (APSL : S + 48 <= lh2 \/ lh2 + 104 <= S) by (eapply (own_apart _ _ _ ps S 48 pl lh2 104 HP INS INL); intros E; apply NTS; left; exact E).
  assert (APKL : LK + 40 <= lh2 \/ lh2 + 104 <= LK) by (eapply (own_apart _ _ _ pk LK 40 pl lh2 104 HP INK INL); intros E; apply NTK; left; exact E).
  assert (APKQ : LK + 40 <= Q2 \/ Q2 + 56 <= LK) by (eapply (own_apart _ _ _ pk LK 40 pq Q2 56 HP INK INQ); exact NKQ).
  assert (APQL : Q2 + 56 <= lh2 \/ lh2 + 104 <= Q2) by (eapply (own_apart _ _ _ pq Q2 56 pl lh2 104 HP INQ INL); intros E; apply NTQ; left; exact E).
  assert (STRm : bytes_at usegs m Ls (str ++ [Z_to_bv 8 0])).
  { apply ro_bytes_at; [exact MI| lia| rewrite length_app; cbn [length]; lia|].
    clear - ROB. revert ROB. generalize Ls. induction str as [|b str IH]; intros S0 H; cbn [app ro_bytes] in H |- *; [exact (conj (proj1 H) I)| exact (conj (proj1 H) (IH _ (proj2 H)))]. }
  hide SIMG. hide LKIMG. hide QIMG. hide LHIMG. hide APSK. hide APSQ. hide APSL. hide APKL. hide APKQ. hide APQL.
  destruct (wA_small 24 ltac:(unfold TIER_A_MAX; lia)) as (W24a & W24b & W24c). destruct (wA_small 32 ltac:(unfold TIER_A_MAX; lia)) as (W32a & W32b & W32c).
  (* [comment removed for export] *)
  eapply climpl_evt.
  { eapply (pstr_seg1_false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m s LBall L C S LK lh1 lh2 ni vi Q1 Q2 Ls lo str ps pk pl pb B items bks);
      first [eassumption | cbn [nmz t_of]; eassumption | lia | idtac]. }
  cbv beta. intros ms1 POST1. destruct POST1 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & j8 & m1 & -> & MU01 & WM01 & MI1 & ST1 & FR1 & LKC1 & REP1).
  cbn [nmz t_of pidx_off] in *.
  (* [comment removed for export] *)
  assert (CST1 : cstate s LBall LB L m1 (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m m1 _ _ tp lo Bd (bv_unsigned sp)); [exact CST| exact MU01| exact WM01| exact MI1| | clear - SPR SLO LO GLO; lia| exact SPB| | rewrite unsigned_lit by (clear - SPR SP96; lia); exact ST1| rewrite unsigned_lit by (clear - SPR SP96; lia); clear - SPB SPR; lia].
    - constructor; [apply cwin_stack; clear - SPR SLO LO GLO; lia| constructor; [| constructor; [| constructor]]].
      + apply (cwin_block _ _ _ (pk, LK, 40)); [exact INK| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia.
      + apply (cwin_block _ _ _ (pl, lh2, 104)); [exact INL| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unhide LKIMG. unhide LHIMG. clear - SPR GLO SLO LKIMG LK0 LHIMG RL. lia. }
  assert (FRM1 : cframe (pstr_T1 ps pk pq pl pb bks) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU01| exact WM01| exact HP| clear - LO SLO SPR GLO; lia|]. constructor; [apply cseg_ok_stack; clear - LO SLO SPR GLO; lia| constructor; [| constructor; [| constructor]]].
    - apply (cseg_ok_block _ _ _ _ _ (pk, LK, 40)); [exact INK| | unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| unfold blk_addr, blk_size; cbn [fst snd]; clear; lia].
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. right; left. reflexivity.
    - apply (cseg_ok_block _ _ _ _ _ (pl, lh2, 104)); [exact INL| | unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| unfold blk_addr, blk_size; cbn [fst snd]; clear; lia].
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. do 3 right. left. reflexivity. }
  assert (SCS1 : rw_cells usegs m1 S (psd_cells LK lh1 lh2 ni vi Q1 Q2)).
  { eapply rw_cells_transport; [exact SCS| exact MU01| exact WM01|]. unfold psd_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unhide APSK. unhide APSL. clear - SPR SLO SC48 LO APSK APSL. lia. }
  assert (QC1 : rw_cells usegs m1 Q2 (sk_cells (Z_to_bv 64 0) qpad (Z_to_bv 64 0) (Z_to_bv 64 1) qnal (Z_to_bv 64 0) qcmpt qfreet qcopyt)).
  { eapply rw_cells_transport; [exact QC| exact MU01| exact WM01|]. unfold sk_cells. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unhide APKQ. unhide APQL. clear - SPR SLO QC56 LO APKQ APQL. lia. }
  clear SCS QC CC LKC STRm.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (pstr_seg2_false CM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 s LBall LB L f lo Bd S LK lh1 lh2 ni vi Q1 Q2 Ls str slack ps);
      [clear - Hf; lia| | exact CST1| clear - SP96; lia| unfold CM_STACK, RMALLOC_STACK; clear - SLO; lia| exact FR1| exact INS| exact SCS1| exact NI0| exact NI1| exact VI0| exact VI1| exact ROB| exact NONUL| exact PAD| exact SLOW| exact SHIGH| exact LEN].
    eapply croom_weaken; [exact ROOM| | |]; rewrite ?W24a, ?W24b, ?W24c, ?W32a, ?W32b, ?W32c; subst len; clear; lia. }
  cbv beta. intros f2 L2 st2 ms2 POST2.
  destruct POST2 as (pn & An & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & m2 & -> & FU2 & -> & GR2 & CST2 & FRM2 & RNGA & FR2 & SCS2 & NC2).
  cbn [nmz t_of pidx_off q_of sl_off cnt_of ni_after vi_after] in *.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). rewrite unsigned_lit in ST2 by (clear - SPR SP96; lia).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _]. cbn [map blk_id fst] in ND2. inversion ND2 as [|xx ll PNF _]; subst xx ll.
  assert (PNEW : forall q Aq nq, In (q, Aq, nq) LBall -> pn <> q).
  { intros q Aq nq Hin E. apply PNF. subst q. apply in_map_iff. exists (pn, Aq, nq). auto. }
  pose proof RNGA as (An0 & _ & _ & AnC & AnIMG). hide AnIMG.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk, LK, 40) CFR2 LKC1 INK (fun E => NSK E) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, mutex_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)) as LKC2.
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pq, Q2, 56) CFR2 QC1 INQ (fun E => NSQ E) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, sk_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)) as QC2.
  pose proof (plh_rep_cframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 FRM2 ltac:(intros q Hq E; apply NTS; rewrite E; exact Hq)) as REP2.
  clear LKC1 QC1 REP1 FR1 SCS1.
  assert (APAQ : An + (len + 16) <= Q2 \/ Q2 + 56 <= An) by (eapply (own_apart _ _ _ pn An (len + 16) pq Q2 56 HP2); [left; reflexivity| right; exact INQ| exact (PNEW _ _ _ INQ)]).
  hide APAQ.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { unfold FZ_SK_PUSH_. eapply (T_sk_push_first_spec CC0) with (psk := pq) (A := Q2) (lo := lo) (B := Bd);
      [clear - Hf FU2; lia| | exact CST2| unfold SK_PUSH_STACK, SK_INSERT_STACK, SK_RESERVE_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; rewrite unsigned_lit by (clear - SPR SP96; lia); clear - SLO; lia| reflexivity| right; exact INQ| exact QC2].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact GR2]| | |]; rewrite ?W24a, ?W24b, ?W24c, ?W32a, ?W32b, ?W32c; subst len; clear; lia. }
  cbv beta. intros f3 L3 st3 ms3 POST3.
  destruct POST3 as (vq & m3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (pd & D & -> & -> & -> & RNGD & QC3 & DC3)).
  destruct RET3 as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
  cret_lit. rewrite (unsigned_lit (bv_unsigned sp + -96)) in FRM3 by (clear - SPR SP96; lia). 
  pose proof FRM3 as (CFR3 & KP3 & _).
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  pose proof RNGD as (D0 & _ & _ & DC8 & DIMG). hide DIMG.
  set (LB2 := (pn, An, Z.of_nat (length str) + 16) :: LBall) in *. set (L2 := (pn, Z.of_nat (length str) + 16) :: L) in *.
  assert (INQ2 : In (pq, Q2, 56) LB2) by (right; exact INQ).
  assert (INS2 : In (ps, S, 48) LB2) by (right; exact INS). assert (INK2 : In (pk, LK, 40) LB2) by (right; exact INK). assert (INA2 : In (pn, An, len + 16) LB2) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _]. cbn [map blk_id fst] in ND3. inversion ND3 as [|xx ll PDF _]; subst xx ll.
  assert (PDNEW : forall q Aq nq, In (q, Aq, nq) LB2 -> pd <> q).
  { intros q Aq nq Hin E. apply PDF. subst q. change (In pd (map blk_id LB2)). apply in_map_iff. exists (pd, Aq, nq). auto. }
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FR2 ltac:(clear; lia)) as FR3.
  assert (SCS3 : rw_cells usegs m3 S (psd_cells LK lh1 lh2 (ni_after false ni) (vi_after false vi) Q1 Q2)).
  { cbn [ni_after vi_after]. exact (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR3 SCS2 INS2 (fun E => NSQ (eq_sym E)) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, psd_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)). }
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pk, LK, 40) CFR3 LKC2 INK2 (fun E => NKQ (eq_sym E)) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, mutex_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)) as LKC3.
  assert (NC3 : rw_cells usegs m3 An [C8 (Z_to_bv 64 (An + 12)); C4 (Z_to_bv 64 (cnt_of false ni vi + 1)); CB (Datatypes.S (length str)) (str ++ [Z_to_bv 8 0])]).
  { cbn [cnt_of]. exact (cfr_cells_block _ _ _ _ _ _ _ _ (pn, An, len + 16) CFR3 NC2 INA2 (fun E => PNEW _ _ _ INQ (eq_sym E)) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; subst len; clear; lia)). }
  assert (REP3 : plh_rep m3 ((pd, D, 32) :: LB2) ((pd, 32) :: L2) lh2 pl pb B items bks).
  { eapply plh_rep_cframe; [exact REP2| exact FRM3|]. intros q Hq E. apply NTQ. rewrite E. exact Hq. }
  assert (NTN : ~ plh_T pl pb bks pn).
  { destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (IL0 & IB0 & IN0). intros [E|[E|E]].
    - exact (PNEW _ _ _ IL0 E). - exact (PNEW _ _ _ IB0 E).
    - apply in_map_iff in E. destruct E as (pa & E1 & E). apply in_map_iff in E. destruct E as (n & E2 & E). pose proof (IN0 n E) as X. rewrite E2, E1 in X. exact (PNEW _ _ _ X eq_refl). }
  clear FR2 SCS2 LKC2 NC2 REP2 QC2.
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (pstr_seg3 CM) with (r := 1) (m := m3) (s := st3) (LBall := (pd, D, 32) :: LB2) (LB := LB) (L := (pd, 32) :: L2) (f := f3) (lo := lo) (Bd := Bd) (S := S) (LK := LK) (lh1 := lh1) (lh2 := lh2)
        (ni := ni_after false ni) (vi := vi_after false vi) (Q1 := Q1) (Q2 := Q2) (lh := lh2) (Ls := Ls) (An := An) (idx := cnt_of false ni vi + 1) (str := str)
        (ps := ps) (pk := pk) (pn := pn) (pl := pl) (pb := pb) (B := B) (items := items) (bks := bks) (j8 := j8);
      [clear - Hf FU2 FU3; lia| | exact CST3| clear - SP96; lia| exact SPB| unfold PLHI_STACK, CM_STACK, RMALLOC_STACK; clear - SLO; lia| exact SP16| exact FR3| right; exact INS2| exact SCS3| right; exact INK2| exact LKC3| exact REP3| exact IT16
      | right; subst len; exact INA2| exact NC3| exact NONUL| exact NE| exact LEN| cbn [cnt_of]; clear - NI0 NI1 VI0 VI1; lia| clear; lia| exact HASHES
      | exact NTS| exact NTK| exact NTN| exact NSK| exact (PNEW _ _ _ INS)| exact (PNEW _ _ _ INK)].
    eapply croom_weaken; [eapply croom_grow; [exact ROOM| exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR2 GR3)]| | |]; rewrite ?W24a, ?W24b, ?W24c, ?W32a, ?W32b, ?W32c; subst len; clear; lia. }
  cbv beta. intros f4 L4 st4 ms4 POST4.
  destruct POST4 as (pnn & N & z0 & z1 & z2 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m4 & -> & FU4 & -> & GR4 & CST4 & FRM4 & RNGN & REP4 & LKC4).
  pose proof FRM4 as (CFR4 & _).
  apply climpl_done. exists (Z_to_bv 64 (cnt_of false ni vi + 1)), m4, ((pnn, N, 24) :: (pd, D, 32) :: LB2).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear - Hf FU2 FU3 FU4; lia|].
  split. { pose proof (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR2 GR3) GR4) as GR. subst L2 len. exact GR. }
  split; [exact CST4|].
  split. { unfold pstr_T1. eapply cframe_call; [eapply cframe_call; [eapply cframe_call; [exact FRM1| exact FRM2| clear - SP96; lia| intros a X; exact X|]| exact FRM3| clear - SP96; lia| intros a X; exact X|]| exact FRM4| clear - SP96; lia| intros a X; exact X|].
    - intros q _ NT E. apply NT. left. symmetry. exact E.
    - intros q _ NT E. apply NT. subst q. do 2 right; left; reflexivity.
    - intros q _ NT [E|E]; apply NT; [subst q; right; left; reflexivity| do 3 right; exact E]. }
  exists pn, An, pd, D, pnn, N. cbv zeta.
  split; [reflexivity|]. split; [subst LB2 len; reflexivity|]. split; [subst L2 len; reflexivity|]. split; [subst len; exact RNGA|]. split; [exact RNGD|]. split; [exact RNGN|].
  assert (INS3 : In (ps, S, 48) ((pd, D, 32) :: LB2)) by (right; exact INS2). assert (INQ3 : In (pq, Q2, 56) ((pd, D, 32) :: LB2)) by (right; exact INQ2).
  assert (IND3 : In (pd, D, 32) ((pd, D, 32) :: LB2)) by (left; reflexivity). assert (INA3 : In (pn, An, len + 16) ((pd, D, 32) :: LB2)) by (right; exact INA2).
  split. { exact (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR4 SCS3 INS3 ltac:(intros [E|E]; [exact (NSK E)| exact (NTS E)]) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, psd_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)). }
  split; [exact LKC4|]. split; [subst LB2 L2 len; exact REP4|].
  assert (NTPD : ~ plh_T pl pb bks pd).
  { destruct (plh_rep_blocks _ _ _ _ _ _ _ _ _ REP) as (IL0 & IB0 & IN0). intros [E|[E|E]].
    - exact (PDNEW _ _ _ (or_intror IL0) E). - exact (PDNEW _ _ _ (or_intror IB0) E).
    - apply in_map_iff in E. destruct E as (pa & E1 & E). apply in_map_iff in E. destruct E as (n & E2 & E). pose proof (IN0 n E) as X. rewrite E2, E1 in X. exact (PDNEW _ _ _ (or_intror X) eq_refl). }
  split. { exact (cfr_cells_block _ _ _ _ _ _ _ _ (pq, Q2, 56) CFR4 QC3 INQ3 ltac:(intros [E|E]; [exact (NKQ (eq_sym E))| exact (NTQ E)]) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size, sk_cells; cbn [fst snd cells_size csize Nat.add]; clear; lia)). }
  split. { exact (cfr_cells_block _ _ _ _ _ _ _ _ (pd, D, 32) CFR4 DC3 IND3 ltac:(intros [E|E]; [exact (PDNEW _ _ _ (or_intror INK) E)| exact (NTPD E)]) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; clear; lia)). }
  exact (cfr_cells_block _ _ _ _ _ _ _ _ (pn, An, len + 16) CFR4 NC3 INA3 ltac:(intros [E|E]; [exact (PNEW _ _ _ INK E)| exact (NTN E)]) ltac:(unfold blk_addr; cbn [fst snd]; clear; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; subst len; clear; lia)).
Qed.
End WithCeiling0.

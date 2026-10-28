(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr Mem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_libiface_pem D_agree D_clx PLayout I_lkit I_ut Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_writec Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux3 Fz_G_kit Fz_W7_defs Fz_W7_segs Fz_W7_inv Fz_W7_calls Fz_W7_x Fz_W7_f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Lemma w7p_grn : forall blen boff s x, blen < 2 ^ 26 -> 0 <= boff <= blen -> 254 * s <= 255 * boff + 254 * 512 -> 0 <= x -> x <= blen - boff + s ->
  gr_n x <= 2 ^ 27.
Proof. intros blen boff s x H1 H2 H3 H4 H5. unfold gr_n. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition W7P_WCOST : Z := 1 + (2 * 2 ^ 27 + 16384).
Lemma w7p_cost : forall len n max, gr_n (len + n) <= 2 ^ 27 -> 0 <= puts_cost len n max <= W7P_WCOST.
Proof.
  intros len n max G. unfold puts_cost, W7P_WCOST, mcost. destruct (Z.ltb_spec max (len + n)) as [L1|L1]; [destruct (Z.leb_spec (gr_n (len + n)) 64512) as [L2|L2]|].
  - clear. unfold Z.pow. cbn. lia.
  - clear - G L2. split; [lia|]. lia.
  - clear; lia.
Qed.
(* [comment removed for export] *)
Definition W7P_CREDIT : Z := 3 * W7P_WCOST + 2.

Section W7P.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Variable LIB : list (Z * Z) -> mem -> Prop.
Variable REST : mem -> Prop.
Variable REST_fp : Z -> Prop.
Hypothesis REST_agree : forall m m', REST m -> agree_on REST_fp m m' -> REST m'.
Hypothesis REST_fp_where : forall a, REST_fp a -> client_static a /\ outside LIB_W a /\ ~ cl_cell a.
Hypothesis SLC : strlen_icontract RT.
Hypothesis C_BW : bio_writeg_stmt RT FZ_SITES FZ_CALLS.
Hypothesis C_B0 : bio_write0_stmt RT.
Hypothesis F7P : F7_stmt RT libenv errst_live FZ_SITES FZ_CALLS LIB REST.

Local Notation w7a := (w7a RT).
Local Notation w7_com := (w7_com RT libenv FZ_SITES FZ_CALLS REST).
Local Notation w7_at := (w7_at RT LIB).
Local Notation w7_mf := (w7_mf RT).
Local Notation P5 x := (x RT libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P6 x := (x RT AF libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P7 x := (x RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation PC x := (x RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS REST REST_fp REST_agree REST_fp_where) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma w7_out_bioW : forall (en : w7a) Σ m crem K max rest x, w7_com en Σ m crem (mbio_ent K max ++ rest) ->
  ((exists p n, In (p, n) rest /\ p <= x < p + n) \/ (a_f RT en + 24 <= x < a_f RT en + 248) \/ (a_sp1 RT en <= x < USTACK_TOP) \/ (a_E RT en <= x < a_E RT en + 904)) ->
  outside ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K max) x.
Proof using AF AFP.
  intros en Σ m crem K max rest x COM Hx.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & _).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & FLO & FSEG & FSHR & FLV & _).
  assert (HLO : a_lo RT en <= a_sp1 RT en) by (clear - LOR; unfold RT_STACK, W7_CALLEE_STACK in *; lia).
  cbn [outside]. split.
  - unfold G_ALLOW_CUST. destruct Hx as [(p & n & Hin & Hp)|[H|[H|H]]].
    + pose proof (af_live_range RT AF Σ m p n ART0 (CLV _ ltac:(apply in_or_app; right; exact Hin))) as (_ & _ & X). clear - X Hp. unfold SEGTOP_A in *. lia.
    + clear - H FSEG. unfold SEGTOP_A in *. lia.
    + clear - H HLO HLOS. lia.
    + pose proof (af_live_range RT AF Σ m (a_E RT en) 904 ART0 (CLL _ INE)) as (_ & _ & X). clear - X H. unfold SEGTOP_A in *. lia.
  - apply outside_intro. intros [u v] Hiv R. cbn [fst snd] in R. apply in_mbio_W in Hiv. destruct Hiv as (e & He & -> & ->).
    assert (HeC : In e (mbio_ent K max ++ rest)) by (apply in_or_app; left; exact He).
    destruct Hx as [(p & n & Hin & Hp)|[H|[H|H]]].
    + destruct (in_split _ _ Hin) as (r1 & r2 & Er).
      destruct (P6 w7_cc_apart en Σ m crem _ (p, n) e (mbio_ent K max ++ r1) r2 COM ltac:(rewrite Er, app_assoc; reflexivity)
                  ltac:(rewrite <- app_assoc; apply in_or_app; left; exact He)) as [Q|Q]; cbn [fst snd] in Q; clear - Q Hp R; lia.
    + destruct e as [q k]. destruct (FLV q k (CLV _ HeC)) as [Q|Q]; cbn [fst snd] in R; clear - Q H R; lia.
    + destruct e as [q k]. pose proof (af_live_range RT AF Σ m q k ART0 (CLV _ HeC)) as (_ & Y & _). cbn [fst snd] in R. clear - Y H R HLO LOW. lia.
    + destruct (P6 w7_cl_apart en Σ m crem _ e (a_E RT en, 904) COM HeC INE) as [Q|Q]; cbn [fst snd] in Q; clear - Q H R; lia.
Qed.

(* [comment removed for export] *)
Lemma w7_out_seg : forall (en : w7a) Σ m crem cur x lo hi, w7_com en Σ m crem cur -> a_SP RT en + -160 <= lo -> hi <= a_SP RT en + -104 ->
  ((exists p n, In (p, n) cur /\ p <= x < p + n) \/ (a_f RT en <= x < a_f RT en + 248) \/ (a_SP RT en + -104 <= x < USTACK_TOP) \/ (a_E RT en <= x < a_E RT en + 904)) ->
  outside [(lo, hi)] x.
Proof using AF AFP.
  intros en Σ m crem cur x lo hi COM HL HI Hx.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & _).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & FLO & FSEG & FSHR & FLV & _).
  assert (HLO : a_lo RT en <= a_SP RT en + -160) by (clear - LOR PD; unfold RT_STACK, W7_CALLEE_STACK, a_sp1 in *; lia).
  cbn. split; [| exact I]. destruct Hx as [(p & n & Hin & Hp)|[H|[H|H]]].
  - pose proof (af_live_range RT AF Σ m p n ART0 (CLV _ Hin)) as (_ & X & _). clear - X Hp LOW HLO HL. lia.
  - clear - H FLO HLO HL. lia.
  - clear - H HI. lia.
  - pose proof (af_live_range RT AF Σ m (a_E RT en) 904 ART0 (CLL _ INE)) as (_ & X & _). clear - X H LOW HLO HL. lia.
Qed.

(* [comment removed for export] *)
Definition w7_fr3 (en : w7a) (m : mem) (j1 j2 j3 j4 j5 j6 : list byte) : Prop :=
  let '(c0, c1, c2, c3, c4, c5, c6) := w7_mframe3 (a_pd RT en) (a_f RT en) j1 j2 j3 j4 j5 j6 in rw_cells asegs m (a_SP RT en + -160) (w7_mf en c0 c1 c2 c3 c4 c5 c6).
(* [comment removed for export] *)
Definition w7_fr2 (en : w7a) (m : mem) (j1 j2 j3 j4 j5 j6 : list byte) : Prop :=
  let '(c1, c2, c3, c4, c5, c6) := w7_mframe2 (a_pd RT en) (a_f RT en) j1 j2 j3 j4 j5 j6 in rw_cells asegs m (a_SP RT en + -160) (w7_mf en (C8 (wz 0)) c1 c2 c3 c4 c5 c6).

Lemma w7_fr3_keep : forall (en : w7a) (m m' : mem) j1 j2 j3 j4 j5 j6 KEEP fr W,
  (a_pd RT en = 0 \/ a_pd RT en = 16) -> a_SP RT en + 16 <= USTACK_TOP -> w7_fr3 en m j1 j2 j3 j4 j5 j6 -> rt_pres_fp KEEP fr (a_sp1 RT en) W m m' ->
  (forall x, a_sp1 RT en <= x < USTACK_TOP -> outside W x) -> w7_fr3 en m' j1 j2 j3 j4 j5 j6.
Proof.
  intros en m m' j1 j2 j3 j4 j5 j6 KEEP fr W PD TOP FR PR HO. unfold w7_fr3, w7_mf, Fz_W7_inv.w7_mf, w7_mframe3, w7_mframe7 in *.
  destruct PD as [E|E]; rewrite E in *; cbn [Z.eqb] in *;
    (eapply stack_keep; [exact FR| exact PR| unfold a_sp1; rewrite E; clear; lia| cbn [cells_size csize Nat.add]; clear - TOP; unfold USTACK_TOP in *; lia|];
     intros x Hx; apply HO; cbn [cells_size csize Nat.add] in Hx; unfold a_sp1; rewrite E; clear - Hx TOP; lia).
Qed.
Lemma w7_fr2_keep : forall (en : w7a) (m m' : mem) j1 j2 j3 j4 j5 j6 KEEP fr W,
  (a_pd RT en = 0 \/ a_pd RT en = 16) -> a_SP RT en + 16 <= USTACK_TOP -> w7_fr2 en m j1 j2 j3 j4 j5 j6 -> rt_pres_fp KEEP fr (a_sp1 RT en) W m m' ->
  (forall x, a_sp1 RT en <= x < USTACK_TOP -> outside W x) -> w7_fr2 en m' j1 j2 j3 j4 j5 j6.
Proof.
  intros en m m' j1 j2 j3 j4 j5 j6 KEEP fr W PD TOP FR PR HO. unfold w7_fr2, w7_mf, Fz_W7_inv.w7_mf, w7_mframe2, w7_mframe7 in *.
  destruct PD as [E|E]; rewrite E in *; cbn [Z.eqb] in *;
    (eapply stack_keep; [exact FR| exact PR| unfold a_sp1; rewrite E; clear; lia| cbn [cells_size csize Nat.add]; clear - TOP; unfold USTACK_TOP in *; lia|];
     intros x Hx; apply HO; cbn [cells_size csize Nat.add] in Hx; unfold a_sp1; rewrite E; clear - Hx TOP; lia).
Qed.
(* [comment removed for export] *)
Lemma w7_fr3_low : forall (en : w7a) (m : mem) j1 j2 j3 j4 j5 j6, (a_pd RT en = 0 \/ a_pd RT en = 16) -> w7_fr3 en m j1 j2 j3 j4 j5 j6 ->
  exists lowc, rw_cells asegs m (a_SP RT en + -160) lowc /\ Z.of_nat (cells_size lowc) = 56 /\ rw_cells asegs m (a_sp1 RT en + 24) [C8 (wz (a_f RT en + 64))].
Proof.
  intros en m j1 j2 j3 j4 j5 j6 PD FR. unfold w7_fr3, w7_mf, Fz_W7_inv.w7_mf, w7_mframe3, w7_mframe7 in FR. unfold a_sp1.
  destruct PD as [E|E]; rewrite E in *; cbn [Z.eqb] in FR.
  - lazymatch type of FR with rw_cells _ _ _ (?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?tl) =>
      destruct (proj1 (rw_cells_app m _ [x0; x1; x2; x3; x4; x5; x6] tl) FR) as [LOW _];
      destruct (proj1 (rw_cells_app m _ [x0; x1; x2] (x3 :: x4 :: x5 :: x6 :: tl)) FR) as [_ SL];
      destruct (proj1 (rw_cells_app m _ [x3] (x4 :: x5 :: x6 :: tl)) SL) as [SL' _] end.
    exists (let '(c0, c1, c2, c3, c4, c5, c6) := w7_mframe3 0 (a_f RT en) j1 j2 j3 j4 j5 j6 in [c0; c1; c2; c3; c4; c5; c6]). cbn [w7_mframe3 Z.eqb].
    split; [exact LOW|]. split; [reflexivity|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SL'.
    replace (a_SP RT en + -160 - 0 + 24) with (a_SP RT en + -160 + 24) by lia. exact SL'.
  - lazymatch type of FR with rw_cells _ _ _ (?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?tl) =>
      destruct (proj1 (rw_cells_app m _ [x0; x1; x2; x3; x4; x5; x6] tl) FR) as [LOW _];
      destruct (proj1 (rw_cells_app m _ [x0] (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: tl)) FR) as [_ SL];
      destruct (proj1 (rw_cells_app m _ [x1] (x2 :: x3 :: x4 :: x5 :: x6 :: tl)) SL) as [SL' _] end.
    exists (let '(c0, c1, c2, c3, c4, c5, c6) := w7_mframe3 16 (a_f RT en) j1 j2 j3 j4 j5 j6 in [c0; c1; c2; c3; c4; c5; c6]). cbn [w7_mframe3 Z.eqb].
    split; [exact LOW|]. split; [reflexivity|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SL'.
    replace (a_SP RT en + -160 - 16 + 24) with (a_SP RT en + -160 + 8) by lia. exact SL'.
Qed.
Lemma w7_fr2_low : forall (en : w7a) (m : mem) j1 j2 j3 j4 j5 j6, (a_pd RT en = 0 \/ a_pd RT en = 16) -> w7_fr2 en m j1 j2 j3 j4 j5 j6 ->
  exists lowc, rw_cells asegs m (a_SP RT en + -160) lowc /\ Z.of_nat (cells_size lowc) = 56 /\ rw_cells asegs m (a_sp1 RT en + 24) [C8 (wz (a_f RT en + 64))].
Proof.
  intros en m j1 j2 j3 j4 j5 j6 PD FR. unfold w7_fr2, w7_mf, Fz_W7_inv.w7_mf, w7_mframe2, w7_mframe7 in FR. unfold a_sp1.
  destruct PD as [E|E]; rewrite E in *; cbn [Z.eqb] in FR.
  - lazymatch type of FR with rw_cells _ _ _ (?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?tl) =>
      destruct (proj1 (rw_cells_app m _ [x0; x1; x2; x3; x4; x5; x6] tl) FR) as [LOW _];
      destruct (proj1 (rw_cells_app m _ [x0; x1; x2] (x3 :: x4 :: x5 :: x6 :: tl)) FR) as [_ SL];
      destruct (proj1 (rw_cells_app m _ [x3] (x4 :: x5 :: x6 :: tl)) SL) as [SL' _] end.
    exists (let '(c1, c2, c3, c4, c5, c6) := w7_mframe2 0 (a_f RT en) j1 j2 j3 j4 j5 j6 in [C8 (wz 0); c1; c2; c3; c4; c5; c6]). cbn [w7_mframe2 Z.eqb].
    split; [exact LOW|]. split; [reflexivity|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SL'.
    replace (a_SP RT en + -160 - 0 + 24) with (a_SP RT en + -160 + 24) by lia. exact SL'.
  - lazymatch type of FR with rw_cells _ _ _ (?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?tl) =>
      destruct (proj1 (rw_cells_app m _ [x0; x1; x2; x3; x4; x5; x6] tl) FR) as [LOW _];
      destruct (proj1 (rw_cells_app m _ [x0] (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: tl)) FR) as [_ SL];
      destruct (proj1 (rw_cells_app m _ [x1] (x2 :: x3 :: x4 :: x5 :: x6 :: tl)) SL) as [SL' _] end.
    exists (let '(c1, c2, c3, c4, c5, c6) := w7_mframe2 16 (a_f RT en) j1 j2 j3 j4 j5 j6 in [C8 (wz 0); c1; c2; c3; c4; c5; c6]). cbn [w7_mframe2 Z.eqb].
    split; [exact LOW|]. split; [reflexivity|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SL'.
    replace (a_SP RT en + -160 - 16 + 24) with (a_SP RT en + -160 + 8) by lia. exact SL'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pw_inv (en : w7a) (Σ : rts RT) (m : mem) (crem : Z) (K : mbk) (BI len max off blen boff top bot : Z) (strs : list (Z * Z))
    (NM nn HD nh DT dlen : Z) (bn bh bd j1 j2 j3 j4 j5 j6 : list byte) : Prop :=
     w7_com en Σ m crem (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)])
  /\ mbio_rep (rt_live RT Σ) m K BI M_MEM len max off
  /\ errst_live (a_E RT en) top bot strs m /\ (length strs <= 2)%nat /\ Forall (fun e => 0 < snd e <= 64) strs
  /\ rw_cells asegs m (a_f RT en + 32) [C8 (wz NM)] /\ rw_cells asegs m (a_f RT en + 64) [C8 (wz HD)] /\ rw_cells asegs m (a_f RT en + 96) [C8 (wz DT)]
  /\ rw_cells asegs m (a_f RT en + 128) [C8 (wz dlen)]
  /\ 1 <= nn <= 255 /\ 1 <= nh < 2 ^ 31 /\ 1 <= dlen < 2 ^ 31
  /\ length bn = Z.to_nat nn /\ rw_cells asegs m NM [CB (Z.to_nat nn) bn] /\ In (Z_to_bv 8 0) bn
  /\ length bh = Z.to_nat nh /\ rw_cells asegs m HD [CB (Z.to_nat nh) bh] /\ nth_error bh (Z.to_nat (nh - 1)) = Some (Z_to_bv 8 0)
  /\ length bd = Z.to_nat dlen /\ rw_cells asegs m DT [CB (Z.to_nat dlen) bd]
  /\ w7_fr3 en m j1 j2 j3 j4 j5 j6
  /\ blen < 2 ^ 26 /\ 0 <= boff <= blen /\ 254 * (dlen + nh + nn) <= 255 * boff + 254 * 512.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pw_ids : forall (en : w7a) Σ m crem K max strs NM nn HD nh DT dlen,
  w7_com en Σ m crem (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) ->
  ~ In DT (mbio_blocks K) /\ ~ In HD (mbio_blocks K) /\ ~ In NM (mbio_blocks K).
Proof.
  intros en Σ m crem K max strs NM nn HD nh DT dlen COM.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & _).
  rewrite map_app, mbio_ent_fst, map_app in ND. pose proof (nd_split _ _ ND) as (_ & _ & DJ). cbn [map fst app] in DJ.
  split; [| split]; intros X; [apply (DJ DT X)| apply (DJ HD X)| apply (DJ NM X)]; apply in_or_app; right; cbn; tauto.
Qed.

(* [comment removed for export] *)
Lemma pw_keep : forall (en : w7a) Σ Σ' (m m' : mem) crem crem' K K' BI len len' max max' off off' blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 KEEP W,
  pw_inv en Σ m crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 ->
  w7_com en Σ' m' crem' (mbio_ent K' max' ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) -> mbio_rep (rt_live RT Σ') m' K' BI M_MEM len' max' off' ->
  rt_pres_fp KEEP (rt_frames RT Σ) (a_sp1 RT en) W m m' ->
  (forall e, In e (strs ++ [(DT, dlen); (HD, nh); (NM, nn)] ++ a_CL RT en) -> In e KEEP) ->
  (forall x, ((exists p n, In (p, n) (strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) /\ p <= x < p + n) \/ (a_f RT en + 24 <= x < a_f RT en + 248) \/ (a_sp1 RT en <= x < USTACK_TOP)
              \/ (a_E RT en <= x < a_E RT en + 904)) -> outside W x) ->
  pw_inv en Σ' m' crem' K' BI len' max' off' blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6.
Proof using AF AFP errst_live_agree errst_fp_where.
  intros en Σ Σ' m m' crem crem' K K' BI len len' max max' off off' blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 KEEP W
         (COM & MB & EL & LS2 & S64 & CN & CH & CD & CL & NN & NH & DL & LBN & NMC & HIN & LBH & HDC & NULH & LBD & DTC & FR & BLT & BOFF & NSZ) COM' MB' PR KIN HO.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & _).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & _).
  assert (HOn : forall p n x, In (p, n) [(DT, dlen); (HD, nh); (NM, nn)] -> p <= x < p + n -> outside W x).
  { intros p n x Hin Hx. apply HO. left. exists p, n. split; [apply in_or_app; right; exact Hin| exact Hx]. }
  assert (KN : forall p n, In (p, n) [(DT, dlen); (HD, nh); (NM, nn)] -> In (p, n) KEEP).
  { intros p n Hin. apply KIN. apply in_or_app; right. apply in_or_app; left. exact Hin. }
  assert (FFK : forall A v, rw_cells asegs m (a_f RT en + A) [C8 v] -> 24 <= A -> A + 8 <= 248 -> rw_cells asegs m' (a_f RT en + A) [C8 v]).
  { intros A v C H1 H2. eapply ff2_keep; [exact C| exact PR| exact INF| clear - H1; lia| cbn [cells_size csize Nat.add]; clear - H2; lia|].
    intros x Hx. apply HO. right; left. cbn [cells_size csize Nat.add] in Hx. clear - Hx H1 H2. lia. }
  split; [exact COM'|]. split; [exact MB'|].
  split. { eapply (elive_keep errst_live errst_fp errst_live_agree errst_fp_where);
             [exact EL| exact PR| apply KIN; apply in_or_app; right; apply in_or_app; right; exact INE| intros e He; apply KIN; apply in_or_app; left; exact He
             | intros x Hx; apply HO; do 3 right; exact Hx|].
           intros e x He Hx. apply HO. left. exists (fst e), (snd e). split; [apply in_or_app; left; destruct e; exact He| exact Hx]. }
  split; [exact LS2|]. split; [exact S64|].
  split; [exact (FFK 32 _ CN ltac:(clear; lia) ltac:(clear; lia))|]. split; [exact (FFK 64 _ CH ltac:(clear; lia) ltac:(clear; lia))|].
  split; [exact (FFK 96 _ CD ltac:(clear; lia) ltac:(clear; lia))|]. split; [exact (FFK 128 _ CL ltac:(clear; lia) ltac:(clear; lia))|].
  split; [exact NN|]. split; [exact NH|]. split; [exact DL|]. split; [exact LBN|].
  split. { eapply w7_cells_keep; [exact NMC| exact PR| apply (KN NM nn); cbn; tauto| clear; lia| cbn [cells_size csize Nat.add]; clear - NN; lia|].
           intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (HOn NM nn); [cbn; tauto| clear - Hx NN; lia]. }
  split; [exact HIN|]. split; [exact LBH|].
  split. { eapply w7_cells_keep; [exact HDC| exact PR| apply (KN HD nh); cbn; tauto| clear; lia| cbn [cells_size csize Nat.add]; clear - NH; lia|].
           intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (HOn HD nh); [cbn; tauto| clear - Hx NH; lia]. }
  split; [exact NULH|]. split; [exact LBD|].
  split. { eapply w7_cells_keep; [exact DTC| exact PR| apply (KN DT dlen); cbn; tauto| clear; lia| cbn [cells_size csize Nat.add]; clear - DL; lia|].
           intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply (HOn DT dlen); [cbn; tauto| clear - Hx DL; lia]. }
  split; [exact (w7_fr3_keep en m m' j1 j2 j3 j4 j5 j6 _ _ _ PD TOP FR PR ltac:(intros x Hx; apply HO; do 2 right; left; exact Hx))|].
  split; [exact BLT|]. split; [exact BOFF| exact NSZ].
Qed.

(* [comment removed for export] *)
Lemma w7_mbio_bnd : forall live (m : mem) K BI meth len max off, mbio_rep live m K BI meth len max off -> 0 <= off <= len /\ len <= max < 2 ^ 31 - 1.
Proof.
  intros live m K BI meth len max off (BM & fl & rrw & numw & padw & nr & nw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (rmx & _ & _ & _ & _ & _ & _ & _ & X1 & X2 & X3 & _)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PW4_stmt : Prop :=
  forall (en : w7a) Σ m crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  pw_inv en Σ m crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 ->
  len - off <= blen - boff + nn + nh -> W7P_WCOST + 2 <= crem -> 2 <= a_len RT en ->
  w7_at en Σ (MS (w7_regs (wz SITE_w7_write3) (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (a_f RT en + 96)) t3 t4 t5 t6 (a_d RT en) BI (a_f RT en) (a_pd RT en))
              F (wz SITE_w7_write3) fc None m (seg_rom asegs)).

Theorem PW4_proof : PW4_stmt.
Proof.
  intros en Σ m crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 PW LENB CRM LEN2.
  unfold w7_at, cps. intros T c HA Hk.
  pose proof PW as (COM & MB & EL & LS2 & S64 & CN & CH & CD & CL & NN & NH & DL & LBN & NMC & HIN & LBH & HDC & NULH & LBD & DTC & FR & BLT & BOFF & NSZ).
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & FLO & FSEG & FSHR & FLV & SH1 & SH2 & SH8).
  assert (HLO : a_lo RT en <= a_SP RT en - 176) by (clear - LOR PD; unfold RT_STACK, W7_CALLEE_STACK, a_sp1 in *; lia).
  assert (SPH : a_SP RT en <= 2 ^ 47) by (clear - TOP; unfold USTACK_TOP in *; lia).
  destruct (pw_ids en Σ m crem K max strs NM nn HD nh DT dlen COM) as (NKD & NKH & NKN).
  pose proof (w7_mbio_bnd _ _ _ _ _ _ _ _ MB) as [OFFB LENM].
  assert (IND : In (DT, dlen) (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  (* [comment removed for export] *)
  pose proof (w7_p4_walk (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) DT dlen
                F0 FLO HLO HLOS SPH ltac:(clear - DL; lia) CD CL MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & -> & Hc1'). clear Hc1 HA.
  (* [comment removed for export] *)
  assert (GRN : gr_n (len - off + dlen) <= 2 ^ 27) by (apply (w7p_grn blen boff (dlen + nh + nn)); [exact BLT| exact BOFF| exact NSZ| clear - OFFB DL; lia| clear - LENB NN NH; lia]).
  pose proof (w7p_cost (len - off) dlen max GRN) as PCB.
  pose proof (rw_cells_bytes_at _ _ _ _ DTC) as DTB. cbn [cells_bytes cbytes] in DTB. rewrite app_nil_r in DTB.
  assert (SB : src_blk (rt_live RT Σ) DT dlen (mbio_blocks K)).
  { right. exists DT, dlen. split; [exact (CLV _ IND)|]. split; [clear; lia|]. split; [clear; lia| exact NKD]. }
  eapply (PC w7c_write C_BW T en Σ m crem (strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) K BI len max off DT dlen bd SITE_w7_write4 F fc t0 t1 t2 a3 a4 a5 a6 a7
            _ _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 c1 COM MB GRN ltac:(clear - DL; lia) DTB ltac:(rewrite LBD; reflexivity) SB ltac:(clear - PCB CRM; unfold W7P_WCOST in *; lia)
            ltac:(rewrite length_app; cbn [length]; clear - LS2; lia)
            ltac:(unfold W7_SITES_OWN; cbn [map]; do 9 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 9 right; left; reflexivity)
            ltac:(unfold SITE_w7_write4; clear; lia) eq_refl Hc1').
  clear Hc1'. intros Σ1 m1 F1 fc1 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c2 pd' max' COM1 FRS1 PR1 KP1 MB1 HMAX HFIT Hc2. cbv beta delta [Fz_W7_calls.w7_cs] in Hc2.
  assert (PW1 : pw_inv en Σ1 m1 (crem - puts_cost (len - off) dlen max) (mbk_data K pd') BI (len - off + dlen) max' 0 blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6).
  { eapply (pw_keep en Σ Σ1 m m1); [exact PW| exact COM1| exact MB1| exact PR1| | intros x Hx; exact (w7_out_bioW en Σ m crem K max _ x COM Hx)].
    intros e He. apply (fun H => proj1 (KP1 e H)). rewrite <- app_assoc. apply in_app_iff in He. apply in_or_app. destruct He as [He|He]; [left; exact He| right].
    apply in_app_iff in He. apply in_or_app. destruct He as [He|He]; [left; exact He| right; apply in_or_app; left; exact He]. }
  pose proof PW1 as (_ & _ & EL1 & _ & _ & CN1 & CH1 & CD1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR1 & _).
  destruct (w7_fr3_low en m1 j1 j2 j3 j4 j5 j6 PD FR1) as (lowc & LOW1 & LSZ & H241).
  exact (F7P en Σ1 m1 (crem - puts_cost (len - off) dlen max) (mbk_data K pd') BI (len - off + dlen) max' 0 strs top bot [(DT, dlen); (HD, nh); (NM, nn)] NM HD DT lowc F1 fc1
           (wz SITE_w7_write4) y0 y1 y2 (wz dlen) b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 COM1 MB1 EL1 LS2 S64
           (or_intror (ex_intro _ nn (ex_intro _ nh (ex_intro _ dlen (conj eq_refl (conj (proj1 NN) (conj (proj1 NH) (proj1 DL))))))))
           CN1 CH1 CD1 LOW1 LSZ H241 ltac:(clear - PCB CRM; unfold W7P_WCOST in *; lia) LEN2 T c2 Hc2 Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PW3_stmt : Prop :=
  forall (en : w7a) Σ m crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word),
  pw_inv en Σ m crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 ->
  len - off <= blen - boff + nn -> 2 * W7P_WCOST + 2 <= crem -> 2 <= a_len RT en ->
  w7_at en Σ (MS (w7_regs (wz SITE_w7_write2) (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 (a_d RT en) BI (a_f RT en) (a_pd RT en))
              F (wz SITE_w7_write2) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Lemma pw_keep0 : forall (en : w7a) Σ (m m' : mem) crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6,
  pw_inv en Σ m crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 ->
  w7_com en Σ m' crem (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [] m m' ->
  pw_inv en Σ m' crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6.
Proof using AF AFP errst_live_agree errst_fp_where.
  intros en Σ m m' crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 PW COM' PR.
  pose proof PW as (COM & MB & _). destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  eapply (pw_keep en Σ Σ m m'); [exact PW| exact COM'| | exact PR| | intros x _; exact I].
  - eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR| intros e He; split; apply CLV; apply in_or_app; left; exact He| intros e x _ _; exact I].
  - intros e He. apply in_app_iff in He. destruct He as [He|He]; [apply CLV; apply in_or_app; right; apply in_or_app; left; exact He|].
    apply in_app_iff in He. destruct He as [He|He]; [apply CLV; apply in_or_app; right; apply in_or_app; right; exact He| exact (CLL _ He)].
Qed.

Theorem PW3_proof : PW4_stmt -> PW3_stmt.
Proof.
  intros PW4P en Σ m crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 F fc t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 PW LENB CRM LEN2.
  unfold w7_at, cps. intros T c HA Hk.
  pose proof PW as (COM & MB & EL & LS2 & S64 & CN & CH & CD & CL & NN & NH & DL & LBN & NMC & HIN & LBH & HDC & NULH & LBD & DTC & FR & BLT & BOFF & NSZ).
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & FLO & FSEG & FSHR & FLV & SH1 & SH2 & SH8).
  assert (HLO : a_lo RT en <= a_SP RT en - 176) by (clear - LOR PD; unfold RT_STACK, W7_CALLEE_STACK, a_sp1 in *; lia).
  assert (SPH : a_SP RT en <= 2 ^ 47) by (clear - TOP; unfold USTACK_TOP in *; lia).
  destruct (pw_ids en Σ m crem K max strs NM nn HD nh DT dlen COM) as (NKD & NKH & NKN).
  pose proof (w7_mbio_bnd _ _ _ _ _ _ _ _ MB) as [OFFB LENM].
  assert (INH : In (HD, nh) (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)])) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  pose proof (P7 w7_cur_facts en Σ m crem _ (HD, nh) COM INH ltac:(clear - NH; cbn; lia)) as (_ & HD0 & HDLO & _ & _ & _ & HD47). cbn [fst snd] in HD0, HDLO, HD47.
  (* [comment removed for export] *)
  pose proof (w7_p2_walk (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 (a_ra RT en) (a_s0 RT en) (a_s1 RT en) (a_s2 RT en) (a_s3 RT en)
                (a_s4 RT en) (a_s5 RT en) (a_s6 RT en) (a_s7 RT en) (a_s8 RT en) (a_s9 RT en) (a_s10 RT en) (a_s11 RT en) F fc m (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) HD
                j1 j2 j3 j4 j5 j6 PD F0 ltac:(clear - FSEG; unfold SEGTOP_A in *; lia) FLO HLO HLOS SPH FR CH MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & -> & Hc1'). clear Hc1 HA.
  (* [comment removed for export] *)
  destruct (first_nul_split (Z_to_bv 8 0) bh (nth_error_In _ _ NULH)) as (str & bh2 & Ebh & NSTR).
  assert (LSTR : Z.of_nat (length str) + 1 + Z.of_nat (length bh2) = nh) by (rewrite Ebh, length_app in LBH; cbn [length] in LBH; clear - LBH NH; lia).
  destruct (af_live_slack RT AF Σ m HD nh ART0 (CLV _ INH)) as (slack & SLB & SLM & SLT).
  assert (HDB : bytes_at asegs m HD (str ++ Z_to_bv 8 0 :: bh2 ++ slack)).
  { pose proof (rw_cells_bytes_at _ _ _ _ HDC) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r, Ebh in B.
    rewrite app_comm_cons, app_assoc. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B|]. rewrite <- Ebh, LBH, Z2Nat.id by (clear - NH; lia). exact SLB. }
  assert (SLK : (- (HD + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length (bh2 ++ slack))) by (rewrite length_app, Nat2Z.inj_add; clear - LSTR SLM NH; Z.div_mod_to_equations; lia).
  assert (LO1 : HD + Z.of_nat (length str) + 1 + Z.of_nat (length (bh2 ++ slack)) <= a_lo RT en) by (rewrite length_app, Nat2Z.inj_add; clear - LSTR SLT LOW; lia).
  pose proof (P7 w7_chk_cur en Σ m crem _ HD nh HD (Z.of_nat (length str) + 1) COM INH ltac:(clear - NH; lia) ltac:(clear; lia) ltac:(clear - LSTR; lia) ltac:(clear; lia)) as CK.
  eapply (PC w7c_slen SLC T en Σ m crem _ HD str (bh2 ++ slack) SITE_w7_slen2 F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 c1 COM HDB NSTR
            ltac:(clear - LSTR NH; lia) SLK ltac:(clear - HD0 HD47 NH; lia) LO1 CK ltac:(unfold SITE_w7_slen2; clear; lia) eq_refl Hc1').
  clear Hc1'. intros m1 F1 fc1 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c2 COM1 PR1 MI1 Hc2. cbv beta delta [Fz_W7_calls.w7_cs] in Hc2.
  pose proof (pw_keep0 en Σ m m1 crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 PW COM1 PR1) as PW1.
  assert (HDB1 : bytes_at asegs m1 HD str).
  { pose proof PW1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDC1 & _).
    pose proof (rw_cells_bytes_at _ _ _ _ HDC1) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r, Ebh in B. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)). }
  pose proof PW1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR1 & _).
  clear COM MI FR CH HDC HDB SLB CK PW. set (n2 := Z.of_nat (length str)) in *.
  assert (N2 : 0 <= n2 <= nh - 1) by (subst n2; clear - LSTR; lia).
  (* [comment removed for export] *)
  pose proof (w7_p3_walk (a_sp RT en) (a_gp RT en) (wz TP_A) y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 (a_ra RT en) (a_s0 RT en) (a_s1 RT en) (a_s2 RT en) (a_s3 RT en)
                (a_s4 RT en) (a_s5 RT en) (a_s6 RT en) (a_s7 RT en) (a_s8 RT en) (a_s9 RT en) (a_s10 RT en) (a_s11 RT en) F1 fc1 m1 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) HD n2
                j1 j2 j3 j4 j5 j6 PD F0 FLO HLO HLOS SPH ltac:(clear - N2 NH; lia) FR1 MI1) as W.
  cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3 Hc2.
  pose proof PW1 as (COM1' & MB1 & _).
  destruct (Z.eq_dec n2 0) as [N0|N1].
  - (* [comment removed for export] *)
    rewrite N0 in Hc3'.
    eapply (PC w7c_write0 C_B0 T en Σ m1 crem _ 0 SITE_w7_write3 F1 fc1 y0 y1 y2 (wz BI) (wz HD) d3 d4 d5 d6 d7 _ _ _ _ _ _ _ _ _ _ _ y3 y4 y5 y6 c3 COM1' ltac:(clear; lia)
              ltac:(unfold W7_SITES_OWN; cbn [map]; do 8 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 8 right; left; reflexivity)
              ltac:(unfold SITE_w7_write3; clear; lia) eq_refl Hc3').
    clear Hc3'. intros m2 F2 fc2 z0 z1 z2 b1 b2 b3 b4 b5 b6 b7 z3 z4 z5 z6 c4 COM2 PR2 Hc4. cbv beta delta [Fz_W7_calls.w7_cs] in Hc4.
    pose proof (pw_keep0 en Σ m1 m2 crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 PW1 COM2 PR2) as PW2.
    exact (PW4P en Σ m2 crem K BI len max off blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 F2 fc2 z0 z1 z2 (wz 0) b1 b2 b3 b4 b5 b6 b7 z3 z4 z5 z6
             PW2 ltac:(clear - LENB NH; lia) ltac:(clear - CRM; unfold W7P_WCOST in *; lia) LEN2 T c4 Hc4 Hk).
  - (* [comment removed for export] *)
    assert (GRN : gr_n (len - off + n2) <= 2 ^ 27) by (apply (w7p_grn blen boff (dlen + nh + nn)); [exact BLT| exact BOFF| exact NSZ| clear - OFFB N2; lia| clear - LENB N2 DL; lia]).
    pose proof (w7p_cost (len - off) n2 max GRN) as PCB.
    assert (SB : src_blk (rt_live RT Σ) HD n2 (mbio_blocks K)).
    { right. exists HD, nh. split; [exact (CLV _ INH)|]. split; [clear; lia|]. split; [clear - N2; lia| exact NKH]. }
    eapply (PC w7c_write C_BW T en Σ m1 crem (strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) K BI len max off HD n2 str SITE_w7_write3 F1 fc1 y0 y1 y2 d3 d4 d5 d6 d7
              _ _ _ _ _ _ _ _ _ _ _ y3 y4 y5 y6 c3 COM1' MB1 GRN ltac:(clear - N1 N2 NH; lia) HDB1 ltac:(subst n2; rewrite Nat2Z.id; reflexivity) SB
              ltac:(clear - PCB CRM; unfold W7P_WCOST in *; lia) ltac:(rewrite length_app; cbn [length]; clear - LS2; lia)
              ltac:(unfold W7_SITES_OWN; cbn [map]; do 8 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 8 right; left; reflexivity)
              ltac:(unfold SITE_w7_write3; clear; lia) eq_refl Hc3').
    clear Hc3'. intros Σ2 m2 F2 fc2 z0 z1 z2 b1 b2 b3 b4 b5 b6 b7 z3 z4 z5 z6 c4 pd' max' COM2 FRS2 PR2 KP2 MB2 HMAX HFIT Hc4. cbv beta delta [Fz_W7_calls.w7_cs] in Hc4.
    assert (PW2 : pw_inv en Σ2 m2 (crem - puts_cost (len - off) n2 max) (mbk_data K pd') BI (len - off + n2) max' 0 blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6).
    { eapply (pw_keep en Σ Σ2 m1 m2); [exact PW1| exact COM2| exact MB2| exact PR2| | intros x Hx; exact (w7_out_bioW en Σ m1 crem K max _ x COM1' Hx)].
      intros e He. apply (fun H => proj1 (KP2 e H)). rewrite <- app_assoc. apply in_app_iff in He. apply in_or_app. destruct He as [He|He]; [left; exact He| right].
      apply in_app_iff in He. apply in_or_app. destruct He as [He|He]; [left; exact He| right; apply in_or_app; left; exact He]. }
    exact (PW4P en Σ2 m2 (crem - puts_cost (len - off) n2 max) (mbk_data K pd') BI (len - off + n2) max' 0 blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6
             F2 fc2 z0 z1 z2 (wz n2) b1 b2 b3 b4 b5 b6 b7 z3 z4 z5 z6 PW2 ltac:(clear - LENB N2; lia) ltac:(clear - CRM PCB; unfold W7P_WCOST in *; lia) LEN2 T c4 Hc4 Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P7_stmt : Prop :=
  forall (en : w7a) Σ m crem K BI blen bmax boff strs top bot news ret (j1 j2 j3 j4 j5 j6 : list byte) (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  w7_com en Σ m crem (mbio_ent K bmax ++ strs ++ news) -> 0 <= boff <= blen -> blen < 2 ^ 26 -> mbio_rep (rt_live RT Σ) m K BI M_MEM blen bmax boff ->
  errst_live (a_E RT en) top bot strs m -> (length strs <= 2)%nat -> Forall (fun e => 0 < snd e <= 64) strs ->
  pem_out ret m (a_f RT en + 32) (a_f RT en + 64) (a_f RT en + 96) (a_f RT en + 128) news -> 254 * news_sz news <= 255 * boff + 254 * 512 ->
  w7_fr2 en m j1 j2 j3 j4 j5 j6 -> W7P_CREDIT <= crem -> 2 <= a_len RT en ->
  w7_at en Σ (MS (w7_regs (wz SITE_w7_pem) (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 (wz ret) a1 a2 a3 a4 a5 a6 a7 (wz (a_f RT en + 96)) t3 t4 t5 t6 (a_d RT en) BI (a_f RT en) (a_pd RT en))
              F (wz SITE_w7_pem) fc None m (seg_rom asegs)).

Theorem P7_proof : PW3_stmt -> P7_stmt.
Proof.
  intros PW3P en Σ m crem K BI blen bmax boff strs top bot news ret j1 j2 j3 j4 j5 j6 F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 COM BOFF BLT MB EL LS2 S64 POUT NSZ FR CRM LEN2.
  unfold w7_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & FLO & FSEG & FSHR & FLV & SH1 & SH2 & SH8).
  assert (HLO : a_lo RT en <= a_SP RT en - 176) by (clear - LOR PD; unfold RT_STACK, W7_CALLEE_STACK, a_sp1 in *; lia).
  assert (SPH : a_SP RT en <= 2 ^ 47) by (clear - TOP; unfold USTACK_TOP in *; lia).
  unfold W7P_CREDIT in CRM. pose proof (w7_mbio_bnd _ _ _ _ _ _ _ _ MB) as [OFFB LENM].
  destruct POUT as [(-> & -> & CN & CH & CD & (lw & CL))|(-> & NM & HD & DT & nn & nh & dlen & bn & bh & bd & -> & NN & NH & DL & CN & CH & CD & CL & LBN & NMC & HIN & LBH & HDC & NULH & LBD & DTC)].
  - (* [comment removed for export] *)
    pose proof (w7_p0f_walk (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m (a_d RT en) BI (a_f RT en) (a_pd RT en) 0
                  ltac:(clear; lia) ltac:(clear; lia) MI) as W.
    cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & -> & Hc1'). clear Hc1 HA.
    destruct (w7_fr2_low en m j1 j2 j3 j4 j5 j6 PD FR) as (lowc & LOWC & LSZ & H24).
    exact (F7P en Σ m crem K BI blen bmax boff strs top bot [] 0 0 0 lowc F fc (wz SITE_w7_pem) t0 t1 t2 (wz 0) (wz 1) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 COM MB EL LS2 S64
             (or_introl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))) CN CH CD LOWC LSZ H24 ltac:(clear - CRM; unfold W7P_WCOST in *; lia) LEN2 T c1 Hc1' Hk).
  - (* [comment removed for export] *)
    cbn [news_sz fold_right snd] in NSZ.
    set (cur := mbio_ent K bmax ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) in *.
    assert (INN : In (NM, nn) cur) by (subst cur; apply in_or_app; right; apply in_or_app; right; do 2 right; left; reflexivity).
    assert (INH : In (HD, nh) cur) by (subst cur; apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
    assert (IND : In (DT, dlen) cur) by (subst cur; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    destruct (pw_ids en Σ m crem K bmax strs NM nn HD nh DT dlen COM) as (NKD & NKH & NKN).
    (* [comment removed for export] *)
    pose proof (w7_p0_walk (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (a_ra RT en) (a_s0 RT en) (a_s1 RT en) (a_s2 RT en) (a_s3 RT en)
                  (a_s4 RT en) (a_s5 RT en) (a_s6 RT en) (a_s7 RT en) (a_s8 RT en) (a_s9 RT en) (a_s10 RT en) (a_s11 RT en) F fc m (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) NM
                  j1 j2 j3 j4 j5 j6 PD F0 ltac:(clear - FSEG; unfold SEGTOP_A in *; lia) FLO HLO HLOS SPH FR GAP CN MI) as W.
    cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & X) & Hc1'). clear Hc1 HA.
    assert (X' : ms1 = MS (w7_regs (wz SITE_w7_slen1) (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 (wz NM) (wz 1) a2 a3 a4 a5 a6 a7 (wz NM) t3 t4 t5 t6 (a_d RT en) BI (a_f RT en) (a_pd RT en))
                          F (wz e_strlen) fc None m1 (seg_rom asegs)
              /\ munch [(bv_unsigned (a_sp RT en) - 160, bv_unsigned (a_sp RT en) - 136)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
              /\ w7_fr3 en m1 j1 j2 j3 j4 j5 j6 /\ stk asegs m1 (bv_unsigned (a_sp RT en) + -160 - a_pd RT en) (bv_unsigned (a_sp RT en) + -160)).
    { unfold w7_fr3, w7_mf, Fz_W7_inv.w7_mf. destruct PD as [E|E]; rewrite E in X |- *; cbn [w7_mframe3 Z.eqb] in X |- *; exact X. }
    clear X. destruct X' as (-> & MU & WM & MI1 & FR1 & GAP1).
    (* [comment removed for export] *)
    assert (ST1 : stk asegs m1 (a_lo RT en) (a_sp1 RT en)).
    { eapply stk_munch; [exact ST| exact MU| exact WM|]. intros x Hx. cbn. split; [| exact I]. unfold a_sp1, a_SP in Hx. clear - Hx PD. lia. }
    assert (COM1 : w7_com en Σ m1 crem cur).
    { eapply (PC w7_seg en Σ m m1 crem cur _ COM MU WM MI1 ST1). constructor; [| constructor]. right; left. cbn [fst snd]. unfold a_SP. clear. lia. }
    assert (PR1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (a_sp1 RT en) [(bv_unsigned (a_sp RT en) - 160, bv_unsigned (a_sp RT en) - 136)] m m1) by (intros a _ Ho; exact (MU a Ho)).
    assert (HO1 : forall x, ((exists p n, In (p, n) cur /\ p <= x < p + n) \/ (a_f RT en <= x < a_f RT en + 248) \/ (a_SP RT en + -104 <= x < USTACK_TOP) \/ (a_E RT en <= x < a_E RT en + 904)) ->
                    outside [(bv_unsigned (a_sp RT en) - 160, bv_unsigned (a_sp RT en) - 136)] x).
    { intros x Hx. exact (w7_out_seg en Σ m crem cur x (bv_unsigned (a_sp RT en) - 160) (bv_unsigned (a_sp RT en) - 136) COM ltac:(unfold a_SP; clear; lia) ltac:(unfold a_SP; clear; lia) Hx). }
    assert (FFK : forall A v, rw_cells asegs m (a_f RT en + A) [C8 v] -> 24 <= A -> A + 8 <= 248 -> rw_cells asegs m1 (a_f RT en + A) [C8 v]).
    { intros A v C H1 H2. eapply ff2_keep; [exact C| exact PR1| exact INF| clear - H1; lia| cbn [cells_size csize Nat.add]; clear - H2; lia|].
      intros x Hx. apply HO1. right; left. cbn [cells_size csize Nat.add] in Hx. clear - Hx H1 H2. lia. }
    assert (BLK : forall p n k cs, In (p, n) cur -> rw_cells asegs m p cs -> Z.of_nat (cells_size cs) = k -> 0 < k <= n -> rw_cells asegs m1 p cs).
    { intros p n k cs Hin C SZ Hk0. eapply w7_cells_keep; [exact C| exact PR1| exact (CLV _ Hin)| clear; lia| rewrite SZ; clear - Hk0; lia|].
      intros x Hx. apply HO1. left. exists p, n. split; [exact Hin| rewrite SZ in Hx; clear - Hx Hk0; lia]. }
    assert (PW1 : pw_inv en Σ m1 crem K BI blen bmax boff blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6).
    { split; [exact COM1|].
      split. { eapply (mbio_rep_keep (rt_live RT Σ)); [exact MB| exact PR1| intros e He; split; apply CLV; subst cur; apply in_or_app; left; exact He|].
               intros e x He Hx. apply HO1. left. exists (fst e), (snd e). split; [subst cur; apply in_or_app; left; destruct e; exact He| exact Hx]. }
      split. { eapply (elive_keep errst_live errst_fp errst_live_agree errst_fp_where); [exact EL| exact PR1| exact (CLL _ INE)| intros e He; apply CLV; subst cur; apply in_or_app; right; apply in_or_app; left; exact He
                 | intros x Hx; apply HO1; do 3 right; exact Hx|].
               intros e x He Hx. apply HO1. left. exists (fst e), (snd e). split; [subst cur; apply in_or_app; right; apply in_or_app; left; destruct e; exact He| exact Hx]. }
      split; [exact LS2|]. split; [exact S64|].
      split; [exact (FFK 32 _ CN ltac:(clear; lia) ltac:(clear; lia))|]. split; [exact (FFK 64 _ CH ltac:(clear; lia) ltac:(clear; lia))|].
      split; [exact (FFK 96 _ CD ltac:(clear; lia) ltac:(clear; lia))|]. split; [exact (FFK 128 _ CL ltac:(clear; lia) ltac:(clear; lia))|].
      split; [exact NN|]. split; [exact NH|]. split; [exact DL|]. split; [exact LBN|].
      split; [exact (BLK NM nn nn _ INN NMC ltac:(cbn [cells_size csize Nat.add]; clear - NN; lia) ltac:(clear - NN; lia))|]. split; [exact HIN|]. split; [exact LBH|].
      split; [exact (BLK HD nh nh _ INH HDC ltac:(cbn [cells_size csize Nat.add]; clear - NH; lia) ltac:(clear - NH; lia))|]. split; [exact NULH|]. split; [exact LBD|].
      split; [exact (BLK DT dlen dlen _ IND DTC ltac:(cbn [cells_size csize Nat.add]; clear - DL; lia) ltac:(clear - DL; lia))|].
      split; [exact FR1|]. split; [exact BLT|]. split; [exact BOFF| clear - NSZ; lia]. }
    pose proof PW1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NMC1 & _).
    clear MU WM FR GAP CN CH CD CL NMC HDC DTC MB EL FFK BLK HO1 PR1 ST1 COM MI.
    pose proof COM1 as (ART1 & _).
    pose proof (P7 w7_cur_facts en Σ m1 crem _ (NM, nn) COM1 INN ltac:(clear - NN; cbn; lia)) as (_ & NM0 & NMLO & _ & _ & _ & NM47). cbn [fst snd] in NM0, NMLO, NM47.
    (* [comment removed for export] *)
    destruct (first_nul_split (Z_to_bv 8 0) bn HIN) as (str & bn2 & Ebn & NSTR).
    assert (LSTR : Z.of_nat (length str) + 1 + Z.of_nat (length bn2) = nn) by (rewrite Ebn, length_app in LBN; cbn [length] in LBN; clear - LBN NN; lia).
    destruct (af_live_slack RT AF Σ m1 NM nn ART1 (CLV _ INN)) as (slack & SLB & SLM & SLT).
    assert (NMB : bytes_at asegs m1 NM (str ++ Z_to_bv 8 0 :: bn2 ++ slack)).
    { pose proof (rw_cells_bytes_at _ _ _ _ NMC1) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r, Ebn in B.
      rewrite app_comm_cons, app_assoc. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B|]. rewrite <- Ebn, LBN, Z2Nat.id by (clear - NN; lia). exact SLB. }
    assert (SLK : (- (NM + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length (bn2 ++ slack))) by (rewrite length_app, Nat2Z.inj_add; clear - LSTR SLM NN; Z.div_mod_to_equations; lia).
    assert (LO1 : NM + Z.of_nat (length str) + 1 + Z.of_nat (length (bn2 ++ slack)) <= a_lo RT en) by (rewrite length_app, Nat2Z.inj_add; clear - LSTR SLT LOW; lia).
    pose proof (P7 w7_chk_cur en Σ m1 crem _ NM nn NM (Z.of_nat (length str) + 1) COM1 INN ltac:(clear - NN; lia) ltac:(clear; lia) ltac:(clear - LSTR; lia) ltac:(clear; lia)) as CK.
    eapply (PC w7c_slen SLC T en Σ m1 crem _ NM str (bn2 ++ slack) SITE_w7_slen1 F fc t0 t1 t2 (wz 1) a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 c1 COM1 NMB NSTR
              ltac:(clear - LSTR NN; lia) SLK ltac:(clear - NM0 NM47 NN; lia) LO1 CK ltac:(unfold SITE_w7_slen1; clear; lia) eq_refl Hc1').
    clear Hc1'. intros m2 F2 fc2 y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 c2 COM2 PR2 MI2 Hc2. cbv beta delta [Fz_W7_calls.w7_cs] in Hc2.
    pose proof (pw_keep0 en Σ m1 m2 crem K BI blen bmax boff blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 PW1 COM2 PR2) as PW2.
    assert (NMB2 : bytes_at asegs m2 NM str).
    { pose proof PW2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NMC2 & _).
      pose proof (rw_cells_bytes_at _ _ _ _ NMC2) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r, Ebn in B. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)). }
    clear COM1 MI1 NMC1 NMB SLB CK PW1. set (n1 := Z.of_nat (length str)) in *.
    assert (N1R : 0 <= n1 <= nn - 1) by (subst n1; clear - LSTR; lia).
    (* [comment removed for export] *)
    pose proof (w7_p1_walk (a_sp RT en) (a_gp RT en) (wz TP_A) y0 y1 y2 d1 d2 d3 d4 d5 d6 d7 y3 y4 y5 y6 F2 fc2 m2 (a_d RT en) BI (a_f RT en) (a_pd RT en) NM n1
                  ltac:(clear - N1R NN; lia) MI2) as W.
    cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3 Hc2.
    pose proof PW2 as (COM2' & MB2 & _).
    destruct (Z.eq_dec n1 0) as [N0|N1].
    + (* [comment removed for export] *)
      rewrite N0 in Hc3'.
      eapply (PC w7c_write0 C_B0 T en Σ m2 crem _ 0 SITE_w7_write2 F2 fc2 y0 y1 y2 (wz BI) (wz NM) d3 d4 d5 d6 d7 _ _ _ _ _ _ _ _ _ _ _ y3 y4 y5 y6 c3 COM2' ltac:(clear; lia)
                ltac:(unfold W7_SITES_OWN; cbn [map]; do 6 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 6 right; left; reflexivity)
                ltac:(unfold SITE_w7_write2; clear; lia) eq_refl Hc3').
      clear Hc3'. intros m3 F3 fc3 z0 z1 z2 b1 b2 b3 b4 b5 b6 b7 z3 z4 z5 z6 c4 COM3 PR3 Hc4. cbv beta delta [Fz_W7_calls.w7_cs] in Hc4.
      pose proof (pw_keep0 en Σ m2 m3 crem K BI blen bmax boff blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 PW2 COM3 PR3) as PW3.
      exact (PW3P en Σ m3 crem K BI blen bmax boff blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6 F3 fc3 z0 z1 z2 (wz 0) b1 b2 b3 b4 b5 b6 b7 (wz NM) z3 z4 z5 z6
               PW3 ltac:(clear - NN; lia) ltac:(clear - CRM; unfold W7P_WCOST in *; lia) LEN2 T c4 Hc4 Hk).
    + (* [comment removed for export] *)
      assert (GRN : gr_n (blen - boff + n1) <= 2 ^ 27) by (apply (w7p_grn blen boff (dlen + nh + nn)); [exact BLT| exact BOFF| clear - NSZ; lia| clear - BOFF N1R; lia| clear - N1R DL NH; lia]).
      pose proof (w7p_cost (blen - boff) n1 bmax GRN) as PCB.
      assert (SB : src_blk (rt_live RT Σ) NM n1 (mbio_blocks K)).
      { right. exists NM, nn. split; [exact (CLV _ INN)|]. split; [clear; lia|]. split; [clear - N1R; lia| exact NKN]. }
      eapply (PC w7c_write C_BW T en Σ m2 crem (strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) K BI blen bmax boff NM n1 str SITE_w7_write2 F2 fc2 y0 y1 y2 d3 d4 d5 d6 d7
                _ _ _ _ _ _ _ _ _ _ _ y3 y4 y5 y6 c3 COM2' MB2 GRN ltac:(clear - N1 N1R NN; lia) NMB2 ltac:(subst n1; rewrite Nat2Z.id; reflexivity) SB
                ltac:(clear - PCB CRM; unfold W7P_WCOST in *; lia) ltac:(rewrite length_app; cbn [length]; clear - LS2; lia)
                ltac:(unfold W7_SITES_OWN; cbn [map]; do 6 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 6 right; left; reflexivity)
                ltac:(unfold SITE_w7_write2; clear; lia) eq_refl Hc3').
      clear Hc3'. intros Σ3 m3 F3 fc3 z0 z1 z2 b1 b2 b3 b4 b5 b6 b7 z3 z4 z5 z6 c4 pd' max' COM3 FRS3 PR3 KP3 MB3 HMAX HFIT Hc4. cbv beta delta [Fz_W7_calls.w7_cs] in Hc4.
      assert (PW3 : pw_inv en Σ3 m3 (crem - puts_cost (blen - boff) n1 bmax) (mbk_data K pd') BI (blen - boff + n1) max' 0 blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6).
      { eapply (pw_keep en Σ Σ3 m2 m3); [exact PW2| exact COM3| exact MB3| exact PR3| | intros x Hx; exact (w7_out_bioW en Σ m2 crem K bmax _ x COM2' Hx)].
        intros e He. apply (fun H => proj1 (KP3 e H)). rewrite <- app_assoc. apply in_app_iff in He. apply in_or_app. destruct He as [He|He]; [left; exact He| right].
        apply in_app_iff in He. apply in_or_app. destruct He as [He|He]; [left; exact He| right; apply in_or_app; left; exact He]. }
      exact (PW3P en Σ3 m3 (crem - puts_cost (blen - boff) n1 bmax) (mbk_data K pd') BI (blen - boff + n1) max' 0 blen boff top bot strs NM nn HD nh DT dlen bn bh bd j1 j2 j3 j4 j5 j6
               F3 fc3 z0 z1 z2 (wz n1) b1 b2 b3 b4 b5 b6 b7 (wz NM) z3 z4 z5 z6 PW3 ltac:(clear - N1R; lia) ltac:(clear - CRM PCB; unfold W7P_WCOST in *; lia) LEN2 T c4 Hc4 Hk).
Qed.
End W7P.

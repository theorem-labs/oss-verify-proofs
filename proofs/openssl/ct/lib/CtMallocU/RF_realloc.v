(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B Malloc_iface. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocFacts_Bpres F_ntf F_free_K F_free F_free_spec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface RMalloc_ifaceP RF_ntf RF_free_K RF_free RRealloc_iface RF_realloc_A RF_realloc_B.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import LibProg MI_Inv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require MallocFacts_inv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Ltac showpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => let v := eval vm_compute in (bv_unsigned pc) in idtac "PC" v | _ => idtac "no evt goal" end.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma implM_get_bind' : forall {A} (f : PState -> M PState A) s Q ms,
  implM ctusegs (f s) s Q ms -> implM ctusegs (mbind mget f) s Q ms.
Proof. intros A f s Q ms H. unfold implM, mbind, mget in *. cbn. exact H. Qed.

Lemma bptr_eqb_neq' : forall p q : bptr, p <> q -> bptr_eqb p q = false.
Proof.
  intros [p1 p2] [q1 q2] NE. unfold bptr_eqb. cbn [fst snd].
  destruct (aptr_eqb p1 q1) eqn:E1; [|reflexivity]. destruct (Z.eqb_spec p2 q2) as [E2|]; [|reflexivity].
  exfalso. apply NE. apply aptr_eqb_eq in E1. subst. reflexivity.
Qed.

Lemma lb_remove_cons_ne : forall p b LB, blk_id b <> p -> lb_remove p (b :: LB) = b :: lb_remove p LB.
Proof.
  intros p b LB NE. unfold lb_remove. rewrite filter_cons. destruct (decide _) as [Y|N0]; [reflexivity|].
  exfalso. apply N0. rewrite (bptr_eqb_neq' _ _ NE). exact I.
Qed.

Lemma lb_remove_incl : forall p LB b, In b (lb_remove p LB) -> In b LB.
Proof.
  intros p LB b H. unfold lb_remove in H. apply In_filter_iff in H. exact (proj1 H).
Qed.

(* [comment removed for export] *)
Lemma rw_cells_app_inv : forall m A cs1 cs2,
  rw_cells ctusegs m A (cs1 ++ cs2) -> rw_cells ctusegs m A cs1 /\ rw_cells ctusegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in Hw. destruct Hw as (H0 & H1 & HW).
  split; (split; [split; assumption|]).
  - split; [Lia.lia|]. split; [Lia.lia|]. intros i Hi. apply HW. Lia.lia.
  - split; [Lia.lia|]. split; [Lia.lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by Lia.lia. apply HW. Lia.lia.
Qed.

Lemma rw_cells_app_intro : forall m A cs1 cs2,
  rw_cells ctusegs m A cs1 -> rw_cells ctusegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells ctusegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[W1 B1] (H0 & H1 & HW1)] [[W2 B2] (H2 & H3 & HW2)].
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length _ W1). exact B2.
  - rewrite cells_size_app. split; [Lia.lia|]. split; [Lia.lia|]. intros i Hi.
    destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))) as [L|G]; [apply HW1; Lia.lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by Lia.lia. apply HW2. Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma rheap_pres_stack : forall s LB m m' W SP,
  RHEAP s LB m -> munch W m m' -> wmono ctusegs m m' ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv /\ snd iv <= SP) W ->
  rheap_pres LB SP m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LB m m' W SP HEAP MU WM FW a Ha CA. split; [| apply WM].
  apply MU. rewrite unsigned_lit by Lia.lia. clear MU WM.
  induction W as [|[l h] W IH]; cbn [outside]; [exact I|]. inversion FW as [|x y [F1 F2] FW']; subst. cbn [fst snd] in F1, F2.
  split; [| apply IH; exact FW'].
  intros [A1 A2]. destruct CA as [CA|[[CA _]|(b & Hb & B1)]].
  - Lia.lia.
  - unfold ceil_window in *. Lia.lia.
  - destruct (RHEAP_block_range_proof s LB m b HEAP Hb) as (_ & _ & _ & BC & _). Lia.lia.
Qed.

Section REALLOC.
Hypothesis HM : rmalloc_impl_stmt.
Hypothesis HF : rfree_impl_stmt.

(* [comment removed for export] *)
Theorem rrealloc_spec_proof : rrealloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n0 n lo B errv old
         HEAP Hin AV HB ST LO SLO ERR OLD MI TP A0 A1 N.
  unfold RREALLOC_STACK in SLO.
  pose proof (RHEAP_block_range_proof s LB m (p, A, n0) HEAP Hin) as BR. cbn [blk_addr blk_size fst snd] in BR.
  unfold raw_realloc. apply implM_get_bind'.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  destruct (realloc_moves (ps_m s) (fst p) n) eqn:MOVES; [| apply implM_unr].
  (* [comment removed for export] *)
  pose proof HEAP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n0) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  destruct (MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLm & INV & _ & _ & _ & CR).
  destruct (MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin0) as (k & Hk & (C1 & C2 & C3)).
  destruct k as [[c bo] nn]. cbn [bslot boff bsize blk_slot blk_addr blk_size fst snd] in C1, C2, C3. subst c nn.
  destruct (MI_WFree.block_facts x0 st L BLm LS INV (fst p) bo n0 Hk) as (g' & bm & i' & ai & a & ar & ka & BF).
  pose proof (MI_WFree.bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as [OFF0 _].
  assert (INI : c_init_done (ctx st) <> 0).
  { destruct (MI_WFree.bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Har & _).
    pose proof INV as (IR & IA & _).
    destruct (MI_Inv.ia_secret _ IA) as [_ [(_ & _ & E0)|(E1 & _)]]; [| unfold ctx; lia].
    exfalso. rewrite E0 in Har. rewrite lookup_empty in Har. discriminate. }
  assert (MV : forall g i, (s_slots st) !! (blk_slot (p, A, n0)) = Some (g, i) ->
             get_stride (get_meta_rec st g) - IB < n /\ (m_sizeclass (get_meta_rec st g) < 48 \/ n < MMAP_THRESHOLD)).
  { intros g i SL. cbn [blk_slot fst] in SL. unfold realloc_moves in MOVES. rewrite <- Hst in MOVES. cbn [strip s_slots] in MOVES. rewrite SL in MOVES.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MOVES.
    apply andb_prop in MOVES as [M1 M2]. apply Z.ltb_lt in M1. apply orb_prop in M2. split; [exact M1|].
    destruct M2 as [M2|M2]; [left|right]; apply Z.ltb_lt; exact M2. }
  clear g' bm i' ai a ar ka BF.
  assert (N0N : 0 <= n0 < n).
  { pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n0) Hin0) as BK.
    destruct BK as [(g & i & b & SL & _ & _ & _ & _ & (off' & O0 & _ & OS & _)) _ SZ].
    destruct (MV g i SL) as [MV1 _]. cbn [blk_size snd] in OS, SZ. unfold UNIT, IB in *. lia. }
  destruct BR as (BR0 & BR16 & BRn & BRC & BRI).
  (* [comment removed for export] *)
  unfold implM. iprefix.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl ctusegs m) as WM.
  unfold RREALLOC_SYM, OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *.
  subst a0 a1.
  assert (ETP : bv_unsigned tp + -164 = 3355012) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  assert (ERR0 : rw_cells ctusegs m 3355012 [C4 errv]) by (rewrite <- ETP; exact ERR). clear ERR.
  (* [comment removed for export] *)
  st1. st1. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  carve_frame 64%nat ST.
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [exact MR | exact MUs | exact WM |]; intros l h [E1|[]]; inversion E1; subst; lia);
    assert (HEAP1 : RHEAP s LB mX) by (eapply RHEAP_frame_proof; [exact HEAP| exact MUs| exact WM|]; constructor; [left; cbn; lia| constructor]);
    assert (AV1 : rauxv_ok mX B) by (eapply rauxv_ok_frame; [exact AV| exact MUs| exact WM|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor])
  end.
  eapply evt_cut.
  { eapply rrealloc_hdr_spec with (st:=st) (LB:=LB0) (blk:=(p, A, n0)) (off:=bo) (n:=n) (L:=L) (BL:=BLm) (LS:=LS);
      [exact C| exact Hin0| exact OFF0| exact C3| exact INV| exact Hk| exact MR1| assumption| exact INI| reflexivity| apply unsigned_lit; lia| exact N| exact MV]. }
  cbv beta. intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & ->).
  cbn [blk_addr blk_size fst snd].
  apply evt_done.
  lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
    change (implM ctusegs tm s (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n0 n lo B old m) msx) end.
  (* [comment removed for export] *)
  eapply implM_bind.
  { eapply HM with (B:=B) (lo:=lo) (LB:=LB) (errv:=errv) (n:=n);
      [exact HEAP1| exact AV1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST| exact LO
      | rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| rewrite ETP; exact ERR0| assumption| exact TP| reflexivity| exact N]. }
  cbv beta. intros r s' ms' PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & EFA & ESO & RES).
  rewrite !unsigned_lit in ST2, HPR by lia.
  replace (ret_pc (Z_to_bv 64 2839284)) with (Z_to_bv 64 2839284) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (ERR2' : rw_cells ctusegs m2 3355012 [C4 errv2]) by (rewrite <- ETP; exact ERR2).
  lazymatch type of FR with rw_cells _ ?mX _ _ =>
    assert (HP01 : rheap_pres LB (bv_unsigned sp) m mX)
      by (eapply (rheap_pres_stack s LB m mX); [exact HEAP| exact MUs| exact WM|]; constructor; [cbn [fst snd]; lia| constructor]) end.
  assert (FR2 : rw_cells ctusegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; lia]).
  assert (OLD2 : rw_cells ctusegs m2 A [CB (Z.to_nat n0) old]).
  { eapply rheap_pres_rw_cells; [exact HPR| exact OLD|]. right; right. exists (p, A, n0). split; [exact Hin|].
    cbn [blk_addr blk_size fst snd cells_size csize]. lia. }
  assert (HP02 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m2).
  { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP01| lia| intros b Hb; exact (lb_remove_incl _ _ _ Hb)]|].
    eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact (lb_remove_incl _ _ _ Hb)]. }
  destruct r as [q|].
  2:{ (* [comment removed for export] *)
    destruct RES as [-> HEAP2].
    apply implM_ret.
    st1. if_cases Kn; zify_cond Kn. 2:{ exfalso. rewrite ?unsigned_lit in Kn by lia. lia. }
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold rrealloc_post.
    do 15 eexists. exists m2, errv2.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|].
    split; [exact HP02|]. split; [exact EFA|]. split; [exact ESO|].
    split; [reflexivity|]. split; [exact HEAP2| exact OLD2]. }
  (* [comment removed for export] *)
  destruct RES as (A' & junkn & -> & BR' & HEAP2 & NEW & _).
  destruct BR' as (BR0' & BR16' & BRn' & BRC' & BRI').
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND2. cbn [map blk_id fst] in ND2.
  assert (QP : q <> p).
  { intros ->. inversion ND2 as [|x l NI _]; subst. apply NI. apply in_map_iff. exists (p, A, n0). split; [reflexivity| exact Hin]. }
  pose proof (RHEAP_blocks_disjoint_proof s' _ m2 (q, A', n) (p, A, n0) HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hin) ltac:(cbn; exact QP)) as DJB.
  cbn [blk_addr blk_size fst snd] in DJB.
  pose proof (rw_cells_split_CB ctusegs m2 A' [] (Z.to_nat n) junkn [] [Z.to_nat n0; Z.to_nat (n - n0)] NEW ltac:(cbn; lia)) as NEWS.
  cbn [app mk_CB_cells] in NEWS.
  destruct (rw_cells_app_inv m2 A' [CB (Z.to_nat n0) (firstn (Z.to_nat n0) junkn)] _ NEWS) as [NEWa NEWb].
  cbn [cells_size csize] in NEWb. replace (A' + Z.of_nat (Z.to_nat n0 + 0)) with (A' + n0) in NEWb by lia.
  pose proof (rw_cells_bytes_at ctusegs m2 A _ OLD2) as SRC. cbn [cells_bytes cbytes] in SRC. rewrite app_nil_r in SRC.
  assert (LENo : length old = Z.to_nat n0) by (destruct OLD2 as [[[WFo _] _] _]; exact WFo).
  unfold implM. iprefix.
  (* [comment removed for export] *)
  st1. if_cases Kq; zify_cond Kq. { exfalso. rewrite ?unsigned_lit in Kq by lia. lia. }
  st1. replace (A + n0 + - A) with n0 by lia.
  st1. st1. if_cases Kl; zify_cond Kl. { exfalso. rewrite ?unsigned_lit in Kl by lia. lia. }
  st1. st1. st1. st1.
  eapply evt_cut.
  { eapply F_memcpy.memcpy_spec with (src:=old) (junk:=firstn (Z.to_nat n0) junkn); rewrite ?unsigned_lit by lia;
      [exact SRC| exact LENo| exact NEWa| lia| exact MI2]. }
  cbv beta. intros ms3 PO3.
  destruct PO3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3).
  assert (EN0 : bv_unsigned (Z_to_bv 64 n0) = n0) by (apply unsigned_lit; lia).
  assert (EA' : bv_unsigned (Z_to_bv 64 A') = A') by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  rewrite ?EN0, ?EA', ?EA in MU3. rewrite ?EN0, ?EA', ?EA in DST3. rewrite ?EN0, ?EA', ?EA in SRC3.
  replace (ret_pc (Z_to_bv 64 2839316)) with (Z_to_bv 64 2839316) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (HEAP3 : RHEAP s' ((q, A', n) :: LB) m3).
  { eapply RHEAP_frame_proof; [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor].
    right; right. exists (q, A', n). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
  assert (AUX3 : rauxv_ok m3 B).
  { eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
  assert (FR3 : rw_cells ctusegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]; cbn [disjoint_from cells_size csize]; lia).
  assert (ERR3 : rw_cells ctusegs m3 3355012 [C4 errv2])
    by (eapply rw_cells_transport; [exact ERR2'| exact MU3| exact WM3|]; cbn [disjoint_from cells_size csize]; lia).
  assert (NEWb3 : rw_cells ctusegs m3 (A' + n0) [CB (Z.to_nat (n - n0)) (firstn (Z.to_nat (n - n0)) (skipn (Z.to_nat n0) junkn))])
    by (eapply rw_cells_transport; [exact NEWb| exact MU3| exact WM3|]; cbn [disjoint_from cells_size csize]; lia).
  assert (ST3 : stk ctusegs m3 lo (bv_unsigned sp + -64))
    by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]; cbn [disjoint_from]; lia).
  assert (HP23 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m2 m3).
  { intros x Hx CA. split; [| apply WM3]. apply MU3. cbn [outside]. split; [| exact I].
    intros [X1 X2]. destruct CA as [CA|[[CA _]|(b & Hb & B1)]].
    + rewrite unsigned_lit in X1, X2 by lia. lia.
    + rewrite unsigned_lit in X1, X2 by lia. lia.
    + pose proof (RHEAP_blocks_disjoint_proof s' _ m2 (q, A', n) b HEAP2 ltac:(left; reflexivity) ltac:(right; exact (lb_remove_incl _ _ _ Hb))) as DJ2.
      cbn [blk_addr blk_size blk_id fst snd] in DJ2.
      assert (NEq : q <> blk_id b).
      { intros ->. inversion ND2 as [|y l NI _]; subst. apply NI. apply in_map_iff. exists b. split; [reflexivity| exact (lb_remove_incl _ _ _ Hb)]. }
      specialize (DJ2 NEq). rewrite unsigned_lit in X1, X2 by lia. lia. }
  (* [comment removed for export] *)
  st1. st1.
  apply evt_done.
  lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
    change (implM ctusegs tm s' (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n0 n lo B old m) msx) end.
  eapply implM_bind.
  { eapply HF with (B:=B) (lo:=lo) (LB:=(q, A', n) :: LB) (p:=p) (A:=A) (n:=n0) (errv:=errv2);
      [exact HEAP3| right; exact Hin| exact AUX3| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST3| exact LO
      | rewrite unsigned_lit by lia; unfold RFREE_STACK; lia| rewrite ETP; exact ERR3| exact MI3| exact TP| reflexivity]. }
  cbv beta. intros [] s'' ms4 PO4.
  destruct PO4 as (w0 & w1 & w2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR4 & EFA4 & ESO4 & HEAP4).
  rewrite !unsigned_lit in ST4, HPR4 by lia.
  replace (ret_pc (Z_to_bv 64 2839324)) with (Z_to_bv 64 2839324) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite (lb_remove_cons_ne p (q, A', n) LB ltac:(cbn; exact QP)) in HPR4, HEAP4.
  assert (FR4 : rw_cells ctusegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rheap_pres_rw_cells; [exact HPR4| exact FR3| left; lia]).
  assert (DST4 : rw_cells ctusegs m4 A' [CB (Z.to_nat n0) old]).
  { eapply rheap_pres_rw_cells; [exact HPR4| exact DST3|]. right; right. exists (q, A', n). split; [left; reflexivity|].
    cbn [blk_addr blk_size fst snd cells_size csize]. lia. }
  assert (NEWb4 : rw_cells ctusegs m4 (A' + n0) [CB (Z.to_nat (n - n0)) (firstn (Z.to_nat (n - n0)) (skipn (Z.to_nat n0) junkn))]).
  { eapply rheap_pres_rw_cells; [exact HPR4| exact NEWb3|]. right; right. exists (q, A', n). split; [left; reflexivity|].
    cbn [blk_addr blk_size fst snd cells_size csize]. lia. }
  apply implM_ret.
  (* [comment removed for export] *)
  st1. st1.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR4 ST4 (bv_unsigned sp).
  apply evt_done. unfold rrealloc_post.
  do 15 eexists. exists m4, errv2.
  split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|].
  split.
  { eapply rheap_pres_trans; [exact HP02|]. eapply rheap_pres_trans; [exact HP23|].
    eapply rheap_pres_weaken; [exact HPR4| lia| intros b Hb; right; exact Hb]. }
  split; [rewrite EFA4; exact EFA|]. split; [rewrite ESO4; exact ESO|].
  exists A', (firstn (Z.to_nat (n - n0)) (skipn (Z.to_nat n0) junkn)).
  split; [reflexivity|]. split; [unfold rblock_range; repeat split; assumption|]. split; [exact HEAP4|]. split; [| lia].
  apply (rw_cells_app_intro m4 A' [CB (Z.to_nat n0) old] [CB (Z.to_nat (n - n0)) (firstn (Z.to_nat (n - n0)) (skipn (Z.to_nat n0) junkn))]); [exact DST4|].
  cbn [cells_size csize]. replace (A' + Z.of_nat (Z.to_nat n0 + 0)) with (A' + n0) by lia. exact NEWb4.
Qed.
End REALLOC.
End WithCeiling0.

(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxQuery.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound HxsKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaImage HxaInv HxaHooks HxaHkRelease HxaRun HxaIface HxaMain HxaQuery.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import BnHeapA LibKitA BnRepDefs LibaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KS_BNNEW : list kb := kbs_bytes (repeat 0 20 ++ [1; 0; 0; 0]).
(* [comment removed for export] *)
Definition Q_pb (i : Z) (t : int) : query := Q 8 12411008 0 (32 * i) (kbs_ptr t).
Definition Q_b (t : int) : query := Q t 0 24 0 KS_BNNEW.
Definition Q_ctx : query := Q 42 0 72 0 (kbs_bytes (repeat 0 72)).
Definition Q_memset_func : query := Q 6 6186592 0 0 (kbs_Z 8 0x1bcc34).
Definition Q_malloc_impl : query := Q 6 6186592 0 32 (kbs_Z 8 0x1f261c).
Definition Q_free_impl : query := Q 6 6186592 0 96 (kbs_Z 8 0x1f2b40).
Definition Q_no_customize : query := Q 8 12411008 0 192 (kbs_Z 1 1).
Definition Q_stopped : query := Q 8 12411008 0 1440 (kbs_Z 1 0).
Definition Q_optsdone : query := Q 8 12411008 0 1600 (kbs_Z 8 2).
Definition Q_base_once : query := Q 8 12411008 0 1632 (kbs_Z 4 2).
Definition Q_base_ret : query := Q 8 12411008 0 1664 (kbs_Z 4 1).
Definition Q_master_once : query := Q 8 12411008 0 352 (kbs_Z 4 2).
Definition Q_master_key : query := Q 8 12411008 0 384 (kbs_Z 4 3).
Definition Q_tsd : query := Q 15 12567040 0 16 (kbs_ptr 64).
Definition Q_mk : query := Q 64 0 72 24 (kbs_ptr 66).
Definition Q_sa : query := Q 66 0 32 0 (kbs_Z 4 1 ++ kbs_any 4 ++ kbs_Z 8 0 ++ kbs_Z 8 1 ++ kbs_ptr 68).
Definition Q_nd : query := Q 68 0 128 0 (kbs_ptr 3298).
Definition Q_es : query := Q 3298 0 904 0 (kbs_bytes (repeat 0 704 ++ repeat 255 64 ++ repeat 0 136)).
Definition Q_base_inited : query := Q 8 12411008 0 1376 (kbs_any 1).
Definition Q_do_cleanup : query := Q 8 12411008 0 1408 (kbs_Z 1 0).

Definition QS : list query :=
  [Q_pb 0 32; Q_pb 1 34; Q_pb 2 36; Q_pb 3 38; Q_pb 4 40; Q_pb 5 42; Q_b 32; Q_b 34; Q_b 36; Q_b 38; Q_b 40; Q_ctx;
   Q_memset_func; Q_malloc_impl; Q_free_impl; Q_no_customize; Q_stopped; Q_optsdone; Q_base_once; Q_base_ret; Q_master_once; Q_master_key;
   Q_tsd; Q_mk; Q_sa; Q_nd; Q_es; Q_base_inited; Q_do_cleanup].

Definition TAGS10 : list int := [32; 34; 36; 38; 40; 42; 64; 66; 68; 3298]%uint63.

(* [comment removed for export] *)
Definition blk_al_ok (S : sstate) (t : int) : bool :=
  match mget (s_mem S) t with Some rg => (rg_al rg =? 4)%uint63 | None => false end.

Definition fin_ok (x : icache * @xres xcd) : bool :=
  match snd x with
  | XDone cd St => forallb (q_ok St) QS && forallb (fun t => existsb (fun t' => (t =? t')%uint63) (x_blocks cd)) TAGS10
                   && forallb (blk_al_ok St) (x_blocks cd) && (x_nb cd <=? 1600)
                   && match mget (s_mem St) 8 with Some rg => rg_wr rg | None => false end
  | _ => false
  end.

(* [comment removed for export] *)
Lemma fin_checked_0 : fin_ok (run_result 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fin_checked_16 : fin_ok (run_result 16) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition id_of (t : int) : Prog.bptr := ((0%N, 0), to_Z t).
Definition OW_of (rho : valuation) (M : HxMem.mem) (bl : list int) : list block := map (fun t => (id_of t, rho t, rsize M t)) bl.

Lemma OW_an (rho : valuation) (M : HxMem.mem) (bl : list int) : map blk_an (OW_of rho M bl) = blk_list rho M bl.
Proof. unfold OW_of, blk_list. rewrite map_map. apply map_ext. intros t. reflexivity. Qed.

Lemma OW_ids_nodup (rho : valuation) (M : HxMem.mem) (bl : list int) : List.NoDup bl -> List.NoDup (map blk_id (OW_of rho M bl)).
Proof.
  intros H. unfold OW_of. rewrite map_map. cbn [blk_id fst]. induction H as [|t l Hni Hnd IH]; [constructor|]. cbn [map]. constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (t' & E & Ht'). unfold id_of in E. injection E as E. apply to_Z_inj in E. subst t'. exact (Hni Ht').
Qed.

Lemma ids10_nodup : List.NoDup (map id_of TAGS10).
Proof. vm_compute. repeat (constructor; [cbn [In]; intuition discriminate|]). constructor. Qed.

(* [comment removed for export] *)
Lemma IDX3 : TL_MASTER_KEY_IDX = 3.
Proof. reflexivity. Qed.

Section Final.
Variable RT : rt_sig.

Local Ltac qin := unfold QS; cbn [In]; repeat (first [left; reflexivity | right]).

Theorem LIBA_final_A : forall (ri : int) (ic : icache) (cd : xcd) (S : sstate) (CL : list (Z * Z)) (lo sp0 : Z) (m0 : word -> option byte) (cr0 anc : Z)
    (rho : valuation) (Σ' : rts RT) (ms' : machine_state),
  ri = 0%uint63 \/ ri = 16%uint63 -> run_result ri = (ic, XDone cd S) ->
  XInv bsegs SHBW (ghost RT) (FInv RT CL lo sp0 (to_Z ri) m0 cr0 anc XP_INIT) (GH RT Σ') rho cd S ms' ->
  LIBA RT Σ' (blk_list rho (s_mem S) (x_blocks cd)) (ms_mem ms').
Proof.
  intros ri ic cd S CL lo sp0 m0 cr0 anc rho Σ' ms' H_ri Erun [[HRn _] [HF _]].
  assert (Hfin : fin_ok (run_result ri) = true) by (destruct H_ri as [-> | ->]; [exact fin_checked_0 | exact fin_checked_16]).
  rewrite Erun in Hfin. cbn [fin_ok snd] in Hfin.
  apply andb_prop in Hfin as [Hfin Hwr8]. apply andb_prop in Hfin as [Hfin Hnb]. apply andb_prop in Hfin as [Hfin HAl]. apply andb_prop in Hfin as [HQ HT].
  apply Z.leb_le in Hnb.
  assert (fin_q : forall q, In q QS -> q_ok S q = true) by exact (proj1 (forallb_forall (q_ok S) QS) HQ).
  assert (fin_t : forall t, In t TAGS10 -> In t (x_blocks cd)).
  { intros t Ht. pose proof (proj1 (forallb_forall _ _) HT t Ht) as X. cbv beta in X. apply existsb_exists in X as (t' & Hin & E). apply Uint63.eqb_spec in E. subst t'. exact Hin. }
  set (m' := ms_mem ms') in *. pose proof (Rn_R bsegs rho S ms' HRn) as (_ & _ & _ & _ & HR). fold m' in HR.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & Hbnd & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr & Hanc & _).
  set (OW := OW_of rho (s_mem S) (x_blocks cd)).
  rewrite <- (OW_an rho (s_mem S) (x_blocks cd)). fold OW.
  (* [comment removed for export] *)
  assert (q_blk : forall q, In q QS -> q_lo q = 0 -> In (q_tag q) TAGS10 ->
            In (id_of (q_tag q), rho (q_tag q), q_size q) OW /\ 0 < rho (q_tag q) /\ rho (q_tag q) + q_size q < 2 ^ 63).
  { intros q Hq E0 Ht. destruct (q_sound rho S m' q HR (fin_q q Hq)) as (rg & bs & Eg & _ & _ & _ & Hh).
    destruct (Hh E0) as (Ea & Es & Hwr & Hne & Hpos & Hr0 & Hr1). split; [|split; assumption].
    unfold OW, OW_of. apply in_map_iff. exists (q_tag q). split; [|exact (fin_t _ Ht)]. rewrite (rsize_get _ _ rg Eg), Es. reflexivity. }
  destruct (q_blk (Q_b 32) ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I1 & P1 & L1).
  destruct (q_blk (Q_b 34) ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I2 & P2 & L2).
  destruct (q_blk (Q_b 36) ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I3 & P3 & L3).
  destruct (q_blk (Q_b 38) ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I4 & P4 & L4).
  destruct (q_blk (Q_b 40) ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I5 & P5 & L5).
  destruct (q_blk Q_ctx ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I6 & P6 & L6).
  destruct (q_blk Q_mk ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I8 & P8 & L8).
  destruct (q_blk Q_sa ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I9 & P9 & L9).
  destruct (q_blk Q_nd ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I10 & P10 & L10).
  destruct (q_blk Q_es ltac:(qin) eq_refl ltac:(cbn; tauto)) as (IE & PE & LE).
  cbn [q_tag q_size Q_b Q_ctx Q_mk Q_sa Q_nd Q_es] in I1, I2, I3, I4, I5, I6, I8, I9, I10, IE, P1, P2, P3, P4, P5, P6, P8, P9, P10, PE, L1, L2, L3, L4, L5, L6, L8, L9, L10, LE.
  (* [comment removed for export] *)
  assert (HndOW : List.NoDup (map blk_id OW)) by (apply OW_ids_nodup; exact (NoDup_app_remove_r _ _ Hnd)).
  assert (HokOW : Forall blk_okA OW).
  { apply Forall_forall. intros b Hb. unfold OW, OW_of in Hb. apply in_map_iff in Hb as (t & <- & Ht). unfold blk_okA. cbn [blk_addr blk_size fst snd].
    destruct (proj1 Hlink t Ht) as (rg & Eg & Ea & Ew & Hs0 & Hs8). rewrite (rsize_get _ _ rg Eg). split; [|exact Hs0].
    pose proof (proj1 (forallb_forall _ _) HAl t Ht) as X. unfold blk_al_ok in X. rewrite Eg in X. apply Uint63.eqb_spec in X.
    destruct (proj1 HR t rg Eg) as (_ & _ & _ & _ & _ & _ & Hmod & _). unfold rbase in Hmod. rewrite Ea, X in Hmod. exact Hmod. }
  assert (HlenOW : Z.of_nat (length OW) <= LIBA_BAL) by (unfold OW, OW_of, LIBA_BAL; rewrite length_map; lia).
  clearbody OW.
  apply (LIBA_init RT Σ' m' OW); [|exact HndOW | exact HokOW | exact HlenOW].
  exists (mkAD (rho 32%uint63) (rho 34%uint63) (rho 36%uint63) (rho 38%uint63) (rho 40%uint63) (rho 42%uint63)
               (id_of 32) (id_of 34) (id_of 36) (id_of 38) (id_of 40) (id_of 42)),
         (mkEA (rho 64%uint63) (rho 66%uint63) (rho 68%uint63) (rho 3298%uint63) (id_of 64) (id_of 66) (id_of 68) (id_of 3298)).
  cbn [ad_b1 ad_b2 ad_b3 ad_b4 ad_b5 ad_ctx ad_p1 ad_p2 ad_p3 ad_p4 ad_p5 ad_pc ea_MK ea_SA ea_ND ea_ES ea_pk ea_ps ea_pn ea_pe ad_ids ea_ids ad_blocks app].
  split; [exact ids10_nodup|].
  split; [repeat split; assumption|].
  (* [comment removed for export] *)
  assert (HP8 : forall q t, In q QS -> q_ks q = kbs_ptr t -> 0 < rho t -> rho t < 2 ^ 63 -> ro_cells bsegs m' (q_addr rho q) [C8 (wz (rho t))]).
  { intros q t Hin Ek H0 H1. apply (q_cells rho S m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C8 (wz (rho t))])); [|exact H]. intros b' H'. exact (F2_ptr rho t [] [] b' H0 H1 (F2_nil rho) H'). }
  assert (HL8 : forall q z, In q QS -> q_ks q = kbs_Z 8 z -> 0 <= z < 2 ^ 64 -> ro_cells bsegs m' (q_addr rho q) [C8 (wz z)]).
  { intros q z Hin Ek Hz. apply (q_cells rho S m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C8 (wz z)])); [|exact H]. intros b' H'. exact (F2_lit8 rho z [] [] b' Hz (F2_nil rho) H'). }
  assert (HL4 : forall q z, In q QS -> q_ks q = kbs_Z 4 z -> 0 <= z < 2 ^ 64 -> ro_cells bsegs m' (q_addr rho q) [C4 (wz z)]).
  { intros q z Hin Ek Hz. apply (q_cells rho S m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C4 (wz z)])); [|exact H]. intros b' H'. exact (F2_lit4 rho z [] [] b' Hz (F2_nil rho) H'). }
  assert (HL1 : forall q z, In q QS -> q_ks q = kbs_Z 1 z -> 0 <= z -> ro_cells bsegs m' (q_addr rho q) [C1 (Z_to_bv 8 z)]).
  { intros q z Hin Ek Hz. apply (q_cells rho S m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C1 (Z_to_bv 8 z)])); [|exact H]. intros b' H'. exact (F2_lit1 rho z [] [] b' Hz (F2_nil rho) H'). }
  (* [comment removed for export] *)
  split.
  { unfold ad_statics. cbn [ad_b1 ad_b2 ad_b3 ad_b4 ad_b5 ad_ctx].
    split; [exact (HP8 (Q_pb 0 32) 32%uint63 ltac:(qin) eq_refl P1 ltac:(lia))|].
    split; [exact (HP8 (Q_pb 1 34) 34%uint63 ltac:(qin) eq_refl P2 ltac:(lia))|].
    split; [exact (HP8 (Q_pb 2 36) 36%uint63 ltac:(qin) eq_refl P3 ltac:(lia))|].
    split; [exact (HP8 (Q_pb 3 38) 38%uint63 ltac:(qin) eq_refl P4 ltac:(lia))|].
    split; [exact (HP8 (Q_pb 4 40) 40%uint63 ltac:(qin) eq_refl P5 ltac:(lia))|].
    exact (HP8 (Q_pb 5 42) 42%uint63 ltac:(qin) eq_refl P6 ltac:(lia)). }
  (* [comment removed for export] *)
  assert (HBN : forall t, In (Q_b t) QS -> rw_cells bsegs m' (rho t) [CB 24 BN_NEW_BYTES]).
  { intros t Hin. pose proof (q_rw_cells rho S m' (Q_b t) [CB 24 BN_NEW_BYTES] HR (fin_q (Q_b t) Hin) eq_refl ltac:(cbn; tauto) eq_refl) as X.
    cbn [q_tag q_off Q_b] in X. rewrite Z.add_0_r in X. apply X. intros bs H. rewrite (F2_bytes rho _ bs H). reflexivity. }
  split; [exact (HBN 32%uint63 ltac:(qin))|]. split; [exact (HBN 34%uint63 ltac:(qin))|]. split; [exact (HBN 36%uint63 ltac:(qin))|].
  split; [exact (HBN 38%uint63 ltac:(qin))|]. split; [exact (HBN 40%uint63 ltac:(qin))|].
  split.
  { pose proof (q_rw_cells rho S m' Q_ctx [CB 72 (repeat (Z_to_bv 8 0) 72)] HR (fin_q Q_ctx ltac:(qin)) eq_refl ltac:(cbn; tauto) eq_refl) as X.
    cbn [q_tag q_off Q_ctx] in X. rewrite Z.add_0_r in X. apply X. intros bs H. rewrite (F2_bytes rho _ bs H). reflexivity. }
  split.
  { unfold crypto_statics.
    split; [exact (HL8 Q_memset_func _ ltac:(qin) eq_refl ltac:(lia))|].
    split; [exact (HL8 Q_malloc_impl _ ltac:(qin) eq_refl ltac:(lia))|].
    split; [exact (HL8 Q_free_impl _ ltac:(qin) eq_refl ltac:(lia))|].
    exact (HL1 Q_no_customize _ ltac:(qin) eq_refl ltac:(lia)). }
  split.
  { split.
    - unfold err_statics. rewrite IDX3.
      split; [exact (HL1 Q_stopped _ ltac:(qin) eq_refl ltac:(lia))|].
      split; [exact (HL8 Q_optsdone _ ltac:(qin) eq_refl ltac:(lia))|].
      split; [exact (HL4 Q_base_once _ ltac:(qin) eq_refl ltac:(lia))|].
      split; [exact (HL4 Q_base_ret _ ltac:(qin) eq_refl ltac:(lia))|].
      split; [exact (HL4 Q_master_once _ ltac:(qin) eq_refl ltac:(lia))|].
      exact (HL4 Q_master_key _ ltac:(qin) eq_refl ltac:(lia)).
    - unfold err_mem. cbn [ea_MK ea_SA ea_ND ea_ES ea_pk ea_ps ea_pn ea_pe]. rewrite IDX3.
      split; [exact I8|]. split; [exact I9|]. split; [exact I10|]. split; [exact IE|].
      split; [exact (HP8 Q_tsd 64%uint63 ltac:(qin) eq_refl P8 ltac:(lia))|].
      split.
      { pose proof (HP8 Q_mk 66%uint63 ltac:(qin) eq_refl P9 ltac:(lia)) as X. unfold q_addr in X. cbn [q_lo q_tag q_off Q_mk Z.eqb] in X. exact X. }
      split.
      { destruct (q_sound rho S m' Q_sa HR (fin_q Q_sa ltac:(qin))) as (rg & bs & _ & HFs & Hb & _).
        unfold q_addr in Hb. cbn [q_lo q_tag q_off Q_sa Z.eqb] in Hb. rewrite Z.add_0_r in Hb.
        unfold Q_sa in HFs. cbn [q_ks] in HFs.
        destruct (Forall2_app_split _ _ _ _ HFs) as (b1 & r1 & -> & F1 & HF1).
        destruct (Forall2_app_split _ _ _ _ HF1) as (pad & r2 & -> & F2 & HF2).
        exists pad. split; [cbn [cells_wf cell_wf]; split; [exact I|]; split; [symmetry; exact (Forall2_length F2)|]; cbn; tauto|].
        cbn [cells_bytes cbytes]. rewrite (bs_lit4 rho 1 b1 ltac:(lia) F1) in Hb.
        assert (E2 : r2 = cells_bytes [C8 (wz 0); C8 (wz 1); C8 (wz (rho 68%uint63))]).
        { eapply (F2_lit8 rho 0); [lia | | exact HF2]. intros b3 H3.
          eapply (F2_lit8 rho 1); [lia | | exact H3]. intros b4 H4.
          eapply (F2_tail rho _ b4 (fun b => b = cells_bytes [C8 (wz (rho 68%uint63))])); [|exact H4]. intros b' H'.
          exact (F2_ptr rho 68%uint63 [] [] b' P10 ltac:(lia) (F2_nil rho) H'). }
        rewrite E2 in Hb. exact Hb. }
      split.
      { pose proof (HP8 Q_nd 3298%uint63 ltac:(qin) eq_refl PE ltac:(lia)) as X. unfold q_addr in X. cbn [q_lo q_tag q_off Q_nd Z.eqb] in X. rewrite Z.add_0_r in X. exact X. }
      pose proof (q_rw_cells rho S m' Q_es [CB 904 ES_CLEARED] HR (fin_q Q_es ltac:(qin)) eq_refl ltac:(cbn; tauto) eq_refl) as X.
      cbn [q_tag q_off Q_es] in X. rewrite Z.add_0_r in X. apply X. intros bs H. rewrite (F2_bytes rho _ bs H). reflexivity. }
  (* [comment removed for export] *)
  destruct (q_sound rho S m' Q_base_inited HR (fin_q Q_base_inited ltac:(qin))) as (rg1 & bs1 & Eg1 & HF1 & Hb1 & Hw1 & _).
  destruct (q_sound rho S m' Q_do_cleanup HR (fin_q Q_do_cleanup ltac:(qin))) as (rg2 & bs2 & Eg2 & HF2 & Hb2 & Hw2 & _).
  cbn [q_tag Q_base_inited Q_do_cleanup] in Eg1, Eg2. rewrite Eg1 in Hwr8. rewrite Eg2 in Eg1. injection Eg1 as <-.
  unfold q_addr in Hb1, Hw1, Hb2, Hw2. cbn [q_lo q_off q_ks Q_base_inited Q_do_cleanup Z.eqb length kbs_any repeat kbs_Z map seq] in Hb1, Hw1, Hb2, Hw2.
  unfold kbs_any in HF1. cbn [q_ks Q_base_inited repeat] in HF1. inversion HF1 as [|k1 b0 ks1 bt1 _ Hnil1 E1 E2]. inversion Hnil1. subst.
  rewrite (bs_lit1 rho 0 bs2 ltac:(lia) HF2) in Hb2.
  exists b0. unfold OSSL_BASE_INITED, OSSL_DO_GLOBAL_CLEANUP. split.
  - split; [split; [cbn; tauto | exact Hb1] | exact (Hw1 Hwr8)].
  - split; [split; [cbn; tauto | exact Hb2] | exact (Hw2 Hwr8)].
Qed.

End Final.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Close.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
(* [comment removed for export] *)
Hypothesis LIVE_POS : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> 0 < n.

Lemma frel_of_AF : frame_release_x RT.
Proof. exact (af_frame_release RT AF). Qed.

Theorem init_cps_A : init_cps RT (LIBA RT).
Proof. exact (init_cps_hx RT AF RTC LIVE_POS frel_of_AF (LIBA RT) (LIBA_final_A RT)). Qed.

End Close.

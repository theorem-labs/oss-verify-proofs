(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxQuery.
From OSSVerify.Proofs.openssl.bignum.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound HxsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXB Require Import HxbInit HxbImage HxbInv HxbHooks HxbHkRelease HxbRun HxbIface HxbMain HxbQuery.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import BnHeapA LibKitA BnRepDefs.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer LibaBg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition T_MK : int := 52.  Definition T_SA : int := 54.  Definition T_ND : int := 56.  Definition T_ES : int := 3286.
Definition Q_memset_func : query := Q 6 6170752 0 160 (kbs_Z 8 0x1bc8ac).
Definition Q_malloc_impl : query := Q 6 6170752 0 64 (kbs_Z 8 0x1fb01c).
Definition Q_free_impl : query := Q 6 6170752 0 128 (kbs_Z 8 0x1fb53c).
Definition Q_no_customize : query := Q 8 12394688 0 1664 (kbs_Z 1 1).
Definition Q_stopped : query := Q 8 12394688 0 64 (kbs_Z 1 0).
Definition Q_optsdone : query := Q 8 12394688 0 224 (kbs_Z 8 2).
Definition Q_base_once : query := Q 8 12394688 0 256 (kbs_Z 4 2).
Definition Q_base_ret : query := Q 8 12394688 0 288 (kbs_Z 4 1).
Definition Q_master_once : query := Q 8 12394688 0 832 (kbs_Z 4 2).
Definition Q_master_key : query := Q 8 12394688 0 864 (kbs_Z 4 3).
Definition Q_tsd : query := Q 15 12550560 0 16 (kbs_ptr T_MK).
Definition Q_mk : query := Q T_MK 0 72 24 (kbs_ptr T_SA).
Definition Q_sa : query := Q T_SA 0 32 0 (kbs_Z 4 1 ++ kbs_any 4 ++ kbs_Z 8 0 ++ kbs_Z 8 1 ++ kbs_ptr T_ND).
Definition Q_nd : query := Q T_ND 0 128 0 (kbs_ptr T_ES).
Definition Q_es : query := Q T_ES 0 904 0 (kbs_bytes (repeat 0 704 ++ repeat 255 64 ++ repeat 0 136)).
Definition Q_base_inited : query := Q 8 12394688 0 0 (kbs_any 1).
Definition Q_do_cleanup : query := Q 8 12394688 0 32 (kbs_Z 1 0).

Definition QS : list query :=
  [Q_memset_func; Q_malloc_impl; Q_free_impl; Q_no_customize; Q_stopped; Q_optsdone; Q_base_once; Q_base_ret; Q_master_once; Q_master_key;
   Q_tsd; Q_mk; Q_sa; Q_nd; Q_es; Q_base_inited; Q_do_cleanup].

Definition TAGS4 : list int := [T_MK; T_SA; T_ND; T_ES].

Definition blk_al_ok (S : sstate) (t : int) : bool :=
  match mget (s_mem S) t with Some rg => (rg_al rg =? 4)%uint63 | None => false end.

Definition fin_ok (x : icache * @xres xcd) : bool :=
  match snd x with
  | XDone cd St => forallb (q_ok St) QS && forallb (fun t => existsb (fun t' => (t =? t')%uint63) (x_blocks cd)) TAGS4
                   && forallb (blk_al_ok St) (x_blocks cd) && (x_nb cd <=? 1600)
                   && match mget (s_mem St) 8 with Some rg => rg_wr rg | None => false end
  | _ => false
  end.

Lemma fin_checked_0 : fin_ok (run_result 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fin_checked_16 : fin_ok (run_result 16) = true.
Proof. vm_compute. reflexivity. Qed.

Definition id_of (t : int) : Prog.bptr := ((0%N, 0), to_Z t).
Definition OW_of (rho : valuation) (M : HxMem.mem) (bl : list int) : list block := map (fun t => (id_of t, rho t, rsize M t)) bl.

Lemma OW_an (rho : valuation) (M : HxMem.mem) (bl : list int) : map blk_an (OW_of rho M bl) = blk_list rho M bl.
Proof. unfold OW_of, blk_list. rewrite map_map. apply map_ext. intros t. reflexivity. Qed.

Lemma OW_ids_nodup (rho : valuation) (M : HxMem.mem) (bl : list int) : List.NoDup bl -> List.NoDup (map blk_id (OW_of rho M bl)).
Proof.
  intros H. unfold OW_of. rewrite map_map. cbn [blk_id fst]. induction H as [|t l Hni Hnd IH]; [constructor|]. cbn [map]. constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (t' & E & Ht'). unfold id_of in E. injection E as E. apply to_Z_inj in E. subst t'. exact (Hni Ht').
Qed.

Lemma ids4_nodup : List.NoDup (map id_of TAGS4).
Proof. vm_compute. repeat (constructor; [cbn [In]; intuition discriminate|]). constructor. Qed.

Lemma IDX3 : TL_MASTER_KEY_IDX = 3.
Proof. reflexivity. Qed.

Section Final.
Variable RT : rt_sig.

Local Ltac qin := unfold QS; cbn [In]; repeat (first [left; reflexivity | right]).

Theorem LIBA_final_A : forall (ri : int) (ic : icache) (cd : xcd) (S : sstate) (CL : list (Z * Z)) (lo sp0 : Z) (m0 : word -> option byte) (cr0 anc : Z)
    (rho : valuation) (Σ' : rts RT) (ms' : machine_state),
  ri = 0%uint63 \/ ri = 16%uint63 -> run_result ri = (ic, XDone cd S) ->
  XInv bgbsegs SHBW (ghost RT) (FInv RT CL lo sp0 (to_Z ri) m0 cr0 anc XP_INIT) (GH RT Σ') rho cd S ms' ->
  LIBA RT Σ' (blk_list rho (s_mem S) (x_blocks cd)) (ms_mem ms').
Proof.
  intros ri ic cd S CL lo sp0 m0 cr0 anc rho Σ' ms' H_ri Erun [[HRn _] [HF _]].
  assert (Hfin : fin_ok (run_result ri) = true) by (destruct H_ri as [-> | ->]; [exact fin_checked_0 | exact fin_checked_16]).
  rewrite Erun in Hfin. cbn [fin_ok snd] in Hfin.
  apply andb_prop in Hfin as [Hfin Hwr8]. apply andb_prop in Hfin as [Hfin Hnb]. apply andb_prop in Hfin as [Hfin HAl]. apply andb_prop in Hfin as [HQ HT].
  apply Z.leb_le in Hnb.
  assert (fin_q : forall q, In q QS -> q_ok S q = true) by exact (proj1 (forallb_forall (q_ok S) QS) HQ).
  assert (fin_t : forall t, In t TAGS4 -> In t (x_blocks cd)).
  { intros t Ht. pose proof (proj1 (forallb_forall _ _) HT t Ht) as X. cbv beta in X. apply existsb_exists in X as (t' & Hin & E). apply Uint63.eqb_spec in E. subst t'. exact Hin. }
  set (m' := ms_mem ms') in *. pose proof (Rn_R bgbsegs rho S ms' HRn) as (_ & _ & _ & _ & HR). fold m' in HR.
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrho & HART & Hmi & Hstk & Hbnd & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr & Hanc & _).
  set (OW := OW_of rho (s_mem S) (x_blocks cd)).
  rewrite <- (OW_an rho (s_mem S) (x_blocks cd)). fold OW.

  assert (q_blk : forall q, In q QS -> q_lo q = 0 -> In (q_tag q) TAGS4 ->
            In (id_of (q_tag q), rho (q_tag q), q_size q) OW /\ 0 < rho (q_tag q) /\ rho (q_tag q) + q_size q < 2 ^ 63).
  { intros q Hq E0 Ht. destruct (q_sound rho S m' q HR (fin_q q Hq)) as (rg & bs & Eg & _ & _ & _ & Hh).
    destruct (Hh E0) as (Ea & Es & Hwr & Hne & Hpos & Hr0 & Hr1). split; [|split; assumption].
    unfold OW, OW_of. apply in_map_iff. exists (q_tag q). split; [|exact (fin_t _ Ht)]. rewrite (rsize_get _ _ rg Eg), Es. reflexivity. }
  destruct (q_blk Q_mk ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I8 & P8 & L8).
  destruct (q_blk Q_sa ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I9 & P9 & L9).
  destruct (q_blk Q_nd ltac:(qin) eq_refl ltac:(cbn; tauto)) as (I10 & P10 & L10).
  destruct (q_blk Q_es ltac:(qin) eq_refl ltac:(cbn; tauto)) as (IE & PE & LE).
  cbn [q_tag q_size Q_mk Q_sa Q_nd Q_es] in I8, I9, I10, IE, P8, P9, P10, PE, L8, L9, L10, LE.

  assert (HndOW : List.NoDup (map blk_id OW)) by (apply OW_ids_nodup; exact (NoDup_app_remove_r _ _ Hnd)).
  assert (HokOW : Forall blk_okA OW).
  { apply Forall_forall. intros b Hb. unfold OW, OW_of in Hb. apply in_map_iff in Hb as (t & <- & Ht). unfold blk_okA. cbn [blk_addr blk_size fst snd].
    destruct (proj1 Hlink t Ht) as (rg & Eg & Ea & Ew & Hs0 & Hs8). rewrite (rsize_get _ _ rg Eg). split; [|exact Hs0].
    pose proof (proj1 (forallb_forall _ _) HAl t Ht) as X. unfold blk_al_ok in X. rewrite Eg in X. apply Uint63.eqb_spec in X.
    destruct (proj1 HR t rg Eg) as (_ & _ & _ & _ & _ & _ & Hmod & _). unfold rbase in Hmod. rewrite Ea, X in Hmod. exact Hmod. }
  assert (HlenOW : Z.of_nat (length OW) <= LIBA_BAL) by (unfold OW, OW_of, LIBA_BAL; rewrite length_map; lia).
  clearbody OW.
  apply (LIBA_init RT Σ' m' OW); [|exact HndOW | exact HokOW | exact HlenOW].
  split; [|exact I].
  exists (BnRepDefs.mkEA (rho T_MK) (rho T_SA) (rho T_ND) (rho T_ES) (id_of T_MK) (id_of T_SA) (id_of T_ND) (id_of T_ES)).
  cbn [BnRepDefs.ea_MK BnRepDefs.ea_SA BnRepDefs.ea_ND BnRepDefs.ea_ES BnRepDefs.ea_pk BnRepDefs.ea_ps BnRepDefs.ea_pn BnRepDefs.ea_pe BnRepDefs.ea_ids].
  split; [exact ids4_nodup|].

  assert (HP8 : forall q t, In q QS -> q_ks q = kbs_ptr t -> 0 < rho t -> rho t < 2 ^ 63 -> ro_cells bgbsegs m' (q_addr rho q) [C8 (wz (rho t))]).
  { intros q t Hin Ek H0 H1. apply (q_cells rho S m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C8 (wz (rho t))])); [|exact H]. intros b' H'. exact (F2_ptr rho t [] [] b' H0 H1 (F2_nil rho) H'). }
  assert (HL8 : forall q z, In q QS -> q_ks q = kbs_Z 8 z -> 0 <= z < 2 ^ 64 -> ro_cells bgbsegs m' (q_addr rho q) [C8 (wz z)]).
  { intros q z Hin Ek Hz. apply (q_cells rho S m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C8 (wz z)])); [|exact H]. intros b' H'. exact (F2_lit8 rho z [] [] b' Hz (F2_nil rho) H'). }
  assert (HL4 : forall q z, In q QS -> q_ks q = kbs_Z 4 z -> 0 <= z < 2 ^ 64 -> ro_cells bgbsegs m' (q_addr rho q) [C4 (wz z)]).
  { intros q z Hin Ek Hz. apply (q_cells rho S m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C4 (wz z)])); [|exact H]. intros b' H'. exact (F2_lit4 rho z [] [] b' Hz (F2_nil rho) H'). }
  assert (HL1 : forall q z, In q QS -> q_ks q = kbs_Z 1 z -> 0 <= z -> ro_cells bgbsegs m' (q_addr rho q) [C1 (Z_to_bv 8 z)]).
  { intros q z Hin Ek Hz. apply (q_cells rho S m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C1 (Z_to_bv 8 z)])); [|exact H]. intros b' H'. exact (F2_lit1 rho z [] [] b' Hz (F2_nil rho) H'). }
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
      split; [exact (HP8 Q_tsd T_MK ltac:(qin) eq_refl P8 ltac:(lia))|].
      split.
      { pose proof (HP8 Q_mk T_SA ltac:(qin) eq_refl P9 ltac:(lia)) as X. unfold q_addr in X. cbn [q_lo q_tag q_off Q_mk Z.eqb] in X. exact X. }
      split.
      { destruct (q_sound rho S m' Q_sa HR (fin_q Q_sa ltac:(qin))) as (rg & bs & _ & HFs & Hb & _).
        unfold q_addr in Hb. cbn [q_lo q_tag q_off Q_sa Z.eqb] in Hb. rewrite Z.add_0_r in Hb.
        unfold Q_sa in HFs. cbn [q_ks] in HFs.
        destruct (Forall2_app_split _ _ _ _ HFs) as (b1 & r1 & -> & F1 & HF1).
        destruct (Forall2_app_split _ _ _ _ HF1) as (pad & r2 & -> & F2 & HF2).
        exists pad. split; [cbn [cells_wf cell_wf]; split; [exact I|]; split; [symmetry; exact (Forall2_length F2)|]; cbn; tauto|].
        cbn [cells_bytes cbytes]. rewrite (bs_lit4 rho 1 b1 ltac:(lia) F1) in Hb.
        assert (E2 : r2 = cells_bytes [C8 (wz 0); C8 (wz 1); C8 (wz (rho T_ND))]).
        { eapply (F2_lit8 rho 0); [lia | | exact HF2]. intros b3 H3.
          eapply (F2_lit8 rho 1); [lia | | exact H3]. intros b4 H4.
          eapply (F2_tail rho _ b4 (fun b => b = cells_bytes [C8 (wz (rho T_ND))])); [|exact H4]. intros b' H'.
          exact (F2_ptr rho T_ND [] [] b' P10 ltac:(lia) (F2_nil rho) H'). }
        rewrite E2 in Hb. exact Hb. }
      split.
      { pose proof (HP8 Q_nd T_ES ltac:(qin) eq_refl PE ltac:(lia)) as X. unfold q_addr in X. cbn [q_lo q_tag q_off Q_nd Z.eqb] in X. rewrite Z.add_0_r in X. exact X. }
      pose proof (q_rw_cells rho S m' Q_es [CB 904 ES_CLEARED] HR (fin_q Q_es ltac:(qin)) eq_refl ltac:(cbn; tauto) eq_refl) as X.
      cbn [q_tag q_off Q_es] in X. rewrite Z.add_0_r in X. apply X. intros bs H. rewrite (F2_bytes rho _ bs H). reflexivity. }

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

Section Close.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.

Hypothesis LIVE_POS : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> 0 < n.

Lemma frel_of_AF : frame_release_x RT.
Proof. exact (af_frame_release RT AF). Qed.

Theorem init_cps_A : init_cps RT (LIBA RT).
Proof. exact (init_cps_hx RT AF RTC LIVE_POS frel_of_AF (LIBA RT) (LIBA_final_A RT)). Qed.

End Close.

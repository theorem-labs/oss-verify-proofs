(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_st4 Z_tr_st1 Z_tr_st2 Z_tr_st3 Z_tr_st5 Z_tr_st6 Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma st_step_keep : forall f X t mc n prevlen nextlen count mx mn,
  1 <= mn -> n <= mc -> count + 1 < mx -> nextlen = Len X t (n + 1) ->
  send_tree_loop (S f) X t mc n prevlen nextlen count mx mn = send_tree_loop f X t mc (n + 1) prevlen (Len X t (n + 1)) (count + 1) mx mn.
Proof.
  intros f X t mc n prevlen nextlen count mx mn Hmn Hn Hc E. rewrite send_loop_S by exact Hmn. cbv zeta.
  rewrite (proj2 (Z.leb_le _ _) Hn), (proj2 (Z.ltb_lt _ _) Hc), (proj2 (Z.eqb_eq _ _) E). reflexivity.
Qed.
Lemma st_step_emit : forall f X t mc n prevlen nextlen count mx mn,
  1 <= mn -> n <= mc -> (mx <= count + 1 \/ nextlen <> Len X t (n + 1)) ->
  send_tree_loop (S f) X t mc n prevlen nextlen count mx mn
  = send_tree_loop f (sbs_run X (st_calls X mn nextlen prevlen (count + 1))) t mc (n + 1) nextlen (Len X t (n + 1)) 0
      (fst (tree_counts nextlen (Len X t (n + 1)))) (snd (tree_counts nextlen (Len X t (n + 1)))).
Proof.
  intros f X t mc n prevlen nextlen count mx mn Hmn Hn Hc. rewrite send_loop_S by exact Hmn. cbv zeta.
  rewrite (proj2 (Z.leb_le _ _) Hn).
  replace ((count + 1 <? mx) && (nextlen =? Len X t (n + 1))) with false.
  2:{ symmetry. apply andb_false_iff. destruct Hc as [Hc|Hc]; [left; apply Z.ltb_ge; exact Hc| right; apply Z.eqb_neq; exact Hc]. }
  destruct (tree_counts nextlen (Len X t (n + 1))); reflexivity.
Qed.
Lemma st_ok_keep : forall P f X t mc n prevlen nextlen count mx mn,
  n <= mc -> count + 1 < mx -> nextlen = Len X t (n + 1) ->
  send_tree_ok P (S f) X t mc n prevlen nextlen count mx mn -> send_tree_ok P f X t mc (n + 1) prevlen (Len X t (n + 1)) (count + 1) mx mn.
Proof.
  intros P f X t mc n prevlen nextlen count mx mn Hn Hc E H. cbn [send_tree_ok] in H. cbv zeta in H.
  rewrite (proj2 (Z.leb_le _ _) Hn), (proj2 (Z.ltb_lt _ _) Hc), (proj2 (Z.eqb_eq _ _) E) in H. exact H.
Qed.
Lemma st_ok_emit : forall P f X t mc n prevlen nextlen count mx mn,
  n <= mc -> (mx <= count + 1 \/ nextlen <> Len X t (n + 1)) ->
  send_tree_ok P (S f) X t mc n prevlen nextlen count mx mn ->
  sbs_ok P X (st_calls X mn nextlen prevlen (count + 1))
  /\ send_tree_ok P f (sbs_run X (st_calls X mn nextlen prevlen (count + 1))) t mc (n + 1) nextlen (Len X t (n + 1)) 0
       (fst (tree_counts nextlen (Len X t (n + 1)))) (snd (tree_counts nextlen (Len X t (n + 1)))).
Proof.
  intros P f X t mc n prevlen nextlen count mx mn Hn Hc H. cbn [send_tree_ok] in H. cbv zeta in H.
  rewrite (proj2 (Z.leb_le _ _) Hn) in H.
  replace ((count + 1 <? mx) && (nextlen =? Len X t (n + 1))) with false in H.
  2:{ symmetry. apply andb_false_iff. destruct Hc as [Hc|Hc]; [left; apply Z.ltb_ge; exact Hc| right; apply Z.eqb_neq; exact Hc]. }
  destruct (tree_counts nextlen (Len X t (n + 1))); exact H.
Qed.
Lemma tree_counts_0 : forall c, tree_counts c 0 = (138, 3).
Proof. reflexivity. Qed.
Lemma tree_counts_nz : forall c n, n <> 0 -> tree_counts c n = (if c =? n then 6 else 7, if c =? n then 3 else 4).
Proof. intros c n H. unfold tree_counts. rewrite (proj2 (Z.eqb_neq _ _) H). destruct (c =? n); reflexivity. Qed.
Lemma blc_flat : forall s PB PD BB BV c, blc (upd4 s PB PD BB BV) c = (arr_get (ds_bl_tree_fc s) c, arr_get (ds_bl_tree_dl s) c).
Proof. intros. unfold blc, Code, Len. rewrite upd4_tree_fc, upd4_tree_dl. reflexivity. Qed.
Lemma sbF_PD_nonneg : forall PD BV l, 0 <= PD -> 0 <= sbF_PD PD BV l.
Proof. intros PD BV l H. pose proof (sbF_PD_range PD BV l H). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ust_trip_post (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 nextlen' : Z) (f : nat) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x8 x9 x18 x19 wbb PB' PD' BB' BV' prevlen' count' mx' mn' pcx m',
    ms' = MS (ustR L T mc n1 nextlen' (wz prevlen') x8 x9 x18 x19 (wz prevlen') (wz count') (wz count') (wz mx') (wz mn') sp gp tp)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = send_tree_loop f (upd4 s PB' PD' BB' BV') t mc n1 prevlen' nextlen' count' mx' mn'
    /\ send_tree_ok 65536 f (upd4 s PB' PD' BB' BV') t mc n1 prevlen' nextlen' count' mx' mn'
    /\ 0 <= BV' <= 16 /\ 0 <= PD' /\ 0 <= count' < mx' /\ (mx' = 138 \/ mx' = 6 \/ mx' = 7) /\ (mn' = 3 \/ mn' = 4)
    /\ -1 <= prevlen' <= 15 /\ (mn' = 4 \/ prevlen' = nextlen' \/ nextlen' = 0)
    /\ ((pcx = ST_BODY /\ n1 <= mc) \/ (pcx = ST_EXIT /\ n1 = mc + 1)).

(* [comment removed for export] *)
Lemma st_latch : forall (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 nextlen' : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen' count' mx' mn' : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x24 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  R = send_tree_loop f (upd4 s PB PD BB BV) t mc n1 prevlen' nextlen' count' mx' mn' ->
  send_tree_ok 65536 f (upd4 s PB PD BB BV) t mc n1 prevlen' nextlen' count' mx' mn' ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count' < mx' -> (mx' = 138 \/ mx' = 6 \/ mx' = 7) -> (mn' = 3 \/ mn' = 4) -> -1 <= prevlen' <= 15 ->
  (mn' = 4 \/ prevlen' = nextlen' \/ nextlen' = 0) ->
  0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  evt usegs (ust_trip_post L s t T mc n1 nextlen' f R sp gp tp F fc m0)
      (MS (ustR L T mc n1 nextlen' x1 x8 x9 x18 x19 (wz prevlen') x24 (wz count') (wz mx') (wz mn') sp gp tp) F (wz ST_LATCH) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI MU WM ER OK RBV RPD Rc Rmx Rmn Rpl INV Rn Rmc. unfold ustR, ST_LATCH.
  zs2. zs2. zstep. br_cases K.
  - apply evt_done. unfold ust_trip_post, ustR. exists x8, x9, x18, x19, wbb, PB, PD, BB, BV, prevlen', count', mx', mn'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact EMH|]. split; [exact HBB|].
    split; [exact ER|]. split; [exact OK|]. split; [exact RBV|]. split; [exact RPD|]. split; [exact Rc|].
    split; [exact Rmx|]. split; [exact Rmn|]. split; [exact Rpl|]. split; [exact INV|]. right. split; [reflexivity| lia].
  - apply evt_done. unfold ust_trip_post, ustR. exists x8, x9, x18, x19, wbb, PB, PD, BB, BV, prevlen', count', mx', mn'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact EMH|]. split; [exact HBB|].
    split; [exact ER|]. split; [exact OK|]. split; [exact RBV|]. split; [exact RPD|]. split; [exact Rc|].
    split; [exact Rmx|]. split; [exact Rmn|]. split; [exact Rpl|]. split; [exact INV|]. left. split; [reflexivity| lia].
Qed.

Lemma st_tail : forall (L : dlay) (s : deflate_state) (t : tree_id) (T mc n1 curlen nextlen' : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV pcx : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x24 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  R = send_tree_loop f (upd4 s PB PD BB BV) t mc n1 curlen nextlen' 0 (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  send_tree_ok 65536 f (upd4 s PB PD BB BV) t mc n1 curlen nextlen' 0 (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= curlen <= 15 -> 0 <= nextlen' < 65536 -> 0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  ((pcx = ST_TAIL /\ nextlen' <> 0) \/ (pcx = ST_T138 /\ nextlen' = 0)) ->
  evt usegs (ust_trip_post L s t T mc n1 nextlen' f R sp gp tp F fc m0)
      (MS (ustR L T mc n1 nextlen' x1 x8 x9 x18 x19 (wz curlen) x24 (wz 0) x26 x27 sp gp tp) F (wz pcx) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI MU WM ER OK RBV RPD Rcl Rnl Rn Rmc [[-> NZ]|[-> ZE]]; unfold ustR, ST_TAIL, ST_T138.
  - rewrite tree_counts_nz in ER, OK by exact NZ. cbn [fst snd] in ER, OK.
    do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn.
    eapply (st_latch L s t T mc n1 nextlen' f R m0 PB PD BB BV curlen 0 (if curlen =? nextlen' then 6 else 7) (if curlen =? nextlen' then 3 else 4) wbb);
      try eassumption; try lia; destruct (Z.eqb_spec curlen nextlen'); auto; lia.
  - subst nextlen'. rewrite tree_counts_0 in ER, OK. cbn [fst snd] in ER, OK.
    do 3 zs2.
    eapply (st_latch L s t T mc n1 0 f R m0 PB PD BB BV curlen 0 138 3 wbb); try eassumption; try lia; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2 :=
  match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _, HP : (_ /\ _) \/ (_ /\ _) |- evt _ _ (MS _ _ (wz ?pcx) _ _ ?mm _) =>
    eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv pcx wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | | exact HP] end.

Lemma st_emit : forall (L : dlay) (s : deflate_state) (t : tree_id) (bfc bdl : arr) (T mc n1 : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen curlen nextlen' count mx mn : Z) (wbb : word)
    (x8 x9 x18 x19 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bfc i < 32768) ->
  0 <= curlen <= 15 -> 0 <= nextlen' < 65536 -> 0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < 138 -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (mn = 4 \/ prevlen = curlen \/ curlen = 0) ->
  R = send_tree_loop f (sbs_run (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1))) t mc n1 curlen nextlen' 0
        (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1)) ->
  send_tree_ok 65536 f (sbs_run (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1))) t mc n1 curlen nextlen' 0
        (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  evt usegs (ust_trip_post L s t T mc n1 nextlen' f R sp gp tp F fc m0)
      (MS (ustR L T mc n1 nextlen' (wz prevlen) x8 x9 x18 x19 (wz curlen) (wz count) (wz (count + 1)) (wz mx) (wz mn) sp gp tp) F (wz 0x1e700) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY MU WM RDB Ebfc Ebdl RBf Rcl Rnl Rn Rmc RBV RPD Rc Rmn Rpl INV ER OK1 OK2.
  assert (RDBm : ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39) by (eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]).
  pose proof LAY as LAY'. lay_open LAY'.
  unfold ustR. zstep. br_cases K1.
  - (* [comment removed for export] *)
    zstep. br_cases_s K2.
    + (* [comment removed for export] *)
      zstep. br_cases K5.
      * (* [comment removed for export] *)
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 18, arr_get bdl 18); (count - 10, 7)]).
        { unfold st_calls, REPZ_11_138. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq curlen 0)) by lia.
          rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [negb]. rewrite blc_flat, <- Ebfc, <- Ebdl. replace (count + 1 - 11) with (count - 10) by lia. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        call (st_repz138 L s bfc bdl T mc n1 nextlen' curlen count (arr_get bfc 18) (arr_get bdl 18) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
      * (* [comment removed for export] *)
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 17, arr_get bdl 17); (count - 2, 3)]).
        { unfold st_calls, REPZ_3_10. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq curlen 0)) by lia.
          rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [negb]. rewrite blc_flat, <- Ebfc, <- Ebdl. replace (count + 1 - 3) with (count - 2) by lia. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        call (st_repz10 L s bfc bdl T mc n1 nextlen' curlen count (arr_get bfc 17) (arr_get bdl 17) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
    + (* [comment removed for export] *)
      zstep. br_cases_s K4.
      * (* [comment removed for export] *)
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1)
                      = [(arr_get bfc curlen, arr_get bdl curlen); (arr_get bfc 16, arr_get bdl 16); (count - 3, 2)]).
        { unfold st_calls, REP_3_6. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq curlen 0)) by lia.
          rewrite (proj2 (Z.eqb_neq curlen prevlen)) by lia. cbn [negb app]. rewrite !blc_flat, <- Ebfc, <- Ebdl. replace (count + 1 - 1 - 3) with (count - 3) by lia. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        apply sbs_ok_cons_flat in OK1. destruct OK1 as (Rl1 & ROOM1 & OK1).
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl2 & _ & _).
       
        call (st_siteB L s bfc bdl T mc n1 nextlen' curlen (arr_get bfc curlen) (arr_get bdl curlen) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. } 1:{ lia. }
        1:{ apply RBf. lia. } 1:{ exact Rl1. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM1. }
        pose proof (sbF_BV_range BV (arr_get bdl curlen) RBV Rl1) as RBV1. pose proof (sbF_PD_range PD BV (arr_get bdl curlen) RPD) as RPD1.
        match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          call (st_rep36 L s bfc bdl T mc n1 nextlen' curlen count (arr_get bfc 16) (arr_get bdl 16) pb pd bb bv wb);
          [reflexivity| reflexivity| exact H| exact HB| eassumption| exact LAY
          | eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]
          | apply RBf; lia| exact RBV1| lia| lia| exact Rnl| exact OK1|] end.
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
      * (* [comment removed for export] *)
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 16, arr_get bdl 16); (count + 1 - 3, 2)]).
        { unfold st_calls, REP_3_6. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq curlen 0)) by lia.
          rewrite (proj2 (Z.eqb_eq curlen prevlen)) by lia. cbn [negb app]. rewrite !blc_flat, <- Ebfc, <- Ebdl. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        zs2. zstep. br_true.
        call (st_rep36 L s bfc bdl T mc n1 nextlen' curlen (count + 1) (arr_get bfc 16) (arr_get bdl 16) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
  - (* [comment removed for export] *)
    assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = repeat (arr_get bfc curlen, arr_get bdl curlen) (S (Z.to_nat count))).
    { unfold st_calls. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite blc_flat, <- Ebfc, <- Ebdl. f_equal. lia. }
    rewrite ESC in ER, OK1, OK2. clear ESC.
    pose proof EMH as EMo. open_EM EMo.
    ustep ST_TRAP. ustep ST_TRAP. zs2. shl_norm. zs2. ustep ST_TRAP. zs2. clear GA GD Gpend LPB LNP.
    reg_as (count + 1) (Z.of_nat (S (Z.to_nat count))).
    call (st_rep (Z.to_nat count) L s bfc bdl T mc n1 nextlen' curlen (arr_get bfc curlen) (arr_get bdl curlen)
                 (sbs_run (upd4 s PB PD BB BV) (repeat (arr_get bfc curlen, arr_get bdl curlen) (S (Z.to_nat count)))) m PB PD BB BV wbb).
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ exact RDBm. } 1:{ lia. } 1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact OK1. } 1:{ reflexivity. }
    match goal with E : sbs_run _ _ = upd4 _ _ _ _ _ |- _ => rewrite E in ER, OK2 end.
    unfold ustR. zs2. zstep. br_cases K3.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv ST_T138 wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | |] end;
        try assumption; try lia.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv ST_TAIL wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | |] end;
        try assumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma st_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (tfc tdl bfc bdl : arr) (T N mc n : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen nextlen count mx mn : Z) (wbb : word)
    (x8 x9 x18 x19 x23 x25 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 T tfc tdl N -> tdl = tree_dl s t -> 0 < T -> T + 4 * N < 2^62 -> mc + 1 < N -> N <= 573 ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bfc i < 32768) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get tdl i <= 15) -> (forall i, 0 <= i < N -> 0 <= arr_get tdl i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get tdl n ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (mn = 4 \/ prevlen = nextlen \/ nextlen = 0) ->
  R = send_tree_loop (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  send_tree_ok 65536 (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  evt usegs (ust_trip_post L s t T mc (n + 1) (arr_get tdl (n + 1)) f R sp gp tp F fc m0)
      (MS (ustR L T mc n nextlen (wz prevlen) x8 x9 x18 x19 x23 (wz count) x25 (wz mx) (wz mn) sp gp tp) F (wz ST_BODY) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HBB MI LAY MU WM RDT Etdl RT1 RT2 RmcN RN RDB Ebfc Ebdl RBf RTl RTn Rn Enl RBV RPD Rc Rmx Rmn Rpl INV ER OK.
  assert (HL : forall i, Len (upd4 s PB PD BB BV) t i = arr_get tdl i) by (intros i; unfold Len; rewrite upd4_tree_dl, <- Etdl; reflexivity).
  pose proof (RTl n Rn) as Rcl. rewrite <- Enl in Rcl.
  pose proof (RTn (n + 1) ltac:(lia)) as Rnl'.
  destruct (RDT m MU WM MI (n + 1) ltac:(lia)) as [_ RDl].
  assert (Rmn1 : 1 <= mn) by lia.
  pose proof LAY as LAY'. lay_open LAY'.
  unfold ustR, ST_BODY.
  do 4 ustep ST_TRAP. ustep ST_TRAP. shl_norm. do 7 ustep ST_TRAP. at_pc 0x1e6f0.
  reg_as ((n + 1) * 4 + T + 2) (T + 4 * (n + 1) + 2).
  zs2. rewrite (zx16_small (arr_get tdl (n + 1))) by lia. zs2.
  zstep. br_cases K1.
  - (* [comment removed for export] *)
    rewrite st_step_emit in ER by (try lia; left; lia). apply st_ok_emit in OK; [|lia| left; lia]. destruct OK as [OK1 OK2]. rewrite HL in ER, OK2.
    eapply (st_emit L s t bfc bdl T mc (n + 1) f R m0 PB PD BB BV prevlen nextlen (arr_get tdl (n + 1)) count mx mn wbb); try eassumption; lia.
  - zstep. br_cases_s K2.
    + (* [comment removed for export] *)
      rewrite st_step_keep in ER by (try lia; rewrite HL; exact K2). apply st_ok_keep in OK; [|lia|lia| rewrite HL; exact K2]. rewrite HL in ER, OK.
      zs2.
      eapply (st_latch L s t T mc (n + 1) (arr_get tdl (n + 1)) f R m0 PB PD BB BV prevlen (count + 1) mx mn wbb); try eassumption; lia.
    + rewrite st_step_emit in ER by (try lia; right; rewrite HL; exact K2). apply st_ok_emit in OK; [|lia| right; rewrite HL; exact K2]. destruct OK as [OK1 OK2]. rewrite HL in ER, OK2.
      eapply (st_emit L s t bfc bdl T mc (n + 1) f R m0 PB PD BB BV prevlen nextlen (arr_get tdl (n + 1)) count mx mn wbb); try eassumption; lia.
Qed.

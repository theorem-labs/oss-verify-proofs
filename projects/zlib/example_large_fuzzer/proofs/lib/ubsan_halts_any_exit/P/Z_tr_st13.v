(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_scan1 Z_tr_st1 Z_tr_st2 Z_tr_st3 Z_tr_st5 Z_tr_st6 Z_tr_st11 Z_tr_st12.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma blc_flat : forall s PB PD BB BV c, blc (upd4 s PB PD BB BV) c = (arr_get (ds_bl_tree_fc s) c, arr_get (ds_bl_tree_dl s) c).
Proof. intros. unfold blc, Code, Len. rewrite upd4_tree_fc, upd4_tree_dl. reflexivity. Qed.

Lemma sbF_PD_nonneg : forall PD BV l, 0 <= PD -> 0 <= sbF_PD PD BV l.
Proof. intros PD BV l H. pose proof (sbF_PD_range PD BV l H). lia. Qed.

Ltac st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2 :=
  match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _, HP : (_ /\ _) \/ (_ /\ _) |- evt _ _ (MS _ _ (wz ?pcx) _ _ ?mm _) =>
    eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv pcx wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | | exact HP] end.

Lemma st_emit : forall (L : dlay) (s : deflate_state) (t : tree_id) (bfc bdl : arr) (T mc n1 : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen curlen nextlen' count mx mn : Z) (wbb : word)
    (ra sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bfc i < 65536) ->
  0 <= curlen <= 15 -> 0 <= nextlen' < 65536 -> 0 <= n1 <= mc + 1 -> mc + 1 < 2^31 ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < 138 -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  R = send_tree_loop f (sbs_run (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1))) t mc n1 curlen nextlen' 0
        (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1)) ->
  send_tree_ok 65536 f (sbs_run (upd4 s PB PD BB BV) (st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1))) t mc n1 curlen nextlen' 0
        (fst (tree_counts curlen nextlen')) (snd (tree_counts curlen nextlen')) ->
  evt psegs (st_trip_post L s t T mc n1 nextlen' f R ra sp gp tp s9 s10 s11 F fc m0)
      (MS (stR L T (mc + 1) n1 nextlen' ra sp gp tp (wz curlen) (wz count) (wz (count + 1)) (wz mx) (wz mn) (wz prevlen) s6 s7 s8 s9 s10 s11) F (wz 0x1cac0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY MU WM RDB Ebfc Ebdl RBf Rcl Rnl Rn Rmc RBV RPD Rc Rmn Rpl ER OK1 OK2.
  assert (RDBm : ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39) by (eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]).
  unfold stR. zstep. br_cases K1.
  -
    pose proof EMH as EMo. open_EM EMo. zs2. clear GA Gpend LPB LNP.
    zstep. br_cases_s K2.
    +
      zs2. clear GD. zs2. zstep. br_cases K5.
      *
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 18, arr_get bdl 18); (count + 1 - 11, 7)]).
        { unfold st_calls, REPZ_11_138. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq curlen 0)) by lia.
          rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [negb]. rewrite blc_flat, <- Ebfc, <- Ebdl. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        call (st_repz138 L s bfc bdl T (mc + 1) n1 nextlen' curlen count (arr_get bfc 18) (arr_get bdl 18) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
      *
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 17, arr_get bdl 17); (count + 1 - 3, 3)]).
        { unfold st_calls, REPZ_3_10. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq curlen 0)) by lia.
          rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [negb]. rewrite blc_flat, <- Ebfc, <- Ebdl. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        call (st_repz10 L s bfc bdl T (mc + 1) n1 nextlen' curlen count (arr_get bfc 17) (arr_get bdl 17) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
    +
      clear GD. zstep. br_cases_s K4.
      *
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1)
                      = [(arr_get bfc curlen, arr_get bdl curlen); (arr_get bfc 16, arr_get bdl 16); (count - 3, 2)]).
        { unfold st_calls, REP_3_6. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq curlen 0)) by lia.
          rewrite (proj2 (Z.eqb_neq curlen prevlen)) by lia. cbn [negb app]. rewrite !blc_flat, <- Ebfc, <- Ebdl. repeat f_equal. lia. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        apply sbs_ok_cons_flat in OK1. destruct OK1 as (Rl1 & ROOM1 & OK1).
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl2 & _ & _).
        call (st_siteB L s bfc bdl T (mc + 1) n1 nextlen' curlen (arr_get bfc curlen) (arr_get bdl curlen) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. } 1:{ lia. }
        1:{ apply RBf. lia. } 1:{ exact Rl1. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM1. }
        pose proof (sbF_BV_range BV (arr_get bdl curlen) RBV Rl1) as RBV1. pose proof (sbF_PD_range PD BV (arr_get bdl curlen) RPD) as RPD1.
        match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          call (st_rep36 L s bfc bdl T (mc + 1) n1 nextlen' curlen count (arr_get bfc 16) (arr_get bdl 16) pb pd bb bv wb);
          [reflexivity| reflexivity| exact H| exact HB| eassumption| exact LAY
          | eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]
          | apply RBf; lia| exact RBV1| lia| lia| exact Rnl| exact OK1|] end.
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
      *
        assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = [(arr_get bfc 16, arr_get bdl 16); (count + 1 - 3, 2)]).
        { unfold st_calls, REP_3_6. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq curlen 0)) by lia.
          rewrite (proj2 (Z.eqb_eq curlen prevlen)) by lia. cbn [negb app]. rewrite !blc_flat, <- Ebfc, <- Ebdl. reflexivity. }
        rewrite ESC in ER, OK1, OK2. clear ESC. rewrite !sbs_run_cons_flat in ER, OK2. cbn [sbs_run] in ER, OK2.
        pose proof OK1 as OKc. apply sbs_ok_cons_flat in OKc. destruct OKc as (Rl1 & _ & _).
        zs2. zs2.
        call (st_rep36 L s bfc bdl T (mc + 1) n1 nextlen' curlen (count + 1) (arr_get bfc 16) (arr_get bdl 16) PB PD BB BV wbb).
        1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDBm. }
        1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact Rnl. } 1:{ exact OK1. }
        st_fin L s t T mc n1 curlen nextlen' f R m0 MU WM ER OK2; try assumption; try lia.
        { repeat (apply sbF_BV_range; [|first [assumption| lia]]). exact RBV. }
        { repeat apply sbF_PD_nonneg. exact RPD. }
  -
    assert (ESC : st_calls (upd4 s PB PD BB BV) mn curlen prevlen (count + 1) = repeat (arr_get bfc curlen, arr_get bdl curlen) (S (Z.to_nat count))).
    { unfold st_calls. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite blc_flat, <- Ebfc, <- Ebdl. f_equal. lia. }
    rewrite ESC in ER, OK1, OK2. clear ESC.
    pose proof EMH as EMo. open_EM EMo. zs2. clear GA GD Gpend LPB LNP.
    zs2. shl_norm. zs2. zs2. reg_as (count + 1) (Z.of_nat (S (Z.to_nat count))).
    call (st_rep (Z.to_nat count) L s bfc bdl T (mc + 1) n1 nextlen' curlen (arr_get bfc curlen) (arr_get bdl curlen)
                 (sbs_run (upd4 s PB PD BB BV) (repeat (arr_get bfc curlen, arr_get bdl curlen) (S (Z.to_nat count)))) m PB PD BB BV wbb).
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ exact RDBm. } 1:{ lia. } 1:{ apply RBf. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ lia. } 1:{ exact OK1. } 1:{ reflexivity. }
    match goal with E : sbs_run _ _ = upd4 _ _ _ _ _ |- _ => rewrite E in ER, OK2 end.
    unfold stR. zs2. zstep. br_cases_s K3.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv 0x1cf38 wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | |] end;
        try assumption; try lia.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wb (wz ?bv), HB : bv_unsigned ?wb mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (st_tail L s t T mc n1 curlen nextlen' f R m0 pb pd bb bv 0x1cb64 wb); [exact H| exact HB| eassumption| exact MU| exact WM| exact ER| exact OK2| | | | | | |] end;
        try assumption; try lia.
Qed.

Lemma st_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (tfc tdl bfc bdl : arr) (T N mc n : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV prevlen nextlen count mx mn : Z) (wbb : word)
    (ra sp gp tp s0 s2 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 T tfc tdl N -> tdl = tree_dl s t -> 0 < T -> T + 4 * N < 2^63 -> mc + 1 < N -> N <= 573 ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bfc i < 65536) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get tdl i <= 15) -> (forall i, 0 <= i < N -> 0 <= arr_get tdl i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get tdl n ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  R = send_tree_loop (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  send_tree_ok 65536 (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  evt psegs (st_trip_post L s t T mc (n + 1) (arr_get tdl (n + 1)) f R ra sp gp tp s9 s10 s11 F fc m0)
      (MS (stR L T (mc + 1) n nextlen ra sp gp tp s0 (wz count) s2 (wz mx) (wz mn) (wz prevlen) s6 s7 s8 s9 s10 s11) F (wz 0x1caa0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EMH HBB MI LAY MU WM RDT Etdl RT1 RT2 RmcN RN RDB Ebfc Ebdl RBf RTl RTn Rn Enl RBV RPD Rc Rmx Rmn Rpl ER OK.
  assert (HL : forall i, Len (upd4 s PB PD BB BV) t i = arr_get tdl i) by (intros i; unfold Len; rewrite upd4_tree_dl, <- Etdl; reflexivity).
  pose proof (RTl n Rn) as Rcl. rewrite <- Enl in Rcl.
  pose proof (RTn (n + 1) ltac:(lia)) as Rnl'.
  destruct (RDT m MU WM MI (n + 1) ltac:(lia)) as [_ RDl].
  replace (T + 4 * (n + 1) + 2) with (T + (n + 1) * 4 + 2) in RDl by lia.
  assert (Rmn1 : 1 <= mn) by lia.
  unfold stR.
  zs2. zs2. zs2. shl_norm. zs2. zs2. rewrite (zx16_small (arr_get tdl (n + 1))) by lia. zs2.
  zstep. br_cases K1.
  -
    rewrite st_step_emit in ER by (try lia; left; lia). apply st_ok_emit in OK; [|lia| left; lia]. destruct OK as [OK1 OK2]. rewrite HL in ER, OK2.
    eapply (st_emit L s t bfc bdl T mc (n + 1) f R m0 PB PD BB BV prevlen nextlen (arr_get tdl (n + 1)) count mx mn wbb); try eassumption; lia.
  - zstep. br_cases_s K2.
    +
      rewrite st_step_keep in ER by (try lia; rewrite HL; exact K2). apply st_ok_keep in OK; [|lia|lia| rewrite HL; exact K2]. rewrite HL in ER, OK.
      zs2.
      eapply (st_latch L s t T mc (n + 1) (arr_get tdl (n + 1)) f R m0 PB PD BB BV prevlen (count + 1) mx mn wbb); try eassumption; lia.
    + rewrite st_step_emit in ER by (try lia; right; rewrite HL; exact K2). apply st_ok_emit in OK; [|lia| right; rewrite HL; exact K2]. destruct OK as [OK1 OK2]. rewrite HL in ER, OK2.
      eapply (st_emit L s t bfc bdl T mc (n + 1) f R m0 PB PD BB BV prevlen nextlen (arr_get tdl (n + 1)) count mx mn wbb); try eassumption; lia.
Qed.

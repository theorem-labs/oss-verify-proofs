(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees FillWinModel ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition scR2 (L : dlay) (T mc : Z) (vt0 vt1 vt2 va1 va3 vt4 : Z) (t4x ra sp gp tp s0 s1 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) :=
  mkR ra sp gp tp (wz vt1) (wz vt2) t3 s0 s1 (wz (dl_As L + 2748)) (wz va1) (wz va3) (wz 4) (wz (T + 4 * (mc + 1) + 6)) (wz 9) a7 (wz vt0)
      s2 s3 s4 s5 (wz (dl_As L + 2506)) s7 s8 s9 s10 s11 (wz vt4) t4x t5 t6.

Definition sd_iter_post (L : dlay) (s1 : deflate_state) (t : tree_id) (T mc n : Z) (dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a7 t3 b' prevlen' count' mx' mn' pcx m',
    ms' = MS (scR2 L T mc mx' mn' count' (arr_get dlT (n + 1)) (T + 4 * (n + 1) + 6) prevlen' t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wbt L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39
    /\ (forall f, scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc n prevlen nextlen count mx mn
                  = scan_tree_loop f (set_bl_tree_fc s1 b') t mc (n + 1) prevlen' (arr_get dlT (n + 1)) count' mx' mn')
    /\ 0 <= count' < mx' /\ (mx' = 138 \/ mx' = 6 \/ mx' = 7) /\ (mn' = 3 \/ mn' = 4) /\ -1 <= prevlen' <= 15
    /\ ((pcx = 0x1b58c /\ n + 1 <= mc) \/ (pcx = 0x1b644 /\ n = mc)).

(* [comment removed for export] *)
Ltac sd_close T n MU WM ARR MOD :=
  let KE := fresh "KE" in
  zs2; zs2; zs2; zstep; reg_as (T + 4 * n + 10) (T + 4 * (n + 1) + 6); br_cases KE;
  (apply evt_done; unfold sd_iter_post, scR2; do 9 eexists;
   split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
   split; [exact ARR|]; split; [rewrite ?arr_len_set; assumption|]; split; [MOD|];
   split; [destr_ifs; lia|]; split; [destr_ifs; auto|]; split; [destr_ifs; auto|]; split; [lia|];
   first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]]).

(* [comment removed for export] *)
Lemma sd_upd : forall (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc n : Z) (dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get dlT n -> 0 <= nextlen <= 15 ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (count + 1 <? mx) && (nextlen =? arr_get dlT (n + 1)) = false ->
  evt psegs (sd_iter_post L s1 t T mc n dlT bdl b prevlen nextlen count mx mn t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (scR2 L T mc mx mn count (arr_get dlT (n + 1)) (T + 4 * n + 6) prevlen t4x ra sp gp tp s0 s1r (wz nextlen) s2 s3 s4 s5 s7 s8 s9 s10 s11 (wz (count + 1)) t5 t6)
          F (wz 0x1b5a0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LNB MI LAY RT1 RT2 RNT HL HDL Rn Enl Rcl Rc Rmx Rmn Rpl CND. unfold scR2.
  pose proof (munch_refl (Wbt L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. pose proof (avct_zlength b bdl 39 ltac:(lia)) as LCT.
  pose proof (HDL (n + 1) ltac:(lia)) as Rnl'.
  assert (CND' : mx <= count + 1 \/ nextlen <> arr_get dlT (n + 1)).
  { apply andb_false_iff in CND. destruct CND as [C|C]; [left; apply Z.ltb_ge in C; lia| right; apply Z.eqb_neq in C; exact C]. }
  zstep. br_cases K1.
  - (* [comment removed for export] *)
    zstep. br_cases_s K2.
    + (* [comment removed for export] *)
      zstep. br_cases K3.
      * (* [comment removed for export] *)
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 18) _ (wa (dl_As L + 2748 + 2 * (2 * 18))) ARR (avct_nth_fc b bdl 39 18 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 18 (wrap16 (arr_get b 18 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { zs2. do 3 zs2. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
      * (* [comment removed for export] *)
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 17) _ (wa (dl_As L + 2748 + 2 * (2 * 17))) ARR (avct_nth_fc b bdl 39 17 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 17 (wrap16 (arr_get b 17 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { zs2. do 3 zs2. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
    + (* [comment removed for export] *)
      zstep. br_cases_s K3.
      * (* [comment removed for export] *)
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * 16) _ (wa (dl_As L + 2748 + 2 * (2 * 16))) ARR (avct_nth_fc b bdl 39 16 ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 16 (wrap16 (arr_get b 16 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { do 3 zs2. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
      * (* [comment removed for export] *)
        pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * nextlen) _ (wa (dl_As L + 2748 + 2 * (2 * nextlen))) ARR (avct_nth_fc b bdl 39 nextlen ltac:(lia)) ltac:(lia) eq_refl) as RD.
        zs2. shl_norm. zs2. zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) nextlen (wrap16 (arr_get b nextlen + 1)) ltac:(apply le2_add_sx16).
        set (b1 := arr_set b nextlen (wrap16 (arr_get b nextlen + 1))) in *.
        lazymatch type of ARR with u8arr _ ?mc _ _ =>
          pose proof (u16arr_read psegs mc (dl_As L + 2748) (avct b1 bdl 39) (2 * 16) _ (wa (dl_As L + 2748 + 2 * (2 * 16))) ARR (avct_nth_fc b1 bdl 39 16 ltac:(lia)) ltac:(lia) eq_refl) as RD1 end.
        zs2. zs2.
        ct_store_fc ARR b1 bdl 39 (dl_As L + 2748) 16 (wrap16 (arr_get b1 16 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. subst b1. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
        { do 3 zs2. subst b1. sd_close T n MU WM ARR ltac:(sc_mod HL CND). }
  - (* [comment removed for export] *)
    pose proof (u16arr_read psegs m (dl_As L + 2748) (avct b bdl 39) (2 * nextlen) _ (wa (dl_As L + 2748 + 2 * (2 * nextlen))) ARR (avct_nth_fc b bdl 39 nextlen ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs2. shl_norm. zs2. zs2. zs2.
    ct_store_fc ARR b bdl 39 (dl_As L + 2748) nextlen (wrap16 (arr_get b nextlen + (count + 1))) ltac:(apply le2_add_sx16).
    zs2. zstep. br_cases K4.
    + do 3 zs2. sd_close T n MU WM ARR ltac:(sc_mod HL CND).
    + do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sd_close T n MU WM ARR ltac:(sc_mod HL CND).
Qed.

(* [comment removed for export] *)
Lemma sd_iter : forall (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc n : Z) (fcT dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wbt L) m T fcT dlT NT -> 0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  0 <= n <= mc -> nextlen = arr_get dlT n ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  evt psegs (sd_iter_post L s1 t T mc n dlT bdl b prevlen nextlen count mx mn t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (scR2 L T mc mx mn count nextlen (T + 4 * n + 6) prevlen t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b58c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR LNB MI LAY RDT RT1 RT2 RNT HL HDL HLEN Rn Enl Rc Rmx Rmn Rpl.
  pose proof (HLEN n ltac:(lia)) as Rcl. rewrite <- Enl in Rcl.
  pose proof (HDL (n + 1) ltac:(lia)) as Rnl'.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (n + 1) ltac:(lia)) as [_ RDl].
  replace (T + 4 * (n + 1) + 2) with (T + 4 * n + 6) in RDl by lia.
  destruct ((count + 1 <? mx) && (nextlen =? arr_get dlT (n + 1))) eqn:CND.
  - (* [comment removed for export] *)
    apply andb_true_iff in CND. destruct CND as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2.
    pose proof (munch_refl (Wbt L) m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
    unfold scR2. zs2. zs2. rewrite (zx16_small (arr_get dlT (n + 1))) by lia. zs2.
    zstep. br_false. zstep. br_true. zs2.
    sd_close T n MU WM ARR ltac:(intros f0; rewrite scan_loop_S; cbv zeta; rewrite !HL; decide_bools; reflexivity).
  - (* [comment removed for export] *)
    unfold scR2. zs2. zs2. rewrite (zx16_small (arr_get dlT (n + 1))) by lia. zs2.
    zstep. br_cases K1; [| zstep; br_cases_s K2; [exfalso; apply andb_false_iff in CND; destruct CND as [C|C]; [apply Z.ltb_ge in C; lia| apply Z.eqb_neq in C; lia]|]].
    all: eapply (sd_upd L s1 t T NT mc n dlT bdl b prevlen nextlen count mx mn); eassumption.
Qed.

(* [comment removed for export] *)
Definition sd_loop_post (L : dlay) (s1 : deflate_state) (T mc : Z) (bdl : arr) (R : deflate_state)
    (t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists vt0 vt1 vt2 va1 va3 vt4 a7 t3 b' m',
    ms' = MS (scR2 L T mc vt0 vt1 vt2 va1 va3 vt4 t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b644) fc None m' (seg_rom psegs)
    /\ munch (Wbt L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39 /\ R = set_bl_tree_fc s1 b'.

Lemma sd_loop : forall (f : nat) (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc : Z) (fcT dlT bdl : arr) (R : deflate_state) (m0 : mem)
    (n : Z) (b : arr) (prevlen nextlen count mx mn : Z)
    (t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wbt L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wbt L) m0 T fcT dlT NT -> 0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  0 <= n <= mc -> nextlen = arr_get dlT n ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  mc + 1 - n <= Z.of_nat (S f) ->
  R = scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc n prevlen nextlen count mx mn ->
  evt psegs (sd_loop_post L s1 T mc bdl R t4x ra sp gp tp s0 s1r s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m0)
      (MS (scR2 L T mc mx mn count nextlen (T + 4 * n + 6) prevlen t4x ra sp gp tp s0 s1r a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1b58c) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR LNB MI LAY MU WM RDT RT1 RT2 RNT HL HDL HLEN Rn Enl Rc Rmx Rmn Rpl FUEL ER.
  - call (sd_iter L s1 t T NT mc n fcT dlT bdl b prevlen nextlen count mx mn).
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RNT. } 1:{ exact HL. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Rn. } 1:{ exact Enl. }
    1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. }
    match goal with E : forall f : nat, scan_tree_loop (S f) _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite E in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    rewrite scan_loop_0 in ER.
    apply evt_done. unfold sd_loop_post. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER].
  - call (sd_iter L s1 t T NT mc n fcT dlT bdl b prevlen nextlen count mx mn).
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RNT. } 1:{ exact HL. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Rn. } 1:{ exact Enl. }
    1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. }
    match goal with E : forall f : nat, scan_tree_loop (S f) _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite E in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
    + eapply (IH L s1 t T NT mc fcT dlT bdl R m0 (n + 1)); try eassumption; try lia; reflexivity.
    + rewrite scan_loop_out in ER by lia.
      apply evt_done. unfold sd_loop_post. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER].
Qed.

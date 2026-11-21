(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees FillWinModel ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

Definition SC_TRAP : Z := 0x1e5fc.
Definition SC_BODY : Z := 0x1e4c0.
Definition SC_UPD : Z := 0x1e500.
Definition SC_EXIT : Z := 0x1e5d8.

(* [comment removed for export] *)
Lemma le2_add_sx16 : forall v c, le2 (wz (bv_unsigned (sx16 (wz v)) + c)) = le2 (wz (wrap16 (v + c))).
Proof.
  intros v c. apply le2_wz_mod. rewrite lo16_unsigned_wz, wrap16_mod, lo16_idem.
  rewrite <- Z.add_mod_idemp_l by lia. rewrite lo16_sx16, lo16_unsigned_wz. rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma counts_mx : forall c n, 0 <= c -> 0 <= n -> Z.lxor (Z.b2z (Z.lxor c n <? 1)) 7 = if c =? n then 6 else 7.
Proof.
  intros c n Hc Hn. destruct (Z.eqb_spec c n) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (Z.lxor c n <> 0) by (rewrite Z.lxor_eq_0_iff; exact NE).
    assert (0 <= Z.lxor c n) by (apply Z.lxor_nonneg; lia).
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma counts_mn : forall c n, 0 <= c -> 0 <= n -> 4 - Z.b2z (Z.lxor c n <? 1) = if c =? n then 3 else 4.
Proof.
  intros c n Hc Hn. destruct (Z.eqb_spec c n) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (Z.lxor c n <> 0) by (rewrite Z.lxor_eq_0_iff; exact NE).
    assert (0 <= Z.lxor c n) by (apply Z.lxor_nonneg; lia).
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Ltac decide_bools :=
  repeat match goal with
  | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
  | |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
  | |- context [?a =? ?b] => first [rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia]
  end; cbn [andb orb negb].
Ltac destr_ifs := repeat match goal with |- context [if ?c then _ else _] => destruct c end.
Ltac fix_mn := match goal with |- context [bv_swrap 32 (if ?c then 3 else 4)] =>
  replace (bv_swrap 32 (if c then 3 else 4)) with (if c then 3 else 4) by (destruct c; reflexivity) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usR (L : dlay) (T mc mx mn count prevlen n nextlen : Z) (ra sp gp tp x8 x21 x22 s7 s8 s9 s10 s11 : word) :=
  mkR ra sp gp tp (wz 9) (wz (-69)) (wz (-73)) x8 (wz mx) (wz 0) (wz T) (wz mc) (wz nextlen) (wz n) (wz (dl_As L + 2047)) (wz 39) (wz 4)
      (wz mn) (wz prevlen) (wz count) x21 x22 s7 s8 s9 s10 s11 (wz (-65)) (wz (dl_As L + 2748)) (wz (18446744073709551615 - (dl_As L + 2748))) (wz 38).

Notation Wbt L := [(dl_As L + 2748, dl_As L + 2904)] (only parsing).

Definition sc_iter_post (L : dlay) (s1 : deflate_state) (t : tree_id) (T mc n : Z) (dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x22 b' prevlen' count' mx' mn' pcx m',
    ms' = MS (usR L T mc mx' mn' count' prevlen' (n + 1) (arr_get dlT (n + 1)) ra sp gp tp (wz prevlen') (wz count') x22 s7 s8 s9 s10 s11)
             F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wbt L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39
    /\ (forall f, scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc n prevlen nextlen count mx mn
                  = scan_tree_loop f (set_bl_tree_fc s1 b') t mc (n + 1) prevlen' (arr_get dlT (n + 1)) count' mx' mn')
    /\ 0 <= count' < mx' /\ (mx' = 138 \/ mx' = 6 \/ mx' = 7) /\ (mn' = 3 \/ mn' = 4) /\ -1 <= prevlen' <= 15
    /\ ((pcx = SC_BODY /\ n + 1 <= mc) \/ (pcx = SC_EXIT /\ n = mc)).

(* [comment removed for export] *)
Ltac sc_close MU WM ARR MOD :=
  let KE := fresh "KE" in
  zs2; zs2; zstep; br_cases KE;
  (apply evt_done; unfold sc_iter_post, usR; do 8 eexists;
   split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
   split; [exact ARR|]; split; [rewrite ?arr_len_set; assumption|]; split; [MOD|];
   split; [destr_ifs; lia|]; split; [destr_ifs; auto|]; split; [destr_ifs; auto|]; split; [lia|];
   first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]]).
(* [comment removed for export] *)
Ltac sc_mod HL CND :=
  intros f0; rewrite scan_loop_S; cbv zeta; rewrite !HL; rewrite CND; unfold tree_counts, st_upd, REP_3_6, REPZ_3_10, REPZ_11_138; decide_bools; rewrite ?andb_false_r, ?andb_true_r; decide_bools; destr_ifs; reflexivity.
(* [comment removed for export] *)
Ltac bl_rd ARR b bdl k RD :=
  lazymatch type of ARR with u8arr _ ?mc (dl_As ?L + 2748) _ =>
    pose proof (u16arr_read usegs mc (dl_As L + 2748) (avct b bdl 39) (2 * k) _ (wa (dl_As L + 2748 + 2 * (2 * k))) ARR (avct_nth_fc b bdl 39 k ltac:(lia)) ltac:(lia) eq_refl) as RD end.

(* [comment removed for export] *)
Lemma sc_upd : forall (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc n : Z) (dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (ra sp gp tp x22 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv usegs m -> dlay_ok L ->
  0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get dlT n -> 0 <= nextlen <= 15 ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  (count + 1 <? mx) && (nextlen =? arr_get dlT (n + 1)) = false ->
  evt usegs (sc_iter_post L s1 t T mc n dlT bdl b prevlen nextlen count mx mn ra sp gp tp s7 s8 s9 s10 s11 F fc m)
      (MS (usR L T mc mx mn count prevlen (n + 1) (arr_get dlT (n + 1)) ra sp gp tp (wz nextlen) (wz (count + 1)) x22 s7 s8 s9 s10 s11)
          F (wz SC_UPD) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR LNB MI LAY RT1 RT2 RNT HL HDL Rn Enl Rcl Rc Rmx Rmn Rpl CND. unfold usR, SC_UPD.
  pose proof (munch_refl (Wbt L) m) as MU. pose proof (wmono_refl usegs m) as WM.
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
        ustep SC_TRAP. ustep SC_TRAP.
        bl_rd ARR b bdl 18 RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 18 (wrap16 (arr_get b 18 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sc_close MU WM ARR ltac:(sc_mod HL CND). }
        { do 3 zs2. sc_close MU WM ARR ltac:(sc_mod HL CND). }
      * (* [comment removed for export] *)
        ustep SC_TRAP. ustep SC_TRAP.
        bl_rd ARR b bdl 17 RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 17 (wrap16 (arr_get b 17 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sc_close MU WM ARR ltac:(sc_mod HL CND). }
        { zs2. do 3 zs2. sc_close MU WM ARR ltac:(sc_mod HL CND). }
    + (* [comment removed for export] *)
      zstep. br_cases_s K3.
      * (* [comment removed for export] *)
        ustep SC_TRAP. ustep SC_TRAP. zs2. shl_norm. ustep SC_TRAP. zs2. reg_as (dl_As L + 2748 + nextlen * 4) (dl_As L + 2748 + 2 * (2 * nextlen)).
        bl_rd ARR b bdl nextlen RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) nextlen (wrap16 (arr_get b nextlen + 1)) ltac:(apply le2_add_sx16).
        set (b1 := arr_set b nextlen (wrap16 (arr_get b nextlen + 1))) in *.
        ustep SC_TRAP.
        bl_rd ARR b1 bdl 16 RD1.
        zs2. zs2.
        ct_store_fc ARR b1 bdl 39 (dl_As L + 2748) 16 (wrap16 (arr_get b1 16 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 3 zs2. subst b1. sc_close MU WM ARR ltac:(sc_mod HL CND). }
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. subst b1. sc_close MU WM ARR ltac:(sc_mod HL CND). }
      * (* [comment removed for export] *)
        zstep. br_true. ustep SC_TRAP.
        bl_rd ARR b bdl 16 RD.
        zs2. zs2.
        ct_store_fc ARR b bdl 39 (dl_As L + 2748) 16 (wrap16 (arr_get b 16 + 1)) ltac:(apply le2_add_sx16).
        zs2. zstep. br_cases K4.
        { do 3 zs2. sc_close MU WM ARR ltac:(sc_mod HL CND). }
        { do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sc_close MU WM ARR ltac:(sc_mod HL CND). }
  - (* [comment removed for export] *)
    ustep SC_TRAP. ustep SC_TRAP. zs2. shl_norm. ustep SC_TRAP. zs2. reg_as (dl_As L + 2748 + nextlen * 4) (dl_As L + 2748 + 2 * (2 * nextlen)).
    bl_rd ARR b bdl nextlen RD.
    zs2. zs2.
    ct_store_fc ARR b bdl 39 (dl_As L + 2748) nextlen (wrap16 (arr_get b nextlen + (count + 1))) ltac:(apply le2_add_sx16).
    zs2. zstep. br_cases K4.
    + do 5 zs2. rewrite counts_mx, counts_mn by lia. fix_mn. sc_close MU WM ARR ltac:(sc_mod HL CND).
    + zs2. do 3 zs2. sc_close MU WM ARR ltac:(sc_mod HL CND).
Qed.

(* [comment removed for export] *)
Lemma sc_iter : forall (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc n : Z) (fcT dlT bdl : arr) (b : arr) (prevlen nextlen count mx mn : Z)
    (ra sp gp tp x8 x21 x22 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wbt L) m T fcT dlT NT -> 0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT -> NT < 2^31 ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  0 <= n <= mc -> nextlen = arr_get dlT n ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  evt usegs (sc_iter_post L s1 t T mc n dlT bdl b prevlen nextlen count mx mn ra sp gp tp s7 s8 s9 s10 s11 F fc m)
      (MS (usR L T mc mx mn count prevlen n nextlen ra sp gp tp x8 x21 x22 s7 s8 s9 s10 s11) F (wz SC_BODY) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR LNB MI LAY RDT RT1 RT2 RNT RN31 HL HDL HLEN Rn Enl Rc Rmx Rmn Rpl.
  pose proof (HLEN n ltac:(lia)) as Rcl. rewrite <- Enl in Rcl.
  pose proof (HDL (n + 1) ltac:(lia)) as Rnl'.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (n + 1) ltac:(lia)) as [_ RDl].
  pose proof (munch_refl (Wbt L) m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  unfold usR, SC_BODY.
  do 4 ustep SC_TRAP. ustep SC_TRAP. shl_norm. do 7 ustep SC_TRAP. at_pc 0x1e4f0.
  reg_as ((n + 1) * 4 + T + 2) (T + 4 * (n + 1) + 2).
  zs2. rewrite (zx16_small (arr_get dlT (n + 1))) by lia. zs2.
  destruct ((count + 1 <? mx) && (nextlen =? arr_get dlT (n + 1))) eqn:CND.
  - (* [comment removed for export] *)
    apply andb_true_iff in CND. destruct CND as [C1 C2]. apply Z.ltb_lt in C1. apply Z.eqb_eq in C2.
    zstep. br_false. zstep. br_true. zs2.
    sc_close MU WM ARR ltac:(intros f0; rewrite scan_loop_S; cbv zeta; rewrite !HL; decide_bools; reflexivity).
  - (* [comment removed for export] *)
    zstep. br_cases K1; [| zstep; br_cases_s K2; [exfalso; apply andb_false_iff in CND; destruct CND as [C|C]; [apply Z.ltb_ge in C; lia| apply Z.eqb_neq in C; lia]|]].
    all: eapply (sc_upd L s1 t T NT mc n dlT bdl b prevlen nextlen count mx mn); eassumption.
Qed.

(* [comment removed for export] *)
Definition sc_loop_post (L : dlay) (s1 : deflate_state) (T mc : Z) (bdl : arr) (R : deflate_state)
    (ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists mx mn count prevlen n nextlen x8 x21 x22 b' m',
    ms' = MS (usR L T mc mx mn count prevlen n nextlen ra sp gp tp x8 x21 x22 s7 s8 s9 s10 s11) F (wz SC_EXIT) fc None m' (seg_rom usegs)
    /\ munch (Wbt L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39 /\ R = set_bl_tree_fc s1 b'.

Lemma sc_loop : forall (f : nat) (L : dlay) (s1 : deflate_state) (t : tree_id) (T NT mc : Z) (fcT dlT bdl : arr) (R : deflate_state) (m0 : mem)
    (n : Z) (b : arr) (prevlen nextlen count mx mn : Z)
    (ra sp gp tp x8 x21 x22 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wbt L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wbt L) m0 T fcT dlT NT -> 0 < T -> T + 4 * NT < 2^62 -> mc + 1 < NT -> NT < 2^31 ->
  (forall i, Len s1 t i = arr_get dlT i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  0 <= n <= mc -> nextlen = arr_get dlT n ->
  0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  mc + 1 - n <= Z.of_nat (S f) ->
  R = scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc n prevlen nextlen count mx mn ->
  evt usegs (sc_loop_post L s1 T mc bdl R ra sp gp tp s7 s8 s9 s10 s11 F fc m0)
      (MS (usR L T mc mx mn count prevlen n nextlen ra sp gp tp x8 x21 x22 s7 s8 s9 s10 s11) F (wz SC_BODY) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR LNB MI LAY MU WM RDT RT1 RT2 RNT RN31 HL HDL HLEN Rn Enl Rc Rmx Rmn Rpl FUEL ER.
  - call (sc_iter L s1 t T NT mc n fcT dlT bdl b prevlen nextlen count mx mn).
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RNT. } 1:{ exact RN31. } 1:{ exact HL. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Rn. } 1:{ exact Enl. }
    1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. }
    match goal with E : forall f : nat, scan_tree_loop (S f) _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite E in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    rewrite scan_loop_0 in ER.
    apply evt_done. unfold sc_loop_post. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER].
  - call (sc_iter L s1 t T NT mc n fcT dlT bdl b prevlen nextlen count mx mn).
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RNT. } 1:{ exact RN31. } 1:{ exact HL. } 1:{ exact HDL. } 1:{ exact HLEN. } 1:{ exact Rn. } 1:{ exact Enl. }
    1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. }
    match goal with E : forall f : nat, scan_tree_loop (S f) _ _ _ _ _ _ _ _ _ = _ |- _ => rewrite E in ER end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
    + eapply (IH L s1 t T NT mc fcT dlT bdl R m0 (n + 1)); try eassumption; try lia; reflexivity.
    + rewrite scan_loop_out in ER by lia.
      apply evt_done. unfold sc_loop_post. do 11 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Z_SCAN_TREE : Z := 0x1e400.
Definition Z_SC_STACK : Z := 64.

Lemma guard_dl_facts : forall (dl : arr) N mc, arr_len dl = N -> 0 <= mc -> mc + 1 < N ->
  (forall i, 0 <= i < N -> 0 <= arr_get dl i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dl i <= 15) ->
  (forall i, 0 <= i < N -> 0 <= arr_get (arr_set dl (mc + 1) (wrap16 65535)) i < 65536)
  /\ (forall i, 0 <= i <= mc -> 0 <= arr_get (arr_set dl (mc + 1) (wrap16 65535)) i <= 15)
  /\ arr_get (arr_set dl (mc + 1) (wrap16 65535)) 0 = arr_get dl 0.
Proof.
  intros dl N mc LN H0 H1 HA HB.
  assert (G : forall i, arr_get (arr_set dl (mc + 1) (wrap16 65535)) i = if mc + 1 =? i then 65535 else arr_get dl i).
  { intros i. rewrite arr_get_set. unfold arr_inb. rewrite LN. destruct (Z.eqb_spec (mc + 1) i); cbn [andb]; [|reflexivity].
    rewrite (proj2 (Z.leb_le 0 (mc + 1))), (proj2 (Z.ltb_lt (mc + 1) N)) by lia. reflexivity. }
  split; [|split].
  - intros i Hi. rewrite G. destruct (mc + 1 =? i); [lia| apply HA; lia].
  - intros i Hi. rewrite G. destruct (Z.eqb_spec (mc + 1) i); [lia| apply HB; lia].
  - rewrite G. destruct (Z.eqb_spec (mc + 1) 0); [lia| reflexivity].
Qed.

Definition scan_tree_body_post (L : dlay) (T NT mc : Z) (fcT dlT bdl : arr) (s1 : deflate_state) (t : tree_id) (b : arr) (lo : Z)
    (ra sp gp tp s0 s1r s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 b' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (T, T + 4 * NT); (dl_As L + 2748, dl_As L + 2904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ u8arr usegs m' T (u16s (avct fcT (arr_set dlT (mc + 1) (wrap16 65535)) NT))
    /\ u8arr usegs m' (dl_As L + 2748) (u16s (avct b' bdl 39)) /\ arr_len b' = 39
    /\ scan_tree_loop (Z.to_nat (mc + 1)) (set_bl_tree_fc s1 b) t mc 0 (-1) (arr_get dlT 0) 0
         (if arr_get dlT 0 =? 0 then 138 else 7) (if arr_get dlT 0 =? 0 then 3 else 4) = set_bl_tree_fc s1 b'.

Lemma scan_tree_body : forall (L : dlay) (T NT mc : Z) (fcT dlT bdl : arr) (s1 : deflate_state) (t : tree_id) (b : arr) (lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct fcT dlT NT)) -> arr_len dlT = NT ->
  u8arr usegs m (dl_As L + 2748) (u16s (avct b bdl 39)) -> arr_len b = 39 ->
  mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_SC_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * NT <= dl_As L + 2748 ->
  0 <= mc -> mc + 1 < NT ->
  (forall i, Len s1 t i = arr_get (arr_set dlT (mc + 1) (wrap16 65535)) i) ->
  (forall i, 0 <= i < NT -> 0 <= arr_get dlT i < 65536) -> (forall i, 0 <= i <= mc -> 0 <= arr_get dlT i <= 15) ->
  a0 = wz (dl_As L) -> a1 = wz T -> a2 = wz mc ->
  evt usegs (scan_tree_body_post L T NT mc fcT dlT bdl s1 t b lo ra sp gp tp s0 s1r s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1r a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_SCAN_TREE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ART LNT ARR LNB MI LAY STK LO BEL AL4 RTlo RThi Rmc RmcN HL HDL HLEN -> -> ->. unfold Z_SCAN_TREE, Z_SC_STACK in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (T, T + 4 * NT); (dl_As L + 2748, dl_As L + 2904)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. below_open BEL. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  pose proof (avct_zlength fcT dlT NT ltac:(lia)) as LCT. pose proof (avct_zlength b bdl 39 ltac:(lia)) as LCB.
  destruct (guard_dl_facts dlT NT mc LNT Rmc RmcN HDL HLEN) as (HDL' & HLEN' & E0).
  pose proof (HDL 0 ltac:(lia)) as Rnl.
  carve_frame 64%nat STK.
  do 8 zstep. do 2 ustep SC_TRAP.
  pose proof (u16arr_read usegs _ T (avct fcT dlT NT) (2 * 0 + 1) _ (wa (T + 2 * (2 * 0 + 1))) ART (avct_nth_dl _ _ NT 0 ltac:(lia)) ltac:(lia) eq_refl) as RD.
  set (nl := arr_get dlT 0) in *.
  zs2. rewrite (zx16_small nl) by lia.
  set (dlT' := arr_set dlT (mc + 1) (wrap16 65535)) in *.
  destruct (Z.to_nat (mc + 1)) as [|f] eqn:Ef; [lia|].
  zstep. br_cases K0.
  - (* [comment removed for export] *)
    zs2.
    do 2 ustep SC_TRAP. ustep SC_TRAP. shl_norm. do 8 ustep SC_TRAP.
    ct_store_dl ART fcT dlT NT T (mc + 1) (wrap16 65535) ltac:(apply le2_wz_mod; vm_compute; reflexivity).
    zstep. br_false.
    do 4 zs2. zs2. al8 (dl_As L). do 6 zs2. zs2. zs2. reg_as (dl_As L + 2047 + 701) (dl_As L + 2748). zs2. rewrite zb_lxor_ones by lia. zs2. zs2.
    replace (0 <? nl) with false by (symmetry; apply Z.ltb_ge; lia). change (bv_swrap 32 (Z.b2z false + 3)) with 3.
    remember (scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc 0 (-1) nl 0 138 3) as R eqn:ER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mK _) =>
      pose proof (ct_readable_rw (Wbt L) mK T fcT dlT' NT NT ART ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; lia)) as RDT;
      call (sc_loop f L s1 t T NT mc fcT dlT' bdl R mK 0 b (-1) nl 0 138 3) end.
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RDT. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact HL. } 1:{ exact HDL'. } 1:{ exact HLEN'. } 1:{ lia. } 1:{ symmetry; exact E0. }
    1:{ lia. } 1:{ auto. } 1:{ auto. } 1:{ lia. } 1:{ lia. } 1:{ exact ER. }
    unfold usR. do 7 zstep. zstep. zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold scan_tree_body_post. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    split; [exact ART|]. split; [eassumption|]. split; [assumption|].
    fold nl. rewrite (proj2 (Z.eqb_eq nl 0) K0). rewrite Ef, <- ER. assumption.
  - (* [comment removed for export] *)
    zs2. zs2.
    do 2 ustep SC_TRAP. ustep SC_TRAP. shl_norm. do 8 ustep SC_TRAP.
    ct_store_dl ART fcT dlT NT T (mc + 1) (wrap16 65535) ltac:(apply le2_wz_mod; vm_compute; reflexivity).
    zstep. br_false.
    do 4 zs2. zs2. al8 (dl_As L). do 6 zs2. zs2. zs2. reg_as (dl_As L + 2047 + 701) (dl_As L + 2748). zs2. rewrite zb_lxor_ones by lia. zs2. zs2.
    replace (0 <? nl) with true by (symmetry; apply Z.ltb_lt; lia). change (bv_swrap 32 (Z.b2z true + 3)) with 4.
    remember (scan_tree_loop (S f) (set_bl_tree_fc s1 b) t mc 0 (-1) nl 0 7 4) as R eqn:ER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mK _) =>
      pose proof (ct_readable_rw (Wbt L) mK T fcT dlT' NT NT ART ltac:(lia) ltac:(lia) ltac:(cbn [disjoint_from]; lia)) as RDT;
      call (sc_loop f L s1 t T NT mc fcT dlT' bdl R mK 0 b (-1) nl 0 7 4) end.
    1:{ exact ARR. } 1:{ exact LNB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RDT. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact HL. } 1:{ exact HDL'. } 1:{ exact HLEN'. } 1:{ lia. } 1:{ symmetry; exact E0. }
    1:{ lia. } 1:{ auto. } 1:{ auto. } 1:{ lia. } 1:{ lia. } 1:{ exact ER. }
    unfold usR. do 7 zstep. zstep. zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold scan_tree_body_post. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    split; [exact ART|]. split; [eassumption|]. split; [assumption|].
    fold nl. rewrite (proj2 (Z.eqb_neq nl 0) K0). rewrite Ef, <- ER. assumption.
Qed.

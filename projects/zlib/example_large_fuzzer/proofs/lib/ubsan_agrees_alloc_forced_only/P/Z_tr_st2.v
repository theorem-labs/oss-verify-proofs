(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_st1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition st_rep_loop_post (L : dlay) (s : deflate_state) (T mc1 n nextlen curlen : Z) (R : deflate_state)
    (ra sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists s3 s5 s6 s7 s8 wbb PB' PD' BB' BV' m',
    ms' = MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) (wz (dl_As L + 2748 + curlen * 4)) (wz 0) s3 (wz BV') s5 s6 s7 s8 s9 s10 s11) F (wz 0x1cb5c) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV' /\ 0 <= BV' <= 16 /\ 0 <= PD'.

Lemma st_rep : forall (k : nat) (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc1 n nextlen curlen V l : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s3 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc curlen -> l = arr_get bdl curlen ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= curlen < 39 ->
  0 <= V < 65536 -> 0 <= BV <= 16 -> 0 <= PD -> Z.of_nat (S k) < 2^31 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (repeat (V, l) (S k)) ->
  R = sbs_run (upd4 s PB PD BB BV) (repeat (V, l) (S k)) ->
  evt psegs (st_rep_loop_post L s T mc1 n nextlen curlen R ra sp gp tp s9 s10 s11 F fc m0)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) (wz (dl_As L + 2748 + curlen * 4)) (wz (Z.of_nat (S k))) s3 (wz BV) s5 s6 s7 s8 s9 s10 s11) F (wz 0x1cb2c) fc None m (seg_rom psegs)).
Proof.
  induction k as [|k IH]; intros until m; intros EV El EMH HBB MI LAY MU WM RDB Rcl RV RBV RPD Rk HSB ER.
  all: cbn [repeat] in HSB, ER; apply sbs_ok_cons_flat in HSB; destruct HSB as (Rl & ROOM & HSB2); rewrite sbs_run_cons_flat in ER.
  - call (st_rep_iter L s bfc bdl T mc1 n nextlen curlen (Z.of_nat 1) V l PB PD BB BV wbb).
    1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ exact Rcl. } 1:{ exact RV. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. } 1:{ lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    cbn [repeat sbs_run] in ER. change (Z.of_nat 1 - 1) with 0.
    apply evt_done. unfold st_rep_loop_post. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER|]. split; [apply sbF_BV_range; assumption| pose proof (sbF_PD_range PD BV l RPD); lia].
  - call (st_rep_iter L s bfc bdl T mc1 n nextlen curlen (Z.of_nat (S (S k))) V l PB PD BB BV wbb).
    1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ exact Rcl. } 1:{ exact RV. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. } 1:{ lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    replace (Z.of_nat (S (S k)) - 1) with (Z.of_nat (S k)) by lia.
    eapply (IH L s bfc bdl T mc1 n nextlen curlen V l R m0); try eassumption; try lia.
    + apply sbF_BV_range; assumption.
    + pose proof (sbF_PD_range PD BV l RPD). lia.
Qed.

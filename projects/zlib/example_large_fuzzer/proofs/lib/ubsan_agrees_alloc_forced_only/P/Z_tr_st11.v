(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_st1 Z_tr_st4 Z_tr_st5 Z_tr_st7 Z_tr_st8 Z_tr_st9 Z_tr_st10.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma st_repz10 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc1 n nextlen curlen count V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s1 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 17 -> l = arr_get bdl 17 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 65536 -> 0 <= BV <= 16 -> 0 <= PD -> 0 <= count < 2^31 - 1 -> 0 <= nextlen < 65536 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) [(V, l); (count + 1 - 3, 3)] ->
  evt psegs (st_tail_post L s T mc1 n nextlen curlen
               (sbF_PB (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (count + 1 - 3) 3) (sbF_PD (sbF_PD PD BV l) (sbF_BV BV l) 3)
               (sbF_BB (sbF_BB BB BV V l) (sbF_BV BV l) (count + 1 - 3) 3) (sbF_BV (sbF_BV BV l) 3) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) s1 (wz (65535 + count)) (wz BV) s4 s5 (zx16 wbb) s7 s8 s9 s10 s11) F (wz 0x1cb98) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV RBV RPD Rcnt Rnl HSB.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2). apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _).
  pose proof (sbF_BV_range BV l RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l RPD) as RPD1.
  assert (EQV : (65535 + count - 1) mod 2^16 = (count + 1 - 3) mod 2^16)
    by (replace (65535 + count - 1) with (count + 65535 - 1) by lia; replace (count + 1 - 3) with (count - (1 + 1)) by lia; apply cnt_eqm).
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  call (st_c10 L s bfc bdl T mc1 n nextlen curlen count V l PB PD BB BV wbb).
  1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDB. } 1:{ exact RV. } 1:{ exact Rl. }
  1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. } 1:{ lia. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
  - eapply evt_mono; [eapply (st_x10_keep L s T mc1 n nextlen curlen (count + 1 - 3) (65535 + count - 1)); try eassumption; lia|].
    intros ms' (r1 & r4 & r5 & r6 & r7 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold st_tail_post. exists r1, r4, r5, r6, r7, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
  - eapply evt_mono; [eapply (st_x10_flush L s T mc1 n nextlen curlen (count + 1 - 3) (65535 + count - 1)); try eassumption; lia|].
    intros ms' (r1 & r4 & r5 & r6 & r7 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold st_tail_post. exists r1, r4, r5, r6, r7, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
Qed.

Lemma st_repz138 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc1 n nextlen curlen count V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s1 s4 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 18 -> l = arr_get bdl 18 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 65536 -> 0 <= BV <= 16 -> 0 <= PD -> 0 <= count < 2^31 - 1 -> 0 <= nextlen < 65536 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) [(V, l); (count + 1 - 11, 7)] ->
  evt psegs (st_tail_post L s T mc1 n nextlen curlen
               (sbF_PB (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (count + 1 - 11) 7) (sbF_PD (sbF_PD PD BV l) (sbF_BV BV l) 7)
               (sbF_BB (sbF_BB BB BV V l) (sbF_BV BV l) (count + 1 - 11) 7) (sbF_BV (sbF_BV BV l) 7) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) s1 (wz (65535 + count)) (wz BV) s4 s5 (zx16 wbb) s7 s8 s9 s10 s11) F (wz 0x1cca0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV RBV RPD Rcnt Rnl HSB.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2). apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _).
  pose proof (sbF_BV_range BV l RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l RPD) as RPD1.
  assert (EQV : (65535 + count - 9) mod 2^16 = (count + 1 - 11) mod 2^16)
    by (replace (65535 + count - 9) with (count + 65535 - 9) by lia; replace (count + 1 - 11) with (count - (9 + 1)) by lia; apply cnt_eqm).
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  call (st_c138 L s bfc bdl T mc1 n nextlen curlen count V l PB PD BB BV wbb).
  1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDB. } 1:{ exact RV. } 1:{ exact Rl. }
  1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. } 1:{ lia. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
  - eapply evt_mono; [eapply (st_x138_keep L s T mc1 n nextlen curlen (count + 1 - 11) (65535 + count - 9)); try eassumption; lia|].
    intros ms' (r1 & r4 & r5 & r6 & r7 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold st_tail_post. exists r1, r4, r5, r6, r7, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
  - eapply evt_mono; [eapply (st_x138_flush L s T mc1 n nextlen curlen (count + 1 - 11) (65535 + count - 9)); try eassumption; lia|].
    intros ms' (r1 & r4 & r5 & r6 & r7 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold st_tail_post. exists r1, r4, r5, r6, r7, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
Qed.

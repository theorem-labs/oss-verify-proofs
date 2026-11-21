(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_st1 Z_tr_st4 Z_tr_st5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition st_c36_post (L : dlay) (s : deflate_state) (T mc1 n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists w s5 s6 s7 wbb pcx m',
    ms' = MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) (wz (65535 + cnt - 2)) w (wz BV) (wz (bv_swrap 32 (Z.shiftl (65535 + cnt - 2) (BV mod 32)))) s5 s6 s7 s8 s9 s10 s11)
             F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD wbb (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1cdb4 /\ BV <= 14) \/ (pcx = 0x1cde8 /\ 15 <= BV)).

Ltac c36_fin MU WM GA GD Gpend LO side EXT :=
  apply evt_done; unfold st_c36_post, stR, sbF_PB, sbF_PD, sbF_BB, sbF_BV;
  rewrite ?(proj2 (Z.ltb_ge _ _)), ?(proj2 (Z.ltb_lt _ _)) by lia; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LO|]; side; (split; [reflexivity| EXT]).

Lemma st_c36 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc1 n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 16 -> l = arr_get bdl 16 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 65536 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) -> 0 <= cnt < 2^31 ->
  evt psegs (st_c36_post L s T mc1 n nextlen curlen cnt (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) (wz cnt) s2 (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1cd38) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV Rl RBV RPD ROOM Rcnt. unfold stR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI 16 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  clear EV El.
  zs2. rewrite (zx16_small l) by lia. zs2. rewrite (zx16_small V) by lia.
  zs2. zs2. zs2. zs2.
  sb_or w LO BB (rewrite lo16_sx16; exact HBB).
  zstep. br_cases K.
  - (* [comment removed for export] *)
    zs2. zs2. zs2. zs2. zs2. replace (65535 + cnt + -2) with (65535 + cnt - 2) by lia.
    zstep. br_cases K2.
    + c36_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(left) ltac:(lia).
    + c36_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(right) ltac:(lia).
  - (* [comment removed for export] *)
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. reg_as (l + BV + -16) (BV + l - 16).
    zs2. zs2. zs2. replace (65535 + cnt + -2) with (65535 + cnt - 2) by lia.
    zstep. br_cases K2.
    + c36_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(lia).
    + c36_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(lia).
Qed.

(* [comment removed for export] *)
Lemma st_rep36 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc1 n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (ra sp gp tp s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 16 -> l = arr_get bdl 16 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 65536 -> 0 <= BV <= 16 -> 0 <= PD -> 0 <= cnt < 2^31 -> 0 <= nextlen < 65536 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) [(V, l); (cnt - 3, 2)] ->
  evt psegs (st_tail_post L s T mc1 n nextlen curlen
               (sbF_PB (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 3) 2) (sbF_PD (sbF_PD PD BV l) (sbF_BV BV l) 2)
               (sbF_BB (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 3) 2) (sbF_BV (sbF_BV BV l) 2) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (stR L T mc1 n nextlen ra sp gp tp (wz curlen) (wz cnt) s2 (wz BV) s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1cd38) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV RBV RPD Rcnt Rnl HSB.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2). apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _).
  pose proof (sbF_BV_range BV l RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l RPD) as RPD1.
  assert (EQV : (65535 + cnt - 2) mod 2^16 = (cnt - 3) mod 2^16) by (replace (65535 + cnt - 2) with (cnt + 65535 - 2) by lia; apply cnt_eqm).
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  call (st_c36 L s bfc bdl T mc1 n nextlen curlen cnt V l PB PD BB BV wbb).
  1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDB. } 1:{ exact RV. } 1:{ exact Rl. }
  1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. } 1:{ exact Rcnt. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
  - eapply evt_mono; [eapply (st_x36_keep L s T mc1 n nextlen curlen (cnt - 3) (65535 + cnt - 2)); try eassumption; lia|].
    intros ms' (r1 & r4 & r5 & r6 & r7 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold st_tail_post. exists r1, r4, r5, r6, r7, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
  - eapply evt_mono; [eapply (st_x36_flush L s T mc1 n nextlen curlen (cnt - 3) (65535 + cnt - 2)); try eassumption; lia|].
    intros ms' (r1 & r4 & r5 & r6 & r7 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold st_tail_post. exists r1, r4, r5, r6, r7, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
Qed.

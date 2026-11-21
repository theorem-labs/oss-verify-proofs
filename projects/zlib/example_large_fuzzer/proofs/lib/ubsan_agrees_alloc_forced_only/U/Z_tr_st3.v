(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_st4 Z_tr_st1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land16_x : forall x, 0 <= x < 65536 -> Z.land (65535 + (x + 3) + -2) 65535 = x.
Proof.
  intros x Hx. change 65535 with (Z.ones 16) at 2. rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
  replace (65535 + (x + 3) + -2) with (x + 1 * 65536) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. exact Hx.
Qed.
Lemma cnt36_eqm : forall cnt, (65535 + cnt + -2) mod 2^16 = (cnt - 3) mod 2^16.
Proof. intros. replace (65535 + cnt + -2) with (cnt - 3 + 1 * 2^16) by lia. apply Z.mod_add. lia. Qed.

Definition ust_c36_post (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z)
    (x1 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists w x9 x18 x19 x27 pcx m',
    ms' = MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1ee54 /\ BV <= 14) \/ (pcx = 0x1ed78 /\ 15 <= BV)).

Ltac c36_fin MU WM GA GD Gpend DEC LO side EXT :=
  apply evt_done; unfold ust_c36_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; DEC; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|];
  split; [close_EM GA GD Gpend|]; split; [LO|]; side; (split; [reflexivity| EXT]).

Lemma st_c36 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 16 -> l = arr_get bdl 16 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 32768 -> 0 <= l <= 16 -> 0 <= BV <= 16 -> 0 <= PD -> (16 - l < BV -> PD + 2 <= 65536) ->
  evt usegs (ust_c36_post L s T mc n nextlen curlen cnt (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) x1 sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) (wz cnt) x25 x26 x27 sp gp tp) F (wz 0x1ec98) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV Rl RBV RPD ROOM. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI 16 ltac:(lia)) as [RDc RDl]. rewrite <- EV in RDc. rewrite <- El in RDl.
  clear EV El.
  ustep ST_TRAP.
  zs. rewrite (zx16_small l) by lia. zs2. zs. rewrite (zx16_small V) by lia.
  do 4 zs2. shl_g0. zs2. zs2. shl_g1.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    ustep ST_TRAP. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zstep. zs2. zs2. zstep.
    zstep. br_cases K2.
    + c36_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia) ltac:(exact LO) ltac:(right) ltac:(lia).
    + c36_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - l) BV)) by lia) ltac:(exact LO) ltac:(left) ltac:(lia).
  - (* [comment removed for export] *)
    ustep ST_TRAP. zs. zs. zs. zs. zs.
    sb_or w LO BB ltac:(rewrite lo16_sx16; exact HBB).
    zs. zs. zstep. zs.
    uwalk 0x1ed04 ST_TRAP. at_pc 0x1ed04.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1ed38 ST_TRAP. at_pc 0x1ed38.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1ed54 ST_TRAP. at_pc 0x1ed54.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zs2. zs2. zstep. ustep ST_TRAP. zs2.
    zstep. reg_as (l + BV + -16) (BV + l - 16).
    zstep. br_cases K2.
    + c36_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(lia).
    + c36_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - l) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(lia).
Qed.

(* [comment removed for export] *)
Ltac x_fin MU WM GA GD Gpend DEC LO :=
  apply evt_done; unfold ust_tail_post, ustR, sbF_PB, sbF_PD, sbF_BB, sbF_BV; DEC; do 11 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LO|];
  first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].

Lemma st_x36_keep : forall (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (x1 x9 x18 x19 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  0 <= BV <= 14 -> 0 <= PD -> 0 <= nextlen < 65536 -> 0 <= cnt < 2^31 ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV (cnt - 3) 2) (sbF_PD PD BV 2) (sbF_BB BB BV (cnt - 3) 2) (sbF_BV BV 2) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz 0x1ee54) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD Rnl Rcnt. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep ST_TRAP. zs2. zs2. zs2. zs2.
  sb_or w1 LO BB (exact HW). rewrite (nbv_eqm BB BV (cnt - 3) (65535 + cnt + -2) (cnt36_eqm cnt)) in LO.
  zstep. zs2. zstep. zs2.
  zstep. br_cases K.
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 2) BV)) by lia) ltac:(exact LO).
  - zstep. x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 2) BV)) by lia) ltac:(exact LO).
Qed.

(* [comment removed for export] *)
Lemma st_x36_flush : forall (L : dlay) (s : deflate_state) (T mc n nextlen curlen cnt : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (x1 x9 x18 x19 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  15 <= BV <= 16 -> 0 <= PD -> PD + 2 <= 65536 -> 0 <= nextlen < 65536 -> 3 <= cnt < 32768 ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen (sbF_PB PB PD BB BV (cnt - 3) 2) (sbF_PD PD BV 2) (sbF_BB BB BV (cnt - 3) 2) (sbF_BV BV 2) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 (wz BV) x9 x18 x19 (wz curlen) (wz cnt) (wz BV) w x27 sp gp tp) F (wz 0x1ed78) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EMH HW MI LAY RBV RPD ROOM Rnl Rcnt. unfold ustR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. open_EM EMH.
  ustep ST_TRAP. zs2. zs2. zs2. replace (65535 + cnt + -2) with (65535 + (cnt - 3 + 3) + -2) by lia. rewrite (land16_x (cnt - 3)) by lia.
  zs2. zs2. shl_g0. ustep ST_TRAP.
  zs. zs. zs. zs.
  sb_or w1 LO BB (exact HW).
  replace (65535 + (cnt - 3 + 3) + -2) with (65535 + cnt + -2) in LO by lia. rewrite (nbv_eqm BB BV (cnt - 3) (65535 + cnt + -2) (cnt36_eqm cnt)) in LO.
  zs. zs. zstep. zs.
  uwalk 0x1edcc ST_TRAP. at_pc 0x1edcc.
  pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV (cnt - 3)) 255)) ltac:(apply lo8_wrap8_land; exact LO).
  zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
  uwalk 0x1ee00 ST_TRAP. at_pc 0x1ee00.
  pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV (cnt - 3)) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV (cnt - 3))) 8)) ltac:(apply hi8_lo16; exact LO).
  uwalk 0x1ee1c ST_TRAP. at_pc 0x1ee1c.
  zs2. rewrite srlw_val16 by lia.
  pose proof (shiftr_wrap16_range (cnt - 3) (16 - BV) ltac:(lia)) as RSH.
  zs2. zstep. zstep. br_true. zstep. zs2. reg_as (BV + -14) (BV + 2 - 16).
  zstep. br_cases K.
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 2) BV)) by lia) ltac:(apply lo16_unsigned_wz).
  - x_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 2) BV)) by lia) ltac:(apply lo16_unsigned_wz).
Qed.

(* [comment removed for export] *)
Lemma st_rep36 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (T mc n nextlen curlen cnt V l : Z) (PB : arr) (PD BB BV : Z) (wbb : word)
    (x1 x8 x9 x18 x19 x25 x26 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bfc 16 -> l = arr_get bdl 16 ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= V < 32768 -> 0 <= BV <= 16 -> 0 <= PD -> 3 <= cnt < 32768 -> 0 <= nextlen < 65536 ->
  sbs_ok 65536 (upd4 s PB PD BB BV) [(V, l); (cnt - 3, 2)] ->
  evt usegs (ust_tail_post L s T mc n nextlen curlen
               (sbF_PB (sbF_PB PB PD BB BV V l) (sbF_PD PD BV l) (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 3) 2) (sbF_PD (sbF_PD PD BV l) (sbF_BV BV l) 2)
               (sbF_BB (sbF_BB BB BV V l) (sbF_BV BV l) (cnt - 3) 2) (sbF_BV (sbF_BV BV l) 2) sp gp tp F fc m)
      (MS (ustR L T mc n nextlen x1 x8 x9 x18 x19 (wz curlen) (wz cnt) x25 x26 x27 sp gp tp) F (wz 0x1ec98) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV El EMH HBB MI LAY RDB RV RBV RPD Rcnt Rnl HSB.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (Rl & ROOM & HSB2). apply sbs_ok_cons_flat in HSB2. destruct HSB2 as (_ & ROOM2 & _).
  pose proof (sbF_BV_range BV l RBV Rl) as RBV1. pose proof (sbF_PD_range PD BV l RPD) as RPD1.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  call (st_c36 L s bfc bdl T mc n nextlen curlen cnt V l PB PD BB BV wbb).
  1:{ exact EV. } 1:{ exact El. } 1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RDB. } 1:{ exact RV. } 1:{ exact Rl. }
  1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact ROOM. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end.
  - eapply evt_mono; [eapply (st_x36_keep L s T mc n nextlen curlen cnt); try eassumption; lia|].
    intros ms' (r1 & r8 & r9 & r18 & r19 & r24 & r26 & r27 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold ust_tail_post. exists r1, r8, r9, r18, r19, r24, r26, r27, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
  - eapply evt_mono; [eapply (st_x36_flush L s T mc n nextlen curlen cnt); try eassumption; lia|].
    intros ms' (r1 & r8 & r9 & r18 & r19 & r24 & r26 & r27 & wb & pcx & m' & E & MU' & WM' & MI' & EM' & HB' & X').
    unfold ust_tail_post. exists r1, r8, r9, r18, r19, r24, r26, r27, wb, pcx, m'.
    split; [exact E|]. split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption|]. split; [exact MI'|]. split; [exact EM'|]. split; [exact HB'| exact X'].
Qed.

(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1 Z_tr_cb3 Z_tr_bt1 Z_tr_bt2 Z_tr_bt10. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_tr_bt12. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_tr_bt13 Z_tr_bt14 Z_tr_bt16.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition eqm (a b : Z) : Prop := a mod 2 ^ 16 = b mod 2 ^ 16.
Lemma eqm_refl : forall a, eqm a a. Proof. intros. reflexivity. Qed.
Lemma eqm_add : forall a a' b b', eqm a a' -> eqm b b' -> eqm (a + b) (a' + b').
Proof. unfold eqm. intros a a' b b' H1 H2. rewrite Zplus_mod, H1, H2, <- Zplus_mod. reflexivity. Qed.
Lemma eqm_addc : forall a a' b b', eqm a b' -> eqm b a' -> eqm (a + b) (a' + b').
Proof. intros a a' b b' H1 H2. rewrite (Z.add_comm a' b'). apply eqm_add; assumption. Qed.
Lemma eqm_mul2 : forall a a', eqm a a' -> eqm (a * 2) (a' * 2 ^ 1).
Proof. unfold eqm. intros a a' H. change (2 ^ 1) with 2. rewrite Zmult_mod, H, <- Zmult_mod. reflexivity. Qed.
Lemma eqm_shl1 : forall a a', eqm a a' -> eqm (Z.shiftl a 1) (a' * 2 ^ 1).
Proof. intros a a' H. rewrite Z.shiftl_mul_pow2 by lia. unfold eqm. rewrite Zmult_mod, H, <- Zmult_mod. reflexivity. Qed.
Lemma eqm_mod64 : forall a a', eqm a a' -> eqm (a mod 18446744073709551616) a'.
Proof. unfold eqm. intros a a' H. rewrite lo16_mod64. exact H. Qed.
Lemma eqm_uwz : forall a a', eqm a a' -> eqm (bv_unsigned (wz a)) a'.
Proof. unfold eqm. intros a a' H. rewrite lo16_unsigned_wz. exact H. Qed.
Lemma eqm_sx16 : forall a a', eqm a a' -> eqm (bv_unsigned (sx16 (wz a))) a'.
Proof. unfold eqm. intros a a' H. rewrite lo16_sx16, lo16_unsigned_wz. exact H. Qed.
Lemma eqm_zx16 : forall a a', eqm a a' -> eqm (bv_unsigned (zx16 (wz a))) a'.
Proof. unfold eqm. intros a a' H. rewrite lo16_zx16, lo16_unsigned_wz. exact H. Qed.

Ltac eqm_go := first
  [ apply eqm_refl
  | apply eqm_mod64; eqm_go
  | apply eqm_shl1; eqm_go
  | apply eqm_mul2; eqm_go
  | apply eqm_sx16; eqm_go
  | apply eqm_zx16; eqm_go
  | apply eqm_uwz; eqm_go
  | apply eqm_add; eqm_go
  | apply eqm_addc; eqm_go ].

Lemma NC_get : forall blc k, (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) -> 1 <= k <= 15 ->
  arr_get (NC blc) k = wrap16 (gcode (arr_get blc) (Z.to_nat k)).
Proof. intros blc k RB Hk. destruct (NC_spec blc RB) as [_ E]. rewrite <- (E (Z.to_nat k)) by lia. f_equal. lia. Qed.

Lemma le2_eqm_NC : forall blc (w : word) k, (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) -> 1 <= k <= 15 ->
  eqm (bv_unsigned w) (gcode (arr_get blc) (Z.to_nat k)) -> le2 w = le2 (wz (arr_get (NC blc) k)).
Proof.
  intros blc w k RB Hk E. apply le2_wz_mod. rewrite (NC_get blc k RB Hk). rewrite wrap16_mod. rewrite lo16_idem. exact E.
Qed.

(* [comment removed for export] *)
Lemma le2_of_bytes : forall j : list byte, length j = 2%nat -> exists w0 : word, le2 w0 = j.
Proof.
  intros [|x [|y [|z l]]] H; try discriminate.
  exists (wz (bv_unsigned x + 256 * bv_unsigned y)).
  pose proof (bv_unsigned_in_range 8 x) as Rx. pose proof (bv_unsigned_in_range 8 y) as Ry. unfold bv_modulus in Rx, Ry. cbn in Rx, Ry.
  unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z_to_le_bytes].
  rewrite Z.mod_small by (cbn; lia).
  f_equal; [| f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus.
  - change (2 ^ Z.of_N 8) with 256. Z.div_mod_to_equations. lia.
  - change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. Z.div_mod_to_equations. lia.
Qed.

Lemma zseq_16 : zseq 16 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ncl_intro : forall m A j0 blc (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : word),
  rw_cells psegs m A [CB 2 j0; C2 r1; C2 r2; C2 r3; C2 r4; C2 r5; C2 r6; C2 r7; C2 r8; C2 r9; C2 r10; C2 r11; C2 r12; C2 r13; C2 r14; C2 r15] ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) ->
  eqm (bv_unsigned r1) (gcode (arr_get blc) 1) -> eqm (bv_unsigned r2) (gcode (arr_get blc) 2) -> eqm (bv_unsigned r3) (gcode (arr_get blc) 3) ->
  eqm (bv_unsigned r4) (gcode (arr_get blc) 4) -> eqm (bv_unsigned r5) (gcode (arr_get blc) 5) -> eqm (bv_unsigned r6) (gcode (arr_get blc) 6) ->
  eqm (bv_unsigned r7) (gcode (arr_get blc) 7) -> eqm (bv_unsigned r8) (gcode (arr_get blc) 8) -> eqm (bv_unsigned r9) (gcode (arr_get blc) 9) ->
  eqm (bv_unsigned r10) (gcode (arr_get blc) 10) -> eqm (bv_unsigned r11) (gcode (arr_get blc) 11) -> eqm (bv_unsigned r12) (gcode (arr_get blc) 12) ->
  eqm (bv_unsigned r13) (gcode (arr_get blc) 13) -> eqm (bv_unsigned r14) (gcode (arr_get blc) 14) -> eqm (bv_unsigned r15) (gcode (arr_get blc) 15) ->
  exists w0, u8arr psegs m A (u16s (ncl w0 (NC blc))).
Proof.
  intros until r15. intros FR RB E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15.
  destruct FR as [[WF BY] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as [Lj _].
  destruct (le2_of_bytes j0 Lj) as [w0 Ew]. exists w0.
  cbn [cells_bytes cbytes app] in BY. cbn [cells_size csize Nat.add] in WR.
  unfold ncl, av16. rewrite zseq_16. cbn [map upd u16s].
  rewrite Ew.
  rewrite <- (le2_eqm_NC blc r1 1 RB ltac:(lia) E1), <- (le2_eqm_NC blc r2 2 RB ltac:(lia) E2), <- (le2_eqm_NC blc r3 3 RB ltac:(lia) E3),
          <- (le2_eqm_NC blc r4 4 RB ltac:(lia) E4), <- (le2_eqm_NC blc r5 5 RB ltac:(lia) E5), <- (le2_eqm_NC blc r6 6 RB ltac:(lia) E6),
          <- (le2_eqm_NC blc r7 7 RB ltac:(lia) E7), <- (le2_eqm_NC blc r8 8 RB ltac:(lia) E8), <- (le2_eqm_NC blc r9 9 RB ltac:(lia) E9),
          <- (le2_eqm_NC blc r10 10 RB ltac:(lia) E10), <- (le2_eqm_NC blc r11 11 RB ltac:(lia) E11), <- (le2_eqm_NC blc r12 12 RB ltac:(lia) E12),
          <- (le2_eqm_NC blc r13 13 RB ltac:(lia) E13), <- (le2_eqm_NC blc r14 14 RB ltac:(lia) E14), <- (le2_eqm_NC blc r15 15 RB ltac:(lia) E15).
  split.
  - destruct j0 as [|x [|y [|z l]]]; try discriminate. cbn [app] in BY |- *. exact BY.
  - rewrite !length_app, !length_le2, Lj. cbn [Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact WR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ncR (L : dlay) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition nc_phase_post (L : dlay) (BC : arr) (ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 w0 m',
    ms' = MS (ncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c464) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp + 8, bv_unsigned sp + 40)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (bv_unsigned sp + 8) (u16s (ncl w0 (NC BC))).

Ltac eqmk := cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm_go.

Lemma nc_phase : forall (L : dlay) (BC : arr) (junk : list byte)
    (a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> rw_cells psegs m (bv_unsigned sp + 8) [CB 32 junk] -> mem_inv psegs m -> dlay_ok L ->
  arr_len BC = 16 -> (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 40 < 2^63 ->
  evt psegs (nc_phase_post L BC ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (ncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c378) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros BLC FR MI LAY LBC RBC SEP RSP.
  pose proof (munch_refl [(bv_unsigned sp + 8, bv_unsigned sp + 40)] m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
  pose proof (RBC 0 ltac:(lia)) as R0. pose proof (RBC 1 ltac:(lia)) as R1. pose proof (RBC 2 ltac:(lia)) as R2. pose proof (RBC 3 ltac:(lia)) as R3.
  pose proof (RBC 4 ltac:(lia)) as R4. pose proof (RBC 5 ltac:(lia)) as R5. pose proof (RBC 6 ltac:(lia)) as R6. pose proof (RBC 7 ltac:(lia)) as R7.
  pose proof (RBC 8 ltac:(lia)) as R8. pose proof (RBC 9 ltac:(lia)) as R9. pose proof (RBC 10 ltac:(lia)) as R10. pose proof (RBC 11 ltac:(lia)) as R11.
  pose proof (RBC 12 ltac:(lia)) as R12. pose proof (RBC 13 ltac:(lia)) as R13. pose proof (RBC 14 ltac:(lia)) as R14.
  apply u16arr_to_cells in BLC. unfold av16 in BLC. rewrite zseq_16 in BLC. cbn [map c2s] in BLC.
  unfold ncR.
  (* [comment removed for export] *)
  zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. rewrite !zx16_small by lia.
  (* [comment removed for export] *)
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  zs2.
  (* [comment removed for export] *)
  zs2. zs2. zs2. zs2. rewrite !zx16_small by lia.
  (* [comment removed for export] *)
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  zs2.
  (* [comment removed for export] *)
  zs2. zs2. zs2.
  (* [comment removed for export] *)
  zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zs2. zs2. shl_norm. zs2. zs2. shl_norm. zs2. zs2. shl_norm.
  zstep. zstep. zstep.
  match goal with FRf : rw_cells psegs ?mm (bv_unsigned sp + 8) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (ncl_intro _ _ _ BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRf RBC ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk)
                ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk)) as [w0 NCA] end.
  apply evt_done. unfold nc_phase_post, ncR. do 8 eexists. exists w0. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact NCA].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gcs_post (s : deflate_state) (t : tree_id) (L : dlay) (T N mc : Z) (DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp t2 s1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s3x FC' junk' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) s1 a0 a1 a2 a3 a4 a5 a6 a7 (wz T) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1c4d8) fc None m' (seg_rom psegs)
    /\ munch (Wgc T N sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL N)) /\ rw_cells psegs m' (bv_unsigned sp + 8) [CB 32 junk']
    /\ R = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = N.

Lemma ncl_cb32 : forall m A w0 nc, u8arr psegs m A (u16s (ncl w0 nc)) -> rw_cells psegs m A [CB 32 (u16s (ncl w0 nc))].
Proof. intros m A w0 nc H. apply rw_cells_of_u8arr in H. rewrite u16s_length, ncl_length in H. exact H. Qed.

Lemma gcs_phase : forall (s : deflate_state) (t : tree_id) (L : dlay) (T N mc : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (junk : list byte)
    (a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> rw_cells psegs m (bv_unsigned sp + 8) [CB 32 junk] ->
  mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N ->
  arr_len BC = 16 -> (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 40 < 2^63 ->
  -1 <= mc < N -> (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) ->
  R = gen_codes (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t mc ->
  evt psegs (gcs_post s t L T N mc DL HP HL HM DP BC OL SL MC R ra sp gp tp t2 s1 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (ncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s1 (wz T) (wz mc) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c378) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR BLC FR MI LAY RT1 RT2 RN LFC LDL LBC RBC SEP RSP Rmc RDL ER.
  pose proof LAY as LAY0. lay_open LAY0.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold gen_codes in ER. rewrite bt_bl_count in ER. change (gen_codes_loop1 16 BC (arr_make (MAX_BITS + 1) 0) 0 1) with (NC BC) in ER.
  pose proof (munch_refl (Wgc T N sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  call (nc_phase L BC junk).
  1:{ exact BLC. } 1:{ exact FR. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact RBC. } 1:{ exact SEP. } 1:{ exact RSP. }
  unfold ncR. zstep. br_cases K.
  - (* [comment removed for export] *)
    replace (mc + 1) with 0 in ER by lia. cbn [Z.to_nat] in ER. rewrite loop2_0 in ER.
    apply evt_done. unfold gcs_post. do 11 eexists. exists FC. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [apply ncl_cb32; eassumption|]. split; [exact ER| exact LFC].
  - zs2. zs2. zs2. zs2. zs2. zs2. zs2.
    rewrite (Z.mod_small (mc + 1) 4294967296) by lia.
    destruct (NC_spec BC RBC) as [LNC _].
    lazymatch goal with HN : u8arr psegs ?mm (bv_unsigned sp + 8) (u16s (ncl ?w0 (NC BC))) |- evt _ _ (MS _ _ _ _ _ ?mm' _) =>
      call (gc_loop (Z.to_nat (mc + 1)) s t T N 0 mc w0 FC DL (NC BC) HP HL HM DP BC OL SL MC R mm') end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ lia. } 1:{ lia. } 1:{ exact RSP. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LNC. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RDL. } 1:{ intros k Hk. apply NC_range; [exact RBC| exact Hk]. }
    1:{ exact ER. }
    unfold gcR. apply evt_done. unfold gcs_post. do 11 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct ?fc' DL N)) |- _ => exists fc' end. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [apply ncl_cb32; eassumption|]. split; assumption.
Qed.

(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_tr_bt13 Z_tr_bt14 Z_tr_bt16 Z_tr_bt17.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_bt_mid Z_tr_bt16.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.

(* [comment removed for export] *)

Lemma uncl_intro : forall m A j0 blc (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : word),
  rw_cells usegs m A [CB 2 j0; C2 r1; C2 r2; C2 r3; C2 r4; C2 r5; C2 r6; C2 r7; C2 r8; C2 r9; C2 r10; C2 r11; C2 r12; C2 r13; C2 r14; C2 r15] ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get blc i < 65536) ->
  eqm (bv_unsigned r1) (gcode (arr_get blc) 1) -> eqm (bv_unsigned r2) (gcode (arr_get blc) 2) -> eqm (bv_unsigned r3) (gcode (arr_get blc) 3) ->
  eqm (bv_unsigned r4) (gcode (arr_get blc) 4) -> eqm (bv_unsigned r5) (gcode (arr_get blc) 5) -> eqm (bv_unsigned r6) (gcode (arr_get blc) 6) ->
  eqm (bv_unsigned r7) (gcode (arr_get blc) 7) -> eqm (bv_unsigned r8) (gcode (arr_get blc) 8) -> eqm (bv_unsigned r9) (gcode (arr_get blc) 9) ->
  eqm (bv_unsigned r10) (gcode (arr_get blc) 10) -> eqm (bv_unsigned r11) (gcode (arr_get blc) 11) -> eqm (bv_unsigned r12) (gcode (arr_get blc) 12) ->
  eqm (bv_unsigned r13) (gcode (arr_get blc) 13) -> eqm (bv_unsigned r14) (gcode (arr_get blc) 14) -> eqm (bv_unsigned r15) (gcode (arr_get blc) 15) ->
  exists w0, u8arr usegs m A (u16s (ncl w0 (NC blc))).
Proof.
  intros until r15. intros FR RB E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15.
  destruct FR as [[WF BY] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as [Lj _].
  destruct (le2_of_bytes j0 Lj) as [w0 Ew]. exists w0.
  cbn [cells_bytes cbytes app] in BY. cbn [cells_size csize Nat.add] in WR.
  unfold ncl, OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P.Z_dview.av16. rewrite Z_tr_bt17.zseq_16. cbn [map upd u16s].
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
Definition uncR (L : dlay) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 s10 s11 t3 t4 t5 t6.

Definition unc_phase_post (L : dlay) (BC : arr) (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 w0 m',
    ms' = MS (uncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1d6b4) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp + 72, bv_unsigned sp + 104)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (bv_unsigned sp + 72) (u16s (ncl w0 (NC BC))).

Ltac eqmk := cbn [gcode Z.of_nat Pos.of_succ_nat Pos.succ]; eqm_go.
Lemma uzseq_16 : zseq 16 = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]. Proof. reflexivity. Qed.

Lemma unc_phase : forall (L : dlay) (BC : arr) (junk : list byte)
    (a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> rw_cells usegs m (bv_unsigned sp + 72) [CB 32 junk] -> mem_inv usegs m -> dlay_ok L ->
  arr_len BC = 16 -> (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  evt usegs (unc_phase_post L BC ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (uncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1d5c8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros BLC FR MI LAY LBC RBC SEP RSP.
  pose proof (munch_refl [(bv_unsigned sp + 72, bv_unsigned sp + 104)] m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  pose proof (RBC 0 ltac:(lia)) as R0. pose proof (RBC 1 ltac:(lia)) as R1. pose proof (RBC 2 ltac:(lia)) as R2. pose proof (RBC 3 ltac:(lia)) as R3.
  pose proof (RBC 4 ltac:(lia)) as R4. pose proof (RBC 5 ltac:(lia)) as R5. pose proof (RBC 6 ltac:(lia)) as R6. pose proof (RBC 7 ltac:(lia)) as R7.
  pose proof (RBC 8 ltac:(lia)) as R8. pose proof (RBC 9 ltac:(lia)) as R9. pose proof (RBC 10 ltac:(lia)) as R10. pose proof (RBC 11 ltac:(lia)) as R11.
  pose proof (RBC 12 ltac:(lia)) as R12. pose proof (RBC 13 ltac:(lia)) as R13. pose proof (RBC 14 ltac:(lia)) as R14.
  apply u16arr_to_cells in BLC. unfold av16 in BLC. rewrite uzseq_16 in BLC. cbn [map c2s] in BLC.
  unfold uncR.
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
  match goal with FRf : rw_cells usegs ?mm (bv_unsigned sp + 72) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (uncl_intro _ _ _ BC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRf RBC ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk)
                ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk) ltac:(eqmk)) as [w0 NCA] end.
  apply evt_done. unfold unc_phase_post, uncR. do 8 eexists. exists w0. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact NCA].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ugcs_post (s : deflate_state) (t : tree_id) (L : dlay) (T N mc : Z) (DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 FC' junk' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz T) s7 (wz (dl_As L + 2976)) s9 s10 s11 t3 t4 t5 t6)
             F (wz 0x1d744) fc None m' (seg_rom usegs)
    /\ munch (uWgc T N sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL N)) /\ rw_cells usegs m' (bv_unsigned sp + 72) [CB 32 junk']
    /\ R = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = N.

Lemma uncl_cb32 : forall m A w0 nc, u8arr usegs m A (u16s (ncl w0 nc)) -> rw_cells usegs m A [CB 32 (u16s (ncl w0 nc))].
Proof. intros m A w0 nc H. apply rw_cells_of_u8arr in H. rewrite u16s_length, ncl_length in H. exact H. Qed.

Lemma ugcs_phase : forall (s : deflate_state) (t : tree_id) (L : dlay) (T N mc : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (junk : list byte)
    (a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> rw_cells usegs m (bv_unsigned sp + 72) [CB 32 junk] ->
  rw_cells usegs m (bv_unsigned sp + 8) [C8 (wz mc)] -> rw_cells usegs m (bv_unsigned sp + 24) [C8 (wz 0)] -> rw_cells usegs m (bv_unsigned sp + 48) [C8 (wz (ONES - T))] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N ->
  arr_len BC = 16 -> (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  -1 <= mc < N -> (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) ->
  R = gen_codes (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t mc ->
  evt usegs (ugcs_post s t L T N mc DL HP HL HM DP BC OL SL MC R ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s9 s10 s11 t5 t6 F fc m)
      (MS (uncR L a0 a1 a2 a3 a4 a5 a6 a7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 (wz T) s7 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1d5c8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR BLC FR F8 F24 F48 MI LAY RT1 RT2 RN LFC LDL LBC RBC SEP RSP Rmc RDL ER.
  pose proof LAY as LAY0. lay_open LAY0.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold gen_codes in ER. rewrite bt_bl_count in ER. change (gen_codes_loop1 16 BC (arr_make (MAX_BITS + 1) 0) 0 1) with (NC BC) in ER.
  pose proof (munch_refl (uWgc T N sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + 72)) = bv_unsigned sp + 72) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  call (unc_phase L BC junk).
  1:{ exact BLC. } 1:{ exact FR. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact RBC. } 1:{ exact SEP. } 1:{ exact RSP. }
  unfold uncR. zs2. zstep. br_cases K.
  - (* [comment removed for export] *)
    replace (mc + 1) with 0 in ER by lia. cbn [Z.to_nat] in ER. rewrite loop2_0 in ER.
    apply evt_done. unfold ugcs_post. do 13 eexists. exists FC. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [apply uncl_cb32; eassumption|]. split; [exact ER| exact LFC].
  - zs2. ustep BT_TRAP. zs2. zs2. zs2. zs2. zs2. zs2.
    rewrite (zb_lxor_ones (bv_unsigned sp + 72)) by lia.
    destruct (NC_spec BC RBC) as [LNC _].
    lazymatch goal with HN : u8arr usegs ?mm (bv_unsigned sp + 72) (u16s (ncl ?w0 (NC BC))) |- evt _ _ (MS _ _ _ _ _ ?mm' _) =>
      call (ugc_loop (Z.to_nat (mc + 1)) s t T N 0 mc w0 FC DL (NC BC) HP HL HM DP BC OL SL MC R mm' sp) end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ lia. } 1:{ lia. } 1:{ exact RSP. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LNC. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RDL. } 1:{ intros k Hk. apply NC_range; [exact RBC| exact Hk]. }
    1:{ exact ER. }
    unfold ugcR. apply evt_done. unfold ugcs_post. do 13 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct ?fc' DL N)) |- _ => exists fc' end. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [eassumption|]. split; [apply uncl_cb32; eassumption|]. split; assumption.
Qed.

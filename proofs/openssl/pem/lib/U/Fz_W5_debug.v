(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SysStep Bytes Ubs ZBridge.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key Th_errno. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_local Fz_T_once Fz_T_sa Fz_T_master Fz_I3_base
  Fz_M_malloc Fz_M_free F_strlen Str_stpcpy Fz_W5_glx Fz_W5_gsi Fz_W5_defs Fz_W5_vset Fz_W5_new.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wstore32 AH BASE ws i ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok usegs mX BASE ws i (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AW" in
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) => pose proof (u32arr_write usegs mX BASE ws i v AH ltac:(lia)) as A2
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mY ?a ?bs) _) =>
        change (write_to_mem mY a bs) with (write_to_mem mY a (le4 (Z_to_bv 64 0))); pose proof (u32arr_write usegs mX BASE ws i (Z_to_bv 64 0) AH ltac:(lia)) as A2
    end;
    replace (BASE + 4 * i) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.
Ltac wstore64 AH BASE ws i ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok usegs mX BASE ws i (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AW" in
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le8 ?v)) _) => pose proof (u64arr_write usegs mX BASE ws i v AH ltac:(lia)) as A2
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mY ?a ?bs) _) =>
        change (write_to_mem mY a bs) with (write_to_mem mY a (le8 (Z_to_bv 64 0))); pose proof (u64arr_write usegs mX BASE ws i (Z_to_bv 64 0) AH ltac:(lia)) as A2
    end;
    replace (BASE + 8 * i) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.

(* [comment removed for export] *)
Ltac lxs_here LXS MU WM KEEP :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (LXS1 : lx_statics mX)
      by (eapply lx_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact LXS]; KEEP;
          intros a Ha; cbv beta; cbn [outside]; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; repeat split; try exact I; lia) end.


Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation nulls := (repeat (Z_to_bv 64 0) 16) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition FZ_ERRDBG : Z := 0xe7638.
Definition SITE_dbg_m1 : Z := 0xe76e0.      (* [comment removed for export] *)
Definition SITE_dbg_m2 : Z := 0xe7764.      (* [comment removed for export] *)
Definition DBG_STACK : Z := 80 + CM_STACK.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma str_head : forall (c : byte) str, ~ In (Z_to_bv 8 0) (c :: str) -> bv_unsigned c <> 0.
Proof. intros c str H Hc. apply H. left. apply bv_eq. rewrite Hc. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dbg_s1_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra s0 s1 s2 s3 s4 s5 s6 : word)
    (E SF SN lo : Z) (line errv : word) (fl mk buf ls : list word) (fstr fslack : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j : list byte) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 SITE_dbg_m1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 SN)
                    (Z_to_bv 64 (Z.of_nat (length fstr) + 1)) a1 a2 a3 a4 a5 a6 a7
                   line (Z_to_bv 64 E) (Z_to_bv 64 SF) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (E + 584)) s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 FZ_CRYPTO_MALLOC) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (bv_unsigned tp + -164) [C4 (sx32 errv)]
    /\ stk usegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells usegs m' (bv_unsigned sp + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ es_rep m' E 1 0 fl mk buf nulls ls nulls.

Lemma dbg_s1_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k MK SA NODES E SF SN : Z) (errv od pad tw ne : word)
    (fl mk buf ls : list word) (fstr fslack : list byte),
  a0 = Z_to_bv 64 SF -> a2 = Z_to_bv 64 SN -> 164 <= bv_unsigned tp ->
  rw_cells usegs m (IC_S + 8) [C1 (Z_to_bv 8 0)] -> rw_cells usegs m (IC_S + 32) [C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 1)] -> rw_cells usegs m (IC_S + 96) [C8 od] ->
  ro_cells usegs m 0x32dea4 [C4 (Z_to_bv 64 2)] ->
  ro_cells usegs m 0x32dea8 [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
  ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 0 <= T ->
  ro_cells usegs m (T + 8 * k) [C8 (Z_to_bv 64 MK)] -> 0 < MK < 2 ^ 64 -> MK mod 8 = 0 ->
  ro_cells usegs m (MK + 8 * 3) [C8 (Z_to_bv 64 SA)] -> 0 < SA < 2 ^ 64 -> SA mod 8 = 0 ->
  ro_cells usegs m SA (sa_hdr (Z_to_bv 64 1) pad tw ne (Z_to_bv 64 NODES)) -> 0 < NODES < 2 ^ 64 -> NODES mod 8 = 0 ->
  ro_cells usegs m NODES [C8 (Z_to_bv 64 E)] -> bv_unsigned ne <> 0 ->
  rw_cells usegs m (bv_unsigned tp + -164) [C4 errv] ->
  lx_statics m ->
  es_rep m E 1 0 fl mk buf nulls ls nulls -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x353000 <= E) -> bv_unsigned tp = RATP ->
  ro_bytes usegs SF (fstr ++ Z_to_bv 8 0 :: fslack) -> ~ In (Z_to_bv 8 0) fstr -> (- (SF + Z.of_nat (length fstr) + 1)) mod 8 <= Z.of_nat (length fslack) ->
  0x10000 <= SF -> SF + (Z.of_nat (length fstr) + 1) + Z.of_nat (length fslack) <= 0x2c0000 -> (1 <= length fstr)%nat -> Z.of_nat (length fstr) + 1 <= 64 ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - DBG_STACK ->
  E + 904 <= lo ->
  (T + 8 * k + 8 <= lo \/ bv_unsigned sp <= T + 8 * k) ->
  (MK + 8 * 3 + 8 <= lo \/ bv_unsigned sp <= MK + 8 * 3) ->
  (SA + 32 <= lo \/ bv_unsigned sp <= SA) ->
  (NODES + 8 <= lo \/ bv_unsigned sp <= NODES) ->
  mem_inv usegs m ->
  evt usegs (dbg_s1_post sp gp tp s7 s8 s9 s10 s11 F fc ra s0 s1 s2 s3 s4 s5 s6 E SF SN lo a1 errv fl mk buf ls fstr fslack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_ERRDBG) fc None m (seg_rom usegs)).
Proof.
  intros until fslack.
  intros -> -> TP STOP ONCE OD OC KC HK TS T0 MKC HMK MKA SAC HSA SAA HC HNO NOA VC NE0 ERR LXS ES E0 EAL EIMG TPV ROB NONUL PAD SLOW SHIGH FNE FLEN ST GLO LO SE S1 S2 S3 S4 MI.
  unfold DBG_STACK, CM_STACK, RMALLOC_STACK, GSI_STACK, FZ_ERRDBG, sa_hdr, IC_S, GLOBALS_TOP, RATP in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64. pose proof (repeat_length (Z_to_bv 64 0) 16) as LN16.
  pose proof (ro_cells_bound _ _ _ _ MKC) as MKB. cbn [cells_size csize Nat.add] in MKB.
  pose proof (ro_cells_bound _ _ _ _ SAC) as SAB. cbn [cells_size csize Nat.add] in SAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * k) in *. set (P3 := MK + 8 * 3) in *.
  assert (HD : exists c, nth_error (fstr ++ Z_to_bv 8 0 :: fslack) 0 = Some c /\ bv_unsigned c <> 0 /\ 0 <= bv_unsigned c < 256).
  { destruct fstr as [|c fstr']; [cbn in FNE; lia|]. exists c. split; [reflexivity|]. split; [exact (str_head _ _ NONUL)|].
    pose proof (bv_unsigned_in_range 8 c) as R8. unfold bv_modulus in R8. cbn in R8. lia. }
  destruct HD as (c & HN & HC0 & HC8).
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  (* [comment removed for export] *)
  do 11 ths. do 3 ths. ths. ths.
  pose proof T_get_state_steady_proof as GSI. unfold T_get_state_steady_stmt, GSI_STACK, sa_hdr, IC_S, GLOBALS_TOP in GSI.
  tcall (GSI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T k MK SA NODES E errv od pad tw ne).
  all: try first [eassumption | reflexivity | lia].
  clear GSI. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths. ths. ths. ubs_if.
  ths. try rewrite (t_sx32_small 1) by lia. ths. ths. th_if_lit.
  ths. ths. ths. ths. if_cases KO1; zify_cond KO1. { exfalso. rewrite ?unsigned_lit in KO1 by lia. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read usegs mX (E + 576) (repeat (Z_to_bv 64 0) 16) 1 (Z_to_bv 64 0) (Z_to_bv 64 (E + 584)) A7
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD.
  (* [comment removed for export] *)
  ths. ths. ths. ths.
  lxs_here LXS MU WM ltac:(clear - LO GLO TPV E0 EIMG).
  tcall (crypto_free_null _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | reflexivity | unfold GLOBALS_TOP; lia].
  clear LXS1. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with H : mem_inv usegs mX |- _ =>
      assert (STRa : bytes_at usegs mX SF (fstr ++ Z_to_bv 8 0 :: fslack))
        by (apply ro_bytes_at; [exact H| lia| rewrite length_app; cbn [length]; lia| exact ROB]) end;
    pose proof (u8ro_read usegs mX SF (fstr ++ Z_to_bv 8 0 :: fslack) 0 c (Z_to_bv 64 SF) STRa HN ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD. cbv beta.
  ths. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  ths. ths.
  tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fstr fslack).
  all: try first [eassumption | lia].
  clear STRa. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. ths. ths. ths.
  apply evt_done. unfold dbg_s1_post, SITE_dbg_m1. do 16 eexists.
  split; [cbv delta [mkR]; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  unfold es_rep; repeat (split; [first [eassumption | lia] |]); lia.
Qed.
End WithCeiling0.

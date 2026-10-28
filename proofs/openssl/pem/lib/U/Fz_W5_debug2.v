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
  Fz_M_malloc Fz_M_free F_strlen Str_stpcpy Fz_W5_glx Fz_W5_gsi Fz_W5_defs Fz_W5_vset Fz_W5_new Fz_W5_debug.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation nulls := (repeat (Z_to_bv 64 0) 16) (only parsing).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dbg_s2_post (sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (rae s0e s1e s2e s3e s4e s5e s6e : word)
    (E SF SN QF lo : Z) (line : word) (fl mk buf ls : list word) (fstr nstr : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j : list byte) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 SITE_dbg_m2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 SN)
                    (Z_to_bv 64 (Z.of_nat (length nstr) + 1)) a1 a2 a3 a4 a5 a6 a7
                    line (Z_to_bv 64 (E + 776)) (Z_to_bv 64 SF) (Z_to_bv 64 8) (Z_to_bv 64 4) (Z_to_bv 64 (E + 584)) s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 FZ_CRYPTO_MALLOC) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp - 80); (QF, QF + (Z.of_nat (length fstr) + 1)); (E, E + 904)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells usegs m' (bv_unsigned sp + -80) [CB 8 j; C8 s7; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ es_rep m' E 1 0 fl mk buf (upd nulls 1%nat (Z_to_bv 64 QF)) (upd ls 1%nat line) nulls
    /\ rw_cells usegs m' QF [CB (S (length fstr)) (fstr ++ [Z_to_bv 8 0])].

Lemma dbg_s2_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rae s0e s1e s2e s3e s4e s5e s6e line : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo E SF SN QF : Z)
    (fl mk buf ls : list word) (fstr fslack nstr nslack junk j8 : list byte),
  164 <= bv_unsigned tp -> bv_unsigned tp = RATP ->
  lx_statics m ->
  es_rep m E 1 0 fl mk buf nulls ls nulls -> 0 < E -> E mod 8 = 0 -> (E + 904 <= 0x10000 \/ 0x353000 <= E) ->
  ro_bytes usegs SF (fstr ++ Z_to_bv 8 0 :: fslack) -> ~ In (Z_to_bv 8 0) fstr -> (- (SF + Z.of_nat (length fstr) + 1)) mod 8 <= Z.of_nat (length fslack) ->
  0x10000 <= SF -> SF + (Z.of_nat (length fstr) + 1) + Z.of_nat (length fslack) <= 0x2c0000 -> (1 <= length fstr)%nat -> Z.of_nat (length fstr) + 1 <= 64 ->
  ro_bytes usegs SN (nstr ++ Z_to_bv 8 0 :: nslack) -> ~ In (Z_to_bv 8 0) nstr -> (- (SN + Z.of_nat (length nstr) + 1)) mod 8 <= Z.of_nat (length nslack) ->
  0x10000 <= SN -> SN + (Z.of_nat (length nstr) + 1) + Z.of_nat (length nslack) <= 0x2c0000 -> (1 <= length nstr)%nat -> Z.of_nat (length nstr) + 1 <= 64 ->
  rw_cells usegs m QF [CB (S (length fstr)) junk] -> rblock_range QF (Z.of_nat (length fstr) + 1) ->
  (QF + (Z.of_nat (length fstr) + 1) <= E \/ E + 904 <= QF) ->
  stk usegs m lo (bv_unsigned sp + -80) -> GLOBALS_TOP <= lo -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DBG_STACK ->
  E + 904 <= lo ->
  rw_cells usegs m (bv_unsigned sp + -80) [CB 8 j8; C8 s7; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
  mem_inv usegs m ->
  evt usegs (dbg_s2_post sp gp tp s7 s8 s9 s10 s11 F fc rae s0e s1e s2e s3e s4e s5e s6e E SF SN QF lo line fl mk buf ls fstr nstr m)
    (MS (mkR (Z_to_bv 64 SITE_dbg_m1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 SN) (Z_to_bv 64 QF) a1 a2 a3 a4 a5 a6 a7
             line (Z_to_bv 64 E) (Z_to_bv 64 SF) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (E + 584)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_dbg_m1) fc None m (seg_rom usegs)).
Proof.
  intros until j8.
  intros TP TPV LXS ES E0 EAL EIMG ROB NONUL PAD SLOW SHIGH FNE FLEN ROBN NONULN PADN SLOWN SHIGHN NNE NLEN BLK RNG QE ST GLO ACL LO SE FR MI.
  unfold DBG_STACK, CM_STACK, RMALLOC_STACK, SITE_dbg_m1, GLOBALS_TOP, RATP in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64. pose proof (repeat_length (Z_to_bv 64 0) 16) as LN16.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof RNG as (Q0 & _ & _ & QCL & QIMG).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp - 80); (QF, QF + (Z.of_nat (length fstr) + 1)); (E, E + 904)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  assert (HD : exists d, nth_error (nstr ++ Z_to_bv 8 0 :: nslack) 0 = Some d /\ bv_unsigned d <> 0 /\ 0 <= bv_unsigned d < 256).
  { destruct nstr as [|d nstr']; [cbn in NNE; lia|]. exists d. split; [reflexivity|]. split; [exact (str_head _ _ NONULN)|].
    pose proof (bv_unsigned_in_range 8 d) as R8. unfold bv_modulus in R8. cbn in R8. lia. }
  destruct HD as (d & HN & HD0 & HD8).
  (* [comment removed for export] *)
  ths. ubs_if.
  wstore64 A7 (E + 576) (repeat (Z_to_bv 64 0) 16) 1 (E + 584).
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with H : mem_inv usegs mX |- _ =>
      assert (STRa : bytes_at usegs mX SF (fstr ++ Z_to_bv 8 0 :: fslack))
        by (apply ro_bytes_at; [exact H| lia| rewrite length_app; cbn [length]; lia| exact ROB]) end end.
  tcall (strcpy_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fstr fslack junk lo).
  all: try first [eassumption | lia].
  clear STRa. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths.
  ths. ths. ths. ths. if_cases KO1; zify_cond KO1. { exfalso. rewrite ?unsigned_lit, ?zb_lxor_ones in KO1 by lia. lia. }
  ths. ths. ths.
  wstore32 A8 (E + 704) ls 1 (E + 708).
  ths. if_cases KO2; zify_cond KO2. { exfalso. rewrite ?unsigned_lit in KO2 by lia. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read usegs mX (E + 768) (repeat (Z_to_bv 64 0) 16) 1 (Z_to_bv 64 0) (Z_to_bv 64 (E + 776)) A9
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD.
  (* [comment removed for export] *)
  ths. ths. ths. ths.
  lxs_here LXS MU WM ltac:(clear - LO GLO ACL TPV E0 EIMG QCL QIMG Q0).
  tcall (crypto_free_null _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | reflexivity | unfold GLOBALS_TOP; lia].
  clear LXS1. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with H : mem_inv usegs mX |- _ =>
      assert (STRb : bytes_at usegs mX SN (nstr ++ Z_to_bv 8 0 :: nslack))
        by (apply ro_bytes_at; [exact H| lia| rewrite length_app; cbn [length]; lia| exact ROBN]) end;
    pose proof (u8ro_read usegs mX SN (nstr ++ Z_to_bv 8 0 :: nslack) 0 d (Z_to_bv 64 SN) STRb HN ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  ths. clear RD. cbv beta.
  ths. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  ths. ths.
  tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nstr nslack).
  all: try first [eassumption | lia].
  clear STRb. cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. ths. ths. ths.
  apply evt_done. unfold dbg_s2_post, SITE_dbg_m2. do 16 eexists.
  split; [cbv delta [mkR]; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [| eassumption].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.
End WithCeiling0.

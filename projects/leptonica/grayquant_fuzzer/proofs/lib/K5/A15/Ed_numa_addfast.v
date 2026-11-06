(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_objkit LeptL_kit Ed_fp Gq_numa Numa_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Lemma numa_arr_app_unview : forall (m : mem) arr cap vals ws (v : word),
  u32arr asegs m arr (upd (vals ++ ws) (Z.to_nat (Z.of_nat (length vals))) v) -> Z.of_nat (length (vals ++ ws)) = cap -> Z.of_nat (length vals) < cap ->
  exists junk', rw_cells asegs m arr (numa_arr_cells cap (vals ++ [v]) junk').
Proof.
  intros m arr cap vals ws v UA L Hn. rewrite Nat2Z.id in UA. rewrite length_app in L.
  destruct ws as [|w0 ws']; [cbn [length] in L; lia|].
  rewrite upd_app_mid in UA. exists (u32s ws').
  pose proof (numa_arr_unview _ arr cap (vals ++ v :: ws') (length (vals ++ [v])) UA
                ltac:(rewrite !length_app in *; cbn [length] in *; lia) ltac:(rewrite !length_app; cbn [length]; lia)) as R.
  replace (vals ++ v :: ws') with ((vals ++ [v]) ++ ws') in R by (rewrite <- app_assoc; reflexivity).
  rewrite firstn_app_exact, skipn_app_exact in R. exact R.
Qed.

Section NUMAADDF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem numaAddNumber_fast_ok : numaAddNumber_fast_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo na cap arr vals v
    FDO MST -> -> FV OB NLT ENV RES.
  unfold lpost, lenv, lres, keeps, keepsL, freg_is in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (numa_obj_facts _ _ _ _ _ _ OB) as (LEN & CAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NE).
  destruct OB as ((pad & NC) & (junk0 & AC) & CHn & CHa & _). unfold numa_cells in NC.
  destruct (numa_arr_view m arr cap vals junk0 AC ltac:(lia)) as (ws & UA & UAL). clear AC.
  remember (vals ++ ws) as aws eqn:EA.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_acc_live RT AF Σ m na 32 ART0 INn) as (_ & ACCn).
  pose proof (af_acc_live RT AF Σ m arr (4 * cap) ART0 INa) as (_ & ACCa).
  pose proof (af_live_range RT AF Σ m na 32 ART0 INn) as (_ & NAR & NAS).
  pose proof (gp_live_hi RT GP Σ m na 32 ART0 INn) as NASH.
  pose proof (af_live_range RT AF Σ m arr (4 * cap) ART0 INa) as (_ & ARR & ARS).
  pose proof (gp_live_hi RT GP Σ m arr (4 * cap) ART0 INa) as ARSH.
  pose proof (live_apart RT AF Σ m na 32 arr (4 * cap) ART0 INn INa ltac:(congruence)) as DJ.
  unfold entry_st, e_numaAddNumber, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  cps_walk AF MST.
  pose proof (munch_refl [(usp - 64, usp); (na, na + 32); (arr, arr + 4 * cap)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  awalk [0x91c6c; 0x91d10; 0x91d6c].        (* [comment removed for export] *)
  rewrite !sx32_small by lia. brT.
  awalk [0x91c6c; 0x91d10; 0x91d6c].        (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ ?FF _ _ _ ?mm _) =>
    lazymatch goal with UAx : u32arr asegs mm arr ?wsx |- _ =>
      pose proof (u32arr_store_ok asegs mm arr wsx (Z.of_nat (length vals)) (wa (arr + 4 * Z.of_nat (length vals))) UAx ltac:(lia) ltac:(f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- context [le4 (reg_get FF ?r)] => replace (reg_get FF r) with v by (symmetry; exact FV) end;
      pose proof (u32arr_write asegs mm arr wsx (Z.of_nat (length vals)) v UAx ltac:(lia)) as UA2; rewrite Nat2Z.id in UA2;
      clear UAx; store_done; rename UA2 into UA
    end end.
  awalk [0x91c6c; 0x91d10; 0x91d6c].        (* [comment removed for export] *)
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| split; [| exact I]]];
                      [ intros zz Hzz; right; right; left; exists na, 32; split; [exact INn| lia]
                      | intros zz Hzz; right; right; left; exists arr, (4 * cap); split; [exact INa| lia] ]).
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  exists Σ. split; [| repeat split; lia].
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
  split.
  { intros a Ha Ho. lazymatch goal with MUx : munch _ m ?mf |- _ => apply MUx end. cbn [outside] in Ho |- *.
    destruct Ho as (Ho1 & Ho2 & _). split; [| split; [exact Ho1| split; [exact Ho2| exact I]]].
    destruct (aclient_split RT AF Σ m usp _ ART0 Ha); unfold STACK_WIN in *; lia. }
  unfold numa_obj. subst aws.
  lazymatch goal with NCx : rw_cells asegs ?mf na _, UAx : u32arr asegs ?mf arr _ |- _ =>
    rewrite ?sx32_small in NCx by lia; rewrite ?unsigned_lit in NCx by lia;
    destruct (numa_arr_app_unview mf arr cap vals ws v ltac:(rewrite Nat2Z.id; exact UAx) UAL NLT) as (junk' & AC');
    split; [eexists; rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold numa_cells; exact NCx|] end.
  split; [exists junk'; exact AC'|].
  split; [exact CHn|]. split; [exact CHa|]. split; [exact NE|]. split; [lia|]. rewrite length_app. cbn [length]. lia.
Qed.
End NUMAADDF.

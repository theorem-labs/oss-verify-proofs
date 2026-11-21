(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.


Ltac gcbn := cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
                  t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                  t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext l_SP l_SPA l_Zs l_F0 l_lo].

Ltac zify_lts_c K CK :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (clear - CK; Z.div_mod_to_equations; lia);
  zify_bool K.
Ltac ck_branchJc U JOIN CK :=
  ck_join U JOIN;
  [ let K := fresh "K" in let K2 := fresh "K2" in
    zstep; if_cases K; zify_cond K;
    try (ck_doneJ U JOIN);
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
            end);
    if_cases K2;
    first [ exfalso; zify_lts_c K2 CK; clear - CK K K2; Z.div_mod_to_equations; lia
          | ck_doneJ U JOIN ]
  | try clear CK ].

Section CANSEC1. Context {rc : runConstT}.
Lemma pull_facts : forall RNG W m m' D n payload ci,
  unpoisoned m D (D + n) -> munch W m m' -> disjoint_from W (shad D) (shad (D + n - 1) + 1 - shad D) ->
  rng RNG D n -> rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1) ->
  bytes_at asegs m' D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = n ->
  D mod 16 = 0 -> 1 <= D -> 0 <= ci < n ->
  exists b, ov_read_bytes asegs m' (Z_to_bv 64 (Z.shiftr (D + ci) 3 + 2147450880)) 1 = Some [b]
    /\ (sval b = 0 \/ (0 < sval b <= 7 /\ (D + ci) mod 8 + 1 - 1 < sval b))
    /\ acc_in RNG (Z_to_bv 64 (Z.shiftr (D + ci) 3 + 2147450880), 1%nat)
    /\ ov_read_bytes asegs m' (Z_to_bv 64 (D + ci)) 1 = Some [Z_to_bv 8 (bz payload ci)]
    /\ acc_in RNG (Z_to_bv 64 (D + ci), 1%nat)
    /\ 0 <= bz payload ci < 256.
Proof.
  intros RNG W m m' D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR.
  destruct (unp_check_mu asegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
  exists b. split; [exact RDB|]. split; [exact CK|].
  split; [apply (pay_sh_acc RNG D n (D + ci) RSD); [first [ apply mod16_mod8; assumption | Z.div_mod_to_equations; lia ]| lia| lia]|].
  split; [exact (pay_read asegs _ D payload ci PAYB ltac:(lia))|].
  split; [apply (rng_acc_litZ RNG D n (D + ci) 1%nat 1 RD eq_refl); lia|].
  apply bz_range. exact PAYR.
Qed.
End CANSEC1.

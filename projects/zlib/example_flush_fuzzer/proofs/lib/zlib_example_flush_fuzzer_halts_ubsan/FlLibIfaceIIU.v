(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr MemRel SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FMQ6 Require Import CallocLib6u CallocTail6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ZlibStmtBase ExSmallIface FlLibStmtU FlLibIfaceU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inflate HarnessSmallFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflCtx6 IRep6 IInit6.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation RSX := Tgt_example_flush_fuzzer_ubsan.M.loaded_segments.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma L_II6_ok : forall (regs : bvmap 5 word) (mem : word -> option byte) (q : iptrs) (zc t ra v16 v24 v32 fa ff ni ai : Z),
    let p := ip_p q in let strm := ip_strm q in
    ip_w q = 0 ->
    getr regs 2 = Z_to_bv 64 (t - 32) -> getr regs 10 = Z_to_bv 64 p -> getr regs 18 = Z_to_bv 64 strm ->
    getr regs 9 = Z_to_bv 64 FL_ISTATE_N ->   (* 1.4 UBSan: s1 holds the state size; memset(p, 0, s1) follows *)
    t mod 16 = 0 -> zc + FL_FRA <= t -> t <= 2 ^ 47 -> FL_IMG_TOP <= zc ->
    blocks_ok mem zc (iblocks q) -> img_clear mem -> 0 < strm -> strm mod 8 = 0 -> strm + 112 <= 2 ^ 47 ->
    store_ok RSX mem (Z_to_bv 64 (t - FL_FRA)) (Z.to_nat FL_FRA) = true -> store_ok RSX mem (Z_to_bv 64 strm) 112%nat = true ->
    all_apart [(t - FL_FRA, FL_FRA); (strm, 112); (p, FL_ISTATE_N)] -> (strm + 112 <= FL_RO_LO \/ FL_IMG_TOP <= strm) ->
    ra_ok ra -> 0 <= v16 < 2 ^ 63 -> 0 <= v24 < 2 ^ 63 -> 0 <= v32 < 2 ^ 63 ->
    zeros_at RSX mem p FL_ISTATE_N ->
    cell8 RSX mem (t - 8) ra -> cell8 RSX mem (t - 16) v16 -> cell8 RSX mem (t - 24) v24 -> cell8 RSX mem (t - 32) v32 ->
    cell8 RSX mem (strm + 48) 0 -> cell8 RSX mem (strm + 64) fa -> cell8 RSX mem (strm + 72) ff -> cell8 RSX mem (strm + 80) 0 ->
    fa = FL_ZCALLOC -> ff = FL_ZCFREE ->
    cell8 RSX mem strm ni -> cell4 RSX mem (strm + 8) ai ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps RSX (mkst regs (Z_to_bv 64 FL_A_II) mem (seg_rom RSX)) (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom RSX))
      /\ frame_mod mem mem' [(Z_to_bv 64 (t - FL_FRA), FL_FRA); (Z_to_bv 64 strm, 112); (Z_to_bv 64 p, FL_ISTATE_N)]
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 t
      /\ getr regs' 8 = Z_to_bv 64 v16 /\ getr regs' 9 = Z_to_bv 64 v24 /\ getr regs' 18 = Z_to_bv 64 v32
      /\ rkeep regs regs' [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
      /\ cell8 RSX mem' (strm + 16) 0 /\ cell8 RSX mem' (strm + 40) 0 /\ cell8 RSX mem' (strm + 48) 0 /\ cell8 RSX mem' (strm + 56) p
      /\ cell8 RSX mem' (strm + 64) fa /\ cell8 RSX mem' (strm + 72) ff /\ cell8 RSX mem' (strm + 80) 0 /\ cell8 RSX mem' (strm + 96) 1
      /\ FL_IREP mem' q FL_IS0
      /\ cell8 RSX mem' strm ni /\ cell4 RSX mem' (strm + 8) ai.
Proof.
  intros regs mem q zc t ra v16 v24 v32 fa ff ni ai. cbv zeta.
  intros Hw0 P2 P10 P9 PS1 T16 ZCL T47 TOP BOK IC S0 S8 S47 SOf SOs AP SIM RA V16 V24 V32 Z0 Cra C16 C24 C32 C48 C64 C72 C80 FA FF Cni Cai.
  set (p := ip_p q) in *. set (strm := ip_strm q) in *.
  unfold FL_FRA, FL_IMG_TOP, FL_ISTATE_N, FL_RO_LO in *.
  unfold blocks_ok, iblocks in BOK. rewrite Hw0 in BOK. cbn [Z.eqb app] in BOK. fold p in BOK.
  apply Forall_inv in BOK. cbn [fst snd] in BOK. unfold blk_okz, FL_ISTATE_N, FL_IMG_TOP in BOK.
  destruct BOK as (P16 & P1 & PZ & PIM & SOP).
  cbn [all_apart apart_from_all] in AP. unfold ExSmallIface.apart in AP.
  destruct AP as ((DTS & DTP & _) & (DSP & _) & _).
  assert (MF : mapped mem (t - 80) 80).
  { intros x Hx. apply (mapped_of_store_ok6u mem (t - 1024) 1024); [clear - ZCL TOP | clear | clear - T47 | clear - ZCL TOP | exact SOf | clear - Hx]; lia. }
  assert (MP : mapped mem p 7176).
  { intros x Hx. apply (mapped_of_store_ok6u mem p 7176); [clear - P1 | clear | clear - PZ ZCL T47 | exact PIM | exact SOP | exact Hx]; lia. }
  assert (MS : mapped mem strm 112).
  { intros x Hx. apply (mapped_of_store_ok6u mem strm 112); [clear - S0 | clear | clear - S47 | exact SIM | exact SOs | exact Hx]; lia. }
  assert (ZP : zblock mem p 7176).
  { unfold zblock. apply (pointwise_of_zeros_at mem p 7176); [clear - P1; lia | clear; lia | clear - PZ ZCL T47; lia | exact MP | exact Z0]. }
  unfold cell8, cell4 in *. rewrite FA in C64. rewrite FF in C72. unfold FL_ZCALLOC, FL_ZCFREE in *.
  assert (Dra : cell s6u_segs mem (t + -8) 8 ra) by (replace (t + -8) with (t - 8) by (clear; lia); exact Cra).
  assert (D16 : cell s6u_segs mem (t + -16) 8 v16) by (replace (t + -16) with (t - 16) by (clear; lia); exact C16).
  assert (D24 : cell s6u_segs mem (t + -24) 8 v24) by (replace (t + -24) with (t - 24) by (clear; lia); exact C24).
  assert (D32 : cell s6u_segs mem (t + -32) 8 v32) by (replace (t + -32) with (t - 32) by (clear; lia); exact C32).
  destruct RA as [RA1 RA2].
  destruct (ii_run regs mem t p strm ra v16 v24 v32 P2 P10 P9 PS1 S8 P16 C64 C72 Dra D16 D24 D32 ZP
              P1 ltac:(clear - PZ ZCL T47; lia) ltac:(clear - ZCL TOP; lia) ltac:(clear - T47; lia) S0 ltac:(clear - S47; lia)
              RA1 RA2 ltac:(clear - V16; lia) ltac:(clear - V24; lia) ltac:(clear - V32; lia)
              ltac:(unfold SymAux.sep; clear - DTP; lia) ltac:(unfold SymAux.sep; clear - DTS; lia) ltac:(unfold SymAux.sep; clear - DSP; lia) MF MP MS)
    as (R' & M' & RUN & Q2 & Q10 & Q8 & Q9 & Q18 & Hfr & SC & AR & X16 & X40 & X48 & X56 & X64 & X72 & X96 & KEEPC & AG & GR).
  exists R', M'.
  split.
  { replace (Z_to_bv 64 FL_A_II) with (Z_to_bv 64 pc6_ii) by (apply bv_eq; reflexivity). exact RUN. }
  split.
  {
    split; [| exact GR].
    intros a Hout. apply AG. intros Hin.
    unfold IIF in Hin. cbn [in_franges] in Hin.
    cbn [outside] in Hout. unfold in_rng in Hout. change (Z_to_bv 64) with zw in Hout.
    rewrite !u_zw_small in Hout by (clear - ZCL TOP T47 S0 S47 P1 PZ; lia).
    clear - Hin Hout ZCL TOP T47. lia. }
  split; [exact Q10|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|].
  split.
  { intros r Hr. apply Hfr. cbn in Hr.
    repeat (destruct Hr as [Hr|Hr]; [subst r; reflexivity|]). destruct Hr. }
  split; [exact X16|]. split; [exact X40|]. split; [exact X48|]. split; [exact X56|].
  split; [rewrite FA; exact X64|]. split; [rewrite FF; exact X72|].
  split; [exact (KEEPC (strm + 80) 8%nat 0 ltac:(cbn; tauto) C80 ltac:(clear; lia))|].
  split; [exact X96|].
  split.
  {
    unfold FL_IREP, ISREP6, IRANGES, FL_IS0, FL_ISTATE_N, FL_WIN_N. fold p strm. rewrite Hw0.
    change (is0 7) with (is0 KI6). rewrite is0_eq.
    split.
    - split; [exact SC|]. destruct AR as (A1 & A2 & A3).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      split; [intros X; exfalso; exact (X eq_refl)|]. split; [split; [reflexivity | intros _; reflexivity]|].
      intros X; exfalso; exact (X eq_refl).
    - split; [clear; cbn [is_mode is0c]; unfold HEAD, SYNC; lia|]. clear - P1 PZ ZCL T47. lia. }
  split; [exact (KEEPC strm 8%nat ni ltac:(cbn; tauto) Cni ltac:(clear; lia))|].
  exact (KEEPC (strm + 8) 4%nat ai ltac:(cbn; tauto) Cai ltac:(clear; lia)).
Qed.
End FXG.

From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
Import ListNotations.
Local Open Scope Z_scope.

Definition PARSE_VALUE : Z := 0x144e4.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition parse_value_contract (d : nat) : Prop :=
  forall L A regs mem md Lam peak cnt fail b q text len p tb v,
    reader_env B API (PARSE_VALUE_K d) L A regs mem md ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 q -> getr regs 11 = Z_to_bv 64 v ->
    pj_in_ok segs mem q text len p (Z.of_nat d) tb ->
    spZ regs <= q -> (st_init_done A = false -> auxv_pre B (ly_sec L) (q + 24) mem) ->
    Z.of_nat (PjRoundTrip.maxrun (zb tb)) < 2 ^ 30 ->
    text_ok B L A Lam regs text len ->
    v <> 0 -> pj_zero segs mem v -> rplace B L A Lam regs mem v ->
    Frame.disjoint_from [(text, text + len); (q, q + 24)] v 56 ->
    Frame.disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)]
      (spZ regs - PARSE_VALUE_K d) (PARSE_VALUE_K d) ->
    cnt + 2 * Z.of_nat (length (rest_at tb text p)) + 2 < 2 ^ 64 - 1 ->
    room_run F b (snd (fst (jr_value jr_strtod d (rest_at tb text p) []))) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PARSE_VALUE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' Lam' peak' cnt' fail' ok res tr okr D,
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
         rpost B API (PARSE_VALUE_K d) L A regs mem md (rd_writes q v D) (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\
         ledger B L' A' mem' Lam' peak' cnt' fail' /\
         jr_value jr_strtod d (rest_at tb text p) ok = (res, tr, okr) /\
         oks ok cnt fail (calls tr) /\
         cnt' = cnt + Z.of_nat (calls tr) /\
         fail_after cnt fail (calls tr) fail' /\
         Permutation Lam' (D ++ Lam) /\ Permutation (map snd D) (map Z.of_nat (lsz tr)) /\ Z.of_nat (length D) = nlive tr /\ new_blks L A D /\
         peak' = Z.max peak (lsum Lam + hpeak tr) /\
         hpeak tr <= 224 * Z.of_nat (length (rest_at tb text p)) + 512 * Z.of_nat (MAXD - d) /\
         rf_ok F A' (rf_run F b tr) /\
         match res with
         | Some (t, r) =>
             getr regs' 10 = Z_to_bv 64 0 /\
             pj_in_ok segs mem' q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb /\
             pj_node segs mem' (lin Lam') v t D /\
             lsum D <= 224 * (Z.of_nat (length (rest_at tb text p)) - Z.of_nat (length r))
         | None =>
             getr regs' 10 = Z_to_bv 64 (-1) /\
             pj_in_after B mem' q text len (Z.of_nat d) 33 /\
             pj_fd segs mem' (lin Lam') (MAXD - d) v D
         end).

End K.

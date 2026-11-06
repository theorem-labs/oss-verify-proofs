From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
Import ListNotations.
Local Open Scope Z_scope.

Definition PJ_PARSE : Z := 0x14454.

Definition pj_parse_writes (out : Z) (x : Z) : Prop := out <= x < out + 56 \/ alloc_statics x.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition pj_parse_contract : Prop :=
  forall L A regs mem md Lam peak cnt fail b t0 len out tb,
    reader_env B API PJ_PARSE_K L A regs mem md ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 t0 -> getr regs 11 = Z_to_bv 64 len -> getr regs 12 = Z_to_bv 64 out ->
    len < 2 ^ 40 -> 0 < t0 -> t0 + len < 2 ^ 62 ->
    Z.of_nat (length tb) = len -> Mem.bytes_at segs mem t0 tb ->
    Z.of_nat (PjRoundTrip.maxrun (zb tb)) < 2 ^ 30 ->
    text_ok B L A Lam regs t0 len ->
    out <> 0 -> pj_rw segs mem out -> rplace B L A Lam regs mem out ->
    (forall a k, In (a, k) Lam -> out + 56 <= a \/ a + k <= out) ->
    Frame.disjoint_from [(t0, t0 + len)] out 56 ->
    Frame.disjoint_from [(t0, t0 + len); (out, out + 56)] (spZ regs - PJ_PARSE_K) PJ_PARSE_K ->
    cnt + 2 * len + 2 < 2 ^ 64 - 1 ->
    room_run F b (snd (jr_run jr_strtod (zb tb) [])) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PJ_PARSE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' Lam' peak' cnt' fail' ok res tr,
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
         rpost B API PJ_PARSE_K L A regs mem md (pj_parse_writes out) (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\
         ledger B L' A' mem' Lam' peak' cnt' fail' /\
         jr_run jr_strtod (zb tb) ok = (res, tr) /\
         oks ok cnt fail (calls tr) /\
         cnt' = cnt + Z.of_nat (calls tr) /\
         fail_after cnt fail (calls tr) fail' /\
         peak' = Z.max peak (lsum Lam + hpeak tr) /\
         hpeak tr <= 224 * len + 16384 /\
         (cnt <= fail < cnt + Z.of_nat (ncalls jr_strtod (zb tb)) -> res = None) /\
         (fail < cnt \/ cnt + Z.of_nat (ncalls jr_strtod (zb tb)) <= fail ->
            res = json_read jr_strtod (zb tb) /\ calls tr = ncalls jr_strtod (zb tb)) /\
         match res with
         | Some t =>
             getr regs' 10 = Z_to_bv 64 0 /\ rf_ok F A' (rf_run F b tr) /\
             exists D, Permutation Lam' (D ++ Lam) /\ Permutation (map snd D) (map Z.of_nat (lsz tr)) /\ Z.of_nat (length D) = nlive tr /\ new_blks L A D /\
               pj_node segs mem' (lin Lam') out t D
         | None =>
             getr regs' 10 = Z_to_bv 64 (-1) /\
             (exists D D', Permutation D D' /\ Permutation (map snd D) (map Z.of_nat (lsz tr)) /\ Z.of_nat (length D) = nlive tr /\
                rf_ok F A' (rf_frees F (rf_run F b tr) D')) /\
             Permutation Lam' Lam /\ pj_zero segs mem' out
         end).

End K.

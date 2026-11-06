From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition PJ_STRING : Z := 0x14890.

Definition pj_string_writes (v : Z) (x : Z) : Prop := v <= x < v + 56 \/ alloc_statics x.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition pj_string_contract : Prop :=
  forall L A regs mem md Lam peak cnt fail b v s cs slack,
    reader_env B API PJ_STRING_K L A regs mem md ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 v -> getr regs 11 = Z_to_bv 64 s ->
    v <> 0 -> pj_rw segs mem v -> rplace B L A Lam regs mem v ->
    Frame.disjoint_from [(v, v + 56)] (spZ regs - PJ_STRING_K) PJ_STRING_K ->
    (s = 0 /\ cs = [] \/
     s <> 0 /\ Mem.bytes_at segs mem s (cs ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) cs /\
     (- (s + Z.of_nat (length cs) + 1)) mod 8 <= Z.of_nat (length slack) /\
     cstr_ok B Lam s (Z.of_nat (length cs) + 1) /\
     Frame.disjoint_from [(v, v + 56)] s (Z.of_nat (length cs) + 1) /\
     Frame.disjoint_from [(s, s + Z.of_nat (length cs) + 1)] (spZ regs - PJ_STRING_K) PJ_STRING_K) ->
    Z.of_nat (length cs) + 17 <= 2 ^ 28 ->
    rf_room F b (Z.of_nat (length cs) + 17) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PJ_STRING) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' Lam' peak' fail' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         rpost B API PJ_STRING_K L A regs mem md (pj_string_writes v) (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\
         getr regs' 10 = Z_to_bv 64 res /\
         ledger B L' A' mem' Lam' peak' ((cnt + 1) mod 2 ^ 64) fail' /\
         ( (cnt <> fail /\ res = 0 /\ fail' = fail /\ rf_ok F A' (rf_malloc F b (Z.of_nat (length cs) + 17)) /\
            exists a, Lam' = (a, Z.of_nat (length cs) + 1) :: Lam /\ new_blks L A [(a, Z.of_nat (length cs) + 1)] /\
              peak' = Z.max peak (lsum Lam') /\
              pj_node segs mem' (lin Lam') v (JStr (zb cs)) [(a, Z.of_nat (length cs) + 1)])
         \/ (cnt = fail /\ res = -1 /\ fail' = 2 ^ 64 - 1 /\ Lam' = Lam /\ peak' = peak /\ rf_ok F A' b /\
             pj_rw segs mem' v /\
             Mem.bytes_at segs mem' v (Mem.le4 (Z_to_bv 64 4) ++ repeat (Z_to_bv 8 0) 52) /\
             pj_fd segs mem' (lin Lam') 0 v []) )).

End K.

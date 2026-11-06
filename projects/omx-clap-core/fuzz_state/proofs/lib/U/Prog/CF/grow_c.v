From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition GROW : Z := 0x14bac.

Definition grow_writes (v ty kids keys n cap : Z) (x : Z) : Prop :=
  n = cap /\
  (v + 24 <= x < v + 40 \/ v + 48 <= x < v + 56 \/
   blk_set (kids_blk kids cap ++ keys_blk ty keys cap) x \/ alloc_statics x).

Definition grow_gone (ty kids keys n cap : Z) (a sz : Z) : Prop :=
  n = cap /\ freed (kids_blk kids cap ++ keys_blk ty keys cap) a sz.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition moved (mem mem' : word -> option byte) (src dst n : Z) : Prop :=
  forall i, 0 <= i < n -> mbyte segs mem' (dst + i) = mbyte segs mem (src + i).

Definition grow_contract : Prop :=
  forall L A regs mem md Lam peak cnt fail b v ty num str kids keys n cap,
    reader_env B API GROW_K L A regs mem md ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 v -> v <> 0 ->
    pj_hdr segs mem v ty num str kids keys n cap ->
    pj_slots_at (lin Lam) ty kids keys n cap ->
    pj_apart (kids_blk kids cap ++ keys_blk ty keys cap) v ->
    rplace B L A Lam regs mem v ->
    Frame.disjoint_from [(v, v + 56)] (spZ regs - GROW_K) GROW_K ->
    cnt + 2 < 2 ^ 64 - 1 ->
    (n = cap ->
       rf_room F b (56 * cap2 cap + 16) /\ 56 * cap2 cap + 16 <= 2 ^ 28 /\
       (ty = 6 -> rf_room F (rf_grow F b (56 * cap) (56 * cap2 cap)) (8 * cap2 cap + 16))) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 GROW) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' Lam' peak' cnt' fail' b' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         rpost B API GROW_K L A regs mem md (grow_writes v ty kids keys n cap) (grow_gone ty kids keys n cap)
           L' A' regs' mem' md' /\
         rd_cells B mem' /\
         getr regs' 10 = Z_to_bv 64 res /\
         ledger B L' A' mem' Lam' peak' cnt' fail' /\
         rf_ok F A' b' /\
         ( (n < cap /\ res = 0 /\ L' = L /\ A' = A /\ Lam' = Lam /\ peak' = peak /\ cnt' = cnt /\
            fail' = fail /\ b' = b /\ pj_hdr segs mem' v ty num str kids keys n cap)
         \/ (n = cap /\ cnt = fail /\ res = -1 /\ Lam' = Lam /\ peak' = peak /\ cnt' = cnt + 1 /\
             fail' = 2 ^ 64 - 1 /\ b' = b /\
             pj_hdr segs mem' v ty num str kids keys n cap /\
             moved mem mem' kids kids (56 * cap) /\ (ty = 6 -> moved mem mem' keys keys (8 * cap)))
         \/ (n = cap /\ cnt <> fail /\ ty <> 6 /\ res = 0 /\
             exists k' Lam0, k' <> 0 /\ k' mod 16 = 0 /\ new_blks L A [(k', 56 * cap2 cap)] /\
               Permutation Lam (kids_blk kids cap ++ Lam0) /\ Permutation Lam' ((k', 56 * cap2 cap) :: Lam0) /\
               peak' = Z.max peak (lsum Lam') /\ cnt' = cnt + 1 /\ fail' = fail /\
               b' = rf_grow F b (56 * cap) (56 * cap2 cap) /\
               moved mem mem' kids k' (56 * cap) /\
               pj_hdr segs mem' v ty num str k' keys n (cap2 cap) /\
               pj_slots_at (lin Lam') ty k' keys n (cap2 cap))
         \/ (n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 = fail /\ res = -1 /\
             exists k' Lam0, k' <> 0 /\ k' mod 16 = 0 /\ new_blks L A [(k', 56 * cap2 cap)] /\
               Permutation Lam (kids_blk kids cap ++ Lam0) /\ Permutation Lam' ((k', 56 * cap2 cap) :: Lam0) /\
               peak' = Z.max peak (lsum Lam') /\ cnt' = cnt + 2 /\ fail' = 2 ^ 64 - 1 /\
               b' = rf_grow F b (56 * cap) (56 * cap2 cap) /\
               moved mem mem' kids k' (56 * cap) /\
               pj_hdr segs mem' v ty num str k' keys n cap /\
               moved mem mem' keys keys (8 * cap))
         \/ (n = cap /\ cnt <> fail /\ ty = 6 /\ cnt + 1 <> fail /\ res = 0 /\
             exists k' y' Lam0, k' <> 0 /\ k' mod 16 = 0 /\ y' <> 0 /\ y' mod 16 = 0 /\
               new_blks L A [(y', 8 * cap2 cap); (k', 56 * cap2 cap)] /\
               Permutation Lam (kids_blk kids cap ++ keys_blk ty keys cap ++ Lam0) /\
               Permutation Lam' ((y', 8 * cap2 cap) :: (k', 56 * cap2 cap) :: Lam0) /\
               peak' = Z.max peak (Z.max (lsum Lam + 56 * (cap2 cap - cap)) (lsum Lam')) /\
               cnt' = cnt + 2 /\ fail' = fail /\
               b' = rf_grow F (rf_grow F b (56 * cap) (56 * cap2 cap)) (8 * cap) (8 * cap2 cap) /\
               moved mem mem' kids k' (56 * cap) /\ moved mem mem' keys y' (8 * cap) /\
               pj_hdr segs mem' v ty num str k' y' n (cap2 cap) /\
               pj_slots_at (lin Lam') ty k' y' n (cap2 cap)) )).

End K.

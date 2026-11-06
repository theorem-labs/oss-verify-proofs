From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes.
Import ListNotations.
Local Open Scope Z_scope.

Definition PJ_SET : Z := 0x15d7c.

Definition set_trace (n cap klen : Z) : list ev :=
  (if n =? cap then [EGrow (Z.to_nat (56 * cap)) (Z.to_nat (56 * cap2 cap));
                     EGrow (Z.to_nat (8 * cap)) (Z.to_nat (8 * cap2 cap))] else []) ++
  [EAlloc (Z.to_nat (klen + 1))].

Definition pj_set_writes (o w : Z) (D Dw : list (Z * Z)) (x : Z) : Prop :=
  o <= x < o + 56 \/ w <= x < w + 56 \/ blk_set (D ++ Dw) x \/ alloc_statics x.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition pj_set_contract : Prop :=
  forall L A regs mem md Lam peak cnt fail b o k w ms tv D Dw num str kids keys n cap kname slack
    (dd : nat),
    reader_env B API (PJ_SET_K dd) L A regs mem md ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 k -> getr regs 12 = Z_to_bv 64 w ->
    o <> 0 -> pj_node segs mem (lin Lam) o (JObj ms) D ->
    pj_hdr segs mem o 6 num str kids keys n cap -> cap <= 2 ^ 54 ->
    rplace B L A Lam regs mem o ->
    w <> 0 -> pj_node segs mem (lin Lam) w tv Dw -> rplace B L A Lam regs mem w ->
    (forall bk, In bk Dw -> ~ In bk D) ->
    (forall x, w <= x < w + 56 -> ~ pj_foot o D x) ->
    pj_apart Dw o ->
    (depth (JObj ms) <= S dd)%nat -> (depth tv <= dd)%nat ->
    Mem.bytes_at segs mem k (kname ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) kname ->
    (- (k + Z.of_nat (length kname) + 1)) mod 8 <= Z.of_nat (length slack) ->
    cstr_ok B Lam k (Z.of_nat (length kname) + 1 + Z.of_nat (length slack)) ->
    (forall x, k <= x < k + Z.of_nat (length kname) + 1 ->
       ~ pj_foot o D x /\ ~ pj_foot w Dw x) ->
    Frame.disjoint_from [(o, o + 56); (w, w + 56); (k, k + Z.of_nat (length kname) + 1)]
      (spZ regs - PJ_SET_K dd) (PJ_SET_K dd) ->
    cnt + 3 < 2 ^ 64 - 1 ->
    room_run F b (set_trace n cap (Z.of_nat (length kname))) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PJ_SET) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' Lam' peak' fail' res (c : nat) Lr Do,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         rpost B API (PJ_SET_K dd) L A regs mem md (pj_set_writes o w D Dw) (freed (D ++ Dw))
           L' A' regs' mem' md' /\
         rd_cells B mem' /\
         getr regs' 10 = Z_to_bv 64 res /\
         ledger B L' A' mem' Lam' peak' (cnt + Z.of_nat c) fail' /\
         fail_after cnt fail c fail' /\
         Permutation Lam (D ++ Dw ++ Lr) /\ Permutation Lam' (Do ++ Lr) /\
         pj_zero segs mem' w /\
         ((fail < cnt \/ cnt + 2 < fail) -> res = 0) /\
         ( (In (zb kname) (map fst ms) /\ c = 0%nat /\ res = 0 /\ peak' = peak /\
            (exists i vi Di Dr, nth_error ms i = Some (zb kname, vi) /\
               (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> zb kname) /\
               pj_node segs mem (lin Lam) (kids + 56 * Z.of_nat i) vi Di /\
               Permutation D (Di ++ Dr) /\ Permutation Do (Dr ++ Dw) /\
               (exists Di', Permutation Di Di' /\ rf_ok F A' (rf_frees F b Di')) /\
               Z.of_nat (length Do) = Z.of_nat (length (D ++ Dw)) - Z.of_nat (length Di) /\
               lsum Do = lsum (D ++ Dw) - lsum Di) /\
            pj_node segs mem' (lin Lam') o (JObj (pj_set_model ms (zb kname) tv)) Do)
         \/ (~ In (zb kname) (map fst ms) /\
             ~ (cnt <= fail < cnt + Z.of_nat (length (set_trace n cap (Z.of_nat (length kname))))) /\
             c = length (set_trace n cap (Z.of_nat (length kname))) /\ res = 0 /\
             peak' = Z.max peak (lsum Lam') /\
             rf_ok F A' (rf_run F b (set_trace n cap (Z.of_nat (length kname)))) /\
             Z.of_nat (length Do) = Z.of_nat (length (D ++ Dw)) + nlive (set_trace n cap (Z.of_nat (length kname))) /\
             lsum Do = lsum (D ++ Dw) + held (set_trace n cap (Z.of_nat (length kname))) /\
             (exists Dold Dnew Dr a, Permutation D (Dold ++ Dr) /\
                Permutation Do (Dnew ++ (a, Z.of_nat (length kname) + 1) :: Dr ++ Dw) /\
                (forall a' k', In (a', k') (Dnew ++ [(a, Z.of_nat (length kname) + 1)]) ->
                   In (a', k') Dold \/ ~ In (a' - 16, k' + 16) (blocks L A)) /\
                (n < cap /\ Dold = [] /\ Dnew = [] \/
                 n = cap /\ Dold = kids_blk kids cap ++ keys_blk 6 keys cap /\
                   exists k' y', Dnew = [(k', 56 * cap2 cap); (y', 8 * cap2 cap)])) /\
             pj_node segs mem' (lin Lam') o (JObj (pj_set_model ms (zb kname) tv)) Do)
         \/ (~ In (zb kname) (map fst ms) /\
             cnt <= fail < cnt + Z.of_nat (length (set_trace n cap (Z.of_nat (length kname)))) /\
             Z.of_nat c = fail - cnt + 1 /\ res = -1 /\
             peak' = Z.max peak (lsum Lam' + lsum Dw) /\
             (exists Dw', Permutation Dw Dw' /\
                rf_ok F A' (rf_frees F (rf_run F b (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname))))) Dw')) /\
             Z.of_nat (length Do) = Z.of_nat (length D) + nlive (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname)))) /\
             lsum Do = lsum D + held (firstn (c - 1)%nat (set_trace n cap (Z.of_nat (length kname)))) /\
             (exists Dold Dnew Dr, Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ Dr) /\
                new_blks L A Dnew /\
                (c = 1%nat /\ Dold = [] /\ Dnew = [] \/
                 n = cap /\ c = 2%nat /\ Dold = kids_blk kids cap /\ (exists k', Dnew = [(k', 56 * cap2 cap)]) \/
                 n = cap /\ c = 3%nat /\ Dold = kids_blk kids cap ++ keys_blk 6 keys cap /\
                   exists k' y', Dnew = [(k', 56 * cap2 cap); (y', 8 * cap2 cap)])) /\
             pj_freeable segs mem' (lin Lam') o Do /\
             (Z.of_nat c = Z.of_nat (length (set_trace n cap (Z.of_nat (length kname)))) ->
                pj_node segs mem' (lin Lam') o (JObj ms) Do)) )).

End K.

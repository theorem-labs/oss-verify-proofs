From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes WriterSpec WriterValue WriterApp WriterRet.
Import ListNotations.
Local Open Scope Z_scope.

Definition PJ_WRITE : Z := 0x15f58.

Definition wlen (t : jv) (p : bool) : Z := Z.of_nat (length (wdoc t p)).

Definition wcalls (t : jv) (p : bool) : Z := Z.of_nat (length (grow_calls 0 0 (piece_lens (wdpieces t p)))).

Definition wcap (t : jv) (p : bool) : Z := grow_cap 0 0 (piece_lens (wdpieces t p)).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition pj_write_hyp (kw : jv -> Z) : Prop :=
  forall L A regs mem md (v pretty : Z) (t : jv) (D Lam : list (Z * Z)) (peak cnt fail : Z) (b : rf_R F),
    let p := negb (pretty =? 0) in
    reader_env B API (kw t) L A regs mem md -> st_init_done A = true ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 v -> getr regs 11 = Z_to_bv 64 pretty -> 0 <= pretty < 2 ^ 64 ->
    pj_node segs mem (lin Lam) v t D -> (forall bk, In bk D -> In bk Lam) ->
    (spZ regs <= v \/ exists a k, In (a, k) Lam /\ a <= v /\ v + 56 <= a + k) ->
    wlen t p + 1 <= 2 ^ 28 -> (depth t <= 2 ^ 31 - 1)%nat ->
    wr_rooms F b (w0 cnt fail) (wdpieces t p) ->
    cnt + wcalls t p < 2 ^ 64 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PJ_WRITE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' Lam' peak' cnt' fail' q b',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
         rpost B API (kw t) L A regs mem md alloc_statics (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\
         ledger B L' A' mem' Lam' peak' cnt' fail' /\ peak <= peak' /\
         rf_ok F A' b' /\
         getr regs' 10 = Z_to_bv 64 q /\
         pj_node segs mem' (lin Lam') v t D /\
         ((fail < cnt \/ cnt + wcalls t p <= fail) ->
            q <> 0 /\ cnt' = cnt + wcalls t p /\ fail' = fail /\ b' = wfold F b (w0 cnt fail) (wdpieces t p) /\
            Permutation Lam' ((q, wcap t p) :: Lam) /\ new_blks L A [(q, wcap t p)] /\
            Forall (fun c => 0 < c < 256) (wdoc t p) /\
            Mem.bytes_at segs mem' q (map (Z_to_bv 8) (wdoc t p ++ [0]))) /\
         (cnt <= fail < cnt + wcalls t p ->
            q = 0 /\ cnt' = fail + 1 /\ fail' = 2 ^ 64 - 1 /\ Permutation Lam' Lam)).

End K.

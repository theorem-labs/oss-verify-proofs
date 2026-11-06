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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require check_reject_clean_c.
Import ListNotations.
Local Open Scope Z_scope.

(* Measured in the symtab of the #102 twin pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain (sha256
   c8f4d6b8e567b0b1...), the unstripped twin of the pinned fuzz_preset.plain 805604bb0907ae1b... (facts 8f3e7e1a07f1):
     parse_noting FUNC LOCAL 0x13a04 size 120: addi sp, sp, -0x30; jal fuzz_alloc_live; jal pj_parse;
     jal fuzz_alloc_ran_out; beqz a0, 0x13a5c; jal check_reject_clean; mv a0, s2; ret.
   Source (fuzz_preset.c of #102, lines 499-507): parse_noting(text, size, doc) has no int *ran_out parameter any more,
   and it no longer calls fuzz_alloc_ran_out_reset: it reads g_ran_out as its caller left it.
   G_RAN_OUT (one byte) is fuzz_alloc_ran_out_c's.  The caller hands in g_ran_out = 0 (every call site of the harness
   runs after the entry's reset and behind an out_of_memory() test).  Under room_run every allocation pj_parse makes
   succeeds, so pj_parse keeps g_ran_out, fuzz_alloc_ran_out returns that 0, the call to check_reject_clean is not
   reached, and g_ran_out is 0 again at the return.  parse_noting writes nothing but its frame and pj_parse's writes.
   PN_K keeps check_reject_clean's frame in its bound although that call is not reached, so that the callers' stack
   arithmetic stays as it was. *)
Definition PARSE_NOTING : Z := 0x13a04.
Definition PN_F : Z := 48.
Definition PN_K : Z := PN_F + Z.max PJ_PARSE_K check_reject_clean_c.CHECK_REJECT_CLEAN_FRAME.

Definition parse_noting_writes (out : Z) (x : Z) : Prop := pj_parse_writes out x.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition parse_noting_contract : Prop :=
  forall L A regs mem md Lam peak cnt fail b t0 len out tb,
    reader_env B API PN_K L A regs mem md ->
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
    Mem.bytes_at segs mem G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
    Frame.disjoint_from [(t0, t0 + len); (out, out + 56)] G_RAN_OUT 1 ->
    Frame.disjoint_from [(t0, t0 + len); (out, out + 56)] (spZ regs - PN_K) PN_K ->
    cnt + 2 * len + 2 < 2 ^ 64 - 1 ->
    room_run F b (snd (jr_run jr_strtod (zb tb) [])) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PARSE_NOTING) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' Lam' peak' cnt' fail' ok res tr,
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
         rpost B API PN_K L A regs mem md (parse_noting_writes out) (fun _ _ => False) L' A' regs' mem' md' /\
         rd_cells B mem' /\
         Mem.bytes_at segs mem' G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) /\
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

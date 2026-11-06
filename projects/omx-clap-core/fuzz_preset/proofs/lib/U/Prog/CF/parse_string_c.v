From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition PARSE_STRING : Z := 0x16ff8.

Definition parse_string_writes (q a n : Z) (x : Z) : Prop :=
  0 < n /\ (q <= x < q + 8 \/ alloc_statics x \/ (a <> 0 /\ a - 16 <= x < a + n)).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.

Definition parse_string_contract : Prop :=
  forall L A regs mem md Lam peak cnt fail b q text len p d tb,
    reader_env B API PARSE_STRING_K L A regs mem md ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok F A b ->
    getr regs 10 = Z_to_bv 64 q ->
    pj_in_ok segs mem q text len p d tb ->
    p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) ->
    spZ regs <= q -> (st_init_done A = false -> auxv_pre B (ly_sec L) (q + 24) mem) ->
    text_ok B L A Lam regs text len ->
    Frame.disjoint_from [(q, q + 24); (text, text + len)] (spZ regs - PARSE_STRING_K) PARSE_STRING_K ->
    cnt + 1 < 2 ^ 64 - 1 ->
    (forall Q, scan (rest_at tb text (p + 1)) = Some Q ->
       rf_room F b (Z.of_nat Q + 17) /\ Z.of_nat Q + 17 <= 2 ^ 28) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PARSE_STRING) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' Lam' peak' cnt' fail' b' res a n,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         rpost B API PARSE_STRING_K L A regs mem md (parse_string_writes q a n) (fun _ _ => False)
           L' A' regs' mem' md' /\
         rd_cells B mem' /\
         getr regs' 10 = Z_to_bv 64 res /\
         ledger B L' A' mem' Lam' peak' cnt' fail' /\
         rf_ok F A' b' /\
         match scan (rest_at tb text (p + 1)) with
         | None =>
             res = 0 /\ a = 0 /\ n = 0 /\ L' = L /\ A' = A /\ Lam' = Lam /\ peak' = peak /\ cnt' = cnt /\
             fail' = fail /\ b' = b /\ pj_in_ok segs mem' q text len p d tb
         | Some Q =>
             n = Z.of_nat Q + 1 /\ cnt' = cnt + 1 /\
             ( (cnt = fail /\ res = 0 /\ a = 0 /\ Lam' = Lam /\ peak' = peak /\ fail' = 2 ^ 64 - 1 /\
                b' = b /\ pj_in_ok segs mem' q text len p d tb)
             \/ (cnt <> fail /\ decode (rest_at tb text (p + 1)) = None /\ res = 0 /\ a <> 0 /\
                 Lam' = Lam /\ peak' = Z.max peak (lsum Lam + n) /\ fail' = fail /\
                 (forall x, a - 16 <= x < a + n ->
                    ~ in_img B x /\ (forall p0 k0, In (p0, k0) (blocks L A) -> ~ (p0 <= x < p0 + k0))) /\
                 a + n <= alloc_ceiling /\
                 b' = rf_free F (rf_malloc F b (n + 16)) (n + 16) /\ pj_in_ok segs mem' q text len p d tb)
             \/ (cnt <> fail /\ res = a /\ a <> 0 /\
                 exists s r, decode (rest_at tb text (p + 1)) = Some (s, r) /\
                   Lam' = (a, n) :: Lam /\ new_blks L A [(a, n)] /\ peak' = Z.max peak (lsum Lam + n) /\ fail' = fail /\
                   b' = rf_malloc F b (n + 16) /\ pj_cbytes segs mem' a s /\
                   pj_in_ok segs mem' q text len (p + n + 1) d tb) )
         end).

End K.

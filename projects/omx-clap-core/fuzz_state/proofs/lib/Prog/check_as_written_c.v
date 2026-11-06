From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm AllocSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger WriterSpec HState.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_AS_WRITTEN : Z := 0x135ec.
Definition CAW_FRAME : Z := 48.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition caw_answer (mem : word -> option byte) (tb : list byte) (bd l : Z) : Prop :=
  (b64_dec (zs tb) = None /\ bd = 0 /\ l = 2 ^ 64 - 1) \/
  (exists bs, b64_dec (zs tb) = Some bs /\ bd <> 0 /\ l = Z.of_nat (length bs) /\
     Mem.bytes_at segs mem bd (bz bs)).

Definition check_as_written_contract : Prop :=
  forall L A regs mem md t tb slack bd l bnd Lam peak cnt fail,
    call_pre_k B MR (ALLOC_STACK + CAW_FRAME) L A regs mem md ->
    getr regs 10 = Z_to_bv 64 t -> getr regs 11 = Z_to_bv 64 bd -> getr regs 12 = Z_to_bv 64 l ->
    Mem.bytes_at segs mem t (tb ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) tb ->
    (- (t + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
    Z.of_nat (length tb) <= 3 * 2 ^ 20 ->
    (forall a, t <= a < t + Z.of_nat (length tb) + 1 + Z.of_nat (length slack) ->
       ~ in_window (spZ regs) (ALLOC_STACK + CAW_FRAME) a) ->
    (exists pt kt, In (pt, kt) (blocks L A) /\ pt <= t /\ t + Z.of_nat (length tb) + 1 <= pt + kt) ->
    caw_answer mem tb bd l ->
    (bd <> 0 -> exists k, In (bd, k) Lam /\ l <= k) ->
    ledger B L A mem Lam peak cnt fail ->
    ro_agree segs mem ->
    res_ok_slots A bnd ->
    room_slots bnd (b64_alloc_bound (Z.of_nat (length tb))) ->
    room_slots (sb_malloc bnd (b64_alloc_bound (Z.of_nat (length tb)))) (Z.max (Z.of_nat (length tb)) 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHECK_AS_WRITTEN) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' w s,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\ st_init_done A' = true /\
         fresh_block B w (b64_alloc_bound (Z.of_nat (length tb))) /\
         fresh_block B s (Z.max (Z.of_nat (length tb)) 1) /\
         (forall a k, In (a, k) (blocks L A) ->
            a + k <= w \/ w + b64_alloc_bound (Z.of_nat (length tb)) <= a) /\
         (forall a k, In (a, k) (blocks L A) ->
            a + k <= s \/ s + Z.max (Z.of_nat (length tb)) 1 <= a) /\
         call_post_k B MR (ALLOC_STACK + CAW_FRAME) L A regs mem md
           (fun a => w <= a < w + b64_alloc_bound (Z.of_nat (length tb)) \/
                     s <= a < s + Z.max (Z.of_nat (length tb)) 1) L' A' regs' mem' md' /\
         blocks L' A' = blocks L A /\
         keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
         ledger B L' A' mem' Lam peak cnt fail /\
         res_ok_slots A' bnd).

End K.

From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition RECORD : Z := 0x1612c.
Definition RECORD_K : Z := 32 + (ALLOC_STACK + 112).

Definition rec_slot (R : rstate) : Z :=
  if Nat.ltb (length (r_calls R)) 16
  then G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))
  else REC_SC.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition record_contract : Prop :=
  forall L A regs mem md (fn : Z) (R : rstate) (O : list (Z * Z)) b,
    call_pre_k B MR RECORD_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 fn -> 0 <= fn < REC_FN_COUNT ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> f18_words segs mem ->
    res_ok_slots A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 RECORD) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' O' D,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_rec B MR RECORD_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 (rec_slot R) /\
         g_rec_rep segs L' A' mem' (rec_record R fn []) O' /\
         (forall pn, In pn O' -> In pn O) /\
         (forall pn, In pn D <-> In pn O /\ ~ In pn O') /\
         Permutation (blocks L A) (blocks L' A' ++ D) /\
         others_kept segs L A mem L' A' mem' O /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         ro_agree segs mem' /\ f18_words segs mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         (st_init_done A = false -> L' = L /\ A' = A /\ (forall lo, spZ regs <= lo ->
            auxv_pre B (ly_sec L) lo mem -> auxv_pre B (ly_sec L') lo mem')) /\
         sb_le (sb_shift b A A') (rfree_b b D) /\
         res_ok_slots A' (sb_shift b A A')).

End K.

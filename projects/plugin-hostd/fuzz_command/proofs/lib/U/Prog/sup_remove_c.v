From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition SUP_REMOVE : Z := 0x1669c.
Definition SUP_REMOVE_K : Z := 12432.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition sup_remove_contract : Prop :=
  forall L A regs mem md (id : Z) (R : rstate) (O : list (Z * Z)) b,
    call_pre_t B API SUP_REMOVE_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_mallocs b [Z.of_nat (length (dec id)) + 1; 17; 17]) 17 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SUP_REMOVE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
         sup_remove_m R id = (R', t) /\
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         fp_kept fx fx' /\
         call_post_rec B MR SUP_REMOVE_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 q /\
         g_rec_rep segs L' A' mem' R' O' /\ owns_new L A O O' /\
         In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
         ~ In q (map fst O') /\
         Mem.bytes_at segs mem' q (t ++ [Z_to_bv 8 0]) /\
         others_kept segs L A mem L' A' mem' O /\
         (forall pn, In pn (blocks L' A') ->
            (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
         (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
         ro_agree segs mem' /\ f18_words segs mem' /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         sb_le (sb_shift b A A') (sb_mallocs b [Z.of_nat (length (dec id)) + 1; Z.of_nat (length t) + 1; Z.of_nat (length t) + 1]) /\
         res_ok_slots A' (sb_shift b A A')).

End K.

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInvP RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition SUP_AFTER_REPLY : Z := 0x16d54.
Definition SUP_AFTER_REPLY_K : Z := 8288.

Definition sup_after_reply_sizes (id : Z) (verb : option (list byte)) : list Z :=
  [Z.of_nat (length (dec id)) + 1; Z.of_nat (length (sarg verb)) + 1].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition sup_after_reply_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (id : Z) (verb : option (list byte)) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config)
    : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    call_post_rec B MR SUP_AFTER_REPLY_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    g_rec_rep segs L' A' mem' (sup_after_reply_m R id verb) O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    others_kept segs L A mem L' A' mem' O /\
    ro_agree segs mem' /\ f18_words segs mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b (sup_after_reply_sizes id verb)) /\
    res_ok_slots A' (sb_shift b A A').

Definition sup_after_reply_contract : Prop :=
  forall L A regs mem md (id pv : Z) (verb : option (list byte)) (R : rstate) (O : list (Z * Z)) b,
    call_pre_t B API SUP_AFTER_REPLY_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
    getr regs 11 = Z_to_bv 64 pv ->
    str_arg B L A O (spZ regs) SUP_AFTER_REPLY_K mem pv verb ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_mallocs b (sup_after_reply_sizes id verb)) (LMAX + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SUP_AFTER_REPLY) mem (seg_rom segs)) md)
      (sup_after_reply_ret L A regs mem md id verb R O b).

End K.

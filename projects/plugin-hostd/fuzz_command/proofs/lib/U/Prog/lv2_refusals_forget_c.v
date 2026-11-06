From Stdlib Require Import String ZArith List Bool Lia.
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

Definition LV2_REFUSALS_FORGET : Z := 0x1731c.
Definition LV2_REFUSALS_FORGET_K : Z := 8368.

Definition lv2_refusals_forget_size (uri : option (list byte)) : Z :=
  Z.of_nat (length (darg uri (bstr "*"%string))) + 1.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition lv2_refusals_forget_contract : Prop :=
  forall L A regs mem md (pu : Z) (uri : option (list byte)) (R : rstate) (O : list (Z * Z)) b,
    call_pre_k B MR LV2_REFUSALS_FORGET_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 pu ->
    str_arg B L A O (spZ regs) LV2_REFUSALS_FORGET_K mem pu uri ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_mallocs b [lv2_refusals_forget_size uri]) (LMAX + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LV2_REFUSALS_FORGET) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' O',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_rec B MR LV2_REFUSALS_FORGET_K L A regs mem md rec_area (fun a => In a (map fst O))
           L' A' regs' mem' md' /\
         g_rec_rep segs L' A' mem' (lv2_refusals_forget_m R uri) O' /\ owns_new L A O O' /\
         others_kept segs L A mem L' A' mem' O /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         ro_agree segs mem' /\ f18_words segs mem' /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         sb_le (sb_shift b A A') (sb_mallocs b [lv2_refusals_forget_size uri]) /\
         res_ok_slots A' (sb_shift b A A')).

End K.

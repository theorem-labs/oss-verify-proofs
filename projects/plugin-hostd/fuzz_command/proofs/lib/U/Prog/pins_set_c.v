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

Definition PINS_SET : Z := 0x170a8.
Definition PINS_SET_K : Z := 8384.

Definition pins_set_args (uri files layout verdict : option (list byte)) : list (list byte) :=
  [sarg uri; sarg files; sarg layout; darg verdict (bstr "-"%string)].

Definition pins_set_sizes (uri files layout verdict : option (list byte)) (r : Z) : list Z :=
  map (fun y => Z.of_nat (length y) + 1) (pins_set_args uri files layout verdict) ++
  [Z.of_nat (length (resp r)) + 1; Z.of_nat (length (resp r)) + 1].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition pins_set_contract : Prop :=
  forall L A regs mem md (pu pf pl pv : Z) (uri files layout verdict : option (list byte)) (R : rstate)
         (O : list (Z * Z)) b,
    call_pre_t B API PINS_SET_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 pu -> getr regs 11 = Z_to_bv 64 pf ->
    getr regs 12 = Z_to_bv 64 pl -> getr regs 13 = Z_to_bv 64 pv ->
    str_arg B L A O (spZ regs) PINS_SET_K mem pu uri -> str_arg B L A O (spZ regs) PINS_SET_K mem pf files ->
    str_arg B L A O (spZ regs) PINS_SET_K mem pl layout -> str_arg B L A O (spZ regs) PINS_SET_K mem pv verdict ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_mallocs b (pins_set_sizes uri files layout verdict (snd (pins_set_m R uri files layout verdict))))
      (LMAX + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PINS_SET) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' r,
         pins_set_m R uri files layout verdict = (R', r) /\
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         fp_kept fx fx' /\
         call_post_rec B MR PINS_SET_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 r /\
         g_rec_rep segs L' A' mem' R' O' /\ owns_new L A O O' /\
         others_kept segs L A mem L' A' mem' O /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         ro_agree segs mem' /\ f18_words segs mem' /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         sb_le (sb_shift b A A') (sb_mallocs b (pins_set_sizes uri files layout verdict r)) /\
         res_ok_slots A' (sb_shift b A A')).

End K.

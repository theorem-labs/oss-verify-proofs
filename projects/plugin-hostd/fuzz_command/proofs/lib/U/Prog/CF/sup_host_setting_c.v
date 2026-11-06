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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition SUP_HOST_SETTING : Z := 0x16810.
Definition SUP_HOST_SETTING_K : Z := 8432.

Definition sup_host_setting_len (toks : list (list byte)) : Z :=
  fold_right (fun w s => Z.of_nat (length w) + 1 + s) 0 toks.

Definition sup_host_setting_sizes (line : list byte) (toks : list (list byte)) : list Z :=
  [Z.of_nat (length line) + 1; Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1;
   sup_host_setting_len toks + 1; Z.of_nat (length (join_sp toks)) + 1].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition sup_host_setting_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (line : list byte) (toks : list (list byte)) (R : rstate) (O : list (Z * Z)) (b : sbound)
    (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    call_post_rec B MR SUP_HOST_SETTING_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    g_rec_rep segs L' A' mem' (sup_host_setting_m R line toks) O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    others_kept segs L A mem L' A' mem' O /\
    ro_agree segs mem' /\ f18_words segs mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b (sup_host_setting_sizes line toks)) /\
    res_ok_slots A' (sb_shift b A A').

Definition sup_host_setting_contract : Prop :=
  forall L A regs mem md (pl ptok : Z) (ps : list Z) (line : list byte) (toks : list (list byte)) (R : rstate)
         (O : list (Z * Z)) b,
    call_pre_t B API SUP_HOST_SETTING_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 pl -> getr regs 11 = Z_to_bv 64 ptok ->
    getr regs 12 = Z_to_bv 64 (Z.of_nat (length toks)) -> (1 <= length toks <= 64)%nat ->
    str_arg B L A O (spZ regs) SUP_HOST_SETTING_K mem pl (Some line) ->
    ptok <> 0 -> ptok mod 8 = 0 ->
    Mem.bytes_at segs mem ptok (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) ps)) ->
    (ptok + 8 * Z.of_nat (length toks) <= spZ regs - SUP_HOST_SETTING_K \/ spZ regs <= ptok) ->
    buf_home B L A O (spZ regs) ptok (8 * Z.of_nat (length toks)) ->
    (forall a, ptok <= a < ptok + 8 * Z.of_nat (length toks) -> ~ rec_area a) ->
    Forall2 (fun p w => str_arg B L A O (spZ regs) SUP_HOST_SETTING_K mem p (Some w)) ps toks ->
    sup_host_setting_len toks <= LMAX + 1 ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_ag (sb_mallocs b (sup_host_setting_sizes line toks)) (LMAX + 2) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SUP_HOST_SETTING) mem (seg_rom segs)) md)
      (sup_host_setting_ret L A regs mem md line toks R O b).

End K.

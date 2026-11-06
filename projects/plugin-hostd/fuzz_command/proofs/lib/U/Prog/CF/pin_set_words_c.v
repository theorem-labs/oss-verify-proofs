From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition PIN_SET_WORDS : Z := 0x17e94.
Definition PSW_K : Z := 48 + 13312.
Definition PSW_MALLOCS : nat := 7%nat.
Definition PSW_REQ : Z := 8194.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition psw_writes (a : Z) : Prop := G_REC <= a < G_REC + REC_SIZE \/ REC_SC <= a < REC_SC + SC_SIZE.

Definition pin_set_words_contract : Prop :=
  forall L A regs mem md b (R : rstate) (O : list (Z * Z)) (line nl tok cb ncb ntok : Z) (T : list byte)
         (ptrs : list Z) (tks : list (list byte)) (can : word),
    call_pre_t B API PSW_K L A regs mem md ->
    ro_agree segs mem -> frm_zero fp_csr ->
    getr regs 10 = Z_to_bv 64 line -> getr regs 11 = Z_to_bv 64 tok -> getr regs 12 = Z_to_bv 64 ntok ->
    In (line, nl) (blocks L A) -> ~ In (line, nl) O ->
    le_at B mem line (T ++ [Z_to_bv 8 0]) -> Forall (fun c => bv_unsigned c <> 0) T ->
    Z.of_nat (length T) + 1 <= nl ->
    In (cb, ncb) (blocks L A) -> ~ In (cb, ncb) O ->
    toks_at B mem tok ptrs tks cb ncb -> ntok = Z.of_nat (length tks) -> 1 <= ntok <= 64 ->
    nth_error tks 0 = Some Verbs.Lit.verb_pin_set ->
    bv_unsigned (getr regs 2) <= tok -> tok + 8 * ntok < 2 ^ 63 ->
    outside B L A PSW_K regs tok (8 * ntok) ->
    g_rec_rep segs L A mem R O -> (r_refuse R <> 0 -> declared (r_code R) = true) ->
    ssp_b B mem can ->
    res_ok_slots A b -> room_ag (sb_n b PSW_MALLOCS) PSW_REQ ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PIN_SET_WORDS) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' O' k,
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         CF.RecKindB.fp_kept fx fx' /\
         CF.RecKindB.call_post_rec B MR PSW_K L A regs mem md psw_writes (fun a => In a (map fst O)) L' A' regs' mem' md' /\
         ro_agree segs mem' /\
         (let '(R', r) := VerbsRun.pin_set_run R T (tl tks) in
            g_rec_rep segs L' A' mem' R' O' /\ getr regs' 10 = Z_to_bv 64 r) /\
         le_at B mem' line (T ++ [Z_to_bv 8 0]) /\ toks_at B mem' tok ptrs tks cb ncb /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> In pn (blocks L' A')) /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> ~ In pn O') /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         blocks_kept B L A mem mem' (fun a => exists j, In (a, j) O) /\
         (exists can', ssp_b B mem' can') /\
         (k <= PSW_MALLOCS)%nat /\ res_ok_slots A' (sb_n b k)).

End K.

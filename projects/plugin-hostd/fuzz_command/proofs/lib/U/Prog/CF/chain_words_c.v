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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHAIN_WORDS : Z := 0x17d0c.
Definition CW_K : Z := 352 + 12512.
Definition CW_MALLOCS : nat := 6%nat.
Definition CW_REQ : Z := 8194.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition cw_writes (a : Z) : Prop := G_REC <= a < G_REC + REC_SIZE \/ REC_SC <= a < REC_SC + SC_SIZE.

Definition chain_words_contract : Prop :=
  forall L A regs mem md b (R : rstate) (O : list (Z * Z)) (tok cb ncb ntok : Z)
         (ptrs : list Z) (tks : list (list byte)) (can : word),
    call_pre_t B API CW_K L A regs mem md ->
    ro_agree segs mem -> frm_zero fp_csr ->
    getr regs 10 = Z_to_bv 64 tok -> getr regs 11 = Z_to_bv 64 ntok ->
    In (cb, ncb) (blocks L A) -> ~ In (cb, ncb) O ->
    toks_at B mem tok ptrs tks cb ncb -> ntok = Z.of_nat (length tks) -> 1 <= ntok <= 64 ->
    nth_error tks 0 = Some Verbs.Lit.verb_chain ->
    bv_unsigned (getr regs 2) <= tok -> tok + 8 * ntok < 2 ^ 63 ->
    outside B L A CW_K regs tok (8 * ntok) ->
    (errno_addr B + 4 <= cb \/ cb + ncb <= errno_addr B) ->
    (errno_addr B + 4 <= SSP_GUARD_B \/ SSP_GUARD_B + 8 <= errno_addr B) ->
    g_rec_rep segs L A mem R O -> (r_refuse R <> 0 -> declared (r_code R) = true) ->
    ssp_b B mem can ->
    Mem.bytes_at segs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
    res_ok_slots A b -> room_ag (sb_n b CW_MALLOCS) CW_REQ ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 CHAIN_WORDS) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' O' k p n,
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         CF.RecKindB.fp_kept fx fx' /\
         CF.RecKindB.call_post_rec B MR CW_K L A regs mem md cw_writes (fun a => In a (map fst O)) L' A' regs' mem' md' /\
         ro_agree segs mem' /\
         (let '(R', x) := VerbsRun.chain_run R (tl tks) in
            g_rec_rep segs L' A' mem' R' O' /\
            le_at B mem' p (x ++ [Z_to_bv 8 0]) /\ Z.of_nat (length x) + 1 <= n) /\
         getr regs' 10 = Z_to_bv 64 p /\ In (p, n) (blocks L' A') /\ ~ In (p, n) O' /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> fst pn + snd pn <= p \/ p + n <= fst pn) /\
         toks_at B mem' tok ptrs tks cb ncb /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> In pn (blocks L' A')) /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (p, n)) /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> ~ In pn O') /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         blocks_kept B L A mem mem' (fun a => exists j, In (a, j) O) /\
         (exists can', ssp_b B mem' can') /\
         Mem.bytes_at segs mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
         (k <= CW_MALLOCS)%nat /\ res_ok_slots A' (sb_n b k)).

End K.

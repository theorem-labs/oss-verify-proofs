From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition REPLY : Z := 0x17c4c.
Definition RP_K : Z := 8448.
Definition RP_MALLOCS : nat := 1%nat.
Definition RP_REQ : Z := 8194.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition rp_writes (a : Z) : Prop := G_REC <= a < G_REC + REC_SIZE \/ REC_SC <= a < REC_SC + SC_SIZE.

Definition reply_contract : Prop :=
  forall L A regs mem md b (R : rstate) (O : list (Z * Z)) (q nq : Z) (X : list byte) (can : word),
    call_pre_t B API RP_K L A regs mem md ->
    ro_agree segs mem ->
    getr regs 11 = Z_to_bv 64 q ->
    In (q, nq) (blocks L A) -> ~ In (q, nq) O ->
    le_at B mem q (X ++ [Z_to_bv 8 0]) -> Forall (fun c => bv_unsigned c <> 0) X ->
    Z.of_nat (length X) + 1 <= nq -> Z.of_nat (length X) <= 4096 ->
    g_rec_rep segs L A mem R O -> r_nreplies R < 2 ^ 31 - 1 ->
    ssp_b B mem can ->
    res_ok_slots A b -> room_ag (sb_n b RP_MALLOCS) RP_REQ ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 REPLY) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' O' k,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         CF.RecKindB.call_post_rec B MR RP_K L A regs mem md rp_writes (fun a => In a (map fst O)) L' A' regs' mem' md' /\
         ro_agree segs mem' /\
         g_rec_rep segs L' A' mem' (fst (socket_send_m R (X ++ [Z_to_bv 8 0]))) O' /\
         ~ In (q, nq) (blocks L' A') /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> pn <> (q, nq) -> In pn (blocks L' A')) /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O /\ pn <> (q, nq)) \/ In pn O') /\
         (forall pn, In pn O' -> In pn O \/ ~ In pn (blocks L A)) /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> ~ In pn O') /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         blocks_kept B L A mem mem' (fun a => (exists j, In (a, j) O) \/ a = q) /\
         (exists can', ssp_b B mem' can') /\
         (k <= RP_MALLOCS)%nat /\ res_ok_slots A' (sb_n b k)).

End K.

From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB rec_calls_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition REC_CLEAR : Z := 0x15ab4.
Definition RCL_K : Z := 16 + RCF_K.

Definition rec_clear_writes (n : nat) (a : Z) : Prop :=
  G_REC + OFF_NCALLS <= a < G_REC + OFF_NCALLS + 4 \/
  nargs_field (G_REC + OFF_CALLS) n a \/
  G_REC + OFF_ANSWER <= a < G_REC + OFF_NREPLIES + 4 \/
  G_REC + OFF_REPLY <= a < G_REC + OFF_REPLY_SIZE + 8.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition rec_clear_contract : Prop :=
  forall L A regs mem md (R : rstate) (O : list (Z * Z)) b,
    call_pre_k B MR RCL_K L A regs mem md ->
    ro_agree segs mem ->
    g_rec_rep segs L A mem R O ->
    res_ok_slots A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 REC_CLEAR) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' O' D,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR RCL_K L A regs mem md (rec_clear_writes (length (r_calls R))) L' A' regs' mem' md' /\
         g_rec_rep segs L' A' mem' (rec_clear R) O' /\
         (forall pn, In pn O' -> In pn O) /\
         (forall pn, In pn D <-> In pn O /\ ~ In pn O') /\
         Permutation (blocks L A) (blocks L' A' ++ D) /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         blocks_kept B L A mem mem' (fun a => In a (map fst D)) /\
         (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) D -> In (q, k) (user_blocks A')) /\
         (forall x, In x (user_blocks A') -> In x (user_blocks A)) /\
         (forall a, in_globals frame_G a -> ~ rec_clear_writes (length (r_calls R)) a ->
            mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (rfree_b b D)).

End K.

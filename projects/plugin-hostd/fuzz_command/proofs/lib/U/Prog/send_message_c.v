From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU VerbsB CommandB
  verbs_receive_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition SEND_MESSAGE : Z := 0x14444.
Definition SEND_MESSAGE_FRAME : Z := 64.
Definition SM_K : Z := SEND_MESSAGE_FRAME + VR_K.
(* Peak extra live blocks and bytes of one call above its entry bound: the message copy (<= 8192 bytes) and
   verbs_receive's peak (32 blocks, 262208 bytes). *)
Definition SM_PEAK : Z := 33.
Definition SM_PEAKB : Z := 2 ^ 19.
Definition sb_up (b : sbound) (k n : Z) : sbound := SB (sb_live b + k) (sb_bytes b + n) (sb_cap b).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition send_message_contract : Prop :=
  forall L A regs mem md b (R : rstate) (O : list (Z * Z)) (src n q0 : Z) (D : list byte) (can : word),
    segs = rsegs ->
    call_pre_t B API SM_K L A regs mem md -> cmd_mem B mem -> frm_zero fp_csr ->
    getr regs 10 = Z_to_bv 64 src -> getr regs 11 = Z_to_bv 64 n ->
    le_at B mem src D -> Z.of_nat (length D) = n -> n <= 8192 ->
    (n <> 0 -> 4096 <= src /\ src + n <= 2 ^ 64 /\ in_live L A O src n /\
       forall i, 0 <= i < n -> ~ vr_writes (src + i) /\ ~ scratch_k B SM_K regs (src + i)) ->
    g_rec_rep segs L A mem R O ->
    (r_refuse R <> 0 -> declared (r_code R) = true) ->
    le_at B mem G_QUIT (Mem.le4 (Z_to_bv 64 q0)) ->
    (forall i, 0 <= i < 4 -> writable_at segs mem (G_QUIT + i)) ->
    outside B L A SM_K regs G_QUIT 4 ->
    vr_tables B mem can ->
    res_ok_slots A b -> room_slots (sb_up b SM_PEAK SM_PEAKB) VR_REQ ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SEND_MESSAGE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md' O' b',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\ frm_zero (@fp_csr fx') /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         call_post_ko B MR SM_K L A regs mem md vr_writes O L' A' regs' mem' md' /\
         cmd_mem B mem' /\
         (let '(R', x, quit) := vr_run (rec_clear R) D in
            g_rec_rep segs L' A' mem' R' O' /\
            le_at B mem' G_QUIT (Mem.le4 (Z_to_bv 64 (if quit then 1 else 0)))) /\
         le_at B mem' src D /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         blocks_stay L A O L' A' /\
         (forall pn, In pn (blocks L A) -> ~ In (fst pn) (map fst O) -> ~ In pn O') /\
         blocks_kept B L A mem mem' (owned_by O) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (exists can', vr_tables B mem' can') /\
         res_ok_slots A' b' /\ sb_cap b' = sb_cap b).

End K.

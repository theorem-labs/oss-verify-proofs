From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require atoi_c sup_reply_code_c rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition VERBS_RECEIVE : Z := 0x1742c.
Definition VR_K : Z := 608 + 14336.
Definition VR_MALLOCS : nat := 32%nat.
Definition VR_REQ : Z := 8194.

Definition vr_run (R : rstate) (D : list byte) : rstate * list byte * bool :=
  VerbsRun.run_receive atoi_c.atoi_val sup_reply_code_c.reply_code R D.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition owned_by (O : list (Z * Z)) (a : Z) : Prop := exists k, In (a, k) O.

Definition vr_writes (a : Z) : Prop :=
  G_REC <= a < G_REC + REC_SIZE \/ REC_SC <= a < REC_SC + SC_SIZE \/ G_QUIT <= a < G_QUIT + 4.

Definition verbs_receive_contract : Prop :=
  forall L A regs mem md b (R : rstate) (O : list (Z * Z)) (msg fd data n q0 : Z) (D : list byte) (can : word),
    call_pre_t B API VR_K L A regs mem md ->
    ro_agree segs mem -> frm_zero fp_csr ->
    getr regs 10 = Z_to_bv 64 msg -> msg mod 8 = 0 -> 4096 <= msg -> msg + 24 <= 2 ^ 63 ->
    bv_unsigned (getr regs 2) <= msg ->
    in_img B (errno_addr B) -> (errno_addr B + 4 <= SSP_GUARD_B \/ SSP_GUARD_B + 8 <= errno_addr B) ->
    le_at B mem msg (Mem.le4 (Z_to_bv 64 fd)) ->
    le_at B mem (msg + 8) (Mem.le8 (Z_to_bv 64 data)) ->
    le_at B mem (msg + 16) (Mem.le8 (Z_to_bv 64 n)) ->
    outside B L A VR_K regs msg 24 -> (forall i, 0 <= i < 24 -> ~ vr_writes (msg + i)) ->
    In (data, Z.max n 1) (blocks L A) -> ~ In (data, Z.max n 1) O ->
    le_at B mem data D -> Z.of_nat (length D) = n -> n <= 8192 ->
    g_rec_rep segs L A mem R O ->
    r_calls R = [] -> r_answer R = None -> r_reply R = None -> r_nreplies R = 0 ->
    (r_refuse R <> 0 -> declared (r_code R) = true) ->
    le_at B mem G_QUIT (Mem.le4 (Z_to_bv 64 q0)) ->
    (forall i, 0 <= i < 4 -> writable_at segs mem (G_QUIT + i)) ->
    outside B L A VR_K regs G_QUIT 4 ->
    vr_tables B mem can ->
    Mem.bytes_at segs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
    res_ok_slots A b -> room_slots (SB (sb_live b + 32) (sb_bytes b + 262208) (sb_cap b)) VR_REQ ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 VERBS_RECEIVE) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' O' b',
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         RecKindB.fp_kept fx fx' /\
         RecKindB.call_post_rec B MR VR_K L A regs mem md vr_writes (fun a => In a (map fst O)) L' A' regs' mem' md' /\
         ro_agree segs mem' /\
         (let '(R', x, quit) := vr_run R D in
            g_rec_rep segs L' A' mem' R' O' /\
            le_at B mem' G_QUIT (Mem.le4 (Z_to_bv 64 (if quit then 1 else q0)))) /\
         In (data, Z.max n 1) (blocks L' A') /\ le_at B mem' data D /\
         ~ In (data, Z.max n 1) O' /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> In pn (blocks L' A')) /\
         (forall pn, In pn (blocks L A) -> ~ In pn O -> ~ In pn O') /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         le_at B mem' msg (Mem.le4 (Z_to_bv 64 fd)) /\
         le_at B mem' (msg + 8) (Mem.le8 (Z_to_bv 64 data)) /\
         le_at B mem' (msg + 16) (Mem.le8 (Z_to_bv 64 n)) /\
         (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
         blocks_kept B L A mem mem' (owned_by O) /\
         (exists can', vr_tables B mem' can') /\
         Mem.bytes_at segs mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
         res_ok_slots A' b' /\ sb_cap b' = sb_cap b).

End K.

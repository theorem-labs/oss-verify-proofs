From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps.
Import ListNotations.
Local Open Scope Z_scope.

Definition JT_BASE : Z := 0x10460.
Definition TAIL_CHECK : Z := 0x142b0.
Definition TAIL_STEP : Z := 0x142bc.
Definition OP9_AT : Z := 0x14424.

Definition jt_target (op : Z) : Z :=
  nth (Z.to_nat op) [0x14248; 0x141fc; 0x14334; 0x143a0; 0x142d0; 0x143d8; 0x143f4; 0x143b4; 0x14408] OP9_AT.

Definition pick_op (op : Z) : bool := (op =? 1) || (op =? 2) || (op =? 3) || (op =? 4) || (op =? 6).

Definition disp_k (E : sstart) (op k : Z) : Z := if pick_op op && (k + 1 <? ss_n E) then k + 2 else k + 1.

Definition disp_src (op s : Z) (hj : list (hsrc * nat)) : Prop :=
  (pick_op op = true /\ exists i, (i < 4)%nat /\ slot_open hj i = true /\ s = G_S + SRC_SIZE * Z.of_nat i) \/
  ((pick_op op = false \/ op = 1) /\ s = 0).

Section MI.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable E : sstart.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition base_regs (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (slot_sp E) /\ getr regs 3 = getr (ss_regs E) 3 /\
  getr regs 4 = getr (ss_regs E) 4 /\ getr regs 20 = Z_to_bv 64 G_RELAY_LO.

Definition fix_regs (regs : bvmap 5 word) : Prop :=
  getr regs 23 = Z_to_bv 64 (slot_sp E + 32) /\ getr regs 25 = Z_to_bv 64 DIV10 /\
  getr regs 21 = Z_to_bv 64 10 /\ getr regs 19 = Z_to_bv 64 4 /\
  getr regs 27 = Z_to_bv 64 (G_S + 4) /\ getr regs 24 = Z_to_bv 64 1.

Definition disp_regs (t k s : Z) (regs : bvmap 5 word) : Prop :=
  base_regs regs /\ fix_regs regs /\
  getr regs 8 = Z_to_bv 64 (ss_p E + k) /\ getr regs 26 = Z_to_bv 64 (ss_n E - k) /\
  getr regs 22 = Z_to_bv 64 t /\ getr regs 9 = Z_to_bv 64 s.

Definition tail_regs (t k : Z) (regs : bvmap 5 word) : Prop :=
  base_regs regs /\ fix_regs regs /\
  getr regs 8 = Z_to_bv 64 (ss_p E + k) /\ getr regs 26 = Z_to_bv 64 (ss_n E - k) /\
  getr regs 22 = Z_to_bv 64 t.

Definition tail48_regs (t k : Z) (regs : bvmap 5 word) : Prop :=
  base_regs regs /\ fix_regs regs /\
  getr regs 9 = Z_to_bv 64 (ss_n E - k) /\ getr regs 18 = Z_to_bv 64 (ss_p E + k) /\
  getr regs 22 = Z_to_bv 64 t.

Definition stack_mid (mem : word -> option byte) : Prop :=
  rw_cells segs mem (slot_sp E + 88) (saved_cells (ss_regs E)) /\
  rw_cells segs mem (slot_sp E) [C8 (Z_to_bv 64 CLIENT_BASE)] /\
  rw_cells segs mem (slot_sp E + 8) [C8 (Z_to_bv 64 G_S)].

Definition MI (RI : sstart -> Z -> rview -> layout -> astate -> Prop) (t k pc : Z)
    (RG : list rentry -> list (hsrc * nat) -> Z -> bvmap 5 word -> Prop) (c : config) : Prop :=
  exists (fx' : FPState) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat)),
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx') /\
    0 <= t < OPS_MAX /\ 0 <= k <= ss_n E /\ ss_n E < INPUT_MAX /\
    RG es hj (bv_unsigned nout) regs /\
    MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
    (exists vm, md = with_vmmaps vm (ss_md E)) /\
    ro_agree segs mem /\
    image_kept (rc := rc) B E mem /\
    stack_mid mem /\
    driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem /\
    globals_at B mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out /\
    0 <= nfd <= t + (if (pc =? TAIL_CHECK) || (pc =? TAIL_STEP) then 2 else 1) /\
    output_at (rc := rc) B L A mem nout cap out /\
    relay_at (rc := rc) B L A mem (t + (if (pc =? TAIL_CHECK) || (pc =? TAIL_STEP) then 1 else 0)) nfd G (bv_unsigned out) es hj /\
    (length es <= 4)%nat /\
    slot_cost es hj <= k /\
    RI E k (view_of G (bv_unsigned out) es hj) L A.

End MI.
